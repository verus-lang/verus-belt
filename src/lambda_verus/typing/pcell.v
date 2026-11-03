From lrust.typing Require Export type own value_ctx shr_bor uniq_bor gmb_cells.
From lrust.typing Require Import programs freeable_util uninit uniq_util bool product gmb_uniq.
From guarding Require Import guard tactics.
From lrust.lifetime Require Import lifetime_full guarded_bor.
Set Default Proof Using "Type".

(** * [PCell] on guarded mutable borrows

Phase 4 of [design_docs/guarded-mutable-borrows-plan.md]: a [PCell<T>] is an instance [γ]
of the GMB library ([lifetime/guarded_bor.v]) whose placement is the location of the cell
and whose logical contents are the fancy value of the contents ([typing/gmb_cells.v]); the
contents are ordinary memory, the exact fancy bytes [gcont l m fv]. Its two halves are two
types:
- [pcell_ty m : type (pcellₛ m)], the cell itself. Its value is the id [g] of the cell, a key
  of the registry of the cells ([gcell_reg g γ m]). The cell is owned by its parent: the
  bytes of a cell at [l] are the contents [gcont l m (FVCell g)], i.e. the move right
  [gmb_a γ l] of the instance ([bytes_own_pcell_ty]). The ownership predicate of the value
  is persistent ([gcell_pers]: the registry entry, the instance invariant, and the bytes
  mask [lazyB]). A [pcell_ty m] has no MiniRust value, so it lives only in memory; it is
  moved by the generic move rules, which move the contents of the cell with it.
- [cell_points_to_ty ty : type (trackedₛ (pcellₛ (syn_mty 𝔄) * 𝔄))], the permission
  ([PointsTo<T>] of Verus): a ghost value [(g, x)] whose ownership is the permission
  [gmb_b γ fv] of the instance at the fancy value [fv] of [x] ([cell_own]), together with
  the ownership of [x]. Its sharing predicate is a guard of the permission (at step-index
  [g]) and the sharing predicate of [x].

A shared reference to the cell guards its move right (through the guard of its bytes), and a
shared reference to the permission guards the permission: (L2) gives a guard of the contents,
which is a shared reference to the contents ([type_pcell_borrow_instr],
[typing/pcell_borrow.v]). A unique borrow of the permission and a shared reference to the
cell give a unique borrow of the contents, by the prophetic lend (L3p) of [gmb_lend_uniq]
([type_pcell_borrow_mut_instr]). *)

Implicit Type 𝔄 𝔅: syn_type.

Section pcell.
  Context `{!typeG Σ}.

  (** The persistent facts of the cell [g] (of contents of MiniRust type [m]): its registry
      entry, its instance invariant, and its bytes mask. *)
  Definition gcell_pers (g: positive) (γ: gmb_name) (m: mty) : iProp Σ :=
    gcell_reg g γ m ∗ gmb_inv (gcont_c m) γ ∗ ⌜gmb_bmask γ = lazyB⌝.

  Global Instance gcell_pers_persistent g γ m : Persistent (gcell_pers g γ m).
  Proof. apply _. Qed.

  Lemma gcell_pers_agree g γ γ' m m' :
    gcell_pers g γ m -∗ gcell_pers g γ' m' -∗ ⌜γ = γ' ∧ m = m'⌝.
  Proof. iIntros "[H1 _] [H2 _]". iApply (gcell_reg_agree with "H1 H2"). Qed.

  Program Definition pcell_ty (m: mty) : type (pcellₛ m) :=
    @ty_of_st _ _ (pcellₛ m) ({|
      st_lfts := []; st_E := [];
      st_gho g _ _ _ := ∃ γ, gcell_pers g γ (syn_mty (pcellₛ m));
    |}%I : simple_type (pcellₛ m)).
  Solve Obligations with
    (try (move=> *; apply _)); (try (move=> *; by iIntros "$")); (try (move=> * ? Hin; by apply elem_of_nil in Hin)).
  Next Obligation. move=> ????????? H. simpl in H. by apply elem_of_nil in H. Qed.

  Global Instance pcell_res_own m : ResOwn (pcell_ty m).
  Proof. done. Qed.

  Global Instance pcell_send m : Send (pcell_ty m).
  Proof.
    split. iIntros (tid tid' x d g G H κs d0 Hineq TG TH) "LFT UNIQ TIME Hg H Gg G #Own #⧖o".
    iApply step_fupdN_intro; first done. iNext.
    iExists x, 0%nat. iModIntro. iFrame "G H". simpl.
    replace (d0 + 0)%nat with d0 by lia. replace (d + 0)%nat with d by lia. by iFrame "#".
  Qed.

  Global Instance pcell_sync m : Sync (pcell_ty m).
  Proof. apply sync_default; [done|]. split; done. Qed.

  Lemma pcell_ty_mty m : mty_wf m → (pcell_ty m).(ty_mty) = m.
  Proof. intros. by rewrite -ty_mty_eq /= decide_True. Qed.

  Lemma pcell_ty_bsize m : mty_wf m → ty_bsize (pcell_ty m) = mty_size m.
  Proof. intros. by rewrite /ty_bsize pcell_ty_mty. Qed.

  Lemma pcell_ty_own m g d d' tid :
    mty_wf m → (pcell_ty m).(ty_gho_own) g d d' tid ⊣⊢ ∃ γ, gcell_pers g γ m.
  Proof. intros. by rewrite /= decide_True. Qed.

  Lemma pcell_ty_pers m g d d' tid :
    mty_wf m → (pcell_ty m).(ty_gho_pers) g d d' tid ⊣⊢ ∃ γ, gcell_pers g γ m.
  Proof. intros. by rewrite /= decide_True. Qed.

  (** The bytes of a cell are its contents at [FVCell g]: the move right of the instance. *)
  Lemma bytes_own_pcell_ty m l g :
    mty_wf m → bytes_own (pcell_ty m) l g ⊣⊢ gcont l m (FVCell g).
  Proof. intros. rewrite (bytes_own_gcont _ _ _ (FVCell g)) // pcell_ty_mty //. Qed.

  Lemma bytes_own_pcell_gca m l g γ :
    mty_wf m → gcell_pers g γ m -∗ bytes_own (pcell_ty m) l g ∗-∗ gmb_a γ l.
  Proof.
    iIntros (Hm) "#[Hreg _]". rewrite bytes_own_pcell_ty //. iSplit.
    - iIntros "C". iDestruct (gcont_cell_inv with "C") as (γ') "[Hreg' Ha]".
      by iDestruct (gcell_reg_agree with "Hreg Hreg'") as %[<- _].
    - iIntros "Ha". iApply (gcont_cell with "Hreg Ha").
  Qed.

  (** A guard of the bytes of a cell is a guard of its move right. *)
  Lemma guard_pcell_gca G n m l g γ :
    mty_wf m →
    gcell_pers g γ m -∗ (G &&{↑NllftG; n}&&> bytes_own (pcell_ty m) l g) -∗
    (G &&{↑NllftG; n}&&> gmb_a γ l).
  Proof.
    iIntros (Hm) "#Hp #G1". iDestruct (guards_include_pers with "Hp G1") as "G1p".
    iApply (guards_weaken_rhs_point with "G1p"); [apply gmb_a_point|].
    iIntros "[Bytes #Hp']". by iApply (bytes_own_pcell_gca with "Hp' Bytes").
  Qed.
End pcell.

Section cell_points_to.
  Context `{!typeG Σ}.

  (** The permission of the cell [g] whose contents are the value [x] of [ty]: the
      permission [gmb_b] of its instance at the fancy value of [x]. *)
  Definition cell_own {𝔄} (ty: type 𝔄) (g: positive) (x: ~~𝔄) : iProp Σ :=
    ∃ γ fv, ⌜ty.(ty_fval) x = Some fv⌝ ∗ gcell_pers g γ ty.(ty_mty) ∗ gmb_b γ fv.

  (** Its persistent part. *)
  Definition cell_pers {𝔄} (ty: type 𝔄) (g: positive) (x: ~~𝔄) : iProp Σ :=
    ∃ γ fv, ⌜ty.(ty_fval) x = Some fv⌝ ∗ gcell_pers g γ ty.(ty_mty).

  (** Its sharing predicate: a guard of the permission. *)
  Definition cell_shr {𝔄} (ty: type 𝔄) (κ: lft) (g: positive) (x: ~~𝔄) (n: nat) : iProp Σ :=
    ∃ γ fv, ⌜ty.(ty_fval) x = Some fv⌝ ∗ gcell_pers g γ ty.(ty_mty) ∗
      (@[κ] &&{↑NllftG; n}&&> gmb_b γ fv).

  Global Instance cell_pers_persistent {𝔄} (ty: type 𝔄) g x : Persistent (cell_pers ty g x).
  Proof. apply _. Qed.
  Global Instance cell_shr_persistent {𝔄} (ty: type 𝔄) κ g x n : Persistent (cell_shr ty κ g x n).
  Proof. apply _. Qed.

  Lemma cell_own_pers {𝔄} (ty: type 𝔄) g x : cell_own ty g x -∗ cell_pers ty g x.
  Proof. iIntros "(%γ & %fv & % & #P & _)". iExists γ, fv. by iFrame "P". Qed.

  Lemma cell_own_same {𝔄} (ty ty': type 𝔄) g x : cell_own ty g x ⊣⊢ cell_own ty' g x.
  Proof. by rewrite /cell_own (ty_mty_same ty ty') (ty_fval_same ty ty'). Qed.

  (** With the persistent part, the permission is the permission of the instance. *)
  Lemma cell_own_gmb_b {𝔄} (ty: type 𝔄) g x γ fv :
    ty.(ty_fval) x = Some fv →
    gcell_pers g γ ty.(ty_mty) -∗ □ (cell_own ty g x ↔ gmb_b γ fv).
  Proof.
    iIntros (Hfv) "#Hp !>". iSplit.
    - iIntros "(%γ' & %fv' & %Hfv' & #Hp' & B)". rewrite Hfv in Hfv'. injection Hfv' as <-.
      by iDestruct (gcell_pers_agree with "Hp Hp'") as %[<- _].
    - iIntros "B". iExists γ, fv. by iFrame "Hp B".
  Qed.

  Lemma cell_shr_lft_mono {𝔄} (ty: type 𝔄) κ κ' g x n n' :
    (@[κ'] &&{↑NllftG; n'}&&> @[κ]) -∗ cell_shr ty κ g x n -∗ cell_shr ty κ' g x (n + n').
  Proof.
    iIntros "#Incl (%γ & %fv & % & #Hp & #G)". iExists γ, fv. iFrame "Hp". iSplit; [done|].
    rewrite Nat.add_comm. iApply (guards_transitive_additive with "Incl G").
  Qed.

  Lemma cell_shr_mono {𝔄} (ty: type 𝔄) κ g x n n' :
    n ≤ n' → cell_shr ty κ g x n -∗ cell_shr ty κ g x n'.
  Proof.
    iIntros (?) "(%γ & %fv & % & #Hp & #G)". iExists γ, fv. iFrame "Hp". iSplit; [done|].
    by iApply (lguards_weaken_later with "G").
  Qed.

  (** Sharing the permission: a borrow of it is a guard of the permission of the instance
      (at step-index [0], since it is timeless), without a step. *)
  Lemma cell_own_share {𝔄} (ty: type 𝔄) E κ g x :
    ↑Nllft ⊆ E →
    llft_ctx -∗ cell_pers ty g x -∗ &{κ} (cell_own ty g x) ={E}=∗ cell_shr ty κ g x 0.
  Proof.
    iIntros (?) "#LFT (%γ & %fv & %Hfv & #Hp) Bor".
    iDestruct (cell_own_gmb_b with "Hp") as "#Iff"; [done|].
    iDestruct (llftl_bor_iff _ _ (gmb_b γ fv) with "[] Bor") as "Bor".
    { iIntros "!> !>". iApply "Iff". }
    iMod (llftl_bor_guard_later with "LFT Bor") as "#G"; [done|].
    iModIntro. iExists γ, fv. iFrame "Hp". iSplit; [done|].
    by iApply guards_remove_later_rhs.
  Qed.

  Program Definition cell_points_to_ty {𝔄} (ty: type 𝔄) :
      type (trackedₛ (pcellₛ (syn_mty 𝔄) * 𝔄)) :=
    {| ty_lfts := ty.(ty_lfts);
      ty_E := ty.(ty_E);
      ty_gho_own x d g tid := cell_own ty x.1 x.2 ∗ ty.(ty_gho_own) x.2 d g tid;
      ty_gho_res x d g tid := cell_own ty x.1 x.2 ∗ ty.(ty_gho_res) x.2 d g tid;
      ty_gho_pers x d g tid := cell_pers ty x.1 x.2 ∗ ty.(ty_gho_pers) x.2 d g tid;
      ty_mty := syn_mty _; ty_val := syn_val; ty_mty_eq := eq_refl; ty_val_eq _ := eq_refl;
      ty_fval := syn_fval; ty_fval_eq _ := eq_refl;
      ty_shr κ x d g tid := cell_shr ty κ x.1 x.2 g ∗ ty.(ty_shr) κ x.2 d g tid;
    |}%I.
  Next Obligation.
    move => 𝔄 ty d g d' g' x tid ??/=. iIntros "[$ Hgho]".
    iDestruct (ty.(ty_gho_own_depth_mono) with "Hgho") as "[$ Hwand]"; [done..|].
    iIntros "[$ Hgho]". by iApply "Hwand".
  Qed.
  Next Obligation.
    move => 𝔄 ty d g d' g' x tid ??/=. iIntros "[$ H]".
    by iApply (ty.(ty_gho_pers_depth_mono) with "H").
  Qed.
  Next Obligation.
    intros 𝔄 ty x d g tid. iIntros "[A1 A2]". iSplitL "A1"; [by iApply cell_own_pers|].
    by iApply ty_gho_pers_impl.
  Qed.
  Next Obligation.
    intros 𝔄 ty κ κ' x n d g tid. iIntros "#Incl [Pt Shr]". iSplit.
    - by iApply (cell_shr_lft_mono with "Incl Pt").
    - iApply (ty_shr_lft_mono with "Incl Shr").
  Qed.
  Next Obligation.
    intros 𝔄 ty κ d g d' g' x tid ??. iIntros "[Pt Shr]". iSplit.
    - by iApply (cell_shr_mono with "Pt").
    - by iApply (ty_shr_depth_mono with "Shr").
  Qed.
  Next Obligation.
    intros 𝔄 ty E κ x d g tid G ??. iIntros "#LFT #Incl [#Pers #Pers'] #Gκ G Bor". simpl.
    iMod (llftl_sep_split with "LFT Bor") as "[Pt Bor]"; [solve_ndisj|].
    iMod (cell_own_share with "LFT Pers Pt") as "#Pt"; [solve_ndisj|].
    iMod (ty_share with "LFT Incl Pers' Gκ G Bor") as "Shr"; [done..|].
    iModIntro. iApply (step_fupdN_wand with "Shr"). iIntros ">[$ $] !>".
    iApply (cell_shr_mono with "Pt"); lia.
  Qed.
  Next Obligation.
    intros 𝔄 ty κ x n0 d g tid ξ R Hin.
    iIntros "#LFT #Incl [_ #Pers] [_ #Shr]".
    by iApply (ty_shr_guard_proph ty κ x.2 n0 d g tid ξ R Hin with "LFT Incl Pers Shr").
  Qed.
  Next Obligation.
    intros 𝔄 ty x d g tid. iIntros "[$ A]". by iApply ty_gho_res_of_own.
  Qed.

  Global Instance cell_points_to_res_own {𝔄} (ty: type 𝔄) :
    ResOwn ty → ResOwn (cell_points_to_ty ty).
  Proof. move=> ? x d g tid /=. by rewrite res_own. Qed.

  Global Instance cell_points_to_send {𝔄} (ty: type 𝔄) :
      Send ty → Send (cell_points_to_ty ty).
  Proof.
    intros [Hgho]. split.
    intros tid tid' x d g G H κs d0 Hineq TG TH.
    iIntros "LFT UNIQ TIME Hg H Gg G [Hown Hgho] #⧖o".
    iPoseProof (Hgho with "LFT UNIQ TIME Hg H Gg G Hgho ⧖o") as "X"; first lia.
    iApply (step_fupdN_wand with "X"). iIntros ">X".
    iDestruct "X" as (x' off) "[gho [#⧖off [%Habs [G H]]]]".
    iExists (x.1, x'), (off). iModIntro. iFrame. iFrame "#".
    iSplitL "Hown".
    - rewrite /cell_own. by rewrite -!ty_fval_eq (syn_abstract_fval_eq _ _ _ Habs).
    - iPureIntro. simpl. by rewrite Habs.
  Qed.

  Global Instance cell_points_to_sync {𝔄} (ty: type 𝔄) :
      Sync ty → Sync (cell_points_to_ty ty).
  Proof.
    move=> HSync tid tid' x d g.
    destruct (HSync tid tid' x.2 d g) as [Hgho [Hpers Hshr]].
    split; [by rewrite /= Hgho|]. split; [by rewrite /= Hpers|].
    move=> κ /=. by rewrite Hshr.
  Qed.

  (** The permission is a ghost value: its MiniRust value is the empty tuple. *)
  Lemma cell_points_to_val {𝔄} (ty: type 𝔄) x :
    (cell_points_to_ty ty).(ty_val) x = Some (VTuple []).
  Proof. done. Qed.

  Lemma cell_points_to_bsize {𝔄} (ty: type 𝔄) : ty_bsize (cell_points_to_ty ty) = 0.
  Proof. by rewrite /ty_bsize -ty_mty_eq. Qed.

  Lemma cell_points_to_fval {𝔄} (ty: type 𝔄) x :
    (cell_points_to_ty ty).(ty_fval) x = Some (fv_lift (VTuple [])).
  Proof. done. Qed.

  Lemma cell_points_to_bytes_own {𝔄} (ty: type 𝔄) l x :
    ⊢ bytes_own (cell_points_to_ty ty) l x.
  Proof. iApply bytes_own_zst_emp; [apply cell_points_to_bsize|done]. Qed.

  Lemma cell_points_to_cbytes {𝔄} (ty: type 𝔄) l x :
    cbytes (cell_points_to_ty ty) x l ⊣⊢ True.
  Proof. rewrite /cbytes bytes_own_zst_true //. Qed.
End cell_points_to.

(** * Creating and destroying a [PCell]

A [PCell] (or any value that contains cells) is moved by the generic move rules: a typed
[Load] out of a place ([type_move_place_instr]) moves its cells out with the loaded value
([val_cells]), and a typed [Store] of the loaded value ([type_write_place_instr]) puts them
back at the new location; a [MemCopy] into a place ([type_memcpy_move_place_instr]) moves
them verbatim. *)
Section pcell_rules.
  Context `{!typeG Σ}.

  (** [PCell::new]: the contents of a box become a cell (a new instance of the GMB library,
      registered, [gcell_create]). The box now holds the cell, and the permission is
      returned (a ghost value). *)
  Definition PCellNew : val := (λ: ["p"], MkTuple [])%V.

  Lemma type_pcell_new_instr {𝔄} n (ty: type 𝔄) p E L I :
    typed_instr E L I +[p ◁ᵥ own_bytes n ty] (PCellNew [p])
      (λ v, +[p ◁ᵥ own_bytes n (pcell_ty ty.(ty_mty)); v ◁ᵥ cell_points_to_ty ty])
      (λ post '-[(l, x)], λ mask π, ∀ g, post -[(l, g); (g, x)] mask π).
  Proof.
    iIntros (tid post mask iκs [[l x] []]) "_ #TIME _ _ _ $ I [p _] Obs".
    iDestruct (invctx_interp_gcells with "I") as "[#GC $]".
    iDestruct (tctx_val_elim with "p") as (vp Hp w d [-> Hw]) "[#⧖ Own]". simpl in Hw. simplify_eq.
    have Hm := ty_mty_wf ty.
    rewrite /PCellNew. wp_bind p.
    iApply (wp_wand with "[]"); [by iApply wp_eval_path|]. iIntros (? ->).
    destruct d as [|d]; [done|]. iDestruct "Own" as "(Bytes & Free & Gho)".
    iDestruct (bytes_own_fval with "Bytes") as %[fv Hfv].
    rewrite (bytes_own_gcont _ _ _ fv) //.
    iMod (gcell_create with "GC Bytes") as (g γ) "(%Hbm & #Hreg & #GI & B & C)"; [solve_ndisj|].
    iApply (wp_persistent_time_receipt with "TIME ⧖"); [done|]. iIntros "£ _".
    iMod (lc_fupd_elim_later with "[£] Gho") as "Gho".
    { iApply (lc_weaken with "£"). rewrite /advance_credits. lia. }
    wp_rec.
    eapply (tac_wp_pure []); [apply (pure_mk_tuple [])|done|tc_solve|simpl; iApply wp_value].
    iExists -[(l, g); (g, x)]. iSplitR "Obs"; last first.
    { iApply (proph_obs_impl with "Obs"). intros π Hpost. apply Hpost. }
    iSplitL "Free C"; [|iSplitL; [|done]].
    - iExists _. iSplit; [done|]. rewrite -(val_own_intro_sep _ _ _ _ (VPtr l) (S d)); [|done|done].
      iFrame "⧖". iSplitL "C"; [|iSplitL].
      + by rewrite bytes_own_pcell_ty.
      + by rewrite pcell_ty_bsize.
      + iNext. rewrite pcell_ty_own //. iExists γ. by iFrame "Hreg GI".
    - rewrite tctx_val_val. iExists (S d). iSplit; [done|]. iFrame "⧖".
      iSplitL "B"; [iExists γ, fv; by iFrame "Hreg GI B"|].
      iDestruct (ty_gho_own_depth_mono _ d (S d) (S d) (S d) with "Gho") as "[$ _]"; lia.
  Qed.

  (** The form of [PCell::new] where the box holds the cell and the (zero-sized)
      permission, as a pair. *)
  Definition PCellFromOwn : val := (λ: ["p"], "p")%V.

  Lemma pcell_pair_bsize {𝔄} (ty: type 𝔄) :
    ty_bsize (pcell_ty ty.(ty_mty) * cell_points_to_ty ty)%T = ty_bsize ty.
  Proof.
    rewrite /ty_bsize -ty_mty_eq /= decide_True; [|apply ty_mty_wf].
    rewrite /seq_size /=. lia.
  Qed.

  Lemma type_pcell_from_own_instr {𝔄} n (ty: type 𝔄) p E L I :
    typed_instr E L I +[p ◁ᵥ own_bytes n ty] (PCellFromOwn [p])
      (λ v, +[v ◁ᵥ own_bytes n (pcell_ty ty.(ty_mty) * cell_points_to_ty ty)%T])
      (λ post '-[(l, x)], λ mask π, ∀ g, post -[(l, (g, (g, x)))] mask π).
  Proof.
    iIntros (tid post mask iκs [[l x] []]) "_ #TIME _ _ _ $ I [p _] Obs".
    iDestruct (invctx_interp_gcells with "I") as "[#GC $]".
    iDestruct (tctx_val_elim with "p") as (vp Hp w d [-> Hw]) "[#⧖ Own]". simpl in Hw. simplify_eq.
    have Hm := ty_mty_wf ty.
    rewrite /PCellFromOwn. wp_bind p.
    iApply (wp_wand with "[]"); [by iApply wp_eval_path|]. iIntros (? ->).
    destruct d as [|d]; [done|]. iDestruct "Own" as "(Bytes & Free & Gho)".
    iDestruct (bytes_own_fval with "Bytes") as %[fv Hfv].
    rewrite (bytes_own_gcont _ _ _ fv) //.
    iMod (gcell_create with "GC Bytes") as (g γ) "(%Hbm & #Hreg & #GI & B & C)"; [solve_ndisj|].
    wp_rec.
    iExists -[(l, (g, (g, x)))]. iSplitR "Obs"; last first.
    { iApply (proph_obs_impl with "Obs"). intros π Hpost. apply Hpost. }
    iSplit; [|done]. rewrite tctx_val_val. iExists (S d). iSplit; [done|]. iFrame "⧖".
    iSplitL "C"; [|iSplitL "Free"].
    - rewrite (bytes_own_pair _ (pcell_ty ty.(ty_mty)) (cell_points_to_ty ty)).
      iSplitL; [by rewrite bytes_own_pcell_ty|iApply cell_points_to_bytes_own].
    - by rewrite pcell_pair_bsize.
    - iNext. iSplitR; [rewrite pcell_ty_own //; iExists γ; by iFrame "Hreg GI"|].
      iSplitL "B"; [iExists γ, fv; by iFrame "Hreg GI B"|]. done.
  Qed.

  (** [PCell::into_inner]: a box holding a cell and the permission of the cell give back a
      box holding the contents (the instance is destroyed, [gcell_destroy]). *)
  Definition PCellIntoInner : val := (λ: ["pcell"; "perm"], "pcell")%V.

  Lemma type_pcell_into_inner_instr {𝔄} n (ty: type 𝔄) p q E L I :
    typed_instr E L I +[p ◁ᵥ own_bytes n (pcell_ty ty.(ty_mty)); q ◁ᵥ cell_points_to_ty ty]
      (PCellIntoInner [p; q]) (λ v, +[v ◁ᵥ own_bytes n ty])
      (λ post '-[(l, g); (g', x)], λ mask π, g = g' ∧ post -[(l, x)] mask π).
  Proof.
    iIntros (tid post mask iκs [[l g] [[g' x] []]]) "_ #TIME #PROPH _ _ $ $ (p & q & _) #Obs".
    iMod (proph_obs_sat with "PROPH Obs") as "(% & <- & _)"; [done|].
    iDestruct (tctx_val_elim with "p") as (vp Hp wp dp [-> Hwp]) "[#⧖p Own]". simpl in Hwp. simplify_eq.
    iDestruct (tctx_val_elim with "q") as (vq Hq wq dq [-> Hwq]) "[#⧖q [Pt Gho]]".
    have Hm := ty_mty_wf ty.
    rewrite /PCellIntoInner.
    wp_bind p. iApply (wp_wand with "[]"); [by iApply wp_eval_path|]. iIntros (? ->).
    wp_bind q. iApply (wp_wand with "[]"); [by iApply wp_eval_path|]. iIntros (? ->).
    destruct dp as [|dp]; [done|].
    iDestruct "Own" as "(Bytes & Free & _)".
    iDestruct "Pt" as (γ fv Hfv) "[#(Hreg & GI & _) B]".
    rewrite bytes_own_pcell_ty //.
    iMod (gcell_destroy with "Hreg GI Bytes B") as "C"; [solve_ndisj|].
    iApply (wp_persistent_time_receipt with "TIME ⧖q"); [done|]. iIntros "_ #⧖S".
    wp_rec. iExists -[(l, x)]. iSplitR "Obs"; last first.
    { iApply (proph_obs_impl with "Obs"). by intros π [_ ?]. }
    iSplit; [|done]. rewrite tctx_val_val. iExists (S dq). iSplit; [done|]. iFrame "⧖S".
    iSplitL "C"; [by rewrite (bytes_own_gcont _ _ _ fv)|]. iSplitL "Free".
    - iEval (rewrite pcell_ty_mty //) in "Free". by rewrite /ty_bsize.
    - iNext. iDestruct (ty_gho_own_depth_mono _ dq dq dq (S dq) with "Gho") as "[$ _]"; lia.
  Qed.
End pcell_rules.

(** * Lends of the contents of a cell

The prophetic lend (L3p) of [gmb_lend_uniq] ([typing/gmb_uniq.v]) for cells: a guard of the
bytes of a cell at [l] (that is, of its move right) and the body of a unique borrow at [κ] of
its permission give the body of a fresh unique borrow at [κ] of the contents of the cell, at
[l]; the prophecy variable of the permission is resolved to [(g, _)] of the prophecy variable
of the contents. *)
Section pcell_lend.
  Context `{!typeG Σ}.

  Lemma pcell_lend_uniq {𝔄} (ty: type 𝔄) κ l g γ n l' x ξi d gi idx tid E G :
    Timeless G → lazyE ⊆ E →
    llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ gcell_pers g γ ty.(ty_mty) -∗
    (@[κ] &&{↑NllftG; n}&&> bytes_own (pcell_ty ty.(ty_mty)) l g) -∗
    κ ⊑ ty_lft ty -∗ (G &&{↑NllftG}&&> @[κ]) -∗ G -∗ £ (5 + n + (1 + n)) -∗
    uniq_body (cell_points_to_ty ty) (g, x) ξi d gi idx κ tid l' ={E}=∗ ∃ ζi ζidx,
      ⟨π, (π (uniq_prvar (𝔄:=trackedₛ (pcellₛ (syn_mty 𝔄) * 𝔄)) (g, x) ξi)).1 = (g, (π (uniq_prvar x ζi)).1)⟩ ∗
      uniq_body ty x ζi d gi ζidx κ tid l ∗ G.
  Proof.
    iIntros (HG HE) "#LFT #PROPH #UNIQ #Hp #Gb #In #Gk G [[£5 £n] £1n] Body".
    have Hm := ty_mty_wf ty.
    iDestruct (guard_pcell_gca with "Hp Gb") as "#Ga"; [done|].
    iDestruct "Hp" as "(#Hreg & #GI & %Hbm)".
    iMod (gmb_lend_uniq (gcont_c ty.(ty_mty)) (cell_points_to_ty ty) ty (λ y, (g, y)) (λ y, (g, y))
      (fv_lift (VTuple [])) γ l l' x ξi d gi idx κ tid E G n
      with "LFT PROPH UNIQ GI [] [] Ga In [] Gk G £5 £n £1n Body") as (ζi ζidx) "(Obs & Body & G)".
    { done. }
    { done. }
    { done. }
    { intros y fv0 Hy. by rewrite /cbytes /gcont_c (bytes_own_gcont _ _ _ fv0). }
    { intros fv0. iIntros "(%y & %Hy & B)". by rewrite /cbytes /gcont_c (bytes_own_gcont _ _ _ fv0). }
    { done. }
    { intros. apply cell_points_to_cbytes. }
    { iIntros "!>" (y' d' g') "[Pt Gho]". iDestruct "Pt" as (γ' fv0 Hfv0) "[Hp' B]".
      iDestruct (gcell_pers_agree with "[$Hreg $GI //] Hp'") as %[<- _].
      iModIntro. iExists fv0. by iFrame. }
    { iIntros "!>" (y' d' g' fv0 Hfv0) "[B Gho]". iFrame "Gho". iExists γ, fv0.
      by iFrame "Hreg GI B". }
    { iApply lft_incl_refl. }
    iModIntro. iExists ζi, ζidx. by iFrame.
  Qed.

  (** Opening a unique borrow: the borrow is opened with [G1], its payload run with [G2],
      and it can be closed with new contents [y]. *)
  Lemma uniq_body_open {𝔄} κ (ty: type 𝔄) l x ξi d g idx tid G1 G2 :
    Timeless G1 → Timeless G2 →
    llft_ctx -∗ uniq_ctx -∗ (G1 &&{↑NllftG}&&> @[κ]) -∗ (G2 &&{↑NllftG}&&> @[κ]) -∗
    κ ⊑ ty_lft ty -∗ uniq_body ty x ξi d g idx κ tid l -∗ G1 -∗ G2 -∗ £1 -∗
    |={⊤ ∖ ↑advN}=> G2 ∗ ⧗1 ∗ ⧖(S d `max` g) ∗ ty.(ty_gho_own) x d g tid ∗ cbytes ty x l ∗
      (∀ y d1 g1, ▷ (⧖(S d1 `max` g1) ∗ ty.(ty_gho_own) y d1 g1 tid ∗ cbytes ty y l) -∗ ⧗1
        ={↑Nllft}=∗ uniq_body ty y ξi d1 g1 idx κ tid l ∗ G1).
  Proof.
    iIntros (??) "#LFT #UNIQ #Gκ1 #Gκ2 #Incl Body G1 G2 £".
    iMod (uniq_body_acc with "LFT UNIQ Gκ1 Body G1") as "(Pay & ⧗ & Close)"; [solve_ndisj|].
    iMod (uniq_payload_force with "[] G2 £ Pay") as "(G2 & ⧖ & Gho & Bytes)"; [solve_lazyE| |].
    { iApply (guards_transitive with "Gκ2 Incl"). }
    iModIntro. iFrame.
  Qed.
End pcell_lend.

(** * Atomic accesses through a cell

At the MiniRust type of the contents (no mixed-size accesses), for contents without cells
([NoCell]; for a load it follows from [Copy]: a copy would duplicate the cells; for a store
and a compare-and-exchange, the GMB-level writes [wp_gcont_store_sc_sub] and
[wp_gcont_mcas_sub] replace a plain value by a plain value, since the old cells would have
to be forgotten, and the new ones put in place, through the registry within the atomic
step). A load needs shared references to the cell
and to its permission ((L2)); a store and a compare-and-exchange need a unique borrow of the
permission: the contents are lent ([pcell_lend_uniq]), accessed through the unique borrow of
the contents, which is resolved. *)
Section pcell_atomics.
  Context `{!typeG Σ}.

  Lemma naN_NllftG : naN = NllftG.
  Proof. done. Qed.

  Lemma type_pcell_load_sc_instr {𝔄} κ (ty: type 𝔄) p q E L I :
    Copy ty → lctx_lft_alive E L κ →
    typed_instr E L I
      +[p ◁ᵥ &shr{κ} (pcell_ty ty.(ty_mty)); q ◁ᵥ &shr{κ} (cell_points_to_ty ty)]
      (Load ScOrd ty.(ty_mty) p)
      (λ v, +[v ◁ᵥ ty]) (λ post '-[(_, g); (_, (g', x))], λ mask π, g = g' ∧ post -[x] mask π).
  Proof.
    intros Hcopy0. assert (NoCell 𝔄) by exact (copy_nocell ty). revert Hcopy0.
    iIntros (? Alv tid post mask iκs [[l g] [[l' [g' x]] []]])
      "#LFT #TIME #PROPH _ #E L $ (p & q & _) #Obs".
    iMod (proph_obs_sat with "PROPH Obs") as "(% & <- & _)"; [done|].
    iDestruct (tctx_val_elim with "q") as (vq Hq wq dq [-> Hwq]) "[#⧖q #Own']".
    wp_bind p. iApply (wp_val with "p"). iIntros (w d Hp Hw) "#⧖ #Own".
    simpl in Hw. simplify_eq. cbn [of_val].
    destruct d as [|d0]; [done|]. destruct dq as [|dq0]; [done|].
    have Hm := ty_mty_wf ty.
    iDestruct "Own" as "(#Gp & _ & _)". iDestruct "Own'" as "(_ & [#Pt #TyShr] & _)".
    iDestruct "Pt" as (γ fv Hfv) "[#Hp #Gb]".
    iMod (llctx_interp_make_guarded with "L") as (γh) "[H1 [H2 [#Gh #Back]]]"; [solve_ndisj|].
    iAssert (|={⊤}=> fractional.half γh ∗ (fractional.half γh &&{↑NllftG}&&> @[κ]))%I
      with "[H1]" as ">[H1 #Gκ]".
    { leaf_open "Gh" with "H1" as "[InterpL back]". { solve_ndisj. }
      iDestruct (Alv with "InterpL E") as "#Alv".
      iMod ("back" with "InterpL") as "$". iModIntro.
      iApply (guards_transitive with "Gh Alv"). }
    set D := S d0 `max` S dq0.
    iAssert (⧖D)%I as "#⧖D"; [rewrite persistent_time_receipt_sep; by iFrame "⧖ ⧖q"|].
    iApply (wp_persistent_time_receipt with "TIME ⧖D"); [done|]. iIntros "£ #⧖S".
    iDestruct (lc_weaken ((S dq0 + 1) + (D + 1)) with "£") as "[£1 £2]";
      [rewrite /advance_credits; lia|].
    iDestruct (copy_shr with "TyShr") as "#GOwn".
    iDestruct (guards_transitive_right with "Gκ GOwn") as "GO".
    iAssert (|={⊤ ∖ ↑advN}=> fractional.half γh ∗ ty.(ty_gho_own) x dq0 (S dq0) tid)%I
      with "[H1 £1]" as ">[H1 #Gho]".
    { iMod (guards_open_later with "GO H1") as "Open"; [solve_ndisj|].
      iMod (lc_fupd_elim_laterN with "£1 Open") as ">[#Gho Close]".
      iMod ("Close" with "Gho") as "$". by iModIntro. }
    iDestruct (guards_transitive_right with "Gκ Gp") as "G1".
    iDestruct (guard_pcell_gca with "Hp G1") as "Ga"; [done|].
    iDestruct (guards_transitive_right with "Gκ Gb") as "Gb'".
    iDestruct (lguards_weaken_later _ _ _ _ (D + 1) with "Ga") as "GaD"; [lia|].
    iDestruct (lguards_weaken_later _ _ _ _ (D + 1) with "Gb'") as "GbD"; [lia|].
    rewrite ty_fval_nocell // in Hfv. apply fmap_Some in Hfv as (v & Hv & ->).
    iDestruct "Hp" as "(_ & #GI & _)".
    have -> : (MLit $ VPtr l) = (MLit $ VPtr (l +ₗ 0%nat)) by rewrite shift_loc_0_nat.
    iApply wp_fupd.
    iApply (wp_gcell_load_sc_shared _ γ l ty.(ty_mty) (fv_lift v) 0 ty.(ty_mty) v
      (fractional.half γh) (D + 1) with "[H1 £2]"); [solve_ndisj|done|apply fv_sub_here|..].
    { rewrite naN_NllftG. iFrame "GI GaD GbD H1 £2". }
    iIntros "!> H1".
    iMod (fupd_mask_mono with "(Back H1 H2)") as "$"; [solve_ndisj|].
    iModIntro. iExists -[x]. iSplitR "Obs"; last first.
    { iApply (proph_obs_impl with "Obs"). by intros π [_ ?]. }
    iSplit; [|done]. rewrite tctx_val_val. iExists D. iSplit; [done|]. iFrame "⧖D".
    iDestruct (ty_gho_own_depth_mono _ dq0 (S dq0) D D with "Gho") as "[$ _]"; lia.
  Qed.

  (** The common part of a store and a compare-and-exchange: the lend of the contents, and
      the opening of the unique borrow of the contents. *)
  Lemma pcell_lend_open {𝔄} κ (ty: type 𝔄) l g d0 l' x ξi di gi ξidx dq dq' tid G1 G2 :
    Timeless G1 → Timeless G2 →
    llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗
    (&shr{κ} (pcell_ty ty.(ty_mty))).(ty_gho_own) (l, g) (S d0) (S d0) tid -∗
    (&uniq{κ} (cell_points_to_ty ty)).(ty_gho_own) (l', (g, x), ξi, di, gi, ξidx) dq dq' tid -∗
    (G1 &&{↑NllftG}&&> @[κ]) -∗ (G2 &&{↑NllftG}&&> @[κ]) -∗ G1 -∗ G2 -∗
    £ ((S d0 + 1) + (5 + (S d0 + 1) + (1 + (S d0 + 1))) + 1) -∗
    |={⊤ ∖ ↑advN}=> ∃ ζi ζidx,
      ⟨π, (π (uniq_prvar (𝔄:=trackedₛ (pcellₛ (syn_mty 𝔄) * 𝔄)) (g, x) ξi)).1 = (g, (π (uniq_prvar x ζi)).1)⟩ ∗
      (κ ⊑ ty_lft ty) ∗ G2 ∗ ⧗1 ∗ ⧖(S di `max` gi) ∗ ty.(ty_gho_own) x di gi tid ∗ cbytes ty x l ∗
      (∀ y d1 g1, ▷ (⧖(S d1 `max` g1) ∗ ty.(ty_gho_own) y d1 g1 tid ∗ cbytes ty y l) -∗ ⧗1
        ={↑Nllft}=∗ uniq_body ty y ζi d1 g1 ζidx κ tid l ∗ G1).
  Proof.
    iIntros (??) "#LFT #PROPH #UNIQ #Own Uniq #Gκ1 #Gκ2 G1 G2 [[£p £l] £o]".
    have Hm := ty_mty_wf ty.
    iDestruct "Own" as "(#Gp & _ & #Pers)".
    iDestruct "Uniq" as "(#Incl & _ & Body)".
    iMod (lc_fupd_elim_laterN with "£p Pers") as "Pers'".
    iEval (rewrite pcell_ty_pers //) in "Pers'". iDestruct "Pers'" as (γ) "#Hp".
    iMod (pcell_lend_uniq ty κ l g γ (S d0 + 1) l' x ξi di gi ξidx tid with
      "LFT PROPH UNIQ Hp Gp Incl Gκ1 G1 £l Body") as (ζi ζidx) "(#Obsl & Body & G1)";
      [solve_lazyE|].
    iMod (uniq_body_open κ ty with "LFT UNIQ Gκ1 Gκ2 Incl Body G1 G2 £o") as "Open".
    iModIntro. iExists ζi, ζidx. by iFrame "Obsl Incl Open".
  Qed.

  Lemma type_pcell_store_sc_instr {𝔄} `{!NoCell 𝔄} κ (ty: type 𝔄) p q r E L I :
    lctx_lft_alive E L κ →
    typed_instr E L I
      +[p ◁ᵥ &shr{κ} (pcell_ty ty.(ty_mty)); q ◁ᵥ &uniq{κ} (cell_points_to_ty ty); r ◁ᵥ ty]
      (Store ScOrd ty.(ty_mty) p r) (λ _, +[])
      (λ post '-[(_, g); bor; y], λ mask π,
        let '(_, (g', _), _, _, _, _) := bor in g = g' ∧
        (uniq_bor_future bor π = (g, vπ y π) → post -[] mask π)).
  Proof.
    iIntros (Alv tid post mask iκs [[l g] [[[[[[l' [g' x]] ξi] di] gi] ξidx] [y []]]])
      "#LFT #TIME #PROPH #UNIQ #E L $ (p & q & r & _) #Obs".
    iMod (proph_obs_sat with "PROPH Obs") as "(% & <- & _)"; [done|].
    iDestruct (Alv with "L E") as "#Alv".
    wp_bind p. iApply (wp_val with "p"). iIntros (w d Hp Hw) "#⧖ #Own".
    simpl in Hw. simplify_eq. cbn [of_val].
    wp_bind r. iApply (wp_val with "r"). iIntros (v dy Hr Hv) "#⧖y Gy".
    iDestruct (tctx_val_elim with "q") as (vq Hq wq dq [-> Hwq]) "[#⧖q Uniq]".
    destruct d as [|d0]; [done|].
    have Hm := ty_mty_wf ty.
    iApply wp_fupd.
    iApply (wp_cumulative_time_receipt2 with "TIME"); [solve_ndisj|]. iIntros "⧗".
    iDestruct (cumulative_time_receipt_sep 1 1 with "⧗") as "[⧗a ⧗b]".
    set D := S d0 `max` dy.
    iAssert (⧖D)%I as "#⧖D"; [rewrite persistent_time_receipt_sep; by iFrame "⧖ ⧖y"|].
    iMod (cumulative_persistent_time_receipt_get_credits with "TIME ⧗a ⧖D") as "[#⧖D1 £]";
      [solve_ndisj|].
    iMod (cumulative_persistent_time_receipt_get_credits with "TIME ⧗b ⧖D1") as "[#⧖D2 _]";
      [solve_ndisj|].
    iDestruct (lc_weaken (((S d0 + 1) + (5 + (S d0 + 1) + (1 + (S d0 + 1))) + 1)) with "£")
      as "£"; [rewrite /advance_credits; lia|].
    iMod (llctx_interp_make_guarded with "L") as (γh) "[H1 [H2 [#Gh #Back]]]"; [solve_ndisj|].
    iDestruct (guards_transitive with "Gh Alv") as "#Gκ".
    iMod (pcell_lend_open with "LFT PROPH UNIQ Own Uniq Gκ Gκ H1 H2 £")
      as (ζi ζidx) "(#Obsl & #Incl & H2 & ⧗s & _ & _ & Bytes & Close)".
    iDestruct (bytes_own_val with "Bytes") as %[vx Hvx].
    rewrite /cbytes (bytes_own_gcont _ _ _ (fv_lift vx)); [|by rewrite ty_fval_nocell // Hvx].
    have -> : (MLit $ VPtr l) = (MLit $ VPtr (l +ₗ 0%nat)) by rewrite shift_loc_0_nat.
    iApply (wp_gcont_store_sc_sub _ l _ _ 0 _ vx v (fv_lift v) with "Bytes");
      [solve_ndisj|done|by eapply ty_val_wf|apply fv_repl_here|].
    iIntros "!> Bytes".
    iMod (fupd_mask_subseteq (↑Nllft)) as "Hback"; [solve_ndisj|].
    iMod ("Close" $! y D D with "[Gy Bytes] ⧗s") as "[UB H1]".
    { iNext. iSplitR.
      { iApply (persistent_time_receipt_mono with "⧖D2"). lia. }
      iSplitL "Gy"; [by iDestruct (ty_gho_own_depth_mono _ dy dy D D with "Gy") as "[$ _]"; lia|].
      rewrite /cbytes (bytes_own_gcont _ _ _ (fv_lift v)) //. by rewrite ty_fval_nocell // Hv. }
    iMod "Hback" as "_".
    iMod (fupd_mask_mono with "(Back H1 H2)") as "L"; [solve_ndisj|].
    iMod (resolve_uniq_body ty y with
      "LFT PROPH UNIQ TIME Incl E [] L [] UB") as "[#Hrslv [L _]]"; [done|solve_ndisj| | |].
    { iApply guards_refl. }
    { iApply (persistent_time_receipt_mono with "⧖D2"). lia. }
    iModIntro. iExists -[]. iFrame "L". iSplit; [done|].
    iCombine "Hrslv Obsl Obs" as "Obs2". iApply (proph_obs_impl with "Obs2").
    intros π (Hres & Hl & _ & Hpost). apply Hpost. rewrite /uniq_bor_future /=.
    rewrite Hl. f_equal.
    etrans; [apply (uniq_prvar_app_irrel x y ζi π)|]. by rewrite Hres.
  Qed.

  Lemma type_pcell_mcas_instr {𝔄} `{!NoCell 𝔄} κ (ty: type 𝔄) p q r1 r2 E L I :
    lctx_lft_alive E L κ →
    typed_instr E L I
      +[p ◁ᵥ &shr{κ} (pcell_ty ty.(ty_mty)); q ◁ᵥ &uniq{κ} (cell_points_to_ty ty);
        r1 ◁ᵥ ty; r2 ◁ᵥ ty]
      (MCAS ty.(ty_mty) p r1 r2) (λ v, +[v ◁ᵥ bool_ty])
      (λ post '-[(_, g); bor; y1; y2], λ mask π,
        let '(_, (g', x), _, _, _, _) := bor in g = g' ∧
        if bool_decide (ty.(ty_val) x = ty.(ty_val) y1)
        then uniq_bor_future bor π = (g, vπ y2 π) → post -[true] mask π
        else uniq_bor_future bor π = (g, vπ x π) → post -[false] mask π).
  Proof.
    iIntros (Alv tid post mask iκs [[l g] [[[[[[l' [g' x]] ξi] di] gi] ξidx] [y1 [y2 []]]]])
      "#LFT #TIME #PROPH #UNIQ #E L $ (p & q & r1 & r2 & _) #Obs".
    iMod (proph_obs_sat with "PROPH Obs") as "(% & <- & _)"; [done|].
    iDestruct (Alv with "L E") as "#Alv".
    wp_bind p. iApply (wp_val with "p"). iIntros (w d Hp Hw) "#⧖ #Own".
    simpl in Hw. simplify_eq. cbn [of_val].
    wp_bind r1. iApply (wp_val with "r1"). iIntros (v1 d1 Hr1 Hv1) "_ _".
    wp_bind r2. iApply (wp_val with "r2"). iIntros (v2 dy Hr2 Hv2) "#⧖y Gy".
    iDestruct (tctx_val_elim with "q") as (vq Hq wq dq [-> Hwq]) "[#⧖q Uniq]".
    destruct d as [|d0]; [done|].
    have Hm := ty_mty_wf ty.
    iApply wp_fupd.
    iApply (wp_cumulative_time_receipt2 with "TIME"); [solve_ndisj|]. iIntros "⧗".
    iDestruct (cumulative_time_receipt_sep 1 1 with "⧗") as "[⧗a ⧗b]".
    set D := S d0 `max` dy.
    iAssert (⧖D)%I as "#⧖D"; [rewrite persistent_time_receipt_sep; by iFrame "⧖ ⧖y"|].
    iMod (cumulative_persistent_time_receipt_get_credits with "TIME ⧗a ⧖D") as "[#⧖D1 £]";
      [solve_ndisj|].
    iMod (cumulative_persistent_time_receipt_get_credits with "TIME ⧗b ⧖D1") as "[#⧖D2 _]";
      [solve_ndisj|].
    iDestruct (lc_weaken (((S d0 + 1) + (5 + (S d0 + 1) + (1 + (S d0 + 1))) + 1)) with "£")
      as "£"; [rewrite /advance_credits; lia|].
    iMod (llctx_interp_make_guarded with "L") as (γh) "[H1 [H2 [#Gh #Back]]]"; [solve_ndisj|].
    iDestruct (guards_transitive with "Gh Alv") as "#Gκ".
    iMod (pcell_lend_open with "LFT PROPH UNIQ Own Uniq Gκ Gκ H1 H2 £")
      as (ζi ζidx) "(#Obsl & #Incl & H2 & ⧗s & #⧖x & Gx & Bytes & Close)".
    iDestruct (bytes_own_val with "Bytes") as %[vx Hvx].
    rewrite /cbytes (bytes_own_gcont _ _ _ (fv_lift vx)); [|by rewrite ty_fval_nocell // Hvx].
    have -> : (MLit $ VPtr l) = (MLit $ VPtr (l +ₗ 0%nat)) by rewrite shift_loc_0_nat.
    iApply (wp_gcont_mcas_sub _ l _ _ 0 _ vx v1 v2 (fv_lift v2) with "Bytes");
      [solve_ndisj|done|by eapply ty_val_wf|apply fv_repl_here|].
    iIntros "!>" (b) "[[[-> %Heq] Bytes]|[[-> %Hne] Bytes]]".
    - subst v1.
      iMod (fupd_mask_subseteq (↑Nllft)) as "Hback"; [solve_ndisj|].
      iMod ("Close" $! y2 D D with "[Gy Bytes] ⧗s") as "[UB H1]".
      { iNext. iSplitR.
        { iApply (persistent_time_receipt_mono with "⧖D2"). lia. }
        iSplitL "Gy"; [by iDestruct (ty_gho_own_depth_mono _ dy dy D D with "Gy") as "[$ _]"; lia|].
        rewrite /cbytes (bytes_own_gcont _ _ _ (fv_lift v2)) //. by rewrite ty_fval_nocell // Hv2. }
      iMod "Hback" as "_".
      iMod (fupd_mask_mono with "(Back H1 H2)") as "L"; [solve_ndisj|].
      iMod (resolve_uniq_body ty y2 with
        "LFT PROPH UNIQ TIME Incl E [] L [] UB") as "[#Hrslv [L _]]"; [done|solve_ndisj| | |].
      { iApply guards_refl. }
      { iApply (persistent_time_receipt_mono with "⧖D2"). lia. }
      iModIntro. iExists -[true]. iFrame "L". iSplitR.
      { iSplit; [|done]. rewrite tctx_val_val. iExists D. iSplit; [done|]. by iFrame "⧖D". }
      iCombine "Hrslv Obsl Obs" as "Obs2". iApply (proph_obs_impl with "Obs2").
      intros π (Hres & Hl & _ & Hpost). rewrite bool_decide_eq_true_2 in Hpost; [|by rewrite Hvx Hv1].
      apply Hpost. rewrite /uniq_bor_future /= Hl. f_equal.
      etrans; [apply (uniq_prvar_app_irrel x y2 ζi π)|]. by rewrite Hres.
    - iMod (fupd_mask_subseteq (↑Nllft)) as "Hback"; [solve_ndisj|].
      iMod ("Close" $! x di gi with "[Gx Bytes] ⧗s") as "[UB H1]".
      { iNext. iFrame "⧖x Gx". by rewrite /cbytes (bytes_own_gcont _ _ _ (fv_lift vx)); [|by rewrite ty_fval_nocell // Hvx]. }
      iMod "Hback" as "_".
      iMod (fupd_mask_mono with "(Back H1 H2)") as "L"; [solve_ndisj|].
      iMod (resolve_uniq_body ty x with
        "LFT PROPH UNIQ TIME Incl E [] L ⧖x UB") as "[#Hrslv [L _]]"; [done|solve_ndisj| |].
      { iApply guards_refl. }
      iModIntro. iExists -[false]. iFrame "L". iSplitR.
      { iSplit; [|done]. rewrite tctx_val_val. iExists D. iSplit; [done|]. by iFrame "⧖D". }
      iCombine "Hrslv Obsl Obs" as "Obs2". iApply (proph_obs_impl with "Obs2").
      intros π (Hres & Hl & _ & Hpost). rewrite bool_decide_eq_false_2 in Hpost; last first.
      { rewrite Hvx Hv1. congruence. }
      apply Hpost. rewrite /uniq_bor_future /= Hl. by rewrite Hres.
  Qed.
End pcell_atomics.
