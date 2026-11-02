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
