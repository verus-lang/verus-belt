From lrust.typing Require Export type.
From lrust.typing Require Import freeable_util bytes_layout.
From lrust.util Require Export non_atomic_cell_map.
From guarding Require Import guard tactics.
From lrust.lifetime Require Import lifetime_full.
Set Default Proof Using "Type".

(** * Owning pointers to bytes (stage 3 of the MiniRust memory model)

[own_bytes n ty] is an owning pointer whose pointee lives in the byte region of the
heap (see [lang/heap.v]): it owns the bytes that represent the value of the pointee
([bytes_own ty l x]), and the freeable token of the [ty_bsize ty] bytes of a block of [n]
bytes (see [design_docs/minirust-memory-model.md], "Outcome: stage 3"). It replaced the
legacy word-level [own_ptr] (deleted in stage 5).

The bytes are _fancy bytes_ (§10 step 4 of [design_docs/pcell-multibyte-cells.md]): the
edges of the locations [l], [l +ₗ 1], ... point to bytes or to the byte-cells of cell
groups ([heap_mapsto_fbytes]), and represent the fancy value [ty_fval x] at [ty_mty ty]
([ty_fbytes R ty x fbs], with a static registry [R] whose fragments [greg] are owned:
[frepr] depends only on the static registry). A value of a type without cells
([NoCell]), or with a MiniRust value, owns plain bytes [l ↦b bs] with [ty_bytes ty x bs]
([bytes_own_nocell], [bytes_own_to_bytes]); the fancy bytes of any value can be turned into
plain bytes by dropping its cells ([wp_bytes_own_forget]). The fancy bytes split along
the layout of pairs ([bytes_own_pair]).

The pointee is read and written with the typed [Load] and [Store] of [ty_mty ty]:
[wp_own_bytes_load], [wp_own_bytes_store], [wp_own_bytes_new] and
[wp_own_bytes_delete]. *)

Implicit Type 𝔄 𝔅: syn_type.

Section own_bytes.
  Context `{!typeG Σ}.

  (** The static registry [R]: its fragments. *)
  Definition greg_map (R: gmap positive (mty * list positive)) : iProp Σ :=
    [∗ map] g ↦ e ∈ R, greg g e.1 e.2.

  Global Instance greg_map_persistent R : Persistent (greg_map R).
  Proof. apply _. Qed.
  Global Instance greg_map_timeless R : Timeless (greg_map R).
  Proof. apply _. Qed.

  (** Two fragments of the static registry agree: their union is a fragment that contains
      both. *)
  Lemma greg_map_union R1 R2 :
    greg_map R1 -∗ greg_map R2 -∗ ⌜R1 ⊆ R1 ∪ R2 ∧ R2 ⊆ R1 ∪ R2⌝ ∗ greg_map (R1 ∪ R2).
  Proof.
    iIntros "#H1 #H2". iSplit.
    - iSplit; [iPureIntro; apply map_union_subseteq_l|].
      rewrite map_subseteq_spec. iIntros (g [m cs] Hg).
      destruct (R1 !! g) as [[m' cs']|] eqn:Hg1.
      + iDestruct (big_sepM_lookup with "H1") as "G1"; [done|].
        iDestruct (big_sepM_lookup with "H2") as "G2"; [done|].
        iDestruct (greg_agree with "G1 G2") as %[Hm Hc]. simpl in Hm, Hc. subst.
        iPureIntro. by apply lookup_union_Some_l.
      + iPureIntro. by rewrite lookup_union_r.
    - rewrite /greg_map. iApply big_sepM_intro. iIntros "!>" (g e Hg).
      apply lookup_union_Some_raw in Hg as [Hg|[_ Hg]].
      + by iApply (big_sepM_lookup with "H1").
      + by iApply (big_sepM_lookup with "H2").
  Qed.

  (** The fancy bytes at [l] represent [x]. It is sealed: unifying it with other
      predicates would unfold the fancy points-to and the representation. *)
  Definition bytes_own_def {𝔄} (ty: type 𝔄) (l: loc) (x: ~~𝔄) : iProp Σ :=
    ∃ R fbs, heap_mapsto_fbytes l fbs ∗ ⌜ty_fbytes R ty x fbs⌝ ∗ greg_map R.
  Local Definition bytes_own_aux : seal (@bytes_own_def). Proof. by eexists. Qed.
  Definition bytes_own := bytes_own_aux.(unseal).
  Definition bytes_own_unseal : @bytes_own = @bytes_own_def := bytes_own_aux.(seal_eq).
  Global Arguments bytes_own {_} _ _ _.

  Global Instance bytes_own_timeless {𝔄} (ty: type 𝔄) l x : Timeless (bytes_own ty l x).
  Proof. rewrite bytes_own_unseal. apply _. Qed.

  (** Types with the same fancy bytes have the same byte ownership. *)
  Lemma bytes_own_iff {𝔄 𝔅} (ty: type 𝔄) (ty': type 𝔅) l x x' :
    (∀ R fbs, ty_fbytes R ty x fbs ↔ ty_fbytes R ty' x' fbs) →
    bytes_own ty l x ⊣⊢ bytes_own ty' l x'.
  Proof. intros Hb. rewrite bytes_own_unseal /bytes_own_def. by setoid_rewrite Hb. Qed.

  Lemma bytes_own_same {𝔄} (ty ty': type 𝔄) l x : bytes_own ty l x ⊣⊢ bytes_own ty' l x.
  Proof. apply bytes_own_iff=> ??. apply ty_fbytes_same. Qed.

  (** The form of [lang/heap_cells.v]: fancy bytes with [brepr]. *)
  Lemma bytes_own_brepr {𝔄} (ty: type 𝔄) l x :
    bytes_own ty l x ⊣⊢ ∃ fbs fv, heap_mapsto_fbytes l fbs ∗
      ⌜length fbs = ty_bsize ty ∧ ty.(ty_fval) x = Some fv⌝ ∗ brepr ty.(ty_mty) fbs fv.
  Proof.
    rewrite bytes_own_unseal /bytes_own_def /brepr /greg_map. iSplit.
    - iIntros "(%R & %fbs & Hfbs & (%Hlen & %fv & %Hfv & %Hrep) & HR)".
      iExists fbs, fv. iFrame. by iPureIntro.
    - iIntros "(%fbs & %fv & Hfbs & [%Hlen %Hfv] & %R & %Hrep & HR)".
      iExists R, fbs. iFrame. iPureIntro. split; [done|]. by exists fv.
  Qed.

  (** Plain bytes. *)
  Lemma bytes_own_of_bytes {𝔄} (ty: type 𝔄) l x bs :
    ty_bytes ty x bs → l ↦b bs -∗ bytes_own ty l x.
  Proof.
    rewrite bytes_own_unseal /bytes_own_def.
    iIntros (Hbs) "Hbs". iExists ∅, (inr <$> bs). rewrite -heap_mapsto_fbytes_bytes.
    iFrame "Hbs". iSplit; [|by rewrite /greg_map big_sepM_empty]. iPureIntro.
    apply ty_fbytes_syn, syn_fbytes_bytes. by apply (ty_bytes_syn ty).
  Qed.

  (** The reduction lemmas: the fancy bytes of a value with a MiniRust value, or of a value
      of a type without cells, are plain bytes. *)
  Lemma bytes_own_to_bytes {𝔄} (ty: type 𝔄) l x v :
    ty.(ty_val) x = Some v → bytes_own ty l x -∗ ∃ bs, l ↦b bs ∗ ⌜ty_bytes ty x bs⌝.
  Proof.
    rewrite bytes_own_unseal /bytes_own_def.
    iIntros (Hv) "(%R & %fbs & Hfbs & %Hfb & _)". rewrite ty_fbytes_syn in Hfb.
    rewrite -ty_val_eq in Hv. apply (syn_fbytes_val _ _ _ _ Hv) in Hfb as (bs & -> & Hbs).
    iExists bs. rewrite heap_mapsto_fbytes_bytes. iFrame. iPureIntro. by apply (ty_bytes_syn ty).
  Qed.

  Lemma bytes_own_nocell {𝔄} `{!NoCell 𝔄} (ty: type 𝔄) l x :
    bytes_own ty l x ⊣⊢ ∃ bs, l ↦b bs ∗ ⌜ty_bytes ty x bs⌝.
  Proof.
    iSplit.
    - rewrite bytes_own_unseal /bytes_own_def. iIntros "(%R & %fbs & Hfbs & %Hfb & _)". rewrite ty_fbytes_syn in Hfb.
      apply syn_fbytes_nocell in Hfb as (bs & -> & Hbs); [|done].
      iExists bs. rewrite heap_mapsto_fbytes_bytes. iFrame. iPureIntro. by apply (ty_bytes_syn ty).
    - iIntros "(%bs & Hbs & %Hbs)". by iApply bytes_own_of_bytes.
  Qed.

  (** The view of the bytes of a value with a MiniRust value, for the guarded reads
      ([wp_load_na_guarded_gen]): its plain bytes. *)
  Lemma bytes_own_view {𝔄} (ty: type 𝔄) l x v :
    ty.(ty_val) x = Some v →
    ⊢ □ (bytes_own ty l x -∗ ∃ bs, ⌜ty_bytes ty x bs⌝ ∗ l ↦b bs ∗ (l ↦b bs -∗ bytes_own ty l x)).
  Proof.
    iIntros (Hv) "!> Bytes". iDestruct (bytes_own_to_bytes with "Bytes") as (bs) "[Hbs %Hbs]";
      [done|].
    iExists bs. iFrame "Hbs". iSplit; [done|]. by iApply bytes_own_of_bytes.
  Qed.

  Lemma bytes_own_nocell_bytes {𝔄} `{!NoCell 𝔄} (ty: type 𝔄) l x :
    bytes_own ty l x -∗ ∃ bs, l ↦b bs ∗ ⌜ty_bytes ty x bs⌝.
  Proof. rewrite bytes_own_nocell. iIntros "$". Qed.

  Lemma bytes_own_view_nocell {𝔄} `{!NoCell 𝔄} (ty: type 𝔄) l x :
    ⊢ □ (bytes_own ty l x -∗ ∃ bs, ⌜ty_bytes ty x bs⌝ ∗ l ↦b bs ∗ (l ↦b bs -∗ bytes_own ty l x)).
  Proof.
    iIntros "!> Bytes". iDestruct (bytes_own_nocell_bytes with "Bytes") as (bs) "[Hbs %Hbs]".
    iExists bs. iFrame "Hbs". iSplit; [done|]. by iApply bytes_own_of_bytes.
  Qed.

  (** A value of a type without cells whose bytes are owned has a MiniRust value. *)
  Lemma bytes_own_val {𝔄} `{!NoCell 𝔄} (ty: type 𝔄) l x :
    bytes_own ty l x -∗ ⌜is_Some (ty.(ty_val) x)⌝.
  Proof.
    rewrite bytes_own_nocell. iIntros "(%bs & _ & %Hbs)". iPureIntro. by eapply ty_bytes_val.
  Qed.

  Lemma bytes_own_length {𝔄} (ty: type 𝔄) l x :
    bytes_own ty l x -∗ ∃ fbs, heap_mapsto_fbytes l fbs ∗ ⌜length fbs = ty_bsize ty⌝ ∗
      (heap_mapsto_fbytes l fbs -∗ bytes_own ty l x).
  Proof.
    rewrite bytes_own_unseal /bytes_own_def.
    iIntros "(%R & %fbs & Hfbs & %Hfb & #HR)". iExists fbs. iFrame "Hfbs".
    iSplit; [by destruct Hfb|]. iIntros "Hfbs". iExists R, fbs. by iFrame "Hfbs HR".
  Qed.

  (** Dropping the cells of the bytes (e.g. to overwrite or deallocate them). *)
  Lemma wp_bytes_own_forget {𝔄} (ty: type 𝔄) l x E e Φ :
    TCEq (to_val e) None → ↑naN ⊆ E →
    bytes_own ty l x -∗
    (∀ bs, l ↦b bs -∗ ⌜length bs = ty_bsize ty⌝ -∗ WP e @ E {{ Φ }}) -∗ WP e @ E {{ Φ }}.
  Proof.
    rewrite bytes_own_unseal /bytes_own_def.
    iIntros (??) "(%R & %fbs & Hfbs & [%Hlen _] & _) Hwp".
    iApply (wp_fbytes_forget with "Hfbs"); [done..|]. iIntros (bs) "Hbs %Hlen'".
    iApply ("Hwp" with "Hbs"). by rewrite Hlen' Hlen.
  Qed.

  (** The fancy bytes of a pair: those of its components, one after the other. *)
  Lemma bytes_own_pair {𝔄 𝔅} (ty: type (𝔄 * 𝔅)) (ty1: type 𝔄) (ty2: type 𝔅) l x1 x2 :
    bytes_own ty l (x1, x2) ⊣⊢ bytes_own ty1 l x1 ∗ bytes_own ty2 (l +ₗ ty_bsize ty1) x2.
  Proof.
    rewrite bytes_own_unseal /bytes_own_def. setoid_rewrite ty_fbytes_syn. iSplit.
    - iIntros "(%R & %fbs & Hfbs & %Hfb & #HR)".
      apply syn_fbytes_pair in Hfb as (f1 & f2 & -> & H1 & H2).
      rewrite heap_mapsto_fbytes_app (syn_fbytes_length _ _ _ H1) -(ty_bsize_eq ty1).
      iDestruct "Hfbs" as "[F1 F2]".
      iSplitL "F1"; iExists R, _; iFrame "∗#"; by iPureIntro.
    - iIntros "[(%R1 & %f1 & F1 & %H1 & #HR1) (%R2 & %f2 & F2 & %H2 & #HR2)]".
      iDestruct (greg_map_union with "HR1 HR2") as "[[%Hs1 %Hs2] HR]".
      iExists (R1 ∪ R2), (f1 ++ f2).
      rewrite heap_mapsto_fbytes_app (syn_fbytes_length _ _ _ H1) -(ty_bsize_eq ty1).
      iFrame "F1 F2 HR". iPureIntro. apply syn_fbytes_pair. exists f1, f2.
      split; [done|]. split; [by eapply (syn_fbytes_mono R1)|by eapply (syn_fbytes_mono R2)].
  Qed.

  (** The fancy bytes of a cell (for the [PCell] types of §10 step 5): a value [g] of
      [pcellₛ m] (with a well-formed content type [m]) is a cell group, and its fancy
      bytes at [l] are exactly the location side of the group ([loc_side]): the edges of
      the locations [l], [l +ₗ 1], ... to the byte-cells of [g]. *)
  Lemma frepr_cell_inv {W} (R: gmap positive (mty * list positive)) m
      (fbs: list (positive + AbstractByte W)) g :
    frepr R m fbs (FVCell g) → ∃ cs, R !! g = Some (m, cs) ∧ fbs = inl <$> cs.
  Proof. inversion 1 as [? ? cs| ? ? v ? Hv| |]; [by eauto|]. by destruct v. Qed.

  Lemma bytes_own_pcell {m} (ty: type (pcellₛ m)) l (g: ~~(pcellₛ m)) :
    mty_wf m →
    bytes_own ty l g ⊣⊢ ∃ cs, loc_side l g m cs ∗ ⌜length cs = mty_size m⌝.
  Proof.
    intros Hwf. rewrite bytes_own_unseal /bytes_own_def /ty_fbytes /ty_bsize -ty_mty_eq -ty_fval_eq /= decide_True //.
    iSplit.
    - iIntros "(%R & %fbs & Hfbs & (%Hlen & %fv & %Hfv & %Hrep) & #HR)".
      injection Hfv as <-.
      destruct (frepr_cell_inv _ _ _ _ Hrep) as (cs & HRg & ->).
      iExists cs. iSplit; [|by rewrite length_fmap in Hlen]. iSplit.
      + by iDestruct (big_sepM_lookup with "HR") as "?".
      + by rewrite /heap_mapsto_fbytes big_sepL_fmap.
    - iIntros "(%cs & [#Hg Hls] & %Hlen)". iExists {[g := (m, cs)]}, (inl <$> cs).
      rewrite /heap_mapsto_fbytes big_sepL_fmap /greg_map big_sepM_singleton. iFrame "Hls Hg".
      iPureIntro. split; [by rewrite length_fmap|]. exists (FVCell g). split; [done|].
      apply frepr_cell. by rewrite lookup_singleton.
  Qed.

  (** Zero-sized values: their fancy bytes are empty. *)
  Lemma bytes_own_zst_emp {𝔄} (ty: type 𝔄) l x :
    ty_bsize ty = 0 → is_Some (ty.(ty_val) x) → ⊢ bytes_own ty l x.
  Proof.
    intros Hz [v Hv]. iApply (bytes_own_of_bytes _ _ _ []).
    - exists v. split; [done|].
      have Hwf := ty_val_wf _ _ _ Hv.
      have Hdec := decode_encode_value (W:=val) _ _ (ty_mty_wf ty) Hwf.
      have Hlen := length_encode_value (W:=val) (ty.(ty_mty)) v.
      rewrite /ty_bsize in Hz. rewrite Hz in Hlen.
      apply nil_length_inv in Hlen. by rewrite Hlen in Hdec.
    - by rewrite heap_mapsto_bytes_eq /heap_mapsto_bytes_def /heap_mapsto_st_vec.
  Qed.

  Lemma bytes_own_zst_true {𝔄} (ty: type 𝔄) l x :
    ty_bsize ty = 0 → is_Some (ty.(ty_val) x) → bytes_own ty l x ⊣⊢ True.
  Proof.
    intros. iSplit; [by iIntros|]. iIntros "_". by iApply bytes_own_zst_emp.
  Qed.

  (** The fancy bytes of a zero-sized value do not depend on the location. *)
  Lemma bytes_own_zst_loc {𝔄} (ty: type 𝔄) l l' x :
    ty_bsize ty = 0 → bytes_own ty l x ⊣⊢ bytes_own ty l' x.
  Proof.
    intros Hz. rewrite bytes_own_unseal /bytes_own_def.
    iSplit; iIntros "(%R & %fbs & _ & %Hfb & HR)"; iExists R, fbs; iFrame "HR";
      have Hfb' := Hfb; destruct Hfb' as [Hlen _]; rewrite Hz in Hlen;
      apply nil_length_inv in Hlen; subst fbs; rewrite /heap_mapsto_fbytes /=; by iSplit.
  Qed.

  (** The sharing predicate is structural, as for [own_ptr]: a guard of the bytes and
      the sharing predicate of the contents, under one later. *)
  Program Definition own_bytes {𝔄} (n: nat) (ty: type 𝔄) : type (at_locₛ 𝔄) := {|
    ty_size := 1;
    ty_lfts := ty.(ty_lfts);
    ty_E := ty.(ty_E);
    ty_gho_own x d g tid := [S(d') := d]
      bytes_own ty x.1 x.2 ∗ freeable_sz n (ty_bsize ty) x.1 ∗
      ▷ ty.(ty_gho_own) x.2 d' g tid;
    ty_gho_res x d g tid := [S(d') := d]
      bytes_own ty x.1 x.2 ∗ freeable_sz n (ty_bsize ty) x.1 ∗
      ▷ ty.(ty_gho_res) x.2 d' g tid;
    ty_gho_pers x d g tid := [S(d') := d] ▷ ty.(ty_gho_pers) x.2 d' g tid;
    ty_mty := syn_mty _; ty_val := syn_val; ty_mty_eq := eq_refl; ty_val_eq _ := eq_refl;
    ty_fval := syn_fval; ty_fval_eq _ := eq_refl;
    ty_phys x tid := [FVal (LitV x.1)];
    ty_shr κ x d g tid :=
      ▷ [S(d') := d]
        (@[κ] &&{↑NllftG; g+1}&&> bytes_own ty x.1 x.2) ∗ ty.(ty_shr) κ x.2 d' g tid;
  |}%I.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation.
    move=> 𝔄 n ty [|d] g d' g' x tid ??; iIntros "H" => //=.
    iDestruct "H" as "(Hown & Hfree & Hgho)". destruct d'; first lia => /=.
    iDestruct (ty.(ty_gho_own_depth_mono) with "Hgho") as "[$ Hwand]" => //; first lia.
    iFrame. iIntros "($ & $ & Hgho)". by iApply "Hwand".
  Qed.
  Next Obligation.
    move=> 𝔄 n ty [|d] g d' g' x tid ??; iIntros "H" => //=.
    destruct d'; first lia => /=.
    iDestruct (ty.(ty_gho_pers_depth_mono) with "H") as "$" => //; first lia.
  Qed.
  Next Obligation.
    intros 𝔄 n ty x d g tid. iIntros "A". destruct d as [|d']; first by done.
    iDestruct "A" as "[_ [_ pers]]". iApply ty_gho_pers_impl. iFrame.
  Qed.
  Next Obligation.
    intros 𝔄 n ty κ κ' x m d g tid. iIntros "#Incl Shr".
    iNext. destruct d as [|d']; [done|]. iDestruct "Shr" as "[Pt Shr]". iSplit.
    - replace (g + m + 1) with (m + (g + 1)) by lia.
      iApply (guards_transitive_additive with "Incl Pt").
    - iApply (ty_shr_lft_mono with "Incl Shr").
  Qed.
  Next Obligation.
    intros 𝔄 n ty κ d g d' g' x tid ??. iIntros "Shr".
    iNext. destruct d as [|d0]; [done|]. destruct d' as [|d0']; [lia|].
    iDestruct "Shr" as "[Pt Shr]". iSplit.
    - leaf_goal laters to (g+1). { lia. } iFrame "Pt".
    - iApply (ty_shr_depth_mono with "Shr"); lia.
  Qed.
  Next Obligation.
    intros 𝔄 n ty E κ x d g tid G ??. iIntros "#LFT #Incl #Pers #Gκ G Bor".
    destruct d as [|d']; [done|]. simpl.
    iMod (llftl_sep_split with "LFT Bor") as "[Pt Bor]"; [solve_ndisj|].
    iMod (llftl_sep_split with "LFT Bor") as "[_ Bor]"; [solve_ndisj|].
    iMod (llftl_bor_guard with "LFT Pt") as "#Pt"; [solve_ndisj|].
    iMod (llftl_bor_later_step with "LFT Gκ G Bor") as "Upd"; [first [apply _ | solve_ndisj]..|].
    iModIntro. iModIntro. iNext. iMod "Upd" as "[G Bor]".
    iMod (ty_share with "LFT Incl Pers Gκ G Bor") as "Shr"; [done..|].
    iModIntro. iApply (step_fupdN_wand with "Shr"). iIntros ">[$ Shr] !> !>".
    iFrame "Shr". leaf_goal laters to 1. { lia. } iFrame "Pt".
  Qed.
  Next Obligation.
    intros 𝔄 n ty κ x n0 d g tid ξ R Hin.
    iIntros "#LFT #Incl #Pers #Shr".
    destruct d as [|d']; first by done. simpl.
    iApply (bi.laterN_le (S (d' * (g + 2)))). { lia. }
    iNext. iDestruct "Shr" as "[_ Shr]".
    iDestruct (ty_shr_guard_proph ty κ x.2 n0 d' g tid ξ R Hin with "LFT Incl Pers Shr")
      as "GP".
    iNext. iIntros "#Rκ".
    leaf_goal laters to (n0 + (d'+1)*(g+1)). { lia. } by iApply "GP".
  Qed.
  Next Obligation.
    intros 𝔄 n ty x [|d] g tid; [by iIntros|]. iIntros "($ & $ & A)".
    iNext. by iApply ty_gho_res_of_own.
  Qed.

  Global Instance own_bytes_ne {𝔄} n : NonExpansive (@own_bytes 𝔄 n).
  Proof.
    move=> m ty ty' Eqv. split=>/=; [done|apply Eqv|apply Eqv| | |done|].
    - move=> [l x] [|d] g tid //=. rewrite /ty_bsize (ty_mty_same ty ty') (bytes_own_same ty ty').
      do 3 f_equiv. apply Eqv.
    - move=> [l x] [|d] g tid //=. do 2 f_equiv. apply Eqv.
    - move=> κ [l x] d g tid. f_equiv. destruct d; [done|]. simpl.
      rewrite (bytes_own_same ty ty'). f_equiv. apply Eqv.
  Qed.

  Global Instance own_bytes_type_contractive 𝔄 n : TypeContractive (@own_bytes 𝔄 n).
  Proof.
    split; [by apply type_lft_morphism_id_like|done| | | |].
    - move=>/= m ty ty' _ _ _ EqOwn _ _ _ [l x] [|d] g tid //=.
      rewrite /ty_bsize (ty_mty_same ty ty') (bytes_own_same ty ty').
      do 2 f_equiv. f_contractive. by apply EqOwn.
    - move=>/= m ty ty' _ _ _ _ EqPers _ _ [l x] [|d] g tid //=.
      f_contractive. by apply EqPers.
    - done.
    - move=>/= m ty ty' _ _ _ _ _ _ EqShr κ [l x] d g tid.
      apply later_contractive. split=> m' Hm. destruct d as [|d']; [done|]. simpl.
      rewrite (bytes_own_same ty ty'). f_equiv. eapply dist_later_lt; [apply EqShr|lia].
  Qed.
End own_bytes.

Section own_bytes_rules.
  Context `{!typeG Σ}.

  Lemma own_bytes_gho_intro {𝔄} n (ty: type 𝔄) l x d g tid :
    bytes_own ty l x -∗ freeable_sz n (ty_bsize ty) l -∗ ▷ ty.(ty_gho_own) x d g tid -∗
    (own_bytes n ty).(ty_gho_own) (l, x) (S d) g tid.
  Proof. iIntros "$ $ $". Qed.

  (** Reading the pointee: a typed [Load] of [ty_mty ty] returns the value of [x]. *)
  Lemma wp_own_bytes_load {𝔄} n (ty: type 𝔄) l x v d g tid E :
    ty.(ty_val) x = Some v →
    {{{ (own_bytes n ty).(ty_gho_own) (l, x) d g tid }}}
      Load Na1Ord ty.(ty_mty) #l @ E
    {{{ RET MLitV v; (own_bytes n ty).(ty_gho_own) (l, x) d g tid }}}.
  Proof.
    iIntros (Hv Φ) "Own HΦ". destruct d as [|d]; [done|].
    iDestruct "Own" as "(Bytes & Free & Gho)".
    iDestruct (bytes_own_to_bytes with "Bytes") as (bs) "[Hbs %Hbs]"; [done|].
    iApply (wp_load_na with "Hbs"); [by eapply ty_bytes_decode|].
    iIntros "!> Hbs". iApply "HΦ". iFrame. by iApply bytes_own_of_bytes.
  Qed.

  (** Writing the pointee: a typed [Store] of the value of [y] replaces [x] by [y];
      the ownership of [x] is given back. *)
  Lemma wp_own_bytes_store {𝔄} n (ty: type 𝔄) l x y v d g tid E :
    ↑naN ⊆ E → ty.(ty_val) y = Some v →
    {{{ (own_bytes n ty).(ty_gho_own) (l, x) (S d) g tid ∗ ▷ ty.(ty_gho_own) y d g tid }}}
      Store Na1Ord ty.(ty_mty) #l (MLit v) @ E
    {{{ RET #☠; (own_bytes n ty).(ty_gho_own) (l, y) (S d) g tid ∗
                ▷ ty.(ty_gho_own) x d g tid }}}.
  Proof.
    iIntros (? Hv Φ) "[Own Gho'] HΦ".
    iDestruct "Own" as "(Bytes & Free & Gho)".
    iApply (wp_bytes_own_forget with "Bytes"); [done..|]. iIntros (bs) "Hbs %Hlen".
    iApply (wp_store_na with "Hbs"); [done|by eapply ty_val_wf|done|].
    iIntros "!> Hbs". iApply "HΦ". iFrame. iApply (bytes_own_of_bytes with "Hbs").
    by apply ty_bytes_encode.
  Qed.

  (** Allocating a box and initialising it with a typed [Store]. *)
  Lemma wp_own_bytes_new {𝔄} (ty: type 𝔄) x v d g tid E :
    ↑naN ⊆ E → ty.(ty_val) x = Some v → (0 < ty_bsize ty)%nat →
    {{{ ▷ ty.(ty_gho_own) x d g tid }}}
      let: "l" := Alloc #(ty_bsize ty) in Store Na1Ord ty.(ty_mty) "l" (MLit v) ;; "l" @ E
    {{{ l, RET #l; (own_bytes (ty_bsize ty) ty).(ty_gho_own) (l, x) (S d) g tid }}}.
  Proof.
    iIntros (? Hv Hsz Φ) "Gho HΦ".
    wp_apply (wp_alloc_bytes with "[//]"); [rewrite /ty_bsize in Hsz; lia|]. iIntros (l sz) "(%Hn & Free & Hbs)".
    have ? : sz = mty_size (ty_mty ty) by lia. subst sz. wp_let.
    wp_bind (Store _ _ _ _). iApply (wp_store_na with "Hbs"); [done|by eapply ty_val_wf| |].
    { by rewrite length_replicate. }
    iIntros "!> Hbs". wp_seq. iApply "HΦ". iFrame "Gho". iSplitL "Hbs".
    - iApply (bytes_own_of_bytes with "Hbs"). by apply ty_bytes_encode.
    - rewrite freeable_sz_full. by iLeft.
  Qed.

  (** Deallocating a box; the ownership of its contents is given back. *)
  Lemma wp_own_bytes_delete {𝔄} (ty: type 𝔄) l x d g tid E :
    ↑naN ⊆ E → (0 < ty_bsize ty)%nat →
    {{{ (own_bytes (ty_bsize ty) ty).(ty_gho_own) (l, x) (S d) g tid }}}
      Free #(ty_bsize ty) #l @ E
    {{{ RET #☠; ▷ ty.(ty_gho_own) x d g tid }}}.
  Proof.
    iIntros (? Hsz Φ) "(Bytes & Free & Gho) HΦ".
    iApply (wp_bytes_own_forget with "Bytes"); [done..|]. iIntros (bs) "Hbs %Hlen".
    rewrite freeable_sz_full. iDestruct "Free" as "[Free|%Hz]".
    - iApply (wp_free_bytes with "[$Hbs Free]"); [done|by rewrite Hlen|by rewrite Hlen|].
      iIntros "!> _". by iApply "HΦ".
    - lia.
  Qed.
  Global Instance own_bytes_send {𝔄} n (ty: type 𝔄) : Send ty → Send (own_bytes n ty).
  Proof. move=> [Hphys Hgho]. split => //=.
       - intros tid tid' x x' He. inversion He. trivial.
       - intros tid tid' x d g G H κs d0 Hineq TG TH.
         iIntros "LFT UNIQ TIME Hg H Gg G Hgho #⧖o".
         destruct d => //=.
         iDestruct "Hgho" as "(Hown&Hfree&Hgho)".
         iModIntro. iNext. iModIntro.
         iPoseProof (Hgho with "LFT UNIQ TIME Hg H Gg G Hgho ⧖o") as "X"; first lia.
         iApply (step_fupdN_wand with "X"). iIntros ">X".
         iDestruct "X" as (x' off) "[gho [#⧖off [%Habs [G H]]]]".
         iExists (x.1, x'), (off). iModIntro. iFrame "G H ⧖off gho Hfree".
         iSplitL "Hown".
         + iApply (bytes_own_iff with "Hown"). intros R fbs.
           rewrite /ty_fbytes -!ty_fval_eq. by rewrite (syn_abstract_fval_eq _ _ _ Habs).
         + iPureIntro. simpl. rewrite Habs. trivial.
  Qed.

  Global Instance own_bytes_sync {𝔄} n (ty: type 𝔄) : Sync ty → Sync (own_bytes n ty).
  Proof.
    move=> HSync tid tid' x d g.
    have EqOwn: ∀ d0 g0, (own_bytes n ty).(ty_gho_own) x d0 g0 tid ⊣⊢
        (own_bytes n ty).(ty_gho_own) x d0 g0 tid'.
    { move=> [|d0] g0 //=. destruct (HSync tid tid' x.2 d0 g0) as [_ [Hgho _]].
      by rewrite Hgho. }
    split => //=. split; [apply EqOwn|]. split.
    - destruct d => //=. destruct (HSync tid tid' x.2 d g) as [_ [_ [-> _]]]. done.
    - move=> κ. f_equiv.
      destruct d => //=. destruct (HSync tid tid' x.2 d g) as [_ [_ [_ Hshr]]].
      by rewrite Hshr.
  Qed.

  Lemma own_bytes_resolve {𝔄} E L n (ty: type 𝔄) Φ :
    resolve E L ty Φ → resolve E L (own_bytes n ty) (λ '(l, v), Φ v).
  Proof.
    iIntros (Rslv G F x d g tid ??) "LFT PROPH UNIQ TIME E L own //".
    iIntros "Hgho".
    destruct d => //=.
    iDestruct "Hgho" as "(Hown&Hfree&Hgho)".
    iModIntro.
    replace (g + 1 + d * (g + 1)) with (S (g + d * (g + 1))) by lia.
    simpl. iModIntro. iNext.
    iDestruct (Rslv G F (snd x) d g tid _ with "[$] [$] [$] [$] [$] [$] [$] Hgho") as "Hrslv".
      { trivial. }
    iMod "Hrslv". iModIntro.
    iDestruct (step_fupdN_nmono with "Hrslv") as "Hrslv"; last first.
     - iApply (step_fupdN_wand with "Hrslv []").
       iIntros "F". iMod "F" as "[Obs G]".
       iModIntro. iFrame "G".
       iApply (proph_obs_impl with "Obs").
       intros π Ha. destruct x. apply Ha.
     - lia.
  Qed.

  Global Instance own_bytes_res_own {𝔄} n (ty: type 𝔄) : ResOwn ty → ResOwn (own_bytes n ty).
  Proof. move=> ? x [|d] g tid //=. by rewrite res_own. Qed.

  Lemma own_bytes_resolve_keep {𝔄} E L n (ty: type 𝔄) Φ :
    resolve_keep E L ty Φ → resolve_keep E L (own_bytes n ty) (λ '(l, v), Φ v).
  Proof.
    iIntros (Rslv G F x d g tid ??) "LFT PROPH UNIQ TIME E L G Hgho".
    destruct d as [|d] => //=.
    iDestruct "Hgho" as "(Hown & Hfree & Hgho)".
    iModIntro.
    replace (g + 1 + d * (g + 1)) with (S (g + d * (g + 1))) by lia.
    simpl. iModIntro. iNext.
    iMod (Rslv G F (snd x) d g tid with "LFT PROPH UNIQ TIME E L G Hgho") as "Hrslv";
      [done..|].
    iModIntro.
    iDestruct (step_fupdN_nmono with "Hrslv") as "Hrslv"; last first.
    - iApply (step_fupdN_wand with "Hrslv"). iIntros ">(Obs & $ & Res) !>".
      iFrame "Hown Hfree Res". iApply (proph_obs_impl with "Obs").
      intros π Ha. destruct x. apply Ha.
    - lia.
  Qed.
End own_bytes_rules.

Global Hint Resolve own_bytes_resolve : lrust_typing.
