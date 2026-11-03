From lrust.typing Require Export type type_context bytes_layout.
From lrust.typing Require Import programs bool int own product sum gmb_cells.
From lrust.lifetime Require Import lifetime_full.
From guarding Require Import guard tactics.
Set Default Proof Using "Type".

(** * Typing MiniRust values (stage 4 of the MiniRust memory model)

The element [p ◁ᵥ ty] types a path that evaluates to a MiniRust value [MLitV w]: it is
the result of a typed [Load] of [ty_mty ty] and the argument of a typed [Store]. The value
[x] may contain cells ([PCell]s): [w] is then the value loaded from the fancy bytes of the
fancy value [ty_fval x], whose cells (GMB instances, [typing/gmb_cells.v]) are in transit
with it ([val_cells]), and a [Store] of [w] puts them back at the new location. For a type
without cells ([NoCell]), or a value with a MiniRust value, this
is the plain form [ty_val x = Some w] ([val_own_nocell], [val_own_val], [tctx_val_elim],
[val_own_intro_sep]). The cells in transit of a tuple or a variant built from parts
([MkTuple], [MkVariant]) are those of the parts ([val_cells_seq_tuple_cons],
[val_cells_enum]; the rules [type_mk_pair_val_instr], [type_mk_tuple_val_instr],
[type_mk_variant_val_instr]). It is a semantic element ([TCtx_sem]), so the type context
needs no new case. (The legacy word element [p ◁ ty] was deleted in
stage 6.)

Pointers are MiniRust values too ([VPtr l], notation [#l]); they are the address arguments of
[Load], [Store], [MemCopy] and of the offset [+ₗ]. *)

Implicit Type 𝔄 𝔅: syn_type.

Section value_ctx.
  Context `{!typeG Σ}.

  (** The cells of a MiniRust value [w] in transit ([gtransit], [typing/gmb_cells.v]): a
      typed [Load] of the contents of the fancy value [fv] moves the cells out
      ([wp_gcont_load_move]), and they travel with the loaded value [w] as closers that put
      them back at the location where bytes that decode to [w] are stored
      ([wp_gtransit_store]). For a value without cells, this is just [w = ⌊fv⌋]
      ([val_cells_plain], [val_cells_intro]). *)
  Definition val_cells (m: mty) (fv: FValue) (w: Value) : iProp Σ := gtransit m fv w.

  Definition val_own {𝔄} (ty: type 𝔄) (x: ~~𝔄) (tid: thread_id) (v: val) : iProp Σ :=
    ∃ w d fv, ⌜v = MLitV w ∧ ty.(ty_fval) x = Some fv⌝ ∗ val_cells ty.(ty_mty) fv w ∗
      ⧖d ∗ ty.(ty_gho_own) x d d tid.
End value_ctx.

Notation "p ◁ᵥ ty" := (TCtx_sem _ p (val_own ty%T)) (at level 55).

(** * The reduction lemmas: values without cells *)
Section value_plain.
  Context `{!typeG Σ}.

  Lemma val_cells_plain m w0 w : val_cells m (fv_lift w0) w -∗ ⌜w = w0⌝.
  Proof. apply gtransit_lift_inv. Qed.

  Lemma val_cells_intro m w : mty_wf m → val_wf m w → ⊢ val_cells m (fv_lift w) w.
  Proof. intros _ Hw. by iApply gtransit_lift. Qed.

  Lemma val_cells_wf m fv w : val_cells m fv w -∗ ⌜val_wf m w⌝.
  Proof. apply gtransit_wf. Qed.

  Lemma ty_fval_val {𝔄} (ty: type 𝔄) x w : ty.(ty_val) x = Some w → ty.(ty_fval) x = Some (fv_lift w).
  Proof. rewrite -ty_val_eq -ty_fval_eq. apply syn_fval_val. Qed.

  (** A value with a MiniRust value [w0] (e.g. of a type without cells) has no cells in
      transit. *)
  Lemma val_own_val {𝔄} (ty: type 𝔄) x tid v w0 :
    ty.(ty_val) x = Some w0 →
    val_own ty x tid v ⊣⊢ ∃ d, ⌜v = MLitV w0⌝ ∗ ⧖d ∗ ty.(ty_gho_own) x d d tid.
  Proof.
    intros Hw0. have Hf := ty_fval_val ty x w0 Hw0. iSplit.
    - iIntros "(%w & %d & %fv & [-> %Hfv] & Hc & ⧖ & Gho)". rewrite Hf in Hfv.
      injection Hfv as <-. iDestruct (val_cells_plain with "Hc") as %->. iExists d. by iFrame.
    - iIntros "(%d & -> & ⧖ & Gho)". iExists w0, d, (fv_lift w0). iFrame. iSplit; [done|].
      iApply val_cells_intro; [apply ty_mty_wf|by eapply ty_val_wf].
  Qed.

  (** For a type without cells, [val_own] is the plain form: the MiniRust value. *)
  Lemma val_own_nocell {𝔄} `{!NoCell 𝔄} (ty: type 𝔄) x tid v :
    val_own ty x tid v ⊣⊢
      ∃ w d, ⌜v = MLitV w ∧ ty.(ty_val) x = Some w⌝ ∗ ⧖d ∗ ty.(ty_gho_own) x d d tid.
  Proof.
    iSplit.
    - iIntros "(%w & %d & %fv & [-> %Hfv] & Hc & ⧖ & Gho)".
      rewrite ty_fval_nocell // in Hfv. apply fmap_Some in Hfv as (w0 & Hw0 & ->).
      iDestruct (val_cells_plain with "Hc") as %->. iExists w0, d. by iFrame.
    - iIntros "(%w & %d & [-> %Hw] & ⧖ & Gho)". rewrite val_own_val //. iExists d. by iFrame.
  Qed.

  Lemma tctx_val_nocell {𝔄} `{!NoCell 𝔄} tid p (ty: type 𝔄) x :
    tctx_elt_interp tid (p ◁ᵥ ty) x ⊣⊢ ∃ v, ⌜eval_path p = Some v⌝ ∗
      ∃ w d, ⌜v = MLitV w ∧ ty.(ty_val) x = Some w⌝ ∗ ⧖d ∗ ty.(ty_gho_own) x d d tid.
  Proof. rewrite /tctx_elt_interp. by setoid_rewrite val_own_nocell. Qed.

  (** The plain form, as a wand (for [iDestruct]). *)
  Lemma tctx_val_elim {𝔄} `{!NoCell 𝔄} tid p (ty: type 𝔄) x :
    tctx_elt_interp tid (p ◁ᵥ ty) x -∗ ∃ v, ⌜eval_path p = Some v⌝ ∗
      ∃ w d, ⌜v = MLitV w ∧ ty.(ty_val) x = Some w⌝ ∗ ⧖d ∗ ty.(ty_gho_own) x d d tid.
  Proof. rewrite tctx_val_nocell. auto. Qed.

  Lemma tctx_val_intro {𝔄} tid p (ty: type 𝔄) x w d :
    eval_path p = Some (MLitV w) → ty.(ty_val) x = Some w →
    ⧖d -∗ ty.(ty_gho_own) x d d tid -∗ tctx_elt_interp tid (p ◁ᵥ ty) x.
  Proof.
    iIntros (Hp Hw) "⧖ Gho". iExists _. iSplit; [done|]. rewrite val_own_val //.
    iExists d. by iFrame.
  Qed.
  (** Introducing a value with a MiniRust value (in the form of the plain [val_own]). *)
  Lemma val_own_intro_sep {𝔄} (ty: type 𝔄) x tid v w d :
    v = MLitV w → ty.(ty_val) x = Some w →
    ⧖d ∗ ty.(ty_gho_own) x d d tid ⊢ val_own ty x tid v.
  Proof. iIntros (-> Hw) "[⧖ Gho]". rewrite val_own_val //. iExists d. by iFrame. Qed.

  (** A typed move out of the bytes of a value: a [Load] of the contents moves their cells
      out (which needs the registry of the cells and a credit). The location keeps plain
      bytes. *)
  Lemma wp_bytes_own_move {𝔄} E (ty: type 𝔄) l y :
    lazyE ∪ ↑gcellsN ⊆ E →
    {{{ gcells_ctx ∗ £ 1 ∗ bytes_own ty l y }}} Load Na1Ord ty.(ty_mty) #l @ E
    {{{ w fv bs, RET MLitV w; ⌜ty.(ty_fval) y = Some fv⌝ ∗ val_cells ty.(ty_mty) fv w ∗
        l ↦b bs ∗ ⌜length bs = ty_bsize ty⌝ }}}.
  Proof.
    iIntros (? Φ) "(#GC & Lc & Own) HΦ". iDestruct (bytes_own_fval with "Own") as %[fv Hfv].
    rewrite (bytes_own_gcont _ _ _ fv) //.
    iApply (wp_gcont_load_move with "[$GC $Lc $Own]"); [done|apply ty_mty_wf|].
    iIntros "!>" (w bs) "(Hbs & %Hlen & Tr)". iApply "HΦ". by iFrame.
  Qed.

  (** A typed [Store] of a value whose cells are in transit puts them back at the new
      location. *)
  Lemma wp_val_cells_store {𝔄} E (ty: type 𝔄) l bs0 e w y fv :
    lazyE ∪ ↑naN ⊆ E → IntoVal e (MLitV w) → ty.(ty_fval) y = Some fv → length bs0 = ty_bsize ty →
    {{{ ▷ l ↦b bs0 ∗ val_cells ty.(ty_mty) fv w }}} Store Na1Ord ty.(ty_mty) #l e @ E
    {{{ RET #☠; bytes_own ty l y }}}.
  Proof.
    iIntros (? <- Hfv Hlen Φ) "[Hbs Hc] HΦ".
    iApply (wp_gtransit_store with "[$Hbs $Hc]"); [done|apply ty_mty_wf|done|].
    iIntros "!> C". iApply "HΦ". by rewrite (bytes_own_gcont _ _ _ fv).
  Qed.
End value_plain.

(** * Values with cells built from parts

The cells in transit of a tuple (laid out in sequence, [seq_tuple]) or of a variant are
those of its parts: bytes that decode to the whole value split along its layout, and the
closer of each part puts its cells back at the offset of the part. *)
Section value_parts.
  Context `{!typeG Σ}.

  Lemma val_cells_seq_tuple_nil : ⊢ val_cells (seq_tuple []) (FVTuple []) (VTuple []).
  Proof. iApply (val_cells_intro _ (VTuple [])); [by apply seq_tuple_wf|by repeat constructor]. Qed.

  Lemma val_cells_seq_tuple_cons m ms fv fvs w ws :
    val_cells m fv w -∗ val_cells (seq_tuple ms) (FVTuple fvs) (VTuple ws) -∗
    val_cells (seq_tuple (m :: ms)) (FVTuple (fv :: fvs)) (VTuple (w :: ws)).
  Proof.
    rewrite /val_cells /gtransit. iIntros "[[%Hw %Hl] Cl] [[%Hws %Hls] Cls]". iSplit.
    - iPureIntro. split.
      + inversion Hws as [| | |? ? ? Hall|]; simplify_eq. constructor.
        apply (Forall2_layout_fields (λ m v, val_wf m v)). constructor; [done|].
        by apply (Forall2_layout_fields (λ m v, val_wf m v)) in Hall.
      + intros w0 Hw0. destruct (fv_lift_tuple_inv _ _ (eq_sym Hw0)) as (vs & -> & Hvs).
        destruct vs as [|v0 vs]; [done|]. injection Hvs as -> Hvs.
        have Hws' := Hls (VTuple vs) ltac:(by rewrite /= -Hvs). injection Hws' as ->.
        by rewrite (Hl v0).
    - iIntros (l' bs' Hd) "Hbs".
      move: Hd. rewrite decode_seq_tuple. case_decide as Hlen; [|done].
      intros (vs' & Hvs' & [= <-])%fmap_Some_1. simpl in Hvs'.
      destruct (decode_value m (take (mty_size m) bs')) as [v1|] eqn:H1; [|done]. simpl in Hvs'.
      destruct (decode_seq ms (drop (mty_size m) bs')) as [vs1|] eqn:H2; [|done].
      simpl in Hvs'. injection Hvs' as -> ->. rewrite seq_size_cons in Hlen.
      rewrite -{1}(take_drop (mty_size m) bs') heap_mapsto_bytes_app length_take Nat.min_l; [|lia].
      iDestruct "Hbs" as "[H1 H2]".
      iMod ("Cl" with "[//] H1") as "C1".
      iMod ("Cls" with "[] H2") as "C2".
      { iPureIntro. rewrite decode_seq_tuple length_drop decide_True; [|lia]. by rewrite H2. }
      iModIntro. rewrite gcont_seq_tuple_cons. iFrame.
  Qed.

  (** The contents of a variant: the bytes of its tag, the contents of its payload, and
      padding bytes. *)
  Lemma gcont_enum_intro l vars tag sz t vm fv bst bsp :
    length bst = int_size tag → decode_int tag bst = Some t → (0 ≤ t)%Z →
    vars !! Z.to_nat t = Some vm → (int_size tag + mty_size vm + length bsp = sz)%nat →
    l ↦b bst -∗ gcont (l +ₗ int_size tag) vm fv -∗
    (l +ₗ (int_size tag + mty_size vm)%nat) ↦b bsp -∗ gcont l (MEnum vars tag sz) (FVVariant t fv).
  Proof.
    iIntros (Hlt Ht Ht0 Hvm Hsz) "Ht (%R & %fbs & Hfb & [%Hrep %HR] & Hc) Hp".
    have Hlf := frepr_length _ _ _ _ HR Hrep.
    iExists R, ((inr <$> bst) ++ fbs ++ (inr <$> bsp)).
    rewrite !gfbytes_app !gfbytes_bytes length_fmap Hlt Hlf shift_loc_assoc_nat. iFrame.
    iSplit.
    - iPureIntro. split; [|done]. eapply (frepr_enum _ _ _ _ _ t vm fv bst); try done.
      + rewrite !length_app !length_fmap. lia.
      + rewrite take_app_length' // length_fmap //.
      + rewrite /list_slice drop_app_length' ?length_fmap // take_app_length' //.
      + intros i fb Hi Hge. rewrite lookup_app_r in Hi; [|rewrite length_fmap; lia].
        rewrite lookup_app_r in Hi; [|rewrite length_fmap; lia].
        rewrite list_lookup_fmap in Hi. destruct (bsp !! _); simplify_eq/=. by eexists.
    - rewrite gcells_enum Hvm. done.
  Qed.

  Lemma val_cells_enum vars tag sz t vm fv w :
    mty_wf (MEnum vars tag sz) → (0 ≤ t)%Z → vars !! Z.to_nat t = Some vm → int_in_range tag t →
    val_cells vm fv w -∗ val_cells (MEnum vars tag sz) (FVVariant t fv) (VVariant t w).
  Proof.
    rewrite /val_cells /gtransit. iIntros (Hwf Ht0 Hvm Hr) "[[%Hw %Hl] Cl]". iSplit.
    - iPureIntro. split; [by econstructor|].
      intros w0 Hw0. destruct (fv_lift_variant_inv _ _ _ (eq_sym Hw0)) as (dv & -> & ->).
      by rewrite (Hl dv).
    - iIntros (l' bs' Hd) "Hbs". move: Hd. rewrite decode_value_enum. case_decide as Hlen; [|done].
      destruct (decode_int tag (take (int_size tag) bs')) as [t'|] eqn:Ht; simpl; [|done].
      case_decide; [|done]. destruct (vars !! Z.to_nat t') as [vm'|] eqn:Hvm'; simpl; [|done].
      intros (d' & Hd & [= <- <-])%fmap_Some_1. rewrite Hvm in Hvm'. injection Hvm' as <-.
      inversion Hwf as [| | | |? ? ? Hvars Htag]; simplify_eq.
      destruct (Forall_lookup_1 _ _ _ _ Hvars Hvm) as [Hsz _].
      rewrite -(take_drop (int_size tag) bs') -(take_drop (mty_size vm) (drop (int_size tag) bs')).
      rewrite !heap_mapsto_bytes_app. iDestruct "Hbs" as "(Ht & Hp & Hr)".
      rewrite !length_take length_drop !Nat.min_l; [|lia..].
      iMod ("Cl" with "[] Hp") as "C"; [done|].
      iModIntro. iApply (gcont_enum_intro _ _ _ _ _ _ _ _ (drop (mty_size vm) (drop (int_size tag) bs')) with "Ht C [Hr]"); [by rewrite length_take; lia|done|done|done| |].
      + rewrite !length_app !length_take !length_drop. lia.
      + by rewrite shift_loc_assoc_nat.
  Qed.

  (** The value of a variant, from the value of its payload. *)
  Lemma val_own_pinj {𝔄l} (tyl: typel 𝔄l) (i: fin (length 𝔄l)) a tid w :
    val_own (tyl +!! i) a tid (MLitV w) -∗
    val_own (Σ! tyl) (pinj i a) tid (MLitV (VVariant (Z.of_nat (fin_to_nat i)) w)).
  Proof.
    iIntros "(%w' & %d & %fv & [%Hv %Hfv] & Hc & ⧖ & Gho)". injection Hv as <-.
    iExists _, d, _. iSplit.
    { iPureIntro. split; [done|]. rewrite -ty_fval_eq syn_fval_pinj (ty_fval_eq (tyl +!! i)) Hfv //. }
    iFrame "⧖". iSplitL "Hc".
    - rewrite -!ty_mty_eq. change (syn_mty (Σ! 𝔄l)) with (seq_enum (syn_mty <$> 𝔄l)).
      iApply (val_cells_enum with "Hc"); [apply (syn_mty_wf (Σ! 𝔄l))|lia| |].
      + rewrite Nat2Z.id list_lookup_fmap llookup_lookup //.
      + rewrite length_fmap. apply enum_tag_in_range, fin_to_nat_lt.
    - rewrite [ty_gho_own (Σ! tyl)]/ty_gho_own /xsum_ty /= to_xsum_pinj. done.
  Qed.

  (** The value of a pair, from the values of its components. *)
  Lemma val_own_pair {𝔄 𝔅} (ty1: type 𝔄) (ty2: type 𝔅) a b tid w1 w2 :
    val_own ty1 a tid (MLitV w1) -∗ val_own ty2 b tid (MLitV w2) -∗
    val_own (ty1 * ty2) (a, b) tid (MLitV (VTuple [w1; w2])).
  Proof.
    iIntros "(%w1' & %d1 & %fv1 & [%Hv1 %Hfv1] & Hc1 & ⧖1 & Gho1)
      (%w2' & %d2 & %fv2 & [%Hv2 %Hfv2] & Hc2 & ⧖2 & Gho2)". injection Hv1 as <-. injection Hv2 as <-.
    iExists _, (d1 `max` d2)%nat, (FVTuple [fv1; fv2]). iSplit.
    { iPureIntro. split; [done|]. rewrite -!ty_fval_eq in Hfv1 Hfv2 |- *. by rewrite /= Hfv1 Hfv2. }
    iCombine "⧖1 ⧖2" as "$". iSplitL "Hc1 Hc2".
    - rewrite -!ty_mty_eq. change (syn_mty (𝔄 * 𝔅)) with (seq_tuple [syn_mty 𝔄; syn_mty 𝔅]).
      iApply (val_cells_seq_tuple_cons with "Hc1").
      iApply (val_cells_seq_tuple_cons with "Hc2"). iApply val_cells_seq_tuple_nil.
    - iSplitL "Gho1".
      + iDestruct (ty_gho_own_depth_mono _ d1 d1 (d1 `max` d2) (d1 `max` d2) with "Gho1") as "[$ _]"; lia.
      + iDestruct (ty_gho_own_depth_mono _ d2 d2 (d1 `max` d2) (d1 `max` d2) with "Gho2") as "[$ _]"; lia.
  Qed.

  (** The value of a tuple [Π! (ty :: tyl)], from the value of its first component and the
      tuple of the others. *)
  Lemma val_own_xprod_nil tid : ⧖0 -∗ val_own (Π! +[]) -[] tid (MLitV (VTuple [])).
  Proof.
    iIntros "⧖". iExists (VTuple []), 0%nat, (FVTuple []). iSplit.
    { iPureIntro. split; [done|]. by rewrite -ty_fval_eq. }
    iFrame "⧖". rewrite -ty_mty_eq. iApply val_cells_seq_tuple_nil.
  Qed.

  Lemma val_own_xprod_cons {𝔄 𝔄l} (ty: type 𝔄) (tyl: typel 𝔄l) a al tid w ws :
    val_own ty a tid (MLitV w) -∗ val_own (Π! tyl) al tid (MLitV (VTuple ws)) -∗
    val_own (Π! (ty +:: tyl)) (a -:: al) tid (MLitV (VTuple (w :: ws))).
  Proof.
    iIntros "(%w1' & %d1 & %fv1 & [%Hv1 %Hfv1] & Hc1 & ⧖1 & Gho1)
      (%w2' & %d2 & %fv2 & [%Hv2 %Hfv2] & Hc2 & ⧖2 & Gho2)". injection Hv1 as <-. injection Hv2 as <-.
    rewrite -!ty_fval_eq in Hfv1 Hfv2. rewrite -!ty_mty_eq.
    change (syn_mty (Π! 𝔄l)) with (seq_tuple (syn_mty <$> 𝔄l)) in *.
    change (syn_fval (𝔄:=Π! 𝔄l) al) with
      (FVTuple <$> mapM id (plist_to_list (pmap (λ _ x0, syn_fval x0) al))) in Hfv2.
    destruct (mapM id _) as [fvs|] eqn:Hfvs; [|done]. injection Hfv2 as <-.
    iExists _, (d1 `max` d2)%nat, (FVTuple (fv1 :: fvs)). iSplit.
    { iPureIntro. split; [done|]. rewrite -ty_fval_eq.
      change (syn_fval (𝔄:=Π! (𝔄 :: 𝔄l)) (a -:: al)) with
        (FVTuple <$> mapM id (syn_fval a :: plist_to_list (pmap (λ _ x0, syn_fval x0) al))).
      by rewrite /= Hfv1 Hfvs. }
    iCombine "⧖1 ⧖2" as "$". iSplitL "Hc1 Hc2".
    - change (syn_mty (Π! (𝔄 :: 𝔄l))) with (seq_tuple (syn_mty 𝔄 :: (syn_mty <$> 𝔄l))).
      iApply (val_cells_seq_tuple_cons with "Hc1 Hc2").
    - rewrite [ty_gho_own (Π! (ty +:: tyl))]/ty_gho_own /=. iSplitL "Gho1".
      + iDestruct (ty_gho_own_depth_mono _ d1 d1 (d1 `max` d2) (d1 `max` d2) with "Gho1") as "[$ _]"; lia.
      + iDestruct (ty_gho_own_depth_mono _ d2 d2 (d1 `max` d2) (d1 `max` d2) with "Gho2") as "[$ _]"; lia.
  Qed.
End value_parts.

Section value_rules.
  Context `{!typeG Σ}.

  Lemma tctx_val_val {𝔄} `{!NoCell 𝔄} tid (w: Value) (ty: type 𝔄) x :
    tctx_elt_interp tid (MLitV w ◁ᵥ ty) x ⊣⊢
      ∃ d, ⌜ty.(ty_val) x = Some w⌝ ∗ ⧖d ∗ ty.(ty_gho_own) x d d tid.
  Proof.
    rewrite tctx_val_nocell eval_path_of_val. iSplit.
    - iIntros "(%v & %Hv & %w' & %d & [%Hw %Hx] & ⧖ & Gho)". simplify_eq. iExists d. by iFrame.
    - iIntros "(%d & %Hx & ⧖ & Gho)". iExists _. iSplit; [done|]. iExists w, d. by iFrame.
  Qed.

  Lemma wp_val {𝔄} `{!NoCell 𝔄} E tid p (ty: type 𝔄) x Φ :
    tctx_elt_interp tid (p ◁ᵥ ty) x -∗
    (∀ w d, ⌜eval_path p = Some (MLitV w)⌝ -∗ ⌜ty.(ty_val) x = Some w⌝ -∗ ⧖d -∗
      ty.(ty_gho_own) x d d tid -∗ Φ (MLitV w)) -∗
    WP p @ E {{ Φ }}.
  Proof.
    rewrite tctx_val_nocell. iIntros "(%v & %Hp & %w & %d & [-> %Hx] & ⧖ & Gho) ToΦ".
    iApply (wp_wand with "[]"); [by iApply wp_eval_path|].
    iIntros (? ->). by iApply ("ToΦ" with "[//] [//] ⧖ Gho").
  Qed.

  (** Evaluating a value that may have cells in transit. *)
  Lemma wp_val_cells {𝔄} E tid p (ty: type 𝔄) x Φ :
    tctx_elt_interp tid (p ◁ᵥ ty) x -∗
    (∀ w d fv, ⌜eval_path p = Some (MLitV w)⌝ -∗ ⌜ty.(ty_fval) x = Some fv⌝ -∗
      val_cells ty.(ty_mty) fv w -∗ ⧖d -∗ ty.(ty_gho_own) x d d tid -∗ Φ (MLitV w)) -∗
    WP p @ E {{ Φ }}.
  Proof.
    iIntros "(%v & %Hp & %w & %d & %fv & [-> %Hx] & Hc & ⧖ & Gho) ToΦ".
    iApply (wp_wand with "[]"); [by iApply wp_eval_path|].
    iIntros (? ->). by iApply ("ToΦ" with "[//] [//] Hc ⧖ Gho").
  Qed.

  (** Duplicating a value of a [Copy] type. *)
  Lemma copy_val_tctx_incl {𝔄 𝔄l} (ty: type 𝔄) `{!Copy ty} (T: tctx 𝔄l) p E L :
    tctx_incl E L (p ◁ᵥ ty +:: T) (p ◁ᵥ ty +:: p ◁ᵥ ty +:: T)
      (λ post '(a -:: al), post (a -:: a -:: al)).
  Proof.
    split; [by intros ??? [??]|].
    iIntros (??[a al]???) "_ _ _ _ _ $ /=[p T] Obs !>".
    iDestruct (tctx_val_elim with "p") as "(%v & %Hp & %w & %d & [-> %Hw] & #⧖ & #Gho)".
    iExists (a -:: a -:: al). iFrame "Obs T".
    iSplitR; by iApply (tctx_val_intro with "⧖ Gho").
  Qed.

  (** An integer literal. *)
  Lemma type_val_int_instr it (z: Z) E L I :
    int_in_range it z →
    typed_instr E L I +[] (MLit (VInt z)) (λ v, +[v ◁ᵥ int_ty it]) (λ post _, post -[z]).
  Proof.
    iIntros (Hz ?????) "_ _ _ _ _ $$ _ Obs". iMod persistent_time_receipt_0 as "⧖".
    iApply wp_value. iExists -[z]. iFrame "Obs". iSplit; [|done].
    rewrite tctx_val_val. iExists 0%nat. iFrame "⧖". iPureIntro. by apply int_ty_val.
  Qed.

  (** The unit value [()]: an empty tuple. *)
  Lemma type_val_unit_instr E L I :
    typed_instr E L I +[] (MkTuple []) (λ v, +[v ◁ᵥ ()]) (λ post _, post -[()]).
  Proof.
    iIntros (?????) "_ _ _ _ _ $$ _ Obs". iMod persistent_time_receipt_0 as "⧖".
    eapply (tac_wp_pure []); [apply (pure_mk_tuple [])|done|tc_solve|simpl; iApply wp_value].
    iExists -[()]. iFrame "Obs". iSplit; [|done].
    rewrite tctx_val_val. iExists 0%nat. by iFrame "⧖".
  Qed.

  (** Evaluating a value, with its ownership (whose cells may be in transit). *)
  Lemma wp_val_own {𝔄} E tid p (ty: type 𝔄) x Φ :
    tctx_elt_interp tid (p ◁ᵥ ty) x -∗
    (∀ w, val_own ty x tid (MLitV w) -∗ Φ (MLitV w)) -∗ WP p @ E {{ Φ }}.
  Proof.
    iIntros "(%v & %Hp & Own) ToΦ". iDestruct "Own" as (w d fv [-> Hx]) "Own".
    iApply (wp_wand with "[]"); [by iApply wp_eval_path|].
    iIntros (? ->). iApply "ToΦ". iExists w, d, fv. by iFrame.
  Qed.

  (** A variant value: the payload (which may contain cells) with the index of the
      variant. *)
  Lemma type_mk_variant_val_instr {𝔄l} (tyl: typel 𝔄l) (i: fin (length 𝔄l)) (t: Z) p E L I :
    t = Z.of_nat (fin_to_nat i) →
    typed_instr E L I +[p ◁ᵥ tyl +!! i] (MkVariant t p) (λ v, +[v ◁ᵥ Σ! tyl])
      (λ post '-[a], post -[pinj i a]).
  Proof.
    iIntros (-> tid post mask iκs [a []]) "_ _ _ _ _ $$ [p _] Obs".
    wp_bind p. iApply (wp_val_own with "p"). iIntros (w) "Own".
    wp_pure _. iExists -[pinj i a]. iSplitR "Obs".
    - iSplit; [|done]. iExists _. iSplit; [by rewrite eval_path_of_val|]. by iApply val_own_pinj.
    - iApply proph_obs_impl; [|done]=> π. by apply.
  Qed.

  (** A pair value, from its components (which may contain cells). *)
  Lemma type_mk_pair_val_instr {𝔄 𝔅} (ty1: type 𝔄) (ty2: type 𝔅) p1 p2 E L I :
    typed_instr E L I +[p1 ◁ᵥ ty1; p2 ◁ᵥ ty2] (MkTuple [p1; p2]) (λ v, +[v ◁ᵥ ty1 * ty2])
      (λ post '-[a; b], post -[(a, b)]).
  Proof.
    iIntros (tid post mask iκs [a [b []]]) "_ _ _ _ _ $$ (p1 & p2 & _) Obs".
    wp_bind p1. iApply (wp_val_own with "p1"). iIntros (w1) "Own1".
    wp_bind p2. iApply (wp_val_own with "p2"). iIntros (w2) "Own2".
    eapply (tac_wp_pure []); [apply (pure_mk_tuple [w1; w2])|done|tc_solve|simpl; iApply wp_value].
    iExists -[(a, b)]. iFrame "Obs". iSplit; [|done]. iExists _. iSplit; [by rewrite eval_path_of_val|].
    iApply (val_own_pair with "Own1 Own2").
  Qed.

  Local Lemma wp_mk_tuple_val {𝔄l} (tyl: typel 𝔄l) (pl: plistc path 𝔄l) ws al tid E Φ :
    tctx_interp tid (hzip_with (λ _ ty q, q ◁ᵥ ty) tyl pl) al -∗
    (∀ ws', val_own (Π! tyl) al tid (MLitV (VTuple ws')) -∗
      WP MkTuple (MLit <$> (ws ++ ws')) @ E {{ Φ }}) -∗
    WP MkTuple ((MLit <$> ws) ++ pl) @ E {{ Φ }}.
  Proof.
    revert ws. induction tyl as [|𝔄 𝔄l ty tyl IH]; intros ws.
    { iIntros "_ Wp". iMod persistent_time_receipt_0 as "⧖".
      iSpecialize ("Wp" $! [] with "[⧖]"); [by iApply (val_own_xprod_nil tid)|]. by rewrite !app_nil_r. }
    destruct pl as [p pl], al as [a al]. iIntros "[p pl] Wp".
    have ->: MkTuple ((MLit <$> ws) ++ p :: pl) = fill_item (MkTupleCtx (MLitV <$> ws) pl) p.
    { by rewrite /= -list_fmap_compose. }
    iApply wp_bind. iApply (wp_val_own with "p"). iIntros (w) "Own".
    have ->: fill_item (MkTupleCtx (MLitV <$> ws) pl) (MLitV w) =
      MkTuple ((MLit <$> (ws ++ [w])) ++ pl).
    { by rewrite /= -list_fmap_compose fmap_app -assoc. }
    iApply (IH with "pl"). iIntros (ws') "Own'". rewrite -assoc /=.
    iApply ("Wp" $! (w :: ws')). iApply (val_own_xprod_cons with "Own Own'").
  Qed.

  (** A tuple value, from its components (which may contain cells). *)
  Lemma type_mk_tuple_val_instr {𝔄l} (tyl: typel 𝔄l) (pl: plistc path 𝔄l) el E L I :
    IntoPlistc el pl →
    typed_instr E L I (hzip_with (λ _ ty q, q ◁ᵥ ty) tyl pl) (MkTuple el)
      (λ v, +[v ◁ᵥ Π! tyl]) (λ post al, post -[al]).
  Proof.
    move=> ->. iIntros (tid post mask iκs al) "_ _ _ _ _ $$ T Obs".
    iApply (wp_mk_tuple_val _ _ [] with "T"). iIntros (ws) "Own".
    eapply (tac_wp_pure []); [apply (pure_mk_tuple ws)|done|tc_solve|simpl; iApply wp_value].
    iExists -[al]. iFrame "Obs". iSplit; [|done]. iExists _. iSplit; [by rewrite eval_path_of_val|].
    done.
  Qed.

  (** Reading the pointee of a box of a [Copy] type: a typed [Load]. *)
  Lemma type_load_own_bytes_copy_instr {𝔄} n (ty: type 𝔄) p E L I :
    Copy ty →
    typed_instr E L I +[p ◁ᵥ own_bytes n ty] (Load Na1Ord ty.(ty_mty) p)
      (λ v, +[p ◁ᵥ own_bytes n ty; v ◁ᵥ ty]) (λ post '-[a], post -[a; a.2]).
  Proof.
    intros Hcopy0. assert (NoCell 𝔄) by exact (copy_nocell ty). revert Hcopy0.
    iIntros (? tid post mask iκs [[l x] []]) "_ #TIME _ _ _ $ $ [p _] Obs".
    wp_bind p. iApply (wp_val with "p"). iIntros (w d Hp Hw) "#⧖ Own".
    simpl in Hw. simplify_eq. cbn [of_val].
    destruct d as [|d]; [done|]. iDestruct "Own" as "(Bytes & Free & Gho)".
    iDestruct (bytes_own_nocell_bytes with "Bytes") as (bs) "[Hbs %Hbs]".
    destruct (ty_bytes_val _ _ _ Hbs) as [v Hv].
    iApply (wp_persistent_time_receipt with "TIME ⧖"); [done|]. iIntros "£ _".
    iDestruct (lc_weaken 1 with "£") as "£"; [rewrite /advance_credits; lia|].
    iMod (lc_fupd_elim_later with "£ Gho") as "#Gho".
    iApply wp_fupd. iApply (wp_load_na with "Hbs"); [by eapply ty_bytes_decode|].
    iIntros "!> Hbs !>". iExists -[(l, x); x]. iFrame "Obs". simpl.
    iDestruct (ty_gho_own_depth_mono _ d (S d) (S d) (S d) with "Gho") as "[#Gho' _]"; [lia..|].
    iSplitL "Hbs Free".
    - iExists _. iSplit; [done|]. rewrite -(val_own_intro_sep _ _ _ _ (VPtr l) (S d)); [|done|done]. iFrame "⧖ Free".
      iSplitL "Hbs"; [by iApply bytes_own_of_bytes|]. done.
    - iSplit; [|done]. iExists _. iSplit; [done|]. rewrite -(val_own_intro_sep _ _ _ _ v (S d)); [|done|done].
      iFrame "⧖ Gho'".
  Qed.

  (** Resolving a value. *)
  Lemma type_resolve_val_instr {𝔄} p (ty: type 𝔄) Φ E L I :
    resolve E L ty Φ →
    typed_instr E L I +[p ◁ᵥ ty] Skip (λ _, +[]) (λ post '-[a], λ mask π, Φ a π → post -[] mask π).
  Proof.
    iIntros (Rslv ????[?[]]) "LFT #TIME PROPH UNIQ E L I /=[(%v & %Hp & %w & %d & %fv & _ & _ & ⧖ & tygho) _] Obs".
    iMod (llctx_interp_make_guarded with "L") as (γ) "[H1 [H2 [#Ghalf #Halfback]]]". { solve_ndisj. }
    iDestruct (Rslv _ (⊤∖↑advN) with "LFT PROPH UNIQ TIME E Ghalf H1 tygho") as "Upd"; [solve_ndisj|].
    iApply (wp_persistent_time_receipt with "TIME ⧖"); [solve_ndisj|]. iIntros "£ ⧖S".
    iMod "Upd".
    iMod (lc_step_fupdN_elim_later with "[£] Upd") as "Upd".
    { iApply (lc_weaken with "£"). unfold advance_credits. lia. }
    iMod "Upd" as "[Obs' H1]".
    iDestruct ("Halfback" with "H1 H2") as "L". iMod (fupd_mask_mono with "L") as "L". { solve_ndisj. }
    wp_seq.
    iExists -[]. iCombine "Obs Obs'" as "?".
    rewrite left_id. iFrame "L I". iApply proph_obs_impl; [|done]=>/= ?[Imp ?]. by apply Imp.
  Qed.

  (** Branching on a boolean value: [if:] cases on the MiniRust boolean. *)
  Lemma type_if_val {𝔄l 𝔅l ℭ} p (T: tctx 𝔄l) (T': tctx 𝔅l) e1 e2 tr1 tr2 trx E L I
      (C: cctx ℭ) :
    tctx_extract_ctx E L +[p ◁ᵥ bool_ty] T T' trx →
    typed_body E L I C T' e1 tr1 -∗ typed_body E L I C T' e2 tr2 -∗
    typed_body E L I C T (if: p then e1 else e2)
      (trx ∘ (λ post '(b -:: vl), if b then tr1 post vl else tr2 post vl)).
  Proof.
    iIntros (?) "e1 e2". iApply typed_body_tctx_incl; [done|]=>/=.
    iIntros (?[b ?]???) "/= #LFT #TIME #PROPH #UNIQ #E L I C [p T] Obs".
    wp_bind p. iApply (wp_val with "p"). iIntros (w d _ Hw) "_ _".
    simpl in Hw. simplify_eq.
    destruct b; wp_if.
    - iApply ("e1" with "LFT TIME PROPH UNIQ E L I C T").
      iApply (proph_obs_impl with "Obs"). intros π. done.
    - iApply ("e2" with "LFT TIME PROPH UNIQ E L I C T").
      iApply (proph_obs_impl with "Obs"). intros π. done.
  Qed.

  Lemma resolve_tctx_cons_val {𝔄 𝔅l} E L p (ty: type 𝔄) Φ (T: tctx 𝔅l) Ψ :
    resolve E L ty Φ → resolve_tctx E L T Ψ →
    resolve_tctx E L (p ◁ᵥ ty +:: T) (λ '(a -:: bl) π φ, Φ a π → Ψ bl π φ).
  Proof.
    iIntros (Rslv Rslv' ???[??]??).
    iIntros "#LFT #PROPH #UNIQ #TIME #E #L G /=[(%v & _ & %w & %d & %fv & _ & _ & ⧖ & ty) T]".
    iMod (fractional.frac_split_guard_in_half NllftG with "G L")
        as (γ) "[F1 [F2 [#guards #back]]]". { solve_ndisj. }
    iMod (Rslv with "LFT PROPH UNIQ TIME E guards F1 ty") as "ToObs"; [set_solver|].
    iMod (Rslv' with "LFT PROPH UNIQ TIME E guards F2 T") as (?) "[⧖' ToObs']"; [done|].
    iCombine "⧖ ⧖'" as "⧖". iCombine "ToObs ToObs'" as "ToObs".
    iModIntro. iExists _. iFrame "⧖".
    rewrite lemma_max_mul.
    iApply (step_fupdN_wand with "ToObs").
    iIntros "[>[Obs F1] >[Obs' F2]]".
    iDestruct ("back" with "F1 F2") as "G". iMod (fupd_mask_mono with "G") as "G". { solve_ndisj. }
    iCombine "Obs Obs'" as "?".
    iModIntro. iFrame "G".
    iApply proph_obs_impl; [|done]=>/= ?[? Imp]? Imp'. apply Imp, Imp'. trivial.
  Qed.
End value_rules.
