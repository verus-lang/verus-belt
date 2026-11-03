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
[val_own_intro_sep]). It is a semantic element ([TCtx_sem]), so the type context needs no
new case. (The legacy word element [p ◁ ty] was deleted in
stage 6.)

Pointers are MiniRust values too ([VPtr l]); the address argument of [Load], [Store],
[MemCopy] and of the offset [+ₗ] is a legacy literal [#l], which [ToLit] gives. *)

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

  (** A variant value: the payload (without cells) with the index of the variant. *)
  Lemma type_mk_variant_val_instr {𝔄l} (tyl: typel 𝔄l) (i: fin (length 𝔄l)) `{!NoCell (𝔄l !!ₗ i)}
      (t: Z) p E L I :
    t = Z.of_nat (fin_to_nat i) →
    typed_instr E L I +[p ◁ᵥ tyl +!! i] (MkVariant t p) (λ v, +[v ◁ᵥ Σ! tyl])
      (λ post '-[a], post -[pinj i a]).
  Proof.
    iIntros (-> tid post mask iκs [a []]) "_ _ _ _ _ $$ [p _] Obs".
    wp_bind p. iApply (wp_val with "p"). iIntros (w d Hp Hw) "⧖ Gho".
    wp_pure _. iExists -[pinj i a]. iSplitR "Obs".
    - iSplit; [|done]. iApply (tctx_val_intro with "⧖ [Gho]"); [by rewrite eval_path_of_val| |].
      + rewrite -ty_val_eq syn_val_pinj (ty_val_eq (tyl +!! i)) Hw //.
      + rewrite [ty_gho_own (Σ! tyl)]/ty_gho_own /xsum_ty /= to_xsum_pinj. done.
    - iApply proph_obs_impl; [|done]=> π. by apply.
  Qed.

  (** Reading the pointee of a box of a [Copy] type: a typed [Load]. *)
  Lemma type_load_own_bytes_copy_instr {𝔄} n (ty: type 𝔄) p E L I :
    Copy ty →
    typed_instr E L I +[p ◁ᵥ own_bytes n ty] (Load Na1Ord ty.(ty_mty) (ToLit p))
      (λ v, +[p ◁ᵥ own_bytes n ty; v ◁ᵥ ty]) (λ post '-[a], post -[a; a.2]).
  Proof.
    intros Hcopy0. assert (NoCell 𝔄) by exact (copy_nocell ty). revert Hcopy0.
    iIntros (? tid post mask iκs [[l x] []]) "_ #TIME _ _ _ $ $ [p _] Obs".
    wp_bind p. iApply (wp_val with "p"). iIntros (w d Hp Hw) "#⧖ Own".
    simpl in Hw. simplify_eq. wp_pure _.
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

  (** Branching on a boolean value. [ToLit] turns the MiniRust boolean into the literal
      that [if:] cases on. *)
  Lemma type_if_val {𝔄l 𝔅l ℭ} p (T: tctx 𝔄l) (T': tctx 𝔅l) e1 e2 tr1 tr2 trx E L I
      (C: cctx ℭ) :
    tctx_extract_ctx E L +[p ◁ᵥ bool_ty] T T' trx →
    typed_body E L I C T' e1 tr1 -∗ typed_body E L I C T' e2 tr2 -∗
    typed_body E L I C T (if: ToLit p then e1 else e2)
      (trx ∘ (λ post '(b -:: vl), if b then tr1 post vl else tr2 post vl)).
  Proof.
    iIntros (?) "e1 e2". iApply typed_body_tctx_incl; [done|]=>/=.
    iIntros (?[b ?]???) "/= #LFT #TIME #PROPH #UNIQ #E L I C [p T] Obs".
    wp_bind p. iApply (wp_val with "p"). iIntros (w d _ Hw) "_ _".
    simpl in Hw. simplify_eq. wp_pure _.
    destruct b; wp_case.
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
