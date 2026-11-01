From lrust.typing Require Export type type_context bytes_layout.
From lrust.typing Require Import programs bool int own product sum.
From lrust.lifetime Require Import lifetime_full.
From guarding Require Import guard tactics.
Set Default Proof Using "Type".

(** * Typing MiniRust values (stage 4 of the MiniRust memory model)

The element [p ◁ᵥ ty] types a path that evaluates to a MiniRust value [MLitV w], the
MiniRust value of [x] ([ty_val x = Some w]): it is the result of a typed [Load] of
[ty_mty ty] and the argument of a typed [Store]. It is a semantic element ([TCtx_sem]),
so the type context needs no new case. (The legacy word element [p ◁ ty] was deleted in
stage 6.)

Pointers are MiniRust values too ([VPtr l]); the address argument of [Load], [Store],
[MemCopy] and of the offset [+ₗ] is a legacy literal [#l], which [ToLit] gives. *)

Implicit Type 𝔄 𝔅: syn_type.

Section value_ctx.
  Context `{!typeG Σ}.

  (** The cells of a MiniRust value [w] in transit: [w] is the decoding (at [m]) of bytes
      [bs] whose byte-cells, at the positions of the fancy bytes [fbs] that represent the
      fancy value [fv], are in transit ([unt_fbytes]). This is what a typed [Load] of the
      fancy bytes of [fv] gives ([wp_fbytes_load]), and what a typed [Store] of [w] needs to
      retether the cells ([wp_fbytes_store]). The cells (and the cells nested in them) are
      frozen while in transit: their final bytes are those of [bs]. For a value without
      cells, this is just [w = ⌊fv⌋] ([val_cells_plain], [val_cells_intro]). *)
  Definition val_cells (m: mty) (fv: FValue) (w: Value) : iProp Σ :=
    ∃ fbs bs, ⌜decode_value m bs = Some w⌝ ∗ brepr m fbs fv ∗ unt_fbytes fbs bs.

  Definition val_own {𝔄} (ty: type 𝔄) (x: ~~𝔄) (tid: thread_id) (v: val) : iProp Σ :=
    ∃ w d fv, ⌜v = MLitV w ∧ ty.(ty_fval) x = Some fv⌝ ∗ val_cells ty.(ty_mty) fv w ∗
      ⧖d ∗ ty.(ty_gho_own) x d d tid.
End value_ctx.

Notation "p ◁ᵥ ty" := (TCtx_sem _ p (val_own ty%T)) (at level 55).

(** * The reduction lemmas: values without cells *)
Section value_plain.
  Context `{!typeG Σ}.

  Lemma unt_fbytes_plain bs0 bs : unt_fbytes (inr <$> bs0) bs -∗ ⌜bs = bs0⌝.
  Proof.
    iIntros "H". iInduction bs0 as [|b0 bs0] "IH" forall (bs); destruct bs as [|b bs];
      try by iDestruct (big_sepL2_length with "H") as %?.
    rewrite /unt_fbytes fmap_cons big_sepL2_cons. iDestruct "H" as "[%Hb H]".
    iDestruct ("IH" with "H") as %->. by subst.
  Qed.

  Lemma unt_fbytes_plain_intro bs : ⊢ unt_fbytes (inr <$> bs) bs.
  Proof.
    iInduction bs as [|b bs] "IH"; [by rewrite /unt_fbytes|].
    rewrite /unt_fbytes fmap_cons big_sepL2_cons. iSplit; [done|]. iApply "IH".
  Qed.

  Lemma val_cells_plain m w0 w : val_cells m (fv_lift w0) w -∗ ⌜w = w0⌝.
  Proof.
    iIntros "(%fbs & %bs & %Hd & Hrep & Hus)".
    iDestruct (brepr_plain_inv with "Hrep") as %(bs0 & -> & Hd0).
    iDestruct (unt_fbytes_plain with "Hus") as %->. iPureIntro. congruence.
  Qed.

  Lemma val_cells_intro m w : mty_wf m → val_wf m w → ⊢ val_cells m (fv_lift w) w.
  Proof.
    iIntros (Hm Hw). iExists (inr <$> encode_value m w), (encode_value m w).
    iSplit; [iPureIntro; by apply decode_encode_value|]. iSplit.
    - iApply brepr_plain. by apply decode_encode_value.
    - iApply unt_fbytes_plain_intro.
  Qed.

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
  Lemma tctx_val_intro_sep {𝔄} tid p (ty: type 𝔄) x w d :
    eval_path p = Some (MLitV w) → ty.(ty_val) x = Some w →
    ⧖d ∗ ty.(ty_gho_own) x d d tid ⊢ tctx_elt_interp tid (p ◁ᵥ ty) x.
  Proof. iIntros (Hp Hw) "[⧖ Gho]". by iApply (tctx_val_intro with "⧖ Gho"). Qed.

  (** Introducing a value with a MiniRust value (in the form of the plain [val_own]). *)
  Lemma val_own_intro_sep {𝔄} (ty: type 𝔄) x tid v w d :
    v = MLitV w → ty.(ty_val) x = Some w →
    ⧖d ∗ ty.(ty_gho_own) x d d tid ⊢ val_own ty x tid v.
  Proof. iIntros (-> Hw) "[⧖ Gho]". rewrite val_own_val //. iExists d. by iFrame. Qed.

  (** A typed move out of the bytes of a value: a [Load] of the fancy bytes untethers their
      cells. The location keeps plain bytes. *)
  Lemma wp_bytes_own_move {𝔄} E (ty: type 𝔄) l y :
    ↑naN ⊆ E →
    {{{ bytes_own ty l y }}} Load Na1Ord ty.(ty_mty) #l @ E
    {{{ w fv bs, RET MLitV w; ⌜ty.(ty_fval) y = Some fv⌝ ∗ val_cells ty.(ty_mty) fv w ∗
        l ↦b bs ∗ ⌜length bs = ty_bsize ty⌝ }}}.
  Proof.
    iIntros (? Φ) "Own HΦ". rewrite bytes_own_brepr.
    iDestruct "Own" as (fbs fv) "(Hfbs & [%Hlenf %Hfv] & #Hrep)".
    iApply (wp_fbytes_load with "[$Hfbs $Hrep]"); [done|].
    iIntros "!>" (w bs) "(Hbs & %Hd & Hus)". iApply "HΦ". iFrame "Hbs". iSplit; [done|].
    iSplitL; [iExists fbs, bs; by iFrame "Hrep Hus"|].
    iPureIntro. by rewrite (decode_value_length _ _ _ Hd).
  Qed.

  (** A typed [Store] of a value whose cells are in transit retethers them. *)
  Lemma wp_val_cells_store {𝔄} E (ty: type 𝔄) l bs0 e w y fv :
    ↑naN ⊆ E → IntoVal e (MLitV w) → ty.(ty_fval) y = Some fv → length bs0 = ty_bsize ty →
    {{{ ▷ l ↦b bs0 ∗ val_cells ty.(ty_mty) fv w }}} Store Na1Ord ty.(ty_mty) #l e @ E
    {{{ RET #☠; bytes_own ty l y }}}.
  Proof.
    iIntros (? ? Hfv Hlen Φ) "[Hbs Hc] HΦ". iDestruct "Hc" as (fbs bs Hd) "[#Hrep Hus]".
    iDestruct (big_sepL2_length with "Hus") as %Hlenu.
    iApply (wp_fbytes_store with "[$Hbs $Hus $Hrep]"); [done|apply ty_mty_wf|done|done|].
    iIntros "!>" (fbs') "(Hfbs & #Hrep' & %Hlen')". iApply "HΦ".
    rewrite bytes_own_brepr. iExists fbs', fv. iFrame "Hfbs Hrep'". iPureIntro.
    split; [|done]. rewrite Hlen' Hlenu (decode_value_length _ _ _ Hd) //.
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

  (** A variant value: the payload with the index of the variant. *)
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
    - rewrite -(tctx_val_intro_sep _ _ _ _ (VPtr l) (S d)); [|done|done]. iFrame "⧖ Free".
      iSplitL "Hbs"; [by iApply bytes_own_of_bytes|]. done.
    - iSplit; [|done]. rewrite -(tctx_val_intro_sep _ _ _ _ v (S d)); [|done|done].
      iFrame "⧖ Gho'".
  Qed.

  (** Writing the pointee of a box: a typed [Store]. The old pointee is dropped. *)
  Lemma type_store_own_bytes_instr {𝔄} n (ty: type 𝔄) p q E L I :
    typed_instr E L I +[p ◁ᵥ own_bytes n ty; q ◁ᵥ ty] (Store Na1Ord ty.(ty_mty) (ToLit p) q)
      (λ _, +[p ◁ᵥ own_bytes n ty]) (λ post '-[a; b], post -[(a.1, b)]).
  Proof.
    iIntros (tid post mask iκs [[l x] [y []]]) "_ #TIME _ _ _ $ $ (p & q & _) Obs".
    wp_bind p. iApply (wp_val with "p"). iIntros (w d Hp Hw) "#⧖ Own".
    simpl in Hw. simplify_eq. wp_pure _.
    wp_bind q. iApply (wp_val_cells with "q"). iIntros (v d' fv Hq Hfv) "Hc #⧖' Gho'".
    destruct d as [|d]; [done|]. iDestruct "Own" as "(Bytes & Free & _)".
    iApply (wp_persistent_time_receipt with "TIME ⧖'"); [done|]. iIntros "_ #⧖S".
    iApply wp_fupd. iApply (wp_bytes_own_forget with "Bytes"); [solve_ndisj|].
    iIntros (bs) "Hbs %Hlen".
    iApply (wp_val_cells_store with "[$Hbs $Hc]"); [solve_ndisj|done|done|].
    iIntros "!> Bytes". iModIntro.
    iExists -[(l, y)]. iFrame "Obs".
    iSplit; [|done]. rewrite -(tctx_val_intro_sep _ _ _ _ (VPtr l) (S (d `max` d'))); [|done|done].
    iSplitR.
    { rewrite Nat.succ_max_distr persistent_time_receipt_sep. by iFrame "⧖ ⧖S". }
    iFrame "Free".
    iFrame "Bytes".
    iNext. iDestruct (ty_gho_own_depth_mono _ d' d' (d `max` d') (S (d `max` d')) with "Gho'")
      as "[$ _]"; lia.
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
