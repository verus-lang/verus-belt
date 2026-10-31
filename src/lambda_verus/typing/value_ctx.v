From lrust.typing Require Export type type_context bytes_layout.
From lrust.typing Require Import programs bool int own product sum.
From lrust.lifetime Require Import lifetime_full.
From guarding Require Import guard tactics.
Set Default Proof Using "Type".

(** * Typing MiniRust values (stage 4 of the MiniRust memory model)

The legacy element [p ◁ ty] types a path that evaluates to a one-word [val] with
[ty_phys x = [FVal v]]. The element [p ◁ᵥ ty] types a path that evaluates to a MiniRust
value [MLitV w], the MiniRust value of [x] ([ty_val x = Some w]): it is the result of a
typed [Load] of [ty_mty ty] and the argument of a typed [Store]. It is a semantic
element ([TCtx_sem]), so the type context needs no new case; the two forms coexist until
the legacy word layer is deleted (stage 5).

Pointers are MiniRust values too ([VPtr l]); the address argument of [Load], [Store],
[MemCopy] and of the offset [+ₗ] is a legacy literal [#l], which [ToLit] gives. *)

Implicit Type 𝔄 𝔅: syn_type.

Section value_ctx.
  Context `{!typeG Σ}.

  Definition val_own {𝔄} (ty: type 𝔄) (x: ~~𝔄) (tid: thread_id) (v: val) : iProp Σ :=
    ∃ w d, ⌜v = MLitV w ∧ ty.(ty_val) x = Some w⌝ ∗ ⧖d ∗ ty.(ty_gho_own) x d d tid.
End value_ctx.

Notation "p ◁ᵥ ty" := (TCtx_sem _ p (val_own ty%T)) (at level 55).

Section value_rules.
  Context `{!typeG Σ}.

  Lemma tctx_val_val {𝔄} tid (w: Value) (ty: type 𝔄) x :
    tctx_elt_interp tid (MLitV w ◁ᵥ ty) x ⊣⊢
      ∃ d, ⌜ty.(ty_val) x = Some w⌝ ∗ ⧖d ∗ ty.(ty_gho_own) x d d tid.
  Proof.
    rewrite /tctx_elt_interp eval_path_of_val. iSplit.
    - iIntros "(%v & %Hv & %w' & %d & [%Hw %Hx] & ⧖ & Gho)". simplify_eq. iExists d. by iFrame.
    - iIntros "(%d & %Hx & ⧖ & Gho)". iExists _. iSplit; [done|]. iExists w, d. by iFrame.
  Qed.

  Lemma wp_val {𝔄} E tid p (ty: type 𝔄) x Φ :
    tctx_elt_interp tid (p ◁ᵥ ty) x -∗
    (∀ w d, ⌜eval_path p = Some (MLitV w)⌝ -∗ ⌜ty.(ty_val) x = Some w⌝ -∗ ⧖d -∗
      ty.(ty_gho_own) x d d tid -∗ Φ (MLitV w)) -∗
    WP p @ E {{ Φ }}.
  Proof.
    iIntros "(%v & %Hp & %w & %d & [-> %Hx] & ⧖ & Gho) ToΦ".
    iApply (wp_wand with "[]"); [by iApply wp_eval_path|].
    iIntros (? ->). by iApply ("ToΦ" with "[//] [//] ⧖ Gho").
  Qed.

  (** Duplicating a value of a [Copy] type. *)
  Lemma copy_val_tctx_incl {𝔄 𝔄l} (ty: type 𝔄) `{!Copy ty} (T: tctx 𝔄l) p E L :
    tctx_incl E L (p ◁ᵥ ty +:: T) (p ◁ᵥ ty +:: p ◁ᵥ ty +:: T)
      (λ post '(a -:: al), post (a -:: a -:: al)).
  Proof.
    split; [by intros ??? [??]|].
    iIntros (??[a al]???) "_ _ _ _ _ $ /=[(%v & %Hp & %w & %d & %Hw & #⧖ & #Gho) T] Obs !>".
    iExists (a -:: a -:: al). iFrame "Obs T".
    iSplit; iExists v; (iSplit; [done|]); iExists w, d; by iFrame "⧖ Gho".
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

  (** A variant value: the payload with the index of the variant. The legacy padding
      component of the value is arbitrary. *)
  Lemma type_mk_variant_val_instr {𝔄l} (tyl: typel 𝔄l) (i: fin (length 𝔄l)) (t: Z) p E L I :
    t = Z.of_nat (fin_to_nat i) →
    typed_instr E L I +[p ◁ᵥ tyl +!! i] (MkVariant t p) (λ v, +[v ◁ᵥ Σ! tyl])
      (λ post '-[a], λ mask π, ∀ pad, post -[(pinj i a, pad)] mask π).
  Proof.
    iIntros (-> tid post mask iκs [a []]) "_ _ _ _ _ $$ [p _] Obs".
    wp_bind p. iApply (wp_val with "p"). iIntros (w d Hp Hw) "⧖ Gho".
    wp_pure _. iExists -[(pinj i a, [])]. iSplitR "Obs".
    - iSplit; [|done]. rewrite tctx_val_val. iExists d. iFrame "⧖". iSplit.
      + iPureIntro. rewrite -ty_val_eq syn_val_pinj (ty_val_eq (tyl +!! i)) Hw //.
      + rewrite [ty_gho_own (Σ! tyl)]/ty_gho_own /xsum_ty /= to_xsum_pinj. done.
    - iApply proph_obs_impl; [|done]=> π. by apply.
  Qed.

  (** Reading the pointee of a box of a [Copy] type: a typed [Load]. *)
  Lemma type_load_own_bytes_copy_instr {𝔄} `{!NoCell 𝔄} n (ty: type 𝔄) p E L I :
    Copy ty →
    typed_instr E L I +[p ◁ᵥ own_bytes n ty] (Load Na1Ord ty.(ty_mty) (ToLit p))
      (λ v, +[p ◁ᵥ own_bytes n ty; v ◁ᵥ ty]) (λ post '-[a], post -[a; a.2]).
  Proof.
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
    - iExists _. iSplit; [done|]. iExists (VPtr l), (S d). iSplit; [done|]. iFrame "⧖ Free".
      iSplitL "Hbs"; [by iApply bytes_own_of_bytes|]. done.
    - iSplit; [|done]. iExists _. iSplit; [done|]. iExists v, (S d). iSplit; [done|].
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
    wp_bind q. iApply (wp_val with "q"). iIntros (v d' Hq Hv) "#⧖' Gho'".
    destruct d as [|d]; [done|]. iDestruct "Own" as "(Bytes & Free & _)".
    iApply (wp_persistent_time_receipt with "TIME ⧖'"); [done|]. iIntros "_ #⧖S".
    iApply wp_fupd. iApply (wp_bytes_own_forget with "Bytes"); [solve_ndisj|].
    iIntros (bs) "Hbs %Hlen".
    iApply (wp_store_na with "Hbs"); [solve_ndisj|by eapply ty_val_wf|by rewrite Hlen|].
    iIntros "!> Hbs !>". iExists -[(l, y)]. iFrame "Obs".
    iSplit; [|done]. iExists _. iSplit; [done|]. iExists (VPtr l), (S (d `max` d')).
    iSplit; [done|]. iSplitR.
    { rewrite Nat.succ_max_distr persistent_time_receipt_sep. by iFrame "⧖ ⧖S". }
    iFrame "Free".
    iSplitL "Hbs". { iApply (bytes_own_of_bytes with "Hbs"). by apply ty_bytes_encode. }
    iNext. iDestruct (ty_gho_own_depth_mono _ d' d' (d `max` d') (S (d `max` d')) with "Gho'")
      as "[$ _]"; lia.
  Qed.
  (** Resolving a value. *)
  Lemma type_resolve_val_instr {𝔄} p (ty: type 𝔄) Φ E L I :
    resolve E L ty Φ →
    typed_instr E L I +[p ◁ᵥ ty] Skip (λ _, +[]) (λ post '-[a], λ mask π, Φ a π → post -[] mask π).
  Proof.
    iIntros (Rslv ????[?[]]) "LFT #TIME PROPH UNIQ E L I /=[(%v & %Hp & %w & %d & _ & ⧖ & tygho) _] Obs".
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
    iIntros "#LFT #PROPH #UNIQ #TIME #E #L G /=[(%v & _ & %w & %d & _ & ⧖ & ty) T]".
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
