From lrust.typing Require Export type type_context bytes_layout.
From lrust.typing Require Import programs int own_bytes.
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

  (** An integer literal. *)
  Lemma type_val_int_instr it (z: Z) E L I :
    int_in_range it z →
    typed_instr E L I +[] (MLit (VInt z)) (λ v, +[v ◁ᵥ int_ty it]) (λ post _, post -[z]).
  Proof.
    iIntros (Hz ?????) "_ _ _ _ _ $$ _ Obs". iMod persistent_time_receipt_0 as "⧖".
    iApply wp_value. iExists -[z]. iFrame "Obs". iSplit; [|done].
    rewrite tctx_val_val. iExists 0%nat. iFrame "⧖". iPureIntro. by apply int_ty_val.
  Qed.

  (** Reading the pointee of a box of a [Copy] type: a typed [Load]. *)
  Lemma type_load_own_bytes_copy_instr {𝔄} n (ty: type 𝔄) p E L I :
    Copy ty →
    typed_instr E L I +[p ◁ᵥ own_bytes n ty] (Load Na1Ord ty.(ty_mty) (ToLit p))
      (λ v, +[p ◁ᵥ own_bytes n ty; v ◁ᵥ ty]) (λ post '-[a], post -[a; a.2]).
  Proof.
    iIntros (? tid post mask iκs [[l x] []]) "_ #TIME _ _ _ $ $ [p _] Obs".
    wp_bind p. iApply (wp_val with "p"). iIntros (w d Hp Hw) "#⧖ Own".
    simpl in Hw. simplify_eq. wp_pure _.
    destruct d as [|d]; [done|]. iDestruct "Own" as "(Bytes & Free & Gho)".
    iDestruct "Bytes" as (bs) "[Hbs %Hbs]". destruct (ty_bytes_val _ _ _ Hbs) as [v Hv].
    iApply (wp_persistent_time_receipt with "TIME ⧖"); [done|]. iIntros "£ _".
    iDestruct (lc_weaken 1 with "£") as "£"; [rewrite /advance_credits; lia|].
    iMod (lc_fupd_elim_later with "£ Gho") as "#Gho".
    iApply wp_fupd. iApply (wp_load_na with "Hbs"); [by eapply ty_bytes_decode|].
    iIntros "!> Hbs !>". iExists -[(l, x); x]. iFrame "Obs". simpl.
    iDestruct (ty_gho_own_depth_mono _ d (S d) (S d) (S d) with "Gho") as "[#Gho' _]"; [lia..|].
    iSplitL "Hbs Free".
    - iExists _. iSplit; [done|]. iExists (VPtr l), (S d). iSplit; [done|]. iFrame "⧖ Free".
      iSplitL "Hbs"; [iExists bs; by iFrame|]. done.
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
    iDestruct "Bytes" as (bs) "[Hbs %Hbs]".
    iApply (wp_persistent_time_receipt with "TIME ⧖'"); [done|]. iIntros "_ #⧖S".
    iApply wp_fupd. iApply (wp_store_na with "Hbs"); [solve_ndisj|by eapply ty_val_wf| |].
    { rewrite (ty_bytes_length _ _ _ Hbs). done. }
    iIntros "!> Hbs !>". iExists -[(l, y)]. iFrame "Obs".
    iSplit; [|done]. iExists _. iSplit; [done|]. iExists (VPtr l), (S (d `max` d')).
    iSplit; [done|]. iSplitR.
    { rewrite Nat.succ_max_distr persistent_time_receipt_sep. by iFrame "⧖ ⧖S". }
    iFrame "Free".
    iSplitL "Hbs". { iExists _. iFrame. iPureIntro. by apply ty_bytes_encode. }
    iNext. iDestruct (ty_gho_own_depth_mono _ d' d' (d `max` d') (S (d `max` d')) with "Gho'")
      as "[$ _]"; lia.
  Qed.
End value_rules.
