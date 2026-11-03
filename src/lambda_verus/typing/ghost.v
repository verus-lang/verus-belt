From lrust.typing Require Export type.
From lrust.typing Require Import programs value_ctx.
From lrust.lifetime Require Import lifetime_full.

Set Default Proof Using "Type".

(** A ghost operation is a no-op that returns the empty tuple, the MiniRust value of a
    ghost value ([GhostOp]), or (the pointer of) its argument ([GhostRet], for an
    operation whose result is a shared reference to a ghost value). *)
Definition GhostOp : expr := (Skip ;; MkTuple [])%E.
Definition GhostRet : val := (λ: ["p"], "p")%V.

Section ghost_op.
  Context `{!typeG Σ}.

  (** A ghost operation takes two steps. *)
  Lemma wp_ghost_op E Φ :
    ▷ ▷ Φ (MLitV (VTuple [])) -∗ WP GhostOp @ E {{ Φ }}.
  Proof.
    iIntros "HΦ". rewrite /GhostOp. wp_seq. wp_seq.
    eapply (tac_wp_pure []); [apply (pure_mk_tuple [])|done|tc_solve|simpl; iApply wp_value].
    done.
  Qed.

  (** A ghost operation, given a ghost update at the value [()] of the operation. The update
      gets two cumulative time receipts (for later credits). *)
  Lemma typed_inv_instr_ghost_op {𝔄l 𝔅l} E L I I' (T: tctx 𝔄l) (T': val → tctx 𝔅l) tr :
    (∀ tid post mask iκs xl, llft_ctx -∗ time_ctx -∗ proph_ctx -∗ uniq_ctx -∗
      elctx_interp E -∗ llctx_interp L -∗ invctx_interp tid mask iκs I -∗
      tctx_interp tid T xl -∗ ⟨π, tr post xl mask π⟩ -∗ ⧗1 -∗ ⧗1 ={⊤}=∗ ∃ xl' mask',
        llctx_interp L ∗ invctx_interp tid mask' iκs I' ∗
        tctx_interp tid (T' (MLitV (VTuple []))) xl' ∗ ⟨π, post xl' mask' π⟩) →
    typed_inv_instr E L I T GhostOp I' T' tr.
  Proof.
    iIntros (Hvs tid post mask iκs xl) "#LFT #TIME #PROPH #UNIQ #E L I T Obs".
    iApply wp_fupd. rewrite /GhostOp.
    iApply (wp_cumulative_time_receipt2 with "TIME"); [solve_ndisj|]. iIntros "⧗".
    iDestruct (cumulative_time_receipt_sep 1 1 with "⧗") as "[⧗ ⧗']".
    wp_seq. wp_seq.
    eapply (tac_wp_pure []); [apply (pure_mk_tuple [])|done|tc_solve|simpl; iApply wp_value].
    iApply (Hvs tid post mask iκs xl with "LFT TIME PROPH UNIQ E L I T Obs ⧗ ⧗'").
  Qed.

  Lemma typed_instr_ghost_op {𝔄l 𝔅l} E L I (T: tctx 𝔄l) (T': val → tctx 𝔅l) tr :
    (∀ tid post mask iκs xl, llft_ctx -∗ time_ctx -∗ proph_ctx -∗ uniq_ctx -∗
      elctx_interp E -∗ llctx_interp L -∗ invctx_interp tid mask iκs I -∗
      tctx_interp tid T xl -∗ ⟨π, tr post xl mask π⟩ -∗ ⧗1 -∗ ⧗1 ={⊤}=∗ ∃ xl',
        llctx_interp L ∗ invctx_interp tid mask iκs I ∗
        tctx_interp tid (T' (MLitV (VTuple []))) xl' ∗ ⟨π, post xl' mask π⟩) →
    typed_instr E L I T GhostOp T' tr.
  Proof.
    iIntros (Hvs tid post mask iκs xl) "#LFT #TIME #PROPH #UNIQ #E L I T Obs".
    iApply wp_fupd. rewrite /GhostOp.
    iApply (wp_cumulative_time_receipt2 with "TIME"); [solve_ndisj|]. iIntros "⧗".
    iDestruct (cumulative_time_receipt_sep 1 1 with "⧗") as "[⧗ ⧗']".
    wp_seq. wp_seq.
    eapply (tac_wp_pure []); [apply (pure_mk_tuple [])|done|tc_solve|simpl; iApply wp_value].
    iApply (Hvs tid post mask iκs xl with "LFT TIME PROPH UNIQ E L I T Obs ⧗ ⧗'").
  Qed.
End ghost_op.

Section ghost.
  Context `{!typeG Σ}.

  Program Definition ghost_ty {𝔄} (ty: type 𝔄) : type (ghostₛ 𝔄) := @ty_of_st _ _ (ghostₛ 𝔄)
    ({|
      st_lfts := ty.(ty_lfts);
      st_E := [];
      st_gho x d g tid := True%I;
    |}%I : simple_type (ghostₛ 𝔄)).
  Next Obligation. intros. iIntros. done. Qed.
  Next Obligation. intros 𝔄 ty κ x n d g tid ξ R Hin. exfalso. simpl in Hin. set_solver. Qed.
  
  Global Instance tracked_ne {𝔄} : NonExpansive (@ghost_ty 𝔄).
  Proof. move=> ????. apply ty_of_st_ne. solve_ne_type. Qed.

  Global Instance ghost_send {𝔄} (ty : type 𝔄) : Send (ghost_ty ty).
  Proof. done. Qed.
  
  Global Instance ghost_sync {𝔄} (ty : type 𝔄) : Sync (ghost_ty ty).
  Proof. apply sync_default; [done|]. split; iSplit; done. Qed.
  
  Global Instance ghost_copy {𝔄} (ty : type 𝔄) : Copy (ghost_ty ty).
  Proof.
    split; [apply _|typeclasses eauto|]. intros. by apply copy_shr_default.
  Qed.

  Lemma ghost_resolve {𝔄} (ty: type 𝔄) E L : resolve E L (ghost_ty ty) (const (const True)).
  Proof. apply resolve_just. Qed.
  
  (** The ghost operations take a ghost value as a MiniRust value ([◁ᵥ]): a ghost value
      is zero-sized, and its MiniRust value is the empty tuple. *)
  Local Lemma ghost_val_own {𝔅} tid (ty: type 𝔅) x :
    ⊢ |==> tctx_elt_interp tid (MLitV (VTuple []) ◁ᵥ ghost_ty ty) x.
  Proof.
    iMod persistent_time_receipt_0 as "⧖". rewrite tctx_val_val. iExists 0%nat. by iFrame.
  Qed.

  Lemma ghost_constant {𝔄} E L I (ty : type 𝔄) (c: ~~𝔄) :
    typed_instr E L I +[] GhostOp (λ v, +[v ◁ᵥ ghost_ty ty]) (λ post '-[], post -[c]).
  Proof.
    iIntros (tid post mask iκs []) "_ _ _ _ _ $ $ _ Obs".
    iMod (ghost_val_own tid ty c) as "G".
    iApply wp_ghost_op. iIntros "!> !>". iExists -[c]. by iFrame.
  Qed.

  (** A snapshot of the value of any element of the type context. *)
  Lemma ghost_snapshot {𝔄} E L I (t : tctx_elt 𝔄) (ty : type 𝔄) :
    typed_instr E L I +[t] GhostOp (λ v, +[t; v ◁ᵥ ghost_ty ty])
      (λ post '-[x], post -[x; x]).
  Proof.
    iIntros (tid post mask iκs [x []]) "_ _ _ _ _ $ $ [T _] Obs".
    iMod (ghost_val_own tid ty x) as "G".
    iApply wp_ghost_op. iIntros "!> !>". iExists -[x; x]. by iFrame.
  Qed.

  Lemma ghost_compute {𝔄 𝔅 ℭ} E L I (t1 : tctx_elt 𝔄) (t2 : tctx_elt 𝔅) (ty: type ℭ)
      (f : (~~𝔄) → (~~𝔅) → (~~ℭ)) :
    typed_instr E L I +[t1; t2] GhostOp (λ v, +[t1; t2; v ◁ᵥ ghost_ty ty])
      (λ post '-[x; y], post -[x; y; f x y]).
  Proof.
    iIntros (tid post mask iκs [x [y []]]) "_ _ _ _ _ $ $ (T1 & T2 & _) Obs".
    iMod (ghost_val_own tid ty (f x y)) as "G".
    iApply wp_ghost_op. iIntros "!> !>". iExists -[x; y; f x y]. by iFrame.
  Qed.
End ghost.

Global Hint Resolve ghost_resolve : lrust_typing.
