From lrust.typing Require Export type.
From lrust.typing Require Import programs.

Set Default Proof Using "Type".

Section bool.
  Context `{!typeG Σ}.

  Program Definition bool_ty: type boolₛ :=
    {|
      pt_size := 1;
      pt_gho (b: ~~boolₛ) _ := True%I ;
      pt_phys (b: ~~boolₛ) _ := [ FVal #b ] ;
    |}%I.
  Next Obligation. move=> *. trivial. Qed.
  Next Obligation. intros. done. Qed.
  Next Obligation. intros. done. Qed.
  Next Obligation. intros. done. Qed.
  Next Obligation. intros. done. Qed.
  Next Obligation. intros. done. Qed.
  
  Global Instance bool_copy: Copy bool_ty.
  Proof.
    split. - typeclasses eauto. - iIntros. iPureIntro. done.
    - intros. by apply copy_shr_default.
  Qed.

  Global Instance bool_send: Send bool_ty.
  Proof.
    intros. split; trivial.
     - intros. unfold syn_abstract in H. subst x'. trivial.
     - iIntros. iApply step_fupdN_intro; first done. iNext.
       iExists x, 0%nat. iModIntro. iFrame. simpl.
       replace (d0 + 0)%nat with d0 by lia. iFrame "#". done.
  Qed.
  
  Global Instance bool_sync: Sync bool_ty.
  Proof. apply sync_default; [done|]. split; trivial. split; iSplit; done. Qed.

  Lemma bool_resolve E L : resolve E L bool_ty (const (const True)).
  Proof. apply resolve_just. Qed.
  
  Lemma bool_stack_okay : StackOkay bool_ty.
  Proof. done. Qed.

  Lemma type_bool_instr (b: bool) : typed_val #b bool_ty b.
  Proof.
    iIntros (????????) "_ _ _ _ _ $$ _ Obs". iMod persistent_time_receipt_0 as "⧖".
    iApply wp_value. iExists -[b]. iFrame "Obs". iSplit; [|done].
    rewrite tctx_hasty_val'; [|done]. iExists 0%nat. iFrame "⧖".
    iSplit; done.
  Qed.

  Lemma type_bool {𝔄l 𝔅} (b: bool) (T: tctx 𝔄l) x e tr E L (I: invctx) (C: cctx 𝔅) :
    Closed (x :b: []) e →
    (∀v: val, typed_body E L I C (v ◁ bool_ty +:: T) (subst' x v e) tr) -∗
    typed_body E L I C T (let: x := #b in e) (λ post al, tr post (b -:: al)).
  Proof.
    iIntros. iApply type_let; [apply type_bool_instr|solve_typing|done..].
  Qed.

  Lemma type_nd_bool_instr E L I :
    typed_instr_ty E L I +[] NdBool bool_ty (λ post '-[], λ mask π, ∀b, post b mask π).
  Proof.
    iIntros (?????) "_ _ _ _ _ $$ _ #?". iMod persistent_time_receipt_0 as "⧖".
    wp_nd_int z. wp_op. iExists -[_]. rewrite right_id tctx_hasty_val'; [|done].
    iSplit. { iExists _. iFrame "⧖". iSplit; done. }
    iApply proph_obs_impl; [|done]=>/= ? Hyp.
    destruct xl; apply Hyp.
  Qed.

  Lemma type_nd_bool {𝔄l 𝔅} (T: tctx 𝔄l) x e tr E L (I: invctx) (C: cctx 𝔅) :
    Closed (x :b: []) e →
    (∀v: val, typed_body E L I C (v ◁ bool_ty +:: T) (subst' x v e) tr) -∗
    typed_body E L I C T (let: x := NdBool in e)
      (λ post al mask π, ∀b, tr post (b -:: al) mask π)%type.
  Proof.
    iIntros. by iApply type_let; [apply type_nd_bool_instr|solve_typing| |done].
  Qed.

  Lemma type_if {𝔄l 𝔅l ℭ} p (T: tctx 𝔄l) (T': tctx 𝔅l) e1 e2 tr1 tr2 trx E L I (C: cctx ℭ) :
    tctx_extract_ctx E L +[p ◁ bool_ty] T T' trx →
    typed_body E L I C T' e1 tr1 -∗ typed_body E L I C T' e2 tr2 -∗
    typed_body E L I C T (if: p then e1 else e2)
      (trx ∘ (λ post '(b -:: vl), if b then tr1 post vl else tr2 post vl)).
  Proof.
    iIntros (?) "e1 e2". iApply typed_body_tctx_incl; [done|]=>/=.
    iIntros (?[b ?]???) "/= #LFT #TIME #PROPH #UNIQ #E L I C [p T] Obs".
    wp_bind p. iApply (wp_hasty with "p"). iIntros (?? _) "_".
    iDestruct 1 as "[_true %Hphys]".
    inversion Hphys. subst v.
    destruct b; wp_case.
    - iApply ("e1" with "LFT TIME PROPH UNIQ E L I C T").
      iApply (proph_obs_impl with "Obs"). intros π. done.
    - iApply ("e2" with "LFT TIME PROPH UNIQ E L I C T").
      iApply (proph_obs_impl with "Obs"). intros π.  done.
  Qed.
End bool.

Global Hint Resolve bool_resolve : lrust_typing.
