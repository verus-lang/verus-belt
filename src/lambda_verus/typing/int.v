From lrust.typing Require Export type.
From lrust.typing Require Import bool programs.
Set Default Proof Using "Type".
Open Scope Z_scope.

Section int.
  Context `{!typeG Σ}.

  Program Definition int: type Zₛ :=
    {| pt_size := 1;
       pt_gho (z: ~~Zₛ) _ := True%I;
       pt_phys (z: ~~Zₛ) _ := [ FVal #z ];
    |}.
  Next Obligation. intros. done. Qed.
  Next Obligation. intros. done. Qed.
  Next Obligation. intros. done. Qed.
  Next Obligation. intros. done. Qed.
  Next Obligation. intros. done. Qed.
  Next Obligation. intros. done. Qed.
  
  Global Instance int_copy: Copy int.
  Proof.
    split. - typeclasses eauto. - iIntros. iPureIntro. done.
    - intros. by apply copy_shr_default.
  Qed.
  
  Lemma int_stack_okay : StackOkay int.
  Proof. done. Qed.
  
  Global Instance int_send: Send bool_ty.
  Proof.
    intros. split; trivial.
     - intros. unfold syn_abstract in H. subst x'. trivial.
     - iIntros. iApply step_fupdN_intro; first done. iNext.
       iExists x, 0%nat. iModIntro. iFrame. simpl.
       replace (d0 + 0)%nat with d0 by lia. iFrame "#". done.
  Qed.

  Global Instance int_sync: Sync bool_ty.
  Proof. apply sync_default; [done|]. split; trivial. split; iSplit; done. Qed.

  Lemma int_resolve E L : resolve E L int (const (const True)).
  Proof. apply resolve_just. Qed.
  
  Program Definition Z_of_boolₛ : boolₛ →ₛ Zₛ := {|
    syn_type_morphism_fn := Z_of_bool ;
    syn_type_morphism_proph_fn := Z_of_bool ;
  |}.
  Next Obligation. intros. done. Qed.
  Next Obligation. intros. done. Qed.

  Lemma bool_ty_to_int E L : subtype E L bool_ty int Z_of_boolₛ.
  Proof.
    apply subtype_plain_type. iIntros "*_!>_/=". iSplit; [done|].
    iSplit; [iApply lft_incl_refl|]. by iIntros.
  Qed.

  Lemma type_int_instr (z: Z) : typed_val #z int z.
  Proof.
    iIntros (????????) "_ _ _ _ _ $$ _ Obs". iMod persistent_time_receipt_0 as "⧖".
    iApply wp_value. iExists -[z]. iFrame "Obs". iSplit; [|done].
    rewrite tctx_hasty_val'; [|done]. iExists 0%nat. iFrame "⧖". done.
  Qed.

  Lemma type_int {𝔄l 𝔅} (z: Z) (T: tctx 𝔄l) x e tr E L I (C: cctx 𝔅) :
    Closed (x :b: []) e →
    (∀v: val, typed_body E L I C (v ◁ int +:: T) (subst' x v e) tr) -∗
    typed_body E L I C T (let: x := #z in e) (λ post al, tr post (z -:: al)).
  Proof. iIntros. iApply type_let; [apply type_int_instr|solve_typing|done..]. Qed.

  Lemma type_plus_instr E L I p1 p2 :
    typed_instr_ty E L I +[p1 ◁ int; p2 ◁ int] (p1 + p2) int
      (λ post '-[z; z'], post (z + z')).
  Proof.
    iIntros (????(z & z' &[])) "_ _ _ _ _ $$ (p1 & p2 &_) Obs".
    wp_apply (wp_hasty with "p1"). iIntros "%v %d _ ⧖ [gho %phys]". inversion phys. subst v.
    wp_apply (wp_hasty with "p2"). iIntros "%v %d' _ ⧖' [gho' %phys']". inversion phys'. subst v.
    wp_op. iExists -[(z + z')]. iFrame "Obs". rewrite right_id
    tctx_hasty_val'; [|done]. iExists d. iFrame "⧖". done.
  Qed.

  Lemma type_plus {𝔄l 𝔅l ℭ} p1 p2 x e trx tr E L I (C: cctx ℭ) (T: tctx 𝔄l) (T': tctx 𝔅l) :
    Closed (x :b: []) e → tctx_extract_ctx E L +[p1 ◁ int; p2 ◁ int] T T' trx →
    (∀v: val, typed_body E L I C (v ◁ int +:: T') (subst' x v e) tr) -∗
    typed_body E L I C T (let: x := p1 + p2 in e)
      (trx ∘ (λ post '(z -:: z' -:: bl), tr post (z + z' -:: bl))).
  Proof.
    iIntros (? Extr) "?". iApply type_let; [by apply type_plus_instr|solve_typing| |done].
    destruct Extr as [Htrx _]=>?? /=. apply Htrx. by case=> [?[??]].
  Qed.

  Lemma type_minus_instr E L I p1 p2 :
    typed_instr_ty E L I +[p1 ◁ int; p2 ◁ int] (p1 - p2) int
      (λ post '-[z; z'], post (z - z')).
  Proof.
    iIntros (????(z & z' &[])) "_ _ _ _ _ $$ (p1 & p2 &_) Obs".
    wp_apply (wp_hasty with "p1"). iIntros "%v %d _ ⧖ [gho %phys]". inversion phys. subst v.
    wp_apply (wp_hasty with "p2"). iIntros "%v %d' _ ⧖' [gho' %phys']". inversion phys'. subst v.
    wp_op. iExists -[(z - z')]. iFrame "Obs". rewrite right_id
    tctx_hasty_val'; [|done]. iExists d. iFrame "⧖". done.
  Qed.

  Lemma type_minus {𝔄l 𝔅l ℭ} p1 p2 x e trx tr E L I (C: cctx ℭ) (T: tctx 𝔄l) (T': tctx 𝔅l) :
    Closed (x :b: []) e → tctx_extract_ctx E L +[p1 ◁ int; p2 ◁ int] T T' trx →
    (∀v: val, typed_body E L I C (v ◁ int +:: T') (subst' x v e) tr) -∗
    typed_body E L I C T (let: x := p1 - p2 in e)
      (trx ∘ (λ post '(z -:: z' -:: bl), tr post (z - z' -:: bl))).
  Proof.
    iIntros (? Extr) "?". iApply type_let; [by apply type_minus_instr|solve_typing| |done].
    destruct Extr as [Htrx _]=>?? /=. apply Htrx. by case=> [?[??]].
  Qed.

  Lemma type_mult_instr E L I p1 p2 :
    typed_instr_ty E L I +[p1 ◁ int; p2 ◁ int] (p1 * p2) int
      (λ post '-[z; z'], post (z * z')).
  Proof.
    iIntros (????(z & z' &[])) "_ _ _ _ _ $$ (p1 & p2 &_) Obs".
    wp_apply (wp_hasty with "p1"). iIntros "%v %d _ ⧖ [gho %phys]". inversion phys. subst v.
    wp_apply (wp_hasty with "p2"). iIntros "%v %d' _ ⧖' [gho' %phys']". inversion phys'. subst v.
    wp_op. iExists -[(z * z')]. iFrame "Obs". rewrite right_id
    tctx_hasty_val'; [|done]. iExists d. iFrame "⧖". done.
  Qed.

  Lemma type_mult {𝔄l 𝔅l ℭ} p1 p2 x e trx tr E L I (C: cctx ℭ) (T: tctx 𝔄l) (T': tctx 𝔅l) :
    Closed (x :b: []) e → tctx_extract_ctx E L +[p1 ◁ int; p2 ◁ int] T T' trx →
    (∀v: val, typed_body E L I C (v ◁ int +:: T') (subst' x v e) tr) -∗
    typed_body E L I C T (let: x := p1 * p2 in e)
      (trx ∘ (λ post '(z -:: z' -:: bl), tr post (z * z' -:: bl))).
  Proof.
    iIntros (? Extr) "?". iApply type_let; [by apply type_mult_instr|solve_typing| |done].
    destruct Extr as [Htrx _]=>?? /=. apply Htrx. by case=> [?[??]].
  Qed.

  Lemma type_le_instr E L I p1 p2 :
    typed_instr_ty E L I +[p1 ◁ int; p2 ◁ int] (p1 ≤ p2) bool_ty
      (λ post '-[z; z'], post (bool_decide (z ≤ z'))).
  Proof.
    iIntros (????(z & z' &[])) "_ _ _ _ _ $$ (p1 & p2 &_) Obs".
    wp_apply (wp_hasty with "p1"). iIntros "%v %d _ ⧖ [gho %phys]". inversion phys. subst v.
    wp_apply (wp_hasty with "p2"). iIntros "%v %d' _ ⧖' [gho' %phys']". inversion phys'. subst v.
    wp_op. iExists -[bool_decide (z ≤ z')]. iFrame "Obs". rewrite right_id
    tctx_hasty_val'; [|done]. iExists d. iFrame "⧖". done.
  Qed.

  Lemma type_le {𝔄l 𝔅l ℭ} p1 p2 x e trx tr E L I (C: cctx ℭ) (T: tctx 𝔄l) (T': tctx 𝔅l) :
    Closed (x :b: []) e → tctx_extract_ctx E L +[p1 ◁ int; p2 ◁ int] T T' trx →
    (∀v: val, typed_body E L I C (v ◁ bool_ty +:: T') (subst' x v e) tr) -∗
    typed_body E L I C T (let: x := p1 ≤ p2 in e)
      (trx ∘ (λ post '(z -:: z' -:: bl), tr post (bool_decide (z ≤ z') -:: bl))).
  Proof.
    iIntros (? Extr) "?". iApply type_let; [by apply type_le_instr|solve_typing| |done].
    destruct Extr as [Htrx _]=>?? /=. apply Htrx. by case=> [?[??]].
  Qed.

  Lemma type_nd_int_instr E L I :
    typed_instr_ty E L I +[] NdInt int (λ post '-[], λ mask π, ∀z, post z mask π).
  Proof.
    iIntros (?????) "_ _ _ _ _ $$ _ #Obs". iMod persistent_time_receipt_0 as "⧖".
    wp_nd_int z. iExists -[_]. rewrite right_id tctx_hasty_val'; [|done].
    iSplit. { iExists _. iFrame "⧖". done. }
    iApply (proph_obs_impl with "Obs"). intros π Ha. destruct xl. apply Ha.
  Qed.

  Lemma type_nd_int {𝔄l 𝔅} x e tr E L I (C: cctx 𝔅) (T: tctx 𝔄l) :
    Closed (x :b: []) e →
    (∀v: val, typed_body E L I C (v ◁ int +:: T) (subst' x v e) tr) -∗
    typed_body E L I C T (let: x := NdInt in e)
      (λ post bl mask π, ∀z, tr post (z -:: bl) mask π)%type.
  Proof.
    iIntros. by iApply type_let; [apply type_nd_int_instr|solve_typing| |done].
  Qed.
  
  Lemma type_int_eq_instr E L I p1 p2 :
    typed_instr_ty E L I +[p1 ◁ int; p2 ◁ int] (p1 = p2) bool_ty
      (λ post '-[z; z'], post (bool_decide (z = z'))).
  Proof.
    iIntros (????(z & z' &[])) "_ _ _ _ _ $$ (p1 & p2 &_) Obs".
    wp_apply (wp_hasty with "p1"). iIntros "%v %d _ ⧖ [gho %phys]". inversion phys. subst v.
    wp_apply (wp_hasty with "p2"). iIntros "%v %d' _ ⧖' [gho' %phys']". inversion phys'. subst v.
    wp_op. iExists -[bool_decide (z = z')]. iFrame "Obs". rewrite right_id
    tctx_hasty_val'; [|done]. iExists d. iFrame "⧖". done.
  Qed.

  Lemma type_int_eq {𝔄l 𝔅l ℭ} p1 p2 x e trx tr E L I (C: cctx ℭ) (T: tctx 𝔄l) (T': tctx 𝔅l) :
    Closed (x :b: []) e → tctx_extract_ctx E L +[p1 ◁ int; p2 ◁ int] T T' trx →
    (∀v: val, typed_body E L I C (v ◁ bool_ty +:: T') (subst' x v e) tr) -∗
    typed_body E L I C T (let: x := p1 = p2 in e)
      (trx ∘ (λ post '(z -:: z' -:: bl), tr post (bool_decide (z = z') -:: bl))).
  Proof.
    iIntros (? Extr) "?". iApply type_let; [by apply type_int_eq_instr|solve_typing| |done].
    destruct Extr as [Htrx _]=>?? /=. apply Htrx. by case=> [?[??]].
  Qed.

End int.

Global Hint Resolve int_resolve : lrust_typing.
