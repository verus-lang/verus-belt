From iris.proofmode Require Import proofmode.
From lrust.typing Require Export type function product programs own cont uninit int
  uniq_bor borrow place.
From lrust.lang Require Import lang notation new_delete.
Set Default Proof Using "Type".

Section get_first.
  Context `{!typeG Σ}.

  (*
  Taking a mutable reference to a field and returning it at the same lifetime, as in

  ```
  fn get_first<'a>(x: &'a mut (i32, i32)) -> &'a mut i32 {
      &mut x.0
  }
  ```

  with the specification (in Verus/Prusti notation)

  ```
  ensures *result == old(x).0,
          fin(x).0 == *fin(result),
          fin(x).1 == old(x).1
  ```

  (this is the shape of RefinedRust's `get_unchecked_mut`, Fig. 10 of the paper).

  The outer borrow `x` is dropped while its field 0 is still blocked by the
  returned reborrow, so its prophecy cannot be resolved to a current value. With
  place types:
    * the referent of `x` is unfolded into a place `ProdLty (OfTy int) (OfTy int)`
      ([tctx_unfold_uniq_prod]);
    * field 0 is reborrowed ([type_reborrow_field0_instr]), which blocks it and
      reserves the prophecy of `x` for the reborrow's prophecy;
    * `x` is dropped while blocked ([type_drop_blocked_field0_instr]): its prophecy is
      resolved through the reservation to the final value of the reborrow and the
      final value of a fresh borrow of field 1;
    * the borrow of field 1 is resolved to its current value ([uniq_resolve]).
  *)

  Definition get_first : val :=
    fn: ["x"] :=
      let: "b" := !"x" in       (* b : &'a mut (i32, i32) *)
      delete [ #1; "x"];;
      ReBor;;                   (* &mut ( *b).0 *)
      SplitBor;;                (* drop b *)
      Skip;;                    (* resolve the borrow of ( *b).1 *)
      let: "r" := new [ #1] in
      "r" <- "b" +ₗ #0;;
      return: ["r"].

  Definition get_first_spec : fn_spec [uniq_borₛ (Zₛ * Zₛ)] (uniq_borₛ Zₛ) () :=
    λ _ post '-[(_, m)], λ mask π, ∀ (lr: loc) (r: ~~ (uniq_borₛ Zₛ)),
      uniq_bor_current r = (uniq_bor_current (𝔄:=Zₛ * Zₛ) m).1 →
      uniq_bor_future (𝔄:=Zₛ * Zₛ) m π =
        (uniq_bor_future r π, (uniq_bor_current (𝔄:=Zₛ * Zₛ) m).2) →
      post (lr, r) mask π.

  Lemma get_first_type :
    typed_val get_first
      ((fn<α>(∅; &uniq{α} (int * int)) → &uniq{α} int) get_first_spec)
      (get_first, ()).
  Proof.
    unfold get_first. unlock.
    opose proof (@type_fn _ _ _ [uniq_borₛ (Zₛ * Zₛ)] (uniq_borₛ Zₛ) () ()
      (λ α, FP ∅ +[&uniq{α} (int * int)]%T (&uniq{α} int)%T AtomicClosed)
      get_first_spec _ [BNamed "x"] _ _ _) as H.
    unlock in H. apply H. clear H.
    intros α ϝ k wl. destruct wl as [vx []]. simpl_subst.
    iApply (typed_body_impl with "[]"); last first. {
      (* let b := !x *)
      iApply (type_let with "[]").
      { eapply (type_deref_instr (own_ptr 1 (&uniq{α} (int * int)))
          (&uniq{α} (int * int))).
        - apply uniq_stack_okay.
        - done.
        - apply (read_own_move (&uniq{α} (int * int))). }
      { apply tctx_extract_elt_here_exact. }
      { reflexivity. }
      iIntros (vb). simpl_subst.
      (* delete x *)
      iApply type_delete. { solve_typing. } { done. } { done. }
      (* unfold the referent of b *)
      iApply typed_body_tctx_incl.
      { apply (tctx_unfold_uniq_prod _ _ vb α int int). solve_typing. }
      (* &mut ( *b).0, at α ⊓ α *)
      iApply type_seq.
      { apply (type_reborrow_field0_instr _ _ _ vb α α int int). solve_typing. }
      { solve_typing. } { reflexivity. }
      (* drop b while its field 0 is blocked *)
      iApply type_seq.
      { apply (type_drop_blocked_field0_instr _ _ _ vb α (α ⊓ α) int int). solve_typing. }
      { solve_typing. } { reflexivity. }
      (* resolve the borrow of field 1 *)
      iApply type_resolve. { solve_typing. } { apply uniq_bor.uniq_resolve. solve_typing. }
      (* return the reborrow of field 0, in a box *)
      iApply (type_new 1). { lia. } iIntros (vr). simpl_subst.
      iApply type_assign. { solve_typing. } { by apply write_own. }
      { apply (resolve'_just _ _ _ (const True)). apply resolve_just. }
      iApply type_jump.
      { rewrite elem_of_list_singleton. reflexivity. }
      { solve_typing. }
      { solve_typing. }
      { reflexivity. }
    }
    intros post [[lx m] []] mask π. simpl.
    destruct m as [[[[[l [x1 x2]] ξi] d] g] idx]. simpl.
    intros Hspec. rewrite /trans_upper /trans_tail /=.
    intros z _ m1 Hl1 Hc1 m2 Hl2 Hc2 Hfin Hres lr junk w ->.
    apply Hspec; [done|]. rewrite Hfin.
    destruct m1 as [[[[[l1 y1] ζi] d1] g1] idx1].
    destruct m2 as [[[[[l2 y2] ηi] d2] g2] idx2].
    simpl in Hc1, Hc2, Hres. subst y1 y2. rewrite !uniq_bor_future_eq. f_equal. exact Hres.
  Qed.
End get_first.
