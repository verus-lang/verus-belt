From iris.proofmode Require Import proofmode.
From lrust.typing Require Export type function product programs own cont uninit int
  uniq_bor shr_bor borrow place place_own place_resolve place_puniq place_pshr place_res
  place_res_rslv place_res_ops.
From lrust.lang Require Import lang notation new_delete.
Set Default Proof Using "Type".

Section place_res.
  Context `{!typeG Σ}.

  (*
  Resolving a local, then reading both of its fields:

  ```
  fn res_pair<'a>(x: (Box<i32>, &'a mut (i32, i32))) -> i32 {
      /* resolve x */
      let a = *x.0;
      let b = ( *x.1).0;
      a + b                       // x is dropped
  }
  ```

  with the specification `ensures result == *x.0 + ( *x.1).0` and the observation
  `fin(x.1) == cur(x.1)`, learnt when [x] is resolved. The argument slot [x] is an owned
  place, unfolded as a pair; it is resolved ([type_resolve_oplace_res_instr],
  [lty_res_prod] of two [lty_res_ofty], two program steps) to
  [ProdLty (OfRes (box int)) (OfRes (&uniq{'a} (int * int)))], which stays readable:
    * [OfRes (box int)] is converted back to [OfTy (box int)] ([tctx_oplace_res_to_ofty]),
      unfolded and read ([type_read_oplace_instr]);
    * [OfRes (&uniq{'a} (int * int))] is re-read as a shared reference to its referent
      at ['a] ([tctx_oplace_res_uniq_to_shr]), viewed as a pair and read below it
      ([type_read_oplace_pshr_instr]);
    * the slot is dropped ([type_drop_oplace_res_instr]), freeing the box.
  *)

  Definition res_pair : val :=
    fn: ["x"] :=
      (Skip;; Skip;; #☠);;                          (* resolve x *)
      let: "a" := !(!"x") in                        (* *x.0 *)
      ReBor;;                                       (* view *x.1 as a pair *)
      let: "b" := Skip;; !(!("x" +ₗ #1)) in         (* ( *x.1).0 *)
      (((#☠;; delete [ #1; !"x"]);; #☠);; delete [ #2; "x"]);; (* drop x *)
      let: "r" := "a" + "b" in
      let: "ret" := new [ #1] in
      "ret" <- "r";;
      return: ["ret"].

  Definition res_pair_spec :
      fn_spec [(at_locₛ Zₛ * uniq_borₛ (Zₛ * Zₛ))%ST] Zₛ () :=
    λ _ post '-[(_, ((_, z), m))], λ mask π,
      uniq_bor_future (𝔄:=Zₛ * Zₛ) m π = uniq_bor_current (𝔄:=Zₛ * Zₛ) m →
      ∀ (lr: loc), post (lr, z + (uniq_bor_current (𝔄:=Zₛ * Zₛ) m).1)%Z mask π.

  Lemma res_pair_type :
    typed_val res_pair
      ((fn<α>(∅; box int * &uniq{α} (int * int)) → int) res_pair_spec)
      (res_pair, ()).
  Proof.
    unfold res_pair. unlock.
    opose proof (@type_fn _ _ _ [(at_locₛ Zₛ * uniq_borₛ (Zₛ * Zₛ))%ST] Zₛ () ()
      (λ α, FP ∅ +[(box int * &uniq{α} (int * int))%T] int%T AtomicClosed)
      res_pair_spec _ [BNamed "x"] _ _ _) as H.
    unlock in H. apply H. clear H.
    intros α ϝ k wl. destruct wl as [vx []]. simpl_subst.
    have Alv: lctx_lft_alive
      (fp_E (FP ∅ +[(box int * &uniq{α} (int * int))%T] int AtomicClosed) ϝ) [ϝ ⊑ₗ []] α.
    { eapply lctx_lft_alive_external; [rewrite /fp_E /=; by left|solve_typing]. }
    iApply (typed_body_impl with "[]"); last first. {
      (* x as an owned place, unfolded *)
      iApply typed_body_tctx_incl.
      { eapply tctx_incl_trans; [apply tctx_own_to_oplace|].
        apply (tctx_unfold_oplace_prod _ _ _ _ PHole (box int) (&uniq{α} (int * int))). }
      (* resolve x *)
      iApply type_seq.
      { apply (type_resolve_oplace_res_instr _ _ _ vx 2
          (ProdLty (OfTy (box int)) (OfTy (&uniq{α} (int * int))))
          (ProdLty (OfRes (box int)) (OfRes (&uniq{α} (int * int)))) (1 + 1)).
        apply lty_res_prod; apply lty_res_ofty.
        - apply resolve_keep_just. apply _.
        - by apply uniq_resolve_keep. }
      { solve_typing. } { reflexivity. }
      (* *x.0: the box is unresolved again, unfolded and read *)
      iApply typed_body_tctx_incl.
      { eapply tctx_incl_trans;
          [apply (tctx_oplace_res_to_ofty _ _ _ _ (PFst PHole (OfRes (&uniq{α} (int * int))))
            (box int))|].
        by apply (tctx_unfold_oplace_own _ _ _ _ (PFst PHole (OfRes (&uniq{α} (int * int))))
          1 int). }
      iApply (type_let with "[]").
      { apply (type_read_oplace_instr _ _ _ vx 2
          (PFst (POwn 1 PHole) (OfRes (&uniq{α} (int * int)))) int); [done|apply _]. }
      { solve_typing. } { reflexivity. }
      iIntros (va). simpl_subst.
      (* ( *x.1).0: the resolved unique borrow is a shared reference to its referent *)
      iApply typed_body_tctx_incl.
      { eapply tctx_incl_tail.
        apply (tctx_oplace_res_uniq_to_shr _ _ _ _ (PSnd (OwnPtrLty 1 (OfTy int)) PHole) α
          (int * int)). done. }
      iApply type_seq.
      { apply (type_change_oplace_shr_instr _ _ _ vx 2 (PSnd (OwnPtrLty 1 (OfTy int)) PHole) α
          PHole (OfTy (int * int)) (ProdLty (OfTy int) (OfTy int))); [solve_typing|done|done|done]. }
      { solve_typing. } { reflexivity. }
      iApply (type_let with "[]").
      { apply (type_read_oplace_pshr_instr _ _ _ vx 2 (PSnd (OwnPtrLty 1 (OfTy int)) PHole) α
          (PFst PHole (OfTy int)) (OfTy int)); [done|apply _|solve_typing|solve_typing]. }
      { solve_typing. } { reflexivity. }
      iIntros (vb). simpl_subst.
      (* drop x, freeing the box *)
      iApply type_seq.
      { apply (type_drop_oplace_res_instr _ _ _ vx 2 2
          (ProdLty (OwnPtrLty 1 (OfTy int)) (ShrLty (ProdLty (OfTy int) (OfTy int)) α)));
          [done|done|done]. }
      { solve_typing. } { reflexivity. }
      (* a + b *)
      iApply (type_plus va vb). { solve_typing. }
      iIntros (vr). simpl_subst.
      iApply (type_new 1). { lia. } iIntros (vret). simpl_subst.
      iApply type_assign. { solve_typing. } { by apply write_own. }
      { apply (resolve'_just _ _ _ (const True)). apply resolve_just. }
      iApply type_jump.
      { rewrite elem_of_list_singleton. reflexivity. }
      { solve_typing. }
      { solve_typing. }
      { reflexivity. }
    }
    intros post [[lx [[lb z] m]] []] mask π. simpl.
    intros Hspec. rewrite /trans_upper /trans_tail /=.
    intros [_ Hres] l0 junk z0 ->. apply Hspec.
    destruct m as [[[[[l' [z1 z2]] ξi] d] g] idx]. simpl in *.
    rewrite uniq_bor_future_eq. exact Hres.
  Qed.
End place_res.

Print Assumptions res_pair_type.
