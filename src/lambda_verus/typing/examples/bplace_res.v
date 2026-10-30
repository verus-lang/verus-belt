From iris.proofmode Require Import proofmode.
From lrust.typing Require Export type programs cont int product value_ctx own_bytes shr_bytes
  uniq_util uniq_bor buniq_bor bplace_own bplace_puniq bplace_resolve bplace_pshr bplace_res
  bplace_res_rslv bplace_res_ops.
From lrust.lang Require Import lang notation new_delete.
Set Default Proof Using "Type".

(** * Resolving places to a readable state, on bytes

The example [res_pair] of [typing/examples/place_res.v], on bytes ([typing/bplace_res.v],
[typing/bplace_res_rslv.v], [typing/bplace_res_ops.v]): the argument is a box of bytes
holding a pair of a box and a unique borrow. *)

Section bplace_res.
  Context `{!typeG Σ}.

  Notation i32t := (int_ty i32).

  Definition ret_zz : predl_trans' [intₛ i32; intₛ i32] (intₛ i32 * intₛ i32) :=
    λ post '-[a; b], post (a, b).

  (*
  Resolving a local, then reading both of its fields:

  ```
  fn res_pair<'a>(x: (Box<i32>, &'a mut (i32, i32))) -> (i32, i32) {
      /* resolve x */
      let a = *x.0;
      let b = ( *x.1).0;
      (a, b)                      // x is dropped
  }
  ```

  with the specification `ensures result == ( *x.0, ( *x.1).0)` and the observation
  `fin(x.1) == cur(x.1)`, learnt when [x] is resolved. The argument is a box of bytes, an
  owned place, unfolded as a pair; it is resolved ([type_resolve_oplace_res_instr],
  [lty_res_prod] of two [lty_res_ofty], two program steps) to
  [ProdLty (OfRes (own_bytes 4 i32)) (OfRes (&uniqb{'a} (i32 * i32)))], which stays
  readable:
    * [OfRes (own_bytes 4 i32)] is converted back to [OfTy (own_bytes 4 i32)]
      ([tctx_oplace_res_to_ofty]), unfolded and read ([type_read_oplace_instr]);
    * [OfRes (&uniqb{'a} (i32 * i32))] is re-read as a shared reference to its referent
      at ['a] ([type_oplace_res_uniq_to_shr_instr], one step), viewed as a pair and read
      below it ([type_read_oplace_pshr_instr], a guarded typed load);
    * the slot is dropped ([type_drop_oplace_res_instr]), freeing the inner box.
  *)
  Definition res_pair_b : expr := (
    (Skip;; Skip;; #☠);;                                         (* resolve x *)
    let: "a" := Load Na1Ord (MInt i32) (ToLit (Load Na1Ord MPtr (ToLit "x"))) in  (* *x.0 *)
    (Skip;; #☠);;                                                (* *x.1 as a shared reference *)
    ReBor;;                                                      (* view *x.1 as a pair *)
    let: "b" := Load Na1Ord (MInt i32)
      (ToLit (Load Na1Ord MPtr (ToLit "x" +ₗ #PTR_SIZE))) in      (* ( *x.1).0 *)
    (((#☠;; delete [ #4; ToLit (Load Na1Ord MPtr (ToLit "x"))]);; #☠);;
      delete [ #(Z.of_nat (PTR_SIZE + PTR_SIZE)); ToLit "x"]);;   (* drop x *)
    jump: "return" ["a"; "b"])%E.

  Definition res_pair_b_spec :
      predl_trans' [at_locₛ (at_locₛ (intₛ i32) * uniq_borₛ (intₛ i32 * intₛ i32))]
        (intₛ i32 * intₛ i32) :=
    λ post '-[(_, ((_, z), m))], λ mask π,
      uniq_bor_future (𝔄:=intₛ i32 * intₛ i32) m π = uniq_bor_current (𝔄:=intₛ i32 * intₛ i32) m →
      post (z, (uniq_bor_current (𝔄:=intₛ i32 * intₛ i32) m).1) mask π.

  Lemma res_pair_b_type ϝ α (k vx: val) :
    ⊢ typed_body [ϝ ⊑ₑ α] [ϝ ⊑ₗ []] (InvCtx [] ϝ AtomicClosed)
        [k ◁cont{[ϝ ⊑ₗ []], InvCtx [] ϝ AtomicClosed,
          λ v: vec val 2, +[vhd v ◁ᵥ i32t; vhd (vtl v) ◁ᵥ i32t] } ret_zz]
        +[vx ◁ᵥ own_bytes (PTR_SIZE + PTR_SIZE) (own_bytes 4 i32t * &uniqb{α} (i32t * i32t))]
        (subst "return" k (subst "x" vx res_pair_b)) res_pair_b_spec.
  Proof.
    rewrite /res_pair_b. simpl_subst.
    iApply (typed_body_impl with "[]"); last first. {
      (* x as an owned place, unfolded *)
      iApply typed_body_tctx_incl.
      { eapply tctx_incl_trans; [apply tctx_own_to_oplace|].
        apply (tctx_unfold_oplace_prod _ _ _ _ PHole (own_bytes 4 i32t) (&uniqb{α} (i32t * i32t))). }
      (* resolve x *)
      iApply type_seq.
      { apply (type_resolve_oplace_res_instr _ _ _ vx (PTR_SIZE + PTR_SIZE)
          (ProdLty (OfTy (own_bytes 4 i32t)) (OfTy (&uniqb{α} (i32t * i32t))))
          (ProdLty (OfRes (own_bytes 4 i32t)) (OfRes (&uniqb{α} (i32t * i32t)))) (1 + 1)).
        apply lty_res_prod; apply lty_res_ofty.
        - apply resolve_keep_just.
        - apply uniq_resolve_keep. solve_typing. }
      { solve_typing. } { reflexivity. }
      (* *x.0: the box is unresolved again, unfolded and read *)
      iApply typed_body_tctx_incl.
      { eapply tctx_incl_trans;
          [apply (tctx_oplace_res_to_ofty _ _ _ _ (PFst PHole (OfRes (&uniqb{α} (i32t * i32t))))
            (own_bytes 4 i32t))|].
        by apply (tctx_unfold_oplace_own _ _ _ _ (PFst PHole (OfRes (&uniqb{α} (i32t * i32t))))
          4 i32t). }
      iApply (type_let with "[]").
      { apply (type_read_oplace_instr _ _ _ vx (PTR_SIZE + PTR_SIZE)
          (PFst (POwn 4 PHole) (OfRes (&uniqb{α} (i32t * i32t)))) i32t). apply _. }
      { solve_typing. } { reflexivity. }
      iIntros (va). simpl_subst.
      (* ( *x.1).0: the resolved unique borrow is a shared reference to its referent *)
      iApply type_seq.
      { apply (type_oplace_res_uniq_to_shr_instr _ _ _ vx (PTR_SIZE + PTR_SIZE)
          (PSnd (OwnPtrLty 4 (OfTy i32t)) PHole) α (i32t * i32t)); [done|solve_typing]. }
      { solve_typing. } { reflexivity. }
      iApply type_seq.
      { apply (type_change_oplace_shr_instr _ _ _ vx (PTR_SIZE + PTR_SIZE)
          (PSnd (OwnPtrLty 4 (OfTy i32t)) PHole) α PHole (OfTy (i32t * i32t))
          (ProdLty (OfTy i32t) (OfTy i32t))); [solve_typing|done|done|by intros]. }
      { solve_typing. } { reflexivity. }
      iApply (type_let with "[]").
      { apply (type_read_oplace_pshr_instr _ _ _ vx (PTR_SIZE + PTR_SIZE)
          (PSnd (OwnPtrLty 4 (OfTy i32t)) PHole) α (PFst PHole (OfTy i32t)) (OfTy i32t));
          [apply _|solve_typing|solve_typing]. }
      { solve_typing. } { reflexivity. }
      iIntros (vb). simpl_subst.
      (* drop x, freeing the inner box *)
      iApply type_seq.
      { apply (type_drop_oplace_res_instr _ _ _ vx (PTR_SIZE + PTR_SIZE)
          (Z.of_nat (PTR_SIZE + PTR_SIZE))
          (ProdLty (OwnPtrLty 4 (OfTy i32t)) (ShrLty (ProdLty (OfTy i32t) (OfTy i32t)) α)));
          [done|by rewrite lty_size_prod|done]. }
      { solve_typing. } { reflexivity. }
      iApply type_jump.
      { rewrite elem_of_list_singleton. reflexivity. }
      { solve_typing. }
      { solve_typing. }
      { reflexivity. }
    }
    intros post [[lx [[lb z] m]] []] mask π. simpl.
    intros Hspec. rewrite /trans_upper /trans_tail /ret_zz /=.
    intros [_ Hres]. apply Hspec.
    destruct m as [[[[[l' [z1 z2]] ξi] d] g] idx]. simpl in *.
    rewrite uniq_bor_future_eq. exact Hres.
  Qed.
End bplace_res.

Print Assumptions res_pair_b_type.
