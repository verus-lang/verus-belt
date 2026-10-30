From iris.proofmode Require Import proofmode.
From lrust.typing Require Export type programs cont int product sum value_ctx own_bytes shr_bytes
  uniq_util uniq_bor buniq_bor bplace_own bplace_puniq bplace_resolve bplace_pshr.
From lrust.lang Require Import lang notation new_delete.
Set Default Proof Using "Type".

(** * Places below shared references, on bytes

The examples of [typing/examples/place_pshr.v], on bytes ([typing/bplace_pshr.v]): the
reads, shared borrows and case analyses below shared references are guarded typed [Load]s,
whose addresses are computed by guarded typed loads of the pointers on the path. The
arguments are MiniRust values ([◁ᵥ]): a shared reference ([get_snd], the root of the place
is the reference itself), a box of bytes holding a shared reference ([get_boxed],
[get_or_zero], the root is the box) and a unique borrow of a shared reference
([first_ref], the root is the unique borrow). *)

Section bplace_pshr.
  Context `{!typeG Σ}.

  Notation i32t := (int_ty i32).

  Definition ret_z : predl_trans' [intₛ i32] (intₛ i32) := λ post '-[z], post z.

  (*
  ```
  fn get_snd<'a, 'b>(x: &'a &'b (i32, i32)) -> i32 { ( **x).1 }
  ```
  The argument is a shared reference value, the root of the place; the view of its
  referent is changed to [ShrLty (ProdLty (OfTy i32) (OfTy i32)) 'b] (no program step),
  and [( **x).1] is read with [K2 = PShr 'b (PSnd _ PHole)]: a guarded load of the inner
  reference, a field offset, and a guarded typed load of [i32].
  *)
  Definition get_snd_pb : expr := (
    let: "v" := Load Na1Ord (MInt i32) (ToLit (Load Na1Ord MPtr (ToLit "x")) +ₗ #4) in
    jump: "return" ["v"])%E.

  Lemma get_snd_pb_type ϝ α β (k vx: val) :
    ⊢ typed_body [ϝ ⊑ₑ α; α ⊑ₑ β] [ϝ ⊑ₗ []] (InvCtx [] ϝ AtomicClosed)
        [k ◁cont{[ϝ ⊑ₗ []], InvCtx [] ϝ AtomicClosed, λ v: vec val 1, +[vhd v ◁ᵥ i32t] } ret_z]
        +[vx ◁ᵥ &shrb{α} (&shrb{β} (i32t * i32t))]
        (subst "return" k (subst "x" vx get_snd_pb))
        (λ post '-[(_, (_, (_, z2)))], λ mask π, post z2 mask π).
  Proof.
    rewrite /get_snd_pb. simpl_subst.
    iApply (typed_body_impl with "[]"); last first. {
      iApply typed_body_tctx_incl.
      { eapply tctx_incl_trans; [apply tctx_ty_to_vplace|].
        eapply tctx_incl_trans; [apply tctx_vplace_unfold_shr|].
        apply (tctx_change_vplace_shr _ _ vx α PHole (OfTy (&shrb{β} (i32t * i32t)))
          (ShrLty (ProdLty (OfTy i32t) (OfTy i32t)) β)); [done|done|by intros]. }
      (* ( **x).1 *)
      iApply (type_let with "[]").
      { apply (type_read_vplace_pshr_root_instr _ _ _ vx α (PShr β (PSnd (OfTy i32t) PHole))
          (OfTy i32t)); [apply _|solve_typing]. }
      { solve_typing. } { reflexivity. }
      iIntros (vv). simpl_subst.
      (* drop x *)
      iApply typed_body_tctx_incl. { eapply tctx_incl_tail. apply tctx_drop_vplace_shr. }
      iApply type_jump.
      { rewrite elem_of_list_singleton. reflexivity. }
      { solve_typing. }
      { solve_typing. }
      { reflexivity. }
    }
    intros post [[l1 [l2 [z1 z2]]] []] mask π. simpl.
    rewrite /trans_upper /trans_tail /ret_z /=. auto.
  Qed.

  (*
  ```
  fn get_boxed(b: Box<&'a (i32, Box<i32>)>) -> i32 { *( **b).1 }
  ```
  The argument is a box of bytes, the root of the place: the shared reference in it is
  unfolded ([K = PHole] of the own-rooted place), the view of its referent is changed to
  [ProdLty (OfTy i32) (OwnPtrLty 4 (OfTy i32))], and the leaf is read below [PShr] through
  the inner box ([K2 = PSnd _ (POwn 4 PHole)]). Dropping the slot frees the outer box (the
  inner one belongs to the referent of the shared reference).
  *)
  Definition get_boxed_pb : expr := (
    ReBor;;                                                    (* unfold *b *)
    ReBor;;                                                    (* view **b as a pair *)
    let: "v" := Load Na1Ord (MInt i32)
      (ToLit (Load Na1Ord MPtr (ToLit (Load Na1Ord MPtr (ToLit "b")) +ₗ #4))) in  (* *( **b).1 *)
    (#☠;; delete [ #(Z.of_nat PTR_SIZE); ToLit "b"]);;         (* drop b *)
    jump: "return" ["v"])%E.

  Lemma get_boxed_pb_type ϝ α (k vb: val) :
    ⊢ typed_body [ϝ ⊑ₑ α] [ϝ ⊑ₗ []] (InvCtx [] ϝ AtomicClosed)
        [k ◁cont{[ϝ ⊑ₗ []], InvCtx [] ϝ AtomicClosed, λ v: vec val 1, +[vhd v ◁ᵥ i32t] } ret_z]
        +[vb ◁ᵥ own_bytes PTR_SIZE (&shrb{α} (i32t * own_bytes 4 i32t))]
        (subst "return" k (subst "b" vb get_boxed_pb))
        (λ post '-[(_, (_, (_, (_, w))))], λ mask π, post w mask π).
  Proof.
    rewrite /get_boxed_pb. simpl_subst.
    iApply (typed_body_impl with "[]"); last first. {
      iApply typed_body_tctx_incl; [apply tctx_own_to_oplace|].
      (* unfold *b *)
      iApply type_seq.
      { apply (type_unfold_oplace_shr_instr _ _ _ vb PTR_SIZE PHole α (i32t * own_bytes 4 i32t)).
        solve_typing. }
      { solve_typing. } { reflexivity. }
      (* view **b as a pair with a box *)
      iApply type_seq.
      { apply (type_change_oplace_shr_instr _ _ _ vb PTR_SIZE PHole α PHole
          (OfTy (i32t * own_bytes 4 i32t)) (ProdLty (OfTy i32t) (OwnPtrLty 4 (OfTy i32t))));
          [solve_typing|done|done|by intros]. }
      { solve_typing. } { reflexivity. }
      (* *( **b).1 *)
      iApply (type_let with "[]").
      { apply (type_read_oplace_pshr_instr _ _ _ vb PTR_SIZE PHole α
          (PSnd (OfTy i32t) (POwn 4 PHole)) (OfTy i32t)); [apply _|solve_typing|solve_typing]. }
      { solve_typing. } { reflexivity. }
      iIntros (vv). simpl_subst.
      (* drop b *)
      iApply type_seq.
      { apply (type_drop_oplace_deep_instr _ _ _ vb PTR_SIZE (Z.of_nat PTR_SIZE)
          (ShrLty (ProdLty (OfTy i32t) (OwnPtrLty 4 (OfTy i32t))) α)); [done|done|done|].
        apply lty_rslv_shr. }
      { solve_typing. } { reflexivity. }
      iApply type_jump.
      { rewrite elem_of_list_singleton. reflexivity. }
      { solve_typing. }
      { solve_typing. }
      { reflexivity. }
    }
    intros post [[lb [l1 [z [lb' w]]]] []] mask π. simpl.
    rewrite /trans_upper /trans_tail /ret_z /=. auto.
  Qed.
End bplace_pshr.

Print Assumptions get_snd_pb_type.
Print Assumptions get_boxed_pb_type.
