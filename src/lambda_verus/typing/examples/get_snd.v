From iris.proofmode Require Import proofmode.
From lrust.typing Require Export type programs cont int product value_ctx own shr_bor place_own place_shr place_resolve.
From lrust.lang Require Import lang notation new_delete.
Set Default Proof Using "Type".

(** * [get_snd] on bytes

The body of [get_snd] of the deleted legacy example [place_pshr.v], on bytes: the argument is a box
of bytes holding a shared reference to a shared reference ([&shrb]); the two references
are loaded with typed [Load]s of [MPtr] (the second one a guarded load), the shared
reference to the field [.1] is a pointer offset ([type_shr_bytes_snd_instr]), and the
field is read with a guarded typed [Load] of [i32]. The reads below shared references go
through shared references, not through shared places: the shared places of
[place_pshr.v] are not ported to bytes yet. *)

Section get_snd.
  Context `{!typeG Σ}.

  Notation i32t := (int_ty i32).

  (*
  ```
  fn get_snd<'a, 'b>(x: &'a &'b (i32, i32)) -> i32 { ( **x).1 }
  ```
  *)
  Definition get_snd : expr := (
    let: "x1" := Load Na1Ord MPtr (ToLit "x") in             (* *x *)
    let: "x2" := Load Na1Ord MPtr (ToLit "x1") in            (* **x *)
    let: "x3" := OfLit (ToLit "x2" +ₗ #4) in                 (* &( **x).1 *)
    let: "v" := Load Na1Ord (MInt i32) (ToLit "x3") in       (* ( **x).1 *)
    Skip;; Skip;;                                            (* drop x1, x3 *)
    (#☠;; delete [ #(Z.of_nat PTR_SIZE); ToLit "x"]);;        (* drop x *)
    jump: "return" ["v"])%E.

  Definition ret_z : predl_trans' [intₛ i32] (intₛ i32) := λ post '-[z], post z.

  Lemma get_snd_type ϝ α β (k vx: val) :
    ⊢ typed_body [ϝ ⊑ₑ α; α ⊑ₑ β] [ϝ ⊑ₗ []] (InvCtx [] ϝ AtomicClosed)
        [k ◁cont{[ϝ ⊑ₗ []], InvCtx [] ϝ AtomicClosed, λ v: vec val 1, +[vhd v ◁ᵥ i32t] } ret_z]
        +[vx ◁ᵥ own_bytes PTR_SIZE (&shr{α} (&shr{β} (i32t * i32t)))%T]
        (subst "return" k (subst "x" vx get_snd))
        (λ post '-[(_, (_, (_, (_, z2))))], λ mask π, post z2 mask π).
  Proof.
    rewrite /get_snd. simpl_subst.
    iApply (typed_body_impl with "[]"); last first. {
      (* *x *)
      iApply (type_let with "[]").
      { apply (type_load_own_bytes_copy_instr PTR_SIZE (&shr{α} (&shr{β} (i32t * i32t)))).
        apply shr_bytes_copy. }
      { solve_typing. } { reflexivity. }
      iIntros (v1). simpl_subst.
      (* **x *)
      iApply (type_let with "[]").
      { apply (type_load_shr_bytes_copy_instr α (&shr{β} (i32t * i32t))); [apply shr_bytes_copy|].
        solve_typing. }
      { solve_typing. } { reflexivity. }
      iIntros (v2). simpl_subst.
      (* &( **x).1 *)
      iApply (type_let with "[]").
      { apply (type_shr_bytes_snd_instr β i32t i32t). }
      { solve_typing. } { reflexivity. }
      iIntros (v3). simpl_subst.
      (* ( **x).1 *)
      iApply (type_let with "[]").
      { apply (type_load_shr_bytes_copy_instr β i32t); [apply _|solve_typing]. }
      { solve_typing. } { reflexivity. }
      iIntros (vv). simpl_subst.
      (* drop the shared references *)
      iApply type_seq. { apply (type_resolve_val_instr v1 (&shr{α} (&shr{β} (i32t * i32t)))).
        apply resolve_just. }
      { solve_typing. } { reflexivity. }
      iApply type_seq. { apply (type_resolve_val_instr v3 (&shr{β} i32t)). apply resolve_just. }
      { solve_typing. } { reflexivity. }
      (* drop x *)
      iApply typed_body_tctx_incl.
      { eapply tctx_incl_tail. apply tctx_own_to_oplace. }
      iApply type_seq.
      { apply (type_drop_oplace_instr _ _ _ vx PTR_SIZE (Z.of_nat PTR_SIZE)
          (OfTy (&shr{α} (&shr{β} (i32t * i32t)))) (const (const True)));
          [done|done|done|apply lty_resolve_just]. }
      { solve_typing. } { reflexivity. }
      iApply type_jump.
      { rewrite elem_of_list_singleton. reflexivity. }
      { solve_typing. }
      { solve_typing. }
      { reflexivity. }
    }
    intros post [[lx [l1 [l2 [z1 z2]]]] []] mask π. simpl.
    rewrite /trans_upper /trans_tail /ret_z /=. auto.
  Qed.
End get_snd.

Print Assumptions get_snd_type.
