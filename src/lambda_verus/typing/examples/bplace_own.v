From iris.proofmode Require Import proofmode.
From lrust.typing Require Export type programs cont int product value_ctx own_bytes uniq_util buniq_bor
  bplace_own bplace_puniq bplace_resolve.
From lrust.lang Require Import lang notation new_delete.
Set Default Proof Using "Type".

(** * Examples of the place machinery on bytes (stage 4 of the MiniRust memory model)

The body of [set_snd] of [typing/examples/place_own.v], on bytes: the argument is a box of
bytes ([own_bytes]); the leaves are read and written with typed [Load] and [Store]; the
borrow [&mut x.1] is a MiniRust pointer value ([&uniqb]); it is written as a place rooted
at its value ([type_uniq_to_vplace_instr], [type_write_vplace_deep_instr]). The body is
stated as a function body ([typed_body], with the return continuation [k]), without the
function type ([fn] still takes legacy boxes). *)

Section bplace_own.
  Context `{!typeG Σ}.

  Notation i32t := (int_ty i32).

  (*
  ```
  fn set_snd(mut x: (i32, i32)) -> i32 {
      { let r = &mut x.1; *r = 5; }   // the borrow ends here
      x.0 = 3;
      x.1
  }
  ```
  *)
  Definition set_snd_b : expr := (
    Newlft;;
    let: "r" := ReBor;; OfLit (ToLit "x" +ₗ #4) in        (* &mut x.1 *)
    let: "five" := MLit (VInt 5) in
    Skip;;                                                (* r as a place *)
    (ReBor;; Store Na1Ord (MInt i32) (ToLit "r") "five");;  (* *r = 5 *)
    Skip;;                                                (* resolve r *)
    Endlft;;                                              (* unblock x.1 *)
    let: "three" := MLit (VInt 3) in
    Store Na1Ord (MInt i32) (ToLit "x") "three";;         (* x.0 = 3 *)
    let: "v" := Load Na1Ord (MInt i32) (ToLit "x" +ₗ #4) in  (* x.1 *)
    ((#☠;; #☠);; delete [ #8; ToLit "x"]);;               (* drop x *)
    jump: "return" ["v"])%E.

  Definition ret_z : predl_trans' [intₛ i32] (intₛ i32) := λ post '-[z], post z.

  Lemma set_snd_b_type ϝ (k vx: val) :
    ⊢ typed_body [] [ϝ ⊑ₗ []] (InvCtx [] ϝ AtomicClosed)
        [k ◁cont{[ϝ ⊑ₗ []], InvCtx [] ϝ AtomicClosed, λ v: vec val 1, +[vhd v ◁ᵥ i32t] } ret_z]
        +[vx ◁ᵥ own_bytes 8 (i32t * i32t)%T]
        (subst "return" k (subst "x" vx set_snd_b))
        (λ post '-[_], λ mask π, post 5%Z mask π).
  Proof.
    rewrite /set_snd_b. simpl_subst.
    iApply (typed_body_impl with "[]"); last first. {
      (* x as an owned place, unfolded *)
      iApply typed_body_tctx_incl.
      { eapply tctx_incl_trans; [apply tctx_own_to_oplace|].
        apply (tctx_unfold_oplace_prod _ _ _ _ PHole i32t i32t). }
      iApply (type_newlft []). iIntros (β).
      (* &mut x.1 *)
      iApply (type_let with "[]").
      { eapply (type_borrow_oplace_instr _ _ _ vx _ β (PSnd (OfTy i32t) PHole) i32t).
        solve_typing. }
      { solve_typing. } { reflexivity. }
      iIntros (vr). simpl_subst.
      (* write through the borrow, as a place; resolve it *)
      iApply (type_let with "[]").
      { apply (type_val_int_instr i32). apply (bool_decide_unpack _); by vm_compute. }
      { solve_typing. } { reflexivity. }
      iIntros (v5). simpl_subst.
      iApply type_seq. { apply (type_uniq_to_vplace_instr _ _ _ vr β i32t). }
      { solve_typing. } { reflexivity. }
      iApply type_seq.
      { apply (type_write_vplace_deep_instr _ _ _ vr v5 (PUniq β PHole) i32t (const (const True)));
          [apply resolve_just|simpl; solve_typing]. }
      { solve_typing. } { simpl. reflexivity. }
      iApply typed_body_tctx_incl.
      { eapply (tctx_incl_frame_r +[_] +[_]). apply tctx_vplace_to_uniq. }
      iApply type_seq. { apply (type_resolve_val_instr vr (&uniqb{β} i32t)). apply buniq_bor.uniq_resolve. solve_typing. }
      { solve_typing. } { reflexivity. }
      (* end β: unblock x.1 *)
      iApply (type_endlft _ _ _ _ β).
      { solve_typing. }
      { apply (unblock_tctx_oplace _ _ _ (PSnd (OfTy i32t) PHole) i32t); [solve_typing|].
        apply unblock_tctx_nil. }
      (* x.0 = 3 *)
      iApply (type_let with "[]").
      { apply (type_val_int_instr i32). apply (bool_decide_unpack _); by vm_compute. }
      { solve_typing. } { reflexivity. }
      iIntros (v3). simpl_subst.
      iApply type_seq.
      { apply (type_write_oplace_instr _ _ _ vx v3 8 (PFst PHole (OfTy i32t)) i32t i32t
          (const (const True))); [done|apply resolve_just|done]. }
      { solve_typing. } { reflexivity. }
      (* x.1 *)
      iApply (type_let with "[]").
      { apply (type_read_oplace_instr _ _ _ vx 8 (PSnd (OfTy i32t) PHole) i32t). apply _. }
      { solve_typing. } { reflexivity. }
      iIntros (vv). simpl_subst.
      (* drop x *)
      iApply type_seq.
      { apply (type_drop_oplace_instr _ _ _ vx 8 8 (ProdLty (OfTy i32t) (OfTy i32t))
          (const (const True))); [done|done|done|apply lty_resolve_just]. }
      { solve_typing. } { reflexivity. }
      (* return x.1 *)
      iApply type_jump.
      { rewrite elem_of_list_singleton. reflexivity. }
      { solve_typing. }
      { solve_typing. }
      { reflexivity. }
    }
    intros post [[lx [a b]] []] mask π Hspec. rewrite /trans_upper /trans_tail /ret_z /=.
    intros [[[[[l1 w1] ζi] d1] g1] idx1] Hc1 _ d g idx Hres
      [[[lx' [a' b']] ζm'] []] (_ & _ & _ & Hfin & _) _ _.
    simpl in Hc1, Hres, Hfin |- *. subst w1.
    rewrite Hfin /oplace_blk_fin /= (uniq_util.uniq_prvar_app_irrel b 5%Z ζi π) Hres. apply Hspec.
  Qed.
End bplace_own.

Print Assumptions set_snd_b_type.
