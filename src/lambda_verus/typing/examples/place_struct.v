From iris.proofmode Require Import proofmode.
From lrust.typing Require Export type programs cont int product value_ctx own place_own place_resolve place_xprod.
From lrust.lang Require Import lang notation new_delete.
Set Default Proof Using "Type".

(** * N-ary products in byte places

[set_mid] of the deleted legacy example [place_struct.v], on bytes: a struct of three [i32] fields
as an n-ary product [Π!], in a box of bytes ([own_bytes 12]); the product is unfolded field
by field ([tctx_unfold_oplace_xprod] of [typing/place_xprod.v], three times), then a
field is written with a typed [Store] and another one read with a typed [Load]. *)

Section place_struct.
  Context `{!typeG Σ}.

  Notation i32t := (int_ty i32).
  Notation S := (Π! +[i32t; i32t; i32t])%T.
  Notation Sₛ := (Π! [intₛ i32; intₛ i32; intₛ i32])%ST.

  (*
  ```
  struct S { a: i32, b: i32, c: i32 }
  fn set_mid(mut x: S) -> i32 { x.b = 7; x.c }
  ```
  *)
  Definition set_mid : expr := (
    let: "seven" := MLit (VInt 7) in
    Store Na1Ord (MInt i32) (ToLit "x" +ₗ #4) "seven";;          (* x.b = 7 *)
    let: "v" := Load Na1Ord (MInt i32) (ToLit "x" +ₗ #4 +ₗ #4) in (* x.c *)
    ((#☠;; (#☠;; (#☠;; #☠)));; delete [ #12; ToLit "x"]);;         (* drop x *)
    jump: "return" ["v"])%E.

  Definition ret_z : predl_trans' [intₛ i32] (intₛ i32) := λ post '-[z], post z.

  Lemma set_mid_type ϝ (k vx: val) :
    ⊢ typed_body [] [ϝ ⊑ₗ []] (InvCtx [] ϝ AtomicClosed)
        [k ◁cont{[ϝ ⊑ₗ []], InvCtx [] ϝ AtomicClosed, λ v: vec val 1, +[vhd v ◁ᵥ i32t] } ret_z]
        +[vx ◁ᵥ own_bytes 12 S]
        (subst "return" k (subst "x" vx set_mid))
        (λ post '-[(_, -[_; _; c])], λ mask π, post c mask π).
  Proof.
    rewrite /set_mid. simpl_subst.
    iApply (typed_body_impl with "[]"); last first. {
      (* x as an owned place, unfolded field by field *)
      iApply typed_body_tctx_incl.
      { eapply tctx_incl_trans; [apply tctx_own_to_oplace|].
        eapply tctx_incl_trans;
          [apply (tctx_unfold_oplace_xprod _ _ _ _ PHole i32t +[i32t; i32t]); done|].
        eapply tctx_incl_trans;
          [apply (tctx_unfold_oplace_xprod _ _ _ _ (PSnd (OfTy i32t) PHole) i32t +[i32t]); done|].
        apply (tctx_unfold_oplace_xprod _ _ _ _ (PSnd (OfTy i32t) (PSnd (OfTy i32t) PHole))
          i32t +[]).
        done. }
      simpl.
      (* x.b = 7 *)
      iApply (type_let with "[]").
      { apply (type_val_int_instr i32). apply (bool_decide_unpack _); by vm_compute. }
      { solve_typing. } { reflexivity. }
      iIntros (v7). simpl_subst.
      iApply type_seq.
      { apply (type_write_oplace_instr _ _ _ vx v7 12
          (PSnd (OfTy i32t) (PFst PHole (ProdLty (OfTy i32t) (OfTy (Π! +[]))))) i32t i32t
          (const (const True))); [done|apply resolve_just|done]. }
      { solve_typing. } { reflexivity. }
      simpl.
      (* x.c *)
      iApply (type_let with "[]").
      { apply (type_read_oplace_instr _ _ _ vx 12
          (PSnd (OfTy i32t) (PSnd (OfTy i32t) (PFst PHole (OfTy (Π! +[]))))) i32t). apply _. }
      { solve_typing. } { reflexivity. }
      iIntros (vv). simpl_subst.
      (* drop x *)
      iApply type_seq.
      { apply (type_drop_oplace_instr _ _ _ vx 12 12
          (ProdLty (OfTy i32t) (ProdLty (OfTy i32t) (ProdLty (OfTy i32t) (OfTy (Π! +[])))))
          (const (const True))); [done|done|done|apply lty_resolve_just]. }
      { solve_typing. } { reflexivity. }
      iApply type_jump.
      { rewrite elem_of_list_singleton. reflexivity. }
      { solve_typing. }
      { solve_typing. }
      { reflexivity. }
    }
    intros post [[lx [a1 [a2 [a3 []]]]] []] mask π Hspec.
    rewrite /trans_upper /trans_tail /ret_z /=. auto.
  Qed.
End place_struct.

Print Assumptions set_mid_type.
