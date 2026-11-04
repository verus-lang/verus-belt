From iris.proofmode Require Import proofmode.
From lrust.typing Require Export type programs cont int value_ctx own place_own place_resolve place_read place_write.
From lrust.lang Require Import lang notation new_delete.
Set Default Proof Using "Type".

(** * Structs in byte places

[set_mid] of the deleted legacy example [place_struct.v], on bytes: a [repr(C)] struct of
three [i32] fields ([struct_ty] at the layout [c_layout]), in a box of bytes ([own_bytes 12]);
the struct is unfolded into a struct place with a leaf per field ([tctx_unfold_oplace_struct]),
then a field is written with a typed [Store] and another one read with a typed [Load], at the
offsets of the layout ([struct_off]). *)

Section place_struct.
  Context `{!typeG Σ}.

  Notation i32t := (int_ty i32).
  Notation Sl := [intₛ i32; intₛ i32; intₛ i32].
  Notation SL := (c_layout [MInt i32; MInt i32; MInt i32]).
  Notation S := (struct_ty SL +[i32t; i32t; i32t]).

  (*
  ```
  #[repr(C)] struct S { a: i32, b: i32, c: i32 }
  fn set_mid(mut x: S) -> i32 { x.b = 7; x.c }
  ```
  *)
  Definition set_mid : expr := (
    let: "seven" := MLit (VInt 7) in
    "x" +ₗ #(struct_off SL Sl 1) <-{MInt i32} "seven";;          (* x.b = 7 *)
    let: "v" := !ᶜ{MInt i32} ("x" +ₗ #(struct_off SL Sl 2)) in  (* x.c *)
    ((#☠;; (#☠;; (#☠;; #☠)));; delete [ #12; "x"]);;            (* drop x *)
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
      (* x as an owned place, unfolded *)
      iApply typed_body_tctx_incl.
      { eapply tctx_incl_trans; [apply tctx_own_to_oplace|].
        apply (tctx_unfold_oplace_struct _ _ _ _ SL PHole +[i32t; i32t; i32t]). }
      (* x.b = 7 *)
      iApply (type_let with "[]").
      { apply (type_val_int_instr i32). apply (bool_decide_unpack _); by vm_compute. }
      { solve_typing. } { reflexivity. }
      iIntros (v7). simpl_subst.
      iApply type_seq.
      { eapply (type_write_place_instr _ _ _ vx v7
          (POwn 12 (PField SL +[OfTy i32t] PHole +[OfTy i32t])) (OfTy i32t) i32t);
          [apply pctx_wty_same|apply resolve_just|solve_typing]. }
      { solve_typing. } { reflexivity. }
      (* x.c *)
      iApply (type_let with "[]").
      { apply (type_read_place_instr _ _ _ vx
          (POwn 12 (PField SL +[OfTy i32t; OfTy i32t] PHole +[])) (OfTy i32t) i32t static);
          [by constructor|apply _|solve_typing]. }
      { solve_typing. } { reflexivity. }
      iIntros (vv). simpl_subst.
      (* drop x *)
      iApply type_seq.
      { apply (type_drop_oplace_instr _ _ _ vx 12 12
          (StructLty SL +[OfTy i32t; OfTy i32t; OfTy i32t]) (const (const True)));
          [done|done|done|apply lty_resolve_just]. }
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
