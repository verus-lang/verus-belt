From iris.proofmode Require Import proofmode.
From lrust.typing Require Export type programs cont int product value_ctx own uniq_util uniq_bor place_own place_puniq place_resolve.
From lrust.lang Require Import lang notation new_delete.
Set Default Proof Using "Type".

(** * [get_first] on bytes

The body of [get_first] of the deleted legacy example [get_first.v], with the argument a MiniRust
pointer value of type [&uniq{α} (i32 * i32)] (a root value, [◁ᵥ]) rather than a box, and
the result returned as a value. *)

Section get_first.
  Context `{!typeG Σ}.

  Notation i32t := (int_ty i32).

  (*
  ```
  fn get_first<'a>(x: &'a mut (i32, i32)) -> &'a mut i32 {
      &mut x.0
  }
  ```
  *)
  Definition get_first : expr := (
    Skip;;                                          (* b as a place *)
    ReBor;;                                         (* unfold *b *)
    let: "r0" := ReBor;; OfLit (ToLit "b") in       (* &mut ( *b).0 *)
    let: "r1" := ReBor;; OfLit (ToLit "b" +ₗ #4) in (* &mut ( *b).1, to drop b *)
    Skip;;                                          (* resolve r1 *)
    jump: "return" ["r0"])%E.

  Definition ret_uniq : predl_trans' [uniq_borₛ (intₛ i32)] (uniq_borₛ (intₛ i32)) :=
    λ post '-[r], post r.

  Definition get_first_spec :
      predl_trans' [uniq_borₛ (intₛ i32 * intₛ i32)] (uniq_borₛ (intₛ i32)) :=
    λ post '-[m], λ mask π, ∀ r: ~~ (uniq_borₛ (intₛ i32)),
      uniq_bor_current r = (uniq_bor_current (𝔄:=intₛ i32 * intₛ i32) m).1 →
      uniq_bor_future (𝔄:=intₛ i32 * intₛ i32) m π =
        (uniq_bor_future r π, (uniq_bor_current (𝔄:=intₛ i32 * intₛ i32) m).2) →
      post r mask π.

  Lemma get_first_type ϝ α (k vb: val) :
    ⊢ typed_body [ϝ ⊑ₑ α] [ϝ ⊑ₗ []] (InvCtx [] ϝ AtomicClosed)
        [k ◁cont{[ϝ ⊑ₗ []], InvCtx [] ϝ AtomicClosed,
          λ v: vec val 1, +[vhd v ◁ᵥ &uniq{α ⊓ α} i32t] } ret_uniq]
        +[vb ◁ᵥ &uniq{α} (i32t * i32t)%T]
        (subst "return" k (subst "b" vb get_first)) get_first_spec.
  Proof.
    rewrite /get_first. simpl_subst.
    iApply (typed_body_impl with "[]"); last first. {
      (* b as a place rooted at its value, and its referent unfolded *)
      iApply type_seq. { apply (type_uniq_to_vplace_instr _ _ _ vb α (i32t * i32t)). }
      { solve_typing. } { reflexivity. }
      iApply type_seq.
      { apply (type_unfold_vplace_prod_instr _ _ _ vb (PUniq α PHole) i32t i32t). simpl. solve_typing. }
      { solve_typing. } { reflexivity. }
      (* &mut ( *b).0, at α ⊓ α *)
      iApply (type_let with "[]").
      { apply (type_borrow_vplace_deep_instr _ _ _ vb α (PUniq α (PFst PHole (OfTy i32t))) i32t);
          [done|simpl; solve_typing|solve_typing]. }
      { solve_typing. } { simpl. reflexivity. }
      iIntros (vr0). simpl_subst.
      (* &mut ( *b).1, at α ⊓ α *)
      iApply (type_let with "[]").
      { apply (type_borrow_vplace_deep_instr _ _ _ vb α
          (PUniq α (PSnd (Blocked i32t (α ⊓ α)) PHole)) i32t); [done|simpl; solve_typing|solve_typing]. }
      { solve_typing. } { simpl. reflexivity. }
      iIntros (vr1). simpl_subst.
      (* resolve the borrow of field 1 *)
      iApply type_seq.
      { apply (type_resolve_val_instr vr1 (&uniq{α ⊓ α} i32t)). apply uniq_bor.uniq_resolve.
        solve_typing. }
      { solve_typing. } { reflexivity. }
      (* drop b while both fields are blocked *)
      iApply typed_body_tctx_incl.
      { apply (tctx_incl_frame_r +[_] +[]). apply tctx_drop_vplace_uniq; [solve_typing|done|done]. }
      (* return the reborrow of field 0 *)
      iApply type_jump.
      { rewrite elem_of_list_singleton. reflexivity. }
      { solve_typing. }
      { solve_typing. }
      { reflexivity. }
    }
    intros post [m []] mask π. simpl.
    destruct m as [[[[[l [x1 x2]] ξi] d] g] idx]. simpl.
    intros Hspec. rewrite /trans_upper /trans_tail /ret_uniq /=.
    intros m1 Hc1 m2 Hc2 Hres Hfin.
    apply Hspec; [done|]. rewrite Hfin.
    destruct m1 as [[[[[l1 y1] ζi] d1] g1] idx1].
    destruct m2 as [[[[[l2 y2] ηi] d2] g2] idx2].
    simpl in Hc1, Hc2, Hres. subst y1 y2.
    rewrite !uniq_bor_future_eq. f_equal. exact Hres.
  Qed.
End get_first.

Print Assumptions get_first_type.
