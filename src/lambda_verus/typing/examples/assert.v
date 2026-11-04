From iris.proofmode Require Import proofmode.
From lrust.typing Require Export type programs bool cont unit value_ctx function.
From lrust.lang Require Import lang notation.
Set Default Proof Using "Type".

Section assert.
  Context `{!typeG Σ}.

  (* assert takes a bool argument b and performs undefined behavior if !b
     It's more like Rust's `assert_unchecked`.
     The argument is a MiniRust boolean value, which [if:] cases on.
  *)
  Definition assert : val :=
    fn: ["b"] :=
      if: "b" then
        let: "r" := MkTuple [] in
        return: ["r"]
      else
        let: "r" := Load Na1Ord MPtr #☠ in (* undefined behavior *)
        return: ["r"]
    .

  (* verify `assert(b)` with precondition `b` *)
  Lemma assert_type :
    typed_val
        assert
        ((fn(∅; bool_ty) → ()) (λ (c: ~~ ()) 𝛷 '-[b] , λ mask π, b ∧ ∀ ret, 𝛷 ret mask π))
        (assert, ()).
  Proof.
    unfold assert. unlock.
    opose proof (@type_fn
        _ _ _
        [boolₛ]
        ()
        ()
        ()
        (λ y: (), FP ∅ +[bool_ty] () AtomicClosed)
        (λ (c: ~~ ()) 𝛷 '-[b] , λ mask π, b ∧ ∀ ret, 𝛷 ret mask π)
        (_)
        [BNamed "b"] _ _ _
    ) as H.
    unlock in H. apply H. clear H.
    intros c ϝ k wl.
    destruct wl as [vb []]. simpl_subst.
    iApply (typed_body_impl with "[]"); last first. {
      iApply (type_if_val _ _ +[]).
      { solve_typing. }
      (* branch 1 *)
      - iApply (type_let with "[]").
        { apply type_val_unit_instr. }
        { apply tctx_extract_ctx_nil. }
        { reflexivity. }
        iIntros (r). simpl_subst. iApply type_jump.
        + rewrite elem_of_list_singleton. reflexivity.
        + solve_typing.
        + apply resolve_tctx_nil.
        + reflexivity.
      (* branch 2 *)
      - iApply typed_body_vacuous.
    }
    intros post [b []] mask π.
    simpl. unfold trans_upper. simpl.
    intros [Hb Hforall]. destruct b; last by done.
    rewrite /trans_tail /tr_ret /=. intros. apply Hforall.
  Qed.

End assert.
