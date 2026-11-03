From iris.proofmode Require Import proofmode.
From lrust.typing Require Export type programs cont int product value_ctx own shr_bor uniq_util uniq_bor place_own place_puniq place_resolve place_pshr place_res place_res_rslv place_res_ops place_read place_share.
From lrust.lang Require Import lang notation new_delete.
Set Default Proof Using "Type".

(** * Resolving the root of a place, and sharing below it

A unique borrow argument is resolved at its root ([type_resolve_place_instr] with
[K = PHole], [vroot_res_uniq_leaf]) and its referent is then shared below the resolved
borrow ([type_share_place_instr] with [K = PResUniq 'a PHole]). *)

Section place_res_root.
  Context `{!typeG Σ}.

  Notation i32t := (int_ty i32).

  (*
  ```
  fn downgrade<'a>(x: &'a mut (i32, i32)) -> &'a (i32, i32) { &*x }
  ```
  `x` is resolved first (it is not used mutably again), learning `fin(x) == cur(x)`; the
  result is a shared reference to its referent at ['a], and the resolved place is
  forgotten.
  *)
  Definition downgrade : expr := (
    Skip;;                                   (* x as a place *)
    (Skip;; #☠);;                            (* resolve x *)
    let: "r" := &ˢ "x" in            (* &*x *)
    jump: "return" ["r"])%E.

  Definition ret_pair : predl_trans' [at_locₛ (intₛ i32 * intₛ i32)] (at_locₛ (intₛ i32 * intₛ i32)) :=
    λ post '-[r], post r.

  Definition downgrade_spec :
      predl_trans' [uniq_borₛ (intₛ i32 * intₛ i32)] (at_locₛ (intₛ i32 * intₛ i32)) :=
    λ post '-[m], λ mask π, ∀ r: ~~ (at_locₛ (intₛ i32 * intₛ i32)),
      r.2 = uniq_bor_current (𝔄:=intₛ i32 * intₛ i32) m →
      uniq_bor_future (𝔄:=intₛ i32 * intₛ i32) m π =
        vπ (uniq_bor_current (𝔄:=intₛ i32 * intₛ i32) m) π →
      post r mask π.

  Lemma downgrade_type ϝ α (k vx: val) :
    ⊢ typed_body [ϝ ⊑ₑ α] [ϝ ⊑ₗ []] (InvCtx [] ϝ AtomicClosed)
        [k ◁cont{[ϝ ⊑ₗ []], InvCtx [] ϝ AtomicClosed,
          λ v: vec val 1, +[vhd v ◁ᵥ &shr{α} (i32t * i32t)] } ret_pair]
        +[vx ◁ᵥ &uniq{α} (i32t * i32t)]
        (subst "return" k (subst "x" vx downgrade)) downgrade_spec.
  Proof.
    rewrite /downgrade. simpl_subst.
    iApply (typed_body_impl with "[]"); last first. {
      (* x as a place rooted at its value *)
      iApply type_seq. { apply (type_uniq_to_vplace_instr _ _ _ vx α (i32t * i32t)). }
      { solve_typing. } { reflexivity. }
      (* resolve x at its root *)
      iApply type_seq.
      { eapply (type_resolve_place_instr _ _ _ vx PHole (UniqLty (OfTy (i32t * i32t)) α));
          [apply pctx_res_root; apply vroot_res_uniq_leaf; solve_typing|done]. }
      { solve_typing. } { reflexivity. }
      (* &*x, below the resolved borrow *)
      iApply (type_let with "[]").
      { eapply (type_share_place_instr _ _ _ vx (PResUniq α PHole) α
          (OfTy (i32t * i32t)) (i32t * i32t)); [split; [constructor|done]|simpl; solve_typing..]. }
      { solve_typing. } { reflexivity. }
      iIntros (vr). simpl_subst.
      (* forget the resolved place *)
      iApply typed_body_tctx_incl. { apply (tctx_incl_resolve_lower +[_] +[_]). }
      iApply type_jump.
      { rewrite elem_of_list_singleton. reflexivity. }
      { solve_typing. }
      { solve_typing. }
      { reflexivity. }
    }
    intros post [m []] mask π. simpl.
    destruct m as [[[[[l [z1 z2]] ξi] d] g] idx]. simpl.
    intros Hspec. rewrite /trans_upper /trans_tail /ret_pair /=.
    intros Hres. apply Hspec; [done|]. by rewrite uniq_bor_future_eq.
  Qed.
End place_res_root.

Print Assumptions downgrade_type.
