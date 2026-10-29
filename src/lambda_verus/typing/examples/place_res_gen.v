From iris.proofmode Require Import proofmode.
From lrust.typing Require Export type function product programs own cont uninit int
  uniq_bor borrow place_own place_resolve place_puniq place_res place_res_rslv
  place_res_ops.
From lrust.lang Require Import lang notation new_delete.
Set Default Proof Using "Type".

Section place_res_gen.
  Context `{!typeG Σ}.

  (*
  Resolving a leaf of an arbitrary generic type, then dropping it:

  ```
  fn res_gen<T>(x: T) { /* resolve x */ }   // x is dropped
  ```

  for an abstract type [T] (of size 1), with no assumption on it (in particular no
  [ResOwn T], no [Copy T]). The argument slot [x] is an owned place [own (OfTy T)]; it is
  resolved ([type_resolve_oplace_res_instr], [lty_res_ofty] with the generic
  [resolve_keep_just], nothing learnt, no lifetime needs to be alive) to [own (OfRes T)],
  and the slot is dropped ([type_drop_oplace_res_instr]).

  For an abstract [T] the resolved leaf [OfRes T] cannot be read: its resolved ownership
  [ty_gho_res T] is only known to follow from the ownership ([ty_gho_res_of_own]), not to
  give it back ([ResOwn]); a [Copy] type is instead resolved from a copy of its
  ownership and kept readable ([res_gen_copy] below).
  *)

  Context {𝔄} (T: type 𝔄).
  Hypothesis (HsT: ty_size T = 1%nat).

  Definition res_gen : val :=
    fn: ["x"] :=
      (Skip;; #☠);;                                  (* resolve x *)
      (#☠;; delete [ #1; "x"]);;                     (* drop x *)
      let: "ret" := new [ #0] in
      return: ["ret"].

  Definition res_gen_spec : fn_spec [𝔄] () () :=
    λ _ post '-[(_, x)], λ mask π, ∀ ret, post ret mask π.

  Lemma res_gen_type :
    typed_val res_gen ((fn(∅; T) → ()) res_gen_spec) (res_gen, ()).
  Proof using HsT T typeG0 Σ 𝔄.
    unfold res_gen. unlock.
    opose proof (@type_fn _ _ _ [𝔄] () () ()
      (λ _: (), FP ∅ +[T] () AtomicClosed)
      res_gen_spec _ [BNamed "x"] _ _ _) as H.
    unlock in H. apply H. clear H.
    intros c ϝ k wl. destruct wl as [vx []]. simpl_subst.
    iApply (typed_body_impl with "[]"); last first. {
      iApply typed_body_tctx_incl; [apply tctx_own_to_oplace|].
      rewrite HsT.
      (* resolve x, for an arbitrary T *)
      iApply type_seq.
      { apply (type_resolve_oplace_res_instr _ _ _ vx 1 (OfTy T) (OfRes T) 1
          (λ x _ _, const (const True) x)).
        apply lty_res_ofty, resolve_keep_just. }
      { solve_typing. } { reflexivity. }
      (* drop x *)
      iApply type_seq.
      { apply (type_drop_oplace_res_instr _ _ _ vx 1 1 (OfRes T)); [done|by rewrite /= HsT|done]. }
      { solve_typing. } { reflexivity. }
      iApply (type_new_subtype () 0). { lia. } { apply uninit_unit_1. }
      iIntros (vret). simpl_subst.
      iApply type_jump.
      { rewrite elem_of_list_singleton. reflexivity. }
      { solve_typing. }
      { solve_typing. }
      { reflexivity. }
    }
    intros post [[lx x] []] mask π. simpl.
    intros Hspec. rewrite /trans_upper /trans_tail /=.
    intros _ l0 junk. apply Hspec.
    Unshelve. eapply (composeₛ empty_prod_to_unitₛ uninit0_to_unitₛ).
  Qed.

  (*
  Resolving a leaf of a generic [Copy] type, keeping it readable:

  ```
  fn res_gen_copy<T: Copy>(x: T) -> T { /* resolve x */ x }
  ```

  for an abstract [Copy] type [T] (of size 1, no [ResOwn T]) whose resolution is
  [resolve E L T ΦT], with the specification `ensures result == x` and the observation
  `ΦT x`, learnt when [x] is resolved. The slot [x] is resolved from a copy of the
  ownership of its value ([lty_res_copy]), so it stays [own (OfTy T)]; it is read and
  dropped.
  *)

  Context `{!Copy T} (ΦT: ~~𝔄 → proph_asn → Prop).
  Hypothesis (HrT: ∀ E L, resolve E L T ΦT).

  Definition res_gen_copy : val :=
    fn: ["x"] :=
      (Skip;; #☠);;                                  (* resolve x *)
      let: "v" := !"x" in
      (#☠;; delete [ #1; "x"]);;                     (* drop x *)
      let: "ret" := new [ #1] in
      "ret" <- "v";;
      return: ["ret"].

  Definition res_gen_copy_spec : fn_spec [𝔄] 𝔄 () :=
    λ _ post '-[(_, x)], λ mask π, ΦT x π → ∀ (lr: loc), post (lr, x) mask π.

  Lemma res_gen_copy_type :
    typed_val res_gen_copy ((fn(∅; T) → T) res_gen_copy_spec) (res_gen_copy, ()).
  Proof using Copy0 HrT HsT T typeG0 Σ ΦT 𝔄.
    unfold res_gen_copy. unlock.
    opose proof (@type_fn _ _ _ [𝔄] 𝔄 () ()
      (λ _: (), FP ∅ +[T] T AtomicClosed)
      res_gen_copy_spec _ [BNamed "x"] _ _ _) as H.
    unlock in H. apply H. clear H.
    intros c ϝ k wl. destruct wl as [vx []]. simpl_subst.
    iApply (typed_body_impl with "[]"); last first. {
      iApply typed_body_tctx_incl; [apply tctx_own_to_oplace|].
      rewrite HsT.
      (* resolve x, keeping it as it is *)
      iApply type_seq.
      { apply (type_resolve_oplace_res_instr _ _ _ vx 1 (OfTy T) (OfTy T) 1 (λ x _ _, ΦT x)).
        apply lty_res_copy; [apply _|apply HrT]. }
      { solve_typing. } { reflexivity. }
      (* it is still readable *)
      iApply (type_let with "[]").
      { apply (type_read_oplace_instr _ _ _ vx 1 PHole T); [done|apply _]. }
      { solve_typing. } { reflexivity. }
      iIntros (vv). simpl_subst.
      (* drop x *)
      iApply type_seq.
      { apply (type_drop_oplace_res_instr _ _ _ vx 1 1 (OfTy T)); [done|by rewrite /= HsT|done]. }
      { solve_typing. } { reflexivity. }
      iApply (type_new 1). { lia. } iIntros (vret). simpl_subst.
      iApply type_assign. { solve_typing. } { apply write_own. by rewrite HsT. }
      { apply (resolve'_just _ _ _ (const True)). apply resolve_just. }
      rewrite /box HsT.
      iApply type_jump.
      { rewrite elem_of_list_singleton. reflexivity. }
      { solve_typing. }
      { solve_typing. }
      { reflexivity. }
    }
    intros post [[lx x] []] mask π. simpl.
    intros Hspec. rewrite /trans_upper /trans_tail /=.
    intros HΦ l0 junk z -> _. by apply Hspec.
  Qed.
End place_res_gen.

Print Assumptions res_gen_type.
Print Assumptions res_gen_copy_type.
