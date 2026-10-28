From iris.proofmode Require Import proofmode.
From lrust.typing Require Export type function product programs own cont uninit int
  uniq_bor borrow place place_own place_resolve place_puniq place_res place_res_rslv
  place_res_ops.
From lrust.lang Require Import lang notation new_delete.
Set Default Proof Using "Type".

Section place_res_gen.
  Context `{!typeG Σ}.

  (*
  Resolving a leaf of a generic type, keeping it readable:

  ```
  fn res_gen<T: Copy>(x: T) -> T { /* resolve x */ x }
  ```

  for an abstract type [T] (of size 1) whose resolution is [resolve E L T ΦT], with the
  specification `ensures result == x` and the observation `ΦT x`, learnt when [x] is
  resolved. The argument slot [x] is an owned place [own (OfTy T)]; it is resolved
  ([type_resolve_oplace_res_instr], [lty_res_ofty], from [resolve] by [resolve_keep_copy])
  to [own (OfRes T)], which is still readable: it is converted back to [OfTy T]
  ([tctx_oplace_res_to_ofty], [ResOwn T]) and read; the slot is then dropped
  ([type_drop_oplace_res_instr]).
  *)

  Context {𝔄} (T: type 𝔄) `{!Copy T} `{!ResOwn T} (ΦT: ~~𝔄 → proph_asn → Prop).
  Hypothesis (HsT: ty_size T = 1%nat).
  Hypothesis (HrT: ∀ E L, resolve E L T ΦT).

  Definition res_gen : val :=
    fn: ["x"] :=
      (Skip;; #☠);;                                  (* resolve x *)
      let: "v" := !"x" in
      (#☠;; delete [ #1; "x"]);;                     (* drop x *)
      let: "ret" := new [ #1] in
      "ret" <- "v";;
      return: ["ret"].

  Definition res_gen_spec : fn_spec [𝔄] 𝔄 () :=
    λ _ post '-[(_, x)], λ mask π, ΦT x π → ∀ (lr: loc), post (lr, x) mask π.

  Lemma res_gen_type :
    typed_val res_gen ((fn(∅; T) → T) res_gen_spec) (res_gen, ()).
  Proof using Copy0 HrT HsT ResOwn0 T typeG0 Σ ΦT 𝔄.
    unfold res_gen. unlock.
    opose proof (@type_fn _ _ _ [𝔄] 𝔄 () ()
      (λ _: (), FP ∅ +[T] T AtomicClosed)
      res_gen_spec _ [BNamed "x"] _ _ _) as H.
    unlock in H. apply H. clear H.
    intros c ϝ k wl. destruct wl as [vx []]. simpl_subst.
    iApply (typed_body_impl with "[]"); last first. {
      iApply typed_body_tctx_incl; [apply tctx_own_to_oplace|].
      rewrite HsT.
      (* resolve x *)
      iApply type_seq.
      { apply (type_resolve_oplace_res_instr _ _ _ vx 1 (OfTy T) (OfRes T) 1 (λ x _ _, ΦT x)).
        apply lty_res_ofty, resolve_keep_copy; [apply _|apply _|apply HrT]. }
      { solve_typing. } { reflexivity. }
      (* it is still readable *)
      iApply typed_body_tctx_incl; [apply (tctx_oplace_res_to_ofty _ _ _ _ PHole T)|].
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
