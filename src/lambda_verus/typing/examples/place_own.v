From iris.proofmode Require Import proofmode.
From lrust.typing Require Export type function product programs own cont uninit int
  uniq_bor borrow place place_own.
From lrust.lang Require Import lang notation new_delete.
Set Default Proof Using "Type".

Section place_own.
  Context `{!typeG Σ}.

  (*
  Borrowing a field of a local pair, then using the pair again:

  ```
  fn set_snd(mut x: (i32, i32)) -> i32 {
      { let r = &mut x.1; *r = 5; }   // the borrow ends here
      x.0 = 3;
      x.1
  }
  ```

  with the specification `ensures result == 5`. The argument `x` is a local variable
  (an owned pointer to its stack slot); it is seen as an owned place
  ([tctx_own_to_oplace]) and unfolded. Field 1 is borrowed at a fresh lifetime
  ([type_borrow_oplace_instr]), which blocks it; once the lifetime has ended, field 1 is
  unblocked ([unblock_tctx_oplace]) and gets the final value of the borrow. Field 0 is
  written directly ([type_write_oplace_instr]) and field 1 is read
  ([type_read_oplace_instr]); the place is folded back and freed.
  *)

  Definition set_snd : val :=
    fn: ["x"] :=
      Newlft;;
      let: "r" := ReBor;; "x" +ₗ #1 in    (* &mut x.1 *)
      let: "five" := #5 in
      "r" <- "five";;
      Skip;;                              (* resolve r *)
      Endlft;;                            (* unblock x.1 *)
      let: "three" := #3 in
      "x" <- "three";;                    (* x.0 = 3 *)
      let: "v" := !("x" +ₗ #1) in         (* x.1 *)
      let: "ret" := new [ #1] in
      "ret" <- "v";;
      delete [ #2; "x"];;
      return: ["ret"].

  Definition set_snd_spec : fn_spec [(Zₛ * Zₛ)%ST] Zₛ () :=
    λ _ post '-[_], λ mask π, ∀ (lr: loc), post (lr, 5%Z) mask π.

  Lemma set_snd_type :
    typed_val set_snd ((fn(∅; int * int) → int) set_snd_spec) (set_snd, ()).
  Proof.
    unfold set_snd. unlock.
    opose proof (@type_fn _ _ _ [(Zₛ * Zₛ)%ST] Zₛ () ()
      (λ _: (), FP ∅ +[(int * int)%T] int%T AtomicClosed)
      set_snd_spec _ [BNamed "x"] _ _ _) as H.
    unlock in H. apply H. clear H.
    intros c ϝ k wl. destruct wl as [vx []]. simpl_subst.
    iApply (typed_body_impl with "[]"); last first. {
      (* x as an owned place, unfolded *)
      iApply typed_body_tctx_incl.
      { eapply tctx_incl_trans; [apply tctx_own_to_oplace|].
        apply (tctx_unfold_oplace_prod _ _ _ _ PHole int int). }
      iApply (type_newlft []). iIntros (β).
      (* &mut x.1 *)
      iApply (type_let with "[]").
      { eapply (type_borrow_oplace_instr _ _ _ vx _ β (PSnd (OfTy int) PHole) int).
        solve_typing. }
      { solve_typing. } { reflexivity. }
      iIntros (vr). simpl_subst.
      (* write through the borrow, resolve it *)
      iApply type_int. iIntros (v5). simpl_subst.
      iApply type_assign. { solve_typing. } { apply write_uniq. solve_typing. }
      { apply (resolve'_just _ _ _ (const True)). apply resolve_just. }
      iApply type_resolve. { solve_typing. } { apply uniq_bor.uniq_resolve. solve_typing. }
      (* end β: unblock x.1 *)
      iApply (type_endlft _ _ _ _ β).
      { solve_typing. }
      { apply unblock_tctx_cons_just_hasty.
        apply (unblock_tctx_oplace _ _ _ (PSnd (OfTy int) PHole) int); [solve_typing|].
        apply unblock_tctx_nil. }
      (* x.0 = 3 *)
      iApply type_int. iIntros (v3). simpl_subst.
      iApply type_seq.
      { apply (type_write_oplace_instr _ _ _ vx v3 2 (PFst PHole (OfTy int)) int int
          (const (const True))); [done|done|apply resolve_just]. }
      { solve_typing. } { reflexivity. }
      (* x.1 *)
      iApply (type_let with "[]").
      { apply (type_read_oplace_instr _ _ _ vx 2 (PSnd (OfTy int) PHole) int); [done|apply _]. }
      { solve_typing. } { reflexivity. }
      iIntros (vv). simpl_subst.
      (* fold x back, return x.1, free x *)
      iApply typed_body_tctx_incl.
      { eapply tctx_incl_tail. eapply (tctx_incl_frame_r +[_] +[_]).
        eapply tctx_incl_trans; [apply (tctx_fold_oplace_prod _ _ _ _ PHole int int)|].
        apply tctx_oplace_to_own. }
      iApply (type_new 1). { lia. } iIntros (vret). simpl_subst.
      iApply type_assign. { solve_typing. } { by apply write_own. }
      { apply (resolve'_just _ _ _ (const True)). apply resolve_just. }
      iApply type_delete. { solve_typing. } { done. } { done. }
      iApply type_jump.
      { rewrite elem_of_list_singleton. reflexivity. }
      { solve_typing. }
      { solve_typing. }
      { reflexivity. }
    }
    intros post [[lx [a b]] []] mask π Hspec. rewrite /trans_upper /trans_tail /=.
    intros [[[[[l1 w1] ζi] d1] g1] idx1] Hc1 [[[[[l2 w2] ζi'] d2] g2] idx2] Hupd Hres
      [? [[[lx' [a' b']] ζm'] []]] (_ & _ & _ & _ & Hfin & _) _ l junk z ->.
    destruct Hupd as (_ & -> & ->). simpl in Hc1, Hres, Hfin |- *. subst w1.
    rewrite Hfin /oplace_blk_fin /= (uniq_prvar_app_irrel b 5%Z ζi π) Hres. apply Hspec.
  Qed.

End place_own.
