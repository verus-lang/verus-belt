From iris.proofmode Require Import proofmode.
From lrust.typing Require Export type function product programs own cont uninit int
  uniq_bor borrow place_own.
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
          (const (const True))); [done|done|apply resolve_just|done]. }
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

  (*
  Borrowing, moving out of and re-assigning a field of a local box:

  ```
  fn box_pair(mut b: Box<(Box<i32>, i32)>) -> Box<(Box<i32>, i32)> {
      { let r = &mut b.0; **r = 7; }   // the borrow ends here
      let c = b.0;                     // move out: b.0 is uninitialized
      b.0 = c;                         // re-assign
      b
  }
  ```

  with the specification `ensures *result == (Box(7), old(b).1)` (the inner box keeps its
  address). The pointee of `b` is an owned place; field 0 is borrowed at a fresh
  lifetime and unblocked after it has ended, then moved out
  ([type_move_oplace_instr]), which leaves an uninitialized leaf [OfTy (↯ 1)], and
  re-assigned ([type_write_oplace_instr]); the place is folded back into
  `Box<(Box<i32>, i32)>`.
  *)

  Definition box_pair : val :=
    fn: ["x"] :=
      let: "b" := !"x" in
      delete [ #1; "x"];;
      Newlft;;
      let: "r" := ReBor;; "b" in          (* &mut ( *b).0 *)
      let: "r'" := !"r" in                 (* &mut **( *b).0 *)
      let: "seven" := #7 in
      "r'" <- "seven";;
      Skip;;                               (* resolve r' *)
      Endlft;;                             (* unblock ( *b).0 *)
      let: "c" := !"b" in                  (* move ( *b).0 out *)
      "b" <- "c";;                         (* re-assign ( *b).0 *)
      let: "ret" := new [ #1] in
      "ret" <- "b";;
      return: ["ret"].

  Notation box_pairₛ := (at_locₛ (at_locₛ Zₛ * Zₛ))%ST.

  Definition box_pair_spec : fn_spec [box_pairₛ] box_pairₛ () :=
    λ _ post '-[(_, (l, ((lb, _), w)))], λ mask π,
      ∀ (lr: loc), post (lr, (l, ((lb, 7%Z), w))) mask π.

  Lemma box_pair_type :
    typed_val box_pair ((fn(∅; box (box int * int)) → box (box int * int)) box_pair_spec)
      (box_pair, ()).
  Proof.
    unfold box_pair. unlock.
    opose proof (@type_fn _ _ _ [box_pairₛ] box_pairₛ () ()
      (λ _: (), FP ∅ +[box (box int * int)] (box (box int * int)) AtomicClosed)
      box_pair_spec _ [BNamed "x"] _ _ _) as H.
    unlock in H. apply H. clear H.
    intros c ϝ k wl. destruct wl as [vx []]. simpl_subst.
    iApply (typed_body_impl with "[]"); last first. {
      iApply (type_let with "[]").
      { eapply (type_deref_instr (own_ptr 1 (box (box int * int))) (box (box int * int))).
        - apply own_stack_okay.
        - done.
        - apply (read_own_move (box (box int * int))). }
      { apply tctx_extract_elt_here_exact. }
      { reflexivity. }
      iIntros (vb). simpl_subst.
      iApply type_delete. { solve_typing. } { done. } { done. }
      (* the pointee of b as an owned place, unfolded *)
      iApply typed_body_tctx_incl.
      { eapply tctx_incl_trans; [apply tctx_own_to_oplace|].
        apply (tctx_unfold_oplace_prod _ _ _ _ PHole (box int) int). }
      iApply (type_newlft []). iIntros (β).
      (* &mut ( *b).0 *)
      iApply (type_let with "[]").
      { eapply (type_borrow_oplace_instr _ _ _ vb _ β (PFst PHole (OfTy int)) (box int)).
        solve_typing. }
      { solve_typing. } { reflexivity. }
      iIntros (vr). simpl_subst.
      (* **r = 7, resolve *)
      iApply (type_let with "[]").
      { apply (type_deref_uniq_own_instr β vr 1 int). solve_typing. }
      { solve_typing. } { reflexivity. }
      iIntros (vr'). simpl_subst.
      iApply type_int. iIntros (v7). simpl_subst.
      iApply type_assign. { solve_typing. } { apply write_uniq. solve_typing. }
      { apply (resolve'_just _ _ _ (const True)). apply resolve_just. }
      iApply type_resolve. { solve_typing. } { apply uniq_bor.uniq_resolve. solve_typing. }
      (* end β: unblock ( *b).0 *)
      iApply (type_endlft _ _ _ _ β).
      { solve_typing. }
      { apply unblock_tctx_cons_just_hasty.
        apply (unblock_tctx_oplace _ _ _ (PFst PHole (OfTy int)) (box int)); [solve_typing|].
        apply unblock_tctx_nil. }
      (* move ( *b).0 out *)
      iApply (type_let with "[]").
      { apply (type_move_oplace_instr _ _ _ vb 2 (PFst PHole (OfTy int)) (box int));
          [done|apply own_stack_okay|done]. }
      { solve_typing. } { reflexivity. }
      iIntros (vc). simpl_subst.
      (* re-assign ( *b).0 *)
      iApply type_seq.
      { apply (type_write_oplace_instr _ _ _ vb vc 2 (PFst PHole (OfTy int)) (↯ 1) (box int)
          (const (const True))); [done|done|apply uninit_resolve|done]. }
      { solve_typing. } { reflexivity. }
      (* fold back, return b *)
      iApply typed_body_tctx_incl.
      { eapply (tctx_incl_frame_r +[_] +[_]).
        eapply tctx_incl_trans; [apply (tctx_fold_oplace_prod _ _ _ _ PHole (box int) int)|].
        apply tctx_oplace_to_own. }
      iApply (type_new 1). { lia. } iIntros (vret). simpl_subst.
      iApply type_assign. { solve_typing. } { by apply write_own. }
      { apply (resolve'_just _ _ _ (const True)). apply resolve_just. }
      iApply type_jump.
      { rewrite elem_of_list_singleton. reflexivity. }
      { solve_typing. }
      { solve_typing. }
      { reflexivity. }
    }
    intros post [[lx [l [[lb v0] w]]] []] mask π Hspec. rewrite /trans_upper /trans_tail /=.
    intros _ _ [[[[[l1 [lb1 v1]] ζi] d1] g1] idx1] Hc1
      [[[[[l2 w2] ξ2] d2] g2] idx2] Hc2 Hf2 Hl2 Hl2' [[[[[l3 w3] ξ3] d3] g3] idx3] Hupd Hres
      [? [[[l' [[lb' v'] w']] ζm'] []]] (_ & -> & Hw' & _ & Hfin & _) _ _ l0 _ z ->.
    destruct Hupd as (_ & -> & ->). simpl in *. injection Hc1 as -> ->. subst w2.
    injection Hw' as ->.
    rewrite !uniq_bor_future_eq in Hf2 Hl2'.
    rewrite /oplace_blk_fin /= in Hfin.
    have Hv: v' = 7%Z.
    { rewrite (_: v' = (lb', v').2) // Hfin -Hf2 (uniq_prvar_app_irrel (𝔄:=Zₛ) v0 7%Z ξ2 π). exact Hres. }
    have Hlb: lb' = lb.
    { rewrite (_: lb' = (lb', v').1) // Hfin -Hl2'. done. }
    subst v' lb'. apply Hspec.
  Qed.
End place_own.
