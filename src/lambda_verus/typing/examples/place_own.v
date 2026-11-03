From iris.proofmode Require Import proofmode.
From lrust.typing Require Export type programs cont int product uninit value_ctx own uniq_util uniq_bor place_own place_puniq place_resolve place_read place_write.
From lrust.lang Require Import lang notation new_delete.
Set Default Proof Using "Type".

(** * Examples of the place machinery on bytes (stage 4 of the MiniRust memory model)

The body of [set_snd] of the deleted legacy example [place_own.v], on bytes: the argument is a box of
bytes ([own_bytes]); the leaves are read and written with typed [Load] and [Store]; the
borrow [&mut x.1] is a MiniRust pointer value ([&uniqb]); it is written as a place rooted
at its value ([type_uniq_to_vplace_instr], [type_write_place_instr]). The body is
stated as a function body ([typed_body], with the return continuation [k]), without the
function type. *)

Section place_own.
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
  Definition set_snd : expr := (
    Newlft;;
    let: "r" := &ᵘ ("x" +ₗ #4) in                  (* &mut x.1 *)
    let: "five" := MLit (VInt 5) in
    Skip;;                                                (* r as a place *)
    "r" <-{MInt i32} "five";;                        (* *r = 5 *)
    Skip;;                                                (* resolve r *)
    Endlft;;                                              (* unblock x.1 *)
    let: "three" := MLit (VInt 3) in
    "x" <-{MInt i32} "three";;                      (* x.0 = 3 *)
    let: "v" := !ᶜ{MInt i32} ("x" +ₗ #4) in          (* x.1 *)
    ((#☠;; #☠);; delete [ #8; "x"]);;               (* drop x *)
    jump: "return" ["v"])%E.

  Definition ret_z : predl_trans' [intₛ i32] (intₛ i32) := λ post '-[z], post z.

  Lemma set_snd_type ϝ (k vx: val) :
    ⊢ typed_body [] [ϝ ⊑ₗ []] (InvCtx [] ϝ AtomicClosed)
        [k ◁cont{[ϝ ⊑ₗ []], InvCtx [] ϝ AtomicClosed, λ v: vec val 1, +[vhd v ◁ᵥ i32t] } ret_z]
        +[vx ◁ᵥ own_bytes 8 (i32t * i32t)%T]
        (subst "return" k (subst "x" vx set_snd))
        (λ post '-[_], λ mask π, post 5%Z mask π).
  Proof.
    rewrite /set_snd. simpl_subst.
    iApply (typed_body_impl with "[]"); last first. {
      (* x as an owned place, unfolded *)
      iApply typed_body_tctx_incl.
      { eapply tctx_incl_trans; [apply tctx_own_to_oplace|].
        apply (tctx_unfold_oplace_prod _ _ _ _ PHole i32t i32t). }
      iApply (type_newlft []). iIntros (β).
      (* &mut x.1 *)
      iApply (type_let with "[]").
      { eapply (type_borrow_place_instr _ _ _ vx (POwn _ (PSnd (OfTy i32t) PHole)) β i32t);
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
      { eapply (type_write_place_instr _ _ _ vr v5 (PUniq β PHole) i32t i32t);
          [apply pctx_wty_same|apply resolve_just|simpl; solve_typing]. }
      { solve_typing. } { simpl. reflexivity. }
      iApply typed_body_tctx_incl.
      { eapply (tctx_incl_frame_r +[_] +[_]). apply tctx_vplace_to_uniq. }
      iApply type_seq. { apply (type_resolve_val_instr vr (&uniq{β} i32t)). apply uniq_bor.uniq_resolve. solve_typing. }
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
      { eapply (type_write_place_instr _ _ _ vx v3 (POwn 8 (PFst PHole (OfTy i32t))) i32t i32t);
          [apply pctx_wty_same|apply resolve_just|solve_typing]. }
      { solve_typing. } { reflexivity. }
      (* x.1 *)
      iApply (type_let with "[]").
      { apply (type_read_place_instr _ _ _ vx (POwn 8 (PSnd (OfTy i32t) PHole)) (OfTy i32t) i32t
          static); [by constructor|apply _|solve_typing]. }
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
  (*
  ```
  fn box_pair(mut b: Box<(Box<i32>, i32)>) -> Box<(Box<i32>, i32)> {
      { let r = &mut *b.0; *r = 7; }   // the borrow ends here
      let c = b.0;                     // move out: b.0 is uninitialized
      b.0 = c;                         // re-assign
      b
  }
  ```

  The body of [box_pair] of the deleted legacy example [place_own.v] (with [&mut *b.0] instead of
  [&mut b.0] and a double dereference), on bytes: the inner box is unfolded in place
  ([tctx_unfold_oplace_own]) and its pointee borrowed through it (the path
  [PFst (POwn 4 PHole) _] loads the address of the inner box); the move out of [b.0] is
  a typed [Load] of [MPtr] ([!ᵐ{MPtr}], [type_move_place_instr]), which leaves [↯ PTR_SIZE]; the re-assignment a typed
  [Store]. *)
  Definition box_pair : expr := (
    Newlft;;
    let: "r" := &ᵘ (Load Na1Ord MPtr "b") in            (* &mut *( *b).0 *)
    let: "seven" := MLit (VInt 7) in
    Skip;;                                                (* r as a place *)
    "r" <-{MInt i32} "seven";;                       (* *r = 7 *)
    Skip;;                                                (* resolve r *)
    Endlft;;                                              (* unblock *( *b).0 *)
    let: "c" := !ᵐ{MPtr} "b" in                   (* move ( *b).0 out *)
    "b" <-{MPtr} "c";;                              (* re-assign ( *b).0 *)
    jump: "return" ["b"])%E.

  Notation box_pairₛ := (at_locₛ (at_locₛ (intₛ i32) * intₛ i32))%ST.

  Definition ret_box_pair : predl_trans' [box_pairₛ] box_pairₛ := λ post '-[r], post r.

  Lemma box_pair_type ϝ (k vb: val) :
    ⊢ typed_body [] [ϝ ⊑ₗ []] (InvCtx [] ϝ AtomicClosed)
        [k ◁cont{[ϝ ⊑ₗ []], InvCtx [] ϝ AtomicClosed,
          λ v: vec val 1, +[vhd v ◁ᵥ own_bytes (PTR_SIZE + 4) (own_bytes 4 i32t * i32t)] }
          ret_box_pair]
        +[vb ◁ᵥ own_bytes (PTR_SIZE + 4) (own_bytes 4 i32t * i32t)%T]
        (subst "return" k (subst "b" vb box_pair))
        (λ post '-[(l, ((lb, _), w))], λ mask π, post (l, ((lb, 7%Z), w)) mask π).
  Proof.
    rewrite /box_pair. simpl_subst.
    iApply (typed_body_impl with "[]"); last first. {
      (* the pointee of b as an owned place, unfolded, with the inner box unfolded *)
      iApply typed_body_tctx_incl.
      { eapply tctx_incl_trans; [apply tctx_own_to_oplace|].
        eapply tctx_incl_trans; [apply (tctx_unfold_oplace_prod _ _ _ _ PHole (own_bytes 4 i32t) i32t)|].
        apply (tctx_unfold_oplace_own _ _ _ _ (PFst PHole (OfTy i32t)) 4 i32t). done. }
      iApply (type_newlft []). iIntros (β).
      (* &mut *( *b).0 *)
      iApply (type_let with "[]").
      { eapply (type_borrow_place_instr _ _ _ vb (POwn _ (PFst (POwn 4 PHole) (OfTy i32t))) β i32t);
          solve_typing. }
      { solve_typing. } { reflexivity. }
      iIntros (vr). simpl_subst.
      (* write through the borrow, as a place; resolve it *)
      iApply (type_let with "[]").
      { apply (type_val_int_instr i32). apply (bool_decide_unpack _); by vm_compute. }
      { solve_typing. } { reflexivity. }
      iIntros (v7). simpl_subst.
      iApply type_seq. { apply (type_uniq_to_vplace_instr _ _ _ vr β i32t). }
      { solve_typing. } { reflexivity. }
      iApply type_seq.
      { eapply (type_write_place_instr _ _ _ vr v7 (PUniq β PHole) i32t i32t);
          [apply pctx_wty_same|apply resolve_just|simpl; solve_typing]. }
      { solve_typing. } { simpl. reflexivity. }
      iApply typed_body_tctx_incl.
      { eapply (tctx_incl_frame_r +[_] +[_]). apply tctx_vplace_to_uniq. }
      iApply type_seq. { apply (type_resolve_val_instr vr (&uniq{β} i32t)). apply uniq_bor.uniq_resolve. solve_typing. }
      { solve_typing. } { reflexivity. }
      (* end β: unblock *( *b).0 *)
      iApply (type_endlft _ _ _ _ β).
      { solve_typing. }
      { apply (unblock_tctx_oplace _ _ _ (PFst (POwn 4 PHole) (OfTy i32t)) i32t); [solve_typing|].
        apply unblock_tctx_nil. }
      (* fold the inner box back; move ( *b).0 out *)
      iApply typed_body_tctx_incl.
      { apply (tctx_fold_oplace_own _ _ _ _ (PFst PHole (OfTy i32t)) 4 i32t). }
      iApply (type_let with "[]").
      { apply (type_move_place_instr _ _ _ vb (POwn (PTR_SIZE + 4) (PFst PHole (OfTy i32t)))
          (own_bytes 4 i32t)). done. }
      { solve_typing. } { reflexivity. }
      iIntros (vc). simpl_subst.
      (* re-assign ( *b).0 *)
      iApply type_seq.
      { eapply (type_write_place_instr _ _ _ vb vc (POwn (PTR_SIZE + 4) (PFst PHole (OfTy i32t)))
          (↯ (ty_bsize (own_bytes 4 i32t))) (own_bytes 4 i32t));
          [by apply pctx_wty_strong|apply uninit_resolve|solve_typing]. }
      { solve_typing. } { reflexivity. }
      (* fold back, return b *)
      iApply typed_body_tctx_incl.
      { eapply tctx_incl_trans; [apply (tctx_fold_oplace_prod _ _ _ _ PHole (own_bytes 4 i32t) i32t)|].
        apply tctx_oplace_to_own. }
      iApply type_jump.
      { rewrite elem_of_list_singleton. reflexivity. }
      { solve_typing. }
      { solve_typing. }
      { reflexivity. }
    }
    intros post [[l [[lb v0] w]] []] mask π Hspec. rewrite /trans_upper /trans_tail /=.
    intros [[[[[l1 w1] ζi] d1] g1] idx1] Hc1 _ d g idx Hres
      [[[l' [[lb' v'] w']] ζm'] []] (-> & Hx & _ & Hfin & _) _.
    simpl in Hc1, Hres, Hx, Hfin |- *. subst w1. injection Hx as -> ->.
    rewrite Hfin /oplace_blk_fin /= (uniq_util.uniq_prvar_app_irrel v0 7%Z ζi π) Hres. apply Hspec.
  Qed.
End place_own.

Print Assumptions set_snd_type.
Print Assumptions box_pair_type.
