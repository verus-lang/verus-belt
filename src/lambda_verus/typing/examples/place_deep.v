From iris.proofmode Require Import proofmode.
From lrust.typing Require Export type programs cont int product uninit value_ctx own uniq_util uniq_bor place_own place_puniq place_resolve place_deep place_write place_read place_memcpy.
From lrust.lang Require Import lang notation new_delete.
Set Default Proof Using "Type".

(** * [swap_snd] on bytes

The body of [swap_snd] of the deleted legacy example [place_deep.v], on bytes: the arguments are
boxes of bytes ([own_bytes]); the pair [( **x).1] (8 bytes, below two unique borrows) is
copied out and assigned with byte-level [MemCopy]s
([type_memcpy_copy_from_oplace_deep_instr], [type_memcpy_oplace_deep_instr]). The box
[c] for the result is passed in uninitialized (there is no byte [new] rule yet). *)

Section place_deep.
  Context `{!typeG Σ}.

  Notation i32t := (int_ty i32).
  Notation tri := (intₛ i32 * (intₛ i32 * intₛ i32))%ST.

  (*
  ```
  fn swap_snd<'a, 'b>(x: &'a mut &'b mut (i32, (i32, i32)), y: (i32, i32)) -> (i32, i32) {
      let c = ( **x).1;   // copy out of ( **x).1 (8 bytes)
      ( **x).1 = y;       // assign ( **x).1 (8 bytes)
      c
  }
  ```
  *)
  Definition swap_snd : expr := (
    ReBor;; ReBor;; ReBor;;                         (* unfold *x, **x, **x as a pair *)
    ToLit "c" <-ᵇ{8}
      (ToLit (Load Na1Ord MPtr (ToLit (Load Na1Ord MPtr (ToLit "x")))) +ₗ #4);;  (* c = ( **x).1 *)
    (ToLit (Load Na1Ord MPtr (ToLit (Load Na1Ord MPtr (ToLit "x")))) +ₗ #4) <-ᵇ{8}
      ToLit "y";;                                   (* ( **x).1 = y *)
    ReBor;; ReBor;; ReBor;;                         (* fold back *)
    (#☠;; delete [ #(Z.of_nat PTR_SIZE); ToLit "x"]);;  (* drop x, resolving it *)
    (#☠;; delete [ #8; ToLit "y"]);;                (* drop y (moved out) *)
    jump: "return" ["c"])%E.

  Definition ret_pair : predl_trans' [at_locₛ (intₛ i32 * intₛ i32)] (at_locₛ (intₛ i32 * intₛ i32)) :=
    λ post '-[r], post r.

  Definition swap_snd_spec : predl_trans'
      [at_locₛ (uniq_borₛ (uniq_borₛ tri)); at_locₛ (intₛ i32 * intₛ i32); at_locₛ (uninitₛ 8)]
      (at_locₛ (intₛ i32 * intₛ i32)) :=
    λ post '-[(_, m); (_, y); (lc, _)], λ mask π,
      let b := uniq_bor_current (𝔄:=uniq_borₛ tri) m in
      uniq_bor_future (𝔄:=uniq_borₛ tri) m π =
        (((uniq_bor_current (𝔄:=tri) b).1, y), uniq_bor_future (𝔄:=tri) b π) →
      post (lc, (uniq_bor_current (𝔄:=tri) b).2) mask π.

  Lemma swap_snd_type ϝ α β (k vx vy vc: val) :
    ⊢ typed_body [ϝ ⊑ₑ α; α ⊑ₑ β] [ϝ ⊑ₗ []] (InvCtx [] ϝ AtomicClosed)
        [k ◁cont{[ϝ ⊑ₗ []], InvCtx [] ϝ AtomicClosed,
          λ v: vec val 1, +[vhd v ◁ᵥ own_bytes 8 (i32t * i32t)] } ret_pair]
        +[vx ◁ᵥ own_bytes PTR_SIZE (&uniq{α} (&uniq{β} (i32t * (i32t * i32t))));
          vy ◁ᵥ own_bytes 8 (i32t * i32t); vc ◁ᵥ own_bytes 8 (↯ 8)]%T
        (subst "return" k (subst "x" vx (subst "y" vy (subst "c" vc swap_snd))))
        swap_snd_spec.
  Proof.
    rewrite /swap_snd. simpl_subst.
    iApply (typed_body_impl with "[]"); last first. {
      iApply typed_body_tctx_incl.
      { eapply (tctx_incl_frame_r +[_] +[_]). apply tctx_own_to_oplace. }
      (* unfold *x, **x, **x as a pair *)
      iApply type_seq.
      { apply (type_unfold_oplace_uniq_instr _ _ _ vx PTR_SIZE PHole (&uniq{β} (i32t * (i32t * i32t))) α).
        solve_typing. }
      { solve_typing. } { reflexivity. }
      iApply type_seq.
      { apply (type_unfold_oplace_uniq_instr _ _ _ vx PTR_SIZE (PUniq α PHole) (i32t * (i32t * i32t)) β).
        solve_typing. }
      { solve_typing. } { reflexivity. }
      iApply type_seq.
      { apply (type_unfold_oplace_prod_instr _ _ _ vx PTR_SIZE (PUniq α (PUniq β PHole)) i32t (i32t * i32t)).
        solve_typing. }
      { solve_typing. } { reflexivity. }
      (* c = ( **x).1 *)
      iApply typed_body_tctx_incl.
      { eapply (tctx_incl_frame_l _ _ +[_]). eapply (tctx_incl_frame_l _ _ +[_]).
        apply tctx_own_to_oplace. }
      iApply type_seq.
      { eapply (type_memcpy_copy_place_instr _ _ _ vc vx (POwn 8 PHole) (↯ 8) _ _ _
          (POwn PTR_SIZE (PUniq α (PUniq β (PSnd (OfTy i32t) PHole)))) (OfTy (i32t * i32t))
          (i32t * i32t) static);
          [by apply pctx_wty_strong|apply resolve_just|solve_typing|by constructor|apply _|
           solve_typing]. }
      { solve_typing. } { reflexivity. }
      (* ( **x).1 = y *)
      iApply typed_body_tctx_incl.
      { eapply (tctx_incl_frame_l _ _ +[_]). eapply (tctx_incl_frame_r +[_] +[_]).
        apply tctx_own_to_oplace. }
      iApply type_seq.
      { eapply (type_memcpy_move_place_instr _ _ _ vx vy
          (POwn PTR_SIZE (PUniq α (PUniq β (PSnd (OfTy i32t) PHole)))) (i32t * i32t) _ _ _
          (POwn 8 PHole) (i32t * i32t));
          [apply pctx_wty_same|apply resolve_just|solve_typing|done]. }
      { solve_typing. } { reflexivity. }
      (* fold back *)
      iApply type_seq.
      { apply (type_fold_oplace_prod_instr _ _ _ vx PTR_SIZE (PUniq α (PUniq β PHole)) i32t (i32t * i32t)).
        solve_typing. }
      { solve_typing. } { reflexivity. }
      iApply type_seq.
      { apply (type_fold_oplace_uniq_instr _ _ _ vx PTR_SIZE (PUniq α PHole) (i32t * (i32t * i32t)) β).
        solve_typing. }
      { solve_typing. } { reflexivity. }
      iApply type_seq.
      { apply (type_fold_oplace_uniq_instr _ _ _ vx PTR_SIZE PHole (&uniq{β} (i32t * (i32t * i32t))) α).
        solve_typing. }
      { solve_typing. } { reflexivity. }
      (* drop x, resolving it *)
      iApply type_seq.
      { apply (type_drop_oplace_deep_instr _ _ _ vx PTR_SIZE (Z.of_nat PTR_SIZE)
          (OfTy (&uniq{α} (&uniq{β} (i32t * (i32t * i32t)))))); [done|done|done|].
        apply lty_rslv_of, lty_resolve_ofty, uniq_bor.uniq_resolve. solve_typing. }
      { solve_typing. } { reflexivity. }
      (* drop y *)
      iApply type_seq.
      { apply (type_drop_oplace_instr _ _ _ vy 8 8 (OfTy (↯ 8)) (const (const True)));
          [done|done|done|apply lty_resolve_just]. }
      { solve_typing. } { reflexivity. }
      iApply type_jump.
      { rewrite elem_of_list_singleton. reflexivity. }
      { solve_typing. }
      { solve_typing. }
      { reflexivity. }
    }
    intros post [[lx m] [[ly [y1 y2]] [[lc junk] []]]] mask π. simpl.
    destruct m as [[[[[l [[[[[l' [x1 x2]] ξb] db] gb] idxb]] ξa] da] ga] idxa].
    simpl. intros Hspec. rewrite /trans_upper /trans_tail /=.
    intros _ _ _ _ _ _ _ _ _ Hres _. apply Hspec.
    rewrite !uniq_bor_future_eq /=.
    rewrite (uniq_util.uniq_prvar_app_irrel (𝔄:=uniq_borₛ tri) _
      (l', (x1, (y1, y2)), ξb, db, gb, idxb) ξa π).
    etrans; [exact Hres|]. f_equal.
    exact (uniq_util.uniq_prvar_app_irrel (𝔄:=tri) (x1, (y1, y2)) (x1, x2) ξb π).
  Qed.
End place_deep.

Print Assumptions swap_snd_type.
