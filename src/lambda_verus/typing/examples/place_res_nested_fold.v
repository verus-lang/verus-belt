From iris.proofmode Require Import proofmode.
From lrust.typing Require Export type function product programs own cont uninit int
  uniq_bor shr_bor borrow place place_own place_resolve place_puniq place_pshr place_res
  place_res_rslv place_res_ops.
From lrust.lang Require Import lang notation new_delete.
Set Default Proof Using "Type".

Section place_res_nested_fold.
  Context `{!typeG Σ}.

  (*
  Resolving a unique borrow whose referent is an unfolded unique borrow, and folding it to
  a shared reference to a unique borrow:

  ```
  fn res_nested_fold<'a, 'b>(x: &'a mut &'b mut (i32, i32)) -> &'a &'b mut (i32, i32) {
      /* resolve x */ &*x
  }
  ```

  with the specification `ensures *result == cur(x) (up to the depths and the index of
  the inner borrow), fin(x) == cur(x)`. The argument slot is an owned place; `*x` and
  `**x` are unfolded ([UniqLty (UniqLty (OfTy (int * int)) 'b) 'a]); `x` is resolved
  ([lty_res_uniq_cpd]): its referent is viewed at `'a`, the nested unique borrow keeps a
  guard of the token of its prophecy variable ([view_uniq]); the view is folded
  ([type_fold_oplace_res_uniq_meta_instr]) to the shared reference
  [ShrLty (OfTy (&uniq{'b} (int * int))) 'a], which is folded to a leaf, read and
  returned; the slot is dropped.
  *)

  Definition res_nested_fold : val :=
    fn: ["x"] :=
      ReBor;; ReBor;;                               (* unfold *x, **x *)
      (Skip;; #☠);;                                  (* resolve x *)
      (Skip;; #☠);;                                  (* fold the view *)
      ReBor;;                                       (* fold the shared reference *)
      let: "r" := !"x" in
      (#☠;; delete [ #1; "x"]);;                     (* drop x *)
      let: "ret" := new [ #1] in
      "ret" <- "r";;
      return: ["ret"].

  Definition res_nested_fold_spec :
      fn_spec [uniq_borₛ (uniq_borₛ (Zₛ * Zₛ))] (at_clocₛ (uniq_borₛ (Zₛ * Zₛ))) () :=
    λ _ post '-[(_, m)], λ mask π,
      let b := uniq_bor_current (𝔄:=uniq_borₛ (Zₛ * Zₛ)) m in
      uniq_bor_future (𝔄:=uniq_borₛ (Zₛ * Zₛ)) m π = vπ b π →
      ∀ (lr: loc) (y: ~~ (uniq_borₛ (Zₛ * Zₛ))),
        uniq_bor_loc y = uniq_bor_loc b → uniq_bor_ξi y = uniq_bor_ξi b →
        uniq_bor_current y = uniq_bor_current b →
        post (lr, (uniq_bor_loc (𝔄:=uniq_borₛ (Zₛ * Zₛ)) m, y)) mask π.

  Lemma res_nested_fold_type :
    typed_val res_nested_fold
      ((fn<(α, β)>(∅; &uniq{α} (&uniq{β} (int * int))) → &shr{α} (&uniq{β} (int * int)))
        res_nested_fold_spec)
      (res_nested_fold, ()).
  Proof.
    unfold res_nested_fold. unlock.
    opose proof (@type_fn _ _ _ [uniq_borₛ (uniq_borₛ (Zₛ * Zₛ))]
      (at_clocₛ (uniq_borₛ (Zₛ * Zₛ))) () ()
      (λ '(α, β), FP ∅ +[&uniq{α} (&uniq{β} (int * int))]%T
        (&shr{α} (&uniq{β} (int * int)))%T AtomicClosed)
      res_nested_fold_spec _ [BNamed "x"] _ _ _) as H.
    unlock in H. apply H. clear H.
    intros [α β] ϝ k wl. destruct wl as [vx []]. simpl_subst.
    iApply (typed_body_impl with "[]"); last first. {
      iApply typed_body_tctx_incl; [apply tctx_own_to_oplace|].
      (* unfold *x, **x *)
      iApply type_seq.
      { apply (type_unfold_oplace_uniq_instr _ _ _ vx 1 PHole (&uniq{β} (int * int)) α).
        solve_typing. }
      { solve_typing. } { reflexivity. }
      iApply type_seq.
      { apply (type_unfold_oplace_uniq_instr _ _ _ vx 1 (PUniq α PHole) (int * int) β).
        solve_typing. }
      { solve_typing. } { reflexivity. }
      (* resolve x *)
      iApply type_seq.
      { apply (type_resolve_oplace_res_instr _ _ _ vx 1
          (UniqLty (UniqLty (OfTy (int * int)%T) β) α)
          (ResUniqLty (UniqLty (OfTy (int * int)%T) β) α) 1).
        apply lty_res_uniq_cpd; [solve_typing|solve_typing|done|done]. }
      { solve_typing. } { reflexivity. }
      (* fold the view to a shared reference, then to a leaf *)
      iApply type_seq.
      { apply (type_fold_oplace_res_uniq_meta_instr _ _ _ vx 1 PHole α
          (UniqLty (OfTy (int * int)%T) β)); done. }
      { solve_typing. } { reflexivity. }
      iApply type_seq.
      { apply (type_fold_oplace_shr_instr _ _ _ vx 1 PHole α (&uniq{β} (int * int))).
        solve_typing. }
      { solve_typing. } { reflexivity. }
      (* read it *)
      iApply (type_let with "[]").
      { apply (type_read_oplace_instr _ _ _ vx 1 PHole (&shr{α} (&uniq{β} (int * int))));
          [done|apply _]. }
      { solve_typing. } { reflexivity. }
      iIntros (vr). simpl_subst.
      (* drop x *)
      iApply type_seq.
      { apply (type_drop_oplace_res_instr _ _ _ vx 1 1
          (OfTy (&shr{α} (&uniq{β} (int * int)))));
          [done|done|done]. }
      { solve_typing. } { reflexivity. }
      iApply (type_new 1). { lia. } iIntros (vret). simpl_subst.
      iApply type_assign. { solve_typing. } { by apply write_own. }
      { apply (resolve'_just _ _ _ (const True)). apply resolve_just. }
      iApply type_jump.
      { rewrite elem_of_list_singleton. reflexivity. }
      { solve_typing. }
      { solve_typing. }
      { reflexivity. }
    }
    intros post [[lx m] []] mask π. simpl.
    intros Hspec. rewrite /trans_upper /trans_tail /=.
    intros Hres y (Hl & Hξ & Hc) l _ z ->. apply Hspec; [|done..].
    destruct m as [[[[[l' [[[[[l'' [c1 c2]] ξb] db] gb] idxb]] ξa] da] ga] idxa]. simpl in *.
    rewrite uniq_bor_future_eq Hres. done.
  Qed.
End place_res_nested_fold.

Print Assumptions res_nested_fold_type.
