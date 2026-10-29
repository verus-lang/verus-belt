From iris.proofmode Require Import proofmode.
From lrust.typing Require Export type function product programs own cont uninit int
  uniq_bor shr_bor borrow place place_own place_resolve place_puniq place_pshr place_res
  place_res_rslv place_res_ops.
From lrust.lang Require Import lang notation new_delete.
Set Default Proof Using "Type".

Section place_res.
  Context `{!typeG Σ}.

  (*
  Resolving a local, then reading both of its fields:

  ```
  fn res_pair<'a>(x: (Box<i32>, &'a mut (i32, i32))) -> i32 {
      /* resolve x */
      let a = *x.0;
      let b = ( *x.1).0;
      a + b                       // x is dropped
  }
  ```

  with the specification `ensures result == *x.0 + ( *x.1).0` and the observation
  `fin(x.1) == cur(x.1)`, learnt when [x] is resolved. The argument slot [x] is an owned
  place, unfolded as a pair; it is resolved ([type_resolve_oplace_res_instr],
  [lty_res_prod] of two [lty_res_ofty], two program steps) to
  [ProdLty (OfRes (box int)) (OfRes (&uniq{'a} (int * int)))], which stays readable:
    * [OfRes (box int)] is converted back to [OfTy (box int)] ([tctx_oplace_res_to_ofty]),
      unfolded and read ([type_read_oplace_instr]);
    * [OfRes (&uniq{'a} (int * int))] is re-read as a shared reference to its referent
      at ['a] ([type_oplace_res_uniq_to_shr_instr], one step), viewed as a pair and read below it
      ([type_read_oplace_pshr_instr]);
    * the slot is dropped ([type_drop_oplace_res_instr]), freeing the box.
  *)

  Definition res_pair : val :=
    fn: ["x"] :=
      (Skip;; Skip;; #☠);;                          (* resolve x *)
      let: "a" := !(!"x") in                        (* *x.0 *)
      (Skip;; #☠);;                                 (* *x.1 as a shared reference *)
      ReBor;;                                       (* view *x.1 as a pair *)
      let: "b" := Skip;; !(!("x" +ₗ #1)) in         (* ( *x.1).0 *)
      (((#☠;; delete [ #1; !"x"]);; #☠);; delete [ #2; "x"]);; (* drop x *)
      let: "r" := "a" + "b" in
      let: "ret" := new [ #1] in
      "ret" <- "r";;
      return: ["ret"].

  Definition res_pair_spec :
      fn_spec [(at_locₛ Zₛ * uniq_borₛ (Zₛ * Zₛ))%ST] Zₛ () :=
    λ _ post '-[(_, ((_, z), m))], λ mask π,
      uniq_bor_future (𝔄:=Zₛ * Zₛ) m π = uniq_bor_current (𝔄:=Zₛ * Zₛ) m →
      ∀ (lr: loc), post (lr, z + (uniq_bor_current (𝔄:=Zₛ * Zₛ) m).1)%Z mask π.

  Lemma res_pair_type :
    typed_val res_pair
      ((fn<α>(∅; box int * &uniq{α} (int * int)) → int) res_pair_spec)
      (res_pair, ()).
  Proof.
    unfold res_pair. unlock.
    opose proof (@type_fn _ _ _ [(at_locₛ Zₛ * uniq_borₛ (Zₛ * Zₛ))%ST] Zₛ () ()
      (λ α, FP ∅ +[(box int * &uniq{α} (int * int))%T] int%T AtomicClosed)
      res_pair_spec _ [BNamed "x"] _ _ _) as H.
    unlock in H. apply H. clear H.
    intros α ϝ k wl. destruct wl as [vx []]. simpl_subst.
    have Alv: lctx_lft_alive
      (fp_E (FP ∅ +[(box int * &uniq{α} (int * int))%T] int AtomicClosed) ϝ) [ϝ ⊑ₗ []] α.
    { eapply lctx_lft_alive_external; [rewrite /fp_E /=; by left|solve_typing]. }
    iApply (typed_body_impl with "[]"); last first. {
      (* x as an owned place, unfolded *)
      iApply typed_body_tctx_incl.
      { eapply tctx_incl_trans; [apply tctx_own_to_oplace|].
        apply (tctx_unfold_oplace_prod _ _ _ _ PHole (box int) (&uniq{α} (int * int))). }
      (* resolve x *)
      iApply type_seq.
      { apply (type_resolve_oplace_res_instr _ _ _ vx 2
          (ProdLty (OfTy (box int)) (OfTy (&uniq{α} (int * int))))
          (ProdLty (OfRes (box int)) (OfRes (&uniq{α} (int * int)))) (1 + 1)).
        apply lty_res_prod; apply lty_res_ofty.
        - apply resolve_keep_just.
        - by apply uniq_resolve_keep. }
      { solve_typing. } { reflexivity. }
      (* *x.0: the box is unresolved again, unfolded and read *)
      iApply typed_body_tctx_incl.
      { eapply tctx_incl_trans;
          [apply (tctx_oplace_res_to_ofty _ _ _ _ (PFst PHole (OfRes (&uniq{α} (int * int))))
            (box int))|].
        by apply (tctx_unfold_oplace_own _ _ _ _ (PFst PHole (OfRes (&uniq{α} (int * int))))
          1 int). }
      iApply (type_let with "[]").
      { apply (type_read_oplace_instr _ _ _ vx 2
          (PFst (POwn 1 PHole) (OfRes (&uniq{α} (int * int)))) int); [done|apply _]. }
      { solve_typing. } { reflexivity. }
      iIntros (va). simpl_subst.
      (* ( *x.1).0: the resolved unique borrow is a shared reference to its referent *)
      iApply type_seq.
      { apply (type_oplace_res_uniq_to_shr_instr _ _ _ vx 2 (PSnd (OwnPtrLty 1 (OfTy int)) PHole) α
          (int * int)); done. }
      { solve_typing. } { reflexivity. }
      iApply type_seq.
      { apply (type_change_oplace_shr_instr _ _ _ vx 2 (PSnd (OwnPtrLty 1 (OfTy int)) PHole) α
          PHole (OfTy (int * int)) (ProdLty (OfTy int) (OfTy int))); [solve_typing|done|done|done]. }
      { solve_typing. } { reflexivity. }
      iApply (type_let with "[]").
      { apply (type_read_oplace_pshr_instr _ _ _ vx 2 (PSnd (OwnPtrLty 1 (OfTy int)) PHole) α
          (PFst PHole (OfTy int)) (OfTy int)); [done|apply _|solve_typing|solve_typing]. }
      { solve_typing. } { reflexivity. }
      iIntros (vb). simpl_subst.
      (* drop x, freeing the box *)
      iApply type_seq.
      { apply (type_drop_oplace_res_instr _ _ _ vx 2 2
          (ProdLty (OwnPtrLty 1 (OfTy int)) (ShrLty (ProdLty (OfTy int) (OfTy int)) α)));
          [done|done|done]. }
      { solve_typing. } { reflexivity. }
      (* a + b *)
      iApply (type_plus va vb). { solve_typing. }
      iIntros (vr). simpl_subst.
      iApply (type_new 1). { lia. } iIntros (vret). simpl_subst.
      iApply type_assign. { solve_typing. } { by apply write_own. }
      { apply (resolve'_just _ _ _ (const True)). apply resolve_just. }
      iApply type_jump.
      { rewrite elem_of_list_singleton. reflexivity. }
      { solve_typing. }
      { solve_typing. }
      { reflexivity. }
    }
    intros post [[lx [[lb z] m]] []] mask π. simpl.
    intros Hspec. rewrite /trans_upper /trans_tail /=.
    intros [_ Hres] l0 junk z0 ->. apply Hspec.
    destruct m as [[[[[l' [z1 z2]] ξi] d] g] idx]. simpl in *.
    rewrite uniq_bor_future_eq. exact Hres.
  Qed.
End place_res.

Print Assumptions res_pair_type.

Section place_res_nested.
  Context `{!typeG Σ}.

  (*
  Resolving a nested unique borrow while one of its leaves is blocked:

  ```
  fn res_nested<'a, 'b>(x: &'a mut &'b mut (i32, i32)) -> i32 {
      let r = &mut ( **x).0;      // at a local lifetime
      /* resolve x */             // ( **x).0 is blocked
      let b = ( **x).1;           // read the other leaf
      *r = 3;                     // r ends here: ( **x).0 is unblocked
      let a = ( **x).0;           // read it
      a + b                       // x is dropped
  }
  ```

  with the specification `ensures result == 3 + ( **old(x)).1,
  fin(x) == ((3, ( **old(x)).1), fin( *old(x)))`. The argument slot is an owned place;
  `*x`, `**x` (and `**x` as a pair) are unfolded; `( **x).0` is reborrowed
  ([type_borrow_oplace_deep_instr]); `x` is resolved ([type_resolve_oplace_res_instr],
  [lty_res_uniq_cpd]): its prophecy variable is resolved through its reservation (the
  blocked leaf: the final value of `r`) and the current value (the other leaf), and its
  referent is viewed at `'a` (the nested borrow at `'a ⊓ 'b`); `( **x).1` is read in the
  view ([type_read_oplace_res_instr]); when the local lifetime ends, `( **x).0` is
  unblocked in the view ([unblock_tctx_oplace_res]) and read; the slot is dropped.
  *)

  Definition res_nested : val :=
    fn: ["x"] :=
      ReBor;; ReBor;; ReBor;;                       (* unfold *x, **x, **x as a pair *)
      Newlft;;
      let: "r" := ReBor;; !(!"x") in                (* r = &mut ( **x).0 *)
      (Skip;; #☠);;                                  (* resolve x *)
      let: "b" := Skip;; !(!(!"x") +ₗ #1) in        (* ( **x).1 *)
      let: "three" := #3 in
      "r" <- "three";;
      Skip;;                                        (* resolve r *)
      Endlft;;                                      (* unblock ( **x).0 *)
      let: "a" := Skip;; !(!(!"x")) in              (* ( **x).0 *)
      (#☠;; delete [ #1; "x"]);;                     (* drop x *)
      let: "s" := "a" + "b" in
      let: "ret" := new [ #1] in
      "ret" <- "s";;
      return: ["ret"].

  Definition res_nested_spec :
      fn_spec [uniq_borₛ (uniq_borₛ (Zₛ * Zₛ))] Zₛ () :=
    λ _ post '-[(_, m)], λ mask π,
      let b := uniq_bor_current (𝔄:=uniq_borₛ (Zₛ * Zₛ)) m in
      let c := uniq_bor_current (𝔄:=Zₛ * Zₛ) b in
      uniq_bor_future (𝔄:=uniq_borₛ (Zₛ * Zₛ)) m π =
        ((3%Z, c.2), uniq_bor_future (𝔄:=Zₛ * Zₛ) b π) →
      ∀ (lr: loc), post (lr, 3 + c.2)%Z mask π.

  Lemma res_nested_type :
    typed_val res_nested
      ((fn<(α, β)>(∅; &uniq{α} (&uniq{β} (int * int))) → int) res_nested_spec)
      (res_nested, ()).
  Proof.
    unfold res_nested. unlock.
    opose proof (@type_fn _ _ _ [uniq_borₛ (uniq_borₛ (Zₛ * Zₛ))] Zₛ () ()
      (λ '(α, β), FP ∅ +[&uniq{α} (&uniq{β} (int * int))]%T int%T AtomicClosed)
      res_nested_spec _ [BNamed "x"] _ _ _) as H.
    unlock in H. apply H. clear H.
    intros [α β] ϝ k wl. destruct wl as [vx []]. simpl_subst.
    iApply (typed_body_impl with "[]"); last first. {
      iApply typed_body_tctx_incl; [apply tctx_own_to_oplace|].
      (* unfold *x, **x, **x as a pair *)
      iApply type_seq.
      { apply (type_unfold_oplace_uniq_instr _ _ _ vx 1 PHole (&uniq{β} (int * int)) α).
        solve_typing. }
      { solve_typing. } { reflexivity. }
      iApply type_seq.
      { apply (type_unfold_oplace_uniq_instr _ _ _ vx 1 (PUniq α PHole) (int * int) β).
        solve_typing. }
      { solve_typing. } { reflexivity. }
      iApply type_seq.
      { apply (type_unfold_oplace_prod_instr _ _ _ vx 1 (PUniq α (PUniq β PHole)) int int).
        solve_typing. }
      { solve_typing. } { reflexivity. }
      iApply (type_newlft []). iIntros (γ).
      (* r = &mut ( **x).0, at α ⊓ (β ⊓ γ) *)
      iApply (type_let with "[]").
      { apply (type_borrow_oplace_deep_instr _ _ _ vx 1 γ
          (PUniq α (PUniq β (PFst PHole (OfTy int)))) int); [done|solve_typing|solve_typing]. }
      { solve_typing. } { reflexivity. }
      iIntros (vr). simpl_subst.
      (* resolve x *)
      iApply type_seq.
      { (* (the observation, stated without the local lifetime) *)
        apply (type_resolve_oplace_res_instr _ _ _ vx 1
          (UniqLty (UniqLty (ProdLty (Blocked int (α ⊓ (β ⊓ γ))) (OfTy int)) β) α)
          (ResUniqLty (UniqLty (ProdLty (Blocked int (α ⊓ (β ⊓ γ))) (OfTy int)) β) α) 1
          (λ x ζm q π, (π (uniq_prvar (uniq_bor_current x) (uniq_bor_ξi x))).1 =
            prfn_den (lty_rfn (UniqLty (ProdLty (Blocked int static) (OfTy int)) β)
              (uniq_bor_current x) ζm (false :: q)) π)).
        eapply lty_res_impl; [apply lty_res_uniq_cpd; [solve_typing|done|done]|].
        intros ????. done. }
      { solve_typing. } { reflexivity. }
      (* ( **x).1 *)
      iApply (type_let with "[]").
      { eapply typed_instr_tr_impl; [|apply (type_read_oplace_res_instr _ _ _ vx 1 PHole α
          (PUniq β (PSnd (Blocked int (α ⊓ (β ⊓ γ))) PHole)) int); [done|apply _|solve_typing]].
        (* (the transformer, stated without the local lifetime) *)
        instantiate (1 := λ post '-[x], post -[(uniq_bor_current (𝔄:=Zₛ * Zₛ)
          (uniq_bor_current (𝔄:=uniq_borₛ (Zₛ * Zₛ)) x.1.2)).2; x]).
        by intros post [x []] mask π. }
      { solve_typing. } { reflexivity. }
      iIntros (vb). simpl_subst.
      (* *r = 3, resolve r *)
      iApply type_int. iIntros (v3). simpl_subst.
      iApply type_assign. { solve_typing. } { apply write_uniq. solve_typing. }
      { apply (resolve'_just _ _ _ (const True)). apply resolve_just. }
      iApply type_resolve. { solve_typing. } { apply uniq_bor.uniq_resolve. solve_typing. }
      (* end γ: unblock ( **x).0 in the view *)
      iApply (type_endlft _ _ _ _ γ).
      { solve_typing. }
      { apply unblock_tctx_cons_just_hasty. apply unblock_tctx_cons_just_hasty.
        eapply (unblock_tctx_oplace_res vx 1 γ PHole α (PUniq β (PFst PHole (OfTy int))) int);
          [solve_typing|solve_typing|].
        apply unblock_tctx_nil. }
      (* ( **x).0 *)
      iApply (type_let with "[]").
      { apply (type_read_oplace_res_instr _ _ _ vx 1 PHole α
          (PUniq β (PFst PHole (OfTy int))) int); [done|apply _|solve_typing]. }
      { solve_typing. } { reflexivity. }
      iIntros (va). simpl_subst.
      (* drop x *)
      iApply type_seq.
      { apply (type_drop_oplace_res_instr _ _ _ vx 1 1
          (ResUniqLty (UniqLty (ProdLty (OfTy int) (OfTy int)) β) α)); [done|done|done]. }
      { solve_typing. } { reflexivity. }
      (* a + b *)
      iApply (type_plus va vb). { solve_typing. }
      iIntros (vs). simpl_subst.
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
    destruct m as [[[[[l [[[[[l' [c1 c2]] ξb] db] gb] idxb]] ξa] da] ga] idxa]. simpl.
    intros [[[[[l1 w1] ζ1] d1] g1] idx1] Hc1 Hres [[[[[l2 w2] ζ2] d2] g2] idx2] Hupd Hrr.
    intros [v3' [vb' [x' []]]] (<- & <- & _ & _ & _ & Hfin & _) l0 junk z0 ->.
    destruct Hupd as (_ & -> & ->). simpl in *.
    have H3: (uniq_bor_current (𝔄:=Zₛ * Zₛ)
      (uniq_bor_current (𝔄:=uniq_borₛ (Zₛ * Zₛ)) x'.1.2)).1 = 3%Z.
    { rewrite Hfin (uniq_prvar_app_irrel (𝔄:=Zₛ) c1 3%Z ζ1 π). exact Hrr. }
    rewrite H3. apply Hspec. rewrite !uniq_bor_future_eq /=. rewrite Hres.
    rewrite (uniq_prvar_app_irrel (𝔄:=Zₛ) c1 3%Z ζ1 π) Hrr. done.
  Qed.
End place_res_nested.

Print Assumptions res_nested_type.
