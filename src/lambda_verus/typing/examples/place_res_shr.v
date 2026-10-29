From iris.proofmode Require Import proofmode.
From lrust.typing Require Export type function product programs own cont uninit int
  uniq_bor shr_bor borrow place place_own place_resolve place_puniq place_pshr place_res
  place_res_rslv place_res_ops.
From lrust.lang Require Import lang notation new_delete.
Set Default Proof Using "Type".

Section place_res_shr.
  Context `{!typeG Σ}.

  (*
  Resolving a unique borrow while a leaf of its referent is shared:

  ```
  fn res_shr<'a>(x: &'a mut (i32, i32)) -> i32 {
      let r = &( *x).0;           // at a local lifetime
      /* resolve x */             // ( *x).0 is shared-blocked
      let a = ( *x).0;            // read the shared-blocked leaf
      let b = ( *x).1;
      let c = *r;
      a + b + c                   // x is dropped, then r ends
  }
  ```

  with the specification `ensures result == 2 * ( *x).0 + ( *x).1, fin(x) == cur(x)`. The
  argument slot is an owned place; `*x` and `*x` as a pair are unfolded; `( *x).0` is
  shared at the local lifetime `'l` ([type_share_oplace_deep_instr]), so it becomes the
  shared-blocked leaf [ShrBlocked int ('a ⊓ 'l)]; `x` is resolved
  ([lty_res_uniq_cpd], with `'a ⊓ 'l` alive: the prophecy variable is resolved to the
  current value, whose prophecy tokens are guarded by the sharing at `'a ⊓ 'l`), and its
  referent is viewed at `'a`, the shared-blocked leaf at `'a ⊓ ('a ⊓ 'l)`; it is read
  ([type_read_oplace_res_shrblk_instr]) while `'l` is alive, the other leaf is read
  ([type_read_oplace_res_instr]); the slot is dropped before `'l` ends.
  *)

  Definition res_shr : val :=
    fn: ["x"] :=
      ReBor;; ReBor;;                               (* unfold *x, *x as a pair *)
      Newlft;;
      let: "r" := Share;; !"x" in                   (* r = &( *x).0 *)
      (Skip;; #☠);;                                  (* resolve x *)
      let: "a" := Skip;; !(!"x") in                 (* ( *x).0 *)
      let: "b" := Skip;; !(!"x" +ₗ #1) in           (* ( *x).1 *)
      let: "c" := !"r" in                           (* *r *)
      (#☠;; delete [ #1; "x"]);;                     (* drop x *)
      Endlft;;
      let: "s" := "a" + "b" in
      let: "t" := "s" + "c" in
      let: "ret" := new [ #1] in
      "ret" <- "t";;
      return: ["ret"].

  Definition res_shr_spec : fn_spec [uniq_borₛ (Zₛ * Zₛ)] Zₛ () :=
    λ _ post '-[(_, m)], λ mask π,
      let c := uniq_bor_current (𝔄:=Zₛ * Zₛ) m in
      uniq_bor_future (𝔄:=Zₛ * Zₛ) m π = c →
      ∀ (lr: loc), post (lr, c.1 + c.2 + c.1)%Z mask π.

  Lemma res_shr_type :
    typed_val res_shr ((fn<α>(∅; &uniq{α} (int * int)) → int) res_shr_spec) (res_shr, ()).
  Proof.
    unfold res_shr. unlock.
    opose proof (@type_fn _ _ _ [uniq_borₛ (Zₛ * Zₛ)] Zₛ () ()
      (λ α, FP ∅ +[&uniq{α} (int * int)]%T int%T AtomicClosed)
      res_shr_spec _ [BNamed "x"] _ _ _) as H.
    unlock in H. apply H. clear H.
    intros α ϝ k wl. destruct wl as [vx []]. simpl_subst.
    iApply (typed_body_impl with "[]"); last first. {
      iApply typed_body_tctx_incl; [apply tctx_own_to_oplace|].
      (* unfold *x, *x as a pair *)
      iApply type_seq.
      { apply (type_unfold_oplace_uniq_instr _ _ _ vx 1 PHole (int * int) α). solve_typing. }
      { solve_typing. } { reflexivity. }
      iApply type_seq.
      { apply (type_unfold_oplace_prod_instr _ _ _ vx 1 (PUniq α PHole) int int).
        solve_typing. }
      { solve_typing. } { reflexivity. }
      iApply (type_newlft []). iIntros (γ).
      (* r = &( *x).0, at α ⊓ γ *)
      iApply (type_let with "[]").
      { apply (type_share_oplace_deep_instr _ _ _ vx 1 γ (PUniq α (PFst PHole (OfTy int))) int);
          [done|solve_typing|solve_typing]. }
      { solve_typing. } { reflexivity. }
      iIntros (vr). simpl_subst.
      (* resolve x *)
      iApply type_seq.
      { apply (type_resolve_oplace_res_instr _ _ _ vx 1
          (UniqLty (ProdLty (ShrBlocked int (α ⊓ γ)) (OfTy int)) α)
          (ResUniqLty (ProdLty (ShrBlocked int (α ⊓ γ)) (OfTy int)) α) 1
          (λ x ζm q π, (π (uniq_prvar (uniq_bor_current x) (uniq_bor_ξi x))).1 =
            vπ (uniq_bor_current x) π)).
        eapply lty_res_impl; [apply lty_res_uniq_cpd; [solve_typing|solve_typing|done|done]|].
        intros [[[[[l' [c1 c2]] ξi] d] g] idx] ζm q π. done. }
      { solve_typing. } { reflexivity. }
      (* ( *x).0, the shared-blocked leaf *)
      iApply (type_let with "[]").
      { apply (type_read_oplace_res_shrblk_instr _ _ _ vx 1 PHole α
          (PFst PHole (OfTy int)) int (α ⊓ γ)); [done|apply _|solve_typing]. }
      { solve_typing. } { reflexivity. }
      iIntros (va). simpl_subst.
      (* ( *x).1 *)
      iApply (type_let with "[]").
      { eapply typed_instr_tr_impl; [|apply (type_read_oplace_res_instr _ _ _ vx 1 PHole α
          (PSnd (ShrBlocked int (α ⊓ γ)) PHole) int); [done|apply _|solve_typing]].
        (* (the transformer, stated without the local lifetime) *)
        instantiate (1 := λ post '-[x], post -[(uniq_bor_current (𝔄:=Zₛ * Zₛ) x.1.2).2; x]).
        by intros post [x []] mask π. }
      { solve_typing. } { reflexivity. }
      iIntros (vb). simpl_subst.
      (* *r *)
      iApply (type_let with "[]").
      { eapply (type_deref_instr (𝔅 := Zₛ) _ int); [apply int_stack_okay|done|].
        apply (read_shr int (α ⊓ γ)); [apply int_copy|solve_typing]. }
      { solve_typing. } { reflexivity. }
      iIntros (vc). simpl_subst.
      (* drop x *)
      iApply type_seq.
      { apply (type_drop_oplace_res_instr _ _ _ vx 1 1
          (ResUniqLty (ProdLty (ShrBlocked int (α ⊓ γ)) (OfTy int)) α)); [done|done|done]. }
      { solve_typing. } { reflexivity. }
      (* end γ *)
      iApply (type_endlft _ _ _ _ γ).
      { solve_typing. }
      { repeat apply unblock_tctx_cons_just_hasty. apply unblock_tctx_nil. }
      iApply (type_plus va vb). { solve_typing. }
      iIntros (vs). simpl_subst.
      iApply (type_plus vs vc). { solve_typing. }
      iIntros (vt). simpl_subst.
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
    intros Hres z _ [x0 [x1 [x2 [x3 [x4 []]]]]] (<- & _ & <- & <- & _) l _ z0 ->.
    apply Hspec. destruct m as [[[[[l' [c1 c2]] ξi] d] g] idx]. simpl in *.
    rewrite uniq_bor_future_eq. exact Hres.
  Qed.
End place_res_shr.

Print Assumptions res_shr_type.
