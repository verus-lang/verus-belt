From iris.proofmode Require Import proofmode.
From lrust.typing Require Export type function product programs own cont uninit int
  uniq_bor borrow place_own place_resolve.
From lrust.lang Require Import lang notation new_delete.
Set Default Proof Using "Type".

Section place_struct.
  Context `{!typeG Σ}.

  (*
  Writing and reading fields of a local struct (an n-ary product, [Π!]):

  ```
  struct S { a: i32, b: i32, c: i32 }
  fn set_mid(mut x: S) -> i32 { x.b = 7; x.c }
  ```

  with the specification `ensures result == old(x).c`. The argument is an owned place;
  the n-ary product is unfolded field by field ([tctx_unfold_oplace_xprod], three
  times: head and tail, the tail's head and tail, …); `x.b` is written
  ([type_write_oplace_instr]) and `x.c` read ([type_read_oplace_instr]); the place is
  dropped ([type_drop_oplace_instr]).
  *)

  Notation S := (Π! +[int; int; int])%T.
  Notation Sₛ := (Π! [Zₛ; Zₛ; Zₛ])%ST.

  Definition set_mid : val :=
    fn: ["x"] :=
      let: "seven" := #7 in
      "x" +ₗ #1 <- "seven";;                     (* x.b = 7 *)
      let: "v" := !("x" +ₗ #1 +ₗ #1) in          (* x.c *)
      ((#☠;; (#☠;; (#☠;; #☠)));;                (* drop x *)
       delete [ #3; "x"]);;
      let: "r" := new [ #1] in
      "r" <- "v";;
      return: ["r"].

  Definition set_mid_spec : fn_spec [Sₛ] Zₛ () :=
    λ _ post '-[(_, -[_; _; c])], λ mask π, ∀ (lr: loc), post (lr, c) mask π.

  Lemma set_mid_type :
    typed_val set_mid ((fn(∅; S) → int) set_mid_spec) (set_mid, ()).
  Proof.
    unfold set_mid. unlock.
    opose proof (@type_fn _ _ _ [Sₛ] Zₛ () ()
      (λ _: (), FP ∅ +[S] int AtomicClosed)
      set_mid_spec _ [BNamed "x"] _ _ _) as H.
    unlock in H. apply H. clear H.
    intros c ϝ k wl. destruct wl as [vx []]. simpl_subst.
    iApply (typed_body_impl with "[]"); last first. {
      (* x as an owned place, unfolded field by field *)
      iApply typed_body_tctx_incl.
      { eapply tctx_incl_trans; [apply tctx_own_to_oplace|].
        eapply tctx_incl_trans; [apply (tctx_unfold_oplace_xprod _ _ _ _ PHole int +[int; int]); done|].
        eapply tctx_incl_trans;
          [apply (tctx_unfold_oplace_xprod _ _ _ _ (PSnd (OfTy int) PHole) int +[int]); done|].
        apply (tctx_unfold_oplace_xprod _ _ _ _ (PSnd (OfTy int) (PSnd (OfTy int) PHole)) int +[]).
        done. }
      simpl.
      (* x.b = 7 *)
      iApply type_int. iIntros (v7). simpl_subst.
      iApply type_seq.
      { apply (type_write_oplace_instr _ _ _ vx v7 3
          (PSnd (OfTy int) (PFst PHole (ProdLty (OfTy int) (OfTy (Π! +[]))))) int int
          (const (const True))); [done|done|apply resolve_just|done]. }
      { solve_typing. } { reflexivity. }
      simpl.
      (* x.c *)
      iApply (type_let with "[]").
      { apply (type_read_oplace_instr _ _ _ vx 3
          (PSnd (OfTy int) (PSnd (OfTy int) (PFst PHole (OfTy (Π! +[]))))) int); [done|apply _]. }
      { solve_typing. } { reflexivity. }
      iIntros (vv). simpl_subst.
      (* drop x *)
      iApply type_seq.
      { apply (type_drop_oplace_instr _ _ _ vx 3 3
          (ProdLty (OfTy int) (ProdLty (OfTy int) (ProdLty (OfTy int) (OfTy (Π! +[]))))));
          [done|done|done|].
        repeat apply lty_resolve_prod; apply lty_resolve_ofty; apply resolve_just. }
      { solve_typing. } { reflexivity. }
      iApply (type_new 1). { lia. } iIntros (vr). simpl_subst.
      iApply type_assign. { solve_typing. } { by apply write_own. }
      { apply (resolve'_just _ _ _ (const True)). apply resolve_just. }
      iApply type_jump.
      { rewrite elem_of_list_singleton. reflexivity. }
      { solve_typing. }
      { solve_typing. }
      { reflexivity. }
    }
    intros post [[lx [a1 [a2 [a3 []]]]] []] mask π Hspec. rewrite /trans_upper /trans_tail /=.
    intros _ _ l _ z ->. apply Hspec.
  Qed.
End place_struct.

Print Assumptions set_mid_type.
