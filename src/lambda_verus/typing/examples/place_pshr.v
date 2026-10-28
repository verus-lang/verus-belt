From iris.proofmode Require Import proofmode.
From lrust.typing Require Export type function product programs own cont uninit int
  uniq_bor shr_bor borrow place place_own place_resolve place_puniq place_pshr.
From lrust.lang Require Import lang notation new_delete.
Set Default Proof Using "Type".

Section place_pshr.
  Context `{!typeG Σ}.

  (*
  Reading through two shared references, the argument being an owned place:

  ```
  fn get_snd<'a, 'b>(x: &'a &'b (i32, i32)) -> i32 { ( **x).1 }
  ```

  with the specification `ensures result == ( **x).1`. The argument slot `x` is an owned
  place [own (&shr{'a} (&shr{'b} (i32, i32)))] ([tctx_own_to_oplace]):
    * `*x` is unfolded ([type_unfold_oplace_shr_instr]), and the view of its referent is
      changed to [ShrLty (ProdLty (OfTy int) (OfTy int)) 'b] ([type_change_oplace_shr_instr]);
    * `( **x).1` is read ([type_read_oplace_pshr_instr], [K = PHole],
      [K2 = PShr 'b (PSnd _ PHole)]: two loads of shared references and a field offset);
    * the slot `x` is dropped ([type_drop_oplace_deep_instr], [lty_rslv_shr]).
  *)

  Definition get_snd : val :=
    fn: ["x"] :=
      ReBor;;                                       (* unfold *x *)
      ReBor;;                                       (* view **x as a pair *)
      let: "v" := Skip;; !(!(!"x") +ₗ #1) in        (* ( **x).1 *)
      (#☠;; delete [ #1; "x"]);;                     (* drop x *)
      let: "ret" := new [ #1] in
      "ret" <- "v";;
      return: ["ret"].

  Definition get_snd_spec :
      fn_spec [at_clocₛ (at_clocₛ (Zₛ * Zₛ))] Zₛ () :=
    λ _ post '-[(_, m)], λ mask π, ∀ (lr: loc), post (lr, m.2.2.2) mask π.

  Lemma get_snd_type :
    typed_val get_snd
      ((fn<(α, β)>(∅; &shr{α} (&shr{β} (int * int))) → int) get_snd_spec)
      (get_snd, ()).
  Proof.
    unfold get_snd. unlock.
    opose proof (@type_fn _ _ _ [at_clocₛ (at_clocₛ (Zₛ * Zₛ))] Zₛ () ()
      (λ '(α, β), FP ∅ +[&shr{α} (&shr{β} (int * int))]%T int%T AtomicClosed)
      get_snd_spec _ [BNamed "x"] _ _ _) as H.
    unlock in H. apply H. clear H.
    intros [α β] ϝ k wl. destruct wl as [vx []]. simpl_subst.
    iApply (typed_body_impl with "[]"); last first. {
      iApply typed_body_tctx_incl; [apply tctx_own_to_oplace|].
      (* unfold *x *)
      iApply type_seq.
      { apply (type_unfold_oplace_shr_instr _ _ _ vx 1 PHole α (&shr{β} (int * int))).
        solve_typing. }
      { solve_typing. } { reflexivity. }
      (* view **x as a pair *)
      iApply type_seq.
      { apply (type_change_oplace_shr_instr _ _ _ vx 1 PHole α PHole
          (OfTy (&shr{β} (int * int))) (ShrLty (ProdLty (OfTy int) (OfTy int)) β));
          [solve_typing|done|done|done]. }
      { solve_typing. } { reflexivity. }
      (* ( **x).1 *)
      iApply (type_let with "[]").
      { apply (type_read_oplace_pshr_instr _ _ _ vx 1 PHole α
          (PShr β (PSnd (OfTy int) PHole)) (OfTy int)); [done|apply _|solve_typing|solve_typing]. }
      { solve_typing. } { reflexivity. }
      iIntros (vv). simpl_subst.
      (* drop x *)
      iApply type_seq.
      { apply (type_drop_oplace_deep_instr _ _ _ vx 1 1
          (ShrLty (ShrLty (ProdLty (OfTy int) (OfTy int)) β) α)); [done|done|done|].
        apply lty_rslv_shr. }
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
    intros post [[lx [l1 [l2 [z1 z2]]]] []] mask π. simpl.
    intros Hspec. rewrite /trans_upper /trans_tail /=. intros _ l0 junk z ->. apply Hspec.
  Qed.
End place_pshr.
