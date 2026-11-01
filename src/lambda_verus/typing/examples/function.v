From iris.proofmode Require Import proofmode.
From lrust.typing Require Export type programs cont int product value_ctx own shr_bor uniq_util uniq_bor place_own place_puniq place_resolve place_pshr place_read place_share function.
From lrust.lang Require Import lang notation new_delete.
Set Default Proof Using "Type".

(** * Function types on MiniRust values

The examples [get_snd] and [first_ref] of [typing/examples/place_pshr.v], as functions of
the byte function type [fn] ([typing/function.v]): the arguments and the results are
MiniRust values ([◁ᵥ]), the specifications are predicate transformers on them
([fn_spec]). [call_get_snd] calls [get_snd] ([type_letcall]). *)

Section bfn_examples.
  Context `{!typeG Σ}.

  Notation i32t := (int_ty i32).

  (*
  ```
  fn get_snd<'a, 'b>(x: &'a &'b (i32, i32)) -> i32 { ( **x).1 }
  ```
  *)
  Definition get_snd_f : val :=
    fn: ["x"] :=
      let: "v" := !ᶜ{MInt i32} (ToLit (Load Na1Ord MPtr (ToLit "x")) +ₗ #4) in
      return: ["v"].

  Definition get_snd_f_spec :
      fn_spec [at_locₛ (at_locₛ (intₛ i32 * intₛ i32))] (intₛ i32) () :=
    λ _ post '-[(_, (_, (_, z2)))], λ mask π, post z2 mask π.

  Lemma get_snd_f_type :
    typed_val get_snd_f
      ((fn<(α, β)>(∅; &shr{α} (&shr{β} (i32t * i32t))) → i32t) get_snd_f_spec)
      (get_snd_f, ()).
  Proof.
    unfold get_snd_f. unlock.
    opose proof (@type_fn _ _ _ [at_locₛ (at_locₛ (intₛ i32 * intₛ i32))] (intₛ i32) () ()
      (λ '(α, β), FP ∅ +[&shr{α} (&shr{β} (i32t * i32t))]%T i32t%T AtomicClosed)
      get_snd_f_spec _ [BNamed "x"] _ _ _) as H.
    unlock in H. apply H. clear H.
    intros [α β] ϝ k wl. destruct wl as [vx []]. simpl_subst.
    iApply (typed_body_impl with "[]"); last first. {
      iApply typed_body_tctx_incl.
      { eapply tctx_incl_trans; [apply tctx_ty_to_vplace|].
        eapply tctx_incl_trans; [apply tctx_vplace_unfold_shr|].
        apply (tctx_change_vplace_shr _ _ vx α PHole (OfTy (&shr{β} (i32t * i32t)))
          (ShrLty (ProdLty (OfTy i32t) (OfTy i32t)) β)); [done|done|by intros]. }
      (* ( **x).1 *)
      iApply (type_let with "[]").
      { apply (type_read_place_instr _ _ _ vx (PShr α (PShr β (PSnd (OfTy i32t) PHole)))
          (OfTy i32t) i32t static); [by split|apply _|solve_typing]. }
      { solve_typing. } { reflexivity. }
      iIntros (vv). simpl_subst.
      iApply typed_body_tctx_incl. { eapply tctx_incl_tail. apply tctx_drop_vplace_shr. }
      iApply type_jump.
      { rewrite elem_of_list_singleton. reflexivity. }
      { solve_typing. }
      { solve_typing. }
      { reflexivity. }
    }
    intros post [[l1 [l2 [z1 z2]]] []] mask π. simpl.
    rewrite /trans_upper /trans_tail /tr_ret /=. auto.
  Qed.

  (*
  ```
  fn first_ref<'a, 'b>(x: &'a mut &'b (i32, i32)) -> &'b i32 { &( **x).0 }
  ```
  *)
  Definition first_ref_f : val :=
    fn: ["x"] :=
      Skip;;                                                     (* x as a place *)
      ReBor;;                                                    (* unfold **x *)
      ReBor;;                                                    (* view ***x as a pair *)
      let: "r" := &ˢ (ToLit (Load Na1Ord MPtr (ToLit "x"))) in (* &( **x).0 *)
      ReBor;; ReBor;;                                            (* fold back *)
      Skip;;                                                     (* resolve x *)
      return: ["r"].

  Definition first_ref_f_spec :
      fn_spec [uniq_borₛ (at_locₛ (intₛ i32 * intₛ i32))] (at_locₛ (intₛ i32)) () :=
    λ _ post '-[m], λ mask π, ∀ r: ~~ (at_locₛ (intₛ i32)),
      r.2 = (uniq_bor_current (𝔄:=at_locₛ (intₛ i32 * intₛ i32)) m).2.1 →
      uniq_bor_future (𝔄:=at_locₛ (intₛ i32 * intₛ i32)) m π =
        vπ (uniq_bor_current (𝔄:=at_locₛ (intₛ i32 * intₛ i32)) m) π →
      post r mask π.

  Lemma first_ref_f_type :
    typed_val first_ref_f
      ((fn<(α, β)>(∅; &uniq{α} (&shr{β} (i32t * i32t))) → &shr{β} i32t) first_ref_f_spec)
      (first_ref_f, ()).
  Proof.
    unfold first_ref_f. unlock.
    opose proof (@type_fn _ _ _ [uniq_borₛ (at_locₛ (intₛ i32 * intₛ i32))]
      (at_locₛ (intₛ i32)) () ()
      (λ '(α, β), FP ∅ +[&uniq{α} (&shr{β} (i32t * i32t))]%T (&shr{β} i32t)%T AtomicClosed)
      first_ref_f_spec _ [BNamed "x"] _ _ _) as H.
    unlock in H. apply H. clear H.
    intros [α β] ϝ k wl. destruct wl as [vx []]. simpl_subst.
    iApply (typed_body_impl with "[]"); last first. {
      iApply type_seq. { apply (type_uniq_to_vplace_instr _ _ _ vx α (&shr{β} (i32t * i32t))). }
      { solve_typing. } { reflexivity. }
      iApply type_seq.
      { apply (type_unfold_vplace_shr_instr _ _ _ vx (PUniq α PHole) β (i32t * i32t)).
        solve_typing. }
      { solve_typing. } { reflexivity. }
      iApply type_seq.
      { apply (type_change_vplace_shr_instr _ _ _ vx (PUniq α PHole) β PHole
          (OfTy (i32t * i32t)) (ProdLty (OfTy i32t) (OfTy i32t))); [solve_typing|done|done|by intros]. }
      { solve_typing. } { reflexivity. }
      iApply (type_let with "[]").
      { eapply (type_share_place_instr _ _ _ vx (PUniq α (PShr β (PFst PHole (OfTy i32t))))
          static (OfTy i32t) i32t); [by split|solve_typing]. }
      { solve_typing. } { reflexivity. }
      iIntros (vr). simpl_subst.
      iApply type_seq.
      { apply (type_change_vplace_shr_instr _ _ _ vx (PUniq α PHole) β PHole
          (ProdLty (OfTy i32t) (OfTy i32t)) (OfTy (i32t * i32t))); [solve_typing|done|done|by intros]. }
      { solve_typing. } { reflexivity. }
      iApply type_seq.
      { apply (type_fold_vplace_shr_instr _ _ _ vx (PUniq α PHole) β (i32t * i32t)).
        solve_typing. }
      { solve_typing. } { reflexivity. }
      iApply typed_body_tctx_incl.
      { eapply (tctx_incl_frame_r +[_] +[_]). apply tctx_vplace_to_uniq. }
      iApply type_seq.
      { apply (type_resolve_val_instr vx (&uniq{α} (&shr{β} (i32t * i32t)))).
        apply uniq_bor.uniq_resolve. solve_typing. }
      { solve_typing. } { reflexivity. }
      iApply type_jump.
      { rewrite elem_of_list_singleton. reflexivity. }
      { solve_typing. }
      { solve_typing. }
      { reflexivity. }
    }
    intros post [m []] mask π. simpl.
    destruct m as [[[[[l [l' [z1 z2]]] ξi] d] g] idx]. simpl.
    intros Hspec. rewrite /trans_upper /trans_tail /tr_ret /=.
    intros d' g' idx' Hres. apply Hspec; [done|]. by rewrite uniq_bor_future_eq.
  Qed.

  (*
  A call of [get_snd] (a function value [f] of its function type):
  ```
  fn call_get_snd<'a, 'b>(x: &'a &'b (i32, i32)) -> i32 { get_snd(x) }
  ```
  *)
  Definition call_get_snd : expr := (letcall: "r" := "f" ["x"] in jump: "return" ["r"])%E.

  Definition ret_z : predl_trans' [intₛ i32] (intₛ i32) := λ post '-[z], post z.

  Lemma call_get_snd_type ϝ α β (k vf vx: val) :
    ⊢ typed_body [ϝ ⊑ₑ α; α ⊑ₑ β] [ϝ ⊑ₗ []] (InvCtx [] ϝ AtomicClosed)
        [k ◁cont{[ϝ ⊑ₗ []], InvCtx [] ϝ AtomicClosed, λ v: vec val 1, +[vhd v ◁ᵥ i32t] } ret_z]
        +[vf ◁ᶠ (fn<(α', β')>(∅; &shr{α'} (&shr{β'} (i32t * i32t))) → i32t) get_snd_f_spec;
          vx ◁ᵥ &shr{α} (&shr{β} (i32t * i32t))]
        (subst "return" k (subst "f" vf (subst "x" vx call_get_snd)))
        (λ post '-[_; (_, (_, (_, z2)))], λ mask π, post z2 mask π).
  Proof.
    rewrite /call_get_snd. simpl_subst.
    iApply (typed_body_impl with "[]"); last first. {
      iApply (type_letcall (α, β) (λ '(α', β'),
        FP ∅ +[&shr{α'} (&shr{β'} (i32t * i32t))]%T i32t%T AtomicClosed)).
      { solve_typing. } { apply lctx_ictx_alive_nil. solve_typing. }
      { solve_typing. } { solve_typing. }
      iIntros (vr). simpl_subst.
      iApply type_jump.
      { rewrite elem_of_list_singleton. reflexivity. }
      { solve_typing. }
      { solve_typing. }
      { reflexivity. }
    }
    intros post [[vf' []] [[l1 [l2 [z1 z2]]] []]] mask π. simpl.
    rewrite /trans_upper /trans_tail /ret_z /get_snd_f_spec /=. auto.
  Qed.
End bfn_examples.

Print Assumptions get_snd_f_type.
Print Assumptions first_ref_f_type.
Print Assumptions call_get_snd_type.
