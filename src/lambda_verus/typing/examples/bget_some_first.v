From iris.proofmode Require Import proofmode.
From lrust.typing Require Export type programs cont int product sum value_ctx own_bytes uniq_util
  uniq_bor buniq_bor bplace_own bplace_puniq bplace_resolve bplace_deep.
From lrust.lang Require Import lang notation new_delete.
Set Default Proof Using "Type".

(** * [get_some_first] on bytes

The body of [get_some_first] of [typing/examples/place_sum.v], on bytes: the argument is
a MiniRust pointer value of type [&uniqb{α} Option<(i32, i32)>] (a root value, [◁ᵥ]);
the [match] reads the tag with a typed [Load] of the tag [IntType] ([type_case_vplace_deep]);
the result [Option<&mut i32>] is a MiniRust variant value built with [MkVariant]
([type_mk_variant_val_instr]). *)

Section bget_some_first.
  Context `{!typeG Σ}.

  Notation i32t := (int_ty i32).
  Notation opt_pair := (Σ! +[(); i32t * i32t])%T.
  Notation opt_pairₛ := (Σ! [unitₛ; (intₛ i32 * intₛ i32)%ST])%ST.
  Notation opt_ref α := (Σ! +[(); &uniqb{α} i32t])%T.
  Notation opt_refₛ := (Σ! [unitₛ; uniq_borₛ (intₛ i32)])%ST.

  (*
  ```
  fn get_some_first<'a>(x: &'a mut Option<(i32, i32)>) -> Option<&'a mut i32> {
      match x { Some(p) => Some(&mut p.0), None => None }
  }
  ```
  *)
  Definition get_some_first_b : expr := (
    Skip;;                                          (* b as a place *)
    case: ToLit (Load Na1Ord (MInt (sum_tag [unitₛ; (intₛ i32 * intₛ i32)%ST])) (ToLit "b")) of
    [ ReBor;;                                       (* None: fold back *)
      Skip;;                                        (* resolve b *)
      let: "u" := MkTuple [] in
      let: "r" := MkVariant 0 "u" in
      jump: "return" ["r"];
      ReBor;;                                       (* Some(p): unfold p *)
      let: "r0" := ReBor;; OfLit (ToLit "b" +ₗ #1) in          (* &mut p.0 *)
      let: "r1" := ReBor;; OfLit (ToLit "b" +ₗ #1 +ₗ #4) in    (* &mut p.1, to drop b *)
      Skip;;                                        (* resolve r1 *)
      let: "r" := MkVariant 1 "r0" in
      jump: "return" ["r"]])%E.

  Definition ret_opt : predl_trans' [opt_refₛ] opt_refₛ := λ post '-[r], post r.

  Definition get_some_first_b_spec : predl_trans' [uniq_borₛ opt_pairₛ] opt_refₛ :=
    λ post '-[m], λ mask π,
      (∀ pad, uniq_bor_current (𝔄:=opt_pairₛ) m = (pinj (Xl:=[unitₛ; (intₛ i32 * intₛ i32)%ST]) 0%fin (), pad) →
        uniq_bor_future (𝔄:=opt_pairₛ) m π = vπ (uniq_bor_current (𝔄:=opt_pairₛ) m) π →
        ∀ pad', post (pinj (Xl:=[unitₛ; uniq_borₛ (intₛ i32)]) 0%fin (), pad') mask π) ∧
      (∀ (a: Z * Z) pad,
        uniq_bor_current (𝔄:=opt_pairₛ) m = (pinj (Xl:=[unitₛ; (intₛ i32 * intₛ i32)%ST]) 1%fin a, pad) →
        ∀ (r: ~~ (uniq_borₛ (intₛ i32))) pad',
          uniq_bor_current r = a.1 →
          uniq_bor_future (𝔄:=opt_pairₛ) m π =
            (pinj (Xl:=[unitₛ; (intₛ i32 * intₛ i32)%ST]) 1%fin (uniq_bor_future r π, a.2), pad) →
          post (pinj (Xl:=[unitₛ; uniq_borₛ (intₛ i32)]) 1%fin r, pad') mask π).

  Lemma get_some_first_b_type ϝ α (k vb: val) :
    ⊢ typed_body [ϝ ⊑ₑ α] [ϝ ⊑ₗ []] (InvCtx [] ϝ AtomicClosed)
        [k ◁cont{[ϝ ⊑ₗ []], InvCtx [] ϝ AtomicClosed,
          λ v: vec val 1, +[vhd v ◁ᵥ opt_ref (α ⊓ α)] } ret_opt]
        +[vb ◁ᵥ &uniqb{α} opt_pair]
        (subst "return" k (subst "b" vb get_some_first_b)) get_some_first_b_spec.
  Proof.
    rewrite /get_some_first_b. simpl_subst.
    iApply (typed_body_impl with "[]"); last first. {
      (* b as a place rooted at its value; match *)
      iApply type_seq. { apply (type_uniq_to_vplace_instr _ _ _ vb α opt_pair). }
      { solve_typing. } { reflexivity. }
      iApply (type_case_vplace_deep _ _ _ _ vb (PUniq α PHole) +[(); i32t * i32t]%T _ _ _ -[_; _]);
        [simpl; solve_typing|].
      iSplitL; [|iSplitL; [|done]].
      - (* None: fold back, resolve b *)
        iApply type_seq.
        { apply (type_fold_vplace_sum_deep_instr _ _ _ vb (PUniq α PHole) +[(); i32t * i32t]%T 0%fin).
          simpl. solve_typing. }
        { solve_typing. } { simpl. reflexivity. }
        iApply typed_body_tctx_incl.
        { apply tctx_vplace_to_uniq. }
        iApply type_seq.
        { apply (type_resolve_val_instr vb (&uniqb{α} opt_pair)). apply buniq_bor.uniq_resolve.
          solve_typing. }
        { solve_typing. } { reflexivity. }
        iApply (type_let with "[]"). { apply type_val_unit_instr. }
        { solve_typing. } { reflexivity. }
        iIntros (vu). simpl_subst.
        iApply (type_let with "[]").
        { apply (type_mk_variant_val_instr +[(); &uniqb{α ⊓ α} i32t]%T 0%fin). done. }
        { solve_typing. } { reflexivity. }
        iIntros (vr). simpl_subst.
        iApply type_jump.
        { rewrite elem_of_list_singleton. reflexivity. }
        { solve_typing. }
        { solve_typing. }
        { reflexivity. }
      - (* Some(p): unfold the payload *)
        iApply type_seq.
        { apply (type_unfold_vplace_prod_instr _ _ _ vb
            (PUniq α (PSum +[(); i32t * i32t]%T 1%fin (0, 0)%Z PHole)) i32t i32t). simpl. solve_typing. }
        { solve_typing. } { simpl. reflexivity. }
        (* &mut p.0, at α ⊓ α *)
        iApply (type_let with "[]").
        { apply (type_borrow_vplace_deep_instr _ _ _ vb α
            (PUniq α (PSum +[(); i32t * i32t]%T 1%fin (0, 0)%Z (PFst PHole (OfTy i32t)))) i32t);
            [done|simpl; solve_typing|solve_typing]. }
        { solve_typing. } { reflexivity. }
        iIntros (vr0). simpl_subst.
        (* &mut p.1, at α ⊓ α *)
        iApply (type_let with "[]").
        { apply (type_borrow_vplace_deep_instr _ _ _ vb α
            (PUniq α (PSum +[(); i32t * i32t]%T 1%fin (0, 0)%Z (PSnd (Blocked i32t (α ⊓ α)) PHole)))
            i32t); [done|simpl; solve_typing|solve_typing]. }
        { solve_typing. } { reflexivity. }
        iIntros (vr1). simpl_subst.
        (* resolve the borrow of p.1 *)
        iApply type_seq.
        { apply (type_resolve_val_instr vr1 (&uniqb{α ⊓ α} i32t)). apply buniq_bor.uniq_resolve.
          solve_typing. }
        { solve_typing. } { reflexivity. }
        (* drop b while both leaves of the payload are blocked *)
        iApply typed_body_tctx_incl.
        { apply (tctx_incl_frame_r +[_] +[] +[_]). apply tctx_drop_vplace_uniq; [solve_typing|done|done]. }
        (* the result: Some(&mut p.0) *)
        iApply (type_let with "[]").
        { apply (type_mk_variant_val_instr +[(); &uniqb{α ⊓ α} i32t]%T 1%fin). done. }
        { solve_typing. } { reflexivity. }
        iIntros (vr). simpl_subst.
        iApply type_jump.
        { rewrite elem_of_list_singleton. reflexivity. }
        { solve_typing. }
        { solve_typing. }
        { reflexivity. }
    }
    intros post [m []] mask π. simpl.
    destruct m as [[[[[l [s pad]] ξi] d] g] idx]. simpl.
    intros [HNone HSome].
    rewrite /trans_upper /trans_tail /=.
    destruct s as [[]|[a|[]]]; simpl.
    - intros d0 g0 idx0 Hres pad0. eapply HNone; [done|rewrite uniq_bor_future_eq /=; exact Hres].
    - intros m1 Hc1 m2 Hc2 Hres Hfin pad0.
      apply (HSome a pad); [done|by rewrite Hc1 /psum_proj_or /=|].
      rewrite Hfin.
      destruct m1 as [[[[[l1 y1] ζi] d1] g1] idx1].
      destruct m2 as [[[[[l2 y2] ηi] d2] g2] idx2].
      rewrite /psum_proj_or /= in Hc1 Hc2. simpl in Hres. subst y1 y2.
      rewrite uniq_bor_future_eq /=. do 4 f_equal. exact Hres.
  Qed.
End bget_some_first.

Print Assumptions get_some_first_b_type.
