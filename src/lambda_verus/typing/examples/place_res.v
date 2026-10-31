From iris.proofmode Require Import proofmode.
From lrust.typing Require Export type programs cont int product value_ctx own_bytes shr_bytes
  uniq_util uniq_bytes place_own place_puniq place_resolve place_pshr place_res place_res_rslv
  place_res_ops.
From lrust.lang Require Import lang notation new_delete.
Set Default Proof Using "Type".

(** * Resolving places to a readable state, on bytes

The example [res_pair] of the deleted legacy example [place_res.v], on bytes ([typing/place_res.v],
[typing/place_res_rslv.v], [typing/place_res_ops.v]): the argument is a box of bytes
holding a pair of a box and a unique borrow. *)

Section place_res.
  Context `{!typeG Σ}.

  Notation i32t := (int_ty i32).

  Definition ret_zz : predl_trans' [intₛ i32; intₛ i32] (intₛ i32 * intₛ i32) :=
    λ post '-[a; b], post (a, b).

  (*
  Resolving a local, then reading both of its fields:

  ```
  fn res_pair<'a>(x: (Box<i32>, &'a mut (i32, i32))) -> (i32, i32) {
      /* resolve x */
      let a = *x.0;
      let b = ( *x.1).0;
      (a, b)                      // x is dropped
  }
  ```

  with the specification `ensures result == ( *x.0, ( *x.1).0)` and the observation
  `fin(x.1) == cur(x.1)`, learnt when [x] is resolved. The argument is a box of bytes, an
  owned place, unfolded as a pair; it is resolved ([type_resolve_oplace_res_instr],
  [lty_res_prod] of two [lty_res_ofty], two program steps) to
  [ProdLty (OfRes (own_bytes 4 i32)) (OfRes (&uniqb{'a} (i32 * i32)))], which stays
  readable:
    * [OfRes (own_bytes 4 i32)] is converted back to [OfTy (own_bytes 4 i32)]
      ([tctx_oplace_res_to_ofty]), unfolded and read ([type_read_oplace_instr]);
    * [OfRes (&uniqb{'a} (i32 * i32))] is re-read as a shared reference to its referent
      at ['a] ([type_oplace_res_uniq_to_shr_instr], one step), viewed as a pair and read
      below it ([type_read_oplace_pshr_instr], a guarded typed load);
    * the slot is dropped ([type_drop_oplace_res_instr]), freeing the inner box.
  *)
  Definition res_pair : expr := (
    (Skip;; Skip;; #☠);;                                         (* resolve x *)
    let: "a" := Load Na1Ord (MInt i32) (ToLit (Load Na1Ord MPtr (ToLit "x"))) in  (* *x.0 *)
    (Skip;; #☠);;                                                (* *x.1 as a shared reference *)
    ReBor;;                                                      (* view *x.1 as a pair *)
    let: "b" := Load Na1Ord (MInt i32)
      (ToLit (Load Na1Ord MPtr (ToLit "x" +ₗ #PTR_SIZE))) in      (* ( *x.1).0 *)
    (((#☠;; delete [ #4; ToLit (Load Na1Ord MPtr (ToLit "x"))]);; #☠);;
      delete [ #(Z.of_nat (PTR_SIZE + PTR_SIZE)); ToLit "x"]);;   (* drop x *)
    jump: "return" ["a"; "b"])%E.

  Definition res_pair_spec :
      predl_trans' [at_locₛ (at_locₛ (intₛ i32) * uniq_borₛ (intₛ i32 * intₛ i32))]
        (intₛ i32 * intₛ i32) :=
    λ post '-[(_, ((_, z), m))], λ mask π,
      uniq_bor_future (𝔄:=intₛ i32 * intₛ i32) m π = uniq_bor_current (𝔄:=intₛ i32 * intₛ i32) m →
      post (z, (uniq_bor_current (𝔄:=intₛ i32 * intₛ i32) m).1) mask π.

  Lemma res_pair_type ϝ α (k vx: val) :
    ⊢ typed_body [ϝ ⊑ₑ α] [ϝ ⊑ₗ []] (InvCtx [] ϝ AtomicClosed)
        [k ◁cont{[ϝ ⊑ₗ []], InvCtx [] ϝ AtomicClosed,
          λ v: vec val 2, +[vhd v ◁ᵥ i32t; vhd (vtl v) ◁ᵥ i32t] } ret_zz]
        +[vx ◁ᵥ own_bytes (PTR_SIZE + PTR_SIZE) (own_bytes 4 i32t * &uniqb{α} (i32t * i32t))]
        (subst "return" k (subst "x" vx res_pair)) res_pair_spec.
  Proof.
    rewrite /res_pair. simpl_subst.
    iApply (typed_body_impl with "[]"); last first. {
      (* x as an owned place, unfolded *)
      iApply typed_body_tctx_incl.
      { eapply tctx_incl_trans; [apply tctx_own_to_oplace|].
        apply (tctx_unfold_oplace_prod _ _ _ _ PHole (own_bytes 4 i32t) (&uniqb{α} (i32t * i32t))). }
      (* resolve x *)
      iApply type_seq.
      { apply (type_resolve_oplace_res_instr _ _ _ vx (PTR_SIZE + PTR_SIZE)
          (ProdLty (OfTy (own_bytes 4 i32t)) (OfTy (&uniqb{α} (i32t * i32t))))
          (ProdLty (OfRes (own_bytes 4 i32t)) (OfRes (&uniqb{α} (i32t * i32t)))) (1 + 1)).
        apply lty_res_prod; apply lty_res_ofty.
        - apply resolve_keep_just.
        - apply uniq_resolve_keep. solve_typing. }
      { solve_typing. } { reflexivity. }
      (* *x.0: the box is unresolved again, unfolded and read *)
      iApply typed_body_tctx_incl.
      { eapply tctx_incl_trans;
          [apply (tctx_oplace_res_to_ofty _ _ _ _ (PFst PHole (OfRes (&uniqb{α} (i32t * i32t))))
            (own_bytes 4 i32t))|].
        by apply (tctx_unfold_oplace_own _ _ _ _ (PFst PHole (OfRes (&uniqb{α} (i32t * i32t))))
          4 i32t). }
      iApply (type_let with "[]").
      { apply (type_read_oplace_instr _ _ _ vx (PTR_SIZE + PTR_SIZE)
          (PFst (POwn 4 PHole) (OfRes (&uniqb{α} (i32t * i32t)))) i32t). apply _. }
      { solve_typing. } { reflexivity. }
      iIntros (va). simpl_subst.
      (* ( *x.1).0: the resolved unique borrow is a shared reference to its referent *)
      iApply type_seq.
      { apply (type_oplace_res_uniq_to_shr_instr _ _ _ vx (PTR_SIZE + PTR_SIZE)
          (PSnd (OwnPtrLty 4 (OfTy i32t)) PHole) α (i32t * i32t)); [done|solve_typing]. }
      { solve_typing. } { reflexivity. }
      iApply type_seq.
      { apply (type_change_oplace_shr_instr _ _ _ vx (PTR_SIZE + PTR_SIZE)
          (PSnd (OwnPtrLty 4 (OfTy i32t)) PHole) α PHole (OfTy (i32t * i32t))
          (ProdLty (OfTy i32t) (OfTy i32t))); [solve_typing|done|done|by intros]. }
      { solve_typing. } { reflexivity. }
      iApply (type_let with "[]").
      { apply (type_read_oplace_pshr_instr _ _ _ vx (PTR_SIZE + PTR_SIZE)
          (PSnd (OwnPtrLty 4 (OfTy i32t)) PHole) α (PFst PHole (OfTy i32t)) (OfTy i32t));
          [apply _|solve_typing|solve_typing]. }
      { solve_typing. } { reflexivity. }
      iIntros (vb). simpl_subst.
      (* drop x, freeing the inner box *)
      iApply type_seq.
      { apply (type_drop_oplace_res_instr _ _ _ vx (PTR_SIZE + PTR_SIZE)
          (Z.of_nat (PTR_SIZE + PTR_SIZE))
          (ProdLty (OwnPtrLty 4 (OfTy i32t)) (ShrLty (ProdLty (OfTy i32t) (OfTy i32t)) α)));
          [done|by rewrite lty_size_prod|done]. }
      { solve_typing. } { reflexivity. }
      iApply type_jump.
      { rewrite elem_of_list_singleton. reflexivity. }
      { solve_typing. }
      { solve_typing. }
      { reflexivity. }
    }
    intros post [[lx [[lb z] m]] []] mask π. simpl.
    intros Hspec. rewrite /trans_upper /trans_tail /ret_zz /=.
    intros [_ Hres]. apply Hspec.
    destruct m as [[[[[l' [z1 z2]] ξi] d] g] idx]. simpl in *.
    rewrite uniq_bor_future_eq. exact Hres.
  Qed.
  (*
  Resolving a nested unique borrow while one of its leaves is blocked:

  ```
  fn res_nested<'a, 'b>(x: &'a mut &'b mut (i32, i32)) -> (i32, i32) {
      let r = &mut ( **x).0;      // at a local lifetime
      /* resolve x */             // ( **x).0 is blocked
      let b = ( **x).1;           // read the other leaf
      *r = 3;                     // r ends here: ( **x).0 is unblocked
      let a = ( **x).0;           // read it
      (a, b)                      // x is dropped
  }
  ```

  with the specification `ensures result == (3, ( **old(x)).1),
  fin(x) == ((3, ( **old(x)).1), fin( *old(x)))`. The argument is a box of bytes, an owned
  place; `*x`, `**x` (and `**x` as a pair) are unfolded; `( **x).0` is reborrowed
  ([type_borrow_oplace_deep_instr]); `x` is resolved ([type_resolve_oplace_res_instr],
  [lty_res_uniq_cpd]); `( **x).1` is read in the view ([type_read_oplace_res_instr], a
  guarded typed load); `*r = 3` is a typed [Store] through the reborrow; when the local
  lifetime ends, `( **x).0` is unblocked in the view ([unblock_tctx_oplace_res]) and read;
  the slot is dropped.
  *)
  Definition res_nested : expr := (
    ReBor;; ReBor;; ReBor;;                                      (* unfold *x, **x, **x as a pair *)
    Newlft;;
    let: "r" := ReBor;;
      OfLit (ToLit (Load Na1Ord MPtr (ToLit (Load Na1Ord MPtr (ToLit "x"))))) in  (* &mut ( **x).0 *)
    (Skip;; #☠);;                                                (* resolve x *)
    let: "b" := Load Na1Ord (MInt i32)
      (ToLit (Load Na1Ord MPtr (ToLit (Load Na1Ord MPtr (ToLit "x")))) +ₗ #4) in  (* ( **x).1 *)
    let: "three" := MLit (VInt 3) in
    Skip;;                                                       (* r as a place *)
    (ReBor;; Store Na1Ord (MInt i32) (ToLit "r") "three");;      (* *r = 3 *)
    Skip;;                                                       (* resolve r *)
    Endlft;;                                                     (* unblock ( **x).0 *)
    let: "a" := Load Na1Ord (MInt i32)
      (ToLit (Load Na1Ord MPtr (ToLit (Load Na1Ord MPtr (ToLit "x"))))) in  (* ( **x).0 *)
    (#☠;; delete [ #(Z.of_nat PTR_SIZE); ToLit "x"]);;           (* drop x *)
    jump: "return" ["a"; "b"])%E.

  Notation pairₛ := (intₛ i32 * intₛ i32)%ST.

  Definition res_nested_spec :
      predl_trans' [at_locₛ (uniq_borₛ (uniq_borₛ pairₛ))] pairₛ :=
    λ post '-[(_, m)], λ mask π,
      let b := uniq_bor_current (𝔄:=uniq_borₛ pairₛ) m in
      let c := uniq_bor_current (𝔄:=pairₛ) b in
      uniq_bor_future (𝔄:=uniq_borₛ pairₛ) m π =
        ((3%Z, c.2), uniq_bor_future (𝔄:=pairₛ) b π) →
      post (3%Z, c.2) mask π.

  Lemma res_nested_type ϝ α β (k vx: val) :
    ⊢ typed_body [ϝ ⊑ₑ α; α ⊑ₑ β] [ϝ ⊑ₗ []] (InvCtx [] ϝ AtomicClosed)
        [k ◁cont{[ϝ ⊑ₗ []], InvCtx [] ϝ AtomicClosed,
          λ v: vec val 2, +[vhd v ◁ᵥ i32t; vhd (vtl v) ◁ᵥ i32t] } ret_zz]
        +[vx ◁ᵥ own_bytes PTR_SIZE (&uniqb{α} (&uniqb{β} (i32t * i32t)))]
        (subst "return" k (subst "x" vx res_nested)) res_nested_spec.
  Proof.
    rewrite /res_nested. simpl_subst.
    iApply (typed_body_impl with "[]"); last first. {
      iApply typed_body_tctx_incl; [apply tctx_own_to_oplace|].
      (* unfold *x, **x, **x as a pair *)
      iApply type_seq.
      { apply (type_unfold_oplace_uniq_instr _ _ _ vx PTR_SIZE PHole (&uniqb{β} (i32t * i32t)) α).
        solve_typing. }
      { solve_typing. } { reflexivity. }
      iApply type_seq.
      { apply (type_unfold_oplace_uniq_instr _ _ _ vx PTR_SIZE (PUniq α PHole) (i32t * i32t) β).
        solve_typing. }
      { solve_typing. } { reflexivity. }
      iApply type_seq.
      { apply (type_unfold_oplace_prod_instr _ _ _ vx PTR_SIZE (PUniq α (PUniq β PHole)) i32t i32t).
        solve_typing. }
      { solve_typing. } { reflexivity. }
      iApply (type_newlft []). iIntros (γ).
      (* r = &mut ( **x).0, at α ⊓ (β ⊓ γ) *)
      iApply (type_let with "[]").
      { apply (type_borrow_oplace_deep_instr _ _ _ vx PTR_SIZE γ
          (PUniq α (PUniq β (PFst PHole (OfTy i32t)))) i32t); [done|solve_typing|solve_typing]. }
      { solve_typing. } { reflexivity. }
      iIntros (vr). simpl_subst.
      (* resolve x *)
      iApply type_seq.
      { (* (the observation, stated without the local lifetime) *)
        apply (type_resolve_oplace_res_instr _ _ _ vx PTR_SIZE
          (UniqLty (UniqLty (ProdLty (Blocked i32t (α ⊓ (β ⊓ γ))) (OfTy i32t)) β) α)
          (ResUniqLty (UniqLty (ProdLty (Blocked i32t (α ⊓ (β ⊓ γ))) (OfTy i32t)) β) α) 1
          (λ x ζm q π, (π (uniq_prvar (uniq_bor_current x) (uniq_bor_ξi x))).1 =
            prfn_den (lty_rfn (UniqLty (ProdLty (Blocked i32t static) (OfTy i32t)) β)
              (uniq_bor_current x) ζm (false :: q)) π)).
        eapply lty_res_impl; [apply lty_res_uniq_cpd; [solve_typing|solve_typing|done|done]|].
        intros ????. done. }
      { solve_typing. } { reflexivity. }
      (* ( **x).1 *)
      iApply (type_let with "[]").
      { eapply typed_instr_tr_impl; [|apply (type_read_oplace_res_instr _ _ _ vx PTR_SIZE PHole α
          (PUniq β (PSnd (Blocked i32t (α ⊓ (β ⊓ γ))) PHole)) i32t); [apply _|solve_typing]].
        (* (the transformer, stated without the local lifetime) *)
        instantiate (1 := λ post '-[x], post -[(uniq_bor_current (𝔄:=pairₛ)
          (uniq_bor_current (𝔄:=uniq_borₛ pairₛ) x.1.2)).2; x]).
        by intros post [x []] mask π. }
      { solve_typing. } { reflexivity. }
      iIntros (vb). simpl_subst.
      (* *r = 3, resolve r *)
      iApply (type_let with "[]").
      { apply (type_val_int_instr i32). apply (bool_decide_unpack _); by vm_compute. }
      { solve_typing. } { reflexivity. }
      iIntros (v3). simpl_subst.
      iApply type_seq. { apply (type_uniq_to_vplace_instr _ _ _ vr (α ⊓ (β ⊓ γ)) i32t). }
      { solve_typing. } { reflexivity. }
      iApply type_seq.
      { apply (type_write_vplace_deep_instr _ _ _ vr v3 (PUniq (α ⊓ (β ⊓ γ)) PHole) i32t
          (const (const True))); [apply resolve_just|simpl; solve_typing]. }
      { solve_typing. } { simpl. reflexivity. }
      iApply typed_body_tctx_incl.
      { eapply (tctx_incl_frame_r +[_] +[_]). apply tctx_vplace_to_uniq. }
      iApply type_seq.
      { apply (type_resolve_val_instr vr (&uniqb{α ⊓ (β ⊓ γ)} i32t)).
        apply uniq_bytes.uniq_resolve. solve_typing. }
      { solve_typing. } { reflexivity. }
      (* end γ: unblock ( **x).0 in the view *)
      iApply (type_endlft _ _ _ _ γ).
      { solve_typing. }
      { apply unblock_tctx_cons_just.
        eapply (unblock_tctx_oplace_res vx PTR_SIZE γ PHole α (PUniq β (PFst PHole (OfTy i32t)))
          i32t); [solve_typing|solve_typing|].
        apply unblock_tctx_nil. }
      (* ( **x).0 *)
      iApply (type_let with "[]").
      { apply (type_read_oplace_res_instr _ _ _ vx PTR_SIZE PHole α
          (PUniq β (PFst PHole (OfTy i32t))) i32t); [apply _|solve_typing]. }
      { solve_typing. } { reflexivity. }
      iIntros (va). simpl_subst.
      (* drop x *)
      iApply type_seq.
      { apply (type_drop_oplace_res_instr _ _ _ vx PTR_SIZE (Z.of_nat PTR_SIZE)
          (ResUniqLty (UniqLty (ProdLty (OfTy i32t) (OfTy i32t)) β) α)); [done|done|done]. }
      { solve_typing. } { reflexivity. }
      iApply type_jump.
      { rewrite elem_of_list_singleton. reflexivity. }
      { solve_typing. }
      { solve_typing. }
      { reflexivity. }
    }
    intros post [[lx m] []] mask π. simpl.
    intros Hspec. rewrite /trans_upper /trans_tail /ret_zz /=.
    destruct m as [[[[[l [[[[[l' [c1 c2]] ξb] db] gb] idxb]] ξa] da] ga] idxa]. simpl.
    intros [[[[[l1 w1] ζ1] d1] g1] idx1] Hc1 Hres _ d' g' idx' Hrr.
    intros [vb' [x' []]] (<- & _ & _ & _ & Hfin & _).
    simpl in *. subst w1.
    have H3: (uniq_bor_current (𝔄:=pairₛ)
      (uniq_bor_current (𝔄:=uniq_borₛ pairₛ) x'.1.2)).1 = 3%Z.
    { rewrite Hfin (uniq_util.uniq_prvar_app_irrel (𝔄:=intₛ i32) c1 3%Z ζ1 π). exact Hrr. }
    rewrite H3. apply Hspec. rewrite !uniq_bor_future_eq /=. rewrite Hres.
    rewrite (uniq_util.uniq_prvar_app_irrel (𝔄:=intₛ i32) c1 3%Z ζ1 π) Hrr. done.
  Qed.
End place_res.

Print Assumptions res_pair_type.
Print Assumptions res_nested_type.
