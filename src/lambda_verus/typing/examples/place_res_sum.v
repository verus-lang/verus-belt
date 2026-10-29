From iris.proofmode Require Import proofmode.
From lrust.typing Require Export type function product programs own cont uninit int sum
  type_sum uniq_bor borrow place place_own place_resolve place_puniq place_sum place_res
  place_res_rslv place_res_ops.
From lrust.lang Require Import lang notation new_delete.
Set Default Proof Using "Type".

Section place_res_sum.
  Context `{!typeG Σ}.

  (*
  Resolving a local sum, then a case analysis on it:

  ```
  fn res_opt<'a>(x: Option<(i32, &'a mut i32)>) -> i32 {
      /* resolve x */
      match x { None => 0, Some(p) => p.0 }       // x is dropped
  }
  ```

  with the specification: if `x == None`, then `result == 0`; if `x == Some(p)`, then
  `result == p.0`, with the observation `fin(p.1) == cur(p.1)`, learnt when [x] is
  resolved. The argument slot [x] is an owned place [own (OfTy (Σ! +[(); int * &uniq int]))];
  it is resolved as a whole ([lty_res_ofty], from [xsum_resolve_keep] of
  [resolve_keep_just] and [prod_resolve_keep] of [resolve_keep_just] and
  [uniq_resolve_keep]) to [own (OfRes (Σ! …))]; the case analysis on the resolved sum
  ([type_case_oplace_res]) gives, in branch [i], the sum place
  [SumLty tyl i (OfRes (tyl +!! i))]. In the branch of [Some], the resolved payload is
  unfolded ([tctx_unfold_oplace_res_prod] below [PSum]), its first field is converted back
  to [OfTy int] ([tctx_oplace_res_to_ofty]) and read; in the branch of [None], the sum
  place is folded back ([tctx_fold_oplace_res_sum]). The slot is dropped in both branches
  ([type_drop_oplace_res_instr]).
  *)

  Notation opt_pair α := (Σ! +[(); int * &uniq{α} int])%T.
  Notation opt_pairₛ := (Σ! [unitₛ; (Zₛ * uniq_borₛ Zₛ)%ST])%ST.

  Definition res_opt : val :=
    fn: ["x"] :=
      (Skip;; #☠);;                                 (* resolve x *)
      case: !"x" of
      [ (#☠;; delete [ #3; "x"]);;                   (* None: drop x *)
        let: "z" := #0 in
        let: "ret" := new [ #1] in
        "ret" <- "z";;
        return: ["ret"];
        let: "a" := !("x" +ₗ #1) in                (* Some(p): p.0 *)
        ((#☠;; #☠);; delete [ #3; "x"]);;           (* drop x *)
        let: "ret" := new [ #1] in
        "ret" <- "a";;
        return: ["ret"]].

  Definition res_opt_spec : fn_spec [opt_pairₛ] Zₛ () :=
    λ _ post '-[(_, x)], λ mask π,
      (∀ pad, x = (pinj (Xl:=[unitₛ; (Zₛ * uniq_borₛ Zₛ)%ST]) 0%fin (), pad) →
        ∀ (lr: loc), post (lr, 0%Z) mask π) ∧
      (∀ (a: Z * ~~ (uniq_borₛ Zₛ)) pad,
        x = (pinj (Xl:=[unitₛ; (Zₛ * uniq_borₛ Zₛ)%ST]) 1%fin a, pad) →
        uniq_bor_future a.2 π = uniq_bor_current a.2 →
        ∀ (lr: loc), post (lr, a.1) mask π).

  (** A default payload, for the context step [PSum]. *)
  Definition w0 : ~~ (Zₛ * uniq_borₛ Zₛ)%ST := (0%Z, (inhabitant, 0%Z, inhabitant, 0%nat, 0%nat, inhabitant)).

  Lemma res_opt_type :
    typed_val res_opt ((fn<α>(∅; opt_pair α) → int) res_opt_spec) (res_opt, ()).
  Proof.
    unfold res_opt. unlock.
    opose proof (@type_fn _ _ _ [opt_pairₛ] Zₛ () ()
      (λ α, FP ∅ +[opt_pair α] int AtomicClosed)
      res_opt_spec _ [BNamed "x"] _ _ _) as H.
    unlock in H. apply H. clear H.
    intros α ϝ k wl. destruct wl as [vx []]. simpl_subst.
    have Alv: lctx_lft_alive (fp_E (FP ∅ +[opt_pair α] int AtomicClosed) ϝ) [ϝ ⊑ₗ []] α.
    { eapply lctx_lft_alive_external; [rewrite /fp_E /=; by left|solve_typing]. }
    iApply (typed_body_impl with "[]"); last first. {
      iApply typed_body_tctx_incl; [apply tctx_own_to_oplace|].
      (* resolve x, as a whole *)
      iApply type_seq.
      { apply (type_resolve_oplace_res_instr _ _ _ vx 3 (OfTy (opt_pair α)) (OfRes (opt_pair α)) 1).
        apply lty_res_ofty, (xsum_resolve_keep _ _ _
          ((-[const (const True); λ '(a, b), λ π, const (const True) a π ∧
              snd (vπ (𝔄:=uniq_borₛ Zₛ) b π) = fst (vπ (𝔄:=uniq_borₛ Zₛ) b π)])
            : plist (λ 𝔄, ~~ 𝔄 → proph_asn → Prop) [unitₛ; (Zₛ * uniq_borₛ Zₛ)%ST])).
        constructor; [apply resolve_keep_just|]. constructor; [|constructor].
        eapply resolve_keep_impl; [apply prod_resolve_keep; [apply resolve_keep_just|by apply uniq_resolve_keep]|].
        by intros [??] ?. }
      { solve_typing. } { reflexivity. }
      (* match x *)
      iApply (type_case_oplace_res _ _ _ _ vx 3 PHole +[(); int * &uniq{α} int]%T _ _ _ -[_; _]).
      iSplitL; [|iSplitL; [|done]].
      - (* None: fold back, drop x *)
        iApply typed_body_tctx_incl.
        { apply (tctx_fold_oplace_res_sum _ _ vx 3 PHole +[(); int * &uniq{α} int]%T 0%fin). }
        iApply type_seq.
        { apply (type_drop_oplace_res_instr _ _ _ vx 3 3 (OfRes (opt_pair α))); done. }
        { solve_typing. } { reflexivity. }
        iApply (type_int 0). iIntros (vz). simpl_subst.
        iApply (type_new 1). { lia. } iIntros (vret). simpl_subst.
        iApply type_assign. { solve_typing. } { by apply write_own. }
        { apply (resolve'_just _ _ _ (const True)). apply resolve_just. }
        iApply type_jump.
        { rewrite elem_of_list_singleton. reflexivity. }
        { solve_typing. }
        { solve_typing. }
        { reflexivity. }
      - (* Some(p): unfold the resolved payload, read p.0 *)
        iApply typed_body_tctx_incl.
        { eapply tctx_incl_trans;
            [apply (tctx_unfold_oplace_res_prod _ _ vx 3
              (PSum +[(); int * &uniq{α} int]%T 1%fin w0 PHole) int (&uniq{α} int))|].
          apply (tctx_oplace_res_to_ofty _ _ vx 3
            (PSum +[(); int * &uniq{α} int]%T 1%fin w0 (PFst PHole (OfRes (&uniq{α} int)))) int). }
        iApply (type_let with "[]").
        { apply (type_read_oplace_instr _ _ _ vx 3
            (PSum +[(); int * &uniq{α} int]%T 1%fin w0 (PFst PHole (OfRes (&uniq{α} int)))) int);
            [done|apply _]. }
        { solve_typing. } { reflexivity. }
        iIntros (va). simpl_subst.
        iApply type_seq.
        { apply (type_drop_oplace_res_instr _ _ _ vx 3 3
            (SumLty +[(); int * &uniq{α} int]%T 1%fin (ProdLty (OfTy int) (OfRes (&uniq{α} int)))));
            done. }
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
    intros post [[lx [[[]|[[z1 m]|[]]] pad]] []] mask π. simpl.
    - intros [Hn _]. rewrite /trans_upper /trans_tail /=.
      intros _ l _ z ->. by apply (Hn pad).
    - intros [_ Hs]. rewrite /trans_upper /trans_tail /=.
      intros [_ Hres] l _ z ->. apply (Hs (z1, m) pad); [done|].
      destruct m as [[[[[l' z2] ξi] d] g] idx]. simpl in *.
      rewrite uniq_bor_future_eq. exact Hres.
  Qed.
End place_res_sum.

Print Assumptions res_opt_type.
