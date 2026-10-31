From iris.proofmode Require Import coq_tactics reduction.
From iris.proofmode Require Export tactics.
From iris.program_logic Require Export weakestpre.
From iris.program_logic Require Import lifting.
From lrust.lang Require Export tactics lifting.
Set Default Proof Using "Type".
Import uPred.

Lemma tac_wp_value `{!lrustGS Σ} Δ E Φ e v :
  IntoVal e v →
  envs_entails Δ (Φ v) → envs_entails Δ (WP e @ E {{ Φ }}).
Proof. rewrite envs_entails_unseal=> ? ->. by apply wp_value. Qed.

Ltac wp_value_head := eapply tac_wp_value; [tc_solve|reduction.pm_prettify].

Lemma tac_wp_pure `{!lrustGS Σ} K Δ Δ' E e1 e2 φ n Φ :
  PureExec φ n e1 e2 →
  φ →
  MaybeIntoLaterNEnvs n Δ Δ' →
  envs_entails Δ' (WP fill K e2 @ E {{ Φ }}) →
  envs_entails Δ (WP fill K e1 @ E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> ??? HΔ'. rewrite into_laterN_env_sound /=.
  rewrite -wp_bind HΔ' -wp_pure_step_later //. rewrite -wp_bind_inv. f_equiv.
  by iIntros.
Qed. 

Tactic Notation "wp_pure" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) => reshape_expr e ltac:(fun K e' =>
    unify e' efoc;
    eapply (tac_wp_pure K);
    [simpl; tc_solve                (* PureExec *)
    |try done                       (* The pure condition for PureExec *)
    |tc_solve                       (* IntoLaters *)
    |simpl_subst; try wp_value_head (* new goal *)])
   || fail "wp_pure: cannot find" efoc "in" e "or" efoc "is not a reduct"
  | _ => fail "wp_pure: not a 'wp'"
  end.

Lemma tac_wp_eq_loc `{!lrustGS Σ} K Δ Δ' E i1 i2 l1 l2 b1 b2 Φ :
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i1 Δ' = Some (false, l1 ↦b [b1])%I →
  envs_lookup i2 Δ' = Some (false, l2 ↦b [b2])%I →
  envs_entails Δ' (WP fill K (Lit (bool_decide (l1 = l2))) @ E {{ Φ }}) →
  envs_entails Δ (WP fill K (BinOp EqOp (Lit (LitLoc l1)) (Lit (LitLoc l2))) @ E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> ? /envs_lookup_sound /=. rewrite sep_elim_l=> ?.
  move /envs_lookup_sound; rewrite sep_elim_l=> ? HΔ. rewrite -wp_bind.
  rewrite into_laterN_env_sound /=. 
  iApply wp_eq_loc; trivial; by apply entails_wand, later_mono.
Qed.

Tactic Notation "wp_eq_loc" :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
     reshape_expr e ltac:(fun K e' => eapply (tac_wp_eq_loc K));
       [tc_solve|iAssumptionCore|iAssumptionCore|simpl; try wp_value_head]
  | _ => fail "wp_pure: not a 'wp'"
  end.

Tactic Notation "wp_rec" := wp_pure (App _ _).
Tactic Notation "wp_lam" := wp_rec.
Tactic Notation "wp_let" := wp_lam.
Tactic Notation "wp_seq" := wp_let.
Tactic Notation "wp_op" := wp_pure (BinOp _ _ _) || wp_eq_loc.
Tactic Notation "wp_if" := wp_pure (If _ _ _).
Tactic Notation "wp_case" := wp_pure (Case _ _); try wp_value_head.

Lemma tac_wp_bind `{!lrustGS Σ} K Δ E Φ e :
  envs_entails Δ (WP e @ E {{ v, WP fill K (of_val v) @ E {{ Φ }} }})%I →
  envs_entails Δ (WP fill K e @ E {{ Φ }}).
Proof. rewrite envs_entails_unseal=> ->. apply: wp_bind. Qed.

Ltac wp_bind_core K :=
  lazymatch eval hnf in K with
  | [] => idtac
  | _ => apply (tac_wp_bind K); simpl
  end.

Tactic Notation "wp_bind" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) => reshape_expr e ltac:(fun K e' =>
    match e' with
    | efoc => unify e' efoc; wp_bind_core K
    end) || fail "wp_bind: cannot find" efoc "in" e
  | _ => fail "wp_bind: not a 'wp'"
  end.

Section heap.
Context `{!lrustGS Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types Δ : envs (uPredI (iResUR Σ)).

Lemma tac_wp_nd_int `{!lrustGS Σ} K Δ Δ' E Φ :
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  (∀z, envs_entails Δ' (WP fill K (Lit (LitInt z)) @ E {{ Φ }})) →
  envs_entails Δ (WP fill K NdInt @ E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> ? HΔ'. rewrite into_laterN_env_sound /=.
  rewrite -wp_bind /=. iIntros "Δ'". iApply (wp_nd_int with "[//]")=>/=. iNext.
  iIntros. by iApply HΔ'.
Qed.

End heap.

Tactic Notation "wp_apply" open_constr(lem) :=
  iPoseProofCore lem as false (fun H =>
    lazymatch goal with
    | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
      reshape_expr e ltac:(fun K e' =>
        wp_bind_core K; iApplyHyp H; try iNext; simpl) ||
      lazymatch iTypeOf H with
      | Some (_,?P) => fail "wp_apply: cannot apply" P
      end
    | _ => fail "wp_apply: not a 'wp'"
    end).

Tactic Notation "wp_nd_int" ident(z) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) => reshape_expr e ltac:(fun K e' =>
    unify e' NdInt;
    eapply (tac_wp_nd_int K);
    [tc_solve                                   (* IntoLaters *)
    |iIntros (z); simpl_subst; try wp_value_head (* new goal *)])
   || fail "wp_nd_int: cannot find NdInt in" e
  | _ => fail "wp_nd_int: not a 'wp'"
  end.
