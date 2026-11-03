Require Import guarding.internal.na_invariants_fork.
From guarding Require Import guard.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Export weakestpre.
From iris.program_logic Require Import ectx_lifting.
From lrust.lang Require Export lang heap time.
From lrust.lang Require Import tactics.
From lrust.util Require Import update atomic_lock_counter.
Set Default Proof Using "Type".
Import uPred.

Open Scope Z_scope.

Class lrustGS Σ := LRustGS {
  lrustGS_invGS : invGS Σ;
  #[global] lrustGS_na_invGS :: na_invG Σ;
  #[global] lrustGS_atomic_lock_ctr_invGS :: alc_logicG Σ;
  #[global] lrustGS_gen_heapGS :: heapGS Σ;
  #[global] lrustGS_gen_timeGS :: timeGS Σ
}.

Global Program Instance lrustGS_irisGS `{!lrustGS Σ} : irisGS lrust_lang Σ := {
  iris_invGS := lrustGS_invGS;
  state_interp σ stepcnt κs _ := (@heap_ctx Σ _ lrustGS_invGS lrustGS_na_invGS lrustGS_atomic_lock_ctr_invGS σ ∗ time_interp stepcnt)%I;
  fork_post _ := True%I;
  num_laters_per_step n := (sum_advance_credits (n + 1))%nat
}.
Next Obligation.
  intros. iIntros "/= [$ H]". by iMod (time_interp_step with "H") as "$".
Qed.

Global Opaque iris_invGS.

Ltac inv_lit :=
  repeat match goal with
  | H : lit_eq _ ?x ?y |- _ => inversion H; clear H; simplify_map_eq/=
  | H : lit_neq ?x ?y |- _ => inversion H; clear H; simplify_map_eq/=
  end.

Ltac inv_bin_op_eval :=
  repeat match goal with
  | H : bin_op_eval _ ?c _ _ _ |- _ => is_constructor c; inversion H; clear H; simplify_eq/=
  end.

Local Hint Extern 0 (atomic _) => solve_atomic : core.
Local Hint Extern 0 (base_reducible _ _) => eexists _, _, _, _; simpl : core.

Local Hint Constructors head_step bin_op_eval lit_neq lit_eq : core.
Local Hint Resolve alloc_fresh : core.
Local Hint Resolve to_of_val : core.

Class AsRec (e : expr) (f : binder) (xl : list binder) (erec : expr) :=
  as_rec : e = Rec f xl erec.
Global Instance AsRec_rec f xl e : AsRec (Rec f xl e) f xl e := eq_refl.
Global Instance AsRec_rec_locked_val v f xl e :
  AsRec (of_val v) f xl e → AsRec (of_val (locked v)) f xl e.
Proof. by unlock. Qed.

Class DoSubst (x : binder) (es : expr) (e er : expr) :=
  do_subst : subst' x es e = er.
Global Hint Extern 0 (DoSubst _ _ _ _) =>
  rewrite /DoSubst; simpl_subst; reflexivity : typeclass_instances.

Class DoSubstL (xl : list binder) (esl : list expr) (e er : expr) :=
  do_subst_l : subst_l xl esl e = Some er.
Global Instance do_subst_l_nil e : DoSubstL [] [] e e.
Proof. done. Qed.
Global Instance do_subst_l_cons x xl es esl e er er' :
  DoSubstL xl esl e er' → DoSubst x es er' er →
  DoSubstL (x :: xl) (es :: esl) e er.
Proof. rewrite /DoSubstL /DoSubst /= => -> <- //. Qed.
Global Instance do_subst_vec xl (vsl : vec val (length xl)) e :
  DoSubstL xl (of_val <$> vec_to_list vsl) e (subst_v xl vsl e).
Proof. by rewrite /DoSubstL subst_v_eq. Qed.

Section lifting.
Context `{!lrustGS Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types e : expr.
Implicit Types ef : option expr.

Local Open Scope nat_scope.

Lemma sqr_bound (n: nat) :
    (2 ^ (S n) * 2^ (S n) ≤ (sum_advance_credits (n + 1))).
Proof.
  destruct n.
  - cbn; lia.
  - rewrite Nat.add_1_r.
    cbn [sum_advance_credits Nat.pow].
    rewrite /advance_credits.
    nia.
Qed.

Lemma Sexp_le_exp_S_lemma (n: nat) :
    (S (2 ^ (S n))) ≤ (2 ^ (S (S n))).
Proof.
    cbn.
    assert (2 ^ n ≥ 1) as H1; last by lia.
    induction n; cbn; nia.
Qed.
    
Lemma sqr_bound' (n: nat) :
    ((2 ^ (S (S n))) * ((2^ (S (S n)))) ≤ (sum_advance_credits (n + 1))).
Proof.
  destruct n.
  - cbn; lia.
  - rewrite Nat.add_1_r.
    cbn [sum_advance_credits Nat.pow].
    rewrite /advance_credits.
    nia.
Qed.

Lemma sqr_bound'' (n: nat) :
    (S (2 ^ (S n)) * (S (2^ (S n))) ≤ (sum_advance_credits (n + 1))).
Proof.
    assert (0 ≤ S (2 ^ (S n))) as H1. { nia. }
    assert (∀ x y z, 0 ≤ x → x ≤ y → y * y ≤ z → x * x ≤ z) as H. { intros. nia. }
    apply (H _ _ _ H1 (Sexp_le_exp_S_lemma n) (sqr_bound' n)).
Qed.

Lemma wp_step_fupdN_time_receipt n m E1 E2 e P Φ :
  TCEq (to_val e) None → E2 ⊆ E1 → ↑advN ∪ ↑timeN ⊆ E1 →
  time_ctx -∗ ⧖n -∗
    (⧗m ∧ ((|={E1∖E2,∅}=> |={∅}▷=>^(S ((n + m) * (n + m))) |={∅,E1∖E2}=> P) ∗
           WP e @ E2 {{ v, P ={E1}=∗ Φ v }})) -∗
  WP e @ E1 {{ Φ }}.
Proof.
  iIntros (???) "#TIME #Hn H".
  iApply (wp_step_fupdN (S ((n + m) * (n + m))) _ _ E2)=>//. iSplit.
  - iIntros "* [_ Ht]". iMod (time_receipt_le with "TIME Ht Hn [H]") as "[% ?]"=>//.
    + iDestruct "H" as "[$ _]".
    + iApply fupd_mask_weaken.
      2: { iIntros "_ !> !% /=". 
           have Hx := sqr_bound ns.
           nia.
      }
      set_solver.
  - iDestruct "H" as "[_ $]".
Qed.

Lemma wp_step_fupdN_time_receipt' n m E1 E2 e P Φ :
  TCEq (to_val e) None → E2 ⊆ E1 → ↑advN ∪ ↑timeN ⊆ E1 →
  time_ctx -∗ ⧖n -∗
    (⧗m ∧ ((|={E1∖E2,∅}=> |={∅}▷=>^((S ((S (n + m)) * S (n + m)))) |={∅,E1∖E2}=> P) ∗
           WP e @ E2 {{ v, P ={E1}=∗ Φ v }})) -∗
  WP e @ E1 {{ Φ }}.
Proof.
  iIntros (???) "#TIME #Hn H".
  iApply (wp_step_fupdN (S (((S (n + m)) * S (n + m)))) _ _ E2)=>//. iSplit.
  - iIntros "* [_ Ht]". iMod (time_receipt_le with "TIME Ht Hn [H]") as "[% ?]"=>//.
    + iDestruct "H" as "[$ _]".
    + iApply fupd_mask_weaken.
      2: { iIntros "_ !> !% /=". 
           have Hx := sqr_bound'' ns.
           nia.
      }
      set_solver.
  - iDestruct "H" as "[_ $]".
Qed.

Lemma wp_step_fupdN_persistent_time_receipt n E1 E2 e P Φ :
  TCEq (to_val e) None → E2 ⊆ E1 → ↑advN ∪ ↑timeN ⊆ E1 →
  time_ctx -∗ ⧖n -∗ (|={E1∖E2,∅}=> |={∅}▷=>^(S (n * n)) |={∅, E1∖E2}=> P) -∗
  WP e @ E2 {{ v, P ={E1}=∗ Φ v }} -∗
  WP e @ E1 {{ Φ }}.
Proof. 
  iIntros (???) "#TIME #Hn HP Hwp".
  iApply (wp_step_fupdN_time_receipt _ _ E1 E2 with "TIME Hn [> -]")=>//.
  iMod cumulative_time_receipt_0 as "$". iFrame. by rewrite -plus_n_O.
Qed.


Lemma wp_step_fupdN_persistent_time_receipt' n E1 E2 e P Φ :
  TCEq (to_val e) None → E2 ⊆ E1 → ↑advN ∪ ↑timeN ⊆ E1 →
  time_ctx -∗ ⧖n -∗ (|={E1∖E2,∅}=> |={∅}▷=>^(S ((S n) * (S n))) |={∅, E1∖E2}=> P) -∗
  WP e @ E2 {{ v, P ={E1}=∗ Φ v }} -∗
  WP e @ E1 {{ Φ }}.
Proof. 
  iIntros (???) "#TIME #Hn HP Hwp".
  iApply (wp_step_fupdN_time_receipt' _ _ E1 E2 with "TIME Hn [> -]")=>//.
  iMod cumulative_time_receipt_0 as "$". iFrame. by rewrite -plus_n_O.
Qed.

Lemma wp_cumulative_time_receipt_linear E e Φ d :
  TCEq (to_val e) None → ↑advN ∪ ↑timeN ⊆ E →
  time_ctx -∗
  ⧖d -∗
  (⧗(S (S d)) -∗ WP e @ (E∖↑advN) {{ v, Φ v }}) -∗
  WP e @ E {{ Φ }}. 
Proof.
  rewrite !wp_unfold /wp_pre /=. iIntros (-> ?) "#TIME ⧖ Hwp".
  iIntros (?????) "[Hσ Ht]".
  iMod (step_cumulative_time_receipt with "TIME Ht ⧖") as "[%ns1 [Ht [EnFalse [⧗ Hclose]]]]"=>//. { solve_ndisj. }
  replace (d + 2) with (S (S d)) by lia.
  (* iDestruct "⧗" as "[⧗ ⧗1 ]". *)
  iDestruct ("Hwp" with "⧗") as "Hwp".
  iMod ("Hwp" $! _ (ns-1)%nat _ [] 0%nat with "[$]") as "[$ Hwp]".
  iIntros "!>" (e2 σ2 efs stp) "credit".
  iDestruct "credit" as "[Hc1 credit]".
  rewrite (sum_advance_credits_ge1 (ns+1)); last by lia.
  iDestruct "credit" as "[credit1 credit2]".
  iCombine "credit2 Hc1" as "credit2".
  replace (ns - 1 + 1)%nat with ns by lia.
  replace (ns + 1 - 1)%nat with ns by lia.
  iMod ("Hwp" $! e2 σ2 efs stp with "credit2") as "Hwp".
  iIntros "!> !>". iMod "Hwp". iModIntro.
  iApply (step_fupdN_nmono (sum_advance_credits (ns))); first by lia.
  iApply (step_fupdN_wand with "Hwp"). iIntros ">([$ Ht] & Hwp & $)".
  replace (S (ns - 1))%nat with ns by lia.
  iMod ("Hclose" with "[EnFalse Ht credit1]") as "?". {
    iFrame. iApply (lc_weaken with "credit1"). 
    rewrite !Nat.add_1_r.
    cbn [Nat.pow].
    opose proof (advance_credits_mono (2 * 2 ^ ns) (2 * (2 * 2 ^ ns)) _);nia.
  }
  iFrame.
  iApply (wp_wand with "[Hwp]"); [iApply (wp_mask_mono with "Hwp"); solve_ndisj|].
  iIntros "!> % H". by iApply "H".
Qed.

Lemma wp_cumulative_time_receipt2 E e Φ :
  TCEq (to_val e) None → ↑advN ∪ ↑timeN ⊆ E →
  time_ctx -∗
  (⧗2 -∗ WP e @ (E∖↑advN) {{ v, Φ v }}) -∗
  WP e @ E {{ Φ }}. 
Proof.
  rewrite !wp_unfold /wp_pre /=. iIntros (-> ?) "#TIME Hwp".
  iIntros (?????) "[Hσ Ht]".
  iMod persistent_time_receipt_0 as "⧖".
  iMod (step_cumulative_time_receipt with "TIME Ht ⧖") as "[%ns1 [Ht [EnFalse [[⧗1 ⧗2] Hclose]]]]"=>//. { solve_ndisj. }
  iDestruct ("Hwp" with "⧗2") as "Hwp".
  iMod ("Hwp" $! _ (ns-1)%nat _ [] 0%nat with "[$]") as "[$ Hwp]".
  iIntros "!>" (e2 σ2 efs stp) "credit".
  iDestruct "credit" as "[Hc1 credit]".
  rewrite (sum_advance_credits_ge1 (ns+1)); last by lia.
  iDestruct "credit" as "[credit1 credit2]".
  iCombine "credit2 Hc1" as "credit2".
  replace (ns - 1 + 1)%nat with ns by lia.
  replace (ns + 1 - 1)%nat with ns by lia.
  iMod ("Hwp" $! e2 σ2 efs stp with "credit2") as "Hwp".
  iIntros "!> !>". iMod "Hwp". iModIntro.
  iApply (step_fupdN_nmono (sum_advance_credits (ns))); first by lia.
  iApply (step_fupdN_wand with "Hwp"). iIntros ">([$ Ht] & Hwp & $)".
  replace (S (ns - 1))%nat with ns by lia.
  iMod ("Hclose" with "[EnFalse Ht credit1]") as "?". {
    iFrame. iApply (lc_weaken with "credit1"). 
    rewrite !Nat.add_1_r.
    cbn [Nat.pow].
    opose proof (advance_credits_mono (2 * 2 ^ ns) (2 * (2 * 2 ^ ns)) _);nia.
  }
  iFrame.
  iApply (wp_wand with "[Hwp]"); [iApply (wp_mask_mono with "Hwp"); solve_ndisj|].
  iIntros "!> % H". by iApply "H".
Qed.

Lemma wp_cumulative_time_receipt1 E e Φ :
  TCEq (to_val e) None → ↑advN ∪ ↑timeN ⊆ E →
  time_ctx -∗ 
  (⧗1 -∗ WP e @ (E∖↑advN) {{ v, Φ v }}) -∗
  WP e @ E {{ Φ }}.
Proof.
  rewrite !wp_unfold /wp_pre /=. iIntros (-> ?) "#TIME Hwp".
  iIntros (?????) "[Hσ Ht]".
  iMod persistent_time_receipt_0 as "⧖".
  iMod (step_cumulative_time_receipt with "TIME Ht ⧖") as "[%ns1 [Ht [EnFalse [[_ ⧗ ] Hclose]]]]"=>//. { solve_ndisj. }
  replace 2 with (1+1) by lia.
  iDestruct "⧗" as "[⧗ _]".
  iDestruct ("Hwp" with "⧗") as "Hwp".
  iMod ("Hwp" $! _ (ns-1)%nat _ [] 0%nat with "[$]") as "[$ Hwp]".
  iIntros "!>" (e2 σ2 efs stp) "credit".
  iDestruct "credit" as "[Hc1 credit]".
  rewrite (sum_advance_credits_ge1 (ns+1)); last by lia.
  iDestruct "credit" as "[credit1 credit2]".
  iCombine "credit2 Hc1" as "credit2".
  replace (ns - 1 + 1)%nat with ns by lia.
  replace (ns + 1 - 1)%nat with ns by lia.
  iMod ("Hwp" $! e2 σ2 efs stp with "credit2") as "Hwp".
  iIntros "!> !>". iMod "Hwp". iModIntro.
  iApply (step_fupdN_nmono (sum_advance_credits (ns))); first by lia.
  iApply (step_fupdN_wand with "Hwp"). iIntros ">([$ Ht] & Hwp & $)".
  replace (S (ns - 1))%nat with ns by lia.
  iMod ("Hclose" with "[EnFalse Ht credit1]") as "?". {
    iFrame. iApply (lc_weaken with "credit1"). 
    rewrite !Nat.add_1_r.
    cbn [Nat.pow].
    nia.
  }
  iFrame.
  iApply (wp_wand with "[Hwp]"); [iApply (wp_mask_mono with "Hwp"); solve_ndisj|].
  iIntros "!> % H". by iApply "H".
Qed.

Lemma wp_persistent_time_receipt n E e Φ :
  TCEq (to_val e) None → ↑advN ∪ ↑timeN ⊆ E →
  time_ctx -∗
  ⧖n -∗
  (£(advance_credits n) -∗ ⧖(S n) -∗ WP e @ (E∖↑advN) {{ v, Φ v }}) -∗
  WP e @ E {{ Φ }}.
Proof.
  intros tceq Hmask. iIntros "#TIME #⧖ Hwp".
  iApply wp_cumulative_time_receipt1; trivial.
  iIntros "⧗".
  iMod (cumulative_persistent_time_receipt_get_credits with "TIME ⧗ ⧖") as "[⧖S £]"; first by solve_ndisj.
  replace (n+1)%nat with (S n) by lia.
  iApply ("Hwp" with "£ ⧖S").
Qed.

(** Base axioms for core primitives of the language: Stateless reductions *)
Lemma wp_fork E e :
  {{{ ▷ WP e {{ _, True }} }}} Fork e @ E {{{ RET LitV LitPoison; True }}}.
Proof.
  iIntros (?) "?HΦ". iApply wp_lift_atomic_base_step; [done|].
  iIntros (σ1 stepcnt κ κs n) "[Hσ Ht] !>"; iSplit; first by eauto.
  iNext; iIntros (v2 σ2 efs Hstep); inv_head_step. iFrame.
  iMod (time_interp_step with "Ht") as "$". iIntros "credit". by iApply "HΦ".
Qed.

(** Pure reductions *)
Local Ltac solve_exec_safe :=
  intros; destruct_and?; subst; do 3 eexists; econstructor; simpl; eauto with lia.
Local Ltac solve_exec_puredet :=
  simpl; intros; destruct_and?; inv_head_step; inv_bin_op_eval; inv_lit; done.
Local Ltac solve_pure_exec :=
  intros ?; apply nsteps_once, pure_base_step_pure_step;
    constructor; [solve_exec_safe | solve_exec_puredet].

Global Instance pure_rec e f xl erec erec' el :
  AsRec e f xl erec →
  TCForall AsVal el →
  Closed (f :b: xl +b+ []) erec →
  DoSubstL (f :: xl) (e :: el) erec erec' →
  PureExec True 1 (App e el) erec'.
Proof.
  rewrite /AsRec /DoSubstL=> -> /TCForall_Forall Hel ??. solve_pure_exec.
  eapply Forall_impl; [exact Hel|]. intros e' [v <-]. rewrite to_of_val; eauto.
Qed.

Close Scope nat_scope.

Global Instance pure_le n1 n2 :
  PureExec True 1 (BinOp LeOp (Lit (LitInt n1)) (Lit (LitInt n2)))
                  (Lit (bool_decide (n1 ≤ n2))).
Proof. solve_pure_exec. Qed.

Global Instance pure_eq_int n1 n2 :
  PureExec True 1 (BinOp EqOp (Lit (LitInt n1)) (Lit (LitInt n2))) (Lit (bool_decide (n1 = n2))).
Proof. case_bool_decide; solve_pure_exec. Qed.

Global Instance pure_eq_loc_0_r l :
  PureExec True 1 (BinOp EqOp (Lit (LitLoc l)) (Lit (LitInt 0))) (Lit false).
Proof. solve_pure_exec. Qed.

Global Instance pure_eq_loc_0_l l :
  PureExec True 1 (BinOp EqOp (Lit (LitInt 0)) (Lit (LitLoc l))) (Lit false).
Proof. solve_pure_exec. Qed.

Global Instance pure_plus z1 z2 :
  PureExec True 1 (BinOp PlusOp (Lit $ LitInt z1) (Lit $ LitInt z2)) (Lit $ LitInt $ z1 + z2).
Proof. solve_pure_exec. Qed.

Global Instance pure_minus z1 z2 :
  PureExec True 1 (BinOp MinusOp (Lit $ LitInt z1) (Lit $ LitInt z2)) (Lit $ LitInt $ z1 - z2).
Proof. solve_pure_exec. Qed.

Global Instance pure_mult z1 z2 :
  PureExec True 1 (BinOp MultOp (Lit $ LitInt z1) (Lit $ LitInt z2)) (Lit $ LitInt $ z1 * z2).
Proof. solve_pure_exec. Qed.

Global Instance pure_offset l z  :
  PureExec True 1 (BinOp OffsetOp (Lit $ LitLoc l) (Lit $ LitInt z)) (Lit $ LitLoc $ l +ₗ z).
Proof. solve_pure_exec. Qed.

Global Instance pure_case i e el :
  PureExec (0 ≤ i ∧ el !! (Z.to_nat i) = Some e) 1 (Case (Lit $ LitInt i) el) e | 10.
Proof. solve_pure_exec. Qed.

Global Instance pure_if b e1 e2 :
  PureExec True 1 (If (Lit (lit_of_bool b)) e1 e2) (if b then e1 else e2) | 1.
Proof. destruct b; solve_pure_exec. Qed.

Lemma wp_nd_int E :
  {{{ True }}} NdInt @ E
  {{{ z, RET LitV $ LitInt z; True }}}.
Proof.
  iIntros (? _) "Φ". iApply wp_lift_atomic_base_step_no_fork; auto.
  iIntros (σ1 stepcnt κ κs n') "[σ t] !>"; iSplit. { unshelve auto. apply 0. }
  iNext; iIntros (v2 σ2 efs Hstep); inv_head_step.
  iMod (time_interp_step with "t") as "$". iFrame "σ". iIntros "credit".
  by iDestruct ("Φ" with "[//]") as "$".
Qed.

Lemma wp_eq_loc E (l1 : loc) (l2: loc) b1 b2 P Φ :
  (P -∗ ▷ l1 ↦b [b1]) →
  (P -∗ ▷ l2 ↦b [b2]) →
  (P -∗ ▷ Φ (LitV (bool_decide (l1 = l2)))) →
  P -∗ WP BinOp EqOp (Lit (LitLoc l1)) (Lit (LitLoc l2)) @ E {{ Φ }}.
Proof.
  iIntros (Hl1 Hl2 Hpost) "HP".
  destruct (bool_decide_reflect (l1 = l2)) as [->|].
  - iApply wp_lift_pure_det_base_step_no_fork';
      [done|solve_exec_safe|solve_exec_puredet|].
    iAssert (▷ (WP Lit true @ E {{ v, Φ v }}))%I with "[HP]" as "X".
     + iApply wp_value. by iApply Hpost.
     + iNext. iIntros. iFrame "X".
  - iApply wp_lift_atomic_base_step_no_fork; subst=>//.
    iIntros (σ1 stepcnt κ κs n') "[Hσ1 Ht]".
    iMod (time_interp_step with "Ht") as "$".
    iModIntro. inv_head_step. iSplitR.
    { iPureIntro. repeat eexists. econstructor. eapply BinOpEqFalse. by auto. }
    (* We need to do a little gymnastics here to apply Hne now and strip away a
       ▷ but also have the ↦s. *)
    iAssert ((▷ l1 ↦b [b1]) ∧ (▷ l2 ↦b [b2]) ∧ ▷ Φ (LitV false))%I
      with "[HP]" as "HP".
    { iSplit; last iSplit.
      + by iApply Hl1.
      + by iApply Hl2.
      + by iApply Hpost. }
    clear Hl1 Hl2. iNext. iIntros (e2 σ2 efs Hs) "£".
    iDestruct "Hσ1" as (hF) "(HB & HhF & %REL & ato)".
    inv_head_step. iSplitR=>//. inv_bin_op_eval; inv_lit.
    + iDestruct "HP" as "[Hl1 _]".
      iDestruct (bytes_ctx_lookup with "HB Hl1") as %[[ls [? _]] _]. by simplify_map_eq.
    + iDestruct "HP" as "[_ [Hl2 _]]".
      iDestruct (bytes_ctx_lookup with "HB Hl2") as %[[ls [? _]] _]. by simplify_map_eq.
    + iDestruct "HP" as "[_ [_ $]]". iExists hF. by iFrame.
Qed.

(** Proof rules for working on the n-ary argument list. *)
Lemma wp_app_ind E f (el : list expr) (Ql : vec (val → iProp Σ) (length el)) vs Φ :
  AsVal f →
  ([∗ list] eQ ∈ zip el Ql, WP eQ.1 @ E {{ eQ.2 }}) -∗
    (∀ vl : vec val (length el), ([∗ list] vQ ∈ zip vl Ql, vQ.2 $ vQ.1) -∗
                    WP App f (of_val <$> vs ++ vl) @ E {{ Φ }}) -∗
    WP App f ((of_val <$> vs) ++ el) @ E {{ Φ }}.
Proof.
  intros [vf <-]. revert vs Ql.
  induction el as [|e el IH]=>/= vs Ql; inv_vec Ql; simpl.
  - iIntros "_ H". iSpecialize ("H" $! [#]). rewrite !app_nil_r /=. by iApply "H".
  - iIntros (Q Ql) "[He Hl] HΦ".
    change (App (of_val vf) ((of_val <$> vs) ++ e :: el))
      with (fill_item (AppRCtx vf vs el) e).
    iApply wp_bind. iApply (wp_wand with "He"). iIntros (v) "HQ /=".
    rewrite cons_middle (assoc app) -(fmap_app _ _ [v]).
    iApply (IH _ _ with "Hl"). iIntros "* Hvl". rewrite -assoc.
    iApply ("HΦ" $! (v:::vl)). iFrame.
Qed.

Lemma wp_app_vec E f el (Ql : vec (val → iProp Σ) (length el)) Φ :
  AsVal f →
  ([∗ list] eQ ∈ zip el Ql, WP eQ.1 @ E {{ eQ.2 }}) -∗
    (∀ vl : vec val (length el), ([∗ list] vQ ∈ zip vl Ql, vQ.2 $ vQ.1) -∗
                    WP App f (of_val <$> (vl : list val)) @ E {{ Φ }}) -∗
    WP App f el @ E {{ Φ }}.
Proof. iIntros (Hf). by iApply (wp_app_ind _ _ _ _ []). Qed.

Lemma wp_app (Ql : list (val → iProp Σ)) E f el Φ :
  length Ql = length el → AsVal f →
  ([∗ list] eQ ∈ zip el Ql, WP eQ.1 @ E {{ eQ.2 }}) -∗
    (∀ vl : list val, ⌜length vl = length el⌝ -∗
            ([∗ list] k ↦ vQ ∈ zip vl Ql, vQ.2 $ vQ.1) -∗
             WP App f (of_val <$> (vl : list val)) @ E {{ Φ }}) -∗
    WP App f el @ E {{ Φ }}.
Proof.
  iIntros (Hlen Hf) "Hel HΦ". rewrite -(vec_to_list_to_vec Ql).
  generalize (list_to_vec Ql). rewrite Hlen. clear Hlen Ql=>Ql.
  iApply (wp_app_vec with "Hel"). iIntros (vl) "Hvl".
  iApply ("HΦ" with "[%] Hvl"). by rewrite length_vec_to_list.
Qed.

Close Scope nat_scope.

(** * The MiniRust layer *)

Local Ltac heap_split :=
  iDestruct "Hσ" as (hF) "(HB & HhF & %REL & ato)".

(** ** Value-level expressions *)
Global Instance pure_mk_tuple (vs : list Value) :
  PureExec True 1 (MkTuple (MLit <$> vs)) (MLit (VTuple vs)).
Proof.
  intros _. apply nsteps_once, pure_base_step_pure_step. constructor.
  - intros σ. do 3 eexists. constructor.
    apply Forall2_fmap_l, Forall_Forall2_diag, Forall_true. done.
  - intros ????? Hstep. inv_head_step.
    match goal with H : Forall2 _ _ ?vs' |- _ =>
      rename H into Hvs; rename vs' into ws; assert (ws = vs) as -> end;
      [|done].
    revert ws Hvs. induction vs as [|v vs IH]; intros ws Hvs;
      inversion Hvs; simplify_eq/=; [done|]. f_equal. by apply IH.
Qed.

Local Ltac solve_pure_exec' :=
  intros ?; apply nsteps_once, pure_base_step_pure_step;
    constructor; [intros; destruct_and?; subst; do 3 eexists; econstructor; eauto
                 |intros; inv_head_step; done].

Global Instance pure_proj i vs v :
  PureExec (vs !! i = Some v) 1 (Proj i (MLit (VTuple vs))) (MLit v).
Proof.
  intros ?. apply nsteps_once, pure_base_step_pure_step. constructor.
  - intros σ. do 3 eexists. by econstructor.
  - intros ????? Hstep. inv_head_step. by simplify_eq.
Qed.

Global Instance pure_mk_variant t v :
  PureExec True 1 (MkVariant t (MLit v)) (MLit (VVariant t v)).
Proof. solve_pure_exec'. Qed.

Global Instance pure_variant_tag t v :
  PureExec True 1 (VariantTag (MLit (VVariant t v))) (MLit (VInt t)).
Proof. solve_pure_exec'. Qed.

Global Instance pure_variant_data t v :
  PureExec True 1 (VariantData (MLit (VVariant t v))) (MLit v).
Proof. solve_pure_exec'. Qed.

Global Instance pure_to_lit v lit :
  PureExec (value_to_lit v = Some lit) 1 (ToLit (MLit v)) (Lit lit).
Proof.
  intros ?. apply nsteps_once, pure_base_step_pure_step. constructor.
  - intros σ. do 3 eexists. by econstructor.
  - intros ????? Hstep. inv_head_step. by simplify_eq.
Qed.

Global Instance pure_of_lit lit v :
  PureExec (lit_to_value lit = Some v) 1 (OfLit (Lit lit)) (MLit v).
Proof.
  intros ?. apply nsteps_once, pure_base_step_pure_step. constructor.
  - intros σ. do 3 eexists. by econstructor.
  - intros ????? Hstep. inv_head_step. by simplify_eq.
Qed.

(** ** Allocation and deallocation of bytes *)
Lemma wp_alloc_bytes E (n : Z) :
  0 < n →
  {{{ True }}} Alloc (Lit $ LitInt n) @ E
  {{{ l (sz: nat), RET LitV $ LitLoc l; ⌜n = sz⌝ ∗ †l…sz ∗ l ↦b replicate sz Uninit }}}.
Proof.
  iIntros (? Φ) "_ HΦ". iApply wp_lift_atomic_base_step_no_fork; auto.
  iIntros (σ1 stepcnt κ κs n') "[Hσ Ht] !>"; iSplit; first by auto.
  iNext; iIntros (v2 σ2 efs Hstep); inv_head_step.
  iMod (heap_alloc_bytes with "Hσ") as "[$ Hl]"; [done..|].
  iMod (time_interp_step with "Ht") as "$". iIntros "credit".
  iModIntro; iSplit=> //. iApply ("HΦ" $! _ (Z.to_nat n)). auto with lia iFrame.
Qed.

Lemma wp_free_bytes E (n:Z) l bs :
  ↑naN ⊆ E → n = length bs →
  {{{ ▷ l ↦b bs ∗ ▷ †l…(length bs) }}}
    Free (Lit $ LitInt n) (Lit $ LitLoc l) @ E
  {{{ RET LitV LitPoison; True }}}.
Proof.
  iIntros (?? Φ) "[>Hmt >Hf] HΦ". iApply wp_lift_atomic_base_step_no_fork; auto.
  iIntros (σ1 stepcnt κ κs n') "[Hσ Ht]".
  iMod (heap_free_bytes _ _ _ n with "Hσ Hmt Hf") as "(% & % & Hσ)"=>//.
  iMod (time_interp_step with "Ht") as "$".
  iModIntro; iSplit; first by auto.
  iNext; iIntros (v2 σ2 efs Hstep); inv_head_step. iIntros "credit".
  iModIntro; iSplit=> //. iFrame. iApply "HΦ"; auto.
Qed.

(** ** Typed loads *)
Lemma wp_load_sc E l m bs v :
  decode_value m bs = Some v →
  {{{ ▷ l ↦b bs }}} Load ScOrd m (Lit $ LitLoc l) @ E
  {{{ RET MLitV v; l ↦b bs }}}.
Proof.
  iIntros (Hdec Φ) ">Hbs HΦ". have Hlen := decode_value_length _ _ _ Hdec.
  iApply wp_lift_atomic_base_step_no_fork; auto.
  iIntros (σ1 stepcnt κ κs n') "[Hσ Ht] !>". heap_split.
  iDestruct (bytes_ctx_lookup with "HB Hbs") as %Hrange.
  have Hrange' := Hrange.
  iSplit. { iPureIntro. eexists _, _, _, _. by eapply LoadScS. }
  iNext; iIntros (e2 σ2 efs Hstep) "credit"; inv_head_step.
  match goal with H : mem_range _ _ _ ?bs' |- _ =>
    have Heq := mem_range_det _ _ _ _ _ _ Hrange' H ltac:(lia) end. subst.
  match goal with H : decode_value _ _ = Some _ |- _ => rewrite Hdec in H; simplify_eq end.
  iMod (time_interp_step with "Ht") as "$". iModIntro. iSplit; [done|].
  iSplitR "HΦ Hbs"; [by iFrame|]. by iApply "HΦ".
Qed.

Lemma wp_load_na E l m bs v :
  decode_value m bs = Some v →
  {{{ ▷ l ↦b bs }}} Load Na1Ord m (Lit $ LitLoc l) @ E
  {{{ RET MLitV v; l ↦b bs }}}.
Proof.
  iIntros (Hdec Φ) ">Hbs HΦ". have Hlen := decode_value_length _ _ _ Hdec.
  iApply wp_lift_base_step; auto.
  iIntros (σ1 stepcnt κ κs n) "[Hσ Ht]". heap_split.
  iMod (bytes_ctx_read_begin with "HB Hbs") as "(%Hrange & HB & Hbs)".
  have Hrange' := Hrange.
  iApply fupd_mask_intro; first set_solver. iIntros "Hclose". iSplit.
  { iPureIntro. eexists _, _, _, _. by eapply LoadNa1S. }
  iNext; iIntros (e2 σ2 efs Hstep); inv_head_step. iMod "Hclose" as "_".
  iMod (time_interp_step with "Ht") as "$". iIntros "credit !>".
  iSplitR "HΦ Hbs".
  { iExists hF. rewrite -Hlen. iFrame. iPureIntro.
    eapply heap_freeable_rel_dom; [|done]. intros ?. by rewrite is_Some_mem_alter. }
  iSplit; last done.
  clear dependent σ1 hF. iApply wp_lift_atomic_base_step_no_fork; auto.
  iIntros (σ1 stepcnt' κ' κs' n') "[Hσ Ht]".
  iMod (time_interp_step with "Ht") as "$". heap_split.
  iMod (bytes_ctx_read_end with "HB Hbs") as "(%Hrange & HB & Hbs)".
  have Hrange' := Hrange.
  iModIntro; iSplit.
  { iPureIntro. eexists _, _, _, _. by eapply LoadNa2S. }
  iNext. iIntros (e2 σ2 efs Hstep) "credit2 !>"; inv_head_step.
  match goal with H : mem_range _ _ _ ?bs' |- _ =>
    have Heq := mem_range_det _ _ _ _ _ _ Hrange' H ltac:(lia) end. subst.
  match goal with H : decode_value _ _ = Some _ |- _ => rewrite Hdec in H; simplify_eq end.
  iSplit; [done|]. iSplitR "HΦ Hbs".
  { iExists hF. rewrite -Hlen. iFrame. iPureIntro.
    eapply heap_freeable_rel_dom; [|done]. intros ?. by rewrite is_Some_mem_alter. }
  by iApply "HΦ".
Qed.

(** ** Typed stores *)
Lemma wp_store_sc E l m bs e v :
  ↑naN ⊆ E → IntoVal e (MLitV v) → val_wf m v → length bs = mty_size m →
  {{{ ▷ l ↦b bs }}} Store ScOrd m (Lit $ LitLoc l) e @ E
  {{{ RET LitV LitPoison; l ↦b encode_value m v }}}.
Proof.
  iIntros (? <- Hwf Hlen Φ) ">Hbs HΦ".
  iApply wp_lift_atomic_base_step_no_fork; auto.
  iIntros (σ1 stepcnt κ κs n') "[Hσ Ht]". heap_split.
  have Hlen' : length (encode_value m v) = length bs by rewrite length_encode_value.
  iMod (bytes_ctx_write _ _ _ _ (encode_value m v) with "HB Hbs") as "(%Hrange & HB & Hbs)"; [done..|].
  have Hrange' := Hrange.
  iModIntro. iSplit. { iPureIntro. eexists _, _, _, _. eapply StoreScS; eauto. }
  iNext; iIntros (e2 σ2 efs Hstep) "credit"; inv_head_step.
  iMod (time_interp_step with "Ht") as "$". iModIntro. iSplit; [done|].
  iSplitR "HΦ Hbs".
  { iExists hF. iFrame. iPureIntro.
    eapply heap_freeable_rel_dom; [|done]. intros ?. simpl.
      by rewrite (is_Some_mem_write _ _ _ _ _ _ Hrange' Hlen'). }
  by iApply "HΦ".
Qed.

Lemma wp_store_na E l m bs e v :
  ↑naN ⊆ E → IntoVal e (MLitV v) → val_wf m v → length bs = mty_size m →
  {{{ ▷ l ↦b bs }}} Store Na1Ord m (Lit $ LitLoc l) e @ E
  {{{ RET LitV LitPoison; l ↦b encode_value m v }}}.
Proof.
  iIntros (? <- Hwf Hlen Φ) ">Hbs HΦ".
  iApply wp_lift_base_step; auto.
  iIntros (σ1 stepcnt κ κs n) "[Hσ Ht]". heap_split.
  iMod (bytes_ctx_write_begin with "HB Hbs") as "(%Hrange & HB & Hbs)"; [done|].
  have Hrange' := Hrange.
  iApply fupd_mask_intro; first set_solver. iIntros "Hclose". iSplit.
  { iPureIntro. eexists _, _, _, _. eapply StoreNa1S; eauto. }
  iNext; iIntros (e2 σ2 efs Hstep); inv_head_step. iMod "Hclose" as "_".
  iMod (time_interp_step with "Ht") as "$". iIntros "credit !>".
  iSplitR "HΦ Hbs".
  { iExists hF. rewrite -Hlen. iFrame. iPureIntro.
    eapply heap_freeable_rel_dom; [|done]. intros ?. by rewrite is_Some_mem_alter. }
  iSplit; last done.
  clear dependent σ1 hF. iApply wp_lift_atomic_base_step_no_fork; auto.
  iIntros (σ1 stepcnt' κ' κs' n') "[Hσ Ht]".
  iMod (time_interp_step with "Ht") as "$". heap_split.
  match goal with H : val_wf m ?w |- _ => rename w into v end.
  have Hlen' : length (encode_value m v) = length bs by rewrite length_encode_value.
  iMod (bytes_ctx_write_end _ _ _ _ (encode_value m v) with "HB Hbs") as "(%Hrange & HB & Hbs)";
    [done..|].
  have Hrange' := Hrange.
  iModIntro; iSplit.
  { iPureIntro. eexists _, _, _, _. eapply StoreNa2S; eauto. }
  iNext. iIntros (e2 σ2 efs Hstep) "credit2 !>"; inv_head_step.
  iSplit; [done|]. iSplitR "HΦ Hbs".
  { iExists hF. iFrame. iPureIntro.
    eapply heap_freeable_rel_dom; [|done]. intros ?. simpl.
      by rewrite (is_Some_mem_write _ _ _ _ _ _ Hrange' Hlen'). }
  by iApply "HΦ".
Qed.

(** ** Byte-level copy *)
Lemma wp_memcopy E l1 l2 bs1 bs2 (n : nat) :
  ↑naN ⊆ E → length bs1 = n → length bs2 = n →
  {{{ ▷ l1 ↦b bs1 ∗ ▷ l2 ↦b bs2 }}}
    MemCopy Na1Ord n (Lit $ LitLoc l1) (Lit $ LitLoc l2) @ E
  {{{ RET LitV LitPoison; l1 ↦b bs2 ∗ l2 ↦b bs2 }}}.
Proof.
  iIntros (? Hlen1 Hlen2 Φ) "[>Hbs1 >Hbs2] HΦ". subst n.
  iApply wp_lift_base_step; auto.
  iIntros (σ1 stepcnt κ κs n') "[Hσ Ht]". heap_split.
  iEval (rewrite heap_mapsto_bytes_st_vec) in "Hbs1".
  iMod (bytes_ctx_lookup_1 with "HB Hbs1") as "(%Hrange1 & HB & Hbs1)"; [done|].
  iEval (rewrite -heap_mapsto_bytes_st_vec) in "Hbs1".
  have Hrange1' := Hrange1.
  iMod (bytes_ctx_read_begin with "HB Hbs2") as "(%Hrange2 & HB & Hbs2)".
  have Hrange2' := Hrange2.
  iMod (bytes_ctx_write_begin with "HB Hbs1") as "(%Hrange1b & HB & Hbs1)"; [done|].
  iApply fupd_mask_intro; first set_solver. iIntros "Hclose". iSplit.
  { iPureIntro. eexists _, _, _, _. eapply MemCopyNa1S; eauto. }
  iNext; iIntros (e2 σ2 efs Hstep); inv_head_step. iMod "Hclose" as "_".
  iMod (time_interp_step with "Ht") as "$". iIntros "credit !>".
  iSplitR "HΦ Hbs1 Hbs2".
  { rewrite Hlen2. iExists hF. iFrame. iPureIntro.
    eapply heap_freeable_rel_dom; [|done]. intros ?. by rewrite !is_Some_mem_alter. }
  iSplit; last done.
  clear dependent σ1 hF. iApply wp_lift_atomic_base_step_no_fork; auto.
  iIntros (σ1 stepcnt' κ' κs' n'') "[Hσ Ht]".
  iMod (time_interp_step with "Ht") as "$". heap_split.
  iMod (bytes_ctx_lookup_1 with "HB Hbs1") as "(%Hrange1 & HB & Hbs1)"; [done|].
  have Hrange1' := Hrange1.
  iMod (bytes_ctx_read_end with "HB Hbs2") as "(%Hrange2 & HB & Hbs2)".
  have Hrange2' := Hrange2.
  have Hlen' : length bs2 = length bs1 by lia.
  iMod (bytes_ctx_write_end _ _ _ _ bs2 with "HB Hbs1") as "(%Hrange1b & HB & Hbs1)"; [done..|].
  iModIntro; iSplit.
  { iPureIntro. eexists _, _, _, _. eapply MemCopyNa2S; eauto. }
  iNext. iIntros (e2 σ2 efs Hstep) "credit2 !>"; inv_head_step.
  match goal with H : mem_range is_reading_S _ l2 ?bs' |- _ =>
    have Heq := mem_range_det _ _ _ _ _ _ Hrange2' H ltac:(lia) end. subst.
  iSplit; [done|]. iSplitR "HΦ Hbs1 Hbs2".
  { rewrite Hlen2. iExists hF. iFrame. iPureIntro.
    eapply heap_freeable_rel_dom; [|done]. intros ?.
    simpl. rewrite is_Some_mem_write'; [by rewrite !is_Some_mem_alter|].
    intros i Hi. rewrite is_Some_mem_alter.
    destruct (mem_range_lookup_1 _ _ _ _ i Hrange1') as (?&?&Hl&_); [lia|]. eexists. exact Hl. }
  iApply "HΦ". iFrame.
Qed.

(** ** Guarded loads and copies

The bytes are only guarded ([G &&{↑naN; d}&&> l ↦b bs], e.g. by the lifetime token of
a shared reference). An atomic load opens the guard around its single step. A
non-atomic load (or copy) deposits [G] in the bank of guarded reads of the byte region
for the duration of the read ([bytes_ctx_read_begin_guarded]); this costs [£d] to look
at the bytes and [£d] that stay with [G] in the bank. *)
Lemma wp_load_sc_guarded E l m bs v G d :
  ↑naN ⊆ E → decode_value m bs = Some v →
  {{{ (G &&{↑naN; d}&&> l ↦b bs) ∗ G ∗ £d }}} Load ScOrd m (Lit $ LitLoc l) @ E
  {{{ RET MLitV v; G }}}.
Proof.
  iIntros (? Hdec Φ) "(#Guard & G & £) HΦ". have Hlen := decode_value_length _ _ _ Hdec.
  iApply wp_lift_atomic_base_step_no_fork; auto.
  iIntros (σ1 stepcnt κ κs n') "[Hσ Ht]". heap_split.
  iMod (guards_open_later with "Guard G") as "Open"; [done|].
  iMod (lc_fupd_elim_laterN with "£ Open") as ">[Hbs Back]".
  iDestruct (bytes_ctx_lookup with "HB Hbs") as %Hrange.
  iMod ("Back" with "Hbs") as "G".
  have Hrange' := Hrange.
  iModIntro. iSplit. { iPureIntro. eexists _, _, _, _. by eapply LoadScS. }
  iNext; iIntros (e2 σ2 efs Hstep) "credit"; inv_head_step.
  match goal with H : mem_range _ _ _ ?bs' |- _ =>
    have Heq := mem_range_det _ _ _ _ _ _ Hrange' H ltac:(lia) end. subst.
  match goal with H : decode_value _ _ = Some _ |- _ => rewrite Hdec in H; simplify_eq end.
  iMod (time_interp_step with "Ht") as "$". iModIntro. iSplit; [done|].
  iSplitR "HΦ G"; [by iFrame|]. by iApply "HΦ".
Qed.

(** The general form: [G] guards some [P] that contains a fraction of bytes [bs] with
    [Ψ bs], which all decode to [v]. *)
Lemma wp_load_na_guarded_gen E l m v G P (Ψ : list abyte → Prop) d :
  ↑naN ⊆ E → (∀ bs, Ψ bs → decode_value m bs = Some v) →
  {{{ (G &&{↑naN; d}&&> P) ∗ □ (P -∗ ∃ bs, ⌜Ψ bs⌝ ∗ l ↦b bs ∗ (l ↦b bs -∗ P)) ∗
      G ∗ £(2*d) }}}
    Load Na1Ord m (Lit $ LitLoc l) @ E
  {{{ RET MLitV v; G }}}.
Proof.
  iIntros (? HΨ Φ) "(#Guard & #HP & G & £) HΦ".
  iApply wp_lift_base_step; auto.
  iIntros (σ1 stepcnt κ κs n) "[Hσ Ht]". heap_split.
  iMod (bytes_ctx_read_begin_guarded _ _ _ Ψ (mty_size m) with "£ Guard HP G HB")
    as (i bs) "(%HΨbs & %Hrange & HB & Tok)";
    [done|intros ??; by eapply decode_value_length, HΨ|].
  have Hdec := HΨ _ HΨbs. have Hlen := decode_value_length _ _ _ Hdec.
  have Hrange' := Hrange.
  iApply fupd_mask_intro; first set_solver. iIntros "Hclose". iSplit.
  { iPureIntro. eexists _, _, _, _. by eapply LoadNa1S. }
  iNext; iIntros (e2 σ2 efs Hstep); inv_head_step. iMod "Hclose" as "_".
  iMod (time_interp_step with "Ht") as "$". iIntros "credit !>".
  iSplitR "HΦ Tok credit".
  { iExists hF. rewrite -Hlen. iFrame. iPureIntro.
    eapply heap_freeable_rel_dom; [|done]. intros ?. by rewrite is_Some_mem_alter. }
  iSplit; last done.
  clear dependent σ1 hF. iApply wp_lift_atomic_base_step_no_fork; auto.
  iIntros (σ1 stepcnt' κ' κs' n') "[Hσ Ht]".
  iMod (time_interp_step with "Ht") as "$". heap_split.
  iMod (bytes_ctx_read_end_guarded with "HB Tok") as "(%Hrange & HB & G)".
  iMod (lc_fupd_elim_later with "credit G") as "G".
  have Hrange' := Hrange.
  iModIntro; iSplit.
  { iPureIntro. eexists _, _, _, _. by eapply LoadNa2S. }
  iNext. iIntros (e2 σ2 efs Hstep) "credit2 !>"; inv_head_step.
  match goal with H : mem_range _ _ _ ?bs' |- _ =>
    have Heq := mem_range_det _ _ _ _ _ _ Hrange' H ltac:(lia) end. subst.
  match goal with H : decode_value _ _ = Some _ |- _ => rewrite Hdec in H; simplify_eq end.
  iSplit; [done|]. iSplitR "HΦ G".
  { iExists hF. rewrite -Hlen. iFrame. iPureIntro.
    eapply heap_freeable_rel_dom; [|done]. intros ?. by rewrite is_Some_mem_alter. }
  by iApply "HΦ".
Qed.

Lemma wp_load_na_guarded E l m bs v G d :
  ↑naN ⊆ E → decode_value m bs = Some v →
  {{{ (G &&{↑naN; d}&&> l ↦b bs) ∗ G ∗ £(2*d) }}} Load Na1Ord m (Lit $ LitLoc l) @ E
  {{{ RET MLitV v; G }}}.
Proof.
  iIntros (? Hdec Φ) "(#Guard & G & £) HΦ".
  iApply (wp_load_na_guarded_gen _ _ _ _ _ _ (.= bs) with "[$Guard $G $£]"); [done|by intros ? ->| |done].
  iIntros "!> Pt". iExists bs. iFrame. iSplit; [done|]. by iIntros "$".
Qed.

Lemma wp_memcopy_guarded_gen E l1 l2 bs1 (n : nat) G P (Ψ : list abyte → Prop) d :
  ↑naN ⊆ E → length bs1 = n → (∀ bs, Ψ bs → length bs = n) →
  {{{ ▷ l1 ↦b bs1 ∗ (G &&{↑naN; d}&&> P) ∗
      □ (P -∗ ∃ bs, ⌜Ψ bs⌝ ∗ l2 ↦b bs ∗ (l2 ↦b bs -∗ P)) ∗ G ∗ £(2*d) }}}
    MemCopy Na1Ord n (Lit $ LitLoc l1) (Lit $ LitLoc l2) @ E
  {{{ bs2, RET LitV LitPoison; ⌜Ψ bs2⌝ ∗ l1 ↦b bs2 ∗ G }}}.
Proof.
  iIntros (? <- HΨ Φ) "(>Hbs1 & #Guard & #HP & G & £) HΦ".
  iApply wp_lift_base_step; auto.
  iIntros (σ1 stepcnt κ κs n') "[Hσ Ht]". heap_split.
  iEval (rewrite heap_mapsto_bytes_st_vec) in "Hbs1".
  iMod (bytes_ctx_lookup_1 with "HB Hbs1") as "(%Hrange1 & HB & Hbs1)"; [done|].
  iEval (rewrite -heap_mapsto_bytes_st_vec) in "Hbs1".
  have Hrange1' := Hrange1.
  iMod (bytes_ctx_read_begin_guarded _ _ _ Ψ (length bs1) with "£ Guard HP G HB")
    as (i bs2) "(%HΨbs & %Hrange2 & HB & Tok)"; [done..|].
  have Hlen2 : length bs2 = length bs1 := HΨ _ HΨbs.
  have Hrange2' := Hrange2.
  iMod (bytes_ctx_write_begin with "HB Hbs1") as "(%Hrange1b & HB & Hbs1)"; [done|].
  iApply fupd_mask_intro; first set_solver. iIntros "Hclose". iSplit.
  { iPureIntro. eexists _, _, _, _. eapply MemCopyNa1S; eauto. }
  iNext; iIntros (e2 σ2 efs Hstep); inv_head_step. iMod "Hclose" as "_".
  iMod (time_interp_step with "Ht") as "$". iIntros "credit !>".
  iSplitR "HΦ Hbs1 Tok credit".
  { iExists hF. iFrame. iPureIntro.
    eapply heap_freeable_rel_dom; [|done]. intros ?. by rewrite !is_Some_mem_alter. }
  iSplit; last done.
  clear dependent σ1 hF. iApply wp_lift_atomic_base_step_no_fork; auto.
  iIntros (σ1 stepcnt' κ' κs' n'') "[Hσ Ht]".
  iMod (time_interp_step with "Ht") as "$". heap_split.
  iMod (bytes_ctx_lookup_1 with "HB Hbs1") as "(%Hrange1 & HB & Hbs1)"; [done|].
  have Hrange1' := Hrange1.
  iMod (bytes_ctx_read_end_guarded with "HB Tok") as "(%Hrange2 & HB & G)".
  iMod (lc_fupd_elim_later with "credit G") as "G".
  have Hrange2' := Hrange2.
  have Hlen' : length bs2 = length bs1 by lia.
  iMod (bytes_ctx_write_end _ _ _ _ bs2 with "HB Hbs1") as "(%Hrange1b & HB & Hbs1)"; [done..|].
  iModIntro; iSplit.
  { iPureIntro. eexists _, _, _, _. eapply MemCopyNa2S; eauto. }
  iNext. iIntros (e2 σ2 efs Hstep) "credit2 !>"; inv_head_step.
  match goal with H : mem_range is_reading_S _ l2 ?bs' |- _ =>
    have Heq := mem_range_det _ _ _ _ _ _ Hrange2' H ltac:(lia) end. subst.
  iSplit; [done|]. iSplitR "HΦ Hbs1 G".
  { iExists hF. rewrite -Hlen'. iFrame. iPureIntro.
    eapply heap_freeable_rel_dom; [|done]. intros ?.
    simpl. rewrite is_Some_mem_write'; [by rewrite !is_Some_mem_alter|].
    intros i' Hi. rewrite is_Some_mem_alter.
    destruct (mem_range_lookup_1 _ _ _ _ i' Hrange1') as (?&?&Hl&_); [lia|]. eexists. exact Hl. }
  iApply "HΦ". by iFrame.
Qed.

Lemma wp_memcopy_guarded E l1 l2 bs1 bs2 (n : nat) G d :
  ↑naN ⊆ E → length bs1 = n → length bs2 = n →
  {{{ ▷ l1 ↦b bs1 ∗ (G &&{↑naN; d}&&> l2 ↦b bs2) ∗ G ∗ £(2*d) }}}
    MemCopy Na1Ord n (Lit $ LitLoc l1) (Lit $ LitLoc l2) @ E
  {{{ RET LitV LitPoison; l1 ↦b bs2 ∗ G }}}.
Proof.
  iIntros (? Hlen1 Hlen2 Φ) "(Hbs1 & #Guard & G & £) HΦ".
  iApply (wp_memcopy_guarded_gen _ _ _ _ _ _ _ (.= bs2) with "[$Hbs1 $Guard $G $£]");
    [done|done|by intros ? ->| |].
  { iIntros "!> Pt". iExists bs2. iFrame. iSplit; [done|]. by iIntros "$". }
  iIntros "!>" (bs) "(-> & ? & ?)". iApply "HΦ". iFrame.
Qed.

(** ** Typed compare-and-exchange

[MCAS m l e1 e2] compares the value decoded at [m] from the bytes at [l] with [e1], by
equality of [Value]s (so padding is not compared), and if they are equal writes the
encoding of [e2]. It is atomic. *)
Lemma wp_mcas E l m bs v e1 v1 e2 v2 :
  ↑naN ⊆ E → IntoVal e1 (MLitV v1) → IntoVal e2 (MLitV v2) → val_wf m v2 →
  decode_value m bs = Some v →
  {{{ ▷ l ↦b bs }}} MCAS m (Lit $ LitLoc l) e1 e2 @ E
  {{{ b, RET MLitV (VBool b);
      (⌜b = true ∧ v = v1⌝ ∗ l ↦b encode_value m v2) ∨ (⌜b = false ∧ v ≠ v1⌝ ∗ l ↦b bs) }}}.
Proof.
  iIntros (? <- <- Hwf Hdec Φ) ">Hbs HΦ". have Hlen := decode_value_length _ _ _ Hdec.
  iApply wp_lift_atomic_base_step_no_fork; auto.
  iIntros (σ1 stepcnt κ κs n') "[Hσ Ht]". heap_split.
  destruct (decide (v = v1)) as [<-|Hne].
  - have Hlen' : length (encode_value m v2) = length bs by rewrite length_encode_value.
    iMod (bytes_ctx_write _ _ _ _ (encode_value m v2) with "HB Hbs") as "(%Hrange & HB & Hbs)";
      [done..|].
    have Hrange' := Hrange.
    iModIntro. iSplit.
    { iPureIntro. eexists _, _, _, _. eapply MCasSucS; [by rewrite to_of_val|by rewrite to_of_val|done|
        by eapply mem_range_impl; [|done]|lia|done]. }
    iNext; iIntros (e2' σ2 efs Hstep) "credit"; inv_head_step.
    + match goal with H : mem_range is_reading _ _ ?bs' |- _ =>
        have Heq := mem_range_det _ _ _ _ _ _ Hrange' H ltac:(lia) end. subst.
      match goal with H : decode_value _ _ = Some _ |- _ => rewrite Hdec in H end. congruence.
    + iMod (time_interp_step with "Ht") as "$". iModIntro. iSplit; [done|].
      iSplitR "HΦ Hbs".
      { iExists hF. iFrame. iPureIntro.
        eapply heap_freeable_rel_dom; [|done]. intros ?. simpl.
          by rewrite (is_Some_mem_write _ _ _ _ _ _ Hrange' Hlen'). }
      iApply "HΦ". iLeft. by iFrame.
    + exfalso. match goal with H : ¬ mem_range _ _ _ ?bs' |- _ => apply H end.
      match goal with H : mem_range is_reading _ _ ?bs' |- _ =>
        have Heq := mem_range_det _ _ _ _ _ _ Hrange' H ltac:(lia) end. by subst.
  - iDestruct (bytes_ctx_lookup with "HB Hbs") as %Hrange.
    have Hrange' := Hrange.
    iModIntro. iSplit.
    { iPureIntro. eexists _, _, _, _. eapply MCasFailS; by rewrite ?to_of_val. }
    iNext; iIntros (e2' σ2 efs Hstep) "credit"; inv_head_step;
      match goal with H : mem_range _ _ _ ?bs' |- _ =>
        have Heq := mem_range_det _ _ _ _ _ _ Hrange' H ltac:(lia) end; subst;
      match goal with H : decode_value _ _ = Some _ |- _ => rewrite Hdec in H; injection H as -> end;
      try done.
    iMod (time_interp_step with "Ht") as "$". iModIntro. iSplit; [done|].
    iSplitR "HΦ Hbs"; [by iFrame|]. iApply "HΦ". iRight. by iFrame.
Qed.

End lifting.
