Require Import guarding.internal.na_invariants_fork.
From guarding Require Import guard.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Export weakestpre.
From iris.program_logic Require Import ectx_lifting.
From lrust.lang Require Export lang heap heap_cells time.
From lrust.lang Require Import tactics.
From lrust.util Require Import update non_atomic_cell_map atomic_lock_counter.
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

(** Heap *)
Lemma wp_alloc E (n : Z) :
  0 < n →
  {{{ True }}} Alloc (Lit $ LitInt n) @ E
  {{{ l (sz: nat), RET LitV $ LitLoc l; ⌜n = sz⌝ ∗ †l…sz ∗ l ↦∗ repeat (LitV LitPoison) sz }}}.
Proof.
  iIntros (? Φ) "_ HΦ". iApply wp_lift_atomic_base_step_no_fork; auto.
  iIntros (σ1 stepcnt κ κs n') "[Hσ Ht] !>"; iSplit; first by auto.
  iNext; iIntros (v2 σ2 efs Hstep); inv_head_step.
  iMod (heap_alloc with "Hσ") as "[$ Hl]"; [done..|].
  iMod (time_interp_step with "Ht") as "$". iIntros "credit".
  iModIntro; iSplit=> //. iApply ("HΦ" $! _ (Z.to_nat n)). auto with lia iFrame.
Qed.

Lemma wp_free E (n:Z) l vl :
  ↑naN ⊆ E →
  n = length vl →
  {{{ ▷ l ↦∗ vl ∗ ▷ †l…(length vl) }}}
    Free (Lit $ LitInt n) (Lit $ LitLoc l) @ E
  {{{ RET LitV LitPoison; True }}}.
Proof.
  iIntros (Hmask ? Φ) "[>Hmt >Hf] HΦ". iApply wp_lift_atomic_base_step_no_fork; auto.
  iIntros (σ1 stepcnt κ κs n') "[Hσ Ht]".
  iMod (heap_free _ _ _ n with "Hσ Hmt Hf") as "(% & % & Hσ)"=>//.
  iMod (time_interp_step with "Ht") as "$".
  iModIntro; iSplit; first by auto.
  iNext; iIntros (v2 σ2 efs Hstep); inv_head_step. iIntros "credit".
  iModIntro; iSplit=> //. iFrame. iApply "HΦ"; auto.
Qed.

Lemma wp_read_sc_guarded_cells E l c v d G :
  ↑naN ⊆ E →
  {{{ (G &&{↑naN; d}&&> l ↦[^ c] v) ∗ G ∗ £(d) }}} Read ScOrd (Lit $ LitLoc l) @ E {{{ RET v; G }}}.
Proof.
  iIntros (Hmask Φ) "[#Gv [G £]] HΦ". iApply wp_lift_base_step; auto.
  iIntros (σ1 stepcnt κ κs n) "[Hσ Ht]". iDestruct "Hσ" as (hF) "(Hσ & HhF & %REL & ato)".
  iMod (heap_atomic_read with "£ [Gv] G Hσ") as (n0) "[%Heq [rim Hσ]]". { trivial. } { rewrite /heap_mapsto_cells_fancy. unfold fv2sum. iFrame "Gv". }
  iApply fupd_mask_intro; first set_solver. iIntros "Hclose". iSplit; first by eauto.
  iNext; iIntros (e2 σ2 efs Hstep); inv_head_step. iMod "Hclose" as "_".
  iMod (time_interp_step with "Ht") as "$". iIntros "credit !>". iFrame.
  iSplit. { iPureIntro. eauto using heap_freeable_rel_stable. }
  iSplit; last done.
  (* clear dependent σ1 n. *)
  iApply wp_value.
  iApply ("HΦ" with "rim").
Qed.

Lemma wp_read_sc E l v :
  ↑naN ⊆ E →
  {{{ ▷ l ↦ v }}} Read ScOrd (Lit $ LitLoc l) @ E
  {{{ RET v; l ↦ v }}}.
Proof.
  iIntros (Hmask Φ) ">pt ToΦ".
  iMod lc_zero as "£0".
  iApply (wp_read_sc_guarded_cells E l [] v 0 with "[pt £0]"); trivial.
  iFrame.
  rewrite /heap_mapsto_cells_fancy /heap_mapsto /=.
  iApply guards_refl.
Qed.

Lemma wp_read_na_guarded_cells E l c G v d :
  ↑naN ⊆ E →
  {{{ (G &&{↑naN; d}&&> (l ↦[^ c] v)) ∗ G ∗ £(3*d) }}} Read Na1Ord (Lit $ LitLoc l) @ E
  {{{ RET v; G }}}.
Proof.
  iIntros (Hmask Φ) "[#Gv [G £]] HΦ". iApply wp_lift_base_step; auto.
  iIntros (σ1 stepcnt κ κs n) "[Hσ Ht]". iDestruct "Hσ" as (hF) "(Hσ & HhF & %REL & ato)".
  iMod (heap_na_read_begin with "£ [Gv] G Hσ") as (n0) "[%Heq [rim Hσ]]". { trivial. } { rewrite /heap_mapsto_cells_fancy. unfold fv2sum. iFrame "Gv". } replace (n0 + 1)%nat with (S n0) by lia.
  iApply fupd_mask_intro; first set_solver. iIntros "Hclose". iSplit. 
    { iExists _, _, _, _. iPureIntro. apply ReadNa1S. apply Heq. }
  iNext; iIntros (e2 σ2 efs Hstep); inv_head_step. iMod "Hclose" as "_".
  iMod (time_interp_step with "Ht") as "$". iIntros "credit !>". iFrame.
  iSplit. { iPureIntro. eauto using heap_freeable_rel_stable. }
  iSplit; last done.
  clear dependent σ1 n. iApply wp_lift_atomic_base_step_no_fork; auto.
  iIntros (σ1 stepcnt' κ' κs' n') "[Hσ Ht]".
  iMod (time_interp_step with "Ht") as "$".
  iDestruct "Hσ" as (hF') "(Hσ & HhF & %REL & ato)".
  iDestruct (heap_na_read_end with "rim Hσ") as "A". { apply Hmask. }
  iMod (lc_fupd_elim_later with "credit A") as "A". iMod "A" as (n) "([%H1 %H2] & G & Hσ)".
  destruct n as [|n]; first by lia. replace (S n - 1)%nat with n by lia.
  iModIntro; iSplit.
    { iExists _, _, _, _. iPureIntro. apply ReadNa2S. eauto. }
  iNext. iIntros (e2 σ2 efs Hstep) "credit2 !>"; inv_head_step.
  iFrame.
  iSplit; [done|].
  iSplit. { iPureIntro. eauto using heap_freeable_rel_stable. }
  iApply "HΦ". iFrame "G".
Qed.

(* Heap-Read *)
Lemma wp_read_na_guarded_cells_0 E l c G v :
  ↑naN ⊆ E →
  {{{ (G &&{↑naN}&&> (l ↦[^ c] v)) ∗ G }}} Read Na1Ord (Lit $ LitLoc l) @ E
  {{{ RET v; G }}}.
Proof.
  iIntros (Hmask 𝛷) "[g G]". iMod (lc_zero) as "£0".
  iApply wp_read_na_guarded_cells; first trivial. iFrame "g G". done.
Qed.

Lemma wp_read_na E l v :
  ↑naN ⊆ E →
  {{{ ▷ l ↦ v }}} Read Na1Ord (Lit $ LitLoc l) @ E
  {{{ RET v; l ↦ v }}}.
Proof.
  iIntros (Hmask Φ) ">pt ToΦ".
  iMod lc_zero as "£0".
  iApply (wp_read_na_guarded_cells E l [] (l ↦ v)%I v 0 with "[pt £0]"); trivial.
  iFrame. iApply guards_refl.
Qed.

Lemma wp_read_na_guarded_cells_singleton E l c G v d :
  ↑naN ⊆ E →
  {{{ (G &&{↑naN; d}&&> (l ↦[^ c]∗ [v])) ∗ G ∗ £(3*d) }}} Read Na1Ord (Lit $ LitLoc l) @ E
  {{{ RET v; G }}}.
Proof.
  case: c=> >; last first.
  { setoid_rewrite guards_weaken_rhs_sep_l. exact: wp_read_na_guarded_cells. }
  iIntros (??) "(gd & G & £ & _) _".
  iAssert (|={E}=> False)%I with "[gd G £]" as ">[]".
  iMod (guards_open_later with "gd G") as "to"=>//.
  iMod (lc_fupd_elim_laterN with "£ to") as ">[[] _]".
Qed.

Lemma wp_read_na_guarded E l G v d :
  ↑naN ⊆ E →
  {{{ (G &&{↑naN; d}&&> (l ↦ v)) ∗ G ∗ £(3*d) }}} Read Na1Ord (Lit $ LitLoc l) @ E
  {{{ RET v; G }}}.
Proof.
  intros Hmask. have Ha := wp_read_na_guarded_cells_singleton E l [[]] G v d. simpl in Ha.
  unfold heap_mapsto_cells_val_vec in Ha. simpl in Ha. unfold heap_mapsto_fancy_vec in Ha.
  simpl in Ha. unfold heap_mapsto. setoid_rewrite bi.sep_True in Ha; last by apply _.
  apply Ha. apply Hmask.
Qed.


(* The extra +1 in £ is problematic*)
Lemma wp_write_sc_guarded E l c e v v' d G :
  ↑naN ⊆ E →
  IntoVal e v →
  {{{ (G &&{↑naN; d}&&> ((l,c) #↦_)) ∗ G ∗ (l,c) #↦ v' ∗ £(3*d+1) }}} Write ScOrd (Lit $ LitLoc l) e @ E
  {{{ RET LitV LitPoison; (l,c) #↦ v ∗ G }}}.
Proof.
  iIntros (Hmask <- Φ) "[#guards [G [Hv £]]] HΦ".
  iApply wp_lift_base_step; auto. iIntros (σ1 stepcnt κ κs n) "[Hσ Ht]".
  iMod (heap_write with "£ Hσ guards G Hv") as "(% & Hσ & G & Hv')"; first by trivial.
  iApply (fupd_mask_intro _ ∅); first set_solver. iIntros "Hclose".
    iSplit. { iPureIntro. eexists _, _, _, _. eapply WriteScS; eauto. }
  iNext; iIntros (e2 σ2 efs Hstep) "credit"; inv_head_step. iMod "Hclose" as "_".
  iMod (time_interp_step with "Ht") as "$". iModIntro. iFrame "Hσ". iSplit; last done.
  clear dependent σ1.
  iApply wp_value.
  iApply ("HΦ" with "[$Hv' $G]").
Qed.

(* The extra £1 is the problem *)
Lemma wp_write_sc E l e v v' :
  ↑naN ⊆ E →
  IntoVal e v →
  {{{ ▷ l ↦ v' ∗ £1 }}} Write ScOrd (Lit $ LitLoc l) e @ E
  {{{ RET LitV LitPoison; l ↦ v }}}.
Proof.
  iIntros (Hmask IntoVal Φ) "[>pt £] ToΦ".
  (* iMod lc_zero as "£0". *)
  iApply (wp_write_sc_guarded E l [] e v v' 0 (True)%I with "[pt £]"); trivial.
   - iFrame. rewrite heap_cloc1_mapsto_val. iFrame. iApply guards_true.
   - iNext. iIntros "[A B]". iApply "ToΦ". rewrite heap_cloc1_mapsto_val. iFrame.
Qed. 

Lemma wp_write_na_guarded E l c e v v' d G :
  ↑naN ⊆ E →
  IntoVal e v →
  {{{ (G &&{↑naN; d}&&> ((l,c) #↦_)) ∗ G ∗ (l,c) #↦ v' ∗ £(3*d) }}} Write Na1Ord (Lit $ LitLoc l) e @ E
  {{{ RET LitV LitPoison; (l,c) #↦ v ∗ G }}}.
Proof.
  iIntros (Hmask <- Φ) "[#guards [G [Hv £]]] HΦ".
  iApply wp_lift_base_step; auto. iIntros (σ1 stepcnt κ κs n) "[Hσ Ht]".
  iMod (heap_write_na with "£ Hσ guards G Hv") as "(% & Hσ & Hσclose)"; first by trivial.
  iApply (fupd_mask_intro _ ∅); first set_solver. iIntros "Hclose". iSplit.
    { iExists _, _, _, _. iPureIntro. eapply WriteNa1S; done. }
  iNext; iIntros (e2 σ2 efs Hstep) "credit"; inv_head_step. iMod "Hclose" as "_".
  iMod (time_interp_step with "Ht") as "$". iModIntro. iFrame "Hσ". iSplit; last done.
  clear dependent σ1. iApply wp_lift_atomic_base_step_no_fork; auto.
  iIntros (σ1 stepcnt' κ' κs' n') "[Hσ Ht]".
  iMod ("Hσclose" with "credit Hσ") as "(%Hw & Hσ & G & Hv)". destruct Hw as [v0 Hw].
  iMod (time_interp_step with "Ht") as "$". iModIntro; iSplit.
    { iExists _, _, _, _. iPureIntro. eapply WriteNa2S; done. }
  iNext; iIntros (e2 σ2 efs Hstep) "credit2 !>"; inv_head_step.
  iFrame "Hσ". iSplit; [done|]. iApply "HΦ". iFrame.
Qed.

Lemma wp_write_na_guarded_0 E l cells e v v' d G :
  ↑naN ⊆ E →
  IntoVal e v →
  {{{ (G &&{↑naN; d}&&> ((l,cells) #↦_)) ∗ G ∗ (l,cells) #↦ v' ∗ £(3*d) }}} Write Na1Ord (Lit $ LitLoc l) e @ E
  {{{ RET LitV LitPoison; (l,cells) #↦ v ∗ G }}}.
Proof.
  iIntros (Hmask Hval 𝛷) "[g G]". iMod (lc_zero) as "£0".
  iApply wp_write_na_guarded; first trivial. iFrame "g G".
Qed.

Local Open Scope nat_scope.

Lemma wp_write_na_guarded_more_credits E l c e v v' d G d' :
  ↑naN ∪ ↑timeN ⊆ E →
  IntoVal e v →
  time_ctx -∗
  {{{ (G &&{↑naN; d}&&> ((l,c) #↦_)) ∗ G ∗ (l,c) #↦ v' ∗ £(3*d) ∗ ⧖(d') }}} Write Na1Ord (Lit $ LitLoc l) e @ E
  {{{ RET LitV LitPoison; (l,c) #↦ v ∗ G ∗ £(6*d') }}}.
Proof.
  iIntros (Hmask <-) "#TIME". iIntros (Φ). iModIntro. iIntros "[#guards [G [Hv [£ ⧖]]]] HΦ".
  rewrite !wp_unfold /wp_pre /=. iIntros (σ1 stepcnt κ κs n) "[Hσ Ht]".
  iMod (heap_write_na with "£ Hσ guards G Hv") as "(% & Hσ & Hσclose)"; first by set_solver.
  iMod cumulative_time_receipt_0 as "⧗0".
  iMod (time_receipt_le' with "TIME Ht ⧖ ⧗0") as "[%Htimebound [Ht ⧗0]]"; first by set_solver.
  iApply (fupd_mask_intro _ ∅); first set_solver. iIntros "Hclose". iSplit.
    { iPureIntro. apply base_prim_reducible. eexists _, _, _, _. eapply WriteNa1S; done. }
  iIntros (e2 σ2 efs Hstep) "credit"; inv_head_step. iModIntro. iNext. iModIntro.
  iApply (step_fupdN_intro); first by set_solver. iNext. iMod "Hclose" as "_".
  assert (base_step (Write Na1Ord (Lit (LitLoc l)) (of_val v)) σ1 κ e2 σ2 efs) as Hbasestep.
    { apply base_reducible_prim_step; trivial. eexists _, _, _, _. eapply WriteNa1S; eauto. }
  inversion Hbasestep. rewrite H in H8. inversion H8.
  iMod (time_interp_step with "Ht") as "$". iModIntro. iFrame "Hσ". iSplit; last done.
  clear dependent σ1. iApply wp_lift_atomic_base_step_no_fork; auto.
  iIntros (σ1 stepcnt' κ' κs' n') "[Hσ Ht]".
  iDestruct "credit" as "[£1 £]".
  iMod ("Hσclose" with "£1 Hσ") as "(%Hw & Hσ & G & Hv)". destruct Hw as [v1 Hw].
  iMod (time_interp_step with "Ht") as "$". iModIntro; iSplit.
    { iExists _, _, _, _. iPureIntro. eapply WriteNa2S; done. }
  iNext; iIntros (e3 σ3 efs3 Hstep3) "credit2 !>"; inv_head_step.
  iFrame "Hσ". iSplit; [done|]. iApply "HΦ". iFrame.
  iApply (lc_weaken with "£").
    - rewrite Nat.add_1_r.
      cbn [sum_advance_credits].
      replace (d' + (d' + (d' + (d' + (d' + (d' + 0)))))) with (2 * (2 * d' + d'))%nat by lia.
      replace (2 ^ stepcnt + (2 ^ stepcnt + 0) + (2 ^ stepcnt + (2 ^ stepcnt + 0) + 0)) with (2 ^ (S (S stepcnt))) in Htimebound.
      2: { cbn [Nat.pow]. lia. }
      trans (2 * (2 * 2 ^ S (S stepcnt) + 2 ^ S (S stepcnt))); try lia.
      cbn [Nat.pow].
      trans (2 * (2 * 2 ^ stepcnt) * advance_credits (2 * (2 * 2 ^ stepcnt))); try lia.
      rewrite /advance_credits.
      cbn [Nat.pow].
      nia.
Qed.
  
Lemma wp_write_na E l e v v' :
  ↑naN ⊆ E →
  IntoVal e v →
  {{{ ▷ l ↦ v' }}} Write Na1Ord (Lit $ LitLoc l) e @ E
  {{{ RET LitV LitPoison; l ↦ v }}}.
Proof.
  iIntros (Hmask IntoVal Φ) ">pt ToΦ".
  iMod lc_zero as "£0".
  iApply (wp_write_na_guarded E l [] e v v' 0 (True)%I with "[pt £0]"); trivial.
   - iFrame. rewrite heap_cloc1_mapsto_val. iFrame. iApply guards_true.
   - iNext. iIntros "[A B]". iApply "ToΦ". rewrite heap_cloc1_mapsto_val. iFrame.
Qed.

(* Heap-Move-Cell *)
(*
In practice, you'll usually want to use one of the "untether" lemmas directly, since these
are more flexible because they let you separate the logical step of moving the cell from
the physical steps of moving data. The proof here illustrates the concept.
Also, this matches the special case presented in the paper.
*)
Lemma wp_cell_move_na E l l' cell v' :
  ↑naN ⊆ E →
  {{{ l ↦! (FCell cell) ∗ l' ↦ v' }}} Write Na1Ord (Lit $ LitLoc l') (Read Na1Ord (Lit $ LitLoc l)) @ E
  {{{ RET LitV LitPoison; ∃ v, l ↦ v ∗ l' ↦! (FCell cell) }}}.
Proof.
  intros Hmask. iIntros (𝛷) "[pt pt'] post". iApply wp_fupd.
  (* untether the cell from the location, get a concrete value v *)
  iMod (mapsto_vec_untether1 (l, []) (FCell cell) with "pt") as (v) "[pt [retether ?]]".
  (* copy the concrete value v *)
  change (Write Na1Ord (Lit (LitLoc l')) (Read Na1Ord (Lit (LitLoc l))))
      with (fill_item (WriteRCtx Na1Ord (LitV (LitLoc l'))) (Read Na1Ord (Lit (LitLoc l)))).
  iApply wp_bind.
  iApply (wp_read_na with "pt"); first trivial. iModIntro. iIntros "pt".
  iApply (wp_write_na _ _ _ v with "pt'"); [trivial|done|].
  (* retether the cell to the new location *)
  iModIntro. iIntros "pt'".
  iMod ("retether" $! (l', []) with "[pt']") as "[? pt']". { iSplitR. { done. } 
    unfold heap_complete_mapsto_fancy, split_at_last, rev. simpl. 
    unfold heap_mapsto. iFrame "pt'".
  }
  iModIntro. iApply "post". iFrame.
Qed.

Lemma wp_cas_int_fail_guarded  E l c z1 e2 lit2 zl d G :
  ↑naN ⊆ E →
  IntoVal e2 (LitV lit2) → z1 ≠ zl →
  {{{ (G &&{↑naN; d}&&> ((l,c) #↦_)) ∗ G ∗ (l,c) #↦ LitV (LitInt zl) ∗ £(3 * d + 1) }}}
    CAS (Lit $ LitLoc l) (Lit $ LitInt z1) e2 @ E
    {{{ RET LitV $ LitInt 0; G ∗ (l,c) #↦ LitV (LitInt zl) }}}.
Proof.
  iIntros (Hmask <- ? Φ) "[#guards [G [Hv £]]] HΦ".
  iApply wp_lift_base_step; auto. iIntros (σ1 stepcnt κ κs n) "[Hσ Ht]".
  iMod (heap_write _ _ _ (LitV $ LitInt zl) with "£ Hσ guards G Hv") as "(% & Hσ & G & Hv')"; first by trivial.
  iApply (fupd_mask_intro _ ∅); first set_solver. iIntros "Hclose". iSplit; first by eauto.
  iNext; iIntros (e2 σ2 efs Hstep) "credit"; inv_head_step.
  - iMod "Hclose" as "_".
    iMod (time_interp_step with "Ht") as "$". iModIntro.
    rewrite insert_id => //.
    iFrame "Hσ". iSplit; last done.
    iApply wp_value.
    iApply ("HΦ" with "[$Hv' $G]").
  - rename select (lit_eq _ _ _) into Hfalse; inversion Hfalse; subst => //.
Qed.

Lemma wp_cas_int_fail E l z1 e2 lit2 zl :
  ↑naN ⊆ E →
  IntoVal e2 (LitV lit2) → z1 ≠ zl →
  {{{ ▷ l ↦ LitV (LitInt zl) ∗ £1 }}}
    CAS (Lit $ LitLoc l) (Lit $ LitInt z1) e2 @ E
  {{{ RET LitV $ LitInt 0; l ↦ LitV (LitInt zl) }}}.
Proof.
  iIntros (Hmask IntoVal ? Φ) "[>pt £] ToΦ".
  (* iMod lc_zero as "£0". *)
  iApply (wp_cas_int_fail_guarded E l [] z1 e2 lit2 zl 0 True with "[pt £]"); trivial.
  -  rewrite heap_cloc1_mapsto_val. iFrame. iApply guards_true.
  - iNext. iIntros "[_ B]". iApply "ToΦ". rewrite heap_cloc1_mapsto_val. iFrame.
Qed.

Lemma wp_cas_suc_guarded  E l c lit1 e2 lit2 d G :
  ↑naN ⊆ E →
  IntoVal e2 (LitV lit2) → lit1 ≠ LitPoison →
  {{{ (G &&{↑naN; d}&&> ((l,c) #↦_)) ∗ G ∗ (l,c) #↦ LitV lit1 ∗ £(3 * d + 1) }}}
    CAS (Lit $ LitLoc l) (Lit lit1) e2 @ E
  {{{ RET LitV $ LitInt 1; G ∗ (l,c) #↦ LitV lit2 }}}.
Proof.
  iIntros (Hmask <- ? Φ) "[#guards [G [Hv £]]] HΦ".
  iApply wp_lift_base_step; auto. iIntros (σ1 stepcnt κ κs n) "[Hσ Ht]".
  iMod (heap_write _ _ _ (LitV lit2) with "£ Hσ guards G Hv") as "(% & Hσ & G & Hv')"; first by trivial.
  iApply (fupd_mask_intro _ ∅); first set_solver. iIntros "Hclose". iSplit. 
  { iPureIntro. eexists _, _, _, _. eapply CasSucS => //. destruct lit1 => //. }
  iNext; iIntros (e2 σ2 efs Hstep) "credit"; inv_head_step.
  - rename select (lit_neq _ _) into Hfalse; inversion Hfalse; subst => //.
  - iMod "Hclose" as "_".
    iMod (time_interp_step with "Ht") as "$". iModIntro.
    iFrame "Hσ". iSplit; last done.
    iApply wp_value.
    iApply ("HΦ" with "[$Hv' $G]").
Qed.

Lemma wp_cas_int_suc_guarded  E l c z1 e2 lit2 d G :
  ↑naN ⊆ E →
  IntoVal e2 (LitV lit2) →
  {{{ (G &&{↑naN; d}&&> ((l,c) #↦_)) ∗ G ∗ (l,c) #↦ LitV (LitInt z1) ∗ £(3 * d + 1) }}}
    CAS (Lit $ LitLoc l) (Lit $ LitInt z1) e2 @ E
  {{{ RET LitV $ LitInt 1; G ∗ (l,c) #↦ LitV lit2 }}}.
Proof.
  iIntros (Hmask <- Φ) "[#guards [G [Hv £]]] HΦ".
  iApply (wp_cas_suc_guarded with "[$guards $G $Hv $£]") => //.
Qed.

Lemma wp_cas_suc E l lit1 e2 lit2 :
  ↑naN ⊆ E →
  IntoVal e2 (LitV lit2) → lit1 ≠ LitPoison →
  {{{ ▷ l ↦ LitV lit1 ∗ £1 }}}
    CAS (Lit $ LitLoc l) (Lit lit1) e2 @ E
  {{{ RET LitV (LitInt 1); l ↦ LitV lit2 }}}.
Proof.
  iIntros (? <- ? Φ) "[>Hv £] HΦ".
  iApply (wp_cas_suc_guarded E l [] lit1 _ lit2 0 True%I with "[Hv £]"); eauto => //.
  -  rewrite heap_cloc1_mapsto_val. iFrame. iApply guards_true.
  - iNext. iIntros "[_ B]". iApply "HΦ". rewrite heap_cloc1_mapsto_val. iFrame.
Qed.

Lemma wp_cas_int_suc E l z1 e2 lit2 :
  ↑naN ⊆ E →
  IntoVal e2 (LitV lit2) →
  {{{ ▷ l ↦ LitV (LitInt z1) ∗ £1 }}}
    CAS (Lit $ LitLoc l) (Lit $ LitInt z1) e2 @ E
  {{{ RET LitV (LitInt 1); l ↦ LitV lit2 }}}.
Proof.
  iIntros (Hmask IntoVal Φ) "[>pt £] ToΦ".
  iApply (wp_cas_suc with "[$]") => //.
Qed.

Lemma wp_cas_loc_suc E l l1 e2 lit2 :
  ↑naN ⊆ E →
  IntoVal e2 (LitV lit2) →
  {{{ ▷ l ↦ LitV (LitLoc l1) ∗ £1 }}}
    CAS (Lit $ LitLoc l) (Lit $ LitLoc l1) e2 @ E
  {{{ RET LitV (LitInt 1); l ↦ LitV lit2 }}}.
Proof.
  iIntros (Hmask IntoVal Φ) "[>pt £] ToΦ".
  iApply (wp_cas_suc with "[$]") => //.
Qed.

Lemma wp_eq_loc E (l1 : loc) (l2: loc) v1 v2 P Φ :
  ↑naN ⊆ E →
  (P -∗ ▷ l1 ↦ v1) →
  (P -∗ ▷ l2 ↦ v2) →
  (P -∗ ▷ Φ (LitV (bool_decide (l1 = l2)))) →
  P -∗ WP BinOp EqOp (Lit (LitLoc l1)) (Lit (LitLoc l2)) @ E {{ Φ }}.
Proof.
  iIntros (Hmask Hl1 Hl2 Hpost) "HP".
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
    iAssert ((▷ ∃ v, l1 ↦ v) ∧ (▷ ∃ v, l2 ↦ v) ∧ ▷ Φ (LitV false))%I
      with "[HP]" as "HP".
    { iSplit; last iSplit.
      + iExists _. by iApply Hl1.
      + iExists _. by iApply Hl2.
      + by iApply Hpost. }
    clear Hl1 Hl2. iNext. iIntros (e2 σ2 efs Hs) "£".
    inv_head_step. iSplitR=>//. inv_bin_op_eval; inv_lit.
    + iDestruct "HP" as "[Hl1 _]".
      iDestruct "Hl1" as (?) "Hl1".
      iMod (heap_read σ2 with "Hσ1 Hl1") as "[_ [_ %X]]"; first by set_solver.
      destruct X as [n0 X]. exfalso. simplify_eq.
    + iDestruct "HP" as "[_ [Hl2 _]]".
      iDestruct "Hl2" as (?) "Hl2".
      iMod (heap_read σ2 with "Hσ1 Hl2") as "[_ [_ %X]]"; first by set_solver.
      destruct X as [n0 X]. exfalso. simplify_eq.
    + iDestruct "HP" as "[_ [_ $]]". done.
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
  iDestruct "Hσ" as (hF) "(Hσ & HhF & %REL & ato)";
  iDestruct "Hσ" as (σL σB) "(%Hr & HL & HB)".

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

(** ** Moving locations between the legacy region and the byte region *)
Lemma wp_words_to_bytes E e l vl Φ :
  TCEq (to_val e) None → ↑naN ⊆ E →
  l ↦∗ vl -∗ (l ↦b (word_to_byte <$> vl) -∗ WP e @ E {{ Φ }}) -∗ WP e @ E {{ Φ }}.
Proof.
  rewrite !wp_unfold /wp_pre /=. iIntros (-> ?) "Hl Hwp".
  iIntros (σ1 ns κ κs nt) "[Hσ Ht]". iDestruct "Hσ" as (hF) "(Hσ & HhF & %REL & ato)".
  iMod (heap_words_to_bytes with "Hσ Hl") as "[Hσ Hl]"; [done|].
  iSpecialize ("Hwp" with "Hl"). iApply ("Hwp" $! σ1 ns κ κs nt). iFrame. by iPureIntro.
Qed.

Lemma wp_bytes_to_words E e l vl Φ :
  TCEq (to_val e) None → ↑naN ⊆ E →
  l ↦b (word_to_byte <$> vl) -∗ (l ↦∗ vl -∗ WP e @ E {{ Φ }}) -∗ WP e @ E {{ Φ }}.
Proof.
  rewrite !wp_unfold /wp_pre /=. iIntros (-> ?) "Hl Hwp".
  iIntros (σ1 ns κ κs nt) "[Hσ Ht]". iDestruct "Hσ" as (hF) "(Hσ & HhF & %REL & ato)".
  iMod (heap_bytes_to_words with "Hσ Hl") as "[Hσ Hl]"; [done|].
  iSpecialize ("Hwp" with "Hl"). iApply ("Hwp" $! σ1 ns κ κs nt). iFrame. by iPureIntro.
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
  have Hrange' := phys_rel_mem_range _ _ _ _ _ _ Hr Hrange.
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
  have Hrange' := phys_rel_mem_range _ _ _ _ _ _ Hr Hrange.
  iApply fupd_mask_intro; first set_solver. iIntros "Hclose". iSplit.
  { iPureIntro. eexists _, _, _, _. by eapply LoadNa1S. }
  iNext; iIntros (e2 σ2 efs Hstep); inv_head_step. iMod "Hclose" as "_".
  iMod (time_interp_step with "Ht") as "$". iIntros "credit !>".
  iSplitR "HΦ Hbs".
  { iExists hF. rewrite -Hlen. iFrame. iPureIntro. split.
    - by eapply phys_rel_mem_alter.
    - eapply heap_freeable_rel_dom; [|done]. intros ?. by rewrite is_Some_mem_alter. }
  iSplit; last done.
  clear dependent σ1 σL σB hF. iApply wp_lift_atomic_base_step_no_fork; auto.
  iIntros (σ1 stepcnt' κ' κs' n') "[Hσ Ht]".
  iMod (time_interp_step with "Ht") as "$". heap_split.
  iMod (bytes_ctx_read_end with "HB Hbs") as "(%Hrange & HB & Hbs)".
  have Hrange' := phys_rel_mem_range _ _ _ _ _ _ Hr Hrange.
  iModIntro; iSplit.
  { iPureIntro. eexists _, _, _, _. by eapply LoadNa2S. }
  iNext. iIntros (e2 σ2 efs Hstep) "credit2 !>"; inv_head_step.
  match goal with H : mem_range _ _ _ ?bs' |- _ =>
    have Heq := mem_range_det _ _ _ _ _ _ Hrange' H ltac:(lia) end. subst.
  match goal with H : decode_value _ _ = Some _ |- _ => rewrite Hdec in H; simplify_eq end.
  iSplit; [done|]. iSplitR "HΦ Hbs".
  { iExists hF. rewrite -Hlen. iFrame. iPureIntro. split.
    - by eapply phys_rel_mem_alter.
    - eapply heap_freeable_rel_dom; [|done]. intros ?. by rewrite is_Some_mem_alter. }
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
  have Hlen' : length (@encode_value val m v) = length bs by rewrite length_encode_value.
  iMod (bytes_ctx_write _ _ _ _ (@encode_value val m v) with "HB Hbs") as "(%Hrange & HB & Hbs)"; [done..|].
  have Hrange' := phys_rel_mem_range _ _ _ _ _ _ Hr Hrange.
  iModIntro. iSplit. { iPureIntro. eexists _, _, _, _. eapply StoreScS; eauto. }
  iNext; iIntros (e2 σ2 efs Hstep) "credit"; inv_head_step.
  iMod (time_interp_step with "Ht") as "$". iModIntro. iSplit; [done|].
  iSplitR "HΦ Hbs".
  { iExists hF. iFrame. iPureIntro. split.
    - by eapply phys_rel_mem_write.
    - eapply heap_freeable_rel_dom; [|done]. intros ?. simpl.
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
  have Hrange' := phys_rel_mem_range _ _ _ _ _ _ Hr Hrange.
  iApply fupd_mask_intro; first set_solver. iIntros "Hclose". iSplit.
  { iPureIntro. eexists _, _, _, _. eapply StoreNa1S; eauto. }
  iNext; iIntros (e2 σ2 efs Hstep); inv_head_step. iMod "Hclose" as "_".
  iMod (time_interp_step with "Ht") as "$". iIntros "credit !>".
  iSplitR "HΦ Hbs".
  { iExists hF. rewrite -Hlen. iFrame. iPureIntro. split.
    - by eapply phys_rel_mem_alter.
    - eapply heap_freeable_rel_dom; [|done]. intros ?. by rewrite is_Some_mem_alter. }
  iSplit; last done.
  clear dependent σ1 σL σB hF. iApply wp_lift_atomic_base_step_no_fork; auto.
  iIntros (σ1 stepcnt' κ' κs' n') "[Hσ Ht]".
  iMod (time_interp_step with "Ht") as "$". heap_split.
  match goal with H : val_wf m ?w |- _ => rename w into v end.
  have Hlen' : length (@encode_value val m v) = length bs by rewrite length_encode_value.
  iMod (bytes_ctx_write_end _ _ _ _ (@encode_value val m v) with "HB Hbs") as "(%Hrange & HB & Hbs)";
    [done..|].
  have Hrange' := phys_rel_mem_range _ _ _ _ _ _ Hr Hrange.
  iModIntro; iSplit.
  { iPureIntro. eexists _, _, _, _. eapply StoreNa2S; eauto. }
  iNext. iIntros (e2 σ2 efs Hstep) "credit2 !>"; inv_head_step.
  iSplit; [done|]. iSplitR "HΦ Hbs".
  { iExists hF. iFrame. iPureIntro. split.
    - by eapply phys_rel_mem_write.
    - eapply heap_freeable_rel_dom; [|done]. intros ?. simpl.
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
  have Hrange1' := phys_rel_mem_range _ _ _ _ _ _ Hr Hrange1.
  iMod (bytes_ctx_read_begin with "HB Hbs2") as "(%Hrange2 & HB & Hbs2)".
  have Hrange2' := phys_rel_mem_range _ _ _ _ _ _ Hr Hrange2.
  have Hr2 := phys_rel_mem_alter _ ls_inc _ _ _ _ _ Hr Hrange2.
  iMod (bytes_ctx_write_begin with "HB Hbs1") as "(%Hrange1b & HB & Hbs1)"; [done|].
  have Hr1 := phys_rel_mem_alter _ (λ _, WSt) _ _ _ _ _ Hr2 Hrange1b.
  iApply fupd_mask_intro; first set_solver. iIntros "Hclose". iSplit.
  { iPureIntro. eexists _, _, _, _. eapply MemCopyNa1S; eauto. }
  iNext; iIntros (e2 σ2 efs Hstep); inv_head_step. iMod "Hclose" as "_".
  iMod (time_interp_step with "Ht") as "$". iIntros "credit !>".
  iSplitR "HΦ Hbs1 Hbs2".
  { rewrite Hlen2 in Hr1. rewrite Hlen2. iExists hF. iFrame. iPureIntro. split; [done|].
    eapply heap_freeable_rel_dom; [|done]. intros ?. by rewrite !is_Some_mem_alter. }
  iSplit; last done.
  clear dependent σ1 σL σB hF. iApply wp_lift_atomic_base_step_no_fork; auto.
  iIntros (σ1 stepcnt' κ' κs' n'') "[Hσ Ht]".
  iMod (time_interp_step with "Ht") as "$". heap_split.
  iMod (bytes_ctx_lookup_1 with "HB Hbs1") as "(%Hrange1 & HB & Hbs1)"; [done|].
  have Hrange1' := phys_rel_mem_range _ _ _ _ _ _ Hr Hrange1.
  iMod (bytes_ctx_read_end with "HB Hbs2") as "(%Hrange2 & HB & Hbs2)".
  have Hrange2' := phys_rel_mem_range _ _ _ _ _ _ Hr Hrange2.
  have Hr2 := phys_rel_mem_alter _ ls_dec _ _ _ _ _ Hr Hrange2.
  have Hlen' : length bs2 = length bs1 by lia.
  iMod (bytes_ctx_write_end _ _ _ _ bs2 with "HB Hbs1") as "(%Hrange1b & HB & Hbs1)"; [done..|].
  have Hr1 := phys_rel_mem_write _ _ _ _ _ _ bs2 Hr2 Hrange1b Hlen'.
  iModIntro; iSplit.
  { iPureIntro. eexists _, _, _, _. eapply MemCopyNa2S; eauto. }
  iNext. iIntros (e2 σ2 efs Hstep) "credit2 !>"; inv_head_step.
  match goal with H : mem_range is_reading_S _ l2 ?bs' |- _ =>
    have Heq := mem_range_det _ _ _ _ _ _ Hrange2' H ltac:(lia) end. subst.
  iSplit; [done|]. iSplitR "HΦ Hbs1 Hbs2".
  { rewrite Hlen2 in Hr1. rewrite Hlen2. iExists hF. iFrame. iPureIntro. split; [done|].
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
  have Hrange' := phys_rel_mem_range _ _ _ _ _ _ Hr Hrange.
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
  have Hrange' := phys_rel_mem_range _ _ _ _ _ _ Hr Hrange.
  iApply fupd_mask_intro; first set_solver. iIntros "Hclose". iSplit.
  { iPureIntro. eexists _, _, _, _. by eapply LoadNa1S. }
  iNext; iIntros (e2 σ2 efs Hstep); inv_head_step. iMod "Hclose" as "_".
  iMod (time_interp_step with "Ht") as "$". iIntros "credit !>".
  iSplitR "HΦ Tok credit".
  { iExists hF. rewrite -Hlen. iFrame. iPureIntro. split.
    - by eapply phys_rel_mem_alter.
    - eapply heap_freeable_rel_dom; [|done]. intros ?. by rewrite is_Some_mem_alter. }
  iSplit; last done.
  clear dependent σ1 σL σB hF. iApply wp_lift_atomic_base_step_no_fork; auto.
  iIntros (σ1 stepcnt' κ' κs' n') "[Hσ Ht]".
  iMod (time_interp_step with "Ht") as "$". heap_split.
  iMod (bytes_ctx_read_end_guarded with "HB Tok") as "(%Hrange & HB & G)".
  iMod (lc_fupd_elim_later with "credit G") as "G".
  have Hrange' := phys_rel_mem_range _ _ _ _ _ _ Hr Hrange.
  iModIntro; iSplit.
  { iPureIntro. eexists _, _, _, _. by eapply LoadNa2S. }
  iNext. iIntros (e2 σ2 efs Hstep) "credit2 !>"; inv_head_step.
  match goal with H : mem_range _ _ _ ?bs' |- _ =>
    have Heq := mem_range_det _ _ _ _ _ _ Hrange' H ltac:(lia) end. subst.
  match goal with H : decode_value _ _ = Some _ |- _ => rewrite Hdec in H; simplify_eq end.
  iSplit; [done|]. iSplitR "HΦ G".
  { iExists hF. rewrite -Hlen. iFrame. iPureIntro. split.
    - by eapply phys_rel_mem_alter.
    - eapply heap_freeable_rel_dom; [|done]. intros ?. by rewrite is_Some_mem_alter. }
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
  have Hrange1' := phys_rel_mem_range _ _ _ _ _ _ Hr Hrange1.
  iMod (bytes_ctx_read_begin_guarded _ _ _ Ψ (length bs1) with "£ Guard HP G HB")
    as (i bs2) "(%HΨbs & %Hrange2 & HB & Tok)"; [done..|].
  have Hlen2 : length bs2 = length bs1 := HΨ _ HΨbs.
  have Hrange2' := phys_rel_mem_range _ _ _ _ _ _ Hr Hrange2.
  have Hr2 := phys_rel_mem_alter _ ls_inc _ _ _ _ _ Hr Hrange2.
  rewrite Hlen2 in Hr2.
  iMod (bytes_ctx_write_begin with "HB Hbs1") as "(%Hrange1b & HB & Hbs1)"; [done|].
  have Hr1 := phys_rel_mem_alter _ (λ _, WSt) _ _ _ _ _ Hr2 Hrange1b.
  iApply fupd_mask_intro; first set_solver. iIntros "Hclose". iSplit.
  { iPureIntro. eexists _, _, _, _. eapply MemCopyNa1S; eauto. }
  iNext; iIntros (e2 σ2 efs Hstep); inv_head_step. iMod "Hclose" as "_".
  iMod (time_interp_step with "Ht") as "$". iIntros "credit !>".
  iSplitR "HΦ Hbs1 Tok credit".
  { iExists hF. iFrame. iPureIntro. split; [done|].
    eapply heap_freeable_rel_dom; [|done]. intros ?. by rewrite !is_Some_mem_alter. }
  iSplit; last done.
  clear dependent σ1 σL σB hF. iApply wp_lift_atomic_base_step_no_fork; auto.
  iIntros (σ1 stepcnt' κ' κs' n'') "[Hσ Ht]".
  iMod (time_interp_step with "Ht") as "$". heap_split.
  iMod (bytes_ctx_lookup_1 with "HB Hbs1") as "(%Hrange1 & HB & Hbs1)"; [done|].
  have Hrange1' := phys_rel_mem_range _ _ _ _ _ _ Hr Hrange1.
  iMod (bytes_ctx_read_end_guarded with "HB Tok") as "(%Hrange2 & HB & G)".
  iMod (lc_fupd_elim_later with "credit G") as "G".
  have Hrange2' := phys_rel_mem_range _ _ _ _ _ _ Hr Hrange2.
  have Hr2 := phys_rel_mem_alter _ ls_dec _ _ _ _ _ Hr Hrange2.
  have Hlen' : length bs2 = length bs1 by lia.
  iMod (bytes_ctx_write_end _ _ _ _ bs2 with "HB Hbs1") as "(%Hrange1b & HB & Hbs1)"; [done..|].
  have Hr1 := phys_rel_mem_write _ _ _ _ _ _ bs2 Hr2 Hrange1b Hlen'.
  iModIntro; iSplit.
  { iPureIntro. eexists _, _, _, _. eapply MemCopyNa2S; eauto. }
  iNext. iIntros (e2 σ2 efs Hstep) "credit2 !>"; inv_head_step.
  match goal with H : mem_range is_reading_S _ l2 ?bs' |- _ =>
    have Heq := mem_range_det _ _ _ _ _ _ Hrange2' H ltac:(lia) end. subst.
  iSplit; [done|]. iSplitR "HΦ Hbs1 G".
  { iExists hF. iFrame. iPureIntro. split; [by rewrite -Hlen'|].
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

(** ** Updates of the byte context around steps

The cell operations of [heap.v] ([bytes_ctx_pcell_create], [_untether], ...) are updates of
the byte context [bytes_ctx σB] that keep [σB]. A program can do them before any step
([wp_bytes_ctx_pre]), or right after the last step of a load, a store or a copy (the
[_post] variants of the rules above). *)
Lemma wp_bytes_ctx_pre E e Φ :
  TCEq (to_val e) None →
  (∀ σB, bytes_ctx σB ={E}=∗ bytes_ctx σB ∗ WP e @ E {{ Φ }}) -∗ WP e @ E {{ Φ }}.
Proof.
  iIntros (Hv%TCEq_eq) "Hwp". iEval (rewrite wp_unfold /wp_pre /= Hv).
  iIntros (σ1 ns κ κs nt) "[Hσ Ht]". iDestruct "Hσ" as (hF) "(Hσ & HhF & %REL & ato)".
  iDestruct "Hσ" as (σL σB) "(%Hr & HL & HB)".
  iMod ("Hwp" with "HB") as "[HB Hwp]". iEval (rewrite wp_unfold /wp_pre /= Hv) in "Hwp".
  iApply ("Hwp" $! σ1 ns κ κs nt). iFrame. by iPureIntro.
Qed.

Lemma wp_load_sc_post E l m bs v Φ :
  decode_value m bs = Some v →
  ▷ l ↦b bs -∗ ▷ (l ↦b bs -∗ ∀ σB, bytes_ctx σB ={E}=∗ bytes_ctx σB ∗ Φ (MLitV v)) -∗
  WP Load ScOrd m (Lit $ LitLoc l) @ E {{ Φ }}.
Proof.
  iIntros (Hdec) ">Hbs HΦ". have Hlen := decode_value_length _ _ _ Hdec.
  iApply wp_lift_atomic_base_step_no_fork; auto.
  iIntros (σ1 stepcnt κ κs n') "[Hσ Ht] !>". heap_split.
  iDestruct (bytes_ctx_lookup with "HB Hbs") as %Hrange.
  have Hrange' := phys_rel_mem_range _ _ _ _ _ _ Hr Hrange.
  iSplit. { iPureIntro. eexists _, _, _, _. by eapply LoadScS. }
  iNext; iIntros (e2 σ2 efs Hstep) "credit"; inv_head_step.
  match goal with H : mem_range _ _ _ ?bs' |- _ =>
    have Heq := mem_range_det _ _ _ _ _ _ Hrange' H ltac:(lia) end. subst.
  match goal with H : decode_value _ _ = Some _ |- _ => rewrite Hdec in H; simplify_eq end.
  iMod ("HΦ" with "Hbs HB") as "[HB HΦ]".
  iMod (time_interp_step with "Ht") as "$". iModIntro. iSplit; [done|].
  iSplitR "HΦ"; [by iFrame|]. done.
Qed.

Lemma wp_load_na_post E l m bs v Φ :
  decode_value m bs = Some v →
  ▷ l ↦b bs -∗ ▷ (l ↦b bs -∗ ∀ σB, bytes_ctx σB ={E}=∗ bytes_ctx σB ∗ Φ (MLitV v)) -∗
  WP Load Na1Ord m (Lit $ LitLoc l) @ E {{ Φ }}.
Proof.
  iIntros (Hdec) ">Hbs HΦ". have Hlen := decode_value_length _ _ _ Hdec.
  iApply wp_lift_base_step; auto.
  iIntros (σ1 stepcnt κ κs n) "[Hσ Ht]". heap_split.
  iMod (bytes_ctx_read_begin with "HB Hbs") as "(%Hrange & HB & Hbs)".
  have Hrange' := phys_rel_mem_range _ _ _ _ _ _ Hr Hrange.
  iApply fupd_mask_intro; first set_solver. iIntros "Hclose". iSplit.
  { iPureIntro. eexists _, _, _, _. by eapply LoadNa1S. }
  iNext; iIntros (e2 σ2 efs Hstep); inv_head_step. iMod "Hclose" as "_".
  iMod (time_interp_step with "Ht") as "$". iIntros "credit !>".
  iSplitR "HΦ Hbs".
  { iExists hF. rewrite -Hlen. iFrame. iPureIntro. split.
    - by eapply phys_rel_mem_alter.
    - eapply heap_freeable_rel_dom; [|done]. intros ?. by rewrite is_Some_mem_alter. }
  iSplit; last done.
  clear dependent σ1 σL σB hF. iApply wp_lift_atomic_base_step_no_fork; auto.
  iIntros (σ1 stepcnt' κ' κs' n') "[Hσ Ht]".
  iMod (time_interp_step with "Ht") as "$". heap_split.
  iMod (bytes_ctx_read_end with "HB Hbs") as "(%Hrange & HB & Hbs)".
  have Hrange' := phys_rel_mem_range _ _ _ _ _ _ Hr Hrange.
  iModIntro; iSplit.
  { iPureIntro. eexists _, _, _, _. by eapply LoadNa2S. }
  iNext. iIntros (e2 σ2 efs Hstep) "credit2"; inv_head_step.
  match goal with H : mem_range _ _ _ ?bs' |- _ =>
    have Heq := mem_range_det _ _ _ _ _ _ Hrange' H ltac:(lia) end. subst.
  match goal with H : decode_value _ _ = Some _ |- _ => rewrite Hdec in H; simplify_eq end.
  iMod ("HΦ" with "Hbs HB") as "[HB HΦ]". iModIntro.
  iSplit; [done|]. iSplitR "HΦ"; [|done].
  iExists hF. rewrite -Hlen. iFrame. iPureIntro. split.
  - by eapply phys_rel_mem_alter.
  - eapply heap_freeable_rel_dom; [|done]. intros ?. by rewrite is_Some_mem_alter.
Qed.

Lemma wp_store_sc_post E l m bs e v Φ :
  ↑naN ⊆ E → IntoVal e (MLitV v) → val_wf m v → length bs = mty_size m →
  ▷ l ↦b bs -∗
  ▷ (l ↦b encode_value m v -∗ ∀ σB, bytes_ctx σB ={E}=∗ bytes_ctx σB ∗ Φ (LitV LitPoison)) -∗
  WP Store ScOrd m (Lit $ LitLoc l) e @ E {{ Φ }}.
Proof.
  iIntros (? <- Hwf Hlen) ">Hbs HΦ".
  iApply wp_lift_atomic_base_step_no_fork; auto.
  iIntros (σ1 stepcnt κ κs n') "[Hσ Ht]". heap_split.
  have Hlen' : length (@encode_value val m v) = length bs by rewrite length_encode_value.
  iMod (bytes_ctx_write _ _ _ _ (@encode_value val m v) with "HB Hbs") as "(%Hrange & HB & Hbs)"; [done..|].
  have Hrange' := phys_rel_mem_range _ _ _ _ _ _ Hr Hrange.
  iModIntro. iSplit. { iPureIntro. eexists _, _, _, _. eapply StoreScS; eauto. }
  iNext; iIntros (e2 σ2 efs Hstep) "credit"; inv_head_step.
  iMod ("HΦ" with "Hbs HB") as "[HB HΦ]".
  iMod (time_interp_step with "Ht") as "$". iModIntro. iSplit; [done|].
  iSplitR "HΦ"; [|done].
  iExists hF. iFrame. iPureIntro. split.
  - by eapply phys_rel_mem_write.
  - eapply heap_freeable_rel_dom; [|done]. intros ?. simpl.
    by rewrite (is_Some_mem_write _ _ _ _ _ _ Hrange' Hlen').
Qed.

Lemma wp_store_na_post E l m bs e v Φ :
  ↑naN ⊆ E → IntoVal e (MLitV v) → val_wf m v → length bs = mty_size m →
  ▷ l ↦b bs -∗
  ▷ (l ↦b encode_value m v -∗ ∀ σB, bytes_ctx σB ={E}=∗ bytes_ctx σB ∗ Φ (LitV LitPoison)) -∗
  WP Store Na1Ord m (Lit $ LitLoc l) e @ E {{ Φ }}.
Proof.
  iIntros (? <- Hwf Hlen) ">Hbs HΦ".
  iApply wp_lift_base_step; auto.
  iIntros (σ1 stepcnt κ κs n) "[Hσ Ht]". heap_split.
  iMod (bytes_ctx_write_begin with "HB Hbs") as "(%Hrange & HB & Hbs)"; [done|].
  have Hrange' := phys_rel_mem_range _ _ _ _ _ _ Hr Hrange.
  iApply fupd_mask_intro; first set_solver. iIntros "Hclose". iSplit.
  { iPureIntro. eexists _, _, _, _. eapply StoreNa1S; eauto. }
  iNext; iIntros (e2 σ2 efs Hstep); inv_head_step. iMod "Hclose" as "_".
  iMod (time_interp_step with "Ht") as "$". iIntros "credit !>".
  iSplitR "HΦ Hbs".
  { iExists hF. rewrite -Hlen. iFrame. iPureIntro. split.
    - by eapply phys_rel_mem_alter.
    - eapply heap_freeable_rel_dom; [|done]. intros ?. by rewrite is_Some_mem_alter. }
  iSplit; last done.
  clear dependent σ1 σL σB hF. iApply wp_lift_atomic_base_step_no_fork; auto.
  iIntros (σ1 stepcnt' κ' κs' n') "[Hσ Ht]".
  iMod (time_interp_step with "Ht") as "$". heap_split.
  match goal with H : val_wf m ?w |- _ => rename w into v end.
  have Hlen' : length (@encode_value val m v) = length bs by rewrite length_encode_value.
  iMod (bytes_ctx_write_end _ _ _ _ (@encode_value val m v) with "HB Hbs") as "(%Hrange & HB & Hbs)";
    [done..|].
  have Hrange' := phys_rel_mem_range _ _ _ _ _ _ Hr Hrange.
  iModIntro; iSplit.
  { iPureIntro. eexists _, _, _, _. eapply StoreNa2S; eauto. }
  iNext. iIntros (e2 σ2 efs Hstep) "credit2"; inv_head_step.
  iMod ("HΦ" with "Hbs HB") as "[HB HΦ]". iModIntro.
  iSplit; [done|]. iSplitR "HΦ"; [|done].
  iExists hF. iFrame. iPureIntro. split.
  - by eapply phys_rel_mem_write.
  - eapply heap_freeable_rel_dom; [|done]. intros ?. simpl.
    by rewrite (is_Some_mem_write _ _ _ _ _ _ Hrange' Hlen').
Qed.

Lemma wp_memcopy_post E l1 l2 bs1 bs2 (n : nat) Φ :
  ↑naN ⊆ E → length bs1 = n → length bs2 = n →
  ▷ l1 ↦b bs1 -∗ ▷ l2 ↦b bs2 -∗
  ▷ (l1 ↦b bs2 -∗ l2 ↦b bs2 -∗ ∀ σB, bytes_ctx σB ={E}=∗ bytes_ctx σB ∗ Φ (LitV LitPoison)) -∗
  WP MemCopy Na1Ord n (Lit $ LitLoc l1) (Lit $ LitLoc l2) @ E {{ Φ }}.
Proof.
  iIntros (? Hlen1 Hlen2) ">Hbs1 >Hbs2 HΦ". subst n.
  iApply wp_lift_base_step; auto.
  iIntros (σ1 stepcnt κ κs n') "[Hσ Ht]". heap_split.
  iEval (rewrite heap_mapsto_bytes_st_vec) in "Hbs1".
  iMod (bytes_ctx_lookup_1 with "HB Hbs1") as "(%Hrange1 & HB & Hbs1)"; [done|].
  iEval (rewrite -heap_mapsto_bytes_st_vec) in "Hbs1".
  have Hrange1' := phys_rel_mem_range _ _ _ _ _ _ Hr Hrange1.
  iMod (bytes_ctx_read_begin with "HB Hbs2") as "(%Hrange2 & HB & Hbs2)".
  have Hrange2' := phys_rel_mem_range _ _ _ _ _ _ Hr Hrange2.
  have Hr2 := phys_rel_mem_alter _ ls_inc _ _ _ _ _ Hr Hrange2.
  iMod (bytes_ctx_write_begin with "HB Hbs1") as "(%Hrange1b & HB & Hbs1)"; [done|].
  have Hr1 := phys_rel_mem_alter _ (λ _, WSt) _ _ _ _ _ Hr2 Hrange1b.
  iApply fupd_mask_intro; first set_solver. iIntros "Hclose". iSplit.
  { iPureIntro. eexists _, _, _, _. eapply MemCopyNa1S; eauto. }
  iNext; iIntros (e2 σ2 efs Hstep); inv_head_step. iMod "Hclose" as "_".
  iMod (time_interp_step with "Ht") as "$". iIntros "credit !>".
  iSplitR "HΦ Hbs1 Hbs2".
  { rewrite Hlen2 in Hr1. rewrite Hlen2. iExists hF. iFrame. iPureIntro. split; [done|].
    eapply heap_freeable_rel_dom; [|done]. intros ?. by rewrite !is_Some_mem_alter. }
  iSplit; last done.
  clear dependent σ1 σL σB hF. iApply wp_lift_atomic_base_step_no_fork; auto.
  iIntros (σ1 stepcnt' κ' κs' n'') "[Hσ Ht]".
  iMod (time_interp_step with "Ht") as "$". heap_split.
  iMod (bytes_ctx_lookup_1 with "HB Hbs1") as "(%Hrange1 & HB & Hbs1)"; [done|].
  have Hrange1' := phys_rel_mem_range _ _ _ _ _ _ Hr Hrange1.
  iMod (bytes_ctx_read_end with "HB Hbs2") as "(%Hrange2 & HB & Hbs2)".
  have Hrange2' := phys_rel_mem_range _ _ _ _ _ _ Hr Hrange2.
  have Hr2 := phys_rel_mem_alter _ ls_dec _ _ _ _ _ Hr Hrange2.
  have Hlen' : length bs2 = length bs1 by lia.
  iMod (bytes_ctx_write_end _ _ _ _ bs2 with "HB Hbs1") as "(%Hrange1b & HB & Hbs1)"; [done..|].
  have Hr1 := phys_rel_mem_write _ _ _ _ _ _ bs2 Hr2 Hrange1b Hlen'.
  iModIntro; iSplit.
  { iPureIntro. eexists _, _, _, _. eapply MemCopyNa2S; eauto. }
  iNext. iIntros (e2 σ2 efs Hstep) "credit2"; inv_head_step.
  match goal with H : mem_range is_reading_S _ l2 ?bs' |- _ =>
    have Heq := mem_range_det _ _ _ _ _ _ Hrange2' H ltac:(lia) end. subst.
  iMod ("HΦ" with "Hbs1 Hbs2 HB") as "[HB HΦ]". iModIntro.
  iSplit; [done|]. iSplitR "HΦ"; [|done].
  rewrite Hlen2 in Hr1. rewrite Hlen2. iExists hF. iFrame. iPureIntro. split; [done|].
  eapply heap_freeable_rel_dom; [|done]. intros ?.
  simpl. rewrite is_Some_mem_write'; [by rewrite !is_Some_mem_alter|].
  intros i Hi. rewrite is_Some_mem_alter.
  destruct (mem_range_lookup_1 _ _ _ _ i Hrange1') as (?&?&Hl&_); [lia|]. eexists. exact Hl.
Qed.

(** ** Cells of the byte region *)

(** Creating a cell group ([PCellFromOwn]) and destroying it ([PCell2Own]) are updates of the
    byte context; they can be done before any step. *)
Lemma wp_pcell_create E e l m fbs fv Φ :
  TCEq (to_val e) None → ↑naN ⊆ E → (0 < mty_size m)%nat → mty_wf m →
  heap_mapsto_fbytes l fbs -∗ brepr m fbs fv -∗
  (∀ g cs, loc_side l g m cs -∗ gdyn g fv -∗
     (if bool_decide (fv_cells fv = []) then gnocell g else True) -∗ WP e @ E {{ Φ }}) -∗
  WP e @ E {{ Φ }}.
Proof.
  iIntros (Hv ???) "Hl Hrep Hwp". iApply wp_bytes_ctx_pre. iIntros (σB) "HB".
  iMod (bytes_ctx_pcell_create with "HB Hl Hrep") as (g cs) "(HB & Hls & Hgd & Hnc)"; [done..|].
  iModIntro. iFrame "HB". iApply ("Hwp" with "Hls Hgd Hnc").
Qed.

Lemma wp_pcell_create_plain E e l m bs v Φ :
  TCEq (to_val e) None → ↑naN ⊆ E → (0 < mty_size m)%nat → mty_wf m → decode_value m bs = Some v →
  l ↦b bs -∗ (∀ g cs, loc_side l g m cs -∗ gdyn g (fv_lift v) -∗ gnocell g -∗ WP e @ E {{ Φ }}) -∗
  WP e @ E {{ Φ }}.
Proof.
  iIntros (Hv ? ? ? Hd) "Hl Hwp". rewrite heap_mapsto_fbytes_bytes.
  iApply (wp_pcell_create with "Hl []"); [done|done|done|..].
  { by iApply brepr_plain. }
  iIntros (g cs) "Hls Hgd". rewrite bool_decide_eq_true_2; [|apply fv_cells_lift].
  iApply ("Hwp" with "Hls Hgd").
Qed.

Lemma wp_pcell_destroy E e l g m cs fv Φ :
  TCEq (to_val e) None →
  loc_side l g m cs -∗ gdyn g fv -∗
  (∀ fbs, heap_mapsto_fbytes l fbs -∗ brepr m fbs fv -∗ WP e @ E {{ Φ }}) -∗ WP e @ E {{ Φ }}.
Proof.
  iIntros (Hv) "Hls Hgd Hwp". iApply wp_bytes_ctx_pre. iIntros (σB) "HB".
  iMod (bytes_ctx_pcell_destroy with "HB Hls Hgd") as (fbs) "(HB & Hl & Hrep)".
  iModIntro. iFrame "HB". iApply ("Hwp" with "Hl Hrep").
Qed.

Lemma wp_pcell_destroy_plain E e l g m cs v Φ :
  TCEq (to_val e) None →
  loc_side l g m cs -∗ gdyn g (fv_lift v) -∗
  (∀ bs, l ↦b bs -∗ ⌜decode_value m bs = Some v⌝ -∗ WP e @ E {{ Φ }}) -∗ WP e @ E {{ Φ }}.
Proof.
  iIntros (Hv) "Hls Hgd Hwp". iApply (wp_pcell_destroy with "Hls Hgd").
  iIntros (fbs) "Hl Hrep". iDestruct (brepr_plain_inv with "Hrep") as %(bs & -> & Hd).
  rewrite -heap_mapsto_fbytes_bytes. by iApply ("Hwp" with "Hl").
Qed.

(** Reads and writes through a cell whose location side is owned: the group is untethered
    for the duration of the access, so the location holds plain bytes. *)
Lemma wp_pcell_load_na E l g m cs fv :
  ↑naN ⊆ E →
  {{{ loc_side l g m cs ∗ gdyn g fv }}} Load Na1Ord m (Lit $ LitLoc l) @ E
  {{{ v, RET MLitV v; loc_side l g m cs ∗ gdyn g fv ∗ ⌜fv_cells fv = [] → fv = fv_lift v⌝ }}}.
Proof.
  iIntros (? Φ) "[Hls Hgd] HΦ". iApply wp_bytes_ctx_pre. iIntros (σB) "HB".
  iMod (bytes_ctx_pcell_untether with "HB Hls") as (bs v) "(HB & Hl & %Hd & Hu)"; [done|].
  iDestruct (bytes_ctx_untethered_val with "HB Hu Hgd") as %(v' & Hd' & Hfv).
  rewrite Hd in Hd'. injection Hd' as <-.
  iModIntro. iFrame "HB". iApply (wp_load_na_post with "Hl"); [done|].
  iIntros "!> Hl" (σB') "HB".
  iMod (bytes_ctx_pcell_retether_eq with "HB Hu Hl") as "[HB Hls]"; [done|].
  iModIntro. iFrame "HB". iApply "HΦ". by iFrame.
Qed.

Lemma wp_pcell_load_sc E l g m cs fv :
  ↑naN ⊆ E →
  {{{ loc_side l g m cs ∗ gdyn g fv }}} Load ScOrd m (Lit $ LitLoc l) @ E
  {{{ v, RET MLitV v; loc_side l g m cs ∗ gdyn g fv ∗ ⌜fv_cells fv = [] → fv = fv_lift v⌝ }}}.
Proof.
  iIntros (? Φ) "[Hls Hgd] HΦ". iApply wp_bytes_ctx_pre. iIntros (σB) "HB".
  iMod (bytes_ctx_pcell_untether with "HB Hls") as (bs v) "(HB & Hl & %Hd & Hu)"; [done|].
  iDestruct (bytes_ctx_untethered_val with "HB Hu Hgd") as %(v' & Hd' & Hfv).
  rewrite Hd in Hd'. injection Hd' as <-.
  iModIntro. iFrame "HB". iApply (wp_load_sc_post with "Hl"); [done|].
  iIntros "!> Hl" (σB') "HB".
  iMod (bytes_ctx_pcell_retether_eq with "HB Hu Hl") as "[HB Hls]"; [done|].
  iModIntro. iFrame "HB". iApply "HΦ". by iFrame.
Qed.

Lemma wp_pcell_store_na E l g m cs fv e v :
  ↑naN ⊆ E → IntoVal e (MLitV v) → mty_wf m → val_wf m v →
  {{{ loc_side l g m cs ∗ gdyn g fv ∗ gnocell g }}} Store Na1Ord m (Lit $ LitLoc l) e @ E
  {{{ RET LitV LitPoison; loc_side l g m cs ∗ gdyn g (fv_lift v) }}}.
Proof.
  iIntros (? He Hm Hv Φ) "(Hls & Hgd & #Hnc) HΦ". iApply wp_bytes_ctx_pre. iIntros (σB) "HB".
  iMod (bytes_ctx_pcell_untether with "HB Hls") as (bs v0) "(HB & Hl & %Hd & Hu)"; [done|].
  iModIntro. iFrame "HB".
  iApply (wp_store_na_post with "Hl"); [done..|by eapply decode_value_length|].
  iIntros "!> Hl" (σB') "HB".
  iMod (bytes_ctx_untethered_set _ _ _ _ _ (encode_value m v) with "HB Hu Hnc Hgd")
    as "(HB & Hu & Hgd)"; [by apply decode_encode_value|].
  iMod (bytes_ctx_pcell_retether_eq with "HB Hu Hl") as "[HB Hls]"; [done|].
  iModIntro. iFrame "HB". iApply "HΦ". by iFrame.
Qed.

Lemma wp_pcell_store_sc E l g m cs fv e v :
  ↑naN ⊆ E → IntoVal e (MLitV v) → mty_wf m → val_wf m v →
  {{{ loc_side l g m cs ∗ gdyn g fv ∗ gnocell g }}} Store ScOrd m (Lit $ LitLoc l) e @ E
  {{{ RET LitV LitPoison; loc_side l g m cs ∗ gdyn g (fv_lift v) }}}.
Proof.
  iIntros (? He Hm Hv Φ) "(Hls & Hgd & #Hnc) HΦ". iApply wp_bytes_ctx_pre. iIntros (σB) "HB".
  iMod (bytes_ctx_pcell_untether with "HB Hls") as (bs v0) "(HB & Hl & %Hd & Hu)"; [done|].
  iModIntro. iFrame "HB".
  iApply (wp_store_sc_post with "Hl"); [done..|by eapply decode_value_length|].
  iIntros "!> Hl" (σB') "HB".
  iMod (bytes_ctx_untethered_set _ _ _ _ _ (encode_value m v) with "HB Hu Hnc Hgd")
    as "(HB & Hu & Hgd)"; [by apply decode_encode_value|].
  iMod (bytes_ctx_pcell_retether_eq with "HB Hu Hl") as "[HB Hls]"; [done|].
  iModIntro. iFrame "HB". iApply "HΦ". by iFrame.
Qed.

(** Moving a [PCell] from [l] to [l'], by a verbatim copy. The old location keeps its
    bytes, as plain bytes. *)
Lemma wp_pcell_memcopy E l l' g m cs bs0 :
  ↑naN ⊆ E → length bs0 = mty_size m →
  {{{ loc_side l g m cs ∗ ▷ l' ↦b bs0 }}}
    MemCopy Na1Ord (mty_size m) (Lit $ LitLoc l') (Lit $ LitLoc l) @ E
  {{{ bs, RET LitV LitPoison; l ↦b bs ∗ loc_side l' g m cs }}}.
Proof.
  iIntros (? Hlen Φ) "[Hls Hl'] HΦ". iApply wp_bytes_ctx_pre. iIntros (σB) "HB".
  iMod (bytes_ctx_pcell_untether with "HB Hls") as (bs v) "(HB & Hl & %Hd & Hu)"; [done|].
  iModIntro. iFrame "HB".
  iApply (wp_memcopy_post with "Hl' Hl"); [done|done|by eapply decode_value_length|].
  iIntros "!> Hl' Hl" (σB') "HB".
  iMod (bytes_ctx_pcell_retether_eq with "HB Hu Hl'") as "[HB Hls]"; [done|].
  iModIntro. iFrame "HB". iApply "HΦ". by iFrame.
Qed.

Lemma mem_range_rst0_inc σ l2 n l1 bs :
  mem_range (.= RSt 0) (mem_alter ls_inc l2 n σ) l1 bs → mem_range (.= RSt 0) σ l1 bs.
Proof.
  rewrite !mem_range_lookup. intros H i b Hb. destruct (H i b Hb) as (ls & Hl & ->).
  destruct (loc_range_dec l2 n (l1 +ₗ i)) as [[j [Hj Heq]]|Hout].
  - rewrite Heq lookup_mem_alter_in // in Hl.
    destruct (σ !! (l2 +ₗ j)) as [[ls' b']|]; simpl in Hl; [destruct ls'|]; by inversion Hl.
  - rewrite lookup_mem_alter_out // in Hl. eauto.
Qed.

Lemma mem_range_wst_dec σ l2 n l1 bs :
  mem_range (.= WSt) (mem_alter ls_dec l2 n σ) l1 bs → mem_range (.= WSt) σ l1 bs.
Proof.
  rewrite !mem_range_lookup. intros H i b Hb. destruct (H i b Hb) as (ls & Hl & ->).
  destruct (loc_range_dec l2 n (l1 +ₗ i)) as [[j [Hj Heq]]|Hout].
  - rewrite Heq lookup_mem_alter_in // in Hl. rewrite Heq.
    destruct (σ !! (l2 +ₗ j)) as [[ls' b']|]; simpl in Hl; [destruct ls'|]; inversion Hl; subst; eauto.
  - rewrite lookup_mem_alter_out // in Hl. eauto.
Qed.

(** ** Accesses through cells at a plain sub-value

The following rules read or write a plain sub-value (of MiniRust type [m'], at the offset
[o']) of the fancy value [fv] of a group [g]. The group [g] may be nested in a live group:
it sits at the offset [o] inside the root group [g0] ([gpath g0 g o]), whose location side
is at [l0] and is only guarded (e.g. by the lifetime token of a shared reference to the
outer [PCell]); a group that is not nested is its own root ([gpath_refl]). The access is
at [l0 +ₗ (o + o')]. *)
Lemma wp_pcell_load_sc_sub E l0 g0 m0 cs0 g o m cs fv o' m' fvs G P d :
  ↑naN ⊆ E → fv_sub m fv o' m' fvs → fv_cells fvs = [] →
  {{{ (G &&{↑naN; d}&&> P) ∗
      □ (P -∗ (loc_side l0 g0 m0 cs0 ∗ gdyn g fv) ∗ (loc_side l0 g0 m0 cs0 -∗ gdyn g fv -∗ P)) ∗
      gpath g0 g o ∗ greg g m cs ∗ G ∗ £d }}}
    Load ScOrd m' (Lit $ LitLoc (l0 +ₗ (o + o')%nat)) @ E
  {{{ v, RET MLitV v; G ∗ ⌜fvs = fv_lift v⌝ }}}.
Proof.
  iIntros (? Hsub Hplain Φ) "(#Guard & #HP & #Hp & #Hg & G & £) HΦ".
  iApply wp_lift_atomic_base_step_no_fork; auto.
  iIntros (σ1 stepcnt κ κs n') "[Hσ Ht]". heap_split.
  iMod (guards_open_later with "Guard G") as "Open"; [done|].
  iMod (lc_fupd_elim_laterN with "£ Open") as ">[P Back]".
  iDestruct ("HP" with "P") as "[[Hls Hgd] Ret]".
  iDestruct (bytes_ctx_cell_lookup_sub with "HB Hls Hp Hg Hgd")
    as %(bs & v & Hrange & Hlen & Hdec & Hfv); [done..|].
  iMod ("Back" with "(Ret Hls Hgd)") as "G".
  have Hrange' := phys_rel_mem_range _ _ _ _ _ _ Hr Hrange.
  iModIntro. iSplit. { iPureIntro. eexists _, _, _, _. by eapply LoadScS. }
  iNext; iIntros (e2 σ2 efs Hstep) "credit"; inv_head_step.
  match goal with H : mem_range _ _ _ ?bs' |- _ =>
    have Heq := mem_range_det _ _ _ _ _ _ Hrange' H ltac:(lia) end. subst.
  match goal with H : decode_value _ _ = Some _ |- _ => rewrite Hdec in H; simplify_eq end.
  iMod (time_interp_step with "Ht") as "$". iModIntro. iSplit; [done|].
  iSplitR "HΦ G"; [by iFrame|]. iApply "HΦ". by iFrame.
Qed.

Lemma wp_pcell_load_na_sub E l0 g0 m0 cs0 g o m cs fv o' m' fvs G P d :
  ↑naN ⊆ E → fv_sub m fv o' m' fvs → fv_cells fvs = [] →
  {{{ (G &&{↑naN; d}&&> P) ∗
      □ (P -∗ (loc_side l0 g0 m0 cs0 ∗ gdyn g fv) ∗ (loc_side l0 g0 m0 cs0 -∗ gdyn g fv -∗ P)) ∗
      gpath g0 g o ∗ greg g m cs ∗ G ∗ £(2*d) }}}
    Load Na1Ord m' (Lit $ LitLoc (l0 +ₗ (o + o')%nat)) @ E
  {{{ v, RET MLitV v; G ∗ ⌜fvs = fv_lift v⌝ }}}.
Proof.
  iIntros (? Hsub Hplain Φ) "(#Guard & #HP & #Hp & #Hg & G & £) HΦ".
  iApply wp_lift_base_step; auto.
  iIntros (σ1 stepcnt κ κs n) "[Hσ Ht]". heap_split.
  iMod (bytes_ctx_cell_read_begin_guarded with "£ Guard HP Hp Hg G HB")
    as (i bs v) "([%Hdec %Hfv] & %Hrange & HB & Tok)"; [done..|].
  have Hlen := decode_value_length _ _ _ Hdec.
  have Hrange' := phys_rel_mem_range _ _ _ _ _ _ Hr Hrange.
  iApply fupd_mask_intro; first set_solver. iIntros "Hclose". iSplit.
  { iPureIntro. eexists _, _, _, _. by eapply LoadNa1S. }
  iNext; iIntros (e2 σ2 efs Hstep); inv_head_step. iMod "Hclose" as "_".
  iMod (time_interp_step with "Ht") as "$". iIntros "credit !>".
  iSplitR "HΦ Tok credit".
  { iExists hF. rewrite -Hlen. iFrame. iPureIntro. split.
    - by eapply phys_rel_mem_alter.
    - eapply heap_freeable_rel_dom; [|done]. intros ?. by rewrite is_Some_mem_alter. }
  iSplit; last done.
  clear dependent σ1 σL σB hF. iApply wp_lift_atomic_base_step_no_fork; auto.
  iIntros (σ1 stepcnt' κ' κs' n') "[Hσ Ht]".
  iMod (time_interp_step with "Ht") as "$". heap_split.
  iMod (bytes_ctx_read_end_guarded with "HB Tok") as "(%Hrange & HB & G)".
  iMod (lc_fupd_elim_later with "credit G") as "G".
  have Hrange' := phys_rel_mem_range _ _ _ _ _ _ Hr Hrange.
  iModIntro; iSplit.
  { iPureIntro. eexists _, _, _, _. by eapply LoadNa2S. }
  iNext. iIntros (e2 σ2 efs Hstep) "credit2 !>"; inv_head_step.
  match goal with H : mem_range _ _ _ ?bs' |- _ =>
    have Heq := mem_range_det _ _ _ _ _ _ Hrange' H ltac:(lia) end. subst.
  match goal with H : decode_value _ _ = Some _ |- _ => rewrite Hdec in H; simplify_eq end.
  iSplit; [done|]. iSplitR "HΦ G".
  { iExists hF. rewrite -Hlen. iFrame. iPureIntro. split.
    - by eapply phys_rel_mem_alter.
    - eapply heap_freeable_rel_dom; [|done]. intros ?. by rewrite is_Some_mem_alter. }
  iApply "HΦ". by iFrame.
Qed.

(** A non-atomic write of a plain sub-value through a cell (as for [borrow_mut] of a [PCell]
    behind a shared reference, and for writes through a [&mut] into its contents), with the
    permission. The fancy value of [g] is updated at [o'] ([fv_upd]). *)
Lemma wp_pcell_store_na_sub E l0 g0 m0 cs0 g o m cs fv o' m' fvs fvn e v G P d :
  ↑naN ⊆ E → IntoVal e (MLitV v) → fv_sub m fv o' m' fvs → fv_cells fvs = [] →
  fv_upd m fv o' m' (fv_lift v) fvn → mty_wf m' → val_wf m' v →
  {{{ (G &&{↑naN; d}&&> P) ∗ □ (P -∗ loc_side l0 g0 m0 cs0 ∗ (loc_side l0 g0 m0 cs0 -∗ P)) ∗
      gpath g0 g o ∗ greg g m cs ∗ G ∗ gdyn g fv ∗ £(2*d) }}}
    Store Na1Ord m' (Lit $ LitLoc (l0 +ₗ (o + o')%nat)) e @ E
  {{{ RET LitV LitPoison; G ∗ gdyn g fvn }}}.
Proof.
  iIntros (? <- Hsub Hplain Hupd Hm Hwf Φ) "(#Guard & #HP & #Hp & #Hg & G & Hgd & £) HΦ".
  iApply wp_lift_base_step; auto.
  iIntros (σ1 stepcnt κ κs n) "[Hσ Ht]". heap_split.
  iMod (bytes_ctx_cell_write_begin with "£ Guard HP Hp Hg G Hgd HB")
    as (bs) "([%Hrange %Hlen] & HB & Tok)"; [done..|].
  have Hrange' := phys_rel_mem_range _ _ _ _ _ _ Hr Hrange.
  iApply fupd_mask_intro; first set_solver. iIntros "Hclose". iSplit.
  { iPureIntro. eexists _, _, _, _. eapply StoreNa1S; eauto. }
  iNext; iIntros (e2 σ2 efs Hstep); inv_head_step. iMod "Hclose" as "_".
  iMod (time_interp_step with "Ht") as "$". iIntros "credit !>".
  iSplitR "HΦ Tok credit".
  { iExists hF. rewrite -Hlen. iFrame. iPureIntro. split.
    - by eapply phys_rel_mem_alter.
    - eapply heap_freeable_rel_dom; [|done]. intros ?. by rewrite is_Some_mem_alter. }
  iSplit; last done.
  clear dependent σ1 σL σB hF. iApply wp_lift_atomic_base_step_no_fork; auto.
  iIntros (σ1 stepcnt' κ' κs' n') "[Hσ Ht]".
  iMod (time_interp_step with "Ht") as "$". heap_split.
  match goal with H : val_wf m' ?w |- _ => rename w into v end.
  iMod (bytes_ctx_cell_write_end _ _ _ _ _ _ _ _ _ _ _ (encode_value m' v) v fvn with "Hg HB Tok")
    as (bs2) "([%Hrange2 %Hlen2] & HB & Hgd & G)"; [done..|by apply decode_encode_value|].
  iMod (lc_fupd_elim_later with "credit G") as "G".
  rewrite shift_loc_assoc_nat in Hrange2 |- *.
  have Hlen' : length (@encode_value val m' v) = length bs2 by rewrite length_encode_value.
  have Hrange' := phys_rel_mem_range _ _ _ _ _ _ Hr Hrange2.
  iModIntro; iSplit.
  { iPureIntro. eexists _, _, _, _. eapply StoreNa2S; eauto. }
  iNext. iIntros (e2 σ2 efs Hstep) "credit2 !>"; inv_head_step.
  iSplit; [done|]. iSplitR "HΦ G Hgd".
  { iExists hF. iFrame. iPureIntro. split.
    - by eapply phys_rel_mem_write.
    - eapply heap_freeable_rel_dom; [|done]. intros ?. simpl.
      by rewrite (is_Some_mem_write _ _ _ _ _ _ Hrange' Hlen'). }
  iApply "HΦ". by iFrame.
Qed.

(** An atomic write of a plain sub-value through a cell: both phases of the cell write
    happen in the single step. *)
Lemma wp_pcell_store_sc_sub E l0 g0 m0 cs0 g o m cs fv o' m' fvs fvn e v G P d :
  ↑naN ⊆ E → IntoVal e (MLitV v) → fv_sub m fv o' m' fvs → fv_cells fvs = [] →
  fv_upd m fv o' m' (fv_lift v) fvn → mty_wf m' → val_wf m' v →
  {{{ (G &&{↑naN; d}&&> P) ∗ □ (P -∗ loc_side l0 g0 m0 cs0 ∗ (loc_side l0 g0 m0 cs0 -∗ P)) ∗
      gpath g0 g o ∗ greg g m cs ∗ G ∗ gdyn g fv ∗ £(2*d) }}}
    Store ScOrd m' (Lit $ LitLoc (l0 +ₗ (o + o')%nat)) e @ E
  {{{ RET LitV LitPoison; G ∗ gdyn g fvn }}}.
Proof.
  iIntros (? <- Hsub Hplain Hupd Hm Hwf Φ) "(#Guard & #HP & #Hp & #Hg & G & Hgd & £) HΦ".
  iApply wp_lift_atomic_base_step_no_fork; auto.
  iIntros (σ1 stepcnt κ κs n') "[Hσ Ht]". heap_split.
  iMod (bytes_ctx_cell_write_begin with "£ Guard HP Hp Hg G Hgd HB")
    as (bs) "([%Hrange %Hlen] & HB & Tok)"; [done..|].
  iMod (bytes_ctx_cell_write_end _ _ _ _ _ _ _ _ _ _ _ (encode_value m' v) v fvn with "Hg HB Tok")
    as (bs2) "(_ & HB & Hgd & G)"; [done..|by apply decode_encode_value|].
  rewrite shift_loc_assoc_nat.
  have Heq : mem_write (l0 +ₗ (o + o')%nat) (@encode_value val m' v)
      (mem_alter (λ _, WSt) (l0 +ₗ (o + o')%nat) (mty_size m') σB) =
    mem_write (l0 +ₗ (o + o')%nat) (encode_value m' v) σB.
  { have := mem_alter_mem_write (λ _, WSt) (l0 +ₗ (o + o')%nat) (@encode_value val m' v) σB.
    by rewrite length_encode_value. }
  rewrite Heq.
  have Hlen' : length (@encode_value val m' v) = length bs by rewrite length_encode_value.
  have Hrange' := phys_rel_mem_range _ _ _ _ _ _ Hr Hrange.
  iModIntro. iSplit. { iPureIntro. eexists _, _, _, _. eapply StoreScS; eauto. }
  iNext; iIntros (e2 σ2 efs Hstep) "credit"; inv_head_step.
  iMod (time_interp_step with "Ht") as "$". iModIntro. iSplit; [done|].
  iSplitR "HΦ G Hgd".
  { iExists hF. iFrame. iPureIntro. split.
    - by eapply phys_rel_mem_write.
    - eapply heap_freeable_rel_dom; [|done]. intros ?. simpl.
      by rewrite (is_Some_mem_write _ _ _ _ _ _ Hrange' Hlen'). }
  iApply "HΦ". by iFrame.
Qed.

(** A verbatim copy of plain bytes [bs2] (that decode to [v] at [m']) into a plain
    sub-value through a cell. *)
Lemma wp_pcell_memcopy_into_sub E l0 g0 m0 cs0 g o m cs fv o' m' fvs fvn l2 bs2 v G P d :
  ↑naN ⊆ E → fv_sub m fv o' m' fvs → fv_cells fvs = [] →
  fv_upd m fv o' m' (fv_lift v) fvn → decode_value m' bs2 = Some v →
  {{{ (G &&{↑naN; d}&&> P) ∗ □ (P -∗ loc_side l0 g0 m0 cs0 ∗ (loc_side l0 g0 m0 cs0 -∗ P)) ∗
      gpath g0 g o ∗ greg g m cs ∗ G ∗ gdyn g fv ∗ £(2*d) ∗ ▷ l2 ↦b bs2 }}}
    MemCopy Na1Ord (mty_size m') (Lit $ LitLoc (l0 +ₗ (o + o')%nat)) (Lit $ LitLoc l2) @ E
  {{{ RET LitV LitPoison; G ∗ gdyn g fvn ∗ l2 ↦b bs2 }}}.
Proof.
  iIntros (? Hsub Hplain Hupd Hdec Φ) "(#Guard & #HP & #Hp & #Hg & G & Hgd & £ & >Hbs2) HΦ".
  have Hlen2 := decode_value_length _ _ _ Hdec.
  iApply wp_lift_base_step; auto.
  iIntros (σ1 stepcnt κ κs n') "[Hσ Ht]". heap_split.
  iMod (bytes_ctx_read_begin with "HB Hbs2") as "(%Hrange2 & HB & Hbs2)".
  have Hrange2' := phys_rel_mem_range _ _ _ _ _ _ Hr Hrange2.
  have Hr2 := phys_rel_mem_alter _ ls_inc _ _ _ _ _ Hr Hrange2.
  iMod (bytes_ctx_cell_write_begin with "£ Guard HP Hp Hg G Hgd HB")
    as (bs) "([%Hrange1 %Hlen] & HB & Tok)"; [done..|].
  have Hrange1' := mem_range_rst0_inc _ _ _ _ _ (phys_rel_mem_range _ _ _ _ _ _ Hr2 Hrange1).
  have Hr1 := phys_rel_mem_alter _ (λ _, WSt) _ _ _ _ _ Hr2 Hrange1.
  iApply fupd_mask_intro; first set_solver. iIntros "Hclose". iSplit.
  { iPureIntro. eexists _, _, _, _. eapply MemCopyNa1S; eauto. }
  iNext; iIntros (e2 σ2 efs Hstep); inv_head_step. iMod "Hclose" as "_".
  iMod (time_interp_step with "Ht") as "$". iIntros "credit !>".
  iSplitR "HΦ Tok Hbs2 credit".
  { rewrite Hlen Hlen2 in Hr1. iExists hF. rewrite Hlen2. iFrame. iPureIntro. split; [done|].
    eapply heap_freeable_rel_dom; [|done]. intros ?. by rewrite !is_Some_mem_alter. }
  iSplit; last done.
  clear dependent σ1 σL σB hF. iApply wp_lift_atomic_base_step_no_fork; auto.
  iIntros (σ1 stepcnt' κ' κs' n'') "[Hσ Ht]".
  iMod (time_interp_step with "Ht") as "$". heap_split.
  iMod (bytes_ctx_read_end with "HB Hbs2") as "(%Hrange2 & HB & Hbs2)".
  have Hrange2' := phys_rel_mem_range _ _ _ _ _ _ Hr Hrange2.
  have Hr2 := phys_rel_mem_alter _ ls_dec _ _ _ _ _ Hr Hrange2.
  iMod (bytes_ctx_cell_write_end _ _ _ _ _ _ _ _ _ _ _ bs2 v fvn with "Hg HB Tok")
    as (bsw) "([%Hrange1 %Hlen1] & HB & Hgd & G)"; [done..|].
  iMod (lc_fupd_elim_later with "credit G") as "G".
  rewrite shift_loc_assoc_nat in Hrange1 |- *.
  have Hrange1' := mem_range_wst_dec _ _ _ _ _ (phys_rel_mem_range _ _ _ _ _ _ Hr2 Hrange1).
  have Hlen' : length bs2 = length bsw by lia.
  have Hr1 := phys_rel_mem_write _ _ _ _ _ _ bs2 Hr2 Hrange1 Hlen'.
  iModIntro; iSplit.
  { iPureIntro. eexists _, _, _, _. eapply MemCopyNa2S; eauto. }
  iNext. iIntros (e2 σ2 efs Hstep) "credit2 !>"; inv_head_step.
  match goal with H : mem_range is_reading_S _ l2 ?bs' |- _ =>
    have Heq := mem_range_det _ _ _ _ _ _ Hrange2' H ltac:(lia) end. subst.
  iSplit; [done|]. iSplitR "HΦ G Hgd Hbs2".
  { rewrite Hlen2 in Hr1. iExists hF. rewrite Hlen2. iFrame. iPureIntro. split; [done|].
    eapply heap_freeable_rel_dom; [|done]. intros ?.
    simpl. rewrite is_Some_mem_write'; [by rewrite !is_Some_mem_alter|].
    intros i Hi. rewrite is_Some_mem_alter.
    destruct (mem_range_lookup_1 _ _ _ _ i Hrange1') as (?&?&Hl&_); [lia|]. eexists. exact Hl. }
  iApply "HΦ". by iFrame.
Qed.

(** Whole-value accesses through a cell that is not nested ([g] is its own root), for a
    group whose fancy value has no cells. *)
Lemma wp_pcell_load_sc_guarded E l g m cs fv G P d :
  ↑naN ⊆ E → fv_cells fv = [] →
  {{{ (G &&{↑naN; d}&&> P) ∗
      □ (P -∗ (loc_side l g m cs ∗ gdyn g fv) ∗ (loc_side l g m cs -∗ gdyn g fv -∗ P)) ∗
      greg g m cs ∗ G ∗ £d }}}
    Load ScOrd m (Lit $ LitLoc l) @ E
  {{{ v, RET MLitV v; G ∗ ⌜fv = fv_lift v⌝ }}}.
Proof.
  iIntros (? Hc Φ) "(#Guard & #HP & #Hg & G & £) HΦ".
  have -> : (Lit $ LitLoc l) = (Lit $ LitLoc (l +ₗ (0 + 0)%nat)) by rewrite /= shift_loc_0_nat.
  iApply (wp_pcell_load_sc_sub E l g m cs g 0 m cs fv 0 m fv with "[$Guard $HP $Hg $G $£]");
    [done|constructor|done| |done]. iApply gpath_refl.
Qed.

Lemma wp_pcell_load_na_guarded E l g m cs fv G P d :
  ↑naN ⊆ E → fv_cells fv = [] →
  {{{ (G &&{↑naN; d}&&> P) ∗
      □ (P -∗ (loc_side l g m cs ∗ gdyn g fv) ∗ (loc_side l g m cs -∗ gdyn g fv -∗ P)) ∗
      greg g m cs ∗ G ∗ £(2*d) }}}
    Load Na1Ord m (Lit $ LitLoc l) @ E
  {{{ v, RET MLitV v; G ∗ ⌜fv = fv_lift v⌝ }}}.
Proof.
  iIntros (? Hc Φ) "(#Guard & #HP & #Hg & G & £) HΦ".
  have -> : (Lit $ LitLoc l) = (Lit $ LitLoc (l +ₗ (0 + 0)%nat)) by rewrite /= shift_loc_0_nat.
  iApply (wp_pcell_load_na_sub E l g m cs g 0 m cs fv 0 m fv with "[$Guard $HP $Hg $G $£]");
    [done|constructor|done| |done]. iApply gpath_refl.
Qed.

Lemma wp_pcell_store_na_guarded E l g m cs fv e v G P d :
  ↑naN ⊆ E → IntoVal e (MLitV v) → fv_cells fv = [] → mty_wf m → val_wf m v →
  {{{ (G &&{↑naN; d}&&> P) ∗ □ (P -∗ loc_side l g m cs ∗ (loc_side l g m cs -∗ P)) ∗
      greg g m cs ∗ G ∗ gdyn g fv ∗ £(2*d) }}}
    Store Na1Ord m (Lit $ LitLoc l) e @ E
  {{{ RET LitV LitPoison; G ∗ gdyn g (fv_lift v) }}}.
Proof.
  iIntros (? ? Hc Hm Hwf Φ) "(#Guard & #HP & #Hg & G & Hgd & £) HΦ".
  have -> : (Lit $ LitLoc l) = (Lit $ LitLoc (l +ₗ (0 + 0)%nat)) by rewrite /= shift_loc_0_nat.
  iApply (wp_pcell_store_na_sub E l g m cs g 0 m cs fv 0 m fv with "[$Guard $HP $Hg $G $Hgd $£]");
    try first [done|apply fv_sub_here|apply fv_upd_here]. iApply gpath_refl.
Qed.

Lemma wp_pcell_store_sc_guarded E l g m cs fv e v G P d :
  ↑naN ⊆ E → IntoVal e (MLitV v) → fv_cells fv = [] → mty_wf m → val_wf m v →
  {{{ (G &&{↑naN; d}&&> P) ∗ □ (P -∗ loc_side l g m cs ∗ (loc_side l g m cs -∗ P)) ∗
      greg g m cs ∗ G ∗ gdyn g fv ∗ £(2*d) }}}
    Store ScOrd m (Lit $ LitLoc l) e @ E
  {{{ RET LitV LitPoison; G ∗ gdyn g (fv_lift v) }}}.
Proof.
  iIntros (? ? Hc Hm Hwf Φ) "(#Guard & #HP & #Hg & G & Hgd & £) HΦ".
  have -> : (Lit $ LitLoc l) = (Lit $ LitLoc (l +ₗ (0 + 0)%nat)) by rewrite /= shift_loc_0_nat.
  iApply (wp_pcell_store_sc_sub E l g m cs g 0 m cs fv 0 m fv with "[$Guard $HP $Hg $G $Hgd $£]");
    try first [done|apply fv_sub_here|apply fv_upd_here]. iApply gpath_refl.
Qed.

(** Recording that a group [g] is nested at [o] in a live group [g0] (an update of the byte
    context, before any step). *)
Lemma wp_pcell_gnest E e g0 m0 cs0 fv0 o m g Φ :
  TCEq (to_val e) None → fv_sub m0 fv0 o m (FVCell g) →
  greg g0 m0 cs0 -∗ gdyn g0 fv0 -∗ (gdyn g0 fv0 -∗ gnest g0 g o -∗ WP e @ E {{ Φ }}) -∗
  WP e @ E {{ Φ }}.
Proof.
  iIntros (Hv Hsub) "Hg Hgd Hwp". iApply wp_bytes_ctx_pre. iIntros (σB) "HB".
  iMod (bytes_ctx_gnest with "HB Hg Hgd") as "(HB & Hgd & Hn)"; [done|].
  iModIntro. iFrame "HB". iApply ("Hwp" with "Hgd Hn").
Qed.

End lifting.
