From stdpp Require Import gmap.
From iris.program_logic Require Import adequacy.
From lrust.lang Require Import tactics.
Set Default Proof Using "Type".

Inductive access_kind : Type := ReadAcc | WriteAcc | FreeAcc.

(* This is a crucial definition; if we forget to sync it with base_step,
   the results proven here are worthless. *)
Inductive next_access_head : expr → state → access_kind * order → loc → Prop :=
| Access_free n l σ i :
    0 ≤ i < n →
    next_access_head (Free (Lit $ LitInt n) (Lit $ LitLoc l))
                     σ (FreeAcc, Na2Ord) (l +ₗ i)
(* Typed accesses: to every byte of the range *)
| Access_load ord m l (i : nat) σ :
    (i < mty_size m)%nat →
    next_access_head (Load ord m (Lit $ LitLoc l)) σ (ReadAcc, ord) (l +ₗ i)
| Access_store ord m l e (i : nat) σ :
    is_Some (to_val e) → (i < mty_size m)%nat →
    next_access_head (Store ord m (Lit $ LitLoc l) e) σ (WriteAcc, ord) (l +ₗ i)
| Access_memcopy_dst ord n l1 l2 (i : nat) σ :
    (i < n)%nat →
    next_access_head (MemCopy ord n (Lit $ LitLoc l1) (Lit $ LitLoc l2)) σ (WriteAcc, ord) (l1 +ₗ i)
| Access_memcopy_src ord n l1 l2 (i : nat) σ :
    (i < n)%nat →
    next_access_head (MemCopy ord n (Lit $ LitLoc l1) (Lit $ LitLoc l2)) σ (ReadAcc, ord) (l2 +ₗ i)
(* A typed CAS reads every byte of the range if the comparison fails, and writes every byte
   if it succeeds. The comparison depends only on the bytes. *)
| Access_mcas_fail m l (i : nat) e1 v1 e2 v2 bs v σ :
    to_val e1 = Some (MLitV v1) → to_val e2 = Some (MLitV v2) → (i < mty_size m)%nat →
    mem_range (λ _, True) σ.1 l bs → length bs = mty_size m → decode_value m bs = Some v →
    v ≠ v1 →
    next_access_head (MCAS m (Lit $ LitLoc l) e1 e2) σ (ReadAcc, ScOrd) (l +ₗ i)
| Access_mcas_suc m l (i : nat) e1 v1 e2 v2 bs σ :
    to_val e1 = Some (MLitV v1) → to_val e2 = Some (MLitV v2) → (i < mty_size m)%nat →
    mem_range (λ _, True) σ.1 l bs → length bs = mty_size m → decode_value m bs = Some v1 →
    next_access_head (MCAS m (Lit $ LitLoc l) e1 e2) σ (WriteAcc, ScOrd) (l +ₗ i).

(* Some sanity checks to make sure the definition above is not entirely insensible. *)
Goal ∀ e1 e2 σ, base_reducible (Free e1 e2) σ →
              ∃ a l, next_access_head (Free e1 e2) σ a l.
Proof.
  intros ?? σ (?&?&?&?&?). inversion H; do 2 eexists; eapply Access_free; done.
Qed.

Goal ∀ o m e σ, base_reducible (Load o m e) σ → (0 < mty_size m)%nat →
              ∃ a l, next_access_head (Load o m e) σ a l.
Proof.
  intros ??? σ (?&?&?&?&?) ?. inversion H; do 2 eexists; by eapply (Access_load _ _ _ 0).
Qed.
Goal ∀ o m e1 e2 σ, base_reducible (Store o m e1 e2) σ → (0 < mty_size m)%nat →
              ∃ a l, next_access_head (Store o m e1 e2) σ a l.
Proof.
  intros ???? σ (?&?&?&?&?) ?. inversion H; do 2 eexists;
    (eapply (Access_store _ _ _ _ 0); [by eexists|done]).
Qed.
Goal ∀ o n e1 e2 σ, base_reducible (MemCopy o n e1 e2) σ → (0 < n)%nat →
              ∃ a l, next_access_head (MemCopy o n e1 e2) σ a l.
Proof.
  intros ???? σ (?&?&?&?&?) ?. inversion H; do 2 eexists; by eapply (Access_memcopy_dst _ _ _ _ 0).
Qed.
Goal ∀ m e0 e1 e2 σ, base_reducible (MCAS m e0 e1 e2) σ → (0 < mty_size m)%nat →
              ∃ a l, next_access_head (MCAS m e0 e1 e2) σ a l.
Proof.
  intros ???? σ (?&?&?&?&H) ?. inversion H; subst; do 2 eexists.
  - eapply (Access_mcas_fail _ _ 0); try done. eapply mem_range_impl; [|done]. done.
  - eapply (Access_mcas_suc _ _ 0); try done. eapply mem_range_impl; [|done]. done.
  - eapply (Access_mcas_suc _ _ 0); try done. eapply mem_range_impl; [|done]. done.
Qed.

Definition next_access_thread (e: expr) (σ : state)
           (a : access_kind * order) (l : loc) : Prop :=
  ∃ K e', next_access_head e' σ a l ∧ e = fill K e'.

Definition next_accesses_threadpool (el: list expr) (σ : state)
           (a1 a2 : access_kind * order) (l : loc): Prop :=
  ∃ t1 e1 t2 e2 t3, el = t1 ++ e1 :: t2 ++ e2 :: t3 ∧
                    next_access_thread e1 σ a1 l ∧ next_access_thread e2 σ a2 l.

Definition nonracing_accesses (a1 a2 : access_kind * order) : Prop :=
  match a1, a2 with
  | (_, ScOrd), (_, ScOrd) => True
  | (ReadAcc, _), (ReadAcc, _) => True
  | _, _ => False
  end.

Definition nonracing_threadpool (el : list expr) (σ : state) : Prop :=
  ∀ l a1 a2, next_accesses_threadpool el σ a1 a2 l →
             nonracing_accesses a1 a2.

Lemma next_access_head_reductible_ctx e σ σ' a l K :
  next_access_head e σ' a l → reducible (fill K e) σ → base_reducible e σ.
Proof.
  intros Hhead Hred. apply prim_base_reducible.
  - eapply (reducible_fill_inv (K:=ectx_language.fill K)), Hred. destruct Hhead; eauto.
  - apply ectxi_language_sub_redexes_are_values. intros [] ? ->; inversion Hhead; eauto.
Qed.

Definition head_reduce_not_to_stuck (e : expr) (σ : state) :=
  ∀ κ e' σ' efs, ectx_language.base_step e σ κ e' σ' efs → e' ≠ App (Lit $ LitInt 0) [].

Lemma next_access_base_reducible_state e σ a l :
  next_access_head e σ a l → base_reducible e σ →
  head_reduce_not_to_stuck e σ →
  match a with
  | (ReadAcc, (ScOrd | Na1Ord)) => ∃ v n, σ.1 !! l = Some (RSt n, v)
  | (ReadAcc, Na2Ord) => ∃ v n, σ.1 !! l = Some (RSt (S n), v)
  | (WriteAcc, (ScOrd | Na1Ord)) => ∃ v, σ.1 !! l = Some (RSt 0, v)
  | (WriteAcc, Na2Ord) => ∃ v, σ.1 !! l = Some (WSt, v)
  | (FreeAcc, _) => ∃ v ls, σ.1 !! l = Some (ls, v)
  end.
Proof.
  intros Ha (κ&e'&σ'&ef&Hstep) Hrednonstuck. destruct Ha; inv_head_step; eauto;
    try match goal with
    | H : mem_range ?P _ ?l ?bs |- context [?l +ₗ Z.of_nat ?i] =>
        let ls := fresh "ls" in let b := fresh "b" in let Hl := fresh "Hl" in
        let HP := fresh "HP" in
        destruct (mem_range_lookup_1 _ _ _ _ i H) as (ls & b & Hl & HP & _); [lia|];
        try unfold is_reading in HP; try unfold is_reading_S in HP; simpl in HP;
        repeat match type of HP with ∃ _, _ => destruct HP as [? HP] end;
        subst; by eauto
    end.
  - match goal with H : ∀ m, _ |- _ => destruct (H i) as [_ [[]?]] end; eauto.
  - exfalso. match goal with
      H1 : mem_range (λ _, True) _ _ ?bs1, H2 : mem_range is_reading _ _ ?bs2 |- _ =>
        have Heq := mem_range_det _ _ _ _ _ _ H1 H2 ltac:(lia) end.
    subst. congruence.
  - exfalso. eapply Hrednonstuck; last done. eapply MCasStuckS; done.
Qed.

(** An access needs its location to be allocated. *)
Lemma next_access_head_is_Some e σ0 σ a l :
  next_access_head e σ0 a l → base_reducible e σ → is_Some (σ.1 !! l).
Proof.
  intros Ha (κ&e'&σ'&ef&Hstep). destruct Ha; inv_head_step; eauto;
    try match goal with
    | H : mem_range ?P _ ?l ?bs |- context [?l +ₗ Z.of_nat ?i] =>
        let ls := fresh "ls" in let b := fresh "b" in let Hl := fresh "Hl" in
        destruct (mem_range_lookup_1 _ _ _ _ i H) as (ls & b & Hl & _); [lia|];
        by rewrite Hl
    end.
  match goal with H : ∀ m, _ |- _ => by apply (H i) end.
Qed.

(** Accesses that are not atomic do not depend on the state. *)
Lemma next_access_head_state_indep e σ σ' a l :
  next_access_head e σ a l → a.2 ≠ ScOrd → next_access_head e σ' a l.
Proof. destruct 1; simpl; intros ?; try done; by econstructor. Qed.

Lemma mem_range_true_bytes (σ σ' : state') l bs :
  mem_range (λ _, True) σ l bs → (∀ l', snd <$> σ !! l' = snd <$> σ' !! l') →
  mem_range (λ _, True) σ' l bs.
Proof.
  rewrite !mem_range_lookup. intros H Hσ i b Hb. destruct (H i b Hb) as (ls & Hl & _).
  specialize (Hσ (l +ₗ i)). rewrite Hl /= in Hσ.
  destruct (σ' !! (l +ₗ i)) as [[ls' b']|] eqn:Hl'; [|done]. injection Hσ as <-. by exists ls'.
Qed.

(** Accesses only depend on the bytes and the domain of the state, not on the lock
    states. *)
Lemma next_access_head_bytes e σ σ' a l :
  next_access_head e σ a l →
  (∀ l', snd <$> σ.1 !! l' = snd <$> σ'.1 !! l') →
  next_access_head e σ' a l.
Proof.
  intros Ha Hσ. assert (Hdom : ∀ l', σ.1 !! l' = None ↔ σ'.1 !! l' = None).
  { intros l'. specialize (Hσ l').
    by rewrite -(fmap_None snd (σ.1 !! l')) -(fmap_None snd (σ'.1 !! l')) Hσ. }
  destruct Ha as [| | | |
    |m l i e1 v1 e2 v2 bs v σ0 Hv1 Hv2 Hi Hbs Hlen Hd Hne
    |m l i e1 v1 e2 v2 bs σ0 Hv1 Hv2 Hi Hbs Hlen Hd].
  6: { eapply Access_mcas_fail; try done. by eapply mem_range_true_bytes. }
  6: { eapply Access_mcas_suc; try done. by eapply mem_range_true_bytes. }
  all: by constructor.
Qed.

Lemma lookup_mem_alter_snd f l n (σ : state') l' :
  snd <$> mem_alter f l n σ !! l' = snd <$> σ !! l'.
Proof.
  revert l. induction n as [|n IH]; intros l; simpl; [done|].
  destruct (decide (l = l')) as [<-|].
  - rewrite lookup_alter. rewrite -(IH (l +ₗ 1)). rewrite -option_fmap_compose. by apply option_fmap_ext.
  - by rewrite lookup_alter_ne.
Qed.

Lemma next_access_head_Na1Ord_bytes e1 e2 ef σ1 σ2 κ a l :
  next_access_head e1 σ1 (a, Na1Ord) l →
  base_step e1 σ1 κ e2 σ2 ef →
  ∀ l', snd <$> σ1.1 !! l' = snd <$> σ2.1 !! l'.
Proof.
  intros Ha Hstep l'. inversion Ha; subst; clear Ha; inv_head_step; simpl;
    rewrite ?lookup_mem_alter_snd //.
  all: match goal with |- context [<[?k := _]> _ !! ?l'] =>
    destruct (decide (k = l')) as [<-|];
      [rewrite lookup_insert; by simplify_map_eq|by rewrite lookup_insert_ne] end.
Qed.

(** After the second phase of a non-atomic write, the location is not locked. *)
Lemma next_access_head_Na2Ord_write_step e1 e2 ef σ1 σ2 κ l :
  next_access_head e1 σ1 (WriteAcc, Na2Ord) l →
  base_step e1 σ1 κ e2 σ2 ef →
  ∃ b, σ2.1 !! l = Some (RSt 0, b).
Proof.
  intros Ha Hstep. inversion Ha; subst; clear Ha; inv_head_step; simpl; eauto.
  - destruct (lookup_lt_is_Some_2 (@encode_value val m v) i) as [b Hb]; [by rewrite length_encode_value|].
    exists b. by apply lookup_mem_write_in.
  - destruct (lookup_lt_is_Some_2 bs2 i) as [b Hb]; [lia|].
    exists b. by apply lookup_mem_write_in.
Qed.

Lemma next_access_head_Na1Ord_step e1 e2 ef σ1 σ2 κ a l :
  next_access_head e1 σ1 (a, Na1Ord) l →
  base_step e1 σ1 κ e2 σ2 ef →
  next_access_head e2 σ2 (a, Na2Ord) l.
Proof.
  intros Ha Hstep. inversion Ha; subst; clear Ha; inv_head_step; econstructor;
    rewrite ?to_of_val; eauto.
Qed.

Lemma next_access_head_Na1Ord_concurent_step e1 e1' e2 e'f σ σ' κ a1 a2 l :
  next_access_head e1 σ (a1, Na1Ord) l →
  base_step e1 σ κ e1' σ' e'f →
  next_access_head e2 σ a2 l →
  next_access_head e2 σ' a2 l.
Proof.
  intros Ha1 Hstep Ha2. eapply next_access_head_bytes; [done|].
  by eapply next_access_head_Na1Ord_bytes.
Qed.

Lemma next_access_head_Free_concurent_step e1 e1' e2 e'f σ σ' κ o1 a2 l :
  next_access_head e1 σ (FreeAcc, o1) l → base_step e1 σ κ e1' σ' e'f →
  next_access_head e2 σ a2 l → base_reducible e2 σ' →
  False.
Proof.
  intros Ha1 Hstep Ha2 Hred2.
  assert (FREE : ∀ l n i, 0 ≤ i ∧ i < n → free_mem l (Z.to_nat n) σ.1 !! (l +ₗ i) = None).
  { clear. intros l n i Hi.
    replace n with (Z.of_nat (Z.to_nat n)) in Hi by (apply Z2Nat.id; lia).
    revert l i Hi. induction (Z.to_nat n) as [|? IH]=>/=l i Hi. lia.
    destruct (decide (i = 0)).
    - subst. by rewrite /shift_loc Z.add_0_r -surjective_pairing lookup_delete.
    - replace i with (1+(i-1)) by lia.
      rewrite lookup_delete_ne -shift_loc_assoc ?IH //. lia.
      destruct l; intros [= ?]. lia. }
  assert (FREE' : σ'.1 !! l = None).
  { inversion Ha1; clear Ha1; inv_head_step. auto. }
  destruct (next_access_head_is_Some _ _ _ _ _ Ha2 Hred2) as [? Hl].
  by rewrite FREE' in Hl.
Qed.

Lemma safe_step_not_reduce_to_stuck el σ K e e' σ' ef κ :
  (∀ el' σ' e', rtc erased_step (el, σ) (el', σ') →
                e' ∈ el' → to_val e' = None → reducible e' σ') →
  fill K e ∈ el → base_step e σ κ e' σ' ef → head_reduce_not_to_stuck e' σ'.
Proof.
  intros Hsafe Hi Hstep κ1 e1 σ1 ? Hstep1 Hstuck.
  cut (reducible (fill K e1) σ1).
  { subst. intros (?&?&?&?&?). by eapply stuck_irreducible. }
  destruct (elem_of_list_split _ _ Hi) as (?&?&->).
  eapply Hsafe; last by (apply: fill_not_val; subst).
  - eapply rtc_l, rtc_l, rtc_refl.
    + eexists. econstructor. done. done. econstructor; done.
    + eexists. econstructor. done. done. econstructor; done.
  - subst. set_solver+.
Qed.

(* TODO: Unify this and the above. *)
Lemma safe_not_reduce_to_stuck el σ K e :
  (∀ el' σ' e', rtc erased_step (el, σ) (el', σ') →
                e' ∈ el' → to_val e' = None → reducible e' σ') →
  fill K e ∈ el → head_reduce_not_to_stuck e σ.
Proof.
  intros Hsafe Hi κ e1 σ1 ? Hstep1 Hstuck.
  cut (reducible (fill K e1) σ1).
  { subst. intros (?&?&?&?&?). by eapply stuck_irreducible. }
  destruct (elem_of_list_split _ _ Hi) as (?&?&->).
  eapply Hsafe; last by (apply: fill_not_val; subst).
  - eapply rtc_l, rtc_refl.
    + eexists. econstructor. done. done. econstructor; done.
  - subst. set_solver+.
Qed.

Theorem safe_nonracing el σ :
  (∀ el' σ' e', rtc erased_step (el, σ) (el', σ') →
                e' ∈ el' → to_val e' = None → reducible e' σ') →
  nonracing_threadpool el σ.
Proof.
  intros Hsafe l a1 a2 (t1&?&t2&?&t3&->&(K1&e1&Ha1&->)&(K2&e2&Ha2&->)).

  assert (to_val e1 = None). by destruct Ha1.
  assert (Hrede1:base_reducible e1 σ).
  { eapply (next_access_head_reductible_ctx e1 σ σ a1 l K1), Hsafe, fill_not_val=>//.
    abstract set_solver. }
  assert (Hnse1:head_reduce_not_to_stuck e1 σ).
  { eapply safe_not_reduce_to_stuck with (K:=K1); first done. set_solver+. }
  assert (Hσe1:=next_access_base_reducible_state _ _ _ _ Ha1 Hrede1 Hnse1).
  destruct Hrede1 as (κ1'&e1'&σ1'&ef1&Hstep1). clear Hnse1.
  assert (Ha1' : a1.2 = Na1Ord → next_access_head e1' σ1' (a1.1, Na2Ord) l).
  { intros. eapply next_access_head_Na1Ord_step, Hstep1.
    by destruct a1; simpl in *; subst. }
  assert (Hrtc_step1:
    rtc erased_step (t1 ++ fill K1 e1 :: t2 ++ fill K2 e2 :: t3, σ)
        (t1 ++ fill K1 e1' :: t2 ++ fill K2 e2 :: t3 ++ ef1, σ1')).
  { eapply rtc_l, rtc_refl. eexists. eapply step_atomic, Ectx_step, Hstep1; try  done.
    by rewrite -assoc. }
  assert (Hrede1: a1.2 = Na1Ord → base_reducible e1' σ1').
  { destruct a1 as [a1 []]=>// _.
    eapply (next_access_head_reductible_ctx e1' σ1' σ1' (a1, Na2Ord) l K1), Hsafe,
           fill_not_val=>//.
    by auto. abstract set_solver. by destruct Hstep1; inversion Ha1. }
  assert (Hnse1: head_reduce_not_to_stuck e1' σ1').
  { eapply safe_step_not_reduce_to_stuck with (K:=K1); first done; last done. set_solver+. }

  assert (to_val e2 = None). by destruct Ha2.
  assert (Hrede2:base_reducible e2 σ).
  { eapply (next_access_head_reductible_ctx e2 σ σ a2 l K2), Hsafe, fill_not_val=>//.
    abstract set_solver. }
  assert (Hnse2:head_reduce_not_to_stuck e2 σ).
  { eapply safe_not_reduce_to_stuck with (K:=K2); first done. set_solver+. }
  assert (Hσe2:=next_access_base_reducible_state _ _ _ _ Ha2 Hrede2 Hnse2).
  destruct Hrede2 as (κ2'&e2'&σ2'&ef2&Hstep2).
  assert (Ha2' : a2.2 = Na1Ord → next_access_head e2' σ2' (a2.1, Na2Ord) l).
  { intros. eapply next_access_head_Na1Ord_step, Hstep2.
    by destruct a2; simpl in *; subst. }
  assert (Hrtc_step2:
    rtc erased_step (t1 ++ fill K1 e1 :: t2 ++ fill K2 e2 :: t3, σ)
        (t1 ++ fill K1 e1 :: t2 ++ fill K2 e2' :: t3 ++ ef2, σ2')).
  { eapply rtc_l, rtc_refl. rewrite app_comm_cons assoc. eexists.
    eapply step_atomic, Ectx_step, Hstep2; try done. by rewrite -assoc. }
  assert (Hrede2: a2.2 = Na1Ord → base_reducible e2' σ2').
  { destruct a2 as [a2 []]=>// _.
    eapply (next_access_head_reductible_ctx e2' σ2' σ2' (a2, Na2Ord) l K2), Hsafe,
           fill_not_val=>//.
    by auto. abstract set_solver. by destruct Hstep2; inversion Ha2. }
  assert (Hnse2':head_reduce_not_to_stuck e2' σ2').
  { eapply safe_step_not_reduce_to_stuck with (K:=K2); first done; last done. set_solver+. }

  assert (Ha1'2 : a1.2 = Na1Ord → next_access_head e2 σ1' a2 l).
  { intros HNa. eapply next_access_head_Na1Ord_concurent_step=>//.
    by rewrite <-HNa, <-surjective_pairing. }
  assert (Hrede1_2: base_reducible e2 σ1').
  { intros. eapply (next_access_head_reductible_ctx e2 σ1' σ  a2 l K2), Hsafe, fill_not_val=>//.
    abstract set_solver. }
  assert (Hnse1_2:head_reduce_not_to_stuck e2 σ1').
  { eapply safe_not_reduce_to_stuck with (K:=K2).
    - intros. eapply Hsafe. etrans; last done. done. done. done.
    - set_solver+. }
  assert (Hσe1'1:=
    λ Hord, next_access_base_reducible_state _ _ _ _ (Ha1' Hord) (Hrede1 Hord) Hnse1).
  assert (Hσe1'2:=
    λ Hord, next_access_base_reducible_state _ _ _ _ (Ha1'2 Hord) Hrede1_2 Hnse1_2).

  assert (Ha2'1 : a2.2 = Na1Ord → next_access_head e1 σ2' a1 l).
  { intros HNa. eapply next_access_head_Na1Ord_concurent_step=>//.
    by rewrite <-HNa, <-surjective_pairing. }
  assert (Hrede2_1: base_reducible e1 σ2').
  { intros. eapply (next_access_head_reductible_ctx e1 σ2' σ a1 l K1), Hsafe, fill_not_val=>//.
    abstract set_solver. }
  assert (Hnse2_1:head_reduce_not_to_stuck e1 σ2').
  { eapply safe_not_reduce_to_stuck with (K:=K1).
    - intros. eapply Hsafe. etrans; last done. done. done. done.
    - set_solver+. }
  assert (Hσe2'1:=
    λ Hord, next_access_base_reducible_state _ _ _ _ (Ha2'1 Hord) Hrede2_1 Hnse2_1).
  assert (Hσe2'2:=
    λ Hord, next_access_base_reducible_state _ _ _ _ (Ha2' Hord) (Hrede2 Hord) Hnse2').

  assert (a1.1 = FreeAcc → False).
  { destruct a1 as [[]?]; inversion 1.
    eauto using next_access_head_Free_concurent_step. }
  assert (a2.1 = FreeAcc → False).
  { destruct a2 as [[]?]; inversion 1.
    eauto using next_access_head_Free_concurent_step. }

  (* Two second phases of non-atomic writes: the first one unlocks the location,
     but the second one still needs it locked. *)
  assert (Hw1 : a1 = (WriteAcc, Na2Ord) → ∃ b, σ1'.1 !! l = Some (RSt 0, b)).
  { intros ->. by eapply next_access_head_Na2Ord_write_step. }
  assert (Hw2 : a2 = (WriteAcc, Na2Ord) → ∃ b, σ1'.1 !! l = Some (WSt, b)).
  { intros ->.
    have := next_access_base_reducible_state _ _ _ _
      (next_access_head_state_indep _ _ σ1' _ _ Ha2 ltac:(done)) Hrede1_2 Hnse1_2.
    done. }

  clear Ha1 Ha2 Ha1' Ha2' Ha1'2 Ha2'1.
  destruct a1 as [[] []], a2 as [[] []]=>//=; simpl in *;
    repeat match goal with
    | H : _ = Na1Ord → _ |- _ => specialize (H (eq_refl Na1Ord)) || clear H
    | H : (WriteAcc, Na2Ord) = (WriteAcc, Na2Ord) → _ |- _ => specialize (H eq_refl)
    | H : _ = (WriteAcc, Na2Ord) → _ |- _ => clear H
    | H : False |- _ => destruct H
    | H : ∃ _, _ |- _ => destruct H
    end;
    try congruence.
Qed.

Corollary adequate_nonracing e1 t2 σ1 σ2 φ :
  adequate NotStuck e1 σ1 φ →
  rtc erased_step ([e1], σ1) (t2, σ2) →
  nonracing_threadpool t2 σ2.
Proof.
  intros [_ Had] Hrtc. apply safe_nonracing. intros el' σ' e' ?? He'.
  edestruct (Had el' σ' e') as [He''|]; try done. etrans; eassumption.
  rewrite /language.to_val /= He' in He''. by edestruct @is_Some_None.
Qed.
