From iris.proofmode Require Import coq_tactics reduction.
From iris.proofmode Require Export tactics.
From iris.program_logic Require Export weakestpre.
From iris.program_logic Require Import lifting.
From lrust.lang Require Export tactics lifting.
From guarding Require Import guard.
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
  envs_entails Δ' (WP fill K (MLit (VBool (bool_decide (l1 = l2)))) @ E {{ Φ }}) →
  envs_entails Δ (WP fill K (BinOp EqOp (MLit (VPtr l1)) (MLit (VPtr l2))) @ E {{ Φ }}).
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
  | |- envs_entails _ (wp ?s ?E ?e ?Q) => first
    [ reshape_expr e ltac:(fun K e' =>
        match e' with
        | efoc => unify e' efoc; wp_bind_core K
        end)
    | fail "wp_bind: cannot find" efoc "in" e ]
  | _ => fail "wp_bind: not a 'wp'"
  end.

Section heap.
Context `{!lrustGS Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types Δ : envs (uPredI (iResUR Σ)).

Lemma tac_wp_nd_int `{!lrustGS Σ} K Δ Δ' E Φ :
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  (∀z, envs_entails Δ' (WP fill K (MLit (VInt z)) @ E {{ Φ }})) →
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

(** * Reading discriminants

[GetDiscr (MEnum vars d sz al) #l] runs the discriminator [d] at [l] ([discr_expr]): a
non-atomic typed load of the integer of each branch on the path. [wp_get_discr_gen] is the
general rule, for a reader [rd] of the integers whose loads are given by [R] ([R n] for [n]
more loads at most); [wp_get_discr] is the rule for owned bytes, in chunks, and
[wp_get_discr_guarded] for guarded ones. *)
Section get_discr.
  Context `{!lrustGS Σ}.

  Lemma discr_expr_closed d l : is_closed [] (discr_expr d l).
  Proof.
    induction d as [t| |off it fb ch IHfb IH] using discr_ind'; simpl; [done|done|].
    rewrite !andb_True. split; [|done].
    induction IH as [|[[lo hi] c] ch Hc _ IHch]; simpl; [by apply is_closed_weaken_nil|].
    rewrite !andb_True. split_and!; try done; by apply is_closed_weaken_nil.
  Qed.

  (** The selection of a child, once the integer [z] is read. *)
  Definition discr_test_at (z lo hi : Z) : expr :=
    Case (BinOp LeOp (MLit (VInt lo)) (MLit (VInt z)))
      [MLit (VBool false); BinOp LeOp (MLit (VInt z)) (MLit (VInt (hi - 1)))].
  Fixpoint discr_sel (z : Z) (ch : list ((Z * Z) * discr)) (fb : discr) (l : loc) : expr :=
    match ch with
    | [] => discr_expr fb l
    | ((lo, hi), c) :: ch => Case (discr_test_at z lo hi) [discr_sel z ch fb l; discr_expr c l]
    end.

  Lemma subst_discr_sel (z : Z) (ch : list ((Z * Z) * discr)) fb l :
    subst "z" (MLit (VInt z))
      ((fix go ch := match ch with
        | [] => discr_expr fb l
        | ((lo, hi), c) :: ch => Case (discr_test lo hi) [go ch; discr_expr c l]
        end) ch) = discr_sel z ch fb l.
  Proof.
    induction ch as [|[[lo hi] c] ch IH]; simpl; [by rewrite is_closed_nil_subst; [|apply discr_expr_closed]|].
    rewrite -IH. rewrite (_ : ∀ e el, subst "z" (MLit (VInt z)) (Case e el) =
      Case (subst "z" (MLit (VInt z)) e) (map (subst "z" (MLit (VInt z))) el)); [|done].
    rewrite /= (is_closed_nil_subst (discr_expr c l)); [done|apply discr_expr_closed].
  Qed.

  Lemma wp_discr_sel E (z : Z) (ch : list ((Z * Z) * discr)) fb l Φ :
    WP (match list_find (λ c, (c.1.1 ≤ z < c.1.2)%Z) ch with
        | Some (_, (_, c)) => discr_expr c l | None => discr_expr fb l end) @ E {{ Φ }} -∗
    WP discr_sel z ch fb l @ E {{ Φ }}.
  Proof.
    induction ch as [|[[lo hi] c] ch IH]; simpl; [by iIntros|]. iIntros "H".
    wp_bind (Case (discr_test_at _ _ _) _). rewrite /discr_test_at.
    wp_bind (BinOp _ _ _). wp_op. case_bool_decide.
    - wp_case. wp_op. case_bool_decide; wp_case.
      + rewrite decide_True; [done|lia].
      + rewrite decide_False; [|lia]. iApply IH.
        by destruct (list_find _ ch) as [[? [? ?]]|].
    - wp_case. wp_case. rewrite decide_False; [|lia]. iApply IH.
      by destruct (list_find _ ch) as [[? [? ?]]|].
  Qed.

  Lemma discr_depth_branch off it fb ch k r c :
    ch !! k = Some (r, c) →
    (discr_depth fb < discr_depth (DBranch off it fb ch) ∧
     discr_depth c < discr_depth (DBranch off it fb ch))%nat.
  Proof.
    simpl. intros Hk. split; [lia|].
    cut (discr_depth c ≤ (fix go ch : nat := match ch with [] => 0%nat
      | (_, c) :: ch => Nat.max (discr_depth c) (go ch) end) ch)%nat; [lia|].
    revert k Hk. induction ch as [|[r' c'] ch IH]; intros [|k] Hk; simplify_eq/=; [lia|].
    specialize (IH k Hk). lia.
  Qed.

  Lemma wp_get_discr_gen E vars d sz al l (rd : nat → IntType → option Z)
      (R : nat → iProp Σ) t n Φ :
    discr_eval rd d = Some t → (discr_depth d ≤ n)%nat →
    □ (∀ off it z k, ⌜rd off it = Some z⌝ -∗ R (S k) -∗
        WP Load Na1Ord (MInt it) (MLit (VPtr (l +ₗ off))) @ E {{ v, ⌜v = MLitV (VInt z)⌝ ∗ R k }}) -∗
    R n -∗ (∀ k, R k -∗ Φ (MLitV (VInt t))) -∗
    WP GetDiscr (MEnum vars d sz al) (MLit (VPtr l)) @ E {{ Φ }}.
  Proof.
    iIntros (Hd Hn) "#Hload HR HΦ". wp_pure (GetDiscr _ _).
    iInduction d as [t'| |off it fb ch] "IH" using discr_ind' forall (n Hd Hn).
    - simplify_eq/=. wp_value_head. by iApply "HΦ".
    - done.
    - rewrite discr_eval_branch in Hd. destruct (rd off it) as [z|] eqn:Hz; simplify_eq/=.
      destruct n as [|n]; [lia|].
      have Hcl := discr_expr_closed (DBranch off it fb ch) l.
      simpl in Hcl. apply andb_True in Hcl as [Hcl _].
      iApply (wp_bind (fill [AppRCtx (@RecV BAnon [BNamed "z"] _ Hcl) [] []])).
      iApply (wp_wand with "(Hload [//] HR)").
      iIntros (v) "[-> HR] /=".
      set body := (fix go (ch : list ((Z * Z) * discr)) : expr := match ch with
        | [] => discr_expr fb l
        | ((lo, hi), c) :: ch => Case (discr_test lo hi) [go ch; discr_expr c l] end) ch.
      have Hpe : PureExec True 1 (App (Rec BAnon [BNamed "z"] body) [MLit (VInt z)])
          (subst "z" (MLit (VInt z)) body).
      { apply (pure_rec _ BAnon [BNamed "z"] body); [done| |exact Hcl|].
        - constructor; [|constructor]. by eexists (MLitV _).
        - rewrite /DoSubstL /=. reflexivity. }
      iApply (wp_pure_step_later _ _ _ _ _ _ _ Hpe); [done|].
      iIntros "!> _". rewrite subst_discr_sel. iApply wp_discr_sel.
      destruct (list_find _ ch) as [[k [r c]]|] eqn:Hf.
      + apply list_find_Some in Hf as (Hk & _ & _).
        have [_ Hc] := discr_depth_branch off it fb ch k r c Hk.
        iDestruct (big_sepL_lookup _ _ k with "IH") as "IHc"; [done|].
        iDestruct "IHc" as "#IHc". iApply ("IHc" with "[%] [%] HR HΦ"); [done|simpl in *; lia].
      + have [Hfb _] : (discr_depth fb < discr_depth (DBranch off it fb ch) ∧ True)%nat.
        { split; [simpl; lia|done]. }
        iApply ("IH1" with "[%] [%] HR HΦ"); [done|simpl in *; lia].
  Qed.

  (** The reader of the integers in chunks [(offset, bytes)] of the bytes of an enum. *)
  Fixpoint chunks_reader (cs : list (nat * list abyte)) (off : nat) (it : IntType) : option Z :=
    match cs with
    | [] => None
    | (o, bs) :: cs =>
        if decide (o ≤ off ∧ off + int_size it ≤ o + length bs)%nat
        then decode_int it (list_slice (off - o) (int_size it) bs)
        else chunks_reader cs off it
    end.

  Definition chunks_own (l : loc) (cs : list (nat * list abyte)) : iProp Σ :=
    [∗ list] c ∈ cs, (l +ₗ (c.1 : nat)) ↦b c.2.

  Lemma heap_mapsto_bytes_split l bs k n :
    (k + n ≤ length bs)%nat →
    l ↦b bs ⊣⊢ l ↦b take k bs ∗ (l +ₗ k) ↦b list_slice k n bs ∗ (l +ₗ (k + n)%nat) ↦b drop (k + n) bs.
  Proof.
    intros Hk. transitivity (l ↦b (take k bs ++ list_slice k n bs ++ drop (k + n) bs))%I.
    { by rewrite /list_slice -{1}(take_drop k bs) -{1}(take_drop n (drop k bs)) drop_drop. }
    rewrite !heap_mapsto_bytes_app shift_loc_assoc_nat /list_slice !length_take length_drop.
    do 3 f_equiv; [f_equal; lia|]. do 2 f_equal. lia.
  Qed.

  Lemma chunks_reader_acc l cs off it z :
    chunks_reader cs off it = Some z →
    chunks_own l cs -∗ ∃ bs, ⌜decode_value (MInt it) bs = Some (VInt z)⌝ ∗ (l +ₗ off) ↦b bs ∗
      ((l +ₗ off) ↦b bs -∗ chunks_own l cs).
  Proof.
    rewrite /chunks_own. induction cs as [|[o bs] cs IH]; simpl; [done|].
    case_decide as Hin; last first.
    { iIntros (Hz) "[Hc Hcs]". iDestruct (IH Hz with "Hcs") as (bs') "(? & ? & Cl)".
      iExists bs'. iFrame. iIntros "H". iFrame. by iApply "Cl". }
    iIntros (Hz) "[Hc $]".
    have Hsp := heap_mapsto_bytes_split (l +ₗ o) bs (off - o) (int_size it) ltac:(lia).
    rewrite shift_loc_assoc_nat (_ : (o + (off - o) = off)%nat) in Hsp; [|lia].
    iDestruct (Hsp with "Hc") as "(Ht & Hs & Hd)".
    iExists (list_slice (off - o) (int_size it) bs). iSplit; [by rewrite /= Hz|].
    iFrame "Hs". iIntros "Hs". iApply Hsp. iFrame.
  Qed.

  (** Owned chunks. *)
  Lemma wp_get_discr E vars d sz al l cs t Φ :
    discr_eval (chunks_reader cs) d = Some t →
    chunks_own l cs -∗ (chunks_own l cs -∗ Φ (MLitV (VInt t))) -∗
    WP GetDiscr (MEnum vars d sz al) (MLit (VPtr l)) @ E {{ Φ }}.
  Proof.
    iIntros (Hd) "Hcs HΦ".
    iApply (wp_get_discr_gen _ _ _ _ _ _ _ (λ _, chunks_own l cs) _ (discr_depth d)
      with "[] Hcs [HΦ]"); [done|done| |by iIntros (k)].
    iIntros "!>" (off it z k Hz) "Hcs".
    iDestruct (chunks_reader_acc with "Hcs") as (bs) "(%Hbs & Hbs & Cl)"; [done|].
    iApply (wp_load_na with "Hbs"); [done|]. iIntros "!> Hbs". iSplit; [done|]. by iApply "Cl".
  Qed.

  (** Guarded chunks: [P] holds chunks of bytes ([Ψ cs]) from which [rd] reads. *)
  Lemma wp_get_discr_guarded E vars d sz al l G P (Ψ : list (nat * list abyte) → Prop) rd
      dg n t Φ :
    ↑naN ⊆ E → discr_eval rd d = Some t → (discr_depth d ≤ n)%nat →
    (∀ cs off it z, Ψ cs → rd off it = Some z → chunks_reader cs off it = Some z) →
    (G &&{↑naN; dg}&&> P) -∗
    □ (P -∗ ∃ cs, ⌜Ψ cs⌝ ∗ chunks_own l cs ∗ (chunks_own l cs -∗ P)) -∗
    G -∗ £(2 * dg * n) -∗ (G -∗ Φ (MLitV (VInt t))) -∗
    WP GetDiscr (MEnum vars d sz al) (MLit (VPtr l)) @ E {{ Φ }}.
  Proof.
    iIntros (? Hd Hn Hrd) "#Guard #HP G £ HΦ".
    iApply (wp_get_discr_gen _ _ _ _ _ _ rd (λ k, G ∗ £(2 * dg * k))%I _ n
      with "[] [$G $£] [HΦ]"); [done|done| |by iIntros (k) "[G _]"; iApply "HΦ"].
    iIntros "!>" (off it z k Hz) "[G £]".
    rewrite (_ : (2 * dg * S k = 2 * dg + 2 * dg * k)%nat); [|lia].
    iDestruct "£" as "[£ £']".
    iApply (wp_load_na_guarded_gen _ _ _ (VInt z) G P
      (λ bs, decode_value (MInt it) bs = Some (VInt z)) dg with "[$G $£ $Guard]"); [done|done| |].
    { iIntros "!> HPx". iDestruct ("HP" with "HPx") as (cs Hcs) "[Hcs Cl]".
      iDestruct (chunks_reader_acc with "Hcs") as (bs) "(%Hbs & Hbs & Cl')"; [by eapply Hrd|].
      iExists bs. iFrame "Hbs". iSplit; [done|]. iIntros "Hbs". iApply "Cl". by iApply "Cl'". }
    iIntros "!> G". iSplit; [done|]. iFrame.
  Qed.
End get_discr.
