Import EqNotations.
From stdpp Require Import strings.
From iris.algebra Require Import auth cmra functions gmap csum frac agree.
From iris.bi Require Import fractional.
From iris.proofmode Require Import proofmode.
From iris.base_logic Require Import invariants.
From lrust.util Require Import basic vector discrete_fun fancy_lists.
From lrust.prophecy Require Export syn_type.
From guarding Require Import factoring_props own_and guard.

(** * Basic Notions *)

Implicit Type (ξ ζ: proph_var) (ξl ζl: list proph_var) (π: proph_asn).

(** * Prophecy Dependency *)

Local Definition proph_asn_eqv ξl π π' := ∀ξ, ξ ∈ ξl → π ξ = π' ξ.
Local Notation "π .≡{ ξl }≡ π'" := (proph_asn_eqv ξl π π')
  (at level 70, format "π  .≡{ ξl }≡  π'").

Definition proph_dep {A} (vπ: proph A) (ξl: list proph_var) :=
  ∀π π', π .≡{ξl}≡ π' → vπ π = vπ π'.
Notation "vπ ./ ξl" := (proph_dep vπ ξl) (at level 70, format "vπ  ./  ξl").
 

(** ** Lemmas *)

Lemma proph_dep_one ξ : (.$ ξ) ./ [ξ].
Proof. move=> ?? Eqv. apply Eqv. constructor. Qed.

Lemma proph_dep_constr {A B} (f: A → B) vπ ξl : vπ ./ ξl → f ∘ vπ ./ ξl.
Proof. move=> Dep ?? /Dep ?. by apply (f_equal f). Qed.

Local Lemma proph_dep_mono {A} ξl ζl (vπ: proph A) :
  ξl ⊆ ζl → vπ ./ ξl → vπ ./ ζl.
Proof. move=> In Dep ?? Eqv. apply Dep => ??. by apply Eqv, In. Qed.

Lemma proph_dep_constr2 {A B C} (f: A → B → C) vπ wπ ξl ζl :
  vπ ./ ξl → wπ ./ ζl → f ∘ vπ ⊛ wπ ./ ξl ++ ζl.
Proof.
  move=> Dep Dep' ?? Eqv.
  eapply proph_dep_mono, (.$ Eqv) in Dep, Dep'; [|set_solver..]=>/=. by f_equal.
Qed.

Lemma proph_dep_constr3 {A B C D} (f: A → B → C → D) uπ vπ wπ ξl₀ ξl₁ ξl₂ :
  uπ ./ ξl₀ → vπ ./ ξl₁ → wπ ./ ξl₂ → f ∘ uπ ⊛ vπ ⊛ wπ ./ ξl₀ ++ ξl₁ ++ ξl₂.
Proof.
  move=> Dep₀ Dep₁ Dep₂ ?? Eqv.
  eapply proph_dep_mono, (.$ Eqv) in Dep₀, Dep₁, Dep₂; [|set_solver..]=>/=. by f_equal.
Qed.

Lemma proph_dep_destr {A B} f `{!@Inj A B (=) (=) f} vπ ξl :
  f ∘ vπ ./ ξl → vπ ./ ξl.
Proof. by move=> Dep ?? /Dep/(inj f) ?. Qed.

Lemma proph_dep_destr2 {A B C} f `{!@Inj2 A B C (=) (=) (=) f} vπ wπ ξl :
  f ∘ vπ ⊛ wπ ./ ξl → vπ ./ ξl ∧ wπ ./ ξl.
Proof.
  move=> Dep. split; move=> ?? /Dep Eq; apply (inj2 f) in Eq; tauto.
Qed.

Lemma proph_dep_destr3 {A B C D} f `{!@Inj3 A B C D (=) (=) (=) (=) f} uπ vπ wπ ξl :
  f ∘ uπ ⊛ vπ ⊛ wπ ./ ξl → uπ ./ ξl ∧ vπ ./ ξl ∧ wπ ./ ξl.
Proof.
  move=> Dep. split; [|split]; move=> ?? /Dep/= Eq; apply (inj3 f) in Eq; tauto.
Qed.

Lemma proph_dep_singleton {A} (vπ: proph A) :
  (∀ u v : A, u = v) → vπ ./ [].
Proof. by intros ????. Qed.

Lemma proph_dep_eq {A} (vπ wπ: proph A) ξl :
  vπ ./ ξl → vπ = wπ → wπ ./ ξl.
Proof. by move=> ?<-. Qed.

Lemma proph_dep_eq_ext {A} (vπ wπ: proph A) ξl :
  vπ ./ ξl → (∀ π, vπ π = wπ π) → wπ ./ ξl.
Proof. unfold "./". intros Ha Hb π π' t. rewrite <- Hb. rewrite <- Hb. exact (Ha π π' t). Qed.

Lemma proph_dep_prod {A B} ξl ζl (vπ: proph (A * B)) :
  fst ∘ vπ ./ ξl → snd ∘ vπ ./ ζl → vπ ./ ξl ++ ζl.
Proof.
  move=> ??. rewrite (surjective_pairing_fun vπ). by apply proph_dep_constr2.
Qed.

Lemma proph_dep_list_prod {A B} ξl ζl (f: proph (list (A * B))) :
  map fst ∘ f ./ ξl → map snd ∘ f ./ ζl → f ./ ξl ++ ζl.
Proof. move=> ??. rewrite -(zip_fst_snd_fun f). by apply proph_dep_constr2. Qed.

Lemma proph_dep_vec_S {A n} ξl ζl (vπ: proph (vec A (S n))) :
  vhd ∘ vπ ./ ξl → vtl ∘ vπ ./ ζl → vπ ./ ξl ++ ζl.
Proof.
  move=> ??. rewrite (surjective_vcons_fun vπ). by apply proph_dep_constr2.
Qed.

Lemma proph_dep_vinsert {A n} (vπl: vec (proph A) n) i wπ ξ ζl ζl' :
  vapply (vtake i vπl) ./ ζl → wπ ./ [ξ] → vapply (vdrop' i vπl) ./ ζl' →
  vapply (vinsert i wπ vπl) ./ ζl ++ ξ :: ζl'.
Proof.
  move=> ???. rewrite vapply_insert_backmid.
  have ->: ξ :: ζl' = [ξ] ++ ζl' by done. by apply proph_dep_constr3.
Qed.

Lemma syn_indep {𝔄} (x: ~~𝔄) : vπ x ./ ξl x.
Proof.
  move: 𝔄 x. fix FIX 1. move=> 𝔄 x. destruct 𝔄; try (clear FIX; done).
   - destruct x; last by (clear FIX; done).
     simpl. apply proph_dep_constr. apply FIX.
   - induction x; first by (clear FIX; done). simpl. apply proph_dep_constr2.
      + apply FIX. + apply IHx.
   - induction x; first by (clear FIX; done). simpl.
     apply (proph_dep_constr2 (λ a b, @Vector.cons _ a _ b)).
      + apply FIX. + apply IHx.
   - destruct x. apply proph_dep_constr2; apply FIX.
   - destruct x.
      + apply proph_dep_constr. apply (FIX 𝔄1 i).
      + apply proph_dep_constr. apply (FIX 𝔄2 i).
   - induction l; first by (clear FIX; done). destruct x. apply proph_dep_constr2.
      + apply FIX. + apply IHl.
   - destruct x as [x padding]. generalize padding. induction l as [|𝔄₀ 𝔄l]; first by (clear FIX; done). clear padding. intros padding.
     destruct x as [x|x].
     + apply (proph_dep_constr (λ a, (inl a, padding)) _ _ (FIX 𝔄₀ x)).
     + clear FIX. have h1 := IH𝔄l x padding.
       replace (@ξl (xsumₛ (@cons syn_type 𝔄₀ 𝔄l))
       (@pair (@psum syn_type indep_interp_of_syn_type (@cons syn_type 𝔄₀ 𝔄l)) 
          (list lang.val)
          (@inr (indep_interp_of_syn_type 𝔄₀) (@psum syn_type indep_interp_of_syn_type 𝔄l) x)
          padding)) with (@ξl (xsumₛ 𝔄l) (@pair (@psum syn_type indep_interp_of_syn_type 𝔄l) (list lang.val) x padding)).
       * apply (proph_dep_constr (λ '(a, b), (inr a, b)) _ _ h1).
       * simpl. destruct (to_xsum (psum_map1 (λ (A : syn_type) (x0 : ~~ A), ξl x0) x)). trivial.
   - destruct x. apply (proph_dep_constr (λ i, (_,i))). apply (FIX 𝔄).
   - destruct x. apply (proph_dep_constr (λ i, (_,i))). apply (FIX 𝔄).
   - destruct x as [[[[[l x0] ξi] d'] g'] idx]. simpl.
     set ξ := PrVar ((𝔄 * (positiveₛ * positiveₛ))%ST
       ↾ @to_inh_syn_type ((𝔄 * (positiveₛ * positiveₛ))%ST) (vπ x0 inhabitant, (1%positive, 1%positive))) ξi.
     apply (proph_dep_constr2 (λ a b, (b, a)) (λ π, (π ξ).1) _ [ξ]).
     + apply (proph_dep_constr fst (λ π, π ξ)). apply proph_dep_one.
     + apply (FIX 𝔄).
   - destruct x as [[??]?]. clear FIX; done.
   - apply (FIX 𝔄).
Qed.

(** * Prophecy Log *)

Record proph_log_item :=
  ProphLogItem { pli_pv: proph_var; pli_val: proph pli_pv.(pv_ty) }.
Local Notation ".{ ξ := vπ }" := (ProphLogItem ξ vπ)
  (at level 1, format ".{ ξ  :=  vπ }").

Local Definition proph_log := list proph_log_item.

Local Definition res (L: proph_log) := pli_pv <$> L.

Local Definition proph_asn_eqv_out ξl π π' := ∀ξ, ξ ∉ ξl → π ξ = π' ξ.
Local Notation "π .≡~{ ξl }≡ π'" := (proph_asn_eqv_out ξl π π')
  (at level 70, format "π  .≡~{ ξl }≡  π'").
Local Definition proph_dep_out {A} (vπ: proph A) ξl :=
  ∀ π π', π .≡~{ ξl }≡ π' → vπ π = vπ π'.
Local Notation "vπ ./~ ξl" := (proph_dep_out vπ ξl)
  (at level 70, format "vπ  ./~  ξl").

Local Fixpoint proph_log_ok L :=
  match L with
  | [] => True
  | .{ξ := vπ} :: L' => ξ ∉ res L' ∧ vπ ./~ res L ∧ proph_log_ok L'
  end.
Local Notation ".✓ L" := (proph_log_ok L) (at level 20, format ".✓  L").

Local Definition proph_sat π L := Forall (λ pli, π pli.(pli_pv) = pli.(pli_val) π) L.
Local Notation "π ◁ L" := (proph_sat π L) (at level 70, format "π  ◁  L").

(** ** Satisfiability *)

Local Definition proph_upd ξ vπ π : proph_asn := λ ζ,
  match decide (ξ = ζ) with left eq => rew eq in vπ π | right _ => π ζ end.
Local Notation ":<[ ξ := vπ ]>" := (proph_upd ξ vπ)
  (at level 5, format ":<[ ξ  :=  vπ ]>").

Local Lemma proph_upd_lookup π ξ vπ : :<[ξ := vπ]> π ξ = vπ π.
Proof. rewrite /proph_upd. case (decide (ξ = ξ))=> [?|?]; by [simpl_eq|]. Qed.
Local Lemma proph_upd_lookup_ne π ξ vπ ζ : ξ ≠ ζ → :<[ξ := vπ]> π ζ = π ζ.
Proof. rewrite /proph_upd. by case (decide (ξ = ζ))=> [?|?]. Qed.

Local Fixpoint proph_modify π L :=
  match L with
  | [] => π
  | .{ξ := vπ} :: L' => proph_modify (:<[ξ := vπ]> π) L'
  end.
Local Notation "π ! L" := (proph_modify π L) (at level 30, format "π  !  L").

Local Lemma proph_modify_eqv L : ∀π, π ! L .≡~{res L}≡ π.
Proof.
  elim L=>/= [|[??]? IH]; [done|]=> > /not_elem_of_cons [??].
  rewrite IH; [|done]. by apply proph_upd_lookup_ne.
Qed.

Local Lemma proph_ok_modify_sat L : .✓ L → ∀π, π ! L ◁ L.
Proof.
  rewrite /proph_sat. elim: L=>/= [|[ξ vπ] L' IH]; [done|]. move=> [?[? /IH ?]]?.
  apply Forall_cons=>/=. split; [|done]. rewrite proph_modify_eqv; [|done].
  rewrite proph_upd_lookup. set L := .{ξ := vπ} :: L'.
  have Dep': vπ ./~ res L by done. symmetry. apply Dep', (proph_modify_eqv L).
Qed.

Local Lemma proph_ok_sat L : .✓ L → ∃π, π ◁ L.
Proof. exists (inhabitant ! L). by apply proph_ok_modify_sat. Qed.

(** * Prophecy Camera *)

Local Definition proph_itemR (𝔄i: syn_typei) :=
  csumR fracR (agreeR (leibnizO (proph 𝔄i))).
Local Definition proph_gmapUR 𝔄i := gmapUR positive (proph_itemR 𝔄i).
Local Definition proph_smryUR := discrete_funUR proph_gmapUR.
Definition prophUR: ucmra := authUR proph_smryUR.

Local Definition aitem {𝔄i} vπ : proph_itemR 𝔄i := Cinr (to_agree vπ).
Local Definition fitem {𝔄i} (q: Qp) : proph_itemR 𝔄i := Cinl q.
Local Definition line ξ it : proph_smryUR := .{[ξ.(pv_ty) := {[ξ.(pv_id) := it]}]}.
Local Definition add_line ξ it (S: proph_smryUR) : proph_smryUR :=
  .<[ξ.(pv_ty) := <[ξ.(pv_id) := it]> (S ξ.(pv_ty))]> S.

Definition prophΣ: gFunctors := #[GFunctor prophUR].
Class prophPreG Σ := ProphPreG { #[global] proph_preG_inG :: inG Σ prophUR }.
Class prophG Σ := ProphG { #[global] proph_inG :: prophPreG Σ; proph_name: gname }.
Global Instance subG_prophPreG Σ : subG prophΣ Σ → prophPreG Σ.
Proof. solve_inG. Qed.

Definition prophN: namespace := nroot .@ "proph".

(** * Iris Propositions *)

Local Definition proph_sim (S: proph_smryUR) (L: proph_log) :=
  ∀ξ vπ, S ξ.(pv_ty) !! ξ.(pv_id) ≡ Some (aitem vπ) ↔ .{ξ := vπ} ∈ L.
Local Notation "S :~ L" := (proph_sim S L) (at level 70, format "S  :~  L").

Section defs.
Context `{!invGS Σ, !prophG Σ}.

(** Prophecy Context *)
Local Definition proph_inv: iProp Σ :=
  ∃S, ⌜∃L, .✓ L ∧ S :~ L⌝ ∗ own proph_name (● S).
Definition proph_ctx: iProp Σ := inv prophN proph_inv.

(** Prophecy Token *)
Definition proph_tok (ξ: proph_var) (q: Qp) : iProp Σ :=
  own proph_name (◯ line ξ (fitem q)).

(** Prophecy Observation *)
Local Definition proph_atom pli : iProp Σ :=
  own proph_name (◯ line pli.(pli_pv) (aitem pli.(pli_val))).
Definition proph_obs (φπ: proph Prop) : iProp Σ :=
  ∃L, ⌜∀π, π ◁ L → φπ π⌝ ∗ [∗ list] pli ∈ L, proph_atom pli.
End defs.

Notation "q :[ ξ ]" := (proph_tok ξ q)
  (at level 2, left associativity, format "q :[ ξ ]") : bi_scope.
Notation "q :+[ ξl ]" := ([∗ list] ξ ∈ ξl, q:[ξ])%I
  (at level 2, left associativity, format "q :+[ ξl ]") : bi_scope.
Notation ".⟨ φπ ⟩" := (proph_obs φπ%type%stdpp)
  (at level 1, format ".⟨ φπ ⟩") : bi_scope.
Notation "⟨ π , φ ⟩" := (proph_obs (λ π, φ%type%stdpp))
  (at level 1, format "⟨ π ,  φ ⟩") : bi_scope.

(** * Iris Lemmas *)

Section proph.
Context `{!invGS Σ, !prophG Σ}.

(** Instances *)

Global Instance proph_ctx_persistent: Persistent proph_ctx := _.

Global Instance proph_tok_timeless q ξ : Timeless q:[ξ] := _.
Global Instance proph_tok_fractional ξ : Fractional (λ q, q:[ξ]%I).
Proof.
  move=> ??. by rewrite -own_op -auth_frag_op discrete_fun_singleton_op
    singleton_op -Cinl_op.
Qed.
Global Instance proph_tok_as_fractional q ξ : AsFractional q:[ξ] (λ q, q:[ξ]%I) q.
Proof. split; by [|apply _]. Qed.
(*
Global Instance frame_proph_tok p ξ q1 q2 RES :
  FrameFractionalHyps p q1:[ξ] (λ q, q:[ξ])%I RES q1 q2 →
  Frame p q1:[ξ] q2:[ξ] RES | 5.
Proof. apply: frame_fractional. Qed.
*)

Global Instance proph_toks_as_fractional q ξl : AsFractional q:+[ξl] (λ q, q:+[ξl]%I) q.
Proof. split; by [|apply _]. Qed.
(*
Global Instance frame_proph_toks p ξl q1 q2 RES :
  FrameFractionalHyps p q1:+[ξl] (λ q, q:+[ξl])%I RES q1 q2 →
  Frame p q1:+[ξl] q2:+[ξl] RES | 5.
Proof. apply: frame_fractional. Qed.
*)

Global Instance proph_obs_persistent φπ : Persistent .⟨φπ⟩ := _.
Global Instance proph_obs_timeless φπ : Timeless .⟨φπ⟩ := _.
Global Instance proph_obs_proper :
  Proper (pointwise_relation _ (↔) ==> (⊣⊢)) proph_obs.
Proof.
  move=> ?? Iff. rewrite /proph_obs. do 4 f_equiv. apply forall_proper=> ?.
  by rewrite Iff.
Qed.
Global Instance proph_obs_mono :
  Proper (pointwise_relation _ impl ==> (⊢)) proph_obs.
Proof.
  move=> ?? Imp. rewrite /proph_obs. do 4 f_equiv. move=> Imp' ??. by apply Imp, Imp'.
Qed.


(** Manipulating Tokens *)

Lemma proph_tok_singleton ξ q : q:[ξ] ⊣⊢ q:+[[ξ]].
Proof. by rewrite/= right_id. Qed.

Lemma proph_tok_combine ξl ζl q q' :
  q:+[ξl] -∗ q':+[ζl] -∗
    ∃q'', q'':+[ξl ++ ζl] ∗ (q'':+[ξl ++ ζl] -∗ q:+[ξl] ∗ q':+[ζl]).
Proof. 
  case (Qp.lower_bound q q')=> [q''[?[?[->->]]]]. iIntros "[ξl ξl'][ζl ζl']".
  iExists q''. iFrame "ξl ζl". iIntros "[ξl ζl]".
  iSplitL "ξl ξl'"; iApply fractional_split; iFrame.
Qed. 

(** Initialization *)

Lemma proph_init `{!prophPreG Σ} E :
  ↑prophN ⊆ E → ⊢ |={E}=> ∃_: prophG Σ, proph_ctx.
Proof.
  move=> ?. iMod (own_alloc (● ε)) as (γ) "●ε"; [by apply auth_auth_valid|].
  set IProphG := ProphG Σ _ γ. iExists IProphG.
  iMod (inv_alloc _ _ proph_inv with "[●ε]") as "?"; [|done]. iModIntro.
  iExists ε. iFrame "●ε". iPureIntro. exists []. split; [done|]=> ??.
  rewrite lookup_empty. split=> Hyp; inversion Hyp.
Qed.

(** Taking 𝔄i Fresh Prophecy Variable *)

Lemma proph_intro 𝔄i (I: gset positive) E :
  ↑prophN ⊆ E → proph_ctx ={E}=∗ ∃i, ⌜i ∉ I⌝ ∗ 1:[PrVar 𝔄i i].
Proof.
  iIntros (?) "?". iInv prophN as (S) ">[(%L &%& %Sim) ●S]".
  case (exist_fresh (I ∪ dom (S 𝔄i)))
    => [i /not_elem_of_union [? /not_elem_of_dom EqNone]].
  set ξ := PrVar 𝔄i i. set S' := add_line ξ (fitem 1) S.
  iMod (own_update _ _ (● S' ⋅ ◯ line ξ (fitem 1)) with "●S") as "[●S' ?]".
  { by apply auth_update_alloc,
      discrete_fun_insert_local_update, alloc_singleton_local_update. }
  iModIntro. iSplitL "●S'"; last first. { by iModIntro; iExists i; iFrame. }
  iModIntro. iExists S'. iFrame "●S'". iPureIntro. exists L.
  split; [done|]. case=> [𝔅i j]?. rewrite /S' /add_line /discrete_fun_insert -Sim /=.
  case (decide (𝔄i = 𝔅i))=>//= ?. subst=>/=.
  case (decide (i = j))=> [<-|?]; [|by rewrite lookup_insert_ne].
  rewrite lookup_insert EqNone. split=> Eqv; [apply (inj Some) in Eqv|]; inversion Eqv.
Qed.

(** Prophecy Resolution *)

Local Lemma proph_tok_out S L ξ q :
  S :~ L → own proph_name (● S) -∗ q:[ξ] -∗ ⌜ξ ∉ res L⌝.
Proof.
  move=> Sim. iIntros "●S ξ".
  iDestruct (own_valid_2 with "●S ξ") as %ValBoth. iPureIntro.
  move=> /(elem_of_list_fmap_2 pli_pv) [[[𝔄i i]?][? /Sim Eqv]]. simpl in *.
  subst. move: ValBoth=> /auth_both_valid_discrete [Inc _].
  move/(discrete_fun_included_spec_1 _ _ 𝔄i) in Inc.
  rewrite /line discrete_fun_lookup_singleton /= in Inc.
  move: Eqv. move: Inc=> /singleton_included_l [?[-> Inc]]. move=> Eqv.
  apply (inj Some) in Eqv. move: Inc. rewrite Eqv.
  by move=> /Some_csum_included [|[[?[?[_[?]]]]|[?[?[?]]]]].
Qed.

Local Lemma proph_tok_ne ξ ζ q : 1:[ξ] -∗ q:[ζ] -∗ ⌜ξ ≠ ζ⌝.
Proof.
  iIntros "ξ ζ". iDestruct (own_valid_2 with "ξ ζ") as %ValBoth.
  iPureIntro=> ?. subst. move: ValBoth.
  rewrite -auth_frag_op auth_frag_valid discrete_fun_singleton_op
    discrete_fun_singleton_valid singleton_op singleton_valid -Cinl_op Cinl_valid.
  apply exclusive_l, _.
Qed.

Lemma proph_resolve P E ξ vπ ζl : ↑prophN ⊆ E → vπ ./ ζl →
  (∀ ζ, ⌜ζ ∈ ζl⌝ → P -∗ ∃ q, q:[ζ]) -∗
  proph_ctx -∗ 1:[ξ] -∗ P ={E}=∗ ⟨π, π ξ = vπ π⟩ ∗ P.
Proof.
  move: ξ vπ => [𝔄i i] vπ. set ξ := PrVar 𝔄i i.
  iIntros (? Dep) "P→ ? ξ P". iInv prophN as (S) ">[(%L & % & %Sim) ●S]".
  iDestruct (proph_tok_out with "●S ξ") as %Outξ; [done|].
  set L' := .{ξ := vπ} :: L. iAssert ⌜∀ζ, ζ ∈ ζl → ζ ∉ res L'⌝%I as %Outζl.
  { iIntros (??). iDestruct ("P→" with "[//] P") as (?) "ζ".
    iDestruct (proph_tok_ne with "ξ ζ") as %?.
    iDestruct (proph_tok_out with "●S ζ") as %?; [done|].
    by rewrite not_elem_of_cons. }
  set S' := add_line ξ (aitem vπ) S.
  iMod (own_update_2 _ _ _ (● S' ⋅ ◯ line ξ (aitem vπ)) with "●S ξ")
    as "[●S' #?]".
  { apply auth_update, discrete_fun_singleton_local_update_any,
      singleton_local_update_any => ? _. by apply exclusive_local_update. }
  iModIntro. iSplitL "●S'"; last first.
  { iModIntro. iFrame "P". iExists [.{ξ := vπ}]. rewrite big_sepL_singleton.
    iSplitR; [|done]. iPureIntro=> ? Sat. by inversion Sat. }
  iModIntro. iExists S'. iFrame "●S'". iPureIntro. exists L'. split.
  { split; [done| split; [|done]] => ?? Eqv. apply Dep => ? /Outζl ?. by apply Eqv. }
  have InLNe ζ wπ : .{ζ := wπ} ∈ L → ξ ≠ ζ.
  { move=> /(elem_of_list_fmap_1 pli_pv) ??. by subst. }
  move=> [𝔅i j] ?. rewrite elem_of_cons. case (decide (ξ = PrVar 𝔅i j))=> [Eq|Ne].
  { dependent destruction Eq.
    rewrite /S' /add_line discrete_fun_lookup_insert lookup_insert. split.
    - move=> /(inj (Some ∘ aitem)) ->. by left.
    - move=> [Eq'|/InLNe ?]; [|done]. by dependent destruction Eq'. }
  have Eqv : S' 𝔅i !! j ≡ S 𝔅i !! j.
  { rewrite /S' /add_line /discrete_fun_insert /=.
    case (decide (𝔄i = 𝔅i))=>// ?. simpl_eq.
    case (decide (i = j))=> [?|?]; [|by rewrite lookup_insert_ne]. by subst. }
  rewrite Eqv Sim. split; [by right|]. case; [|done]=> Eq. by dependent destruction Eq.
Qed.

Lemma proph_resolve_toks E ξ vπ ζl q : ↑prophN ⊆ E → vπ ./ ζl →
  proph_ctx -∗ 1:[ξ] -∗ q:+[ζl] ={E}=∗ ⟨π, π ξ = vπ π⟩ ∗ q:+[ζl].
Proof.
  iIntros (??). iApply proph_resolve=>//. iIntros (??) "ζl". iExists _. 
  by iApply (big_sepL_elem_of with "ζl").
Qed.

(** Manipulating Prophecy Observations *)

Implicit Type φπ ψπ: proph Prop.

Lemma proph_obs_true φπ : (∀π, φπ π) → ⊢ ⟨π, φπ π⟩.
Proof. move=> ?. iExists []. by iSplit. Qed.

Lemma proph_obs_impl φπ ψπ : (∀π, φπ π → ψπ π) → .⟨φπ⟩ ⊢ .⟨ψπ⟩.
Proof. move=> Imp. (do 2 f_equiv)=> ?. exact: Imp. Qed. 

Lemma proph_obs_eq φπ ψπ : (∀π, φπ π = ψπ π) → .⟨φπ⟩ ⊢ .⟨ψπ⟩.
Proof. move=> Eq. apply proph_obs_impl=> ?. by rewrite Eq. Qed.

Lemma proph_obs_and φπ ψπ : .⟨φπ⟩ -∗ .⟨ψπ⟩ -∗ ⟨π, φπ π ∧ ψπ π⟩.
Proof.
  iIntros "(%L & %Toφπ & L) (%L' & %Toψπ & L')". iExists (L ++ L'). iFrame "L L'".
  iPureIntro=> ? /Forall_app[??]. split; by [apply Toφπ|apply Toψπ].
Qed.

Global Instance proph_obs_from_sep φπ ψπ : FromSep ⟨π, φπ π ∧ ψπ π⟩ .⟨φπ⟩ .⟨ψπ⟩.
Proof. rewrite /FromSep. iIntros "#[??]". by iApply proph_obs_and. Qed.

Global Instance proph_obs_combine_sep_as φπ ψπ : CombineSepAs .⟨φπ⟩ .⟨ψπ⟩ ⟨π, φπ π ∧ ψπ π⟩.
Proof. rewrite /CombineSepAs. iIntros "#[??]". by iApply proph_obs_and. Qed.

Lemma proph_obs_sat E φπ :
  ↑prophN ⊆ E → proph_ctx -∗ .⟨φπ⟩ ={E}=∗ ⌜∃π₀, φπ π₀⌝.
Proof.
  iIntros "% ? (%L' & %Toφπ & #L')". iInv prophN as (S) ">[(%L & %Ok & %Sim) ●S]".
  move: (Ok)=> /proph_ok_sat [π /Forall_forall Sat]. iModIntro.
  iAssert ⌜π ◁ L'⌝%I as %?; last first.
  { iSplitL; last first. { iPureIntro. exists π. by apply Toφπ. }
    iModIntro. iExists S. iFrame "●S". iPureIntro. by exists L. }
  rewrite /proph_sat Forall_forall. iIntros ([[𝔄i i] vπ] In)=>/=.
  set ξ := PrVar 𝔄i i. iAssert (proph_atom .{ξ := vπ}) with "[L']" as "ξvπ".
  { iApply big_sepL_elem_of; by [apply In|]. }
  iDestruct (own_valid_2 with "●S ξvπ") as %ValBoth. iPureIntro.
  move: ValBoth=> /auth_both_valid_discrete [Inc Val]. apply (Sat .{ξ := vπ}), Sim.
  move/(discrete_fun_included_spec_1 _ _ 𝔄i) in Inc.
  rewrite /line discrete_fun_lookup_singleton in Inc.
  move: Inc=> /singleton_included_l [it [Eqv /Some_included [->|Inc]]]; [done|].
  rewrite Eqv. constructor. apply (lookup_valid_Some _ i it) in Val; [|done]. move: Val.
  move: Inc=> /csum_included [->|[[?[?[?]]]|[?[?[Eq[-> Inc]]]]]]; [done|done|].
  move=> Val. move: Inc. move: Val=> /Cinr_valid/to_agree_uninj [?<-].
  inversion Eq. by move/to_agree_included <-.
Qed.

Lemma proph_obs_false E φπ :
  ↑prophN ⊆ E → (∀π, ¬ φπ π) → proph_ctx -∗ .⟨φπ⟩ ={E}=∗ False.
Proof.
  iIntros (? Neg) "PROPH Obs".
  iMod (proph_obs_sat with "PROPH Obs") as %[? Ex]; [done|]. by apply Neg in Ex.
Qed.

Lemma proph_tok_point_prop q ξ : factoring_props.point_prop q:[ξ].
  apply factoring_props.point_prop_own.
Qed.


Lemma proph_tokl_point_prop q ξl : factoring_props.point_prop q:+[ξl].
  induction ξl.
   - apply factoring_props.point_prop_True.
   - apply factoring_props.point_prop_sep; last by trivial.
     apply proph_tok_point_prop.
Qed.

Local Lemma frag_incl_lemma (a b c : proph_smryUR) :
(∀ z, ✓z → a ≼ z → b ≼ z → c ≼ z) →
∀ z, ✓z → ◯ a ≼ z → ◯ b ≼ z → ◯ c ≼ z.
Proof.
  intros Hz z Hvalz az bz.
  destruct z as [authz fragz].
  assert (a ≼ fragz) as Hincla.
  { destruct az as [[authk fragk] az]. exists fragk. inversion az. done. }
  assert (b ≼ fragz) as Hinclb.
  { destruct bz as [[authk fragk] bz]. exists fragk. inversion bz. done. }
  assert (✓ fragz) as Hvalz'. {
    rewrite cmra_valid_validN. intros n.
    destruct authz as [[dq p]|].
      - destruct Hvalz as [H1 H2].
        destruct (H2 n) as [ax [H4 H5]]. 
        apply (auth_view_rel_raw_valid _ _ _ _ H5).
      - destruct (Hvalz n) as [ax H4]. 
        apply (auth_view_rel_raw_valid _ _ _ _ H4).
  }
  destruct (Hz fragz Hvalz' Hincla Hinclb) as [d Hz1].
  exists (View authz d). rewrite Hz1. destruct authz; done.
Qed.

Local Lemma val_lemma 𝔄i x :
    ✓ (Some (@fitem 𝔄i 1) ⋅ x) →
    Some (@fitem 𝔄i 1) ⋅ x = Some (@fitem 𝔄i 1).
Proof.
  destruct x as [[| |] | ]; try done. intros Ha. exfalso.
  unfold "✓", cmra_valid, optionR, proph_itemR, option_valid_instance, "⋅", cmra_op, option_op_instance, union_with, option_union_with, fitem, "✓", cmra_valid, csumR, csum_valid_instance, "⋅", cmra_op, csum_op_instance in Ha.  
  generalize Ha. apply exclusive_l, _.
Qed.

Local Lemma eq_none_lemma {𝔄i} (x : proph_itemR 𝔄i) a :
  a = None → Some x ≡ Some x ⋅ a ⋅ None.
Proof.
  intros Heq. subst a. done.
Qed.

Lemma proph_tok_list_and ξ ζl :
    ξ ∉ ζl → 1:[ξ] ∧ 1:+[ζl] ⊢ 1:[ξ] ∗ 1:+[ζl].
Proof.
    destruct (decide (ζl = [])) as [->|Hn].
      - iIntros (Hnotin) "[$ _]". done.
      - unfold proph_tok. setoid_rewrite <- big_opL_own; trivial.
        intros Hnotin. rewrite <- own_op.
        apply and_own_discrete_ucmra_specific. intros z Hvalz Hincl1 Hincl2.
        
        setoid_rewrite <- big_opL_auth_frag.
        setoid_rewrite <- big_opL_auth_frag in Hincl2.
        eapply (frag_incl_lemma _ _ _ _ z Hvalz Hincl1 Hincl2). Unshelve.
        clear Hvalz. clear  Hincl1. clear Hincl2. clear z.
        intros z Hvalz Hincl1 Hincl2. simpl.
        
        destruct Hincl2 as [b2 Hincl2].
        exists ((discrete_fun_insert (pv_ty ξ) (delete (pv_id ξ) (b2 (pv_ty ξ))) b2)).
        
        destruct Hincl1 as [b1 Hincl1]. 
        
        intros xty.
        destruct (decide (xty = pv_ty ξ)) as [->|Hno].
         + intros xid. destruct (decide (xid = pv_id ξ)) as [->|Hno2].
           * do 2 (rewrite discrete_fun_lookup_op). rewrite lookup_op.
             rewrite lookup_op. rewrite discrete_fun_lookup_insert.
             rewrite lookup_delete.
             rewrite (Hincl1 (pv_ty ξ)).
             rewrite lookup_op. unfold line. rewrite discrete_fun_lookup_singleton.
             rewrite lookup_singleton.
             assert (✓(Some (fitem 1) ⋅ b1 (pv_ty ξ) !! pv_id ξ)). {
                setoid_rewrite Hincl1 in Hvalz.
                have H1 := Hvalz (pv_ty ξ) (pv_id ξ). rewrite lookup_op in H1.
                unfold line in H1. rewrite discrete_fun_lookup_singleton in H1.
                rewrite lookup_singleton in H1. apply H1.
             }
             rewrite val_lemma; trivial.
             apply eq_none_lemma. generalize Hnotin.
             clear Hn. clear Hnotin. clear H. clear Hincl2. clear b2. clear Hincl1.
             clear b1. clear Hvalz. clear z.
             induction ζl; first done. intros Ha. rewrite not_elem_of_cons in Ha.
             destruct Ha as [Hne Hnotin].
             rewrite big_opL_cons. rewrite lookup_op. rewrite IHζl; trivial.
             destruct (decide (pv_ty ξ = pv_ty a)) as [He | Hn].
               -- rewrite He. rewrite discrete_fun_lookup_singleton.
                  destruct (decide (pv_id ξ = pv_id a)) as [He2 | Hn2].
                   ++ exfalso. apply Hne. destruct ξ, a. f_equal; trivial.
                   ++ rewrite lookup_singleton_ne; done.
               -- rewrite discrete_fun_lookup_singleton_ne; done.
          * do 2 (rewrite discrete_fun_lookup_op). rewrite lookup_op.
            rewrite discrete_fun_lookup_insert.
            rewrite lookup_delete_ne; last done.
            rewrite (Hincl2 (pv_ty ξ)).
            rewrite lookup_op. unfold line.
            rewrite discrete_fun_lookup_singleton.
            rewrite lookup_op. rewrite lookup_singleton_ne; last done.
            rewrite left_id. done.
       + do 2 (rewrite discrete_fun_lookup_op).
         rewrite discrete_fun_lookup_insert_ne; last done.
         unfold line. rewrite discrete_fun_lookup_singleton_ne; last done.
         rewrite left_id. rewrite (Hincl2 xty). rewrite discrete_fun_lookup_op. done.
  Qed.
End proph.

Global Opaque proph_ctx proph_tok proph_obs.

(** * Prophecy Equalizer *)

Definition proph_eqz `{!invGS Σ, !prophG Σ} {A} (uπ vπ: proph A) : iProp Σ :=
  ∀E ξl q, ⌜↑prophN ⊆ E ∧ vπ ./ ξl⌝ -∗ q:+[ξl] ={E}=∗ ⟨π, uπ π = vπ π⟩ ∗ q:+[ξl].

Notation "uπ :== vπ" := (proph_eqz uπ vπ) (at level 70, format "uπ  :==  vπ") : bi_scope.

Section proph_eqz.
Context `{!invGS Σ, !prophG Σ}.

Global Instance proph_eqz_proper {A} :
  Proper (pointwise_relation _ (=) ==> pointwise_relation _ (=) ==> (⊣⊢)) (@proph_eqz _ _ _ A).
Proof.
  move=> ?? E1 ?? E2.
  unfold ":==".
  iSplit.
    - iIntros "A" (E ξl q) "%B C". iDestruct ("A" $! E ξl q) as "A".
      iMod ("A" with "[] C") as "[A X]".
      { iPureIntro. destruct B as [B C]. split; trivial.
        unfold "./". intros. unfold "./" in C.  rewrite E2. apply C. trivial. }
      iModIntro. iFrame "X". iApply (proph_obs_impl with "A"). intros π Ha.
      rewrite <- E1. rewrite <- E2. trivial.
    - iIntros "A" (E ξl q) "%B C". iDestruct ("A" $! E ξl q) as "A".
      iMod ("A" with "[] C") as "[A X]".
      { iPureIntro. destruct B as [B C]. split; trivial.
        unfold "./". intros. unfold "./" in C.  rewrite <- E2. apply C. trivial. }
      iModIntro. iFrame "X". iApply (proph_obs_impl with "A"). intros π Ha.
      rewrite E1. rewrite E2. trivial.
Qed.

(** ** Constructing Prophecy Equalizers *)

Lemma proph_eqz_token ξ vπ : proph_ctx -∗ 1:[ξ] -∗ (.$ ξ) :== vπ.
Proof.
  iIntros "PROPH ξ" (???[??]) "ξl". by iMod (proph_resolve_toks with "PROPH ξ ξl").
Qed.

Lemma proph_eqz_obs {A} (uπ vπ: proph A) : ⟨π, uπ π = vπ π⟩ -∗ uπ :== vπ.
Proof. iIntros "?" (???[??]) "? !>". iFrame. Qed.

Lemma proph_eqz_refl {A} (vπ: proph A) : ⊢ vπ :== vπ.
Proof. iApply proph_eqz_obs. by iApply proph_obs_true. Qed.

Lemma proph_eqz_modify {A} (uπ uπ' vπ: proph A) :
  ⟨π, uπ' π = uπ π⟩ -∗ uπ :== vπ -∗ uπ' :== vπ.
Proof.
  iIntros "Obs Eqz" (???[??]) "ξl". iMod ("Eqz" with "[%//] ξl") as "[Obs' $]".
  iModIntro. iCombine "Obs Obs'" as "?". by iApply proph_obs_impl; [|done]=> ?[->].
Qed.

Lemma proph_eqz_constr {A B} f `{!@Inj A B (=) (=) f} uπ vπ :
  uπ :== vπ -∗ f ∘ uπ :== f ∘ vπ.
Proof.
  iIntros "Eqz" (???[? Dep]) "ξl". move/proph_dep_destr in Dep.
  iMod ("Eqz" with "[%//] ξl") as "[Obs $]". iModIntro.
  iApply proph_obs_impl; [|by iApply "Obs"]=> ??/=. by f_equal.
Qed.

Lemma proph_eqz_constr2 {A B C} f `{!@Inj2 A B C (=) (=) (=) f} uπ uπ' vπ vπ' :
  uπ :== vπ -∗ uπ' :== vπ' -∗ f ∘ uπ ⊛ uπ' :== f ∘ vπ ⊛ vπ'.
Proof.
  iIntros "Eqz Eqz'" (???[? Dep]) "ξl". move: Dep=> /proph_dep_destr2[??].
  iMod ("Eqz" with "[%//] ξl") as "[Obs ξl]".
  iMod ("Eqz'" with "[%//] ξl") as "[Obs' $]". iModIntro.
  iCombine "Obs Obs'" as "?". by iApply proph_obs_impl; [|done]=>/= ?[->->].
Qed.

Lemma proph_eqz_constr3 {A B C D} f `{!@Inj3 A B C D (=) (=) (=) (=) f}
    uπ₀ uπ₁ uπ₂ vπ₀ vπ₁ vπ₂ :
  uπ₀ :== vπ₀ -∗ uπ₁ :== vπ₁ -∗ uπ₂ :== vπ₂ -∗
  f ∘ uπ₀ ⊛ uπ₁ ⊛ uπ₂ :== f ∘ vπ₀ ⊛ vπ₁ ⊛ vπ₂.
Proof.
  iIntros "Eqz₀ Eqz₁ Eqz₂" (???[? Dep]) "ξl". move: Dep=> /proph_dep_destr3[?[??]].
  iMod ("Eqz₀" with "[%//] ξl") as "[Obs ξl]".
  iMod ("Eqz₁" with "[%//] ξl") as "[Obs' ξl]". iCombine "Obs Obs'" as "Obs".
  iMod ("Eqz₂" with "[%//] ξl") as "[Obs' $]". iCombine "Obs Obs'" as "?".
  by iApply proph_obs_impl; [|done]=>/= ?[[->->]->].
Qed.

Lemma proph_eqz_eq {A} (uπ uπ' vπ vπ': proph A) :
  uπ = uπ' → vπ = vπ' → uπ :== vπ -∗ uπ' :== vπ'.
Proof. iIntros (->->) "$". Qed.

Lemma proph_eqz_prod {A B} (uπ vπ: proph (A * B)) :
  fst ∘ uπ :== fst ∘ vπ -∗ snd ∘ uπ :== snd ∘ vπ -∗ uπ :== vπ.
Proof.
  iIntros "Eqz Eqz'". iDestruct (proph_eqz_constr2 with "Eqz Eqz'") as "?".
  by rewrite -!surjective_pairing_fun.
Qed.

(** Map an equalizer through an arbitrary function, provided that the
    dependencies of the mapped right-hand side cover those of the original. *)
Lemma proph_eqz_constr_refl {A B} (f: A → B) (uπ vπ: proph A) :
  (∀ ξl, f ∘ vπ ./ ξl → vπ ./ ξl) → uπ :== vπ -∗ f ∘ uπ :== f ∘ vπ.
Proof.
  intros Hrefl. iIntros "Eqz" (E ξl q [? Dep]) "Hξl". apply Hrefl in Dep.
  iMod ("Eqz" with "[%//] Hξl") as "[Obs $]". iModIntro.
  iApply proph_obs_impl; [|by iApply "Obs"]=> ??/=. by f_equal.
Qed.

(** Project out the first component of an equalizer whose right-hand side
    has a constant second component. *)
Lemma proph_eqz_fst_const {A B} (uπ: proph (A * B)) (wπ: proph A) (k: B) :
  uπ :== (λ π, (wπ π, k)) -∗ fst ∘ uπ :== wπ.
Proof.
  iIntros "Eqz" (???[? Dep]) "ξl".
  iMod ("Eqz" with "[%] ξl") as "[Obs $]".
  { split; [done|]. by apply (proph_dep_constr (λ a, (a, k))). }
  iModIntro. iApply proph_obs_impl; [|by iApply "Obs"]=> ? /= ->. done.
Qed.

Lemma proph_eqz_vinsert {A n} xπ yπ (zπl: vec (proph A) n) i :
  xπ :== yπ -∗ vapply (vinsert i xπ zπl) :== vapply (vinsert i yπ zπl).
Proof.
  iIntros "Eqz". rewrite !vapply_insert_backmid.
  iApply (proph_eqz_constr3 with "[] Eqz []"); iApply proph_eqz_refl.
Qed.

End proph_eqz.
