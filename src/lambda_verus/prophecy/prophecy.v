Import EqNotations.
From stdpp Require Import strings.
From iris.algebra Require Import auth cmra functions gmap csum frac agree excl.
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

(** An entry of the log is an item together with a reservation flag:
  [None] means that the item is resolved, and [Some ζl] means that the
  variable is merely reserved (its value in the log being a placeholder),
  and that it will be resolved to a value depending on [ζl] and on variables
  that are unresolved at resolution time. *)
Local Definition proph_log_ent : Type := proph_log_item * option (list proph_var).
Local Definition proph_log := list proph_log_ent.

Local Definition res (L: proph_log) := (λ e, e.1.(pli_pv)) <$> L.
Local Arguments res : simpl never.

Local Definition proph_asn_eqv_out ξl π π' := ∀ξ, ξ ∉ ξl → π ξ = π' ξ.
Local Notation "π .≡~{ ξl }≡ π'" := (proph_asn_eqv_out ξl π π')
  (at level 70, format "π  .≡~{ ξl }≡  π'").
Local Definition proph_dep_out {A} (vπ: proph A) ξl :=
  ∀ π π', π .≡~{ ξl }≡ π' → vπ π = vπ π'.
Local Notation "vπ ./~ ξl" := (proph_dep_out vπ ξl)
  (at level 70, format "vπ  ./~  ξl").

(** A reserved entry records that its dependencies [ζl] were unresolved
  at (and before) its position in the log. *)
Local Definition rsv_ok (r: option (list proph_var)) ξl :=
  match r with None => True | Some ζl => ∀ζ, ζ ∈ ζl → ζ ∉ ξl end.

Local Fixpoint proph_log_ok (L: proph_log) :=
  match L with
  | [] => True
  | (.{ξ := vπ}, r) :: L' =>
      ξ ∉ res L' ∧ vπ ./~ ξ :: res L' ∧ rsv_ok r (ξ :: res L') ∧ proph_log_ok L'
  end.
Local Notation ".✓ L" := (proph_log_ok L) (at level 20, format ".✓  L").

Local Definition proph_sat π (L: list proph_log_item) :=
  Forall (λ pli, π pli.(pli_pv) = pli.(pli_val) π) L.
Local Notation "π ◁ L" := (proph_sat π L) (at level 70, format "π  ◁  L").

(** ** Basic Facts on the Log *)

Local Lemma res_cons e L : res (e :: L) = e.1.(pli_pv) :: res L.
Proof. done. Qed.
Local Lemma res_app_cons L1 e L2 :
  res (L1 ++ e :: L2) = res L1 ++ e.1.(pli_pv) :: res L2.
Proof. by rewrite /res fmap_app. Qed.
Local Lemma res_elem e L : e ∈ L → e.1.(pli_pv) ∈ res L.
Proof. apply (elem_of_list_fmap_1 (λ e, e.1.(pli_pv))). Qed.

Local Lemma pli_inj ξ vπ wπ : .{ξ := vπ} = .{ξ := wπ} → vπ = wπ.
Proof.
  move=> Eq.
  have := f_equal (λ pli, existT (P:=λ ζ, proph ζ.(pv_ty)) pli.(pli_pv) pli.(pli_val)) Eq.
  by move=> /= /(Eqdep_dec.inj_pair2_eq_dec _ proph_var_eq_dec _ _ _ _).
Qed.
Local Lemma pli_ent_eq ξ vπ wπ (r r': option (list proph_var)) :
  (.{ξ := wπ}, r') = (.{ξ := vπ}, r) ↔ (wπ, r') = (vπ, r).
Proof.
  split=> Eq; [|by case: Eq=> -> ->].
  have /pli_inj -> := f_equal fst Eq. by have /= -> := f_equal snd Eq.
Qed.

Local Lemma proph_dep_out_anti {A} (vπ: proph A) ξl ζl :
  ξl ⊆ ζl → vπ ./~ ζl → vπ ./~ ξl.
Proof.
  move=> Sub Dep ?? Eqv. apply Dep=> ? Nin. apply Eqv=> In. by apply Nin, Sub.
Qed.
Local Lemma rsv_ok_anti r ξl ζl : ξl ⊆ ζl → rsv_ok r ζl → rsv_ok r ξl.
Proof. case: r=> [?|] //= Sub Ok ζ /Ok Nin In. by apply Nin, Sub. Qed.

Local Lemma proph_log_ok_suffix L1 L2 : .✓ (L1 ++ L2) → .✓ L2.
Proof. elim: L1=> [|[[??]?] L1 IH] //= [_[_[_ /IH ?]]]. done. Qed.

Local Lemma proph_log_ok_unique L1 e L2 :
  .✓ (L1 ++ e :: L2) → e.1.(pli_pv) ∉ res (L1 ++ L2).
Proof.
  elim: L1=> [|[[ζ wπ] r] L1 IH].
  - by case: e=> [[??]?] /= [].
  - move=> /= [Nin [_ [_ /IH ?]]]. rewrite res_cons not_elem_of_cons.
    split; [|done]. move=> /= Eq. apply Nin. rewrite res_app_cons Eq. set_solver.
Qed.

(** Replacing an entry in place by one with the same variable *)
Local Lemma proph_log_ok_replace L1 e e' L2 :
  e.1.(pli_pv) = e'.1.(pli_pv) → .✓ (e' :: L2) →
  .✓ (L1 ++ e :: L2) → .✓ (L1 ++ e' :: L2).
Proof.
  move=> Eq ?. elim: L1=> [|[[ζ wπ] r] L1 IH]; [done|].
  have Eqr: res (L1 ++ e :: L2) = res (L1 ++ e' :: L2) by rewrite !res_app_cons Eq.
  rewrite /= Eqr. move=> [?[?[? /IH ?]]]. done.
Qed.

(** Deleting an entry: this only weakens the conditions of newer entries *)
Local Lemma proph_log_ok_delete L1 e L2 : .✓ (L1 ++ e :: L2) → .✓ (L1 ++ L2).
Proof.
  elim: L1=> [|[[ζ wπ] r] L1 IH]; [by case: e=> [[??]?] /= [?[?[??]]]|].
  have Sub: res (L1 ++ L2) ⊆ res (L1 ++ e :: L2).
  { rewrite res_app_cons /res fmap_app. set_solver. }
  move=> /= [Nin [Dep [Rsv /IH ?]]]. split; [set_solver|].
  split; [|split; [|done]].
  - apply: proph_dep_out_anti Dep. set_solver.
  - apply: rsv_ok_anti Rsv. set_solver.
Qed.

(** ** Satisfiability *)

Local Definition proph_upd ξ vπ π : proph_asn := λ ζ,
  match decide (ξ = ζ) with left eq => rew eq in vπ π | right _ => π ζ end.
Local Notation ":<[ ξ := vπ ]>" := (proph_upd ξ vπ)
  (at level 5, format ":<[ ξ  :=  vπ ]>").

Local Lemma proph_upd_lookup π ξ vπ : :<[ξ := vπ]> π ξ = vπ π.
Proof. rewrite /proph_upd. case (decide (ξ = ξ))=> [?|?]; by [simpl_eq|]. Qed.
Local Lemma proph_upd_lookup_ne π ξ vπ ζ : ξ ≠ ζ → :<[ξ := vπ]> π ζ = π ζ.
Proof. rewrite /proph_upd. by case (decide (ξ = ζ))=> [?|?]. Qed.

Local Fixpoint proph_modify π (L: proph_log) :=
  match L with
  | [] => π
  | (.{ξ := vπ}, _) :: L' => proph_modify (:<[ξ := vπ]> π) L'
  end.
Local Notation "π ! L" := (proph_modify π L) (at level 30, format "π  !  L").

Local Lemma proph_modify_eqv L : ∀π, π ! L .≡~{res L}≡ π.
Proof.
  elim L=>/= [|[[??]?]? IH]; [done|]. rewrite res_cons /=.
  move=> > /not_elem_of_cons [??]. rewrite IH; [|done]. by apply proph_upd_lookup_ne.
Qed.

Local Lemma proph_ok_modify_sat L : .✓ L → ∀π, π ! L ◁ L.*1.
Proof.
  rewrite /proph_sat. elim: L=>/= [|[[ξ vπ] r] L' IH]; [done|].
  move=> [?[?[_ /IH ?]]]?. apply Forall_cons=>/=. split; [|done].
  rewrite proph_modify_eqv; [|done]. rewrite proph_upd_lookup.
  set L := (.{ξ := vπ}, r) :: L'.
  have Dep': vπ ./~ res L by done. symmetry. apply Dep', (proph_modify_eqv L).
Qed.

Local Lemma proph_ok_sat L : .✓ L → ∃π, π ◁ L.*1.
Proof. exists (inhabitant ! L). by apply proph_ok_modify_sat. Qed.

(** * Prophecy Camera *)

(** An item is either a fractional token, an (exclusive) reservation recording
  its dependencies, or an (agreeing) resolved value. *)
Local Definition proph_itemR (𝔄i: syn_typei) :=
  csumR fracR (csumR (exclR (leibnizO (list proph_var))) (agreeR (leibnizO (proph 𝔄i)))).
Local Definition proph_gmapUR 𝔄i := gmapUR positive (proph_itemR 𝔄i).
Local Definition proph_smryUR := discrete_funUR proph_gmapUR.
Definition prophUR: ucmra := authUR proph_smryUR.

Local Definition aitem {𝔄i} vπ : proph_itemR 𝔄i := Cinr (Cinr (to_agree vπ)).
Local Definition fitem {𝔄i} (q: Qp) : proph_itemR 𝔄i := Cinl q.
Local Definition ritem {𝔄i} (ζl: list proph_var) : proph_itemR 𝔄i := Cinr (Cinl (Excl ζl)).
Local Definition ent_item {𝔄i} vπ (r: option (list proph_var)) : proph_itemR 𝔄i :=
  match r with None => aitem vπ | Some ζl => ritem ζl end.
Local Definition line ξ it : proph_smryUR := .{[ξ.(pv_ty) := {[ξ.(pv_id) := it]}]}.
Local Definition add_line ξ it (S: proph_smryUR) : proph_smryUR :=
  .<[ξ.(pv_ty) := <[ξ.(pv_id) := it]> (S ξ.(pv_ty))]> S.

Definition prophΣ: gFunctors := #[GFunctor prophUR].
Class prophPreG Σ := ProphPreG { #[global] proph_preG_inG :: inG Σ prophUR }.
Class prophG Σ := ProphG { #[global] proph_inG :: prophPreG Σ; proph_name: gname }.
Global Instance subG_prophPreG Σ : subG prophΣ Σ → prophPreG Σ.
Proof. solve_inG. Qed.

Definition prophN: namespace := nroot .@ "proph".

(** ** Camera Facts *)

Local Lemma aitem_inj {𝔄i: syn_typei} (vπ wπ: proph 𝔄i) :
  Some (aitem vπ) ≡ Some (aitem wπ) → vπ = wπ.
Proof. by move=> /(inj (Some ∘ aitem)). Qed.
Local Lemma ritem_inj {𝔄i: syn_typei} ζl ζl' :
  Some (@ritem 𝔄i ζl) ≡ Some (ritem ζl') → ζl = ζl'.
Proof.
  move=> Eq. apply (inj Some) in Eq. apply (inj Cinr) in Eq.
  apply (inj Cinl) in Eq. by apply (inj Excl) in Eq.
Qed.
Local Lemma aitem_ritem_ne {𝔄i: syn_typei} (vπ: proph 𝔄i) ζl :
  ¬ Some (aitem vπ) ≡ Some (ritem ζl).
Proof. move=> Eq. apply (inj Some), (inj Cinr) in Eq. inversion Eq. Qed.
Local Lemma ritem_aitem_ne {𝔄i: syn_typei} (vπ: proph 𝔄i) ζl :
  ¬ Some (ritem ζl) ≡ Some (aitem vπ).
Proof. move=> Eq. apply (inj Some), (inj Cinr) in Eq. inversion Eq. Qed.

Local Lemma fitem_Cinr_included {𝔄i: syn_typei} q b : ¬ Some (@fitem 𝔄i q) ≼ Some (Cinr b).
Proof. by move=> /Some_csum_included [|[[?[?[_[?]]]]|[?[?[?]]]]]. Qed.

Local Lemma aitem_included {𝔄i: syn_typei} (vπ: proph 𝔄i) it :
  ✓ it → Some (aitem vπ) ≼ Some it → it ≡ aitem vπ.
Proof.
  rewrite /aitem.
  move=> Val /Some_included [?|Inc]; [done|].
  move: Inc Val=> /csum_included [->|[[?[?[??]]]|[b [b' [Eb [-> Inc]]]]]] //.
  move: Eb Inc=> [<-] Inc /Cinr_valid Val. f_equiv.
  move: Inc Val=> /csum_included [->|[[?[?[??]]]|[c [c' [Ec [-> Inc]]]]]] //.
  move: Ec Inc=> [<-] Inc /Cinr_valid /to_agree_uninj [w Ew]. f_equiv.
  rewrite -Ew in Inc *. by move: Inc=> /to_agree_included ->.
Qed.

Local Lemma add_line_lookup ξ it S : add_line ξ it S ξ.(pv_ty) !! ξ.(pv_id) = Some it.
Proof. by rewrite /add_line discrete_fun_lookup_insert lookup_insert. Qed.
Local Lemma add_line_lookup_ne ξ ζ it S : ξ ≠ ζ →
  add_line ξ it S ζ.(pv_ty) !! ζ.(pv_id) = S ζ.(pv_ty) !! ζ.(pv_id).
Proof.
  move: ξ it ζ=> [𝔄i i] it [𝔅i j] Ne. rewrite /add_line /discrete_fun_insert /=.
  case (decide (𝔄i = 𝔅i))=>// ?. subst=>/=.
  case (decide (i = j))=> [?|?]; [|by rewrite lookup_insert_ne]. by subst.
Qed.

(** * Iris Propositions *)

Local Definition proph_sim (S: proph_smryUR) (L: proph_log) :=
  (∀ξ vπ, S ξ.(pv_ty) !! ξ.(pv_id) ≡ Some (aitem vπ) ↔ (.{ξ := vπ}, None) ∈ L) ∧
  (∀ξ ζl, S ξ.(pv_ty) !! ξ.(pv_id) ≡ Some (ritem ζl) ↔
    ∃vπ, (.{ξ := vπ}, Some ζl) ∈ L).
Local Notation "S :~ L" := (proph_sim S L) (at level 70, format "S  :~  L").

(** ** Updating the Simulation *)

Local Lemma proph_sim_fitem S L L' ξ :
  S :~ L → (∀ e, ξ ≠ e.1.(pli_pv) → e ∈ L' ↔ e ∈ L) →
  (∀ wπ r, (.{ξ := wπ}, r) ∉ L') → add_line ξ (fitem 1) S :~ L'.
Proof.
  move=> [SimA SimR] Oth Here. split.
  - move=> ζ wπ. case (decide (ξ = ζ))=> [?|Ne].
    + subst ζ. rewrite add_line_lookup.
      split; [by move=> Eq; apply (inj Some) in Eq; inversion Eq|by move=> /Here].
    + rewrite add_line_lookup_ne; [|done]. by rewrite SimA Oth.
  - move=> ζ ζl. case (decide (ξ = ζ))=> [?|Ne].
    + subst ζ. rewrite add_line_lookup.
      split; [by move=> Eq; apply (inj Some) in Eq; inversion Eq|by move=> [? /Here]].
    + rewrite add_line_lookup_ne; [|done]. rewrite SimR.
      split=> [[w ?]|[w ?]]; exists w; by apply Oth.
Qed.

Local Lemma proph_sim_add S L L' ξ vπ r :
  S :~ L → (∀ e, ξ ≠ e.1.(pli_pv) → e ∈ L' ↔ e ∈ L) →
  (∀ wπ r', (.{ξ := wπ}, r') ∈ L' ↔ (wπ, r') = (vπ, r)) →
  add_line ξ (ent_item vπ r) S :~ L'.
Proof.
  move=> [SimA SimR] Oth Here. split.
  - move=> ζ wπ. case (decide (ξ = ζ))=> [?|Ne].
    + subst ζ. rewrite add_line_lookup Here. destruct r as [ζl|]=>/=; split.
      * by move=> /ritem_aitem_ne.
      * by move=> [=].
      * by move=> /aitem_inj ->.
      * by move=> [= ->].
    + rewrite add_line_lookup_ne; [|done]. by rewrite SimA Oth.
  - move=> ζ ζl. case (decide (ξ = ζ))=> [?|Ne].
    + subst ζ. rewrite add_line_lookup. setoid_rewrite Here.
      destruct r as [ζl'|]=>/=; split.
      * move=> /ritem_inj ->. by exists vπ.
      * by move=> [? [= _ ->]].
      * by move=> /aitem_ritem_ne.
      * by move=> [? [=]].
    + rewrite add_line_lookup_ne; [|done]. rewrite SimR.
      split=> [[w ?]|[w ?]]; exists w; by apply Oth.
Qed.

Local Lemma proph_sim_fresh S L ξ :
  S :~ L → S ξ.(pv_ty) !! ξ.(pv_id) = None → add_line ξ (fitem 1) S :~ L.
Proof.
  move=> Sim EqNone. apply (proph_sim_fitem _ _ _ _ Sim); [done|].
  move=> wπ [ζl|] In.
  - have: S ξ.(pv_ty) !! ξ.(pv_id) ≡ Some (ritem ζl).
    { apply (proj2 Sim ξ ζl). by exists wπ. }
    rewrite EqNone. by inversion 1.
  - have: S ξ.(pv_ty) !! ξ.(pv_id) ≡ Some (aitem wπ) by apply (proj1 Sim ξ wπ).
    rewrite EqNone. by inversion 1.
Qed.

Local Lemma proph_sim_cons S L ξ vπ r :
  S :~ L → ξ ∉ res L → add_line ξ (ent_item vπ r) S :~ (.{ξ := vπ}, r) :: L.
Proof.
  move=> Sim Out. apply (proph_sim_add _ _ _ _ _ _ Sim).
  - move=> e Ne. rewrite elem_of_cons.
    have ?: e ≠ (.{ξ := vπ}, r) by move=> ?; subst e; by apply Ne.
    tauto.
  - move=> wπ r'. rewrite elem_of_cons pli_ent_eq.
    have ?: (.{ξ := wπ}, r') ∉ L by move=> /res_elem /Out.
    tauto.
Qed.

Local Lemma proph_sim_replace S L1 L2 ξ vπ r vπ' r' :
  S :~ L1 ++ (.{ξ := vπ}, r) :: L2 → ξ ∉ res (L1 ++ L2) →
  add_line ξ (ent_item vπ' r') S :~ L1 ++ (.{ξ := vπ'}, r') :: L2.
Proof.
  move=> Sim Out. apply (proph_sim_add _ _ _ _ _ _ Sim).
  - move=> e Ne. rewrite !elem_of_app !elem_of_cons.
    have Ne': ∀ wπ r'', e ≠ (.{ξ := wπ}, r'') by move=> ?? ?; subst e; by apply Ne.
    move: (Ne' vπ r) (Ne' vπ' r'). tauto.
  - move=> wπ r''. rewrite !elem_of_app elem_of_cons pli_ent_eq.
    have: (.{ξ := wπ}, r'') ∉ L1 ++ L2 by move=> /res_elem /Out.
    rewrite elem_of_app. tauto.
Qed.

Local Lemma proph_sim_delete S L1 L2 ξ vπ r :
  S :~ L1 ++ (.{ξ := vπ}, r) :: L2 → ξ ∉ res (L1 ++ L2) →
  add_line ξ (fitem 1) S :~ L1 ++ L2.
Proof.
  move=> Sim Out. apply (proph_sim_fitem _ _ _ _ Sim).
  - move=> e Ne. rewrite !elem_of_app elem_of_cons.
    have ?: e ≠ (.{ξ := vπ}, r) by move=> ?; subst e; by apply Ne.
    tauto.
  - by move=> ?? /res_elem /Out.
Qed.

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

(** Resolution Reservation *)
(** [proph_reserved ξ ζl] is obtained by giving up [1:[ξ]]. It commits [ξ] to
  be (possibly) resolved later to a value depending on [ζl] (and on currently
  unresolved variables), without requiring tokens for [ζl] at that time. *)
Definition proph_reserved (ξ: proph_var) (ζl: list proph_var) : iProp Σ :=
  own proph_name (◯ line ξ (ritem ζl)).
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
  iExists ε. iFrame "●ε". iPureIntro. exists []. split; [done|].
  split=> ??; rewrite lookup_empty; (split; [by inversion 1|]).
  - by move=> /elem_of_nil.
  - by move=> [? /elem_of_nil].
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
  split; [done|]. by apply proph_sim_fresh.
Qed.

(** Prophecy Resolution *)

Local Lemma proph_tok_out S L ξ q :
  S :~ L → own proph_name (● S) -∗ q:[ξ] -∗ ⌜ξ ∉ res L⌝.
Proof.
  move=> [SimA SimR]. iIntros "●S ξ".
  iDestruct (own_valid_2 with "●S ξ") as %ValBoth. iPureIntro.
  rewrite /res. move=> /elem_of_list_fmap [[[[𝔄i i] vπ] r] [/= ? In]]. subst ξ.
  move: ValBoth=> /auth_both_valid_discrete [Inc _].
  move/(discrete_fun_included_spec_1 _ _ 𝔄i) in Inc.
  rewrite /line discrete_fun_lookup_singleton /= in Inc.
  move: Inc=> /singleton_included_l [it [Eqv Inc]].
  have: Some it ≡ Some (ent_item vπ r).
  { rewrite -Eqv. destruct r as [ζl|]=>/=.
    - apply (SimR (PrVar 𝔄i i) ζl). by exists vπ.
    - by apply (SimA (PrVar 𝔄i i)). }
  move=> Eqit. apply (inj Some) in Eqit. move: Inc. rewrite Eqit.
  destruct r; by apply fitem_Cinr_included.
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
  iIntros (? Dep) "P→ ? ξ P". iInv prophN as (S) ">[(%L & % & %Sim) ●S]".
  iDestruct (proph_tok_out with "●S ξ") as %Outξ; [done|].
  iAssert ⌜∀ζ, ζ ∈ ζl → ζ ∉ ξ :: res L⌝%I as %Outζl.
  { iIntros (??). iDestruct ("P→" with "[//] P") as (?) "ζ".
    iDestruct (proph_tok_ne with "ξ ζ") as %?.
    iDestruct (proph_tok_out with "●S ζ") as %?; [done|].
    iPureIntro. rewrite not_elem_of_cons. split; [by apply not_eq_sym|done]. }
  set S' := add_line ξ (aitem vπ) S.
  iMod (own_update_2 _ _ _ (● S' ⋅ ◯ line ξ (aitem vπ)) with "●S ξ")
    as "[●S' #?]".
  { apply auth_update, discrete_fun_singleton_local_update_any,
      singleton_local_update_any => ? _. by apply exclusive_local_update. }
  iModIntro. iSplitL "●S'"; last first.
  { iModIntro. iFrame "P". iExists [.{ξ := vπ}]. rewrite big_sepL_singleton.
    iSplitR; [|done]. iPureIntro=> ? Sat. by inversion Sat. }
  iModIntro. iExists S'. iFrame "●S'". iPureIntro.
  exists ((.{ξ := vπ}, None) :: L). split.
  { split; [done| split; [|done]] => ?? Eqv. apply Dep => ? /Outζl ?. by apply Eqv. }
  by apply (proph_sim_cons S L ξ vπ None).
Qed.

Lemma proph_resolve_toks E ξ vπ ζl q : ↑prophN ⊆ E → vπ ./ ζl →
  proph_ctx -∗ 1:[ξ] -∗ q:+[ζl] ={E}=∗ ⟨π, π ξ = vπ π⟩ ∗ q:+[ζl].
Proof.
  iIntros (??). iApply proph_resolve=>//. iIntros (??) "ζl". iExists _. 
  by iApply (big_sepL_elem_of with "ζl").
Qed.

(** Resolution Reservations *)

Global Instance proph_reserved_timeless ξ ζl : Timeless (proph_reserved ξ ζl) := _.

Lemma proph_reserved_tok_excl ξ ζl q : proph_reserved ξ ζl -∗ q:[ξ] -∗ False.
Proof.
  iIntros "ξ ξ'". iDestruct (own_valid_2 with "ξ ξ'") as %ValBoth. iPureIntro.
  move: ValBoth. rewrite -auth_frag_op auth_frag_valid discrete_fun_singleton_op
    discrete_fun_singleton_valid singleton_op singleton_valid.
  apply exclusive_l, _.
Qed.

Lemma proph_reserved_excl ξ ζl ζl' :
  proph_reserved ξ ζl -∗ proph_reserved ξ ζl' -∗ False.
Proof.
  iIntros "ξ ξ'". iDestruct (own_valid_2 with "ξ ξ'") as %ValBoth. iPureIntro.
  move: ValBoth. rewrite -auth_frag_op auth_frag_valid discrete_fun_singleton_op
    discrete_fun_singleton_valid singleton_op singleton_valid.
  apply exclusive_l, _.
Qed.

Local Lemma proph_reserved_lookup S ξ ζl :
  own proph_name (● S) -∗ proph_reserved ξ ζl -∗
    ⌜S ξ.(pv_ty) !! ξ.(pv_id) ≡ Some (ritem ζl)⌝.
Proof.
  iIntros "●S ξ". iDestruct (own_valid_2 with "●S ξ") as %ValBoth. iPureIntro.
  move: ValBoth=> /auth_both_valid_discrete [Inc Val].
  move/(discrete_fun_included_spec_1 _ _ ξ.(pv_ty)) in Inc.
  rewrite /line discrete_fun_lookup_singleton in Inc.
  move: Inc=> /singleton_included_l [it [Eqv Inc]]. rewrite Eqv. f_equiv.
  have ?: ✓ it by apply (lookup_valid_Some (S ξ.(pv_ty)) ξ.(pv_id)); [apply Val|].
  symmetry. by apply: Some_included_exclusive.
Qed.

(** Unresolved variables are not resolved, nor reserved, in the log *)
Local Lemma proph_toks_out S L P ζl :
  S :~ L → (∀ ζ, ⌜ζ ∈ ζl⌝ → P -∗ ∃ q, q:[ζ]) -∗ own proph_name (● S) -∗ P -∗
    ⌜∀ζ, ζ ∈ ζl → ζ ∉ res L⌝.
Proof.
  iIntros (Sim) "P→ ●S P". iIntros (??).
  iDestruct ("P→" with "[//] P") as (?) "ζ". by iApply (proph_tok_out with "●S ζ").
Qed.

Lemma proph_reserve E ξ ζl q : ↑prophN ⊆ E →
  proph_ctx -∗ 1:[ξ] -∗ q:+[ζl] ={E}=∗ proph_reserved ξ ζl ∗ q:+[ζl].
Proof.
  iIntros (?) "? ξ ζl". iInv prophN as (S) ">[(%L & % & %Sim) ●S]".
  iDestruct (proph_tok_out with "●S ξ") as %Outξ; [done|].
  iAssert ⌜∀ζ, ζ ∈ ζl → ζ ∉ ξ :: res L⌝%I as %Outζl.
  { iIntros (ζ ?). iDestruct (big_sepL_elem_of with "ζl") as "ζ"; [done|].
    iDestruct (proph_tok_ne with "ξ ζ") as %?.
    iDestruct (proph_tok_out with "●S ζ") as %?; [done|].
    iPureIntro. rewrite not_elem_of_cons. split; [by apply not_eq_sym|done]. }
  set S' := add_line ξ (ritem ζl) S.
  iMod (own_update_2 _ _ _ (● S' ⋅ ◯ line ξ (ritem ζl)) with "●S ξ")
    as "[●S' ξ]".
  { apply auth_update, discrete_fun_singleton_local_update_any,
      singleton_local_update_any => ? _. by apply exclusive_local_update. }
  iModIntro. iSplitL "●S'"; [|by iFrame].
  iModIntro. iExists S'. iFrame "●S'". iPureIntro.
  exists ((.{ξ := λ _, inhabitant}, Some ζl) :: L). split.
  { split; [done|]. split; [by move=> ???|]. by split. }
  by apply (proph_sim_cons S L ξ (λ _, inhabitant) (Some ζl)).
Qed.

Lemma proph_unreserve E ξ ζl : ↑prophN ⊆ E →
  proph_ctx -∗ proph_reserved ξ ζl ={E}=∗ 1:[ξ].
Proof.
  iIntros (?) "? ξ". iInv prophN as (S) ">[(%L & %Ok & %Sim) ●S]".
  iDestruct (proph_reserved_lookup with "●S ξ") as %Eqv.
  have [vπ In] := proj1 (proj2 Sim ξ ζl) Eqv.
  destruct (elem_of_list_split _ _ In) as [L1 [L2 Eq]].
  subst L. set S' := add_line ξ (fitem 1) S.
  iMod (own_update_2 _ _ _ (● S' ⋅ ◯ line ξ (fitem 1)) with "●S ξ")
    as "[●S' ξ]".
  { apply auth_update, discrete_fun_singleton_local_update_any,
      singleton_local_update_any => ? _. by apply exclusive_local_update. }
  iModIntro. iSplitL "●S'"; [|done].
  iModIntro. iExists S'. iFrame "●S'". iPureIntro.
  exists (L1 ++ L2). split; [by eapply proph_log_ok_delete|].
  apply: proph_sim_delete; [done|].
  by apply (proph_log_ok_unique L1 (.{ξ := vπ}, Some ζl) L2).
Qed.

Lemma proph_reserve_extend E ξ ζl ζl' q : ↑prophN ⊆ E →
  proph_ctx -∗ proph_reserved ξ ζl -∗ q:+[ζl'] ={E}=∗
    proph_reserved ξ (ζl ++ ζl') ∗ q:+[ζl'].
Proof.
  iIntros (?) "? ξ ζl'". iInv prophN as (S) ">[(%L & %Ok & %Sim) ●S]".
  iDestruct (proph_reserved_lookup with "●S ξ") as %Eqv.
  have [vπ In] := proj1 (proj2 Sim ξ ζl) Eqv.
  destruct (elem_of_list_split _ _ In) as [L1 [L2 Eq]].
  subst L. iDestruct (proph_toks_out _ _ _ ζl' with "[] ●S ζl'") as %Outζl'; [done| |].
  { iIntros (??) "ζl'". iExists _. by iApply (big_sepL_elem_of with "ζl'"). }
  set S' := add_line ξ (ritem (ζl ++ ζl')) S.
  iMod (own_update_2 _ _ _ (● S' ⋅ ◯ line ξ (ritem (ζl ++ ζl'))) with "●S ξ")
    as "[●S' ξ]".
  { apply auth_update, discrete_fun_singleton_local_update_any,
      singleton_local_update_any => ? _. by apply exclusive_local_update. }
  iModIntro. iSplitL "●S'"; [|by iFrame].
  iModIntro. iExists S'. iFrame "●S'". iPureIntro.
  have [? [? [Rsv ?]]] := proph_log_ok_suffix L1 _ Ok.
  exists (L1 ++ (.{ξ := vπ}, Some (ζl ++ ζl')) :: L2). split.
  { apply (proph_log_ok_replace L1 (.{ξ := vπ}, Some ζl)); [done| |done].
    split; [done|]. split; [done|]. split; [|done].
    move=> ζ /elem_of_app [/Rsv //|/Outζl' Out]. rewrite res_app_cons in Out.
    set_solver. }
  apply (proph_sim_replace S L1 L2 ξ vπ (Some ζl) vπ (Some (ζl ++ ζl'))); [done|].
  by apply (proph_log_ok_unique L1 (.{ξ := vπ}, Some ζl) L2).
Qed.

Lemma proph_resolve_reserved_gen P E ξ vπ ζl ηl : ↑prophN ⊆ E → vπ ./ ζl ++ ηl →
  (∀ η, ⌜η ∈ ηl⌝ → P -∗ ∃ q, q:[η]) -∗
  proph_ctx -∗ proph_reserved ξ ζl -∗ P ={E}=∗ ⟨π, π ξ = vπ π⟩ ∗ P.
Proof.
  iIntros (? Dep) "P→ ? ξ P". iInv prophN as (S) ">[(%L & %Ok & %Sim) ●S]".
  iDestruct (proph_reserved_lookup with "●S ξ") as %Eqv.
  have [wπ In] := proj1 (proj2 Sim ξ ζl) Eqv.
  destruct (elem_of_list_split _ _ In) as [L1 [L2 Eq]].
  subst L. iDestruct (proph_toks_out with "P→ ●S P") as %Outηl; [done|].
  set S' := add_line ξ (aitem vπ) S.
  iMod (own_update_2 _ _ _ (● S' ⋅ ◯ line ξ (aitem vπ)) with "●S ξ")
    as "[●S' #?]".
  { apply auth_update, discrete_fun_singleton_local_update_any,
      singleton_local_update_any => ? _. by apply exclusive_local_update. }
  iModIntro. iSplitL "●S'"; last first.
  { iModIntro. iFrame "P". iExists [.{ξ := vπ}]. rewrite big_sepL_singleton.
    iSplitR; [|done]. iPureIntro=> ? Sat. by inversion Sat. }
  iModIntro. iExists S'. iFrame "●S'". iPureIntro.
  have [? [? [Rsv ?]]] := proph_log_ok_suffix L1 _ Ok.
  exists (L1 ++ (.{ξ := vπ}, None) :: L2). split.
  { apply (proph_log_ok_replace L1 (.{ξ := wπ}, Some ζl)); [done| |done].
    split; [done|]. split; [|by split].
    move=> ?? Eqv'. apply Dep=> ζ /elem_of_app [/Rsv ?|/Outηl Out]; apply Eqv'; [done|].
    rewrite res_app_cons in Out. set_solver. }
  apply (proph_sim_replace S L1 L2 ξ wπ (Some ζl) vπ None); [done|].
  by apply (proph_log_ok_unique L1 (.{ξ := wπ}, Some ζl) L2).
Qed.

Lemma proph_resolve_reserved E ξ vπ ζl ηl q : ↑prophN ⊆ E → vπ ./ ζl ++ ηl →
  proph_ctx -∗ proph_reserved ξ ζl -∗ q:+[ηl] ={E}=∗ ⟨π, π ξ = vπ π⟩ ∗ q:+[ηl].
Proof.
  iIntros (??). iApply proph_resolve_reserved_gen=>//. iIntros (??) "ηl". iExists _.
  by iApply (big_sepL_elem_of with "ηl").
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
  move: ValBoth=> /auth_both_valid_discrete [Inc Val]. apply (Sat .{ξ := vπ}).
  apply (elem_of_list_fmap_1 fst L (.{ξ := vπ}, None)), (proj1 Sim ξ vπ).
  move/(discrete_fun_included_spec_1 _ _ 𝔄i) in Inc.
  rewrite /line discrete_fun_lookup_singleton in Inc.
  move: Inc=> /singleton_included_l [it [Eqv Inc]]. rewrite Eqv. f_equiv.
  apply aitem_included; [|done]. by apply (lookup_valid_Some (S 𝔄i) i it); [apply Val|].
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

Global Opaque proph_ctx proph_tok proph_obs proph_reserved.

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
