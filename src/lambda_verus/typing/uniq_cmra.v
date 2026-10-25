From iris.algebra Require Import auth cmra functions gmap dfrac_agree.
From iris.proofmode Require Import proofmode.
From iris.base_logic Require Import invariants.
From lrust.util Require Import discrete_fun update cancellable.
From lrust.prophecy Require Import prophecy.
From guarding Require Import guard own_and tactics.

From lrust.lifetime Require Import lifetime_full.

Implicit Type (𝔄i: syn_typei) (𝔄: syn_type).

(** * Camera for Unique Borrowing *)

(** An item records whether the prophecy variable is resolved ("done"), its
  reservation (if any; see [proph_reserved]), and the current value. *)
Local Definition uniq_itemR 𝔄i :=
  dfrac_agreeR (leibnizO (bool * option (list proph_var) * (~~ (`𝔄i)))).
Local Definition uniq_gmapUR 𝔄i := gmapUR positive (uniq_itemR 𝔄i).
Local Definition uniq_smryUR := discrete_funUR uniq_gmapUR.
Definition uniqUR: ucmra := authUR uniq_smryUR.

Local Definition item {𝔄i} q b r x : uniq_itemR 𝔄i :=
  @to_frac_agree (leibnizO _) q (b, r, x).
Local Definition line ξ q b r x : uniq_smryUR :=
  .{[ξ.(pv_ty) := {[ξ.(pv_id) := item q b r x]}]}.
Local Definition add_line ξ q b r x (S: uniq_smryUR) : uniq_smryUR :=
  .<[ξ.(pv_ty) := <[ξ.(pv_id) := item q b r x]> (S ξ.(pv_ty))]> S.

Definition uniqΣ: gFunctors := #[GFunctor uniqUR; cnaInv_logicΣ].
Class uniqPreG Σ := UniqPreG {
  #[global] uniq_preG_inG :: inG Σ uniqUR ;
  #[global] type_cnaInv_logicΣ :: cnaInv_logicG Σ
}.
Class uniqG Σ := UniqG { #[global] uniq_inG :: uniqPreG Σ; uniq_name: gname; atomic_pool_name: gname }.
Global Instance subG_uniqPreG Σ : subG uniqΣ Σ → uniqPreG Σ.
Proof. solve_inG. Qed.

Definition uniqN: namespace := NllftUsr .@ "uniq".

(** * Iris Propositions *)

Section defs.
Context `{!invGS Σ, !prophG Σ, !uniqG Σ}.

Definition SendN : namespace := nroot .@ "send_guard".

(** Unique Reference Context *)
Definition uniq_inv: iProp Σ := ∃S, own uniq_name (● S).
Definition uniq_ctx: iProp Σ := inv uniqN uniq_inv
    (* the atomic pool actually has nothing to do with uniq borrows, but I didn't want
       to go through the effort of making a new ctx proposition for this, so I reused
       this one *)
    ∗ (True &&{↑SendN}&&> (cna_lifetimes atomic_pool_name ∅)).

Lemma uniq_ctx_get_cna_lifetimes_inv :
    uniq_ctx -∗ (True &&{↑SendN}&&> (cna_lifetimes atomic_pool_name ∅)).
Proof. iIntros "[_ $]". Qed.

Local Definition own_line ξ q b r x := own uniq_name (◯ line ξ q b r x).

(** Value Observer *)
Definition val_obs (ξ: proph_var) x : iProp Σ :=
  own_line ξ (1/2) false None x.

(** Reserved Value Observer: like [val_obs], but the prophecy variable [ξ] has
  been reserved (see [proph_reserved]) for the dependencies [ζl]. *)
Definition val_obs_rsv (ξ: proph_var) (ζl: list proph_var) x : iProp Σ :=
  own_line ξ (1/2) false (Some ζl) x.

Local Definition val_obs2 ξ x : iProp Σ := own_line ξ 1 false None x.

Local Definition val_obs2_rsv ξ ζl x : iProp Σ := own_line ξ 1 false (Some ζl) x.

Local Definition val_obs2_done ξ x : iProp Σ := own_line ξ 1 true None x.

(** Prophecy Controller *)  (* TODO vπ arg is superfluous, it's always `vπ x` *)
(** The controller is in one of three states: unresolved (paired with [.VO]),
  reserved (paired with [.VOR]), or resolved. *)
Definition proph_ctrl (ξ: proph_var) x (vπ: proph ξ.(pv_ty)) : iProp Σ :=
  (val_obs ξ x ∗ 1:[ξ]) ∨
  (∃ζl, val_obs_rsv ξ ζl x ∗ proph_reserved ξ ζl) ∨
  ((∃x', val_obs2_done ξ x') ∗ (.$ ξ) :== vπ).
End defs.

Notation ".VO[ ξ ]" := (val_obs ξ) (at level 5, format ".VO[ ξ ]") : bi_scope.
Notation ".VOR[ ξ ; ζl ]" := (val_obs_rsv ξ ζl)
  (at level 5, format ".VOR[ ξ ; ζl ]") : bi_scope.
Local Notation ".VO2[ ξ ]" := (val_obs2 ξ)
  (at level 5, format ".VO2[ ξ ]") : bi_scope.
Local Notation ".VO2R[ ξ ; ζl ]" := (val_obs2_rsv ξ ζl)
  (at level 5, format ".VO2R[ ξ ; ζl ]") : bi_scope.
Notation ".PC[ ξ ]" := (proph_ctrl ξ)
  (at level 5, format ".PC[ ξ ]") : bi_scope.

(** * Lemmas *)

Definition prval_to_inh {𝔄} (vπ: proph 𝔄) : inh_syn_type 𝔄 :=
  to_inh_syn_type (vπ inhabitant).

Section lemmas.
Context `{!invGS Σ, !prophG Σ, !uniqG Σ}.

Global Instance uniq_ctx_persistent : Persistent uniq_ctx := _.
Global Instance val_obs_timeless ξ x : Timeless (.VO[ξ] x) := _.
Global Instance val_obs_rsv_timeless ξ ζl x : Timeless (.VOR[ξ;ζl] x) := _.

Global Instance proph_ctrl_proper ξ :
  Proper ((=) ==> pointwise_relation _ (=) ==> (⊣⊢)) (proph_ctrl ξ).
Proof.
  move=> ?? E1 ?? E2. rewrite /proph_ctrl. subst. do 3 f_equiv.
  setoid_rewrite E2. trivial.
Qed.

Local Lemma own_line_agree ξ q q' b r x b' r' x' :
  own_line ξ q b r x -∗ own_line ξ q' b' r' x' -∗
    ⌜(q + q' ≤ 1)%Qp ∧ x = x' ∧ b = b' ∧ r = r'⌝.
Proof.
  iIntros "line line'". iDestruct (own_valid_2 with "line line'") as %Val.
  iPureIntro. move: Val.
  rewrite -auth_frag_op auth_frag_valid discrete_fun_singleton_op
    discrete_fun_singleton_valid singleton_op singleton_valid.
  by move/frac_agree_op_valid=> [?[= ???]].
Qed.

Local Lemma auth_view_valid_frag au fr : ✓ (View au fr : uniqUR) → ✓ fr.
Proof.
  case: au; [|by apply auth_frag_valid]. move=> [dq ag] [_ valx].
  case: (valx 0)=>/= ?[_[/cmra_discrete_included_r + /cmra_discrete_valid ?]].
  exact: cmra_valid_included.
Qed.

Local Lemma auth_frag_view_included au fr fr' :
  ◯ fr' ≼ (View au fr : uniqUR) → fr' ≼ fr.
Proof. move=> [[??][/=??]]. by eexists _. Qed.

Local Lemma line_included fr ξ q b r x :
  line ξ q b r x ≼ fr → Some (item q b r x) ≼ fr (pv_ty ξ) !! pv_id ξ.
Proof.
  move=> /(discrete_fun_included_spec_1 _ _ ξ.(pv_ty)).
  setoid_rewrite discrete_fun_lookup_singleton. rewrite lookup_included=> inc.
  move: {inc}(inc (pv_id ξ)). by rewrite lookup_singleton.
Qed.

Local Lemma and_line_agree ξ q q' b r x b' r' x' :
  own_line ξ q b r x ∧ own_line ξ q' b' r' x' ⊢ ⌜x = x' ∧ b = b' ∧ r = r'⌝.
Proof.
  rewrite and_own_discrete. iDestruct 1 as ([au fr]) "H". rewrite own_valid.
  iDestruct "H" as %[val incs]. iPureIntro. move: val=> /auth_view_valid_frag val.
  move: incs=> [/Some_included_total/auth_frag_view_included/line_included +
    /Some_included_total/auth_frag_view_included/line_included +].
  move: {val}(val (pv_ty ξ) (pv_id ξ)).
  case: (fr (pv_ty ξ) !! pv_id ξ); last by move=> _ /Some_included_is_Some[].
  move=> [? ag] [/=_ ?] /Some_pair_included_r/Some_included_total inc
    /Some_pair_included_r/Some_included_total inc'.
  apply agree_valid_included in inc=>//. apply agree_valid_included in inc'=>//.
  move: inc. by rewrite -inc'=> /to_agree_inj/leibniz_equiv_iff[=].
Qed.

Local Lemma own_line_half ξ b r x :
  own_line ξ (1/2) b r x ∗ own_line ξ (1/2) b r x ⊣⊢ own_line ξ 1 b r x.
Proof.
  by rewrite -own_op -auth_frag_op discrete_fun_singleton_op singleton_op /item
    -frac_agree_op Qp.half_half.
Qed.

Local Lemma vo_vo2 ξ x : .VO[ξ] x ∗ .VO[ξ] x ⊣⊢ .VO2[ξ] x.
Proof. apply own_line_half. Qed.

Local Lemma vor_vor2 ξ ζl x : .VOR[ξ;ζl] x ∗ .VOR[ξ;ζl] x ⊣⊢ .VO2R[ξ;ζl] x.
Proof. apply own_line_half. Qed.

Local Lemma vo_pc ξ x x' vπ' :
  .VO[ξ] x -∗ .PC[ξ] x' vπ' -∗ ⌜x = x'⌝ ∗ .VO2[ξ] x ∗ 1:[ξ].
Proof.
  iIntros "Vo [[Vo' ?]|[(%& Vo' & _)|[(%& Vo2) _]]]";
  [|by iDestruct (own_line_agree with "Vo Vo'") as %[_[_[_ ?]]]
   |by iDestruct (own_line_agree with "Vo Vo2") as %[? _]].
  iDestruct (own_line_agree with "Vo Vo'") as %[A[B C]].
  iSplit; [done|]. rewrite -vo_vo2. iFrame. subst x. iFrame.
Qed.

Local Lemma vor_pc ξ ζl x x' vπ' :
  .VOR[ξ;ζl] x -∗ .PC[ξ] x' vπ' -∗ ⌜x = x'⌝ ∗ .VO2R[ξ;ζl] x ∗ proph_reserved ξ ζl.
Proof.
  iIntros "Vo [[Vo' _]|[(%ζl' & Vo' & ξ)|[(%& Vo2) _]]]".
  - by iDestruct (own_line_agree with "Vo Vo'") as %[_[_[_ ?]]].
  - iDestruct (own_line_agree with "Vo Vo'") as %[_[<-[_ [= <-]]]].
    iSplit; [done|]. rewrite -vor_vor2. iFrame.
  - by iDestruct (own_line_agree with "Vo Vo2") as %[? _].
Qed.

Local Lemma own_line_update ξ b r x b' r' x' E :
    ↑uniqN ⊆ E →
    uniq_ctx -∗ own_line ξ 1 b r x ={E}=∗ own_line ξ 1 b' r' x'.
Proof.
  iIntros (?) "[#? _] Vo2".
  iInv uniqN as (S) ">●S". set S' := add_line ξ 1 b' r' x' S.
  iMod (own_update_2 _ _ _ (● S' ⋅ ◯ line ξ 1 b' r' x') with "●S Vo2") as "[? Vo2]".
  { apply auth_update, discrete_fun_singleton_local_update_any,
    singleton_local_update_any => ? _. by apply exclusive_local_update. }
  iModIntro. iSplitR "Vo2"; [by iExists S'|]. iModIntro.
  iFrame.
Qed.

Local Lemma vo2_vo2_done ξ x E :
    ↑uniqN ⊆ E →
    uniq_ctx -∗ .VO2[ξ] x ={E}=∗ val_obs2_done ξ x.
Proof. apply own_line_update. Qed.

Local Lemma vo2r_vo2_done ξ ζl x E :
    ↑uniqN ⊆ E →
    uniq_ctx -∗ .VO2R[ξ;ζl] x ={E}=∗ val_obs2_done ξ x.
Proof. apply own_line_update. Qed.

Local Lemma proph_dep_incl {A} (vπ: proph A) ζl ζl' :
  vπ ./ ζl → (∀ζ, ζ ∈ ζl → ζ ∈ ζl') → vπ ./ ζl'.
Proof. move=> Dep Incl ?? Eqv. apply Dep=> ??. by apply Eqv, Incl. Qed.

(** A reservation for [ξ] yields an equalizer for [ξ]. *)
Local Lemma proph_eqz_reserved ξ ζl vπ :
  proph_ctx -∗ proph_reserved ξ ζl -∗ (.$ ξ) :== vπ.
Proof.
  iIntros "PROPH ξ" (???[? Dep]) "ξl".
  iMod (proph_resolve_reserved _ _ _ ζl with "PROPH ξ ξl") as "[$ $]"; [done| |done].
  apply (proph_dep_incl _ _ _ Dep)=> ??. set_solver.
Qed.

(** Initialization *)

Lemma uniq_init `{!uniqPreG Σ} E :
  ↑uniqN ⊆ E → ⊢ |={E}=> ∃_: uniqG Σ, uniq_ctx.
Proof.
  move=> ?. iMod (own_alloc (● ε)) as (γ) "●ε"; [by apply auth_auth_valid|].
  iMod (cna_pool_alloc) as (p) "[_ cna_lifetimes]".
  iMod (guards_alloc _ SendN with "cna_lifetimes") as "#G".
  iDestruct (guards_remove_later_rhs with "G") as "G'".
  set IUniqG := UniqG Σ _ γ p. iExists IUniqG. iFrame "G'".
  iMod (inv_alloc _ _ uniq_inv with "[●ε]") as "?"; by [iExists ε|].
Qed.

Lemma uniq_intro {𝔄} (x: ~~𝔄) (vπ: proph 𝔄) E :
  ↑prophN ∪ ↑uniqN ⊆ E → proph_ctx -∗ uniq_ctx ={E}=∗ ∃ξi,
    let ξ := PrVar (𝔄 ↾ prval_to_inh vπ) ξi in .VO[ξ] x ∗ .PC[ξ] x vπ.
Proof.
  iIntros (?) "PROPH [? _]". iInv uniqN as (S) ">●S".
  set 𝔄i := 𝔄 ↾ prval_to_inh vπ. set I := dom (S 𝔄i).
  iMod (proph_intro 𝔄i I with "PROPH") as (ξi NIn) "ξ"; [by solve_ndisj|].
  set ξ := PrVar 𝔄i ξi. set S' := add_line ξ 1 false None x S.
  move: NIn=> /not_elem_of_dom ?.
  iMod (own_update _ _ (● S' ⋅ ◯ line ξ 1 false None x) with "●S") as "[? Vo2]".
  { by apply auth_update_alloc,
      discrete_fun_insert_local_update, alloc_singleton_local_update. }
  iModIntro. iSplitR "Vo2 ξ"; [by iExists S'|]. iModIntro. iExists ξi.
  iDestruct (vo_vo2 with "Vo2") as "[$?]". iLeft. iFrame.
Qed.

Lemma uniq_strip_later ξ x x' vπ' :
  ▷ .VO[ξ] x -∗ ▷ .PC[ξ] x' vπ' -∗
    ◇ (⌜x = x'⌝ ∗ .VO[ξ] x ∗ .PC[ξ] x' vπ').
Proof.
  iIntros ">Vo [>[Vo' ?]|[>(%& Vo' & _)|[>(%& Vo2) _]]]";
  [|by iDestruct (own_line_agree with "Vo Vo'") as %[_[_[_ ?]]]
   |by iDestruct (own_line_agree with "Vo Vo2") as %[? _]].
  iDestruct (own_line_agree with "Vo Vo'") as %[_ [-> _]]. iModIntro.
  iSplit; [done|]. iSplitL "Vo"; [done|]. iLeft. by iSplitL "Vo'".
Qed.

Lemma uniq_rsv_strip_later ξ ζl x x' vπ' :
  ▷ .VOR[ξ;ζl] x -∗ ▷ .PC[ξ] x' vπ' -∗
    ◇ (⌜x = x'⌝ ∗ .VOR[ξ;ζl] x ∗ .PC[ξ] x' vπ').
Proof.
  iIntros ">Vo [>[Vo' _]|[>(%ζl' & Vo' & ξ)|[>(%& Vo2) _]]]".
  - by iDestruct (own_line_agree with "Vo Vo'") as %[_[_[_ ?]]].
  - iDestruct (own_line_agree with "Vo Vo'") as %[_[->[_ [= <-]]]]. iModIntro.
    iSplit; [done|]. iSplitL "Vo"; [done|]. iRight. iLeft. iExists ζl. iFrame.
  - by iDestruct (own_line_agree with "Vo Vo2") as %[? _].
Qed.

Lemma uniq_agree ξ x x' vπ' :
  .VO[ξ] x -∗ .PC[ξ] x' vπ' -∗ ⌜x = x'⌝.
Proof.
  iIntros "Vo Pc". by iDestruct (vo_pc with "Vo Pc") as (->) "?".
Qed.

Lemma uniq_rsv_agree ξ ζl x x' vπ' :
  .VOR[ξ;ζl] x -∗ .PC[ξ] x' vπ' -∗ ⌜x = x'⌝.
Proof.
  iIntros "Vo Pc". by iDestruct (vor_pc with "Vo Pc") as (->) "?".
Qed.

Lemma uniq_and_agree ξ x x' vπ' :
  .VO[ξ] x ∧ .PC[ξ] x' vπ' -∗ ⌜x = x'⌝.
Proof.
  iIntros "A". unfold proph_ctrl. rewrite !bi.and_or_l. iDestruct "A" as "[A|[A|A]]".
  - iDestruct (and_line_agree with "[A]") as "[-> _]". { iSplit.
      { iDestruct "A" as "[$ _]". } { iDestruct "A" as "[_ [$ _]]". } } done.
  - rewrite bi.and_exist_l. iDestruct "A" as (ζl) "A".
    iDestruct (and_line_agree with "[A]") as "[_ [_ %Heq]]". { iSplit.
      { iDestruct "A" as "[$ _]". } { iDestruct "A" as "[_ [$ _]]". } } discriminate.
  - iAssert (_ ∧ _)%I with "[A]" as "A". { iSplit. { iDestruct "A" as "[X _]". iApply "X". }
      { iDestruct "A" as "[_ [X _]]". iApply "X". } }
    rewrite bi.and_exist_l. iDestruct "A" as (x'') "A".
    iDestruct (and_line_agree with "[A]") as "[_ [%Heq _]]". { iSplit.
      { iDestruct "A" as "[$ _]". } { iDestruct "A" as "[_ $]". } } discriminate.
Qed.

Lemma uniq_rsv_and_agree ξ ζl x x' vπ' :
  .VOR[ξ;ζl] x ∧ .PC[ξ] x' vπ' -∗ ⌜x = x'⌝.
Proof.
  iIntros "A". unfold proph_ctrl. rewrite !bi.and_or_l. iDestruct "A" as "[A|[A|A]]".
  - iDestruct (and_line_agree with "[A]") as "[_ [_ %Heq]]". { iSplit.
      { iDestruct "A" as "[$ _]". } { iDestruct "A" as "[_ [$ _]]". } } discriminate.
  - rewrite bi.and_exist_l. iDestruct "A" as (ζl') "A".
    iDestruct (and_line_agree with "[A]") as "[-> _]". { iSplit.
      { iDestruct "A" as "[$ _]". } { iDestruct "A" as "[_ [$ _]]". } } done.
  - iAssert (_ ∧ _)%I with "[A]" as "A". { iSplit. { iDestruct "A" as "[X _]". iApply "X". }
      { iDestruct "A" as "[_ [X _]]". iApply "X". } }
    rewrite bi.and_exist_l. iDestruct "A" as (x'') "A".
    iDestruct (and_line_agree with "[A]") as "[_ [%Heq _]]". { iSplit.
      { iDestruct "A" as "[$ _]". } { iDestruct "A" as "[_ $]". } } discriminate.
Qed.

Lemma uniq_proph_tok ξ x x' vπ' :
  .VO[ξ] x -∗ .PC[ξ] x' vπ' -∗ .VO[ξ] x ∗ 1:[ξ] ∗ (1:[ξ] -∗ .PC[ξ] x' vπ').
Proof.
  iIntros "Vo Pc". iDestruct (vo_pc with "Vo Pc") as (->) "[Vo2 $]".
  iDestruct (vo_vo2 with "Vo2") as "[$?]". iIntros "?". iLeft. iFrame.
Qed.

Lemma uniq_update ξ x'' vπ'' x x' vπ' E : ↑uniqN ⊆ E →
  uniq_ctx -∗ .VO[ξ] x -∗ .PC[ξ] x' vπ' ={E}=∗ .VO[ξ] x'' ∗ .PC[ξ] x'' vπ''.
Proof.
  iIntros (?) "[? _] Vo Pc". iDestruct (vo_pc with "Vo Pc") as (->) "[Vo2 ξ]".
  iInv uniqN as (S) ">●S". set S' := add_line ξ 1 false None x'' S.
  iMod (own_update_2 _ _ _ (● S' ⋅ ◯ line ξ 1 false None x'') with "●S Vo2") as "[? Vo2]".
  { apply auth_update, discrete_fun_singleton_local_update_any,
    singleton_local_update_any => ? _. by apply exclusive_local_update. }
  iModIntro. iSplitR "Vo2 ξ"; [by iExists S'|]. iModIntro.
  iDestruct (vo_vo2 with "Vo2") as "[$?]". iLeft. iFrame.
Qed.

Lemma uniq_resolve ξ ζl q x x' vπ' E : ↑uniqN ∪ ↑prophN ⊆ E → vπ' ./ ζl →
  uniq_ctx -∗ proph_ctx -∗ .VO[ξ] x -∗ .PC[ξ] x' vπ' -∗ q:+[ζl] ={E}=∗
    ⟨π, π ξ = vπ' π⟩ ∗ .PC[ξ] x vπ' ∗ q:+[ζl].
Proof.
  iIntros (??) "UNIQ PROPH Vo Pc ζl". iDestruct (vo_pc with "Vo Pc") as (<-) "[Vo2 ξ]".
  iMod (proph_resolve_toks with "PROPH ξ ζl") as "[#? $]"; [solve_ndisj|done|].
  iMod (vo2_vo2_done with "UNIQ Vo2") as "Vo2". { solve_ndisj. }
  iModIntro. iSplitR; [done|]. iRight. iRight. iSplitL; [by iExists x|].
  by iApply proph_eqz_obs.
Qed.

Lemma uniq_preresolve ξ ζl uπ q x x'' vπ'' E : ↑uniqN ∪ ↑prophN ⊆ E → uπ ./ ζl →
  uniq_ctx -∗ proph_ctx -∗ .VO[ξ] x -∗ .PC[ξ] x'' vπ'' -∗ q:+[ζl] ={E}=∗
    ⟨π, π ξ = uπ π⟩ ∗ q:+[ζl] ∗ (∀x' vπ', uπ :== vπ' -∗ .PC[ξ] x' vπ').
Proof.
  iIntros (??) "UNIQ PROPH Vo Pc ζl". iDestruct (vo_pc with "Vo Pc") as (<-) "[Vo2 ξ]".
  iMod (proph_resolve_toks with "PROPH ξ ζl") as "[#Obs $]"; [solve_ndisj|done|].
  iMod (vo2_vo2_done with "UNIQ Vo2") as "Vo2"; [solve_ndisj|].
  iModIntro. iSplitR; [done|]. iIntros (??) "Eqz". iRight. iRight.
  iSplitR "Eqz"; [by iExists x|].
  by iDestruct (proph_eqz_modify with "Obs Eqz") as "?".
Qed.

(** ** Reservations

  While unresolved, the controller can be switched to a reserved state
  (see [proph_reserved]), in which the observer is [.VOR[ξ;ζl]] instead of
  [.VO[ξ]]. In this state, [ξ] can be resolved to a value depending on [ζl]
  without tokens for [ζl]. *)

Lemma uniq_reserve ξ ζl q x x' vπ' E : ↑uniqN ∪ ↑prophN ⊆ E →
  uniq_ctx -∗ proph_ctx -∗ .VO[ξ] x -∗ .PC[ξ] x' vπ' -∗ q:+[ζl] ={E}=∗
    .VOR[ξ;ζl] x ∗ .PC[ξ] x vπ' ∗ q:+[ζl].
Proof.
  iIntros (?) "UNIQ PROPH Vo Pc ζl". iDestruct (vo_pc with "Vo Pc") as (<-) "[Vo2 ξ]".
  iMod (proph_reserve with "PROPH ξ ζl") as "[ξ $]"; [solve_ndisj|].
  iMod (own_line_update _ _ _ _ false (Some ζl) x with "UNIQ Vo2") as "Vo2"; [solve_ndisj|].
  iModIntro. iDestruct (vor_vor2 with "Vo2") as "[$ Vo]". iRight. iLeft. iExists ζl. iFrame.
Qed.

Lemma uniq_unreserve ξ ζl x x' vπ' E : ↑uniqN ∪ ↑prophN ⊆ E →
  uniq_ctx -∗ proph_ctx -∗ .VOR[ξ;ζl] x -∗ .PC[ξ] x' vπ' ={E}=∗
    .VO[ξ] x ∗ .PC[ξ] x vπ'.
Proof.
  iIntros (?) "UNIQ PROPH Vo Pc". iDestruct (vor_pc with "Vo Pc") as (<-) "[Vo2 ξ]".
  iMod (proph_unreserve with "PROPH ξ") as "ξ"; [solve_ndisj|].
  iMod (own_line_update _ _ _ _ false None x with "UNIQ Vo2") as "Vo2"; [solve_ndisj|].
  iModIntro. iDestruct (vo_vo2 with "Vo2") as "[$ Vo]". iLeft. iFrame.
Qed.

Lemma uniq_reserve_extend ξ ζl ζl' q x x' vπ' E : ↑uniqN ∪ ↑prophN ⊆ E →
  uniq_ctx -∗ proph_ctx -∗ .VOR[ξ;ζl] x -∗ .PC[ξ] x' vπ' -∗ q:+[ζl'] ={E}=∗
    .VOR[ξ;ζl ++ ζl'] x ∗ .PC[ξ] x vπ' ∗ q:+[ζl'].
Proof.
  iIntros (?) "UNIQ PROPH Vo Pc ζl'". iDestruct (vor_pc with "Vo Pc") as (<-) "[Vo2 ξ]".
  iMod (proph_reserve_extend with "PROPH ξ ζl'") as "[ξ $]"; [solve_ndisj|].
  iMod (own_line_update _ _ _ _ false (Some (ζl ++ ζl')) x with "UNIQ Vo2") as "Vo2";
    [solve_ndisj|].
  iModIntro. iDestruct (vor_vor2 with "Vo2") as "[$ Vo]". iRight. iLeft.
  iExists (ζl ++ ζl'). iFrame.
Qed.

Lemma uniq_rsv_update ξ ζl x'' vπ'' x x' vπ' E : ↑uniqN ⊆ E →
  uniq_ctx -∗ .VOR[ξ;ζl] x -∗ .PC[ξ] x' vπ' ={E}=∗ .VOR[ξ;ζl] x'' ∗ .PC[ξ] x'' vπ''.
Proof.
  iIntros (?) "UNIQ Vo Pc". iDestruct (vor_pc with "Vo Pc") as (<-) "[Vo2 ξ]".
  iMod (own_line_update _ _ _ _ false (Some ζl) x'' with "UNIQ Vo2") as "Vo2"; [done|].
  iModIntro. iDestruct (vor_vor2 with "Vo2") as "[$ Vo]". iRight. iLeft.
  iExists ζl. iFrame.
Qed.

Lemma uniq_resolve_reserved ξ ζl ηl q x x' vπ' E : ↑uniqN ∪ ↑prophN ⊆ E →
  vπ' ./ ζl ++ ηl →
  uniq_ctx -∗ proph_ctx -∗ .VOR[ξ;ζl] x -∗ .PC[ξ] x' vπ' -∗ q:+[ηl] ={E}=∗
    ⟨π, π ξ = vπ' π⟩ ∗ .PC[ξ] x vπ' ∗ q:+[ηl].
Proof.
  iIntros (??) "UNIQ PROPH Vo Pc ηl". iDestruct (vor_pc with "Vo Pc") as (<-) "[Vo2 ξ]".
  iMod (proph_resolve_reserved with "PROPH ξ ηl") as "[#? $]"; [solve_ndisj|done|].
  iMod (vo2r_vo2_done with "UNIQ Vo2") as "Vo2". { solve_ndisj. }
  iModIntro. iSplitR; [done|]. iRight. iRight. iSplitL; [by iExists x|].
  by iApply proph_eqz_obs.
Qed.

Lemma uniq_preresolve_reserved ξ ζl ηl uπ q x x'' vπ'' E : ↑uniqN ∪ ↑prophN ⊆ E →
  uπ ./ ζl ++ ηl →
  uniq_ctx -∗ proph_ctx -∗ .VOR[ξ;ζl] x -∗ .PC[ξ] x'' vπ'' -∗ q:+[ηl] ={E}=∗
    ⟨π, π ξ = uπ π⟩ ∗ q:+[ηl] ∗ (∀x' vπ', uπ :== vπ' -∗ .PC[ξ] x' vπ').
Proof.
  iIntros (??) "UNIQ PROPH Vo Pc ηl". iDestruct (vor_pc with "Vo Pc") as (<-) "[Vo2 ξ]".
  iMod (proph_resolve_reserved with "PROPH ξ ηl") as "[#Obs $]"; [solve_ndisj|done|].
  iMod (vo2r_vo2_done with "UNIQ Vo2") as "Vo2"; [solve_ndisj|].
  iModIntro. iSplitR; [done|]. iIntros (??) "Eqz". iRight. iRight.
  iSplitR "Eqz"; [by iExists x|].
  by iDestruct (proph_eqz_modify with "Obs Eqz") as "?".
Qed.

Local Fixpoint remove_dupes (ζl: list proph_var) : list proph_var :=
  match ζl with
    | [] => []
    | ζ :: ζl' => if bool_decide (ζ ∈ ζl') then remove_dupes ζl' else ζ :: remove_dupes ζl'
  end.

Local Lemma elem_of_remove_dupes ζ (ζl: list proph_var) :
    ζ ∈ ζl ↔ ζ ∈ remove_dupes ζl.
Proof.
  induction ζl in ζ |- *; first done.
  simpl. case_bool_decide.
   - destruct (decide (ζ = a)) as [He|Hn].
    + subst a. split.
      * intros Ha. rewrite <- IHζl. trivial.
      * intros Ha. rewrite elem_of_cons. left; trivial.
    + rewrite elem_of_cons. have Ih := IHζl ζ. intuition.
   - destruct (decide (ζ = a)) as [He|Hn].
    + do 2 (rewrite elem_of_cons). intuition.
    + do 2 (rewrite elem_of_cons). have Ih := IHζl ζ. intuition.
Qed.

Local Lemma indep_remove_dupes {A} (vπ: proph A) ζl :
  vπ ./ ζl → vπ ./ remove_dupes ζl.
Proof.
  unfold proph_dep. intros Ha π π' Hc. apply (Ha π π').
  unfold prophecy.proph_asn_eqv. intros ξ Hin.
  rewrite elem_of_remove_dupes in Hin. apply Hc. apply Hin.
Qed.


Local Lemma combine_guard_proph_vars ζl n F G :
    (∀ ζ , ⌜ζ ∈ ζl⌝ -∗ (G &&{F; n}&&> 1:[ζ])) -∗
    (G &&{F; n}&&> 1:+[remove_dupes ζl]).
Proof.
    induction ζl.
     - iIntros. iApply guards_true.
     - iIntros "#G". simpl. case_bool_decide as Ha.
      + iApply IHζl. iIntros (ζ) "%Hin". iApply "G". iPureIntro. rewrite elem_of_cons.
        right; trivial.
      + simpl. iApply (guards_and_point _ (1:[a])%I (1:+[remove_dupes ζl])%I).
        * apply factoring_props.point_prop_sep.
          -- apply proph_tok_point_prop.
          -- apply proph_tokl_point_prop.
        * apply proph_tok_list_and. rewrite <- elem_of_remove_dupes. trivial.
        * iApply "G". iPureIntro. rewrite elem_of_cons. left. trivial.
        * iApply IHζl. iIntros (ζ) "%Hin". iApply "G". iPureIntro.
          rewrite elem_of_cons. right. trivial.
Qed.

Local Lemma proph_eqz_to_obs_with_guard {A} (uπ vπ: proph A) E n (ξl: list proph_var) G :
    ↑NllftG ∪ ↑prophN ⊆ E →
    vπ ./ ξl →
    £n -∗
    (∀ ζ : proph_var, ⌜ζ ∈ ξl⌝ -∗ (G &&{ ↑NllftG; n }&&> 1:[ζ])) -∗
    G -∗
    uπ :== vπ ={E}=∗ ⟨π, uπ π = vπ π⟩ ∗ G.
Proof.
    iIntros (Hmask Indep) "£ Guard' G eqz".
    iDestruct (combine_guard_proph_vars with "Guard'") as "#Guard".
    leaf_open_laters "Guard" with "G" as "Opened"; first by solve_ndisj.
    iMod (lc_fupd_elim_laterN with "£ Opened") as ">[tok back]".
    iMod ("eqz" with "[] tok") as "[Obs tok]".
      - iSplit; first solve_ndisj. iPureIntro. apply indep_remove_dupes. trivial.
      - iMod ("back" with "tok") as "G". iModIntro. iFrame.
Qed.

Lemma uniq_resolve_guarded ξ ζl x x' vπ' E G n : ↑NllftG ∪ ↑prophN ∪ ↑uniqN ⊆ E → vπ' ./ ζl →
  (∀ ζ , ⌜ζ ∈ ζl⌝ -∗ (G &&{↑NllftG; n}&&> 1:[ζ])) -∗
  uniq_ctx -∗ proph_ctx -∗
  .VO[ξ] x -∗ .PC[ξ] x' vπ' -∗ G ={E,E∖↑NllftG}=∗ ▷^n |={E∖↑NllftG,E}=>
    ⟨π, π ξ = vπ' π⟩ ∗ .PC[ξ] x vπ' ∗ G.
Proof.
  iIntros (Hmask Indep) "Guard' UNIQ PROPH Vo Pc G".
  iDestruct (combine_guard_proph_vars with "Guard'") as "#Guard".
  leaf_open_laters "Guard" with "G" as "Opened"; first by solve_ndisj. iModIntro. iNext.
  iMod "Opened" as "[tok back]".
  iMod (uniq_resolve with "UNIQ PROPH Vo Pc tok") as "(Obs & Pc & Tok)"; first by solve_ndisj.
   { apply (indep_remove_dupes _ _ Indep). }
  iMod ("back" with "Tok") as "G".
  iModIntro. iFrame.
Qed.

(** Like [uniq_resolve_guarded], for a reserved controller: the value may
  depend on the reserved [ζl], and guarded tokens are needed only for the
  remaining dependencies [ηl]. *)
Lemma uniq_resolve_reserved_guarded ξ ζl ηl x x' vπ' E G n :
  ↑NllftG ∪ ↑prophN ∪ ↑uniqN ⊆ E → vπ' ./ ζl ++ ηl →
  (∀ η , ⌜η ∈ ηl⌝ -∗ (G &&{↑NllftG; n}&&> 1:[η])) -∗
  uniq_ctx -∗ proph_ctx -∗
  .VOR[ξ;ζl] x -∗ .PC[ξ] x' vπ' -∗ G ={E,E∖↑NllftG}=∗ ▷^n |={E∖↑NllftG,E}=>
    ⟨π, π ξ = vπ' π⟩ ∗ .PC[ξ] x vπ' ∗ G.
Proof.
  iIntros (Hmask Indep) "Guard' UNIQ PROPH Vo Pc G".
  iDestruct (combine_guard_proph_vars with "Guard'") as "#Guard".
  leaf_open_laters "Guard" with "G" as "Opened"; first by solve_ndisj. iModIntro. iNext.
  iMod "Opened" as "[tok back]".
  iMod (uniq_resolve_reserved with "UNIQ PROPH Vo Pc tok") as "(Obs & Pc & Tok)";
    first by solve_ndisj.
  { apply (proph_dep_incl _ _ _ Indep)=> ?. rewrite !elem_of_app -elem_of_remove_dupes.
    done. }
  iMod ("back" with "Tok") as "G".
  iModIntro. iFrame.
Qed.

Lemma proph_ctrl_eqz ξ x vπ : proph_ctx -∗ .PC[ξ] x vπ -∗ (.$ ξ) :== vπ.
Proof.
  iIntros "#? [[_ ?]|[(%& _ & ?)|[_ ?]]]";
    by [iApply proph_eqz_token|iApply proph_eqz_reserved|].
Qed.

Lemma proph_ctrl_and_value_obs_entails_proph_tok ξ x vπ :
  .PC[ξ] x vπ ∧ .VO[ξ] x ⊢ 1:[ξ].
Proof.
  iIntros "A". unfold proph_ctrl. rewrite !bi.and_or_r. iDestruct "A" as "[A|[A|A]]".
   - iDestruct "A" as "[[_ $] _]".
   - rewrite bi.and_exist_r. iDestruct "A" as (ζl) "A".
    iDestruct (and_line_agree with "[A]") as "[_ [_ %Heq]]". { iSplit.
      { iDestruct "A" as "[[$ _] _]". } { iDestruct "A" as "[_ $]". } } discriminate.
   - iAssert (_ ∧ _)%I with "[A]" as "A". { iSplit. { iDestruct "A" as "[_ X]". iApply "X". }
      { iDestruct "A" as "[[X _] _]". iApply "X". } }
    rewrite bi.and_exist_l. iDestruct "A" as (x'') "A".
    iDestruct (and_line_agree with "[A]") as "[_ [%Heq _]]". { iSplit.
      { iDestruct "A" as "[$ _]". } { iDestruct "A" as "[_ $]". } } discriminate.
Qed.

End lemmas.

Global Opaque uniq_ctx val_obs val_obs_rsv proph_ctrl.
