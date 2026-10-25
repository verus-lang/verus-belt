Require Import guarding.guard.
Require Import guarding.own_and.
Require Import guarding.tactics.
Require Import guarding.lib.boxes.
Require Import guarding.lib.fractional.
From lrust.lifetime.lifetime_internals Require Import ra inv augment_outlives new_lt expire_lt iff join split reborrow unborrow unnest.
Require Import stdpp.base.
Require Import stdpp.namespaces.
From iris.algebra Require Export cmra updates.
From iris.algebra Require Import proofmode_classes.
From iris.algebra Require Import excl.
From iris.prelude Require Import options.

From iris.base_logic.lib Require Export own iprop.
From iris.proofmode Require Import base.
From iris.proofmode Require Import ltac_tactics.
From iris.proofmode Require Import tactics.
From iris.proofmode Require Import coq_tactics.
From iris.base_logic.lib Require Export invariants.

(** The Leaf Liftime Logic.

This is based on RustBelt's lifetime logic, and has many similar rules, but it incorporates
Leaf's guarding operator to handle both shared borrows and lifetime inclusions. *)

Class llft_logicGpreS Σ := {
  llft_logic_inG : lifetime_internals.ra.llft_logicGS Σ ;
  llft_boxG : boxG Σ
}.

Class llft_logicGS Σ := LlftLogicG {
  llft_in_preG : llft_logicGpreS Σ;
  
  llft_name: gname;
  o_name: gname;
  d_name: gname;
}.
Global Existing Instance llft_in_preG.

Local Existing Instance llft_boxG.
Local Existing Instance llft_logic_inG.

Definition llft_logicΣ : gFunctors := #[
  lifetime_internals.ra.llft_logicΣ ;
  boxΣ
].

Global Instance subG_lt_logicΣ Σ : subG llft_logicΣ Σ → llft_logicGpreS Σ.
Proof.
  solve_inG.
Qed.

Section LlftLogic.
  Context {Σ: gFunctors}.
  Context `{!llft_logicGS Σ}.
  Context `{!invGS Σ}.
  
  (** There are the namespaces to know about as the user of the logic.
      All view shifts take place at [↑Nllft] and all guards (e.g., in lifetime inclusions)
      take place at [↑NllftG]. *)

  Definition Nllft := nroot .@ "leaf_lifetime_logic".
  Definition NllftG := nroot .@ "leaf_lifetime_logic" .@ "guarding".
  Definition NllftUsr := nroot .@ "leaf_lifetime_logic" .@ "user".
  Definition NllftUsr2 := nroot .@ "leaf_lifetime_logic" .@ "guarding" .@ "user".

  (*** Lifetime logic ***)

  (** A Lifetime κ is defined as a [gset nat]. Though this should technically be
  an implementation detail, this makes it easy to export the basic properties of [Lifetime]
  (EqDecidable, Countable) and [⊓] (associativity, commutativity). *)
  
  Definition lft := gset nat.

  Global Instance llft_intersect : Meet lft := λ κ1 κ2, κ1 ∪ κ2.
  Definition llft_empty : lft := ∅.
  (* begin hide *)
  
  Local Definition llft_alive_def' (lt : gset lt_atom) : iProp Σ := [∗ set] k ∈ lt , Alive llft_name k.
  Local Definition llft_dead_def' (lt : gset lt_atom) : iProp Σ := ∃ k , ⌜ k ∈ lt ⌝ ∗ Dead llft_name k.
  
  Local Definition llft_alive_def (κ : lft) : iProp Σ := [∗ set] k ∈ κ , Alive llft_name (LtAtomSwell k).
  Local Definition llft_dead_def (κ : lft) : iProp Σ := ∃ k , ⌜ k ∈ κ ⌝ ∗ Dead llft_name (LtAtomSwell k).

  Local Definition llft_ctx_def : iProp Σ :=
    (inv NllftO (∃ outlives, £1 ∗ Delayed d_name None ∗ Outlives o_name outlives
        ∗ ∀ o, ⌜o ∈ outlives⌝ -∗ (llft_alive_def' o.1 &&{↑NllftG}&&> Alive llft_name o.2))) ∗
    (True &&{↑Nmain}&&>
      ∃ (sa sd blocked : gset lt_atom),
        LtState llft_name sa sd
          ∗ llft_alive_def' sa
          ∗ (▷ outer_inv llft_name o_name d_name sa sd blocked)
          ∗ llft_alive_def' blocked
    ).

  Local Definition llft_alive_aux : seal (@llft_alive_def). Proof. by eexists. Qed.
  Local Definition llft_dead_aux : seal (@llft_dead_def). Proof. by eexists. Qed.
  Local Definition llft_ctx_aux : seal (@llft_ctx_def). Proof. by eexists. Qed.
  
  Local Lemma set_map_inter (κ1 κ2: lft) :
      set_map LtAtomSwell (κ1 ⊓ κ2)
        = set_map LtAtomSwell κ1 ∪ (set_map LtAtomSwell κ2 : gset lt_atom).
  Proof. apply set_eq. apply set_map_union. Qed.
        
  Local Lemma set_map_singleton (x: nat) :
        (set_map LtAtomSwell ({[ x ]} : gset nat) : gset lt_atom) = ({[ LtAtomSwell x ]} : gset lt_atom).
  Proof. apply set_eq. apply set_map_singleton. Qed.
  
  Local Lemma big_sepS_set_map (κ: lft) : 
      (([∗ set] k ∈ (set_map LtAtomSwell κ) , Alive llft_name k) ⊣⊢
      ([∗ set] k ∈ κ , Alive llft_name (LtAtomSwell k)))%I.
  Proof using invGS0 llft_logicGS0 Σ.
    induction κ as [|x T ? IH] using set_ind_L.
      - do 2 rewrite big_sepS_empty. done.
      - rewrite set_map_inter.
        do 2 (rewrite big_sepS_union; last by set_solver).
        rewrite set_map_singleton. do 2 (rewrite big_sepS_singleton).
        rewrite IH. done.
  Qed.
      
  Local Lemma dead_def_set_map (κ: lft) :
        (∃ k : nat, ⌜k ∈ κ⌝ ∗ Dead llft_name (LtAtomSwell k)) ⊣⊢
        (∃ k : lt_atom, ⌜k ∈ (set_map LtAtomSwell κ : gset lt_atom)⌝ ∗ Dead llft_name k).
  Proof.
    iSplit.
      - iDestruct 1 as (k) "[%Hin Dead]". iExists (LtAtomSwell k). iFrame.
        iPureIntro. set_solver.
      - iDestruct 1 as (k) "[%Hin Dead]". rewrite elem_of_map in Hin.
        destruct Hin as [x [Heq Hin]]. subst k. iExists x. iFrame. done.
  Qed.
  
  Local Lemma swell_set_set_map (κ: gset nat) :
      swell_set (set_map LtAtomSwell κ).
  Proof.
      intros x. rewrite elem_of_map. intros [k [Heq Hin]]. rewrite Heq. done.
  Qed.
      
  Local Definition atom_unwrap (atom: lt_atom) : nat := match atom with LtAtomSwell k => k | LtAtomNotSwell k => k end.
  
  Local Lemma atom_not_in_swell (k: nat) (s : gset lt_atom) :
      k ∉ (set_map atom_unwrap s : gset nat) →
      LtAtomSwell k ∉ s.
  Proof. intros Ha Hb. apply Ha. rewrite elem_of_map. exists (LtAtomSwell k); done. Qed.
      
  Local Lemma atom_not_in_not_swell (k: nat) (s : gset lt_atom) :
      k ∉ (set_map atom_unwrap s : gset nat) →
      LtAtomNotSwell k ∉ s.
  Proof. intros Ha Hb. apply Ha. rewrite elem_of_map. exists (LtAtomNotSwell k); done. Qed.

  (* end hide *)
  
  (** Definitions of the lifetime tokens. Note that these aren't fractional since you
  use Leaf concepts instead. *)
  
  Definition llft_alive (κ : lft) : iProp Σ. exact (llft_alive_aux.(unseal) κ). Defined.
  Definition llft_dead (κ : lft) : iProp Σ. exact (llft_dead_aux.(unseal) κ). Defined.
  Definition llft_ctx : iProp Σ. exact (llft_ctx_aux.(unseal)). Defined.
  (* begin hide *)

  Local Definition llft_alive_unseal :
      @llft_alive = @llft_alive_def := llft_alive_aux.(seal_eq).
  Local Definition llft_dead_unseal :
      @llft_dead = @llft_dead_def := llft_dead_aux.(seal_eq).
  Local Definition llft_ctx_unseal :
      @llft_ctx = @llft_ctx_def := llft_ctx_aux.(seal_eq).

  Local Ltac unseal := rewrite
    ?llft_alive_unseal /llft_alive_def
    ?llft_dead_unseal /llft_dead_def
    ?llft_ctx_unseal /llft_ctx_def.
    
  Local Instance pers_dead2 γlt k : Persistent (Dead γlt k).
  Proof. apply own_core_persistent. unfold CoreId. trivial. Qed.

  (* end hide *)

  Notation "@[ κ ]" := (llft_alive κ) (format "@[ κ ]") : bi_scope.
  Notation "[† κ ]" := (llft_dead κ) (format "[† κ ]") : bi_scope.
  
  (** Lifetime inclusion is, by definition, a guard proposition. This provides us with
  an analogue of RustBelt's "dynamic lifetime inclusion": to derive new lifetime inclusions
  we can use Leaf to derive new guard propositions. *)
  
  (** LeLiLo-Incl-Guard *)
  Definition llft_incl (κ1 κ2 : lft) : iProp Σ :=
      @[ κ1 ] &&{↑NllftG}&&> @[ κ2 ].
  
  Infix "⊑" := llft_incl (at level 70) : bi_scope.
  
  (** Lifetime tokens and their algebra *)

  Global Instance pers_llft_ctx : Persistent llft_ctx.
  Proof. unseal. typeclasses eauto. Qed.
  
  Global Instance pers_llft_dead κ : Persistent ([† κ ]).
  Proof. unseal. typeclasses eauto. Qed.

  Global Instance timeless_llft_alive κ : Timeless (@[ κ ]).
  Proof. unseal. typeclasses eauto. Qed.

  Global Instance timeless_llft_dead κ : Timeless ([† κ ]).
  Proof. unseal. typeclasses eauto. Qed.

  Lemma point_prop_llft_alive κ : factoring_props.point_prop @[ κ ].
  Proof.
    unseal. apply factoring_props.point_prop_big_sepS=> ??.
    apply factoring_props.point_prop_own.
  Qed.

  (* begin hide *)
  Lemma llftl_not_own_end_unswell κ : llft_alive_def' κ -∗ llft_dead_def' κ -∗ False.
  Proof.
    unseal. iIntros "A D". iDestruct "D" as (k) "[%kk D]".
    iDestruct ((big_sepS_delete _ _ k) with "A") as "[A _]". { trivial. }
    iApply (lt_alive_dead_false llft_name k). iSplit; iFrame.
  Qed.
  (* end hide *)

  (** LeLiLo-Not-Own-End *)
  Lemma llftl_not_own_end κ : @[ κ ] -∗ [† κ ] -∗ False.
  Proof.
    unseal. iIntros "A D". iDestruct "D" as (k) "[%kk D]".
    iDestruct ((big_sepS_delete _ _ k) with "A") as "[A _]". { trivial. }
    iApply (lt_alive_dead_false llft_name (LtAtomSwell k)). iSplit; iFrame.
  Qed.
  
  Lemma llftl_not_own_end_and κ : @[ κ ] ∧ [† κ ] ⊢ False.
  Proof.
    (* note: since [† κ ] is persistent, there's an easier proof *)
    unseal. iIntros "AD". unfold llft_dead. rewrite bi.and_exist_l. iDestruct "AD" as (k) "AD".
    iApply (lt_alive_dead_false llft_name (LtAtomSwell k)).
    iAssert (⌜k ∈ κ⌝)%I as "%kk". { iDestruct "AD" as "[_ [D _]]".  iFrame. }
    iSplit; iFrame.
    { iDestruct "AD" as "[A _]".
      iDestruct ((big_sepS_delete _ _ k) with "A") as "[A _]". { trivial. } iFrame. }
    { iDestruct "AD" as "[_ [_ D]]". iFrame. }
  Qed.
  
  (* begin hide *)
  Lemma llftl_incl_dead_implies_dead_unswell E κ κ' :
      ↑NllftG ⊆ E →
      ⊢ llft_ctx -∗ (llft_alive_def' κ &&{↑NllftG}&&> llft_alive_def' κ') -∗ llft_dead_def' κ' ={E}=∗ llft_dead_def' κ.
  Proof.
    intros Hmask. iIntros "#ctx #incl #dead". unseal.
    iDestruct "ctx" as "[#other #ctx]".

    unfold llft_incl.

    leaf_hyp "incl" rhs to (False)%I as "G2".
    {
      leaf_by_sep. iIntros "a". iExFalso.
      iApply (llftl_not_own_end_unswell κ' with "a"). unseal. iFrame "dead".
    }
    leaf_hyp "ctx" rhs to ((∃ sa sd blocked : gset lt_atom, ⌜ κ ⊆ sa ⌝ ∗ LtState llft_name sa sd ∗ llft_alive_def' sa ∗ ▷ outer_inv llft_name o_name d_name sa sd blocked ∗ llft_alive_def' blocked)
        ∨ (∃ sa sd blocked : gset lt_atom, ⌜ ¬(κ ⊆ sa) ⌝ ∗ LtState llft_name sa sd ∗ llft_alive_def' sa ∗ ▷ outer_inv llft_name o_name d_name sa sd blocked ∗ llft_alive_def' blocked) )%I
        as "ctx'".
    {
      leaf_by_sep. iIntros "T". iSplitL.
        - iDestruct "T" as (sa sd blocked) "[state_alive [alive ou]]".
          have h : Decision (κ ⊆ sa) by solve_decision. destruct h as [h|n]; trivial.
          + unseal. iLeft. iExists sa. iExists sd. iExists blocked. iFrame. iPureIntro. trivial.
          + unseal. iRight. iExists sa. iExists sd. iExists blocked. iFrame. iPureIntro. trivial.
        - iIntros "T". iDestruct "T" as "[T|T]".
          + iDestruct "T" as (sa sd blocked) "[_ T]". iExists sa. iExists sd. iExists blocked. unseal. iFrame.
          + iDestruct "T" as (sa sd blocked) "[_ T]". iExists sa. iExists sd. iExists blocked. unseal. iFrame.
      }
      leaf_hyp "ctx'" mask to (↑NllftG) as "ctx2". { solve_ndisj. }

      iAssert (True &&{ ↑NllftG }&&> (∃ sa sd blocked : gset lt_atom, ⌜κ ⊈ sa⌝ ∗ LtState llft_name sa sd ∗ llft_alive_def' sa ∗ ▷ outer_inv llft_name o_name d_name sa sd blocked ∗ llft_alive_def' blocked)) as "G3".
        { iApply (guards_cancel_or_by_chaining with "ctx2").
          leaf_goal rhs to (llft_alive_def' κ). { iFrame "G2". }
          leaf_by_sep.
          { iIntros "T". 
              iDestruct "T" as (sa sd blocked) "[%ksa [state alive]]".
                unseal. unfold llft_alive_def.
                replace sa with (κ ∪ (sa ∖ κ)) at 2.
                { setoid_rewrite big_sepS_union.
                  { iDestruct "alive" as "[[alive1 alive2] ou]".
                    iSplitL "alive1". { iFrame. }
                    iIntros "rest".
                    iExists sa. iExists sd. iExists blocked. iFrame.
                    iCombine "rest alive2" as "alive".
                    setoid_rewrite <- big_sepS_union.
                    { replace (κ ∪ sa ∖ κ) with sa. { iFrame. iPureIntro. trivial. }
                    rewrite <- union_difference_L; trivial.
                }
                set_solver.
              }
              set_solver.
          } rewrite <- union_difference_L; trivial.
        }
      }            

      leaf_open "G3" with "[]" as "[J back]". { set_solver. } { done. }

      iDestruct "J" as (sa sd blocked) "[%k_sa [State [alive [ou Blo]]]]".
      have the_k := not_subset_eq_get (κ) sa k_sa. destruct the_k as [k [k_in k_not_in]].
      have h : Decision (k ∈ sd) by solve_decision. destruct h as [h|n]; trivial.
        - iDestruct (LtState_entails_Dead llft_name k sa sd with "State") as "#deadk"; trivial.
          iMod ("back" with "[State alive ou Blo]") as "true". { iExists sa. iExists sd. iExists blocked. iFrame. iPureIntro; trivial. } iModIntro. unfold llft_dead.
          iExists k. iFrame "deadk". iPureIntro. apply k_in.
        - (* weird technicality, if k was never made alive in the first place;
            first create it, then immediately kill it *)
          iMod (new_lt llft_name k sa sd with "State") as "[State [al1 al2]]"; trivial.
          iMod (kill_lt llft_name k (sa ∪ {[ k ]}) sd with "[State al1 al2]") as "[State #deadk]". { iFrame. }
          iDestruct (outer_instant_kill_lt llft_name o_name d_name sa sd blocked k with "[deadk ou]") as "ou".
          { set_solver. } { iFrame. iFrame "deadk". }
          iMod (fupd_mask_mono with "ou") as "ou". { solve_ndisj. }
          
          iMod ("back" with "[State alive ou Blo]") as "J".
          { iExists sa. iExists (sd ∪ {[k]}). iExists blocked. iFrame.
            replace (((sa ∪ {[k]}) ∖ {[k]})) with sa.
            { iFrame. iPureIntro. trivial. } set_solver.
          }
          iModIntro. unfold llft_dead.
          iExists k. iFrame "deadk". iPureIntro; trivial.
  Qed.
  (* end hide *)

  (** LeLiLo-Incl-Dead *)
  Lemma llftl_incl_dead_implies_dead E κ κ' :
      ↑NllftG ⊆ E →
      ⊢ llft_ctx -∗ κ ⊑ κ' -∗ [† κ' ] ={E}=∗ [† κ ].
  Proof.
      iIntros (Hmask) "#LFT #Incl #A".
      iMod (llftl_incl_dead_implies_dead_unswell with "LFT [] []") as "J"; trivial.
       - unseal. unfold llft_incl. unseal. unfold llft_alive_def'.
         do 2 rewrite <- big_sepS_set_map. iFrame "Incl".
       - unseal. iDestruct "A" as (k) "[%Hin Dead]". iExists (LtAtomSwell k).
         iFrame "Dead". iPureIntro. rewrite elem_of_map. exists k; split; trivial.
       - iModIntro. unseal. iDestruct "J" as (k) "[%Hin Dead]".
         rewrite elem_of_map in Hin. destruct Hin as [k0 [Heq Hin]]. subst k.
         iExists k0. iFrame "Dead". done.
  Qed.

  Lemma llftl_intersect_incl_l κ κ' : ⊢ (κ ⊓ κ') ⊑ κ.
  Proof.
    leaf_by_sep. unseal. iIntros "Alive".
    replace (κ ∪ κ') with (κ ∪ ((κ ∪ κ') ∖ κ)).
    - rewrite big_sepS_union.
      + iDestruct "Alive" as "[A1 A2]". iFrame "A1". iIntros "A3". iFrame.
      + set_solver.
    - symmetry. apply union_difference_L. set_solver.
  Qed.
  
  Lemma llftl_intersect_incl_r κ κ' : ⊢ (κ' ⊓ κ) ⊑ κ.
  Proof.
    replace (κ' ⊓ κ) with (κ ⊓ κ') by (unfold llft_intersect; set_solver).
    apply llftl_intersect_incl_l.
  Qed.
  
  Lemma llftl_incl_trans κ κ' κ'' : ⊢ κ ⊑ κ' -∗ κ' ⊑ κ'' -∗ κ ⊑ κ''.
  Proof.
    apply guards_transitive.
  Qed.

  Lemma llftl_incl_glb κ κ' κ'' :
      κ ⊑ κ' -∗ κ ⊑ κ'' -∗ κ ⊑ (κ' ⊓ κ'').
  Proof.
    iIntros "A B".
    iApply (guards_and_point with "A B"); [exact: point_prop_llft_alive|].
    unseal. unfold llft_alive_def. do 3 rewrite <- big_sepS_set_map.
    rewrite set_map_inter. apply alive_and_bigSepS.
  Qed.
  
  Lemma llftl_incl_weaken_lhs_l κ κ' κ'' :
      κ ⊑ κ' ⊢ (κ ⊓ κ'') ⊑ κ'.
  Proof.
    iIntros "#incl". leaf_goal lhs to (@[κ])%I. - iApply llftl_intersect_incl_l. - iFrame "#".
  Qed.
  
  Lemma llftl_incl_weaken_lhs_r κ κ' κ'' :
      κ ⊑ κ' ⊢ (κ'' ⊓ κ) ⊑ κ'.
  Proof.
      replace (κ'' ⊓ κ) with (κ ⊓ κ'') by (unfold llft_intersect; set_solver).
      apply llftl_incl_weaken_lhs_l.
  Qed.

  Lemma llftl_tok_inter_l κ κ' :
      @[ κ ⊓ κ' ] ⊢ @[ κ ].
  Proof.
    iIntros "Alive".
    replace (κ ∪ κ') with (κ ∪ ((κ ∪ κ') ∖ κ)).
    - unseal. rewrite big_sepS_union.
      + iDestruct "Alive" as "[A1 A2]". iFrame "A1".
      + set_solver.
    - symmetry. apply union_difference_L. set_solver.
  Qed.

  Lemma llftl_tok_inter_r κ κ' :
      @[ κ ⊓ κ' ] ⊢ @[ κ' ].
  Proof.
    replace (κ ⊓ κ') with (κ' ⊓ κ).
    - apply llftl_tok_inter_l. 
    - unfold meet, llft_intersect. set_solver.
  Qed.

  (** LeLiLo-Tok-Inter *)
  Lemma llftl_tok_inter_and κ κ' :
      @[ κ ⊓ κ' ] ⊣⊢ @[ κ ] ∧ @[ κ' ].
  Proof using invGS0 llft_logicGS0 Σ.
    iIntros. iSplit.
    - iIntros "t". iSplit.
      + iApply llftl_tok_inter_l. iFrame "t".
      + iApply llftl_tok_inter_r. iFrame "t".
  - unseal. iIntros.
      do 3 rewrite <- big_sepS_set_map.
      rewrite set_map_inter. 
      iApply alive_and_bigSepS. iFrame.
  Qed.
  
  (** LeLiLo-End-Inter *)
  Lemma llftl_end_inter κ κ' :
      [† κ ⊓ κ'] ⊣⊢ [† κ ] ∨ [† κ' ].
  Proof.
    unseal. iIntros. iSplit.
    - iIntros "t".  iDestruct "t" as (k) "[%kin t]".
      unfold llft_intersect in kin. rewrite elem_of_union in kin. destruct kin as [h|h].
      + iLeft. iExists k. iFrame "t". iPureIntro. trivial.
      + iRight. iExists k. iFrame "t". iPureIntro. trivial.
    - iIntros "t". iDestruct "t" as "[h|h]".
      + iDestruct "h" as (k) "[%kin t]".
        iExists k. iFrame "t". iPureIntro. unfold llft_intersect. set_solver.
      + iDestruct "h" as (k) "[%kin t]".
        iExists k. iFrame "t". iPureIntro. unfold llft_intersect. set_solver.
  Qed.

  Lemma llftl_tok_unit :
      ⊢ @[ llft_empty ].
  Proof.
    unseal. unfold llft_empty. rewrite big_sepS_empty. iIntros. done.
  Qed.

  Lemma llftl_end_unit :
      [† llft_empty ] ⊢ False.
  Proof.
    unseal. unfold llft_empty.
    iIntros "t". iDestruct "t" as (k) "[%p t]".
    rewrite elem_of_empty in p. contradiction.
  Qed.
  
  (** Allocating a new lifetime token *)
  
  (* begin hide *)
  Local Lemma llftl_begin_maybe_swell' E (b: bool) :
      ↑Nllft ⊆ E →
      llft_ctx ⊢ |={E}=> ∃ k, Alive llft_name (if b then LtAtomSwell k else LtAtomNotSwell k).
  Proof.
      intros Hmask. unseal. iIntros "[#other #ctx]".  unfold llft_ctx.
      iDestruct (guards_open (True)%I _ E (↑Nmain) with "ctx []") as "J". { solve_ndisj. } { done. }
      iMod "J" as "[J back]". iDestruct "J" as (sa sd blocked) "[State [Alive [Ou Blo]]]".
      
      assert (∃ k , (if b then LtAtomSwell k else LtAtomNotSwell k) ∉ (sa ∪ sd)) as Fres. {
          exists (fresh (set_map atom_unwrap (sa ∪ sd) : gset nat)).
          destruct b.
           - apply atom_not_in_swell. apply is_fresh.
           - apply atom_not_in_not_swell. apply is_fresh.
      }
      destruct Fres as [k Fres].
      
      iInv "other" as (outlives) "[£ [>Delayed O]]" "Hclose".
      iDestruct (outer_new_lt llft_name o_name d_name sa sd blocked (if b then LtAtomSwell k else LtAtomNotSwell k) with "[Ou Delayed]") as "X"; trivial. { iFrame "Ou". iFrame "Delayed". }
      iMod (fupd_mask_mono with "X") as "[Ou Delayed]". { solve_ndisj. }
      iMod ("Hclose" with "[£ Delayed O]"). { iFrame. }
      
      iMod (new_lt llft_name (if b then LtAtomSwell k else LtAtomNotSwell k) sa sd with "[State]") as "T".
      { set_solver. } { set_solver. } { iFrame. }
      iDestruct "T" as "[State [A1 A2]]".
      iMod ("back" with "[Alive State A1 Ou Blo]").
      { iExists (sa ∪ {[ (if b then LtAtomSwell k else LtAtomNotSwell k) ]}). iExists sd. iExists blocked. iFrame.
        unfold llft_alive.
        replace ((sa ∪ {[ (if b then LtAtomSwell k else LtAtomNotSwell k) ]})) with (({[ (if b then LtAtomSwell k else LtAtomNotSwell k) ]} ∪ sa)).
        { unfold llft_alive_def'. rewrite big_sepS_insert. { iFrame. } set_solver. } set_solver.
      }
      iModIntro.
      iExists (k). iFrame "A2".
  Qed.
  (* end hide *)
  
  Lemma llftl_begin' E :
      ↑Nllft ⊆ E →
      llft_ctx ⊢ |={E}=> ∃ κ, @[ κ ] ∗ ⌜κ ≠ llft_empty⌝.
  Proof.
      iIntros (Hmask) "LFT".
      iMod (llftl_begin_maybe_swell' E true with "LFT") as (k) "S"; trivial.
      unseal. iModIntro. iExists ({[ k ]}).
      rewrite big_sepS_singleton. iFrame. done.
  Qed.
  
  (* begin hide *)
  Local Lemma step_opt_mono (E1 E2 : coPset) (b: bool) (P : iProp Σ) :
      E1 ⊆ E2 →
      (|={E1}=> ▷?b (|={E1}=> P)) ⊢ |={E2,∅}=> ▷?b (|={∅,E2}=> P).
  Proof.
      intros Hmask. iIntros "A".
      iMod (fupd_mask_subseteq_emptyset_difference E2 E1) as "J"; trivial. iMod "A".
      iMod (fupd_mask_subseteq_emptyset_difference E1 ∅) as "J2"; first by set_solver.
      iModIntro. iNext. iMod "J2". replace (E1 ∖ ∅) with E1 by set_solver. iMod "A".
      iDestruct (fupd_mask_frame_r _ _ E1 with "J") as "J". { set_solver. }
      replace (∅ ∪ E1) with E1 by set_solver. replace ((E2 ∖ E1) ∪ E1) with E2.
         - iMod "J". iModIntro. iFrame. - replace (E2 ∖ E1 ∪ E1) with (E1 ∪ E2 ∖ E1) by set_solver. apply guard.copset_diff_union. trivial.
  Qed.

  Local Lemma llftl_end_maybe_swell' (k: lt_atom) b :
      (swell k → b = true) →
      llft_ctx -∗ Alive llft_name k ={↑Nllft,∅}=∗ ▷?b |={∅,↑Nllft}=> Dead llft_name k.
  Proof.
      intros Hswell. unseal. iIntros "[#other #ctx] token".  unfold llft_ctx.
  
      (* ending the lifetime *)
      iInv "other" as (outlives1) "[>£ [>Delayed [>O1 O2]]]" "Hclose".
      
      iDestruct (guards_open (True)%I _ (↑Nllft ∖ ↑NllftO) (↑Nmain) with "ctx []") as "J". { solve_ndisj. }
      { done. }
      iMod "J" as "[J back]". iDestruct "J" as (sa1 sd1 blocked1) "[State Alive]".
      iAssert (⌜k ∈ sa1⌝)%I as "%k_sa1".
      { iApply (lt_state_alive llft_name k sa1 sd1). iSplit. { iFrame "State". } iFrame "token". }
      
      iDestruct (LtState_disjoint llft_name _ _ with "State") as "%Hdisj".
      
      unfold llft_alive_def'. rewrite (big_sepS_delete _ sa1 k); trivial.
      iDestruct "Alive" as "[[token2 Alive] [Ou Blo]]".
      iMod (kill_lt llft_name k sa1 sd1 with "[State token token2]") as "[State #dead]". { iFrame. }
      
      iDestruct (outer_kill_lt_step1 llft_name o_name d_name sa1 sd1 blocked1 k with "[Ou Delayed]") as "X"; trivial. { set_solver. } { iFrame "Ou". iFrame "Delayed". }
      iMod (fupd_mask_mono with "X") as "[Ou Delayed]". { solve_ndisj. }
      
      iMod ("back" with "[State Alive Ou Blo]") as "true".
      { iExists (sa1 ∖ {[k]}). iExists (sd1 ∪ {[k]}). iExists blocked1. iFrame. }
      
      destruct (decide (filter (λ (o: (gset lt_atom * lt_atom)) , o.2 = k ∧ o.1 ⊆ sa1 ∖ {[k]}) outlives1 = ∅)).
      { 
        assert (∀ other , (other, k) ∈ outlives1 → ¬(other ⊆ sa1 ∖ {[k]})) as Houtlives.
        { intros other. intros Hin Hdisj2. 
          assert ((other,  k) ∈ filter (λ o : gset lt_atom * lt_atom, o.2 = k ∧ o.1 ⊆ sa1 ∖ {[k]}) outlives1) as X. { rewrite elem_of_filter. set_solver. } rewrite e in X. set_solver. }
          
       iDestruct (guards_open (True)%I _ (↑Nllft ∖ ↑NllftO) (↑Nmain) with "ctx []") as "J". { solve_ndisj. }
      { done. }
      iMod "J" as "[J back]". iDestruct "J" as (sa2 sd2 blocked2) "[State [Alive [Ou Blo]]]".
      
      destruct (decide (k ∈ blocked2)). {
        iDestruct (big_sepS_delete _ _ k with "Blo") as "[B Blo]"; trivial.
        iExFalso. iApply (lt_alive_dead_false llft_name k). iSplit. { iFrame. } iFrame "dead".
      }
      
      iDestruct (outer_kill_lt_step2 llft_name o_name d_name sa2 sd2 blocked2 outlives1 k (sa1 ∖ {[k]}) b with "[Ou Delayed O1]") as "X"; trivial. { iFrame "Ou". iFrame "Delayed". iFrame "O1". iFrame "dead". }
      iDestruct (step_opt_mono (↑Nbox ∪ ↑NllftUsr ∪ ↑NllftUsr2) (↑Nllft ∖ ↑NllftO ∖ ↑Nmain) with "X") as "X". { apply union_subseteq. split; solve_ndisj. }
      iMod "X". iModIntro. iNext. iMod "X". iDestruct "X" as "[Inv [Outlives Delayed]]".
       
      iMod ("back" with "[Alive State Blo Inv]") as "X". { iExists sa2. iExists sd2. iExists blocked2.
        iFrame "State". iFrame "Alive". iFrame "Inv". iFrame "Blo". }
      iMod ("Hclose" with "[Outlives Delayed O2 £]") as "Y".
      { iNext. iExists outlives1. iFrame. }
      
      iModIntro. iFrame "dead".
     }
     
     (* case: something violates the outlives relation. derive a contradiction. *)
     assert (∃ (x : gset lt_atom * lt_atom) , x ∈ filter (λ o : gset lt_atom * lt_atom, o.2 = k ∧ o.1 ⊆ sa1 ∖ {[k]}) outlives1) as Hex_x. { apply set_choose_L; trivial. }
     destruct Hex_x as [[oalive odead] Hex].
     rewrite elem_of_filter in Hex. simpl in Hex. destruct Hex as [[Hex1 Hex2] Hex3].
     subst odead.
     iMod (fupd_mask_subseteq ∅) as "Hupd". { set_solver. }
     iMod (lc_fupd_elim_later with "£ O2") as "O2".
     iModIntro. iModIntro. iMod "Hupd" as "_".
     iDestruct ("O2" $! ((oalive, k)) with "[]") as "#Oguard". { iPureIntro; trivial. }
     iDestruct (llftl_incl_dead_implies_dead_unswell (↑NllftG) oalive {[k]} with "[] [] []") as "#OdeadUpd".
     { solve_ndisj. }
     { unseal. iFrame "#". }
     { unseal. unfold llft_incl. unseal. unfold llft_alive_def'. rewrite big_sepS_singleton.
      iFrame "Oguard". }
     { unseal. iFrame "dead". iPureIntro. set_solver. }
     
     iMod (fupd_mask_mono with "OdeadUpd") as "#Odead". { solve_ndisj. }
     
     iDestruct (guards_open (True)%I _ (↑Nllft ∖ ↑NllftO) (↑Nmain) with "ctx []") as "J". { solve_ndisj. }  { done. }
     iMod "J" as "[J back]". iDestruct "J" as (sa2 sd2 blocked2) "[State [Alive [Ou Blo]]]".
     iDestruct "Ou" as (opt_k) "[>Delayed2 X]".
     iDestruct (delayed_agree with "[Delayed Delayed2]") as "%Dagree". { iFrame "Delayed". iFrame "Delayed2". }
     subst opt_k. iDestruct "X" as "[X1 [X2 [X3 >X4]]]". iDestruct "X4" as "%Hsa2eq".
     subst sa2.
     iDestruct (big_sepS_subseteq _ _ oalive with "Alive") as "Alive"; trivial.
     iExFalso. iApply (llftl_not_own_end_unswell oalive with "[Alive] Odead"). { unseal. iFrame "Alive". }
  Qed.
  (* end hide *)
  
  Lemma llftl_end' κ :
      κ ≠ llft_empty →
      llft_ctx -∗ @[ κ ] ={↑Nllft}[∅]▷=∗ [† κ ].
  Proof.
      intros Hnotempty.
      assert (∃ k, k ∈ κ) as Hex_k. { apply set_choose_L; trivial. }
      destruct Hex_k as [k Hin_k].
      iIntros "LFT A". iMod (llftl_end_maybe_swell' (LtAtomSwell k) true with "LFT [A]") as "J".
        - intros; done.
        - unseal. rewrite (big_sepS_delete _ _ k); last by trivial.
          iDestruct "A" as "[$ _]".
        - iModIntro. iNext. iMod "J". iModIntro. unseal. iExists k. iSplit; done.
  Qed.
  
  (** LeLiLo-Begin *)
  Lemma llftl_begin E :
      ↑Nllft ⊆ E →
      llft_ctx ⊢ |={E}=> ∃ κ, @[ κ ] ∗ □ (@[ κ ] ={↑Nllft}[∅]▷=∗ [† κ ]).
  Proof.
    intros Hmask. iIntros "#ctx".
    iMod (llftl_begin' with "ctx") as (κ) "[Alive %nonemp]"; first by trivial.
    iModIntro. iExists κ. iFrame "Alive". iModIntro.
    iApply llftl_end'; done.
  Qed.
  
  (** Shared borrows *)
  
  (* begin hide *)
  Local Lemma llftl_borrow_shared_maybe_swell E κ (P : iProp Σ) :
      ↑Nllft ⊆ E →
      ▷ P ={E}=∗ (llft_alive_def' κ &&{↑NllftG}&&> ▷ P) ∗ (llft_dead_def' κ ={E}=∗ ▷ P).
  Proof.
    intros Hmask. iIntros "P".
    iMod new_cancel as (γc) "c1".
    iMod (guards_alloc_with_inv (NllftG) E ((P ∨ (llft_dead_def' κ ∗ CCancel γc))) with "[P]") as "[#Tinv #Tguard]".
    { iNext. iLeft. iFrame "P". }
    iModIntro.
    iSplit.
    { 
      iAssert (llft_alive_def' κ &&{ ↑NllftG ∪ ↑NllftG }&&> ▷ P) as "H".
      { iApply
        (guards_cancel_or (llft_alive_def' κ) (llft_alive_def' κ) (llft_dead_def' κ ∗ CCancel γc) (▷ P)).
        { iIntros "t".
          iAssert (llft_dead_def' κ) as "#D". { iDestruct "t" as "[_ [$ _]]". }
          iApply (llftl_not_own_end_unswell κ with "[t] D").
          { iDestruct "t"  as "[$ _]". }
        }
        iSplit. { iApply guards_refl. }
        { setoid_replace (llft_dead_def' κ ∗ CCancel γc ∨ ▷ P)%I
            with (▷ P ∨ llft_dead_def' κ ∗ CCancel γc)%I.
          { iDestruct (guards_true (↑NllftG) (llft_alive_def' κ)) as "gt".
            iDestruct (guards_transitive (↑NllftG) (llft_alive_def' κ)%I with "gt Tguard") as "J".
            rewrite bi.later_or.
            iDestruct (guards_remove_later_or_r (llft_dead_def' κ ∗ CCancel γc) (▷ P) (↑NllftG)) as "X".
            iDestruct (guards_transitive (↑NllftG) (llft_alive_def' κ)%I with "J X") as "R".
            iFrame "R".
          }
          rewrite bi.or_comm. trivial.
        }
      }
      rewrite subseteq_union_1_L. { iFrame "H". } set_solver.
    }
    iIntros "deadk".
    iDestruct (guards_open (True)%I (▷ (P ∨ llft_dead_def' κ ∗ CCancel γc))%I E (↑ NllftG) with "Tguard []") as "J". { solve_ndisj. }
    { done. }
    iMod "J" as "[J K]". rewrite bi.later_or. iDestruct "J" as "[P|J]".
    { iDestruct ("K" with "[deadk c1]") as "K". { iRight. iFrame. }
        iMod "K" as "K". iModIntro. iFrame "P". }
    iDestruct "J" as "[_ c2]". iMod "c2".
    iDestruct (cancel_cancel_false γc with "[c1 c2]") as "J". { iFrame. } iExFalso. iFrame "J".
  Qed.
  (* end hide *)
  
  (** LeLiLo-Shr-Borrow *)
  Lemma llftl_borrow_shared E κ (P : iProp Σ) :
      ↑Nllft ⊆ E →
      ▷ P ={E}=∗ (@[ κ ] &&{↑NllftG}&&> ▷ P) ∗ ([† κ ] ={E}=∗ ▷ P).
  Proof.
      unseal. rewrite <- big_sepS_set_map. rewrite dead_def_set_map.
      apply llftl_borrow_shared_maybe_swell.
  Qed.
  
  (** LeLiLo-Shr-Pers *)
  Lemma llftl_borrow_shared_persistent κ (P : iProp Σ) :
      Persistent (@[ κ ] &&{↑NllftG}&&> ▷ P).
  Proof.
      typeclasses eauto.
  Qed.
  
  (** Indexed borrows and full borrows *)
  
  Definition Idx: Type := slice_name * gset nat. 
  
  (* begin hide *)
  Local Definition idx_bor_def' (κ: gset lt_atom) (idx: Idx) (P: iProp Σ) : iProp Σ :=
      let (sn, κ') := idx in
        (llft_alive_def' κ &&{↑NllftG}&&> @[κ']) ∗ (∃ P', ▷ □ (P' ↔ P) ∗ slice Nbox sn P').
  
  Local Definition idx_bor_def (κ: lft) (idx: Idx) (P: iProp Σ) : iProp Σ :=
      let (sn, κ') := idx in
        κ ⊑ κ' ∗ (∃ P', ▷ □ (P' ↔ P) ∗ slice Nbox sn P').
  Local Definition idx_bor_aux : seal (@idx_bor_def). Proof. by eexists. Qed.
  
  Local Definition full_bor_def (κ: lft) (P: iProp Σ) : iProp Σ :=
      ∃ sn κ' ,
        κ ⊑ κ'
          ∗ (∃ P', ▷ □ (P' ↔ P) ∗ slice Nbox sn P')
          ∗ OwnBorState llft_name sn (Borrow (set_map LtAtomSwell κ') {[default_dead]}).
  Local Definition full_bor_aux : seal (@full_bor_def). Proof. by eexists. Qed.

  (* end hide *)
        
  Definition idx_bor (κ: lft) (idx: Idx) (P: iProp Σ) : iProp Σ.
    exact (idx_bor_aux.(unseal) κ idx P). Defined.
  
  Definition full_bor (κ: lft) (P: iProp Σ) : iProp Σ.
    exact (full_bor_aux.(unseal) κ P). Defined.
    
  (* begin hide *)
  Local Definition idx_bor_unseal : @idx_bor = @idx_bor_def := idx_bor_aux.(seal_eq).
  Local Definition full_bor_unseal : @full_bor = @full_bor_def := full_bor_aux.(seal_eq).
      
  Local Ltac unseal_bor := rewrite
    ?idx_bor_unseal /idx_bor_def
    ?full_bor_unseal /full_bor_def.
  (* end hide *) 
        
  Global Instance pers_idx_bor κ idx P : Persistent (idx_bor κ idx P).
  Proof. destruct idx. unseal_bor. typeclasses eauto. Qed.
  
  Definition idx_bor_tok (idx: Idx) : iProp Σ :=
      let (sn, κ') := idx in
          OwnBorState llft_name sn (Borrow (set_map LtAtomSwell κ') {[default_dead]}).
          
          
  Notation "&{ κ }" := (full_bor κ) (format "&{ κ }") : bi_scope.
  Notation "&{ κ , i }" := (idx_bor κ i) (format "&{ κ , i }") : bi_scope.
          
  Global Instance full_bor_proper κ :
    Proper ((≡) ==> (≡)) (&{κ})%I.
  Proof. unseal_bor. solve_proper. Qed.
  
  Global Instance full_bor_nonexpansive κ :
    NonExpansive (&{κ})%I.
  Proof. unseal_bor. solve_proper. Qed.
  
  Global Instance full_bor_contractive κ :
    Contractive (&{κ})%I.
  Proof. unseal_bor. solve_contractive. Qed.
  
  Global Instance idx_bor_proper κ i :
    Proper ((≡) ==> (≡)) (&{κ, i})%I.
  Proof. unseal_bor. solve_proper. Qed.
  
  Global Instance idx_bor_nonexpansive κ i :
    NonExpansive (&{κ, i})%I.
  Proof. unseal_bor. solve_proper. Qed.
  
  Global Instance idx_bor_contractive κ i :
    Contractive (&{κ, i})%I.
  Proof. unseal_bor. solve_contractive. Qed.
  
  Global Instance timeless_idx_bor_tok i : Timeless (idx_bor_tok i).
  Proof. destruct i. typeclasses eauto. Qed.
  
  Lemma llftl_bor_idx κ P :
      &{κ} P ⊣⊢ ∃ idx , &{κ, idx} P ∗ idx_bor_tok idx.
  Proof.
    unseal_bor. iIntros. iSplit.
    { iIntros "F". iDestruct "F" as (sn κ') "[F [G H]]". iExists (sn, κ'). iFrame. }
    { iIntros "F". iDestruct "F" as (idx) "[F G]". destruct idx as [sn κ'].
      iDestruct "F" as "[F H]". iFrame. }
  Qed.
  
  Lemma llftl_bor_idx_to_full κ idx P :
      &{κ, idx} P -∗ idx_bor_tok idx -∗ &{κ} P.
  Proof.
    iIntros "A B". iApply llftl_bor_idx. iExists idx. iFrame.
  Qed.

  Lemma llftl_idx_shorten κ κ' idx P :
      κ' ⊑ κ -∗ &{κ, idx} P -∗ &{κ', idx} P.
  Proof.
      unseal_bor. destruct idx as [sn κ2]. iIntros "#g [#g2 #slice]". unfold idx_bor. 
      iFrame "slice".
      leaf_goal rhs to (@[κ])%I; iFrame "#".
  Qed.

  (* begin hide *) 
  Local Lemma make_everything_alive new sa sd blocked E :
      (↑Nbox ⊆ E) →
      LtState llft_name sa sd
        -∗ llft_alive_def' sa
        -∗ ▷ outer_inv llft_name o_name d_name sa sd blocked
        -∗ Delayed d_name None
        -∗ |={E}=> ∃ sa' ,
        ⌜ new ⊆ sa' ∪ sd ⌝
        ∗ LtState llft_name sa' sd
        ∗ llft_alive_def' sa'
        ∗ ▷ outer_inv llft_name o_name d_name sa' sd blocked
        ∗ Delayed d_name None.
  Proof.
    intros Hmask. induction new as [|x T ? IH] using set_ind_L. 
    - iIntros "State Alive OuInv Delayed". iModIntro. iExists sa. iFrame "OuInv".
      iFrame. iPureIntro. set_solver.
    - iIntros "State Alive OuInv Delayed". iMod (IH with "State Alive OuInv Delayed") as "X".
      iDestruct "X" as (sa') "[%HTin [State [Alive [OuInv Delayed]]]]".
      destruct (decide (x ∈ sa' ∪ sd)) as [Hin|Hout].
      + iModIntro. iExists sa'. iFrame "OuInv". iFrame. iPureIntro. set_solver.
      + iDestruct (outer_new_lt llft_name o_name d_name sa' sd blocked x with "[OuInv Delayed]") as "X".
        { trivial. } { iFrame "OuInv". iFrame. }
        iMod (fupd_mask_mono with "X") as "[OuInv Delayed]"; trivial.
        iMod (new_lt llft_name x sa' sd with "State") as "[State [Al1 Al2]]".
        { set_solver. } { set_solver. }
        iModIntro. iExists (sa' ∪ {[x]}). iFrame "OuInv". iFrame.
        iSplitR.
        { iPureIntro. set_solver. }
        unfold llft_alive_def'. rewrite big_sepS_union; last by set_solver.
        iFrame "Alive". rewrite big_sepS_singleton. iFrame "Al1".
  Qed.
  
  Local Lemma outer_get_dead alive dead blocked
    : Delayed d_name None -∗ ▷ outer_inv llft_name o_name d_name alive dead blocked -∗ ▷ ⌜default_dead ∈ dead⌝.
  Proof.
    iIntros "Delayed1 OuInv". iNext. iDestruct "OuInv" as (opt_k) "[Delayed2 OuInv]".
    iDestruct (delayed_agree with "[Delayed1 Delayed2]") as "%Heq".
      { iFrame "Delayed1". iFrame "Delayed2". }
    subst opt_k.
    unfold inner_inv.
    iDestruct "OuInv" as (mbs mprops Ptotal outlives) "[_ [_ [_ [_ [%W _]]]]]".
    iPureIntro. unfold lifetime_internals.inv.map_wf in W. intuition.
  Qed.
  
  Local Lemma alive_alive_disjoint κ κ' sa :
    κ ⊆ sa →
    llft_alive_def' sa -∗ llft_alive_def' κ -∗ llft_alive_def' κ' -∗ ⌜κ ## κ'⌝.
  Proof.
    unfold llft_alive_def'. intros Hksa. iIntros "Set1 Set2 Set3".
    destruct (decide (κ ## κ')) as [Hdisj|Hnotdisj]; first by iPureIntro; trivial.
    assert (∃ x , x ∈ κ ∩ κ') as Hex_x. { apply set_choose_L; set_solver. }
    destruct Hex_x as [x Hxin].
    rewrite (big_sepS_delete _ sa x); last by set_solver.
    rewrite (big_sepS_delete _ κ x); last by set_solver.
    rewrite (big_sepS_delete _ κ' x); last by set_solver.
    iDestruct "Set1" as "[Alive1 _]".
    iDestruct "Set2" as "[Alive2 _]".
    iDestruct "Set3" as "[Alive3 _]".
    iExFalso. iApply alive_alive_alive_false. iFrame "Alive1". iFrame.
  Qed.
  
  Local Lemma augment_outlives sa sd blocked outlives κ κ' E :
    (κ ⊆ sa) →
    (κ' ⊆ sa) →
    (↑Nbox ⊆ E) →
    (llft_alive_def' κ &&{↑NllftG}&&> llft_alive_def'  κ')
    -∗ Delayed d_name None
    -∗ ▷ (Outlives o_name outlives ∗
           ∀ o : gset lt_atom * lt_atom,
             ⌜o ∈ outlives⌝ -∗ llft_alive_def' o.1 &&{ ↑NllftG }&&> Alive llft_name o.2)
    -∗ ▷ outer_inv llft_name o_name d_name sa sd blocked
    -∗ LtState llft_name sa sd
    -∗ |={E}=> ∃ outlives' ,
    ⌜ ∀ k : lt_atom, k ∈ κ' → (κ, k) ∈ outlives' ⌝
    ∗ Delayed d_name None
    ∗ ▷ (Outlives o_name outlives' ∗
           ∀ o : gset lt_atom * lt_atom,
             ⌜o ∈ outlives'⌝ -∗ llft_alive_def' o.1 &&{ ↑NllftG }&&> Alive llft_name o.2)
    ∗ ▷ outer_inv llft_name o_name d_name sa sd blocked
    ∗ LtState llft_name sa sd.
  Proof.
    intros Hk Hk' Hmask. iIntros "#Hincl Delayed [>Outlives #Hf] OuInv LtState".
    
    iDestruct (bi.later_mono _ _ (inv_get_outlives_condition llft_name o_name sa sd blocked outlives) with "[Outlives OuInv Delayed]") as "#>%Howf".
    { unfold outer_inv. iDestruct "OuInv" as (opt_k) "[Delayed1 X]".  iNext.
      iDestruct (delayed_agree with "[Delayed1 Delayed]") as "%Heq".
      { iFrame "Delayed". iFrame "Delayed1". } subst opt_k. iFrame. }
      
    iDestruct (bi.later_mono _ _ (inv_get_outlives_consistent llft_name o_name sa sd blocked outlives) with "[Outlives OuInv Delayed]") as "#>%Hoc".
    { unfold outer_inv. iDestruct "OuInv" as (opt_k) "[Delayed1 X]".  iNext.
      iDestruct (delayed_agree with "[Delayed1 Delayed]") as "%Heq".
      { iFrame "Delayed". iFrame "Delayed1". } subst opt_k. iFrame. }
      
    iDestruct (bi.later_mono _ _ (inv_get_alive_dead_disj llft_name o_name sa sd blocked) with "[Outlives OuInv Delayed]") as "#>%Hdisj".
    { unfold outer_inv. iDestruct "OuInv" as (opt_k) "[Delayed1 X]".  iNext.
      iDestruct (delayed_agree with "[Delayed1 Delayed]") as "%Heq".
      { iFrame "Delayed". iFrame "Delayed1". } subst opt_k. iFrame. }
    
    iDestruct (outer_augment_outlives llft_name o_name d_name sa sd blocked outlives
        (outlives ∪ (set_map (λ k, (κ, k)) κ'))
        with "[Delayed Outlives OuInv]") as "X".
    { set_solver. }
    { set_solver. }
    { unfold outlives_consistent. unfold outlives_consistent in Hoc. set_solver. }
    { iFrame. }
    
    iMod (fupd_mask_mono with "X") as "[D [OuInv X]]"; trivial.
    
    iExists (outlives ∪ (set_map (λ k, (κ, k)) κ')).
    iModIntro.
    iFrame.
    iSplitL.
    { iPureIntro. set_solver. }
    iNext.
    iIntros (o) "%Hoin". rewrite elem_of_union in Hoin.
    destruct Hoin as [Hoin_outlives|Hoin_setmap].
    - iApply "Hf". iPureIntro. trivial.
    - rewrite elem_of_map in Hoin_setmap. destruct Hoin_setmap as [x [Hoeq Hxin]]. subst o.
      simpl.
      leaf_goal rhs to (llft_alive_def' κ').
      + unfold llft_alive_def'. rewrite (big_sepS_delete _ κ' x); trivial.
        iApply guards_weaken_sep_l.
      + iFrame "Hincl".
  Qed.
  
  Local Lemma llftl_idx_acc_fwd E κ idx P :
      ↑Nllft ⊆ E →
      llft_ctx ∗ idx_bor_def' κ idx P ⊢
        idx_bor_tok idx ∗ llft_alive_def' κ ={E}=∗ (▷ P)
          ∗ OwnBorState llft_name (idx.1) (Unborrow κ (set_map LtAtomSwell idx.2) {[default_dead]}).
  Proof.
      unseal_bor. unseal. unfold idx_bor_def'. intros Hmask.
      destruct idx as [sn κ']. iIntros "[[#other #ctx] [#Incl #Slice]] [OwnBor k]". unfold idx_bor_tok.
      
      iInv "other" as (outlives) "[>£ [>Delayed O]]" "Hclose".
      
      iDestruct (guards_open (True)%I _ (E ∖ ↑NllftO) (↑Nmain) with "ctx []") as "J". { solve_ndisj. } { done. }
      iMod "J" as "[J back]". iDestruct "J" as (sa sd blocked) "[State [Alive [OuInv Blo]]]".
      iMod (make_everything_alive (κ ∪ (set_map LtAtomSwell κ') ∪ {[default_dead]}) with "State Alive OuInv Delayed") as (sa') "[%Hsa [State [Alive [OuInv Delayed]]]]". { solve_ndisj. }
      
      
      iDestruct (outer_get_dead with "Delayed OuInv") as "#>%Hdd".
      iDestruct (lt_state_alive_set llft_name κ sa' sd with "[State k]") as "%Hksa'". { iFrame. }
      
      destruct (decide (set_map LtAtomSwell κ' ⊆ sa')) as [Hk'sa'|Hk'sa'].
      { 
      iDestruct (alive_alive_disjoint with "Alive k Blo") as "%Hblocked_disj"; trivial.
      iMod (augment_outlives _ _ _ _ κ (set_map LtAtomSwell κ') with "[Incl] Delayed O OuInv State") as (outlives') "[%Ho' [Delayed [O [OuInv State]]]]".
      { set_solver. } { set_solver. } { solve_ndisj. }
      { unseal. unfold llft_alive_def'. rewrite big_sepS_set_map. iFrame "Incl". }
      iDestruct "O" as "[>Ostate Oguards]".
      
      iClear "other". iClear "ctx".
      
      iDestruct "Slice" as (P') "[PEquiv Slice]".
      iDestruct (outer_unborrow_start llft_name o_name d_name sa' sd blocked outlives' sn κ (set_map LtAtomSwell κ') {[default_dead]} P' with "[Delayed OuInv OwnBor Ostate]") as "X"; trivial. { set_solver. } { set_solver. } { iFrame. iFrame "Slice". }
      iMod (fupd_mask_mono with "X") as "[Delayed [OuInv [Ostate [OwnBor P]]]]". { solve_ndisj. }
      
      iMod ("back" with "[State Alive OuInv Blo k]"). {
        iExists sa'. iExists sd. iExists (blocked ∪ κ). iFrame "State".
        iFrame "Alive". iFrame "OuInv". unfold llft_alive_def'. rewrite big_sepS_union.
        { iFrame. } set_solver.
      }
      iMod ("Hclose" with "[Delayed Ostate Oguards £]"). { iNext. iExists outlives'. iFrame. }
      iModIntro. iFrame. iNext. iApply "PEquiv". iFrame.
      }
      
      assert (∃ x , x ∈ (set_map LtAtomSwell κ') ∩ sd) as Hex_x. { apply set_choose_L.
          assert ((set_map LtAtomSwell κ') ⊆ sa' ∪ sd) as X by set_solver.
          set_solver. }
      destruct Hex_x as [x Hex].
      iDestruct (LtState_entails_Dead llft_name x sa' sd with "State") as "#Deadx". { set_solver. }
      
      iMod ("back" with "[State Alive OuInv Blo]"). { iExists sa'. iExists sd. iExists blocked. iFrame. }
      
      iMod (llftl_incl_dead_implies_dead_unswell _ κ (set_map LtAtomSwell κ') with "[] [Incl] []") as "HdeadkUpd".
          { solve_ndisj. }
          { iFrame "#". unseal. iFrame "#". }
          { unseal. unfold llft_alive_def'. rewrite big_sepS_set_map. iFrame "Incl". }
          { unseal. iFrame "Deadx". iPureIntro. set_solver. }
      iMod (fupd_mask_mono with "HdeadkUpd") as "#Hdeadk". { solve_ndisj. }
      iExFalso. iApply (llftl_not_own_end_unswell κ with "[k] Hdeadk"). unseal. iFrame.
  Qed.
  
  (*Lemma llftl_idx_acc_back κ idx P :
      llft_ctx ∗ &{κ, idx} P ⊢
        OwnBorState llft_name (idx.1) (Unborrow κ idx.2 {[default_dead]}) ∗ (▷ P)
        ={↑Nllft}=∗ idx_bor_tok idx.
  Proof.*)
  
  Local Instance pers_idx_bor_def' κ idx P : Persistent (idx_bor_def' κ idx P).
  Proof. destruct idx. unseal_bor. typeclasses eauto. Qed.
  
  Local Lemma llftl_idx_acc_back_vs κ idx P Q :
      llft_ctx ∗ idx_bor_def' κ idx P ⊢
        OwnBorState llft_name (idx.1) (Unborrow κ (set_map LtAtomSwell idx.2) {[default_dead]}) ∗ (▷ Q)
          ∗ ▷ (▷ Q ∗ llft_dead_def' κ ={↑NllftUsr ∪ ↑NllftUsr2}=∗ ▷ P)
        ={↑Nllft}=∗ ∃ sn, idx_bor_def' κ (sn, idx.2) Q ∗ idx_bor_tok (sn, idx.2) ∗ llft_alive_def' κ.
  Proof.
      unseal_bor. unseal.
      iIntros "[[#other #ctx] #idxbor] [OwnBor [Q vs]]". destruct idx as [sn κ'].
      unfold idx_bor. iDestruct "idxbor" as "[#incl #slice]".
      
      iInv "other" as (outlives) "[£ [>Delayed O]]" "Hclose".
      iDestruct (guards_open (True)%I _ (↑Nllft ∖ ↑NllftO) (↑Nmain) with "ctx []") as "J". { solve_ndisj. } { done. }
      iMod "J" as "[J back]". iDestruct "J" as (sa sd blocked) "[State [Alive [OuInv Blo]]]".
      
      iDestruct "slice" as (P') "[PEquiv slice]".
      iDestruct (outer_unborrow_end llft_name o_name d_name sa sd blocked sn κ (set_map LtAtomSwell κ') {[default_dead]} P' Q with "[Delayed OuInv OwnBor slice vs Q]") as "X". { apply swell_set_set_map. } { apply swell_set_default_dead. } { iFrame. iFrame "#". iNext. 
        iIntros "A". iMod ("vs" with "A") as "P". iModIntro. iApply "PEquiv". iFrame. }
      iMod (fupd_mask_mono with "X") as (sn2) "[Delayed [OuInv [OwnBor [#slice2 %Hbl]]]]". { solve_ndisj. }
      
      iAssert (llft_alive_def' (blocked ∖ κ) ∗ llft_alive_def' κ)%I with "[Blo]" as "[Blo Ret]". {
        unfold llft_alive_def'. rewrite <- big_sepS_union. { 
          replace (blocked ∖ κ ∪ κ) with blocked. { iFrame. }
          apply set_eq. intro x. destruct (decide (x ∈ κ)); set_solver.
        } set_solver.
      }
      
      iMod ("back" with "[State Alive OuInv Blo]"). { iExists sa. iExists sd. iExists (blocked ∖ κ). iFrame. }
      iMod ("Hclose" with "[Delayed O £]"). { iNext. iExists outlives. iFrame. }
      iModIntro. iFrame "Ret". iExists sn2. iFrame "OwnBor". iFrame "incl". iExists Q.
      iFrame "#". iModIntro. iModIntro. iSplit; iIntros; done.
  Qed.
  
  Local Lemma llftl_idx_acc_back_at_same_idx κ idx P :
      llft_ctx ∗ idx_bor_def' κ idx P ⊢
        OwnBorState llft_name (idx.1) (Unborrow κ (set_map LtAtomSwell idx.2) {[default_dead]}) ∗ (▷ P)
        ={↑Nllft}=∗ idx_bor_tok idx ∗ llft_alive_def' κ.
  Proof.
      unseal_bor. unseal.
      iIntros "[[#other #ctx] #idxbor] [OwnBor Q]". destruct idx as [sn κ'].
      unfold idx_bor. iDestruct "idxbor" as "[#incl #slice]".
      
      iInv "other" as (outlives) "[£ [>Delayed O]]" "Hclose".
      iDestruct (guards_open (True)%I _ (↑Nllft ∖ ↑NllftO) (↑Nmain) with "ctx []") as "J". { solve_ndisj. } { done. }
      iMod "J" as "[J back]". iDestruct "J" as (sa sd blocked) "[State [Alive [OuInv Blo]]]".
      
      iDestruct "slice" as (P') "[PEquiv slice]".
      iDestruct (outer_unborrow_end_at_same_idx llft_name o_name d_name sa sd blocked sn κ (set_map LtAtomSwell κ') {[default_dead]} P' with "[Delayed OuInv OwnBor slice Q]") as "X".
      { apply swell_set_set_map. } { apply swell_set_default_dead. }
      { iFrame. iFrame "#". iNext. iApply "PEquiv". iFrame. }
      iMod (fupd_mask_mono with "X") as "[Delayed [OuInv [OwnBor %Hbl]]]". { solve_ndisj. }
      
      iAssert (llft_alive_def' (blocked ∖ κ) ∗ llft_alive_def' κ)%I with "[Blo]" as "[Blo Ret]". {
        unfold llft_alive_def'. rewrite <- big_sepS_union. { 
          replace (blocked ∖ κ ∪ κ) with blocked. { iFrame. }
          apply set_eq. intro x. destruct (decide (x ∈ κ)); set_solver.
        } set_solver.
      }
      
      iMod ("back" with "[State Alive OuInv Blo]"). { iExists sa. iExists sd. iExists (blocked ∖ κ). iFrame. }
      iMod ("Hclose" with "[Delayed O £]"). { iNext. iExists outlives. iFrame. }
      iModIntro. iFrame "Ret". iFrame "OwnBor".
  Qed.
  
  Lemma llftl_bor_acc_maybe_swell' E P κ' κ :
      ↑Nllft ⊆ E →
      llft_ctx -∗ (llft_alive_def' κ' &&{↑NllftG}&&> @[κ]) -∗ &{κ} P -∗ llft_alive_def' κ' -∗ |={E}=> (▷ P) ∗
          (∀ Q, ▷ (▷ Q ={↑NllftUsr ∪ ↑NllftUsr2}=∗ ▷ P) ∗ ▷ Q ={↑Nllft}=∗ (&{κ} Q) ∗ llft_alive_def' κ').
  Proof.
    unseal_bor. intros Hmask.
    iIntros "#ctx #incl1 fb alive". unfold full_bor. iDestruct "fb" as (sn κ'') "[#incl [#slice OwnBor]]". iDestruct (guards_transitive with "incl1 incl") as "incl2".
    iMod (llftl_idx_acc_fwd E κ' (sn, κ'') P with "[] [OwnBor alive]") as "[P OwnBor]".
      { trivial. } { iFrame "#". } { iFrame. }
    iModIntro. iFrame "P". iIntros (Q) "[vs Q]".
    iMod (llftl_idx_acc_back_vs κ' (sn, κ'') P Q with "[] [OwnBor Q vs]") as (sn2) "[#bor2 [tok2 alive]]".
      { unseal_bor. iFrame "#". } { iFrame. iNext. iIntros "[Q _]". iApply "vs". iFrame. }
    iModIntro. unseal_bor. iFrame "tok2". iFrame "incl".
    iDestruct "bor2" as "[incl3 slice']". iFrame "slice'". iFrame "alive".
  Qed.
  
  (* end hide *)
  
  Lemma llftl_bor_acc' E P κ' κ :
      ↑Nllft ⊆ E →
      llft_ctx -∗ κ' ⊑ κ -∗ &{κ} P -∗ @[κ'] -∗ |={E}=> (▷ P) ∗
          (∀ Q, ▷ (▷ Q ={↑NllftUsr ∪ ↑NllftUsr2}=∗ ▷ P) ∗ ▷ Q ={↑Nllft}=∗ (&{κ} Q) ∗ @[κ']).
  Proof.
    iIntros (Hmask) "ctx Incl Bor Alive".
    iMod (llftl_bor_acc_maybe_swell' E P (set_map LtAtomSwell κ') κ Hmask with "ctx [Incl] Bor [Alive]") as "[P R]".
      - unfold llft_incl. unseal. unfold llft_alive_def'. rewrite <- big_sepS_set_map. iFrame.
      - unseal. unfold llft_alive_def'. rewrite <- big_sepS_set_map. iFrame.
      - iModIntro. iFrame "P". iIntros (Q) "[A B]". iMod ("R" $! Q with "[A B]") as "[$ A]".
        + iFrame.
        + iModIntro. unseal. unfold llft_alive_def'. rewrite <- big_sepS_set_map. iFrame.
  Qed.
  
  Lemma llftl_bor_acc E P κ :
      ↑Nllft ⊆ E →
      llft_ctx -∗ &{κ} P -∗ @[κ] -∗ |={E}=> (▷ P) ∗
          (∀ Q, ▷ (▷ Q ∗ [†κ] ={↑NllftUsr ∪ ↑NllftUsr2}=∗ ▷ P) ∗ ▷ Q ={↑Nllft}=∗ (&{κ} Q) ∗ @[κ]).
  Proof.
    unseal_bor. intros Hmask.
    iIntros "#ctx fb alive". unfold full_bor. iDestruct "fb" as (sn κ') "[#incl [#slice OwnBor]]".
    iMod (llftl_idx_acc_fwd E (set_map LtAtomSwell κ) (sn, κ') P with "[] [OwnBor alive]") as "[P OwnBor]".
      { trivial. } { unseal_bor. iFrame "#". unfold llft_incl. unseal. unfold llft_alive_def'. rewrite big_sepS_set_map. iFrame "incl". } { iFrame. unseal. unfold llft_alive_def'. rewrite big_sepS_set_map. iFrame "alive". }
    iModIntro. iFrame "P". iIntros (Q) "[vs Q]".
    iMod (llftl_idx_acc_back_vs (set_map LtAtomSwell κ) (sn, κ') P Q with "[] [OwnBor Q vs]") as (sn2) "[#bor2 [fb alive]]".
      { unseal_bor. iFrame "#". unfold llft_incl. unseal. unfold llft_alive_def'. rewrite big_sepS_set_map. iFrame "incl". } { iFrame. unseal. unfold llft_dead_def'. rewrite dead_def_set_map. iFrame "vs". }
    iModIntro. iSplitR "alive". { unfold idx_bor_def'. iDestruct "bor2" as "[a b]". iFrame. iFrame "#". }
    unseal. unfold llft_alive_def'. rewrite big_sepS_set_map. iFrame "alive".
  Qed.
  
  Lemma llftl_bor_acc_atomic P κ :
      llft_ctx -∗ &{κ} P -∗ |={↑Nllft, ∅}=>
          (▷ P ∗ (∀ Q, ▷ (▷ Q ∗ [†κ] ={↑NllftUsr ∪ ↑NllftUsr2}=∗ ▷ P) -∗ ▷ Q ={∅, ↑Nllft}=∗ &{κ} Q))
          ∨ ([†κ] ∗ (|={∅, ↑Nllft}=> True)).
  Proof.
      unseal_bor. unseal.
      iIntros "[#other #ctx] fb". unfold full_bor.
      iDestruct "fb" as (sn κ') "[#Incl [#slice OwnBor]]".
      
      iInv "other" as (outlives) "[£ [>Delayed O]]" "Hclose".
      
      iDestruct (guards_open (True)%I _ (↑Nllft ∖ ↑NllftO) (↑Nmain) with "ctx []") as "J". { solve_ndisj. } { done. }
      iMod "J" as "[J back]". iDestruct "J" as (sa sd blocked) "[State [Alive [OuInv Blo]]]".
      iMod (make_everything_alive (set_map LtAtomSwell κ ∪ set_map LtAtomSwell κ') with "State Alive OuInv Delayed") as (sa') "[%Hsa [State [Alive [OuInv Delayed]]]]". { solve_ndisj. }
      
      iDestruct (outer_get_dead with "Delayed OuInv") as "#>%Hdd".
      
      destruct (decide (set_map LtAtomSwell κ ⊆ sa')) as [Hksa'|Hksa'].
      { 
      destruct (decide (set_map LtAtomSwell κ' ⊆ sa')) as [Hk'sa'|Hk'sa'].
      { 
        iMod (augment_outlives _ _ _ _ (set_map LtAtomSwell κ) (set_map LtAtomSwell κ') with "[Incl] Delayed O OuInv State") as (outlives') "[%Ho' [Delayed [O [OuInv State]]]]". { set_solver. } { set_solver. } { solve_ndisj. }
        { unfold llft_incl. unseal. unfold llft_alive_def'. do 2 rewrite big_sepS_set_map. iFrame "Incl". }
        iDestruct "O" as "[>Ostate Oguards]".

        iClear "other". iClear "ctx".

        iDestruct "slice" as (P') "[PEquiv slice]".
        iDestruct (outer_unborrow_atomic llft_name o_name d_name sa' sd blocked outlives' sn (set_map LtAtomSwell κ) (set_map LtAtomSwell κ') {[default_dead]} P' with "[Delayed OuInv OwnBor Ostate]") as "X"; trivial. { set_solver. } { iFrame. iFrame "slice". }
        iMod (fupd_mask_subseteq (↑Nbox)) as "Upd". { solve_ndisj. }

        iMod "X" as "[P X]". iModIntro. iLeft.
        iSplitL "P". { iApply "PEquiv". iFrame. }
        iIntros (Q). iDestruct ("X" $! Q) as "X".
        iIntros "Y Y2". iDestruct ("X" with "[Y Y2]") as "X". { iFrame "Y2".
            iNext. iIntros "A".
            rewrite dead_def_set_map.
            iMod ("Y" with "A") as "Y". iModIntro. iApply "PEquiv". iFrame.
        }

        iMod "X" as (sn2) "[Delayed [OuInv [Ostate [OwnBor #slice2]]]]".
        iMod "Upd".

        iMod ("back" with "[State Alive OuInv Blo]"). {
          iExists sa'. iExists sd. iExists blocked. iFrame "State".
          iFrame "Alive". iFrame "OuInv". unfold llft_alive_def. { iFrame. } 
        }
        iMod ("Hclose" with "[Delayed Ostate Oguards £]"). { iNext. iExists outlives'. iFrame. }
        iModIntro. iFrame. iFrame "#".
        iModIntro. iModIntro. iSplit; iIntros; done.
      }
      {
        assert (∃ x , x ∈ (set_map LtAtomSwell κ') ∩ sd) as Hex_x. { apply set_choose_L. set_solver. }
        destruct Hex_x as [x Hex].
        iDestruct (LtState_entails_Dead llft_name x sa' sd with "State") as "#Deadx". { set_solver. }

        iMod ("back" with "[State Alive OuInv Blo]"). { iExists sa'. iExists sd. iExists blocked. iFrame. }
        iMod ("Hclose" with "[Delayed O £]"). { iNext. iExists outlives. iFrame. }
        
        iMod (llftl_incl_dead_implies_dead _ κ κ' with "[] Incl [Deadx]") as "HdeadkUpd". { solve_ndisj. } { iFrame "#". unseal. iFrame "#". } { unseal. rewrite dead_def_set_map. iFrame "#". iPureIntro. set_solver. }
        iDestruct "HdeadkUpd" as "#Hdeadk".
        
        iMod (fupd_mask_subseteq ∅) as "Upd". { solve_ndisj. }
        iModIntro. iRight. iFrame "Upd". unseal. iFrame "Hdeadk".
      }
      }
      {
        assert (∃ x , x ∈ (set_map LtAtomSwell κ) ∩ sd) as Hex_x. { apply set_choose_L. set_solver. }
        destruct Hex_x as [x Hex].
        iDestruct (LtState_entails_Dead llft_name x sa' sd with "State") as "#Deadx". { set_solver. }

        iMod ("back" with "[State Alive OuInv Blo]"). { iExists sa'. iExists sd. iExists blocked. iFrame. }
        iMod ("Hclose" with "[Delayed O £]"). { iNext. iExists outlives. iFrame. }
        
        iMod (fupd_mask_subseteq ∅) as "Upd". { solve_ndisj. }
        iModIntro. iRight. rewrite dead_def_set_map. iFrame "Upd". iExists x. iFrame "Deadx". iPureIntro. set_solver.
      }
  Qed.
  
  (* begin hide *)
  Local Lemma llftl_bor_idx_acc_maybe_swell E P κ idx :
      ↑Nllft ⊆ E →
      llft_ctx -∗ idx_bor_def' κ idx P -∗ idx_bor_tok idx -∗ llft_alive_def' κ -∗ |={E}=> (▷ P) ∗
          (▷ P ={↑Nllft}=∗ idx_bor_tok idx ∗ llft_alive_def' κ).
  Proof.
    unseal_bor. intros Hmask.
    destruct idx as [sn κ'].
    iIntros "#ctx [#Incl X] OwnBor alive". iDestruct "X" as (P') "[#HIff #slice]".
    iMod (llftl_idx_acc_fwd E κ (sn, κ') P with "[] [OwnBor alive]") as "[P OwnBor]".
      { trivial. } { unfold idx_bor_def'. iFrame "#". } { iFrame. }
    iModIntro. iFrame "P". iIntros "P".
    iMod (llftl_idx_acc_back_at_same_idx κ (sn, κ') P with "[] [OwnBor P]") as "[tok alive]".
      { iFrame "#".  } { iFrame. }
    iModIntro. iFrame.
  Qed.
  (* end hide *)
  
  Lemma llftl_bor_idx_acc E P κ idx :
      ↑Nllft ⊆ E →
      llft_ctx -∗ &{κ, idx} P -∗ idx_bor_tok idx -∗ @[κ] -∗ |={E}=> (▷ P) ∗
          (▷ P ={↑Nllft}=∗ idx_bor_tok idx ∗ @[κ]).
  Proof.
    iIntros (Hmask) "ctx".
    iDestruct (llftl_bor_idx_acc_maybe_swell E P (set_map LtAtomSwell κ) idx Hmask with "ctx") as "A".
    unseal_bor. unfold llft_incl, idx_bor_def', llft_alive_def'. destruct idx. 
    unseal. rewrite big_sepS_set_map. iFrame "A".
  Qed.
  
  (* begin hide *)
  Local Lemma llftl_borrow_fwd E P (κ: gset nat) :
      ↑Nllft ⊆ E →
      llft_ctx -∗ ▷ P -∗ |={E}=> ∃ sn1 sn2 ,
          slice Nbox sn1 P
          ∗ slice Nbox sn2 P
          ∗ OwnBorState llft_name sn1 (Borrow (set_map LtAtomSwell κ : gset lt_atom) {[default_dead]})
          ∗ OwnBorState llft_name sn2 (Borrow ∅ (set_map LtAtomSwell κ : gset lt_atom)).
  Proof.
      unseal. intros Hmask.
      iIntros "[#other #ctx] P".
      
      iInv "other" as (outlives) "[£ [>Delayed O]]" "Hclose".
      iDestruct (guards_open (True)%I _ (E ∖ ↑NllftO) (↑Nmain) with "ctx []") as "J". { solve_ndisj. } { done. }
      iMod "J" as "[J back]". iDestruct "J" as (sa sd blocked) "[State [Alive [OuInv Blo]]]".
      iMod (make_everything_alive (set_map LtAtomSwell κ) with "State Alive OuInv Delayed") as (sa') "[%Hsa' [State [Alive [OuInv Delayed]]]]". { solve_ndisj. }
      
      iDestruct (outer_borrow_create llft_name o_name d_name sa' sd blocked (set_map LtAtomSwell κ) P with "[Delayed OuInv State P]") as "X"; trivial. { apply swell_set_set_map. } { iFrame. }
      iMod (fupd_mask_mono with "X") as "[Delayed X]". { solve_ndisj. }
      iDestruct "X" as (sn1 sn2) "[OuInv [State [OwnBor1 [OwnBor2 [#slice1 #slice2]]]]]".
      
      iMod ("back" with "[State Alive OuInv Blo]"). { iExists sa'. iExists sd. iExists blocked. iFrame. }
      iMod ("Hclose" with "[Delayed O £]"). { iNext. iExists outlives. iFrame. }
      iModIntro. iExists sn1. iExists sn2. iFrame. iFrame "#".
  Qed.
  
  Local Lemma llftl_borrow_rev P (κ: gset nat) sn :
      llft_ctx -∗ slice Nbox sn P -∗ OwnBorState llft_name sn (Borrow ∅ (set_map LtAtomSwell κ)) -∗ [†κ] -∗
        |={↑Nllft}=> ▷ P.
  Proof.
      unseal.
      iIntros "[#other #ctx] P OwnBor #Dead".
      
      iInv "other" as (outlives) "[£ [>Delayed O]]" "Hclose".
      iDestruct (guards_open (True)%I _ (↑Nllft ∖ ↑NllftO) (↑Nmain) with "ctx []") as "J". { solve_ndisj. } { done. }
      iMod "J" as "[J back]". iDestruct "J" as (sa sd blocked) "[State [Alive [OuInv Blo]]]".
      iMod (make_everything_alive (set_map LtAtomSwell κ) with "State Alive OuInv Delayed") as (sa') "[%Hsa' [State [Alive [OuInv Delayed]]]]". { solve_ndisj. }
      
      iDestruct "Dead" as (k) "[%Hkdead Deadkin]".
      iAssert (⌜ LtAtomSwell k ∈ sd ⌝)%I as "%Hksd". { iApply (lt_state_dead llft_name (LtAtomSwell k) sa' sd). iSplitL; iFrame. iFrame "#". }
      
      iDestruct "O" as "[>Ostate #Oguards]".
      
      iDestruct (outer_unborrow_start llft_name o_name d_name sa' sd blocked outlives sn ∅ ∅ (set_map LtAtomSwell κ) P with "[Delayed OuInv P Ostate OwnBor]") as "X"; trivial. { set_solver. } { set_solver. } { set_solver. } { set_solver. } { intros k0. set_solver. } { iFrame "OuInv". iFrame. }
      iMod (fupd_mask_mono with "X") as "[Delayed [OuInv [Ostate [OwnBor P]]]]". { solve_ndisj. }
      
      iMod ("back" with "[State Alive OuInv Blo]"). { iExists sa'. iExists sd. iExists blocked. replace (blocked ∪ ∅) with blocked by set_solver. iFrame "OuInv". iFrame. }
      iMod ("Hclose" with "[Delayed Ostate £]"). { iNext. iExists outlives. iFrame. iFrame "Oguards". }
      iModIntro. iFrame "P".
  Qed.
    
  Local Lemma llftl_weaken E sn (κ κ' : gset nat) P :
      ↑Nllft ⊆ E →
      llft_ctx -∗ OwnBorState llft_name sn (Borrow (set_map LtAtomSwell κ) {[default_dead]}) -∗ slice Nbox sn P ={E}=∗
          ∃ sn' , OwnBorState llft_name sn' (Borrow (set_map LtAtomSwell κ ∪ set_map LtAtomSwell κ') {[default_dead]}) ∗ slice Nbox sn' P.
  Proof.
    unseal. intros Hmask. iIntros "[#other #ctx] OwnBor #slice". unfold full_bor.
    
    iInv "other" as (outlives) "[£ [>Delayed O]]" "Hclose".
    iDestruct (guards_open (True)%I _ (E ∖ ↑NllftO) (↑Nmain) with "ctx []") as "J". { solve_ndisj. } { done. }
    iMod "J" as "[J back]". iDestruct "J" as (sa sd blocked) "[State [Alive [OuInv Blo]]]".
    iMod (make_everything_alive (set_map LtAtomSwell κ') with "State Alive OuInv Delayed") as (sa') "[%Hsa [State [Alive [OuInv Delayed]]]]". { solve_ndisj. }
    
    iDestruct (outer_reborrow llft_name o_name d_name sa' sd blocked P sn (set_map LtAtomSwell κ) (set_map LtAtomSwell κ') with "[Delayed OuInv OwnBor slice]") as "X".
    { apply swell_set_set_map. }
    { trivial. } { iFrame. iFrame "slice". }
    iMod (fupd_mask_mono with "X") as (sn1 sn2) "[Delayed [OuInv [OwnBor1 [OwnBor2 [#slice1 #slice2]]]]]". { solve_ndisj. }

    iMod ("back" with "[State Alive OuInv Blo]"). { iExists sa'. iExists sd. iExists blocked. iFrame. }
    iMod ("Hclose" with "[Delayed O £]"). { iNext. iExists outlives. iFrame. }
    iModIntro.
    iExists sn1. iFrame "OwnBor1". iFrame "slice1".
  Qed.
  (* end hide *)
  
  Lemma llftl_borrow E κ P :
      ↑Nllft ⊆ E →
      llft_ctx -∗ ▷ P -∗ |={E}=> &{κ} P ∗ ([†κ] ={↑Nllft}=∗ ▷ P).
  Proof.
    unseal_bor. intros Hmask. iIntros "#ctx P".
    iMod (llftl_borrow_fwd E P κ with "ctx P") as (sn1 sn2) "[#slice1 [#slice2 [OwnBor1 OwnBor2]]]". { trivial. }
    iModIntro. unfold full_bor. iSplitL "OwnBor1". { iExists sn1. iExists κ. iFrame. iFrame "slice1". iSplit. { iApply guards_refl. } iModIntro. iModIntro. iSplit; iIntros; done. }
    iIntros "#kdead". iDestruct (llftl_borrow_rev P κ sn2 with "ctx slice2 OwnBor2 kdead") as "X". iFrame "X".
  Qed.
  
  Lemma llftl_sep_split E P Q κ :
      ↑Nllft ⊆ E →
      llft_ctx -∗ &{κ} (P ∗ Q) ={E}=∗ &{κ} P ∗ &{κ} Q.
  Proof.
      unseal_bor. unseal. intros Hmask. iIntros "[#other #ctx] fbPQ". unfold full_bor.
      iDestruct "fbPQ" as (sn κ') "[#incl [#slice OwnBor]]".
      
      iInv "other" as (outlives) "[£ [>Delayed O]]" "Hclose".
      iDestruct (guards_open (True)%I _ (E ∖ ↑NllftO) (↑Nmain) with "ctx []") as "J". { solve_ndisj. } { done. }
      iMod "J" as "[J back]". iDestruct "J" as (sa sd blocked) "[State [Alive [OuInv Blo]]]".
      
      iDestruct "slice" as (PQ) "[PQEquiv slice]".
      iDestruct (outer_iff llft_name o_name d_name sa sd blocked sn (set_map LtAtomSwell κ') {[default_dead]} PQ (P ∗ Q)
        with "[Delayed OuInv OwnBor slice]") as "X". { iFrame. iFrame "slice". iFrame "PQEquiv". }
      iMod (fupd_mask_mono with "X") as (sn0) "[Delayed [OuInv [OwnBor #slice0]]]". { solve_ndisj. }
      
      iDestruct (outer_split llft_name o_name d_name sa sd blocked sn0 (set_map LtAtomSwell κ') {[default_dead]} P Q
        with "[Delayed OuInv OwnBor slice]") as "X". { iFrame. iFrame "slice0". }
      iMod (fupd_mask_mono with "X") as (sn1 sn2) "[Delayed [OuInv [OwnBor1 [OwnBor2 [#slice1 #slice2]]]]]". { solve_ndisj. }
      
      iMod ("back" with "[State Alive OuInv Blo]"). { iExists sa. iExists sd. iExists blocked. iFrame. }
      iMod ("Hclose" with "[Delayed O £]"). { iNext. iExists outlives. iFrame. }
      iModIntro.
      
      iSplitL "OwnBor1". { iExists sn1. iExists κ'. iFrame. iFrame "#".
        iModIntro. iModIntro. iSplit; iIntros; done.
      }
      { iExists sn2. iExists κ'. iFrame. iFrame "#".
        iModIntro. iModIntro. iSplit; iIntros; done.
      }
  Qed.
  
  Lemma llftl_sep_join E P Q κ :
      ↑Nllft ⊆ E →
      llft_ctx -∗ &{κ} P -∗ &{κ} Q ={E}=∗ &{κ} (P ∗ Q).
  Proof.
      unseal_bor. unseal. intros Hmask. iIntros "[#other #ctx] fbP fbQ". unfold full_bor.
      iDestruct "fbP" as (sn1 κ1) "[#incl1 [#slice1 OwnBor1]]".
      iDestruct "fbQ" as (sn2 κ2) "[#incl2 [#slice2 OwnBor2]]".
      
      iDestruct "slice1" as (P') "[PEquiv slice1]".
      iDestruct "slice2" as (Q') "[QEquiv slice2]".
      
      iMod (llftl_weaken E sn1 κ1 κ2 with "[] OwnBor1 slice1") as (sn1') "[OwnBor1 #slice1']". { trivial. } { unseal. iFrame "#". }
      iMod (llftl_weaken E sn2 κ2 κ1 with "[] OwnBor2 slice2") as (sn2') "[OwnBor2 #slice2']". { trivial. } { unseal. iFrame "#". }
      replace (κ2 ∪ κ1) with (κ1 ∪ κ2) by set_solver.
      
      iInv "other" as (outlives) "[£ [>Delayed O]]" "Hclose".
      iDestruct (guards_open (True)%I _ (E ∖ ↑NllftO) (↑Nmain) with "ctx []") as "J". { solve_ndisj. } { done. }
      iMod "J" as "[J back]". iDestruct "J" as (sa sd blocked) "[State [Alive [OuInv Blo]]]".
      iMod (make_everything_alive ({[default_dead]}) with "State Alive OuInv Delayed") as (sa') "[%Hsa [State [Alive [OuInv Delayed]]]]". { solve_ndisj. }
      
      iDestruct (outer_join llft_name o_name d_name sa' sd blocked sn1' sn2' (set_map LtAtomSwell κ1 ∪ set_map LtAtomSwell κ2) {[default_dead]} P' Q'
        with "[Delayed OuInv OwnBor1 OwnBor2]") as "X". { apply swell_set_default_dead. } { set_solver. } { iFrame. iFrame "#".
            replace (set_map LtAtomSwell κ1 ∪ set_map LtAtomSwell κ2)
              with ((set_map LtAtomSwell κ2 : gset lt_atom) ∪ set_map LtAtomSwell κ1) by set_solver. iFrame.
        }
      iMod (fupd_mask_mono with "X") as (sn) "[Delayed [OuInv [OwnBor #slice]]]". { solve_ndisj. }
      
      iMod ("back" with "[State Alive OuInv Blo]"). { iExists sa'. iExists sd. iExists blocked. iFrame. }
      iMod ("Hclose" with "[Delayed O £]"). { iNext. iExists outlives. iFrame. }
      iModIntro.
      iExists sn. iExists (κ1 ∪ κ2). rewrite set_map_inter. iFrame. iFrame "#".
      iSplit.
      { iApply llftl_incl_glb; iFrame "#". }
      iModIntro. iModIntro. iSplit; iIntros "[P Q]".
      - iSplitL "P". { iApply "PEquiv". iFrame. } { iApply "QEquiv". iFrame. }
      - iSplitL "P". { iApply "PEquiv". iFrame. } { iApply "QEquiv". iFrame. }
  Qed.
  
  Lemma llftl_idx_bor_unnest E κ κ' idx P :
      ↑Nllft ⊆ E →
      llft_ctx -∗ &{κ, idx} P -∗ &{κ'} (idx_bor_tok idx) -∗ |={E}=> &{κ ⊓ κ'} P.
  Proof.
      unseal_bor. unseal. intros Hmask. unfold idx_bor. destruct idx as [sn κ2]. unfold full_bor.
      iIntros "[#other #ctx] [#incl #slice] fb".
      iDestruct "fb" as (sn' κ2') "[#incl2 [#slice2 OwnBor2]]".
      
      iInv "other" as (outlives) "[£ [>Delayed O]]" "Hclose".
      iDestruct (guards_open (True)%I _ (E ∖ ↑NllftO) (↑Nmain) with "ctx []") as "J". { solve_ndisj. } { done. }
      iMod "J" as "[J back]". iDestruct "J" as (sa sd blocked) "[State [Alive [OuInv Blo]]]".
      
      iDestruct "slice" as (P') "[PEquiv slice]".
      iDestruct "slice2" as (Pibt) "[PibtEquiv slice2]".
      
      iDestruct (outer_iff llft_name o_name d_name sa sd blocked sn' (set_map LtAtomSwell κ2') {[default_dead]} Pibt (idx_bor_tok (sn, κ2))
        with "[Delayed OuInv OwnBor2 slice2]") as "X". { iFrame. iFrame "slice2". iFrame "PibtEquiv". }
      iMod (fupd_mask_mono with "X") as (sn0) "[Delayed [OuInv [OwnBor2 #slice0]]]". { solve_ndisj. }
      
      iDestruct (outer_unnest llft_name o_name d_name sa sd blocked sn sn0 (set_map LtAtomSwell κ2) (set_map LtAtomSwell κ2') P' with "[Delayed OuInv OwnBor2]") as "X"; trivial. { iFrame. iFrame "#". }
      iMod (fupd_mask_mono with "X") as (sn2) "[Delayed [OuInv [OwnBor #slice3]]]". { solve_ndisj. }
      
      iMod ("back" with "[State Alive OuInv Blo]"). { iExists sa. iExists sd. iExists blocked. replace (blocked ∪ ∅) with blocked by set_solver. iFrame "OuInv". iFrame. }
      iMod ("Hclose" with "[Delayed O £]"). { iNext. iExists outlives. iFrame. }
      iModIntro. iExists sn2. iExists (κ2 ∪ κ2'). 
      iFrame "#". rewrite set_map_inter. iFrame. iApply llftl_incl_glb.
      - iApply llftl_incl_weaken_lhs_l. iFrame "incl".
      - iApply llftl_incl_weaken_lhs_r. iFrame "incl2".
  Qed.
  
  Lemma llftl_bor_fake E κ P :
    ↑Nllft ⊆ E →
    llft_ctx -∗ [†κ] ={E}=∗ &{κ} P.
  Proof. 
      unseal_bor. unseal. unfold full_bor.
      intros Hmask. iIntros "[#other #ctx] #dead".
      
      iInv "other" as (outlives) "[£ [>Delayed O]]" "Hclose".
      iDestruct (guards_open (True)%I _ (E ∖ ↑NllftO) (↑Nmain) with "ctx []") as "J". { solve_ndisj. } { done. }
      iMod "J" as "[J back]". iDestruct "J" as (sa sd blocked) "[State [Alive [OuInv Blo]]]".
      iDestruct "dead" as (k) "[%HkK deadk]".
      iAssert (⌜LtAtomSwell k ∈ sd⌝)%I as "%Hksd". { iApply lt_state_dead. iSplit. { iFrame "State". } iFrame "deadk". }
      iDestruct (outer_fake llft_name o_name d_name sa sd blocked (set_map LtAtomSwell κ) {[default_dead]} P with "[Delayed OuInv]") as "X". { set_solver. } { iFrame. }
      iMod (fupd_mask_mono with "X") as (sn) "[Delayed [OuInv [OwnBor #slice]]]". { solve_ndisj. }
      iMod ("back" with "[State Alive OuInv Blo]"). { iExists sa. iExists sd. iExists blocked. iFrame "OuInv". iFrame. }
      iMod ("Hclose" with "[Delayed O £]"). { iNext. iExists outlives. iFrame. }
      iModIntro. iExists sn. iExists κ. iFrame. iFrame "#". iSplit. { iApply guards_refl. }
      iModIntro. iModIntro. iSplit; iIntros; done.
  Qed.
  
  (** Indexed borrows and guards *)
    
  (* begin hide *)
  Local Lemma exists_combine X Y (R : X → Y → iProp Σ) :
      (∃ (x : X) (y : Y), R x y) ⊣⊢ (∃ (xy : (X * Y)), R (fst xy) (snd xy)).
  Proof.
      iSplit.
        - iIntros "A". iDestruct "A" as (x y) "R". iExists (x, y). done.
        - iIntros "A". iDestruct "A" as (xy) "R". iExists (xy.1). iExists (xy.2). done.
  Qed.
     
  Local Lemma guards_strengthen_exists3 X Y Z (P Q : iProp Σ) (S R : X → Y → Z → iProp Σ) F n
    (pr_impl_s: (∀ x y z, Q ∧ R x y z ⊢ S x y z))
    (pers: ∀ x y z, Persistent (S x y z))
    :
      (P &&{F; n}&&> Q) -∗
      (P &&{F; n}&&> ((∃ (x: X) (y: Y) (z: Z), R x y z))) -∗
      (P &&{F; n}&&> (∃ (x: X) (y: Y) (z: Z), R x y z ∗ S x y z))
    .
  Proof.
    setoid_rewrite exists_combine.
    setoid_rewrite exists_combine.
    apply guards_strengthen_exists.
    - intros x. apply pr_impl_s.
    - intros x. apply pers.
  Qed.
  
  Local Lemma exists_commute_helper X Y Z (P : X → Y → Z → iProp Σ) (Q : iProp Σ)
    : (∃ x y z , P x y z ∗ Q) ⊣⊢ ((∃ x y z , P x y z) ∗ Q).
  Proof.
    iSplit.
    - iIntros "A". iDestruct "A" as (x y z) "[P Q]". iFrame.
    - iIntros "[A Q]". iDestruct "A" as (x y z) "P". iFrame.
  Qed.
  
  Local Lemma exists_commute_helper2 X Y Z W (P R : X → Y → Z → iProp Σ) (Q : W → iProp Σ)
    {inh: Inhabited W}
    :
      (∃ x y z , (P x y z ∗ ▷ ∃ w : W, Q w) ∗ R x y z)%I
      ⊣⊢
      ∃ w , (∃ x y z , P x y z ∗ R x y z) ∗ ▷ Q w.
  Proof.
      iSplit.
      - iIntros "A". iDestruct "A" as (x y z) "[[P W] R]".
        rewrite bi.later_exist. iDestruct "W" as (w) "Q". iFrame.
      - iIntros "A". iDestruct "A" as (w) "[A B]". iDestruct "A" as (x y z) "[P R]". iFrame.
  Qed.
  
  Local Lemma guard_helper2 sn κ' b sa sd blocked :
      set_map LtAtomSwell κ' ⊆ sa →
      idx_bor_tok (sn, κ')
      ∧ inner_inv llft_name o_name sa sd blocked
          ∗ box_own_auth sn (excl_auth.excl_auth_auth b)
      ⊢ ⌜b=true⌝.
  Proof. 
    intros Hsub. iIntros "A". unfold inner_inv.
    rewrite bi.sep_exist_r.
    setoid_rewrite bi.sep_exist_r. setoid_rewrite bi.sep_exist_r. setoid_rewrite bi.sep_exist_r. 
    rewrite bi.and_exist_l.
    setoid_rewrite bi.and_exist_l. setoid_rewrite bi.and_exist_l. setoid_rewrite bi.and_exist_l.
    iDestruct "A" as (mbs mprops Ptotal outlives) "A".
    iAssert (⌜sa ## sd ∧ default_dead ∈ sd⌝)%I as "[%Hdisj %Hdd]". {
      iDestruct "A" as "[_ [(? & ? & ? & ? & %Hall & ?) _]]".
      unfold lifetime_internals.inv.map_wf in Hall. iPureIntro. intuition.
    }
    iDestruct (agree_bor_state_borrow_lts_and llft_name sn mbs sd (set_map LtAtomSwell κ') {[default_dead]} with "[A]") as (de') "%Hde'". { set_solver. }
    { iSplit.
      - iDestruct "A" as "[A _]". iFrame "A".
      - iDestruct "A" as "[_ ((? & ? & ?) & ?)]". iFrame.
    }
    destruct Hde' as [Hmbssn Hx].
    iDestruct "A" as "[_ ((_ & _ & Box & _) & BoxOwnAuth)]".
    assert (boxmap sa sd mbs !! sn = Some true) as Htrue. {
      unfold boxmap. rewrite lookup_fmap. rewrite Hmbssn. simpl.
      f_equiv. rewrite bool_decide_eq_true. set_solver.
    }
    iApply (box_own_auth_agree sn b true). iFrame "BoxOwnAuth".
    unfold box, tc_opaque. iDestruct "Box" as (Φ) "[_ A]". 
    rewrite (big_sepM_delete _ _ sn); last by apply Htrue.
    iDestruct "A" as "[[A B] _]". iFrame "A".
  Qed.
  
  Local Lemma guard_helper1 sn κ' b sa sd blocked :
      idx_bor_tok (sn, κ')
        ∧ outer_inv llft_name o_name d_name sa sd blocked
              ∗ LtState llft_name sa sd
              ∗ ⌜set_map LtAtomSwell κ' ⊆ sa⌝
              ∗ box_own_auth sn (excl_auth.excl_auth_auth b)
      ⊢ ⌜b=true⌝.
  Proof.
    unfold outer_inv.
    iIntros "A".
    iAssert (⌜set_map LtAtomSwell κ' ⊆ sa⌝)%I as "%Hsub". { iDestruct "A" as "[_ (? & ? & ? & ?)]". iFrame. }
    rewrite bi.sep_exist_r. 
    rewrite bi.and_exist_l.
    iDestruct "A" as (opt_k) "A". destruct opt_k as [p|].
    - destruct p as [k alive'].
      iApply (guard_helper2 sn κ' b (sa ∪ {[k]}) (sd ∖ {[k]}) blocked). { set_solver. }
      iSplit.
        + iDestruct "A" as "[A _]". iFrame.
        + iDestruct "A" as "[_ ((? & ? & ?) & (? & ? & ?))]". iFrame.
    - iApply (guard_helper2 sn κ' b sa sd blocked). { trivial. }
      iSplit.
        + iDestruct "A" as "[A _]". iFrame.
        + iDestruct "A" as "[_ ((? & ?) & ? & ? & ?)]". iFrame.
  Qed.
  (* end hide *)
  
  Lemma llftl_idx_bor_guard' κ i P G n :
    llft_ctx -∗ &{ κ, i } P -∗
      (G &&{↑NllftG; n}&&> @[κ]) -∗
      (G &&{↑NllftG; n}&&> idx_bor_tok i) -∗
      G &&{↑NllftG; n}&&> (@[κ] ∗ ▷ P).
  Proof.
    unseal_bor. unseal. destruct i as [sn κ']. 
    iIntros "[_ #ctxG] [#Incl #Slice] #Galive #Gtok".
    iDestruct "Slice" as (P') "[PEquiv Slice]".
    unfold slice. iDestruct "Slice" as "[#BoxOwnProp #SliceGuard]".
    iDestruct (guards_true_sep_mask_disjoint with "ctxG SliceGuard") as "G". { solve_ndisj. }
    iClear "ctxG". iClear "SliceGuard".
    
    leaf_hyp "G" mask to (↑NllftG) as "G1". { solve_ndisj. } iClear "G".
    
    leaf_hyp "G1" lhs to G as "G2". { iApply guards_true. }
    iClear "G1".
    
    setoid_rewrite <- exists_commute_helper.
    
    iDestruct (llftl_incl_glb _ _ κ with "Incl []") as "Incl2". { iApply guards_refl. }
    leaf_hyp "G2" laters to n as "G2n". { lia. }
    
    iDestruct (guards_strengthen_exists3 (gset lt_atom) (gset lt_atom) (gset lt_atom)
        _ (@[κ' ⊓ κ])%I (λ sa sd blocked, ⌜ set_map LtAtomSwell κ ∪ set_map LtAtomSwell κ' ⊆ sa ⌝)%I _ _ n with "[] G2n") as "G3".
      { intros sa sd blocked. iIntros "A".
        iAssert (∀ k, ⌜ k ∈ κ ∪ κ' → LtAtomSwell k ∈ sa ⌝)%I with "[A]" as "%J".
        { iIntros (k) "%Hk". iApply (lt_state_alive llft_name (LtAtomSwell k) sa sd). iSplit.
          { iDestruct "A" as "[_ [[A _] _]]". iFrame. }
          { iDestruct "A" as "[A _]". unseal.
            rewrite big_sepS_delete. { iDestruct "A" as "[A _]". iFrame "A". }
            unfold "⊓", llft_intersect. set_solver.
          }
        }
        iPureIntro. intro x.
        rewrite <- set_map_inter. intros Ha. rewrite elem_of_map in Ha. destruct Ha as [x0 [Heq Hin]]. subst x. apply J. trivial.
      }
      {
        iApply (guards_transitive_left with "[] Incl2"). unseal. iApply "Galive".
      }
    iClear "G2".
    
    unfold slice_inv.
    setoid_rewrite exists_commute_helper2. 2: { typeclasses eauto. }
    
    iDestruct (guards_strengthen_exists _ _ _ (λ b, ▷ ⌜b = true⌝)%I with "Gtok G3") as "G4".
    {
      intros b. iIntros "A". iNext.
      rewrite bi.sep_exist_r. setoid_rewrite bi.sep_exist_r. setoid_rewrite bi.sep_exist_r.
      rewrite bi.and_exist_l. setoid_rewrite bi.and_exist_l. setoid_rewrite bi.and_exist_l.
      iDestruct "A" as (sa sd blocked) "A".
      iApply (guard_helper1 sn κ' b sa sd blocked).
      iSplit.
      - iDestruct "A" as "[? _]". iFrame.
      - iDestruct "A" as "[_ ([(? & ? & ? & ?) %Hsub] & ? & ?)]". iFrame.
        iPureIntro. set_solver.
    }
    iClear "G3".
    
    unseal. iApply (guards_transitive_left with "G4 []").
    leaf_by_sep_except0.
    iIntros "A". iDestruct "A" as (x) "[[B [>BoxOwnAuth ITE]] #>%xtrue]".
    subst x.
    iDestruct "B" as (sa sd blocked) "[[LtState [Alive More]] %Sub]".
    
    assert (sa = set_map LtAtomSwell κ ∪ (sa ∖ set_map LtAtomSwell κ)) as Hunion. { apply set_eq. intros x. destruct (decide (x ∈ (set_map LtAtomSwell κ : gset lt_atom))); set_solver. }
    
    unfold llft_alive_def'.
    assert (([∗ set] k ∈ sa, Alive llft_name k) ⊣⊢
        ([∗ set] k ∈ κ, Alive llft_name (LtAtomSwell k)) ∗
        ([∗ set] k ∈ (sa ∖ set_map LtAtomSwell κ), Alive llft_name k))%I as Hsep.
    { rewrite <- big_sepS_set_map.
      rewrite <- big_sepS_union; last by set_solver. setoid_rewrite <- Hunion. trivial. }
    
    setoid_rewrite Hsep.
    iDestruct "Alive" as "[Alive1 Alive2]".
    
    iModIntro. iFrame "Alive1".
    iSplitL "ITE". { iApply "PEquiv". iFrame. }
    iIntros "[Alive1 P]".
    iExists true.
    iSplitL; last by done.
    iFrame "BoxOwnAuth".
    iSplitR "P". {
      iExists sa. iExists sd. iExists blocked.
      setoid_rewrite Hsep.
      iFrame. done.
    }
    iApply "PEquiv". iFrame "P".
  Qed.
  
  Lemma llftl_idx_bor_guard κ i P :
    llft_ctx -∗ &{ κ, i } P -∗ (@[κ] ∗ &{ κ, i } P ∗ idx_bor_tok i) &&{↑NllftG}&&> (@[κ] ∗ ▷ P).
  Proof.
    iIntros "#ctx #idx".
    iApply llftl_idx_bor_guard'.
    - done.
    - iFrame "idx".
    - leaf_by_sep. iIntros "(A & B & C)". iFrame. iIntros. done.
    - leaf_by_sep. iIntros "(A & B & C)". iFrame. iIntros. done.
  Qed.
  
  Lemma llftl_idx_bor_iff κ i P P' : ▷ □ (P ↔ P') -∗ &{κ,i}P -∗ &{κ,i}P'.
  Proof.
    unseal_bor. destruct i as [sn κ']. iIntros "#Eq [#Incl #S]". 
    iDestruct "S" as (P'') "[#Eq' slice]". iFrame "Incl". iExists P''. iFrame "slice".
    iModIntro. iModIntro. iSplit.
    - iIntros. iApply "Eq". iApply "Eq'". iFrame.
    - iIntros. iApply "Eq'". iApply "Eq". iFrame.
  Qed.
  
  (** Derived rules about full borrows (all derived from the above, without using the model) *)
  
  Lemma llftl_bor_shorten κ κ' P :
      κ' ⊑ κ -∗ &{κ} P -∗ &{κ'} P.
  Proof.
      rewrite llftl_bor_idx. rewrite llftl_bor_idx.
      iIntros "#incl fb". iDestruct "fb" as (idx) "[idx tok]".
      iDestruct (llftl_idx_shorten κ κ' with "incl idx") as "idx". iExists idx. iFrame.
  Qed.

  Lemma llftl_reborrow E κ κ' P :
      ↑Nllft ⊆ E →
      llft_ctx -∗ κ' ⊑ κ -∗ &{κ} P -∗ |={E}=> &{κ'} P ∗ ([†κ'] ={↑Nllft}=∗ &{κ} P).
  Proof.
      intros Hmask. iIntros "#ctx #incl fb". rewrite llftl_bor_idx.
      iDestruct "fb" as (idx) "[#idx tok]".
      iMod (llftl_borrow E κ' with "ctx tok") as "[tokbor back]"; trivial.
      iMod (llftl_idx_bor_unnest E κ κ' idx P with "ctx idx tokbor") as "fullbor"; trivial.
      iModIntro. iSplitL "fullbor".
      { iDestruct (llftl_bor_shorten _ κ' with "[] fullbor") as "fullbor".
        { iApply llftl_incl_glb. { iFrame "incl". } iApply guards_refl. } iFrame.
      }
      iIntros "#dead". 
      destruct idx as [sn κ2].
      iMod ("back" with "dead") as ">tok".
      iModIntro. iExists (sn, κ2). iFrame. iFrame "#".
  Qed.
  
  Lemma llftl_bor_freeze `{!Inhabited T} E κ (P : T → iProp Σ):
      ↑Nllft ⊆ E →
      llft_ctx -∗ &{κ} (∃ (x: T) , P x) ={E}=∗ ∃ (x: T), &{κ} (P x).
  Proof.
      intros Hmask. iMod (fupd_mask_subseteq (↑Nllft)) as "Upd". { solve_ndisj. }
      iIntros "#ctx fb".
      iMod (llftl_bor_acc_atomic with "ctx fb") as "[[P back]|[#dead back]]".
      - iDestruct "P" as (x) "P".
        iDestruct ("back" $! (P x)) as "back".
        iDestruct ("back" with "[] P") as "back".
          { iNext. iIntros "[P k]". iModIntro. iExists x. iFrame "P". }
        iMod "back". iMod "Upd".
        iModIntro. iExists x. iFrame "back".
      - iMod "back".
        iMod (llftl_bor_fake _ κ (P (@inhabitant T _)) with "ctx dead"). { solve_ndisj. }
        iMod "Upd". iModIntro. iFrame.
  Qed.
  
  Lemma llftl_bor_pers_from_wand E κ P Q (pers: Persistent Q):
      ↑Nllft ⊆ E →
      llft_ctx -∗ &{κ} P -∗ (P -∗ Q) ={E}=∗ &{κ} P ∗ ((▷ Q) ∨ [†κ]).
  Proof.
      intros Hmask. iMod (fupd_mask_subseteq (↑Nllft)) as "Upd". { solve_ndisj. }
      iIntros "#ctx fb wand".
      iMod (llftl_bor_acc_atomic with "ctx fb") as "[[P back]|[#dead back]]".
      - iDestruct ("wand" with "P") as "#Q".
        iMod ("back" $! (P)%I with "[] P") as "fb".
          { iNext. iIntros "[P2 dead]". iFrame. iModIntro. done. }
        iMod "Upd". iModIntro. iFrame "fb". iLeft. iFrame "Q".
      - iMod "back".
        iMod (llftl_bor_fake _ κ P with "ctx dead"). { solve_ndisj. }
        iMod "Upd". iModIntro. iFrame. iRight. iFrame "dead".
  Qed.
  
  Lemma llftl_bor_pers_from_wand2 E κ P Q R (pers: Persistent Q):
      ↑Nllft ⊆ E →
      llft_ctx -∗ &{κ} P -∗ (R -∗ P -∗ Q) -∗ R ={E}=∗ &{κ} P ∗ ((▷ Q) ∨ [†κ]) ∗ R.
  Proof.
      intros Hmask. iMod (fupd_mask_subseteq (↑Nllft)) as "Upd". { solve_ndisj. }
      iIntros "#ctx fb wand R".
      iMod (llftl_bor_acc_atomic with "ctx fb") as "[[P back]|[#dead back]]".
      - iDestruct ("wand" with "R P") as "#Q".
        iMod ("back" $! (P)%I with "[] P") as "fb".
          { iNext. iIntros "[P2 dead]". iFrame. iModIntro. done. }
        iMod "Upd". iModIntro. iFrame "fb". iFrame "R". iLeft. iFrame "Q".
      - iMod "back".
        iMod (llftl_bor_fake _ κ P with "ctx dead"). { solve_ndisj. }
        iMod "Upd". iModIntro. iFrame. iRight. iFrame "dead".
  Qed.
      
  Lemma llftl_bor_pers E κ P (pers: Persistent P):
      ↑Nllft ⊆ E →
      llft_ctx -∗ &{κ} P ={E}=∗ &{κ} P ∗ ((▷ P) ∨ [†κ]).
  Proof.
      intros Hmask. 
      iIntros "#ctx fb".
      iApply (llftl_bor_pers_from_wand E κ P P pers with "ctx fb []"). { set_solver. }
      iIntros. done.
  Qed.
  
  Lemma llftl_bor_unnest E κ κ' P :
      ↑Nllft ⊆ E →
      llft_ctx -∗ &{κ'} (&{κ} P) -∗ |={E}▷=> &{κ ⊓ κ'} P.
  Proof.
      intros Hmask. iIntros "#ctx fb".
      rewrite (llftl_bor_idx κ).
      
      iMod (llftl_bor_freeze with "ctx fb") as (idx) "fb"; trivial.
      iMod (llftl_sep_split with "ctx fb") as "[fb1 fb2]"; trivial.
      iMod (llftl_bor_pers with "ctx fb1") as "[fb1 [#idxbor|dead]]"; trivial.
      - iModIntro. iNext.
        iMod (llftl_idx_bor_unnest E κ κ' idx P with "ctx idxbor fb2") as "fb3". { trivial. }
        iModIntro. iFrame "fb3".
      - iMod (llftl_bor_fake _ (κ ⊓ κ') P with "ctx [dead]") as "fb3". { solve_ndisj. }
        { rewrite llftl_end_inter. iRight. iFrame. }
        iModIntro. iNext. iModIntro. iFrame. 
  Qed.
  
  Lemma llftl_bor_iff κ P P' : ▷ □ (P ↔ P') -∗ &{κ}P -∗ &{κ}P'.
  Proof.
    rewrite !llftl_bor_idx. iIntros "#HP Hbor".
    iDestruct "Hbor" as (i) "[Hbor Htok]". iExists i. iFrame "Htok".
    iApply llftl_idx_bor_iff; done.
  Qed.
  
  Lemma llftl_bor_simple_atomic P κ :
    llft_ctx -∗ &{κ} P -∗ |={↑Nllft, ∅}=>
        (▷ P ∗ (▷ P ={∅, ↑Nllft}=∗ &{κ} P))
        ∨ ([†κ] ∗ (|={∅, ↑Nllft}=> True)).
  Proof.
    iIntros "ctx bor". iMod (llftl_bor_acc_atomic P κ with "ctx bor") as "[[P back]|[dead back]]".
    - iDestruct ("back" $! (P)) as "back". iModIntro. iLeft. iFrame. iIntros "P".
      iApply "back". { iNext. iIntros "[$ _]". done. } done.
    - iModIntro. iRight. iFrame.
  Qed.
  
  (** Guarded accessors *)

  (* begin hide *)
  (* To use the guarded accessor laws without incurring a later, it is slightly difficult because
  ending a lifetime usually incurs a later. To implement guarded accessor laws without a later,
  we use special lifetime tokens that can't be used for full borrows. *)

  Local Lemma llftl_guarded_tok_to_tmp
    E G κ :
    Timeless G →
    ↑Nllft ⊆ E →
    llft_ctx -∗
    (G &&{↑NllftG}&&> @[κ]) -∗
    G ={E}=∗ ∃ κ' ,
        (llft_alive_def' κ' &&{↑NllftG}&&> @[κ]) ∗
        llft_alive_def' κ' ∗
        □ (llft_alive_def' κ' ={↑Nllft}=∗ llft_dead_def' κ') ∗
        (llft_dead_def' κ' ={↑Nllft}=∗ G)
    .
  Proof.
    intros TimelessG Hmask. iIntros "#ctx #Gk G".
    iMod (llftl_begin_maybe_swell' _ false with "ctx") as (κ1) "A1". { trivial. }
    iDestruct (llftl_borrow_shared_maybe_swell (↑Nllft) ({[ LtAtomNotSwell κ1 ]}) with "G") as "X". { trivial. }
    iMod (fupd_mask_mono with "X") as "[#G1later back]".  { trivial. }
    iDestruct (guards_remove_later_rhs with "G1later") as "G1".
    iDestruct (guards_transitive with "G1 Gk") as "Incl".
    iModIntro. iExists ({[ LtAtomNotSwell κ1 ]}).
    unfold llft_alive_def'. rewrite big_sepS_singleton.
    iFrame. iFrame "#". iSplitR.
    - iModIntro. iIntros "Alive".
      iMod (llftl_end_maybe_swell' _ false with "ctx Alive") as "D". { done. }
      iMod "D".  iModIntro. iExists (LtAtomNotSwell κ1). iFrame. iPureIntro. set_solver.
    - iIntros "A". iMod ("back" with "A") as ">A". done.
  Qed.
  (* end hide *)

  Lemma llftl_bor_idx_acc_guarded
    E G κ idx P :
    Timeless G →
    ↑Nllft ⊆ E →
    llft_ctx -∗
    &{κ, idx} P -∗
    idx_bor_tok idx -∗
    (G &&{↑NllftG}&&> @[κ]) -∗
    G ={E}=∗
        (▷ P) ∗ (▷ P ={↑Nllft}=∗ idx_bor_tok idx ∗ G).
  Proof.
    intros TimelessG Hmask. iIntros "#ctx #bor tok #Gk G".
    iMod (llftl_guarded_tok_to_tmp E G κ TimelessG Hmask with "ctx Gk G") as (κ') "(#Incl & Alive & #Kill & Back)".
    iMod (llftl_bor_idx_acc_maybe_swell E P κ' idx Hmask with "ctx [] tok Alive") as "[P Pback]".
    { unseal_bor. destruct idx as [sn κ2]. unfold idx_bor_def'. iDestruct "bor" as "[B1 $]".
      iApply (guards_transitive with "Incl B1"). }
    iModIntro. iFrame "P". iIntros "P". iMod ("Pback" with "P") as "[tok alive]".
    iMod ("Kill" with "alive") as "X".
    iMod ("Back" with "X") as "G". iModIntro. iFrame.
  Qed.

  Lemma llftl_bor_acc_guarded
    E G κ P :
    Timeless G →
    ↑Nllft ⊆ E →
    llft_ctx -∗
    &{κ} P -∗
    (G &&{↑NllftG}&&> @[κ]) -∗
    G ={E}=∗
        (▷ P) ∗ (∀ Q, ▷ (▷ Q ={↑NllftUsr ∪ ↑NllftUsr2}=∗ ▷ P) ∗ ▷ Q ={↑Nllft}=∗ (&{κ} Q) ∗ G).
  Proof.
    intros TimelessG Hmask. iIntros "#ctx bor #Gk G".
    iMod (llftl_guarded_tok_to_tmp E G κ TimelessG Hmask with "ctx Gk G") as (κ') "(#Incl & Alive & #Kill & Back)".
    iMod (llftl_bor_acc_maybe_swell' E P κ' κ Hmask with "ctx Incl bor Alive") as "[P Pback]".
    iModIntro. iFrame "P". iIntros (Q) "[vs Q]". iMod ("Pback" $! (Q) with "[vs Q]") as "[tok alive]". { iFrame. }
    iMod ("Kill" with "alive") as "X". iMod ("Back" with "X") as "G". iModIntro. iFrame.
  Qed.

  (** Freezing a full borrow into a guard *)

  (** A full borrow can be given up for good in exchange for a (persistent) guard of its
      contents by [@[κ]]: the borrow's index token is itself put under a shared borrow at
      [κ]. Since the contents of an indexed borrow are only available under a later,
      the guard has a step-index of [1]. *)
  Lemma llftl_bor_guard_later E κ P :
    ↑Nllft ⊆ E →
    llft_ctx -∗ &{κ} P ={E}=∗ @[κ] &&{↑NllftG}&&> ▷ P.
  Proof.
    intros Hmask. iIntros "#ctx Bor".
    iDestruct (llftl_bor_idx with "Bor") as (idx) "[#Idx Tok]".
    iMod (llftl_borrow_shared _ κ (idx_bor_tok idx) with "Tok") as "[#Glat _]"; [done|].
    iDestruct (guards_remove_later_rhs with "Glat") as "Gtok".
    iDestruct (llftl_idx_bor_guard' κ idx _ (@[κ])%I with "ctx Idx [] Gtok") as "GBor".
    { iApply guards_refl. }
    iModIntro. iApply (guards_weaken_rhs_sep_r with "GBor").
  Qed.

  Lemma llftl_bor_guard E κ P :
    ↑Nllft ⊆ E →
    llft_ctx -∗ &{κ} P ={E}=∗ @[κ] &&{↑NllftG; 1}&&> P.
  Proof.
    intros Hmask. iIntros "#ctx Bor".
    iMod (llftl_bor_guard_later with "ctx Bor") as "#G"; [done|].
    iModIntro. iApply (guards_later_absorb_1 _ _ _ 0 with "G").
  Qed.

  (** Running a fancy update inside a full borrow, given a guard for [κ]. One later
      credit pays for stripping the later off the borrowed contents. *)
  Lemma llftl_bor_fupd_guarded E M G κ P :
    Timeless G →
    ↑Nllft ⊆ E → M ⊆ E →
    llft_ctx -∗
    (G &&{↑NllftG}&&> @[κ]) -∗
    G -∗ £ 1 -∗ &{κ} (|={M}=> P) ={E}=∗ &{κ} P ∗ G.
  Proof.
    intros TimelessG Hmask HM. iIntros "#ctx #Gk G £ Bor".
    iMod (llftl_bor_acc_guarded with "ctx Bor Gk G") as "[Upd Back]"; [done|].
    iMod (lc_fupd_elim_later with "£ Upd") as "Upd".
    iMod (fupd_mask_mono with "Upd") as "P"; [done|].
    iDestruct ("Back" $! P with "[P]") as "Close".
    { iSplitR; [|by iNext]. iIntros "!> P !> !>". by iModIntro. }
    iMod (fupd_mask_mono with "Close") as "[$ $]"; done.
  Qed.
End LlftLogic.

(** Initializing the [llft_ctx] *)

Lemma llft_alloc {Σ: gFunctors} `{!llft_logicGpreS Σ} `{!invGS Σ} E
  : £1 ⊢ |={E}=> ∃ _ : llft_logicGS Σ, llft_ctx.
Proof.
  iIntros "£".
  iMod lt_alloc as (γ) "[J [Ab Modulo]]".
  iMod (outlives_alloc ∅) as (γo) "[O1 O2]".
  iMod (delayed_alloc None) as (γd) "[D1 D2]".
  iMod (new_lt γ default_dead ∅ ∅ with "J") as "J". { set_solver. } { set_solver. }
  iMod (kill_lt γ default_dead with "J") as "[J dd]".
  iMod (modulo_dead_new γ default_dead ∅ with "[dd Modulo]") as "Modulo". { iFrame. }
  iMod (guards_alloc_with_inv (Nmain) E
      (∃ sa sd blocked : gset lt_atom, LtState γ sa sd ∗ ([∗ set] k ∈ sa , Alive γ k)
          ∗ (outer_inv γ γo γd sa sd blocked)
          ∗ ([∗ set] k ∈ blocked , Alive γ k)
      ) with "[J O1 D1 Ab Modulo]") as "[_ K]".
   { iModIntro. iExists ∅. iExists {[default_dead]}. iExists ∅.
     replace ((∅ ∪ {[default_dead]}) ∖ {[default_dead]}) with (∅ : gset lt_atom); last by set_solver.
     replace (∅ ∪ {[default_dead]}) with ({[default_dead]} : gset lt_atom); last by set_solver.
     iFrame "J".
     rewrite big_sepS_empty.
     iSplitR; first by done. iSplitL; last by done.
     iExists None. iFrame "D1". iExists ∅. iExists ∅. iExists True%I. iExists ∅.
     iFrame "Ab". iFrame "O1". iFrame "Modulo".
     iSplitL. { unfold boxmap. rewrite fmap_empty. iApply box_alloc. }
     iSplitL. { rewrite future_vs_def. iIntros (k) "[%Hk _]". set_solver. }
     iSplitL. {
      iPureIntro. split; trivial. split.
      - unfold lifetime_internals.inv.map_wf.
        split. { set_solver. }
        split. { set_solver. }
        split. { set_solver. }
        split. { intros sn bs Hl. rewrite lookup_empty in Hl. discriminate. }
        split. { intros sn1 bs1 sn2 bs2 Hne Hl. rewrite lookup_empty in Hl. discriminate. }
        intros o Ho. set_solver.
      - intros o Ho. set_solver.
     }
     rewrite big_sepM_empty. done.
  }
  iMod (inv_alloc (NllftO) _ (∃ (outlives : outlives_set), £1 ∗ Delayed γd None ∗ Outlives γo outlives
        ∗ ∀ (o : gset lt_atom * lt_atom), ⌜o ∈ outlives⌝ -∗ (([∗ set] k ∈ o.1, Alive γ k) &&{↑NllftG}&&> Alive γ o.2))%I with "[O2 D2 £]") as "Inv".
  {
    iNext. iExists ∅. iFrame "O2". iFrame "D2". iFrame "£". iIntros (o) "%Ho". set_solver.
  }
  iModIntro.
  iExists (LlftLogicG _ _ γ γo γd).
  rewrite llft_ctx_unseal /llft_ctx_def.
  iSplitL "Inv". { iFrame "Inv". }
  leaf_goal rhs to _; last by iFrame "K".
  leaf_by_sep_except0.
  iIntros "A". iDestruct "A" as (sa sd blocked) "[A [B [C D]]]". iMod "A". iMod "B". iMod "D".
  iModIntro. iSplitL. {
    iExists sa. iExists sd. iExists blocked. iFrame.
  }
  iIntros "A". iDestruct "A" as (sa1 sd1 blocked1) "[A [B [C D]]]".
  iNext. iExists sa1. iExists sd1. iExists blocked1. iFrame.
Qed.

Notation "@[ κ ]" := (llft_alive κ) (format "@[ κ ]") : bi_scope.
Notation "[† κ ]" := (llft_dead κ) (format "[† κ ]") : bi_scope.
Infix "⊑" := llft_incl (at level 70) : bi_scope.
Notation "&{ κ }" := (full_bor κ) (format "&{ κ }") : bi_scope.
Notation "&{ κ , i }" := (idx_bor κ i) (format "&{ κ , i }") : bi_scope.

(** One difference between the Leaf Lifetime Logic and the classic RustBelt lifetime logic
is that our tokens aren't fractional. This might seem limiting, for example, because
rules like [llftl_bor_acc] require relinquishing the entire lifetime token [@[κ]],
whereas in the classic lifetime logic you could instead relinquish an arbitrary fraction of it.

Is it possible to use [llftl_bor_acc] in a more fine-grained way in the Leaf Lifetime Logic?
It is, if you combine it with other guarding capabilities.

For example, here's one thing you could do, demonstrated by [llftl_split_token]:

  1. Use Leaf to split a lifetime token [@[κ]] into two half tokens, [(1/2)@[k]], where:
  
      [(1/2)@[κ] &&{↑NllftG}&&> @[κ]]
  
  2. Create fresh lifetimes κ1 and κ2. Use [llftl_borrow_shared] on these half tokens with
     these fresh lifetimes.
     
      [@[κ1] &&{↑NllftG}&&> (1/2)@[κ]]
      
      [@[κ2] &&{↑NllftG}&&> (1/2)@[κ]]
  
  3. Using transitivity, we can establish [@[κ1] &&{↑NllftG}&&> @[κ]], i.e.,
     [κ1 ⊑ κ]. Likewise, we can get [κ2 ⊑ κ].
  
  Now if we want to use [llftl_bor_acc], we can use the [@[κ1]] and [@[κ2]] tokens in place
  of [@[κ]].
*)

Lemma llftl_split_token {Σ: gFunctors} `{!llft_logicGS Σ} `{!invGS Σ} `{!frac_logicG Σ}
  E κ :
  ↑Nllft ⊆ E →
  llft_ctx -∗
  @[κ] ={E}=∗ ∃ κ1 κ2 ,
      κ1 ⊑ κ ∗
      κ2 ⊑ κ ∗
      @[κ1] ∗
      @[κ2] ∗
      □ (@[ κ1 ] ={↑Nllft}[∅]▷=∗ [† κ1 ]) ∗
      □ (@[ κ2 ] ={↑Nllft}[∅]▷=∗ [† κ2 ]) ∗
      ([†κ1] ∗ [†κ2] ={E}=∗ @[κ])
  .
Proof.
  intros Hmask. iIntros "#ctx aliveK".
  iMod (frac_split_in_half NllftG _ E with "aliveK") as (γ) "[F1 [F2 [#guardHalf #back]]]". { solve_ndisj. }
  iMod (llftl_begin with "ctx") as (κ1) "[A1 #Kill1] ". { trivial. }
  iMod (llftl_begin with "ctx") as (κ2) "[A2 #Kill2]". { trivial. }
  iMod (llftl_borrow_shared E κ1 with "F1") as "[#G1 F1]". { trivial. }
  iMod (llftl_borrow_shared E κ2 with "F2") as "[#G2 F2]". { trivial. }
  iModIntro. iExists κ1. iExists κ2.
  iDestruct (guards_remove_later_rhs with "G1") as "G1'".
  iDestruct (guards_remove_later_rhs with "G2") as "G2'".
  iFrame "A1". iFrame "A2". iFrame "Kill1". iFrame "Kill2".
  iSplitR. {
    leaf_goal rhs to _; last by iFrame "G1'".
    iFrame "guardHalf".
  }
  iSplitR. {
    leaf_goal rhs to _; last by iFrame "G2'".
    iFrame "guardHalf".
  }
  iIntros "[#D1 #D2]".
  iDestruct ("F1" with "D1") as "F1". iMod "F1". iMod "F1".
  iDestruct ("F2" with "D2") as "F2". iMod "F2". iMod "F2".
  iDestruct ("back" with "F1 F2") as "alive".
  iMod (fupd_mask_mono with "alive") as "alive". { solve_ndisj. }
  iModIntro. iFrame "alive".
Qed.
