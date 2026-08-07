Require Import guarding.lib.boxes.
Require Import lrust.lifetime.lifetime_internals.ra.

Require Import stdpp.base.
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

(* This is the invariant part of the lifetime logic that's relevant for *full borrows*
(and indexed borrows).
*)

(* Namespaces: Nllft and NllftG are the masks that are part of the "public" interface.

NllftG has 2 important sub-namespaces, Nmain, which is the main invariant goes,
and Nbox, which is where box stuff goes. We want Nbox to be part of NllftG so we can
guard on stuff that is borrowed.

NlltfO is for the part of the invariant that needs to be _outside_ NllftG.
(See the explanation on outer_inv below.)
*)

Definition Nllft       : namespace := nroot .@ "leaf_lifetime_logic".
Definition NllftG      : namespace := nroot .@ "leaf_lifetime_logic" .@ "guarding".

Definition NllftO      : namespace := nroot .@ "leaf_lifetime_logic" .@ "other".
Definition Nmain       : namespace := NllftG .@ "main".
Definition Nbox        : namespace := NllftG .@ "box".

Definition NllftUsr    : namespace := nroot .@ "leaf_lifetime_logic" .@ "user".
Definition NllftUsr2   : namespace := NllftG .@ "user".

Definition swell (k: lt_atom) := match k with LtAtomSwell _ => true | LtAtomNotSwell _ => false end.
Definition swell_set (ks: gset lt_atom) := ∀ k , k ∈ ks → swell k.

Lemma swell_set_union a b :
    swell_set a → swell_set b → swell_set (a ∪ b).
Proof.
    intros Ha Hb x Hin. rewrite elem_of_union in Hin. destruct Hin as [Hin|Hin].
      - apply Ha; trivial.
      - apply Hb; trivial.
Qed.

Lemma swell_set_default_dead : swell_set {[default_dead]}.
Proof.
  intros x Hin. rewrite elem_of_singleton in Hin. subst x. done.
Qed.

Section FullBorrows.
  Context {Σ: gFunctors}.
  Context `{!llft_logicGS Σ}.
  Context `{!invGS_gen hlc Σ}.
  Context `{!boxG Σ}.
  
  Context (γ: gname).
  Context (γo: gname).
  Context (γd: gname).
      
  Definition boxmap
      (alive dead : gset lt_atom) (m: gmap_bor_state)
        : gmap slice_name bool :=
      (λ bs , match bs with
        | Borrow al de => bool_decide (al ⊆ alive ∧ ¬(de ## dead))
        | Unborrow _ _ _ => false
      end) <$> m.
      
  (* (A, B) means A must end before B
      A alive ==> B alive
      B dead ==> A dead
  *)
  Definition outlives_consistent (dead: gset lt_atom) (outlives : outlives_set)
    := ∀ (o: gset lt_atom * lt_atom) , o ∈ outlives → (o.2 ∈ dead) → ¬(o.1 ## dead).
  
  Definition map_wf
      (alive dead blocked : gset lt_atom) (outlives : outlives_set) (m: gmap_bor_state)
    :=
    alive ## dead
    ∧ blocked ⊆ alive
    ∧ default_dead ∈ dead
    ∧ (∀ sn bs , m !! sn = Some bs → match bs with
      | Borrow al de => (al ∪ de) ⊆ (alive ∪ dead)
          ∧ swell_set al ∧ swell_set de
      | Unborrow bl al de => bl ⊆ blocked ∧ ¬(de ## dead)
          ∧ (∀ a , a ∈ al → (bl, a) ∈ outlives)
          ∧ (al ∪ de) ⊆ (alive ∪ dead)
    end)
    ∧ (∀ sn1 bs1 sn2 bs2 , sn1 ≠ sn2 → m !! sn1 = Some bs1 → m !! sn2 = Some bs2 →
        match (bs1, bs2) with
        | (Unborrow bl1 _ _, Unborrow bl2 _ _) => bl1 ## bl2
        | _ => True
        end)
    ∧ (∀ o , o ∈ outlives → o.1 ⊆ alive ∪ dead ∧ o.2 ∈ alive ∪ dead)
    .
  
  Lemma map_wf_insert_unborrow alive dead blocked bl al de outlives mbs sn :
    (al ⊆ alive) →
    (bl ⊆ alive) →
    ¬(de ## dead) →
    (de ⊆ (alive ∪ dead)) →
    (bl ## blocked) →
    (∀ a : lt_atom, a ∈ al → (bl, a) ∈ outlives) →
    map_wf alive dead blocked outlives mbs →
    map_wf alive dead (blocked ∪ bl) outlives (<[sn:=Unborrow bl al de]> mbs).
  Proof.
    unfold map_wf.
    intros Hal Hblalive Hde Hdewf Hbl Ho [Hdisj [Hblal [Hdd [Hf1 [Hf2 Hf3]]]]]. 
      split; trivial.
      split. { set_solver. }
      split; trivial.
      split. {
        intros sn' bs'. destruct (decide (sn = sn')).
        + intros Hmbssn'. subst sn'. rewrite lookup_insert in Hmbssn'. inversion Hmbssn'.
          split. { set_solver. } split; trivial. split; trivial. set_solver.
        + intros Hmbssn'. rewrite lookup_insert_ne in Hmbssn'; trivial.
          have Hfa := Hf1 sn' bs' Hmbssn'. destruct bs'; trivial. set_solver.
      }
      split. {
      intros sn1 bs1 sn2 bs2. destruct (decide (sn = sn1)).
        + subst sn1. intros Hne2 Hmbssn1 Hmbssn2.
          rewrite lookup_insert in Hmbssn1. rewrite lookup_insert_ne in Hmbssn2; trivial.
          inversion Hmbssn1. destruct bs2 as [|bl2 al2 de2]; trivial.
          subst bs1. have Hfa := Hf1 sn2 (Unborrow bl2 al2 de2) Hmbssn2. set_solver.
        + destruct (decide (sn = sn2)).
        * subst sn2. intros Hne1 Hmbssn1 Hmbssn2.
          rewrite lookup_insert in Hmbssn2. rewrite lookup_insert_ne in Hmbssn1; trivial.
          inversion Hmbssn2. destruct bs1 as [|bl1 al1 de1]; trivial.
          subst bs2. have Hfa := Hf1 sn1 (Unborrow bl1 al1 de1) Hmbssn1. set_solver.
        * intros Hne Hmbssn1 Hmbssn2.
          destruct bs1 as [|bl1 al1 de1]; destruct bs2 as [|bl2 al2 de2]; trivial.
          rewrite lookup_insert_ne in Hmbssn1; trivial.
          rewrite lookup_insert_ne in Hmbssn2; trivial.
          have Hfa := Hf2 sn1 (Unborrow bl1 al1 de1) sn2 (Unborrow bl2 al2 de2).
          intuition.
      }
      trivial.
  Qed.
  
  Lemma map_wf_delete_unborrow alive dead blocked bl al de outlives mbs sn :
    (al ⊆ alive) →
    (bl ⊆ blocked) →
    (mbs !! sn = Some (Unborrow bl al de)) →
    map_wf alive dead blocked outlives mbs →
    map_wf alive dead (blocked ∖ bl) outlives (delete sn mbs).
  Proof.
    unfold map_wf.
    intros Hal Hbl Hmbssn [Hdisj [Hblal [Hdd [Hf1 [Hf2 Hf3]]]]]. 
      split; trivial.
      split. { set_solver. }
      split; trivial.
      split. {
      intros sn' bs' Hdel. destruct (decide (sn = sn')) as [He|Hn].
        + subst sn'. rewrite lookup_delete in Hdel. discriminate.
        + rewrite lookup_delete_ne in Hdel; trivial.
          have Hfa := Hf1 sn' bs'. destruct bs'; intuition.
          have Hf2' := Hf2 _ _ _ _ Hn Hmbssn Hdel. intros x Hxing.
          rewrite elem_of_difference. split. { eauto. } set_solver.
      }
      split. {
        intros sn1 bs1 sn2 bs2 Hne Hdel1 Hdel2. 
      
        destruct (decide (sn = sn1)). { subst sn1. rewrite lookup_delete in Hdel1. discriminate. }
        destruct (decide (sn = sn2)). { subst sn2. rewrite lookup_delete in Hdel2. discriminate. }
        rewrite lookup_delete_ne in Hdel1; trivial.
        rewrite lookup_delete_ne in Hdel2; trivial.
        apply (Hf2 sn1 bs1 sn2 bs2); trivial.
      }
      trivial.
  Qed.
    
  Lemma map_wf_insert
      (alive dead blocked : gset lt_atom) (outlives : outlives_set) (m: gmap_bor_state) sn al de :
    swell_set al →
    swell_set de →
    map_wf alive dead blocked outlives m →
    (al ∪ de) ⊆ (alive ∪ dead) →
    map_wf alive dead blocked outlives (<[sn:=Borrow al de]> m).
  Proof.
    unfold map_wf. intros swell_al swell_de [Hdisj [Hblal [Hdd [Hf1 [Hf2 Hf3]]]]] Halde. 
    split; trivial.
    split; trivial.
    split; trivial.
    split. {
      intros sn' bs'. destruct (decide (sn = sn')).
      + subst sn'. intros Hsn. rewrite lookup_insert in Hsn. inversion Hsn. split; trivial.
        split; trivial.
      + rewrite lookup_insert_ne; trivial. intros Hsn'.
        apply (Hf1 sn' bs' Hsn').
    }
    split. {
      intros sn1 bs1 sn2 bs2. destruct (decide (sn = sn1)).
      + subst sn1. intros Hne Hsn1 Hsn2. rewrite lookup_insert in Hsn1. inversion Hsn1. trivial.
      + destruct (decide (sn = sn2)).
      - subst sn2. intros Hne Hsn1 Hsn2. rewrite lookup_insert in Hsn2. inversion Hsn2. destruct bs1; trivial.
      - intros Hne Hsn1 Hsn2. 
        rewrite lookup_insert_ne in Hsn1; trivial.
        rewrite lookup_insert_ne in Hsn2; trivial.
        apply (Hf2 sn1 bs1 sn2 bs2 Hne Hsn1 Hsn2).
    }
    - trivial.
  Qed.
  
  Lemma map_wf_delete
      (alive dead blocked : gset lt_atom) (outlives : outlives_set) (m: gmap_bor_state) sn :
    map_wf alive dead blocked outlives m →
    map_wf alive dead blocked outlives (delete sn m).
  Proof.
    unfold map_wf. intros [Hdisj [Hblal [Hdd [Hf1 [Hf2 Hf3]]]]].
    split; trivial.
    split; trivial.
    split; trivial.
    split. {
      intros sn' bs'. destruct (decide (sn = sn')).
      + subst sn'. intros Hsn. rewrite lookup_delete in Hsn. discriminate.
      + rewrite lookup_delete_ne; trivial. intros Hsn'.
        apply (Hf1 sn' bs' Hsn').
    }
    split. {
      intros sn1 bs1 sn2 bs2. destruct (decide (sn = sn1)).
      + subst sn1. intros Hne Hsn1 Hsn2. rewrite lookup_delete in Hsn1. discriminate.
      + destruct (decide (sn = sn2)).
      - subst sn2. intros Hne Hsn1 Hsn2. rewrite lookup_delete in Hsn2. discriminate.
      - intros Hne Hsn1 Hsn2. 
        rewrite lookup_delete_ne in Hsn1; trivial.
        rewrite lookup_delete_ne in Hsn2; trivial.
        apply (Hf2 sn1 bs1 sn2 bs2 Hne Hsn1 Hsn2).
    }
    - trivial.
  Qed.
   
  Lemma map_wf_new_lt alive dead blocked outlives mbs k :
    (k ∉ alive ∪ dead) →
    map_wf alive dead blocked outlives mbs →
    map_wf (alive ∪ {[k]}) dead blocked outlives mbs.
  Proof.
    unfold map_wf. intros Hk [Hdisj [Hblal [Hdd [Hf1 [Hf2 Hf3]]]]].
    split. { set_solver. }
    split. { set_solver. }
    split; trivial.
    split. {
      intros sn bs Hsn. have Hf := Hf1 sn bs Hsn. clear Hf1. clear Hf2.
      destruct bs.
        - split; last by intuition. destruct Hf as [Hf _]. 
          intros x Hin. rewrite elem_of_union. rewrite elem_of_union.
          have Hf1 := (Hf x Hin). rewrite elem_of_union in Hf1. intuition.
        - destruct Hf as [Hg [Hh [Hi Hj]]]. split; trivial. split; trivial. split; trivial.
          intros x Hin. rewrite elem_of_union. rewrite elem_of_union.
          have Hf1 := (Hj x Hin). rewrite elem_of_union in Hf1. intuition.
    }
    split. { trivial. }
    intros o Hoin. destruct (Hf3 o Hoin) as [Hf3' Hf3''].  split.
      - intros x Hxin. do 2 (rewrite elem_of_union). have Hf3'1 := Hf3' x Hxin.
        rewrite elem_of_union in Hf3'1. intuition.
      - move: Hf3''. do 3 (rewrite elem_of_union). intuition.
  Qed.
  
  Lemma map_wf_new_lt_dead alive dead blocked outlives mbs k :
    (k ∉ alive ∪ dead) →
    map_wf alive dead blocked outlives mbs →
    map_wf alive (dead ∪ {[k]}) blocked outlives mbs.
  Proof.
    unfold map_wf. intros Hk [Hdisj [Hblal [Hdd [Hf1 [Hf2 Hf3]]]]].
    split. { set_solver. }
    split. { trivial. }
    split. { set_solver. }
    split. {
      intros sn bs Hsn. have Hf := Hf1 sn bs Hsn. destruct bs.
        - destruct Hf as [Hf [Hg Hh]]. intuition.
          intros x Hin. rewrite elem_of_union. rewrite elem_of_union.
          have Hf' := (Hf x Hin). rewrite elem_of_union in Hf'. intuition.
        - destruct Hf as [Hf [Hg [Hh Hi]]]. intuition.
          + apply Hg. set_solver.
          + intros x Hin. rewrite elem_of_union. rewrite elem_of_union.
            have Hf' := (Hi x Hin). rewrite elem_of_union in Hf'. intuition.
    }
    split. { trivial. }
    intros o Hoin. destruct (Hf3 o Hoin) as [Hf3' Hf3''].  split.
      - intros x Hxin. do 2 (rewrite elem_of_union). have Hf3'1 := Hf3' x Hxin.
        rewrite elem_of_union in Hf3'1. intuition.
      - move: Hf3''. do 3 (rewrite elem_of_union). intuition.
  Qed.
  
  Lemma map_wf_preserved_on_kill alive dead blocked outlives k mbs :
    (k ∉ blocked) →
    map_wf alive dead blocked outlives mbs →
    map_wf (alive ∖ {[k]}) (dead ∪ {[k]}) blocked outlives mbs.
  Proof.
    unfold map_wf. intros H [Ha [Hb [Hc [Hforall [Hforall2 Hforall3]]]]].
    split. { set_solver. } split. { set_solver. } split. { set_solver. }
    split. {
    intros sn bs Hso. have Hdx := Hforall sn bs Hso. destruct bs as [al de|bl al de].
    - destruct Hdx as [H0 H1]. split; last by trivial.
      intro k'. destruct (decide (k' = k)).
        + subst k'. set_solver.
        + intros Hin. rewrite elem_of_union. rewrite elem_of_union.
          rewrite elem_of_difference. rewrite elem_of_singleton.
          have H0' := (H0 k' Hin). rewrite elem_of_union in H0'. intuition.
    - destruct Hdx as [He [Hf [Hg Hi]]]. split; trivial. split. { set_solver. }
      split; trivial.
      intro k'. destruct (decide (k' = k)).
        + subst k'. set_solver.
        + intros Hin. rewrite elem_of_union. rewrite elem_of_union.
          rewrite elem_of_difference. rewrite elem_of_singleton.
          have H0' := (Hi k' Hin). rewrite elem_of_union in H0'. intuition.
    }
    split. { trivial. }
    intros o Ho. have Hf := Hforall3 o Ho. split.
      - intro o2. destruct (decide (o2 = k)); set_solver.
      - destruct (decide (o.2 = k)); set_solver.
  Qed.
  
  Lemma swell_set_of_map_wf alive dead blocked outlives mbs sn al de :
      map_wf alive dead blocked outlives mbs →
      mbs !! sn = Some (Borrow al de) →
      swell_set al.
  Proof.
    intros Hmwf Hmbssn. destruct Hmwf as [Ha [Hb [Hc [Hforall [Hforall2 Hforall3]]]]].
    have Hf := Hforall sn (Borrow al de) Hmbssn. destruct Hf as [?[??]]. trivial.
  Qed.
  
  Lemma swell_set_of_map_wf_de alive dead blocked outlives mbs sn al de :
      map_wf alive dead blocked outlives mbs →
      mbs !! sn = Some (Borrow al de) →
      swell_set de.
  Proof.
    intros Hmwf Hmbssn. destruct Hmwf as [Ha [Hb [Hc [Hforall [Hforall2 Hforall3]]]]].
    have Hf := Hforall sn (Borrow al de) Hmbssn. destruct Hf as [?[??]]. trivial.
  Qed.

  Definition borrow_sum (f: BorState → bool) (m: gmap_bor_state) (mprops: gmap_props Σ) : iProp Σ := [∗ map] sn ↦ bs ∈ m ,
    match (f bs, mprops !! sn) with
      | (true, Some P) => P
      | _ => True%I
    end.
  
  Definition invalidated (alive dead : gset lt_atom) (k: lt_atom) (bs: BorState) := match bs with
    | Borrow al de => bool_decide (al ⊆ alive ∧ ¬(de ## dead) ∧ k ∈ al)
    | Unborrow _ al de => bool_decide (al ⊆ alive ∧ ¬(de ## dead) ∧ k ∈ al)
  end.
  
  Definition revalidated (alive dead : gset lt_atom) (k: lt_atom) (bs: BorState) := match bs with
    | Borrow al de => bool_decide (al ⊆ (alive ∖ {[k]}) ∧ (de ## dead) ∧ k ∈ de)
    | Unborrow _ _ _ => false
  end.
  
  Definition full_borrows_invalidated_via
    (alive dead : gset lt_atom) (k: lt_atom) (m: gmap_bor_state) (mprops: gmap_props Σ) : iProp Σ :=
      borrow_sum (invalidated alive dead k) m mprops.
    
  Definition full_borrows_revalidated_via
    (alive dead : gset lt_atom) (k: lt_atom) (m: gmap_bor_state) (mprops: gmap_props Σ) : iProp Σ :=
      borrow_sum (revalidated alive dead k) m mprops.
  
  Lemma borrow_sum_empty f m mprops
      : (∀ i x , m !! i = Some x → f x = false) →
      ⊢ borrow_sum f m mprops.
  Proof.
    intros Hf. iIntros. iApply big_sepM_intro. iModIntro. iIntros (sn bs) "%Hsn".
    destruct (f bs) eqn:Hfbs; last by done.
    destruct (mprops !! sn) eqn:Hmprops; last by done.
    rewrite (Hf sn bs Hsn) in Hfbs. discriminate.
  Qed.
      
  Lemma borrow_sum_equiv f f' m mprops
      : (∀ i x , m !! i = Some x → f x = true → f' x = true) →
      borrow_sum f' m mprops ⊢ borrow_sum f m mprops.
  Proof.
      intros Hf. iIntros "H". iDestruct (big_sepM_impl with "H []") as "H".
      2: { iFrame "H". }
      iModIntro. iIntros (sn bs) "%Hsn R".
      destruct (f bs) eqn:Hfbs; last by done.
      destruct (f' bs) eqn:Hf'bs; first by iFrame.
      iExFalso. rewrite (Hf sn bs Hsn Hfbs) in Hf'bs. discriminate.
  Qed.
  
  (* I think this is similar in spirit to the LftVs definition in RustBelt
     (https://plv.mpi-sws.org/rustbelt/popl18/appendix.pdf, Section 4.3)
     
     The idea is basically: when an Unborrow ends, instead of returning P, you're allowed
     to return some Q that can view-shift back to P. Thus we need to maintain all these
     view shifts somewhere in the invariant. The idea for defining this is basically to say,
     "for any possible future ordering sequence of lifetime expirations, we have the view
     shifts that we need".
     
     Note that `Dead γ k` appears on the LHS of the view shift. This is useful for two reasons:
      - Because [†κ] appears in llftl_bor_acc
      - Because it's needed for unnest
  *)
  
  Fixpoint future_vs' (fuel: nat) (alive dead : gset lt_atom) (outlives: outlives_set) 
      (m: gmap_bor_state) (mprops: gmap_props Σ) : iProp Σ :=
  match fuel with
    | 0 => True
    | S fuel' =>
      (∀ (k: lt_atom),
        ⌜k ∈ alive ∧ outlives_consistent (dead ∪ {[k]}) outlives⌝ -∗ ModuloDeadPers γ k -∗ (
        (⌜¬ swell k⌝ -∗ future_vs' fuel' (alive ∖ {[k]}) (dead ∪ {[k]}) outlives m mprops) ∧ (
          ▷ (full_borrows_invalidated_via alive dead k m mprops)
        ={↑NllftUsr ∪ ↑NllftUsr2}=∗ ▷ (full_borrows_revalidated_via alive dead k m mprops)
            ∗ future_vs' fuel' (alive ∖ {[k]}) (dead ∪ {[k]}) outlives m mprops)
        ))
  end.
      
  Definition future_vs (alive dead : gset lt_atom) (outlives: outlives_set) 
      (m: gmap_bor_state) (mprops: gmap_props Σ) : iProp Σ :=
    future_vs' (size alive) alive dead outlives m mprops.
      
  Lemma future_vs_def (alive dead : gset lt_atom) (outlives: outlives_set) 
      (m: gmap_bor_state) (mprops: gmap_props Σ) :
    future_vs alive dead outlives m mprops ⊣⊢
    ∀ (k: lt_atom),
      ⌜k ∈ alive ∧ outlives_consistent (dead ∪ {[k]}) outlives⌝ -∗ ModuloDeadPers γ k -∗ (
      (⌜¬ swell k⌝ -∗ future_vs (alive ∖ {[k]}) (dead ∪ {[k]}) outlives m mprops) ∧ (
        ▷ (full_borrows_invalidated_via alive dead k m mprops)
      ={↑NllftUsr ∪ ↑NllftUsr2}=∗ ▷ (full_borrows_revalidated_via alive dead k m mprops)
           ∗ future_vs (alive ∖ {[k]}) (dead ∪ {[k]}) outlives m mprops)).
  Proof.
    unfold future_vs.
    destruct (size alive) eqn:Heqn.
    - iSplit.
      + iIntros "H". iIntros (k). iIntros "[%Hk_in_alive _]".
      exfalso. rewrite size_empty_iff in Heqn. set_solver.
      + iIntros "H". unfold future_vs'. done.
    - iSplit.
      + iIntros "H" (k). iIntros "[%Hk %Hoc]".
        rewrite size_difference; last by set_solver.
        rewrite size_singleton. replace (size alive - 1) with n by lia.
        iApply "H". iFrame. iPureIntro. split; trivial.
      + iIntros "H" (k). iIntros "[%Hk %Hoc]".
        iDestruct ("H" $! (k)) as "H".
        rewrite size_difference; last by set_solver.
        rewrite size_singleton. replace (size alive - 1) with n by lia.
        iApply "H". iFrame. iPureIntro. split; trivial.
  Qed.
  
  Lemma set_ind_strong `{FinSet A C} `{!LeibnizEquiv C} (P : C → Prop) :
  (∀ X , (∀ x , x ∈ X → P (X ∖ {[ x ]})) → P X) → ∀ X, P X.
  Proof.
    intros Hind. 
    enough (∀ n Y , size Y = n → P Y) as Hall. {
      intros X. apply (Hall (set_size X)). trivial.
    }
    induction n.
     - intros Y. intros Heq0. rewrite size_empty_iff in Heq0.
       apply Hind. intros x. set_solver.
     - intros Y. intros HeqSn. apply Hind. intros x Hxy. apply IHn.
       rewrite size_difference; last by set_solver.
       rewrite HeqSn. rewrite size_singleton. lia.
  Qed.
  
  Lemma borrow_sum_insert f sn bs P mbs mprops :
      mbs !! sn = None →
      ▷ borrow_sum f (<[sn:=bs]> mbs) (<[sn:=P]> mprops)
      ⊢ ▷ ((if f bs then P else True) ∗ borrow_sum f mbs mprops).
  Proof.
    intros Hmbs. unfold borrow_sum. rewrite big_sepM_insert; trivial. iIntros "[H J]".
    iSplitL "H".
    - destruct (f bs) eqn:Hfbs; last by trivial. rewrite lookup_insert. iFrame.
    - iApply big_sepM_mono; last by iFrame "J". intros sn' bs' Hsn'. simpl.
      rewrite lookup_insert_ne; first by trivial. intros Heq. subst sn'.
      rewrite Hmbs in Hsn'. discriminate.
  Qed.
  
  Lemma borrow_sum_delete (f : BorState → bool) sn bs P mbs mprops :
      (mbs !! sn = Some bs) →
      ▷ (if f bs then mprops !! sn ≡ Some P else True)
      ∗ ▷ borrow_sum f (delete sn mbs) (delete sn mprops)
      ∗ ▷ (if f bs then P else True)
      ⊢  ▷ borrow_sum f mbs mprops.
  Proof.
    intros Hmbs. unfold borrow_sum. rewrite (big_sepM_delete _ mbs); last by apply Hmbs.
    iIntros "[#Eq [H P]]". iNext. iSplitL "P".
    - destruct (f bs) eqn:Hfbs; last by trivial. rewrite option_equivI.
      destruct (mprops !! sn); trivial. iRewrite "Eq". iFrame.
    - iApply big_sepM_mono; last by iFrame "H". intros sn' bs' Hsn'. simpl.
      rewrite lookup_delete_ne; first by trivial. intros Heq. subst sn'.
      rewrite lookup_delete in Hsn'. discriminate.
  Qed.
  
  Lemma borrow_sum_insert_2 (f : BorState → bool) sn bs P mbs mprops :
      mbs !! sn = None →
      ▷ ((if f bs then P else True) ∗ borrow_sum f mbs mprops)
      ⊢ ▷ borrow_sum f (<[sn:=bs]> mbs) (<[sn:=P]> mprops).
  Proof.
    intros Hmbs. unfold borrow_sum. rewrite big_sepM_insert; trivial. iIntros "[H J]".
    iSplitL "H".
    - destruct (f bs) eqn:Hfbs; last by trivial. rewrite lookup_insert. iFrame.
    - iApply big_sepM_mono; last by iFrame "J". intros sn' bs' Hsn'. simpl.
      rewrite lookup_insert_ne; first by trivial. intros Heq. subst sn'.
      rewrite Hmbs in Hsn'. discriminate.
  Qed.
  
  Lemma borrow_sum_delete_2 (f : BorState → bool) sn bs P mbs mprops :
      (mbs !! sn = Some bs) →
      ▷ (if f bs then mprops !! sn ≡ Some P else True)
      ∗ ▷ borrow_sum f mbs mprops
      ⊢ ▷ borrow_sum f (delete sn mbs) (delete sn mprops)
      ∗ ▷ (if f bs then P else True).
  Proof.
    intros Hmbs. unfold borrow_sum. rewrite (big_sepM_delete _ mbs); last by apply Hmbs.
    iIntros "[#Eq [H P]]". iSplitL "P".
    - iNext. iApply big_sepM_mono; last by iFrame "P". intros sn' bs' Hsn'. simpl.
      rewrite lookup_delete_ne; first by trivial. intros Heq. subst sn'.
      rewrite lookup_delete in Hsn'. discriminate.
    - iNext. destruct (f bs) eqn:Hfbs; last by trivial. rewrite option_equivI.
      destruct (mprops !! sn); trivial. iRewrite "Eq" in "H". iFrame.
  Qed.
  
  Lemma borrow_sum_delete_3 (f : BorState → bool) sn bs  mbs mprops :
      (mbs !! sn = Some bs) →
      ▷ borrow_sum f mbs mprops
      ⊢ ▷ borrow_sum f (delete sn mbs) (delete sn mprops).
  Proof.
    intros Hmbs. unfold borrow_sum. rewrite (big_sepM_delete _ mbs); last by apply Hmbs.
    iIntros "[H P]".
    iNext. iApply big_sepM_mono; last by iFrame "P". intros sn' bs' Hsn'. simpl.
    rewrite lookup_delete_ne; first by trivial. intros Heq. subst sn'.
    rewrite lookup_delete in Hsn'. discriminate.
  Qed.
  
  Lemma full_borrows_invalidated_via_insert alive dead k sn mbs mprops bs P :
      mbs !! sn = None →
      invalidated alive dead k bs = true →
      ▷ (full_borrows_invalidated_via alive dead k (<[sn := bs]> mbs) (<[ sn := P ]> mprops))
      ⊢ ▷ (P ∗ full_borrows_invalidated_via alive dead k mbs mprops).
  Proof.
      intros Hsn Hinv. iIntros "H".
      iDestruct (borrow_sum_insert with "H") as "H"; trivial. rewrite Hinv. iFrame.
  Qed.
      
  Lemma full_borrows_invalidated_via_insert_false alive dead k sn mbs mprops bs P :
      mbs !! sn = None →
      ▷ (full_borrows_invalidated_via alive dead k (<[sn := bs]> mbs) (<[ sn := P ]> mprops))
      ⊢ ▷ (full_borrows_invalidated_via alive dead k mbs mprops).
  Proof.
      intros Hsn. iIntros "H".
      iDestruct (borrow_sum_insert with "H") as "[b H]"; trivial.
  Qed.
      
  Lemma full_borrows_invalidated_via_delete alive dead k sn mbs mprops bs P :
      (mbs !! sn = Some bs) →
      ▷ (mprops !! sn ≡ Some P)
        ∗ ▷ (full_borrows_invalidated_via alive dead k (delete sn mbs) (delete sn mprops))
        ∗ ▷ P
      ⊢ 
      ▷ full_borrows_invalidated_via alive dead k mbs mprops.
  Proof.
      intros Hsn. iIntros "[#Heq [H P]]".
      iDestruct (borrow_sum_delete with "[H P]") as "H"; trivial. { apply Hsn. }
        { destruct (invalidated alive dead k bs); trivial; iFrame; iFrame "#".
            iSplitL; iNext; trivial. }
  Qed.
      
  Lemma full_borrows_invalidated_via_delete_false alive dead k sn mbs mprops bs :
      (mbs !! sn = Some bs) →
      invalidated alive dead k bs = false →
      ▷ (full_borrows_invalidated_via alive dead k (delete sn mbs) (delete sn mprops))
      ⊢ 
      ▷ full_borrows_invalidated_via alive dead k mbs mprops.
  Proof.
      intros Hsn Hinv. iIntros "H".
      iDestruct (borrow_sum_delete _ _ _ True%I with "[H]") as "H"; trivial. { apply Hsn. }
        { rewrite Hinv. iFrame. iSplit; iNext; trivial. }
  Qed.
      
  Lemma full_borrows_revalidated_via_insert alive dead k sn mbs mprops bs P :
      mbs !! sn = None →
      ▷ (full_borrows_revalidated_via alive dead k mbs mprops)
      ∗ ▷ P
      ⊢
      ▷ (full_borrows_revalidated_via alive dead k (<[sn := bs]> mbs) (<[ sn := P ]> mprops)).
  Proof.
      intros Hsn. iIntros "[H P]".
      iDestruct (borrow_sum_insert_2 with "[H P]") as "H"; trivial. { apply Hsn. }
      destruct (revalidated alive dead k bs) eqn:Heq; iFrame.
  Qed.
      
  Lemma full_borrows_revalidated_via_insert_false alive dead k sn mbs mprops bs P :
      mbs !! sn = None →
      revalidated alive dead k bs = false →
      ▷ (full_borrows_revalidated_via alive dead k mbs mprops)
      ⊢
      ▷ (full_borrows_revalidated_via alive dead k (<[sn := bs]> mbs) (<[ sn := P ]> mprops)).
  Proof.
      intros Hsn Hfalse. iIntros "H". unfold full_borrows_revalidated_via.
      iDestruct (borrow_sum_insert_2 with "[H]") as "H". { apply Hsn. }
      2: { iFrame "H". } rewrite Hfalse. iFrame.
  Qed.
 
  Lemma full_borrows_revalidated_via_delete alive dead k sn mbs mprops bs P :
      mbs !! sn = Some bs →
      revalidated alive dead k bs = true →
      ▷ (mprops !! sn ≡ Some P)
      ∗  ▷ full_borrows_revalidated_via alive dead k mbs mprops
      ⊢
        ▷ (full_borrows_revalidated_via alive dead k (delete sn mbs) (delete sn mprops))
      ∗ ▷ P.
  Proof.
      intros Hsn Hinv. iIntros "[#Heq H]".
      iDestruct (borrow_sum_delete_2 _ _ _ P with "[H]") as "[H P]"; trivial. { apply Hsn. }
        { iFrame "H". rewrite Hinv. iFrame. iFrame "#". }
        rewrite Hinv. iFrame.
  Qed.
 
  Lemma full_borrows_revalidated_via_delete_false alive dead k sn mbs mprops bs :
      mbs !! sn = Some bs →
        ▷ full_borrows_revalidated_via alive dead k mbs mprops
      ⊢
        ▷ (full_borrows_revalidated_via alive dead k (delete sn mbs) (delete sn mprops)).
  Proof.
      intros Hsn. iIntros "H".
      iDestruct (borrow_sum_delete_3 _ _ _ with "[H]") as "H"; trivial. { apply Hsn. }
  Qed.
 
  Lemma full_borrows_delete_insert_same alive dead k sn mbs mprops bs bs' P :
      (invalidated alive dead k bs = true → invalidated alive dead k bs' = true) →
      mbs !! sn = Some bs →
        ▷ (full_borrows_invalidated_via alive dead k 
            (<[sn := bs']> (delete sn mbs)) (<[sn := P]> (delete sn mprops)))
      ∗ ▷ (mprops !! sn ≡ Some P)
      ⊢ ▷ full_borrows_invalidated_via alive dead k mbs mprops.
  Proof using invGS_gen0 Σ γ.
    intros Himpl Hmbssn.
    iIntros "[inval #Heq]".
    destruct (invalidated alive dead k bs) eqn:Hcmp.
    - iDestruct (full_borrows_invalidated_via_insert alive dead k sn (delete sn mbs) (delete sn mprops) _ P with "[inval]") as "[p inval]".
      { rewrite lookup_delete. trivial. } { apply Himpl. trivial. } { iFrame "inval". }
      iDestruct (full_borrows_invalidated_via_delete with "[inval p]") as "inval".
      { apply Hmbssn. } { iFrame "Heq". iFrame "inval". iFrame "p". } iFrame.
    - iDestruct (full_borrows_invalidated_via_insert_false alive dead k sn (delete sn mbs) (delete sn mprops) _ P with "[inval]") as "inval".
      { apply lookup_delete. } { iFrame. }
      iDestruct (full_borrows_invalidated_via_delete_false with "[inval]") as "inval".
      { apply Hmbssn. } { apply Hcmp. } { iFrame "inval". } iFrame.
  Qed.
      
  Definition inner_inv (alive dead blocked : gset lt_atom) : iProp Σ :=
    ∃ (mbs: gmap_bor_state) (mprops: gmap_props Σ) Ptotal (outlives: outlives_set),
        AuthBorState γ mbs
          ∗ ModuloDead γ dead
          ∗ box Nbox (boxmap alive dead mbs) Ptotal
          ∗ future_vs alive dead outlives mbs mprops
          ∗ ⌜dom mbs = dom mprops
              ∧ map_wf alive dead blocked outlives mbs
              ∧ outlives_consistent dead outlives
             ⌝
          ∗ ([∗ map] sn ↦ Q ∈ mprops, slice Nbox sn Q)
          ∗ Outlives γo outlives.
          
  Lemma inner_fake (alive dead blocked al de : gset lt_atom) Q :
    ¬(al ## dead) →
    ModuloDead γ dead ⊢ |={↑Nbox}=> ∃ sn, 
    ModuloDead γ dead ∗ OwnBorState γ sn (Borrow al de) ∗ slice Nbox sn Q.
  Proof.
    intros Hnotdisj.
    iIntros "Modulo".
    iDestruct (box_alloc Nbox) as "box".
    iMod (slice_insert_empty Nbox (↑Nbox) false ∅ Q (True)%I with "box") as (sn) "[H [slice box2]]".
    iMod (alloc_fake_bor_state_lts γ sn alive dead al de with "Modulo") as "[Modulo OwnBor]".
    { trivial. }
    iModIntro. iExists sn. iFrame.
  Qed.
  
  Lemma delete_boxmap_implies_delete_original_is_none alive dead mbs sn1 sn2
    : delete sn1 (boxmap alive dead mbs) !! sn2 = None →
      delete sn1 mbs !! sn2 = None.
  Proof.
      intros Hdel. destruct (decide (sn1 = sn2)).
      - subst sn2. rewrite lookup_delete. trivial.
      - unfold boxmap in Hdel. rewrite lookup_delete_ne in Hdel; trivial.
        rewrite lookup_fmap in Hdel. rewrite lookup_delete_ne; trivial.
        destruct (mbs !! sn2) eqn:Hmbs; rewrite Hmbs; trivial. rewrite Hmbs in Hdel.
        discriminate.
  Qed.
  
  Lemma lookup_insert_delete_boxmap_helper sn sn' sn2 alive dead mbs bs :
      <[sn:=false]> (delete sn' (boxmap alive dead mbs)) !! sn2 = None →
      <[sn:=bs]> (delete sn' mbs) !! sn2 = None.
  Proof.
      destruct (<[sn:=bs]> (delete sn' mbs) !! sn2) eqn:Heq; trivial.
      intros Ha. exfalso. unfold boxmap in Ha. destruct (decide (sn = sn2)).
      - subst sn2. rewrite lookup_insert in Ha. discriminate.
      - rewrite lookup_insert_ne in Ha; trivial.
        rewrite lookup_insert_ne in Heq; trivial. destruct (decide (sn' = sn2)).
          + subst sn2. rewrite lookup_delete in Heq. discriminate.
          + rewrite lookup_delete_ne in Ha; trivial.
            rewrite lookup_delete_ne in Heq; trivial.
            rewrite lookup_fmap in Ha. rewrite Heq in Ha. discriminate.
  Qed.
      
  Lemma lookup_insert_delete_boxmap_helper2 sn sn' sn2 alive dead mbs  :
      <[sn:=false]> (delete sn' (boxmap alive dead mbs)) !! sn2 = None →
      (delete sn' mbs) !! sn2 = None.
  Proof.
      intros Ha. destruct (decide (sn2 = sn')).
      - subst sn'. apply lookup_delete.
      - destruct (decide (sn = sn2)).
        + subst sn2. rewrite lookup_insert in Ha. discriminate.
        + rewrite lookup_insert_ne in Ha; trivial. destruct (decide (sn' = sn2)); trivial.
          * subst sn'. rewrite lookup_delete; trivial.
          * rewrite lookup_delete_ne in Ha; trivial. rewrite lookup_delete_ne; trivial.
            unfold boxmap in Ha. rewrite lookup_fmap in Ha.
            destruct (mbs !! sn2) eqn:Heq; trivial. exfalso. rewrite Heq in Ha. discriminate.
  Qed.
      
  Lemma lookup_insert_boxmap_helper3 sn b alive dead mbs sn2 :
    <[sn:=b]> (boxmap alive dead mbs) !! sn2 = None →
    mbs !! sn2 = None ∧ sn ≠ sn2.
  Proof.
    intros Ha. assert (sn ≠ sn2) as Hne.
        { intros Heq. subst sn2. rewrite lookup_insert in Ha. discriminate. }
    split; trivial. rewrite lookup_insert_ne in Ha; trivial.
    unfold boxmap in Ha. rewrite lookup_fmap in Ha.
    destruct (mbs !! sn2) eqn:Heq; trivial. exfalso. rewrite Heq in Ha. discriminate.
  Qed.
  
  Lemma delete_delete_boxmap_helper4 sn sn1 sn2 alive dead mbs :
    delete sn2 (delete sn1 (boxmap alive dead mbs)) !! sn = None →
    delete sn2 (delete sn1 mbs) !! sn = None.
  Proof.
    intro Hx.
    destruct (decide (sn2 = sn)). { subst sn2. rewrite lookup_delete. trivial. }
    rewrite lookup_delete_ne; trivial.
    rewrite lookup_delete_ne in Hx; trivial.
    destruct (decide (sn1 = sn)). { subst sn1. rewrite lookup_delete. trivial. }
    rewrite lookup_delete_ne; trivial.
    rewrite lookup_delete_ne in Hx; trivial.
    unfold boxmap in Hx. rewrite lookup_fmap in Hx.
    destruct (mbs !! sn) eqn:Hmbs; trivial.
    rewrite Hmbs in Hx. discriminate.
  Qed.
      
  Lemma boxmap_insert_Borrow alive dead sn al de mbs
    : boxmap alive dead (<[ sn := Borrow al de ]> mbs)
      = <[ sn := bool_decide (al ⊆ alive ∧ ¬(de ## dead)) ]> (boxmap alive dead mbs).
  Proof.
    unfold boxmap. rewrite fmap_insert. trivial.
  Qed.
  
  Lemma boxmap_insert_Unborrow alive dead sn bl al de mbs
    : boxmap alive dead (<[ sn := Unborrow bl al de ]> mbs)
      = <[ sn := false ]> (boxmap alive dead mbs).
  Proof.
    unfold boxmap. rewrite fmap_insert. trivial.
  Qed.
       
  Lemma boxmap_delete alive dead sn mbs
      : boxmap alive dead (delete sn mbs)
        = delete sn (boxmap alive dead mbs).
  Proof.
    unfold boxmap. rewrite fmap_delete. trivial.
  Qed.
  
  Lemma agree_slice sn P Q :
    slice Nbox sn P -∗
    slice Nbox sn Q -∗
    ▷ (Some Q ≡ Some P).
  Proof.
    unfold slice. iIntros "[s1 _] [s2 _]".
    iDestruct (box_own_agree sn P Q with "[s1 s2]") as "X". { iFrame. }
    iNext. iRewrite "X". trivial.
  Qed.
  
  Lemma agree_slice_with_map (mbs : gmap_bor_state) (mprops : gmap_props Σ) sn bs P :
      dom mbs = dom mprops →
      mbs !! sn = Some bs →
      slice Nbox sn P ∗ ([∗ map] sn0↦Q0 ∈ mprops, slice Nbox sn0 Q0)
        ⊢ ▷ (mprops !! sn ≡ Some P).
  Proof using invGS_gen0 llft_logicGS0 Σ.
    intros Hdom Hmbssn. iIntros "[#s1 #smap]".
    destruct (mprops !! sn) as [Q|] eqn:Hmpropssn.
    - rewrite (big_sepM_delete _ _ sn Q); trivial. iDestruct "smap" as "[s2 _]".
      iApply agree_slice; iFrame "#".
    - exfalso.
      assert (sn ∈ dom mbs) as X. { apply elem_of_dom. exists bs. trivial. }
      assert (sn ∉ dom mprops) as Y. { rewrite not_elem_of_dom. trivial. }
      rewrite Hdom in X. contradiction.
  Qed.
  
  Lemma big_sepM_insert_1 `{Countable K} {A : Type} (Φ : K → A → iProp Σ) (m : gmap K A) i x :
    (Φ i x ∗ [∗ map] k↦y ∈ m, Φ k y)%I ⊢ ([∗ map] k↦y ∈ <[i:=x]> m, Φ k y).
  Proof.
    rewrite big_sepM_insert_delete.
    iIntros "[Phi Op]". iFrame. iDestruct (big_sepM_subseteq with "Op") as "Op";
        last by iFrame "Op". apply delete_subseteq.
  Qed.
      
  Lemma inv_get_dead alive dead blocked
    : inner_inv alive dead blocked ⊢ ⌜default_dead ∈ dead⌝.
  Proof.
    iIntros "Inv". iDestruct "Inv" as (mbs mprops Ptotal outlives) "[auth [modulo [box [vs [%pures [#slices outlives]]]]]]".
    unfold map_wf in pures. intuition.
  Qed.
    
  Lemma bool_decide_equiv P Q `{Decision P, Decision Q} :
    (P ↔ Q) → bool_decide P = bool_decide Q.
  Proof.
    intros Hiff. destruct (bool_decide P) eqn:Hp.
    - symmetry. rewrite bool_decide_eq_true. rewrite bool_decide_eq_true in Hp.
      rewrite <- Hiff. trivial.
    - symmetry. rewrite bool_decide_eq_false. rewrite bool_decide_eq_false in Hp.
      rewrite <- Hiff. trivial.
  Qed.
    
  (* The reason for the "outer inv" is that killing a lifetime has to proceed in
     multiple "phases". I couldn't find another way to do this that doesn't require
     the nested masks NllftG ⊂ Nllft.
     
     To kill a lifetime κ = {[k]} we have to:
  
     1. Exchange the Alive k tokens for a Dead k token
     
     2. Deduce that anything dependent on k according to the 'outlives' relationship is also dead
     
     3. Invoke kill_lt on the full borrows inv
     
     In order for step 2 to work, we need to employ the rule:
        `κ' ⊑ κ -∗ [†κ] ={↑NllftG}=∗ [†κ']`
     Thus (1) has to happen before (2) (so we can get the [†κ] token)
     But (2) is also a precondition for (3). Furthermore, we have to close up the llftG mask
     in order to do (2). Hence, we need the two "phases".
     
     To track when we're in the middle of these two phases, we use the Delayed token;
     `Delayed (Some k)` basically means, "we are in the middle of killing the lifetime k",
     i.e., we have created the `Dead k` token but not yet updated the full-borrows part
     of the invariant.
     
     The reason for having the larger mask Nllft is so we have somewhere to put the
     other `Delayed None` token that is outside the NllftG mask.
  *)
  
  Definition outer_inv (alive dead blocked : gset lt_atom) : iProp Σ :=
      ∃ opt_k , Delayed γd opt_k ∗ 
          match opt_k with
          | None => inner_inv alive dead blocked
          | Some (k, alive') =>
              inner_inv (alive ∪ {[k]}) (dead ∖ {[k]}) blocked ∗ ⌜ k ∉ alive ∧ k ∈ dead ∧ alive' = alive ⌝
          end.
             
  Lemma outer_fake (alive dead blocked al de : gset lt_atom) Q :
    ¬(al ## dead) →
    Delayed γd None ∗ (▷ outer_inv alive dead blocked)
    ={↑Nbox}=∗
    ∃ sn,
    Delayed γd None ∗ (▷ outer_inv alive dead blocked)
     ∗ OwnBorState γ sn (Borrow al de) ∗ slice Nbox sn Q.
  Proof.
    intros Hal.
    iIntros "[Delayed Inv]".
    iDestruct "Inv" as (opt_k) "[>D Inv]".
    iDestruct (delayed_agree with "[D Delayed]") as "%Heq". { iFrame "D Delayed". }
    subst opt_k.
    iDestruct "Inv" as (mbs mprops Ptotal outlives) "[>auth [>Modulo [box [vs [#pures [#slices outlives]]]]]]".
    iMod (inner_fake alive dead blocked al de with "Modulo") as (sn) "(X & Y & Z)". { trivial. }
    iModIntro. iExists sn. iFrame. iNext.
    unfold inner_inv. iExists mbs. iExists mprops. iExists Ptotal. iExists outlives.
    iFrame. iFrame "#".
  Qed.
End FullBorrows.
