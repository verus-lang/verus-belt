Require Import guarding.lib.boxes.
Require Import lrust.lifetime.lifetime_internals.ra.
Require Import lrust.lifetime.lifetime_internals.inv.

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

Section FullBorrows.
  Context {Σ: gFunctors}.
  Context `{!llft_logicGS Σ}.
  Context `{!invGS_gen hlc Σ}.
  Context `{!boxG Σ}.
  
  Context (γ: gname).
  Context (γo: gname).
  Context (γd: gname).
  
  Implicit Types (mprops: gmap_props Σ).
  
  Local Instance modulo_dead_pers γ1 k : Persistent (ModuloDeadPers γ1 k).
  Proof. apply own_core_persistent. unfold CoreId. trivial. Qed.
    
  Lemma future_vs_for_unborrow_start alive dead outlives mbs mprops sn bl al de de' P :
    (alive ## dead) →
    (mbs !! sn = Some (Borrow al de')) →
    (¬ de' ## dead) →
    (¬ de ## dead) →
    future_vs γ alive dead outlives mbs mprops
      ∗ ▷ (mprops !! sn ≡ Some P)
    ⊢
    future_vs γ alive dead outlives (<[sn:=Unborrow bl al de]> mbs) (<[sn:=P]> (delete sn mprops)).
  Proof using invGS_gen0 Σ γ γd γo.
    replace (<[sn:=Unborrow bl al de]> mbs) with 
        (<[sn:=Unborrow bl al de]> (delete sn mbs)).
      2: { apply map_eq. { intros i. destruct (decide (sn = i)).
          - subst sn. rewrite lookup_insert. rewrite lookup_insert. trivial.
          - rewrite lookup_insert_ne; trivial. rewrite lookup_insert_ne; trivial.
              rewrite lookup_delete_ne; trivial. } }
  
    generalize dead. clear dead.
    induction alive as [my_alive IH] using set_ind_strong. 
    iIntros (my_dead Hdisj Hmbssn Hde' Hde) "[Hvs #Heq]".
    
    rewrite future_vs_def.
    rewrite (future_vs_def γ my_alive).
    iIntros (k) "%Hin_my_alive #Dead". iSplit.
      { iIntros "NotSwell". iDestruct ("Hvs" $! k with "[] Dead") as "[Hvs _]".
        { iPureIntro. destruct Hin_my_alive. split; trivial. }
        iApply IH. { intuition. } { set_solver. } { trivial. } { set_solver. } { set_solver. }
        iFrame "#". iApply "Hvs". iApply "NotSwell".
      }
    iIntros "inval".
    iDestruct ("Hvs" $! k Hin_my_alive with "Dead") as "[_ Hvs]".
    
    iDestruct (full_borrows_delete_insert_same γ my_alive my_dead k sn mbs mprops (Borrow al de') (Unborrow bl al de) P with "[inval]") as "inval".
      { unfold invalidated. rewrite bool_decide_eq_true. rewrite bool_decide_eq_true.
        set_solver. }
      { trivial. } { iFrame. iFrame "#". }
      
    iMod ("Hvs" with "[inval]") as "[reval vs]". { iFrame. }
    
    iModIntro.
    
    iSplitL "reval". {
      iApply full_borrows_revalidated_via_insert_false.
      { apply lookup_delete. } { unfold revalidated. trivial. }
      iApply full_borrows_revalidated_via_delete_false.
      { apply Hmbssn. } iFrame.
    }
    
    iApply IH; trivial. { set_solver. } { set_solver. } { set_solver. }
      { set_solver. } iFrame. iFrame "#".
  Qed.
  
  Lemma inner_unborrow_start alive dead blocked outlives sn (bl al de : gset lt_atom) P :
    (al ⊆ alive) →
    (de ⊆ alive ∪ dead) →
    ¬(de ## dead) →
    (bl ## blocked) →
    (bl ⊆ alive) →
    (∀ (k : lt_atom) , k ∈ al → (bl, k) ∈ outlives) →
    (▷ inner_inv γ γo alive dead blocked) ∗ Outlives γo outlives
        ∗ OwnBorState γ sn (Borrow al de)
        ∗ slice Nbox sn P
      ⊢ |={↑Nbox}=> 
    (▷ inner_inv γ γo alive dead (blocked ∪ bl))
        ∗ Outlives γo outlives
        ∗ OwnBorState γ sn (Unborrow bl al de)
        ∗ (▷ P).
  Proof using invGS_gen0 Σ γ γd γo.
    intros Hal Hdewf Hde Hbl Hblalive Houtlives.
    iIntros "[Inv [Outlives [OwnBor #slice]]]".
    unfold inner_inv.
    iDestruct "Inv" as (mbs mprops Ptotal outlives') "[>auth [>Modulo [box [vs [>%pures [#slices >outlives]]]]]]".
    iDestruct (outlives_agree with "[outlives Outlives]") as "%Hoeq". { iFrame. }
    subst outlives'.
    
    assert (al ## dead) as Hdisj_al_dead. { unfold inv.map_wf in pures; set_solver. }
    
    iDestruct (agree_bor_state_borrow_lts γ sn mbs dead al de Hdisj_al_dead
        with "[Modulo auth OwnBor]") as (de') "[%Hmbssn %Hrel_de]". { iFrame. }
    assert (boxmap alive dead mbs !! sn = Some true) as Hboxmaptrue.
    { unfold boxmap. rewrite lookup_fmap. rewrite Hmbssn. simpl.
      f_equiv. rewrite bool_decide_eq_true. split; trivial.
      destruct (decide (de = de')); intuition. subst de'; intuition. }
    
    iMod (slice_empty (Nbox) (↑Nbox) true (boxmap alive dead mbs) Ptotal P sn with "slice box") as "[P box]". { set_solver. } { trivial. }
    
    iMod (update_bor_state_borrow_lts γ sn mbs dead al de (Unborrow bl al de) Hdisj_al_dead with "[Modulo auth OwnBor]") as "[Modulo [auth OwnBor]]". { iFrame. }
    
    assert (alive ## dead) as Hdisj. { unfold inv.map_wf in pures; intuition. }
    assert (¬ de' ## dead) as Hde'. { set_solver. }
    
    iDestruct (bi.later_mono _ _ (future_vs_for_unborrow_start alive dead outlives mbs mprops sn bl al de de' P Hdisj Hmbssn Hde' Hde) with "[vs]") as "vs".
      { iFrame. iNext. iDestruct (agree_slice_with_map mbs mprops sn _ P with "[]") as "EqSlice".
        { intuition. } { apply Hmbssn. } { iFrame "#". }
       iFrame. iFrame "#".
     }
    
    iModIntro.
    iFrame "Modulo". iFrame "outlives". iFrame "Outlives". iFrame "P". iFrame "OwnBor".
    
    iNext.
    iExists (<[sn:=Unborrow bl al de]> mbs). iExists (<[sn:=P]> (delete sn mprops)).
    iExists Ptotal.
    
    iFrame "auth".
    iSplitL "box". { rewrite boxmap_insert_Unborrow. iFrame. }
    iFrame "vs".
    
    destruct pures as [Hdom [Hwf Hoc]].
    assert (al ∪ de' ⊆ alive ∪ dead) as Hwfalde. {
      destruct Hwf as [Ha [Hb [Hc [Hforall Hforall2]]]].
      apply (Hforall sn (Borrow al de') Hmbssn).
    }
    iSplitL. { iPureIntro. 
      split. {
        rewrite dom_insert_L.
        rewrite dom_insert_L.
        rewrite dom_delete_L. rewrite Hdom. apply set_eq. intro x.
          destruct (decide (x = sn)); set_solver.
      }
      split. { apply map_wf_insert_unborrow; trivial. }
      trivial.
    }
    { iApply big_sepM_insert_1. iFrame "slice".
      rewrite big_sepM_forall. rewrite big_sepM_forall. iIntros (x R) "%Dm".
      iApply "slices". iPureIntro. rewrite lookup_delete_Some in Dm. intuition. }
  Qed.
    
  Lemma llft_vs_for_unborrow_end' k1 alive dead outlives mbs mprops bl al de sn sn2 Q :
    (mbs !! sn = Some (Unborrow bl al de)) →
    ((delete sn mbs) !! sn2 = None) →
    (∀ a, a ∈ al → (bl, a) ∈ outlives) →
    (k1 ∈ al) →
    (k1 ∉ alive) →
    (¬(de ## dead)) →
  future_vs γ alive dead outlives mbs mprops
  ⊢ future_vs γ alive dead outlives (<[sn2:=Borrow al de]> (delete sn mbs))
    (<[sn2:=Q]> (delete sn mprops)).
  Proof using invGS_gen0 Σ γ γd γo.
    intros Hsn Hsnmbs2 Hbl_a_outlives Hk1al. generalize dead. clear dead.
    induction alive as [my_alive IH] using set_ind_strong. 
    iIntros (my_dead Hk1alive Hde_dead) "Hvs".
    
    rewrite future_vs_def.
    rewrite (future_vs_def γ my_alive).
    iIntros (k) "%Hin_my_alive #Dead". iSplit.
      { iIntros "NotSwell". iDestruct ("Hvs" $! k Hin_my_alive with "Dead") as "[Hvs _]".
        iApply IH. { intuition. } { set_solver. } { set_solver. }
        iApply "Hvs". iFrame.
      }
    iIntros "inval".
    iDestruct ("Hvs" $! k Hin_my_alive with "Dead") as "[_ Hvs]".

    iDestruct (full_borrows_invalidated_via_insert_false with "inval") as "inval".
      { trivial. }
     iDestruct (full_borrows_invalidated_via_delete_false with "inval") as "inval".
      { apply Hsn. }
      { unfold invalidated.  rewrite bool_decide_eq_false. set_solver. }
      
      iMod ("Hvs" with "[inval]") as "[reval vs]". { iFrame. }
      
      iModIntro.
      
      iSplitL "reval". {
          iApply full_borrows_revalidated_via_insert_false.
          { trivial. }
          { unfold revalidated. rewrite bool_decide_eq_false. set_solver. }
          iApply full_borrows_revalidated_via_delete_false.
          { apply Hsn. }
          iFrame.
      }
      
      iApply IH; trivial. { set_solver. } { set_solver. } { set_solver. }
   Qed.
  
  Lemma llft_vs_for_unborrow_end alive dead outlives mbs mprops bl al de sn sn2 P Q :
    (mbs !! sn = Some (Unborrow bl al de)) →
    ((delete sn mbs) !! sn2 = None) →
    (∀ a, a ∈ al → (bl, a) ∈ outlives) →
    (al ⊆ alive) →
    (¬(de ## dead)) →
    swell_set al →
  future_vs γ alive dead outlives mbs mprops
    ∗ (∀ d, ⌜d ∈ dead⌝ -∗ ModuloDeadPers γ d)
    ∗ (▷ Q ∗ (∃ k : lt_atom, ⌜k ∈ bl⌝ ∗ Dead γ k) ={↑NllftUsr ∪ ↑NllftUsr2}=∗ ▷ P)
    ∗ (▷ (mprops !! sn ≡ Some P))
  ⊢
  future_vs γ alive dead outlives (<[sn2:=Borrow al de]> (delete sn mbs))
    (<[sn2:=Q]> (delete sn mprops)).
  Proof using invGS_gen0 Σ γ γd γo.
    intros Hsn Hsn2 Hbl_a_outlives. generalize dead. clear dead.
    induction alive as [my_alive IH] using set_ind_strong. 
    iIntros (my_dead Hal_alive Hde_dead swell_al) "[Hvs [#Halldead [qvs #Heq]]]".
    
    rewrite future_vs_def.
    rewrite (future_vs_def γ my_alive).
    iIntros (k) "%Hin_my_alive #Dead".
    (*iIntros (k) "[[%Hin_my_alive %Hoc] [#Dead inval]]".*)
    
    iAssert (∀ d : lt_atom, ⌜d ∈ (my_dead ∪ {[ k ]})⌝ -∗ ModuloDeadPers γ d)%I as "#Halldead2".
      { iIntros (d) "%Hdin". rewrite elem_of_union in Hdin. destruct Hdin as [Hdin1|Hdin2].
        - iApply "Halldead". iPureIntro; trivial.
        - rewrite elem_of_singleton in Hdin2. subst k. iApply "Dead".
      }
    
    destruct (decide (k ∈ al)) as [Hin|Hout].
    
    - iSplit.
      { iIntros "%Hnotswell". exfalso. apply Hnotswell. apply swell_al. apply Hin. }
      assert (invalidated my_alive my_dead k (Borrow al de) = true) as Hinval_true.
      { unfold invalidated. rewrite bool_decide_eq_true. intuition. }
      iDestruct ("Hvs" $! k Hin_my_alive with "Dead") as "[_ Hvs]".
      destruct Hin_my_alive as [Hin_my_alive Hoc].
      iIntros "inval".
      iDestruct ((full_borrows_invalidated_via_insert my_alive my_dead k sn2 _ _ _ _ Hsn2 Hinval_true) with "inval") as "[Q inval]".
      
      assert (¬(bl ## my_dead ∪ {[ k ]})) as Hbl_disj_my_dead_u.
      {
        have Hoc2 := Hoc (bl, k) (Hbl_a_outlives k Hin). apply Hoc2. set_solver.
      }
      assert (bl ∩ (my_dead ∪ {[ k ]}) ≠ ∅) as Hbl_disj_my_dead_u2. { set_solver. }
      assert (∃ x , x ∈ (bl ∩ (my_dead ∪ {[ k ]}))) as Hex_x. { apply set_choose_L; trivial. }
      destruct Hex_x as [x Hex_x].
      assert (x ∈ bl) as Hex_bl by set_solver.
      assert (x ∈ (my_dead ∪ {[ k ]})) as Hex_d by set_solver.
      
      iMod ("qvs" with "[Q]") as "P".
      { iFrame "Q". iExists x. iSplitL. { iPureIntro; trivial. }
        iApply modulo_dead_pers_implies_dead. iApply "Halldead2". iPureIntro; trivial. }
        
      iDestruct (full_borrows_invalidated_via_delete my_alive my_dead k sn mbs mprops (Unborrow bl al de) P Hsn with "[Heq inval P]") as "inval".
        { iFrame. iFrame "Heq". }
      
      iMod ("Hvs" with "[inval]") as "[reval vs]". { iFrame. }
      
      iModIntro.
      
      iSplitL "reval". {
          iApply full_borrows_revalidated_via_insert_false.
          { apply Hsn2. }
          { unfold revalidated. rewrite bool_decide_eq_false. set_solver. }
          iApply full_borrows_revalidated_via_delete_false.
          { apply Hsn. }
          iFrame.
      }
      
      iApply (llft_vs_for_unborrow_end' k); trivial. { set_solver. } { set_solver. }
        { set_solver. } set_solver.
   - iSplit.
     { iIntros "NotSwell". iDestruct ("Hvs" $! k Hin_my_alive with "Dead") as "[Hvs _]".
        iApply IH. { intuition. } { set_solver. } { set_solver. } { trivial. }
        iFrame. iFrame "#".
        iApply "Hvs". iFrame.
      }
     iDestruct ("Hvs" $! k Hin_my_alive with "Dead") as "[_ Hvs]".
     iIntros "inval".
     iDestruct (full_borrows_invalidated_via_insert_false with "inval") as "inval".
      { apply Hsn2. }
     iDestruct (full_borrows_invalidated_via_delete_false with "inval") as "inval".
      { apply Hsn. }
      { unfold invalidated.  rewrite bool_decide_eq_false. set_solver. }
      
      iMod ("Hvs" with "[inval]") as "[reval vs]". { iFrame. }
      
      iModIntro.
      
      iSplitL "reval". {
          iApply full_borrows_revalidated_via_insert_false.
          { apply Hsn2. }
          { unfold revalidated. rewrite bool_decide_eq_false. set_solver. }
          iApply full_borrows_revalidated_via_delete_false.
          { apply Hsn. }
          iFrame.
      }
      
      iApply IH; trivial. { set_solver. } { set_solver. } { set_solver. }
      iFrame. iFrame "#".
  Qed.
   
  Lemma llft_vs_for_unborrow_end_at_same_idx alive dead outlives mbs mprops bl al de sn P :
    (mbs !! sn = Some (Unborrow bl al de)) →
    (∀ a, a ∈ al → (bl, a) ∈ outlives) →
    (al ⊆ alive) →
    (¬(de ## dead)) →
    (swell_set al) →
  future_vs γ alive dead outlives mbs mprops
    ∗ (∀ d, ⌜d ∈ dead⌝ -∗ ModuloDeadPers γ d)
    ∗ (▷ (mprops !! sn ≡ Some P))
  ⊢
  future_vs γ alive dead outlives (<[sn:=Borrow al de]> mbs) (<[sn:=P]> (delete sn mprops)).
  Proof using hlc invGS_gen0 llft_logicGS0 Σ γ γd γo.
    intros Hsn Hsn2 Hbl_a_outlives Hde al_swell.
    iIntros "[vs [dead #eq]]".
    iDestruct (llft_vs_for_unborrow_end alive dead outlives mbs mprops bl al de sn sn P P
        with "[vs dead eq]") as "X".
      - apply Hsn. - apply lookup_delete. - apply Hsn2. - apply Hbl_a_outlives. - apply Hde.
      - trivial.
      - iFrame. iFrame "#". iIntros "[P _]". iModIntro. iFrame.
      - replace ((<[sn:=Borrow al de]> (delete sn mbs)))
          with ((<[sn:=Borrow al de]> mbs)).
          + iFrame "X".
          + rewrite insert_delete_insert. trivial.
  Qed.
  
  Lemma llft_vs_for_unborrow_end_atomic' k1 alive dead outlives mbs mprops bl al de sn sn2 Q :
    (mbs !! sn = Some (Borrow al de)) →
    ((delete sn mbs) !! sn2 = None) →
    (∀ a, a ∈ al → (bl, a) ∈ outlives) →
    (k1 ∈ al) →
    (k1 ∉ alive) →
    (¬(de ## dead)) →
  future_vs γ alive dead outlives mbs mprops
  ⊢ future_vs γ alive dead outlives (<[sn2:=Borrow al de]> (delete sn mbs))
    (<[sn2:=Q]> (delete sn mprops)).
  Proof using invGS_gen0 Σ γ γd γo.
    intros Hsn Hsnmbs2 Hbl_a_outlives Hk1al. generalize dead. clear dead.
    induction alive as [my_alive IH] using set_ind_strong. 
    iIntros (my_dead Hk1alive Hde_dead) "Hvs".
    
    rewrite future_vs_def.
    rewrite (future_vs_def γ my_alive).
    iIntros (k) "%Hin_my_alive Dead". iSplit.
      { iIntros "NotSwell". iDestruct ("Hvs" $! k Hin_my_alive with "Dead") as "[Hvs _]".
        iApply IH. { intuition. } { set_solver. } { set_solver. }
        iApply "Hvs". iFrame.
      }
    iIntros "inval".
    iDestruct ("Hvs" $! k Hin_my_alive with "Dead") as "[_ Hvs]".
    
    iDestruct (full_borrows_invalidated_via_insert_false with "inval") as "inval".
      { trivial. }
     iDestruct (full_borrows_invalidated_via_delete_false with "inval") as "inval".
      { apply Hsn. }
      { unfold invalidated.  rewrite bool_decide_eq_false. set_solver. }
      
      iMod ("Hvs" with "[inval]") as "[reval vs]". { iFrame. }
      
      iModIntro.
      
      iSplitL "reval". {
          iApply full_borrows_revalidated_via_insert_false.
          { trivial. }
          { unfold revalidated. rewrite bool_decide_eq_false. set_solver. }
          iApply full_borrows_revalidated_via_delete_false.
          { apply Hsn. }
          iFrame.
      }
      
      iApply IH; trivial. { set_solver. } { set_solver. } { set_solver. }
   Qed.
  
  Lemma llft_vs_for_unborrow_end_atomic alive dead outlives mbs mprops bl al de sn sn2 P Q :
    (mbs !! sn = Some (Borrow al de)) →
    ((delete sn mbs) !! sn2 = None) →
    (∀ a, a ∈ al → (bl, a) ∈ outlives) →
    (al ⊆ alive) →
    (¬(de ## dead)) →
    swell_set al →
  future_vs γ alive dead outlives mbs mprops
    ∗ (∀ d, ⌜d ∈ dead⌝ -∗ ModuloDeadPers γ d)
    ∗ (▷ Q ∗ (∃ k : lt_atom, ⌜k ∈ bl⌝ ∗ Dead γ k) ={↑NllftUsr ∪ ↑NllftUsr2}=∗ ▷ P)
    ∗ (▷ (mprops !! sn ≡ Some P))
  ⊢
  future_vs γ alive dead outlives (<[sn2:=Borrow al de]> (delete sn mbs))
    (<[sn2:=Q]> (delete sn mprops)).
  Proof using invGS_gen0 Σ γ γd γo.
    intros Hsn Hsn2 Hbl_a_outlives. generalize dead. clear dead.
    induction alive as [my_alive IH] using set_ind_strong. 
    iIntros (my_dead Hal_alive Hde_dead swell_al) "[Hvs [#Halldead [qvs #Heq]]]".
    
    rewrite future_vs_def.
    rewrite (future_vs_def γ my_alive).
    iIntros (k) "[%Hin_my_alive %Hoc] #Dead".
    
    iAssert (∀ d : lt_atom, ⌜d ∈ (my_dead ∪ {[ k ]})⌝ -∗ ModuloDeadPers γ d)%I as "#Halldead2".
      { iIntros (d) "%Hdin". rewrite elem_of_union in Hdin. destruct Hdin as [Hdin1|Hdin2].
        - iApply "Halldead". iPureIntro; trivial.
        - rewrite elem_of_singleton in Hdin2. subst k. iApply "Dead".
      }
    
    destruct (decide (k ∈ al)) as [Hin|Hout].
    
    - iSplit.
      { iIntros "%Hnotswell". exfalso. apply Hnotswell. apply swell_al. apply Hin. }
      assert (invalidated my_alive my_dead k (Borrow al de) = true) as Hinval_true.
      { unfold invalidated. rewrite bool_decide_eq_true. intuition. }
      iIntros "inval".
      iDestruct ((full_borrows_invalidated_via_insert my_alive my_dead k sn2 _ _ _ _ Hsn2 Hinval_true) with "inval") as "[Q inval]".
      
      assert (¬(bl ## my_dead ∪ {[ k ]})) as Hbl_disj_my_dead_u.
      {
        have Hoc2 := Hoc (bl, k) (Hbl_a_outlives k Hin). apply Hoc2. set_solver.
      }
      assert (bl ∩ (my_dead ∪ {[ k ]}) ≠ ∅) as Hbl_disj_my_dead_u2. { set_solver. }
      assert (∃ x , x ∈ (bl ∩ (my_dead ∪ {[ k ]}))) as Hex_x. { apply set_choose_L; trivial. }
      destruct Hex_x as [x Hex_x].
      assert (x ∈ bl) as Hex_bl by set_solver.
      assert (x ∈ (my_dead ∪ {[ k ]})) as Hex_d by set_solver.
      
      iMod ("qvs" with "[Q]") as "P".
      { iFrame "Q". iExists x. iSplitL. { iPureIntro; trivial. }
        iApply modulo_dead_pers_implies_dead. iApply "Halldead2". iPureIntro; trivial. }
        
      iDestruct (full_borrows_invalidated_via_delete my_alive my_dead k sn mbs mprops (Borrow al de) P Hsn with "[Heq inval P]") as "inval".
        { iFrame. iFrame "Heq". }
      
      iDestruct ("Hvs" $! k with "[] Dead") as "Hvs".
        { iPureIntro; split; trivial. }
      iMod ("Hvs" with "[inval]") as "[reval vs]". { iFrame. }
      
      iModIntro.
      
      iSplitL "reval". {
          iApply full_borrows_revalidated_via_insert_false.
          { apply Hsn2. }
          { unfold revalidated. rewrite bool_decide_eq_false. set_solver. }
          iApply full_borrows_revalidated_via_delete_false.
          { apply Hsn. }
          iFrame.
      }
      
      iApply (llft_vs_for_unborrow_end_atomic' k); trivial. { set_solver. } { set_solver. }
        { set_solver. }
   - iSplit.
     { iIntros "NotSwell". iDestruct ("Hvs" $! k with "[] Dead") as "[Hvs _]".
        { iPureIntro. split; trivial. }
        iApply IH. { intuition. } { set_solver. } { set_solver. } { trivial. }
        iFrame. iFrame "#".
        iApply "Hvs". iFrame.
      }
     iDestruct ("Hvs" $! k with "[] Dead") as "[_ Hvs]".
        { iPureIntro. split; trivial. }
     iIntros "inval".
   iDestruct (full_borrows_invalidated_via_insert_false with "inval") as "inval".
      { apply Hsn2. }
     iDestruct (full_borrows_invalidated_via_delete_false with "inval") as "inval".
      { apply Hsn. }
      { unfold invalidated.  rewrite bool_decide_eq_false. set_solver. }
      
      iMod ("Hvs" with "[inval]") as "[reval vs]". { iFrame. }
      
      iModIntro.
      
      iSplitL "reval". {
          iApply full_borrows_revalidated_via_insert_false.
          { apply Hsn2. }
          { unfold revalidated. rewrite bool_decide_eq_false. set_solver. }
          iApply full_borrows_revalidated_via_delete_false.
          { apply Hsn. }
          iFrame.
      }
      
      iApply IH; trivial. { set_solver. } { set_solver. }
      iFrame. iFrame "#".
  Qed.
          
  Lemma inner_unborrow_end alive dead blocked sn bl al de P Q :
    swell_set al →
    swell_set de  →
    (▷ inner_inv γ γo alive dead blocked)
        ∗ OwnBorState γ sn (Unborrow bl al de)
        ∗ slice Nbox sn P
        ∗ (▷ (▷ Q ∗ (∃ k , ⌜ k ∈ bl ⌝ ∗ Dead γ k) ={↑NllftUsr ∪ ↑NllftUsr2}=∗ ▷ P))
        ∗ (▷ Q)
        ={↑Nbox ∪ ↑NllftUsr}=∗ ∃ sn2,
          (▷ inner_inv γ γo alive dead (blocked ∖ bl))
          ∗ OwnBorState γ sn2 (Borrow al de)
          ∗ slice Nbox sn2 Q
          ∗ ⌜bl ⊆ blocked⌝
        .
  Proof using invGS_gen0 Σ γ γd γo.
    iIntros (swell_al swell_de) "[Inv [OwnBor [#slice [qvs q]]]]".
    unfold inner_inv.
    iDestruct "Inv" as (mbs mprops Ptotal outlives) "[>auth [>Modulo [box [vs [>%pures [#slices >outlives]]]]]]".
    destruct pures as [Hdom [Hwf Houtlives]].
    iDestruct (agree_bor_state_unborrow γ sn mbs bl al de with "[auth OwnBor]") as "%Hmbssn". { iFrame. }
    assert (boxmap alive dead mbs !! sn = Some false) as Hboxmapsn. {
      unfold boxmap. rewrite lookup_fmap. rewrite Hmbssn. trivial.
    }
    assert (bl ⊆ blocked) as Hbl. {
      destruct Hwf as [Ha [Hb [Hc [Hforall Hforall2]]]].
      have Hf := Hforall sn _ Hmbssn. intuition.
    }
    assert (¬(de ## dead)) as Hde. {
      destruct Hwf as [Ha [Hb [Hc [Hforall Hforall2]]]].
      have Hf := Hforall sn _ Hmbssn. intuition.
    }
    assert (al ⊆ alive) as Hal. {
      destruct Hwf as [Ha [Hb [Hc [Hforall Hforall2]]]].
      have Hf := Hforall sn _ Hmbssn. intros a Haal.
      destruct (decide (a ∈ alive)) as [Hin|Hout]; trivial. exfalso.
      assert (a ∈ dead) as Hadead by set_solver.
      destruct Hf as [Hx [Hy [Hz Hw]]]. have Hzz := Hz a Haal.
      have Hzzz := Houtlives (bl, a) Hzz Hadead.
      set_solver.
    }
    assert (bl ⊆ alive) as Hblalive. { unfold inv.map_wf in Hwf. set_solver. }
    
    iMod (delete_bor_state_unborrow γ sn mbs bl al de with "[auth OwnBor]") as "auth". { iFrame. }
    iMod (slice_delete_empty Nbox (↑Nbox ∪ ↑NllftUsr) true (boxmap alive dead mbs) Ptotal P sn with "slice box") as (Ptotal') "[HeqPtotal box]". { set_solver. } { trivial. }
    iMod (slice_insert_full Nbox (↑Nbox ∪ ↑NllftUsr) true (delete sn (boxmap alive dead mbs)) Ptotal' Q with "q box") as (sn2) "[%Hlookup_sn2 [#slice2 box]]". { set_solver. }
    iMod (alloc_bor_state γ sn2 (delete sn mbs) (Borrow al de) with "auth") as "[auth OwnBor2]". { apply (delete_boxmap_implies_delete_original_is_none _ _ _ _ _ Hlookup_sn2). }
    
    assert (delete sn mbs !! sn2 = None) as Hsn2. { apply (delete_boxmap_implies_delete_original_is_none _ _ _ _ _ Hlookup_sn2). }
    
    iDestruct (get_all_modulo_dead_pers with "Modulo") as "[Modulo #Halldeadspers]".
    
    assert (∀ a : lt_atom, a ∈ al → (bl, a) ∈ outlives) as Hoforall. { 
      destruct Hwf as [Ha [Hb [Hc [Hforall Hforall2]]]].
      have Hf := Hforall sn _ Hmbssn. intuition.
    }
    
    iDestruct (bi.later_mono _ _ (llft_vs_for_unborrow_end alive dead outlives mbs mprops bl al de sn sn2 P Q Hmbssn Hsn2 Hoforall Hal Hde swell_al) with "[vs qvs]") as "vs".
    { iFrame. iNext.
      iDestruct (agree_slice_with_map mbs mprops sn _ P with "[]") as "EqSlice"; trivial.
      { apply Hmbssn. } { iFrame "#". } iFrame "EqSlice". iFrame "Halldeadspers".
    }
    
    iModIntro. iExists sn2. iFrame "OwnBor2". iFrame "slice2". iFrame "Modulo".
    iSplitL. 2: { iPureIntro; trivial. }
    iNext.
    iExists (<[sn2:=Borrow al de]> (delete sn mbs)).
    iExists (<[sn2:=Q]> (delete sn mprops)).
    iExists (Q ∗ Ptotal')%I.
    iExists outlives.
    iFrame "auth". iFrame "outlives".
    iSplitL "box". {
      rewrite boxmap_insert_Borrow.
      rewrite boxmap_delete.
      rewrite bool_decide_eq_true_2. { iFrame. } split; trivial.
    }
    iFrame "vs".
    
    assert (al ∪ de ⊆ alive ∪ dead) as Hwfalde. {
      destruct Hwf as [Ha [Hb [Hc [Hforall Hforall2]]]].
      apply (Hforall sn (Unborrow bl al de) Hmbssn).
    }

    iSplitL. { iPureIntro. 
      split. {
        rewrite dom_insert_L. rewrite dom_insert_L.
        rewrite dom_delete_L. rewrite dom_delete_L. rewrite Hdom. trivial.
      }
      split.
      { apply map_wf_insert; trivial.
        apply (map_wf_delete_unborrow alive dead blocked bl al de); trivial.
      }
      trivial.
    }
    iApply big_sepM_insert_1. iFrame "slice2".
    rewrite big_sepM_forall. rewrite big_sepM_forall. iIntros (x R) "%Dm".
    iApply "slices". iPureIntro. rewrite lookup_delete_Some in Dm. intuition.
  Qed.
  
          
  Lemma inner_unborrow_end_at_same_idx alive dead blocked sn bl al de P :
    swell_set al →
    swell_set de →
    (▷ inner_inv γ γo alive dead blocked)
        ∗ OwnBorState γ sn (Unborrow bl al de)
        ∗ slice Nbox sn P
        ∗ (▷ P)
        ={↑Nbox}=∗
          (▷ inner_inv γ γo alive dead (blocked ∖ bl))
          ∗ OwnBorState γ sn (Borrow al de)
          ∗ ⌜bl ⊆ blocked⌝
        .
  Proof using invGS_gen0 Σ γ γd γo.
    iIntros (swell_al swell_de) "[Inv [OwnBor [#slice q]]]".
    unfold inner_inv.
    iDestruct "Inv" as (mbs mprops Ptotal outlives) "[>auth [>Modulo [box [vs [>%pures [#slices >outlives]]]]]]".
    destruct pures as [Hdom [Hwf Houtlives]].
    iDestruct (agree_bor_state_unborrow γ sn mbs bl al de with "[auth OwnBor]") as "%Hmbssn". { iFrame. }
    assert (boxmap alive dead mbs !! sn = Some false) as Hboxmapsn. {
      unfold boxmap. rewrite lookup_fmap. rewrite Hmbssn. trivial.
    }
    assert (bl ⊆ blocked) as Hbl. {
      destruct Hwf as [Ha [Hb [Hc [Hforall Hforall2]]]].
      have Hf := Hforall sn _ Hmbssn. intuition.
    }
    assert (¬(de ## dead)) as Hde. {
      destruct Hwf as [Ha [Hb [Hc [Hforall Hforall2]]]].
      have Hf := Hforall sn _ Hmbssn. intuition.
    }
    assert (al ⊆ alive) as Hal. {
      destruct Hwf as [Ha [Hb [Hc [Hforall Hforall2]]]].
      have Hf := Hforall sn _ Hmbssn. intros a Haal.
      destruct (decide (a ∈ alive)) as [Hin|Hout]; trivial. exfalso.
      assert (a ∈ dead) as Hadead by set_solver.
      destruct Hf as [Hx [Hy [Hz Hw]]]. have Hzz := Hz a Haal.
      have Hzzz := Houtlives (bl, a) Hzz Hadead.
      set_solver.
    }
    assert (bl ⊆ alive) as Hblalive. { unfold inv.map_wf in Hwf. set_solver. }
    
    iMod (slice_fill Nbox (↑Nbox) true (boxmap alive dead mbs) sn Ptotal P with "slice q box")
        as "box". { set_solver. } { trivial. }
    (*iMod (slice_delete_empty Nbox (↑Nbox) true (boxmap alive dead mbs) Ptotal P sn with "slice box") as (Ptotal') "[HeqPtotal box]". { set_solver. } { trivial. }
    iMod (slice_insert_full Nbox (↑Nbox) true (delete sn (boxmap alive dead mbs)) Ptotal' Q with "q box") as (sn2) "[%Hlookup_sn2 [#slice2 box]]". { set_solver. }*)
    (*iMod (alloc_bor_state γ sn2 (delete sn mbs) (Borrow al de) with "auth") as "[auth OwnBor2]". { apply (delete_boxmap_implies_delete_original_is_none _ _ _ _ _ Hlookup_sn2). }*)
    
    iMod (update_bor_state_unborrow_lts γ sn mbs dead bl al de (Borrow al de) with "[Modulo auth OwnBor]") as "[Modulo [auth OwnBor]]". { iFrame. }
    
    iDestruct (get_all_modulo_dead_pers with "Modulo") as "[Modulo #Halldeadspers]".
    
    assert (∀ a : lt_atom, a ∈ al → (bl, a) ∈ outlives) as Hoforall. { 
      destruct Hwf as [Ha [Hb [Hc [Hforall Hforall2]]]].
      have Hf := Hforall sn _ Hmbssn. intuition.
    }
    
    iDestruct (bi.later_mono _ _ (llft_vs_for_unborrow_end_at_same_idx alive dead outlives mbs mprops bl al de sn P Hmbssn Hoforall Hal Hde swell_al) with "[vs]") as "vs".
    { iFrame. iNext.
      iDestruct (agree_slice_with_map mbs mprops sn _ P with "[]") as "EqSlice"; trivial.
      { apply Hmbssn. } { iFrame "#". } iFrame "EqSlice". iFrame "Halldeadspers".
    }
    
    iModIntro. iFrame "OwnBor". iFrame "Modulo".
    iSplitL. 2: { iPureIntro; trivial. }
    iNext.
    iExists (<[sn:=Borrow al de]> mbs).
    iExists (<[sn:=P]> (delete sn mprops)).
    iExists Ptotal.
    iExists outlives.
    iFrame "auth". iFrame "outlives".
    iSplitL "box". {
      rewrite boxmap_insert_Borrow.
      rewrite bool_decide_eq_true_2. { iFrame. } split; trivial.
    }
    iFrame "vs".
    
    assert (al ∪ de ⊆ alive ∪ dead) as Hwfalde. {
      destruct Hwf as [Ha [Hb [Hc [Hforall Hforall2]]]].
      apply (Hforall sn (Unborrow bl al de) Hmbssn).
    }

    iSplitL. { iPureIntro. 
      split. {
        rewrite dom_insert_L. rewrite dom_insert_L.
        rewrite dom_delete_L. rewrite Hdom. trivial.
        apply set_eq. intros x. destruct (decide (x = sn)); set_solver.
      }
      split.
      { replace (<[sn:=Borrow al de]> mbs) with (<[sn:=Borrow al de]> (delete sn mbs)).
        { apply map_wf_insert; trivial.
          apply (map_wf_delete_unborrow alive dead blocked bl al de); trivial. }
        rewrite insert_delete_insert. trivial.
      }
      trivial.
    }
    iApply big_sepM_insert_1. iFrame "slice".
    rewrite big_sepM_forall. rewrite big_sepM_forall. iIntros (x R) "%Dm".
    iApply "slices". iPureIntro. rewrite lookup_delete_Some in Dm. intuition.
  Qed.
  
  Lemma inner_unborrow_atomic alive dead blocked outlives sn bl al de P :
    (al ⊆ alive) →
    ¬(de ## dead) →
    (∀ (k : lt_atom) , k ∈ al → (bl, k) ∈ outlives) →
    (▷ inner_inv γ γo alive dead blocked)
        ∗ Outlives γo outlives
        ∗ OwnBorState γ sn (Borrow al de)
        ∗ slice Nbox sn P
        ={↑Nbox,∅}=∗ ▷ P ∗ ∀ Q, 
        (▷ (▷ Q ∗ (∃ k , ⌜ k ∈ bl ⌝ ∗ Dead γ k) ={↑NllftUsr ∪ ↑NllftUsr2}=∗ ▷ P)) ∗ (▷ Q)
          ={∅,↑Nbox}=∗ ∃ sn2,
    (▷ inner_inv γ γo alive dead blocked)
        ∗ Outlives γo outlives
        ∗ OwnBorState γ sn2 (Borrow al de)
        ∗ slice Nbox sn2 Q
        .
  Proof using invGS_gen0 Σ γ γd γo.
    intros Hal Hde Houtlives.
    iIntros "[Inv [Outlives [OwnBor #slice]]]".
    unfold inner_inv.
    iDestruct "Inv" as (mbs mprops Ptotal outlives') "[>auth [>Modulo [box [vs [>%pures [#slices >outlives]]]]]]".
    iDestruct (outlives_agree with "[outlives Outlives]") as "%Hoeq". { iFrame. }
    subst outlives'.
    
    assert (al ## dead) as Hdisj_al_dead. { unfold inv.map_wf in pures; set_solver. }
    
    iDestruct (agree_bor_state_borrow_lts γ sn mbs dead al de Hdisj_al_dead
        with "[Modulo auth OwnBor]") as (de') "[%Hmbssn %Hrel_de]". { iFrame. }
        
    assert (boxmap alive dead mbs !! sn = Some true) as Hboxmaptrue.
    { unfold boxmap. rewrite lookup_fmap. rewrite Hmbssn. simpl.
      f_equiv. rewrite bool_decide_eq_true. split; trivial.
      destruct (decide (de = de')); intuition. subst de'; intuition. }
    
    iMod (slice_delete_full (Nbox) (↑Nbox) true (boxmap alive dead mbs) Ptotal P sn with "slice box") as (Ptotal') "[P [#Ptotal_eq box]]". { set_solver. } { trivial. }
    
    iMod (fupd_mask_subseteq ∅) as "Upd". { set_solver. }
    iModIntro. iFrame "P". iIntros (Q) "[qvs q]". iMod "Upd".
    
    iMod (slice_insert_full Nbox (↑Nbox) true (delete sn (boxmap alive dead mbs)) Ptotal' Q with "q box") as (sn2) "[%Hlookup_sn2 [#slice2 box]]". { set_solver. }
    
    assert (delete sn mbs !! sn2 = None) as Hsn2. { apply (delete_boxmap_implies_delete_original_is_none _ _ _ _ _ Hlookup_sn2). }
    
    destruct pures as [Hdom [Hwf Hoc]].
    have swell_al := swell_set_of_map_wf _ _ _ _ _ _ _ _ Hwf Hmbssn.
    have swell_de' := swell_set_of_map_wf_de _ _ _ _ _ _ _ _ Hwf Hmbssn.
    
    assert (¬(de' ## dead)) as Hde'. {
      destruct Hwf as [Ha [Hb [Hc [Hforall Hforall2]]]].
      have Hf := Hforall sn _ Hmbssn. intuition. subst de'. intuition.
    }
    
    iMod (delete_bor_state_borrow_lts γ sn mbs dead al de with "[Modulo auth OwnBor]") as "[Modulo auth]"; trivial. { iFrame. }
    
    iMod (alloc_bor_state2 γ sn2 (delete sn mbs) dead al de de' with "[Modulo auth]") as "[Modulo [auth OwnBor2]]"; trivial. { iFrame. }
    
    iDestruct (get_all_modulo_dead_pers with "Modulo") as "[Modulo #Halldeadspers]".
    
    iDestruct (bi.later_mono _ _ (llft_vs_for_unborrow_end_atomic alive dead outlives mbs mprops bl al de' sn sn2 P Q Hmbssn Hsn2 Houtlives Hal Hde' swell_al) with "[vs qvs]") as "vs".
    { iFrame. iNext.
      iDestruct (agree_slice_with_map mbs mprops sn _ P with "[]") as "EqSlice"; trivial.
      { apply Hmbssn. } { iFrame "#". } iFrame "EqSlice". iFrame "Halldeadspers".
    }
    
    iModIntro. iExists sn2.
    iFrame "OwnBor2". iFrame "slice2". iFrame "Outlives". iFrame "outlives".
    iFrame "Modulo".
    iExists (<[sn2:=Borrow al de']> (delete sn mbs)).
    iExists (<[sn2:=Q]> (delete sn mprops)).
    iExists (Q ∗ Ptotal')%I.
    iNext. iFrame "auth".
    iSplitL "box". {
      rewrite boxmap_insert_Borrow.
      rewrite boxmap_delete.
      rewrite bool_decide_eq_true_2. { iFrame. } split; trivial.
    }
    iFrame "vs".
    
    assert (al ∪ de' ⊆ alive ∪ dead) as Hwfalde. {
      destruct Hwf as [Ha [Hb [Hc [Hforall Hforall2]]]].
      apply (Hforall sn (Borrow al de') Hmbssn).
    }

    iSplitL. { iPureIntro. 
      split. {
        rewrite dom_insert_L. rewrite dom_insert_L.
        rewrite dom_delete_L. rewrite dom_delete_L. rewrite Hdom. trivial.
      }
      split.
      { apply map_wf_insert; trivial.
        apply (map_wf_delete alive dead blocked outlives mbs sn); trivial.
      }
      trivial.
    }
    iApply big_sepM_insert_1. iFrame "slice2".
    rewrite big_sepM_forall. rewrite big_sepM_forall. iIntros (x R) "%Dm".
    iApply "slices". iPureIntro. rewrite lookup_delete_Some in Dm. intuition.
  Qed.

  
  Lemma outer_unborrow_start alive dead blocked outlives sn (bl al de : gset lt_atom) P :
    (al ⊆ alive) →
    (de ⊆ alive ∪ dead) →
    ¬(de ## dead) →
    (bl ## blocked) →
    (bl ⊆ alive) →
    (∀ (k : lt_atom) , k ∈ al → (bl, k) ∈ outlives) →
      Delayed γd None
        ∗ (▷ outer_inv γ γo γd alive dead blocked) ∗ Outlives γo outlives
        ∗ OwnBorState γ sn (Borrow al de)
        ∗ slice Nbox sn P
      ⊢ |={↑Nbox}=> 
      Delayed γd None
        ∗ (▷ outer_inv γ γo γd alive dead (blocked ∪ bl))
        ∗ Outlives γo outlives
        ∗ OwnBorState γ sn (Unborrow bl al de)
        ∗ (▷ P).
  Proof.
    intros Hal Hdewf Hde Hbl Hblal Ho. iIntros "[Delayed [Inv H]]".
    iDestruct "Inv" as (opt_k) "[>D Inv]".
    iDestruct (delayed_agree with "[D Delayed]") as "%Heq". { iFrame "D Delayed". }
    subst opt_k.
    iMod (inner_unborrow_start alive dead blocked outlives sn bl al de P Hal Hdewf Hde Hbl Hblal Ho with "[H Inv]") as "[Inv H]". { iFrame. }
    iModIntro. iFrame "Delayed H". iExists None. iFrame.
  Qed.
  
  Lemma outer_unborrow_end alive dead blocked sn bl al de P Q :
      swell_set al →
      swell_set de →
      Delayed γd None
        ∗ (▷ outer_inv γ γo γd alive dead blocked)
        ∗ OwnBorState γ sn (Unborrow bl al de)
        ∗ slice Nbox sn P
        ∗ (▷ (▷ Q ∗ (∃ k , ⌜ k ∈ bl ⌝ ∗ Dead γ k) ={↑NllftUsr ∪ ↑NllftUsr2}=∗ ▷ P))
        ∗ (▷ Q)
        ={↑Nbox ∪ ↑NllftUsr}=∗ ∃ sn2,
      Delayed γd None
        ∗ (▷ outer_inv γ γo γd alive dead (blocked ∖ bl))
        ∗ OwnBorState γ sn2 (Borrow al de)
        ∗ slice Nbox sn2 Q
        ∗ ⌜bl ⊆ blocked⌝
        .
  Proof.
    iIntros (swell_al swell_de) "[Delayed [Inv H]]".
    iDestruct "Inv" as (opt_k) "[>D Inv]".
    iDestruct (delayed_agree with "[D Delayed]") as "%Heq". { iFrame "D Delayed". }
    subst opt_k.
    iMod (inner_unborrow_end alive dead blocked sn bl al de P Q with "[H Inv]") as (sn2) "[Inv H]". { trivial. } { trivial. } { iFrame. }
    iModIntro. iFrame "Delayed H". iExists None. iFrame.
  Qed.
   
  Lemma outer_unborrow_end_at_same_idx alive dead blocked sn bl al de P :
      swell_set al →
      swell_set de →
      Delayed γd None
        ∗ (▷ outer_inv γ γo γd alive dead blocked)
        ∗ OwnBorState γ sn (Unborrow bl al de)
        ∗ slice Nbox sn P
        ∗ (▷ P)
        ={↑Nbox}=∗
      Delayed γd None
        ∗ (▷ outer_inv γ γo γd alive dead (blocked ∖ bl))
        ∗ OwnBorState γ sn (Borrow al de)
        ∗ ⌜bl ⊆ blocked⌝
        .
  Proof.
    iIntros (swell_al swell_de) "[Delayed [Inv H]]".
    iDestruct "Inv" as (opt_k) "[>D Inv]".
    iDestruct (delayed_agree with "[D Delayed]") as "%Heq". { iFrame "D Delayed". }
    subst opt_k.
    iMod (inner_unborrow_end_at_same_idx alive dead blocked sn bl al de P with "[H Inv]") as "[Inv H]". { trivial. } { trivial. } { iFrame. }
    iModIntro. iFrame "Delayed H". iExists None. iFrame.
  Qed.

End FullBorrows.
