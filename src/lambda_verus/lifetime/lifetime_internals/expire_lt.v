Require Import guarding.lib.boxes.
Require Import lrust.lifetime.lifetime_internals.ra.
Require Import lrust.lifetime.lifetime_internals.inv.
Require Import lrust.lifetime.lifetime_internals.new_lt.
Require Import lrust.lifetime.lifetime_internals.unborrow.

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
 
  Lemma inv_get_alive_dead_disj alive dead blocked
    : inner_inv γ γd alive dead blocked ⊢ ⌜alive ## dead⌝.
  Proof.
    iIntros "Inv". iDestruct "Inv" as (mbs mprops Ptotal outlives) "[auth [modulo [box [vs [%pures [#slices outlives]]]]]]".
    unfold inv.map_wf in pures. intuition.
  Qed.
  
  Lemma inv_get_outlives_condition alive dead blocked outlives
    : inner_inv γ γo alive dead blocked ∗ Outlives γo outlives ⊢ 
      ⌜∀ o , o ∈ outlives → o.1 ⊆ alive ∪ dead ∧ o.2 ∈ alive ∪ dead⌝.
  Proof.
    iIntros "[Inv Outlives]". iDestruct "Inv" as (mbs mprops Ptotal outlives') "[auth [modulo [box [vs [%pures [#slices outlives]]]]]]".
    iDestruct (outlives_agree with "[outlives Outlives]") as "%Hoeq". { iFrame. }
    subst outlives'. unfold inv.map_wf in pures. intuition.
  Qed.
  
  Lemma inv_get_outlives_consistent alive dead blocked outlives
    : inner_inv γ γo alive dead blocked ∗ Outlives γo outlives ⊢ 
      ⌜outlives_consistent dead outlives⌝.
  Proof.
    iIntros "[Inv Outlives]". iDestruct "Inv" as (mbs mprops Ptotal outlives') "[auth [modulo [box [vs [%pures [#slices outlives]]]]]]".
    iDestruct (outlives_agree with "[outlives Outlives]") as "%Hoeq". { iFrame. }
    subst outlives'. intuition.
  Qed.
  
  Lemma lemma_set6 (al' dd' alive dead : gset lt_atom) :
    al'  ⊆ alive ∪ dead →
    al' ## dead →
    al' ⊆ alive. Proof. set_solver. Qed.
    
  
  Lemma outlives_consistent_instant_kill alive dead blocked outlives mbs k :
    (k ∉ alive ∪ dead) →
    inv.map_wf alive dead blocked outlives mbs →
    outlives_consistent dead outlives →
    outlives_consistent (dead ∪ {[k]}) outlives.
  Proof.
    intros Hk Hwf Hoc o. 
    destruct Hwf as [Ha [Hb [Hc [Hforall [Hforall2 Hforall3]]]]].
    have H1 := Hoc o. have H2 := Hforall3 o. set_solver.
  Qed.
  
  Lemma inner_instant_kill_lt alive dead blocked k :
    (k ∉ alive ∪ dead) →
    Dead γ k ∗
    (▷ inner_inv γ γo alive dead blocked)
      ={∅}=∗
    (▷ inner_inv γ γo alive (dead ∪ {[k]}) blocked).
  Proof.
    intros Hk_fresh.
    iIntros "[Dead Inv]".
    unfold inner_inv.
    iDestruct "Inv" as (mbs mprops Ptotal outlives) "[>auth [>Modulo [box [vs [>%pures [#slices >outlives]]]]]]".
    
    iMod (modulo_dead_new γ k dead with "[Dead Modulo]") as "Modulo".
      { iFrame. }
    
    iDestruct (llfb_fb_vs_for_new_lt' γ alive dead blocked outlives alive dead mbs mprops k with "vs") as "vs"; trivial.
      { intuition. }
      { unfold inv.map_wf in pures. intuition. }
      { set_solver. }
      { set_solver. }
    
    iModIntro. iNext.
    iExists mbs. iExists mprops. iExists Ptotal. iExists outlives.
    iFrame "auth". iFrame "Modulo".
    destruct pures as [Hdom [Hwf Hoc]].
    iSplitL "box". {
      replace (boxmap alive (dead ∪ {[k]}) mbs) with (boxmap alive dead mbs). { iFrame. }
      unfold boxmap. apply map_eq. intros sn.
      rewrite lookup_fmap. rewrite lookup_fmap.
      destruct (mbs !! sn) as [[al de|bl al de]|] eqn:Hmbssn.
      - rewrite Hmbssn. simpl. f_equiv. apply bool_decide_equiv.
        destruct Hwf as [Ha [Hb [Hc [Hforall Hforall2]]]].
        have Hf2 := Hforall sn (Borrow al de). set_solver.
      - rewrite Hmbssn. simpl. trivial.
      - rewrite Hmbssn. trivial.
    }
    iFrame "vs".
    iSplitR. { iPureIntro.
      split; trivial. split; trivial.
      { apply map_wf_new_lt_dead; trivial. }
      apply (outlives_consistent_instant_kill alive dead blocked outlives mbs k); trivial.
    }
    iFrame "slices". iFrame "outlives".
  Qed.
  
  Lemma outlives_consistent_preserved_on_kill outlives dead k :
      (∀ other : gset lt_atom, (other, k) ∈ outlives → ¬ other ## (dead ∪ {[k]})) →
      (outlives_consistent dead outlives) →
      outlives_consistent (dead ∪ {[k]}) outlives.
  Proof.
    unfold outlives_consistent. intros Ho Hoc o Ho_in Ho2_dead.
    have Hoc2 := Hoc o. have Ho2 := Ho (o.1). set_solver.
  Qed.
  
  (*Lemma big_opM_imap {M: ofe} `{Countable K} {A B : Type} (h : A → B) (f : K → B → M) (m : gmap K A) : 
    ([^o map] k↦y ∈ h <$> m, f k y) ≡ ([^o map] k↦y ∈ m, f k (h y)).
  Proof.
    rewrite big_opM_unseal /big_opM_def map_to_list_fmap big_opL_fmap.
    by apply big_opL_proper=> ? [??].
  Qed. *)
  
  Lemma big_sepM_imap `{Countable K} {A B} (f : K → A → option B) (Φ : K → B → iProp Σ) (m : gmap K A) :
    ([∗ map] k↦y ∈ map_imap f m, Φ k y) ⊣⊢ ([∗ map] k↦y ∈ m, from_option (Φ k) emp (f k y)).
  Proof. 
    induction m as [|i x' m Hl IH] using map_ind.
    - rewrite map_imap_empty. rewrite big_sepM_empty. rewrite big_sepM_empty. trivial.
    - rewrite map_imap_insert. destruct (f i x') eqn:Hfix.
      + rewrite big_sepM_insert.
        * rewrite big_sepM_insert; trivial. rewrite IH. unfold from_option.
          rewrite Hfix. trivial.
        * rewrite map_lookup_imap. unfold mbind, option_bind. rewrite Hl. trivial.
      + replace (delete i (map_imap f m)) with (map_imap f m).
        * rewrite big_sepM_insert; trivial. rewrite Hfix. rewrite IH. unfold from_option.
          iSplit. { iIntros "A". iFrame. } { iIntros "[A B]". iFrame. }
        * rewrite <- map_imap_delete. f_equal. rewrite delete_notin; trivial.
  Qed.
  
  (*Lemma big_sepM_mono2 `{Countable K} {A B} (Φ : K → A → iProp Σ) (Ψ : K → B → iProp Σ) (m : gmap K A) (m2: gmap K B) :
    (∀ k x, m2 !! k = Some x → ∃ y, (m !! k = Some y) ∧ (Φ k y ⊢ Ψ k x)) → 
    ([∗ map] k ↦ x ∈ m, Φ k x) ⊢ [∗ map] k ↦ x ∈ m2, Ψ k x. *)
  
  Lemma box_take_all_invalidate alive dead k mbs mprops Ptotal :
    (∀ sn bl al de , mbs !! sn = Some (Unborrow bl al de) → k ∉ al) →
    (dom mbs = dom mprops) →
    box Nbox (boxmap alive dead mbs) Ptotal
        ∗ ([∗ map] sn↦Q ∈ mprops, slice Nbox sn Q)
    ={↑Nbox}=∗
    box Nbox (boxmap (alive ∖ {[k]}) dead mbs) Ptotal
        ∗ ▷ full_borrows_invalidated_via alive dead k mbs mprops.
  Proof.
    intros Hunb Hdom. iIntros "[box #slices]".
    unfold full_borrows_invalidated_via. unfold borrow_sum.
    iDestruct (slice_empty_many Nbox (↑Nbox) false (boxmap alive dead mbs) Ptotal
      (map_imap (λ sn bs, (if invalidated alive dead k bs
                            then Some (match mprops !! sn with
                                 | Some P => P
                                 | None => True%I
                                 end)
                            else None)) mbs) with "[] box") as "X".
    { set_solver. }
    { intros sn Q Hm. rewrite map_lookup_imap in Hm.
      unfold mbind, option_bind in Hm.
      destruct (mbs !! sn) eqn:Hmbs.
      - rewrite Hmbs in Hm. unfold boxmap. destruct (invalidated alive dead k b) eqn:Hinv.
        + rewrite lookup_fmap. rewrite Hmbs. simpl. f_equiv. unfold invalidated in Hinv.
          destruct b as [|bl al de].
          * rewrite bool_decide_eq_true. rewrite bool_decide_eq_true in Hinv. intuition.
          * rewrite bool_decide_eq_true in Hinv. have Hu := Hunb sn bl al de. set_solver.
        + discriminate.
     - rewrite Hmbs in Hm. discriminate.
   }
   { iIntros (sn Q) "%Hm". rewrite (big_sepM_delete _ _ sn Q);
      first by iDestruct "slices" as "[slice _]"; iFrame.
     rewrite map_lookup_imap in Hm.
     unfold mbind, option_bind in Hm. destruct (mbs !! sn) eqn:Hmbs.
     - rewrite Hmbs in Hm. destruct (invalidated alive dead k b) eqn:Hinv.
      + destruct (mprops !! sn) eqn:Hmprops.
        * rewrite Hmprops in Hm. rewrite Hmprops. trivial.
        * assert (sn ∈ dom mbs) as X. { eapply elem_of_dom_2; apply Hmbs. }
          setoid_rewrite <- (not_elem_of_dom mprops) in Hmprops. set_solver.
      + discriminate.
     - rewrite Hmbs in Hm. discriminate.
   }
   iMod "X" as "[H box]". iModIntro.
   iSplitL "box". {
      replace ((boxmap (alive ∖ {[k]}) dead mbs)) with (((λ _ : iProp Σ, false) <$>
                      map_imap
                        (λ (sn : gname) (bs : BorState),
                           if invalidated alive dead k bs
                           then Some match mprops !! sn with
                                     | Some P => P
                                     | None => True
                                     end
                           else None) mbs) ∪ boxmap alive dead mbs)%I.
       { iFrame "box". }
       apply map_eq. intros sn.
       destruct (mbs !! sn) as [bs|] eqn:Hmbssn.
        - rewrite lookup_union. rewrite lookup_fmap. rewrite map_lookup_imap.
          rewrite lookup_fmap. rewrite lookup_fmap.
          rewrite Hmbssn. simpl.
          destruct bs as [al de|bl al de].
          + destruct (invalidated alive dead k (Borrow al de)) eqn:Hinv.
            * simpl. unfold union, option_union, union_with, option_union_with. 
              f_equiv. unfold invalidated in Hinv. rewrite bool_decide_eq_true in Hinv.
              symmetry. rewrite bool_decide_eq_false. set_solver.
            * unfold union, option_union, union_with, option_union_with. simpl. f_equiv.
              apply bool_decide_equiv. rewrite bool_decide_eq_false in Hinv.
              set_solver.
          + destruct (invalidated alive dead k (Unborrow bl al de)) eqn:Hinv.
            * trivial.
            * trivial.
        - rewrite lookup_union. rewrite lookup_fmap. rewrite map_lookup_imap.
          rewrite lookup_fmap. rewrite lookup_fmap.
          rewrite Hmbssn. simpl. trivial.
     }
  rewrite big_sepM_imap.
  iDestruct (big_sepM_mono with "H") as "H". 2: { iFrame "H". }
  intros sn bs Hmbssn. simpl. unfold from_option.
  destruct (invalidated alive dead k bs); trivial.
  Qed.
  
  Lemma box_put_all_revalidate alive dead k mbs (mprops : gmap slice_name (iProp Σ)) Ptotal :
    (dom mbs = dom mprops) →
    box Nbox (boxmap (alive ∖ {[k]}) dead mbs) Ptotal
        ∗ ▷ full_borrows_revalidated_via alive dead k mbs mprops
        ∗ ([∗ map] sn↦Q ∈ mprops, slice Nbox sn Q)
    ={↑Nbox}=∗
    box Nbox (boxmap (alive ∖ {[k]}) (dead ∪ {[k]}) mbs) Ptotal.
  Proof.
    intros Hdom. iIntros "[box [reval #slices]]".
    unfold full_borrows_revalidated_via. unfold borrow_sum.
    iDestruct (slice_fill_many Nbox (↑Nbox) false (boxmap (alive ∖ {[k]}) dead mbs) Ptotal
      (map_imap (λ sn bs, (if revalidated alive dead k bs
                            then Some (match mprops !! sn with
                                 | Some P => P
                                 | None => True%I
                                 end)
                            else None)) mbs) with "[] [reval] box") as "X".
    { set_solver. }
    { intros sn Q Hm. rewrite map_lookup_imap in Hm.
      unfold mbind, option_bind in Hm.
      destruct (mbs !! sn) eqn:Hmbs.
      - rewrite Hmbs in Hm. unfold boxmap. destruct (revalidated alive dead k b) eqn:Hinv.
        + rewrite lookup_fmap. rewrite Hmbs. simpl. f_equiv. unfold revalidated in Hinv.
          destruct b as [al de|bl al de].
          * rewrite bool_decide_eq_false. rewrite bool_decide_eq_true in Hinv. intuition.
          * trivial.
        + discriminate.
     - rewrite Hmbs in Hm. discriminate.
   }
   { iIntros (sn Q) "%Hm". rewrite (big_sepM_delete _ _ sn Q);
      first by iDestruct "slices" as "[slice _]"; iFrame.
     rewrite map_lookup_imap in Hm.
     unfold mbind, option_bind in Hm. destruct (mbs !! sn) eqn:Hmbs.
     - rewrite Hmbs in Hm. destruct (revalidated alive dead k b) eqn:Hinv.
      + destruct (mprops !! sn) eqn:Hmprops.
        * rewrite Hmprops in Hm. trivial.
        * assert (sn ∈ dom mbs) as X. { eapply elem_of_dom_2; apply Hmbs. }
          rewrite <- not_elem_of_dom in Hmprops. set_solver.
      + discriminate.
     - rewrite Hmbs in Hm. discriminate.
   }
   {
      rewrite big_sepM_imap.
      iDestruct (big_sepM_mono with "reval") as "reval". 2: { iFrame "reval". }
      intros sn bs Hmbssn. simpl. unfold from_option.
      destruct (revalidated alive dead k bs); trivial.
   }
   replace (boxmap (alive ∖ {[k]}) (dead ∪ {[k]}) mbs) with
      ((((λ _ : iProp Σ, true) <$>
                      map_imap
                        (λ (sn : gname) (bs : BorState),
                           if revalidated alive dead k bs
                           then Some match mprops !! sn with
                                     | Some P => P
                                     | None => True%I
                                     end
                           else None) mbs) ∪ boxmap (alive ∖ {[k]}) dead mbs)).
       { iFrame "X". }
    apply map_eq. intros sn.
    destruct (mbs !! sn) as [bs|] eqn:Hmbssn.
    - rewrite lookup_union. rewrite lookup_fmap. rewrite map_lookup_imap.
      rewrite lookup_fmap. rewrite lookup_fmap.
      rewrite Hmbssn. simpl.
      destruct bs as [al de|bl al de].
      + destruct (revalidated alive dead k (Borrow al de)) eqn:Hinv.
        * simpl. unfold union at 1, option_union, union_with, option_union_with. 
          f_equiv. unfold revalidated in Hinv. rewrite bool_decide_eq_true in Hinv.
          symmetry. rewrite bool_decide_eq_true. split; intuition.
          set_solver.
        * unfold union at 1, option_union, union_with, option_union_with. simpl. f_equiv.
          apply bool_decide_equiv. rewrite bool_decide_eq_false in Hinv.
          set_solver.
      + destruct (revalidated alive dead k (Unborrow bl al de)) eqn:Hinv.
        * unfold revalidated in Hinv. discriminate.
        * trivial.
    - rewrite lookup_union. rewrite lookup_fmap. rewrite map_lookup_imap.
      rewrite lookup_fmap. rewrite lookup_fmap.
      rewrite Hmbssn. simpl. trivial.
  Qed.
  
  Local Instance dead_pers γ1 k : Persistent (Dead γ1 k).
  Proof. apply own_core_persistent. unfold CoreId. trivial. Qed.
  
  Local Instance modulo_dead_pers γ1 k : Persistent (ModuloDeadPers γ1 k).
  Proof. apply own_core_persistent. unfold CoreId. trivial. Qed.
  
  Lemma inner_kill_lt alive dead blocked outlives k :
    (k ∈ alive) →
    (k ∉ blocked) →
    (∀ other , (other, k) ∈ outlives → ¬(other ## (dead ∪ {[k]}))) →
    (▷ inner_inv γ γo alive dead blocked) ∗ Outlives γo outlives ∗ Dead γ k
      ={↑Nbox ∪ ↑NllftUsr ∪ ↑NllftUsr2}=∗ ▷ |={↑Nbox ∪ ↑NllftUsr ∪ ↑NllftUsr2}=>
    (▷ inner_inv γ γo (alive ∖ {[k]}) (dead ∪ {[k]}) blocked) ∗ Outlives γo outlives.
  Proof.
    intros Hk_alive Hk_not_blocked Houtlives_okay.
    iIntros "[Inv [Outlives #Dead]]".
    iDestruct "Inv" as (mbs mprops Ptotal outlives') "[>auth [>Modulo [box [vs [>%pures [#slices >outlives]]]]]]".
    iDestruct (outlives_agree with "[outlives Outlives]") as "%Hoeq". { iFrame. }
    subst outlives'.
    
    iMod (modulo_dead_new γ k dead with "[Dead Modulo]") as "Modulo". { iFrame. iFrame "#". }
    iDestruct (get_all_modulo_dead_pers γ with "Modulo") as "[Modulo #alldeadpers]".
    
    destruct pures as [Hp [Hwf Hrest]]. 
    
    iModIntro. iNext.
    
    iDestruct (box_take_all_invalidate alive dead k mbs mprops Ptotal with "[box]") as "A".  
    { intros sn bl al de Hmbssn Hkal. 
      destruct Hwf as [Ha [Hb [Hc [Hforall [Hforall2 Hforall3]]]]].
      have Hf := Hforall sn (Unborrow bl al de) Hmbssn.
      destruct Hf as [Hx [Hy [Hz Hw]]].
      have Hzk := Hz k Hkal. set_solver. }
    { trivial. }
    { iFrame. iFrame "slices". }
    iMod (fupd_mask_mono with "A") as "[box inval]". { set_solver. }
    
    rewrite future_vs_def. iDestruct ("vs" $! k with "[] []") as "[_ vs]".
    {
      iPureIntro. split; trivial.
      apply outlives_consistent_preserved_on_kill; trivial.
    }
    {
        iApply "alldeadpers". iPureIntro. set_solver.
    }
    iDestruct ("vs" with "inval") as "vs".
    iMod (fupd_mask_mono _ (↑Nbox ∪ ↑NllftUsr ∪ ↑NllftUsr2) with "vs") as "[reval vs]". {
      set_solver.
    }
   
    iDestruct (box_put_all_revalidate alive dead k mbs mprops Ptotal with "[box reval]") as "box".
      { trivial. } { iFrame.  iFrame "slices". }
    iMod (fupd_mask_mono with "box") as "box". { set_solver. }

    iModIntro. iSplitR "Outlives". 2: { iFrame. }
    iNext. unfold inner_inv. iExists mbs. iExists mprops. iExists Ptotal.
    iExists outlives. iFrame. iFrame "slices". iPureIntro.
   
    split; trivial. split.
    { apply map_wf_preserved_on_kill; trivial. }
    { apply outlives_consistent_preserved_on_kill; trivial. }
  Qed.
  
  Lemma boxmap_unswell_eq alive dead blocked outlives mbs k :
    (¬ swell k) →
    inv.map_wf alive dead blocked outlives mbs →
    boxmap alive dead mbs = boxmap (alive ∖ {[k]}) (dead ∪ {[k]}) mbs.
  Proof.
    intros Hnot Hwf.
    (*destruct Hwf as [Ha [Hb [Hc [Hforall [Hforall2 Hforall3]]]]].*)
    apply map_eq. intros k'. unfold boxmap. do 2 rewrite lookup_fmap.
    destruct (mbs !! k') as [[al de|bl al de]|] eqn:Heq; rewrite Heq.
      - simpl.
        have Hs := swell_set_of_map_wf _ _ _ _ _ _ _ _ Hwf Heq.
        have Hd := swell_set_of_map_wf_de _ _ _ _ _ _ _ _ Hwf Heq.
        assert (k ∉ al) as Hnot_in_al. { intros Hk. apply Hnot. apply Hs. apply Hk. }
        assert (k ∉ de) as Hnot_in_de. { intros Hk. apply Hnot. apply Hd. apply Hk. }
        f_equal. apply bool_decide_ext. set_solver.
      - done.
      - done.
  Qed.
  
  Lemma inner_kill_lt_unswell alive dead blocked outlives k :
    ¬swell k →
    (k ∈ alive) →
    (k ∉ blocked) →
    (∀ other , (other, k) ∈ outlives → ¬(other ## (dead ∪ {[k]}))) →
    (▷ inner_inv γ γo alive dead blocked) ∗ Outlives γo outlives ∗ Dead γ k
      ={↑Nbox}=∗
    (▷ inner_inv γ γo (alive ∖ {[k]}) (dead ∪ {[k]}) blocked) ∗ Outlives γo outlives.
  Proof.
    intros Hnotswell Hk_alive Hk_not_blocked Houtlives_okay.
    iIntros "[Inv [Outlives #Dead]]".
    iDestruct "Inv" as (mbs mprops Ptotal outlives') "[>auth [>Modulo [box [vs [>%pures [#slices >outlives]]]]]]".
    iDestruct (outlives_agree with "[outlives Outlives]") as "%Hoeq". { iFrame. }
    subst outlives'.
    
    iMod (modulo_dead_new γ k dead with "[Dead Modulo]") as "Modulo". { iFrame. iFrame "#". }
    iDestruct (get_all_modulo_dead_pers γ with "Modulo") as "[Modulo #alldeadpers]".
    
    destruct pures as [Hp [Hwf Hrest]]. 
    
    rewrite future_vs_def. iDestruct ("vs" $! k with "[] []") as "[vs _]".
    {
      iPureIntro. split; trivial.
      apply outlives_consistent_preserved_on_kill; trivial.
    }
    {
        iApply "alldeadpers". iPureIntro. set_solver.
    }
    iDestruct ("vs" $! Hnotswell) as "vs".

    iModIntro. iSplitR "Outlives". 2: { iFrame. }
    iNext. unfold inner_inv. iExists mbs. iExists mprops. iExists Ptotal.
    iExists outlives.
    rewrite <- (boxmap_unswell_eq alive dead blocked outlives); trivial.
    iFrame. iFrame "slices". 
    iPureIntro.
    split; trivial. split.
    { apply map_wf_preserved_on_kill; trivial. }
    { apply outlives_consistent_preserved_on_kill; trivial. }
  Qed.
  
  Lemma inner_kill_lt_maybe_swell alive dead blocked outlives k b :
    (swell k → b = true) →
    (k ∈ alive) →
    (k ∉ blocked) →
    (∀ other , (other, k) ∈ outlives → ¬(other ## (dead ∪ {[k]}))) →
    (▷ inner_inv γ γo alive dead blocked) ∗ Outlives γo outlives ∗ Dead γ k
      ={↑Nbox ∪ ↑NllftUsr ∪ ↑NllftUsr2}=∗ ▷?b |={↑Nbox ∪ ↑NllftUsr ∪ ↑NllftUsr2}=>
    (▷ inner_inv γ γo (alive ∖ {[k]}) (dead ∪ {[k]}) blocked) ∗ Outlives γo outlives.
  Proof.
    destruct b.
    - intros _. apply inner_kill_lt.
    - intros Ht. iIntros. iModIntro.
      iApply fupd_mask_mono; last first.
       + iApply inner_kill_lt_unswell; try done. intuition. discriminate.
       + set_solver.
  Qed.
  
  Lemma outer_instant_kill_lt alive dead blocked k :
    (k ∉ alive ∪ dead) →
    Dead γ k ∗ (▷ outer_inv γ γo γd alive dead blocked) ={∅}=∗
    (▷ outer_inv γ γo γd alive (dead ∪ {[k]}) blocked).
  Proof.
    intros Had.
    iIntros "[#Dead Inv]". iDestruct "Inv" as (opt_k) "[>D Inv]".
    destruct opt_k as [[k' alive']|].
    {
      iDestruct "Inv" as "[Inv >Hndead]".
      iDestruct "Hndead" as "%Hndead".
      iMod (inner_instant_kill_lt _ _ blocked k with "[Inv]") as "Inv"; trivial.
      2: { iFrame "Inv". iFrame "Dead". }
      { set_solver. }
      iModIntro. iExists (Some (k', alive')). iSplitL "D". { iFrame. }
      replace ((dead ∖ {[k']} ∪ {[k]})) with ((dead ∪ {[k]}) ∖ {[k']}).
      2: { apply set_eq. intros x. set_solver. }
      iFrame. iPureIntro. set_solver.
    }
    {
      iMod (inner_instant_kill_lt alive dead blocked k with "[Inv]") as "Inv"; trivial.
      { iFrame. iFrame "#". }
      iModIntro. iExists None. iFrame "Inv". iFrame "D".
    }
  Qed.
  
  Lemma outer_kill_lt_step1 alive dead blocked k :
    (k ∈ alive) →
    (k ∉ dead) →
    (▷ outer_inv γ γo γd alive dead blocked) ∗ Delayed γd None
      ={↑Nbox}=∗
    (▷ outer_inv γ γo γd (alive ∖ {[k]}) (dead ∪ {[k]}) blocked) ∗ Delayed γd (Some (k, alive ∖ {[k]})).
  Proof.
    intros kalive kdead.
    iIntros "[Inv Delayed]". iDestruct "Inv" as (opt_k) "[>D Inv]".
    iDestruct (delayed_agree with "[D Delayed]") as "%Heq". { iFrame "D Delayed". }
    subst opt_k.
    iMod (delayed_update γd _ _ (Some (k, alive ∖ {[k]})) with "[D Delayed]") as "[D Delayed]". { iFrame "D Delayed". }
    iModIntro.
    iFrame "Delayed". iFrame "D". 
    replace (alive ∖ {[k]} ∪ {[k]}) with alive.
    - replace ((dead ∪ {[k]}) ∖ {[k]}) with dead.
      + iFrame. iPureIntro. set_solver.
      + set_solver.
    - apply set_eq. intros x. destruct (decide (x = k)); set_solver.
  Qed.
  
  Lemma set_lemma7 (other alive dead : gset lt_atom) (k : lt_atom) :
        k ∉ alive →
        k ∈ dead →
        other ⊈ alive →
        other ⊆ alive ∪ {[k]} ∪ dead ∖ {[k]} →
        ¬ other ## dead ∖ {[k]} ∪ {[k]}.
  Proof.
    set_solver.
  Qed.

  Lemma outer_kill_lt_step2 alive dead blocked outlives k alive' b :
    (swell k → b = true) →
    (k ∉ blocked) →
    (∀ other , (other, k) ∈ outlives → ¬(other ⊆ alive')) →
    (▷ outer_inv γ γo γd alive dead blocked)
      ∗ Outlives γo outlives
      ∗ Dead γ k
      ∗ Delayed γd (Some (k, alive'))
      ={↑Nbox ∪ ↑NllftUsr ∪ ↑NllftUsr2}=∗ ▷?b |={↑Nbox ∪ ↑NllftUsr ∪ ↑NllftUsr2}=>
    (▷ outer_inv γ γo γd alive dead blocked)
      ∗ Outlives γo outlives
      ∗ Delayed γd None.
  Proof.
    intros Hswell Hblocked Houtlives.
    iIntros "[Inv [Outlives [Dead Delayed]]]".
    iDestruct "Inv" as (opt_k) "[>D Inv]".
    iDestruct (delayed_agree with "[D Delayed]") as "%Heq". { iFrame "D Delayed". }
    subst opt_k.
    iDestruct "Inv" as "[Inv #>p]". iDestruct "p" as "[%Hkdead [%Hkalive %Heq]]". subst alive'.
    
    iDestruct (bi.later_mono _ _ (inv_get_outlives_condition (alive ∪ {[k]}) (dead ∖ {[k]}) blocked outlives) with "[Inv Outlives]") as "#>%Hoc". { iFrame "Inv". iFrame. }
    
    assert (∀ o : gset lt_atom * lt_atom, o ∈ outlives → o.1 ⊆ alive ∪ {[k]} ∪ dead ∖ {[k]}) as H2.
    {
      intros o. have Hoco := Hoc o. set_solver.
    }
    
    iMod (delayed_update γd _ _ None with "[D Delayed]") as "[D Delayed]".
        { iFrame "D Delayed". }
    iMod (inner_kill_lt_maybe_swell (alive ∪ {[k]}) (dead ∖ {[k]}) blocked outlives k b Hswell with "[Inv Outlives Dead]")
      as "X"; trivial. { set_solver. }
      { 
        intros other. have Ho := Houtlives other.
        have Ho2 := H2 (other, k).
        intros Hin. have Hox := Ho Hin. have Hoy := Ho2 Hin. simpl in Hoy.
        apply (set_lemma7 other alive dead k); trivial.
      } { iFrame "Dead". iFrame "Inv". iFrame "Outlives". }
    iModIntro. iNext. iMod "X". iModIntro.
    iDestruct "X" as "[X Y]".
    iFrame "Y". iSplitL "X D". {
      iExists None. iFrame "D".
      replace (((alive ∪ {[k]}) ∖ {[k]})) with alive by set_solver.
      replace ((dead ∖ {[k]} ∪ {[k]})) with dead. 2: {
        apply set_eq. intro x. destruct (decide (x = k)); set_solver.
      }
      iFrame.
    }
    iFrame "Delayed".
  Qed.
  
  Lemma outer_unborrow_atomic alive dead blocked outlives sn bl al de P :
    (al ⊆ alive) →
    ¬(de ## dead) →
    (∀ (k : lt_atom) , k ∈ al → (bl, k) ∈ outlives) →
    Delayed γd None
        ∗ (▷ outer_inv γ γo γd alive dead blocked)
        ∗ Outlives γo outlives
        ∗ OwnBorState γ sn (Borrow al de)
        ∗ slice Nbox sn P
        ={↑Nbox,∅}=∗ ▷ P ∗ ∀ Q, 
        (▷ (▷ Q ∗ (∃ k , ⌜ k ∈ bl ⌝ ∗ Dead γ k) ={↑NllftUsr ∪ ↑NllftUsr2}=∗ ▷ P)) ∗ (▷ Q)
          ={∅,↑Nbox}=∗ ∃ sn2,
    Delayed γd None
        ∗ (▷ outer_inv γ γo γd alive dead blocked)
        ∗ Outlives γo outlives
        ∗ OwnBorState γ sn2 (Borrow al de)
        ∗ slice Nbox sn2 Q
        .
  Proof.
    intros Hal Hde Houtlives.
    iIntros "[Delayed [Inv H]]".
    iDestruct "Inv" as (opt_k) "[>D Inv]".
    iDestruct (delayed_agree with "[D Delayed]") as "%Heq". { iFrame "D Delayed". }
    subst opt_k.
    iMod (inner_unborrow_atomic γ γo γd alive dead blocked outlives sn bl al de P Hal Hde with "[H Inv]") as "[P H]"; trivial. { iFrame. }
    iModIntro. iFrame "P". iIntros (Q). iDestruct ("H" $! Q) as "H". iIntros "A".
    iDestruct ("H" with "A") as "H". iMod "H" as (sn2) "H". iModIntro. iExists sn2.
    iFrame. iFrame "H".
  Qed.
End FullBorrows.
