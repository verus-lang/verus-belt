Require Import stdpp.base.
From iris.algebra Require Export cmra updates excl gmap.
From iris.base_logic.lib Require Export own.
From iris.proofmode Require Import proofmode.
Require Import guarding.own_and.
Require Import guarding.factoring_props.
From iris.prelude Require Import options.

Section Cmap.
  Context (L C V: Type) `{Countable C} `{Countable L}.
  Context {Infinite_C: Infinite C}.
  
  Definition untether_id := positive.
  
  Definition heap_map := gmap L V.
  Definition full_map := gmap (L + untether_id) (list C * V).
  
  Definition fine_map := gmap (L + C) (C + V).
  Definition unt_map := gmap untether_id (C * V).
  
  Implicit Type (𝛼: full_map).
  Implicit Type (𝛽: fine_map).
  Implicit Type (𝜃: unt_map).
  Implicit Type (σ: heap_map).
  
  Definition 𝜙build (k: L + untether_id) (cs_v: list C * V) (σ: heap_map) :=
      match k with
          | inl l => <[ l := snd cs_v ]> σ
          | inr _ => σ
      end.
  Definition 𝜙 (𝛼 : full_map) : heap_map :=
      map_fold 𝜙build ∅ 𝛼.
      
  Local Instance 𝜙build_proper k cs_v :
      Proper ((=) ==> (=)) (𝜙build k cs_v).
  Proof. unfold 𝜙build. solve_proper. Qed.
  
  Local Lemma 𝜙build_assoc j1 z1 j2 z2 y :
      j1 ≠ j2 → 𝜙build j1 z1 (𝜙build j2 z2 y) = 𝜙build j2 z2 (𝜙build j1 z1 y).
  Proof.
      intros Hne. unfold 𝜙build. destruct j1, j2; trivial. apply insert_commute. congruence.
  Qed.
      
  Local Definition 𝜙_lookup l 𝛼 :
      𝜙 𝛼 !! l = match 𝛼 !! (inl l) with Some (_, v) => Some v | _ => None end.
  Proof.
      induction 𝛼 as [|x T ? IH] using map_ind; first by done.
      unfold 𝜙.
      setoid_rewrite map_fold_insert; try typeclasses eauto; try eauto using 𝜙build_assoc.
      unfold 𝜙build. destruct x as [l'|c'].
         - fold 𝜙build. unfold 𝜙 in IH𝛼. destruct (decide (l = l')) as [He|Hn].
            + subst l'. rewrite lookup_insert. rewrite lookup_insert. destruct T; trivial.
            + rewrite lookup_insert_ne; last by done. rewrite IH𝛼.
              rewrite lookup_insert_ne; last by congruence. trivial.
         - fold 𝜙build. unfold 𝜙 in IH𝛼. rewrite IH𝛼. 
           rewrite lookup_insert_ne; last by congruence. trivial.
  Qed.
  
  Local Definition 𝜙_insert_l l cells v 𝛼 :
      𝜙 (<[ inl l := (cells, v) ]> 𝛼) = <[ l := v ]> (𝜙 𝛼).
  Proof.
      apply map_eq. intros k. destruct (decide (k = l)) as [He|Hn].
       - subst l. rewrite 𝜙_lookup. do 2 (rewrite lookup_insert). trivial.
       - rewrite lookup_insert_ne; last by done. do 2 (rewrite 𝜙_lookup).
         rewrite lookup_insert_ne; last by congruence. trivial.
  Qed.
  
  Local Definition 𝜙_insert_u u cells v 𝛼 :
      𝜙 (<[ inr u := (cells, v) ]> 𝛼) = (𝜙 𝛼).
  Proof.
      apply map_eq. intros k. do 2 (rewrite 𝜙_lookup).
      rewrite lookup_insert_ne; last by discriminate. trivial.
  Qed.
  
  Local Definition 𝜙_delete_l l 𝛼 :
      𝜙 (delete (inl l) 𝛼) = delete l (𝜙 𝛼).
  Proof.
      apply map_eq. intros k. destruct (decide (k = l)) as [He|Hn].
       - subst l. rewrite 𝜙_lookup. do 2 (rewrite lookup_delete). trivial.
       - rewrite lookup_delete_ne; last by done. do 2 (rewrite 𝜙_lookup).
         rewrite lookup_delete_ne; last by congruence. trivial.
  Qed.
  
  Local Definition 𝜙_delete_u u 𝛼 :
      𝜙 (delete (inr u) 𝛼) = (𝜙 𝛼).
  Proof.
      apply map_eq. intros k. do 2 (rewrite 𝜙_lookup).
      rewrite lookup_delete_ne; last by discriminate. trivial.
  Qed.
  
  (* no dupes *)
  
  Definition cell_list_build (k: L + untether_id) (cs_v: list C * V) (l: list C) :=
      cs_v.1 ++ l.
      
  Local Instance cell_list_build_proper k cs_v :
      Proper (Permutation ==> Permutation) (cell_list_build k cs_v).
  Proof. unfold cell_list_build. solve_proper. Qed.
  
  Local Lemma cell_list_build_assoc j1 z1 j2 z2 y :
       cell_list_build j1 z1 (cell_list_build j2 z2 y)
         ≡ₚ cell_list_build j2 z2 (cell_list_build j1 z1 y).
  Proof. unfold cell_list_build. solve_Permutation. Qed.
  
  Definition cell_list 𝛼 := map_fold cell_list_build [] 𝛼.
  
  Definition cells_no_dupes (𝛼: full_map) : Prop := NoDup (cell_list 𝛼).
    

  
  Local Lemma cells_no_dupes_upd_value 𝛼 k cells v v' :
      𝛼 !! k = Some (cells, v) →
      cells_no_dupes 𝛼 →
      cells_no_dupes (<[k := (cells, v')]> 𝛼).
  Proof using C EqDecision0 EqDecision1 H H0 L V.
      unfold cells_no_dupes. intros Hsome Hc.
      rewrite <- (insert_delete_insert 𝛼).
      setoid_rewrite map_fold_insert;
        try typeclasses eauto; try eauto using cell_list_build_assoc.
       - have h1 := map_fold_delete (≡ₚ) cell_list_build [] k (cells, v) 𝛼 _ _ Hsome.
         setoid_rewrite <- h1; try typeclasses eauto; try eauto using cell_list_build_assoc.
       - rewrite lookup_delete. trivial.
  Qed.
  
  
  Local Lemma cells_no_dupes_delete 𝛼 k :
      cells_no_dupes 𝛼 →
      cells_no_dupes (delete k 𝛼).
  Proof.
      destruct (𝛼 !! k) as [|] eqn:Hlookup.
       - unfold cells_no_dupes, cell_list. intros Hc.
         rewrite (map_fold_delete (≡ₚ) cell_list_build [] k p 𝛼 _ _ Hlookup) in Hc;
            try eauto using cell_list_build_assoc.
         unfold cell_list_build in Hc. rewrite NoDup_app in Hc. intuition.
       - rewrite delete_notin; done.
  Qed.
  
  Local Lemma cells_no_dupes_insert_emp 𝛼 k v :
      cells_no_dupes 𝛼 →
      cells_no_dupes (<[ k := ([], v) ]> 𝛼).
  Proof.
      rewrite <- (insert_delete_insert 𝛼). intros Hb.
      have Hc := cells_no_dupes_delete 𝛼 k Hb.
      unfold cells_no_dupes, cell_list in Hc. unfold cells_no_dupes, cell_list.
      rewrite (map_fold_insert (≡ₚ)); try eauto using cell_list_build_assoc.
      rewrite lookup_delete. trivial.
  Qed.
  
  Local Lemma cells_no_dupes_get_no_dupes 𝛼 k cells v :
    cells_no_dupes 𝛼 →
    𝛼 !! k = Some (cells, v) → NoDup cells.
  Proof.
    intros Hc Hsome.
    assert (<[k:=(cells, v)]> (delete k 𝛼) = <[k:=(cells, v)]> 𝛼) as X
        by apply insert_delete_insert.
    rewrite (insert_id 𝛼) in X; last by trivial.
    rewrite <- X in Hc.
    unfold cells_no_dupes, cell_list in Hc.
    rewrite (map_fold_insert (≡ₚ)) in Hc; try eauto using cell_list_build_assoc.
     - unfold cell_list_build in Hc. rewrite NoDup_app in Hc. intuition.
     - apply lookup_delete.
  Qed.
  
  Local Lemma cells_no_dupes_duplicate_contradiction 𝛼 k c (cs1 cs2 cs3: list C) v :
    cells_no_dupes 𝛼 →
    𝛼 !! k = Some (cs1 ++ c :: cs2 ++ c :: cs3, v) → False.
  Proof.
    intros Ha Hb. have Hnodup := cells_no_dupes_get_no_dupes 𝛼 k _ _ Ha Hb.
    rewrite NoDup_app in Hnodup. destruct Hnodup as [_ [_ Hnodup]].
    rewrite NoDup_cons in Hnodup. destruct Hnodup as [Hnodup _].
    rewrite not_elem_of_app in Hnodup. destruct Hnodup as [_ Hnodup].
    rewrite not_elem_of_cons in Hnodup. destruct Hnodup as [Hnodup _]. done.
  Qed.
  
  Local Lemma NoDup_implies_decomposition_identical cs1 cs2 cs1' cs2' (c: C) :
    NoDup (cs1 ++ c :: cs2) → cs1 ++ c :: cs2 = cs1' ++ c :: cs2' → cs1 = cs1' ∧ cs2 = cs2'.
  Proof.
    induction cs1 in cs1' |- *.
     - simpl. intros Hnd Heq. destruct cs1' as [|d ds].
       + simpl in Heq. inversion Heq. done.
       + simpl in Heq. inversion Heq. subst d. subst cs2. exfalso.
         rewrite NoDup_cons in Hnd. destruct Hnd as [Hnd _].
         rewrite not_elem_of_app in Hnd. destruct Hnd as [_ Hnd].
         rewrite not_elem_of_cons in Hnd. destruct Hnd as [Hnd _]. done.
     - intros Hnd Heq. destruct cs1' as [|d ds].
       + simpl in Heq. inversion Heq. subst a. subst cs2'. exfalso.
         rewrite NoDup_app in Hnd. destruct Hnd as [_ [Hnd _]].
         have Hnd' := Hnd c. apply Hnd'; rewrite elem_of_cons; left; trivial.
       + simpl in Heq. inversion Heq. subst a. simpl in Hnd.
         rewrite NoDup_cons in Hnd. destruct Hnd as [_ Hnd].
         destruct (IHcs1 ds Hnd H3) as [-> ->]. split; trivial.
  Qed.
  
  Local Lemma cells_no_dupes_different_rows_disjoint 𝛼 k cells v k' cells' v' :
      cells_no_dupes 𝛼 →
      k ≠ k' →
      𝛼 !! k = Some (cells, v) →
      𝛼 !! k' = Some (cells', v') →
      (∀ x, x ∈ cells → x ∉ cells').
  Proof.
      intros Hc Hne Ha1 Ha2.
      assert (<[k := (cells, v)]> (<[k' := (cells', v')]> (delete k' (delete k 𝛼))) = 𝛼) as X. {
         rewrite insert_delete. { rewrite insert_delete; trivial. }
         rewrite lookup_delete_ne; done.
      }
      rewrite <- X in Hc. unfold cells_no_dupes, cell_list in Hc.
      rewrite (map_fold_insert (≡ₚ)) in Hc; try eauto using cell_list_build_assoc.
       2: { rewrite lookup_insert_ne; last by done. rewrite lookup_delete_ne; last by done.
            apply lookup_delete. }
      rewrite (map_fold_insert (≡ₚ)) in Hc; try eauto using cell_list_build_assoc.
       2: { apply lookup_delete. }
      unfold cell_list_build in Hc. rewrite List.app_assoc in Hc.
      do 2 (rewrite NoDup_app in Hc). intuition.
  Qed.
  
  Local Lemma cells_no_dupes_compare_rows 𝛼 k cs1 cs2 v k' cs1' cs2' v' c :
      cells_no_dupes 𝛼 →
      𝛼 !! k = Some (cs1 ++ c :: cs2, v) →
      𝛼 !! k' = Some (cs1' ++ c :: cs2', v') →
      k = k' ∧ cs1 = cs1' ∧ cs2 = cs2'.
  Proof.
      intros Hc Ha1 Ha2. destruct (decide (k = k')) as [He|Hn].
        - subst k'. split; first trivial.
          have Hnd := cells_no_dupes_get_no_dupes 𝛼 k _ _ Hc Ha1.
          rewrite Ha1 in Ha2. inversion Ha2.
          apply (NoDup_implies_decomposition_identical _ _ _ _ _ Hnd H2).
        - exfalso.
          assert (c ∈ cs1 ++ c :: cs2) as Hin1. { rewrite elem_of_app; right. rewrite elem_of_cons; left; trivial. }
          assert (c ∈ cs1' ++ c :: cs2') as Hin2. { rewrite elem_of_app; right. rewrite elem_of_cons; left; trivial. }
          apply (cells_no_dupes_different_rows_disjoint _ _ _ _ _ _ _ Hc Hn Ha1 Ha2 c Hin1 Hin2).
  Qed.
  
  Local Lemma no_dup_remove1 cs1 cs2 cs3 (c: C) :
      NoDup ((cs1 ++ c :: cs2) ++ cs3) → NoDup ((cs1 ++ cs2) ++ cs3).
  Proof.
      repeat (rewrite NoDup_app). repeat (rewrite NoDup_cons).
      intros [[Ha [Hb [Hc Hd]]] [He Hf]]. intuition.
       - apply (Hb x); trivial. rewrite elem_of_cons. right; trivial.
       - apply (He x); trivial. decompose_elem_of_list.
         + rewrite elem_of_app. left; trivial.
         + rewrite elem_of_app. right. rewrite elem_of_cons. right; trivial.
  Qed.
    
  Local Lemma cells_no_dupes_remove_mid 𝛼 k cells1 c cells2 v :
      𝛼 !! k = Some (cells1 ++ c :: cells2, v) →
      cells_no_dupes 𝛼 →
      cells_no_dupes (<[ k := (cells1 ++ cells2, v) ]> 𝛼).
  Proof.
      intros Hsome Hc.
      assert ((<[k := (cells1 ++ c :: cells2, v)]> (delete k 𝛼)) = 𝛼) as X. {
          apply insert_delete. trivial.
      }
      rewrite <- X in Hc. unfold cells_no_dupes, cell_list in Hc.
      rewrite (map_fold_insert (≡ₚ)) in Hc; try eauto using cell_list_build_assoc;
          last by apply lookup_delete.
      rewrite <- (insert_delete_insert 𝛼). unfold cells_no_dupes, cell_list.
      rewrite (map_fold_insert (≡ₚ)); try eauto using cell_list_build_assoc;
          last by apply lookup_delete.
      unfold cell_list_build. unfold cell_list_build in Hc.
      apply (no_dup_remove1 _ _ _ _ Hc).
  Qed.
  
  Local Lemma cells_no_dupes_join_2_rows 𝛼 k1 cells1 v1 k2 cells2 v2 v3 :
      k1 ≠ k2 →
      𝛼 !! k1 = Some (cells1, v1) →
      𝛼 !! k2 = Some (cells2, v2) →
      cells_no_dupes 𝛼 →
      cells_no_dupes (<[ k1 := (cells1 ++ cells2, v3) ]> (delete k2 𝛼)).
  Proof.
      intros Hne Ha1 Ha2 Hc.
      rewrite <- (insert_delete_insert (delete k2 𝛼)).
      assert (<[k1 := (cells1, v1)]> (<[k2 := (cells2, v2)]> (delete k1 (delete k2 𝛼))) = 𝛼)
        as X. {
        rewrite <- (delete_insert_ne (delete k2 𝛼)); last by trivial.
        rewrite insert_delete. 2: { rewrite lookup_insert_ne; last by done.
          rewrite lookup_delete_ne; last by done. trivial. }
        apply insert_delete. trivial.
      }
      rewrite <- X in Hc. unfold cells_no_dupes, cell_list in Hc.
      rewrite (map_fold_insert (≡ₚ)) in Hc; try eauto using cell_list_build_assoc.
          2: { rewrite lookup_insert_ne; last by done. apply lookup_delete. }
      rewrite (map_fold_insert (≡ₚ)) in Hc; try eauto using cell_list_build_assoc.
          2: { rewrite lookup_delete_ne; last by done. apply lookup_delete. }
      unfold cells_no_dupes, cell_list.
      rewrite (map_fold_insert (≡ₚ)); try eauto using cell_list_build_assoc.
          2: { apply lookup_delete. }
      unfold cell_list_build. unfold cell_list_build in Hc.
      simpl. rewrite <- List.app_assoc. apply Hc.
  Qed.
  
  Local Lemma cells_no_dupes_split_row 𝛼 k1 cells1 v1 k2 cells2 v2 v3 :
      k1 ≠ k2 →
      𝛼 !! k1 = Some (cells1 ++ cells2, v3) →
      𝛼 !! k2 = None →
      cells_no_dupes 𝛼 →
      cells_no_dupes (<[ k1 := (cells1, v1) ]> (<[ k2 := (cells2, v2) ]> 𝛼)).
  Proof.
      intros Hne Ha1 Ha2 Hc.
      assert (<[k1 := (cells1, v1)]> (<[k2 := (cells2, v2)]> (delete k1 𝛼)) = 
          (<[k1:=(cells1, v1)]> (<[k2:=(cells2, v2)]> 𝛼)))
      as X. {
        rewrite <- (delete_insert_ne 𝛼); last by trivial.
        apply insert_delete_insert.
      }
      assert (<[k1 := (cells1 ++ cells2, v3)]> (delete k1 𝛼) = 𝛼) as Y. {
        apply insert_delete. trivial.
      }
      rewrite <- X. unfold cells_no_dupes, cell_list.
      rewrite <- Y in Hc. unfold cells_no_dupes, cell_list in Hc.
      rewrite (map_fold_insert (≡ₚ)) in Hc; try eauto using cell_list_build_assoc.
          2: { apply lookup_delete. }
      rewrite (map_fold_insert (≡ₚ)); try eauto using cell_list_build_assoc.
          2: { rewrite lookup_insert_ne; last by done. apply lookup_delete. }
      rewrite (map_fold_insert (≡ₚ)); try eauto using cell_list_build_assoc.
          2: { rewrite lookup_delete_ne; done. }
      unfold cell_list_build. unfold cell_list_build in Hc.
      rewrite List.app_assoc. apply Hc.
  Qed.
     
  (* list utils *)
  
  Fixpoint list_has_pair {A} (l: list A) (a1 a2: A) :=
      match l with
        | [] => False
        | x :: xl => match xl with
            | [] => False
            | x' :: _ => (x = a1 ∧ x' = a2) ∨ list_has_pair xl a1 a2
        end
      end.
      
  Definition last_lc (l: L) (cells: list C) : L+C :=
      List.last (inr <$> cells) (inl l).
      
  Definition last_c (cells: list C) : option C :=
      List.last (Some <$> cells) (None).
      
  Definition list_ends_with (l: list C) (a1: C) := last_c l = Some a1.
  
  Lemma list_has_pair_destruct {A} cells (c1 c2 : A) :
      list_has_pair cells c1 c2 → ∃ cells1 cells2 , cells = cells1 ++ c1 :: c2 :: cells2.
  Proof.
      induction cells; first by done. intros Ha. simpl in Ha. destruct cells; first by done.
      destruct Ha as [[Eq1 Eq2]|Pair].
        - subst c1. subst c2. exists [], cells; trivial.
        - destruct (IHcells Pair) as [cells1 [cells2 Eq]]. exists (a :: cells1), cells2.
          rewrite Eq. done.
  Qed.
  
  Lemma list_last_lc_app_singleton l cells c :
      last_lc l (cells ++ [c]) = inr c.
  Proof.
      induction cells; first by done. rewrite <- IHcells. simpl.
      destruct (cells ++ [c]); done.
  Qed.
  
  Lemma list_last_c_app_singleton cells c :
      last_c (cells ++ [c]) = Some c.
  Proof.
      induction cells; first by done. rewrite <- IHcells. simpl.
      destruct (cells ++ [c]); done.
  Qed.
  
  Local Lemma list_has_pair_cons {A} cells (c c' c0 : A) :
      list_has_pair cells c c' →
      list_has_pair (c0 :: cells) c c'.
  Proof.
      destruct cells; first by done. destruct cells; first by done. 
      intros [[Ha Hb]|Hb].
        - rewrite Ha. rewrite Hb. right. left. done. - right. right. trivial.
  Qed.
    
  Local Lemma list_has_pair_app_case {A} cells1 cells2 (c c' : A) :
        list_has_pair (cells1 ++ cells2) c c' →
        list_has_pair cells1 c c' ∨ list_has_pair cells2 c c' ∨ (∃ cells0 , cells1 = cells0 ++ [c]).
  Proof.
      induction cells1 as [|a cells1]; first by simpl; intuition.
      destruct cells1.
        - intros Ha. destruct cells2.
          + simpl in Ha. done.
          + simpl in Ha. destruct Ha as [[Eq1 Eq2]|Pairs2].
            * right. right. exists []. subst c. done.
            * destruct cells2; first by done. destruct Pairs2 as [[Eq1 Eq2]|Pairs3].
              -- subst c. subst c'. right. left. left. done.
              -- right. left. right. trivial.
        - intros Ha.
          replace ((a :: a0 :: cells1) ++ cells2) with (a :: (a0 :: cells1) ++ cells2) in Ha
              by (simpl; done).
          destruct Ha as [[Eq1 Eq2]|Pairs2].
           + subst c. subst c'. left. left. done.
           + destruct (IHcells1 Pairs2) as [Hb|[Hc|[cells0 Hd]]].
            -- left. apply list_has_pair_cons; trivial. -- right. left. trivial.
            -- right. right. exists (a :: cells0). rewrite Hd. by simpl.
  Qed.
  
  Local Lemma case_last_lc l cells :
      (last_lc l cells = inl l ∧ cells = [])
      ∨ ∃ prefix last, last_lc l cells = inr last ∧ cells = prefix ++ [last].
  Proof.
      induction cells; first by (left; done).
      destruct IHcells as [[Heq1 Heq2]|[prefix [last [Eq1 Eq2]]]].
       - subst cells. right. exists [], a. done.
       - right. exists (a :: prefix), last. subst cells. split.
         + rewrite <- Eq1. simpl. destruct (prefix ++ [last]); done. + by simpl.
  Qed.
  
  Local Lemma case_last_c cells :
      (last_c cells = None ∧ cells = [])
      ∨ ∃ prefix last, last_c cells = Some last ∧ cells = prefix ++ [last] .
  Proof.
      induction cells; first by (left; done).
      destruct IHcells as [[Heq1 Heq2]|[prefix [last [Eq1 Eq2]]]].
       - subst cells. right. exists [], a. done.
       - right. exists (a :: prefix), last. subst cells. split.
         + rewrite <- Eq1. simpl. destruct (prefix ++ [last]); done. + by simpl.
  Qed.
  
  Local Lemma facts_from_last_lc_is_l l0 l1 cells :
      inl l0 = last_lc l1 cells → l0 = l1 ∧ cells = [].
  Proof.
      destruct (case_last_lc l1 cells) as [[Eq1 Eq2]|[prefix [last [Eq1 Eq2]]]];
        intros Ha; rewrite Eq1 in Ha; inversion Ha; done.
  Qed.
      
  Local Lemma facts_from_last_lc_is_c c0 l1 cells :
      inr c0 = last_lc l1 cells → ∃ prefix, cells = prefix ++ [c0].
  Proof.
      destruct (case_last_lc l1 cells) as [[Eq1 Eq2]|[prefix [last [Eq1 Eq2]]]].
        - intros Ha; rewrite Eq1 in Ha; inversion Ha; done.
        - intros Ha; rewrite Eq1 in Ha. inversion Ha. exists prefix. done.
  Qed.
      
  Local Lemma facts_from_list_ends_with (cs : list C) c :
      list_ends_with cs c → ∃ cs' , cs = cs' ++ [c].
  Proof.
      unfold list_ends_with. intros Ha.
      destruct (case_last_c cs) as [[Eq1 Eq2]|[prefix [last [Eq1 Eq2]]]].
        - rewrite Ha in Eq1. discriminate.
        - exists prefix. rewrite Ha in Eq1. inversion Eq1. done.
  Qed.
      
  Local Lemma facts_from_list_has_pair {A} (cs : list A) c1 c2 :
      list_has_pair cs c1 c2 → ∃ cs' cs'' , cs = cs' ++ c1 :: c2 :: cs''.
  Proof.
      induction cs as [|a cs]; first by done. destruct cs as [|a1 cs]; first by done.
      intros [[Heq1 Heq2]|Hb].
        - subst a1. subst a. exists [], cs. done.
        - destruct (IHcs Hb) as [cs' [cs'' Eq]]. exists (a :: cs'), cs''. rewrite Eq. by simpl.
  Qed.
  
  Local Lemma list_has_pair_app_r {A} cells1 cells2 (c1 c2 : A) :
    list_has_pair cells2 c1 c2 →
    list_has_pair (cells1 ++ cells2) c1 c2.
  Proof.
    induction cells1; first by done. eauto using list_has_pair_cons.
  Qed.
    
  Local Lemma list_has_pair_app_l {A} cells1 cells2 (c1 c2 : A) :
    list_has_pair cells1 c1 c2 →
    list_has_pair (cells1 ++ cells2) c1 c2.
  Proof.
    induction cells1; first by done.
    intros Ha. destruct cells1 as [|c cells1]; first by done.
    destruct Ha as [[Eq1 Eq2]|Hb].
     - subst c1. subst c2. simpl. left; done.
     - have Hc := IHcells1 Hb. apply list_has_pair_cons. apply Hc.
  Qed.
    
  Local Lemma list_has_pair_mid {A} cs1 (c1 c2 : A) cs2 :
    list_has_pair (cs1 ++ c1 :: c2 :: cs2) c1 c2.
  Proof.
      induction cs1.
        - left. done.
        - apply list_has_pair_cons. apply IHcs1.
  Qed.
  
  Local Lemma list_has_pair_app_app_cons {A} cs1 (c1 c2 : A) cs2 :
      list_has_pair (cs1 ++ [c1] ++ c2 :: cs2) c1 c2.
  Proof.
      simpl. apply list_has_pair_mid.
  Qed.
  
  Local Lemma list_ends_with_uncons cells (c1 c2 : C) :
      c1 ≠ c2 →
      list_ends_with (c1 :: cells) c2 → 
      list_ends_with cells c2.
  Proof.
      intros Ha Hb. destruct cells.
        - unfold list_ends_with, last_c in Hb. simpl in Hb. inversion Hb. contradiction.
        - unfold list_ends_with, last_c. unfold list_ends_with, last_c in Hb.
          rewrite <- Hb. done.
  Qed.
  
  Local Lemma list_has_pair_uncons {A} cells (c1 c2 c3 : A) :
      c1 ≠ c2 →
      list_has_pair (c1 :: cells) c2 c3 → 
      list_has_pair cells c2 c3.
  Proof.
      destruct cells; first by done. intros He [[Heq1 Heq2]|Hb]; done.
  Qed.
  
  Local Lemma list_ends_with_app_singleton cells1 (c1 : C) :
    list_ends_with (cells1 ++ [c1]) c1.
  Proof.
    apply list_last_c_app_singleton.
  Qed.
    
  Local Lemma list_ends_with_app_r cells1 cells2 (c1 : C) :
    list_ends_with cells2 c1 →
    list_ends_with (cells1 ++ cells2) c1.
  Proof.
    intros Ha. destruct (facts_from_list_ends_with _ _ Ha) as [cs' Heq].
    subst cells2. rewrite List.app_assoc. apply list_ends_with_app_singleton.
  Qed.
    
  Local Lemma list_ends_with_app_r_rev cells1 cells2 (c c1 : C) :
    list_ends_with (cells1 ++ c :: cells2) c1 →
    list_ends_with (c :: cells2) c1.
  Proof.
    induction cells1; first by done.
    intros Ha. apply IHcells1. unfold list_ends_with, last_c.
    unfold list_ends_with, last_c in Ha. rewrite <- Ha. simpl. 
    destruct (cells1 ++ c :: cells2) eqn:Ho; last by done.
    exfalso. assert (length (cells1 ++ c :: cells2) = length []) as X by (rewrite Ho; done).
    rewrite length_app in X. simpl in X. lia.
  Qed.
    
  Local Lemma list_ends_with_gives_last_lc l cells cell :
      list_ends_with cells cell →
          inr cell = last_lc l cells.
  Proof.
      induction cells; first by done.
      intros Ha. destruct cells.
       - unfold list_ends_with, last_c in Ha. simpl in Ha. inversion Ha. done.
       - unfold list_ends_with, last_c in Ha. unfold list_ends_with in IHcells.
         assert (last_c (c :: cells) = Some cell) as X. { rewrite <- Ha. done. }
         rewrite (IHcells X). done.
  Qed.
          
  Local Lemma list_ends_with_from_last_lc cells c :
      last_c cells = Some c ↔ list_ends_with cells c.
  Proof. done. Qed.

  Local Lemma last_lc_cons_ne_l l c cells :
      last_lc l (c :: cells) ≠ inl l.
  Proof.
      intros Hl. symmetry in Hl. destruct (facts_from_last_lc_is_l _ _ _ Hl). discriminate.
  Qed.
  
  Local Lemma elem_of_from_list_has_pair_1 cells (c1 c2 : C) :
      list_has_pair cells c1 c2 → c1 ∈ cells.
  Proof.
      intros Ha. destruct (facts_from_list_has_pair _ _ _ Ha) as [cs' [cs'' He]].
      subst cells. rewrite elem_of_app. right. rewrite elem_of_cons. left. done.
  Qed.
      
  Local Lemma elem_of_from_list_ends_with cells (c : C) :
      list_ends_with cells c → c ∈ cells.
  Proof.
      intros Ha. destruct (facts_from_list_ends_with _ _ Ha) as [cs' He].
      subst cells. rewrite elem_of_app. right. rewrite elem_of_cons. left. done.
  Qed.
  
  (* inv definitions *)
  
  Definition 𝛼_fine_pair (𝛼: full_map) (src: L+C) (dst: C+V) :=
      match src, dst with
        | inl loc, inl cell =>
            match 𝛼 !! (inl loc) with Some (c :: _, _) => cell = c | _ => False end
        | inl loc, inr val => 𝛼 !! (inl loc) = Some ([], val)
        | inr cell, inl cell2 => ∃ lu cs v, 𝛼 !! lu = Some (cs, v) ∧ list_has_pair cs cell cell2
        | inr cell, inr val => ∃ lu cs, 𝛼 !! lu = Some (cs, val) ∧ list_ends_with cs cell
      end.
      
  Definition fine_map_inv (𝛼 : full_map) (𝛽: fine_map) :=
      ∀ src dst, 𝛽 !! src = Some dst → 𝛼_fine_pair 𝛼 src dst.
          
  Definition unt_map_inv (𝛼 : full_map) (𝜃: unt_map) :=
      ∀ uid cell val, 𝜃 !! uid = Some (cell, val) →
          match 𝛼 !! (inr uid) with
              | Some (c :: _, v) => cell = c ∧ v = val
              | _ => False
          end.
  
  Definition big_inv (𝛼: full_map) (𝛽: fine_map) (𝜃: unt_map) :=
      fine_map_inv 𝛼 𝛽 ∧ unt_map_inv 𝛼 𝜃 ∧ cells_no_dupes 𝛼.
        
  (* freshness *)
  
  Definition fresh_uid 𝛼 (u: untether_id) := 𝛼 !! (inr u) = None.
  Definition fresh_cell_id 𝛼 (c: C) : Prop := c ∉ cell_list 𝛼.
  
  Local Lemma fresh_ne_to_existing_key 𝛼 (lu: L + untether_id) u cells_v :
      𝛼 !! lu = Some cells_v → fresh_uid 𝛼 u → lu ≠ (inr u).
  Proof.
      intros Ha Hnone Heq. subst lu. rewrite Hnone in Ha. discriminate.
  Qed.
  
    
  Local Definition uid_list_build (k: L + untether_id) (cs_v: list C * V) (l: list untether_id) :=
      match k with inl _ => l | inr u => u :: l end.
      
  Local Instance uid_list_build_proper k cs_v :
      Proper (Permutation ==> Permutation) (uid_list_build k cs_v).
  Proof. unfold uid_list_build. solve_proper. Qed.
  
  Local Lemma uid_list_build_assoc j1 z1 j2 z2 y :
       uid_list_build j1 z1 (uid_list_build j2 z2 y)
         ≡ₚ uid_list_build j2 z2 (uid_list_build j1 z1 y).
  Proof. unfold uid_list_build. destruct j1; destruct j2; solve_Permutation. Qed.
  
  Local Definition uid_list 𝛼 : list untether_id := map_fold uid_list_build [] 𝛼.
  
  Lemma not_in_uid_list_implies_fresh 𝛼 u :
      u ∉ uid_list 𝛼 → fresh_uid 𝛼 u.
  Proof.
      induction 𝛼 as [|x T ? IH] using map_ind; first by done.
      intros Hnotin. unfold fresh_uid.
      setoid_rewrite (map_fold_insert (≡ₚ)) in Hnotin;
        try typeclasses eauto; try eauto using uid_list_build_assoc.
      destruct (decide (x = inr u)).
       - subst x. exfalso. unfold uid_list in Hnotin.
         rewrite not_elem_of_cons in Hnotin.
         unfold uid_list_build in Hnotin. destruct Hnotin as [??]. done.
       - rewrite lookup_insert_ne; last by done. apply IH𝛼. destruct x.
         + apply Hnotin. + rewrite not_elem_of_cons in Hnotin. intuition.
  Qed.
  
  Local Lemma exists_fresh_uid 𝛼 : ∃ u , fresh_uid 𝛼 u.
  Proof.
      exists (fresh (uid_list 𝛼)). apply not_in_uid_list_implies_fresh. apply infinite_is_fresh.
  Qed.
  
  Local Lemma exists_fresh_cell_id 𝛼 : ∃ c , fresh_cell_id 𝛼 c.
  Proof using C EqDecision1 H0 Infinite_C L V.
      exists (fresh (cell_list 𝛼)). apply infinite_is_fresh.
  Qed.
  
  Local Lemma fresh_cell_not_in_𝛼 𝛼 c k cells v :
      fresh_cell_id 𝛼 c → 𝛼 !! k = Some (cells, v) → c ∉ cells.
  Proof.
      intros Hfresh Hl.
      assert (<[k:=(cells, v)]> (delete k 𝛼) = 𝛼) as X. { by rewrite insert_delete. }
      rewrite <- X in Hfresh. unfold fresh_cell_id, cell_list in Hfresh.
      setoid_rewrite map_fold_insert in Hfresh;
        try typeclasses eauto; try eauto using cell_list_build_assoc.
      - unfold cell_list_build in Hfresh. rewrite not_elem_of_app in Hfresh. intuition.
      - apply lookup_delete.
  Qed.
  
  Local Lemma fresh_cell_not_in_𝛽 𝛼 𝛽 𝜃 c :
      fresh_cell_id 𝛼 c → big_inv 𝛼 𝛽 𝜃 → 𝛽 !! (inr c) = None.
  Proof.
      intros Hfresh big. destruct (𝛽 !! inr c) as [cv|] eqn:Hl; last trivial.
      exfalso. destruct big as [fine_inv [u_inv no_dupes]]. have Hf := fine_inv _ _ Hl.
      unfold 𝛼_fine_pair in Hf. destruct cv as [c1|v1].
       - destruct Hf as [lu [cs [v2 [H𝛼l Hpair]]]].
         have Hin := elem_of_from_list_has_pair_1 _ _ _ Hpair.
         apply (fresh_cell_not_in_𝛼 _ _ _ _ _ Hfresh H𝛼l Hin).
       - destruct Hf as [lu [cs [H𝛼l Hends]]].
         have Hin := elem_of_from_list_ends_with _ _ Hends.
         apply (fresh_cell_not_in_𝛼 _ _ _ _ _ Hfresh H𝛼l Hin).
  Qed.
  
  Local Lemma fresh_uid_not_in_𝜃 𝛼 𝛽 𝜃 u :
      fresh_uid 𝛼 u → big_inv 𝛼 𝛽 𝜃 → 𝜃 !! u = None.
  Proof.
      intros Hfresh big. destruct (𝜃 !! u) as [[c v]|] eqn:Hl; last trivial.
      exfalso. destruct big as [fine_inv [u_inv no_dupes]]. have Hf := u_inv _ _ _ Hl.
      by rewrite Hfresh in Hf.
  Qed.
  
  Local Lemma cells_no_dupes_of_fresh_singleton 𝛼 u c v :
      𝛼 !! u = None →
      fresh_cell_id 𝛼 c →
      cells_no_dupes 𝛼 →
      cells_no_dupes (<[ u := ([c], v) ]> 𝛼).
  Proof.
      intros Hf Hc. unfold cells_no_dupes, cell_list.
      setoid_rewrite map_fold_insert;
        try typeclasses eauto; try eauto using cell_list_build_assoc.
      intros Hnodup. unfold cell_list_build. rewrite NoDup_app.
      split; first by apply NoDup_singleton. split; last by trivial.
      intros x. simpl. rewrite elem_of_list_singleton. intros ->. apply Hc.
  Qed.
  
  (* utils *)
  
  Fixpoint read 𝛽 (lc: L + C) (cells: list C) (cv: C + V) :=
    match cells with
        | cell :: cells' => 𝛽 !! lc = Some (inl cell) ∧ read 𝛽 (inr cell) cells' cv
        | [] => 𝛽 !! lc = Some cv
    end.
      
  Definition write 𝛽 (l: L) (cells: list C) (cv': C+V) :=
      <[ last_lc l cells := cv' ]> 𝛽.
      

  (* invariant preservation *)
  
  (* alloc *)
  
  Definition 𝛼_alloc 𝛼 l v := (<[ inl l := ([], v) ]> 𝛼).
  
  Definition alloc_preserves_inv 𝛼 𝛽 𝜃 l v :
      𝜙 𝛼 !! l = None →
      big_inv 𝛼 𝛽 𝜃 →
      big_inv (𝛼_alloc 𝛼 l v) ((<[ inl l := inr v ]>) 𝛽) 𝜃
          ∧ 𝛽 !! (inl l) = None
          ∧ 𝜙 (𝛼_alloc 𝛼 l v) = <[ l := v ]> (𝜙 𝛼).
  Proof.
    intros Hnone big.
    rewrite 𝜙_lookup in Hnone.
    destruct big as [fine_inv [unt_inv no_dupes]].
    split; [split; [|split] | split].
      - intros src dst Hl. destruct (decide (src = inl l)).
        { subst src. rewrite lookup_insert in Hl. inversion Hl. subst dst.
          apply lookup_insert. }
        rewrite lookup_insert_ne in Hl; last by done.
        have f1 := fine_inv _ _ Hl.
        unfold 𝛼_fine_pair, 𝛼_alloc. unfold 𝛼_fine_pair in f1.
        destruct src.
        + rewrite lookup_insert_ne; last by congruence. trivial.
        + destruct dst.
          * destruct f1 as [k [cs [v0 [Eq Pair]]]]. 
            destruct (decide (k = inl l)).
            -- subst k. rewrite Eq in Hnone. discriminate.
            -- exists k, cs, v0. rewrite lookup_insert_ne; done.
          * destruct f1 as [k [cs [Eq Pair]]]. 
            destruct (decide (k = inl l)).
            -- subst k. rewrite Eq in Hnone. discriminate.
            -- exists k, cs. rewrite lookup_insert_ne; done.
    - intros u1 cell1 v1 Hs. unfold 𝛼_alloc. rewrite lookup_insert_ne; last by discriminate.
      apply (unt_inv _ _ _ Hs).
    - apply cells_no_dupes_insert_emp; trivial.
    - destruct (𝛽 !! inl l) as [dst|] eqn:Hl; last by done. exfalso.
      have f1 := fine_inv _ _ Hl. unfold 𝛼_fine_pair in f1.
      destruct dst as [v0|c0]; destruct (𝛼 !! inl l) as [[cells v1]|]; try done.
    - apply 𝜙_insert_l.
  Qed.
  
  (* delete *)
  
  Definition 𝛼_delete 𝛼 l := delete (inl l) 𝛼.
  
  Lemma del_preserves_inv 𝛼 𝛽 𝜃 l v :
      𝛽 !! (inl l) = Some (inr v) →
      big_inv 𝛼 𝛽 𝜃 →
      big_inv (𝛼_delete 𝛼 l) (delete (inl l) 𝛽) 𝜃
          ∧ 𝜙 (𝛼_delete 𝛼 l) = delete l (𝜙 𝛼).
  Proof.
    intros Hsome big.
    destruct big as [fine_inv [unt_inv no_dupes]].
    have f0 := fine_inv _ _ Hsome. unfold 𝛼_fine_pair in f0.
    split; [split; [|split] | ].
      - intros src dst Hl. destruct (decide (src = inl l)).
        { subst src. rewrite lookup_delete in Hl. discriminate. }
        rewrite lookup_delete_ne in Hl; last by done.
        have f1 := fine_inv _ _ Hl.
        unfold 𝛼_fine_pair, 𝛼_delete. unfold 𝛼_fine_pair in f1.
        destruct src.
        + rewrite lookup_delete_ne; last by congruence. trivial.
        + destruct dst.
          * destruct f1 as [k [cs [v0 [Eq Pair]]]]. 
            destruct (decide (k = inl l)).
            -- subst k. rewrite f0 in Eq. inversion Eq. subst cs. done.
            -- exists k, cs, v0. rewrite lookup_delete_ne; done.
          * destruct f1 as [k [cs [Eq Pair]]]. 
            destruct (decide (k = inl l)).
            -- subst k. rewrite f0 in Eq. inversion Eq. subst cs. done.
            -- exists k, cs. rewrite lookup_delete_ne; done.
    - intros u1 cell1 v1 Hs. unfold 𝛼_delete. rewrite lookup_delete_ne; last by discriminate.
      apply (unt_inv _ _ _ Hs).
    - apply cells_no_dupes_delete; trivial.
    - apply 𝜙_delete_l.
  Qed.
  
  (* read *)
  
  Local Lemma read_get_first lc cells cv 𝛽 :
      read 𝛽 lc cells cv → 𝛽 !! lc = Some (match cells with c :: _ => inl c | _ => cv end).
  Proof. destruct cells; unfold read; intuition. Qed.
  
  Local Lemma read_get_last' 𝛽 lc prefix last cv :
      read 𝛽 lc (prefix ++ [last]) cv → 𝛽 !! inr last = Some cv.
  Proof.
      induction prefix in lc |- *. { simpl. intros [a b]; trivial. }
      intros [Hr Hrest]. apply (IHprefix (inr a)). apply Hrest.
  Qed.
  
  Local Lemma read_get_last l cells cv 𝛽 :
      read 𝛽 (inl l) cells cv → 𝛽 !! (last_lc l cells) = Some cv.
  Proof.
      destruct (case_last_lc l cells) as [[Heq Hceq]|[prefix [last [Heq1 Heq2]]]].
      - subst cells. done.
      - rewrite Heq1. rewrite Heq2. apply read_get_last'.
  Qed.
  
  Local Lemma read_𝛽_mono lc cells cv 𝛽 𝛽' :
      𝛽 ⊆ 𝛽' → read 𝛽 lc cells cv → read 𝛽' lc cells cv.
  Proof.
    induction cells in lc |- *.
      - intros Hsub Hin. apply (lookup_weaken _ _ _ _ Hin Hsub).
      - intros Hsub [Hin Hin2]. split; eauto using IHcells, lookup_weaken.
  Qed.
      
  Local Lemma read_𝛽_insert lc c cells cv 𝛽 :
      𝛽 !! lc = None →
      read 𝛽 (inr c) cells cv →
      read (<[lc:=inl c]> 𝛽) lc (c :: cells) cv.
  Proof.
      intros Hnone Hr. split.
       - rewrite lookup_insert. trivial.
       - apply (read_𝛽_mono _ _ _ 𝛽); trivial. apply insert_subseteq. trivial.
  Qed.
  
  Local Lemma read_𝛽_insert2 lc cell cells cv 𝛽 𝛽' :
      𝛽 ⊆ 𝛽' → {[lc := inl cell]} ⊆ 𝛽' →
      read 𝛽 (inr cell) cells cv →
      read 𝛽' lc (cell :: cells) cv.
  Proof.
      intros Hsub Hsub2 Hr. split; last by eauto using read_𝛽_mono.
      rewrite map_singleton_subseteq_l in Hsub2. trivial.
  Qed.
  
  Local Lemma read_𝛽_delete_loc 𝛽 c cells cv l :
      read 𝛽 (inr c) cells cv → read (delete (inl l) 𝛽) (inr c) cells cv.
  Proof.
    induction cells in c |- *.
      - unfold read. rewrite lookup_delete_ne; done.
      - intros [Hr Hread]. split.
        + rewrite lookup_delete_ne; done. + apply IHcells. apply Hread.
  Qed.
  
  Local Lemma read_𝛽_delete_cell 𝛽 c cells cv (c': C) :
      c' ∉ c :: cells →
      read 𝛽 (inr c) cells cv → read (delete (inr c') 𝛽) (inr c) cells cv.
  Proof.
      induction cells in c |- *.
      - unfold read. intros Hc. rewrite elem_of_list_singleton in Hc.
        rewrite lookup_delete_ne; trivial. intros Ha. inversion Ha. subst c'. done.
      - intros Hnotin Hread. destruct Hread as [Hr Hread].
        do 2 (rewrite not_elem_of_cons in Hnotin). 
        assert (c' ∉ a :: cells) as Hnotin2. { rewrite not_elem_of_cons. intuition. }
        have IH := IHcells a Hnotin2 Hread. split; trivial.
        rewrite lookup_delete_ne; trivial. intro He. inversion He. subst c'. intuition.
  Qed.
     
    
  Lemma extend_next_after_cell_is_value 𝛼 𝛽 𝜃 k cells1 c cells2 v v' :
        𝛼 !! k = Some (cells1 ++ c :: cells2, v') →
        big_inv 𝛼 𝛽 𝜃 →
        𝛼_fine_pair 𝛼 (inr c) (inr v) →
        cells2 = [] ∧ v' = v.
  Proof.
      intros Hk big fine. destruct fine as [k' [cs [Hk' ends]]].
      destruct (facts_from_list_ends_with cs c ends) as [prefix Heq]. subst cs.
      destruct big as [fine_inv [u_inv no_dupes]].
      destruct (cells_no_dupes_compare_rows _ _ _ _ _ _ _ _ _ _ no_dupes Hk Hk')
          as [-> [-> ->]].
      rewrite Hk in Hk'. inversion Hk'. done.
  Qed.
  
  Lemma extend_next_after_cell_is_cell 𝛼 𝛽 𝜃 k cells1 c cells2 c2 v' :
        𝛼 !! k = Some (cells1 ++ c :: cells2, v') →
        big_inv 𝛼 𝛽 𝜃 →
        𝛼_fine_pair 𝛼 (inr c) (inl c2) →
        ∃ cells2', cells2 = c2 :: cells2'.
  Proof.
      intros Hk big fine. destruct fine as [k' [cs [v [Hk' haspair]]]].
      destruct (facts_from_list_has_pair cs c c2 haspair) as [prefix [suffix Heq]]. subst cs.
      destruct big as [fine_inv [u_inv no_dupes]].
      destruct (cells_no_dupes_compare_rows _ _ _ _ _ _ _ _ _ _ no_dupes Hk Hk')
          as [-> [-> ->]]. exists suffix. trivial.
  Qed.
  
  Local Lemma read_l_v_gives_𝛼_row' 𝛼 𝛽 𝜃 c k cells1 cells2 cells2' v v' :
      read 𝛽 (inr c) cells2 (inr v) →
      big_inv 𝛼 𝛽 𝜃 →
      𝛼 !! k = Some (cells1 ++ c :: cells2', v') →
      𝛼 !! k = Some (cells1 ++ c :: cells2, v).
  Proof.
      induction cells2 in c, cells1, cells2' |- *.
      - intros Hr big row.
        assert (big_inv 𝛼 𝛽 𝜃) as big2 by trivial.
        destruct big as [fine_inv [u_inv no_dupes]].
        unfold read in Hr. have f1 := fine_inv _ _ Hr.
        destruct (extend_next_after_cell_is_value _ _ _ _ _ _ _ _ _ row big2 f1).
        subst cells2'. subst v'. trivial.
      - intros Hr big row.
        assert (big_inv 𝛼 𝛽 𝜃) as big2 by trivial.
        destruct big as [fine_inv [u_inv no_dupes]].
        destruct Hr as [Hr Hrest]. have f1 := fine_inv _ _ Hr.
        destruct (extend_next_after_cell_is_cell _ _ _ _ _ _ _ _ _ row big2 f1) as [cells2'' Heq]. subst cells2'.
        have IH1 := IHcells2 a (cells1 ++ [c]) cells2'' Hrest big2.
        do 2 (rewrite <- List.app_assoc in IH1). apply IH1. simpl. apply row.
  Qed.
    
  Local Lemma read_l_v_gives_𝛼_row 𝛼 𝛽 𝜃 l cells v :
      read 𝛽 (inl l) cells (inr v) →
      big_inv 𝛼 𝛽 𝜃 →
      𝛼 !! inl l = Some (cells, v).
  Proof.
      intros Hr big.
      assert (big_inv 𝛼 𝛽 𝜃) as big2 by trivial.
      destruct big as [fine_inv [u_inv no_dupes]].
      destruct cells as [|cell cells].
       - unfold read in Hr. apply (fine_inv _ _ Hr).
       - destruct Hr as [Hr Hrest].
         have f1 := fine_inv _ _ Hr. unfold 𝛼_fine_pair in f1.
         destruct (𝛼 !! inl l) as [[[|c cells'] v']|] eqn:Hlookup; try done. subst cell.
         have rl := read_l_v_gives_𝛼_row' 𝛼 𝛽 𝜃 c _ [] cells cells' v v' Hrest big2 Hlookup.
         simpl in rl. rewrite <- rl. rewrite <- Hlookup. trivial.
  Qed.
  
  Local Lemma read_c_v_gives_𝛼_row 𝛼 𝛽 𝜃 c cells v :
      read 𝛽 (inr c) cells (inr v) →
      big_inv 𝛼 𝛽 𝜃 →
      ∃ k cells0 , 𝛼 !! k = Some (cells0 ++ c :: cells, v).
  Proof.
      intros Hr big.
      assert (big_inv 𝛼 𝛽 𝜃) as big2 by trivial.
      destruct big as [fine_inv [u_inv no_dupes]].
      destruct cells as [|cell cells].
       - unfold read in Hr. have f1 := fine_inv _ _ Hr. destruct f1 as [k [cs [Hk ends]]].
         destruct (facts_from_list_ends_with _ _ ends) as [cs' ->]. exists k, cs'. trivial.
       - destruct Hr as [Hr Hrest].
         have f1 := fine_inv _ _ Hr. unfold 𝛼_fine_pair in f1.
         destruct f1 as [k [cs [v' [Hk pair]]]].
         destruct (facts_from_list_has_pair _ _ _ pair) as [cs' [cs'' ->]].
         exists k, cs'.
         have rl := read_l_v_gives_𝛼_row' 𝛼 𝛽 𝜃 cell k (cs' ++ [c]) cells cs'' v v' Hrest big2.
         do 2 (rewrite <- List.app_assoc in rl).
         apply rl. apply Hk.
  Qed.
  
  Local Lemma read_l_c_gives_𝛼_row' 𝛼 𝛽 𝜃 c k cells1 cells2 cells2' c2 v' :
      read 𝛽 (inr c) cells2 (inl c2) →
      big_inv 𝛼 𝛽 𝜃 →
      𝛼 !! k = Some (cells1 ++ c :: cells2', v') →
      ∃ cells3, cells2' = cells2 ++ c2 :: cells3.
  Proof.
      induction cells2 in c, cells1, cells2' |- *.
      - intros Hr big row.
        assert (big_inv 𝛼 𝛽 𝜃) as big2 by trivial.
        destruct big as [fine_inv [u_inv no_dupes]].
        unfold read in Hr. have f1 := fine_inv _ _ Hr.
        destruct (extend_next_after_cell_is_cell _ _ _ _ _ _ _ _ _ row big2 f1)
            as [cells2'' Eq]. subst cells2'. exists cells2''. done.
      - intros Hr big row.
        assert (big_inv 𝛼 𝛽 𝜃) as big2 by trivial.
        destruct big as [fine_inv [u_inv no_dupes]].
        destruct Hr as [Hr Hrest]. have f1 := fine_inv _ _ Hr.
        destruct (extend_next_after_cell_is_cell _ _ _ _ _ _ _ _ _ row big2 f1)
            as [cells2'' Heq]. subst cells2'.
        have IH1 := IHcells2 a (cells1 ++ [c]) cells2'' Hrest big2.
        rewrite <- List.app_assoc in IH1. destruct (IH1 row) as [cells3 Eq].
        subst cells2''. exists cells3. done.
  Qed.
  
  Local Lemma read_l_c_gives_𝛼_row 𝛼 𝛽 𝜃 l cells c :
      read 𝛽 (inl l) cells (inl c) →
      big_inv 𝛼 𝛽 𝜃 →
      ∃ cells2 v , 𝛼 !! inl l = Some (cells ++ c :: cells2, v).
  Proof.
      intros Hr big.
      assert (big_inv 𝛼 𝛽 𝜃) as big2 by trivial.
      destruct big as [fine_inv [u_inv no_dupes]].
      destruct cells as [|cell cells].
       - unfold read in Hr. have Hf := (fine_inv _ _ Hr).
         unfold 𝛼_fine_pair in Hf. destruct (𝛼 !! inl l) as [[[|c0 cells] ?]|]; try done.
         subst c0. exists cells. exists v. trivial.
       - destruct Hr as [Hr Hrest].
         have f1 := fine_inv _ _ Hr. unfold 𝛼_fine_pair in f1.
         destruct (𝛼 !! inl l) as [[[|c0 cells'] v']|] eqn:Hlookup; try done. subst cell.
         have rl := read_l_c_gives_𝛼_row' 𝛼 𝛽 𝜃 c0 _ [] cells cells' c v' Hrest big2 Hlookup.
         destruct rl as [cells3 Heq]. subst cells'.
         exists cells3, v'. done.
  Qed.
    
  Local Lemma read_c_c_gives_𝛼_row 𝛼 𝛽 𝜃 c0 cells c :
      read 𝛽 (inr c0) cells (inl c) →
      big_inv 𝛼 𝛽 𝜃 →
      ∃ k cells1 cells2 v , 𝛼 !! k = Some (cells1 ++ c0 :: cells ++ c :: cells2, v).
  Proof.
      intros Hr big.
      assert (big_inv 𝛼 𝛽 𝜃) as big2 by trivial.
      destruct big as [fine_inv [u_inv no_dupes]].
      destruct cells as [|cell cells].
       - unfold read in Hr. have Hf := (fine_inv _ _ Hr).
         unfold 𝛼_fine_pair in Hf. destruct Hf as [k [allcells [v [Hk pair]]]].
         destruct (facts_from_list_has_pair _ _ _ pair) as [cs' [cs'' ->]].
         exists k, cs', cs'', v. simpl. apply Hk.
      - destruct Hr as [Hr Hrest].
         have f1 := fine_inv _ _ Hr. unfold 𝛼_fine_pair in f1.
         destruct f1 as [k [cs [v' [Hk pair]]]].
         destruct (facts_from_list_has_pair _ _ _ pair) as [cs' [cs'' ->]].
         have rl := read_l_c_gives_𝛼_row' 𝛼 𝛽 𝜃 cell k (cs' ++ [c0]) cells (cs'') c v' Hrest big2.
         rewrite <- List.app_assoc in rl.
         destruct (rl Hk) as [cells3 Heq]. subst cs''.
         exists k, cs', cells3, v'. simpl. apply Hk.
  Qed.
  
  Lemma read_duplicate_contradiction 𝛼 𝛽 𝜃 l c (cs1 cs2 cs3: list C) cv :
      big_inv 𝛼 𝛽 𝜃 →
      (* could be generalized to L+C *)
      read 𝛽 (inl l) (cs1 ++ c :: cs2 ++ c :: cs3) cv → False.
  Proof.
    intros big Hr. destruct cv as [c1|v1].
      - have Ha := read_l_c_gives_𝛼_row 𝛼 𝛽 𝜃 _ _ _ Hr big.
        destruct Ha as [cells2 [v Ha]]. do 2 (rewrite <- List.app_assoc in Ha; simpl in Ha).
        destruct big as [_ [_ no_dupes]].
        eauto using cells_no_dupes_duplicate_contradiction.
      - have Ha := read_l_v_gives_𝛼_row 𝛼 𝛽 𝜃 _ _ _ Hr big.
        destruct big as [fine_inv [u_inv no_dupes]].
        eauto using cells_no_dupes_duplicate_contradiction.
  Qed.
    
  Lemma read_last_not_in_prefix 𝛼 𝛽 𝜃 l prefix last cv :
      big_inv 𝛼 𝛽 𝜃 →
      read 𝛽 (inl l) (prefix ++ [last]) cv →
      last ∉ prefix.
  Proof.
      intros big Hr InPrefix. destruct (elem_of_list_split _ _ InPrefix) as [cs1 [cs2 Heq]].
      subst prefix. rewrite <- List.app_assoc in Hr. simpl in Hr.
      eauto using read_duplicate_contradiction.
  Qed.
    
  Local Lemma read_𝛽_cons_is_absent 𝛼 𝛽 𝜃 c cells cv :
      read 𝛽 (inr c) cells cv →
      big_inv 𝛼 𝛽 𝜃 →
      c ∉ cells.
  Proof.
      intros Hr big InCells.
      destruct (elem_of_list_split _ _ InCells) as [cs1 [cs2 Heq']]. subst cells.
      destruct cv as [c1|v1].
       - have Ha := read_c_c_gives_𝛼_row 𝛼 𝛽 ∅ _ _ _ Hr big.
         destruct Ha as [k [cells1 [cells2 [v Heq]]]].
         rewrite <- List.app_assoc in Heq. simpl in Heq.
         destruct big as [fine_inv [u_inv no_dupes]].
         eauto using cells_no_dupes_duplicate_contradiction.
       - have Ha := read_c_v_gives_𝛼_row 𝛼 𝛽 ∅ _ _ _ Hr big.
         destruct Ha as [k [cells1 Heq]].
         destruct big as [fine_inv [u_inv no_dupes]].
         eauto using cells_no_dupes_duplicate_contradiction.
  Qed.
  
  Local Lemma read_agrees 𝛼 𝛽 𝜃 l cells v :
      read 𝛽 (inl l) cells (inr v) →
      big_inv 𝛼 𝛽 𝜃 →
      𝜙 𝛼 !! l = Some v.
  Proof.
      rewrite 𝜙_lookup. intros Hr big.
      have H𝛼 := read_l_v_gives_𝛼_row _ _ _ _ _ _ Hr big. rewrite H𝛼. trivial.
  Qed.
  
  (* the bulk read operation *)
  
  Local Definition rrc_filter l (cells: list C) (k: (L+C) * (C+V)) :=
      match fst k with
        | inl l' => l' = l
        | inr c' => c' ∈ cells
      end.
      
  Local Definition rrc_filter_neg l (cells: list C) (k: (L+C) * (C+V)) := ¬ rrc_filter l cells k.
  
  Local Instance rrc_filter_dec l (cells: list C) (k: (L+C) * (C+V))
      : Decision (rrc_filter l cells k).
  Proof using C EqDecision0 EqDecision1 L V.
    destruct k as [[a|b] c]; unfold rrc_filter; simpl; solve_decision.
  Qed.
  
  Local Instance rrc_filter_dec_neg l (cells: list C) (k: (L+C) * (C+V))
      : Decision (rrc_filter_neg l cells k).
  Proof using C EqDecision0 EqDecision1 L V. unfold rrc_filter_neg. solve_decision. Qed.
  
  Local Lemma read_with_filter' 𝛽 l cells' c cells cv :
    read 𝛽 (inr c) cells cv →
    read (filter (rrc_filter l (cells' ++ c :: cells)) 𝛽) (inr c) cells cv.
  Proof.
    induction cells as [|c0 cells0] in c, cells' |- *.
     - unfold read. rewrite map_lookup_filter_Some. intros Hb. split; trivial.
       unfold rrc_filter. simpl. rewrite elem_of_app. right.
       rewrite elem_of_list_singleton; trivial.
     - intros [Hr Hrest]. split.
       + rewrite map_lookup_filter_Some. split; first trivial.
         unfold rrc_filter. simpl. rewrite elem_of_app. right. apply elem_of_cons.
         left; trivial.
       + have IH := IHcells0 (cells' ++ [c]) c0 Hrest.
         simpl in IH. rewrite <- List.app_assoc in IH. apply IH.
  Qed.
  
  Local Lemma read_with_filter 𝛽 l cells cv :
    read 𝛽 (inl l) cells cv →
    read (filter (rrc_filter l cells) 𝛽) (inl l) cells cv.
  Proof.
    destruct cells.
     - unfold read. rewrite map_lookup_filter_Some. done.
     - intros [Hr Hrest]. split.
       + rewrite map_lookup_filter_Some. done.
       + apply (read_with_filter' 𝛽 l [] c cells cv). apply Hrest.
  Qed.
    
  Local Lemma read_with_filter_comp' 𝛽 l cells c' cells' cv' :
    c' ∉ cells →
    (∀ c , c ∈ cells → c ∈ cells' → False) →
    read 𝛽 (inr c') cells' cv' →
    read (filter (rrc_filter_neg l cells) 𝛽) (inr c') cells' cv'.
  Proof.
    induction cells' as [|c0 cells0] in c' |- *.
     - unfold read. rewrite map_lookup_filter_Some. intros Hb. split; trivial.
     - intros Hnotin Hforall [Hr Hrest]. split.
       + rewrite map_lookup_filter_Some. split; first trivial. apply Hnotin.
       + apply IHcells0; trivial.
         * intros Hin. apply (Hforall c0 Hin). apply elem_of_cons. left; trivial.
         * intros c Hc Hc0. apply (Hforall c Hc). apply elem_of_cons; right; trivial.
  Qed.
  
  Local Lemma read_with_filter_comp 𝛽 l cells l' cells' cv' :
    l ≠ l' →
    (∀ c , c ∈ cells → c ∈ cells' → False) →
    read 𝛽 (inl l') cells' cv' →
    read (filter (rrc_filter_neg l cells) 𝛽) (inl l') cells' cv'.
  Proof.
    destruct cells'.
     - unfold read. rewrite map_lookup_filter_Some. intros Hb. split; trivial.
       unfold rrc_filter_neg, rrc_filter. simpl. done.
     - intros Hne Hforall [Hr Hrest]. split.
       + rewrite map_lookup_filter_Some. split; first trivial.
         unfold rrc_filter_neg, rrc_filter. simpl. done.
       + apply read_with_filter_comp'; trivial.
         * intros Hin. apply (Hforall c Hin). apply elem_of_cons. left; trivial.
         * intros c0 Hc Hc0. apply (Hforall c0 Hc). apply elem_of_cons; right; trivial.
  Qed.
  
  Local Lemma read_with_filter2 𝛼 𝛽 𝜃 l cells cv l' cells' cv' :
    big_inv 𝛼 𝛽 𝜃 →
    l ≠ l' →
    read 𝛽 (inl l) cells cv →
    read 𝛽 (inl l') cells' cv' →
    read (filter (rrc_filter_neg l cells) 𝛽) (inl l') cells' cv'.
  Proof.
    intros big Hne Hread Hread'. apply read_with_filter_comp; trivial.
    intros c Hc Hc'.
    destruct (elem_of_list_split _ _ Hc) as [d1 [d2 Heq]]. subst cells.
    destruct (elem_of_list_split _ _ Hc') as [d1' [d2' Heq']]. subst cells'.
    destruct cv as [c1|v1]; destruct cv' as [c1'|v1'].
     - destruct (read_l_c_gives_𝛼_row 𝛼 𝛽 𝜃 l _ c1 Hread big) as [cells2 [v Hrow]].
       destruct (read_l_c_gives_𝛼_row 𝛼 𝛽 𝜃 l' _ c1' Hread' big) as [cells2' [v' Hrow']].
       destruct big as [_ [_ no_dupes]].
       rewrite <- List.app_assoc in Hrow. simpl in Hrow.
       rewrite <- List.app_assoc in Hrow'. simpl in Hrow'.
       have H1 := cells_no_dupes_compare_rows _ _ _ _ _ _ _ _ _ c no_dupes Hrow Hrow'.
       destruct H1 as [x _]. inversion x. done.
     - destruct (read_l_c_gives_𝛼_row 𝛼 𝛽 𝜃 l _ c1 Hread big) as [cells2 [v Hrow]].
       have Hrow' := read_l_v_gives_𝛼_row 𝛼 𝛽 𝜃 l' _ v1' Hread' big.
       destruct big as [_ [_ no_dupes]].
       rewrite <- List.app_assoc in Hrow. simpl in Hrow.
       have H1 := cells_no_dupes_compare_rows _ _ _ _ _ _ _ _ _ c no_dupes Hrow Hrow'.
       destruct H1 as [x _]. inversion x. done.
     - have Hrow := read_l_v_gives_𝛼_row 𝛼 𝛽 𝜃 l _ v1 Hread big.
       destruct (read_l_c_gives_𝛼_row 𝛼 𝛽 𝜃 l' _ c1' Hread' big) as [cells2' [v' Hrow']].
       destruct big as [_ [_ no_dupes]].
       rewrite <- List.app_assoc in Hrow'. simpl in Hrow'.
       have H1 := cells_no_dupes_compare_rows _ _ _ _ _ _ _ _ _ c no_dupes Hrow Hrow'.
       destruct H1 as [x _]. inversion x. done.
     - have Hrow := read_l_v_gives_𝛼_row 𝛼 𝛽 𝜃 l _ v1 Hread big.
       have Hrow' := read_l_v_gives_𝛼_row 𝛼 𝛽 𝜃 l' _ v1' Hread' big.
       destruct big as [_ [_ no_dupes]].
       have H1 := cells_no_dupes_compare_rows _ _ _ _ _ _ _ _ _ c no_dupes Hrow Hrow'.
       destruct H1 as [x _]. inversion x. done.
  Qed.
  
  Local Lemma read_row_cons 𝛼 𝛽 𝜃 (rows: gmap L (list C * (C + V))) l cells cv :
      big_inv 𝛼 𝛽 𝜃 →
      rows !! l = None →
      read 𝛽 (inl l) cells cv →
      (∀ (l0 : L) (cells0 : list C) (cv0 : C + V),
          rows !! l0 = Some (cells0, cv0) → read 𝛽 (inl l0) cells0 cv0) →
      ∃ 𝛽₀ 𝛽₁, 𝛽 = 𝛽₀ ∪ 𝛽₁ ∧ 𝛽₀ ##ₘ 𝛽₁ ∧
      read 𝛽₀ (inl l) cells cv ∧
      (∀ (l0 : L) (cells0 : list C) (cv0 : C + V),
          rows !! l0 = Some (cells0, cv0) → read 𝛽₁ (inl l0) cells0 cv0).
  Proof.
      intros big Hrow Hread Hforall.
      exists (filter (rrc_filter l cells) 𝛽).
      exists (filter (rrc_filter_neg l cells) 𝛽).
      split; last split; last split.
      - apply map_eq. intros k. rewrite lookup_union.
        rewrite map_lookup_filter. rewrite map_lookup_filter.
        destruct (𝛽 !! k) as [[c|v]|] eqn:Hb; rewrite Hb; simpl; unfold guard;
          try done; case_decide; case_decide; done.
      - rewrite map_disjoint_spec. intros k a b.
        rewrite map_lookup_filter. rewrite map_lookup_filter.
        destruct (𝛽 !! k) as [[c|v]|] eqn:Hb; rewrite Hb; simpl; unfold guard;
          try done; case_decide; case_decide; done.
      - eauto using read_with_filter.
      - intros l' cells0 cv0 Hsome. have Hr := Hforall _ _ _ Hsome.
        assert (l ≠ l') as Hne. { intros Heq. subst l. rewrite Hrow in Hsome. discriminate. }
        eauto using read_with_filter2.
  Qed.
  
  (* write *)
        
  Lemma write_preserves_disjointness 𝛽 𝛽0 l cells cv cv' :
      read 𝛽 (inl l) cells cv → 𝛽 ##ₘ 𝛽0 → write 𝛽 l cells cv' ##ₘ 𝛽0.
  Proof.
      intros Hr. have Hl := read_get_last _ _ _ _ Hr. unfold write.
      intros Hdisj. enough (𝛽0 !! last_lc l cells = None). { solve_map_disjoint. }
      rewrite map_disjoint_alt in Hdisj. destruct (Hdisj (last_lc l cells)) as [a|b]; trivial.
      rewrite a in Hl. discriminate.
  Qed.
      
  Lemma read_of_write' 𝛼 𝛽 𝜃 (lc: L+C) (cells: list C) (c: C) (cv cv': C+V) :
      lc ≠ inr c →
      c ∉ cells →
      read 𝛽 lc (cells ++ [c]) cv →
      read (<[inr c:=cv']> 𝛽) lc (cells ++ [c]) cv'.
  Proof.
      induction cells in lc |- *.
       - intros Ha Hb [Hc Hd]. simpl. rewrite lookup_insert.
         rewrite lookup_insert_ne; last by done. split; trivial.
       - intros Ha Hb [Hc Hd]. simpl.
         rewrite lookup_insert_ne; last by done. split; trivial.
         rewrite not_elem_of_cons in Hb. destruct Hb as [Hne Hnotin].
         apply IHcells; trivial. intros He. inversion He. done.
  Qed.
  
  Lemma read_of_write 𝛼 𝛽 𝜃 (l: L) (cells: list C) (cv cv': C+V) :
      read 𝛽 (inl l) cells cv →
      big_inv 𝛼 𝛽 𝜃 →
      read (write 𝛽 l cells cv') (inl l) cells cv'.
  Proof.
      intros Hr big. unfold write. 
      destruct (case_last_lc l cells) as [[Hll Hcells]|[prefix [last [Hlc Hcells]]]].
       - subst cells. rewrite Hll. unfold read. rewrite lookup_insert. trivial.
       - rewrite Hlc. rewrite Hcells. rewrite Hcells in Hr.
         apply (read_of_write' 𝛼 𝛽 𝜃 _ _ _ cv); trivial; first by discriminate.
         apply (read_last_not_in_prefix 𝛼 𝛽 𝜃 _ _ _ _ big Hr).
  Qed.
    
  Lemma write_union 𝛽 𝛽0 l cells cv cv' :
      𝛽 ##ₘ 𝛽0 →
      read 𝛽 (inl l) cells cv →
      (write 𝛽 l cells cv') ∪ 𝛽0 = (write (𝛽 ∪ 𝛽0) l cells cv').
  Proof.
      unfold write. intros Hdisj Hr. rewrite insert_union_l. trivial.
  Qed.
  
  Definition 𝛼_write 𝛼 (l: L) (cells: list C) (v': V) :=
      <[ inl l := (cells, v') ]> 𝛼.
  
  Lemma write_updates_heap 𝛼 l cells v' :
      𝜙 (𝛼_write 𝛼 l cells v') = <[l:=v']> (𝜙 𝛼).
  Proof.
      apply 𝜙_insert_l.
  Qed.
  
  Lemma write_preserves_inv 𝛼 𝛽 𝜃 l v cells v' :
      read 𝛽 (inl l) cells (inr v) →
      big_inv 𝛼 𝛽 𝜃 →
      big_inv (𝛼_write 𝛼 l cells v') (write 𝛽 l cells (inr v')) 𝜃.
  Proof.
      intros Hread big.
      have H𝛼row := read_l_v_gives_𝛼_row 𝛼 𝛽 𝜃 l cells v Hread big.
      destruct big as [fine_inv [unt_inv cells_no_dupes]].
      split; last split.
      - intros src dst Hlookup'. unfold 𝛼_fine_pair, 𝛼_write. unfold write in Hlookup'.
        destruct (decide (src = last_lc l cells)).
        + subst src. rewrite lookup_insert in Hlookup'. inversion Hlookup'. subst dst.
          destruct (case_last_lc l cells) as [[Hll Hcells]|[prefix [last [Hlc Hcells]]]].
          * rewrite Hll. rewrite lookup_insert. rewrite Hcells. trivial.
          * rewrite Hlc. exists (inl l), cells. rewrite lookup_insert.
            split; trivial. subst cells. apply list_ends_with_app_r. done.
        + rewrite lookup_insert_ne in Hlookup'; last done.
          have f1 := (fine_inv src dst Hlookup'). unfold 𝛼_fine_pair in f1.
          destruct (decide (inl l = src)).
          * subst src. rewrite lookup_insert. rewrite H𝛼row in f1. destruct dst.
           -- apply f1.
           -- inversion f1. subst cells. done.
          * destruct src; last destruct dst.
            -- assert (l ≠ l0) by congruence.
               rewrite lookup_insert_ne; last by congruence. apply f1.
            -- destruct f1 as [lu1 [cs1 [v1 [Hsome Hpair]]]].
               destruct (decide (lu1 = inl l)) as [He2|Hn2].
               ++ subst lu1. rewrite H𝛼row in Hsome. inversion Hsome. subst v1. subst cs1.
                  exists (inl l), cells, v'. rewrite lookup_insert. split; trivial.
               ++ exists lu1, cs1, v1. rewrite lookup_insert_ne; last by done. split; trivial.
            -- destruct f1 as [lu1 [cs1 [Hsome Hpair]]].
               destruct (decide (lu1 = inl l)) as [He2|Hn2].
               ++ subst lu1. rewrite H𝛼row in Hsome. inversion Hsome. subst cs1. 
                  exfalso. apply n. apply list_ends_with_gives_last_lc. trivial.
               ++ exists lu1, cs1. rewrite lookup_insert_ne; last by done. split; trivial.
   - intros u1 cell1 v1 Hs. unfold 𝛼_write. rewrite lookup_insert_ne; last by done.
     apply (unt_inv _ _ _ Hs).
   - apply (cells_no_dupes_upd_value _ _ _ v); trivial.
  Qed.
  
  (* alloc cell *)
  
  Definition 𝛼_alloc_unt 𝛼 (u: untether_id) (c: C) (v: V) :=
      <[ inr u := ([c], v) ]> 𝛼.
        
  Lemma alloc_unt_preserves_heap 𝛼 u c v :
      𝜙 (𝛼_alloc_unt 𝛼 u c v) = 𝜙 𝛼.
  Proof.
      apply 𝜙_insert_u.
  Qed.
      
  Lemma alloc_unt_preserves_inv 𝛼 𝛽 𝜃 u c v :
      fresh_uid 𝛼 u →
      fresh_cell_id 𝛼 c →
      big_inv 𝛼 𝛽 𝜃 →
      big_inv (𝛼_alloc_unt 𝛼 u c v) (<[ inr c := inr v ]> 𝛽) (<[ u := (c, v) ]> 𝜃).
  Proof.
    intros freshu freshc big.
    destruct big as [fine_inv [unt_inv cells_no_dupes]].
    split; last split.
    - intros src dst Hlookup'. unfold 𝛼_fine_pair, 𝛼_alloc_unt. destruct src as [l'|c'].
      + rewrite lookup_insert_ne in Hlookup'; last by done.
        rewrite lookup_insert_ne; last by done. trivial.
        apply (fine_inv (inl l') dst Hlookup').
      + destruct (decide (c' = c)) as [He|Hn].
        * subst c'. rewrite lookup_insert in Hlookup'. inversion Hlookup'.
          exists (inr u), [c]. rewrite lookup_insert. split; done.
        * rewrite lookup_insert_ne in Hlookup'; last by congruence.
          have Hf := (fine_inv (inr c') dst Hlookup'). unfold 𝛼_fine_pair in Hf.
          destruct dst as [c''|v''].
          -- destruct Hf as [lu [cs [v1 [H𝛼lu Hpair]]]].
             have lu_ne := fresh_ne_to_existing_key _ _ _ _ H𝛼lu freshu.
             exists lu, cs, v1. rewrite lookup_insert_ne; last by done. split; trivial.
          -- destruct Hf as [lu [cs [H𝛼lu Hpair]]].
             have lu_ne := fresh_ne_to_existing_key _ _ _ _ H𝛼lu freshu.
             exists lu, cs. rewrite lookup_insert_ne; last by done. split; trivial.
  - intros u1 cell1 v1 Hs. 
    unfold 𝛼_alloc_unt. destruct (decide (u = u1)).
    + subst u1. rewrite lookup_insert in Hs. inversion Hs. subst cell1. subst v1.
      rewrite lookup_insert. split; trivial.
    + rewrite lookup_insert_ne in Hs; last by done. have Hu1 := unt_inv u1 cell1 v1 Hs.
      rewrite lookup_insert_ne; last by congruence. apply Hu1.
  - apply cells_no_dupes_of_fresh_singleton; trivial.
  Qed.
  
  (* untether cell *)
  
  Definition is_row_for_lc 𝛼
    (lc: L + C) (k: L + untether_id) (cells1: list C) (c: C) (cells2: list C) (v: V)
    := 𝛼 !! k = Some (cells1 ++ c :: cells2, v) ∧
        match k with
            | inl l => lc = last_lc l cells1
            | inr u => match last_c cells1 with Some c => lc = inr c | None => False end
        end.
  
  Lemma get_row_for_lc 𝛼 𝛽 𝜃 (lc: L + C) (c: C) :
      𝛽 !! lc = Some (inl c) →
      big_inv 𝛼 𝛽 𝜃 →
      ∃ k cells1 cells2 v, is_row_for_lc 𝛼 lc k cells1 c cells2 v.
  Proof.
      intros Hlc [fine_inv [u_inv cells_no_dupes]].
      have f1 := fine_inv lc (inl c) Hlc. unfold 𝛼_fine_pair in f1. unfold is_row_for_lc.
      destruct lc as [l|c'].
        - exists (inl l), [].
          destruct (𝛼 !! inl l) as [[[|c' cells'] v]|]; try contradiction.
          subst c'. exists cells', v. done.
        - destruct f1 as [k [cells [v [Hsome Hpair]]]].
          destruct (list_has_pair_destruct cells c' c Hpair) as [cells1 [cells2 Hcelleq]].
          subst cells. exists k, (cells1 ++ [c']), (cells2), v.
          rewrite <- List.app_assoc. simpl. split; first by trivial.
          destruct k.
           + rewrite list_last_lc_app_singleton. trivial.
           + rewrite list_last_c_app_singleton. trivial.
  Qed.
      
  Definition 𝛼_untether 𝛼 (lc: L + C) k cells1 c cells2 v u : full_map :=
      <[ k := (cells1, v) ]> (<[ inr u := (c :: cells2, v) ]> 𝛼).
  
  Lemma untether_preserves_heap 𝛼 lc k cells1 c cells2 v u :
      is_row_for_lc 𝛼 lc k cells1 c cells2 v →
      𝜙 (𝛼_untether 𝛼 lc k cells1 c cells2 v u) = 𝜙 𝛼.
  Proof using C EqDecision0 EqDecision1 H H0 Infinite_C L V.
      intros IsRow. unfold 𝛼_untether. unfold is_row_for_lc in IsRow. destruct k.
        - rewrite 𝜙_insert_l. rewrite 𝜙_insert_u. apply insert_id.
          rewrite 𝜙_lookup. destruct IsRow as [Eq Last]. rewrite Eq. trivial.
        - rewrite 𝜙_insert_u. rewrite 𝜙_insert_u. trivial.
  Qed.
  
  Lemma untether_preserves_inv 𝛼 𝛽 𝜃 (lc: L + C) k cells1 c cells2 v u :
      is_row_for_lc 𝛼 lc k cells1 c cells2 v →
      fresh_uid 𝛼 u →
      big_inv 𝛼 𝛽 𝜃 →
      big_inv (𝛼_untether 𝛼 lc k cells1 c cells2 v u)
        (<[ lc := inr v ]> 𝛽)
        (<[ u := (c, v) ]> 𝜃).
  Proof.
    intros Hr Hu big. 
    destruct big as [fine_inv [unt_inv cells_no_dupes]]. destruct Hr as [H𝛼k Hrow].
    have k_ne := fresh_ne_to_existing_key _ _ _ _ H𝛼k Hu.
    split; last split.
    - intros src dst Hlookup'. unfold 𝛼_fine_pair, 𝛼_untether.
      destruct (decide (src = lc)).
       + subst src. rewrite lookup_insert in Hlookup'. inversion Hlookup'.
         destruct lc as [l0|c0].
         * destruct k as [l1|u1].
           -- destruct (facts_from_last_lc_is_l _ _ _ Hrow) as [Hleq Hcellsempty].
              subst l1. subst cells1. rewrite lookup_insert. trivial.
           -- destruct (last_c cells1); done.
         * exists k, cells1. rewrite lookup_insert. split; trivial.
           destruct k as [l1|u1].
           -- destruct (facts_from_last_lc_is_c _ _ _ Hrow) as [prefix Hcellseq].
              rewrite Hcellseq. apply list_ends_with_app_singleton.
           -- destruct (last_c cells1) as [c2|] eqn:Hlasteq; last done.
              inversion Hrow. subst c2. apply list_ends_with_from_last_lc. trivial.
      + rewrite lookup_insert_ne in Hlookup'; last by done.
        have f1 := fine_inv src dst Hlookup'. unfold 𝛼_fine_pair in f1.
        destruct src as [l0|c0].
        * destruct (decide (inl l0 = k)) as [He1|Hn1].
          -- subst k.  rewrite lookup_insert. rewrite H𝛼k in f1. destruct dst.
            ++ destruct cells1.
              ** simpl in f1. subst c0. rewrite Hrow in n. done.
              ** simpl in f1. trivial.
            ++ inversion f1. rewrite app_nil in H2. inversion H2. done.
          -- do 2 (rewrite lookup_insert_ne; last by done). apply f1.
        * destruct dst as [c1|v1].
          -- destruct f1 as [k' [cells' [v' [H𝛼k' HasPair]]]].
             destruct (decide (k' = k)) as [Hn2|He2].
             ++ subst k'. rewrite H𝛼k in H𝛼k'. inversion H𝛼k'. subst v'. subst cells'.
                destruct (list_has_pair_app_case _ _ _ _ HasPair) as [front|[back|middle]].
              ** exists k, cells1, v. rewrite lookup_insert. split; trivial.
              ** exists (inr u), (c :: cells2), v.
                 rewrite lookup_insert_ne; last by done. rewrite lookup_insert.
                 split; trivial.
              ** destruct middle as [cells0 Hcellseq]. subst cells1.
                 destruct k.
                  --- rewrite list_last_lc_app_singleton in Hrow. done.
                  --- rewrite list_last_c_app_singleton in Hrow. done.
             ++ exists k', cells', v'.
                have k'_ne := fresh_ne_to_existing_key _ _ _ _ H𝛼k' Hu.
                do 2 (rewrite lookup_insert_ne; last by done).
                split; trivial.
          -- destruct f1 as [k' [cells' [H𝛼k' HasPair]]].
             destruct (decide (k' = k)) as [Hn2|He2].
             ++ subst k'. rewrite H𝛼k in H𝛼k'. inversion H𝛼k'. subst v1. subst cells'.
                have HasPair2 := (list_ends_with_app_r_rev _ _ _ _ HasPair).
                exists (inr u), (c :: cells2).
                rewrite lookup_insert_ne; last by done. rewrite lookup_insert.
                split; trivial.
             ++ exists k', cells'.
                have k'_ne := fresh_ne_to_existing_key _ _ _ _ H𝛼k' Hu.
                do 2 (rewrite lookup_insert_ne; last by done).
                split; trivial.
  - intros u1 cell1 v1 Hs. 
    unfold 𝛼_untether. destruct (decide (u = u1)).
    + subst u1. rewrite lookup_insert in Hs. inversion Hs. subst cell1. subst v1.
      rewrite lookup_insert_ne; last by done. rewrite lookup_insert. split; trivial.
    + rewrite lookup_insert_ne in Hs; last by done. have Hu1 := unt_inv u1 cell1 v1 Hs.
      destruct (decide (inr u1 = k)).
      * subst k. rewrite lookup_insert. rewrite H𝛼k in Hu1. destruct cells1; done.
      * rewrite lookup_insert_ne; last by done.
        rewrite lookup_insert_ne; last by congruence. trivial.
  - unfold 𝛼_untether. apply (cells_no_dupes_split_row _ _ _ _ _ _ _ v); trivial.
  Qed.
  
  (* retether cell *)
    
  Definition 𝛼_retether 𝛼 (u: untether_id) (l: L) (cells: list C) (v: V) (c': C) :=
      match 𝛼 !! (inr u) with
        | Some (cells', _) => <[ inl l := (cells ++ cells', v) ]> (delete (inr u) 𝛼)
        | None => 𝛼
      end. 
      
  Lemma retether_preserves_heap 𝛼 𝛽 𝜃 (u: untether_id) (l: L) (cells: list C) (v: V) (c': C) :
      read 𝛽 (inl l) cells (inr v) →     
      𝜃 !! u = Some (c', v) →
      big_inv 𝛼 𝛽 𝜃 →
      𝜙 (𝛼_retether 𝛼 u l cells v c') = 𝜙 𝛼.
  Proof.
      intros Hr Hl big. unfold 𝛼_retether. destruct (𝛼 !! inr u) as [p|]; last trivial.
      destruct p as [cells0 v0]. rewrite 𝜙_insert_l. rewrite 𝜙_delete_u.
      apply insert_id. apply (read_agrees _ _ _ _ _ _ Hr big).
  Qed.
  
  Lemma retether_preserves_inv 𝛼 𝛽 𝜃 (u: untether_id) (l: L) (cells: list C) (v: V) (c': C) :
      read 𝛽 (inl l) cells (inr v) →     
      𝜃 !! u = Some (c', v) →
      big_inv 𝛼 𝛽 𝜃 →
      big_inv (𝛼_retether 𝛼 u l cells v c')
          (write 𝛽 l cells (inl c'))
          (delete u 𝜃).
  Proof.
    intros Hr Hu big. 
    have H𝛼row := read_l_v_gives_𝛼_row 𝛼 𝛽 𝜃 l cells v Hr big.
    destruct big as [fine_inv [unt_inv cells_no_dupes]].
    have Hu1 := unt_inv u c' v Hu.
    destruct (𝛼 !! inr u) as [[[|c1 cells1] cv1]|] eqn:H𝛼u;
        last by contradiction. { contradiction. }
    destruct Hu1 as [Hu2 Hu3]. subst c1. subst cv1.
    split; last split.
    - intros src dst Hlookup'. destruct (decide (src = last_lc l cells)) as [He|Hn].
      + unfold write in Hlookup'. subst src. rewrite lookup_insert in Hlookup'.
        inversion Hlookup'. subst dst.
        unfold 𝛼_fine_pair.
        destruct (case_last_lc l cells) as [[Hll Hcs]|[prefix [last [Hll Hcs]]]].
        * subst cells. rewrite Hll. unfold 𝛼_retether. rewrite H𝛼u. rewrite lookup_insert.
          done.
        * subst cells. rewrite Hll. exists (inl l), (prefix ++ [last] ++ c' :: cells1), v.
          split; last by apply list_has_pair_app_app_cons.
          unfold 𝛼_retether. rewrite H𝛼u. rewrite lookup_insert.
          rewrite <- List.app_assoc. done.
     + unfold write in Hlookup'.
       rewrite lookup_insert_ne in Hlookup'; last by done.
       have f1 := fine_inv src dst Hlookup'. unfold 𝛼_fine_pair in *.
       destruct src as [sloc|scell].
       * unfold 𝛼_retether. rewrite H𝛼u. destruct (decide (sloc = l)) as [Hsl|Hsl].
         -- subst sloc. rewrite lookup_insert. rewrite H𝛼row in f1.
            destruct cells; first by contradiction. destruct dst as [dloc|dcell].
            ++ subst dloc. done.
            ++ inversion f1.
         -- rewrite lookup_insert_ne; last by congruence.
            rewrite lookup_delete_ne; last by discriminate. trivial.
       * destruct dst as [dcell|dval].
         -- destruct f1 as [lu0 [cells0 [v0 [Hin Hpair]]]].
            destruct (decide (lu0 = inr u)); last destruct (decide (lu0 = inl l)).
            ++ subst lu0. rewrite H𝛼u in Hin. inversion Hin. subst cells0. subst v0.
               exists (inl l), (cells ++ c' :: cells1), v.
               split; last by apply list_has_pair_app_r.
               unfold 𝛼_retether. rewrite H𝛼u. rewrite lookup_insert. done.
            ++ subst lu0. rewrite H𝛼row in Hin. inversion Hin. subst cells0. subst v0.
               exists (inl l), (cells ++ c' :: cells1), v.
               split; last by apply list_has_pair_app_l.
               unfold 𝛼_retether. rewrite H𝛼u. rewrite lookup_insert. done.
            ++ exists lu0, cells0, v0. unfold 𝛼_retether. rewrite H𝛼u.
               split; last by trivial.
               rewrite lookup_insert_ne; last by done.
               rewrite lookup_delete_ne; done.
        -- destruct f1 as [lu0 [cells0 [Hin Hends]]].
            destruct (decide (lu0 = inr u)); last destruct (decide (lu0 = inl l)).
            ++ subst lu0. rewrite H𝛼u in Hin. inversion Hin. subst cells0.
               exists (inl l), (cells ++ c' :: cells1).
               split; last by apply list_ends_with_app_r.
               unfold 𝛼_retether. rewrite H𝛼u. rewrite lookup_insert. done.
            ++ subst lu0. rewrite H𝛼row in Hin. inversion Hin. subst cells0.
               exfalso. apply Hn. apply list_ends_with_gives_last_lc. apply Hends.
            ++ exists lu0, cells0. unfold 𝛼_retether. rewrite H𝛼u.
               split; last by trivial.
               rewrite lookup_insert_ne; last by done.
               rewrite lookup_delete_ne; done.
   - intros u1 cell1 v1 Hl. destruct (decide (u = u1)) as [He|Hn].
     + subst u1. rewrite lookup_delete in Hl. discriminate.
     + rewrite lookup_delete_ne in Hl; last by trivial.
       unfold 𝛼_retether. rewrite H𝛼u. rewrite lookup_insert_ne; last by discriminate.
       rewrite lookup_delete_ne; last by congruence. apply unt_inv. apply Hl.
   - unfold 𝛼_retether. rewrite H𝛼u. apply (cells_no_dupes_join_2_rows _ _ _ v _ _ v); trivial.
     discriminate.
   Qed.
   
  (* Delete cell *)
  
  Definition 𝛼_delete_cell 𝛼 (k: L + untether_id) (cells1: list C) (cells2: list C) (v: V) :=
      <[ k := (cells1 ++ cells2, v) ]> 𝛼.
      
  Lemma delete_cell_preserves_heap 𝛼 lc k cells1 c cells2 v :
      is_row_for_lc 𝛼 lc k cells1 c cells2 v →
      𝜙 (𝛼_delete_cell 𝛼 k cells1 cells2 v) = 𝜙 𝛼.
  Proof using C EqDecision0 EqDecision1 H H0 L V.
      intros Hrow. unfold 𝛼_delete_cell. destruct k as [l|u].
        - rewrite 𝜙_insert_l. rewrite insert_id; trivial.
          rewrite 𝜙_lookup. by destruct Hrow as [-> _].
        - by rewrite 𝜙_insert_u.
  Qed.
  
  Lemma delete_cell_preserves_inv 𝛼 𝛽 𝜃
      (lc: L + C) (c: C) (cv: C + V)
      (k: L + untether_id) (cells1: list C) (cells2: list C) (v: V)  :
      𝛽 !! lc = Some (inl c) →
      𝛽 !! (inr c) = Some cv →
      is_row_for_lc 𝛼 lc k cells1 c cells2 v →
      big_inv 𝛼 𝛽 𝜃 →
      big_inv (𝛼_delete_cell 𝛼 k cells1 cells2 v) (<[ lc := cv ]> (delete (inr c) 𝛽)) 𝜃.
  Proof.
      intros Hb1 Hb2 Hr big.
      assert (big_inv 𝛼 𝛽 𝜃) as big2 by trivial.
      destruct big2 as [fine_inv [unt_inv cells_no_dupes]]. destruct Hr as [H𝛼k Hrow].
      have Hp1 := fine_inv _ _ Hb1.
      have Hp2 := fine_inv _ _ Hb2.
      split; last split.
      - intros src dst Hlookup'. unfold 𝛼_fine_pair, 𝛼_delete_cell.
        destruct (decide (src = lc)) as [He|Hn].
        + subst src. rewrite lookup_insert in Hlookup'. inversion Hlookup'. subst dst.
          destruct lc as [l0|c0].
         * destruct k as [l1|u1].
           -- destruct (facts_from_last_lc_is_l _ _ _ Hrow) as [Hleq Hcellsempty].
              subst l1. subst cells1. rewrite lookup_insert. destruct cv as [c2|v2].
             ++ have e1 := extend_next_after_cell_is_cell _ _ _ _ _ _ _ _ _ H𝛼k big Hp2.
                destruct e1 as [cells2' Eq]. subst cells2. done.
             ++ have e1 := extend_next_after_cell_is_value _ _ _ _ _ _ _ _ _ H𝛼k big Hp2.
                destruct e1 as [cells2' Eq]. subst cells2. subst v2. done.
           -- destruct (last_c cells1); done.
         * destruct cv as [c2|v2].
          -- exists k, (cells1 ++ cells2), v. rewrite lookup_insert. split; trivial.
             have e1 := extend_next_after_cell_is_cell _ _ _ _ _ _ _ _ _ H𝛼k big Hp2.
             destruct e1 as [cells2' Eq]. subst cells2. destruct k.
              ** destruct (facts_from_last_lc_is_c _ _ _ Hrow) as [prefix Eq]. subst cells1.
                 rewrite <- List.app_assoc. simpl. apply list_has_pair_mid.
              ** destruct (case_last_c cells1) as [[Hnone Heq]|[prefix [last [Hsome Heq]]]].
                --- rewrite Hnone in Hrow; contradiction.
                --- rewrite Hsome in Hrow. inversion Hrow. subst last. subst cells1.
                    rewrite <- List.app_assoc. simpl. apply list_has_pair_mid.
          -- exists k, (cells1 ++ cells2). rewrite lookup_insert.
             have e1 := extend_next_after_cell_is_value _ _ _ _ _ _ _ _ _ H𝛼k big Hp2.
             destruct e1 as [cells2' Eq]. subst cells2. subst v2. split; trivial.
             rewrite right_id_L. destruct k.
              ** destruct (facts_from_last_lc_is_c _ _ _ Hrow) as [prefix Eq]. subst cells1.
                 apply list_ends_with_app_singleton.
              ** destruct (case_last_c cells1) as [[Hnone Heq]|[prefix [last [Hsome Heq]]]].
                --- rewrite Hnone in Hrow; contradiction.
                --- rewrite Hsome in Hrow. inversion Hrow. subst last. subst cells1.
                    apply list_ends_with_app_singleton.
        + rewrite lookup_insert_ne in Hlookup'; last by done.
          destruct (decide (src = inr c)).
              { subst src. rewrite lookup_delete in Hlookup'. discriminate. }
          rewrite lookup_delete_ne in Hlookup'; last by done.
          have f1 := fine_inv _ _ Hlookup'. unfold 𝛼_fine_pair in f1.
          destruct src as [l0|c0].
          * destruct (decide (inl l0 = k)) as [He1|Hn1].
            -- subst k.  rewrite lookup_insert. rewrite H𝛼k in f1. destruct dst.
              ++ destruct cells1.
                ** simpl in f1. subst c0. rewrite Hrow in Hn. done.
                ** simpl in f1. trivial.
              ++ inversion f1. rewrite app_nil in H2. inversion H2. done.
            -- rewrite lookup_insert_ne; last by done. apply f1.
          * destruct dst as [c1|v1].
          -- destruct f1 as [k' [cells' [v' [H𝛼k' HasPair]]]].
             destruct (decide (k' = k)) as [Hn2|He2].
             ++ subst k'. rewrite H𝛼k in H𝛼k'. inversion H𝛼k'. subst v'. subst cells'.
                destruct (list_has_pair_app_case _ _ _ _ HasPair) as [front|[back|middle]].
              ** exists k, (cells1 ++ cells2), v. rewrite lookup_insert. split; trivial.
                 apply list_has_pair_app_l. trivial.
              ** exists k, (cells1 ++ cells2), v. rewrite lookup_insert. split; trivial.
                 apply list_has_pair_app_r. apply (list_has_pair_uncons cells2 c); trivial.
                 congruence.
              ** destruct middle as [cells0 Hcellseq]. subst cells1.
                 destruct k.
                  --- rewrite list_last_lc_app_singleton in Hrow. done.
                  --- rewrite list_last_c_app_singleton in Hrow. done.
             ++ exists k', cells', v'.
                rewrite lookup_insert_ne; last by done. split; trivial.
          -- destruct f1 as [k' [cells' [H𝛼k' HasPair]]].
             destruct (decide (k' = k)) as [Hn2|He2].
             ++ subst k'. rewrite H𝛼k in H𝛼k'. inversion H𝛼k'. subst v1. subst cells'.
                have HasPair2 := (list_ends_with_app_r_rev _ _ _ _ HasPair).
                exists k, (cells1 ++ cells2). rewrite lookup_insert. split; trivial.
                apply list_ends_with_app_r. apply (list_ends_with_uncons _ c); trivial.
                congruence.
             ++ exists k', cells'. rewrite lookup_insert_ne; last by done. split; trivial.
   - intros u1 cell1 v1 Hs. 
     unfold 𝛼_delete_cell. 
     have Hu1 := unt_inv u1 cell1 v1 Hs.
     destruct (decide (inr u1 = k)).
      + subst k. rewrite lookup_insert. rewrite H𝛼k in Hu1. destruct cells1; first by done.
        apply Hu1.
      + rewrite lookup_insert_ne; last by done. apply Hu1.
   - apply (cells_no_dupes_remove_mid _ _ _ c); trivial.
  Qed.
     
  (* Insert fresh cell *)
  
  Definition 𝛼_insert_fresh_cell 𝛼 (k: L + untether_id) (cells1: list C) (c new_c: C) (cells2: list C)  (v: V) :=
      <[ k := (cells1 ++ c :: new_c :: cells2, v) ]> 𝛼.
      
  Lemma insert_fresh_cell_preserves_heap 𝛼 k cells1 c new_c cells2 v :
      fresh_cell_id 𝛼 new_c →
      𝛼 !! k = Some (cells1 ++ c :: cells2, v) →
      𝜙 (𝛼_insert_fresh_cell 𝛼 k cells1 c new_c cells2 v) = 𝜙 𝛼.
  Proof using C EqDecision0 EqDecision1 H H0 L V.
      intros Hfresh Hrow. unfold 𝛼_insert_fresh_cell. destruct k as [l|u].
        - rewrite 𝜙_insert_l. rewrite insert_id; trivial.
          rewrite 𝜙_lookup. rewrite Hrow. trivial.
        - by rewrite 𝜙_insert_u.
  Qed.
  
  Lemma list_lasts_eq (cells1 cells2 : list C) (c1 c2: C) :
      cells1 ++ [c1] = cells2 ++ [c2] → c1 = c2.
  Proof.
      generalize cells2. clear cells2. induction cells1.
       - intros cells2 H1. destruct cells2.
        + simpl in H1. inversion H1. done.
        + inversion H1. exfalso. destruct cells2; done.
       - intros cells2. intros Ha. destruct cells2.
        + destruct cells1; done.
        + simpl in Ha. inversion Ha. apply (IHcells1 _ H3).
  Qed.
  
   
  Local Lemma no_dup_insert1 cs1 cs2 cs3 (c: C) :
      ¬(c ∈ ((cs1 ++ cs2) ++ cs3)) →
      NoDup ((cs1 ++ cs2) ++ cs3) → NoDup ((cs1 ++ c :: cs2) ++ cs3).
  Proof.
      repeat (rewrite NoDup_app). repeat (rewrite NoDup_cons).
      intros Hnotin [[Ha Hd] [Hb Hc]]. rewrite elem_of_app in Hnotin.
      rewrite elem_of_app in Hnotin. intuition.
       - rewrite elem_of_cons in H7. destruct H7 as [Hx|Hy].
         + subst x. intuition.
         + apply (H1 x); trivial.
       - rewrite elem_of_app in H3. destruct H3 as [Hx|Hy].
         + apply (Hb x); trivial. rewrite elem_of_app; left; trivial.
         + rewrite elem_of_cons in Hy. destruct Hy as [Hy|Hz].
           * subst x. intuition.
           * apply (Hb x); trivial. rewrite elem_of_app; right; trivial.
  Qed.
   
  Local Lemma cells_no_dupes_insert_mid 𝛼 k cells1 c cells2 v :
      fresh_cell_id 𝛼 c →
      𝛼 !! k = Some (cells1 ++ cells2, v) →
      cells_no_dupes 𝛼 →
      cells_no_dupes (<[ k := (cells1 ++ c :: cells2, v) ]> 𝛼).
  Proof.
      intros Hfresh Hsome Hc.
      assert ((<[k := (cells1 ++ cells2, v)]> (delete k 𝛼)) = 𝛼) as X. {
          apply insert_delete. trivial.
      }
      rewrite <- X in Hc. unfold cells_no_dupes, cell_list in Hc.
      rewrite (map_fold_insert (≡ₚ)) in Hc; try eauto using cell_list_build_assoc;
          last by apply lookup_delete.
      rewrite <- X in Hfresh. unfold fresh_cell_id, cell_list in Hfresh.
      rewrite (map_fold_insert (≡ₚ)) in Hfresh; try eauto using cell_list_build_assoc;
          last by apply lookup_delete.
      rewrite <- (insert_delete_insert 𝛼). unfold cells_no_dupes, cell_list.
      rewrite (map_fold_insert (≡ₚ)); try eauto using cell_list_build_assoc;
          last by apply lookup_delete.
      unfold cell_list_build. unfold cell_list_build in Hc.
      apply (no_dup_insert1 _ _ _ c); last trivial.
      apply Hfresh.
  Qed.
  
  Lemma get_row_containing_cell 𝛼 𝛽 𝜃 c cv :
      big_inv 𝛼 𝛽 𝜃 →
      𝛽 !! (inr c) = Some cv →
      ∃ k cells1 cells2 v, 𝛼 !! k = Some (cells1 ++ c :: cells2, v).
  Proof.
      intros Hinv Hb. destruct Hinv as [fine_inv _].
      have f := fine_inv _ _ Hb. unfold 𝛼_fine_pair in f. destruct cv as [c0|v0].
      - destruct f as [lu [cs [v [Hx1 Hx2]]]].
        destruct (list_has_pair_destruct _ _ _ Hx2) as [cells1 [cells2 Heq]].
        exists lu, cells1, (c0 :: cells2), v. subst cs. trivial.
      - destruct f as [lu [cs [Hx1 Hx2]]].
        destruct (facts_from_list_ends_with cs c Hx2) as [cs' Heq]. subst cs.
        exists lu. exists cs'. exists []. exists v0. trivial.
  Qed.
 
  Lemma insert_fresh_cell_preserves_inv 𝛼 𝛽 𝜃
      (c: C) (cv: C + V)
      (k: L + untether_id) (cells1: list C) (new_c: C) (cells2: list C) (v: V)  :
      𝛽 !! (inr c) = Some cv →
      fresh_cell_id 𝛼 new_c →
      𝛼 !! k = Some (cells1 ++ c :: cells2, v) →
      big_inv 𝛼 𝛽 𝜃 →
      big_inv (𝛼_insert_fresh_cell 𝛼 k cells1 c new_c cells2 v)
        (<[ inr c := inl new_c ]> (<[ inr new_c := cv ]> 𝛽)) 𝜃.
  Proof.
      intros Hb1 Hfresh Hr big.
      assert (big_inv 𝛼 𝛽 𝜃) as big2 by trivial.
      destruct big2 as [fine_inv [unt_inv cells_no_dupes]].
      have Hp1 := fine_inv _ _ Hb1.
      split; last split.
      - intros src dst Hlookup'. unfold 𝛼_fine_pair, 𝛼_delete_cell.
        destruct (decide (src = inr c)) as [He|Hn].
        + subst src. rewrite lookup_insert in Hlookup'. inversion Hlookup'. subst dst.
          exists k. exists (cells1 ++ c :: new_c :: cells2). exists v.
          split; last by apply list_has_pair_mid.
          unfold 𝛼_insert_fresh_cell. rewrite lookup_insert. trivial.
        + rewrite lookup_insert_ne in Hlookup'; last by done.
          destruct (decide (src = inr new_c)) as [He|Hn'].
          * subst src. rewrite lookup_insert in Hlookup'. inversion Hlookup'. subst dst.
            destruct cv as [c2|v2].
          -- exists k, (cells1 ++ c :: new_c :: cells2), v. 
             split.
             ++ unfold 𝛼_insert_fresh_cell. rewrite lookup_insert. trivial.
             ++ have e1 := extend_next_after_cell_is_cell _ _ _ _ _ _ _ _ _ Hr big Hp1.
                destruct e1 as [cells2' e1]. subst cells2.
                replace ((cells1 ++ c :: new_c :: c2 :: cells2'))
                   with ((cells1 ++ [c]) ++ new_c :: c2 :: cells2').
                ** apply list_has_pair_mid.
                ** rewrite <- List.app_assoc. done.
          -- exists k, (cells1 ++ c :: new_c :: cells2).
             have e1 := extend_next_after_cell_is_value _ _ _ _ _ _ _ _ _ Hr big Hp1.
             destruct e1 as [Hcells2eq Hveq]. subst cells2. subst v2.
             split.
             ++ unfold 𝛼_insert_fresh_cell. rewrite lookup_insert. trivial.
             ++ replace (cells1 ++ [c; new_c]) with ((cells1 ++ [c]) ++ [new_c]).
               ** apply list_ends_with_app_singleton.
               ** rewrite <- List.app_assoc. done.
          * rewrite lookup_insert_ne in Hlookup'; last by done.
            have f1 := fine_inv _ _ Hlookup'. unfold 𝛼_fine_pair in f1.
            destruct src as [l0|c0].
              ** destruct (decide (inl l0 = k)) as [He1|Hn1].
                -- subst k.  rewrite lookup_insert. rewrite Hr in f1. destruct dst.
                  ++ destruct cells1.
                    *** simpl in f1. subst c0. done.
                    *** simpl in f1. trivial.
                  ++ inversion f1. rewrite app_nil in H2. inversion H2. done.
                -- rewrite lookup_insert_ne; last by done. apply f1.
              ** destruct dst as [c1|v1].
              -- destruct f1 as [k' [cells' [v' [H𝛼k' HasPair]]]].
                destruct (decide (k' = k)) as [Hn2|He2].
                ++ subst k'. rewrite Hr in H𝛼k'. inversion H𝛼k'. subst v'. subst cells'.
                   replace (cells1 ++ c :: cells2) with ((cells1 ++ [c]) ++ cells2) in HasPair.
                    2: { rewrite <- List.app_assoc. done. }
                    destruct (list_has_pair_app_case _ _ _ _ HasPair) as [front|[back|middle]].
                    *** exists k, (cells1 ++ c :: new_c :: cells2), v. rewrite lookup_insert. split; trivial. 
                    replace (cells1 ++ c :: new_c :: cells2) with ((cells1 ++ [c]) ++ (new_c :: cells2)).
                     ---- apply list_has_pair_app_l. trivial.
                     ---- rewrite <- List.app_assoc. done.
                  *** exists k, (cells1 ++ c :: new_c :: cells2), v. rewrite lookup_insert. split; trivial.
                    replace (cells1 ++ c :: new_c :: cells2) with ((cells1 ++ [c]) ++ (new_c :: cells2)).
                    ---- apply list_has_pair_app_r. apply (list_has_pair_cons); trivial.
                    ---- rewrite <- List.app_assoc. done.
                  *** destruct middle as [cells0 Hcellseq]. 
                    have Heq := (list_lasts_eq _ _ _ _ Hcellseq). subst c0. done.
                    
                ++ exists k', cells', v'.
                    rewrite lookup_insert_ne; last by done. split; trivial.
             -- destruct f1 as [k' [cells' [H𝛼k' HasPair]]].
             destruct (decide (k' = k)) as [Hn2|He2].
             ++ subst k'. rewrite Hr in H𝛼k'. inversion H𝛼k'. subst v1. subst cells'.
                have HasPair2 := (list_ends_with_app_r_rev _ _ _ _ HasPair).
                exists k, (cells1 ++ c :: new_c :: cells2). rewrite lookup_insert. split; trivial.
                apply list_ends_with_app_r.
                replace (c :: new_c :: cells2) with ([c; new_c] ++ cells2); last by done.
                apply list_ends_with_app_r.
                apply (list_ends_with_uncons _ c); trivial.
                congruence.
             ++ exists k', cells'. rewrite lookup_insert_ne; last by done. split; trivial.
   - intros u1 cell1 v1 Hs. 
     unfold 𝛼_delete_cell. 
     have Hu1 := unt_inv u1 cell1 v1 Hs.
     destruct (decide (inr u1 = k)).
      + subst k. rewrite lookup_insert. rewrite Hr in Hu1. destruct cells1; first by done.
        apply Hu1.
      + rewrite lookup_insert_ne; last by done. apply Hu1.
   - unfold 𝛼_insert_fresh_cell.
     replace (cells1 ++ c :: new_c :: cells2) with ((cells1 ++ [c]) ++ new_c :: cells2).
      2: { rewrite <- List.app_assoc. done. }
     apply (cells_no_dupes_insert_mid _ _ _ new_c); trivial.
     rewrite <- List.app_assoc. apply Hr.
  Qed.
  
  (* RA defn *)
  
  Inductive cmap_car :=
    | COk (σ: option heap_map) (𝛽: fine_map) (𝜃: unt_map)
    | CFail.
  
  Instance cmap_op : Op cmap_car := λ a b, match a, b with
      | COk (Some _) _ _, COk (Some _) _ _ => CFail
      | COk σ 𝛽 𝜃, COk σ' 𝛽' 𝜃'  => 
          if bool_decide(𝛽 ##ₘ 𝛽' ∧ 𝜃 ##ₘ 𝜃') then
              COk (match σ with Some _ => σ | None => σ' end) (𝛽 ∪ 𝛽') (𝜃 ∪ 𝜃')
          else
              CFail
      | _, _ => CFail
  end.
  
  Instance cmap_valid : Valid cmap_car := λ a, match a with
      | COk (Some h) 𝛽 𝜃 => ∃ 𝛼 , 𝜙 𝛼 = h ∧ big_inv 𝛼 𝛽 𝜃
      | COk None 𝛽 𝜃 => ∃ 𝛼 , big_inv 𝛼 𝛽 𝜃
      | CFail => False
  end.
  
  Instance cmap_equiv : Equiv cmap_car := λ a b , a = b.

  Instance cmap_pcore : PCore cmap_car := λ a , Some (COk None ∅ ∅).
  
  Lemma cmap_assoc : Assoc (=) cmap_op.
  Proof.
    intros x y z.
    destruct x as [[σ1|] 𝛽1 𝜃1|], y as [[σ2|] 𝛽2 𝜃2|], z as [[σ3|] 𝛽3 𝜃3|];
      unfold cmap_op; try done;
    repeat case_bool_decide; try done; try f_equal; trivial;
    try (apply map_union_assoc; destruct_and?; solve_map_disjoint);
    try (exfalso; (match goal with | [ H' : ¬ _ |- _ ] =>
        apply H'; destruct_and?; solve_map_disjoint end)).
  Qed.
  
  Lemma cmap_comm : Comm (=) cmap_op.
  Proof.
    intros x y. destruct x as [[σ1|] 𝛽1 𝜃1|], y as [[σ2|] 𝛽2 𝜃2|]; unfold cmap_op; try done;
    repeat case_bool_decide; try done; try f_equal; trivial;
      try (apply map_union_comm; destruct_and?; solve_map_disjoint);
      try (exfalso; (match goal with | [ H' : ¬ _ |- _ ] =>
        apply H'; destruct_and?; solve_map_disjoint end)).
  Qed.
  
  Lemma fine_map_inv_mono 𝛼 𝛽 𝛽' :
    𝛽 ##ₘ 𝛽' →
    fine_map_inv 𝛼 (𝛽 ∪ 𝛽') →
    fine_map_inv 𝛼 𝛽.
  Proof.
    intros Hdisj Ha src dst Hin. apply Ha. rewrite lookup_union. rewrite Hin.
      apply union_Some_l.
  Qed.
  
  Lemma unt_map_inv_mono 𝛼 𝜃 𝜃' :
    𝜃 ##ₘ 𝜃' →
    unt_map_inv 𝛼 (𝜃 ∪ 𝜃') →
    unt_map_inv 𝛼 𝜃.
  Proof.
    intros Hdisj Ha src c val Hin. apply Ha. rewrite lookup_union. rewrite Hin.
      unfold union, option_union, union_with, option_union_with.
      destruct (𝜃' !! src) eqn:He; rewrite He; trivial.
  Qed.
  
  Lemma big_inv_mono 𝛼 𝛽 𝛽' 𝜃 𝜃' :
    𝛽 ##ₘ 𝛽' → 𝜃 ##ₘ 𝜃' →
    big_inv 𝛼 (𝛽 ∪ 𝛽') (𝜃 ∪ 𝜃') →
    big_inv 𝛼 𝛽 𝜃.
  Proof.
    intros H𝛽 H𝜃 [a [b c]].
    split. { eapply (fine_map_inv_mono 𝛼 𝛽 𝛽'); trivial. }
    split. { eapply (unt_map_inv_mono 𝛼 𝜃 𝜃'); trivial. }
    trivial.
  Qed.
  
  Lemma left_id x :
      (COk None ∅ ∅) ⋅ x = x.
  Proof.
    destruct x as [[h|] 𝛽 𝜃|].
      + unfold "⋅", cmap_op. case_bool_decide.
        * do 2 rewrite map_empty_union. trivial.
        * exfalso. apply H1. split; apply map_disjoint_empty_l.
      + unfold "⋅", cmap_op. case_bool_decide.
        * do 2 rewrite map_empty_union. trivial.
        * exfalso. apply H1. split; apply map_disjoint_empty_l.
      + done.
  Qed.
  
  Lemma right_id x :
      x ⋅ (COk None ∅ ∅) = x.
  Proof.
      unfold "⋅". rewrite cmap_comm. apply left_id.
  Qed.
  
  Lemma op_cfail x : x ⋅ CFail = CFail.
  Proof. destruct x as [[σ|] 𝛽 𝜃|]; try done. Qed.
  
  Local Lemma op_split_out_𝛽 o 𝛽 𝜃 :
     (COk o 𝛽 𝜃) = (COk o ∅ 𝜃) ⋅ (COk None 𝛽 ∅).
  Proof.
      destruct o; unfold "⋅", cmap_op; case_bool_decide as Hdisj.
      + rewrite map_empty_union. rewrite map_union_empty. done.
      + exfalso. apply Hdisj. solve_map_disjoint.
      + rewrite map_empty_union. rewrite map_union_empty. done.
      + exfalso. apply Hdisj. solve_map_disjoint.
  Qed.
  
  Definition cmap_ra_mixin : RAMixin cmap_car.
  Proof. split.
    - typeclasses eauto.
    - intros. exists cx. done.
    - typeclasses eauto.
    - apply cmap_assoc.
    - apply cmap_comm.
    - intros x cx H2. unfold pcore, cmap_pcore in H2. inversion H2. apply left_id.
    - intros x cx H2. unfold pcore, cmap_pcore in H2. inversion H2. done.
    - intros x y cx incl H2. unfold pcore, cmap_pcore in H2. inversion H2. exists (COk None ∅ ∅). split; try done. exists (COk None ∅ ∅). rewrite left_id; trivial.
    - intros x y. destruct x as [[h|] 𝛽 𝜃|]; destruct y as [[h'|] 𝛽' 𝜃'|]; try done.
      + unfold "✓", cmap_valid, "⋅", cmap_op. case_bool_decide; try done.
        intros [𝛼 [Ha Inv]]. exists 𝛼. split; trivial.
        apply (big_inv_mono 𝛼 𝛽 𝛽' 𝜃 𝜃'); intuition.
      + unfold "✓", cmap_valid, "⋅", cmap_op. case_bool_decide; try done.
        intros [𝛼 [Ha Inv]]. exists 𝛼.
        apply (big_inv_mono 𝛼 𝛽 𝛽' 𝜃 𝜃'); intuition.
      + unfold "✓", cmap_valid, "⋅", cmap_op. case_bool_decide; try done.
        intros [𝛼 Inv]. exists 𝛼.
        apply (big_inv_mono 𝛼 𝛽 𝛽' 𝜃 𝜃'); intuition.
  Qed.
  
  Canonical Structure cmapO := discreteO cmap_car.
  
  Canonical Structure cmapR := discreteR cmap_car cmap_ra_mixin.

  Global Instance cmap_cmra_discrete : CmraDiscrete cmapR.
  Proof. apply discrete_cmra_discrete. Qed.

  Global Instance cmap_unit : Unit cmap_car := COk None ∅ ∅.
  
  Lemma big_inv_empty : big_inv ∅ ∅ ∅.
  Proof.
    unfold big_inv. split. { done. } split. { done. }
    unfold cells_no_dupes, cell_list. rewrite map_fold_empty. by apply NoDup_nil.
  Qed.

  Definition cmap_ucmra_mixin : UcmraMixin cmap_car.
  Proof.
    split; trivial.
    - exists ∅. apply big_inv_empty.
    - intro x. apply left_id.
  Qed.

  Canonical Structure cmapUR := Ucmra cmap_car cmap_ucmra_mixin.
  
  Definition ra_σ σ := COk (Some σ) ∅ ∅.
  Definition ra_𝛽 𝛽 := COk None 𝛽 ∅.
  Definition ra_𝜃 𝜃 := COk None ∅ 𝜃.
  Definition ra_pt (lc: L + C) (cv: C + V) := ra_𝛽 {[ lc := cv ]}.
  Definition ra_unt (uid: untether_id) (c: C) (v: V) := ra_𝜃 {[ uid := (c, v) ]}.
  
  (* updates *)
  
  Local Lemma ra_𝛽_split 𝛽₀ 𝛽₁ :
    𝛽₀ ##ₘ 𝛽₁ →
    ra_𝛽 (𝛽₀ ∪ 𝛽₁) = ra_𝛽 𝛽₀ ⋅ ra_𝛽 𝛽₁.
  Proof.
    unfold "⋅", cmap_op, ra_𝛽. intros Hdisj. case_bool_decide as Hd; trivial.
    exfalso. apply Hd. solve_map_disjoint.
  Qed.
  
(*  Lemma upd_helper_general σ σ old𝛽 new𝛽 old𝜃 new𝜃 :
      (∀ 𝛼 𝛽 𝜃 , 𝛽 ##ₘ old𝛽 → 𝜃 ##ₘ old𝜃 →
      ra_σ σ ~~> ra_σ σ' ⋅ ra_𝛽 sub𝛽.*)
      
  Lemma upd_helper_l_𝛽𝜃_r_𝛽 old𝛽 new𝛽 old𝜃 :
      (∀ 𝛼 𝛽 𝜃 , old𝛽 ##ₘ 𝛽 → old𝜃 ##ₘ 𝜃 → big_inv 𝛼 (old𝛽 ∪ 𝛽) (old𝜃 ∪ 𝜃) → 
        ∃ 𝛼', 𝜙 𝛼' = 𝜙 𝛼 ∧ new𝛽 ##ₘ 𝛽 ∧ big_inv 𝛼' (new𝛽 ∪ 𝛽) 𝜃)
      → ra_𝛽 old𝛽 ⋅ ra_𝜃 old𝜃 ~~> ra_𝛽 new𝛽.
  Proof.
      intros Ha. rewrite cmra_discrete_total_update.
      intros z Hval. destruct z as [[σ2|] 𝛽 𝜃|].
      - unfold "✓", cmra_valid, cmapR, cmap_valid, "⋅", cmra_op, cmap_op, ra_σ, ra_𝛽, ra_𝜃 in Hval.
        case_bool_decide; last by done. case_bool_decide as Hdisj; last by done.
        destruct Hval as [𝛼 [heap inv]].
        rewrite map_empty_union in inv. rewrite map_union_empty in inv.
        destruct Hdisj as [Hdisj𝛽 Hdisj𝜃].
        rewrite map_union_empty in Hdisj𝛽. rewrite map_empty_union in Hdisj𝜃.
        destruct (Ha 𝛼 𝛽 𝜃 Hdisj𝛽 Hdisj𝜃 inv) as [𝛼' [Hheap [Hdisj𝛽' inv']]].
        unfold "✓", cmra_valid, cmapR, cmap_valid, "⋅", cmra_op, cmap_op, ra_σ, ra_𝛽, ra_𝜃.
        case_bool_decide as Hd.
         + exists 𝛼'. rewrite <- heap. rewrite map_empty_union. split; trivial.
         + apply Hd. solve_map_disjoint.
      - unfold "✓", cmra_valid, cmapR, cmap_valid, "⋅", cmra_op, cmap_op, ra_σ, ra_𝛽, ra_𝜃 in Hval.
        case_bool_decide; last by done. case_bool_decide as Hdisj; last by done.
        destruct Hval as [𝛼 inv].
        rewrite map_empty_union in inv. rewrite map_union_empty in inv.
        destruct Hdisj as [Hdisj𝛽 Hdisj𝜃].
        rewrite map_union_empty in Hdisj𝛽. rewrite map_empty_union in Hdisj𝜃.
        destruct (Ha 𝛼 𝛽 𝜃 Hdisj𝛽 Hdisj𝜃 inv) as [𝛼' [Hheap [Hdisj𝛽' inv']]].
        unfold "✓", cmra_valid, cmapR, cmap_valid, "⋅", cmra_op, cmap_op, ra_σ, ra_𝛽, ra_𝜃.
        case_bool_decide as Hd.
         + exists 𝛼'. rewrite map_empty_union. trivial.
         + apply Hd. solve_map_disjoint.
     - rewrite op_cfail in Hval. done.
  Qed.
  
  Lemma upd_helper_l_𝛽_r_𝛽 old𝛽 new𝛽 :
      (∀ 𝛼 𝛽 𝜃 , old𝛽 ##ₘ 𝛽 → big_inv 𝛼 (old𝛽 ∪ 𝛽) 𝜃 → 
        ∃ 𝛼', 𝜙 𝛼' = 𝜙 𝛼 ∧ new𝛽 ##ₘ 𝛽 ∧ big_inv 𝛼' (new𝛽 ∪ 𝛽) 𝜃)
      → ra_𝛽 old𝛽 ~~> ra_𝛽 new𝛽.
  Proof.
      intros Ha. replace (ra_𝛽 old𝛽) with (ra_𝛽 old𝛽 ⋅ ra_𝜃 ∅) by (rewrite right_id; done).
      apply upd_helper_l_𝛽𝜃_r_𝛽. intros 𝛼 𝛽 𝜃 Hdisj Hdisj2.
      rewrite map_empty_union. apply Ha. trivial.
  Qed.
      
  Lemma upd_helper_heap_l_𝛽_r_𝛽 σ σ' old𝛽 new𝛽 :
      (∀ 𝛼 𝛽 𝜃 , 𝜙 𝛼 = σ → old𝛽 ##ₘ 𝛽 → big_inv 𝛼 (old𝛽 ∪ 𝛽) 𝜃 → 
        ∃ 𝛼', 𝜙 𝛼' = σ' ∧ new𝛽 ##ₘ 𝛽 ∧ big_inv 𝛼' (new𝛽 ∪ 𝛽) 𝜃)
      → ra_σ σ ⋅ ra_𝛽 old𝛽 ~~> ra_σ σ' ⋅ ra_𝛽 new𝛽.
  Proof.
      intros Ha. rewrite cmra_discrete_total_update.
      intros z Hval. destruct z as [[σ2|] 𝛽 𝜃|].
      - unfold "✓", cmra_valid, cmapR, cmap_valid, "⋅", cmra_op, cmap_op, ra_σ, ra_𝛽 in Hval.
        case_bool_decide; done.
      - unfold "✓", cmra_valid, cmapR, cmap_valid, "⋅", cmra_op, cmap_op, ra_σ, ra_𝛽 in Hval.
        case_bool_decide; last by done. case_bool_decide as Hdisj; last by done.
        destruct Hdisj as [Hdisj _]. rewrite map_empty_union in Hdisj.
        destruct Hval as [𝛼 [Hheap Hinv]].
        repeat rewrite map_empty_union in Hinv.
        destruct (Ha 𝛼 𝛽 𝜃 Hheap Hdisj Hinv) as [𝛼' [heap [disj𝛽' inv']]].
        unfold "✓", cmra_valid, cmapR, cmap_valid, "⋅", cmra_op, cmap_op, ra_σ, ra_𝛽.
        repeat case_bool_decide.
         + exists 𝛼'. repeat rewrite map_empty_union. intuition.
         + apply H3; solve_map_disjoint.
         + apply H2; solve_map_disjoint.
      - repeat (rewrite op_cfail in Hval). done.
  Qed.
  
  Lemma upd_helper_heap_l_emp_r_𝛽 σ σ' new𝛽 :
      (∀ 𝛼 𝛽 𝜃 , 𝜙 𝛼 = σ → big_inv 𝛼 𝛽 𝜃 → 
        ∃ 𝛼', 𝜙 𝛼' = σ' ∧ 𝛽 ##ₘ new𝛽 ∧ big_inv 𝛼' (new𝛽 ∪ 𝛽) 𝜃)
      → ra_σ σ ~~> ra_σ σ' ⋅ ra_𝛽 new𝛽.
  Proof.
      intros Ha. rewrite cmra_discrete_total_update.
      intros z Hval. destruct z as [[σ2|] 𝛽 𝜃|]; try done.
      unfold "✓", cmra_valid, cmapR, cmap_valid, "⋅", cmra_op, cmap_op, ra_σ in Hval.
      case_bool_decide; last by done. destruct Hval as [𝛼 [Hheap Hinv]].
      do 2 rewrite map_empty_union in Hinv.
      destruct (Ha 𝛼 𝛽 𝜃 Hheap Hinv) as [𝛼' [heap' [disj𝛽' inv']]].
      unfold "✓", cmra_valid, cmapR, cmap_valid, "⋅", cmra_op, cmap_op, ra_σ, ra_𝛽.
      repeat case_bool_decide.
       - exists 𝛼'. repeat rewrite map_empty_union. intuition.
       - apply H3. solve_map_disjoint.
       - apply H2. solve_map_disjoint.
  Qed.
  
  Lemma upd_helper_heap_l_𝛽_r_emp σ σ' old𝛽 :
      (∀ 𝛼 𝛽 𝜃 , 𝜙 𝛼 = σ → old𝛽 ##ₘ 𝛽 → big_inv 𝛼 (old𝛽 ∪ 𝛽) 𝜃 → 
        ∃ 𝛼', 𝜙 𝛼' = σ' ∧ big_inv 𝛼' 𝛽 𝜃)
      → ra_σ σ ⋅ ra_𝛽 old𝛽 ~~> ra_σ σ'.
  Proof.
      intros Ha. rewrite cmra_discrete_total_update.
      intros z Hval. destruct z as [[σ2|] 𝛽 𝜃|].
      - unfold "✓", cmra_valid, cmapR, cmap_valid, "⋅", cmra_op, cmap_op, ra_σ, ra_𝛽 in Hval.
        case_bool_decide; done.
      - unfold "✓", cmra_valid, cmapR, cmap_valid, "⋅", cmra_op, cmap_op, ra_σ, ra_𝛽 in Hval.
        case_bool_decide; last by done. case_bool_decide as Hdisj; last by done.
        destruct Hdisj as [Hdisj _]. rewrite map_empty_union in Hdisj.
        destruct Hval as [𝛼 [Hheap Hinv]].
        repeat rewrite map_empty_union in Hinv.
        destruct (Ha 𝛼 𝛽 𝜃 Hheap Hdisj Hinv) as [𝛼' [disj𝛽' inv']].
        unfold "✓", cmra_valid, cmapR, cmap_valid, "⋅", cmra_op, cmap_op, ra_σ, ra_𝛽.
        case_bool_decide as Bd.
         + exists 𝛼'. repeat rewrite map_empty_union. intuition.
         + apply Bd; solve_map_disjoint.
      - repeat (rewrite op_cfail in Hval). done.
  Qed.
  
  Lemma upd_helper_l_𝛽_r_𝛽𝜃_nondet (P : fine_map → unt_map → Prop) (Q : cmap_car → Prop) old𝛽 :
      (∀ z , (∃ new𝛽 new𝜃 , P new𝛽 new𝜃 ∧ z = ra_𝛽 new𝛽 ⋅ ra_𝜃 new𝜃) → Q z) →
      (∀ 𝛼 𝛽 𝜃 , old𝛽 ##ₘ 𝛽 → big_inv 𝛼 (old𝛽 ∪ 𝛽) 𝜃 →
        ∃ 𝛼' new𝛽 new𝜃, P new𝛽 new𝜃 ∧ 𝜙 𝛼' = 𝜙 𝛼 ∧ 𝛽 ##ₘ new𝛽 ∧ 𝜃 ##ₘ new𝜃 ∧ big_inv 𝛼' (new𝛽 ∪ 𝛽) (new𝜃 ∪ 𝜃))
      → ra_𝛽 old𝛽 ~~>: Q.
  Proof.
      intros Himpl Ha. rewrite cmra_discrete_total_updateP.
      intros z Hval. destruct z as [[σ2|] 𝛽 𝜃|]; try done. {
      unfold "✓", cmra_valid, cmapR, cmap_valid, "⋅", cmra_op, cmap_op, ra_σ, ra_𝛽, ra_𝜃, ε, cmap_unit in Hval.
      case_bool_decide as Hd; last by done. destruct Hval as [𝛼 [Hheap Hinv]].
      rewrite map_empty_union in Hinv. destruct Hd as [Hd _].
      destruct (Ha 𝛼 𝛽 𝜃 Hd Hinv) as [𝛼' [new𝛽 [new𝜃 [HP [Hheap2 [disj𝛽' [disj𝜃' inv']]]]]]]. exists (ra_𝛽 new𝛽 ⋅ ra_𝜃 new𝜃).
      split. { apply Himpl. exists new𝛽, new𝜃; split; trivial. }
      unfold "✓", cmra_valid, cmapR, cmap_valid, "⋅", cmra_op, cmap_op, ra_σ, ra_𝛽, ra_𝜃, ε.
      repeat case_bool_decide.
       - exists 𝛼'. repeat rewrite map_empty_union. rewrite map_union_empty. rewrite Hheap2. intuition.
       - apply H2. solve_map_disjoint.
       - apply H1. solve_map_disjoint.
     } {
     unfold "✓", cmra_valid, cmapR, cmap_valid, "⋅", cmra_op, cmap_op, ra_σ, ra_𝛽, ra_𝜃, ε, cmap_unit in Hval.
      case_bool_decide as Hd; last by done. destruct Hval as [𝛼 Hinv].
      rewrite map_empty_union in Hinv. destruct Hd as [Hd _].
      destruct (Ha 𝛼 𝛽 𝜃 Hd Hinv) as [𝛼' [new𝛽 [new𝜃 [HP [Hheap2 [disj𝛽' [disj𝜃' inv']]]]]]].
      exists (ra_𝛽 new𝛽 ⋅ ra_𝜃 new𝜃).
      split. { apply Himpl. exists new𝛽, new𝜃; split; trivial. }
      unfold "✓", cmra_valid, cmapR, cmap_valid, "⋅", cmra_op, cmap_op, ra_σ, ra_𝛽, ra_𝜃, ε.
      repeat case_bool_decide.
       - exists 𝛼'. repeat rewrite map_empty_union. rewrite map_union_empty. trivial.
       - apply H2. solve_map_disjoint. - apply H1. solve_map_disjoint.
    }
  Qed.
  
  Lemma upd_helper_l_emp_r_𝛽𝜃_nondet (P : fine_map → unt_map → Prop) (Q : cmap_car → Prop) :
      (∀ z , (∃ new𝛽 new𝜃 , P new𝛽 new𝜃 ∧ z = ra_𝛽 new𝛽 ⋅ ra_𝜃 new𝜃) → Q z) →
      (∀ 𝛼 𝛽 𝜃 , big_inv 𝛼 𝛽 𝜃 → 
        ∃ 𝛼' new𝛽 new𝜃, P new𝛽 new𝜃 ∧ 𝜙 𝛼' = 𝜙 𝛼 ∧ 𝛽 ##ₘ new𝛽 ∧ 𝜃 ##ₘ new𝜃 ∧ big_inv 𝛼' (new𝛽 ∪ 𝛽) (new𝜃 ∪ 𝜃))
      → ε ~~>: Q.
  Proof.
      intros Ha Hb. apply (upd_helper_l_𝛽_r_𝛽𝜃_nondet P Q ∅ Ha).
      intros 𝛼 𝛽 𝜃 _ big. rewrite map_empty_union in big. apply (Hb 𝛼 𝛽 𝜃 big).
  Qed.
  
  Lemma upd_helper_l_𝛽_r_𝛽_nondet (P : fine_map → Prop) (Q : cmap_car → Prop) old𝛽 :
      (∀ z , (∃ new𝛽 , P new𝛽 ∧ z = ra_𝛽 new𝛽) → Q z) →
      (∀ 𝛼 𝛽 𝜃 , old𝛽 ##ₘ 𝛽 →  big_inv 𝛼 (old𝛽 ∪ 𝛽) 𝜃 → 
        ∃ 𝛼' new𝛽, P new𝛽 ∧ 𝜙 𝛼' = 𝜙 𝛼 ∧ 𝛽 ##ₘ new𝛽 ∧ big_inv 𝛼' (new𝛽 ∪ 𝛽) 𝜃)
      → ra_𝛽 old𝛽 ~~>: Q.
  Proof.
      intros Ha Hb.
      apply (upd_helper_l_𝛽_r_𝛽𝜃_nondet (λ new𝛽 new𝜃, P new𝛽 ∧ new𝜃 = ∅) Q old𝛽).
       - intros z [new𝛽 [new𝜃 [[Hx1 Hx2] Hx3]]]. apply Ha. subst new𝜃.
         exists new𝛽. split; trivial. unfold ra_𝜃 in Hx3. rewrite right_id in Hx3. trivial.
       - intros 𝛼 𝛽 𝜃 Hdisj big. 
         destruct (Hb 𝛼 𝛽 𝜃 Hdisj big) as [𝛼' [new𝛽 [Hx1 [Hx2 [Hx3 Hx4]]]]].
         exists 𝛼', new𝛽, ∅. rewrite map_empty_union.
         assert (𝜃 ##ₘ ∅) by solve_map_disjoint. intuition.
  Qed.
  
  Lemma upd_alloc σ l v :
      σ !! l = None →
      ra_σ σ ~~> ra_σ (<[ l := v ]> σ) ⋅ ra_pt (inl l) (inr v).
  Proof.
      intros Hnotin. apply upd_helper_heap_l_emp_r_𝛽.
      intros 𝛼 𝛽 𝜃 Hheap Hinv. exists (𝛼_alloc 𝛼 l v).
      have Hinv' := alloc_preserves_inv 𝛼 𝛽 𝜃 l v. subst σ.
      rewrite insert_union_singleton_l in Hinv'. intuition. solve_map_disjoint.
  Qed.
  
  Lemma upd_delete σ l v :
      ra_σ σ ⋅ ra_pt (inl l) (inr v) ~~> ra_σ (delete l σ).
  Proof.
      apply upd_helper_heap_l_𝛽_r_emp. intros 𝛼 𝛽 𝜃 Hheap Hdisj Hinv. exists (𝛼_delete 𝛼 l).
      assert (({[inl l := inr v]} ∪ 𝛽) !! inl l = Some (inr v)) as Hin2.
        { rewrite lookup_union. rewrite lookup_singleton. apply union_Some_l. }
      have Hinv' := del_preserves_inv 𝛼 ({[inl l := inr v]} ∪ 𝛽) 𝜃 l v Hin2 Hinv. subst σ. 
      rewrite delete_union in Hinv'. rewrite delete_singleton in Hinv'.
      rewrite map_empty_union in Hinv'. split; first by intuition.
      rewrite delete_notin in Hinv'; first by intuition. solve_map_disjoint.
  Qed.
  
  Lemma upd_write σ 𝛽 l cells v v' :
      read 𝛽 (inl l) cells (inr v) →
      ra_σ σ ⋅ ra_𝛽 𝛽 ~~> ra_σ (<[l:=v']> σ) ⋅ ra_𝛽 (write 𝛽 l cells (inr v')).
  Proof.
      intros Hr. apply upd_helper_heap_l_𝛽_r_𝛽. intros 𝛼 𝛽0 𝜃 Hheap Hdisj big.
      exists (𝛼_write 𝛼 l cells v').
      split. { rewrite <- Hheap. apply write_updates_heap. }
      split. { apply (write_preserves_disjointness _ _ _ _ (inr v)); trivial. }
      rewrite (write_union _ _ _ _ (inr v)); trivial.
      apply (write_preserves_inv _ _ _ _ v); trivial.
      apply (read_𝛽_mono _ _ _ 𝛽); trivial. apply map_union_subseteq_l.
  Qed.
  
  Lemma upd_retether 𝛽 l cells v u c :
      read 𝛽 (inl l) cells (inr v) →     
      ra_𝛽 𝛽 ⋅ ra_unt u c v ~~> ra_𝛽 (write 𝛽 l cells (inl c)).
  Proof.
      intros Hr. apply upd_helper_l_𝛽𝜃_r_𝛽. intros 𝛼 𝛽0 𝜃 Hdisj𝛽 Hdisj𝜃 big.
      exists (𝛼_retether 𝛼 u l cells v c).
      assert (𝛽 ⊆ 𝛽 ∪ 𝛽0) as Hsub by apply map_union_subseteq_l.
      have Hr' := read_𝛽_mono _ _ _ _ _ Hsub Hr.
      rewrite <- (insert_union_singleton_l 𝜃 u (c, v)) in big.
      assert ((<[u := (c, v)]> 𝜃) !! u = Some (c, v)) as Hl by apply lookup_insert.
      split. { apply (retether_preserves_heap _ _ _ _ _ _ _ _ Hr' Hl big). }
      split. { apply (write_preserves_disjointness _ _ _ _ (inr v)); trivial. }
      rewrite (write_union _ _ _ _ (inr v)); trivial.
      have Ha := retether_preserves_inv 𝛼 (𝛽 ∪ 𝛽0) (<[u:=(c, v)]> 𝜃) u l cells v c Hr' Hl big.
      rewrite delete_insert in Ha; trivial. solve_map_disjoint.
  Qed.
  
  Lemma upd_alloc_unt v :
      ε ~~>: λ z, ∃ u c, z = ra_pt (inr c) (inr v) ⋅ ra_unt u c v.
  Proof using C EqDecision0 EqDecision1 H H0 Infinite_C L V.
      apply upd_helper_l_emp_r_𝛽𝜃_nondet with (P := λ 𝛽 𝜃, ∃ u c, 𝛽 = {[ inr c := inr v ]} ∧ 𝜃 = {[ u := (c, v) ]}).
      { intros z [new𝛽 [new𝜃 [[u [c [Ha Hb]]] Hc]]]. exists u, c. rewrite Hc. rewrite Ha. rewrite Hb. done. }
      intros 𝛼 𝛽 𝜃 Hinv.
      destruct (exists_fresh_uid 𝛼) as [u freshu].
      destruct (exists_fresh_cell_id 𝛼) as [c freshc].
      exists (𝛼_alloc_unt 𝛼 u c v), ({[ inr c := inr v ]}), ({[ u := (c, v) ]}).
      have Ha := (alloc_unt_preserves_inv 𝛼 𝛽 𝜃 u c v freshu freshc Hinv).
      split. { exists u, c; done. } split. { apply alloc_unt_preserves_heap. }
      split. { have Hnotin := fresh_cell_not_in_𝛽 𝛼 𝛽 𝜃 c freshc Hinv. solve_map_disjoint. }
      split. { have Hnotin := fresh_uid_not_in_𝜃 𝛼 𝛽 𝜃 u freshu Hinv. solve_map_disjoint. }
      do 2 rewrite insert_union_singleton_l in Ha. apply Ha.
  Qed.
  
  Lemma upd_alloc_insert c cv :
      ra_pt (inr c) cv ~~>: λ z, ∃ new_c, z = ra_pt (inr c) (inl new_c) ⋅ ra_pt (inr new_c) cv.
  Proof using C EqDecision0 EqDecision1 H H0 Infinite_C L V.
      apply upd_helper_l_𝛽_r_𝛽_nondet with
          (P := λ 𝛽, ∃ new_c, 𝛽 = <[ inr c := inl new_c ]> ({[ inr new_c := cv ]}) ∧ c ≠ new_c ).
      { intros z [new𝛽 [[new_c [Hc Hne]] Hzeq]]. subst z. subst new𝛽. exists new_c. unfold ra_𝛽.
        unfold ra_pt, ra_𝛽. unfold "⋅", cmap_op.
        case_bool_decide.
        - rewrite insert_union_singleton_l. rewrite map_union_empty. done.
        - exfalso. apply H1. split; last by solve_map_disjoint.
          rewrite map_disjoint_singleton_r. rewrite lookup_singleton_ne; trivial. congruence.
      }
      intros 𝛼 𝛽 𝜃 Hdisj Hinv.
      destruct (exists_fresh_cell_id 𝛼) as [new_c freshc].
      destruct (get_row_containing_cell 𝛼 ({[inr c := cv]} ∪ 𝛽) 𝜃 c cv) as [k [cells1 [cells2 [v Heq]]]]; first trivial. { rewrite lookup_union_l'. { rewrite lookup_singleton. trivial. } rewrite lookup_singleton. trivial. }
      exists (𝛼_insert_fresh_cell 𝛼 k cells1 c new_c cells2 v).
      exists (<[ inr c := inl new_c ]> ({[ inr new_c := cv ]})).
      have Hf := fresh_cell_not_in_𝛽 𝛼 ({[inr c := cv]} ∪ 𝛽) 𝜃 new_c freshc Hinv.
      assert (c ≠ new_c) as Hne. { intro Heq2. subst new_c.
        rewrite lookup_union_l' in Hf. { rewrite lookup_singleton in Hf. discriminate. }
        rewrite lookup_singleton. trivial. }
      assert (𝛽 !! inr c = None). { solve_map_disjoint. }
      assert (𝛽 !! inr new_c = None). { rewrite lookup_union_None in Hf. intuition. }
      split. { exists new_c. split; trivial. }
      split. { apply insert_fresh_cell_preserves_heap; trivial. }
      split. { 
          solve_map_disjoint.
      }
      replace ({[inr c := inl new_c; inr new_c := cv]} ∪ 𝛽) with
        (<[ inr c := inl new_c ]> (<[ inr new_c := cv ]> ({[inr c := cv]} ∪ 𝛽))).
        { apply insert_fresh_cell_preserves_inv; trivial.
          rewrite lookup_union_l'. { rewrite lookup_singleton. trivial. } rewrite lookup_singleton. trivial. }
      apply map_eq. intros lc.
      destruct (decide (lc = inr c)) as [He|Hn].
       - subst lc. rewrite lookup_insert. rewrite lookup_union_l'; rewrite lookup_insert; trivial.
       - rewrite lookup_insert_ne; last by done.
         destruct (decide (lc = inr new_c)) as [He'|Hn'].
         + subst lc. rewrite lookup_insert. rewrite lookup_union_l'.
           * rewrite lookup_insert_ne; last by congruence. rewrite lookup_singleton. trivial.
           * rewrite lookup_insert_ne; last by congruence. rewrite lookup_singleton. trivial.
         + rewrite lookup_insert_ne; last by done. rewrite lookup_union_r.
           * rewrite lookup_union_r; trivial.
             rewrite lookup_insert_ne; last by done.
             rewrite lookup_singleton_ne; done. 
           * rewrite lookup_singleton_ne; done.
  Qed.
  
  Lemma upd_untether lc c :
      ra_pt lc (inl c) ~~>: λ z, ∃ v u, z = ra_pt lc (inr v) ⋅ ra_unt u c v.
  Proof using C EqDecision0 EqDecision1 H H0 Infinite_C L V.
      apply upd_helper_l_𝛽_r_𝛽𝜃_nondet with (P := λ 𝛽 𝜃, ∃ u v, 𝛽 = {[ lc := inr v ]} ∧ 𝜃 = {[ u := (c, v) ]}).
      { intros z [new𝛽 [new𝜃 [[u [v [Hb Hc]]] Hz]]]. exists v, u. rewrite Hz. rewrite Hb. rewrite Hc. done. }
      intros 𝛼 𝛽 𝜃 Hdisj big.
      destruct (exists_fresh_uid 𝛼) as [u freshu].
      assert ((<[lc := inl c]> 𝛽) !! lc = Some (inl c)) as Hl by apply lookup_insert.
      rewrite <- (insert_union_singleton_l 𝛽 lc (inl c)) in big.
      destruct (get_row_for_lc 𝛼 (<[lc := inl c]> 𝛽) 𝜃 lc c Hl big)
          as [k [cells1 [cells2 [v Hisrow]]]].
      exists (𝛼_untether 𝛼 lc k cells1 c cells2 v u). exists {[lc := inr v]}.
      exists {[u := (c, v)]}.
      split. { exists u. exists v. split; trivial. }
      split. { apply untether_preserves_heap. trivial. }
      split. { solve_map_disjoint. }
      split. { have Hnotin := fresh_uid_not_in_𝜃 𝛼 _ 𝜃 u freshu big. solve_map_disjoint. }
      have Ha := (untether_preserves_inv 𝛼 _ 𝜃 lc k cells1 c cells2 v u Hisrow freshu big).
      rewrite insert_insert in Ha. do 2 rewrite insert_union_singleton_l in Ha. apply Ha.
  Qed.
  
  Lemma upd_delete_cell lc c cv :
      ra_pt lc (inl c) ⋅ ra_pt (inr c) cv ~~> ra_pt lc cv.
  Proof.
      unfold "⋅", cmap_op, ra_pt, ra_𝛽. case_bool_decide as Hdisj1.
      - destruct Hdisj1 as [Hdisj1 Hdisjemp].
        rewrite map_disjoint_singleton_l in Hdisj1. rewrite lookup_singleton_None in Hdisj1.
        rewrite map_empty_union. apply upd_helper_l_𝛽_r_𝛽. intros 𝛼 𝛽 𝜃 Hdisj2 big.
        rewrite <- (insert_union_singleton_l 𝛽). rewrite <- map_union_assoc in big.
        rewrite <- (insert_union_singleton_l 𝛽) in big.
        rewrite <- (insert_union_singleton_l (<[inr c := cv]> 𝛽)) in big.
        assert ((<[lc:=inl c]> (<[inr c:=cv]> 𝛽)) !! lc = Some (inl c)) as Hl
            by apply lookup_insert.
        destruct (get_row_for_lc 𝛼 (<[lc := inl c]> (<[inr c := cv]> 𝛽)) 𝜃 lc c Hl big)
            as [k [cells1 [cells2 [v Hisrow]]]].
        exists (𝛼_delete_cell 𝛼 k cells1 cells2 v).
        split; first by eauto using delete_cell_preserves_heap.
        split; first by solve_map_disjoint.
        replace (<[lc:=cv]> 𝛽) with 
            (<[ lc := cv ]> (delete (inr c) (<[lc:=inl c]> (<[inr c:=cv]> 𝛽)))).
         + apply delete_cell_preserves_inv; trivial. rewrite lookup_insert_ne; last by done.
           by rewrite lookup_insert.
         + rewrite delete_insert_ne; last by done.
           rewrite delete_insert; last by solve_map_disjoint. apply insert_insert.
      - rewrite cmra_discrete_total_update. done.
  Qed.
  
  Lemma val_read' σ 𝛽 l cells v :
      read 𝛽 (inl l) cells (inr v) → ✓ COk (Some σ) 𝛽 ∅ → σ !! l = Some v.
  Proof.
      intros Ha Hval. unfold "✓", cmap_valid in Hval. destruct Hval as [𝛼 [Hheap Hinv]].
      rewrite <- Hheap. apply (read_agrees 𝛼 𝛽 ∅ l cells v); trivial.
  Qed.
  
  Lemma val_read σ 𝛽 l cells v :
      read 𝛽 (inl l) cells (inr v) → ✓ (ra_σ σ ⋅ ra_𝛽 𝛽) → σ !! l = Some v.
  Proof.
     unfold "⋅", cmap_op, ra_σ, ra_𝛽.
     case_bool_decide as Ha. 2: { exfalso. apply Ha. solve_map_disjoint. }
     do 2 rewrite map_empty_union. apply val_read'.
  Qed.
  
  Local Lemma read_𝛽_valid_cons_is_absent 𝛽 c cells cv :
    read 𝛽 (inr c) cells cv → ✓ ra_𝛽 𝛽 → c ∉ cells.
  Proof.
    intros Hr [𝛼 Hbig]. apply (read_𝛽_cons_is_absent 𝛼 𝛽 ∅ c cells cv Hr Hbig).
  Qed.
  
  Local Lemma val_lc_ne lc cv lc' cv' :
      ✓ (ra_pt lc cv ⋅ ra_pt lc' cv') → lc ≠ lc'.
  Proof.
      unfold ra_pt, ra_𝛽, "⋅", cmap_op. case_bool_decide as Hdisj; last by done.
      intros _ Heq.  subst lc'. destruct Hdisj as [Hdisj _]. 
      rewrite map_disjoint_spec in Hdisj. apply (Hdisj lc cv cv'); apply lookup_singleton.
  Qed.
  
  Local Lemma 𝛽sub_of_incl 𝛽' o 𝛽 𝜃 : ra_𝛽 𝛽' ≼ COk o 𝛽 𝜃 → 𝛽' ⊆ 𝛽.
  Proof. intros [y Heq]. destruct y; last by done.
     - unfold "⋅", cmap_op, ra_𝛽 in Heq. case_bool_decide; last by discriminate.
       inversion Heq. subst 𝛽. apply map_union_subseteq_l.
  Qed.
  
  Local Lemma val_to_inv 𝛽 :
      ✓ (ra_𝛽 𝛽) → ∃ 𝛼 𝜃 , big_inv 𝛼 𝛽 𝜃.
  Proof.
    unfold "✓", cmap_valid, "⋅", cmap_op, ra_𝛽. intros [𝛼 big]. exists 𝛼, ∅. trivial.
  Qed.
  
  Local Lemma val_to_disj 𝛽₀ 𝛽₁ :
    ✓ (ra_𝛽 𝛽₀ ⋅ ra_𝛽 𝛽₁) → 𝛽₀ ##ₘ 𝛽₁.
  Proof.
    unfold "✓", cmap_valid, "⋅", cmap_op, ra_𝛽. case_bool_decide; intuition.
  Qed.
  
  Local Lemma val_to_inv_incl2 𝛽₀ 𝛽₁ (z: cmap_car) :
      ra_𝛽 𝛽₀ ≼ z → ra_𝛽 𝛽₁ ≼ z → ✓ z → ∃ 𝛼 𝛽 𝜃 , big_inv 𝛼 𝛽 𝜃 ∧ 𝛽₀ ⊆ 𝛽 ∧ 𝛽₁ ⊆ 𝛽.
  Proof.
      destruct z as [o 𝛽 𝜃|]; last by done. intros incl1 incl2.
      have sub1 := (𝛽sub_of_incl _ _ _ _ incl1). have sub2 := (𝛽sub_of_incl _ _ _ _ incl2).
      destruct o.
       - intros [𝛼 [Hheap Hbig]]. exists 𝛼, 𝛽, 𝜃. intuition.
       - intros [𝛼 Hbig]. exists 𝛼, 𝛽, 𝜃. intuition.
  Qed.
  
  Local Lemma val_and_cv_eq lc cv cv' (z: cmap_car) :
      ra_pt lc cv ≼ z → ra_pt lc cv' ≼ z → ✓ z → cv = cv'.
  Proof.
    intros Hincl1 Hincl2 Hval.
    destruct (val_to_inv_incl2 _ _ _ Hincl1 Hincl2 Hval) as [𝛼 [𝛽 [𝜃 [big [sub1 sub2]]]]].
    rewrite map_singleton_subseteq_l in sub1. rewrite map_singleton_subseteq_l in sub2.
    rewrite sub1 in sub2. inversion sub2. trivial.
  Qed.
  
  (** * The full-authority cell map

  A variant of [cmapR] whose authoritative element is the whole [full_map] [𝛼]: all the
  rows, with their chains of cells and their values, tethered (at a location) or
  untethered. The fragments are those of [cmapR] (edges [𝛽] and untethered rows [𝜃]).
  As the authority determines [𝛼], every update that changes [𝛼] needs it, including
  untethering, retethering and inserting or deleting cells. In exchange, the owner of the
  authority knows every row, e.g. the contents of every cell. The update lemmas reuse the
  invariant-preservation lemmas above. *)

  (** The last link of a row: its last cell, or the location of a row without cells. *)
  Definition row_last (k: L + untether_id) (cs: list C) : option (L + C) :=
    match last_c cs with
    | Some c => Some (inr c)
    | None => match k with inl l => Some (inl l) | inr _ => None end
    end.

  Local Lemma row_last_cons k c cs : ∃ c', row_last k (c :: cs) = Some (inr c') ∧ list_ends_with (c :: cs) c'.
  Proof.
    destruct (case_last_c (c :: cs)) as [[_ ?]|(prefix & last & Hl & Heq)]; [done|].
    exists last. rewrite /row_last Hl. split; [done|]. done.
  Qed.

  Lemma write_row_preserves_inv 𝛼 𝛽 𝜃 𝜃' k cs v v' lc :
      𝛼 !! k = Some (cs, v) →
      row_last k cs = Some lc →
      unt_map_inv (<[k := (cs, v')]> 𝛼) 𝜃' →
      big_inv 𝛼 𝛽 𝜃 →
      big_inv (<[k := (cs, v')]> 𝛼) (<[lc := inr v']> 𝛽) 𝜃'.
  Proof.
    intros Hk Hlast Hunt [fine_inv [_ no_dupes]].
    split; last split; [|done|by eapply cells_no_dupes_upd_value].
    intros src dst Hl. destruct (decide (src = lc)) as [->|Hne].
    { rewrite lookup_insert in Hl. simplify_eq. rewrite /row_last in Hlast.
      destruct (last_c cs) as [c|] eqn:Hc.
      - simplify_eq. exists k, cs. rewrite lookup_insert. done.
      - destruct k as [l|u]; [|done]. simplify_eq.
        destruct (case_last_c cs) as [[_ ->]|(?&?&Hc'&_)]; [|by rewrite Hc in Hc'].
        rewrite /𝛼_fine_pair lookup_insert. done. }
    rewrite lookup_insert_ne in Hl; [|done]. have Hf := fine_inv _ _ Hl.
    unfold 𝛼_fine_pair in *. destruct src as [l0|c0], dst as [c1|v1].
    - destruct (decide (inl l0 = k)) as [<-|]; [|by rewrite lookup_insert_ne].
      rewrite lookup_insert. by rewrite Hk in Hf.
    - destruct (decide (inl l0 = k)) as [<-|]; [|by rewrite lookup_insert_ne].
      exfalso. rewrite Hk in Hf. simplify_eq. rewrite /row_last /= in Hlast. simplify_eq. done.
    - destruct Hf as (lu & cs0 & v0 & Hlu & Hp).
      destruct (decide (lu = k)) as [->|].
      + rewrite Hk in Hlu. simplify_eq. exists k, cs0, v'. by rewrite lookup_insert.
      + exists lu, cs0, v0. by rewrite lookup_insert_ne.
    - destruct Hf as (lu & cs0 & Hlu & Hp).
      destruct (decide (lu = k)) as [->|].
      + rewrite Hk in Hlu. simplify_eq. exfalso. apply Hne.
        rewrite /row_last Hp in Hlast. by simplify_eq.
      + exists lu, cs0. by rewrite lookup_insert_ne.
  Qed.

  Lemma unt_map_inv_insert_loc 𝛼 𝜃 l row :
      unt_map_inv 𝛼 𝜃 → unt_map_inv (<[inl l := row]> 𝛼) 𝜃.
  Proof.
    intros Hu u c v Hl. rewrite lookup_insert_ne; [|done]. by apply Hu.
  Qed.

  Lemma insert_front_preserves_inv 𝛼 𝛽 𝜃 l cs v cv0 nc :
      𝛼 !! inl l = Some (cs, v) →
      𝛽 !! inl l = Some cv0 →
      fresh_cell_id 𝛼 nc →
      big_inv 𝛼 𝛽 𝜃 →
      big_inv (<[inl l := (nc :: cs, v)]> 𝛼) (<[inl l := inl nc]> (<[inr nc := cv0]> 𝛽)) 𝜃.
  Proof.
    intros Hk Hb Hfresh big.
    have Hnc := fresh_cell_not_in_𝛽 _ _ _ _ Hfresh big.
    destruct big as [fine_inv [unt_inv no_dupes]].
    split; last split.
    - intros src dst Hl. destruct (decide (src = inl l)) as [->|Hne1].
      { rewrite lookup_insert in Hl. simplify_eq. by rewrite /𝛼_fine_pair lookup_insert. }
      rewrite lookup_insert_ne in Hl; [|done].
      destruct (decide (src = inr nc)) as [->|Hne2].
      { rewrite lookup_insert in Hl. simplify_eq. have Hf := fine_inv _ _ Hb.
        unfold 𝛼_fine_pair in *. rewrite Hk in Hf. destruct cv0 as [c1|v1].
        - destruct cs as [|c1' cs]; [done|]. simplify_eq.
          exists (inl l), (nc :: c1 :: cs), v. rewrite lookup_insert. split; [done|].
          by apply (list_has_pair_mid []).
        - simplify_eq. exists (inl l), [nc]. rewrite lookup_insert. done. }
      rewrite lookup_insert_ne in Hl; [|done]. have Hf := fine_inv _ _ Hl.
      unfold 𝛼_fine_pair in *. destruct src as [l0|c0], dst as [c1|v1].
      + rewrite lookup_insert_ne; [done|congruence].
      + rewrite lookup_insert_ne; [done|congruence].
      + destruct Hf as (lu & cs0 & v0 & Hlu & Hp).
        destruct (decide (lu = inl l)) as [->|].
        * rewrite Hk in Hlu. simplify_eq. exists (inl l), (nc :: cs0), v0.
          rewrite lookup_insert. split; [done|]. by apply list_has_pair_cons.
        * exists lu, cs0, v0. by rewrite lookup_insert_ne.
      + destruct Hf as (lu & cs0 & Hlu & Hp).
        destruct (decide (lu = inl l)) as [->|].
        * rewrite Hk in Hlu. simplify_eq. exists (inl l), (nc :: cs0).
          rewrite lookup_insert. split; [done|]. by apply (list_ends_with_app_r [nc]).
        * exists lu, cs0. by rewrite lookup_insert_ne.
    - by apply unt_map_inv_insert_loc.
    - by apply (cells_no_dupes_insert_mid _ _ []).
  Qed.

  Inductive fcmap_car :=
    | FOk (a: option full_map) (𝛽: fine_map) (𝜃: unt_map)
    | FFail.

  Instance fcmap_op : Op fcmap_car := λ a b, match a, b with
      | FOk (Some _) _ _, FOk (Some _) _ _ => FFail
      | FOk a 𝛽 𝜃, FOk a' 𝛽' 𝜃' =>
          if bool_decide (𝛽 ##ₘ 𝛽' ∧ 𝜃 ##ₘ 𝜃') then
            FOk (match a with Some _ => a | None => a' end) (𝛽 ∪ 𝛽') (𝜃 ∪ 𝜃')
          else FFail
      | _, _ => FFail
  end.

  Instance fcmap_valid : Valid fcmap_car := λ a, match a with
      | FOk (Some 𝛼) 𝛽 𝜃 => big_inv 𝛼 𝛽 𝜃
      | FOk None 𝛽 𝜃 => ∃ 𝛼 , big_inv 𝛼 𝛽 𝜃
      | FFail => False
  end.

  Instance fcmap_equiv : Equiv fcmap_car := λ a b , a = b.

  Instance fcmap_pcore : PCore fcmap_car := λ a , Some (FOk None ∅ ∅).

  Lemma fcmap_assoc : Assoc (=) fcmap_op.
  Proof.
    intros x y z.
    destruct x as [[σ1|] 𝛽1 𝜃1|], y as [[σ2|] 𝛽2 𝜃2|], z as [[σ3|] 𝛽3 𝜃3|];
      unfold fcmap_op; try done;
    repeat case_bool_decide; try done; try f_equal; trivial;
    try (apply map_union_assoc; destruct_and?; solve_map_disjoint);
    try (exfalso; (match goal with | [ H' : ¬ _ |- _ ] =>
        apply H'; destruct_and?; solve_map_disjoint end)).
  Qed.

  Lemma fcmap_comm : Comm (=) fcmap_op.
  Proof.
    intros x y. destruct x as [[σ1|] 𝛽1 𝜃1|], y as [[σ2|] 𝛽2 𝜃2|]; unfold fcmap_op; try done;
    repeat case_bool_decide; try done; try f_equal; trivial;
      try (apply map_union_comm; destruct_and?; solve_map_disjoint);
      try (exfalso; (match goal with | [ H' : ¬ _ |- _ ] =>
        apply H'; destruct_and?; solve_map_disjoint end)).
  Qed.

  Lemma fcmap_left_id x : (FOk None ∅ ∅) ⋅ x = x.
  Proof.
    destruct x as [[h|] 𝛽 𝜃|].
      + unfold "⋅", fcmap_op. case_bool_decide as Hd.
        * do 2 rewrite map_empty_union. trivial.
        * exfalso. apply Hd. split; apply map_disjoint_empty_l.
      + unfold "⋅", fcmap_op. case_bool_decide as Hd.
        * do 2 rewrite map_empty_union. trivial.
        * exfalso. apply Hd. split; apply map_disjoint_empty_l.
      + done.
  Qed.

  Definition fcmap_ra_mixin : RAMixin fcmap_car.
  Proof. split.
    - typeclasses eauto.
    - intros. exists cx. done.
    - typeclasses eauto.
    - apply fcmap_assoc.
    - apply fcmap_comm.
    - intros x cx H2. unfold pcore, fcmap_pcore in H2. inversion H2. apply fcmap_left_id.
    - intros x cx H2. unfold pcore, fcmap_pcore in H2. inversion H2. done.
    - intros x y cx incl H2. unfold pcore, fcmap_pcore in H2. inversion H2.
      exists (FOk None ∅ ∅). split; try done. exists (FOk None ∅ ∅).
      rewrite fcmap_left_id; trivial.
    - intros x y. destruct x as [[h|] 𝛽 𝜃|]; destruct y as [[h'|] 𝛽' 𝜃'|]; try done.
      + unfold "✓", fcmap_valid, "⋅", fcmap_op. case_bool_decide; try done.
        intros Inv. apply (big_inv_mono h 𝛽 𝛽' 𝜃 𝜃'); intuition.
      + unfold "✓", fcmap_valid, "⋅", fcmap_op. case_bool_decide; try done.
        intros Inv. exists h'. apply (big_inv_mono h' 𝛽 𝛽' 𝜃 𝜃'); intuition.
      + unfold "✓", fcmap_valid, "⋅", fcmap_op. case_bool_decide; try done.
        intros [𝛼 Inv]. exists 𝛼. apply (big_inv_mono 𝛼 𝛽 𝛽' 𝜃 𝜃'); intuition.
  Qed.

  Canonical Structure fcmapO := discreteO fcmap_car.
  Canonical Structure fcmapR := discreteR fcmap_car fcmap_ra_mixin.

  Global Instance fcmap_cmra_discrete : CmraDiscrete fcmapR.
  Proof. apply discrete_cmra_discrete. Qed.

  Global Instance fcmap_unit : Unit fcmap_car := FOk None ∅ ∅.

  Definition fcmap_ucmra_mixin : UcmraMixin fcmap_car.
  Proof.
    split; trivial.
    - exists ∅. apply big_inv_empty.
    - intro x. apply fcmap_left_id.
  Qed.

  Canonical Structure fcmapUR := Ucmra fcmap_car fcmap_ucmra_mixin.

  Lemma fcmap_op_frag 𝛽1 𝜃1 𝛽2 𝜃2 :
    𝛽1 ##ₘ 𝛽2 → 𝜃1 ##ₘ 𝜃2 →
    FOk None 𝛽1 𝜃1 ⋅ FOk None 𝛽2 𝜃2 = FOk None (𝛽1 ∪ 𝛽2) (𝜃1 ∪ 𝜃2).
  Proof. intros ??. unfold "⋅", cmra_op; simpl. unfold fcmap_op. by rewrite bool_decide_true. Qed.

  Lemma fcmap_op_auth 𝛼 𝛽1 𝜃1 𝛽2 𝜃2 :
    𝛽1 ##ₘ 𝛽2 → 𝜃1 ##ₘ 𝜃2 →
    FOk (Some 𝛼) 𝛽1 𝜃1 ⋅ FOk None 𝛽2 𝜃2 = FOk (Some 𝛼) (𝛽1 ∪ 𝛽2) (𝜃1 ∪ 𝜃2).
  Proof. intros ??. unfold "⋅", cmra_op; simpl. unfold fcmap_op. by rewrite bool_decide_true. Qed.

  Lemma fcmap_valid_frag_disj 𝛽1 𝜃1 𝛽2 𝜃2 o :
    ✓ (FOk o 𝛽1 𝜃1 ⋅ FOk None 𝛽2 𝜃2) → 𝛽1 ##ₘ 𝛽2 ∧ 𝜃1 ##ₘ 𝜃2.
  Proof.
    unfold "⋅", cmra_op; simpl. unfold fcmap_op. destruct o; case_bool_decide; done.
  Qed.

  (** The basic update: the authority [𝛼] with the fragments [𝛽], [𝜃] becomes the
      authority [𝛼'] with [𝛽'], [𝜃'], when this preserves the invariant for every frame. *)
  Lemma fcmap_update 𝛼 𝛼' 𝛽 𝛽' 𝜃 𝜃' :
    (∀ 𝛽f 𝜃f, 𝛽 ##ₘ 𝛽f → 𝜃 ##ₘ 𝜃f → big_inv 𝛼 (𝛽 ∪ 𝛽f) (𝜃 ∪ 𝜃f) →
       𝛽' ##ₘ 𝛽f ∧ 𝜃' ##ₘ 𝜃f ∧ big_inv 𝛼' (𝛽' ∪ 𝛽f) (𝜃' ∪ 𝜃f)) →
    FOk (Some 𝛼) 𝛽 𝜃 ~~> FOk (Some 𝛼') 𝛽' 𝜃'.
  Proof.
    intros Ha. rewrite cmra_discrete_total_update. intros z Hval.
    destruct z as [[𝛼f|] 𝛽f 𝜃f|].
    - unfold "⋅", cmra_op in Hval; simpl in Hval. done.
    - unfold "⋅", cmra_op in Hval; simpl in Hval. unfold fcmap_op in Hval.
      case_bool_decide as Hd; [|done]. destruct Hd as [Hd1 Hd2].
      destruct (Ha 𝛽f 𝜃f Hd1 Hd2 Hval) as (Hd1' & Hd2' & Hinv).
      unfold "⋅", cmra_op; simpl. unfold fcmap_op. rewrite bool_decide_true; done.
    - unfold "⋅", cmra_op in Hval; simpl in Hval. unfold fcmap_op in Hval. done.
  Qed.

  (** The authority knows every edge, and the untethered rows. *)
  Lemma fcmap_valid_auth 𝛼 𝛽 𝜃 : ✓ FOk (Some 𝛼) 𝛽 𝜃 ↔ big_inv 𝛼 𝛽 𝜃.
  Proof. done. Qed.

  Lemma big_inv_eq 𝛼 𝛽 𝛽' 𝜃 : 𝛽' = 𝛽 → big_inv 𝛼 𝛽' 𝜃 → big_inv 𝛼 𝛽 𝜃.
  Proof. by intros ->. Qed.

  (* into the logic *)
      
  Class cmap_logicG Σ := {
    #[global] cmap_logic_inG :: inG Σ cmapUR
  }.
  
  Definition cmap_logicΣ : gFunctors := #[ GFunctor cmapUR ].
  
  Global Instance subG_cmap_logicΣ {Σ} : subG cmap_logicΣ Σ → cmap_logicG Σ.
  Proof. solve_inG. Qed.

  Class fcmap_logicG Σ := {
    #[global] fcmap_logic_inG :: inG Σ fcmapUR
  }.

  Definition fcmap_logicΣ : gFunctors := #[ GFunctor fcmapUR ].

  Global Instance subG_fcmap_logicΣ {Σ} : subG fcmap_logicΣ Σ → fcmap_logicG Σ.
  Proof. solve_inG. Qed.
  
  Context {Σ: gFunctors}.
  Context {cmapl: cmap_logicG Σ}.
  
  Definition heap γ (σ: gmap L V) := own γ (ra_σ σ).
  Definition pt γ (lc: L + C) (cv: C + V) := own γ (ra_pt lc cv).
  Definition untether γ (c: C) (v: V) := (∃ u, own γ (ra_unt u c v))%I.
  
  Fixpoint pt_seq γ (lc: L + C) (cells: list C) (cv: C + V) : iProp Σ :=
      match cells with
          | [] => pt γ lc cv
          | cell :: cells' => pt γ lc (inl cell) ∗ pt_seq γ (inr cell) cells' cv
      end.
      
  Global Instance pt_seq_timeless γ lc cells cv : Timeless (pt_seq γ lc cells cv).
  Proof.
      generalize lc. induction cells. { apply _. } intro lc0. simpl. apply _.
  Qed.
  
  Lemma own_ra_𝛽_disj γ 𝛽₀ 𝛽₁ :
      own γ (ra_𝛽 𝛽₀) -∗ own γ (ra_𝛽 𝛽₁) -∗ ⌜𝛽₀ ##ₘ 𝛽₁⌝.
  Proof.
      iIntros "A B". iCombine "A B" as "A". iDestruct (own_valid with "A") as "%Hval".
      iPureIntro. apply val_to_disj. apply Hval.
  Qed.
  
  Lemma own_ra_𝛽_join γ 𝛽₀ 𝛽₁ :
      own γ (ra_𝛽 𝛽₀) -∗
      own γ (ra_𝛽 𝛽₁) -∗
      own γ (ra_𝛽 (𝛽₀ ∪ 𝛽₁)) ∗ ⌜𝛽₀ ⊆ 𝛽₀ ∪ 𝛽₁ ∧ 𝛽₁ ⊆ 𝛽₀ ∪ 𝛽₁⌝.
  Proof.
      iIntros "A B". iDestruct (own_ra_𝛽_disj with "A B") as "%Hdisj".
      iCombine "A B" as "A". rewrite ra_𝛽_split; last by trivial. iFrame. iPureIntro.
      split. { apply map_union_subseteq_l. } apply map_union_subseteq_r. apply Hdisj.
  Qed.
  
  Lemma own_ra_𝛽_split γ 𝛽₀ 𝛽₁ :
    𝛽₀ ##ₘ 𝛽₁ →
    own γ (ra_𝛽 (𝛽₀ ∪ 𝛽₁)) ⊢ own γ (ra_𝛽 𝛽₀) ∗ own γ (ra_𝛽 𝛽₁).
  Proof.
    intros Hdisj. rewrite <- own_op. rewrite ra_𝛽_split; done.
  Qed.
  
  Local Lemma own_ra_𝛽_delete γ 𝛽 (lc: L+C) (cv: C+V) :
      𝛽 !! lc = Some cv →
      own γ (ra_𝛽 𝛽) ⊢ own γ (ra_pt lc cv) ∗ own γ (ra_𝛽 (delete lc 𝛽)).
  Proof.
      intros Hnone. iIntros "A". iApply (own_ra_𝛽_split).
        { apply map_disjoint_singleton_l_2. apply lookup_delete. }
      replace ({[lc := cv]} ∪ delete lc 𝛽) with 𝛽; first by done.
      rewrite union_insert_delete; trivial. rewrite map_empty_union. trivial.
  Qed.
  
  Local Lemma pt_own_ra_𝛽_disj γ lc cv 𝛽 :
      pt γ lc cv -∗ own γ (ra_𝛽 𝛽) -∗ ⌜𝛽 !! lc = None⌝.
  Proof.
      iIntros "A B". iDestruct (own_ra_𝛽_disj with "A B") as "%Hdisj".
      iPureIntro. solve_map_disjoint.
  Qed.
  
  Local Lemma own_ra_𝛽_insert γ lc c 𝛽 :
      𝛽 !! lc = None
      → pt γ lc (inl c) -∗ own γ (ra_𝛽 𝛽) -∗ own γ (ra_𝛽 (<[lc:=inl c]> 𝛽)).
  Proof.
      iIntros (Hnone) "A B". iDestruct (own_ra_𝛽_join with "A B") as "[own [%Hsub1 %Hsub2]]".
      rewrite insert_union_singleton_l. iFrame.
  Qed.
  
  Local Lemma pt_seq_equiv𝛽 γ lc cells cv :
      pt_seq γ lc cells cv ⊣⊢ ∃ 𝛽 , own γ (ra_𝛽 𝛽) ∗ ⌜read 𝛽 lc cells cv⌝.
  Proof.
    induction cells in lc |- *.
    - iSplit.
       + iIntros "a". iExists {[ lc := cv ]}. iFrame. iPureIntro. apply lookup_singleton.
       + iDestruct 1 as (𝛽) "[own %Hr]".
         iDestruct (own_ra_𝛽_delete with "own") as "[$ _]". apply Hr.
    - iSplit.
       + iIntros "[a b]". iDestruct (IHcells (inr a) with "b") as (𝛽) "[own %Hr]".
         iExists (<[ lc := inl a ]> 𝛽). iDestruct (pt_own_ra_𝛽_disj with "a own") as "%Hnotin".
         iSplit. { iApply (own_ra_𝛽_insert _ _ _ _ Hnotin with "a own"). }
         iPureIntro. apply (read_𝛽_insert _ _ _ _ _ Hnotin Hr).
       + iDestruct 1 as (𝛽) "[own %Hr]". iDestruct (own_valid with "own") as "%Hval".
         destruct Hr as [Hr Hrest].
         iDestruct (own_ra_𝛽_delete _ _ _ _ Hr with "own") as "[$ rest]".
         setoid_rewrite IHcells. iExists (delete lc 𝛽). iFrame. iPureIntro.
         destruct lc. { apply read_𝛽_delete_loc. trivial. }
         apply read_𝛽_delete_cell; trivial.
         apply (read_𝛽_valid_cons_is_absent 𝛽 c (a :: cells) cv); trivial. split; trivial.
  Qed.
  
  Local Lemma pt_seq_big_sepM_equiv𝛽 γ (rows: gmap L (list C * (C + V))) :
    ([∗ map] k↦'(cells0, cv) ∈ rows, pt_seq γ (inl k) cells0 cv)
        ⊣⊢ ⌜rows = ∅⌝ ∨ (∃ 𝛽 , own γ (ra_𝛽 𝛽)
        ∗ ⌜∀ l cells cv, rows !! l = Some (cells, cv) → read 𝛽 (inl l) cells cv⌝).
  Proof.
    induction rows as [|l row rows Hnone IH] using map_ind; iSplit.
     - iIntros "A". iLeft; done.
     - iIntros "_". done.
     - rewrite big_sepM_insert; last by trivial. destruct row as [cells cv].
       iIntros "[pt map]". rewrite IH. iDestruct "map" as "[%emp | own]".
        + subst rows. iRight. rewrite pt_seq_equiv𝛽. iDestruct "pt" as (𝛽) "[own %Hr]".
          iExists 𝛽. iFrame. iPureIntro. iIntros (l' cells' cv'). intros Ha.
          rewrite insert_empty in Ha. rewrite lookup_singleton_Some in Ha.
          destruct Ha as [Hl Hi]. inversion Hi. subst l'. subst cells'. subst cv'. apply Hr.
        + iRight. rewrite pt_seq_equiv𝛽. iDestruct "pt" as (𝛽) "[own0 %Hr]".
          iDestruct "own" as (𝛽rows) "[own1 %Hreads]".
          iDestruct (own_ra_𝛽_join with "own0 own1") as "[ownjoin [%sub1 %sub2]]".
          iExists (𝛽 ∪ 𝛽rows). iFrame. iPureIntro. intros l' cells' cv' Hin.
          destruct (decide (l = l')) as [Heq|Hne].
            * subst l'. rewrite lookup_insert in Hin. inversion Hin. subst cells'. subst cv'.
              apply (read_𝛽_mono _ _ _ _ _ sub1 Hr).
            * rewrite lookup_insert_ne in Hin; last by trivial.
              apply (read_𝛽_mono _ _ _ _ _ sub2). apply Hreads. apply Hin.
    - iIntros "[%contra|A]". { exfalso.
        assert (<[l:=row]> rows !! l = Some row) as Hlo by apply lookup_insert.
        rewrite contra in Hlo. rewrite lookup_empty in Hlo. discriminate. }
        iDestruct "A" as (𝛽) "[own %Hreads]". iDestruct (own_valid with "own") as "%Hval".
        destruct (val_to_inv 𝛽 Hval) as [𝛼 [𝜃 Hbig]].
        assert (∀ (l0 : L) (cells : list C) (cv : C + V),
          rows !! l0 = Some (cells, cv) → read 𝛽 (inl l0) cells cv) as Hreads'.
          { intros l0 cells0 cv0 Hsome. apply Hreads. destruct (decide (l = l0)).
              { subst l. rewrite Hnone in Hsome. discriminate. }
              rewrite lookup_insert_ne; trivial. }
        destruct row as [cells cv].
        assert (read 𝛽 (inl l) cells cv) as Hr. { apply Hreads. apply lookup_insert. }
        destruct (read_row_cons 𝛼 𝛽 𝜃 rows l cells cv Hbig Hnone Hr Hreads') as
            [𝛽₀ [𝛽₁ [Hunion [Hdisj [Hr2 Hreads2]]]]]. subst 𝛽.
        rewrite big_sepM_insert; last by trivial.
        iDestruct (own_ra_𝛽_split γ 𝛽₀ 𝛽₁ Hdisj with "own") as "[o1 o2]".
        iSplitL "o1".
          * rewrite pt_seq_equiv𝛽. iExists 𝛽₀. iFrame; done.
          * rewrite IH. iRight. iExists 𝛽₁. iFrame; done.
  Qed.
  
  Local Lemma own_with_incl2 γ 𝛽₀ 𝛽₁ (z: cmap_car) :
      ra_𝛽 𝛽₀ ≼ z → ra_𝛽 𝛽₁ ≼ z →
        own γ z ⊢ ∃ 𝛼 𝛽 𝜃 , ⌜big_inv 𝛼 𝛽 𝜃 ∧ 𝛽₀ ⊆ 𝛽 ∧ 𝛽₁ ⊆ 𝛽⌝ ∗ own γ (ra_𝛽 𝛽).
  Proof.
      intros incl1 incl2. iIntros "own". iDestruct (own_valid with "own") as "%Hval".
      destruct z as [o 𝛽 𝜃|]; last by done.
      have sub1 := (𝛽sub_of_incl _ _ _ _ incl1). have sub2 := (𝛽sub_of_incl _ _ _ _ incl2).
      assert (∃ 𝛼 , big_inv 𝛼 𝛽 𝜃) as Ha. {
        destruct o.
          - destruct Hval as [𝛼 [Hheap Hbig]]. exists 𝛼. apply Hbig.
          - destruct Hval as [𝛼 Hbig]. exists 𝛼. apply Hbig.
      }
      destruct Ha as [𝛼 Ha]. iExists 𝛼, 𝛽, 𝜃. iSplit; first by iPureIntro; intuition.
      rewrite op_split_out_𝛽. iDestruct "own" as "[_ $]".
  Qed.
  
  Lemma pt_seq_singleton γ lc cv :
      pt_seq γ lc [] cv ⊣⊢ pt γ lc cv.
  Proof. done. Qed.
  
  Lemma cmap_init : ⊢ |==> ∃ γ, heap γ ∅.
  Proof.
    apply own_alloc. exists ∅. split; trivial. apply big_inv_empty.
  Qed.
  
  Lemma cmap_alloc γ σ l v :
      σ !! l = None →
      ⊢ heap γ σ ==∗ heap γ (<[l:=v]> σ) ∗ pt γ (inl l) (inr v).
  Proof.
      intros Hnone. unfold heap, pt. rewrite <- own_op.
      iApply own_update. apply upd_alloc. trivial.
  Qed.
  
  Lemma cmap_delete γ σ l v :
      ⊢ heap γ σ -∗ pt γ (inl l) (inr v) ==∗ heap γ (delete l σ).
  Proof.
      unfold heap, pt. iIntros "a b". iCombine "a b" as "a".
      iApply own_update; last by iFrame "a". apply upd_delete.
  Qed.
  
  Lemma cmap_alloc_unt γ v :
      ⊢ |==> ∃ c, pt γ (inr c) (inr v) ∗ untether γ c v.
  Proof using C EqDecision0 EqDecision1 H H0 Infinite_C L V cmapl Σ.
      iIntros. iMod (own_unit _ γ) as "U".
      iMod (own_updateP with "U") as "A". { apply (upd_alloc_unt v). }
      iDestruct "A" as (a') "[%Ha own]". destruct Ha as [u [c Heq]]. subst a'.
      iModIntro. iDestruct "own" as "[a1 a2]". iFrame.
  Qed.
  
  Lemma cmap_alloc_cell_after_cell γ c cv :
      pt γ (inr c) cv ⊢ |==> ∃ new_c, pt γ (inr c) (inl new_c) ∗ pt γ (inr new_c) cv.
  Proof using C EqDecision0 EqDecision1 H H0 Infinite_C L V cmapl Σ.
      iIntros "P".
      iMod (own_updateP with "P") as "A". { apply (upd_alloc_insert c cv). }
      iDestruct "A" as (a') "[%Ha own]". destruct Ha as [new_c Heq]. subst a'.
      iModIntro. iDestruct "own" as "[a1 a2]". iFrame.
  Qed.
  
  Lemma cmap_read γ σ l cells v :
      heap γ σ -∗ pt_seq γ (inl l) cells (inr v) -∗ ⌜σ !! l = Some v⌝.
  Proof.
      iIntros "heap seq". rewrite pt_seq_equiv𝛽. iDestruct "seq" as (𝛽) "[b %Rd]".
      iCombine "heap b" as "own". iDestruct (own_valid with "own") as "%Hv".
      iPureIntro. apply (val_read σ 𝛽 l cells v Rd Hv).
  Qed.
  
  Lemma cmap_write γ σ l cells v v' :
      heap γ σ -∗ pt_seq γ (inl l) cells (inr v) ==∗
      heap γ (<[ l := v' ]> σ) ∗ pt_seq γ (inl l) cells (inr v').
  Proof.
      iIntros "heap seq". rewrite pt_seq_equiv𝛽. iDestruct "seq" as (𝛽) "[b %Rd]".
      iDestruct (own_valid with "b") as "%Hval".
      iCombine "heap b" as "own". iMod (own_update with "own") as "[heap b]".
          { apply (upd_write σ 𝛽 l cells v v' Rd). }
      iModIntro. iFrame "heap". rewrite pt_seq_equiv𝛽. iFrame "b". iPureIntro.
      destruct (val_to_inv 𝛽 Hval) as [𝛼 [𝜃 big]].
      apply (read_of_write 𝛼 𝛽 𝜃 l cells (inr v) (inr v') Rd big).
  Qed.
  
  Lemma cmap_untether γ lc c :
      pt γ lc (inl c) ==∗ ∃ v, pt γ lc (inr v) ∗ untether γ c v.
  Proof using C EqDecision0 EqDecision1 H H0 Infinite_C L V cmapl Σ.
      iIntros "A".
      iMod (own_updateP with "A") as "A". { apply (upd_untether lc c). }
      iDestruct "A" as (a') "[%Ha own]". destruct Ha as [v [u Heq]]. subst a'.
      iModIntro. iDestruct "own" as "[a1 a2]". iFrame.
  Qed.
  
  Lemma cmap_retether γ l c cells v :
      pt_seq γ (inl l) cells (inr v) -∗ untether γ c v ==∗ pt_seq γ (inl l) cells (inl c).
  Proof.
      iIntros "seq unt". rewrite pt_seq_equiv𝛽. iDestruct "seq" as (𝛽) "[b %Rd]".
      iDestruct "unt" as (u) "unt".
      iDestruct (own_valid with "b") as "%Hval".
      iCombine "b unt" as "own". iMod (own_update with "own") as "b".
          { apply upd_retether. apply Rd. }
      iModIntro. rewrite pt_seq_equiv𝛽. iFrame "b". iPureIntro.
      destruct (val_to_inv 𝛽 Hval) as [𝛼 [𝜃 big]].
      apply (read_of_write 𝛼 𝛽 𝜃 l cells (inr v) (inl c) Rd big).
  Qed.
  
  Lemma cmap_delete_cell γ lc c cv :
      pt γ lc (inl c) -∗ pt γ (inr c) cv ==∗ pt γ lc cv.
  Proof.
      iIntros "A B". iCombine "A B" as "A".
      iApply (own_update with "A"). apply upd_delete_cell.
  Qed.
  
  Lemma cmap_pt_lc_ne γ lc cv lc' cv' :
      pt γ lc cv -∗ pt γ lc' cv' -∗ ⌜lc ≠ lc'⌝.
  Proof.
      iIntros "A B". iCombine "A B" as "A". iDestruct (own_valid with "A") as "%Hval".
      iPureIntro. apply (val_lc_ne lc cv lc' cv' Hval).
  Qed.
  
  Lemma cmap_lc_ne γ lc cells cv lc' cells' cv' :
      pt_seq γ lc cells cv -∗ pt_seq γ lc' cells' cv' -∗ ⌜lc ≠ lc'⌝.
  Proof.
      destruct cells, cells'.
      - do 2 rewrite pt_seq_singleton. apply cmap_pt_lc_ne.
      - iIntros "A [B _]". rewrite pt_seq_singleton. iApply (cmap_pt_lc_ne with "A B").
      - iIntros "[A _] B". rewrite pt_seq_singleton. iApply (cmap_pt_lc_ne with "A B").
      - iIntros "[A _] [B _]". iApply (cmap_pt_lc_ne with "A B").
  Qed.
  
  Lemma cmap_locs_ne γ l cells cv l' cells' cv' :
      pt_seq γ (inl l) cells cv -∗ pt_seq γ (inl l') cells' cv' -∗ ⌜l ≠ l'⌝.
  Proof.
      iIntros "A B". iDestruct (cmap_lc_ne with "A B") as "%Ha". iPureIntro. intro a.
      subst. contradiction.
  Qed.
  
  Lemma cmap_cells_ne γ c cells cv c' cells' cv' :
      pt_seq γ (inr c) cells cv -∗ pt_seq γ (inr c') cells' cv' -∗ ⌜c ≠ c'⌝.
  Proof.
      iIntros "A B". iDestruct (cmap_lc_ne with "A B") as "%Ha". iPureIntro. intro a.
      subst. contradiction.
  Qed.
  
  Lemma cmap_pt_seq_cons γ lc cell cells cv :
      pt_seq γ lc (cell :: cells) cv ⊣⊢
      pt_seq γ lc [] (inl cell) ∗ pt_seq γ (inr cell) cells cv.
  Proof. done. Qed.
  
  Lemma cmap_pt_seq_cons_app γ lc cells cell cells' cv :
      pt_seq γ lc (cells ++ cell :: cells') cv ⊣⊢
      pt_seq γ lc cells (inl cell) ∗ pt_seq γ (inr cell) cells' cv.
  Proof.
      induction cells in lc |- *; first by done. simpl. rewrite IHcells. apply bi.sep_assoc.
  Qed.
  
  Lemma cmap_pt_seq_cons_back γ lc cell cells cv :
      pt_seq γ lc (cells ++ [cell]) cv ⊣⊢
      pt_seq γ lc cells (inl cell) ∗ pt_seq γ (inr cell) [] cv.
  Proof. apply cmap_pt_seq_cons_app. Qed.
  
  Lemma cmap_pt_seq_and_gives_eq γ lc cv cv' :
      pt γ lc cv ∧ pt γ lc cv' ⊢ ⌜cv = cv'⌝.
  Proof.
      iIntros "A". iDestruct (and_own_discrete_ucmra with "A") as (z) "[own [%Hi1 %Hi2]]".
      iDestruct (own_valid with "own") as "%Hval". iPureIntro.
      apply (val_and_cv_eq _ _ _ _ Hi1 Hi2 Hval).
  Qed.
  
  Lemma cmap_pt_and_gives_prefix γ lc cells cells' cell v :
      pt_seq γ lc cells (inl cell) ∧ pt_seq γ lc cells' (inr v) ⊢
          ⌜ ∃ cells2, cells' = cells ++ cell :: cells2 ⌝.
  Proof.
    induction cells' in lc, cells |- *.
      - destruct cells as [|c1 cells].
        + do 2 rewrite pt_seq_singleton. iIntros "A".
          iDestruct (cmap_pt_seq_and_gives_eq with "A") as "%Heq". discriminate.
        + rewrite pt_seq_singleton. iIntros "A". 
          iDestruct (cmap_pt_seq_and_gives_eq γ lc (inl c1) (inr v) with "[A]") as "%Heq".
            * iSplit. -- iDestruct "A" as "[[$ _] _]". -- iDestruct "A" as "[_ $]".
            * discriminate.
      - destruct cells as [|c1 cells].
        + rewrite pt_seq_singleton. iIntros "A". 
          iDestruct (cmap_pt_seq_and_gives_eq γ lc (inl cell) (inl a) with "[A]") as "%Heq".
            * iSplit. -- iDestruct "A" as "[$ _]". -- iDestruct "A" as "[_ [$ _]]".
            * inversion Heq. subst cell. iPureIntro. exists cells'. done.
        + iIntros "A".
          iDestruct (cmap_pt_seq_and_gives_eq γ lc (inl c1) (inl a) with "[A]") as "%Heq".
            * iSplit. -- iDestruct "A" as "[[$ _] _]". -- iDestruct "A" as "[_ [$ _]]".
            * inversion Heq. subst a. iDestruct (IHcells' (inr c1) cells with "[A]") as "%Ha".
              ** iSplit. -- iDestruct "A" as "[[_ $] _]". -- iDestruct "A" as "[_ [_ $]]".
              ** iPureIntro. destruct Ha as [cells2 Hc]. subst cells'. exists cells2. done.
  Qed.
  
  (*Lemma cmap_pt_and_gives_contra γ lc cells cells' cell cell' cv cv' :
      (pt_seq γ lc cells (inl cell) ∧ pt_seq γ lc cells' (inl cell'))
        -∗ pt γ (inr cell) cv -∗ pt γ (inr cell') cv' -∗ False.*)
  
  Lemma cmap_pt_and_gives_contra γ lc cells cells' cell v v' :
    (pt_seq γ lc cells (inr v) ∧ pt_seq γ lc cells' (inl cell))
    -∗ pt γ (inr cell) (inr v') -∗ False.
  Proof.
    iIntros "A B". rewrite bi.and_comm.
    iDestruct (cmap_pt_and_gives_prefix with "A") as "%Hpref".
    destruct Hpref as [cells2 Heq]. subst cells.
    rewrite cmap_pt_seq_cons_app. iDestruct "A" as "[_ [_ A]]". rewrite <- pt_seq_singleton.
    iDestruct (cmap_cells_ne with "A B") as "%Hne". contradiction.
  Qed.
  
  Lemma cmap_pt_and_cons γ lc cells cell cv :
      pt_seq γ lc [] (inl cell) ∧ pt_seq γ (inr cell) cells cv ⊢
          pt_seq γ lc (cell :: cells) cv.
  Proof.
      rewrite pt_seq_singleton. unfold pt, ra_pt. rewrite pt_seq_equiv𝛽.
      rewrite bi.and_exist_l. iDestruct 1 as (𝛽) "And".
      iAssert (⌜read 𝛽 (inr cell) cells cv⌝)%I as "%Hread". { iDestruct "And" as "[_ [_ $]]". }
      iAssert (own γ (ra_𝛽 {[lc := inl cell]}) ∧ own γ (ra_𝛽 𝛽))%I with "[And]" as "And". {
        iSplit. { iDestruct "And" as "[$ _]". } iDestruct "And" as "[_ [$ _]]". }
      iDestruct (and_own_discrete_ucmra with "And") as (z) "[own [%Hincl1 %Hincl2]]".
      iDestruct (own_with_incl2 _ _ _ _ Hincl1 Hincl2 with "own")
          as (𝛼 𝛽' 𝜃) "[[%Hbig [%Hsub1 %Hsub2]] own]".
      rewrite pt_seq_equiv𝛽. iExists 𝛽'. iFrame "own". iPureIntro.
      apply (read_𝛽_insert2 _ _ _ _ 𝛽 𝛽' Hsub2 Hsub1 Hread).
  Qed.
    
  Lemma cmap_pt_and_app γ lc cells cell cells' cv :
      pt_seq γ lc cells (inl cell) ∧ pt_seq γ (inr cell) cells' cv ⊢
          pt_seq γ lc (cells ++ cell :: cells') cv.
  Proof.
    induction cells in lc |- *.
    - apply cmap_pt_and_cons.
    - iIntros "And". iApply (cmap_pt_and_cons γ lc (cells ++ cell :: cells') a cv). iSplit.
      + iDestruct "And" as "[[$ _] _]".
      + iApply IHcells. iSplit. * iDestruct "And" as "[[_ $] _]". * iDestruct "And" as "[_ $]".
  Qed.
  
  Lemma cmap_pt_and_cons_back γ lc cells cell cv :
      pt_seq γ lc cells (inl cell) ∧ pt_seq γ (inr cell) [] cv ⊢
          pt_seq γ lc (cells ++ [cell]) cv.
  Proof. apply cmap_pt_and_app. Qed.
  
  Local Lemma cmap_and_sepM_cons_row γ (rows: gmap L (list C * (C + V))) l cells cv :
    rows !! l = None →
    pt_seq γ (inl l) cells cv ∧ ([∗ map] k↦'(cells0, cv0) ∈ rows, pt_seq γ (inl k) cells0 cv0) ⊢
    pt_seq γ (inl l) cells cv ∗ ([∗ map] k↦'(cells0, cv0) ∈ rows, pt_seq γ (inl k) cells0 cv0).
  Proof.
    intros Hnone. iIntros "And". destruct (decide (rows = ∅)).
     { subst rows. rewrite big_sepM_empty. iDestruct "And" as "[$ _]". }
    rewrite <- (big_sepM_insert (λ l '(cells, cv),
        pt_seq γ (inl l) cells cv) rows l (cells, cv)); last by trivial.
    rewrite pt_seq_equiv𝛽. rewrite bi.and_exist_r. iDestruct "And" as (𝛽) "And".
    rewrite pt_seq_big_sepM_equiv𝛽. rewrite bi.and_or_l.
    iDestruct "And" as "[[_ %Hemp]|And]"; first by contradiction.
    rewrite bi.and_exist_l. iDestruct "And" as (𝛽rows) "And".
    iAssert (⌜read 𝛽 (inl l) cells cv⌝)%I as "%Hread". { iDestruct "And" as "[[_ $] _]". }
    iAssert (⌜_⌝)%I as "%Hread2". { iDestruct "And" as "[_ [_ $]]". }
    iAssert (own γ (ra_𝛽 𝛽) ∧ own γ (ra_𝛽 𝛽rows))%I with "[And]" as "And". {
        iSplit. { iDestruct "And" as "[[$ _] _]". } iDestruct "And" as "[_ [$ _]]". }
    iDestruct (and_own_discrete_ucmra with "And") as (z) "[own [%Hincl1 %Hincl2]]".
    iDestruct (own_with_incl2 _ _ _ _ Hincl1 Hincl2 with "own")
          as (𝛼 𝛽' 𝜃) "[[%Hbig [%Hsub1 %Hsub2]] own]".
    rewrite pt_seq_big_sepM_equiv𝛽. iRight. iExists 𝛽'. iFrame "own". iPureIntro.
    intros l' cells' cv'. destruct (decide (l = l')) as [Heq|Hne].
     - subst l'. intros Hin. rewrite lookup_insert in Hin. inversion Hin. subst cells'. subst cv'.
       apply (read_𝛽_mono _ _ _ _ _ Hsub1 Hread).
     - intros Hin. rewrite lookup_insert_ne in Hin; last by trivial.
       apply (read_𝛽_mono _ _ _ _ _ Hsub2). apply Hread2. apply Hin.
  Qed.
  
  Lemma cmap_andM_sepM γ (rows: gmap L (list C * (C + V))) :
      ([∧ map] l ↦ '(cells, cv) ∈ rows, pt_seq γ (inl l) cells cv)%I ⊢
      [∗ map] l ↦ '(cells, cv) ∈ rows, pt_seq γ (inl l) cells cv.
  Proof.
    induction rows as [|l row ? Hnone IH] using map_ind.
    { iIntros. rewrite big_sepM_empty. done. }
    iIntros "And". destruct row as [cells cell].
    rewrite big_andM_insert; last by trivial. rewrite big_sepM_insert; last by trivial.
    iApply cmap_and_sepM_cons_row; first by trivial.
    iSplit. - iDestruct "And" as "[$ _]". - iApply IH. iDestruct "And" as "[_ $]".
  Qed.
  
  Lemma cmap_pt_seq_point_prop γ lc cells cv :
      factoring_props.point_prop (pt_seq γ lc cells cv).
  Proof.
      induction cells in lc |- *.
        - apply point_prop_own.
        - apply point_prop_sep. + apply point_prop_own. + apply IHcells.
  Qed.

  (** ** The full-authority cell map in the logic *)
  Context {fcmapl: fcmap_logicG Σ}.

  Definition fheap γ (𝛼: full_map) : iProp Σ := own γ (FOk (Some 𝛼) ∅ ∅).
  Definition fpt γ (lc: L + C) (cv: C + V) : iProp Σ := own γ (FOk None {[ lc := cv ]} ∅).
  Definition funt γ (u: untether_id) (c: C) (v: V) : iProp Σ :=
    own γ (FOk None ∅ {[ u := (c, v) ]}).

  Global Instance fpt_timeless γ lc cv : Timeless (fpt γ lc cv).
  Proof. apply _. Qed.
  Global Instance funt_timeless γ u c v : Timeless (funt γ u c v).
  Proof. apply _. Qed.
  Global Instance fheap_timeless γ 𝛼 : Timeless (fheap γ 𝛼).
  Proof. apply _. Qed.

  Lemma fpt_point_prop γ lc cv : factoring_props.point_prop (fpt γ lc cv).
  Proof. apply point_prop_own. Qed.

  Local Lemma fheap_own γ 𝛼 𝛽 𝜃 :
    fheap γ 𝛼 ∗ own γ (FOk None 𝛽 𝜃) ⊣⊢ own γ (FOk (Some 𝛼) 𝛽 𝜃).
  Proof.
    rewrite /fheap -own_op fcmap_op_auth; [|solve_map_disjoint..].
    by rewrite !map_empty_union.
  Qed.

  Local Lemma own_frag_op γ 𝛽1 𝜃1 𝛽2 𝜃2 :
    𝛽1 ##ₘ 𝛽2 → 𝜃1 ##ₘ 𝜃2 →
    own γ (FOk None 𝛽1 𝜃1) ∗ own γ (FOk None 𝛽2 𝜃2) ⊣⊢ own γ (FOk None (𝛽1 ∪ 𝛽2) (𝜃1 ∪ 𝜃2)).
  Proof. intros ??. by rewrite -own_op fcmap_op_frag. Qed.

  Lemma fcmap_init : ⊢ |==> ∃ γ, fheap γ ∅.
  Proof. iApply own_alloc. apply big_inv_empty. Qed.

  Lemma fheap_valid γ 𝛼 𝛽 𝜃 : own γ (FOk (Some 𝛼) 𝛽 𝜃) -∗ ⌜big_inv 𝛼 𝛽 𝜃⌝.
  Proof. iIntros "H". by iDestruct (own_valid with "H") as %?. Qed.

  Lemma fheap_no_dupes γ 𝛼 : fheap γ 𝛼 -∗ ⌜cells_no_dupes 𝛼⌝.
  Proof. iIntros "H". iDestruct (fheap_valid with "H") as %(_&_&?). done. Qed.

  Lemma fheap_fpt γ 𝛼 lc cv : fheap γ 𝛼 -∗ fpt γ lc cv -∗ ⌜𝛼_fine_pair 𝛼 lc cv⌝.
  Proof.
    iIntros "A B". iCombine "A B" as "A". rewrite fheap_own.
    iDestruct (fheap_valid with "A") as %(Hf&_&_). iPureIntro. apply Hf. apply lookup_singleton.
  Qed.

  Lemma fheap_funt γ 𝛼 u c v :
    fheap γ 𝛼 -∗ funt γ u c v -∗ ⌜∃ cs, 𝛼 !! inr u = Some (c :: cs, v)⌝.
  Proof.
    iIntros "A B". iCombine "A B" as "A". rewrite fheap_own.
    iDestruct (fheap_valid with "A") as %(_&Hu&_). iPureIntro.
    have := Hu u c v (lookup_singleton _ _). destruct (𝛼 !! inr u) as [[[|c' cs] v']|]; try done.
    intros [-> ->]. by eexists.
  Qed.

  Lemma fpt_excl γ lc cv cv' : fpt γ lc cv -∗ fpt γ lc cv' -∗ False.
  Proof.
    iIntros "A B". iDestruct (own_valid_2 with "A B") as %Hv.
    apply fcmap_valid_frag_disj in Hv as [Hd _].
    exfalso. eapply map_disjoint_spec; [done|apply lookup_singleton..].
  Qed.

  Lemma funt_excl γ u c v c' v' : funt γ u c v -∗ funt γ u c' v' -∗ False.
  Proof.
    iIntros "A B". iDestruct (own_valid_2 with "A B") as %Hv.
    apply fcmap_valid_frag_disj in Hv as [_ Hd].
    exfalso. eapply map_disjoint_spec; [done|apply lookup_singleton..].
  Qed.

  Lemma fcmap_alloc γ 𝛼 l v :
    𝛼 !! inl l = None →
    fheap γ 𝛼 ==∗ fheap γ (<[inl l := ([], v)]> 𝛼) ∗ fpt γ (inl l) (inr v).
  Proof.
    intros Hnone. rewrite /fpt fheap_own. iApply own_update. apply fcmap_update.
    intros 𝛽f 𝜃f _ _ Hinv. rewrite !map_empty_union in Hinv |- *.
    have Hnone' : 𝜙 𝛼 !! l = None by rewrite 𝜙_lookup Hnone.
    destruct (alloc_preserves_inv 𝛼 𝛽f 𝜃f l v Hnone' Hinv) as (Hinv' & H𝛽 & _).
    split; [by apply map_disjoint_singleton_l_2|]. split; [solve_map_disjoint|].
    by rewrite -insert_union_singleton_l.
  Qed.

  Lemma fcmap_delete γ 𝛼 l v :
    fheap γ 𝛼 -∗ fpt γ (inl l) (inr v) ==∗
      ⌜𝛼 !! inl l = Some ([], v)⌝ ∗ fheap γ (delete (inl l) 𝛼).
  Proof.
    iIntros "A B". iDestruct (fheap_fpt with "A B") as %Hp.
    iCombine "A B" as "A". rewrite fheap_own.
    iMod (own_update with "A") as "A"; last first.
    { iModIntro. iSplit; [done|]. rewrite /fheap. iExact "A". }
    apply fcmap_update. intros 𝛽f 𝜃f Hd _ Hinv.
    have Hl : ({[inl l := inr v]} ∪ 𝛽f) !! inl l = Some (inr v).
    { by rewrite lookup_union lookup_singleton union_Some_l. }
    destruct (del_preserves_inv 𝛼 _ _ l v Hl Hinv) as [Hinv' _].
    rewrite delete_union delete_singleton map_empty_union in Hinv'.
    rewrite delete_notin in Hinv'; [|by eapply map_disjoint_singleton_l].
    split; [solve_map_disjoint|]. split; [solve_map_disjoint|].
    by rewrite !map_empty_union.
  Qed.

  Lemma fcmap_write_loc γ 𝛼 l cs v v' lc :
    𝛼 !! inl l = Some (cs, v) → row_last (inl l) cs = Some lc →
    fheap γ 𝛼 -∗ fpt γ lc (inr v) ==∗ fheap γ (<[inl l := (cs, v')]> 𝛼) ∗ fpt γ lc (inr v').
  Proof.
    iIntros (Hk Hlast) "A B". iCombine "A B" as "A". rewrite /fpt !fheap_own.
    iApply (own_update with "A"). apply fcmap_update. intros 𝛽f 𝜃f Hd _ Hinv.
    rewrite map_empty_union in Hinv. rewrite map_empty_union.
    have Hinv' := write_row_preserves_inv 𝛼 _ 𝜃f 𝜃f (inl l) cs v v' lc Hk Hlast
      (unt_map_inv_insert_loc _ _ _ _ (proj1 (proj2 Hinv))) Hinv.
    rewrite insert_union_l insert_singleton in Hinv'.
    split; [|split; [solve_map_disjoint|done]].
    apply map_disjoint_singleton_l_2. by eapply map_disjoint_singleton_l.
  Qed.

  Lemma fcmap_write_unt γ 𝛼 u c cs v v' lc :
    𝛼 !! inr u = Some (c :: cs, v) → row_last (inr u) (c :: cs) = Some lc →
    fheap γ 𝛼 -∗ funt γ u c v -∗ fpt γ lc (inr v) ==∗
      fheap γ (<[inr u := (c :: cs, v')]> 𝛼) ∗ funt γ u c v' ∗ fpt γ lc (inr v').
  Proof.
    iIntros (Hk Hlast) "A B C". iCombine "B C" as "B". rewrite /funt /fpt.
    rewrite own_frag_op; [|solve_map_disjoint..]. rewrite !map_empty_union map_union_empty.
    iCombine "A B" as "A". rewrite fheap_own.
    iMod (own_update with "A") as "A".
    2: { rewrite -fheap_own. iDestruct "A" as "[$ A]".
         rewrite -(map_empty_union {[lc := _]}) -(map_union_empty {[u := _]}) -own_frag_op;
           [|solve_map_disjoint..].
         iDestruct "A" as "[$ $]". done. }
    apply fcmap_update. intros 𝛽f 𝜃f Hd1 Hd2 Hinv.
    have Hu : unt_map_inv (<[inr u:=(c :: cs, v')]> 𝛼) ({[u := (c, v')]} ∪ 𝜃f).
    { intros u' c' v0 Hl. destruct (decide (u' = u)) as [->|Hne].
      - rewrite lookup_insert. rewrite lookup_union lookup_singleton in Hl.
        rewrite (map_disjoint_singleton_l _ _ _ _ Hd2) in Hl. by simplify_eq.
      - rewrite lookup_insert_ne; [|congruence].
        rewrite lookup_union lookup_singleton_ne // left_id in Hl.
        apply (proj1 (proj2 Hinv)). rewrite lookup_union lookup_singleton_ne // left_id //. }
    have Hinv' := write_row_preserves_inv 𝛼 _ _ _ (inr u) (c :: cs) v v' lc Hk Hlast Hu Hinv.
    rewrite insert_union_l insert_singleton in Hinv'.
    split; [|split; [|done]].
    - apply map_disjoint_singleton_l_2. by eapply map_disjoint_singleton_l.
    - apply map_disjoint_singleton_l_2. by eapply map_disjoint_singleton_l.
  Qed.

  Lemma fcmap_untether γ 𝛼 lc c :
    fheap γ 𝛼 -∗ fpt γ lc (inl c) ==∗ ∃ k cells1 cells2 v u,
      ⌜is_row_for_lc 𝛼 lc k cells1 c cells2 v ∧ fresh_uid 𝛼 u⌝ ∗
      fheap γ (𝛼_untether 𝛼 lc k cells1 c cells2 v u) ∗ fpt γ lc (inr v) ∗ funt γ u c v.
  Proof using Infinite_C.
    iIntros "A B". iCombine "A B" as "A". rewrite /fpt fheap_own.
    iDestruct (fheap_valid with "A") as %Hinv0.
    destruct (get_row_for_lc 𝛼 _ ∅ lc c (lookup_singleton _ _) Hinv0)
      as (k & cells1 & cells2 & v & Hrow).
    destruct (exists_fresh_uid 𝛼) as [u Hu].
    iMod (own_update _ _ (FOk (Some (𝛼_untether 𝛼 lc k cells1 c cells2 v u))
      {[lc := inr v]} {[u := (c, v)]}) with "A") as "A".
    { apply fcmap_update. intros 𝛽f 𝜃f Hd1 Hd2 Hinv.
      have Hinv' := untether_preserves_inv 𝛼 _ _ lc k cells1 c cells2 v u Hrow Hu Hinv.
      have H𝜃 := fresh_uid_not_in_𝜃 _ _ _ u Hu Hinv. rewrite map_empty_union in H𝜃.
      rewrite insert_union_l insert_singleton map_empty_union insert_union_singleton_l in Hinv'.
      split; [|split; [by apply map_disjoint_singleton_l_2|done]].
      apply map_disjoint_singleton_l_2. by eapply map_disjoint_singleton_l. }
    iModIntro. iExists k, cells1, cells2, v, u. iSplit; [done|].
    rewrite -fheap_own. iDestruct "A" as "[$ A]".
    rewrite /funt -(map_union_empty {[lc := _]}) -(map_empty_union {[u := _]}) -own_frag_op;
      [|solve_map_disjoint..]. iExact "A".
  Qed.

  Lemma fcmap_retether γ 𝛼 l v u c :
    fheap γ 𝛼 -∗ fpt γ (inl l) (inr v) -∗ funt γ u c v ==∗ ∃ cs,
      ⌜𝛼 !! inl l = Some ([], v) ∧ 𝛼 !! inr u = Some (c :: cs, v)⌝ ∗
      fheap γ (<[inl l := (c :: cs, v)]> (delete (inr u) 𝛼)) ∗ fpt γ (inl l) (inl c).
  Proof.
    iIntros "A B C". iDestruct (fheap_fpt with "A B") as %Hl.
    iDestruct (fheap_funt with "A C") as %[cs Hu].
    iCombine "B C" as "B". rewrite /fpt /funt own_frag_op; [|solve_map_disjoint..].
    rewrite !map_empty_union map_union_empty. iCombine "A B" as "A". rewrite fheap_own.
    iMod (own_update _ _ (FOk (Some (<[inl l := (c :: cs, v)]> (delete (inr u) 𝛼)))
      {[inl l := inl c]} ∅) with "A") as "A".
    { apply fcmap_update. intros 𝛽f 𝜃f Hd1 Hd2 Hinv.
      have Hr : read ({[inl l := inr v]} ∪ 𝛽f) (inl l) [] (inr v).
      { by rewrite /= lookup_union lookup_singleton union_Some_l. }
      have H𝜃 : ({[u := (c, v)]} ∪ 𝜃f) !! u = Some (c, v).
      { by rewrite lookup_union lookup_singleton union_Some_l. }
      have Hinv' := retether_preserves_inv 𝛼 _ _ u l [] v c Hr H𝜃 Hinv.
      rewrite /𝛼_retether Hu /write /= insert_union_l insert_singleton in Hinv'.
      rewrite delete_union delete_singleton map_empty_union in Hinv'.
      rewrite delete_notin in Hinv'; [|by eapply map_disjoint_singleton_l].
      rewrite map_empty_union.
      split; [|split; [solve_map_disjoint|done]].
      apply map_disjoint_singleton_l_2. by eapply map_disjoint_singleton_l. }
    iModIntro. iExists cs. iSplit; [done|]. by rewrite -fheap_own.
  Qed.

  Lemma fcmap_insert_front γ 𝛼 l cs v cv0 :
    𝛼 !! inl l = Some (cs, v) →
    fheap γ 𝛼 -∗ fpt γ (inl l) cv0 ==∗ ∃ nc, ⌜fresh_cell_id 𝛼 nc⌝ ∗
      fheap γ (<[inl l := (nc :: cs, v)]> 𝛼) ∗ fpt γ (inl l) (inl nc) ∗ fpt γ (inr nc) cv0.
  Proof using Infinite_C.
    iIntros (Hk) "A B". iCombine "A B" as "A". rewrite /fpt fheap_own.
    iDestruct (fheap_valid with "A") as %Hinv0.
    destruct (exists_fresh_cell_id 𝛼) as [nc Hnc].
    have Hnc𝛽 := fresh_cell_not_in_𝛽 _ _ _ nc Hnc Hinv0.
    have Hne : inl l ≠ (inr nc : L + C) by done.
    iMod (own_update _ _ (FOk (Some (<[inl l := (nc :: cs, v)]> 𝛼))
      ({[inl l := inl nc]} ∪ {[inr nc := cv0]}) ∅) with "A") as "A".
    { apply fcmap_update. intros 𝛽f 𝜃f Hd1 Hd2 Hinv.
      have Hb : ({[inl l := cv0]} ∪ 𝛽f) !! inl l = Some cv0.
      { by rewrite lookup_union lookup_singleton union_Some_l. }
      have Hnc' := fresh_cell_not_in_𝛽 _ _ _ nc Hnc Hinv.
      have Hinv' := insert_front_preserves_inv 𝛼 _ _ l cs v cv0 nc Hk Hb Hnc Hinv.
      rewrite lookup_union_None in Hnc'. destruct Hnc' as [_ Hnc'].
      have Hl : 𝛽f !! inl l = None by eapply map_disjoint_singleton_l.
      split; [|split; [done|]].
      - apply map_disjoint_union_l_2; by apply map_disjoint_singleton_l_2.
      - rewrite map_empty_union in Hinv' |- *. eapply big_inv_eq; [|exact Hinv'].
        f_equal. apply map_eq. intros i.
        destruct (decide (i = inl l)) as [->|]; [by rewrite !lookup_insert lookup_union lookup_singleton|].
        rewrite lookup_insert_ne //. destruct (decide (i = inr nc)) as [->|].
        + rewrite lookup_insert !lookup_union lookup_singleton_ne // lookup_singleton.
          by rewrite left_id Hnc'.
        + rewrite lookup_insert_ne // !lookup_union !lookup_singleton_ne //. }
    iModIntro. iExists nc. iSplit; [done|]. rewrite -fheap_own. iDestruct "A" as "[$ A]".
    rewrite -(map_union_empty (∅ : unt_map)) -own_frag_op; [done|..|solve_map_disjoint].
    by apply map_disjoint_singleton_l_2, lookup_singleton_ne.
  Qed.

  Lemma fcmap_delete_front γ 𝛼 l c cv :
    fheap γ 𝛼 -∗ fpt γ (inl l) (inl c) -∗ fpt γ (inr c) cv ==∗ ∃ cs v,
      ⌜𝛼 !! inl l = Some (c :: cs, v)⌝ ∗ fheap γ (<[inl l := (cs, v)]> 𝛼) ∗ fpt γ (inl l) cv.
  Proof.
    iIntros "A B C". iDestruct (fheap_fpt with "A B") as %Hl.
    rewrite /𝛼_fine_pair in Hl.
    destruct (𝛼 !! inl l) as [[[|c' cs] v]|] eqn:Hk; try done. simplify_eq.
    have Hne : (inl l : L + C) ≠ inr c by done.
    iCombine "B C" as "B". rewrite /fpt own_frag_op; [|by apply map_disjoint_singleton_l_2, lookup_singleton_ne|solve_map_disjoint].
    rewrite map_empty_union. iCombine "A B" as "A". rewrite fheap_own.
    iMod (own_update _ _ (FOk (Some (<[inl l := (cs, v)]> 𝛼)) {[inl l := cv]} ∅) with "A") as "A".
    { apply fcmap_update. intros 𝛽f 𝜃f Hd1 Hd2 Hinv.
      have Hb1 : ({[inl l := inl c]} ∪ {[inr c := cv]} ∪ 𝛽f) !! inl l = Some (inl c).
      { by rewrite !lookup_union lookup_singleton lookup_singleton_ne // right_id union_Some_l. }
      have Hb2 : ({[inl l := inl c]} ∪ {[inr c := cv]} ∪ 𝛽f) !! inr c = Some cv.
      { by rewrite !lookup_union lookup_singleton lookup_singleton_ne // left_id union_Some_l. }
      have Hrow : is_row_for_lc 𝛼 (inl l) (inl l) [] c cs v by done.
      have Hinv' := delete_cell_preserves_inv 𝛼 _ _ (inl l) c cv (inl l) [] cs v Hb1 Hb2 Hrow Hinv.
      rewrite /𝛼_delete_cell /= in Hinv'.
      have Hf1 : 𝛽f !! inl l = None.
      { eapply map_disjoint_Some_l in Hd1; [done|]. by rewrite lookup_union lookup_singleton union_Some_l. }
      have Hf2 : 𝛽f !! inr c = None.
      { eapply map_disjoint_Some_l in Hd1; [done|].
        by rewrite lookup_union lookup_singleton lookup_singleton_ne // left_id. }
      split; [by apply map_disjoint_singleton_l_2|]. split; [done|].
      eapply big_inv_eq; [|exact Hinv']. apply map_eq. intros i.
      destruct (decide (i = inl l)) as [->|]; [by rewrite lookup_insert lookup_union lookup_singleton|].
      rewrite lookup_insert_ne //. destruct (decide (i = inr c)) as [->|].
      + by rewrite lookup_delete lookup_union lookup_singleton_ne // left_id Hf2.
      + by rewrite lookup_delete_ne // !lookup_union !lookup_singleton_ne // !left_id. }
    iModIntro. iExists cs, v. iSplit; [done|]. by rewrite -fheap_own.
  Qed.

End Cmap.
