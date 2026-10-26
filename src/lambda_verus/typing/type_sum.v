From iris.proofmode Require Import proofmode.
From lrust.lang Require Import memcpy.
From lrust.typing Require Import int uninit uniq_bor shr_bor own sum.
From lrust.typing Require Import lft_contexts type_context programs product programs_util.
From lrust.typing Require Import base_type freeable_util uniq_util.
From guarding Require Import guard tactics.
From lrust.lifetime Require Import lifetime_full.

Set Default Proof Using "Type".
Open Scope nat.

Implicit Type (𝔄 𝔅: syn_type) (𝔄l 𝔅l: syn_typel).

Notation sum_pad_size tyl ty := (max_ty_size tyl - ty.(ty_size))%nat.

Fixpoint padding_to_vec (n: nat) (p: list val) : vec val n :=
    match n, p with
      | 0, _ => [# ]
      | S n', [] => (#☠) ::: padding_to_vec n' []
      | S n', p' :: pad' => p' ::: padding_to_vec n' pad'
    end.

Lemma pad_eq_padding_to_vec b n :
  pad (fmap FVal b) n = fmap FVal (vec_to_list (padding_to_vec n b)).
Proof.
  generalize b. clear b. induction n.
  - intros. simpl. unfold pad. case_decide. { done. } simpl. destruct b. { done. }
    simpl in H. lia.
  - intros. simpl. destruct b.
    + simpl. rewrite <- IHn.
      unfold pad. case_decide. { simpl in H. lia. } simpl. f_equal. f_equal. lia.
    + rewrite pad_cons. simpl. rewrite <- IHn. trivial.
Qed.
    
Lemma pad_app
  (a : list fancy_val) (b: list val) (n: nat) :
  length a ≤ n →
  pad (a ++ fmap FVal b) n = a ++ fmap FVal (vec_to_list (padding_to_vec (n - length a) b)).
Proof.
  generalize n. clear n. induction a.
  - intros n Hineq. simpl. rewrite <- pad_eq_padding_to_vec. f_equal. lia.
  - intros n Hineq. simpl. simpl in Hineq. destruct n.
    + lia. + rewrite pad_cons. rewrite IHa; last by lia. done.
Qed.

Section type_sum.
  Context `{!typeG Σ}.
  
  Lemma split_freeable_xsum {𝔄l} i (tyl: typel 𝔄l) n l :
    freeable_util.freeable_sz n (ty_size (Σ! tyl)) l
    ⊣⊢ 
      freeable_util.freeable_sz n 1 l
      ∗ freeable_util.freeable_sz n (ty_size (tyl +!! i)) (l +ₗ 1)
      ∗ freeable_util.freeable_sz n (sum_pad_size tyl (tyl +!! i)) (l +ₗ S ((ty_size (tyl +!! i)))).
  Proof.
    replace (S (ty_size (tyl +!! i))) with (1 + (ty_size (tyl +!! i))); last by lia.
    rewrite <- shift_loc_assoc_nat. rewrite freeable_sz_split. rewrite freeable_sz_split.
    f_equiv. simpl. have h := max_hlist_with_ge (λ X : syn_type, ty_size) tyl i.
    rewrite Nat.add_comm. rewrite Nat.sub_add; trivial.
  Qed.
  
  Lemma split_pt_xsum {𝔄l} i (tyl: typel 𝔄l) x0 pad tid l :
      l ↦!∗ ty_phys (Σ! tyl) (pinj i x0, pad) tid
      ⊣⊢
        (l ↦∗ [ #i ])
        ∗ ((l +ₗ 1) ↦!∗ ty_phys (tyl +!! i) x0 tid)
        ∗ ((l +ₗ S ((ty_size (tyl +!! i)))) ↦!∗ fmap FVal
            (vec_to_list (padding_to_vec (sum_pad_size tyl (tyl +!! i)) (pad)))).
  Proof.
    replace (S (ty_size (tyl +!! i))) with (1 + (ty_size (tyl +!! i))); last by lia.
    rewrite <- shift_loc_assoc_nat. 
    replace (l +ₗ 1%nat +ₗ ty_size (tyl +!! i)) with (l +ₗ 1%nat +ₗ length (ty_phys (tyl +!! i) x0 tid)). 2: { f_equal. rewrite ty_size_eq. trivial. }
    rewrite <- heap_mapsto_fancy_vec_app.
    rewrite heap_mapsto_vec_singleton.
    replace (l ↦ #i)%I with (l ↦! FVal #i)%I; last by done.
    rewrite <- (heap_mapsto_fancy_vec_cons _ (FVal #i)).
    unfold ty_phys, xsum_ty. rewrite to_xsum_pinj.
    rewrite pad_cons. f_equal. simpl. rewrite pad_app.
      - rewrite ty_size_eq. done.
      - rewrite ty_size_eq. apply (max_hlist_with_ge (λ X : syn_type, ty_size) tyl i).
  Qed.
 
  Local Lemma drop_drop {A} n (cells: list A) :
      drop n (drop 1 cells) = drop (S n) cells.
  Proof. destruct n; destruct cells; trivial. Qed.
    
  Lemma xsum_gho_pers_pinj {𝔄l} i (tyl: typel 𝔄l) x0 pad d g tid :
    ty_gho_pers (Σ! tyl) (pinj i x0, pad) d g tid ⊣⊢ ty_gho_pers (tyl +!! i) x0 d g tid.
  Proof.
    rewrite [ty_gho_pers (Σ! tyl)]/ty_gho_pers /xsum_ty /=. by rewrite to_xsum_pinj.
  Qed.

  Lemma split_pt_xsum_cells {𝔄l} i (tyl: typel 𝔄l) x0 pad tid l cells :
      l ↦[^ cells ]!∗ ty_phys (Σ! tyl) (pinj i x0, pad) tid
      ⊣⊢
        (l ↦[^ take 1 cells ]∗ [ #i ])
        ∗ ((l +ₗ 1) ↦[^ take (ty_size (tyl +!! i)) (drop 1 cells) ]!∗ ty_phys (tyl +!! i) x0 tid)
        ∗ ((l +ₗ S ((ty_size (tyl +!! i)))) ↦[^ drop (S (ty_size (tyl +!! i))) cells ]!∗ fmap FVal
            (vec_to_list (padding_to_vec (sum_pad_size tyl (tyl +!! i)) (pad)))).
  Proof.
    replace (S (ty_size (tyl +!! i))) with (1 + (ty_size (tyl +!! i))); last by lia.
    rewrite <- shift_loc_assoc_nat. 
    replace (l +ₗ 1%nat +ₗ ty_size (tyl +!! i)) with (l +ₗ 1%nat +ₗ length (ty_phys (tyl +!! i) x0 tid)). 2: { f_equal. rewrite ty_size_eq. trivial. }
    unfold xsum_ty, ty_phys. rewrite to_xsum_pinj.
    eassert ((FVal #i :: _ ++ _) = ([FVal #i] ++ _) ++ _) as ->. { rewrite <- List.app_assoc. trivial. }
    rewrite pad_app. rewrite <- List.app_assoc.
    - do 2 (rewrite heap_mapsto_cells_fancy_vec_app'). f_equiv; [|f_equiv].
      + rewrite <- heap_mapsto_cells_fancy_fmap_eq. trivial.
      + rewrite ty_size_eq. trivial.
      + rewrite List.length_app. rewrite ty_size_eq. simpl. rewrite drop_drop. trivial.
    - rewrite List.length_app. rewrite ty_size_eq.
      have Ha := (max_hlist_with_ge (λ X : syn_type, ty_size) tyl i).
      simpl. assert (∀ x y, x <= y → S x <= S y) as Ht by lia. apply Ht. apply Ha.
  Qed.
  
  Lemma split_pt_xsum_cells' {𝔄l} i (tyl: typel 𝔄l) l cells :
      (l, cells) #↦∗_ 
      ⊣⊢
        ((l, take 1 cells) #↦∗_)
        ∗ ((l +ₗ 1, take (ty_size (tyl +!! i)) (drop 1 cells)) #↦∗_)
        ∗ ((l +ₗ S ((ty_size (tyl +!! i))), drop (S (ty_size (tyl +!! i))) cells) #↦∗_ ).
  Proof.
    replace (S (ty_size (tyl +!! i))) with (1 + (ty_size (tyl +!! i))); last by lia.
    rewrite <- shift_loc_assoc_nat. 
    rewrite (heap_cloc_mapsto_emp_vec_app _ (1 + (ty_size (tyl +!! i)))).
    rewrite bi.sep_assoc.
    f_equiv.
     - rewrite (heap_cloc_mapsto_emp_vec_app _ 1). f_equiv.
      + destruct cells; trivial.
      + destruct cells; trivial. destruct ((ty_size (tyl +!! i))); trivial.
     - simpl. unfold cloc_skip. simpl. f_equiv. f_equal.
      * rewrite shift_loc_assoc_nat. trivial.
  Qed.
  
  Lemma split_pt_xsum_cells'' {𝔄l} i (tyl: typel 𝔄l) x0 pad tid l :
      l #↦!∗ ty_phys (Σ! tyl) (pinj i x0, pad) tid
      ⊣⊢
        ((cloc_take l 1) #↦∗ [ #i ])
        ∗ (cloc_take (cloc_skip l 1) (ty_size (tyl +!! i)) #↦!∗ ty_phys (tyl +!! i) x0 tid)
        ∗ (cloc_skip (cloc_skip l 1) (ty_size (tyl +!! i)) #↦!∗ fmap FVal
            (vec_to_list (padding_to_vec (sum_pad_size tyl (tyl +!! i)) (pad)))).
  Proof.
    unfold ty_phys, xsum_ty. simpl. rewrite to_xsum_pinj.
    eassert ((FVal #i :: _ ++ _) = ([FVal #i] ++ _) ++ _) as ->. { rewrite <- List.app_assoc. trivial. }
    rewrite pad_app. rewrite <- List.app_assoc.
    - do 2 (rewrite heap_cloc_mapsto_fancy_vec_app). f_equiv; [|f_equiv].
      + rewrite <- heap_complete_mapsto_fancy_fmap_eq. trivial.
      + rewrite ty_size_eq. trivial.
      + rewrite List.length_app. rewrite ty_size_eq. simpl.
        unfold cloc_skip. rewrite drop_drop. trivial.
    - rewrite List.length_app. rewrite ty_size_eq.
      have Ha := (max_hlist_with_ge (λ X : syn_type, ty_size) tyl i).
      simpl. assert (∀ x y, x <= y → S x <= S y) as Ht by lia. apply Ht. apply Ha.
  Qed.

  (** * Owning Pointers *)

  Lemma tctx_unwrap_own_xsum {𝔄l 𝔅l} i (tyl: typel 𝔄l) n p (T: tctx 𝔅l) E L :
    let tyi := tyl +!! i in
    tctx_incl E L (p ◁ own_ptr n (Σ! tyl) +:: T)
      (p +ₗ #0 ◁ own_ptr n int +:: p +ₗ #1 ◁ own_ptr n tyi +::
        p +ₗ #(S tyi.(ty_size)) ◁ own_ptr n (↯ (sum_pad_size tyl tyi)) +:: T)
      (λ post '((l, (s, pad)) -:: bl), λ mask π, ∃a: ~~(𝔄l !!ₗ i),
        s = pinj i a ∧ ∀ pad', post (
          (l, Z.of_nat i) -::
          (l +ₗ 1, a) -::
          (l +ₗ (S tyi.(ty_size)), pad') -::
          bl) mask π).
  Proof.
    split. { move=>/= ?? Hyp [[[??][??]]?]. do 5 f_equiv. apply forall_iff. intros p0. apply Hyp. }
    iIntros (G tid [[l [x pad]] xl] mask post TimelessG) "#LFT #PROPH #UNIQ #E #GguardsL G /=[T Tl] #Obs".
    iMod (proph_obs_sat with "PROPH Obs") as (π) "%X". { solve_ndisj. }
    destruct X as [x0 [Heqx _]]. subst x.
    iDestruct "T" as (v d) "(%path & #⧖ & [gho %phys])". inversion phys. subst v.
    destruct d as [|d']; first by done.
    iDestruct "gho" as "[pt [free gho]]".
    iDestruct (split_freeable_xsum i with "free") as "[free1 [free2 free3]]".
    iDestruct (split_pt_xsum i with "pt") as "[pt1 [pt2 pt3]]".
    iModIntro.
    set tyi := tyl +!! i.
    set pad' := padding_to_vec (sum_pad_size tyl tyi) pad.
    iExists ((l, Z.of_nat i) -:: (l +ₗ 1, x0) -:: (l +ₗ (S tyi.(ty_size)), pad') -:: xl).
    iFrame "G". iFrame "Tl". simpl. 
    iSplit.
      - iSplitL "pt1 free1". { iExists (#l), (S d'). iFrame "⧖".
          iSplit. { iPureIntro. simpl. rewrite path. rewrite shift_loc_0. trivial. }
          rewrite <- heap_mapsto_fancy_fmap_eq.
          iFrame "pt1". iFrame "free1". iSplit; done.
        }
        iSplitL "pt2 free2 gho". { iExists (#(l +ₗ 1)), (S d'). iFrame "⧖".
          iSplit. { iPureIntro. simpl. rewrite path. trivial. }
          iFrame "pt2". iFrame "free2". unfold ty_gho_own, xsum_ty.
          rewrite to_xsum_pinj. iFrame "gho". done.
        }
        { iExists (#((l +ₗ S (ty_size tyi)))), (S d'). iFrame "⧖".
          iSplit. { iPureIntro. simpl. rewrite path. trivial. }
          iFrame "pt3". iFrame "free3". done.
        }
     - iApply (proph_obs_impl with "Obs").
       intros π0 [x1 [Peq Ha]]. apply pinj_Inj in Peq. subst x1. apply Ha.
  Qed.

  Lemma type_case_own_outer {𝔄l 𝔅l ℭl 𝔇} (tyl: typel 𝔄l) trl (T: tctx 𝔅l)
      (T': tctx ℭl) n p el el' trx E L I (C: cctx 𝔇) :
    IntoPlistc el el' →
    tctx_extract_ctx E L +[p ◁ own_ptr n (Σ! tyl)] T T' trx →
    ([∗ hlist] ty;- e; tr ∈ tyl;- el'; trl,
      typed_body E L I C (p ◁ own_ptr n (Σ! tyl) +:: T') e tr) -∗
    typed_body E L I C T (case: !p of el)
      (trx ∘ (λ post '((l, (s, pad)) -:: cl), let 'xinj i _ := to_xsum s in
        (trl -!! i) post ((l, (s, pad)) -:: cl)))%type.
  Proof.
    move=> ->. iIntros (?) "el". iApply typed_body_tctx_incl; [done|].
    iIntros (tid [s ?] mask post iκs) "LFT TIME PROPH UNIQ E L I C /=[p T] #?".
    destruct s as [l [x pad]].
    replace x with (@of_xsum _ (~~) (𝔄l) (to_xsum x)); last by rewrite semi_iso'; trivial.
    refine (match (to_xsum x) with | xinj i x0 => _ end).
    wp_apply (wp_hasty with "p").
    iIntros (v d) "%Hpath #⧖ [gho %phys]". inversion phys. subst v.
    destruct d as [|d']; first by done.
    iDestruct "gho" as "[pt [free gho]]".
    iDestruct (split_pt_xsum i with "pt") as "[pt1 [pt2 pt3]]".
    rewrite heap_mapsto_vec_singleton. wp_read.
    rewrite <- heap_mapsto_vec_singleton. 
    wp_case.
    { split; [lia|]. by rewrite Nat2Z.id -vlookup_lookup plistc_to_vec_lookup. }
    iDestruct (big_sepHL_2_lookup with "el") as "el".
    iApply ("el" $! _ ((_) -:: _) with "LFT TIME PROPH UNIQ E L I C [-] []"); last first.
    { iApply proph_obs_impl; [|done]=>/= ?. by rewrite to_xsum_pinj. }
    iFrame "T". iExists _, _. iSplit; [done|]. iFrame "⧖".
    iFrame. rewrite split_pt_xsum. iFrame. done.
  Qed.

  (* these are just utilities that combine tctx_unwrap_own_xsum with type_case_own_outer *)
(*
  Lemma type_case_own {𝔄l 𝔅l ℭl 𝔇} (tyl: typel 𝔄l) (trl : plist (λ _ : syn_type, predl_trans' (at_locₛ (Σ! 𝔄l) :: ℭl) 𝔇) 𝔄l) (T: tctx 𝔅l)
      (T': tctx ℭl) n p el el' trx E L I (C: cctx 𝔇) :
    IntoPlistc el el' →
    tctx_extract_ctx E L +[p ◁ own_ptr n (Σ! tyl)] T T' trx →
    ([∗ hlist] ty;- e; tr ∈ tyl;- el'; trl, match tr with
      | inl otr => typed_body E L I C (p ◁ own_ptr n (Σ! tyl) +:: T') e otr
      | inr itr => typed_body E L I C
          (p +ₗ #0 ◁ own_ptr n int +:: p +ₗ #1 ◁ own_ptr n ty +::
            p +ₗ #(S ty.(ty_size)) ◁ own_ptr n (↯ (sum_pad_size tyl ty)) +:: T') e itr
      end) -∗
    typed_body E L I C T (case: !p of el) (trx ∘ (λ post '(s -:: cl),
      let 'xinj i a := to_xsum s in match trl -!! i with
        | inl otr => otr post (s -:: cl)
        | inr itr => itr post (Z.of_nat i -:: a -:: () -:: cl)
        end)).
  Proof.
    iIntros (??) "el". iApply typed_body_tctx_incl; [done|]. via_tr_impl.
    { iApply (type_case_own_outer _ (pbyidx (λ i post '(s -:: cl),
        match trl -!! i with inl otr => otr post (s -:: cl) | inr itr => _ end
        : Prop))); [apply tctx_incl_refl|].
      rewrite !big_sepHL_2_big_sepN. iApply (big_sepN_impl with "el").
      iIntros "!>" (i) "?". rewrite pbyidx_plookup.
      case (trl -!! i)=> ?; [by via_tr_impl; [done|]=> ?[??]?|]. via_tr_impl.
      { iApply typed_body_tctx_incl; [apply tctx_unwrap_own_xsum|done]. }
      move=>/= ?[??]. exact id. }
    move=> ?[s ?]/=. case (to_xsum s) as [i ?] eqn: Eq. rewrite pbyidx_plookup.
    move: (trl -!! i). case; [done|]=>/= ??. eexists _. split; [|done].
    move: Eq=> /(f_equal of_xsum)=>/= <-. by rewrite semi_iso'.
  Qed.

  Lemma type_case_own_inner {𝔄l 𝔅l ℭl 𝔇} (tyl: typel 𝔄l) trl (T: tctx 𝔅l)
      (T': tctx ℭl) n p el el' trx E L (C: cctx 𝔇) :
    IntoPlistc el el' →
    tctx_extract_ctx E L +[p ◁ own_ptr n (Σ! tyl)] T T' trx →
    ([∗ hlist] ty;- e; tr ∈ tyl;- el'; trl,
      typed_body E L C (p +ₗ #0 ◁ own_ptr n int +:: p +ₗ #1 ◁ own_ptr n ty +::
        p +ₗ #(S ty.(ty_size)) ◁ own_ptr n (↯ (sum_pad_size tyl ty)) +:: T') e tr) -∗
    typed_body E L C T (case: !p of el) (trx ∘ (λ post '(s -:: cl),
      let 'xinj i a := to_xsum s in
      (trl -!! i) post (Z.of_nat i -:: a -:: () -:: cl))).
  Proof.
    iIntros (??) "el". iApply typed_body_tctx_incl; [done|]. via_tr_impl.
    { iApply (type_case_own _ (pbyidx (λ i, inr (trl -!! i)))); [solve_typing|].
      rewrite !big_sepHL_2_big_sepN. iApply (big_sepN_impl with "el").
      iIntros "!>" (?) "?". by rewrite pbyidx_plookup. }
    move=> ?[s ?]/=. case (to_xsum s)=>/= ??. by rewrite pbyidx_plookup.
  Qed.
  *)

  (** * Shared References *)
 
  Lemma tctx_unwrap_shr_xsum {𝔄l 𝔅l} i (tyl: typel 𝔄l) κ p (T: tctx 𝔅l) E L :
    tctx_incl E L (p ◁ &shr{κ} (Σ! tyl) +:: T) (p +ₗ #1 ◁ &shr{κ} (tyl +!! i) +:: T)
      (λ post '((l, (s, pad)) -:: bl), λ mask π, ∃a: (~~(𝔄l !!ₗ i)), s = pinj i a
          ∧ post ((cloc_take (cloc_skip l 1) (ty_size (tyl +!! i)), a) -:: bl) mask π).
  Proof.
    split. { move=>/= x y H [[?[??]]?]. do 5 f_equiv. apply H. }
    iIntros (? tid [[cloc [x pad]] xl] ???) "_ PROPH _ _ _ $ /=[p T] #Obs".
    iMod (proph_obs_sat with "PROPH Obs") as %[?[?[Eq _]]]; [done|]. iModIntro.
    iDestruct "p" as (val d Ev) "[#⧖ [gho %phys]]".
    destruct d; first by done.
    destruct val as [|l]; last by done. destruct l as [| |]; [done| |done].
    iExists ((cloc_take (cloc_skip cloc 1) (ty_size (tyl +!! i)), x1) -:: _). iFrame "T". iSplit.
    { iExists _, _. iSplit; [by rewrite/= Ev|]. iFrame "⧖".
    iDestruct "gho" as "(#pt & #gho & #ghopers)".
    iSplit; [iSplit; [|iSplit]|].
      - simpl. iApply (guards_transitive_left with "pt []"). leaf_by_sep.
        destruct cloc as [q cells]. simpl. rewrite Eq. rewrite split_pt_xsum_cells.
        iIntros "(A & B & C)". iFrame. iIntros. iFrame.
      - simpl. unfold xsum_ty, ty_shr. simpl. rewrite Eq.
        rewrite to_xsum_pinj. iFrame "gho".
      - simpl. unfold xsum_ty, ty_gho_own, ty_phys, ty_gho_pers. simpl. rewrite Eq.
        rewrite to_xsum_pinj. iFrame "ghopers".
      - iPureIntro. simpl in phys. inversion phys. trivial.
    }
    iApply (proph_obs_impl with "Obs"). intros π [xi [-> Ha]].
    apply pinj_Inj in Eq. subst x1. apply Ha.
  Qed.

  Lemma type_case_shr_outer {𝔄l 𝔅l ℭl 𝔇} (tyl: typel 𝔄l) trl (T: tctx 𝔅l)
      (T': tctx ℭl) κ p el el' trx E L I (C: cctx 𝔇) :
    IntoPlistc el el' →
    tctx_extract_ctx E L +[p ◁ &shr{κ} (Σ! tyl)] T T' trx → lctx_lft_alive E L κ →
    ([∗ hlist] ty;- e; tr ∈ tyl;- el'; trl,
      typed_body E L I C (p ◁ &shr{κ} (Σ! tyl) +:: T') e tr) -∗
    typed_body E L I C T (case: !p of el)
      (trx ∘ (λ post '((l, (s, pad)) -:: cl), let 'xinj i _ := to_xsum s in
        (trl -!! i) post ((l, (s, pad)) -:: cl)))%type.
  Proof.
    move=> ->. iIntros (? Alv) "el". iApply typed_body_tctx_incl; [done|].
    iIntros (tid [s ?] mask post iκs) "#LFT #TIME PROPH UNIQ #E L I C /=[p T] #?".
    destruct s as [l [x pad]].
    replace x with (@of_xsum _ (~~) (𝔄l) (to_xsum x)); last by rewrite semi_iso'; trivial.
    refine (match (to_xsum x) with | xinj i x0 => _ end).
    wp_apply (wp_hasty with "p").
    iIntros (v d) "%Hpath #⧖ [gho %phys]". inversion phys. subst v.
    destruct d as [|d']; first by done.
    iDestruct "gho" as "[#pt [free gho]]".
    iDestruct (Alv with "L E") as "#Alv".
    iDestruct (guards_transitive_right with "Alv pt") as "#Gpt".
    rewrite (split_pt_xsum_cells i).
    iDestruct (guards_weaken_rhs_sep_l with "Gpt") as "#Gdiscriminant".
    iDestruct (guards_weaken_rhs_sep_r with "Gpt") as "#Grest".
    iDestruct (guards_weaken_rhs_sep_l with "Grest") as "#Gmain".
    wp_bind (!(LitV l.1))%E.
    iApply (wp_persistent_time_receipt with "TIME ⧖"). { set_solver. } iIntros "H£ ⧖'".
    iDestruct (lc_weaken (_)%nat with "H£") as "£1"; last first.
    {
    iApply (wp_read_na_guarded_cells_singleton with "[L £1]"); first by solve_ndisj.
    { iFrame "Gdiscriminant". iFrame. }
    iNext. iIntros "L".
    wp_case. { split; [lia|]. by rewrite Nat2Z.id -vlookup_lookup plistc_to_vec_lookup. }
    iDestruct (big_sepHL_2_lookup with "el") as "el".
    iApply ("el" $! _ ((_) -:: _) with "LFT TIME PROPH UNIQ E L I C [-] []"); last first.
    { iApply proph_obs_impl; [|done]=>/= ?. by rewrite to_xsum_pinj. }
    iFrame "T". iExists _, _. iSplit; [done|]. iFrame "⧖".
    iFrame. simpl.
    replace (S d' + 1) with (S (d' + 1)) by lia.
    rewrite (split_pt_xsum_cells i).
    iFrame "pt". done.
    }
    unfold advance_credits. lia.
  Qed.
    
  Lemma type_case_shr {𝔄l 𝔅l ℭl 𝔇} (tyl: typel 𝔄l) trl (T: tctx 𝔅l)
      (T': tctx ℭl) κ p el el' trx E L I (C: cctx 𝔇) :
    IntoPlistc el el' →
    tctx_extract_ctx E L +[p ◁ &shr{κ} (Σ! tyl)] T T' trx → lctx_lft_alive E L κ →
    ([∗ hlist] ty;- e; tr ∈ tyl;- el'; trl, match tr with
      | inl otr => typed_body E L I C (p ◁ &shr{κ} (Σ! tyl) +:: T') e otr
      | inr itr => typed_body E L I C (p +ₗ #1 ◁ &shr{κ} ty +:: T') e itr
      end) -∗
    typed_body E L I C T (case: !p of el) (trx ∘ (λ post '((l, (s, pad)) -:: cl),
      let 'xinj i a := to_xsum s in match trl -!! i with
        | inl otr => otr post ((l, (s, pad)) -:: cl)
        | inr itr => itr post ((cloc_take (cloc_skip l 1) (ty_size (tyl +!! i)), a) -:: cl)
        end)).
  Proof.
    iIntros (???) "el". iApply typed_body_tctx_incl; [done|]. via_tr_impl.
    { iApply (type_case_shr_outer _ (pbyidx (λ i post '((l, (s, pad)) -:: cl), λ mask π,
        match trl -!! i with inl otr => otr post ((l, (s, pad)) -:: cl) mask π | inr itr => _ end
        : Prop))); [apply tctx_incl_refl|done|].
      rewrite !big_sepHL_2_big_sepN. iApply (big_sepN_impl with "el").
      iIntros "!>" (i) "?". rewrite pbyidx_plookup.
      case (trl -!! i)=> ?. { via_tr_impl; first by done. intros post xl mask π Ha. 
          destruct xl as [[l [s pad]] cl]. trivial. }
      via_tr_impl.
      { iApply typed_body_tctx_incl; [apply tctx_unwrap_shr_xsum|done]. }
      move=>/= ?[[?[??]]?]??. exact id. }
    move=> ?[[l [s pad]] ?]/=. case (to_xsum s) as [i ?] eqn: Eq. rewrite pbyidx_plookup.
    move: (trl -!! i). case; [done|]=>/= ??. eexists _. split; [|done].
    move: Eq=> /(f_equal of_xsum)=>/= <-. by rewrite semi_iso'.
  Qed.

  Lemma type_case_shr_inner {𝔄l 𝔅l ℭl 𝔇} (tyl: typel 𝔄l) trl (T: tctx 𝔅l)
      (T': tctx ℭl) κ p el el' trx E L I (C: cctx 𝔇) :
    IntoPlistc el el' →
    tctx_extract_ctx E L +[p ◁ &shr{κ} (Σ! tyl)] T T' trx → lctx_lft_alive E L κ →
    ([∗ hlist] ty;- e; tr ∈ tyl;- el'; trl,
      typed_body E L I C (p +ₗ #1 ◁ &shr{κ} ty +:: T') e tr) -∗
    typed_body E L I C T (case: !p of el) (trx ∘ (λ post '((l, (s, pad)) -:: cl),
      let 'xinj i a := to_xsum s in (trl -!! i) post ((cloc_take (cloc_skip l 1) (ty_size (tyl +!! i)), a) -:: cl))).
  Proof.
    iIntros (???) "el". iApply typed_body_tctx_incl; [done|]. via_tr_impl.
    { iApply (type_case_shr _ (pbyidx (λ i, inr (trl -!! i))));
        [apply tctx_incl_refl|done|].
      rewrite !big_sepHL_2_big_sepN. iApply (big_sepN_impl with "el").
      iIntros "!>" (?) "?". by rewrite pbyidx_plookup. }
    move=> ?[[l [s pad]] ?]/=. case (to_xsum s)=>/= ??. by rewrite pbyidx_plookup.
  Qed.

  (** * Unique References *)

  (** Unwrapping a unique borrow of a sum to a unique borrow of its variant. This splits
      the points-to of the payload, so it needs to run the lazy update of the payload,
      and hence a later credit. It is therefore not a [tctx_incl], but is done during the
      step of [type_case_uniq]. *)
  Lemma typed_body_unwrap_uniq_xsum {𝔄l 𝔅l 𝔇} i (tyl: typel 𝔄l) κ p (T: tctx 𝔅l) e tr
      E L I (C: cctx 𝔇) :
    lctx_lft_alive E L κ →
    typed_body E L I C (p +ₗ #1 ◁ &uniq{κ} (tyl +!! i) +:: T) e tr -∗ £1 -∗
    typed_body E L I C (p ◁ &uniq{κ} (Σ! tyl) +:: T) e
      (λ post '(bor -:: bl), λ mask π, ∃a: ~~(𝔄l !!ₗ i), (uniq_bor_current bor).1 = pinj i a ∧
        ∀a': (𝔄l !!ₗ i), (uniq_bor_future bor π).1 = pinj i a' →
        ∀ (bor_inner: ~~ (uniq_borₛ (𝔄l !!ₗ i))),
          (uniq_bor_current bor_inner) = a →
          (uniq_bor_future bor_inner π) = a' →
          tr post (bor_inner -:: bl) mask π)%type.
  Proof.
    iIntros (Alv) "Body £".
    iIntros (tid [x xl] mask post iκs) "#LFT #TIME #PROPH #UNIQ #E L I C /=[p T] #Obs".
    iAssert (llctx_interp L &&{↑NllftG}&&> llctx_interp L)%I as "#GL". { iApply guards_refl. }
    iMod (lctx_lft_alive_get_guards _ _ _ _ _ Alv with "GL E L") as "[L #GuardsK]". { solve_ndisj. }
    
    iDestruct "p" as (val d Ev) "[#⧖ [Own %Phys]]".
    iMod (proph_obs_sat with "PROPH Obs") as (πSat) "%X". { solve_ndisj. }
    destruct x as [[[[[l [x0 pad]] ξi] d'] g'] idx].
          
    destruct X as [x1 [PinjEq X]]. simpl in PinjEq. subst x0.
    
    iDestruct "Own" as "[#Incl [%Ineqs [UniqBody #PtBase]]]".
    iDestruct (guards_transitive with "GL GuardsK") as "HalfGuardsK".
    iDestruct "UniqBody" as (κp γo) "(#Inclp & (Gho & ξTok) & £2 & #ξBor)".
    have ?: Inhabited (𝔄l !!ₗ i) := populate (vπ x1 inhabitant).
    iMod (ghost_var_alloc (lstate_triv x1)) as (γ1) "[Gh1 Gh1']".
    iMod (proph_loan_intro (uniq_cell_tyi x1) ⊤ (uniq_cell x1 d' g' γ1) with "PROPH UNIQ")
      as (ζi) "Loan"; [solve_ndisj|].
    set ξ := uniq_prvar (𝔄:=Σ! 𝔄l) (pinj i x1, pad) ξi.
    set ζ := uniq_prvar x1 ζi.
    (* Only the first component of the old controller matters. *)
    set fπ := λ (c: uniq_cellₛ (𝔄l !!ₗ i)),
      ((((pinj i c.1, pad), (1%positive, (1%positive, 1%positive)))) : uniq_cellₛ (Σ! 𝔄l)).
    have Hinj: Inj (=) (=) (λ a: (𝔄l !!ₗ i), ((pinj i a, pad) : (Σ! 𝔄l)%ST)).
    { intros ?? [=Heq]. by apply pinj_Inj in Heq. }
    destruct l as [l cells].
    iMod (proph_idx_bor_gen_map ⊤ κ ξ (uniq_cell (𝔄:=Σ! 𝔄l) (pinj i x1, pad) d' g' γo) idx
      (uniq_gbody κp (Σ! tyl) tid (l, cells)) ζ (uniq_cell x1 d' g' γ1)
      (uniq_gbody κ (tyl +!! i) tid (cloc_take (cloc_skip (l, cells) 1) (ty_size (tyl +!! i))))
      fπ (llctx_interp L)
      with "LFT PROPH UNIQ HalfGuardsK [£ Gho Gh1'] L Loan ξTok ξBor") as "(#Obs' & Bor & L)";
      [solve_ndisj| |].
    { iIntros (G' wπ ?) "#G'κ G' Body".
      iMod (uniq_gbody_triv_open with "Gho Body") as "(_ & Gho & Gho' & Payload)".
      iMod (uniq_payload_force with "[] G' £ Payload") as "($ & #⧖1 & Gho1 & Pt1)";
        [rewrite /lazyE; solve_ndisj| |].
      { iApply (guards_transitive with "G'κ Incl"). }
      rewrite split_pt_xsum_cells''. iDestruct "Pt1" as "(Pt1 & Pt2 & Pt3)".
      iModIntro. iExists (vπ (uniq_cell x1 d' g' γ1)). iSplitL "Gho1 Pt2 Gh1'".
      { iApply (uniq_gbody_triv_close with "Gh1'"); [done|].
        iApply uniq_payload_intro_later. iNext. iFrame "⧖1".
        unfold xsum_ty, ty_gho_own. rewrite to_xsum_pinj. iFrame. }
      (* The old body, once the new borrow has ended: blocked at [κ], and rebuilt from
         the settled contents of the new borrow. *)
      iIntros (c1 w1) "Pc1 Q1".
      set sO := lstate (PatBlocked κ)
        (inl (PlaceProph (𝔄:=Σ! 𝔄l) (pinj i x1, pad) (λ π, (pinj i (π ζ).1, pad)))).
      iMod (ghost_var_update_halves sO with "Gho Gho'") as "[Gho _]".
      iModIntro. iNext. iExists (uniq_cell (𝔄:=Σ! 𝔄l) (pinj i x1, pad) d' g' γo).
      rewrite /uniq_gbody cpd_body_cell.
      iExists (PatBlocked κ), (inl (PlaceProph (𝔄:=Σ! 𝔄l) (pinj i x1, pad) (λ π, (pinj i (π ζ).1, pad)))).
      iFrame "Gho". iSplit; [iApply pat_ok_blocked; iApply "Inclp"|].
      iSplit; [iPureIntro; intros π; by rewrite prfn_den_inl|].
      iApply guarded_upd_intro. iModIntro. iFrame "⧖1".
      rewrite leaf_node_inl /leaf_owned /blocked_owned. iIntros "#†κ". iModIntro.
      iDestruct (uniq_lender_settle with "LFT PROPH †κ [Pc1 Q1]") as "S1".
      { iExists c1, w1. iFrame. }
      iApply (guarded_upd_weaken with "[]"); [iApply lft_intersect_tyl_lfts_lookup_incl|].
      iApply (guarded_upd_mono with "[Pt1 Pt3] S1").
      iIntros "(%y & %d1 & %g1 & Eq & #⧖2 & Gho1 & Pt2)". iModIntro.
      iExists (pinj i y, pad), d1, g1. iFrame "⧖2".
      iSplitL "Eq".
      { rewrite /place_rfn_rel. iNext.
        iDestruct (proph_eqz_constr (λ a: (𝔄l !!ₗ i), ((pinj i a, pad) : (Σ! 𝔄l)%ST)) with "Eq") as "Eq".
        iApply (proph_eqz_eq with "Eq"); [done|]. fun_ext=>π /=. by rewrite psum_map1_pinj. }
      rewrite /ofty_owned /=. iSplitR "Gho1".
      { rewrite split_pt_xsum_cells''. iFrame. }
      unfold xsum_ty, ty_gho_own. rewrite to_xsum_pinj. iFrame "Gho1". }
    iCombine "Obs Obs'" as "#Obs2".
    iDestruct "Bor" as (ζidx) "[ζTok #Bor]".

    iAssert (@[κ] &&{ ↑NllftG; d + 1 }&&> (_))%I as "PtBaseExp".
    { rewrite split_pt_xsum_cells'. iFrame "PtBase". }
    iDestruct (guards_weaken_rhs_sep_l with "PtBaseExp") as "PtBase1".
    iDestruct (guards_weaken_rhs_sep_r with "PtBaseExp") as "PtBasex".
    iDestruct (guards_weaken_rhs_sep_l with "PtBasex") as "PtBase2".

    inversion Phys. subst val.
    iApply ("Body" $! tid
      ((cloc_take (cloc_skip (l,cells) 1) (ty_size (tyl +!! i)), x1, ζi, d', g', ζidx) -:: xl)
      with "LFT TIME PROPH UNIQ E L I C [ζTok Gh1 £2 T] []").
    { iFrame "T".
         unfold tctx_elt_interp. iExists (#(l +ₗ 1)), d.
         iSplit. { iPureIntro. simpl. rewrite Ev. trivial. }
         iSplit. { iApply (persistent_time_receipt_mono with "⧖"). lia. }
         iSplit; last by done.
         iSplit. { iApply (guards_transitive with "Incl []").
           iApply lft_intersect_tyl_lfts_lookup_incl. }
         iSplit. { iPureIntro. lia. }
         iSplitL "ζTok Gh1 £2". { iExists κ, γ1. iFrame "∗#". iApply guards_refl. }
         iFrame "PtBase2".
    }
    iApply proph_obs_impl; [|done]=>/= π.
    intros [[x2 [Heq Ha]] Hb]. apply pinj_Inj in Heq. subst x2.
    apply (Ha ((π ζ).1)); trivial.
     + simpl. unfold uniq_bor_future. simpl. rewrite Hb. trivial.
  Qed.

  (** Reading the discriminant of a unique borrow of a sum. Each branch gets a later
      credit (e.g. to unwrap the borrow with [typed_body_unwrap_uniq_xsum]). *)
  Lemma type_case_uniq_outer_cred {𝔄l 𝔅l ℭl 𝔇} (tyl: typel 𝔄l) trl (T: tctx 𝔅l)
      (T': tctx ℭl) κ p el el' trx E L I (C: cctx 𝔇) :
    IntoPlistc el el' →
    tctx_extract_ctx E L +[p ◁ &uniq{κ} (Σ! tyl)] T T' trx → lctx_lft_alive E L κ →
    ([∗ hlist] ty;- e; tr ∈ tyl;- el'; trl,
      £1 -∗ typed_body E L I C (p ◁ &uniq{κ} (Σ! tyl) +:: T') e tr) -∗
    typed_body E L I C T (case: !p of el)
      (trx ∘ (λ post '(bor -:: cl), let 'xinj i _ := to_xsum (uniq_bor_current bor).1 in
        (trl -!! i) post (bor -:: cl)))%type.
  Proof.
    move=> ->. iIntros (? Alv) "el". iApply typed_body_tctx_incl; [done|].
    iIntros (tid [s ?] mask post iκs) "#LFT #TIME PROPH UNIQ #E L I C /=[p T] #?".
    destruct s as [[[[[l [x pad]] ξi] d'] g'] idx].
    replace x with (@of_xsum _ (~~) (𝔄l) (to_xsum x)); last by rewrite semi_iso'; trivial.
    refine (match (to_xsum x) with | xinj i x0 => _ end).
    wp_apply (wp_hasty with "p").
    iIntros (v d) "%Hpath #⧖ [gho %phys]". inversion phys. subst v.
    iDestruct "gho" as "[#Incl [%Hle [uniq #pt]]]".
    destruct d as [|dx]; first by lia.
    iDestruct (Alv with "L E") as "#LguardsK".
    wp_bind (!(LitV l.1))%E.
    iApply (wp_persistent_time_receipt with "TIME ⧖"). { set_solver. } iIntros "H£ ⧖'".
    iDestruct (lc_weaken (_ + 1 + 1)%nat with "H£") as "[[£1 £o] £b]"; last first.
    {
    iMod (llctx_interp_make_guarded with "L") as (γ) "[H1 [H2 [#Ghalf #Halfback]]]".
    { solve_ndisj. }
    iDestruct (guards_transitive with "Ghalf LguardsK") as "#HguardsK".
    (* Open the borrow and run the lazy update of the payload; the points-to is put in
       the guarding proposition for the read of the discriminant. *)
    iMod (uniq_body_acc_keep (Σ! tyl) with "LFT HguardsK Incl £o uniq H1") as "(_ & Gho & Pt & Close)".
    { rewrite /lazyE. solve_ndisj. }
    iAssert ((fractional.half γ ∗ l #↦!∗ ty_phys (Σ! tyl) (of_xsum (xinj i x0), pad) tid)
      &&{↑NllftG; S dx + 1}&&>
        (l.1 ↦[^ l.2]!∗ ty_phys (Σ! tyl) (of_xsum (xinj i x0), pad) tid))%I as "#Gpt".
    { iApply guard_cloc_combine_fancy.
      - iApply guards_weaken_lhs_sep_l. iApply (guards_transitive_right with "HguardsK pt").
      - leaf_goal laters to 0. { lia. } iApply guards_weaken_sep_r. }
    iEval (rewrite (split_pt_xsum_cells i)) in "Gpt".
    iDestruct (guards_weaken_rhs_sep_l with "Gpt") as "#Gdiscriminant".
    iApply (wp_read_na_guarded_cells_singleton with "[H2 Pt £1]"); first by solve_ndisj.
    { iFrame "Gdiscriminant". iFrame. }
    iNext. iIntros "[H2 Pt]".
    iDestruct ("Close" with "[Gho Pt]") as "Close". { iNext. iFrame. }
    iMod (fupd_mask_mono with "Close") as "[uniq H1]"; [solve_ndisj|].
    iDestruct ("Halfback" with "H1 H2") as "L".
    iMod (fupd_mask_mono with "L") as "L"; [solve_ndisj|].
    wp_case. { split; [lia|]. by rewrite Nat2Z.id -vlookup_lookup plistc_to_vec_lookup. }
    iDestruct (big_sepHL_2_lookup with "el") as "el".
    iSpecialize ("el" with "£b").
    iApply ("el" $! _ ((_) -:: _) with "LFT TIME PROPH UNIQ E L I C [-] []"); last first.
    { iApply proph_obs_impl; [|done]=>/= ?. by rewrite to_xsum_pinj. }
    iFrame "T". iExists _, _. iSplit; [done|]. iFrame "⧖".
    iFrame. iFrame "pt". iSplit; last by done.
    iSplit; first by iFrame "Incl". done.
    }
    unfold advance_credits. lia.
  Qed.

  Lemma type_case_uniq_outer {𝔄l 𝔅l ℭl 𝔇} (tyl: typel 𝔄l) trl (T: tctx 𝔅l)
      (T': tctx ℭl) κ p el el' trx E L I (C: cctx 𝔇) :
    IntoPlistc el el' →
    tctx_extract_ctx E L +[p ◁ &uniq{κ} (Σ! tyl)] T T' trx → lctx_lft_alive E L κ →
    ([∗ hlist] ty;- e; tr ∈ tyl;- el'; trl,
      typed_body E L I C (p ◁ &uniq{κ} (Σ! tyl) +:: T') e tr) -∗
    typed_body E L I C T (case: !p of el)
      (trx ∘ (λ post '(bor -:: cl), let 'xinj i _ := to_xsum (uniq_bor_current bor).1 in
        (trl -!! i) post (bor -:: cl)))%type.
  Proof.
    iIntros (???) "el". iApply type_case_uniq_outer_cred; [done..|].
    rewrite !big_sepHL_2_big_sepN. iApply (big_sepN_impl with "el").
    iIntros "!>" (i) "H _". iExact "H".
  Qed.

  Lemma type_case_uniq {𝔄l 𝔅l ℭl 𝔇} (tyl: typel 𝔄l) trl (T: tctx 𝔅l)
      (T': tctx ℭl) κ p el el' trx E L I (C: cctx 𝔇) :
    IntoPlistc el el' →
    tctx_extract_ctx E L +[p ◁ &uniq{κ} (Σ! tyl)] T T' trx → lctx_lft_alive E L κ →
    ([∗ hlist] ty;- e; tr ∈ tyl;- el'; trl, match tr with
      | inl otr => typed_body E L I C (p ◁ &uniq{κ} (Σ! tyl) +:: T') e otr
      | inr itr => typed_body E L I C (p +ₗ #1 ◁ &uniq{κ} ty +:: T') e itr
      end) -∗
    typed_body E L I C T (case: !p of el) (trx ∘ (λ post '(bor -:: cl), λ mask π,
      let 'xinj i a := to_xsum (uniq_bor_current bor).1 in match trl -!! i with
        | inl otr => otr post (bor -:: cl) mask π
        | inr itr => ∀a': 𝔄l !!ₗ i, (uniq_bor_future bor π).1 = pinj i a' →
          ∀ (bor_inner: ~~ (uniq_borₛ (𝔄l !!ₗ i))),
          (uniq_bor_current bor_inner) = a →
          (uniq_bor_future bor_inner π) = a' →
          itr post (bor_inner -:: cl) mask π
        end))%type.
  Proof.
    iIntros (???) "el". iApply typed_body_tctx_incl; [done|]. via_tr_impl.
    { iApply (type_case_uniq_outer_cred _ (pbyidx (λ i post '(bor -:: cl), λ mask π,
        match trl -!! i with inl otr => otr post (bor -:: cl) mask π | inr itr => _ end
        : Prop))); [apply tctx_incl_refl|done|].
      rewrite !big_sepHL_2_big_sepN. iApply (big_sepN_impl with "el").
      iIntros "!>" (i) "Hb £". rewrite pbyidx_plookup.
      case (trl -!! i)=> ?; [by via_tr_impl; [done|]=> ?[[??]?]?|]. via_tr_impl.
      { iApply (typed_body_unwrap_uniq_xsum with "Hb £"). done. }
      move=>/= ?[[??]?]??. exact id. }
    move=> ?[bor ?]/=. case (to_xsum (uniq_bor_current bor).1) as [i ?] eqn: Eq. rewrite pbyidx_plookup.
    move: (trl -!! i). case; [done|]=>/= ??. eexists _. split; [|done].
    move: Eq=> /(f_equal of_xsum)=>/= <-. by rewrite semi_iso'.
  Qed.

  Lemma type_case_uniq_inner {𝔄l 𝔅l ℭl 𝔇} (tyl: typel 𝔄l) trl (T: tctx 𝔅l)
      (T': tctx ℭl) κ p el el' trx E L I (C: cctx 𝔇) :
    IntoPlistc el el' →
    tctx_extract_ctx E L +[p ◁ &uniq{κ} (Σ! tyl)] T T' trx → lctx_lft_alive E L κ →
    ([∗ hlist] ty;- e; tr ∈ tyl;- el'; trl,
      typed_body E L I C (p +ₗ #1 ◁ &uniq{κ} ty +:: T') e tr) -∗
    typed_body E L I C T (case: !p of el) (trx ∘ (λ post '(bor -:: cl), λ mask π,
      let 'xinj i a := to_xsum (uniq_bor_current bor).1 in
      ∀a': 𝔄l !!ₗ i, (uniq_bor_future bor π).1 = pinj i a' →
        ∀ (bor_inner: ~~ (uniq_borₛ (𝔄l !!ₗ i))),
        (uniq_bor_current bor_inner) = a →
        (uniq_bor_future bor_inner π) = a' →
        (trl -!! i) post (bor_inner -:: cl) mask π))%type.
  Proof.
    iIntros (???) "el". iApply typed_body_tctx_incl; [done|]. via_tr_impl.
    { iApply (type_case_uniq _ (pbyidx (λ i, inr (trl -!! i))));
        [apply tctx_incl_refl|done|].
      rewrite !big_sepHL_2_big_sepN. iApply (big_sepN_impl with "el").
      iIntros "!>" (?) "?". by rewrite pbyidx_plookup. }
    move=> ?[bor ?]/=. case (to_xsum (uniq_bor_current bor).1)=>/= ??. by rewrite pbyidx_plookup.
  Qed.

  (** * Write *)

  Lemma type_sum_assign_instr {𝔄 𝔄' 𝔅 𝔅l} (tyl: typel 𝔅l) (i: fin _)
      (ty: type 𝔄) (tyb: type 𝔅) (ty': type 𝔄')  p q gt st Φ E L I :
    typed_write E L ty tyb ty' (Σ! tyl) gt st → resolve' E L tyb Φ →
    typed_instr E L I +[p ◁ ty; q ◁ tyl +!! i] (p <-{Σ i} q) (λ _, +[p ◁ ty'])
      (λ post '-[a; b], λ mask π, ∀ pad,
        Φ (gt a) π (∀ z, st a (pinj i b, pad) z → post -[z] mask π)).
  Proof.
    iIntros ([Eq Wrt] Rslv ???? (x & y &[]))
      "#LFT #TIME PROPH #UNIQ #E L I (p & q & _) Obs".
    iMod (llctx_interp_make_guarded with "L") as (γ) "[H1 [H2 [#Ghalf #Halfback]]]". { solve_ndisj. }
    iDestruct (closed_hasty with "p") as %C1. iDestruct (closed_hasty with "q") as %C2.
    wp_apply (wp_hasty with "p"). iIntros (v d Heq) "#⧖ ty".
    
    iMod (Wrt with "LFT UNIQ E Ghalf H1 ty") as (l d' H Heqv ->) "[Old [H [#Hguards Toty']]]". inversion Heqv. subst v.
    unfold ty_own.
    destruct l as [l cells].
    
    wp_bind (LitV (l, cells).1 <- #i)%E.
    iApply (wp_persistent_time_receipt with "TIME ⧖"); [solve_ndisj|].
    iIntros "H£ #⧖S".
    iDestruct (lc_weaken (_ + _)%nat with "H£") as "[£0 £1]"; first last.
    {
    iMod (lc_fupd_elim_later with "£0 Old") as "Old".
    iMod (guarded_upd_run with "Ghalf H2 Old") as "[H2 (%vl & ↦ & A)]"; [solve_ndisj|].
    iDestruct "A" as "[tyb_ghos %tyb_phys]".
    assert (length vl = ty_size tyb) as Sz. { rewrite <- tyb_phys. apply ty_size_eq. }
    destruct vl as [|v vl]. { rewrite Eq in Sz. done. }
    destruct cells as [|cells0 cells]. { done. }
    
    rewrite heap_mapsto_cloc_fancy_vec_cons.
    iDestruct "↦" as "[↦1 ↦2]".
    rewrite <- heap_complete_mapsto_fancy_singleton.
    iMod (mapsto_vec_untether_singleton _ _ _ ∅ with "↦1") as (v₀ l₀ c₀) "[%Hl [↦1 Retether]]".
    inversion Hl. subst l₀ c₀.
    
    iApply (wp_write_na_guarded with "[H ↦1 £1]"). { solve_ndisj. }
      { rewrite heap_mapsto_cloc_emp_cons.
        iDestruct (guards_weaken_rhs_sep_l with "Hguards") as "Hguards2". iFrame "Hguards2".
        iFrame "H". iFrame "↦1". iFrame "£1". }
    iModIntro. iIntros "[↦1 H]".
    
    wp_let.
    
    wp_bind p. iApply wp_wand; [by iApply wp_eval_path|]. iIntros (?->).
    wp_op.
    wp_bind q. iApply (wp_hasty with "q"). iIntros (vb db ?) "#⧖' tyb'".
    
    iApply wp_fupd.
    iCombine "⧖ ⧖'" as "⧖max".
    iApply (wp_persistent_time_receipt with "TIME ⧖max"); [solve_ndisj|].
    iIntros "H£ #⧖S2".
    iDestruct (lc_weaken (_ + _ + _ + _)%nat with "H£") as "[[[£1 £2] £3] £4]"; first last.
    {
    
    iDestruct (Rslv _ (⊤ ∖ (⊤ ∖ ↑Nllft ∖ ↑prophN ∖ ↑timeN ∖ ↑uniqN)) with "LFT PROPH UNIQ TIME E Ghalf H2 tyb_ghos") as "ToObs"; [set_solver|].
    iDestruct "tyb'" as "[tyb'_gho %tyb'_phys]".
    assert (ty_size (tyl +!! i) = 1) as Sz'. {
      rewrite <- (ty_size_eq _ y tid). rewrite tyb'_phys. trivial.
    }
    destruct vl as [|v2 vl]. { exfalso. clear Wrt.
      have Hge := max_hlist_with_ge (λ _, ty_size) tyl i. 
      assert (ty_size tyb = S (max_hlist_with (λ X : syn_type, ty_size) tyl)) as X.
        { apply Eq. } simpl in Sz. rewrite <- Sz in X. 
        assert ((max_hlist_with (λ X : syn_type, ty_size) tyl) = 0) as X0 by lia.
        rewrite X0 in Hge. rewrite Sz' in Hge. lia.
    }
    destruct cells as [|cells2 cells]. { done. }
    
    iMod (lc_fupd_elim_later with "£1 ToObs") as "ToObs".
    iMod (fupd_mask_mono with "ToObs") as "ToObs". { solve_ndisj. }
    iDestruct (lc_step_fupdN_elim_later with "£2 ToObs") as "ToObs".
    iMod (fupd_mask_mono with "ToObs") as "ToObs". { solve_ndisj. }
    iMod (fupd_mask_mono with "ToObs") as "ToObs". { solve_ndisj. }
    iDestruct "ToObs" as "[Obs' H1]".
    
    rewrite heap_mapsto_cloc_fancy_vec_cons.
    iDestruct "↦2" as "[↦2 ↦3]".
    rewrite <- heap_complete_mapsto_fancy_singleton.
    iMod (mapsto_vec_untether_singleton _ _ _ ∅ with "↦2") as (v₁ l₁ c₁) "[%Hl₁ [↦2 Retether₁]]".
    inversion Hl₁. subst l₁ c₁.
       
    iApply (wp_write_na_guarded with "[H ↦2 £3]"). { solve_ndisj. }
      { rewrite heap_mapsto_cloc_emp_cons. rewrite heap_mapsto_cloc_emp_cons.
        iDestruct (guards_weaken_rhs_sep_r with "Hguards") as "Hguards2".
        iDestruct (guards_weaken_rhs_sep_l with "Hguards2") as "Hguards3".
        iFrame "Hguards3". iFrame "H". iFrame "↦2". iFrame "£3". }
    iModIntro. iIntros "[↦2 H]".
    
    iMod (mapsto_vec_untether _ _ _ ∅ with "↦3") as (vlconcrete) "[↦3 [%Hlen3 Retether3]]".
    
    iCombine "Obs Obs'" as "Obs".
    iMod ("Toty'" $! (pinj i y, vlconcrete) with "[↦1 ↦2 ↦3 tyb'_gho] ⧖S2 £4 H") as (z) "[H2 [%Hz [ty' ty'phys]]]".
    { iExists (FVal #i :: FVal vb :: fmap FVal vlconcrete). 
      rewrite heap_mapsto_cloc_fancy_vec_cons.
      rewrite heap_mapsto_cloc_fancy_vec_cons. iFrame. iNext.
      unfold xsum_ty, ty_gho_own, ty_phys. simpl. rewrite to_xsum_pinj.
      iDestruct (ty_gho_own_depth_mono with "tyb'_gho") as "[$ _]". { lia. } { lia. }
      iPureIntro. 
      eassert (FVal #i :: _ = [FVal #i] ++ _) as ->. { done. } rewrite List.app_assoc.
      rewrite pad_app.
       - rewrite <- List.app_assoc. simpl.  f_equal.
         eassert (FVal vb :: _ = [FVal vb] ++ _) as ->. { done. } rewrite <- tyb'_phys.
         f_equal. rewrite <- pad_eq_padding_to_vec. apply pad_length'.
         rewrite length_fmap. rewrite Hlen3.
         rewrite Eq in Sz. rewrite ty_size_eq. rewrite Sz'.
         assert (∀ x y, S (S x) = S y → y - 1 = x) as Hlia by lia. apply Hlia. apply Sz.
       - simpl. rewrite ty_size_eq.
         have Hge := max_hlist_with_ge (λ _, ty_size) tyl i.
         assert (∀ x y, x ≤ y → S x ≤ S y) as Hlia by lia. apply Hlia. apply Hge.
    }
    iDestruct ("Halfback" with "H1 H2") as "L". iMod (fupd_mask_mono with "L") as "L". { solve_ndisj. }
    
    iExists -[z]. iFrame "L I". iSplitR "Obs".
    - rewrite right_id tctx_hasty_val'; [|done]. iExists (S (S d' `max` db)). iFrame "#".
      iFrame. iModIntro. iDestruct (ty_gho_own_depth_mono with "ty'") as "[$ _]". { lia. } { lia. }
    - iApply proph_obs_impl; [|done]=>/= π [Ha Imp].
      generalize Hz. generalize z. apply Imp. apply Ha.
    }
    unfold advance_credits. nia.
    }
    unfold advance_credits. lia.
  Qed.

  Lemma type_sum_assign {𝔄 𝔄' 𝔅 𝔅l ℭl 𝔇l 𝔈} (tyl: typel 𝔅l) (i: fin _)
      (k: Z) (ty: type 𝔄) (tyb: type 𝔅) (ty': type 𝔄')
      (T: tctx ℭl) (T': tctx 𝔇l) p q gt st Φ tr trx E L I (C: cctx 𝔈) e :
    Closed [] e → k = i → tctx_extract_ctx E L +[p ◁ ty; q ◁ tyl +!! i] T T' trx →
    typed_write E L ty tyb ty' (Σ! tyl) gt st → resolve' E L tyb Φ →
    typed_body E L I C (p ◁ ty' +:: T') e tr -∗
    typed_body E L I C T (p <-{Σ k} q;; e) (trx ∘ (λ post '(a -:: b' -:: dl), λ mask π, forall pad,
      Φ (gt a) π (forall z, st a (pinj i b', pad) z → tr post (z -:: dl) mask π))).
  Proof.
    iIntros (?->???) "e". iApply typed_body_tctx_incl; [done|].
    iApply type_seq; [by eapply type_sum_assign_instr|apply tctx_incl_refl| |done].
    by move=> ?[?[??]]/=.
  Qed.

  Lemma type_sum_unit_instr {𝔄 𝔄' 𝔅 𝔅l} (tyl: typel 𝔅l) (i: fin _)
      (ty: type 𝔄) (tyb: type 𝔅) (ty': type 𝔄') f p gt st Φ E L I :
    typed_write E L ty tyb ty' (Σ! tyl) gt st → resolve' E L tyb Φ →
    subtype E L () (tyl +!! i) f →
    typed_instr E L I +[p ◁ ty] (p <-{Σ i} ()) (λ _, +[p ◁ ty'])
      (λ post '-[a], λ mask π, ∀ pad,
        Φ (gt a) π (∀ z, st a (pinj i (f ~~$ₛ ()), pad) z → (post -[z] mask π))).
  Proof.
    iIntros ([Eq Wrt] Rslv Subtype ???? (x & []))
      "#LFT #TIME PROPH #UNIQ #E L I (p & _) Obs".
    iDestruct (Subtype with "L E") as "#(%Ssz & SIncl & Sgho & Sghopers & %Sphys & _)".
    iMod (llctx_interp_make_guarded with "L") as (γ) "[H1 [H2 [#Ghalf #Halfback]]]". { solve_ndisj. }
    iDestruct (closed_hasty with "p") as %C1.
    wp_apply (wp_hasty with "p"). iIntros (v d Heq) "#⧖ ty".
    
    iMod (Wrt with "LFT UNIQ E Ghalf H1 ty") as (l d' H Heqv ->) "[Old [H [#Hguards Toty']]]". inversion Heqv. subst v.
    unfold ty_own.
    destruct l as [l cells].
    
    iApply wp_fupd.
    wp_bind (LitV (l, cells).1 <- #i)%E.
    iApply (wp_persistent_time_receipt with "TIME ⧖"); [solve_ndisj|].
    iIntros "H£ #⧖S".
    iDestruct (lc_weaken (_ + _ + _ + _ + _)%nat with "H£") as "[[[[£0 £1] £2] £3] £4]"; first last.
    {
    iMod (lc_fupd_elim_later with "£0 Old") as "Old".
    iMod (guarded_upd_run with "Ghalf H2 Old") as "[H2 (%vl & ↦ & A)]"; [solve_ndisj|].
    iDestruct "A" as "[tyb_ghos %tyb_phys]".
    assert (length vl = ty_size tyb) as Sz. { rewrite <- tyb_phys. apply ty_size_eq. }
    destruct vl as [|v vl]. { rewrite Eq in Sz. done. }
    destruct cells as [|cells0 cells]. { done. }
    
    rewrite heap_mapsto_cloc_fancy_vec_cons.
    iDestruct "↦" as "[↦1 ↦2]".
    rewrite <- heap_complete_mapsto_fancy_singleton.
    iMod (mapsto_vec_untether_singleton _ _ _ ∅ with "↦1") as (v₀ l₀ c₀) "[%Hl [↦1 Retether]]".
    inversion Hl. subst l₀ c₀.
    
    iApply (wp_write_na_guarded with "[H ↦1 £1]"). { solve_ndisj. }
      { rewrite heap_mapsto_cloc_emp_cons.
        iDestruct (guards_weaken_rhs_sep_l with "Hguards") as "Hguards2". iFrame "Hguards2".
        iFrame "H". iFrame "↦1". iFrame "£1". }
    iModIntro. iIntros "[↦1 H]".
    
    wp_let. iApply wp_fupd. wp_seq.
    
    iDestruct (Rslv _ (⊤ ∖ (⊤ ∖ ↑Nllft ∖ ↑prophN ∖ ↑timeN ∖ ↑uniqN)) with "LFT PROPH UNIQ TIME E Ghalf H2 tyb_ghos") as "ToObs"; [set_solver|].
    assert (ty_size (tyl +!! i) = 0) as Sz'. {
      rewrite <- Ssz.  done.
    }
    
    iMod (lc_fupd_elim_later with "£2 ToObs") as "ToObs".
    iMod (fupd_mask_mono with "ToObs") as "ToObs". { solve_ndisj. }
    iDestruct (lc_step_fupdN_elim_later with "£3 ToObs") as "ToObs".
    iMod (fupd_mask_mono with "ToObs") as "ToObs". { solve_ndisj. }
    iMod (fupd_mask_mono with "ToObs") as "ToObs". { solve_ndisj. }
    iDestruct "ToObs" as "[Obs' H1]".
    
    iMod (mapsto_vec_untether _ _ _ ∅ with "↦2") as (vlconcrete) "[↦2 [%Hlen2 Retether2]]".
    
    iCombine "Obs Obs'" as "Obs".
    iMod ("Toty'" $! (pinj i (f ~~$ₛ ()), vlconcrete) with "[↦1 ↦2] ⧖S £4 H") as (z) "[H2 [%Hz [ty' ty'phys]]]".
    { iExists (FVal #i :: fmap FVal vlconcrete). 
      rewrite heap_mapsto_cloc_fancy_vec_cons.
      iFrame. iNext.
      unfold xsum_ty, ty_gho_own, ty_phys. simpl. rewrite to_xsum_pinj.
      iDestruct ("Sgho" with "[]") as "[$ _]"; first done.
      iPureIntro. 
      eassert (FVal #i :: _ = [FVal #i] ++ _) as ->. { done. } rewrite List.app_assoc.
      rewrite pad_app.
       - rewrite <- List.app_assoc. simpl. f_equal. rewrite <- Sphys. simpl.
         rewrite <- pad_eq_padding_to_vec. apply pad_length'.
         rewrite length_fmap. rewrite Hlen2.
         rewrite Eq in Sz.
         assert (∀ x y, S x = S y → y - 0 = x) as Hlia by lia. apply Hlia. apply Sz.
       - simpl. rewrite ty_size_eq.
         have Hge := max_hlist_with_ge (λ _, ty_size) tyl i.
         assert (∀ x y, x ≤ y → S x ≤ S y) as Hlia by lia. apply Hlia. apply Hge.
    }
    iDestruct ("Halfback" with "H1 H2") as "L". iMod (fupd_mask_mono with "L") as "L". { solve_ndisj. }
    
    iModIntro. iModIntro.
    iExists -[z]. iFrame "L I". iSplitR "Obs".
    - rewrite right_id tctx_hasty_val'; [|done]. iExists (S (S d')). iFrame "#".
      iFrame. iDestruct (ty_gho_own_depth_mono with "ty'") as "[$ _]". { lia. } { lia. }
    - iApply proph_obs_impl; [|done]=>/= π [Ha Imp].
      generalize Hz. generalize z. apply Imp. apply Ha.
    }
    unfold advance_credits. nia.
  Qed.

  Lemma type_sum_unit {𝔄 𝔄' 𝔅 𝔅l ℭl 𝔇l 𝔈} (tyl: typel 𝔅l) (i: fin _) (k: Z)
      (ty: type 𝔄) (tyb: type 𝔅) (ty': type 𝔄') (T: tctx ℭl) (T': tctx 𝔇l)
      f trx tr p gt st e Φ E L I (C: cctx 𝔈) :
    Closed [] e → k = i → tctx_extract_ctx E L +[p ◁ ty] T T' trx →
    typed_write E L ty tyb ty' (Σ! tyl) gt st → resolve' E L tyb Φ →
    subtype E L () (tyl +!! i) f →
    typed_body E L I C (p ◁ ty' +:: T') e tr -∗
    typed_body E L I C T (p <-{Σ k} ();; e) (trx ∘
      (λ post '(a -:: dl), λ mask π, forall pad,
        Φ (gt a) π (forall z, st a (pinj i (f ~~$ₛ ()), pad) z → tr post (z -:: dl) mask π))).
  Proof.
    iIntros (?->????) "e". iApply typed_body_tctx_incl; [done|].
    iApply type_seq; [by eapply type_sum_unit_instr|by apply tctx_incl_refl| |done].
    by move=> ?[??]/=.
  Qed.

  Lemma type_sum_memcpy_instr {𝔄 𝔄' 𝔅 𝔅' ℭ ℭl} (tyl: typel ℭl) (i: fin _)
      (tyw: type 𝔄) (tyw': type 𝔄') (tyr: type 𝔅) (tyr': type 𝔅')
      (tyb: type ℭ) p q gtw stw gtr str Φ E L I :
    typed_write E L tyw tyb tyw' (Σ! tyl) gtw stw → resolve' E L tyb Φ →
    typed_read E L tyr (tyl +!! i) tyr' gtr str →
    typed_instr E L I +[p ◁ tyw; q ◁ tyr]
      (p <-{(tyl +!! i).(ty_size),Σ i} !q) (λ _, +[p ◁ tyw'; q ◁ tyr'])
      (λ post '-[a; b], λ mask π, ∀ pad,
        Φ (gtw a) π (∀ zw zr,
          stw a (pinj i (gtr b), pad) zw → str b zr →
          post -[zw; zr] mask π)).
  Proof.
    iIntros ([Eq Wrt] Rslv Rd ???? (x & y &[]))
      "#LFT #TIME PROPH #UNIQ #E L I (p & q & _) Obs".
    iMod (llctx_interp_make_guarded with "L") as (γ) "[H1 [H2 [#Ghalf #Halfback]]]". { solve_ndisj. }
    iMod (fractional.frac_split_guard_in_half with "H2 Ghalf") as (γ2) "[H2 [H3 [#Ghalf2 #Halfback2]]]". { solve_ndisj. }
    
    iDestruct (closed_hasty with "p") as %C1. iDestruct (closed_hasty with "q") as %C2.
    wp_apply (wp_hasty with "p"). iIntros (v d Heq) "#⧖ ty".
    
    iMod (Wrt with "LFT UNIQ E Ghalf H1 ty") as (l d' Hw Heqv ->) "[Old (Hw & #Hwpt & Totyw)]". inversion Heqv. subst v.
    unfold ty_own.
    destruct l as [l cells].
    
    wp_bind (LitV (l, cells).1 <- #i)%E.
    iApply (wp_persistent_time_receipt with "TIME ⧖"); [solve_ndisj|].
    iIntros "H£ #⧖S".
    iDestruct (lc_weaken (_ + (_ + _))%nat with "H£") as "[£0 £1]"; first last.
    {
    iMod (lc_fupd_elim_later with "£0 Old") as "Old".
    iMod (guarded_upd_run with "Ghalf2 H2 Old") as "[H2 (%vl & ↦ & A)]"; [solve_ndisj|].
    iDestruct "A" as "[tyb_ghos %tyb_phys]".
    assert (length vl = ty_size tyb) as Sz. { rewrite <- tyb_phys. apply ty_size_eq. }
    destruct vl as [|v vl]. { rewrite Eq in Sz. done. }
    destruct cells as [|cells0 cells]. { done. }
    
    rewrite heap_mapsto_cloc_fancy_vec_cons.
    iDestruct "↦" as "[↦1 ↦2]".
    rewrite <- heap_complete_mapsto_fancy_singleton.
    iMod (mapsto_vec_untether_singleton _ _ _ ∅ with "↦1") as (v₀ l₀ c₀) "[%Hl [↦1 _Retether]]".
    inversion Hl. subst l₀ c₀.
    
    iApply (wp_write_na_guarded with "[Hw ↦1 £1]"). { solve_ndisj. }
      { rewrite heap_mapsto_cloc_emp_cons.
        iDestruct (guards_weaken_rhs_sep_l with "Hwpt") as "Hguards2". iFrame "Hguards2".
        iFrame "Hw". iFrame "↦1". iFrame "£1". }
    iModIntro. iIntros "[↦1 Hw]".
    
    wp_let.
    
    wp_bind p. iApply wp_wand; [by iApply wp_eval_path|]. iIntros (?->).
    wp_op.
    wp_bind q. iApply (wp_hasty with "q"). iIntros (vb db ?) "#⧖' tyr".
    
    iApply wp_fupd.
    iCombine "⧖ ⧖'" as "⧖max".
    iApply (wp_persistent_time_receipt with "TIME ⧖max"); [solve_ndisj|].
    iIntros "H£ #⧖S2".
    iDestruct (lc_weaken (_ + _ + _ + _ + _ + _ + _)%nat with "H£")
        as "[[[[[[£1 £2] £3] £4] £5] £6] £7]"; first last.
    {
    
    iMod (Rd with "LFT E Ghalf2 H2 tyr £1") as (? vlb_concrete vlb Hr Heqv2 Hleneq) "(Hr & #Hrpt' & Retether & _ & Own' & Totyr')".
      inversion Heqv2. subst vb.
    iDestruct "Own'" as "[tyb'_gho #>%tyb'_phys]".
    
    assert ((length vlb) = ty_size (tyl +!! i)) as Sz'. { rewrite <- tyb'_phys. apply ty_size_eq. }
    assert (length vlb ≤ length vl) as HlenLe. {
      rewrite Eq in Sz. rewrite Sz'.
      have h := max_hlist_with_ge (λ X : syn_type, ty_size) tyl i.
      assert (∀ x y z, S x = S y → z ≤ y → z ≤ x) as Hlia by lia.
      apply (Hlia _ _ _ Sz h).
    }
    
    iDestruct (Rslv _ (⊤ ∖ (⊤ ∖ ↑Nllft ∖ ↑prophN ∖ ↑timeN ∖ ↑uniqN)) with "LFT PROPH UNIQ TIME E Ghalf2 H3 tyb_ghos") as "ToObs"; [set_solver|].
    
    iMod (lc_fupd_elim_later with "£2 ToObs") as "ToObs".
    iMod (fupd_mask_mono with "ToObs") as "ToObs". { solve_ndisj. }
    iDestruct (lc_step_fupdN_elim_later with "£3 ToObs") as "ToObs".
    iMod (fupd_mask_mono with "ToObs") as "ToObs". { solve_ndisj. }
    iMod (fupd_mask_mono with "ToObs") as "ToObs". { solve_ndisj. }
    iDestruct "ToObs" as "[Obs' H1]".
    
    replace ((l +ₗ 1, cells) #↦!∗ vl)%I with ((l +ₗ 1, cells) #↦!∗ (take (length vlb) vl ++ List.skipn (length vlb) vl))%I. 2: {  f_equal. apply take_drop. }
    rewrite heap_cloc_mapsto_fancy_vec_app.
    iDestruct "↦2" as "[↦2 ↦3]".
    iMod (mapsto_vec_untether _ _ _ ∅ with "↦2") as (vl2_concrete) "[↦2 [%Hvlen2 _]]".
    iMod (mapsto_vec_untether _ _ _ ∅ with "↦3") as (vl3_concrete) "[↦3 [%Hvlen3 _]]".
    
    iApply (wp_memcpy_guarded _ (cloc_take (l +ₗ 1, cells) (length (take (length vlb) vl))) l0 vl2_concrete vlb_concrete Hw Hr _ (S (S d' `max` db)) with "TIME [$↦2 Hwpt Hr Hw £4]"). { solve_ndisj. }
    { rewrite <- Sz'. rewrite Hvlen2. rewrite length_take. lia. }
    { congruence. } { replace (S (d' + 1)) with (S d' + 1) by lia.
      iSplit. { leaf_goal laters to (S d' + 1); first by lia. 
        rewrite heap_mapsto_cloc_emp_cons. 
        rewrite (heap_cloc_mapsto_emp_vec_app _ (length vlb)).
        iDestruct (guards_weaken_rhs_sep_r with "Hwpt") as "Hguards2".
        iDestruct (guards_weaken_rhs_sep_l with "Hguards2") as "Hguards3".
        rewrite length_take. eassert (_ `min` _ = _) as ->; last by iApply "Hguards3". lia.
      }
      iSplit. { leaf_goal laters to (db + 1); first by lia. iFrame "Hrpt'". }
      iFrame. iFrame "⧖S2".
    }
       
    iModIntro. iIntros "[↦2 [Hw Hr]]".
    
    iCombine "Obs Obs'" as "Obs".
     
    leaf_open_laters "Hwpt" with "Hw" as "A". { trivial. }
    iMod (lc_fupd_elim_later with "£5 A") as "A".
    iMod (lc_fupd_elim_laterN with "£6 A") as "A". iMod "A" as "[prefix back]".
    rewrite heap_mapsto_cloc_emp_cons. 
    rewrite (heap_cloc_mapsto_emp_vec_app _ (length vlb)).
    iDestruct "prefix" as "[prefix1 [prefix2 prefix3]]".
    iDestruct ("Retether" with "[prefix2 ↦2]") as "↦2". { unfold cloc_take. iFrame.
        rewrite length_take. eassert (_ `min` _ = _) as ->; last by iApply "prefix2". lia.
    }
    iMod (fupd_mask_mono with "↦2") as "[prefix2 ↦2]". { solve_ndisj. }
    iMod ("back" with "[prefix1 prefix2 prefix3]") as "Hw". { iFrame.
        rewrite length_take. eassert (_ `min` _ = _) as ->; last by iApply "prefix2". lia.
    }
    
    iMod ("Totyw" $! (pinj i (gtr y), vl3_concrete) with "[↦1 ↦2 ↦3 tyb'_gho] ⧖S2 £7 Hw") as (z) "[H1' [%Hz tyw']]". { 
      iExists (FVal #i :: vlb ++ fmap FVal vl3_concrete).
      rewrite heap_mapsto_cloc_fancy_vec_cons.
      rewrite heap_cloc_mapsto_fancy_vec_app.
      rewrite length_take. eassert (length vlb `min` length vl = length vlb) as ->. { lia. }
      iFrame.
      unfold xsum_ty, ty_gho_own, ty_phys. simpl. rewrite to_xsum_pinj.
      iDestruct (ty_gho_own_depth_mono with "tyb'_gho") as "[$ _]". { lia. } { lia. }
      iPureIntro. 
      unfold ty_phys in tyb'_phys. rewrite tyb'_phys. rewrite pad_cons. f_equal.
      rewrite pad_app.
        - rewrite <- pad_eq_padding_to_vec. f_equal. apply pad_length'.
          rewrite length_fmap. rewrite length_drop in Hvlen3. rewrite Hvlen3. f_equal.
          rewrite Eq in Sz.
          assert (∀ x y, S x = S y → y = x) as Hlia by lia. apply (Hlia _ _ Sz).
        - rewrite Eq in Sz.
          assert (∀ x y z, x ≤ y → S y = S z → x ≤ z) as Hlia by lia.
          apply (Hlia _ _ _ HlenLe Sz).
    }
    iDestruct ("Totyr'" with "Hr") as "Totyr'".
    iMod (fupd_mask_mono with "Totyr'") as (zr) "(%Hzr & H3 & tyr')". { solve_ndisj. }
    iDestruct ("Halfback2" with "H3 H1") as "L". iMod (fupd_mask_mono with "L") as "L". { solve_ndisj. }
    iDestruct ("Halfback" with "H1' L") as "L". iMod (fupd_mask_mono with "L") as "L". { solve_ndisj. }
    iModIntro.
    iExists -[z; zr]. iFrame "L I". iSplitR "Obs".
    - rewrite right_id.
      + iSplitL "tyw'"; (rewrite tctx_hasty_val'; [|done]); iExists (S (S d' `max` db)).
        * iFrame "⧖S2". iDestruct "tyw'" as "[gho phys]". iFrame.
          iDestruct (ty_gho_own_depth_mono with "gho") as "[$ _]"; lia.
        * iFrame "⧖S2". iDestruct "tyr'" as "[gho phys]". iFrame.
          iDestruct (ty_gho_own_depth_mono with "gho") as "[$ _]"; lia.
    - iApply proph_obs_impl; [|done]=>/= ?[? Imp].
      generalize Hzr. generalize Hz. generalize zr. generalize z. apply Imp.
      trivial.
   }
   unfold advance_credits. nia.
   }
   unfold advance_credits. nia.
  Qed.

  Lemma type_sum_memcpy {𝔄 𝔄' 𝔅 𝔅' ℭ ℭl 𝔇l 𝔈l 𝔉} (tyl: typel ℭl) (i: fin _)
      (tyw: type 𝔄) (tyr: type 𝔅) (tyw': type 𝔄') (tyr': type 𝔅') (tyb: type ℭ) (k n: Z)
      (T: tctx 𝔇l) (T': tctx 𝔈l) p q gtw stw gtr str trx tr e Φ E L I (C: cctx 𝔉) :
    Closed [] e → k = i → tctx_extract_ctx E L +[p ◁ tyw; q ◁ tyr] T T' trx →
    typed_write E L tyw tyb tyw' (Σ! tyl) gtw stw → resolve' E L tyb Φ →
    n = (tyl +!! i).(ty_size) → typed_read E L tyr (tyl +!! i) tyr' gtr str →
    typed_body E L I C (p ◁ tyw' +:: q ◁ tyr' +:: T') e tr -∗
    typed_body E L I C T (p <-{n,Σ k} !q;; e)
      (trx ∘ (λ post '(a -:: b -:: el), λ mask π, forall pad,
        Φ (gtw a) π (forall zw zr,
          stw a (pinj i (gtr b), pad) zw → str b zr →
          tr post (zw -:: zr -:: el) mask π))).
  Proof.
    iIntros (?->???->?) "e". iApply typed_body_tctx_incl; [done|].
    iApply type_seq; [by eapply type_sum_memcpy_instr|by apply tctx_incl_refl| |done].
    by move=> ?[?[??]]/=.
  Qed.

  Lemma ty_outlives_E_elctx_sat_sum {𝔄l} E L (tyl: typel 𝔄l) κ :
    elctx_sat E L (tyl_outlives_E tyl κ) →
    elctx_sat E L (ty_outlives_E (Σ! tyl) κ).
  Proof.
    move=> Sat. eapply eq_ind; [done|]. clear Sat.
    rewrite /tyl_outlives_E /ty_outlives_E /=.
    induction tyl as [|???? IH]=>//=. by rewrite IH fmap_app.
  Qed.
End type_sum.

Global Hint Resolve ty_outlives_E_elctx_sat_sum : lrust_typing.
