From lrust.typing Require Export type.
From lrust.typing Require Import product.
Set Default Proof Using "Type".

Open Scope nat.

Section uninit.
  Context `{!typeG Σ}.

  Program Definition uninit n : type (uninitₛ n) := {|
    ty_size := n;
    ty_lfts := [];
    ty_E := [];
    ty_gho_own vπ _ _ _ := True;
    ty_gho_pers vπ _ _ _ := True;
    ty_phys x _ := fmap FVal (vec_to_list x);
    ty_shr := default_shr (λ vπ _ _ _, True);
  |}%I.
  Next Obligation. intros. rewrite length_fmap. rewrite length_vec_to_list. trivial. Qed.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation. by iIntros. Qed.
  Next Obligation. set_solver. Qed.
  Next Obligation. by iIntros. Qed.
  Solve All Obligations with solve_default_shr.
End uninit.

Notation "↯" := uninit : lrust_type_scope.

Section typing.
  Context `{!typeG Σ}.

  Global Instance uninit_copy n : Copy (↯ n).
  Proof.
    split; [apply _| |intros; by apply copy_shr_default]=>/= *.
    iIntros. iPureIntro. apply all_concrete_fmap_fval.
  Qed.

  Global Instance uninit_send n : Send (↯ n).
  Proof.
    intros. split.
      - intros tid tid' x x' Hsyn. unfold syn_abstract in Hsyn. subst x'. trivial.
      - iIntros. iApply step_fupdN_intro; first done. iNext.
        iExists x, 0%nat. iModIntro. iFrame. simpl.
        replace (d0 + 0)%nat with d0 by lia. iFrame "#". done.
  Qed.
  
  Global Instance uninit_sync n : Sync (↯ n).
  Proof. apply sync_default; [done|]. split => //=. Qed.

  Lemma uninit_resolve n E L : resolve E L (↯ n) (const (const True)).
  Proof. apply resolve_just. Qed.

  Notation "()" := unit0 : lrust_type_scope.
  
  Program Definition uninit0_to_unitₛ : uninitₛ 0 →ₛ Π! [] := {|
    syn_type_morphism_fn := const -[] ;
    syn_type_morphism_proph_fn := const -[] ;
  |}.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
   
  Program Definition unit_to_uninit0ₛ : Π! [] →ₛ uninitₛ 0 := {|
    syn_type_morphism_fn := const [# ] ;
    syn_type_morphism_proph_fn := const () ;
  |}.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  
  Lemma uninit_unit E L : eqtype E L (↯ 0) () (uninit0_to_unitₛ) (unit_to_uninit0ₛ).
  Proof.
    apply eqtype_unfold. { 
      split.
        + split.
          * fun_ext. intros x. simpl. unfold indep_interp_of_syn_type in x.
            refine (match x with vnil => _ end). trivial.
          * fun_ext. intros. destruct x. done.
        + split.
          * fun_ext. intros x. destruct x. trivial.
          * fun_ext. intros x. destruct x. trivial.
        + done.
        + intros. refine (match x with vnil => _ end). trivial.
    }
    iIntros "_!>_". iSplit; [done|]. iSplit; [iApply lft_equiv_refl|].
    iSplit; first iModIntro=>/=.
    - iIntros (??? vl). naive_solver. 
    - iSplit; [|iSplit].
    + iIntros (??? vl). naive_solver. 
    + iPureIntro. intros. refine (match x with vnil => _ end). trivial.
    + iIntros "!>" (?????). iSplit; iIntros; [done|iApply default_shr_True].
  Qed.
  Lemma uninit_unit_1 E L : subtype E L (↯ 0) () (uninit0_to_unitₛ).
  Proof. eapply proj1, uninit_unit. Qed.
  Lemma uninit_unit_2 E L : subtype E L () (↯ 0) (unit_to_uninit0ₛ).
  Proof. eapply proj2, uninit_unit. Qed.

  Lemma uninit_plus_prod_helper1 m n (vl : list val) :
    length vl = m + n →
    length (take m vl) = m.
  Proof. rewrite length_take; lia. Qed.
  Lemma uninit_plus_prod_helper2 m n (vl : list val) :
    length vl = m + n →
    length (drop m vl) = n.
  Proof. rewrite length_drop; lia. Qed.

  Program Definition uninit_joinₛ {n m} : (uninitₛ n * uninitₛ m) →ₛ (uninitₛ (n + m)) := {|
    syn_type_morphism_fn := uncurry vapp ;
    syn_type_morphism_proph_fn := const () ;
  |}.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  
  Program Definition uninit_splitₛ {n m} : (uninitₛ (n + m)) →ₛ (uninitₛ n * uninitₛ m) := {|
    syn_type_morphism_fn := @vsepat _ n m ;
    syn_type_morphism_proph_fn := const ((), ()) ;
  |}.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.

  Lemma uninit_plus_prod E L m n :
    eqtype E L (↯ (m + n)) (↯ m * ↯ n) uninit_splitₛ uninit_joinₛ.
  Proof.
    apply eqtype_unfold.
    { destruct (@vapp_vsepat_iso val m n) as [A B]. split.
      - split; trivial.
      - split; trivial; fun_ext; intro x.
        + destruct x; done. + destruct x as [[] []]. done.
      - done.
      - intros. simpl. destruct (vsepat m x) eqn:Heqn.
        rewrite <- fmap_app. rewrite <- vec_to_list_app.
        replace (t) with ((vsepat m x).1); last by rewrite Heqn.
        replace (t0) with ((vsepat m x).2); last by rewrite Heqn.
        rewrite <- vsepat_app. trivial.
    }
    iIntros "_!>_". iSplit; [done|]. iSplit; [iApply lft_equiv_refl|].
    iSplit; first iModIntro=>/=.
    - iIntros (????). naive_solver. 
    - iSplit; [|iSplit].
      + iIntros "!>" (????). iSplit; iIntros; done.
      + iPureIntro. rewrite /ty_phys /= .
        intros x tid. rewrite <- fmap_app. rewrite <- vec_to_list_app. rewrite <- vsepat_app. trivial.
      + iIntros "!>" (?????). iSplit; iIntros; [iSplit|]; iApply default_shr_True.
  Qed.
  Lemma uninit_plus_prod_1 E L m n :
    subtype E L (↯ (m + n) ) (↯ m  * ↯ n ) uninit_splitₛ.
  Proof. eapply proj1, uninit_plus_prod. Qed.
  Lemma uninit_plus_prod_2 E L m n :
    subtype E L (↯ m * ↯ n) (↯ (m + n)) uninit_joinₛ.
  Proof. eapply proj2, uninit_plus_prod. Qed.
End typing.

Global Hint Resolve uninit_resolve (*uninit_unit_1 uninit_unit_2*)
  uninit_plus_prod_1 uninit_plus_prod_2 : lrust_typing.
