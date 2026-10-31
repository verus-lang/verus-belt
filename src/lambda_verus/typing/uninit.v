From lrust.typing Require Export type.
From lrust.typing Require Import product bytes_layout.
Set Default Proof Using "Type".

Open Scope nat.

Section uninit.
  Context `{!typeG Σ}.

  Program Definition uninit n : type (uninitₛ n) := {|
    ty_lfts := [];
    ty_E := [];
    ty_gho_own vπ _ _ _ := True;
    ty_gho_res vπ _ _ _ := True;
    ty_gho_pers vπ _ _ _ := True;
    ty_mty := syn_mty _; ty_val := syn_val; ty_mty_eq := eq_refl; ty_val_eq _ := eq_refl;
    ty_fval := syn_fval; ty_fval_eq _ := eq_refl;
    ty_shr := default_shr (λ vπ _ _ _, True);
  |}%I.
  Next Obligation. by iIntros. Qed.
  Next Obligation. set_solver. Qed.
  Next Obligation. by iIntros. Qed.
  Solve All Obligations with solve_default_shr.
  Next Obligation. by iIntros. Qed.
End uninit.

Notation "↯" := uninit : lrust_type_scope.

Section typing.
  Context `{!typeG Σ}.

  Global Instance uninit_copy n : Copy (↯ n).
  Proof.
    split; [apply _|intros; by apply copy_shr_default].
  Qed.

  Global Instance uninit_send n : Send (↯ n).
  Proof.
    intros. split.
      iIntros. iApply step_fupdN_intro; first done. iNext.
        iExists x, 0%nat. iModIntro. iFrame. simpl.
        replace (d0 + 0)%nat with d0 by lia. iFrame "#". done.
  Qed.
  
  Global Instance uninit_sync n : Sync (↯ n).
  Proof. apply sync_default; [done|]. split => //=. Qed.

  Lemma uninit_resolve n E L : resolve E L (↯ n) (const (const True)).
  Proof. apply resolve_just. Qed.

  Global Instance uninit_res_own n : ResOwn (↯ n).
  Proof. done. Qed.

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
        + intros. refine (match x with vnil => _ end). done.
    }
    { by apply syn_bincl_same. }
    iIntros "_!>_". iSplit; [iApply lft_equiv_refl|].
    iSplit; first iModIntro=>/=.
    - iIntros (??? vl). naive_solver. 
    - iSplit.
    + iIntros (??? vl). naive_solver. 
    + iIntros "!>" (?????). iSplit; iIntros; [done|iApply default_shr_True].
  Qed.
  Lemma uninit_unit_1 E L : subtype E L (↯ 0) () (uninit0_to_unitₛ).
  Proof. eapply proj1, uninit_unit. Qed.
  Lemma uninit_unit_2 E L : subtype E L () (↯ 0) (unit_to_uninit0ₛ).
  Proof. eapply proj2, uninit_unit. Qed.

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

  Lemma syn_bincl_uninit_split {n m} : syn_bincl (uninit_splitₛ (n:=n) (m:=m)).
  Proof.
    split; [by rewrite syn_bsize_prod|]. intros x R fbs.
    cbn [syn_type_morphism_fn uninit_splitₛ]. destruct (vsepat x) as [a b].
    rewrite syn_fbytes_pair !syn_fbytes_uninit. split.
    - intros [Hl [bs ->]]. rewrite length_fmap in Hl.
      exists (inr <$> take n bs), (inr <$> drop n bs). rewrite -fmap_app take_drop.
      split; [done|]. rewrite !length_fmap length_take length_drop.
      split; split; [lia|eauto|lia|eauto].
    - intros (f1 & f2 & -> & [Hl1 [b1 ->]] & [Hl2 [b2 ->]]).
      split; [rewrite length_app; lia|]. exists (b1 ++ b2). by rewrite fmap_app.
  Qed.

  Lemma uninit_plus_prod E L m n :
    eqtype E L (↯ (m + n)) (↯ m * ↯ n) uninit_splitₛ uninit_joinₛ.
  Proof.
    apply eqtype_unfold.
    { destruct (@vapp_vsepat_iso val m n) as [A B]. split.
      - split; trivial.
      - split; trivial; fun_ext; intro x.
        + destruct x; done. + destruct x as [[] []]. done.
      - rewrite /syn_bsize /= !seq_size_cons seq_size_nil /=. lia.
      - intros x bs. cbn [syn_mty syn_val]. rewrite decode_pad decode_pad_pair.
        destruct (syn_type_morphism_fn _ x). case_decide; naive_solver.
    }
    { apply syn_bincl_uninit_split. }
    iIntros "_!>_". iSplit; [iApply lft_equiv_refl|].
    iSplit; first iModIntro=>/=.
    - iIntros (????). naive_solver. 
    - iSplit.
      + iIntros "!>" (????). iSplit; iIntros; done.
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
