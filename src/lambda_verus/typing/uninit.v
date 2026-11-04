From lrust.typing Require Export type.
From lrust.typing Require Import product bytes_layout struct.
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
    split; [apply _|apply _|intros; by apply copy_shr_default].
  Qed.

  Global Instance uninit_send n : Send (↯ n).
  Proof. done. Qed.
  
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
    syn_type_morphism_fn := const () ;
    syn_type_morphism_proph_fn := const () ;
  |}.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  
  Lemma uninit_unit E L : eqtype E L (↯ 0) () (uninit0_to_unitₛ) (unit_to_uninit0ₛ).
  Proof.
    apply eqtype_unfold. {
      split.
        + split; fun_ext; by intros [].
        + split; fun_ext; by intros [].
        + by intros [].
        + by apply syn_bincl_same.
    }
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
    syn_type_morphism_fn := const () ;
    syn_type_morphism_proph_fn := const () ;
  |}.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  
  Program Definition uninit_splitₛ {n m} : (uninitₛ (n + m)) →ₛ (uninitₛ n * uninitₛ m) := {|
    syn_type_morphism_fn := const ((), ()) ;
    syn_type_morphism_proph_fn := const ((), ()) ;
  |}.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.

  Lemma syn_bincl_uninit_split {n m} : syn_bincl (uninit_splitₛ (n:=n) (m:=m)).
  Proof.
    split; [by rewrite syn_bsize_prod|]. split; last first.
    { intros x R fbs fv fv' _ Hx Hx'. simpl in *. simplify_eq. done. }
    intros x R fbs.
    cbn [syn_type_morphism_fn uninit_splitₛ]. destruct x.
    rewrite syn_fbytes_pair !syn_fbytes_uninit. split.
    - intros [Hl [bs ->]]. rewrite length_fmap in Hl.
      exists (inr <$> take n bs), (inr <$> drop n bs). rewrite -fmap_app take_drop.
      split; [done|]. rewrite !syn_fbytes_uninit !length_fmap length_take length_drop.
      split; split; [lia|eauto|lia|eauto].
    - intros (f1 & f2 & -> & Ha & Hb). apply syn_fbytes_uninit in Ha as [Hl1 [b1 ->]].
      apply syn_fbytes_uninit in Hb as [Hl2 [b2 ->]].
      split; [rewrite length_app; lia|]. exists (b1 ++ b2). by rewrite fmap_app.
  Qed.

  Lemma uninit_plus_prod E L m n :
    eqtype E L (↯ (m + n)) (↯ m * ↯ n) uninit_splitₛ uninit_joinₛ.
  Proof.
    apply eqtype_unfold.
    { split.
      - split; fun_ext; by [intros []|intros [[] []]].
      - split; fun_ext; by [intros []|intros [[] []]].
      - intros [] bs. cbn [syn_mty syn_val]. rewrite decode_pad decode_pad_pair.
        case_decide; naive_solver.
      - apply syn_bincl_uninit_split.
    }
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
  (** ** Splitting uninitialized bytes into a struct of two *)

  (** The struct of [↯ m] and [↯ n], with no padding. *)
  Definition uninit_pair_layout (m n: nat) : struct_layout := SL [0; m] (m + n) 1.

  Lemma uninit_pair_lay m n :
    struct_lay (uninit_pair_layout m n) (syn_mty <$> [uninitₛ m; uninitₛ n]) =
    uninit_pair_layout m n.
  Proof.
    apply struct_lay_wf_eq. split; [done|]. rewrite /sl_mty /uninit_pair_layout /=.
    constructor.
    - intros i j o1 m1 o2 m2 Hij H1 H2.
      destruct i as [|[|i]], j as [|[|j]]; simplify_eq/=; lia.
    - repeat constructor; simpl; lia.
    - by repeat constructor.
  Qed.

  Program Definition uninit_join_structₛ {m n} :
      structₛ (uninit_pair_layout m n) [uninitₛ m; uninitₛ n] →ₛ uninitₛ (m + n) := {|
    syn_type_morphism_fn := const ();
    syn_type_morphism_proph_fn := const ();
  |}.
  Next Obligation. done. Qed.
  Next Obligation. by intros ?? [[] [[] []]]. Qed.

  Program Definition uninit_split_structₛ {m n} :
      uninitₛ (m + n) →ₛ structₛ (uninit_pair_layout m n) [uninitₛ m; uninitₛ n] := {|
    syn_type_morphism_fn := const -[(); ()];
    syn_type_morphism_proph_fn := const -[(); ()];
  |}.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.

  Lemma uninit_pair_mty m n :
    syn_mty (structₛ (uninit_pair_layout m n) [uninitₛ m; uninitₛ n]) =
    MTuple [(0%nat, MTuple [] m 1); (m, MTuple [] n 1)] (m + n) 1.
  Proof. by rewrite /= /struct_mty uninit_pair_lay. Qed.

  Lemma syn_bincl_uninit_split_struct {m n} : syn_bincl (uninit_split_structₛ (m:=m) (n:=n)).
  Proof.
    split; [by rewrite syn_bsize_struct /struct_size uninit_pair_lay|]. split; last first.
    { intros x R fbs fv fv' _ Hx Hx'. simpl in Hx. simplify_eq.
      rewrite uninit_pair_mty. simpl in Hx'. by simplify_eq. }
    intros x R fbs. cbn [syn_type_morphism_fn uninit_split_structₛ].
    rewrite syn_fbytes_struct syn_fbytes_uninit /struct_size /struct_fields /struct_offs
      uninit_pair_lay /= !syn_fbytes_uninit /list_slice !length_take !length_drop.
    change (syn_bsize (uninitₛ m)) with m. change (syn_bsize (uninitₛ n)) with n.
    rewrite drop_0 Nat.sub_0_r. split.
    - intros [Hl [bs ->]]. rewrite length_fmap in Hl. split_and!.
      + by rewrite length_fmap.
      + intros i fb Hi _. apply list_lookup_fmap_Some in Hi as (b & Ha & Hb).
        simplify_eq. by eexists.
      + rewrite length_fmap. lia.
      + exists (take m bs). by rewrite fmap_take.
      + rewrite length_fmap. lia.
      + exists (take n (drop m bs)). by rewrite fmap_take fmap_drop.
      + done.
    - intros (Hl & Hpad & (_ & bs1 & H1) & (_ & bs2 & H2) & _). split; [done|].
      apply plain_fbytes. intros i fb Hi.
      destruct (decide (i < m)%nat) as [Him|Him].
      + have : (take m fbs) !! i = Some fb by rewrite lookup_take.
        rewrite H1. intros (b & Ha & Hb)%list_lookup_fmap_Some. simplify_eq. by eexists.
      + have Hin : (i - m < n)%nat by (apply lookup_lt_Some in Hi; lia).
        have : (take n (drop m fbs)) !! (i - m)%nat = Some fb.
        { rewrite lookup_take // lookup_drop. by replace (m + (i - m))%nat with i by lia. }
        rewrite H2. intros (b & Ha & Hb)%list_lookup_fmap_Some. simplify_eq. by eexists.
  Qed.

  Lemma uninit_plus_struct E L m n :
    eqtype E L (↯ (m + n)) (struct_ty (uninit_pair_layout m n) +[↯ m; ↯ n]%T)
      uninit_split_structₛ uninit_join_structₛ.
  Proof.
    apply eqtype_unfold.
    { split.
      - split; fun_ext; by [intros []|intros [[] [[] []]]].
      - split; fun_ext; by [intros []|intros [[] [[] []]]].
      - intros [] bs. rewrite uninit_pair_mty. cbn [syn_mty syn_val].
        rewrite decode_pad decode_value_tuple /=.
        case_decide as Hl; [|done]. rewrite /list_slice !length_take !length_drop.
        rewrite !decide_True; [done|lia|lia].
      - apply syn_bincl_uninit_split_struct. }
    iIntros "_!>_". iSplit; [iApply lft_equiv_refl|].
    iSplit; first iModIntro=>/=.
    - iIntros (????). naive_solver.
    - iSplit.
      + iIntros "!>" (????). iSplit; iIntros; done.
      + iIntros "!>" (?????). iSplit; iIntros; [|iApply default_shr_True].
        iSplit; [iApply default_shr_True|]. iSplit; [iApply default_shr_True|done].
  Qed.
  Lemma uninit_plus_struct_1 E L m n :
    subtype E L (↯ (m + n)) (struct_ty (uninit_pair_layout m n) +[↯ m; ↯ n]%T)
      uninit_split_structₛ.
  Proof. eapply proj1, uninit_plus_struct. Qed.
  Lemma uninit_plus_struct_2 E L m n :
    subtype E L (struct_ty (uninit_pair_layout m n) +[↯ m; ↯ n]%T) (↯ (m + n))
      uninit_join_structₛ.
  Proof. eapply proj2, uninit_plus_struct. Qed.
End typing.

Global Hint Resolve uninit_resolve (*uninit_unit_1 uninit_unit_2*)
  uninit_plus_prod_1 uninit_plus_prod_2 : lrust_typing.
