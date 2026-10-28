From lrust.lang Require Import proofmode.
From lrust.typing Require Export lft_contexts type bool.
From lrust.typing Require Import base_type.
From lrust.lifetime Require Import lifetime_full.
From guarding Require Import guard tactics.
Import uPred.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

Module fix_defs.

Section S.
  Context `{!typeG Σ} {𝔄} (T: type 𝔄 → type 𝔄) {HT: TypeContractive T}.

  Definition Tn n := Nat.iter (S n) T base.

  Lemma Tn_ty_lft_const n n' : ⊢ ty_lft (Tn n) ≡ₗ ty_lft (Tn n').
  Proof using HT.
    have Eq: ∀n, ⊢ ty_lft (Tn n) ≡ₗ ty_lft (Tn 0); last first.
    { iApply lft_equiv_trans; [|iApply lft_equiv_sym]; iApply Eq. }
    clear n n'=> n. case type_contractive_type_lft_morphism=> [> Hα ?|> Hα ?]; last first.
    { iApply lft_equiv_trans; [iApply Hα|]. iApply lft_equiv_sym. iApply Hα. }
    elim: n=> [|n IH]; [apply lft_equiv_refl|]. rewrite /Tn /=.
    iApply lft_equiv_trans; [iApply type_lft_morphism_lft_equiv_proper; iApply IH|].
    iApply lft_equiv_trans; [iApply Hα|]. iApply lft_equiv_trans.
    { iApply lft_intersect_equiv_proper; [iApply lft_equiv_refl|iApply Hα]. }
    iApply lft_equiv_trans; [|iApply lft_equiv_sym; iApply Hα].
    rewrite assoc. iApply lft_intersect_equiv_proper; [|iApply lft_equiv_refl].
    iApply lft_intersect_equiv_idemp.
  Qed.

  Lemma Tn_ty_E_const n n' :
    elctx_interp (Tn (S n)).(ty_E) ≡ elctx_interp (Tn (S n')).(ty_E).
  Proof using HT.
    have Eq: ∀n, elctx_interp (Tn (S n)).(ty_E) ≡ elctx_interp (Tn 1).(ty_E);
    [|by rewrite !Eq]. clear n n'=> n.
    case type_contractive_type_lft_morphism=> [> Hα HE|> ? HE]; last by rewrite !HE.
    elim: n; [done|]=> n IH.
    rewrite (HE (Tn (S n))) IH !HE !assoc -!persistent_sep_dup -!assoc.
    iSplit; iIntros "#H"; repeat iDestruct "H" as "[? H]"; iFrame "#".
    iApply (big_sepL_impl with "H"). iIntros "!> * _". iIntros "#?".
    iApply llftl_incl_trans; [done|]. iDestruct (Tn_ty_lft_const (S n) 0) as "[_ $]".
  Qed.
  
  (* The ownership predicates converge one step later than the sharing predicates
     (see [TypeContractive]). *)
  Lemma Tn_cauchy n i : (n ≤ i)%nat →
    (∀x d g tid, dist_later n
      ((Tn (2 + i)).(ty_gho_own) x d g tid) ((Tn (2 + n)).(ty_gho_own) x d g tid)) ∧
    (∀x d g tid, dist_later n
      ((Tn (2 + i)).(ty_gho_pers) x d g tid) ((Tn (2 + n)).(ty_gho_pers) x d g tid)) ∧
    (∀κ x d g tid,
      (Tn (2 + i)).(ty_shr) κ x d g tid ≡{n}≡ (Tn (2 + n)).(ty_shr) κ x d g tid).
  Proof using HT.
    move: i. elim: n=> /=[|n IH]=> i ?.
    - split; [|split].
      + intros. apply dist_later_0.
      + intros. apply dist_later_0.
      + apply HT=>//.
        * apply type_contractive_ty_size.
        * apply (Tn_ty_lft_const (S i) 1).
        * apply (Tn_ty_E_const i 0).
        * intros. apply dist_later_0.
        * intros. apply dist_later_0.
        * intros. do 2 (rewrite <- ty_phys_eq2). trivial.
        * intros. apply dist_later_0.
    - case i as [|]; [lia|]. case (IH i) as [Own [Pers Shr]]; [lia|].
      have EqOwn: ∀x d g tid,
        (Tn (3 + i)).(ty_gho_own) x d g tid ≡{n}≡ (Tn (3 + n)).(ty_gho_own) x d g tid.
      { intros =>/=. apply HT.
        * apply type_contractive_ty_size.
        * apply (Tn_ty_lft_const (2 + i) (2 + n)).
        * apply (Tn_ty_E_const (S i) (S n)).
        * apply Own.
        * apply Pers.
        * intros. do 2 (rewrite <- ty_phys_eq2). trivial.
        * apply Shr. }
      have EqPers: ∀x d g tid,
        (Tn (3 + i)).(ty_gho_pers) x d g tid ≡{n}≡ (Tn (3 + n)).(ty_gho_pers) x d g tid.
      { intros =>/=. apply HT.
        * apply type_contractive_ty_size.
        * apply (Tn_ty_lft_const (2 + i) (2 + n)).
        * apply (Tn_ty_E_const (S i) (S n)).
        * apply Own.
        * apply Pers.
        * intros. do 2 (rewrite <- ty_phys_eq2). trivial.
        * apply Shr. }
      split; [|split].
      + intros. by apply dist_later_S.
      + intros. by apply dist_later_S.
      + intros. apply HT.
        * apply type_contractive_ty_size.
        * apply (Tn_ty_lft_const (2 + i) (2 + n)).
        * apply (Tn_ty_E_const (S i) (S n)).
        * apply Own.
        * apply Pers.
        * intros. do 2 (rewrite <- ty_phys_eq2). trivial.
        * intros. apply dist_later_S, Shr.
  Qed.

  (* The ownership predicate, the persistent predicate and the sharing predicate. *)
  Program Definition gho_chain :=
    {| chain_car n := ((Tn (3 + n)).(ty_gho_own), (Tn (3 + n)).(ty_gho_pers),
                       (Tn (3 + n)).(ty_shr)) :
        prodO (prodO ((~~𝔄) -d> nat -d> nat -d> thread_id -d> iPropO Σ)
          ((~~𝔄) -d> nat -d> nat -d> thread_id -d> iPropO Σ))
          (lft -d> (~~𝔄) -d> nat -d> nat -d> thread_id -d> iPropO Σ) |}.
  Next Obligation.
    move=> n i Hni. split; [split|]=>/=.
    - move=> >. apply dist_later_S, (Tn_cauchy (S _)). lia.
    - move=> >. apply dist_later_S, (Tn_cauchy (S _)). lia.
    - move=> >. apply dist_S, (Tn_cauchy (S _)). lia.
  Qed.

  Program Definition Tn' n : type 𝔄 := {|
    ty_size := (Tn 0).(ty_size);  ty_lfts := (Tn 0).(ty_lfts);  ty_E := (Tn 1).(ty_E);
    ty_gho_own := (Tn n).(ty_gho_own);  ty_gho_res := (Tn n).(ty_gho_res);  ty_gho_pers := (Tn n).(ty_gho_pers);
    ty_phys := (Tn 0).(ty_phys);
    ty_shr := (Tn n).(ty_shr);
  |}.
  Next Obligation.
    move=> *. rewrite ty_size_eq /Tn. (*iIntros "->!%/=". apply type_contractive_ty_size.*)
    trivial.
  Qed.
  Next Obligation. intros. apply ty_size_eq2. Qed.
  Next Obligation. intros. apply ty_phys_eq2. Qed.
  Next Obligation. move=> >. apply ty_gho_own_depth_mono. Qed.
  Next Obligation. move=> >. apply ty_gho_pers_depth_mono. Qed.
  Next Obligation. move=> >. apply ty_gho_pers_impl. Qed.
  Next Obligation. move=> >. apply ty_shr_lft_mono. Qed.
  Next Obligation. move=> >. by apply ty_shr_depth_mono. Qed.
  Next Obligation.
    move=> n *. iIntros "#LFT #?". iApply (ty_share with "LFT"); [done..|].
    iApply llftl_incl_trans; [done|]. iDestruct (Tn_ty_lft_const n 0) as "[_ $]".
  Qed.
  Next Obligation.
    move=> n *. iIntros "#LFT #?". iApply (ty_shr_guard_proph with "LFT"); [done|].
    iApply llftl_incl_trans; [done|]. iDestruct (Tn_ty_lft_const n 0) as "[_ $]".
  Qed.

  Program Definition fix_ty: type 𝔄 := {|
    ty_size := (Tn 0).(ty_size);  ty_lfts := (Tn 0).(ty_lfts);  ty_E := (Tn 1).(ty_E);
    ty_gho_own := (compl gho_chain).1.1;  ty_gho_res := (compl gho_chain).1.1;  ty_gho_pers := (compl gho_chain).1.2;
    ty_phys := (Tn 0).(ty_phys);
    ty_shr := (compl gho_chain).2;
  |}.
  Next Obligation. intros. apply ty_size_eq. Qed.
  Next Obligation. intros. apply ty_size_eq2. Qed.
  Next Obligation. intros. apply ty_phys_eq2. Qed.
  Next Obligation.
    move=> *. apply @limit_preserving; [|move=> ?; by apply ty_gho_own_depth_mono].
    apply limit_preserving_entails=> ??? Eq. { done. } f_equiv. { apply Eq. }
    f_equiv. { apply Eq. } f_equiv; apply Eq.
  Qed.
  Next Obligation.
    move=> *. apply @limit_preserving; [|move=> ?; by apply ty_gho_pers_depth_mono].
    apply limit_preserving_entails=> ??? Eq. { done. } f_equiv; apply Eq.
  Qed.
  Next Obligation.
    move=> *. apply @limit_preserving, _.
    apply limit_preserving_Persistent=> ??? Eq. apply Eq.
  Qed.
  Next Obligation.
    move=> *. apply @limit_preserving; [|move=> ?; by apply ty_gho_pers_impl].
    apply limit_preserving_entails; [done|]=> ??? Eq.
    f_equiv; apply Eq.
  Qed.
  Next Obligation.
    move=> *. apply @limit_preserving, _.
    apply limit_preserving_Persistent=> ??? Eq. apply Eq.
  Qed.
  Next Obligation.
    move=> *. apply @limit_preserving; [|move=> ?; by apply (ty_shr_lft_mono (Tn' _))].
    apply limit_preserving_entails; [done|]=> ??? Eq.
    do 2 f_equiv; apply Eq.
  Qed.
  Next Obligation.
    move=> *. apply @limit_preserving; [|move=> ?; by apply (ty_shr_depth_mono (Tn' _))].
    apply limit_preserving_entails=> ??? Eq. { done. } f_equiv; apply Eq.
  Qed.
  Next Obligation.
    move=> *. apply @limit_preserving; [|move=> ?; by apply (ty_share (Tn' _))].
    apply limit_preserving_entails; [done|]=> ??? Eq.
    repeat (apply Eq || f_equiv).
  Qed.
  Next Obligation.
    move=> > ?. apply @limit_preserving; [|move=> ?; by apply (ty_shr_guard_proph (Tn' _))].
    apply limit_preserving_entails; [done|]=> ??? Eq.
    repeat (apply Eq || f_equiv).
  Qed.

  Lemma fix_ty_Tn'_dist n : fix_ty ≡{n}≡ Tn' (3 + n).
  Proof. split=>// *; apply conv_compl. Qed.
End S.
End fix_defs.

Import fix_defs.
Global Notation fix_ty := fix_ty.

Section fix_ty.
  Context `{!typeG Σ}.

  Lemma fix_unfold_fold {𝔄} (T: type 𝔄 → type 𝔄) {HT: TypeContractive T} E L :
    eqtype E L (fix_ty T) (T (fix_ty T)) idₛ idₛ.
  Proof.
    have EqOwn: ∀n vπ d tid vl, (T $ Tn T (3 + n)).(ty_gho_own) vπ d tid vl ≡
      (T $ Tn' T (3 + n)).(ty_gho_own) vπ d tid vl.
    { move=> n *. apply equiv_dist=> ?. apply HT=>//; [apply HT|
        apply (Tn_ty_lft_const T (3 + n) 0)|apply (Tn_ty_E_const T (2 + n) 0)|].
      intros. by do 2 (rewrite <- ty_phys_eq2).
    }
    have EqShr: ∀n vπ d tid l, (T $ Tn T (3 + n)).(ty_gho_pers) vπ d tid l ≡
      (T $ Tn' T (3 + n)).(ty_gho_pers) vπ d tid l.
    { move=> n *. apply equiv_dist=> n'. apply HT=>//; [apply HT|
        apply (Tn_ty_lft_const T (3 + n) 0)|apply (Tn_ty_E_const T (2 + n) 0)|].
      intros. by do 2 (rewrite <- ty_phys_eq2).
    }
    have EqShr2: ∀n κ vπ d tid l, (T $ Tn T (3 + n)).(ty_shr) κ vπ d tid l ≡
      (T $ Tn' T (3 + n)).(ty_shr) κ vπ d tid l.
    { move=> n *. apply equiv_dist=> n'. apply HT=>//; [apply HT|
        apply (Tn_ty_lft_const T (3 + n) 0)|apply (Tn_ty_E_const T (2 + n) 0)|].
      intros. by do 2 (rewrite <- ty_phys_eq2).
    }
    have EqOwn': ∀vπ d tid vl, (fix_ty T).(ty_gho_own) vπ d tid vl ≡
      (T (fix_ty T)).(ty_gho_own) vπ d tid vl.
    { move=> *. apply equiv_dist=> n. etrans; [apply dist_S, conv_compl|].
      rewrite/= (EqOwn n). symmetry.
      case (fix_ty_Tn'_dist T n)=> [_ _ _ EqO EqP _ EqS].
      apply HT=>// *; [apply lft_equiv_refl|apply dist_dist_later, EqO
        |apply dist_dist_later, EqP]. }
    have EqShr': ∀vπ d tid l, (fix_ty T).(ty_gho_pers) vπ d tid l ≡
      (T (fix_ty T)).(ty_gho_pers) vπ d tid l.
    { move=> *. apply equiv_dist=> n. etrans; [apply dist_S, conv_compl|].
      rewrite/= (EqShr n). symmetry.
      case (fix_ty_Tn'_dist T n)=> [_ _ _ EqO EqP _ EqS].
      apply HT=>// *; [apply lft_equiv_refl|apply dist_dist_later, EqO
        |apply dist_dist_later, EqP]. }
    have EqShr2': ∀κ vπ d tid l, (fix_ty T).(ty_shr) κ vπ d tid l ≡
      (T (fix_ty T)).(ty_shr) κ vπ d tid l.
    { move=> *. apply equiv_dist=> n. etrans; [apply dist_S, conv_compl|].
      rewrite/= (EqShr2 n). symmetry.
      case (fix_ty_Tn'_dist T n)=> [_ _ _ EqO EqP _ EqS].
      apply HT=>// *; [apply lft_equiv_refl|apply dist_later_pred, dist_dist_later, EqO
        |apply dist_later_pred, dist_dist_later, EqP|apply dist_dist_later, EqS]. }
    apply eqtype_id_unfold. iIntros "*_!>_". iSplit; [iPureIntro; by apply HT|].
    iSplit.
    { case type_contractive_type_lft_morphism=> [α βs E' Hα HE'|α E' Hα HE'].
      + iApply lft_equiv_trans; [|iApply lft_equiv_sym; iApply Hα].
        iApply lft_equiv_trans; [iApply Hα|].
        iApply lft_equiv_trans; [|iApply lft_intersect_equiv_proper;
          [iApply lft_equiv_refl|iApply lft_equiv_sym; iApply Hα]].
        rewrite assoc. iApply lft_intersect_equiv_proper; [|iApply lft_equiv_refl].
        iApply lft_equiv_sym. iApply lft_intersect_equiv_idemp.
      + iApply lft_equiv_trans; [iApply Hα|iApply lft_equiv_sym; iApply Hα].
    }
    iSplit. { iModIntro. iIntros. rewrite EqOwn'. by iApply bi.equiv_iff. }
    iSplit. { iModIntro. iIntros. rewrite EqShr'. by iApply bi.equiv_iff. }
    iSplit. { iPureIntro. intros. do 2 (rewrite <- ty_phys_eq2). trivial. }
    { iModIntro. iIntros. rewrite EqShr2'. by iApply bi.equiv_iff. }
  Qed.
  Lemma fix_fold_unfold {𝔄} (T: type 𝔄 → type 𝔄) {HT: TypeContractive T} E L :
    eqtype E L (T (fix_ty T)) (fix_ty T) idₛ idₛ.
  Proof. apply eqtype_symm, fix_unfold_fold. Qed.
  Lemma fix_unfold {𝔄} (T: type 𝔄 → type 𝔄) {HT: TypeContractive T} E L :
    subtype E L (fix_ty T) (T (fix_ty T)) idₛ.
  Proof. eapply proj1, fix_unfold_fold. Qed.
  Lemma fix_fold {𝔄} (T: type 𝔄 → type 𝔄) {HT: TypeContractive T} E L :
    subtype E L (T (fix_ty T)) (fix_ty T) idₛ.
  Proof. eapply proj2, fix_unfold_fold. Qed.

  Lemma fix_ty_ne {𝔄} (T T': type 𝔄 → type 𝔄)
      `{!TypeContractive T, !NonExpansive T, !TypeContractive T'} n :
    (∀ty, T ty ≡{n}≡ T' ty) → fix_ty T ≡{n}≡ fix_ty T'.
  Proof.
    move=> Eq.
    have Eq': compl (gho_chain T) ≡{n}≡ compl (gho_chain T').
    { have Eq'': Tn T (3 + n) ≡{n}≡ Tn T' (3 + n).
      { rewrite /Tn. elim (S (3 + n)); [done|]=> ? IH. by rewrite !Nat.iter_succ IH Eq. }
      etrans; [apply conv_compl|]. etrans; [|symmetry; apply conv_compl].
      split; [split|]; repeat move=> ? /=; apply Eq''. }
    move: Eq'=> [[EqO EqP] EqS].
    split=>/=; [apply Eq|apply Eq|by rewrite /Tn /= (Eq base) Eq|apply EqO|apply EqP
      |apply Eq|apply EqS].
  Qed.

  Lemma fix_type_ne {𝔄 𝔅} (T : type 𝔄 → type 𝔅 → type 𝔅)
      `{!(∀ty, TypeContractive (T ty))} :
    (∀`{!TypeNonExpansive U}, TypeNonExpansive (λ ty, T ty (U ty))) →
      TypeNonExpansive (λ ty, fix_ty (T ty)).
  Proof.
    move=> HT. have Hne: ∀n, TypeNonExpansive (λ ty, Tn (T ty) n).
    { elim=> [|? IH]; [apply HT, _|apply HT, IH]. }
    split=>/=.
    - case (type_ne_type_lft_morphism (T := λ ty, Tn (T ty) 1))=>
      [α βs E Hα HE|α E Hα HE].
      + eapply (type_lft_morphism_add _ α βs E), HE=> ?.
        iApply lft_equiv_trans; [|iApply Hα]. iApply lft_equiv_sym.
        iApply (Tn_ty_lft_const _ 1 0).
      + eapply (type_lft_morphism_const _ α E), HE=> ?.
        iApply lft_equiv_trans; [|iApply Hα]. iApply lft_equiv_sym.
        iApply (Tn_ty_lft_const _ 1 0).
    - apply HT, _.
    - move=> *. etrans; [apply conv_compl|].
      etrans; [|symmetry; apply conv_compl]. by apply Hne.
    - move=> *. etrans; [apply conv_compl|].
      etrans; [|symmetry; apply conv_compl]. by apply Hne.
    - intros. do 2 (rewrite <- ty_phys_eq2). trivial.
    - move=> *. etrans; [apply conv_compl|].
      etrans; [|symmetry; apply conv_compl]. by apply Hne.
  Qed.

  Lemma fix_type_contractive {𝔄 𝔅} (T : type 𝔄 → type 𝔅 → type 𝔅)
      `{!(∀ty, TypeContractive (T ty))} :
    (∀`{!TypeContractive U}, TypeContractive (λ ty, T ty (U ty))) →
      TypeContractive (λ ty, fix_ty (T ty)).
  Proof.
    move=> HT. have Hne: ∀n, TypeContractive (λ ty, Tn (T ty) n).
    { elim=> [|? IH]; [apply HT, _|apply HT, IH]. }
    split=>/=.
    - case (type_ne_type_lft_morphism (T := λ ty, Tn (T ty) 1))=>
      [α βs E Hα HE|α E Hα HE].
      + eapply (type_lft_morphism_add _ α βs E), HE=> ?.
        iApply lft_equiv_trans; [|iApply Hα]. iApply lft_equiv_sym.
        iApply (Tn_ty_lft_const _ 1 0).
      + eapply (type_lft_morphism_const _ α E), HE=> ?.
        iApply lft_equiv_trans; [|iApply Hα]. iApply lft_equiv_sym.
        iApply (Tn_ty_lft_const _ 1 0).
    - apply HT, _.
    - move=> *. etrans; [apply conv_compl|].
      etrans; [|symmetry; apply conv_compl]. by apply Hne.
    - move=> *. etrans; [apply conv_compl|].
      etrans; [|symmetry; apply conv_compl]. by apply Hne.
    - intros. do 2 (rewrite <- ty_phys_eq2). trivial.
    - move=> *. etrans; [apply conv_compl|].
      etrans; [|symmetry; apply conv_compl]. by apply Hne.
  Qed.
End fix_ty.

Section fix_ty.
  Context `{!typeG Σ} {𝔄} (T: type 𝔄 → type 𝔄) {HT: TypeContractive T}.

  Global Instance fix_copy :
    (∀`(!Copy ty), Copy (T ty)) → Copy (fix_ty T).
  Proof.
    move=> ?. have ?: ∀n, Copy (Tn T n) by elim; apply _.
    split; rewrite /fix_ty /=.
    - move=> >. eapply @limit_preserving; [|apply _].
      apply limit_preserving_Persistent=> ??? Eq. apply Eq.
    - move=> >. 
      eapply @limit_preserving.
      + apply limit_preserving_entails=> ??? Eq.
        * apply Eq.
        * done.
      + intros. iIntros "G". iDestruct (copy_concrete with "G") as "%Hconc".
        iPureIntro. rewrite <- ty_phys_eq2 in Hconc. rewrite <- ty_phys_eq2. done.
    - move=> >. eapply @limit_preserving; [|intros; apply copy_shr].
      apply limit_preserving_entails=> ??? Eq.
      + apply Eq.
      + f_equiv. apply Eq.
  Qed.

  Global Instance fix_send :
    (∀`(!Send ty), Send (T ty)) → Send (fix_ty T).
  Proof.
    move=> ?. have ?: ∀n, Send (Tn T n) by elim; apply _. split; rewrite /fix_ty=> > /=.
    { do 2 (rewrite <- ty_phys_eq2). apply syn_abstract_phys_eq. }
    eapply @limit_preserving.
    + apply limit_preserving_forall. intro.
      apply limit_preserving_forall. intro.
      apply limit_preserving_forall. intro.
      apply limit_preserving_entails=> ??? Eq; [done|].
      do 8 f_equiv. { apply Eq. }
      do 8 f_equiv. apply Eq.
    + intros. apply send_change_tid; trivial.
  Qed.

  Global Instance fix_sync :
    (∀`(!Sync ty), Sync (T ty)) → Sync (fix_ty T).
  Proof.
    move=> ?. have ?: ∀n, Sync (Tn T n) by elim; apply _. rewrite /fix_ty=> > /=.
    eapply @limit_preserving.
      + apply limit_preserving_and; [|apply limit_preserving_and; [|apply limit_preserving_and]].
        * do 2 (rewrite <- ty_phys_eq2). done.
        * apply limit_preserving_equiv=> ??? Eq; apply Eq.
        * apply limit_preserving_equiv=> ??? Eq; apply Eq.
        * apply limit_preserving_forall=> ?.
          apply limit_preserving_equiv=> ??? Eq; apply Eq.
      + intros. split.
        * do 2 (rewrite <- ty_phys_eq2). done.
        * apply sync_change_tid.
  Qed.

  (** The resolved ownership of [fix_ty] is its ownership (it is not computed as a limit;
      see [ty_gho_res]). *)
  Global Instance fix_res_own : ResOwn (fix_ty T).
  Proof. done. Qed.

  Lemma fix_resolve E L Φ :
    (∀ty, resolve E L ty Φ → resolve E L (T ty) Φ) → resolve E L (fix_ty T) Φ.
  Proof.
    move=> Loop. have Rslv: ∀n, resolve E L (Tn T n) Φ.
    { elim=> [|? H]; apply Loop; [apply base_resolve|apply H]. }
    rewrite /fix_ty=> > /=. eapply @limit_preserving; [|move=> ?; apply Rslv].
    apply limit_preserving_forall=> ?. 2: { done. }
    apply limit_preserving_entails; [done|]=> ??? Eq. do 8 f_equiv. apply Eq.
  Qed.
End fix_ty.

Section fix_subtyping.
  Context `{!typeG Σ}.

  Local Lemma wand_forall P (Φ: nat → iProp Σ) : (∀n, P -∗ Φ n) ⊢ (P -∗ ∀n, Φ n).
  Proof. iIntros "To P %". iApply ("To" with "P"). Qed.
  Local Lemma entails_dist_True (P Q: iProp Σ) : (P ⊢ Q) ↔ ∀n, (P → Q)%I ≡{n}≡ True%I.
  Proof. by rewrite entails_eq_True equiv_dist. Qed.

  Lemma fix_subtype {𝔄 𝔅} (f: 𝔄 →ₛ 𝔅)
    (T : type 𝔄 → type 𝔄) `{!TypeContractive T}
    (T' : type 𝔅 → type 𝔅) `{!TypeContractive T'} E L :
    (∀ x, ξl x = ξl ((~~!ₛ) f x)) →
    (size_of 𝔄 = size_of 𝔅) →
    (∀ x, syn_phys x = syn_phys ((~~!ₛ) f x)) →
    (∀ty ty', subtype E L ty ty' f → subtype E L (T ty) (T' ty') f) →
    subtype E L (fix_ty T) (fix_ty T') f.
  Proof.
    move=> Heq1 Heq2 Heq3 Loop.
    have Incl: llctx_interp L ⊢ □ (elctx_interp E -∗
      ∀n, type_incl (Tn T n) (Tn T' n) f).
    { apply wand_entails.
      rewrite intuitionistically_into_persistently -wand_forall persistently_forall.
      rewrite -wand_forall.
      apply forall_intro=> n. rewrite -intuitionistically_into_persistently.
      apply Loop. elim n=> [|??]; [apply base_subtype; done|by apply Loop].
    }
    unfold subtype.
    rewrite Incl /type_incl -!persistent_and_sep /=. apply entails_wand. do 2 f_equiv.
    (* FIXME : change the definition of limit_preserving so that it
       applies even if the limti is not computed with compl. *)
    apply and_intro; [|apply and_intro; [|apply and_intro; [|apply and_intro; [|apply and_intro]]]].
    - iIntros "H". iDestruct ("H" $! 0%nat) as "($&_)".
    - iIntros "H". iDestruct ("H" $! 0%nat) as "(_&$&_)".
    - apply entails_dist_True=> ?. setoid_rewrite conv_compl=>/=.
      apply entails_dist_True. iIntros "H". iDestruct ("H" $! _) as "(_&_&$&_)".
    - apply entails_dist_True=> ?. setoid_rewrite conv_compl=>/=.
      apply entails_dist_True. iIntros "H". iDestruct ("H" $! _) as "(_&_&_&$&_)".
    - iIntros. iPureIntro. intros. do 2 (rewrite <- ty_phys_eq2). done.
    - apply entails_dist_True=> ?. setoid_rewrite conv_compl=>/=.
      apply entails_dist_True. iIntros "H". iDestruct ("H" $! _) as "(_&_&_&_&_&$)".
  Qed.

  Lemma fix_eqtype_subtype {𝔄 𝔅} f g
    (T : type 𝔄 → type 𝔄) `{!TypeContractive T}
    (T' : type 𝔅 → type 𝔅) `{!TypeContractive T'} E L :
    (∀ty ty', eqtype E L ty ty' f g → eqtype E L (T ty) (T' ty') f g) →
    (∀ x, ξl x = ξl ((~~!ₛ) f x)) →
    (∀ x, ξl x = ξl ((~~!ₛ) g x)) →
    (size_of 𝔄 = size_of 𝔅) →
    (∀ x, syn_phys x = syn_phys ((~~!ₛ) f x)) →
    (∀ x, syn_phys x = syn_phys ((~~!ₛ) g x)) →
    subtype E L (fix_ty T) (fix_ty T') f.
  Proof.
    move=> Loop Eq1 Eq2 Eq3 Eq4 Eq5.
    have Incl: llctx_interp L ⊢ □ (elctx_interp E -∗
      ∀n, type_incl (Tn T n) (Tn T' n) f).
    { apply wand_entails.
      rewrite intuitionistically_into_persistently -wand_forall persistently_forall.
      rewrite -wand_forall.
      apply forall_intro=> n. rewrite -intuitionistically_into_persistently.
      apply Loop. elim n=> [|??]; [apply base_eqtype|by apply Loop]; done. }
    unfold subtype.
    rewrite Incl /type_incl -!persistent_and_sep /=. apply entails_wand. do 2 f_equiv.
    apply and_intro; [|apply and_intro; [|apply and_intro; [|apply and_intro; [|apply and_intro]]]].
    - iIntros "H". iDestruct ("H" $! 0%nat) as "($&_)".
    - iIntros "H". iDestruct ("H" $! 0%nat) as "(_&$&_)".
    - apply entails_dist_True=> ?. setoid_rewrite conv_compl=>/=.
      apply entails_dist_True. iIntros "H". iDestruct ("H" $! _) as "(_&_&$&_)".
    - apply entails_dist_True=> ?. setoid_rewrite conv_compl=>/=.
      apply entails_dist_True. iIntros "H". iDestruct ("H" $! _) as "(_&_&_&$&_)".
    - iIntros. iPureIntro. intros. do 2 (rewrite <- ty_phys_eq2). done.
    - apply entails_dist_True=> ?. setoid_rewrite conv_compl=>/=.
      apply entails_dist_True. iIntros "H". iDestruct ("H" $! _) as "(_&_&_&_&_&$)".
  Qed.

  Lemma fix_eqtype {𝔄 𝔅} f g
    (T: type 𝔄 → type 𝔄) `{!TypeContractive T}
    (T': type 𝔅 → type 𝔅) `{!TypeContractive T'} E L :
    (∀ty ty', eqtype E L ty ty' f g → eqtype E L (T ty) (T' ty') f g) →
    (∀ x, ξl x = ξl ((~~!ₛ) f x)) →
    (∀ x, ξl x = ξl ((~~!ₛ) g x)) →
    (size_of 𝔄 = size_of 𝔅) →
    (∀ x, syn_phys x = syn_phys ((~~!ₛ) f x)) →
    (∀ x, syn_phys x = syn_phys ((~~!ₛ) g x)) →
    eqtype E L (fix_ty T) (fix_ty T') f g.
  Proof.
    move=> Loop.
    have ?: ∀ty' ty, eqtype E L ty' ty g f → eqtype E L (T' ty') (T ty) g f.
    { move=> ??[??]. split; apply Loop; by split. }
    split; by eapply fix_eqtype_subtype.
  Qed.

  Lemma fix_subtype_l {𝔄 𝔅} (f: 𝔄 →ₛ 𝔅) ty T `{!TypeContractive T} E L :
    subtype E L ty (T (fix_ty T)) f → subtype E L ty (fix_ty T) f.
  Proof.
    move=> ?. eapply (subtype_trans _ _ _ _ idₛ); [done|]. apply fix_fold.
  Qed.
  Lemma fix_subtype_r {𝔄 𝔅} (f: 𝔄 →ₛ 𝔅) ty T `{!TypeContractive T} E L :
    subtype E L (T (fix_ty T)) ty f → subtype E L (fix_ty T) ty f.
  Proof.
    move=> ?. eapply (subtype_trans _ _ _ idₛ); [|done]. apply fix_unfold.
  Qed.
  Lemma fix_eqtype_l {𝔄 𝔅} (f: 𝔄 →ₛ 𝔅) g ty T `{!TypeContractive T} E L :
    eqtype E L ty (T (fix_ty T)) f g → eqtype E L ty (fix_ty T) f g.
  Proof.
    move=> ?. eapply (eqtype_trans _ _ _ _ _ idₛ idₛ); [done|]. apply fix_fold_unfold.
  Qed.
  Lemma fix_eqtype_r {𝔄 𝔅} (f: 𝔄 →ₛ 𝔅) g ty T `{!TypeContractive T} E L :
    eqtype E L (T (fix_ty T)) ty f g → eqtype E L (fix_ty T) ty f g.
  Proof.
    move=> ?. eapply (eqtype_trans _ _ _ idₛ idₛ); [|done]. apply fix_unfold_fold.
  Qed.
End fix_subtyping.

Global Hint Resolve fix_subtype_l fix_subtype_r fix_eqtype_l fix_eqtype_r | 100
  : lrust_typing.
