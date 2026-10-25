From iris.proofmode Require Import proofmode.
From iris.algebra Require Import list numbers.
From lrust.typing Require Import lft_contexts.
From lrust.typing Require Export type.
From guarding Require Import guard tactics guard_later_pers.
From lrust.lifetime Require Import lifetime_full.
From lrust.typing Require Import mod_ty.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅 ℭ 𝔇: syn_type.

Section product.
  Context `{!typeG Σ}.

  Program Definition unit0 : type (Π! []) :=
    {| ty_size := 0;
       ty_lfts := [];
       ty_E := [];
       ty_gho_own x d g tid := True%I;
       ty_gho_pers x d g tid := True%I;
       ty_phys x tid := [];
       ty_shr := default_shr (λ x d g tid, True%I);
    |}%I.
  Next Obligation. iIntros (??). trivial. Qed.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation. intros. iIntros. done. Qed.
  Next Obligation. intros. iIntros. done. Qed.
  Next Obligation. intros. set_solver. Qed.
  Next Obligation. iIntros. done. Qed.
  Solve All Obligations with solve_default_shr.

  Global Instance unit0_copy : Copy unit0.
  Proof.
    split. - by apply _. - done.
  Qed.

  Global Instance unit0_send : Send unit0.
  Proof.
    intros. split; trivial. iIntros. iApply step_fupdN_intro; first done. iNext.
    iExists x, 0%nat. iModIntro. iFrame. simpl.
    replace (d0 + 0)%nat with d0 by lia. iFrame "#". done.
  Qed.
  
  Global Instance unit0_sync : Sync unit0.
  Proof. intros. split; trivial; split; trivial. Qed.

  Lemma unit0_resolve E L : resolve E L unit0 (const (const True)).
  Proof. apply resolve_just. Qed.

  Program Definition prod_ty {𝔄 𝔅} (ty: type 𝔄) (ty': type 𝔅) : type (𝔄 * 𝔅) := {|
    ty_size := ty.(ty_size) + ty'.(ty_size);
    ty_lfts := ty.(ty_lfts) ++ ty'.(ty_lfts);
    ty_E := ty.(ty_E) ++ ty'.(ty_E);
    ty_gho_own x d g tid := ty.(ty_gho_own) (fst x) d g tid ∗ ty'.(ty_gho_own) (snd x) d g tid;
    ty_gho_pers x d g tid := ty.(ty_gho_pers) (fst x) d g tid ∗ ty'.(ty_gho_pers) (snd x) d g tid;
    ty_phys x tid := ty.(ty_phys) (fst x) tid ++ ty'.(ty_phys) (snd x) tid;
    ty_shr := default_shr (λ (x: ~~(𝔄 * 𝔅)) d g tid, ty.(ty_gho_own) (fst x) d g tid ∗ ty'.(ty_gho_own) (snd x) d g tid);
  |}%I.
  Next Obligation. intros. rewrite length_app !ty_size_eq. trivial. Qed.
  Next Obligation. intros. simpl. by do 2 (rewrite <- ty_size_eq2). Qed.
  Next Obligation. intros. destruct x. simpl. by do 2 (rewrite <- ty_phys_eq2). Qed.
  Next Obligation. intros ty ty' tty tty' d g d' g'. move=>/= *. iIntros "[A B]".
    iDestruct ((ty_gho_own_depth_mono _ d g d' g') with "A") as "[A A']"; trivial.
    iDestruct ((ty_gho_own_depth_mono _ d g d' g') with "B") as "[B B']"; trivial.
    iFrame. iIntros "[x y]".
    iDestruct ("A'" with "x") as "A'".
    iDestruct ("B'" with "y") as "B'".
    iFrame.
  Qed.
  Next Obligation. intros ty ty' tty tty' d g d' g'. move=>/= *. iIntros "[A B]".
    iDestruct ((ty_gho_pers_depth_mono _ d g d' g') with "A") as "A'"; trivial.
    iDestruct ((ty_gho_pers_depth_mono _ d g d' g') with "B") as "B'"; trivial.
    iFrame.
  Qed.
  Next Obligation. intros 𝔄 𝔅 ty ty' κ x n d g tid ξ R Hin.
    iIntros "LFT #Incl [Gho1 Gho2]".
    rewrite elem_of_app in Hin. destruct Hin as [Hin|Hin].
    - iDestruct (ty_guard_proph 𝔄 ty κ (fst x) n d g tid ξ R with "LFT [] Gho1") as "A1".
      { apply Hin. }
      { rewrite lft_intersect_list_app. iApply (guards_transitive with "Incl []").
        iApply llftl_intersect_incl_l. }
      iNext. iIntros "#Rk #Rgho". iApply "A1". { iFrame "Rk". }
      iApply guards_weaken_rhs_sep_l. iFrame "Rgho".
    - iDestruct (ty_guard_proph 𝔅 ty' κ (snd x) n d g tid ξ R with "LFT [] Gho2") as "A2".
      { apply Hin. }
      { rewrite lft_intersect_list_app. iApply (guards_transitive with "Incl []").
        iApply llftl_intersect_incl_r. }
      iNext. iIntros "#Rk #Rgho". iApply "A2". { iFrame "Rk". }
      iApply guards_weaken_rhs_sep_r. iFrame "Rgho".
  Qed.
  Next Obligation.
    intros 𝔄 𝔅 ty ty' x d g tid. iIntros "[A B]".
    iDestruct (ty_gho_pers_impl with "A") as "#A1".
    iDestruct (ty_gho_pers_impl with "B") as "#B1".
    iFrame "#".
  Qed.
  Solve All Obligations with solve_default_shr.

  Global Instance prod_ty_ne {𝔄 𝔅} : NonExpansive2 (@prod_ty 𝔄 𝔅).
  Proof. solve_ne_type. Qed.

  Fixpoint xprod_ty {𝔄l} (tyl: typel 𝔄l) : type (Π! 𝔄l) :=
    match tyl in hlist _ 𝔄l return type (Π! 𝔄l) with
    | +[] => unit0
    | ty +:: tyl' => mod_ty (𝔄:=_*Π!_) (𝔅:=Π!(_::_))
                            to_cons_prodₛ of_cons_prodₛ (prod_ty ty (xprod_ty tyl'))
    end.

  Global Instance product_ne {𝔄l} : NonExpansive (@xprod_ty 𝔄l).
  Proof. move=> ???. elim; [done|]=> */=. by do 2 f_equiv. Qed.

  Definition unit_ty := (<{empty_prod_to_unitₛ;empty_prod_of_unitₛ}> (xprod_ty +[]))%T.
  (*@mod_ty  _ _ (Π! []) unitₛ empty_prod_to_unitₛ empty_prod_of_unitₛ
      isoₛ_empty_prod_unit (xprod_ty +[]).*)
End product.

Notation "ty * ty'" := (prod_ty ty%T ty'%T) : lrust_type_scope.
Notation "Π!" := xprod_ty : lrust_type_scope.
Notation "()" := unit_ty : lrust_type_scope.

Section typing.
  Context `{!typeG Σ}.

  Lemma unit_ty_own x d g tid vl :
    ty_own () x d g tid vl ⊣⊢ ⌜vl = []⌝.
  Proof. rewrite /unit_ty mod_ty_own. iSplit.
      { iIntros "[A %B]". symmetry in B. iPureIntro. apply B. }
      { iIntros "%B". symmetry in B. iSplit. { done. } iPureIntro. apply B. }
  Qed.

  Lemma unit_resolve E L : resolve E L () (const (const True)).
  Proof. apply resolve_just. Qed.

  Global Instance prod_lft_morphism {𝔄 𝔅 ℭ} (T: type 𝔄 → type 𝔅) (T': type 𝔄 → type ℭ):
    TypeLftMorphism T → TypeLftMorphism T' → TypeLftMorphism (λ ty, T ty * T' ty)%T.
  Proof.
    case=> [α βs E Hα HE|α E Hα HE]; case=> [α' βs' E' Hα' HE'|α' E' Hα' HE'].
    - apply (type_lft_morphism_add _ (α ⊓ α') (βs ++ βs') (E ++ E'))=> ty.
      + rewrite lft_intersect_list_app. iApply lft_equiv_trans.
        { iApply lft_intersect_equiv_proper; [iApply Hα|iApply Hα']. }
        rewrite -!assoc (comm (⊓) (ty_lft ty) (α' ⊓ _)) -!assoc.
        repeat iApply lft_intersect_equiv_proper; try iApply lft_equiv_refl.
        iApply lft_intersect_equiv_idemp.
      + rewrite/= !elctx_interp_app HE HE' big_sepL_app -!assoc.
        iSplit; iIntros "#H"; repeat iDestruct "H" as "[?H]"; iFrame "#".
    - apply (type_lft_morphism_add _ (α ⊓ α') βs (E ++ E'))=>ty.
      + rewrite lft_intersect_list_app -assoc (comm (⊓) α' (ty_lft ty)) assoc.
        iApply lft_intersect_equiv_proper; [iApply Hα|iApply Hα'].
      + rewrite/= !elctx_interp_app HE HE' -!assoc.
        iSplit; iIntros "#H"; repeat iDestruct "H" as "[?H]"; iFrame "#".
    - apply (type_lft_morphism_add _ (α ⊓ α') βs' (E ++ E'))=>ty.
      + rewrite lft_intersect_list_app -assoc.
        iApply lft_intersect_equiv_proper; [iApply Hα|iApply Hα'].
      + by rewrite/= !elctx_interp_app HE HE' -!assoc.
    - apply (type_lft_morphism_const _ (α ⊓ α') (E ++ E'))=>ty.
      + rewrite lft_intersect_list_app.
        iApply lft_intersect_equiv_proper; [iApply Hα|iApply Hα'].
      + by rewrite/= !elctx_interp_app HE HE'.
  Qed.

  Global Instance prod_type_ne {𝔄 𝔅 ℭ} (T: type 𝔄 → type 𝔅) (T': type 𝔄 → type ℭ) :
    TypeNonExpansive T → TypeNonExpansive T' → TypeNonExpansive (λ ty, T ty * T' ty)%T.
  Proof.
    move=> ??. split=>/=; first apply _.
    - move=> *. f_equiv; by apply type_ne_ty_size.
    - move=> *. f_equiv; by apply type_ne_ty_gho_own.
    - move=> *. f_equiv; by apply type_ne_ty_gho_pers.
    - move=> *. f_equiv; by apply type_ne_ty_phys.
  Qed.
  
  Global Instance prod_type_contractive {𝔄 𝔅 ℭ} (T: type 𝔄 → type 𝔅) (T': type 𝔄 → type ℭ) :
    TypeContractive T → TypeContractive T' → TypeContractive (λ ty, T ty * T' ty)%T.
  Proof.
    move=> ??. split=>/=; first apply _.
    - move=> *. f_equiv; by apply type_contractive_ty_size.
    - move=> *. f_equiv; by apply type_contractive_ty_gho_own.
    - move=> *. f_equiv; by apply type_contractive_ty_gho_pers.
    - move=> *. f_equiv; by apply type_contractive_ty_phys.
  Qed.

  Global Instance xprod_type_ne {𝔄 𝔅l} (T: type 𝔄 → typel 𝔅l) :
    ListTypeNonExpansive T → TypeNonExpansive (Π! ∘ T)%T.
  Proof.
    move=> [?[->All]]. clear T. elim All. { rewrite /happly /compose. apply _. }
    move=> ?? T Tl ???. apply (type_ne_ne_compose (mod_ty _ _) _ _ _).
  Qed.
  
  Global Instance xprod_type_contractive {𝔄 𝔅l} (T: type 𝔄 → typel 𝔅l) :
    ListTypeContractive T → TypeContractive (Π! ∘ T)%T.
  Proof.
    move=> [?[->All]]. clear T. elim All. { rewrite /happly /compose. apply _. }
    move=> ?? T Tl ???. apply (type_contractive_compose_left (mod_ty _ _) _ _ _).
  Qed.

  Global Instance prod_copy {𝔄 𝔅} (ty: type 𝔄) (ty': type 𝔅) :
    Copy ty → Copy ty' → Copy (ty * ty').
  Proof.
    move=> C1 C2. split.
    - intros. unfold ty_gho_own, prod_ty. typeclasses eauto.
    - intros x d g tid. iIntros "[G1 G2]".
      iDestruct (copy_concrete with "G1") as "%Conc1".
      iDestruct (copy_concrete with "G2") as "%Conc2".
      iPureIntro. apply all_concrete_app. split; trivial.
  Qed.

  Global Instance prod_send {𝔄 𝔅} (ty: type 𝔄) (ty': type 𝔅) :
    Send ty → Send ty' → Send (ty * ty').
  Proof.
    intros [Hphys1 Hgho1] [Hphys2 Hgho2]. split.
      - intros tid tid' x x'. move=> /=. intros Hsyn. inversion Hsyn.
        rewrite (Hphys1 tid tid' x.1 x'.1); trivial.
        rewrite (Hphys2 tid tid' x.2 x'.2); trivial.
      - intros tid tid' x d g G H κs d0 Hineq TG TH.
        iIntros "#LFT #UNIQ #TIME #Hg H #Gg G [gho1 gho2] #⧖o".
        iApply fupd_step_fupdN_front.
        iMod (fractional.frac_split_guard_in_half with "H Hg") as (γH) "(H1 & H2 & #HgHalf & Hback)"; first by solve_ndisj.
        iMod (fractional.frac_split_in_half (NllftG) with "G") as (γG) "(G1 & G2 & #GgHalf' & Gback)"; first by solve_ndisj.
        iAssert (∀ κ : lft, ⌜κ ∈ κs⌝ -∗ fractional.half γG &&{ ↑NllftG }&&> @[κ])%I as "GgHalf".
          { iIntros (κ) "%Hκ". iApply (guards_transitive with "GgHalf' []").
            iApply "Gg". done. }
        iDestruct (Hgho1 with "LFT UNIQ TIME HgHalf H1 GgHalf G1 gho1 ⧖o") as "gho1"; trivial.
        iDestruct (Hgho2 with "LFT UNIQ TIME HgHalf H2 GgHalf G2 gho2 ⧖o") as "gho2"; trivial.
        iCombine "gho1 gho2" as "gho".
        iModIntro. iApply (step_fupdN_wand with "gho").
        iIntros "[>gho1 >gho2]".
        iDestruct "gho1" as (x'1 off1) "[gho1 [⧖1 [%s1 [G1 H1]]]]".
        iDestruct "gho2" as (x'2 off2) "[gho2 [⧖2 [%s2 [G2 H2]]]]".
        iExists (x'1, x'2), (off1 `max` off2)%nat.
        iDestruct ("Hback" with "H1 H2") as "H". iMod (fupd_mask_mono with "H") as "H"; first solve_ndisj.
        iDestruct ("Gback" with "G1 G2") as "G". iMod (fupd_mask_mono with "G") as "G"; first solve_ndisj.
        iModIntro.
        iDestruct (ty_gho_own_depth_mono with "gho1") as "[$ _]". { lia. } { lia. }
        iDestruct (ty_gho_own_depth_mono with "gho2") as "[$ _]". { lia. } { lia. }
        iCombine "⧖1 ⧖2" as "⧖". iFrame "G H".
        iSplit.
         + iApply (persistent_time_receipt_mono with "⧖"). lia.
         + iPureIntro. destruct x. simpl. rewrite s1. rewrite s2. done.
  Qed.
  
  Global Instance prod_sync {𝔄 𝔅} (ty: type 𝔄) (ty': type 𝔅) :
    Sync ty → Sync ty' → Sync (ty * ty').
  Proof. intros S1 S2. intro tid. intro tid'. intro x. intros d g. 
      destruct (S1 tid tid' (fst x) d g) as [S1p [S1g S1gp]].
      destruct (S2 tid tid' (snd x) d g) as [S2p [S2g S2gp]].
      move=> >/=. split.
      - f_equiv; trivial.
      - split.
        + f_equiv; trivial.
        + f_equiv; trivial.
  Qed.

  Global Instance xprod_copy {𝔄l} (tyl: typel 𝔄l) : ListCopy tyl → Copy (Π! tyl).
  Proof. elim; apply _. Qed.
  
  Global Instance xprod_send {𝔄l} (tyl: typel 𝔄l) : ListSend tyl → Send (Π! tyl).
  Proof. 
    elim.
     - apply _.
     - intros. apply mod_ty_send; last by apply _.
       + intros [x1 xs1] [x2 xs2]. simpl. intros Ha. inversion Ha. trivial.
       + intros [x1 xs1] [x2 xs2]. simpl. intros Ha. inversion Ha. trivial.
  Qed.
  
  Global Instance xprod_sync {𝔄l} (tyl: typel 𝔄l) : ListSync tyl → Sync (Π! tyl).
  Proof. elim; apply _. Qed.
 
  Lemma prod_resolve {𝔄 𝔅} (ty: type 𝔄) (ty': type 𝔅) Φ Φ' E L :
    resolve E L ty Φ → resolve E L ty' Φ' →
    resolve E L (ty * ty') (λ '(a, b), λ π , Φ a π ∧ Φ' b π).
  Proof.
    iIntros (Rslv Rslv' ? vπ ???? Ti Ma) "#LFT #PROPH #UNIQ #TIME #E #L G [T1 T2]".
    
    iMod (fractional.frac_split_guard_in_half NllftG with "G L") as (hγ) "[F1 [F2 [#Ghalf #back]]]". { solve_ndisj. }
    
    iMod (Rslv with "LFT PROPH UNIQ TIME E Ghalf F1 T1") as "ToObs"; [done|].
    iMod (Rslv' with "LFT PROPH UNIQ TIME E Ghalf F2 T2") as "ToObs'"; [done|].
    iCombine "ToObs ToObs'" as "ToObs".
    iModIntro.
    iApply (step_fupdN_wand with "ToObs").
    iIntros "[A B]".
    iMod "A". iMod "B".
    iDestruct "A" as "[A F1]".
    iDestruct "B" as "[B F2]".
    iDestruct ("back" with "F1 F2") as "G".
    iMod (fupd_mask_mono with "G") as "G". { solve_ndisj. }
    iFrame "G".
    iCombine "A B" as "C".
    iModIntro. iApply proph_obs_eq; [|done]=>/= π. destruct x; trivial.
  Qed.

  Lemma prod_resolve_just {𝔄 𝔅} (ty: type 𝔄) (ty': type 𝔅) E L :
    resolve E L ty (const (const True)) → resolve E L ty' (const (const True)) →
    resolve E L (ty * ty') (const (const True)).
  Proof. move=> ??. apply resolve_just. Qed.

  Hint Resolve prod_resolve : lrust_typing.
  
  Lemma xprod_resolve {𝔄l} (tyl: typel 𝔄l) Φl E L :
    resolvel E L tyl Φl →
    resolve E L (Π! tyl) (λ al π, pforall (λ _ '(Φ, a), Φ a π) (pzip Φl al)).
  Proof.
    elim; [eapply resolve_impl; [apply resolve_just|done]|]=>/= *.
    eapply resolve_impl.
     - solve_typing.
     - intros a. intros. destruct a. done.
  Qed.

  Lemma xprod_resolve_just {𝔄l} (tyl: typel 𝔄l) E L :
    HForall (λ _ ty, resolve E L ty (const (const True))) tyl →
    resolve E L (Π! tyl) (const (const True)).
  Proof. move=> ?. apply resolve_just. Qed.

  Lemma prod_subtype {𝔄 𝔅 𝔄' 𝔅'} E L (f : 𝔄 →ₛ 𝔄') (g : 𝔅 →ₛ 𝔅')
                     (ty1: type 𝔄) (ty2: type 𝔅) (ty1': type 𝔄') (ty2': type 𝔅') :
    subtype E L ty1 ty1' f → subtype E L ty2 ty2' g →
    subtype E L (ty1 * ty2) (ty1' * ty2') (prod_mapₛ f g).
  Proof.
    move=> Sub Sub'. iIntros "L".
    iDestruct (Sub with "L") as "#Sub".
    iDestruct (Sub' with "L") as "#Sub'". iIntros "!> #E".
    iDestruct ("Sub" with "E") as (Eq) "(#? & #InOwn & #InOwnPers & %InPhys)".
    iDestruct ("Sub'" with "E") as (?) "(#? & #InOwn' & #InOwnPers' & %InPhys')".
    iSplit=>/=; [|iSplit; [|iSplit; [|iSplit]]].
    - iPureIntro. by f_equal.
    - rewrite !lft_intersect_list_app. by iApply lft_intersect_mono.
    - iModIntro. iIntros "* [A B]".
      iDestruct ("InOwn" with "A") as "[A1 A2]".
      iDestruct ("InOwn'" with "B") as "[B1 B2]".
      iFrame "A1". iFrame "B1". iIntros "[A3 B3]".
      iDestruct ("A2" with "A3") as "A4".
      iDestruct ("B2" with "B3") as "B4".
      iFrame.
    - iModIntro. iIntros "* [A B]".
      iDestruct ("InOwnPers" with "A") as "A1".
      iDestruct ("InOwnPers'" with "B") as "B1".
      iFrame "A1". iFrame "B1".
    - iPureIntro. intros. f_equiv; done.
  Qed.
  
  Lemma prod_eqtype {𝔄 𝔅 𝔄' 𝔅'} E L (f: 𝔄 →ₛ 𝔄') f' (g: 𝔅 →ₛ 𝔅') g'
        (ty1: type 𝔄) (ty2: type  𝔅) (ty1': type 𝔄') (ty2': type 𝔅') :
    eqtype E L ty1 ty1' f f' → eqtype E L ty2 ty2' g g' →
    eqtype E L (ty1 * ty2) (ty1' * ty2') (prod_mapₛ f g) (prod_mapₛ f' g').
  Proof. move=> [??][??]. split; by apply prod_subtype. Qed.
  
  Lemma xprod_subtype {𝔄l 𝔅l} E L (tyl: typel 𝔄l) (tyl': typel 𝔅l) fl :
    subtypel E L tyl tyl' fl → subtype E L (Π! tyl) (Π! tyl') (plist_mapₛ fl).
  Proof.
    move=> Subs. elim Subs. { solve_typing. }
    intros. eapply subtype_eq.
    { apply mod_ty_subtype. by apply prod_subtype. }
    { simpl. unfold cons_prodₛ, to_cons_prodₛ, of_cons_prodₛ, "∘ₛ". simpl.
      unfold to_cons_prod, of_cons_prod, "∘".
      apply extensₛ; simpl; fun_ext; by case.
    }
  Qed.
  
  Lemma xprod_eqtype {𝔄l 𝔅l} E L (tyl: typel 𝔄l) (tyl': typel 𝔅l) fl gl :
    eqtypel E L tyl tyl' fl gl →
    eqtype E L (Π! tyl) (Π! tyl') (plist_mapₛ fl) (plist_mapₛ gl).
  Proof.
    move=> /eqtypel_subtypel[??]. by split; apply xprod_subtype.
  Qed.

  Lemma prod_ty_assoc {𝔄 𝔅 ℭ} E L (ty1: type 𝔄) (ty2: type 𝔅) (ty3: type ℭ) :
    eqtype E L (ty1 * (ty2 * ty3)) ((ty1 * ty2) * ty3) prod_assocₛ prod_assoc'ₛ.
  Proof.
    apply eqtype_unfold.
      { split. apply _. apply _. simpl. { lia. } intros [x0 [x1 x2]]. simpl. rewrite List.app_assoc. trivial. }
    iIntros "*_!>_/=".
    iSplit; [iPureIntro; lia|].
    iSplit; [rewrite (assoc (++)); by iApply lft_equiv_refl|].
    iSplit; [|iSplit].
    - iIntros "!>" (x) "*". iSplit.
      + iIntros "[a [b c]]". destruct x as [x [y z]]. iFrame.
      + iIntros "[[a b] c]". destruct x as [x [y z]]. iFrame.
    - iIntros "!>" (x) "*". iSplit.
      + iIntros "[a [b c]]". destruct x as [x [y z]]. iFrame.
      + iIntros "[[a b] c]". destruct x as [x [y z]]. iFrame.
    - iPureIntro. intros [x [y z]]. intros. rewrite assoc. trivial.
  Qed.
  
  Lemma prod_ty_left_id {𝔄} E L (ty: type 𝔄) :
    eqtype E L (() * ty) ty prod_left_idₛ prod_left_id'ₛ.
  Proof.
    apply eqtype_unfold; [apply _|]. iIntros "*_!>_/=". iSplit; [done|].
    iSplit; [by iApply lft_equiv_refl|].
    iSplit. { iModIntro. iIntros (x d g tid). destruct x as [[]x]. iSplit.
      { iIntros "[_ A]". iFrame "A". } { iIntros "A". iFrame "A". } }
    iSplit. { iModIntro. iIntros (x d g tid). destruct x as [[]x]. iSplit.
      { iIntros "[_ A]". iFrame "A". } { iIntros "A". iFrame "A". } }
    { iPureIntro. intros [[]?] tid. done. }
  Qed.

  Lemma prod_ty_right_id {𝔄} E L (ty: type 𝔄) :
    eqtype E L (ty * ()) ty prod_right_idₛ prod_right_id'ₛ.
  Proof.
    apply eqtype_unfold; [apply _|]. iIntros "*_!>_/=".
    rewrite !right_id. iSplit; [done|]. iSplit; [by iApply lft_equiv_refl|].
    iSplit. { iModIntro. iIntros (x d g tid). destruct x as [x[]]. iSplit.
      { iIntros "[A _]". iFrame "A". } { iIntros "A". iFrame "A". } }
    iSplit. { iModIntro. iIntros (x d g tid). destruct x as [x[]]. iSplit.
      { iIntros "[A _]". iFrame "A". } { iIntros "A". iFrame "A". } }
    { iPureIntro. intros [?[]] tid. rewrite <- app_nil_r. done. }
  Qed.
  
  (*
  Lemma xprod_ty_app_prod {𝔄l 𝔅l} E L (tyl: typel 𝔄l) (tyl': typel 𝔅l) :
    eqtype E L (Π! (tyl h++ tyl')) (Π! tyl * Π! tyl') psep (uncurry papp).
  Proof.
    elim: tyl=> [|> Eq].
    - eapply eqtype_eq.
      + eapply eqtype_trans; [apply eqtype_symm, prod_ty_left_id|].
        apply prod_eqtype; solve_typing.
      + done.
      + done.
    - eapply eqtype_eq.
      + eapply eqtype_trans; [by apply mod_ty_outin, _|].
        eapply eqtype_trans. { eapply prod_eqtype; [solve_typing|apply Eq]. }
        eapply eqtype_trans; [by apply prod_ty_assoc|].
        apply prod_eqtype; solve_typing.
      + fun_ext. by case.
      + fun_ext. by case=> [[??]?].
  Qed.
  *)

  Lemma prod_outlives_E {𝔄 𝔅} (ty: type 𝔄) (ty': type 𝔅) κ :
    ty_outlives_E (ty * ty') κ = ty_outlives_E ty κ ++ ty_outlives_E ty' κ.
  Proof. by rewrite /ty_outlives_E /= fmap_app. Qed.

  Lemma xprod_outlives_E_elctx_sat {𝔄l} E L (tyl: typel 𝔄l) κ:
    elctx_sat E L (tyl_outlives_E tyl κ) → elctx_sat E L (ty_outlives_E (Π! tyl) κ).
  Proof.
    move=> ?. eapply eq_ind; [done|]. rewrite /ty_outlives_E /=.
    elim tyl=>/= [|> IH]; [done|]. by rewrite fmap_app -IH.
  Qed.
End typing.

Global Hint Resolve prod_resolve xprod_resolve | 5 : lrust_typing.
Global Hint Resolve unit_resolve prod_resolve_just xprod_resolve_just
  prod_subtype prod_eqtype xprod_subtype xprod_eqtype
  xprod_outlives_E_elctx_sat : lrust_typing.
