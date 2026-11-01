From iris.proofmode Require Import proofmode.
From iris.algebra Require Import list numbers.
From lrust.typing Require Import lft_contexts bytes_layout.
From lrust.typing Require Export type.
From guarding Require Import guard tactics guard_later_pers.
From lrust.lifetime Require Import lifetime_full.
From lrust.typing Require Import mod_ty.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅 ℭ 𝔇: syn_type.

Section product.
  Context `{!typeG Σ}.

  Program Definition unit0 : type (Π! []) :=
    {| ty_lfts := [];
       ty_E := [];
       ty_gho_own x d g tid := True%I;
       ty_gho_res x d g tid := True%I;
       ty_gho_pers x d g tid := True%I;
       ty_mty := syn_mty _; ty_val := syn_val; ty_mty_eq := eq_refl; ty_val_eq _ := eq_refl;
       ty_fval := syn_fval; ty_fval_eq _ := eq_refl;
       ty_shr κ x d g tid := True%I;
    |}%I.
  Next Obligation. intros. iIntros. done. Qed.
  Next Obligation. intros. iIntros. done. Qed.
  Next Obligation. iIntros. done. Qed.
  Next Obligation. iIntros. done. Qed.
  Next Obligation. iIntros. done. Qed.
  Next Obligation.
    iIntros. iFrame. iModIntro. iApply step_fupdN_intro; [done|].
    by iApply bi.laterN_intro.
  Qed.
  Next Obligation. intros. set_solver. Qed.
  Next Obligation. by iIntros. Qed.

  Global Instance unit0_copy : Copy unit0.
  Proof.
    split. - by apply _. - intros. iIntros. iApply guards_true.
  Qed.

  Global Instance unit0_send : Send unit0.
  Proof.
    intros. split; trivial. iIntros. iApply step_fupdN_intro; first done. iNext.
    iExists x, 0%nat. iModIntro. iFrame. simpl.
    replace (d0 + 0)%nat with d0 by lia. iFrame "#". done.
  Qed.
  
  Global Instance unit0_sync : Sync unit0.
  Proof. intros. split; [|split]; trivial. Qed.

  Lemma unit0_resolve E L : resolve E L unit0 (const (const True)).
  Proof. apply resolve_just. Qed.

  Program Definition prod_ty {𝔄 𝔅} (ty: type 𝔄) (ty': type 𝔅) : type (𝔄 * 𝔅) := {|
    ty_lfts := ty.(ty_lfts) ++ ty'.(ty_lfts);
    ty_E := ty.(ty_E) ++ ty'.(ty_E);
    ty_gho_own x d g tid := ty.(ty_gho_own) (fst x) d g tid ∗ ty'.(ty_gho_own) (snd x) d g tid;
    ty_gho_res x d g tid := ty.(ty_gho_res) (fst x) d g tid ∗ ty'.(ty_gho_res) (snd x) d g tid;
    ty_gho_pers x d g tid := ty.(ty_gho_pers) (fst x) d g tid ∗ ty'.(ty_gho_pers) (snd x) d g tid;
    ty_mty := syn_mty _; ty_val := syn_val; ty_mty_eq := eq_refl; ty_val_eq _ := eq_refl;
    ty_fval := syn_fval; ty_fval_eq _ := eq_refl;
    ty_shr κ x d g tid := ty.(ty_shr) κ (fst x) d g tid ∗ ty'.(ty_shr) κ (snd x) d g tid;
  |}%I.
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
  Next Obligation.
    intros 𝔄 𝔅 ty ty' x d g tid. iIntros "[A B]".
    iDestruct (ty_gho_pers_impl with "A") as "#A1".
    iDestruct (ty_gho_pers_impl with "B") as "#B1".
    iFrame "#".
  Qed.
  Next Obligation.
    intros. simpl. iIntros "#Incl [A B]". iSplit; by iApply (ty_shr_lft_mono with "Incl").
  Qed.
  Next Obligation.
    intros. simpl. iIntros "[A B]". iSplitL "A"; by iApply (ty_shr_depth_mono with "[$]").
  Qed.
  Next Obligation.
    intros 𝔄 𝔅 ty ty' E κ x d g tid G ??. simpl. iIntros "#LFT #Incl [P1 P2] #Gκ G Bor".
    rewrite lft_intersect_list_app.
    iAssert (κ ⊑ ty_lft ty)%I as "#Incl1".
    { iApply (llftl_incl_trans with "Incl"). iApply llftl_intersect_incl_l. }
    iAssert (κ ⊑ ty_lft ty')%I as "#Incl2".
    { iApply (llftl_incl_trans with "Incl"). iApply llftl_intersect_incl_r. }
    iMod (llftl_sep_split with "LFT Bor") as "[B1 B2]"; [solve_ndisj|].
    iApply (share_par with "Gκ G [P1 B1] [P2 B2]"); [solve_ndisj|..].
    - iIntros (W ?) "#Wκ W". by iApply (ty_share with "LFT Incl1 P1 Wκ W B1").
    - iIntros (W ?) "#Wκ W". by iApply (ty_share with "LFT Incl2 P2 Wκ W B2").
  Qed.
  Next Obligation.
    intros 𝔄 𝔅 ty ty' κ x n d g tid ξ R Hin. simpl.
    iIntros "LFT #Incl [P1 P2] [S1 S2]".
    rewrite elem_of_app in Hin. rewrite lft_intersect_list_app.
    destruct Hin as [Hin|Hin].
    - iApply (ty_shr_guard_proph with "LFT [] P1 S1"); [done|].
      iApply (llftl_incl_trans with "Incl"). iApply llftl_intersect_incl_l.
    - iApply (ty_shr_guard_proph with "LFT [] P2 S2"); [done|].
      iApply (llftl_incl_trans with "Incl"). iApply llftl_intersect_incl_r.
  Qed.
  Next Obligation.
    intros. iIntros "[A B]".
    iSplitL "A"; by iApply ty_gho_res_of_own.
  Qed.

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
    move=> ??. split=>/=; [apply _| | |].
    - move=> *. f_equiv; by apply type_ne_ty_gho_own.
    - move=> *. f_equiv; by apply type_ne_ty_gho_pers.
    - move=> *. f_equiv; by apply type_ne_ty_shr.
  Qed.
  
  Global Instance prod_type_contractive {𝔄 𝔅 ℭ} (T: type 𝔄 → type 𝔅) (T': type 𝔄 → type ℭ) :
    TypeContractive T → TypeContractive T' → TypeContractive (λ ty, T ty * T' ty)%T.
  Proof.
    move=> ??. split=>/=; [apply _| | |].
    - move=> *. f_equiv; by apply type_contractive_ty_gho_own.
    - move=> *. f_equiv; by apply type_contractive_ty_gho_pers.
    - move=> *. f_equiv; by apply type_contractive_ty_shr.
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
    - intros. iIntros "[S1 S2]".
      iDestruct (copy_shr with "S1") as "#G1". iDestruct (copy_shr with "S2") as "#G2".
      by iApply (guards_sep_pers with "G1 G2").
  Qed.

  Global Instance prod_send {𝔄 𝔅} (ty: type 𝔄) (ty': type 𝔅) :
    Send ty → Send ty' → Send (ty * ty').
  Proof.
    intros [Hgho1] [Hgho2]. split.
      intros tid tid' x d g G H κs d0 Hineq TG TH.
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
      destruct (S1 tid tid' (fst x) d g) as [S1g [S1gp S1s]].
      destruct (S2 tid tid' (snd x) d g) as [S2g [S2gp S2s]].
      move=> >/=. split; [|split].
      + f_equiv; trivial.
      + f_equiv; trivial.
      + move=> ?. f_equiv; trivial.
  Qed.

  Global Instance xprod_copy {𝔄l} (tyl: typel 𝔄l) : ListCopy tyl → Copy (Π! tyl).
  Proof. elim; apply _. Qed.
  
  Global Instance xprod_send {𝔄l} (tyl: typel 𝔄l) : ListSend tyl → Send (Π! tyl).
  Proof. 
    elim.
     - apply _.
     - intros. apply mod_ty_send; last by apply _.
       intros [x1 xs1] [x2 xs2]. simpl. intros Ha. inversion Ha. trivial.
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


  Global Instance unit0_res_own : ResOwn unit0.
  Proof. done. Qed.
  Global Instance prod_res_own {𝔄 𝔅} (ty: type 𝔄) (ty': type 𝔅) :
    ResOwn ty → ResOwn ty' → ResOwn (ty * ty').
  Proof. move=> ?? x d g tid /=. by rewrite !res_own. Qed.

  Lemma prod_resolve_keep {𝔄 𝔅} (ty: type 𝔄) (ty': type 𝔅) Φ Φ' E L :
    resolve_keep E L ty Φ → resolve_keep E L ty' Φ' →
    resolve_keep E L (ty * ty') (λ '(a, b), λ π , Φ a π ∧ Φ' b π).
  Proof.
    iIntros (Rslv Rslv' ? vπ ???? Ti Ma) "#LFT #PROPH #UNIQ #TIME #E #L G [T1 T2]".
    iMod (fractional.frac_split_guard_in_half NllftG with "G L")
      as (hγ) "[F1 [F2 [#Ghalf #back]]]"; [solve_ndisj|].
    iMod (Rslv with "LFT PROPH UNIQ TIME E Ghalf F1 T1") as "ToObs"; [done|].
    iMod (Rslv' with "LFT PROPH UNIQ TIME E Ghalf F2 T2") as "ToObs'"; [done|].
    iCombine "ToObs ToObs'" as "ToObs". iModIntro.
    iApply (step_fupdN_wand with "ToObs").
    iIntros "[>(A & F1 & R1) >(B & F2 & R2)]".
    iMod (fupd_mask_mono with "(back F1 F2)") as "$"; [solve_ndisj|].
    iFrame "R1 R2". iCombine "A B" as "C".
    iModIntro. iApply proph_obs_eq; [|done]=>/= π. destruct x; trivial.
  Qed.

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
    iDestruct ("Sub" with "E") as "(%Hb & #? & #InOwn & #InOwnPers & #InShr)".
    iDestruct ("Sub'" with "E") as "(%Hb' & #? & #InOwn' & #InOwnPers' & #InShr')".
    iSplit; [iPureIntro; by apply syn_bincl_prod_map|].
    iSplit=>/=; [|iSplit; [|iSplit]].
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
    - iModIntro. iIntros "* [A B]". iSplitL "A"; [by iApply "InShr"|by iApply "InShr'"].
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
    { apply mod_ty_subtype; [apply syn_bincl_to_cons_prod..|]. by apply prod_subtype. }
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

  Lemma syn_bincl_prod_assoc {𝔄 𝔅 ℭ} : syn_bincl (prod_assocₛ (𝔄:=𝔄) (𝔅:=𝔅) (ℭ:=ℭ)).
  Proof.
    split; [rewrite !syn_bsize_prod; lia|]. intros [x [y z]] R fbs. rewrite /= !syn_fbytes_pair.
    split.
    - intros (f1 & f23 & -> & H1 & H23). apply syn_fbytes_pair in H23 as (f2 & f3 & -> & H2 & H3).
      exists (f1 ++ f2), f3. split; [by rewrite assoc|]. split; [|done].
      apply syn_fbytes_pair. by exists f1, f2.
    - intros (f12 & f3 & -> & H12 & H3). apply syn_fbytes_pair in H12 as (f1 & f2 & -> & H1 & H2).
      exists f1, (f2 ++ f3). split; [by rewrite assoc|]. split; [done|].
      apply syn_fbytes_pair. by exists f2, f3.
  Qed.

  Lemma syn_bincl_prod_left_id {𝔄} : syn_bincl (prod_left_idₛ (𝔄:=𝔄)).
  Proof.
    split; [by rewrite syn_bsize_prod|]. intros [[] x] R fbs. rewrite /= syn_fbytes_pair.
    split.
    - intros (f1 & f2 & -> & H1 & H2). by apply syn_fbytes_zst in H1 as ->.
    - intros H. exists [], fbs. split; [done|]. split; [by apply syn_fbytes_zst|done].
  Qed.

  Lemma syn_bincl_prod_right_id {𝔄} : syn_bincl (prod_right_idₛ (𝔄:=𝔄)).
  Proof.
    split; [rewrite syn_bsize_prod; change (syn_bsize ()) with 0%nat; lia|]. intros [x []] R fbs. rewrite /= syn_fbytes_pair.
    split.
    - intros (f1 & f2 & -> & H1 & H2). apply syn_fbytes_zst in H2 as ->; [|done..].
      by rewrite app_nil_r.
    - intros H. exists fbs, []. rewrite app_nil_r. split; [done|].
      split; [done|by apply syn_fbytes_zst].
  Qed.

  Lemma prod_ty_assoc {𝔄 𝔅 ℭ} E L (ty1: type 𝔄) (ty2: type 𝔅) (ty3: type ℭ) :
    eqtype E L (ty1 * (ty2 * ty3)) ((ty1 * ty2) * ty3) prod_assocₛ prod_assoc'ₛ.
  Proof.
    apply eqtype_unfold.
      { split. apply _. apply _. apply prod_assoc_bsize. apply prod_assoc_bytes. }
      { apply syn_bincl_prod_assoc. }
    iIntros "*_!>_/=".
    iSplit; [rewrite (assoc (++)); by iApply lft_equiv_refl|].
    iSplit; [|iSplit].
    - iIntros "!>" (x) "*". iSplit.
      + iIntros "[a [b c]]". destruct x as [x [y z]]. iFrame.
      + iIntros "[[a b] c]". destruct x as [x [y z]]. iFrame.
    - iIntros "!>" (x) "*". iSplit.
      + iIntros "[a [b c]]". destruct x as [x [y z]]. iFrame.
      + iIntros "[[a b] c]". destruct x as [x [y z]]. iFrame.
    - iIntros "!>" (κ x) "*". iSplit.
      + iIntros "[a [b c]]". destruct x as [x [y z]]. iFrame.
      + iIntros "[[a b] c]". destruct x as [x [y z]]. iFrame.
  Qed.
  
  Lemma prod_ty_left_id {𝔄} E L (ty: type 𝔄) :
    eqtype E L (() * ty) ty prod_left_idₛ prod_left_id'ₛ.
  Proof.
    apply eqtype_unfold; [apply _|apply syn_bincl_prod_left_id|].
    iIntros "*_!>_/=".
    iSplit; [by iApply lft_equiv_refl|].
    iSplit. { iModIntro. iIntros (x d g tid). destruct x as [[]x]. iSplit.
      { iIntros "[_ A]". iFrame "A". } { iIntros "A". iFrame "A". } }
    iSplit. { iModIntro. iIntros (x d g tid). destruct x as [[]x]. iSplit.
      { iIntros "[_ A]". iFrame "A". } { iIntros "A". iFrame "A". } }
    iModIntro. iIntros (κ x d g tid). destruct x as [[]x]. iSplit.
    { iIntros "[_ A]". iFrame "A". } { iIntros "A". iFrame "A". }
  Qed.

  Lemma prod_ty_right_id {𝔄} E L (ty: type 𝔄) :
    eqtype E L (ty * ()) ty prod_right_idₛ prod_right_id'ₛ.
  Proof.
    apply eqtype_unfold; [apply _|apply syn_bincl_prod_right_id|].
    iIntros "*_!>_/=".
    rewrite !right_id. iSplit; [by iApply lft_equiv_refl|].
    iSplit. { iModIntro. iIntros (x d g tid). destruct x as [x[]]. iSplit.
      { iIntros "[A _]". iFrame "A". } { iIntros "A". iFrame "A". } }
    iSplit. { iModIntro. iIntros (x d g tid). destruct x as [x[]]. iSplit.
      { iIntros "[A _]". iFrame "A". } { iIntros "A". iFrame "A". } }
    iModIntro. iIntros (κ x d g tid). destruct x as [x[]]. iSplit.
    { iIntros "[A _]". iFrame "A". } { iIntros "A". iFrame "A". }
  Qed.
  

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
