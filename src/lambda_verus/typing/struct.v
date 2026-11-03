From iris.proofmode Require Import proofmode.
From iris.algebra Require Import list numbers.
From lrust.typing Require Import lft_contexts bytes_layout.
From lrust.typing Require Export type.
From guarding Require Import guard tactics guard_later_pers.
From lrust.lifetime Require Import lifetime_full.
Set Default Proof Using "Type".

(** * Structs

[struct_ty L tyl : type (structₛ L 𝔄l)] is a struct with fields of types [tyl], laid out by
the explicit layout [L] (see [design_docs/minirust-layout.md], §7). Its value is the
[plist] of the values of the fields. The layout only determines the bytes (through
[syn_mty (structₛ L 𝔄l)], [struct_mty]); the ghost parts are those of the fields. The type
is built from [struct_nil_ty] and [struct_cons_ty] (a field followed by the struct of the
other fields, at the same layout parameter, whose own layout is irrelevant). *)

Implicit Type 𝔄 𝔅 ℭ 𝔇: syn_type.

Section struct.
  Context `{!typeG Σ}.

  Program Definition struct_nil_ty (L: struct_layout) : type (structₛ L []) :=
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

  Program Definition struct_cons_ty {𝔄 𝔄l} (L: struct_layout) (ty: type 𝔄)
      (ty': type (structₛ L 𝔄l)) : type (structₛ L (𝔄 :: 𝔄l)) := {|
    ty_lfts := ty.(ty_lfts) ++ ty'.(ty_lfts);
    ty_E := ty.(ty_E) ++ ty'.(ty_E);
    ty_gho_own x d g tid := ty.(ty_gho_own) (phd x) d g tid ∗ ty'.(ty_gho_own) (ptl x) d g tid;
    ty_gho_res x d g tid := ty.(ty_gho_res) (phd x) d g tid ∗ ty'.(ty_gho_res) (ptl x) d g tid;
    ty_gho_pers x d g tid := ty.(ty_gho_pers) (phd x) d g tid ∗ ty'.(ty_gho_pers) (ptl x) d g tid;
    ty_mty := syn_mty _; ty_val := syn_val; ty_mty_eq := eq_refl; ty_val_eq _ := eq_refl;
    ty_fval := syn_fval; ty_fval_eq _ := eq_refl;
    ty_shr κ x d g tid := ty.(ty_shr) κ (phd x) d g tid ∗ ty'.(ty_shr) κ (ptl x) d g tid;
  |}%I.
  Next Obligation. intros ? ? ? ty ty' d g d' g'. move=>/= *. iIntros "[A B]".
    iDestruct ((ty_gho_own_depth_mono _ d g d' g') with "A") as "[A A']"; trivial.
    iDestruct ((ty_gho_own_depth_mono _ d g d' g') with "B") as "[B B']"; trivial.
    iFrame. iIntros "[x y]".
    iDestruct ("A'" with "x") as "A'".
    iDestruct ("B'" with "y") as "B'".
    iFrame.
  Qed.
  Next Obligation. intros ? ? ? ty ty' d g d' g'. move=>/= *. iIntros "[A B]".
    iDestruct ((ty_gho_pers_depth_mono _ d g d' g') with "A") as "A'"; trivial.
    iDestruct ((ty_gho_pers_depth_mono _ d g d' g') with "B") as "B'"; trivial.
    iFrame.
  Qed.
  Next Obligation.
    intros 𝔄 𝔄l L ty ty' x d g tid. iIntros "[A B]".
    iDestruct (ty_gho_pers_impl with "A") as "#A1".
    iDestruct (ty_gho_pers_impl with "B") as "#B1".
    iFrame "#".
  Qed.
  Next Obligation.
    intros 𝔄 𝔄l L ty ty' κ κ' x n d g tid. simpl. iIntros "#Incl [A B]".
    iSplitL "A"; [iApply (ty_shr_lft_mono ty with "Incl A")|iApply (ty_shr_lft_mono ty' with "Incl B")].
  Qed.
  Next Obligation.
    intros 𝔄 𝔄l L ty ty' κ d g d' g' x tid ??. simpl. iIntros "[A B]".
    iSplitL "A"; [iApply (ty_shr_depth_mono ty with "A")|iApply (ty_shr_depth_mono ty' with "B")]; done.
  Qed.
  Next Obligation.
    intros 𝔄 𝔄l L ty ty' E κ x d g tid G ??. simpl. iIntros "#LFT #Incl [P1 P2] #Gκ G Bor".
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
    intros 𝔄 𝔄l L ty ty' κ [x xs] n d g tid ξ R Hin. simpl.
    iIntros "LFT #Incl [P1 P2] [S1 S2]".
    rewrite /= elem_of_app in Hin. rewrite lft_intersect_list_app.
    destruct Hin as [Hin|Hin].
    - iApply (ty_shr_guard_proph with "LFT [] P1 S1"); [done|].
      iApply (llftl_incl_trans with "Incl"). iApply llftl_intersect_incl_l.
    - iApply (ty_shr_guard_proph with "LFT [] P2 S2"); [done|].
      iApply (llftl_incl_trans with "Incl"). iApply llftl_intersect_incl_r.
  Qed.
  Next Obligation.
    intros 𝔄 𝔄l L ty ty' x d g tid. iIntros "[A B]".
    iSplitL "A"; [iApply (ty_gho_res_of_own ty with "A")|iApply (ty_gho_res_of_own ty' with "B")].
  Qed.

  Global Instance struct_cons_ty_ne {𝔄 𝔄l} L : NonExpansive2 (@struct_cons_ty 𝔄 𝔄l L).
  Proof. solve_ne_type. Qed.

  Fixpoint struct_ty {𝔄l} (L: struct_layout) (tyl: typel 𝔄l) : type (structₛ L 𝔄l) :=
    match tyl in hlist _ 𝔄l return type (structₛ L 𝔄l) with
    | +[] => struct_nil_ty L
    | ty +:: tyl' => struct_cons_ty L ty (struct_ty L tyl')
    end.

  Global Instance struct_ty_ne {𝔄l} L : NonExpansive (@struct_ty 𝔄l L).
  Proof. move=> ???. elim; [done|]=> */=. by f_equiv. Qed.

  Lemma struct_ty_lfts {𝔄l} L (tyl: typel 𝔄l) : ty_lfts (struct_ty L tyl) = tyl_lfts tyl.
  Proof.
    rewrite /tyl_lfts. induction tyl as [|𝔄 𝔄l ty tyl IH]; [done|]. by rewrite /= IH.
  Qed.

  Lemma struct_ty_E {𝔄l} L (tyl: typel 𝔄l) : ty_E (struct_ty L tyl) = tyl_E tyl.
  Proof.
    rewrite /tyl_E. induction tyl as [|𝔄 𝔄l ty tyl IH]; [done|]. by rewrite /= IH.
  Qed.
End struct.

(** The struct laid out by [repr(C)] ([c_layout]). *)
Notation cstructₛ 𝔄l := (structₛ (c_layout (syn_mty <$> 𝔄l)) 𝔄l).
Notation cstruct_ty tyl := (struct_ty (c_layout (syn_mty <$> _)) tyl).

Section typing.
  Context `{!typeG Σ}.

  Global Instance struct_cons_lft_morphism {𝔄 𝔅 𝔅l} L (T: type 𝔄 → type 𝔅)
      (T': type 𝔄 → type (structₛ L 𝔅l)) :
    TypeLftMorphism T → TypeLftMorphism T' → TypeLftMorphism (λ ty, struct_cons_ty L (T ty) (T' ty)).
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

  Global Instance struct_cons_type_ne {𝔄 𝔅 𝔅l} L (T: type 𝔄 → type 𝔅)
      (T': type 𝔄 → type (structₛ L 𝔅l)) :
    TypeNonExpansive T → TypeNonExpansive T' →
    TypeNonExpansive (λ ty, struct_cons_ty L (T ty) (T' ty)).
  Proof.
    move=> ??. split=>/=; [apply _| | |].
    - move=> *. f_equiv; by apply type_ne_ty_gho_own.
    - move=> *. f_equiv; by apply type_ne_ty_gho_pers.
    - move=> *. f_equiv; by apply type_ne_ty_shr.
  Qed.

  Global Instance struct_cons_type_contractive {𝔄 𝔅 𝔅l} L (T: type 𝔄 → type 𝔅)
      (T': type 𝔄 → type (structₛ L 𝔅l)) :
    TypeContractive T → TypeContractive T' →
    TypeContractive (λ ty, struct_cons_ty L (T ty) (T' ty)).
  Proof.
    move=> ??. split=>/=; [apply _| | |].
    - move=> *. f_equiv; by apply type_contractive_ty_gho_own.
    - move=> *. f_equiv; by apply type_contractive_ty_gho_pers.
    - move=> *. f_equiv; by apply type_contractive_ty_shr.
  Qed.

  Global Instance struct_type_ne {𝔄 𝔅l} L (T: type 𝔄 → typel 𝔅l) :
    ListTypeNonExpansive T → TypeNonExpansive (struct_ty L ∘ T)%T.
  Proof.
    move=> [?[->All]]. clear T. elim All. { rewrite /happly /compose. apply _. }
    move=> ?? T Tl ???. by apply struct_cons_type_ne.
  Qed.

  Global Instance struct_type_contractive {𝔄 𝔅l} L (T: type 𝔄 → typel 𝔅l) :
    ListTypeContractive T → TypeContractive (struct_ty L ∘ T)%T.
  Proof.
    move=> [?[->All]]. clear T. elim All. { rewrite /happly /compose. apply _. }
    move=> ?? T Tl ???. by apply struct_cons_type_contractive.
  Qed.
End typing.
