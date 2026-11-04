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
[syn_mty (structₛ L 𝔄l)], [struct_mty]); the ghost parts are those of the fields:
[struct_ty L tyl] is [struct_of L (fields_ty tyl)], where [fields_ty tyl : type (Π! 𝔄l)]
is the list of the fields, at the logical type [Π! 𝔄l] (built from [fields_nil_ty] and
[fields_cons_ty]), and [struct_of L] gives a type of fields the bytes of a struct of layout
[L]. The place type of a struct ([StructLty] in [typing/ltype.v]) is likewise a list of
field places ([FieldsLty]) under the layout. *)

Implicit Type 𝔄 𝔅 ℭ 𝔇: syn_type.

Section struct.
  Context `{!typeG Σ}.

  Program Definition fields_nil_ty : type (Π! []) :=
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

  Program Definition fields_cons_ty {𝔄 𝔄l} (ty: type 𝔄) (ty': type (Π! 𝔄l))
      : type (Π! (𝔄 :: 𝔄l)) := {|
    ty_lfts := ty.(ty_lfts) ++ ty'.(ty_lfts);
    ty_E := ty.(ty_E) ++ ty'.(ty_E);
    ty_gho_own x d g tid := ty.(ty_gho_own) (phd x) d g tid ∗ ty'.(ty_gho_own) (ptl x) d g tid;
    ty_gho_res x d g tid := ty.(ty_gho_res) (phd x) d g tid ∗ ty'.(ty_gho_res) (ptl x) d g tid;
    ty_gho_pers x d g tid := ty.(ty_gho_pers) (phd x) d g tid ∗ ty'.(ty_gho_pers) (ptl x) d g tid;
    ty_mty := syn_mty _; ty_val := syn_val; ty_mty_eq := eq_refl; ty_val_eq _ := eq_refl;
    ty_fval := syn_fval; ty_fval_eq _ := eq_refl;
    ty_shr κ x d g tid := ty.(ty_shr) κ (phd x) d g tid ∗ ty'.(ty_shr) κ (ptl x) d g tid;
  |}%I.
  Next Obligation. intros ? ? ty ty' d g d' g'. move=>/= *. iIntros "[A B]".
    iDestruct ((ty_gho_own_depth_mono _ d g d' g') with "A") as "[A A']"; trivial.
    iDestruct ((ty_gho_own_depth_mono _ d g d' g') with "B") as "[B B']"; trivial.
    iFrame. iIntros "[x y]".
    iDestruct ("A'" with "x") as "A'".
    iDestruct ("B'" with "y") as "B'".
    iFrame.
  Qed.
  Next Obligation. intros ? ? ty ty' d g d' g'. move=>/= *. iIntros "[A B]".
    iDestruct ((ty_gho_pers_depth_mono _ d g d' g') with "A") as "A'"; trivial.
    iDestruct ((ty_gho_pers_depth_mono _ d g d' g') with "B") as "B'"; trivial.
    iFrame.
  Qed.
  Next Obligation.
    intros 𝔄 𝔄l ty ty' x d g tid. iIntros "[A B]".
    iDestruct (ty_gho_pers_impl with "A") as "#A1".
    iDestruct (ty_gho_pers_impl with "B") as "#B1".
    iFrame "#".
  Qed.
  Next Obligation.
    intros 𝔄 𝔄l ty ty' κ κ' x n d g tid. simpl. iIntros "#Incl [A B]".
    iSplitL "A"; [iApply (ty_shr_lft_mono ty with "Incl A")|iApply (ty_shr_lft_mono ty' with "Incl B")].
  Qed.
  Next Obligation.
    intros 𝔄 𝔄l ty ty' κ d g d' g' x tid ??. simpl. iIntros "[A B]".
    iSplitL "A"; [iApply (ty_shr_depth_mono ty with "A")|iApply (ty_shr_depth_mono ty' with "B")]; done.
  Qed.
  Next Obligation.
    intros 𝔄 𝔄l ty ty' E κ x d g tid G ??. simpl. iIntros "#LFT #Incl [P1 P2] #Gκ G Bor".
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
    intros 𝔄 𝔄l ty ty' κ [x xs] n d g tid ξ R Hin. simpl.
    iIntros "LFT #Incl [P1 P2] [S1 S2]".
    rewrite /= elem_of_app in Hin. rewrite lft_intersect_list_app.
    destruct Hin as [Hin|Hin].
    - iApply (ty_shr_guard_proph with "LFT [] P1 S1"); [done|].
      iApply (llftl_incl_trans with "Incl"). iApply llftl_intersect_incl_l.
    - iApply (ty_shr_guard_proph with "LFT [] P2 S2"); [done|].
      iApply (llftl_incl_trans with "Incl"). iApply llftl_intersect_incl_r.
  Qed.
  Next Obligation.
    intros 𝔄 𝔄l ty ty' x d g tid. iIntros "[A B]".
    iSplitL "A"; [iApply (ty_gho_res_of_own ty with "A")|iApply (ty_gho_res_of_own ty' with "B")].
  Qed.

  Global Instance fields_cons_ty_ne {𝔄 𝔄l} : NonExpansive2 (@fields_cons_ty 𝔄 𝔄l).
  Proof. solve_ne_type. Qed.

  Fixpoint fields_ty {𝔄l} (tyl: typel 𝔄l) : type (Π! 𝔄l) :=
    match tyl in hlist _ 𝔄l return type (Π! 𝔄l) with
    | +[] => fields_nil_ty
    | ty +:: tyl' => fields_cons_ty ty (fields_ty tyl')
    end.

  Global Instance fields_ty_ne {𝔄l} : NonExpansive (@fields_ty 𝔄l).
  Proof. move=> ???. elim; [done|]=> */=. by f_equiv. Qed.

  Lemma fields_ty_lfts {𝔄l} (tyl: typel 𝔄l) : ty_lfts (fields_ty tyl) = tyl_lfts tyl.
  Proof.
    rewrite /tyl_lfts. induction tyl as [|𝔄 𝔄l ty tyl IH]; [done|]. by rewrite /= IH.
  Qed.

  Lemma fields_ty_E {𝔄l} (tyl: typel 𝔄l) : ty_E (fields_ty tyl) = tyl_E tyl.
  Proof.
    rewrite /tyl_E. induction tyl as [|𝔄 𝔄l ty tyl IH]; [done|]. by rewrite /= IH.
  Qed.

  (** The parts of the fields [tb h++ ta]: those of [tb] and those of [ta]. *)
  Lemma fields_ty_gho_own_app {𝔄lb 𝔄la} (tb: typel 𝔄lb) (ta: typel 𝔄la) x d g tid :
    (fields_ty (tb h++ ta)).(ty_gho_own) x d g tid ⊣⊢
      (fields_ty tb).(ty_gho_own) (psepl x) d g tid ∗
      (fields_ty ta).(ty_gho_own) (psepr x) d g tid.
  Proof.
    induction tb as [|𝔄 𝔄lb ty tb IH] in x |- *; simpl; [by rewrite left_id|].
    destruct x as [x0 x]. by rewrite /= IH assoc.
  Qed.

  Lemma fields_ty_gho_pers_app {𝔄lb 𝔄la} (tb: typel 𝔄lb) (ta: typel 𝔄la) x d g tid :
    (fields_ty (tb h++ ta)).(ty_gho_pers) x d g tid ⊣⊢
      (fields_ty tb).(ty_gho_pers) (psepl x) d g tid ∗
      (fields_ty ta).(ty_gho_pers) (psepr x) d g tid.
  Proof.
    induction tb as [|𝔄 𝔄lb ty tb IH] in x |- *; simpl; [by rewrite left_id|].
    destruct x as [x0 x]. by rewrite /= IH assoc.
  Qed.

  Lemma fields_ty_shr_app {𝔄lb 𝔄la} (tb: typel 𝔄lb) (ta: typel 𝔄la) κ x d g tid :
    (fields_ty (tb h++ ta)).(ty_shr) κ x d g tid ⊣⊢
      (fields_ty tb).(ty_shr) κ (psepl x) d g tid ∗
      (fields_ty ta).(ty_shr) κ (psepr x) d g tid.
  Proof.
    induction tb as [|𝔄 𝔄lb ty tb IH] in x |- *; simpl; [by rewrite left_id|].
    destruct x as [x0 x]. by rewrite /= IH assoc.
  Qed.

  (** A type of fields as a struct of layout [L]. *)
  Program Definition struct_of {𝔄l} (L: struct_layout) (ty: type (Π! 𝔄l)) : type (structₛ L 𝔄l) := {|
    ty_lfts := ty.(ty_lfts);
    ty_E := ty.(ty_E);
    ty_gho_pers x d g tid := ty.(ty_gho_pers) x d g tid ;
    ty_gho_own x d g tid := ty.(ty_gho_own) x d g tid ;
    ty_gho_res x d g tid := ty.(ty_gho_res) x d g tid ;
    ty_mty := syn_mty _; ty_val := syn_val; ty_mty_eq := eq_refl; ty_val_eq _ := eq_refl;
    ty_fval := syn_fval; ty_fval_eq _ := eq_refl;
    ty_shr κ x d g tid := ty.(ty_shr) κ x d g tid;
  |}%I.
  Next Obligation. intros. apply ty_gho_own_depth_mono; trivial. Qed.
  Next Obligation. intros. apply ty_gho_pers_depth_mono; trivial. Qed.
  Next Obligation. intros. apply ty_gho_pers_impl. Qed.
  Next Obligation. intros. apply ty_shr_lft_mono. Qed.
  Next Obligation. intros. by apply ty_shr_depth_mono. Qed.
  Next Obligation. intros. by apply ty_share. Qed.
  Next Obligation. intros. by apply ty_shr_guard_proph. Qed.
  Next Obligation. intros. apply ty_gho_res_of_own. Qed.

  Global Instance struct_of_ne {𝔄l} L : NonExpansive (@struct_of 𝔄l L).
  Proof. solve_ne_type. Qed.

  Definition struct_ty {𝔄l} (L: struct_layout) (tyl: typel 𝔄l) : type (structₛ L 𝔄l) :=
    struct_of L (fields_ty tyl).

  Global Instance struct_ty_ne {𝔄l} L : NonExpansive (@struct_ty 𝔄l L).
  Proof. solve_proper. Qed.

  Lemma struct_ty_lfts {𝔄l} L (tyl: typel 𝔄l) : ty_lfts (struct_ty L tyl) = tyl_lfts tyl.
  Proof. apply fields_ty_lfts. Qed.

  Lemma struct_ty_E {𝔄l} L (tyl: typel 𝔄l) : ty_E (struct_ty L tyl) = tyl_E tyl.
  Proof. apply fields_ty_E. Qed.
End struct.

(** The struct laid out by [repr(C)] ([c_layout]). *)
Notation cstructₛ 𝔄l := (structₛ (c_layout (syn_mty <$> 𝔄l)) 𝔄l).
(** The index of a list of types. *)
Definition typel_idx `{!typeG Σ} {𝔄l} (tyl: typel 𝔄l) : syn_typel := 𝔄l.
Notation cstruct_ty tyl := (struct_ty (c_layout (syn_mty <$> typel_idx tyl)) tyl).

Section typing.
  Context `{!typeG Σ}.

  Global Instance fields_cons_lft_morphism {𝔄 𝔅 𝔅l} (T: type 𝔄 → type 𝔅)
      (T': type 𝔄 → type (Π! 𝔅l)) :
    TypeLftMorphism T → TypeLftMorphism T' → TypeLftMorphism (λ ty, fields_cons_ty (T ty) (T' ty)).
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

  Global Instance fields_cons_type_ne {𝔄 𝔅 𝔅l} (T: type 𝔄 → type 𝔅)
      (T': type 𝔄 → type (Π! 𝔅l)) :
    TypeNonExpansive T → TypeNonExpansive T' →
    TypeNonExpansive (λ ty, fields_cons_ty (T ty) (T' ty)).
  Proof.
    move=> ??. split=>/=; [apply _| | |].
    - move=> *. f_equiv; by apply type_ne_ty_gho_own.
    - move=> *. f_equiv; by apply type_ne_ty_gho_pers.
    - move=> *. f_equiv; by apply type_ne_ty_shr.
  Qed.

  Global Instance fields_cons_type_contractive {𝔄 𝔅 𝔅l} (T: type 𝔄 → type 𝔅)
      (T': type 𝔄 → type (Π! 𝔅l)) :
    TypeContractive T → TypeContractive T' →
    TypeContractive (λ ty, fields_cons_ty (T ty) (T' ty)).
  Proof.
    move=> ??. split=>/=; [apply _| | |].
    - move=> *. f_equiv; by apply type_contractive_ty_gho_own.
    - move=> *. f_equiv; by apply type_contractive_ty_gho_pers.
    - move=> *. f_equiv; by apply type_contractive_ty_shr.
  Qed.

  Global Instance fields_type_ne {𝔄 𝔅l} (T: type 𝔄 → typel 𝔅l) :
    ListTypeNonExpansive T → TypeNonExpansive (fields_ty ∘ T)%T.
  Proof.
    move=> [?[->All]]. clear T. elim All. { rewrite /happly /compose. apply _. }
    move=> ?? T Tl ???. by apply fields_cons_type_ne.
  Qed.

  Global Instance fields_type_contractive {𝔄 𝔅l} (T: type 𝔄 → typel 𝔅l) :
    ListTypeContractive T → TypeContractive (fields_ty ∘ T)%T.
  Proof.
    move=> [?[->All]]. clear T. elim All. { rewrite /happly /compose. apply _. }
    move=> ?? T Tl ???. by apply fields_cons_type_contractive.
  Qed.

  Global Instance struct_of_type_ne {𝔄l} L : TypeNonExpansive (struct_of (𝔄l:=𝔄l) L).
  Proof.
    split=>/= *; by [apply type_lft_morphism_id_like|do 3 f_equiv|do 3 f_equiv|eauto].
  Qed.

  Global Instance struct_type_ne {𝔄 𝔅l} L (T: type 𝔄 → typel 𝔅l) :
    ListTypeNonExpansive T → TypeNonExpansive (struct_ty L ∘ T)%T.
  Proof. intros. apply (type_ne_ne_compose (struct_of L) (fields_ty ∘ T)); apply _. Qed.

  Global Instance struct_type_contractive {𝔄 𝔅l} L (T: type 𝔄 → typel 𝔅l) :
    ListTypeContractive T → TypeContractive (struct_ty L ∘ T)%T.
  Proof. intros. apply (type_contractive_compose_left (struct_of L) (fields_ty ∘ T)); apply _. Qed.

  Global Instance fields_cons_copy {𝔄 𝔄l} (ty: type 𝔄) (ty': type (Π! 𝔄l)) :
    Copy ty → Copy ty' → Copy (fields_cons_ty ty ty').
  Proof.
    move=> C1 C2. split.
    - rewrite /NoCell /=. apply andb_True. split; [apply C1|apply C2].
    - intros. unfold ty_gho_own, fields_cons_ty. typeclasses eauto.
    - intros. iIntros "[S1 S2]".
      iDestruct (copy_shr with "S1") as "#G1". iDestruct (copy_shr with "S2") as "#G2".
      by iApply (guards_sep_pers with "G1 G2").
  Qed.

  Global Instance fields_nil_copy : Copy (fields_nil_ty).
  Proof.
    split. - done. - by apply _. - intros. iIntros. iApply guards_true.
  Qed.

  Global Instance fields_copy {𝔄l} (tyl: typel 𝔄l) : ListCopy tyl → Copy (fields_ty tyl).
  Proof. elim; apply _. Qed.

  Global Instance fields_cons_send {𝔄 𝔄l} (ty: type 𝔄) (ty': type (Π! 𝔄l)) :
    Send ty → Send ty' → Send (fields_cons_ty ty ty').
  Proof. move=> S1 S2 tid tid' x d g /=. f_equiv; [apply S1|apply S2]. Qed.

  Global Instance fields_nil_send : Send (fields_nil_ty).
  Proof. done. Qed.

  Global Instance fields_send {𝔄l} (tyl: typel 𝔄l) : ListSend tyl → Send (fields_ty tyl).
  Proof. elim; apply _. Qed.

  Global Instance fields_cons_send_upd {𝔄 𝔄l} (ty: type 𝔄) (ty': type (Π! 𝔄l)) :
    SendUpd ty → SendUpd ty' → SendUpd (fields_cons_ty ty ty').
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
        iExists (x'1 -:: x'2), (off1 `max` off2)%nat.
        iDestruct ("Hback" with "H1 H2") as "H". iMod (fupd_mask_mono with "H") as "H"; first solve_ndisj.
        iDestruct ("Gback" with "G1 G2") as "G". iMod (fupd_mask_mono with "G") as "G"; first solve_ndisj.
        iModIntro.
        iDestruct (ty_gho_own_depth_mono with "gho1") as "[$ _]". { lia. } { lia. }
        iDestruct (ty_gho_own_depth_mono with "gho2") as "[$ _]". { lia. } { lia. }
        iCombine "⧖1 ⧖2" as "⧖". iFrame "G H".
        iSplit.
         + iApply (persistent_time_receipt_mono with "⧖"). lia.
         + iPureIntro. destruct x. simpl. rewrite s1. simpl in s2. rewrite s2. done.
  Qed.

  Global Instance fields_nil_send_upd : SendUpd (fields_nil_ty).
  Proof. apply send_send_upd, _. Qed.

  Global Instance fields_send_upd {𝔄l} (tyl: typel 𝔄l) :
    ListSendUpd tyl → SendUpd (fields_ty tyl).
  Proof. elim; apply _. Qed.

  Global Instance fields_cons_sync {𝔄 𝔄l} (ty: type 𝔄) (ty': type (Π! 𝔄l)) :
    Sync ty → Sync ty' → Sync (fields_cons_ty ty ty').
  Proof. intros S1 S2. intro tid. intro tid'. intro x. intros d g.
      destruct (S1 tid tid' (phd x) d g) as [S1g [S1gp S1s]].
      destruct (S2 tid tid' (ptl x) d g) as [S2g [S2gp S2s]].
      move=> >/=. split; [|split].
      + f_equiv; trivial.
      + f_equiv; trivial.
      + move=> ?. f_equiv; trivial.
  Qed.

  Global Instance fields_nil_sync : Sync (fields_nil_ty).
  Proof. intros. split; [|split]; trivial. Qed.

  Global Instance fields_sync {𝔄l} (tyl: typel 𝔄l) : ListSync tyl → Sync (fields_ty tyl).
  Proof. elim; apply _. Qed.

  Lemma fields_cons_resolve {𝔄 𝔄l} (ty: type 𝔄) (ty': type (Π! 𝔄l)) Φ Φ' E L' :
    resolve E L' ty Φ → resolve E L' ty' Φ' →
    resolve E L' (fields_cons_ty ty ty') (λ '(a -:: b), λ π , Φ a π ∧ Φ' b π).
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

  Lemma fields_nil_resolve E L' : resolve E L' (fields_nil_ty) (const (const True)).
  Proof. apply resolve_just. Qed.

  Lemma fields_resolve {𝔄l} (tyl: typel 𝔄l) Φl E L' :
    resolvel E L' tyl Φl →
    resolve E L' (fields_ty tyl) (λ al π, pforall (λ _ '(Φ, a), Φ a π) (pzip Φl al)).
  Proof.
    elim; [eapply resolve_impl; [apply resolve_just|done]|]=>/= *.
    eapply resolve_impl.
     - apply fields_cons_resolve; done.
     - intros [a al]. intros. done.
  Qed.

  Global Instance fields_nil_res_own : ResOwn (fields_nil_ty).
  Proof. done. Qed.
  Global Instance fields_cons_res_own {𝔄 𝔄l} (ty: type 𝔄) (ty': type (Π! 𝔄l)) :
    ResOwn ty → ResOwn ty' → ResOwn (fields_cons_ty ty ty').
  Proof. move=> ?? x d g tid /=. by rewrite !res_own. Qed.
  Global Instance fields_res_own {𝔄l} (tyl: typel 𝔄l) :
    TCHForall (λ 𝔄, @ResOwn _ _ 𝔄) tyl → ResOwn (fields_ty tyl).
  Proof. elim; apply _. Qed.

  Lemma fields_cons_resolve_keep {𝔄 𝔄l} (ty: type 𝔄) (ty': type (Π! 𝔄l)) Φ Φ' E L' :
    resolve_keep E L' ty Φ → resolve_keep E L' ty' Φ' →
    resolve_keep E L' (fields_cons_ty ty ty') (λ '(a -:: b), λ π , Φ a π ∧ Φ' b π).
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

  (** The struct instances, from those of the fields. *)
  Global Instance struct_of_copy {𝔄l} L (ty: type (Π! 𝔄l)) : Copy ty → Copy (struct_of L ty).
  Proof.
    intros Hcopy. inversion Hcopy. split.
    - exact copy_nocell.
    - intros. apply copy_persistent.
    - intros. apply copy_shr.
  Qed.

  Global Instance struct_of_send {𝔄l} L (ty: type (Π! 𝔄l)) : Send ty → Send (struct_of L ty).
  Proof. move=> Hsend ?????. apply Hsend. Qed.

  Global Instance struct_of_send_upd {𝔄l} L (ty: type (Π! 𝔄l)) :
    SendUpd ty → SendUpd (struct_of L ty).
  Proof.
    intros [Hgho]. split.
    iIntros (tid tid' x d g G H κs d0 Hineq TG TH) "LFT UNIQ TIME Hg H Gg G Gho ⧖".
    iApply (Hgho with "LFT UNIQ TIME Hg H Gg G Gho ⧖"); trivial.
  Qed.

  Global Instance struct_of_sync {𝔄l} L (ty: type (Π! 𝔄l)) : Sync ty → Sync (struct_of L ty).
  Proof. intros Hsync tid tid' x d g. apply Hsync. Qed.

  Global Instance struct_of_res_own {𝔄l} L (ty: type (Π! 𝔄l)) :
    ResOwn ty → ResOwn (struct_of L ty).
  Proof. move=> ? x d g tid /=. by rewrite res_own. Qed.

  Lemma struct_of_resolve {𝔄l} L (ty: type (Π! 𝔄l)) Φ E L' :
    resolve E L' ty Φ → resolve E L' (struct_of L ty) Φ.
  Proof. done. Qed.

  Lemma struct_of_resolve_keep {𝔄l} L (ty: type (Π! 𝔄l)) Φ E L' :
    resolve_keep E L' ty Φ → resolve_keep E L' (struct_of L ty) Φ.
  Proof. done. Qed.

  Global Instance struct_copy {𝔄l} L (tyl: typel 𝔄l) : ListCopy tyl → Copy (struct_ty L tyl).
  Proof. intros. apply _. Qed.
  Global Instance struct_send {𝔄l} L (tyl: typel 𝔄l) : ListSend tyl → Send (struct_ty L tyl).
  Proof. intros. apply _. Qed.
  Global Instance struct_send_upd {𝔄l} L (tyl: typel 𝔄l) :
    ListSendUpd tyl → SendUpd (struct_ty L tyl).
  Proof. intros. apply _. Qed.
  Global Instance struct_sync {𝔄l} L (tyl: typel 𝔄l) : ListSync tyl → Sync (struct_ty L tyl).
  Proof. intros. apply _. Qed.
  Global Instance struct_res_own {𝔄l} L (tyl: typel 𝔄l) :
    TCHForall (λ 𝔄, @ResOwn _ _ 𝔄) tyl → ResOwn (struct_ty L tyl).
  Proof. intros. apply _. Qed.

  Lemma struct_resolve {𝔄l} L (tyl: typel 𝔄l) Φl E L' :
    resolvel E L' tyl Φl →
    resolve E L' (struct_ty L tyl) (λ al π, pforall (λ _ '(Φ, a), Φ a π) (pzip Φl al)).
  Proof. intros. by apply struct_of_resolve, fields_resolve. Qed.

  Lemma struct_resolve_just {𝔄l} L (tyl: typel 𝔄l) E L' :
    resolve E L' (struct_ty L tyl) (const (const True)).
  Proof. apply resolve_just. Qed.

  (** Subtyping, field-wise. *)
  Lemma struct_mapₛ_fn {𝔄l 𝔅l} L (fl: plist2 (λ 𝔄 𝔅, 𝔄 →ₛ 𝔅) 𝔄l 𝔅l) (x: ~~(structₛ L 𝔄l)) :
    struct_mapₛ L fl ~~$ₛ x = plist_mapₛ fl ~~$ₛ x.
  Proof.
    revert 𝔅l fl. induction 𝔄l as [|𝔄 𝔄l IH]; intros [|𝔅 𝔅l] fl; try done.
    destruct fl as [f fl], x as [x xs]. simpl. by rewrite IH.
  Qed.

  Local Lemma fields_gho_incl {𝔄l 𝔅l} E L' (tyl: typel 𝔄l) (tyl': typel 𝔅l) fl :
    subtypel E L' tyl tyl' fl →
    llctx_interp L' -∗ □ (elctx_interp E -∗
      (ty_lft (fields_ty tyl') ⊑ ty_lft (fields_ty tyl)) ∗
      (□ ∀x d g tid, (fields_ty tyl).(ty_gho_own) x d g tid -∗
         (fields_ty tyl').(ty_gho_own) (plist_mapₛ fl ~~$ₛ x) d g tid ∗
         ((fields_ty tyl').(ty_gho_own) (plist_mapₛ fl ~~$ₛ x) d g tid -∗
           (fields_ty tyl).(ty_gho_own) x d g tid)) ∗
      (□ ∀x d g tid, (fields_ty tyl).(ty_gho_pers) x d g tid -∗
         (fields_ty tyl').(ty_gho_pers) (plist_mapₛ fl ~~$ₛ x) d g tid) ∗
      (□ ∀κ x d g tid, (fields_ty tyl).(ty_shr) κ x d g tid -∗
         (fields_ty tyl').(ty_shr) κ (plist_mapₛ fl ~~$ₛ x) d g tid)).
  Proof.
    induction 1 as [|𝔄 𝔅 𝔄l 𝔅l ty ty' tyl tyl' f fl Sub _ IH].
    - iIntros "_ !> _". iSplit; [by iApply lft_incl_refl|]. iSplit; [|iSplit].
      + iIntros "!>" (x d g tid) "_". iSplit; [done|]. by iIntros.
      + iIntros "!>" (x d g tid) "_". done.
      + iIntros "!>" (κ x d g tid) "_". done.
    - iIntros "L". iDestruct (Sub with "L") as "#Sub". iDestruct (IH with "L") as "#IH".
      iIntros "!> #E".
      iDestruct ("Sub" with "E") as "(_ & #Lft & #InOwn & #InOwnPers & #InShr)".
      iDestruct ("IH" with "E") as "(#Lft' & #InOwn' & #InOwnPers' & #InShr')".
      iSplit; [|iSplit; [|iSplit]]=>/=.
      + rewrite !lft_intersect_list_app. by iApply lft_intersect_mono.
      + iIntros "!>" ([x xs] d g tid) "[A B] /=".
        iDestruct ("InOwn" with "A") as "[A1 A2]".
        iDestruct ("InOwn'" with "B") as "[B1 B2]".
        iFrame "A1 B1". iIntros "[A3 B3]".
        iDestruct ("A2" with "A3") as "$". iApply ("B2" with "B3").
      + iIntros "!>" ([x xs] d g tid) "[A B] /=".
        iSplitL "A"; [by iApply "InOwnPers"|by iApply "InOwnPers'"].
      + iIntros "!>" (κ [x xs] d g tid) "[A B] /=".
        iSplitL "A"; [by iApply "InShr"|by iApply "InShr'"].
  Qed.

  Lemma struct_subtype {𝔄l 𝔅l} E L' L (tyl: typel 𝔄l) (tyl': typel 𝔅l) fl :
    subtypel E L' tyl tyl' fl → subtype E L' (struct_ty L tyl) (struct_ty L tyl') (struct_mapₛ L fl).
  Proof.
    move=> Subs. iIntros "L".
    iDestruct (fields_gho_incl E L' with "L") as "#Gho"; [done|].
    iDestruct (subtypel_llctx_lookup with "L") as "#InTyl"; [done|].
    iIntros "!> #E".
    iAssert ⌜∀ i, syn_bincl (fl -2!! i)⌝%I as %Hb.
    { iSpecialize ("InTyl" with "E"). rewrite bi.pure_forall. iIntros (i).
      by iDestruct ("InTyl" $! i) as "[$ _]". }
    iSplit; [iPureIntro; by apply syn_bincl_struct_map|].
    iDestruct ("Gho" with "E") as "(Lft & #Own & #Pers & #Shr)". rewrite /struct_ty /=.
    iFrame "Lft". setoid_rewrite struct_mapₛ_fn. by iFrame "#".
  Qed.

  Lemma struct_eqtype {𝔄l 𝔅l} E L' L (tyl: typel 𝔄l) (tyl': typel 𝔅l) fl gl :
    eqtypel E L' tyl tyl' fl gl →
    eqtype E L' (struct_ty L tyl) (struct_ty L tyl') (struct_mapₛ L fl) (struct_mapₛ L gl).
  Proof. move=> /eqtypel_subtypel[??]. by split; apply struct_subtype. Qed.

  Lemma struct_outlives_E_elctx_sat {𝔄l} E L' L (tyl: typel 𝔄l) κ:
    elctx_sat E L' (tyl_outlives_E tyl κ) → elctx_sat E L' (ty_outlives_E (struct_ty L tyl) κ).
  Proof.
    move=> ?. eapply eq_ind; [done|]. rewrite /ty_outlives_E /=.
    elim tyl=>/= [|> IH]; [done|]. by rewrite fmap_app -IH.
  Qed.
End typing.

Global Hint Resolve struct_resolve | 5 : lrust_typing.
Global Hint Resolve struct_resolve_just struct_subtype struct_eqtype
  struct_outlives_E_elctx_sat : lrust_typing.
