From lrust.util Require Import basic.
From lrust.typing Require Export type.
From guarding Require Import guard.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅 ℭ: syn_type.

Section mod_ty.
  Context `{!typeG Σ}.

(*
  Lemma split_mt_mod_ty {𝔄 𝔅} (f: 𝔄 → 𝔅) ty vπ' d tid l :
    (l ↦∗: λ vl, ∃vπ, ⌜vπ' = f ∘ vπ⌝ ∗ ty.(ty_own) vπ d tid vl) ⊣⊢
    ∃vπ, ⌜vπ' = f ∘ vπ⌝ ∗ l ↦∗: ty.(ty_own) vπ d tid.
  Proof.
    iSplit.
    - iIntros "(%vl &?& %vπ &->&?)". iExists vπ. iSplit; [done|]. iExists vl. iFrame.
    - iIntros "(%vπ &->& %vl & ↦ &?)". iExists vl. iFrame "↦". iExists vπ.
      by iSplit; [done|].
  Qed.
  *)

  Program Definition mod_ty {𝔄 𝔅} (f: 𝔄 →ₛ 𝔅) (fⁱ: 𝔅 →ₛ 𝔄) `{!Isoₛ f fⁱ} (ty: type 𝔄) : type 𝔅 := {|
    ty_size := ty.(ty_size);
    ty_lfts := ty.(ty_lfts);
    ty_E := ty.(ty_E);
    ty_gho_pers x d g tid := ty.(ty_gho_pers) (fⁱ ~~$ₛ x) d g tid ;
    ty_gho_own x d g tid := ty.(ty_gho_own) (fⁱ ~~$ₛ x) d g tid ;
    ty_phys x tid := ty.(ty_phys) (fⁱ ~~$ₛ  x) tid ;
    ty_shr := default_shr (λ x d g tid, ty.(ty_gho_own) (fⁱ ~~$ₛ x) d g tid);
  |}%I.
  Next Obligation. intros. apply ty_size_eq. Qed.
  Next Obligation. intros. rewrite <- ty_size_eq2. inversion Isoₛ0. done. Qed.
  Next Obligation. intros. simpl. rewrite <- ty_phys_eq2. inversion Isoₛ0.
    rewrite (syn_iso_phys_eq ((~~!ₛ) fⁱ x)). by rewrite semi_iso'. Qed.
  Next Obligation. intros. apply ty_gho_own_depth_mono; trivial. Qed.
  Next Obligation. intros. apply ty_gho_pers_depth_mono; trivial. Qed.
  Next Obligation. intros. apply ty_guard_proph. by rewrite <- syn_type_morphism_ξl. Qed.
  Next Obligation. intros. apply ty_gho_pers_impl. Qed.
  Solve All Obligations with solve_default_shr.

  Global Instance mod_ty_ne {𝔄 𝔅} (f: 𝔄 →ₛ 𝔅) (fⁱ: 𝔅 →ₛ 𝔄) `{!Isoₛ f fⁱ} : NonExpansive (mod_ty f fⁱ).
  Proof. solve_ne_type. Qed.
End mod_ty.

Notation "<{ f ; fⁱ }>" := (mod_ty f fⁱ) (format "<{ f ; fⁱ }>"): lrust_type_scope.

Section typing.
  Context `{!typeG Σ}.

  Lemma mod_ty_own' {𝔄 𝔅} fⁱ f `{!@Isoₛ 𝔄 𝔅 f fⁱ} ty x d g tid vl :
    ty_own (<{ f ; fⁱ }> ty) x d g tid vl ⊢ ty_own ty (fⁱ ~~$ₛ x) d g tid vl.
  Proof. iIntros "A". done. Qed.
  
  Lemma mod_ty_own {𝔄 𝔅} fⁱ f `{!@Isoₛ 𝔄 𝔅 f fⁱ} ty x d g tid vl :
    ty_own (<{f;fⁱ}> ty) x d g tid vl ⊣⊢ ty_own ty (fⁱ ~~$ₛ x) d g tid vl.
  Proof.
    done.
  Qed.

  Global Instance mod_ty_type_ne {𝔄 𝔅} `{!@Isoₛ 𝔄 𝔅 f fⁱ} : TypeNonExpansive <{f;fⁱ}>%T.
  Proof.
    split=>/= *; by [apply type_lft_morphism_id_like| |do 3 f_equiv|do 3 f_equiv
      |apply default_shr_contractive].
  Qed.

  Global Instance mod_ty_copy {𝔄 𝔅} `{!@Isoₛ 𝔄 𝔅 f fⁱ} ty : Copy ty → Copy (<{f;fⁱ}> ty).
  Proof.
    intros Hcopy. inversion Hcopy. split.
      - intros. apply copy_persistent.
      - intros. apply copy_concrete.
      - intros. by apply copy_shr_default.
  Qed.

  Global Instance mod_ty_send {𝔄 𝔅} `{!@Isoₛ 𝔄 𝔅 f fⁱ} ty
    (syn_abstract_consistent0 : ∀ x x', syn_abstract x = syn_abstract x' →
        syn_abstract (fⁱ ~~$ₛ x) = syn_abstract (fⁱ ~~$ₛ x'))
    (syn_abstract_consistent1 : ∀ x x', syn_abstract x = syn_abstract x' →
        syn_abstract (f ~~$ₛ x) = syn_abstract (f ~~$ₛ x'))
    : Send ty → Send (<{f;fⁱ}> ty).
  Proof.
    intros Hsend. destruct Hsend as [Hphys Hgho]. split.
     - intros. apply Hphys. apply syn_abstract_consistent0. trivial.
     - iIntros (tid tid' x d g G H1 κs d0 Hineq TG TH)
        "LFT UNIQ TIME Hg H Gg G Gho ⧖".
       iDestruct (Hgho with "LFT UNIQ TIME Hg H Gg G Gho ⧖") as "X"; trivial.
       iApply (step_fupdN_wand with "X"). iIntros ">X". iModIntro.
       iDestruct "X" as (x' off) "[gho [⧖ [%Habs [G H]]]]".
       iExists (f ~~$ₛ x'). iExists off. iFrame. 
       unfold mod_ty. simpl. rewrite semi_iso'. iFrame "gho". iPureIntro.
       have Hs := syn_abstract_consistent1 _ _ Habs. rewrite semi_iso' in Hs.
       trivial.
  Qed.

  Global Instance mod_ty_sync {𝔄 𝔅} `{!@Isoₛ 𝔄 𝔅 f fⁱ} ty : Sync ty → Sync (<{f;fⁱ}> ty).
  Proof.
    intros Hsync. apply sync_default; [done|]. unfold Sync in Hsync. intros tid tid' x d g.
      have Hsync' := Hsync tid tid' (fⁱ ~~$ₛ x) d g. split; [apply Hsync'|split; apply Hsync'].
  Qed.

  Lemma mod_ty_resolve {𝔄 𝔅} E L `{!@Isoₛ 𝔄 𝔅 f fⁱ} ty Φ :
    resolve E L ty Φ → resolve E L (<{f;fⁱ}> ty) (λ b, Φ (fⁱ ~~$ₛ b)).
  Proof.
    intros Hres G F x d g tid Htimeless Hmask. iIntros "#LFT #PROPH #E #GuardsL G Gho".
    iApply (Hres with "LFT PROPH E GuardsL G Gho"). trivial.
  Qed.

  Lemma mod_ty_resolve_just {𝔄 𝔅} E L `{!@Isoₛ 𝔄 𝔅 f fⁱ} ty :
    resolve E L ty (const (const True)) → resolve E L (<{f;fⁱ}> ty) (const (const True)).
  Proof. move=> ?. apply resolve_just. Qed.

  Lemma mod_ty_id {𝔄} (ty: type 𝔄) : <{idₛ;idₛ}>%T ty ≡ ty.
  Proof.
    split; move=>// *; by [rewrite mod_ty_own|rewrite /= ty_shr_default_equiv].
  Qed.

  Lemma mod_ty_compose {𝔄 𝔅 ℭ} `{!@Isoₛ 𝔄 𝔅 f fⁱ} `{!@Isoₛ 𝔅 ℭ g gⁱ} ty :
    (<{g;gⁱ}> (<{f;fⁱ}> ty) ≡ <{g ∘ₛ f ; fⁱ ∘ₛ gⁱ}> ty)%T.
  Proof.
    split=>// *; (iSplit=>/=; [
      iIntros "(%&->& %vπ &->&?)"; iExists vπ; by iFrame|
      iIntros "[%vπ[->?]]"; iExists (f ∘ vπ); (iSplit; [done|]); iExists vπ; by iFrame
    ]).
  Qed.

  Lemma mod_ty_in {𝔄 𝔅} E L `{!@Isoₛ 𝔄 𝔅 f fⁱ} ty : subtype E L ty (<{f;fⁱ}> ty) f.
  Proof.
    iIntros "*_!>_". iSplit; [done|]. iSplit; [by iApply lft_incl_refl|].
    unfold mod_ty; simpl.
    iSplit. { iModIntro. iIntros. rewrite semi_iso'. iFrame. iIntros. done. }
    iSplit. { iModIntro. iIntros. rewrite semi_iso'. done. }
    iSplit. { iPureIntro; intros; rewrite semi_iso'; done. }
    (* TEMPORARY: uses [ty_shr_to_default]; [mod_ty] should pass [ty_shr] through. *)
    iIntros "!>" (κ x d g tid) "Shr".
    iDestruct (ty_shr_to_default with "Shr") as (d0 g0) "[% Guard]".
    iExists d0, g0. rewrite /= semi_iso'. by iFrame.
  Qed.

  Lemma mod_ty_out {𝔄 𝔅} E L f fⁱ `{!@Isoₛ 𝔄 𝔅 f fⁱ} ty :
    subtype E L (<{f;fⁱ}> ty) ty fⁱ.
  Proof.
    iIntros "*_!>_". iSplit; [done|]. iSplit; [by iApply lft_incl_refl|].
    unfold mod_ty; simpl.
    iSplit. { iModIntro. iIntros. iFrame. iIntros. done. }
    iSplit. { iModIntro. iIntros. done. }
    iSplit. { iPureIntro; intros; done. }
    (* TEMPORARY: uses [ty_shr_default_equiv]; [mod_ty] should pass [ty_shr] through. *)
    iIntros "!>" (κ x d g tid) "Shr". iDestruct "Shr" as (d0 g0) "[% Guard]".
    rewrite ty_shr_default_equiv. iExists d0, g0. by iFrame.
  Qed.

  Lemma mod_ty_inout {𝔄 𝔅} E L f fⁱ `{!@Isoₛ 𝔄 𝔅 f fⁱ} ty :
    eqtype E L ty (<{f;fⁱ}> ty) f fⁱ.
  Proof. by split; [apply mod_ty_in|apply mod_ty_out]. Qed.
  
  Lemma mod_ty_outin {𝔄 𝔅} E L f fⁱ `{!@Isoₛ 𝔄 𝔅 f fⁱ} ty :
    eqtype E L (<{f;fⁱ}> ty) ty fⁱ f.
  Proof. by apply eqtype_symm, mod_ty_inout. Qed.
  
  Lemma mod_ty_subtype {𝔄 𝔅 𝔄' 𝔅'} E L (h: 𝔄 →ₛ 𝔄')
      `{!@Isoₛ 𝔄 𝔅 f fⁱ} `{!@Isoₛ 𝔄' 𝔅' g gⁱ} (ty : type 𝔄) (ty' : type 𝔄') :
    subtype E L ty ty' h → subtype E L (<{f;fⁱ}> ty) (<{g;gⁱ}> ty') (g ∘ₛ h ∘ₛ fⁱ).
  Proof.
    move=> ?. eapply subtype_trans; [by apply mod_ty_out|].
    eapply subtype_trans; by [|apply mod_ty_in].
  Qed.
  
  Lemma mod_ty_eqtype {𝔄 𝔅 𝔄' 𝔅'} E L (h: 𝔄 →ₛ 𝔄') (h': 𝔄' →ₛ 𝔄) f fⁱ g gⁱ
      `{!@Isoₛ 𝔄 𝔅 f fⁱ} `{!@Isoₛ 𝔄' 𝔅' g gⁱ} (ty : type 𝔄) (ty' : type 𝔄') :
    eqtype E L ty ty' h h' →
    eqtype E L (<{f;fⁱ}> ty) (<{g;gⁱ}> ty') (g ∘ₛ h ∘ₛ fⁱ) (f ∘ₛ h' ∘ₛ gⁱ).
  Proof.
    move=> [??]. split; by apply mod_ty_subtype.
  Qed.
End typing.

Global Hint Resolve mod_ty_in mod_ty_out mod_ty_inout mod_ty_outin
  | 20 : lrust_typing.
Global Hint Resolve mod_ty_resolve | 5 : lrust_typing.
Global Hint Resolve mod_ty_resolve_just mod_ty_subtype mod_ty_eqtype
  : lrust_typing.
