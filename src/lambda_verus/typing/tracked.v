From lrust.typing Require Export type.
From lrust.typing Require Import programs bytes_layout.

Set Default Proof Using "Type".

Section tracked.
  Context `{!typeG Σ}.
  
  (* Tracked<T> is just T, zero-sized (its MiniRust type is that of [trackedₛ]) *)
  
  Program Definition tracked_ty {𝔄} (ty: type 𝔄) : type (trackedₛ 𝔄) := {|
    ty_lfts := ty.(ty_lfts);
    ty_E := ty.(ty_E);
    ty_gho_own x d g tid := (ty.(ty_gho_own) x d g tid) ;
    ty_gho_res x d g tid := (ty.(ty_gho_res) x d g tid) ;
    ty_gho_pers x d g tid := (ty.(ty_gho_pers) x d g tid) ;
    ty_mty := syn_mty _; ty_val := syn_val; ty_mty_eq := eq_refl; ty_val_eq _ := eq_refl;
    ty_fval := syn_fval; ty_fval_eq _ := eq_refl;
    ty_shr κ x d g tid := ty.(ty_shr) κ x d g tid;
  |}%I.
  Next Obligation. intros. apply (ty_gho_own_depth_mono ty); trivial. Qed.
  Next Obligation. intros. apply (ty_gho_pers_depth_mono ty); trivial. Qed.
  Next Obligation. intros. apply (ty_gho_pers_impl); trivial. Qed.
  Next Obligation. intros. apply ty_shr_lft_mono. Qed.
  Next Obligation. intros. by apply ty_shr_depth_mono. Qed.
  Next Obligation. intros. by apply ty_share. Qed.
  Next Obligation. intros. by apply ty_shr_guard_proph. Qed.
  Next Obligation. intros. apply (ty_gho_res_of_own ty). Qed.
  
  Global Instance tracked_ne {𝔄} : NonExpansive (@tracked_ty 𝔄).
  Proof. solve_ne_type. Qed.

  Global Instance tracked_send {𝔄} (ty : type 𝔄) : Send ty → Send (tracked_ty ty).
  Proof. intros [Hgho]. split; trivial. Qed.
  
  Global Instance tracked_sync {𝔄} (ty : type 𝔄) : Sync ty → Sync (tracked_ty ty).
  Proof. intros Hsync tid tid' x d g.
    destruct (Hsync tid tid' x d g) as [B [C D]]. split; trivial. split; trivial.
  Qed.
  
  Global Instance tracked_copy {𝔄} (ty : type 𝔄) : Copy ty → Copy (tracked_ty ty).
  Proof.
    intros Hcopy. destruct Hcopy. split; [apply _|trivial..].
  Qed.

  Lemma tracked_resolve {𝔄} (ty: type 𝔄) E L f : resolve E L ty f → resolve E L (tracked_ty ty) f.
  Proof. intros Hresolve. apply Hresolve. Qed.

  Global Instance tracked_res_own {𝔄} (ty: type 𝔄) : ResOwn ty → ResOwn (tracked_ty ty).
  Proof. move=> ? x d g tid /=. by rewrite res_own. Qed.

  Lemma tracked_resolve_keep {𝔄} (ty: type 𝔄) E L f :
    resolve_keep E L ty f → resolve_keep E L (tracked_ty ty) f.
  Proof. intros Hresolve. apply Hresolve. Qed.
  
  (* subtyping *)
  
  Lemma tracked_type_incl {𝔄 𝔅} (ty: type 𝔄) (ty': type 𝔅) f :
    type_incl ty ty' f ⊢ type_incl (tracked_ty ty) (tracked_ty ty') (tracked_mapₛ f).
  Proof.
    iIntros "(_ & #B & #C & #D & #F)". iFrame "B C D F".
    iPureIntro. by apply syn_bincl_same.
  Qed.
  
  Lemma tracked_subtype {𝔄 𝔅} E L (ty: type 𝔄) (ty': type 𝔅) f :
      subtype E L ty ty' f → subtype E L (tracked_ty ty) (tracked_ty ty') (tracked_mapₛ f).
  Proof.
    intros Hsub. iIntros "A". iDestruct (Hsub with "A") as "#B". iModIntro.
    iIntros "E". iApply tracked_type_incl. iApply "B". iFrame.
  Qed.
  
  Lemma tracked_eqtype {𝔄 𝔅} E L (ty: type 𝔄) (ty': type 𝔅) f g :
      eqtype E L ty ty' f g → eqtype E L (tracked_ty ty) (tracked_ty ty') (tracked_mapₛ f) (tracked_mapₛ g).
  Proof.
    intros [Ha Hb]. split; apply tracked_subtype; trivial.
  Qed.
  
End tracked.

Global Hint Resolve tracked_resolve : lrust_typing.
