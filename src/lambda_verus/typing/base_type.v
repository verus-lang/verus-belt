From lrust.typing Require Export type.
From guarding Require Import guard tactics.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

(* [base] is a version of the empty type used internally in the model, using an
  arbitrary refinement type. It is used for the base case of the fixpoint
  type. *)

Section base.
  Context `{!typeG Σ}.

  Program Definition base {𝔄} : type 𝔄 := {|
    ty_lfts := [];
    ty_E := [];
    ty_gho_pers x d g tid := False;
    ty_gho_own x d g tid := False;
    ty_gho_res x d g tid := False;
    ty_mty := syn_mty _; ty_val := syn_val; ty_mty_eq := eq_refl; ty_val_eq _ := eq_refl;
    ty_fval := syn_fval; ty_fval_eq _ := eq_refl;
    ty_shr := default_shr (λ x d g tid, False);
  |}%I.
  Next Obligation. by iIntros. Qed.
  Next Obligation. by iIntros. Qed.
  Next Obligation. iIntros. done. Qed.
  Solve All Obligations with solve_default_shr.
  Next Obligation. iIntros "* _ _ _ []". Qed.
  Next Obligation. by iIntros. Qed.
  
  Global Instance base_copy {𝔄} : Copy (@base 𝔄).
  Proof. split=>//.
     - typeclasses eauto.
     - intros. by apply copy_shr_default.
  Qed.

  Global Instance base_send {𝔄} : Send (@base 𝔄).
  Proof. split=>//.
     by iIntros.
  Qed.

  Global Instance base_sync {𝔄} : Sync (@base 𝔄).
  Proof. done. Qed.

  Lemma base_resolve {𝔄} E L Φ : resolve E L (@base 𝔄) Φ.
  Proof. by iIntros. Qed.

  Global Instance base_res_own {𝔄} : ResOwn (@base 𝔄).
  Proof. done. Qed.

  Lemma base_subtype {𝔄 𝔅} (f : 𝔄 →ₛ 𝔅) E L :
    (∀ x, ξl x = ξl ((~~!ₛ) f x)) →
    subtype E L (base) (base) f.
  Proof.
    move=> Eq. iIntros "L". iModIntro. iIntros "E".
    iSplit; [|iSplit; [|iSplit]].
      - iApply lft_incl_refl.
      - iModIntro. iIntros. contradiction.
      - iModIntro. iIntros. contradiction.
      - iApply type_incl_shr_default; [done|done|]. iModIntro. iIntros. contradiction.
  Qed.

  Lemma base_eqtype {𝔄 𝔅} (f : 𝔄 →ₛ 𝔅) (g : 𝔅 →ₛ 𝔄) E L :
    (∀ x, ξl x = ξl ((~~!ₛ) f x)) →
    (∀ x, ξl x = ξl ((~~!ₛ) g x)) →
    eqtype E L (base) (base) f g.
  Proof. split; exact: base_subtype. Qed.

End base.

Global Hint Resolve base_resolve base_subtype base_eqtype : lrust_typing.
