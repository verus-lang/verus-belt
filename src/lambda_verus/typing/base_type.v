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
    ty_size := size_of 𝔄;
    ty_lfts := [];
    ty_E := [];
    ty_gho_pers x d g tid := False;
    ty_gho_own x d g tid := False;
    ty_phys x tid := @syn_phys 𝔄 x;
    ty_shr := default_shr (λ x d g tid, False);
  |}%I.
  Next Obligation. intros. apply syn_phys_size_eq. Qed.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation. by iIntros. Qed.
  Next Obligation. by iIntros. Qed.
  Next Obligation.
    iIntros. iNext. iIntros "_ #G".
    iApply (guards_transitive_additive with "G").
    leaf_by_sep. iIntros "?". iExFalso. done.
  Qed.
  Next Obligation. iIntros. done. Qed.
  Solve All Obligations with solve_default_shr.
  
  Global Instance base_copy {𝔄} : Copy (@base 𝔄).
  Proof. split=>//.
     - typeclasses eauto.
     - iIntros. contradiction.
  Qed.

  Global Instance base_send {𝔄} : Send (@base 𝔄).
  Proof. split=>//.
     - intros. by apply syn_abstract_phys_eq.
     - by iIntros.
  Qed.

  Global Instance base_sync {𝔄} : Sync (@base 𝔄).
  Proof. done. Qed.

  Lemma base_resolve {𝔄} E L Φ : resolve E L (@base 𝔄) Φ.
  Proof. by iIntros. Qed.

  Lemma base_subtype {𝔄 𝔅} (f : 𝔄 →ₛ 𝔅) E L :
    (∀ x, ξl x = ξl ((~~!ₛ) f x)) →
    (size_of 𝔄 = size_of 𝔅) →
    (∀ x, syn_phys x = syn_phys ((~~!ₛ) f x)) →
    subtype E L (base) (base) f.
  Proof.
    move=> Eq Eq2 Eq3. iIntros "L". iModIntro. iIntros "E". iSplit; [|iSplit; [|iSplit; [|iSplit]]].
      - iPureIntro. rewrite <- ty_size_eq2. by rewrite <- ty_size_eq2.
      - iApply lft_incl_refl.
      - iModIntro. iIntros. contradiction.
      - iModIntro. iIntros. contradiction.
      - iPureIntro. simpl. intros. rewrite Eq3. trivial.
  Qed.

  Lemma base_eqtype {𝔄 𝔅} (f : 𝔄 →ₛ 𝔅) (g : 𝔅 →ₛ 𝔄) E L :
    (∀ x, ξl x = ξl ((~~!ₛ) f x)) →
    (∀ x, ξl x = ξl ((~~!ₛ) g x)) →
    (size_of 𝔄 = size_of 𝔅) →
    (∀ x, syn_phys x = syn_phys ((~~!ₛ) f x)) →
    (∀ x, syn_phys x = syn_phys ((~~!ₛ) g x)) →
    eqtype E L (base) (base) f g.
  Proof. split; exact: base_subtype. Qed.

End base.

Global Hint Resolve base_resolve base_subtype base_eqtype : lrust_typing.
