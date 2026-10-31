From lrust.typing Require Export type.
From lrust.typing Require Import bool programs.
Set Default Proof Using "Type".
Open Scope Z_scope.

Section int_ty.
  Context `{!typeG Σ}.

  (** The integers of an [IntType] [it]. Its MiniRust type is [MInt it] (of [int_size it]
      bytes), and [ty_val] is [Some (VInt z)] iff [z] is in the range of [it] (see
      [syn_val]). In the legacy word layer it is still one word [#z], of any [z]. *)
  Program Definition int_ty (it: IntType) : type (intₛ it) :=
    {| pt_size := 1;
       pt_gho (z: ~~(intₛ it)) _ := True%I;
       pt_phys (z: ~~(intₛ it)) _ := [ FVal #z ];
    |}.
  Next Obligation. intros. done. Qed.
  Next Obligation. intros. done. Qed.
  Next Obligation. intros. done. Qed.
  Next Obligation. intros. done. Qed.
  Next Obligation. intros. done. Qed.
  Next Obligation. intros. done. Qed.

  Lemma int_ty_mty it : (int_ty it).(ty_mty) = MInt it.
  Proof. by rewrite -ty_mty_eq. Qed.
  Lemma int_ty_val it z :
    int_in_range it z → (int_ty it).(ty_val) z = Some (VInt z).
  Proof. intros. rewrite -ty_val_eq /=. by case_decide. Qed.

  Global Instance int_ty_copy it : Copy (int_ty it).
  Proof.
    split. - typeclasses eauto. - iIntros. iPureIntro. done.
    - intros. by apply copy_shr_default.
  Qed.
End int_ty.

(** The legacy integer type, [isize]; the arithmetic rules below are for it (with
    unbounded results, as before). *)
Notation int := (int_ty isize).

Section int.
  Context `{!typeG Σ}.

  Global Instance int_copy: Copy int.
  Proof.
    split. - typeclasses eauto. - iIntros. iPureIntro. done.
    - intros. by apply copy_shr_default.
  Qed.
  
  Global Instance int_send: Send int.
  Proof.
    intros. split; trivial.
     - intros. unfold syn_abstract in H. subst x'. trivial.
     - iIntros. iApply step_fupdN_intro; first done. iNext.
       iExists x, 0%nat. iModIntro. iFrame. simpl.
       replace (d0 + 0)%nat with d0 by lia. iFrame "#". done.
  Qed.

  Global Instance int_sync: Sync int.
  Proof. apply sync_default; [done|]. split; trivial. split; iSplit; done. Qed.

  Lemma int_resolve E L : resolve E L int (const (const True)).
  Proof. apply resolve_just. Qed.
  
  Program Definition Z_of_boolₛ : boolₛ →ₛ Zₛ := {|
    syn_type_morphism_fn := Z_of_bool ;
    syn_type_morphism_proph_fn := Z_of_bool ;
  |}.
  Next Obligation. intros. done. Qed.
  Next Obligation. intros. done. Qed.

  Lemma bool_ty_to_int E L : subtype E L bool_ty int Z_of_boolₛ.
  Proof.
    apply subtype_plain_type. iIntros "*_!>_/=". iSplit; [done|].
    iSplit; [iApply lft_incl_refl|]. by iIntros.
  Qed.

End int.

Global Hint Resolve int_resolve : lrust_typing.
