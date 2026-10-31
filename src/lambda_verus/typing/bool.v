From lrust.typing Require Export type.
From lrust.typing Require Import programs.

Set Default Proof Using "Type".

Section bool.
  Context `{!typeG Σ}.

  Program Definition bool_ty: type boolₛ :=
    {|
      pt_gho (b: ~~boolₛ) _ := True%I ;
    |}%I.
  Next Obligation. move=> *. trivial. Qed.
  Next Obligation. intros. done. Qed.
  
  Global Instance bool_copy: Copy bool_ty.
  Proof.
    split. - typeclasses eauto.
    - intros. by apply copy_shr_default.
  Qed.

  Global Instance bool_send: Send bool_ty.
  Proof.
    intros. split.
     iIntros. iApply step_fupdN_intro; first done. iNext.
       iExists x, 0%nat. iModIntro. iFrame. simpl.
       replace (d0 + 0)%nat with d0 by lia. iFrame "#". done.
  Qed.
  
  Global Instance bool_sync: Sync bool_ty.
  Proof. apply sync_default; [done|]. split; iSplit; done. Qed.

  Lemma bool_resolve E L : resolve E L bool_ty (const (const True)).
  Proof. apply resolve_just. Qed.
  
End bool.

Global Hint Resolve bool_resolve : lrust_typing.
