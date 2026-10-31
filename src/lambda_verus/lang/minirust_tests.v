(** Sanity tests for the MiniRust layer: typed stores followed by typed loads
    of an integer, a pointer, a tuple and an enum, and a byte-level copy
    followed by a load. *)
From lrust.lang Require Import proofmode notation.
Set Default Proof Using "Type".

(** A pair [(i32, *const T)] with the pointer at offset 4. *)
Definition pair_mty : mty := MTuple [(0%nat, MInt i32); (4%nat, MPtr)] (4 + PTR_SIZE).
(** [Option<i32>], with a one-byte tag. *)
Definition opt_mty : mty := MEnum [MTuple [] 0; MInt i32] (IntTy false 1) 5.

Lemma pair_mty_wf : mty_wf pair_mty.
Proof.
  constructor.
  - rewrite /fields_disjoint. intros [|[|i]] [|[|j]] ???? Hij Hi Hj; simplify_eq/=; lia.
  - rewrite !Forall_cons /=. split_and!; [lia|lia|done].
  - rewrite !Forall_cons /=. split_and!; [constructor|constructor|done].
Qed.

Lemma opt_mty_wf : mty_wf opt_mty.
Proof.
  constructor; [|simpl; lia].
  rewrite !Forall_cons /=. split_and!; [lia| |lia|constructor|done].
  constructor; [|done..]. intros ???????. by rewrite lookup_nil.
Qed.

Section tests.
  Context `{!lrustGS Σ}.

  Lemma wp_store_load E l m bs v :
    ↑naN ⊆ E → mty_wf m → val_wf m v → length bs = mty_size m →
    {{{ ▷ l ↦b bs }}}
      Store Na1Ord m (#l) (MLit v) ;; Load Na1Ord m (#l) @ E
    {{{ RET MLitV v; l ↦b encode_value m v }}}.
  Proof.
    iIntros (? Hm Hv Hlen Φ) "Hl HΦ".
    wp_bind (Store _ _ _ _). iApply (wp_store_na with "Hl"); [done..|].
    iIntros "!> Hl". wp_seq.
    iApply (wp_load_na with "Hl"); [by apply decode_encode_value|].
    iIntros "!> Hl". by iApply "HΦ".
  Qed.

  Lemma test_int E l bs :
    ↑naN ⊆ E → length bs = 4%nat →
    {{{ ▷ l ↦b bs }}}
      Store Na1Ord (MInt i32) (#l) (MLit (VInt (-5))) ;; Load Na1Ord (MInt i32) (#l) @ E
    {{{ RET MLitV (VInt (-5)); l ↦b encode_value (MInt i32) (VInt (-5)) }}}.
  Proof.
    intros. apply wp_store_load; [done|constructor|constructor|done].
    apply (bool_decide_unpack _); by vm_compute.
  Qed.

  Lemma test_ptr E l bs l' :
    ↑naN ⊆ E → length bs = PTR_SIZE →
    {{{ ▷ l ↦b bs }}}
      Store Na1Ord MPtr (#l) (MLit (VPtr l')) ;; Load Na1Ord MPtr (#l) @ E
    {{{ RET MLitV (VPtr l'); l ↦b encode_value MPtr (VPtr l') }}}.
  Proof. intros. apply wp_store_load; [done|constructor|constructor|done]. Qed.

  Lemma test_tuple E l bs l' :
    ↑naN ⊆ E → length bs = (4 + PTR_SIZE)%nat →
    {{{ ▷ l ↦b bs }}}
      Store Na1Ord pair_mty (#l) (MLit (VTuple [VInt 7; VPtr l'])) ;;
      Load Na1Ord pair_mty (#l) @ E
    {{{ RET MLitV (VTuple [VInt 7; VPtr l']);
        l ↦b encode_value pair_mty (VTuple [VInt 7; VPtr l']) }}}.
  Proof.
    intros. apply wp_store_load; [done|apply pair_mty_wf| |done].
    repeat constructor. apply (bool_decide_unpack _); by vm_compute.
  Qed.

  Lemma test_enum E l bs :
    ↑naN ⊆ E → length bs = 5%nat →
    {{{ ▷ l ↦b bs }}}
      Store Na1Ord opt_mty (#l) (MLit (VVariant 1 (VInt 42))) ;;
      Load Na1Ord opt_mty (#l) @ E
    {{{ RET MLitV (VVariant 1 (VInt 42));
        l ↦b encode_value opt_mty (VVariant 1 (VInt 42)) }}}.
  Proof.
    intros. apply wp_store_load; [done|apply opt_mty_wf| |done].
    econstructor; [lia|done|..].
    - apply (bool_decide_unpack _); by vm_compute.
    - constructor. apply (bool_decide_unpack _); by vm_compute.
  Qed.

  (** Store a tuple at [l1], copy its bytes to [l2], and load it from [l2]. *)
  Lemma test_memcopy E l1 l2 bs1 bs2 l' :
    ↑naN ⊆ E → length bs1 = (4 + PTR_SIZE)%nat → length bs2 = (4 + PTR_SIZE)%nat →
    {{{ ▷ l1 ↦b bs1 ∗ ▷ l2 ↦b bs2 }}}
      Store Na1Ord pair_mty (#l1) (MLit (VTuple [VInt 7; VPtr l'])) ;;
      MemCopy Na1Ord (4 + PTR_SIZE) (#l2) (#l1) ;;
      Load Na1Ord pair_mty (#l2) @ E
    {{{ RET MLitV (VTuple [VInt 7; VPtr l']);
        l1 ↦b encode_value pair_mty (VTuple [VInt 7; VPtr l']) ∗
        l2 ↦b encode_value pair_mty (VTuple [VInt 7; VPtr l']) }}}.
  Proof.
    iIntros (? Hlen1 Hlen2 Φ) "[Hl1 Hl2] HΦ".
    have Hwf : val_wf pair_mty (VTuple [VInt 7; VPtr l']).
    { repeat constructor. apply (bool_decide_unpack _); by vm_compute. }
    have Hdec := decode_encode_value _ _ pair_mty_wf Hwf.
    have Hlen := length_encode_value pair_mty (VTuple [VInt 7; VPtr l']).
    remember (encode_value pair_mty (VTuple [VInt 7; VPtr l'])) as enc eqn:Henc.
    wp_bind (Store _ _ _ _). iApply (wp_store_na with "Hl1"); [done..|].
    iIntros "!> Hl1". rewrite -Henc. wp_seq.
    wp_bind (MemCopy _ _ _ _). iApply (wp_memcopy with "[$Hl2 $Hl1]"); [done|simpl in *; lia..|].
    iIntros "!> [Hl2 Hl1]". wp_seq.
    iApply (wp_load_na with "Hl2"); [done|].
    iIntros "!> Hl2". iApply "HΦ". iFrame.
  Qed.
End tests.
