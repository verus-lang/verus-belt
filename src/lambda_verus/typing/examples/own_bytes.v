(** Tests for stage 3 of the MiniRust memory model: typed [Load]s and [Store]s of the
    pointee of a box that owns bytes ([own_bytes], see [typing/own_bytes.v]), for a pair
    of integers and for [Option<i32>]. *)
From lrust.typing Require Import int product sum own_bytes.
Set Default Proof Using "Type".

Section own_bytes_tests.
  Context `{!typeG Σ}.

  (** ** [Box<(i32, i32)>] *)
  Notation pair_ty := (int_ty i32 * int_ty i32)%T.

  (** The layout: two [i32] fields at offsets 0 and 4. *)
  Lemma pair_ty_mty : pair_ty.(ty_mty) = MTuple [(0%nat, MInt i32); (4%nat, MInt i32)] 8.
  Proof. by rewrite -ty_mty_eq. Qed.

  Lemma pair_ty_val a b :
    int_in_range i32 a → int_in_range i32 b →
    pair_ty.(ty_val) (a, b) = Some (VTuple [VInt a; VInt b]).
  Proof. intros. rewrite -ty_val_eq /=. by rewrite !decide_True. Qed.

  (** Load the pair, store the swapped pair, and load it again. *)
  (** Re-establishes the ownership of a box whose contents have trivial ownership (the
      proof mode unfolds it when it is introduced). *)
  Local Ltac rebuild d g tid :=
    iDestruct "Own" as "(B & F & _)";
    iDestruct (own_bytes_gho_intro _ _ _ _ d g tid with "B F []") as "Own";
    [iNext; repeat iSplit; done|].

  (** Load the pair, store the swapped pair, and load it again. *)
  Lemma test_box_pair_swap n l a b d g tid E :
    ↑naN ⊆ E → int_in_range i32 a → int_in_range i32 b →
    {{{ (own_bytes n pair_ty).(ty_gho_own) (l, (a, b)) (S d) g tid }}}
      Load Na1Ord pair_ty.(ty_mty) #l ;;
      Store Na1Ord pair_ty.(ty_mty) #l (MLit (VTuple [VInt b; VInt a])) ;;
      Load Na1Ord pair_ty.(ty_mty) #l @ E
    {{{ RET MLitV (VTuple [VInt b; VInt a]);
        (own_bytes n pair_ty).(ty_gho_own) (l, (b, a)) (S d) g tid }}}.
  Proof.
    iIntros (? Ha Hb Φ) "Own HΦ". rebuild d g tid.
    wp_bind (Load _ _ _).
    iApply (wp_own_bytes_load n pair_ty l (a, b) _ (S d) g tid with "Own"); [by apply pair_ty_val|].
    iIntros "!> Own". wp_seq. rebuild d g tid.
    wp_bind (Store _ _ _ _).
    iApply (wp_own_bytes_store n pair_ty l (a, b) (b, a) _ d g tid with "[$Own]");
      [done|by apply pair_ty_val|iNext; by iSplit|].
    iIntros "!> [Own _]". wp_seq. rebuild d g tid.
    iApply (wp_own_bytes_load n pair_ty l (b, a) _ (S d) g tid with "Own"); [by apply pair_ty_val|].
    iIntros "!> Own". rebuild d g tid. by iApply "HΦ".
  Qed.

  (** ** [Box<Option<i32>>] *)
  Notation opt_ty := (Σ! +[(); int_ty i32])%T.

  (** The layout: a one-byte tag at offset 0 and the [i32] at offset 1 (as [opt_mty]
      in [lang/minirust_tests.v]). *)
  Lemma opt_ty_mty : opt_ty.(ty_mty) = MEnum [MTuple [] 0; MInt i32] (IntTy false 1) 5.
  Proof. by rewrite -ty_mty_eq. Qed.

  Definition some_i32 (z: Z) : ~~(Σ! [unitₛ; intₛ i32]) := (inr (inl z), []).
  Definition none_i32 : ~~(Σ! [unitₛ; intₛ i32]) := (inl (), []).

  Lemma opt_ty_val_some z :
    int_in_range i32 z → opt_ty.(ty_val) (some_i32 z) = Some (VVariant 1 (VInt z)).
  Proof. intros. rewrite -ty_val_eq /=. by rewrite decide_True. Qed.
  Lemma opt_ty_val_none : opt_ty.(ty_val) none_i32 = Some (VVariant 0 (VTuple [])).
  Proof. by rewrite -ty_val_eq. Qed.

  Lemma opt_ty_bsize : ty_bsize opt_ty = 5%nat.
  Proof. by rewrite /ty_bsize opt_ty_mty. Qed.

  (** [let b = Box::new(Some(5)); let v = *b; *b = None; drop(b); v] *)
  Lemma test_box_option (tid: thread_id) E :
    ↑naN ⊆ E →
    {{{ True }}}
      let: "b" := (let: "l" := Alloc #(ty_bsize opt_ty) in
                   Store Na1Ord opt_ty.(ty_mty) "l" (MLit (VVariant 1 (VInt 5))) ;; "l") in
      let: "v" := Load Na1Ord opt_ty.(ty_mty) "b" in
      Store Na1Ord opt_ty.(ty_mty) "b" (MLit (VVariant 0 (VTuple []))) ;;
      Free #(ty_bsize opt_ty) "b" ;;
      "v" @ E
    {{{ RET MLitV (VVariant 1 (VInt 5)); True }}}.
  Proof.
    iIntros (? Φ) "_ HΦ".
    have Hin : int_in_range i32 5 by apply (bool_decide_unpack _); vm_compute.
    wp_bind (let: "l" := _ in _)%E.
    iApply (wp_own_bytes_new opt_ty (some_i32 5) _ 0 0 tid with "[]");
      [done|by apply opt_ty_val_some|unfold ty_bsize; rewrite -ty_mty_eq /=; lia|done|].
    iIntros "!>" (l) "Own". wp_let. rebuild 0%nat 0%nat tid.
    wp_bind (Load _ _ _).
    iApply (wp_own_bytes_load _ opt_ty l (some_i32 5) _ 1 0 tid with "Own");
      [by apply opt_ty_val_some|].
    iIntros "!> Own". wp_let. rebuild 0%nat 0%nat tid.
    wp_bind (Store _ _ _ _).
    iApply (wp_own_bytes_store _ opt_ty l (some_i32 5) none_i32 _ 0 0 tid with "[$Own]");
      [done|apply opt_ty_val_none|done|].
    iIntros "!> [Own _]". wp_seq. rebuild 0%nat 0%nat tid.
    wp_bind (Free _ _).
    iApply (wp_own_bytes_delete opt_ty l none_i32 0 0 tid with "Own");
      [done|unfold ty_bsize; rewrite -ty_mty_eq /=; lia|].
    iIntros "!> _". wp_seq. by iApply "HΦ".
  Qed.
End own_bytes_tests.

Print Assumptions test_box_pair_swap.
Print Assumptions test_box_option.
