From lrust.typing Require Export type.
Set Default Proof Using "Type".

(** * Byte layouts of syntactic types (stage 4 of the MiniRust memory model)

[syn_bytes x bs]: the bytes [bs] represent the value [x] of the syntactic type [𝔄]: [x]
has a MiniRust value, and [bs] decode to it at [syn_mty 𝔄]. A type's [ty_bytes] is the
[syn_bytes] of its syntactic type ([ty_bytes_syn]), since [ty_mty] and [ty_val] are
determined by the syntactic type. The lemmas below split the bytes of a value along its
layout: the two halves of a pair ([syn_bytes_pair]), the tag, the payload and the
padding of a variant of a sum ([syn_bytes_sum]); and they characterize the bytes of a
pointer ([syn_bytes_ptr]) and of an integer ([syn_bytes_int]). *)

Implicit Type 𝔄 𝔅: syn_type.

Definition syn_bytes {𝔄} (x: ~~𝔄) (bs: list abyte) : Prop :=
  ∃ v, syn_val x = Some v ∧ decode_value (syn_mty 𝔄) bs = Some v.

Lemma ty_bytes_syn `{!typeG Σ} {𝔄} (ty: type 𝔄) x bs : ty_bytes ty x bs ↔ syn_bytes x bs.
Proof. by rewrite /ty_bytes /syn_bytes -ty_mty_eq -ty_val_eq. Qed.

Lemma syn_bytes_length {𝔄} (x: ~~𝔄) bs : syn_bytes x bs → length bs = syn_bsize 𝔄.
Proof. intros (v & _ & Hd). by eapply decode_value_length. Qed.

(** ** Pairs: the bytes of the first component, then those of the second one. *)
Lemma syn_bytes_pair {𝔄 𝔅} (x: ~~𝔄) (y: ~~𝔅) bs :
  syn_bytes (𝔄:=𝔄 * 𝔅) (x, y) bs ↔
  ∃ bs1 bs2, bs = bs1 ++ bs2 ∧ syn_bytes x bs1 ∧ syn_bytes y bs2.
Proof.
  rewrite /syn_bytes. change (syn_mty (𝔄 * 𝔅)) with (seq_tuple [syn_mty 𝔄; syn_mty 𝔅]).
  change (syn_val (𝔄:=𝔄 * 𝔅) (x, y)) with
    (v₀ ← syn_val x; v₁ ← syn_val y; Some (VTuple [v₀; v₁])).
  split.
  - intros (v & Hv & Hd).
    destruct (syn_val x) as [v1|] eqn:H1; [|done]. destruct (syn_val y) as [v2|] eqn:H2; [|done].
    simpl in Hv. simplify_eq.
    move: Hd. rewrite decode_seq_tuple seq_size_cons seq_size_cons seq_size_nil.
    case_decide as Hlen; [|done]. rewrite /decode_seq.
    destruct (decode_value (syn_mty 𝔄) _) as [w1|] eqn:Hd1; [|done]. simpl.
    destruct (decode_value (syn_mty 𝔅) _) as [w2|] eqn:Hd2; [|done]. simpl.
    intros [= <- <-]. exists (take (mty_size (syn_mty 𝔄)) bs), (drop (mty_size (syn_mty 𝔄)) bs).
    split; [by rewrite take_drop|]. split; [by exists w1|]. exists w2. split; [done|].
    rewrite take_ge in Hd2; [done|]. rewrite length_drop. lia.
  - intros (bs1 & bs2 & -> & (v1 & H1 & Hd1) & (v2 & H2 & Hd2)).
    exists (VTuple [v1; v2]). rewrite H1 H2. split; [done|].
    have Hl1 := decode_value_length _ _ _ Hd1. have Hl2 := decode_value_length _ _ _ Hd2.
    rewrite decode_seq_tuple seq_size_cons seq_size_cons seq_size_nil decide_True;
      [|rewrite length_app; lia].
    rewrite /decode_seq -Hl1 take_app_length drop_app_length Hd1 /= take_ge; [|lia].
    by rewrite Hd2.
Qed.

(** ** Pointers *)
Lemma syn_bytes_at_loc {𝔄} (x: ~~ (at_locₛ 𝔄)) bs :
  syn_bytes x bs ↔ decode_value MPtr bs = Some (VPtr x.1).
Proof. rewrite /syn_bytes /=. split; [by intros (v & [= <-] & ?)|]. eauto. Qed.

Lemma syn_bytes_at_cloc {𝔄} (x: ~~ (at_clocₛ 𝔄)) bs :
  syn_bytes x bs ↔ decode_value MPtr bs = Some (VPtr x.1.1).
Proof. rewrite /syn_bytes /=. split; [by intros (v & [= <-] & ?)|]. eauto. Qed.

Lemma syn_bytes_uniq_bor {𝔄} (l: cloc) x ξi d g idx bs :
  syn_bytes (𝔄:=uniq_borₛ 𝔄) (l, x, ξi, d, g, idx) bs ↔ decode_value MPtr bs = Some (VPtr l.1).
Proof. rewrite /syn_bytes /=. split; [by intros (v & [= <-] & ?)|]. eauto. Qed.

(** ** Integers *)
Lemma syn_bytes_int it (z: Z) bs :
  syn_bytes (𝔄:=intₛ it) z bs ↔ int_in_range it z ∧ decode_value (MInt it) bs = Some (VInt z).
Proof.
  rewrite /syn_bytes /=. case_decide.
  - split; [by intros (v & [= <-] & ?)|]. intros [_ ?]. eauto.
  - split; [by intros (v & ? & _)|]. by intros [].
Qed.

(** The bytes of a pointer. *)
Definition ptr_bytes (l: loc) (bs: list abyte) : Prop := decode_value MPtr bs = Some (VPtr l).

Lemma ptr_bytes_encode l : ptr_bytes l (encode_value MPtr (VPtr l)).
Proof. rewrite /ptr_bytes. apply decode_encode_value; constructor. Qed.

Lemma ptr_bytes_length l bs : ptr_bytes l bs → length bs = PTR_SIZE.
Proof. intros H. by apply decode_value_length in H. Qed.

(** ** Sums: the tag, the payload of the variant, and the padding. *)
Definition sum_max (𝔄l: syn_typel) : nat := list_max (syn_bsize <$> 𝔄l).
Definition sum_tag (𝔄l: syn_typel) : IntType := enum_tag (length 𝔄l).

Lemma syn_bsize_sum 𝔄l : syn_bsize (Σ! 𝔄l) = (int_size (sum_tag 𝔄l) + sum_max 𝔄l)%nat.
Proof.
  rewrite /syn_bsize /= /sum_max /sum_tag length_fmap -list_fmap_compose. done.
Qed.

Lemma sum_max_ge 𝔄l (i: fin (length 𝔄l)) : (syn_bsize (𝔄l !!ₗ i) ≤ sum_max 𝔄l)%nat.
Proof.
  apply (list_max_lookup _ (fin_to_nat i)). rewrite list_lookup_fmap llookup_lookup. done.
Qed.

Lemma syn_val_pinj {𝔄l} (i: fin (length 𝔄l)) (y: ~~(𝔄l !!ₗ i)) pad :
  syn_val (𝔄:=Σ! 𝔄l) (pinj i y, pad) = VVariant (Z.of_nat (fin_to_nat i)) <$> syn_val y.
Proof. by rewrite /= psum_map1_pinj to_xsum_pinj. Qed.

Lemma syn_bytes_sum {𝔄l} (i: fin (length 𝔄l)) (y: ~~(𝔄l !!ₗ i)) pad bs :
  syn_bytes (𝔄:=Σ! 𝔄l) (pinj i y, pad) bs ↔
  ∃ bt bp bq, bs = bt ++ bp ++ bq ∧
    decode_value (MInt (sum_tag 𝔄l)) bt = Some (VInt (Z.of_nat (fin_to_nat i))) ∧
    syn_bytes y bp ∧ length bq = (sum_max 𝔄l - syn_bsize (𝔄l !!ₗ i))%nat.
Proof.
  have Hge := sum_max_ge 𝔄l i.
  have Hvi : (syn_mty <$> 𝔄l) !! fin_to_nat i = Some (syn_mty (𝔄l !!ₗ i)).
  { by rewrite list_lookup_fmap llookup_lookup. }
  rewrite /syn_bytes syn_val_pinj. change (syn_mty (Σ! 𝔄l)) with (seq_enum (syn_mty <$> 𝔄l)).
  rewrite /seq_enum decode_value_enum length_fmap -/(sum_tag 𝔄l).
  rewrite -list_fmap_compose -/(sum_max 𝔄l).
  change (mty_size ∘ syn_mty) with syn_bsize. rewrite -/(sum_max 𝔄l).
  split.
  - intros (v & Hv & Hd). destruct (syn_val y) as [w|] eqn:Hw; [|done]. simpl in Hv. simplify_eq.
    case_decide as Hlen; [|done].
    destruct (decode_int _ _) as [t|] eqn:Ht; [|done]. simpl in Hd.
    case_decide as Ht0; [|done].
    destruct ((syn_mty <$> 𝔄l) !! Z.to_nat t) as [vm|] eqn:Hvm; [|done]. simpl in Hd.
    destruct (decode_value vm _) as [w'|] eqn:Hw'; [|done]. simpl in Hd. simplify_eq.
    rewrite Nat2Z.id Hvi in Hvm. simplify_eq.
    exists (take (int_size (sum_tag 𝔄l)) bs),
      (list_slice (int_size (sum_tag 𝔄l)) (syn_bsize (𝔄l !!ₗ i)) bs),
      (drop (int_size (sum_tag 𝔄l) + syn_bsize (𝔄l !!ₗ i)) bs).
    split; [|split; [|split]].
    + rewrite /list_slice -{1}(take_drop (int_size (sum_tag 𝔄l)) bs). f_equal.
      rewrite -drop_drop. by rewrite take_drop.
    + by rewrite /= Ht.
    + exists w. split; [done|]. done.
    + rewrite length_drop. lia.
  - intros (bt & bp & bq & -> & Ht & (w & Hw & Hp) & Hq). exists (VVariant (Z.of_nat (fin_to_nat i)) w).
    rewrite Hw. split; [done|].
    have Hlt : length bt = int_size (sum_tag 𝔄l).
    { by apply decode_value_length in Ht. }
    have Hlp : length bp = syn_bsize (𝔄l !!ₗ i) by apply decode_value_length in Hp.
    rewrite decide_True; [|rewrite !length_app; lia].
    rewrite -Hlt take_app_length. simpl in Ht. apply fmap_Some in Ht as (t & Hdt & Heq).
    simplify_eq. rewrite Hdt /=.
    rewrite decide_True; [|lia]. rewrite Nat2Z.id Hvi /= /list_slice.
    rewrite drop_app_length. change (mty_size (syn_mty (𝔄l !!ₗ i))) with (syn_bsize (𝔄l !!ₗ i)).
    rewrite -Hlp take_app_length. by rewrite Hp.
Qed.
