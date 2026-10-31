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

Lemma syn_bytes_uniq_bor {𝔄} (l: loc) x ξi d g idx bs :
  syn_bytes (𝔄:=uniq_borₛ 𝔄) (l, x, ξi, d, g, idx) bs ↔ decode_value MPtr bs = Some (VPtr l).
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

Lemma syn_val_pinj {𝔄l} (i: fin (length 𝔄l)) (y: ~~(𝔄l !!ₗ i)) :
  syn_val (𝔄:=Σ! 𝔄l) (pinj i y) = VVariant (Z.of_nat (fin_to_nat i)) <$> syn_val y.
Proof. by rewrite /= psum_map1_pinj to_xsum_pinj. Qed.

Lemma syn_bytes_sum {𝔄l} (i: fin (length 𝔄l)) (y: ~~(𝔄l !!ₗ i)) bs :
  syn_bytes (𝔄:=Σ! 𝔄l) (pinj i y) bs ↔
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

(** * Fancy bytes (§10 step 4 of [design_docs/pcell-multibyte-cells.md])

[syn_fbytes R x fbs]: the fancy bytes [fbs] (each a byte-cell or an abstract byte)
represent the value [x], with the static registry [R]: they have the size of [𝔄], and
represent the fancy value of [x] ([syn_fval x], where a cell [pcellₛ m] is its group) at
[syn_mty 𝔄] ([frepr]). For a value with a MiniRust value ([syn_val x = Some v]), and so
for every value of a type without cells ([syn_nocell 𝔄]), these are the plain bytes of
[syn_bytes] ([syn_fbytes_val], [syn_fbytes_nocell]). The lemmas below split fancy bytes
along the layout, as those above do for plain bytes: pairs ([syn_fbytes_pair]) and sums
([syn_fbytes_sum]; the tag and the padding are plain). *)

(** ** Representations at the MiniRust types of products and sums *)
Section frepr_layout.
  Implicit Types (fbs : list (positive + AbstractByte)) (R : gmap positive (mty * list positive)).

  Lemma plain_fbytes fbs :
    (∀ i fb, fbs !! i = Some fb → is_plain fb) → ∃ bs, fbs = inr <$> bs.
  Proof.
    induction fbs as [|fb fbs IH]; intros Hpl; [by exists []|].
    destruct (Hpl 0%nat fb) as [b ->]; [done|]. destruct IH as [bs ->].
    { intros i fb' ?. by apply (Hpl (S i)). }
    by exists (b :: bs).
  Qed.

  Lemma frepr_tuple_iff R fs sz fbs fvs :
    frepr R (MTuple fs sz) fbs (FVTuple fvs) ↔
    length fbs = sz ∧ length fvs = length fs ∧
    (∀ k f fv, fs !! k = Some f → fvs !! k = Some fv →
       frepr R f.2 (list_slice f.1 (mty_size f.2) fbs) fv) ∧
    (∀ i fb, fbs !! i = Some fb → ¬ in_field fs i → is_plain fb).
  Proof.
    split.
    - intros Hrep. destruct (frepr_tuple_inv _ _ _ _ _ Hrep) as (? & ? & ?).
      split_and!; [done|done| |done]. intros. by eapply frepr_field.
    - intros (? & ? & ? & ?). by apply frepr_tuple.
  Qed.

  Lemma frepr_enum_iff R vars tag sz fbs t d :
    frepr R (MEnum vars tag sz) fbs (FVVariant t d) ↔
    length fbs = sz ∧ (∃ bst, take (int_size tag) fbs = inr <$> bst ∧ decode_int tag bst = Some t) ∧
    (0 ≤ t)%Z ∧ ∃ vm, vars !! Z.to_nat t = Some vm ∧
      frepr R vm (list_slice (int_size tag) (mty_size vm) fbs) d ∧
      (∀ i fb, fbs !! i = Some fb → (int_size tag + mty_size vm ≤ i)%nat → is_plain fb).
  Proof.
    split.
    - intros Hrep. destruct (frepr_enum_inv _ _ _ _ _ _ _ Hrep)
        as (? & ? & ? & vm & Hvm & ?).
      split_and!; [done|done|done|]. exists vm. split_and!; [done| |done].
      by eapply frepr_payload.
    - intros (? & (bst & ? & ?) & ? & vm & ? & ? & ?). by eapply frepr_enum.
  Qed.

  Lemma layout_fields_shift a o ms :
    layout_fields (a + o) ms = (λ f : nat * mty, ((a + f.1)%nat, f.2)) <$> layout_fields o ms.
  Proof.
    revert o. induction ms as [|m ms IH]; intros o; [done|]. simpl. f_equal.
    by rewrite -Nat.add_assoc IH.
  Qed.

  Lemma in_field_layout o ms i :
    (o ≤ i < o + seq_size ms)%nat → in_field (layout_fields o ms) i.
  Proof.
    revert o. induction ms as [|m ms IH]; intros o Hi; [rewrite seq_size_nil in Hi; lia|].
    rewrite seq_size_cons in Hi. destruct (decide (i < o + mty_size m)%nat).
    - exists (o, m). split; [by left|simpl; lia].
    - destruct (IH (o + mty_size m)%nat) as (f & Hf & Hfi); [lia|].
      exists f. split; [by right|done].
  Qed.

  Lemma list_slice_drop {A} a o n (l : list A) :
    list_slice o n (drop a l) = list_slice (a + o) n l.
  Proof. by rewrite /list_slice drop_drop. Qed.

  Lemma list_slice_app_r {A} o n (l1 l2 : list A) :
    list_slice (length l1 + o) n (l1 ++ l2) = list_slice o n l2.
  Proof. by rewrite -list_slice_drop drop_app_length. Qed.

  (** A [seq_tuple] has no padding: its representations are those of its fields. *)
  Lemma frepr_seq_tuple R ms fbs fvs :
    frepr R (seq_tuple ms) fbs (FVTuple fvs) ↔
    length fbs = seq_size ms ∧ length fvs = length ms ∧
    ∀ k f fv, layout_fields 0 ms !! k = Some f → fvs !! k = Some fv →
      frepr R f.2 (list_slice f.1 (mty_size f.2) fbs) fv.
  Proof.
    rewrite /seq_tuple frepr_tuple_iff.
    have Hlf : length (layout_fields 0 ms) = length ms.
    { by rewrite -(length_fmap snd) layout_fields_snd. }
    split.
    - intros (? & ? & ? & _). rewrite -Hlf. done.
    - intros (Hlen & ? & ?). split_and!; [done|by rewrite Hlf|done|].
      intros i fb Hi Hn. exfalso. apply Hn, in_field_layout.
      apply lookup_lt_Some in Hi. lia.
  Qed.

  Lemma frepr_seq_tuple_nil R fbs fvs :
    frepr R (seq_tuple []) fbs (FVTuple fvs) ↔ fbs = [] ∧ fvs = [].
  Proof.
    rewrite frepr_seq_tuple seq_size_nil. split.
    - intros (Hl & Hv & _). by split; apply nil_length_inv.
    - intros [-> ->]. split_and!; [done|done|]. by intros ? ? ? ?.
  Qed.

  Lemma frepr_seq_tuple_cons R m ms fbs fv fvs :
    frepr R (seq_tuple (m :: ms)) fbs (FVTuple (fv :: fvs)) ↔
    ∃ fbs1 fbs2, fbs = fbs1 ++ fbs2 ∧ length fbs1 = mty_size m ∧
      frepr R m fbs1 fv ∧ frepr R (seq_tuple ms) fbs2 (FVTuple fvs).
  Proof.
    rewrite frepr_seq_tuple seq_size_cons /=.
    rewrite -(Nat.add_0_r (mty_size m)) layout_fields_shift Nat.add_0_r.
    split.
    - intros (Hlen & Hlv & Hf).
      exists (take (mty_size m) fbs), (drop (mty_size m) fbs).
      split; [by rewrite take_drop|]. split; [rewrite length_take; lia|].
      split; [|apply frepr_seq_tuple; split_and!; [rewrite length_drop; lia|lia|]].
      + have := Hf 0%nat (0%nat, m) fv eq_refl eq_refl. by rewrite /list_slice drop_0.
      + intros k f fv' Hk Hfv. rewrite list_slice_drop.
        have := Hf (S k) ((mty_size m + f.1)%nat, f.2) fv'. simpl.
        rewrite list_lookup_fmap Hk. by intros H; apply H.
    - intros (fbs1 & fbs2 & -> & Hl1 & H1 & H2).
      apply frepr_seq_tuple in H2 as (Hl2 & Hlv & Hf).
      split; [rewrite length_app; lia|]. split; [simpl; lia|].
      intros [|k] f fv'; simpl.
      + intros [= <-] [= <-]. simpl. by rewrite /list_slice drop_0 -Hl1 take_app_length.
      + rewrite list_lookup_fmap. intros (f' & Hk & ->)%fmap_Some_1 Hfv. simpl.
        rewrite -Hl1 list_slice_app_r. by eapply Hf.
  Qed.
End frepr_layout.

(** ** Fancy values of syntactic types *)

(** A value with a MiniRust value has no cells: its fancy value is the MiniRust value. *)
Lemma syn_fval_val {𝔄} (x: ~~𝔄) v : syn_val x = Some v → syn_fval x = Some (fv_lift v).
Proof.
  move: 𝔄 x v. fix FIX 1. move=> 𝔄 x v. destruct 𝔄; simpl;
    try (clear FIX; intros H; first [by rewrite H|destruct x; by simplify_eq/=
      |case_decide; by simplify_eq/=|by simplify_eq/=]).
  - destruct x as [x₀ x₁].
    destruct (syn_val x₀) as [v₀|] eqn:H₀; [|done]. destruct (syn_val x₁) as [v₁|] eqn:H₁; [|done].
    simpl. intros [= <-]. by rewrite (FIX _ _ _ H₀) (FIX _ _ _ H₁).
  - intros (vs & Hvs & ->)%fmap_Some_1.
    assert (∀ vs, mapM id (plist_to_list (pmap (λ _ x0, syn_val x0) x)) = Some vs →
      mapM id (plist_to_list (pmap (λ _ x0, syn_fval x0) x)) = Some (map fv_lift vs)) as Hall.
    { clear Hvs vs. induction l as [|𝔄 l IH]; intros vs.
      { simpl. by intros [= <-]. }
      destruct x as [x xl]. simpl.
      destruct (syn_val x) as [w|] eqn:Hw; [|done]. simpl.
      destruct (mapM id (plist_to_list (pmap (λ _ x0, syn_val x0) xl))) as [ws|] eqn:Hws;
        [|done].
      simpl. intros [= <-]. by rewrite (FIX _ _ _ Hw) (IH xl ws Hws). }
    clear FIX. by rewrite (Hall vs Hvs).
  - assert (∀ (i: fin (length l)) (x0 : ~~ (l !!ₗ i)) w,
      syn_val x0 = Some w → syn_fval x0 = Some (fv_lift w)) as Hall.
    { clear x. induction l as [|𝔄0 l IH]; intros i; [inv_fin i|].
      inv_fin i; [intros x0 w; by apply (FIX _ x0)|by apply IH]. }
    clear FIX.
    replace x with (of_xsum (to_xsum x)); last by rewrite semi_iso'.
    destruct (to_xsum x) as [i x0]. simpl. rewrite !psum_map1_pinj !to_xsum_pinj.
    intros (w & Hw & ->)%fmap_Some_1. by rewrite (Hall i x0 w Hw).
Qed.

Lemma syn_fval_pinj {𝔄l} (i: fin (length 𝔄l)) (y: ~~(𝔄l !!ₗ i)) :
  syn_fval (𝔄:=Σ! 𝔄l) (pinj i y) = FVVariant (Z.of_nat (fin_to_nat i)) <$> syn_fval y.
Proof. by rewrite /= psum_map1_pinj to_xsum_pinj. Qed.

(** ** Fancy bytes of syntactic types ([syn_fbytes], [typing/type.v]) *)

Lemma ty_fbytes_syn `{!typeG Σ} {𝔄} (ty: type 𝔄) R x fbs :
  ty_fbytes R ty x fbs ↔ syn_fbytes R x fbs.
Proof. rewrite /ty_fbytes /syn_fbytes ty_bsize_eq -ty_mty_eq. by setoid_rewrite <-ty_fval_eq. Qed.

Lemma syn_fbytes_length {𝔄} R (x: ~~𝔄) fbs : syn_fbytes R x fbs → length fbs = syn_bsize 𝔄.
Proof. by intros [? _]. Qed.

Lemma syn_fbytes_mono {𝔄} R R' (x: ~~𝔄) fbs : R ⊆ R' → syn_fbytes R x fbs → syn_fbytes R' x fbs.
Proof. intros ? (? & fv & ? & ?). split; [done|]. exists fv. split; [done|]. by eapply frepr_mono. Qed.

(** Plain bytes are fancy bytes. *)
Lemma syn_fbytes_bytes {𝔄} R (x: ~~𝔄) bs : syn_bytes x bs → syn_fbytes R x (inr <$> bs).
Proof.
  intros (v & Hv & Hd). split; [rewrite length_fmap; by eapply decode_value_length|].
  exists (fv_lift v). split; [by apply syn_fval_val|]. by apply frepr_plain.
Qed.

(** The reduction lemmas: the fancy bytes of a value with a MiniRust value, or of a value of
    a type without cells, are plain bytes. *)
Lemma syn_fbytes_val {𝔄} R (x: ~~𝔄) fbs v :
  syn_val x = Some v → syn_fbytes R x fbs ↔ ∃ bs, fbs = inr <$> bs ∧ syn_bytes x bs.
Proof.
  intros Hv. split.
  - intros (_ & fv & Hfv & Hrep). rewrite (syn_fval_val _ _ Hv) in Hfv. injection Hfv as <-.
    destruct (frepr_lift _ _ _ _ Hrep) as (bs & -> & Hd). exists bs. split; [done|].
    by exists v.
  - intros (bs & -> & Hbs). by apply syn_fbytes_bytes.
Qed.

Lemma syn_fbytes_nocell {𝔄} R (x: ~~𝔄) fbs :
  syn_nocell 𝔄 → syn_fbytes R x fbs ↔ ∃ bs, fbs = inr <$> bs ∧ syn_bytes x bs.
Proof.
  intros Hnc. destruct (syn_val x) as [v|] eqn:Hv; [by eapply syn_fbytes_val|]. split.
  - intros (_ & fv & Hfv & _). by rewrite syn_fval_nocell // Hv in Hfv.
  - intros (bs & _ & (v & Hv' & _)). congruence.
Qed.

(** *** Pairs *)
Lemma syn_fbytes_pair {𝔄 𝔅} R (x: ~~𝔄) (y: ~~𝔅) fbs :
  syn_fbytes (𝔄:=𝔄 * 𝔅) R (x, y) fbs ↔
  ∃ fbs1 fbs2, fbs = fbs1 ++ fbs2 ∧ syn_fbytes R x fbs1 ∧ syn_fbytes R y fbs2.
Proof.
  rewrite /syn_fbytes /syn_bsize. change (syn_mty (𝔄 * 𝔅)) with (seq_tuple [syn_mty 𝔄; syn_mty 𝔅]).
  change (syn_fval (𝔄:=𝔄 * 𝔅) (x, y)) with
    (fv₀ ← syn_fval x; fv₁ ← syn_fval y; Some (FVTuple [fv₀; fv₁])).
  rewrite mty_size_seq_tuple !seq_size_cons seq_size_nil.
  split.
  - intros (Hlen & fv & Hfv & Hrep).
    destruct (syn_fval x) as [fv₀|] eqn:H₀; [|done]. destruct (syn_fval y) as [fv₁|] eqn:H₁; [|done].
    simpl in Hfv. injection Hfv as <-.
    apply frepr_seq_tuple_cons in Hrep as (fbs1 & fbs' & -> & Hl1 & Hr1 & Hrep).
    apply frepr_seq_tuple_cons in Hrep as (fbs2 & fbs3 & -> & Hl2 & Hr2 & Hrep).
    apply frepr_seq_tuple_nil in Hrep as [-> _].
    exists fbs1, fbs2. rewrite app_nil_r. split; [done|].
    split; split; [done| |done|]; eauto.
  - intros (fbs1 & fbs2 & -> & (Hl1 & fv₀ & H₀ & Hr1) & (Hl2 & fv₁ & H₁ & Hr2)).
    split; [rewrite length_app; lia|]. rewrite H₀ H₁ /=. eexists. split; [done|].
    apply frepr_seq_tuple_cons. exists fbs1, fbs2. split_and!; [done|done|done|].
    apply frepr_seq_tuple_cons. exists fbs2, []. rewrite app_nil_r. split_and!; [done|done|done|].
    by apply frepr_seq_tuple_nil.
Qed.

(** *** Sums: the tag and the padding are plain bytes. *)
Lemma syn_fbytes_sum {𝔄l} R (i: fin (length 𝔄l)) (y: ~~(𝔄l !!ₗ i)) fbs :
  syn_fbytes (𝔄:=Σ! 𝔄l) R (pinj i y) fbs ↔
  ∃ bt fp bq, fbs = (inr <$> bt) ++ fp ++ (inr <$> bq) ∧
    decode_value (MInt (sum_tag 𝔄l)) bt = Some (VInt (Z.of_nat (fin_to_nat i))) ∧
    syn_fbytes R y fp ∧ length bq = (sum_max 𝔄l - syn_bsize (𝔄l !!ₗ i))%nat.
Proof.
  have Hge := sum_max_ge 𝔄l i.
  have Hvi : (syn_mty <$> 𝔄l) !! fin_to_nat i = Some (syn_mty (𝔄l !!ₗ i)).
  { by rewrite list_lookup_fmap llookup_lookup. }
  rewrite /syn_fbytes syn_fval_pinj syn_bsize_sum.
  change (syn_mty (Σ! 𝔄l)) with (seq_enum (syn_mty <$> 𝔄l)).
  rewrite /seq_enum length_fmap -/(sum_tag 𝔄l) -list_fmap_compose.
  change (mty_size ∘ syn_mty) with syn_bsize. rewrite -/(sum_max 𝔄l).
  split.
  - intros (Hlen & fv & Hfv & Hrep).
    destruct (syn_fval y) as [fy|] eqn:Hfy; [|done]. simpl in Hfv. injection Hfv as <-.
    apply frepr_enum_iff in Hrep as (_ & (bst & Ht & Hdt) & Ht0 & vm & Hvm & Hp & Hpad).
    rewrite Nat2Z.id Hvi in Hvm. injection Hvm as <-.
    change (mty_size (syn_mty (𝔄l !!ₗ i))) with (syn_bsize (𝔄l !!ₗ i)) in Hp. change (mty_size (syn_mty (𝔄l !!ₗ i))) with (syn_bsize (𝔄l !!ₗ i)) in Hpad.
    destruct (plain_fbytes (drop (int_size (sum_tag 𝔄l) + syn_bsize (𝔄l !!ₗ i)) fbs))
      as [bq Hbq].
    { intros j fb. rewrite lookup_drop. intros Hj. apply (Hpad _ fb Hj). lia. }
    exists bst, (list_slice (int_size (sum_tag 𝔄l)) (syn_bsize (𝔄l !!ₗ i)) fbs), bq.
    split; [|split; [|split]].
    + rewrite -Hbq -Ht /list_slice -{1}(take_drop (int_size (sum_tag 𝔄l)) fbs). f_equal.
      by rewrite -drop_drop take_drop.
    + by rewrite /= Hdt.
    + split; [rewrite /list_slice length_take length_drop; lia|]. eauto.
    + rewrite -(length_fmap (@inr positive abyte) bq) -Hbq length_drop. lia.
  - intros (bt & fp & bq & -> & Ht & (Hlp & fy & Hfy & Hp) & Hq).
    have Hlt : length bt = int_size (sum_tag 𝔄l) by apply decode_value_length in Ht.
    simpl in Ht. apply fmap_Some in Ht as (t & Hdt & [= <-]).
    split; [rewrite !length_app !length_fmap; lia|].
    rewrite Hfy. eexists. split; [done|].
    apply frepr_enum_iff. split; [rewrite !length_app !length_fmap; lia|].
    split; [exists bt; split; [by rewrite -Hlt -(length_fmap (@inr positive abyte) bt) take_app_length|done]|].
    split; [lia|]. exists (syn_mty (𝔄l !!ₗ i)). rewrite Nat2Z.id Hvi. split; [done|]. split.
    + rewrite -Hlt -(length_fmap (@inr positive abyte) bt) /list_slice drop_app_length.
      change (mty_size (syn_mty (𝔄l !!ₗ i))) with (syn_bsize (𝔄l !!ₗ i)).
      by rewrite -Hlp take_app_length.
    + intros j fb Hj Hge'. rewrite lookup_app_r in Hj; [|rewrite length_fmap; lia].
      rewrite lookup_app_r in Hj; [|rewrite length_fmap in Hge' |- *;
        change (mty_size (syn_mty (𝔄l !!ₗ i))) with (syn_bsize (𝔄l !!ₗ i)) in Hge'; lia].
      rewrite list_lookup_fmap in Hj. destruct (bq !! _); simplify_eq/=. by eexists.
Qed.

(** *** Zero-sized values, uninitialized bytes, tuples *)
Lemma syn_fbytes_zst {𝔄} R (x: ~~𝔄) fbs :
  syn_mty 𝔄 = zst_mty → syn_fval x = Some (FVTuple []) → syn_fbytes R x fbs ↔ fbs = [].
Proof.
  intros Hm Hv. rewrite /syn_fbytes /syn_bsize Hm Hv. split.
  - intros (Hl & _). by apply nil_length_inv.
  - intros ->. split; [done|]. eexists. split; [done|].
    apply frepr_tuple_iff. split_and!; [done|done| |].
    + intros k f fv Hk. by rewrite lookup_nil in Hk.
    + intros i fb Hi. by rewrite lookup_nil in Hi.
Qed.

Lemma syn_fbytes_uninit n R (x: ~~(uninitₛ n)) fbs :
  syn_fbytes R x fbs ↔ length fbs = n ∧ ∃ bs, fbs = inr <$> bs.
Proof.
  rewrite /syn_fbytes /syn_bsize /=. split.
  - intros (Hl & fv & [= <-] & Hr). apply frepr_tuple_iff in Hr as (_ & _ & _ & Hp).
    split; [done|]. apply plain_fbytes. intros i fb Hi. apply (Hp i fb Hi).
    by intros (f & Hf%elem_of_nil & _).
  - intros [Hl [bs ->]]. split; [done|]. eexists. split; [done|].
    apply frepr_tuple_iff. split_and!; [done|done| |].
    + intros k f fv Hk. by rewrite lookup_nil in Hk.
    + intros i fb Hi _. rewrite list_lookup_fmap in Hi.
      destruct (bs !! i); simplify_eq/=. by eexists.
Qed.

Lemma syn_bsize_prod 𝔄 𝔅 : syn_bsize (𝔄 * 𝔅) = (syn_bsize 𝔄 + syn_bsize 𝔅)%nat.
Proof.
  rewrite /syn_bsize. change (syn_mty (𝔄 * 𝔅)) with (seq_tuple [syn_mty 𝔄; syn_mty 𝔅]).
  rewrite mty_size_seq_tuple !seq_size_cons seq_size_nil. lia.
Qed.

Lemma syn_bsize_xprod_cons 𝔄 𝔄l :
  syn_bsize (Π! (𝔄 :: 𝔄l)) = (syn_bsize 𝔄 + syn_bsize (Π! 𝔄l))%nat.
Proof.
  rewrite /syn_bsize.
  change (syn_mty (Π! (𝔄 :: 𝔄l))) with (seq_tuple (syn_mty 𝔄 :: (syn_mty <$> 𝔄l))).
  change (syn_mty (Π! 𝔄l)) with (seq_tuple (syn_mty <$> 𝔄l)).
  by rewrite !mty_size_seq_tuple seq_size_cons.
Qed.

Lemma syn_fbytes_xprod_nil R (x: ~~(Π! [])) fbs : syn_fbytes R x fbs ↔ fbs = [].
Proof. by apply syn_fbytes_zst. Qed.

Lemma syn_fbytes_xprod_cons {𝔄 𝔄l} R (x: ~~𝔄) (xl: ~~(Π! 𝔄l)) fbs :
  syn_fbytes (𝔄:=Π! (𝔄 :: 𝔄l)) R (x -:: xl) fbs ↔
  ∃ fbs1 fbs2, fbs = fbs1 ++ fbs2 ∧ syn_fbytes R x fbs1 ∧ syn_fbytes R xl fbs2.
Proof.
  rewrite /syn_fbytes syn_bsize_xprod_cons.
  change (syn_mty (Π! (𝔄 :: 𝔄l))) with (seq_tuple (syn_mty 𝔄 :: (syn_mty <$> 𝔄l))).
  change (syn_mty (Π! 𝔄l)) with (seq_tuple (syn_mty <$> 𝔄l)).
  change (syn_fval (𝔄:=Π! (𝔄 :: 𝔄l)) (x -:: xl)) with
    (FVTuple <$> mapM id (syn_fval x :: plist_to_list (pmap (λ _ x0, syn_fval x0) xl))).
  change (syn_fval (𝔄:=Π! 𝔄l) xl) with
    (FVTuple <$> mapM id (plist_to_list (pmap (λ _ x0, syn_fval x0) xl))).
  generalize (plist_to_list (pmap (λ _ x0, syn_fval x0) xl)) => ol.
  rewrite /= /syn_bsize. split.
  - intros (Hlen & fv & Hfv & Hrep).
    destruct (syn_fval x) as [fv₀|] eqn:H₀; [|done]. simpl in Hfv.
    destruct (mapM id ol) as [fvs|] eqn:H₁; [|done]. simpl in Hfv. injection Hfv as <-.
    apply frepr_seq_tuple_cons in Hrep as (fbs1 & fbs2 & -> & Hl1 & Hr1 & Hr2).
    exists fbs1, fbs2. split; [done|]. rewrite length_app in Hlen.
    split; [split; [done|eauto]|]. split; [lia|]. eexists. split; [done|]. done.
  - intros (fbs1 & fbs2 & -> & (Hl1 & fv₀ & H₀ & Hr1) & (Hl2 & fv₁ & H₁ & Hr2)).
    destruct (mapM id ol) as [fvs|] eqn:H₁'; [|done]. simpl in H₁. injection H₁ as <-.
    split; [rewrite length_app; lia|]. exists (FVTuple (fv₀ :: fvs)). split.
    { apply fmap_Some. exists (fv₀ :: fvs). split; [|done]. by rewrite H₀. }
    apply frepr_seq_tuple_cons. by exists fbs1, fbs2.
Qed.

(** ** Byte-preserving maps ([syn_bincl], [typing/type.v]) *)

(** A map between two syntactic types of the same MiniRust type that preserves the fancy
    value preserves the bytes (e.g. on pointers, on zero-sized types). *)
Lemma syn_bincl_same {𝔄 𝔅} (f: 𝔄 →ₛ 𝔅) :
  syn_mty 𝔄 = syn_mty 𝔅 → (∀ x, syn_fval (f ~~$ₛ x) = syn_fval x) → syn_bincl f.
Proof.
  intros Hm Hv. split; [by rewrite /syn_bsize Hm|]. intros x R fbs.
  by rewrite /syn_fbytes /syn_bsize Hm Hv.
Qed.

Lemma syn_bincl_at_loc_map {𝔄 𝔅} (f: 𝔄 →ₛ 𝔅) : syn_bincl (at_loc_mapₛ f).
Proof. apply syn_bincl_same; [done|]. by intros [??]. Qed.

Lemma syn_bincl_prod_map {𝔄 𝔅 𝔄' 𝔅'} (f: 𝔄 →ₛ 𝔄') (g: 𝔅 →ₛ 𝔅') :
  syn_bincl f → syn_bincl g → syn_bincl (prod_mapₛ f g).
Proof.
  intros [Hs Hf] [Hs' Hg]. split; [rewrite !syn_bsize_prod; lia|].
  intros [x y] R fbs. rewrite /= !syn_fbytes_pair.
  setoid_rewrite (Hf x). by setoid_rewrite (Hg y).
Qed.

Lemma syn_bincl_to_cons_prod {𝔄 𝔅l} : syn_bincl (to_cons_prodₛ (𝔄:=𝔄) (𝔅l:=𝔅l)).
Proof.
  split; [by rewrite syn_bsize_prod syn_bsize_xprod_cons|].
  intros [x xl] R fbs. by rewrite syn_fbytes_pair /= syn_fbytes_xprod_cons.
Qed.

Lemma syn_bincl_of_cons_prod {𝔄 𝔅l} : syn_bincl (of_cons_prodₛ (𝔄:=𝔄) (𝔅l:=𝔅l)).
Proof. apply (syn_bincl_iso to_cons_prodₛ); [apply _|apply syn_bincl_to_cons_prod]. Qed.
