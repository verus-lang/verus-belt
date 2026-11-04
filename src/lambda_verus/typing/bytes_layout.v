From lrust.typing Require Export type.
Set Default Proof Using "Type".

(** * Byte layouts of syntactic types (stage 4 of the MiniRust memory model)

[syn_bytes x bs]: the bytes [bs] represent the value [x] of the syntactic type [𝔄]: [x]
has a MiniRust value, and [bs] decode to it at [syn_mty 𝔄]. A type's [ty_bytes] is the
[syn_bytes] of its syntactic type ([ty_bytes_syn]), since [ty_mty] and [ty_val] are
determined by the syntactic type. The lemmas below split the bytes of a value along its
layout: the tag, the payload and the padding of a variant of a sum ([syn_bytes_sum]),
the fields of a struct; and they characterize the bytes of a pointer ([syn_bytes_ptr])
and of an integer ([syn_bytes_int]). *)

Implicit Type 𝔄 𝔅: syn_type.

Definition syn_bytes {𝔄} (x: ~~𝔄) (bs: list abyte) : Prop :=
  ∃ v, syn_val x = Some v ∧ decode_value (syn_mty 𝔄) bs = Some v.

Lemma ty_bytes_syn `{!typeG Σ} {𝔄} (ty: type 𝔄) x bs : ty_bytes ty x bs ↔ syn_bytes x bs.
Proof. by rewrite /ty_bytes /syn_bytes -ty_mty_eq -ty_val_eq. Qed.

Lemma syn_bytes_length {𝔄} (x: ~~𝔄) bs : syn_bytes x bs → length bs = syn_bsize 𝔄.
Proof. intros (v & _ & Hd). by eapply decode_value_length. Qed.

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
  rewrite decode_seq_enum length_fmap -/(sum_tag 𝔄l).
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

(** ** Reading the discriminant of a sum ([GetDiscr]): the discriminator of [Σ! 𝔄l] reads
    the tag at offset 0. *)
Lemma sum_tag_chunk 𝔄l (j: nat) bt :
  decode_value (MInt (sum_tag 𝔄l)) bt = Some (VInt (Z.of_nat j)) →
  chunks_reader [(0%nat, bt)] 0 (sum_tag 𝔄l) = Some (Z.of_nat j).
Proof.
  intros Hbt. have Hl := decode_value_length _ _ _ Hbt. simpl in Hl.
  rewrite /= decide_True; [|lia]. rewrite ?Nat.sub_0_r /list_slice drop_0 take_ge; [|lia].
  simpl in Hbt. by apply fmap_Some in Hbt as (z & Hz & [= ->]).
Qed.

Lemma sum_tag_chunk_discr 𝔄l (j: nat) bt :
  decode_value (MInt (sum_tag 𝔄l)) bt = Some (VInt (Z.of_nat j)) → (j < length 𝔄l)%nat →
  discr_eval (chunks_reader [(0%nat, bt)]) (seq_discr (length 𝔄l)) = Some (Z.of_nat j).
Proof. intros. apply seq_discr_eval; [done|]. by apply sum_tag_chunk. Qed.

Section get_discr_sum.
  Context `{!lrustGS Σ}.

  Lemma wp_get_discr_sum E 𝔄l (j: nat) l bt Φ :
    decode_value (MInt (sum_tag 𝔄l)) bt = Some (VInt (Z.of_nat j)) → (j < length 𝔄l)%nat →
    l ↦b bt -∗ (l ↦b bt -∗ Φ (MLitV (VInt (Z.of_nat j)))) -∗
    WP GetDiscr (syn_mty (Σ! 𝔄l)) (MLit (VPtr l)) @ E {{ Φ }}.
  Proof.
    iIntros (Hbt Hj) "Hl HΦ".
    iApply (wp_get_discr _ _ _ _ _ _ [(0%nat, bt)] with "[Hl]").
    - rewrite length_fmap. by apply sum_tag_chunk_discr.
    - by rewrite /chunks_own /= shift_loc_0 right_id.
    - iIntros "H". iApply "HΦ". by rewrite /chunks_own /= shift_loc_0 right_id.
  Qed.

End get_discr_sum.

(** * Fancy bytes (§10 step 4 of [design_docs/pcell-multibyte-cells.md])

[syn_fbytes R x fbs]: the fancy bytes [fbs] (each a byte-cell or an abstract byte)
represent the value [x], with the static registry [R]: they have the size of [𝔄], and
represent the fancy value of [x] ([syn_fval x], where a cell [pcellₛ m] is its group) at
[syn_mty 𝔄] ([frepr]). For a value with a MiniRust value ([syn_val x = Some v]), and so
for every value of a type without cells ([syn_nocell 𝔄]), these are the plain bytes of
[syn_bytes] ([syn_fbytes_val], [syn_fbytes_nocell]). The lemmas below split fancy bytes
along the layout, as those above do for plain bytes: structs ([syn_fbytes_struct]) and
sums ([syn_fbytes_sum]; the tag and the padding are plain). *)

(** ** Representations at the MiniRust types of tuples and enums *)
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

  Lemma frepr_tuple_iff R fs sz al fbs fvs :
    frepr R (MTuple fs sz al) fbs (FVTuple fvs) ↔
    length fbs = sz ∧ length fvs = length fs ∧
    (∀ k f fv, fs !! k = Some f → fvs !! k = Some fv →
       frepr R f.2 (list_slice f.1 (mty_size f.2) fbs) fv) ∧
    (∀ i fb, fbs !! i = Some fb → ¬ in_field fs i → is_plain fb).
  Proof.
    split.
    - intros Hrep. destruct (frepr_tuple_inv _ _ _ _ _ _ Hrep) as (? & ? & ?).
      split_and!; [done|done| |done]. intros. by eapply frepr_field.
    - intros (? & ? & ? & ?). by apply frepr_tuple.
  Qed.

  Lemma frepr_enum_iff R vars dc sz al fbs t d :
    frepr R (MEnum vars dc sz al) fbs (FVVariant t d) ↔
    length fbs = sz ∧ decode_discr dc (fb_erase <$> fbs) = Some t ∧
    (0 ≤ t)%Z ∧ ∃ vm o tg, vars !! Z.to_nat t = Some (vm, o, tg) ∧
      frepr R vm (list_slice o (mty_size vm) fbs) d ∧
      (∀ i fb, fbs !! i = Some fb → ¬ (o ≤ i < o + mty_size vm)%nat → is_plain fb).
  Proof.
    split.
    - intros Hrep. destruct (frepr_enum_inv _ _ _ _ _ _ _ _ Hrep)
        as (? & ? & ? & vm & o & tg & Hvm & ?).
      split_and!; [done|done|done|]. exists vm, o, tg. split_and!; [done| |done].
      by eapply frepr_payload.
    - intros (? & ? & ? & vm & o & tg & ? & ? & ?). by eapply frepr_enum.
  Qed.

  (** The representations at [seq_enum]: the tag (plain), the payload after it, and the
      padding (plain). *)
  Lemma frepr_seq_enum_iff R ms fbs t d :
    frepr R (seq_enum ms) fbs (FVVariant t d) ↔
    length fbs = (int_size (enum_tag (length ms)) + list_max (mty_size <$> ms))%nat ∧
    (∃ bst, take (int_size (enum_tag (length ms))) fbs = inr <$> bst ∧
      decode_int (enum_tag (length ms)) bst = Some t) ∧
    (0 ≤ t)%Z ∧ ∃ vm, ms !! Z.to_nat t = Some vm ∧
      frepr R vm (list_slice (int_size (enum_tag (length ms))) (mty_size vm) fbs) d ∧
      (∀ i fb, fbs !! i = Some fb → (int_size (enum_tag (length ms)) + mty_size vm ≤ i)%nat →
        is_plain fb).
  Proof.
    set tsz := int_size (enum_tag (length ms)).
    rewrite /seq_enum frepr_enum_iff decode_discr_seq. split.
    - intros (Hlen & Hd & Ht0 & vm & o & tg & Hvm & Hp & Hpad).
      rewrite list_lookup_imap in Hvm. apply fmap_Some in Hvm as (vm' & Hvm & [= -> -> ->]).
      change (if decide (length ms ≤ 256)%nat then 1%nat else length ms) with tsz in *.
      apply bind_Some in Hd as (t' & Ht' & Hd).
      destruct (decide ((0 ≤ t' < Z.of_nat (length ms))%Z)); simplify_eq.
      destruct (plain_fbytes (take tsz fbs)) as [bst Hbst].
      { intros j fb. rewrite lookup_take_Some. intros [Hj ?]. apply (Hpad _ fb Hj). lia. }
      split; [done|]. split; [|split; [done|]].
      + exists bst. split; [done|]. by rewrite -fmap_take Hbst fb_erase_plain in Ht'.
      + exists vm'. split_and!; [done|done|]. intros j fb Hj ?. apply (Hpad _ _ Hj). lia.
    - intros (Hlen & (bst & Hbst & Ht) & Ht0 & vm & Hvm & Hp & Hpad).
      have Hlt : (Z.to_nat t < length ms)%nat by eapply lookup_lt_Some.
      split; [done|]. split; [|split; [done|]].
      + rewrite -fmap_take Hbst fb_erase_plain Ht /=.
        destruct (decide ((0 ≤ t < Z.of_nat (length ms))%Z)); [done|lia].
      + exists vm, tsz, [(0%nat, enum_tag (length ms), Z.of_nat (Z.to_nat t))].
        rewrite list_lookup_imap Hvm /=. split_and!; [done|done|].
        intros j fb Hj Hn. destruct (decide (j < tsz)%nat).
        * have : take tsz fbs !! j = Some fb by rewrite lookup_take.
          rewrite Hbst list_lookup_fmap. destruct (bst !! j); simpl; intros Hb; simplify_eq. by eexists.
        * apply (Hpad _ _ Hj). lia.
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
  - assert (∀ (i: fin (length l)) (x0 : ~~ (l !!ₗ i)) w,
      syn_val x0 = Some w → syn_fval x0 = Some (fv_lift w)) as Hall.
    { clear x. induction l as [|𝔄0 l IH]; intros i; [inv_fin i|].
      inv_fin i; [intros x0 w; by apply (FIX _ x0)|by apply IH]. }
    clear FIX.
    replace x with (of_xsum (to_xsum x)); last by rewrite semi_iso'.
    destruct (to_xsum x) as [i x0]. simpl. rewrite !psum_map1_pinj !to_xsum_pinj.
    intros (w & Hw & ->)%fmap_Some_1. by rewrite (Hall i x0 w Hw).
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
Qed.

Lemma syn_fval_pinj {𝔄l} (i: fin (length 𝔄l)) (y: ~~(𝔄l !!ₗ i)) :
  syn_fval (𝔄:=Σ! 𝔄l) (pinj i y) = FVVariant (Z.of_nat (fin_to_nat i)) <$> syn_fval y.
Proof. by rewrite /= psum_map1_pinj to_xsum_pinj. Qed.

(** ** Fancy bytes of syntactic types ([syn_fbytes], [prophecy/syn_type.v]) *)

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
  split.
  - intros (Hlen & fv & Hfv & Hrep).
    destruct (syn_fval y) as [fy|] eqn:Hfy; [|done]. simpl in Hfv. injection Hfv as <-.
    apply frepr_seq_enum_iff in Hrep as (_ & (bst & Ht & Hdt) & Ht0 & vm & Hvm & Hp & Hpad).
    rewrite length_fmap -/(sum_tag 𝔄l) in Ht Hdt Hp Hpad.
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
    apply frepr_seq_enum_iff. rewrite length_fmap -/(sum_tag 𝔄l) -list_fmap_compose.
    change (mty_size ∘ syn_mty) with syn_bsize. rewrite -/(sum_max 𝔄l).
    split; [rewrite !length_app !length_fmap; lia|].
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

(** *** Zero-sized values, uninitialized bytes *)
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

(** ** The cells of syntactic values ([mcells], [typing/gcont.v]) *)

Lemma mcells_sum {𝔄l} (i: fin (length 𝔄l)) (y: ~~(𝔄l !!ₗ i)) fv :
  syn_fval (𝔄:=Σ! 𝔄l) (pinj i y) = Some fv → ∃ fv', syn_fval y = Some fv' ∧
  mcells (syn_mty (Σ! 𝔄l)) fv = mshift (int_size (sum_tag 𝔄l)) (mcells (syn_mty (𝔄l !!ₗ i)) fv').
Proof.
  rewrite syn_fval_pinj. destruct (syn_fval y) as [fv'|]; [|done]. simpl. intros [= <-].
  exists fv'. split; [done|]. change (syn_mty (Σ! 𝔄l)) with (seq_enum (syn_mty <$> 𝔄l)).
  rewrite mcells_seq_enum Nat2Z.id list_lookup_fmap llookup_lookup /= length_fmap. done.
Qed.

(** ** Byte-preserving maps ([syn_bincl], [prophecy/syn_type.v]) *)

(** [syn_bincl_same] (same MiniRust type and fancy value, e.g. pointers and zero-sized
    types) is in [prophecy/syn_type.v]. *)

Lemma syn_bincl_at_loc_map {𝔄 𝔅} (f: 𝔄 →ₛ 𝔅) : syn_bincl (at_loc_mapₛ f).
Proof. apply syn_bincl_same; [done|]. by intros [??]. Qed.


(** * Structs: the layout of [structₛ L 𝔄l] is [struct_lay L (syn_mty <$> 𝔄l)] *)

Definition struct_offs (L: struct_layout) (𝔄l: syn_typel) : list nat :=
  (struct_lay L (syn_mty <$> 𝔄l)).(sl_offs).
Definition struct_size (L: struct_layout) (𝔄l: syn_typel) : nat :=
  (struct_lay L (syn_mty <$> 𝔄l)).(sl_size).
(** The fields of the MiniRust type, with their offsets. *)
Definition struct_fields (L: struct_layout) (𝔄l: syn_typel) : list (nat * mty) :=
  zip (struct_offs L 𝔄l) (syn_mty <$> 𝔄l).

(** The offset of field [j]. *)
Definition struct_off (L: struct_layout) (𝔄l: syn_typel) (j: nat) : nat :=
  default 0%nat (struct_offs L 𝔄l !! j).
Global Arguments struct_off : simpl never.

Lemma syn_mty_struct L 𝔄l :
  syn_mty (structₛ L 𝔄l) =
    MTuple (struct_fields L 𝔄l) (struct_size L 𝔄l) (struct_lay L (syn_mty <$> 𝔄l)).(sl_align).
Proof. done. Qed.

Lemma syn_bsize_struct L 𝔄l : syn_bsize (structₛ L 𝔄l) = struct_size L 𝔄l.
Proof. done. Qed.

Lemma length_struct_offs L 𝔄l : length (struct_offs L 𝔄l) = length 𝔄l.
Proof. rewrite /struct_offs length_struct_lay ?length_fmap //. apply syn_mty_wf_list. Qed.

Lemma struct_off_lookup L 𝔄l j :
  (j < length 𝔄l)%nat → struct_offs L 𝔄l !! j = Some (struct_off L 𝔄l j).
Proof.
  intros Hj. rewrite /struct_off. destruct (struct_offs L 𝔄l !! j) eqn:Hl; [done|].
  apply lookup_ge_None in Hl. rewrite length_struct_offs in Hl. lia.
Qed.

Lemma struct_fields_bounds L 𝔄l :
  Forall (λ f, f.1 + mty_size f.2 ≤ struct_size L 𝔄l)%nat (struct_fields L 𝔄l).
Proof.
  have Hwf := syn_mty_wf (structₛ L 𝔄l). rewrite syn_mty_struct in Hwf.
  by apply mty_wf_tuple_inv in Hwf as (_ & ? & _).
Qed.

Lemma struct_fields_disjoint L 𝔄l : fields_disjoint (struct_fields L 𝔄l).
Proof.
  have Hwf := syn_mty_wf (structₛ L 𝔄l). rewrite syn_mty_struct in Hwf.
  by apply mty_wf_tuple_inv in Hwf as (? & _ & _).
Qed.

(** The effective layout of a well-formed [L] is [L]. *)
Lemma struct_offs_wf L 𝔄l : sl_wf L (syn_mty <$> 𝔄l) → struct_offs L 𝔄l = L.(sl_offs).
Proof. intros. by rewrite /struct_offs struct_lay_wf_eq. Qed.

(** Maps preserving the sizes of the fields preserve the layout. *)
Lemma struct_lay_bsize L 𝔄l 𝔅l :
  syn_bsize <$> 𝔄l = syn_bsize <$> 𝔅l →
  struct_lay L (syn_mty <$> 𝔄l) = struct_lay L (syn_mty <$> 𝔅l).
Proof.
  intros Hs. apply struct_lay_sizes; [apply syn_mty_wf_list|apply syn_mty_wf_list|].
  by rewrite -!list_fmap_compose.
Qed.

Lemma struct_offs_bsize L 𝔄l 𝔅l :
  syn_bsize <$> 𝔄l = syn_bsize <$> 𝔅l → struct_offs L 𝔄l = struct_offs L 𝔅l.
Proof. intros. by rewrite /struct_offs (struct_lay_bsize L 𝔄l 𝔅l). Qed.

Lemma struct_size_bsize L 𝔄l 𝔅l :
  syn_bsize <$> 𝔄l = syn_bsize <$> 𝔅l → struct_size L 𝔄l = struct_size L 𝔅l.
Proof. intros. by rewrite /struct_size (struct_lay_bsize L 𝔄l 𝔅l). Qed.

Lemma struct_off_bsize L 𝔄l 𝔅l j :
  syn_bsize <$> 𝔄l = syn_bsize <$> 𝔅l → struct_off L 𝔄l j = struct_off L 𝔅l j.
Proof. intros. by rewrite /struct_off (struct_offs_bsize L 𝔄l 𝔅l). Qed.

(** The fancy bytes of the fields of a struct at the offsets [offs]. *)
Fixpoint fields_fbytes (R: gmap positive (mty * list positive)) (𝔄l: syn_typel) :
    list nat → plist (~~) 𝔄l → list (positive + abyte) → Prop :=
  match 𝔄l with
  | [] => λ _ _ _, True
  | 𝔄 :: 𝔄l' => λ offs xs fbs,
      match offs with
      | [] => False
      | o :: offs' => syn_fbytes R (phd xs) (list_slice o (syn_bsize 𝔄) fbs) ∧
          fields_fbytes R 𝔄l' offs' (ptl xs) fbs
      end
  end.

Lemma fields_frepr_iff R 𝔄l offs (xs : plist (~~) 𝔄l) fbs :
  length offs = length 𝔄l →
  Forall (λ f, f.1 + mty_size f.2 ≤ length fbs)%nat (zip offs (syn_mty <$> 𝔄l)) →
  (∃ fvs, mapM id (plist_to_list (pmap (λ _ x, syn_fval x) xs)) = Some fvs ∧
     ∀ k f fv, zip offs (syn_mty <$> 𝔄l) !! k = Some f → fvs !! k = Some fv →
       frepr R f.2 (list_slice f.1 (mty_size f.2) fbs) fv) ↔
  fields_fbytes R 𝔄l offs xs fbs.
Proof.
  revert offs. induction 𝔄l as [|𝔄 𝔄l IH]; intros [|o offs] Hlen Hb; simpl in *; try lia.
  - split; [done|]. intros _. exists []. split; [done|]. intros ???. by rewrite lookup_nil.
  - destruct xs as [x xs]. simpl. inversion Hb as [|? ? Hb0 Hbs]; subst. simpl in Hb0.
    rewrite -(IH xs offs); [|lia|done]. split.
    + intros (fvs & Hfvs & Hfs).
      destruct (syn_fval x) as [fv|] eqn:Hfv; [|done]. simpl in Hfvs.
      destruct (mapM id _) as [fvs'|] eqn:Hfvs'; [|done]. simpl in Hfvs. injection Hfvs as <-.
      split.
      * split; [rewrite /list_slice length_take length_drop; rewrite /syn_bsize; lia|].
        exists fv. split; [done|]. by apply (Hfs 0%nat (o, syn_mty 𝔄) fv).
      * exists fvs'. split; [done|]. intros k f fv' Hk Hfv'. by apply (Hfs (S k)).
    + intros [(_ & fv & Hfv & Hrep) (fvs & Hfvs & Hfs)].
      exists (fv :: fvs). rewrite Hfv /= Hfvs /=. split; [done|].
      intros [|k] f fv'; simpl; intros Hk Hfv'; simplify_eq; [done|]. by apply (Hfs k).
Qed.

(** The fancy bytes of a struct: the plain bytes outside its fields, and the fancy bytes of
    the fields at their offsets. *)
Lemma syn_fbytes_struct R L 𝔄l (xs : ~~(structₛ L 𝔄l)) fbs :
  syn_fbytes R xs fbs ↔
  length fbs = struct_size L 𝔄l ∧
  (∀ i fb, fbs !! i = Some fb → ¬ in_field (struct_fields L 𝔄l) i → is_plain fb) ∧
  fields_fbytes R 𝔄l (struct_offs L 𝔄l) xs fbs.
Proof.
  rewrite /syn_fbytes syn_bsize_struct syn_mty_struct.
  change (syn_fval (𝔄:=structₛ L 𝔄l) xs) with
    (FVTuple <$> mapM id (plist_to_list (pmap (λ _ x0, syn_fval x0) xs))).
  have Hlo := length_struct_offs L 𝔄l. have Hb := struct_fields_bounds L 𝔄l.
  have Hlf : length (struct_fields L 𝔄l) = length 𝔄l.
  { rewrite /struct_fields length_zip_with length_fmap. lia. }
  split.
  - intros (Hlen & fv & Hfv & Hrep). apply fmap_Some in Hfv as (fvs & Hfvs & ->).
    apply frepr_tuple_iff in Hrep as (_ & _ & Hfs & Hpad).
    split_and!; [done|done|]. apply fields_frepr_iff; [done| |by exists fvs].
    eapply Forall_impl; [exact Hb|]. simpl. lia.
  - intros (Hlen & Hpad & Hfs). apply fields_frepr_iff in Hfs as (fvs & Hfvs & Hfs); [|done|];
      last by (eapply Forall_impl; [exact Hb|]; simpl; lia).
    split; [done|]. exists (FVTuple fvs). rewrite Hfvs. split; [done|].
    apply frepr_tuple_iff. split_and!; [done| |done|done].
    apply mapM_Some in Hfvs. apply Forall2_length in Hfvs.
    by rewrite -Hfvs length_plist_to_list.
Qed.

Lemma in_field_ranges fs fs' i :
  field_ranges fs = field_ranges fs' → in_field fs i ↔ in_field fs' i.
Proof.
  intros Heq. rewrite /in_field. split.
  - intros ([o m] & (k & Hk)%elem_of_list_lookup & Hi).
    have Hk' : field_ranges fs !! k = Some (o, mty_size m) by rewrite /field_ranges list_lookup_fmap Hk.
    rewrite Heq /field_ranges list_lookup_fmap in Hk'.
    apply fmap_Some in Hk' as ([o' m'] & Hk'' & [= -> Hs]).
    exists (o', m'). split; [by eapply elem_of_list_lookup_2|]. simpl in *. lia.
  - intros ([o m] & (k & Hk)%elem_of_list_lookup & Hi).
    have Hk' : field_ranges fs' !! k = Some (o, mty_size m) by rewrite /field_ranges list_lookup_fmap Hk.
    rewrite -Heq /field_ranges list_lookup_fmap in Hk'.
    apply fmap_Some in Hk' as ([o' m'] & Hk'' & [= -> Hs]).
    exists (o', m'). split; [by eapply elem_of_list_lookup_2|]. simpl in *. lia.
Qed.

Lemma bsize_plist2_bincl {𝔄l 𝔅l} (fl: plist2 (λ 𝔄 𝔅, 𝔄 →ₛ 𝔅) 𝔄l 𝔅l) :
  (∀ i, syn_bincl (fl -2!! i)) → syn_bsize <$> 𝔄l = syn_bsize <$> 𝔅l.
Proof.
  revert 𝔅l fl. induction 𝔄l as [|𝔄 𝔄l IH]; intros [|𝔅 𝔅l] fl Hb; [done|done|done|].
  destruct fl as [f fl]. simpl. f_equal; [apply (Hb 0%fin)|].
  apply (IH _ fl). intros i. apply (Hb (FS i)).
Qed.

Lemma fields_fbytes_map R L {𝔄l 𝔅l} (fl: plist2 (λ 𝔄 𝔅, 𝔄 →ₛ 𝔅) 𝔄l 𝔅l) offs xs fbs :
  (∀ i, syn_bincl (fl -2!! i)) →
  fields_fbytes R 𝔄l offs xs fbs ↔ fields_fbytes R 𝔅l offs (struct_mapₛ L fl ~~$ₛ xs) fbs.
Proof.
  revert 𝔅l fl offs. induction 𝔄l as [|𝔄 𝔄l IH]; intros [|𝔅 𝔅l] fl offs Hb; [done|done|done|].
  destruct fl as [f fl], xs as [x xs], offs as [|o offs]; [done|]. simpl.
  have Hb0 : syn_bincl f := Hb 0%fin. destruct Hb0 as [Hs [Hf _]]. rewrite -Hs (Hf x).
  f_equiv. apply IH. intros i. apply (Hb (FS i)).
Qed.

Lemma mcells_tuple_cons o m offs ms sz al fv fvs :
  mcells (MTuple (zip (o :: offs) (m :: ms)) sz al) (FVTuple (fv :: fvs)) =
  mshift o (mcells m fv) ++ mcells (MTuple (zip offs ms) sz al) (FVTuple fvs).
Proof. by rewrite !mcells_tuple imap_cons. Qed.

Lemma fields_mcells_map R L {𝔄l 𝔅l} (fl: plist2 (λ 𝔄 𝔅, 𝔄 →ₛ 𝔅) 𝔄l 𝔅l) offs xs fbs fvs fvs' sz al :
  (∀ i, syn_bincl (fl -2!! i)) → fields_fbytes R 𝔄l offs xs fbs →
  mapM id (plist_to_list (pmap (λ _ x, syn_fval x) xs)) = Some fvs →
  mapM id (plist_to_list (pmap (λ _ x, syn_fval x) (struct_mapₛ L fl ~~$ₛ xs))) = Some fvs' →
  mcells (MTuple (zip offs (syn_mty <$> 𝔄l)) sz al) (FVTuple fvs) =
  mcells (MTuple (zip offs (syn_mty <$> 𝔅l)) sz al) (FVTuple fvs').
Proof.
  revert 𝔅l fl offs fvs fvs'. induction 𝔄l as [|𝔄 𝔄l IH];
    intros [|𝔅 𝔅l] fl offs fvs fvs' Hb Hfb Hfvs Hfvs'; [|done|done|].
  { simpl in Hfvs, Hfvs'. injection Hfvs as <-. injection Hfvs' as <-.
    by rewrite !mcells_tuple. }
  destruct fl as [f fl], xs as [x xs], offs as [|o offs]; [done|]. simpl in Hfb, Hfvs, Hfvs'.
  destruct Hfb as [Hfb0 Hfb].
  destruct (syn_fval x) as [fv|] eqn:Hfv; [|done]. simpl in Hfvs.
  destruct (mapM id _) as [fvt|] eqn:Hfvt; [|done]. injection Hfvs as <-.
  destruct (syn_fval (f ~~$ₛ x)) as [fv'|] eqn:Hfv'; [|done]. simpl in Hfvs'.
  destruct (mapM id (plist_to_list (pmap _ (struct_mapₛ L fl ~~$ₛ xs)))) as [fvt'|] eqn:Hfvt';
    [|done]. injection Hfvs' as <-.
  rewrite !fmap_cons !mcells_tuple_cons. have Hb0 : syn_bincl f := Hb 0%fin. destruct Hb0 as [_ [_ Hc]].
  rewrite (Hc x R _ fv fv' Hfb0) //. f_equal. eapply IH; [|done..]. intros i. apply (Hb (FS i)).
Qed.

Lemma syn_bincl_struct_map L {𝔄l 𝔅l} (fl: plist2 (λ 𝔄 𝔅, 𝔄 →ₛ 𝔅) 𝔄l 𝔅l) :
  (∀ i, syn_bincl (fl -2!! i)) → syn_bincl (struct_mapₛ L fl).
Proof.
  intros Hb. have Hlay := struct_lay_bsize L _ _ (bsize_plist2_bincl fl Hb).
  have Hoffs : struct_offs L 𝔄l = struct_offs L 𝔅l by rewrite /struct_offs Hlay.
  have Hsz : struct_size L 𝔄l = struct_size L 𝔅l by rewrite /struct_size Hlay.
  have Hrng : field_ranges (struct_fields L 𝔄l) = field_ranges (struct_fields L 𝔅l).
  { rewrite /struct_fields !field_ranges_zip Hoffs -!list_fmap_compose.
    by rewrite (bsize_plist2_bincl fl Hb). }
  split; [by rewrite !syn_bsize_struct|]. split.
  - intros xs R fbs. rewrite !syn_fbytes_struct -Hsz -Hoffs (fields_fbytes_map R L fl) //.
    setoid_rewrite (in_field_ranges _ _ _ Hrng). done.
  - intros xs R fbs fv fv' Hfb Hx Hx'. apply syn_fbytes_struct in Hfb as (_ & _ & Hfb).
    change (syn_fval (𝔄:=structₛ L 𝔄l) xs) with
      (FVTuple <$> mapM id (plist_to_list (pmap (λ _ x0, syn_fval x0) xs))) in Hx.
    change (syn_fval (𝔄:=structₛ L 𝔅l) (struct_mapₛ L fl ~~$ₛ xs)) with
      (FVTuple <$> mapM id (plist_to_list (pmap (λ _ x0, syn_fval x0) (struct_mapₛ L fl ~~$ₛ xs))))
      in Hx'.
    apply fmap_Some in Hx as (fvs & Hfvs & ->). apply fmap_Some in Hx' as (fvs' & Hfvs' & ->).
    rewrite !syn_mty_struct /struct_fields -Hoffs -Hsz -Hlay.
    by eapply fields_mcells_map.
Qed.

Lemma syn_bincl_struct_relay {𝔄l} L L' : L = L' → syn_bincl (struct_relayₛ (𝔄l:=𝔄l) L L').
Proof. intros <-. apply syn_bincl_same; [done|]. by intros ?. Qed.
