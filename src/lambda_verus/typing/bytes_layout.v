From lrust.typing Require Export type.
From guarding Require Import guard.
Set Default Proof Using "Type".

(** * Byte layouts of syntactic types (stage 4 of the MiniRust memory model)

[syn_bytes x bs]: the bytes [bs] represent the value [x] of the syntactic type [𝔄]: [x]
has a MiniRust value, and [bs] decode to it at [syn_mty 𝔄]. A type's [ty_bytes] is the
[syn_bytes] of its syntactic type ([ty_bytes_syn]), since [ty_mty] and [ty_val] are
determined by the syntactic type. The lemmas below split the bytes of a value along its
layout: the rest of the bytes and the payload of a variant of an enum ([syn_bytes_enum]),
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

(** ** Enums: the payload of the variant at its offset, and the rest of the bytes (the
    taggers and the padding), from which the discriminator reads the variant. The layout
    of [enumₛ EL 𝔄l] is [enum_ly EL 𝔄l] ([EL] if it is well formed). *)
Definition enum_ly (EL: enum_layout) (𝔄l: syn_typel) : enum_layout :=
  enum_lay EL (syn_mty <$> 𝔄l).
Definition enum_vars (EL: enum_layout) (𝔄l: syn_typel) : list (mty * nat * tagger) :=
  zip_with (λ m v, (m, v.1, v.2)) (syn_mty <$> 𝔄l) (enum_ly EL 𝔄l).(el_vars).
Definition enum_size (EL: enum_layout) (𝔄l: syn_typel) : nat := (enum_ly EL 𝔄l).(el_size).
Definition enum_discr (EL: enum_layout) (𝔄l: syn_typel) : discr := (enum_ly EL 𝔄l).(el_discr).
(** The offset of the payload of variant [i]. *)
Definition enum_off (EL: enum_layout) (𝔄l: syn_typel) (i: nat) : nat :=
  default 0%nat (fst <$> (enum_ly EL 𝔄l).(el_vars) !! i).
Global Arguments enum_off : simpl never.

Lemma syn_mty_enum EL 𝔄l :
  syn_mty (enumₛ EL 𝔄l) =
    MEnum (enum_vars EL 𝔄l) (enum_discr EL 𝔄l) (enum_size EL 𝔄l) (enum_ly EL 𝔄l).(el_align).
Proof. done. Qed.

Lemma syn_bsize_enum EL 𝔄l : syn_bsize (enumₛ EL 𝔄l) = enum_size EL 𝔄l.
Proof. done. Qed.

Lemma enum_vars_lookup EL 𝔄l (i: fin (length 𝔄l)) :
  ∃ tg, enum_vars EL 𝔄l !! fin_to_nat i = Some (syn_mty (𝔄l !!ₗ i), enum_off EL 𝔄l i, tg).
Proof.
  have Hlen := length_enum_lay EL (syn_mty <$> 𝔄l) (syn_mty_wf_list 𝔄l).
  destruct (lookup_lt_is_Some_2 (enum_ly EL 𝔄l).(el_vars) i) as [[o tg] Hv].
  { rewrite /enum_ly Hlen length_fmap. apply fin_to_nat_lt. }
  exists tg. rewrite /enum_vars /enum_off lookup_zip_with list_lookup_fmap llookup_lookup /= Hv //.
Qed.

Lemma enum_vars_lookup_inv EL 𝔄l (t: nat) v :
  enum_vars EL 𝔄l !! t = Some v → ∃ i: fin (length 𝔄l), fin_to_nat i = t.
Proof.
  rewrite /enum_vars lookup_zip_with list_lookup_fmap.
  destruct (𝔄l !! t) eqn:Ht; [|done]. intros _. apply lookup_lt_Some in Ht.
  exists (nat_to_fin Ht). by rewrite fin_to_nat_to_fin.
Qed.

Lemma enum_layout_ok_syn EL 𝔄l :
  enum_layout_ok (enum_vars EL 𝔄l) (enum_discr EL 𝔄l) (enum_size EL 𝔄l).
Proof. have := syn_mty_wf (enumₛ EL 𝔄l). rewrite syn_mty_enum. by intros [? _]%mty_wf_enum_inv. Qed.

Lemma enum_off_bound EL 𝔄l (i: fin (length 𝔄l)) :
  (enum_off EL 𝔄l i + syn_bsize (𝔄l !!ₗ i) ≤ enum_size EL 𝔄l)%nat.
Proof.
  destruct (enum_vars_lookup EL 𝔄l i) as [tg Hv]. destruct (enum_layout_ok_syn EL 𝔄l) as [Hb _].
  by destruct (Forall_lookup_1 _ _ _ _ Hb Hv).
Qed.

(** The discriminator reads only outside the payload of each variant, within the size. *)
Lemma enum_reads EL 𝔄l (i: fin (length 𝔄l)) off it :
  (off, it) ∈ discr_reads (enum_discr EL 𝔄l) →
  (off + int_size it ≤ enum_size EL 𝔄l)%nat ∧
  (off + int_size it ≤ enum_off EL 𝔄l i ∨ enum_off EL 𝔄l i + syn_bsize (𝔄l !!ₗ i) ≤ off)%nat.
Proof.
  intros Hr. destruct (enum_vars_lookup EL 𝔄l i) as [tg Hv].
  destruct (enum_layout_ok_syn EL 𝔄l) as (_ & Ht & _).
  rewrite /discr_tag_only Forall_forall in Ht. destruct (Ht _ Hr) as [Hsz Hall].
  split; [done|]. rewrite /syn_bsize. exact (Forall_lookup_1 _ _ _ _ Hall Hv).
Qed.

Lemma list_slice_app_le {A} off k (l1 l2: list A) :
  (off + k ≤ length l1)%nat → list_slice off k (l1 ++ l2) = list_slice off k l1.
Proof.
  intros. rewrite /list_slice drop_app_le; [|lia]. rewrite take_app_le; [done|].
  rewrite length_drop. lia.
Qed.

Lemma list_slice_app_ge {A} off k (l1 l2: list A) :
  (length l1 ≤ off)%nat → list_slice off k (l1 ++ l2) = list_slice (off - length l1) k l2.
Proof. intros. by rewrite /list_slice drop_app_ge. Qed.

(** The rest of the bytes of variant [i]: the bytes [b1] before the payload and [b2]
    after it, from which (with the payload erased) the discriminator reads [i]. *)
Definition enum_rest_ok EL 𝔄l (i: fin (length 𝔄l)) (b1 b2: list abyte) : Prop :=
  length b1 = enum_off EL 𝔄l i ∧
  (length b1 + syn_bsize (𝔄l !!ₗ i) + length b2 = enum_size EL 𝔄l)%nat ∧
  decode_discr (enum_discr EL 𝔄l) (b1 ++ replicate (syn_bsize (𝔄l !!ₗ i)) Uninit ++ b2) =
    Some (Z.of_nat i).

(** The discriminant does not depend on the payload. *)
Lemma decode_discr_enum_payload EL 𝔄l (i: fin (length 𝔄l)) b1 b2 bp bp' :
  length b1 = enum_off EL 𝔄l i → length bp = syn_bsize (𝔄l !!ₗ i) → length bp' = length bp →
  decode_discr (enum_discr EL 𝔄l) (b1 ++ bp ++ b2) =
    decode_discr (enum_discr EL 𝔄l) (b1 ++ bp' ++ b2).
Proof.
  intros H1 Hp Hp'. apply discr_eval_agree. intros off it Hr.
  destruct (enum_reads EL 𝔄l i off it Hr) as [_ [Hlt|Hge]]; rewrite /bytes_reader.
  - rewrite !list_slice_app_le //; lia.
  - rewrite !(list_slice_app_ge _ _ b1); [|lia..].
    rewrite (list_slice_app_ge _ _ bp); [|lia]. rewrite (list_slice_app_ge _ _ bp'); [|lia].
    by rewrite Hp'.
Qed.

Lemma syn_val_pinj {EL 𝔄l} (i: fin (length 𝔄l)) (y: ~~(𝔄l !!ₗ i)) :
  syn_val (𝔄:=enumₛ EL 𝔄l) (pinj i y) = VVariant (Z.of_nat (fin_to_nat i)) <$> syn_val y.
Proof. by rewrite /= psum_map1_pinj to_xsum_pinj. Qed.

Lemma syn_bytes_enum {EL 𝔄l} (i: fin (length 𝔄l)) (y: ~~(𝔄l !!ₗ i)) bs :
  syn_bytes (𝔄:=enumₛ EL 𝔄l) (pinj i y) bs ↔
  ∃ b1 bp b2, bs = b1 ++ bp ++ b2 ∧ enum_rest_ok EL 𝔄l i b1 b2 ∧ syn_bytes y bp.
Proof.
  have Hb := enum_off_bound EL 𝔄l i. destruct (enum_vars_lookup EL 𝔄l i) as [tg Hv].
  rewrite /syn_bytes syn_val_pinj syn_mty_enum decode_value_enum.
  set o := enum_off EL 𝔄l i in Hb Hv |- *. set n := syn_bsize (𝔄l !!ₗ i) in Hb |- *. split.
  - intros (v & Hv' & Hd). destruct (syn_val y) as [w|] eqn:Hw; [|done]. simpl in Hv'.
    simplify_eq. case_decide as Hlen; [|done].
    destruct (decode_discr _ bs) as [t|] eqn:Ht; [|done]. simpl in Hd.
    case_decide as Ht0; [|done].
    destruct (enum_vars EL 𝔄l !! Z.to_nat t) as [[[vm o'] tg']|] eqn:Hvm; [|done].
    simpl in Hd. destruct (decode_value vm _) as [w'|] eqn:Hw'; [|done].
    simpl in Hd. simplify_eq. rewrite Nat2Z.id Hv in Hvm. injection Hvm as <- <- <-.
    have Hsplit : bs = take o bs ++ list_slice o n bs ++ drop (o + n) bs.
    { by rewrite /list_slice -{1}(take_drop o bs) -{1}(take_drop n (drop o bs)) drop_drop. }
    exists (take o bs), (list_slice o n bs), (drop (o + n) bs). split; [done|]. split.
    + split_and!; [rewrite length_take; lia|rewrite length_take length_drop; lia|].
      rewrite -Ht [in decode_discr _ bs]Hsplit. apply (decode_discr_enum_payload EL 𝔄l i).
      * rewrite length_take. lia.
      * by rewrite length_replicate.
      * rewrite /list_slice length_take length_drop length_replicate. lia.
    + by exists w.
  - intros (b1 & bp & b2 & -> & (H1 & H2 & Hd) & (w & Hw & Hp)).
    exists (VVariant (Z.of_nat (fin_to_nat i)) w). rewrite Hw. split; [done|].
    have Hlp : length bp = n by apply decode_value_length in Hp.
    rewrite decide_True; [|rewrite !length_app; lia].
    rewrite (decode_discr_enum_payload EL 𝔄l i b1 b2 bp (replicate n Uninit)) //;
      [|by rewrite length_replicate].
    rewrite Hd /= decide_True; [|lia]. rewrite Nat2Z.id Hv /=.
    have ->: o = length b1 by rewrite H1.
    rewrite /list_slice drop_app_length. change (mty_size (syn_mty (𝔄l !!ₗ i))) with n.
    by rewrite -Hlp take_app_length Hp.
Qed.

(** ** Reading the discriminant of an enum ([GetDiscr]) from the rest of its bytes. *)
Lemma enum_rest_chunks EL 𝔄l (i: fin (length 𝔄l)) b1 b2 :
  enum_rest_ok EL 𝔄l i b1 b2 →
  discr_eval (chunks_reader [(0%nat, b1);
      ((enum_off EL 𝔄l i + syn_bsize (𝔄l !!ₗ i))%nat, b2)]) (enum_discr EL 𝔄l) =
    Some (Z.of_nat (fin_to_nat i)).
Proof.
  intros (H1 & H2 & Hd). rewrite -Hd. symmetry. apply discr_eval_agree. intros off it Hr.
  destruct (enum_reads EL 𝔄l i off it Hr) as [Hsz Hor]; rewrite /bytes_reader /=.
  case_decide as Hin.
  - rewrite Nat.sub_0_r list_slice_app_le //. lia.
  - destruct Hor as [?|Hge]; [lia|]. rewrite decide_True; [|lia].
    rewrite list_slice_app_ge; [|lia]. rewrite list_slice_app_ge; rewrite length_replicate; [|lia].
    do 2 f_equal. lia.
Qed.

Section get_discr_enum.
  Context `{!lrustGS Σ}.

  Lemma wp_get_discr_enum E EL 𝔄l (i: fin (length 𝔄l)) l b1 b2 Φ :
    enum_rest_ok EL 𝔄l i b1 b2 →
    l ↦b b1 -∗ (l +ₗ (enum_off EL 𝔄l i + syn_bsize (𝔄l !!ₗ i))%nat) ↦b b2 -∗
    (l ↦b b1 -∗ (l +ₗ (enum_off EL 𝔄l i + syn_bsize (𝔄l !!ₗ i))%nat) ↦b b2 -∗
      Φ (MLitV (VInt (Z.of_nat (fin_to_nat i))))) -∗
    WP GetDiscr (syn_mty (enumₛ EL 𝔄l)) (MLit (VPtr l)) @ E {{ Φ }}.
  Proof.
    iIntros (Hr) "H1 H2 HΦ". rewrite syn_mty_enum.
    iApply (wp_get_discr _ _ _ _ _ _ [(0%nat, b1); (_, b2)] with "[H1 H2]").
    - by apply enum_rest_chunks.
    - rewrite /chunks_own /= shift_loc_0. iFrame.
    - iIntros "(H1 & H2 & _)". rewrite /= shift_loc_0. iApply ("HΦ" with "H1 H2").
  Qed.

  (** Through a guard of the rest of the bytes, which may give other bytes at each opening:
      for a discriminator with at most one read ([enum_discr_depth1]). *)
  Lemma wp_get_discr_enum_guarded E EL 𝔄l (i: fin (length 𝔄l)) l G P dg Φ :
    ↑naN ⊆ E → (discr_depth (enum_discr EL 𝔄l) ≤ 1)%nat →
    (G &&{↑naN; dg}&&> P) -∗
    □ (P -∗ ∃ b1 b2, ⌜enum_rest_ok EL 𝔄l i b1 b2⌝ ∗ l ↦b b1 ∗
        (l +ₗ (enum_off EL 𝔄l i + syn_bsize (𝔄l !!ₗ i))%nat) ↦b b2 ∗
        (l ↦b b1 -∗ (l +ₗ (enum_off EL 𝔄l i + syn_bsize (𝔄l !!ₗ i))%nat) ↦b b2 -∗ P)) -∗
    G -∗ £(2 * dg) -∗ (G -∗ Φ (MLitV (VInt (Z.of_nat (fin_to_nat i))))) -∗
    WP GetDiscr (syn_mty (enumₛ EL 𝔄l)) (MLit (VPtr l)) @ E {{ Φ }}.
  Proof.
    iIntros (? Hd) "#Guard #HP G £ HΦ". rewrite syn_mty_enum.
    set o := (enum_off EL 𝔄l i + syn_bsize (𝔄l !!ₗ i))%nat.
    iApply (wp_get_discr_guarded_all _ _ _ _ _ l G P
      (λ cs, ∃ b1 b2, cs = [(0%nat, b1); (o, b2)] ∧ enum_rest_ok EL 𝔄l i b1 b2) dg 1
      with "Guard [] G [£] HΦ"); [done| |done| | |by rewrite Nat.mul_1_r].
    - apply discr_eval_all_depth1; [done| |].
      + destruct (enum_vars_lookup EL 𝔄l i) as [tg Hv]. destruct (enum_layout_ok_syn EL 𝔄l) as (_ & _ & Hok).
        exists (tagger_reader tg). exact (discr_ok_lookup _ _ _ _ Hok Hv).
      + intros off it z (cs & (b1 & b2 & -> & Hr) & Hz). exists (chunks_reader [(0%nat, b1); (o, b2)]).
        split; [done|]. by apply enum_rest_chunks.
    - intros off it Hr cs (b1 & b2 & -> & Hrest).
      eapply discr_reads_depth1; [done|done|]. by apply enum_rest_chunks.
    - iIntros "!> HPx". iDestruct ("HP" with "HPx") as (b1 b2 Hr) "(B1 & B2 & Cl)".
      iExists [(0%nat, b1); (o, b2)]. iSplit; [by eauto|].
      rewrite /chunks_own /= shift_loc_0. iFrame "B1 B2". iIntros "(B1 & B2 & _)".
      iApply ("Cl" with "B1 B2").
  Qed.
End get_discr_enum.

Lemma enum_discr_depth1 EL 𝔄l :
  (discr_depth EL.(el_discr) ≤ 1)%nat → (discr_depth (enum_discr EL 𝔄l) ≤ 1)%nat.
Proof.
  intros. rewrite /enum_discr /enum_ly /enum_lay. case_decide; [done|].
  rewrite /tagged_layout. cbn [el_discr]. rewrite discr_depth_seq. lia.
Qed.

(** * Fancy bytes (§10 step 4 of [design_docs/pcell-multibyte-cells.md])

[syn_fbytes R x fbs]: the fancy bytes [fbs] (each a byte-cell or an abstract byte)
represent the value [x], with the static registry [R]: they have the size of [𝔄], and
represent the fancy value of [x] ([syn_fval x], where a cell [pcellₛ m] is its group) at
[syn_mty 𝔄] ([frepr]). For a value with a MiniRust value ([syn_val x = Some v]), and so
for every value of a type without cells ([syn_nocell 𝔄]), these are the plain bytes of
[syn_bytes] ([syn_fbytes_val], [syn_fbytes_nocell]). The lemmas below split fancy bytes
along the layout, as those above do for plain bytes: structs ([syn_fbytes_struct]) and
enums ([syn_fbytes_enum]; the rest of the bytes is plain). *)

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

Lemma syn_fval_pinj {EL 𝔄l} (i: fin (length 𝔄l)) (y: ~~(𝔄l !!ₗ i)) :
  syn_fval (𝔄:=enumₛ EL 𝔄l) (pinj i y) = FVVariant (Z.of_nat (fin_to_nat i)) <$> syn_fval y.
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

(** *** Enums: the rest of the bytes is plain. *)
Lemma syn_fbytes_enum {EL 𝔄l} R (i: fin (length 𝔄l)) (y: ~~(𝔄l !!ₗ i)) fbs :
  syn_fbytes (𝔄:=enumₛ EL 𝔄l) R (pinj i y) fbs ↔
  ∃ b1 fp b2, fbs = (inr <$> b1) ++ fp ++ (inr <$> b2) ∧ enum_rest_ok EL 𝔄l i b1 b2 ∧
    syn_fbytes R y fp.
Proof.
  have Hb := enum_off_bound EL 𝔄l i. destruct (enum_vars_lookup EL 𝔄l i) as [tg Hv].
  rewrite /syn_fbytes syn_fval_pinj syn_bsize_enum syn_mty_enum.
  set o := enum_off EL 𝔄l i in Hb Hv |- *. set n := syn_bsize (𝔄l !!ₗ i) in Hb |- *. split.
  - intros (Hlen & fv & Hfv & Hrep).
    destruct (syn_fval y) as [fy|] eqn:Hfy; [|done]. simpl in Hfv. injection Hfv as <-.
    apply frepr_enum_iff in Hrep as (_ & Hd & _ & vm & o' & tg' & Hvm & Hp & Hpad).
    rewrite Nat2Z.id Hv in Hvm. injection Hvm as <- <- <-.
    change (mty_size (syn_mty (𝔄l !!ₗ i))) with n in Hp. change (mty_size (syn_mty (𝔄l !!ₗ i))) with n in Hpad.
    destruct (plain_fbytes (take o fbs)) as [b1 Hb1].
    { intros j fb. rewrite lookup_take_Some. intros [Hj ?]. apply (Hpad _ fb Hj). lia. }
    destruct (plain_fbytes (drop (o + n) fbs)) as [b2 Hb2].
    { intros j fb. rewrite lookup_drop. intros Hj. apply (Hpad _ fb Hj). lia. }
    have Hsplit : fbs = take o fbs ++ list_slice o n fbs ++ drop (o + n) fbs.
    { by rewrite /list_slice -{1}(take_drop o fbs) -{1}(take_drop n (drop o fbs)) drop_drop. }
    have Hl1 : length b1 = o.
    { rewrite -(length_fmap (@inr positive abyte) b1) -Hb1 length_take. lia. }
    have Hl2 : length b2 = (enum_size EL 𝔄l - (o + n))%nat.
    { rewrite -(length_fmap (@inr positive abyte) b2) -Hb2 length_drop. lia. }
    have Hls : length (list_slice o n fbs) = n.
    { rewrite /list_slice length_take length_drop. lia. }
    exists b1, (list_slice o n fbs), b2. split; [by rewrite -Hb1 -Hb2|]. split.
    + split_and!; [done|lia|]. rewrite -Hd [in fb_erase <$> fbs]Hsplit Hb1 Hb2 !fmap_app !fb_erase_plain.
      apply (decode_discr_enum_payload EL 𝔄l i); [done|by rewrite length_replicate|].
      by rewrite length_fmap Hls length_replicate.
    + split; [done|]. by exists fy.
  - intros (b1 & fp & b2 & -> & (H1 & H2 & Hd) & (Hlp & fy & Hfy & Hp)).
    split; [rewrite !length_app !length_fmap; lia|].
    rewrite Hfy. eexists. split; [done|]. apply frepr_enum_iff.
    split; [rewrite !length_app !length_fmap; lia|].
    split.
    { rewrite !fmap_app !fb_erase_plain.
      rewrite (decode_discr_enum_payload EL 𝔄l i b1 b2 _ (replicate n Uninit)) //;
        [by rewrite length_fmap|by rewrite length_replicate length_fmap]. }
    split; [lia|]. exists (syn_mty (𝔄l !!ₗ i)), o, tg. rewrite Nat2Z.id Hv. split; [done|].
    change (mty_size (syn_mty (𝔄l !!ₗ i))) with n. split.
    + have ->: o = length ((inr <$> b1) : list (positive + abyte)) by rewrite length_fmap H1.
      rewrite /list_slice drop_app_length.
      by rewrite -Hlp take_app_length.
    + intros j fb Hj Hn. destruct (decide (j < o)%nat).
      * rewrite lookup_app_l in Hj; [|rewrite length_fmap; lia].
        rewrite list_lookup_fmap in Hj. destruct (b1 !! _); simplify_eq/=. by eexists.
      * rewrite lookup_app_r in Hj; [|rewrite length_fmap; lia].
        rewrite lookup_app_r in Hj; [|rewrite length_fmap; lia].
        rewrite list_lookup_fmap in Hj. destruct (b2 !! _); simplify_eq/=. by eexists.
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

Lemma mcells_enum_pinj {EL 𝔄l} (i: fin (length 𝔄l)) (y: ~~(𝔄l !!ₗ i)) fv :
  syn_fval (𝔄:=enumₛ EL 𝔄l) (pinj i y) = Some fv → ∃ fv', syn_fval y = Some fv' ∧
  mcells (syn_mty (enumₛ EL 𝔄l)) fv =
    mshift (enum_off EL 𝔄l i) (mcells (syn_mty (𝔄l !!ₗ i)) fv').
Proof.
  rewrite syn_fval_pinj syn_mty_enum. intros (fv' & Hfv' & ->)%fmap_Some.
  exists fv'. split; [done|]. destruct (enum_vars_lookup EL 𝔄l i) as [tg Hv].
  rewrite mcells_enum Nat2Z.id Hv. done.
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
