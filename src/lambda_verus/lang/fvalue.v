(** * Fancy MiniRust values

The values held by cells (see [design_docs/pcell-multibyte-cells.md]; since phase 5 of
[design_docs/guarded-mutable-borrows-plan.md] there is no physical cell heap, and the cells
are instances of guarded mutable borrows: the registry [R] and its byte-cells only name the
positions of the cells in fancy bytes, for [frepr] in [gcont], [typing/gcont.v]). A _fancy
value_ ([FValue]) is a MiniRust [Value] that may embed cells: [FVCell g] stands for the
current value of the cell [g]. A registry [R : gmap gid (mty * list positive)] records for
each cell its MiniRust type [m_g] and its byte-cells [cs_g] (one per byte).

- [frepr R m fbs fv]: the _fancy bytes_ [fbs] (each a byte-cell or an abstract byte)
  represent [fv] at the MiniRust type [m]: a cell [FVCell g] must sit at a position whose
  sub-type is [m_g] (a tuple field, an enum payload or the whole value: alignment
  requirement A), and occupy exactly the byte-cells [cs_g]; the other parts are plain bytes
  that decode as [decode_value] does.
- [fv_sub], [fv_upd]: sub-values and their replacement; [fb_mix]: fancy bytes with new
  plain bytes. *)
From lrust.lang Require Export minirust.
From stdpp Require Import ssreflect.
Set Default Proof Using "Type".

(** ** Fancy values *)
Inductive FValue : Set :=
| FVInt (z : Z)
| FVBool (b : bool)
| FVPtr (l : loc)
| FVTuple (fvs : list FValue)
| FVVariant (tag : Z) (data : FValue)
| FVCell (g : positive).

Lemma FValue_ind' (P : FValue → Prop) :
  (∀ z, P (FVInt z)) → (∀ b, P (FVBool b)) → (∀ l, P (FVPtr l)) →
  (∀ fvs, Forall P fvs → P (FVTuple fvs)) →
  (∀ t d, P d → P (FVVariant t d)) → (∀ g, P (FVCell g)) →
  ∀ fv, P fv.
Proof.
  intros Hi Hb Hp Ht Hv Hc.
  refine (fix FIX fv := match fv with
    | FVInt z => Hi z | FVBool b => Hb b | FVPtr l => Hp l
    | FVTuple fvs => Ht fvs ((fix go fvs := match fvs return Forall P fvs with
        | [] => @List.Forall_nil _ P | fv :: fvs => @List.Forall_cons _ P fv fvs (FIX fv) (go fvs) end) fvs)
    | FVVariant t d => Hv t d (FIX d)
    | FVCell g => Hc g
    end).
Qed.

Global Instance FValue_inhabited : Inhabited FValue := populate (FVTuple []).

(** A value without cells. *)
Fixpoint fv_lift (v : Value) : FValue :=
  match v with
  | VInt z => FVInt z
  | VBool b => FVBool b
  | VPtr l => FVPtr l
  | VTuple vs => FVTuple (map fv_lift vs)
  | VVariant t d => FVVariant t (fv_lift d)
  end.

(** The groups that a fancy value embeds. *)
Fixpoint fv_cells (fv : FValue) : list positive :=
  match fv with
  | FVTuple fvs => concat (map fv_cells fvs)
  | FVVariant _ d => fv_cells d
  | FVCell g => [g]
  | _ => []
  end.

Lemma fv_cells_lift v : fv_cells (fv_lift v) = [].
Proof.
  induction v as [| | |vs IH|t d IH] using Value_ind'; simpl; try done.
  induction IH as [|v vs Hv _ IH']; [done|]. by rewrite /= Hv IH'.
Qed.

Lemma fv_cells_tuple fvs k fv g :
  fvs !! k = Some fv → g ∈ fv_cells fv → g ∈ fv_cells (FVTuple fvs).
Proof.
  intros Hk Hg. rewrite /= elem_of_list_In in_concat. exists (fv_cells fv).
  split; [|by apply elem_of_list_In]. apply in_map, elem_of_list_In. by eapply elem_of_list_lookup_2.
Qed.

Lemma fv_lift_inj v v' : fv_lift v = fv_lift v' → v = v'.
Proof.
  revert v'. induction v as [z|b|l|vs IH|t d IH] using Value_ind';
    intros [z'|b'|l'|vs'|t' d'] Heq; simplify_eq/=; try done.
  - f_equal. revert vs' Heq. induction IH as [|v vs Hv _ IHvs]; intros [|v' vs'] Heq;
      simplify_eq/=; [done|]. f_equal; [by apply Hv|by apply IHvs].
  - f_equal. by apply IH.
Qed.

(** ** Fancy bytes and their representation *)
Section frepr.
  Implicit Types (fbs : list (positive + AbstractByte)) (bs : list (AbstractByte)).
  Implicit Types (R : gmap positive (mty * list positive)).

  Definition is_plain (fb : positive + AbstractByte) : Prop := ∃ b, fb = inr b.

  (** The plain bytes of fancy bytes, with the byte-cells as [Uninit]. *)
  Definition fb_erase (fb : positive + AbstractByte) : AbstractByte :=
    match fb with inl _ => Uninit | inr b => b end.

  (** The position [i] is in one of the fields [fs]. *)
  Definition in_field (fs : list (nat * mty)) (i : nat) : Prop :=
    ∃ f, f ∈ fs ∧ (f.1 ≤ i < f.1 + mty_size f.2)%nat.

  Global Instance in_field_dec fs i : Decision (in_field fs i).
  Proof.
    rewrite /in_field.
    destruct (decide (Exists (λ f : nat * mty, (f.1 ≤ i < f.1 + mty_size f.2)%nat) fs)) as [H|H].
    - left. by apply Exists_exists in H.
    - right. intros Hx. apply H. by apply Exists_exists.
  Defined.

  Inductive frepr R : mty → list (positive + AbstractByte) → FValue → Prop :=
  | frepr_cell m g cs : R !! g = Some (m, cs) → frepr R m (inl <$> cs) (FVCell g)
  | frepr_plain m bs v : decode_value m bs = Some v → frepr R m (inr <$> bs) (fv_lift v)
  | frepr_tuple fs sz al fbs fvs :
      length fbs = sz → length fvs = length fs →
      (∀ k f fv, fs !! k = Some f → fvs !! k = Some fv →
         frepr R f.2 (list_slice f.1 (mty_size f.2) fbs) fv) →
      (∀ i fb, fbs !! i = Some fb → ¬ in_field fs i → is_plain fb) →
      frepr R (MTuple fs sz al) fbs (FVTuple fvs)
  | frepr_enum vars d sz al fbs t vm o tg w :
      length fbs = sz →
      decode_discr d (fb_erase <$> fbs) = Some t → (0 ≤ t)%Z →
      vars !! Z.to_nat t = Some (vm, o, tg) →
      frepr R vm (list_slice o (mty_size vm) fbs) w →
      (∀ i fb, fbs !! i = Some fb → ¬ (o ≤ i < o + mty_size vm)%nat → is_plain fb) →
      frepr R (MEnum vars d sz al) fbs (FVVariant t w).

  Lemma frepr_mono R R' m fbs fv : R ⊆ R' → frepr R m fbs fv → frepr R' m fbs fv.
  Proof.
    intros Hsub. induction 1; econstructor; eauto. by eapply lookup_weaken.
  Qed.

End frepr.

(** ** Sub-values and their replacement

A sub-value of a fancy value [fv] at MiniRust type [m] sits at a tuple field, an enum
payload (of the current variant) or the whole value, at a byte offset [o] and with a
MiniRust type [m'] (alignment requirement A). *)
Inductive fv_sub : mty → FValue → nat → mty → FValue → Prop :=
| fv_sub_here m fv : fv_sub m fv 0 m fv
| fv_sub_field fs sz al fvs k off fm fvk o m' fv' :
    fs !! k = Some (off, fm) → fvs !! k = Some fvk → fv_sub fm fvk o m' fv' →
    fv_sub (MTuple fs sz al) (FVTuple fvs) (off + o) m' fv'
| fv_sub_payload vars d sz al t w vm off tg o m' fv' :
    vars !! Z.to_nat t = Some (vm, off, tg) → fv_sub vm w o m' fv' →
    fv_sub (MEnum vars d sz al) (FVVariant t w) (off + o) m' fv'.

(** [fv_upd m fv o m' fv' fvn]: [fvn] is [fv] with the sub-value at [o] (of type [m'])
    replaced by [fv']. *)
Inductive fv_upd : mty → FValue → nat → mty → FValue → FValue → Prop :=
| fv_upd_here m fv fv' : fv_upd m fv 0 m fv' fv'
| fv_upd_field fs sz al fvs k off fm fvk o m' fv' fvk' :
    fs !! k = Some (off, fm) → fvs !! k = Some fvk → fv_upd fm fvk o m' fv' fvk' →
    fv_upd (MTuple fs sz al) (FVTuple fvs) (off + o) m' fv' (FVTuple (<[k := fvk']> fvs))
| fv_upd_payload vars d sz al t w vm off tg o m' fv' w' :
    vars !! Z.to_nat t = Some (vm, off, tg) → fv_upd vm w o m' fv' w' →
    fv_upd (MEnum vars d sz al) (FVVariant t w) (off + o) m' fv' (FVVariant t w').

Lemma fv_sub_bound m fv o m' fv' :
  fv_sub m fv o m' fv' → mty_wf m → (o + mty_size m' ≤ mty_size m)%nat.
Proof.
  induction 1 as [|fs sz al fvs k off fm fvk o m' fv' Hk Hfvk Hsub IH
    |vars d sz al t w vm off tg o m' fv' Hvm Hsub IH]; intros Hwf; [lia| |].
  - inversion Hwf as [| | |? ? ? Hdisj Hin Hwfs|]; simplify_eq.
    have := Forall_lookup_1 _ _ _ _ Hin Hk. have := IH (Forall_lookup_1 _ _ _ _ Hwfs Hk).
    simpl. lia.
  - apply mty_wf_enum_inv in Hwf as [[Hvars _] Hwfs].
    destruct (Forall_lookup_1 _ _ _ _ Hvars Hvm) as [Hsz _].
    have := IH (Forall_lookup_1 _ _ _ _ Hwfs Hvm). simpl in *. lia.
Qed.

Lemma fv_upd_sub m fv o m' fv' fvn : fv_upd m fv o m' fv' fvn → ∃ fvo, fv_sub m fv o m' fvo.
Proof. induction 1 as [| |]; naive_solver eauto using fv_sub. Qed.

Lemma fv_upd_bound m fv o m' fv' fvn :
  fv_upd m fv o m' fv' fvn → mty_wf m → (o + mty_size m' ≤ mty_size m)%nat.
Proof. intros [fvo Hsub]%fv_upd_sub. by eapply fv_sub_bound. Qed.

Lemma list_lookup_map {A B} (f : A → B) (l : list A) k : map f l !! k = f <$> l !! k.
Proof. revert k. induction l as [|x l IH]; intros [|k]; simpl; auto. Qed.

Lemma fv_lift_tuple_inv v fvs : fv_lift v = FVTuple fvs → ∃ vs, v = VTuple vs ∧ fvs = map fv_lift vs.
Proof. destruct v; simpl; try done. intros [= <-]. eauto. Qed.
Lemma fv_lift_variant_inv v t d : fv_lift v = FVVariant t d → ∃ dv, v = VVariant t dv ∧ d = fv_lift dv.
Proof. destruct v; simpl; try done. intros [= <- <-]. eauto. Qed.

(** Slices and insertions. *)
Lemma lookup_list_slice {A} o n (l : list A) i :
  list_slice o n l !! i = if decide (i < n)%nat then l !! (o + i)%nat else None.
Proof.
  rewrite /list_slice. case_decide.
  - by rewrite lookup_take // lookup_drop.
  - rewrite lookup_take_ge //. lia.
Qed.

Lemma list_slice_slice {A} o n off N (l : list A) :
  (o + n ≤ N)%nat → list_slice o n (list_slice off N l) = list_slice (off + o) n l.
Proof.
  intros Hn. apply list_eq. intros i. rewrite !lookup_list_slice.
  repeat case_decide; try done; try lia. f_equal. lia.
Qed.

Lemma list_slice_inserts_out {A} o n o' (e l : list A) :
  (o' + length e ≤ o ∨ o + n ≤ o')%nat →
  list_slice o n (list_inserts o' e l) = list_slice o n l.
Proof.
  intros Ho. apply list_eq. intros i. rewrite !lookup_list_slice. case_decide; [|done].
  destruct Ho; [rewrite list_lookup_inserts_ge //; lia|rewrite list_lookup_inserts_lt //; lia].
Qed.

Lemma list_slice_inserts_in {A} o n o' (e l : list A) :
  (o + n ≤ length l)%nat → (o' + length e ≤ n)%nat →
  list_slice o n (list_inserts (o + o') e l) = list_inserts o' e (list_slice o n l).
Proof.
  intros Hl He. apply list_eq. intros i. rewrite lookup_list_slice.
  destruct (decide (i < o')%nat).
  { rewrite (list_lookup_inserts_lt _ o' _ i) // lookup_list_slice. case_decide; [|done].
    rewrite list_lookup_inserts_lt //. lia. }
  destruct (decide (i < o' + length e)%nat).
  { rewrite decide_True; [|lia].
    rewrite (list_lookup_inserts _ (o + o') e (o + i)); [|lia|lia].
    rewrite (list_lookup_inserts _ o' e i); [|lia|rewrite /list_slice length_take length_drop; lia].
    f_equal. lia. }
  rewrite (list_lookup_inserts_ge _ o' _ i); [|lia]. rewrite lookup_list_slice. case_decide; [|done].
  rewrite list_lookup_inserts_ge //. lia.
Qed.

Section frepr_ops.
  Implicit Types (fbs : list (positive + AbstractByte)) (bs : list (AbstractByte)).
  Implicit Types (R : gmap positive (mty * list positive)).

  (** The registry gives each group as many cells as its type has bytes. *)
  Definition reg_wf R : Prop := ∀ g m cs, R !! g = Some (m, cs) → length cs = mty_size m.

  Lemma frepr_length R m fbs fv : reg_wf R → frepr R m fbs fv → length fbs = mty_size m.
  Proof.
    intros HR. induction 1 as [m g cs Hg|m bs v Hdec|fs sz al fbs fvs Hlen|vars d sz al fbs t vm o tg w Hlen];
      simpl; try done.
    - rewrite length_fmap. by eapply HR.
    - rewrite length_fmap. by eapply decode_value_length.
  Qed.

  Lemma frepr_plain_of_nocells R m fbs fv :
    frepr R m fbs fv → fv_cells fv = [] → ∀ fb, fb ∈ fbs → is_plain fb.
  Proof.
    induction 1 as [m g cs Hg|m bs v Hdec|fs sz al fbs fvs Hlen Hlenf Hfs IH Hpad
      |vars d sz al fbs t vm o tg w Hlen Hd Ht0 Hvm Hw IH Hpad]; simpl; try done.
    - intros _ fb (b & -> & _)%elem_of_list_fmap. by eexists.
    - intros Hc fb (i & Hi)%elem_of_list_lookup.
      destruct (decide (in_field fs i)) as [(f & Hf & Hfi)|]; [|by eapply Hpad].
      apply elem_of_list_lookup in Hf as [k Hk].
      destruct (fvs !! k) as [fvk|] eqn:Hfvk; [|apply lookup_ge_None in Hfvk; apply lookup_lt_Some in Hk; lia].
      apply (IH k f fvk Hk Hfvk).
      + apply elem_of_nil_inv. intros g Hg. have : g ∈ fv_cells (FVTuple fvs) by eapply fv_cells_tuple.
        rewrite /= Hc. apply not_elem_of_nil.
      + apply elem_of_list_lookup. exists (i - f.1)%nat. rewrite lookup_list_slice decide_True; [|lia].
        rewrite -Hi. f_equal. lia.
    - intros Hc fb (i & Hi)%elem_of_list_lookup.
      destruct (decide (o ≤ i < o + mty_size vm)%nat); [|by eapply Hpad].
      apply IH; [done|]. apply elem_of_list_lookup. exists (i - o)%nat.
      rewrite lookup_list_slice decide_True; [|lia]. rewrite -Hi. f_equal. lia.
  Qed.

  Lemma fb_erase_plain (bs : list AbstractByte) : fb_erase <$> (inr <$> bs) = bs.
  Proof. rewrite -list_fmap_compose. apply list_fmap_id. Qed.

  (** A representation of a value without cells is plain bytes that decode to it. *)
  Lemma frepr_lift R m fbs v :
    frepr R m fbs (fv_lift v) → ∃ bs, fbs = inr <$> bs ∧ decode_value m bs = Some v.
  Proof.
    intros Hrep.
    have Hpl := frepr_plain_of_nocells _ _ _ _ Hrep (fv_cells_lift v).
    assert (∃ bs, fbs = inr <$> bs) as [bs ->].
    { clear Hrep. induction fbs as [|fb fbs IH]; [by exists []|].
      destruct (Hpl fb) as [b ->]; [by left|]. destruct IH as [bs ->].
      { intros fb' ?. apply Hpl. by right. }
      by exists (b :: bs). }
    exists bs. split; [done|]. clear Hpl.
    remember (inr <$> bs) as fbs eqn:Hfbs. remember (fv_lift v) as fv eqn:Hfv.
    revert bs v Hfbs Hfv.
    induction Hrep as [m g cs Hg|m bs0 v0 Hdec|fs sz al fbs fvs Hlen Hlenf Hfs IH Hpad
      |vars d sz al fbs t vm o tg w Hlen Hd Ht0 Hvm Hw IH Hpad]; intros bs v Hfbs Hfv.
    - by destruct v.
    - apply (inj (fmap inr)) in Hfbs as ->. by apply fv_lift_inj in Hfv as ->.
    - destruct (fv_lift_tuple_inv _ _ (eq_sym Hfv)) as (vs & -> & ->).
      rewrite decode_value_tuple -Hlen Hfbs length_fmap decide_True //.
      apply fmap_Some_2, mapM_Some, Forall2_lookup. intros k.
      rewrite length_map in Hlenf.
      destruct (fs !! k) as [f|] eqn:Hf, (vs !! k) as [vk|] eqn:Hvk; simpl; try constructor.
      + apply (IH k f (fv_lift vk) Hf); [by rewrite list_lookup_map Hvk|by rewrite Hfbs /list_slice fmap_take fmap_drop|done].
      + apply lookup_ge_None in Hvk. apply lookup_lt_Some in Hf. lia.
      + apply lookup_ge_None in Hf. apply lookup_lt_Some in Hvk. lia.
    - destruct (fv_lift_variant_inv _ _ _ (eq_sym Hfv)) as (dv & -> & ->).
      rewrite decode_value_enum -Hlen Hfbs length_fmap decide_True //.
      rewrite Hfbs fb_erase_plain in Hd. rewrite Hd /= decide_True // Hvm /=.
      rewrite (IH _ dv) //. by rewrite Hfbs /list_slice fmap_take fmap_drop.
  Qed.

  (** The representation of a field, or of the payload of a variant. *)
  Lemma frepr_field R fs sz al fbs fvs k f fv :
    frepr R (MTuple fs sz al) fbs (FVTuple fvs) → fs !! k = Some f → fvs !! k = Some fv →
    frepr R f.2 (list_slice f.1 (mty_size f.2) fbs) fv.
  Proof.
    intros Hrep Hf Hfv. inversion Hrep as [|m bs v Hdec Hm Hbs Hv| |]; simplify_eq; [|eauto].
    destruct (fv_lift_tuple_inv _ _ Hv) as (vs & -> & ->).
    rewrite list_lookup_map in Hfv. destruct (vs !! k) as [vk|] eqn:Hvk; [|done].
    simpl in Hfv. injection Hfv as <-.
    move: Hdec. rewrite decode_value_tuple. case_decide; [|done].
    intros (vs' & Hvs & [= <-])%fmap_Some_1. apply mapM_Some in Hvs.
    have Hd := Forall2_lookup_lr _ _ _ _ _ _ Hvs Hf Hvk.
    rewrite /list_slice -fmap_drop -fmap_take. by apply frepr_plain.
  Qed.

  Lemma frepr_payload R vars d sz al fbs t w vm o tg :
    frepr R (MEnum vars d sz al) fbs (FVVariant t w) → vars !! Z.to_nat t = Some (vm, o, tg) →
    frepr R vm (list_slice o (mty_size vm) fbs) w.
  Proof.
    intros Hrep Hvm. inversion Hrep as [|m bs v Hdec Hm Hbs Hv| |]; simplify_eq.
    - destruct (fv_lift_variant_inv _ _ _ Hv) as (dv & -> & ->).
      move: Hdec. rewrite decode_value_enum. case_decide; [|done].
      destruct (decode_discr d bs) as [t'|]; simpl; [|done].
      case_decide; [|done]. destruct (vars !! Z.to_nat t') as [vv|] eqn:Hvm'; simpl; [|done].
      intros (d' & Hd & [= <- <-])%fmap_Some_1. rewrite Hvm in Hvm'. simplify_eq/=.
      rewrite /list_slice -fmap_drop -fmap_take. by apply frepr_plain.
    - by simplify_eq.
  Qed.

  Lemma frepr_sub R m fbs fv o m' fv' :
    reg_wf R → frepr R m fbs fv → fv_sub m fv o m' fv' → mty_wf m →
    frepr R m' (list_slice o (mty_size m') fbs) fv'.
  Proof.
    intros HR Hrep Hsub. revert fbs Hrep.
    induction Hsub as [m fv|fs sz al fvs k off fm fvk o m' fv' Hk Hfvk Hsub IH
      |vars d sz al t w vm off tg o m' fv' Hvm Hsub IH]; intros fbs Hrep Hwf.
    - rewrite /list_slice drop_0 take_ge //. by erewrite frepr_length.
    - inversion Hwf as [| | |? ? ? Hdisj Hin Hwfs|]; simplify_eq.
      have Hf := frepr_field _ _ _ _ _ _ k _ _ Hrep Hk Hfvk.
      have Hwffm := Forall_lookup_1 _ _ _ _ Hwfs Hk. simpl in Hwffm.
      have Hb := fv_sub_bound _ _ _ _ _ Hsub Hwffm.
      rewrite -(list_slice_slice _ _ _ (mty_size fm)) //. by apply IH.
    - apply mty_wf_enum_inv in Hwf as [_ Hwfs].
      have Hwfvm := Forall_lookup_1 _ _ _ _ Hwfs Hvm.
      have Hp := frepr_payload _ _ _ _ _ _ _ _ _ _ _ Hrep Hvm.
      have Hb := fv_sub_bound _ _ _ _ _ Hsub Hwfvm.
      rewrite -(list_slice_slice _ _ _ (mty_size vm)) //. by apply IH.
  Qed.

  Lemma frepr_tuple_inv R fs sz al fbs fvs :
    frepr R (MTuple fs sz al) fbs (FVTuple fvs) →
    length fbs = sz ∧ length fvs = length fs ∧
    (∀ i fb, fbs !! i = Some fb → ¬ in_field fs i → is_plain fb).
  Proof.
    intros Hrep. inversion Hrep as [|m bs v Hdec Hm Hbs Hv|? ? ? ? ? Hlen Hlenf Hfs Hpad|]; simplify_eq; [|done].
    destruct (fv_lift_tuple_inv _ _ Hv) as (vs & -> & ->).
    move: (Hdec). rewrite decode_value_tuple. case_decide as Hlen; [|done].
    intros (vs' & Hvs & [= <-])%fmap_Some_1. apply mapM_Some in Hvs.
    split_and!.
    - by rewrite length_fmap.
    - rewrite length_map. symmetry. by eapply Forall2_length.
    - intros i fb Hi _. rewrite list_lookup_fmap in Hi. destruct (bs !! i); simplify_eq/=. by eexists.
  Qed.

  Lemma frepr_enum_inv R vars d sz al fbs t w :
    frepr R (MEnum vars d sz al) fbs (FVVariant t w) →
    length fbs = sz ∧ decode_discr d (fb_erase <$> fbs) = Some t ∧ (0 ≤ t)%Z ∧
    ∃ vm o tg, vars !! Z.to_nat t = Some (vm, o, tg) ∧
    (∀ i fb, fbs !! i = Some fb → ¬ (o ≤ i < o + mty_size vm)%nat → is_plain fb).
  Proof.
    intros Hrep. inversion Hrep as [|m bs v Hdec Hm Hbs Hv| |]; simplify_eq; [|naive_solver].
    destruct (fv_lift_variant_inv _ _ _ Hv) as (dv & -> & ->).
    move: (Hdec). rewrite decode_value_enum. case_decide as Hlen; [|done].
    destruct (decode_discr d bs) as [t'|] eqn:Ht; simpl; [|done].
    case_decide; [|done]. destruct (vars !! Z.to_nat t') as [[[vm o] tg]|] eqn:Hvm; simpl; [|done].
    intros (d' & Hd & [= <- <-])%fmap_Some_1. split_and!.
    - by rewrite length_fmap.
    - by rewrite fb_erase_plain.
    - done.
    - exists vm, o, tg. split; [done|]. intros i fb Hi _. rewrite list_lookup_fmap in Hi.
      destruct (bs !! i); simplify_eq/=. by eexists.
  Qed.

  Lemma list_inserts_all {A} (e l : list A) : length e = length l → list_inserts 0 e l = e.
  Proof.
    intros Hlen. apply list_eq. intros i.
    destruct (decide (i < length e)%nat).
    - rewrite list_lookup_inserts; [|lia|lia]. f_equal. lia.
    - rewrite list_lookup_inserts_ge; [|lia]. rewrite !lookup_ge_None_2 //; lia.
  Qed.

  Lemma take_inserts_ge {A} n o (e l : list A) : (n ≤ o)%nat → take n (list_inserts o e l) = take n l.
  Proof.
    intros Hn. apply list_eq. intros i. destruct (decide (i < n)%nat).
    - rewrite !lookup_take // list_lookup_inserts_lt //. lia.
    - rewrite !lookup_take_ge //; lia.
  Qed.

  Lemma fmap_list_inserts {A B} (f : A → B) o (e l : list A) :
    f <$> list_inserts o e l = list_inserts o (f <$> e) (f <$> l).
  Proof.
    apply list_eq. intros i. rewrite list_lookup_fmap.
    destruct (decide (i < o)%nat); [rewrite !list_lookup_inserts_lt // list_lookup_fmap //|].
    destruct (decide (i < o + length e)%nat).
    - destruct (decide (i < length l)%nat).
      + rewrite !list_lookup_inserts; rewrite ?length_fmap; try lia. by rewrite list_lookup_fmap.
      + rewrite !lookup_ge_None_2 //; rewrite ?length_inserts ?length_fmap; lia.
    - rewrite !list_lookup_inserts_ge; rewrite ?length_fmap; try lia. by rewrite list_lookup_fmap.
  Qed.

  (** The discriminator of a well-formed enum reads no byte of the payload range of any
      variant, so changing bytes there does not change the discriminant. *)
  Lemma decode_discr_inserts_payload vars d sz al bs k vm o tg o' bs' :
    mty_wf (MEnum vars d sz al) → vars !! k = Some (vm, o, tg) →
    (o ≤ o')%nat → (o' + length bs' ≤ o + mty_size vm)%nat →
    decode_discr d (list_inserts o' bs' bs) = decode_discr d bs.
  Proof.
    intros Hwf Hvm Ho1 Ho2. apply mty_wf_enum_inv in Hwf as [(_ & Htag & _) _].
    apply discr_eval_agree. intros off it Hr. rewrite /bytes_reader.
    rewrite /discr_tag_only Forall_forall in Htag. have [_ Hdisj] := Htag _ Hr. simpl in Hdisj.
    have := Forall_lookup_1 _ _ _ _ Hdisj Hvm. simpl. intros Hor.
    rewrite list_slice_inserts_out //. lia.
  Qed.

  (** Replacing a plain sub-value with the plain bytes [bs] of a value [v]. *)
  Lemma frepr_upd R m fbs fv o m' fvn bs v :
    reg_wf R → frepr R m fbs fv → fv_upd m fv o m' (fv_lift v) fvn → mty_wf m →
    decode_value m' bs = Some v →
    frepr R m (list_inserts o (inr <$> bs) fbs) fvn.
  Proof.
    intros HR Hrep Hupd. remember (fv_lift v) as fl eqn:Hfl. revert fbs Hrep.
    induction Hupd as [m fv fv'|fs sz al fvs k off fm fvk o m' fv' fvk' Hk Hfvk Hupd IH
      |vars d sz al t w vm off tg o m' fv' w' Hvm Hupd IH]; intros fbs Hrep Hwf Hdec.
    - subst. rewrite list_inserts_all; [by apply frepr_plain|].
      rewrite length_fmap (decode_value_length _ _ _ Hdec). by erewrite frepr_length.
    - inversion Hwf as [| | |? ? ? Hdisj Hin Hwfs|]; simplify_eq.
      destruct (frepr_tuple_inv _ _ _ _ _ _ Hrep) as (Hlen & Hlenf & Hpad).
      have Hwffm := Forall_lookup_1 _ _ _ _ Hwfs Hk. simpl in Hwffm.
      have Hb := fv_upd_bound _ _ _ _ _ _ Hupd Hwffm.
      have Hin_k := Forall_lookup_1 _ _ _ _ Hin Hk. simpl in Hin_k.
      have HlenX : length (inr <$> bs : list (positive + AbstractByte)) = mty_size m'.
      { by rewrite length_fmap (decode_value_length _ _ _ Hdec). }
      apply frepr_tuple.
      + by rewrite length_inserts.
      + by rewrite length_insert.
      + intros j f fvj Hf Hfvj. destruct (decide (j = k)) as [->|Hne].
        * rewrite Hk in Hf. simplify_eq. rewrite list_lookup_insert in Hfvj; [|by eapply lookup_lt_Some].
          simplify_eq/=. rewrite list_slice_inserts_in; [|lia|lia].
          apply IH; [done| |done|done]. by eapply (frepr_field _ _ _ _ _ _ k (off, fm)).
        * rewrite list_lookup_insert_ne in Hfvj; [|done].
          rewrite list_slice_inserts_out; [by eapply frepr_field|].
          destruct (Hdisj j k f.1 f.2 off fm) as [?|?]; [done|by destruct f|done|lia|lia].
      + intros i fb Hi Hnf. rewrite list_lookup_inserts_Some in Hi.
        destruct Hi as [[_ Hi]|(Hr & _ & _)]; [by eapply Hpad|].
        exfalso. apply Hnf. exists (off, fm). split; [by eapply elem_of_list_lookup_2|]. simpl. lia.
    - have Hwf' := Hwf. apply mty_wf_enum_inv in Hwf' as [[Hvars _] Hwfs].
      have Hwfvm := Forall_lookup_1 _ _ _ _ Hwfs Hvm.
      have [Hsz _] := Forall_lookup_1 _ _ _ _ Hvars Hvm. simpl in Hsz.
      destruct (frepr_enum_inv _ _ _ _ _ _ _ _ Hrep) as (Hlen & Hd & Ht0 & vm' & o' & tg' & Hvm' & Hpad).
      rewrite Hvm in Hvm'. simplify_eq.
      have Hb := fv_upd_bound _ _ _ _ _ _ Hupd Hwfvm.
      have HlenX : length (inr <$> bs : list (positive + AbstractByte)) = mty_size m'.
      { by rewrite length_fmap (decode_value_length _ _ _ Hdec). }
      eapply (frepr_enum R vars d _ al _ t vm' o' tg'); try done.
      + by rewrite length_inserts.
      + rewrite fmap_list_inserts. erewrite decode_discr_inserts_payload; [done|exact Hwf|exact Hvm| |];
          rewrite ?length_fmap; rewrite ?length_fmap in HlenX; lia.
      + rewrite list_slice_inserts_in; [|lia|lia]. apply IH; [done| |done|done].
        by eapply frepr_payload.
      + intros i fb Hi Hge. rewrite list_lookup_inserts_Some in Hi.
        destruct Hi as [[_ Hi]|(Hr & _ & _)]; [by eapply Hpad|]. lia.
  Qed.

  Lemma elem_of_list_slice {A} (x : A) o n (l : list A) : x ∈ list_slice o n l → x ∈ l.
  Proof.
    intros (i & Hi)%elem_of_list_lookup. rewrite lookup_list_slice in Hi.
    case_decide; [|done]. by eapply elem_of_list_lookup_2.
  Qed.

  Lemma fv_cells_tuple_inv fvs g :
    g ∈ fv_cells (FVTuple fvs) → ∃ k fv, fvs !! k = Some fv ∧ g ∈ fv_cells fv.
  Proof.
    rewrite /= elem_of_list_In in_concat. intros (l & Hl & Hg).
    apply in_map_iff in Hl as (fv & <- & Hfv). apply elem_of_list_In in Hfv.
    apply elem_of_list_lookup_1 in Hfv as [k Hk]. exists k, fv. split; [done|].
    by apply elem_of_list_In.
  Qed.

  (** The byte-cells of a group embedded in a fancy value are among its fancy bytes. *)
  Lemma frepr_cells_in R m fbs fv g :
    frepr R m fbs fv → g ∈ fv_cells fv →
    ∃ m' cs, R !! g = Some (m', cs) ∧ ∀ c, c ∈ cs → inl c ∈ fbs.
  Proof.
    induction 1 as [m g' cs Hg'|m bs v Hdec|fs sz al fbs fvs Hlen Hlenf Hfs IH Hpad
      |vars d sz al fbs t vm o tg w Hlen Hd Ht0 Hvm Hw IH Hpad]; intros Hg.
    - apply elem_of_list_singleton in Hg as ->. exists m, cs. split; [done|].
      intros c Hc. apply elem_of_list_fmap. eauto.
    - rewrite fv_cells_lift in Hg. by apply not_elem_of_nil in Hg.
    - destruct (fv_cells_tuple_inv _ _ Hg) as (k & fvk & Hk & Hgk).
      destruct (fs !! k) as [f|] eqn:Hf; [|apply lookup_ge_None in Hf; apply lookup_lt_Some in Hk; lia].
      destruct (IH k f fvk Hf Hk Hgk) as (m' & cs & HR & Hin). exists m', cs. split; [done|].
      intros c Hc. eapply elem_of_list_slice. by apply Hin.
    - destruct (IH Hg) as (m' & cs & HR & Hin). exists m', cs. split; [done|].
      intros c Hc. eapply elem_of_list_slice. by apply Hin.
  Qed.
End frepr_ops.

(** ** More on sub-values *)
Lemma fv_sub_wf m fv o m' fv' : fv_sub m fv o m' fv' → mty_wf m → mty_wf m'.
Proof.
  induction 1 as [|fs sz al fvs k off fm fvk o m' fv' Hk Hfvk Hsub IH
    |vars d sz al t w vm off tg o m' fv' Hvm Hsub IH]; intros Hwf; [done| |].
  - inversion Hwf as [| | |? ? ? Hdisj Hin Hwfs|]; simplify_eq. apply IH.
    exact (Forall_lookup_1 _ _ _ _ Hwfs Hk).
  - apply mty_wf_enum_inv in Hwf as [_ Hwfs]. apply IH.
    exact (Forall_lookup_1 _ _ _ _ Hwfs Hvm).
Qed.

(** A fancy value without cells is a plain value. *)
Lemma fv_nocells_lift fv : fv_cells fv = [] → ∃ v, fv = fv_lift v.
Proof.
  induction fv as [z|b|l|fvs IH|t d IH|g] using FValue_ind'; simpl; intros Hc.
  - by exists (VInt z).
  - by exists (VBool b).
  - by exists (VPtr l).
  - assert (∃ vs, fvs = map fv_lift vs) as [vs ->]; [|by exists (VTuple vs)].
    revert Hc. induction IH as [|fv fvs Hfv _ IHl]; intros Hc; [by exists []|].
    simpl in Hc. apply app_eq_nil in Hc as [Hc1 Hc2].
    destruct (Hfv Hc1) as [v ->]. destruct (IHl Hc2) as [vs ->]. by exists (v :: vs).
  - destruct (IH Hc) as [v ->]. by exists (VVariant t v).
  - done.
Qed.

Section frepr_more.
  Implicit Types (fbs : list (positive + AbstractByte)) (bs : list (AbstractByte)).
  Implicit Types (R : gmap positive (mty * list positive)).

  (** A plain sub-value is represented by plain bytes. *)
  Lemma frepr_sub_plain R m fbs fv o m' fvs :
    reg_wf R → frepr R m fbs fv → fv_sub m fv o m' fvs → mty_wf m → fv_cells fvs = [] →
    ∃ bs v, list_slice o (mty_size m') fbs = inr <$> bs ∧ decode_value m' bs = Some v ∧
      fvs = fv_lift v.
  Proof.
    intros HR Hrep Hsub Hwf Hc. destruct (fv_nocells_lift _ Hc) as [v ->].
    have Hr := frepr_sub _ _ _ _ _ _ _ HR Hrep Hsub Hwf.
    destruct (frepr_lift _ _ _ _ Hr) as (bs & Hbs & Hd). eauto.
  Qed.

  (** ** Fancy bytes with new plain bytes

  [fb_mix fbs bs'] keeps the byte-cells of [fbs] and takes its plain bytes from [bs'] (the
  bytes of a value with cells after a typed move: the cells keep their positions, and the
  other bytes are those that the [Store] wrote). *)
  Definition fb_mix (fbs : list (positive + AbstractByte)) (bs' : list AbstractByte) :=
    zip_with (λ fb b, match fb with inl c => inl c | inr _ => inr b end) fbs bs'.

  Lemma fb_mix_length fbs bs' : length bs' = length fbs → length (fb_mix fbs bs') = length fbs.
  Proof. intros. rewrite /fb_mix length_zip_with. lia. Qed.

  Lemma fb_mix_lookup fbs bs' i fb b :
    fbs !! i = Some fb → bs' !! i = Some b →
    fb_mix fbs bs' !! i = Some (match fb with inl c => inl c | inr _ => inr b end).
  Proof. intros Hfb Hb. by rewrite /fb_mix lookup_zip_with Hfb Hb. Qed.

  Lemma fb_mix_cells cs bs' : length bs' = length cs → fb_mix (inl <$> cs) bs' = inl <$> cs.
  Proof.
    revert bs'. induction cs as [|c cs IH]; intros [|b bs'] Hlen; simpl in *; try done; try lia.
    f_equal. apply IH. lia.
  Qed.
End frepr_more.
