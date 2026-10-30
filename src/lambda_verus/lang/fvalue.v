(** * Fancy MiniRust values

The values held by multi-byte cells (see [design_docs/pcell-multibyte-cells.md]). A
_fancy value_ ([FValue]) is a MiniRust [Value] that may embed cells: [FVCell g] stands for
the current value of the cell group [g]. Groups are registered in a _static registry_
[R : gmap gid (mty * list positive)], which records for each group its MiniRust type
[m_g] and its byte-cells [cs_g] (one per byte); the _dynamic registry_
[ρ : gmap gid FValue] records the current fancy value of each group.

- [fval_erase ρ fv v] ([⌊fv⌋_ρ = v]): [v] is [fv] with every [FVCell g] replaced by the
  erasure of [ρ g], recursively.
- [frepr R m fbs fv]: the _fancy bytes_ [fbs] (each a byte-cell or an abstract byte)
  represent [fv] at the MiniRust type [m]. It depends only on the static registry: a cell
  [FVCell g] must sit at a position whose sub-type is [m_g] (a tuple field, an enum payload
  or the whole value: alignment requirement A), and occupy exactly the byte-cells [cs_g];
  the other parts are plain bytes that decode as [decode_value] does.
- [registry_decode]: the compositionality lemma. If every group's contents represent its
  fancy value, then the final bytes of every group (following the cells) decode to the
  erasure of its fancy value. *)
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

(** ** Erasure: [⌊fv⌋_ρ] *)
Inductive fval_erase (ρ : gmap positive FValue) : FValue → Value → Prop :=
| fval_erase_int z : fval_erase ρ (FVInt z) (VInt z)
| fval_erase_bool b : fval_erase ρ (FVBool b) (VBool b)
| fval_erase_ptr l : fval_erase ρ (FVPtr l) (VPtr l)
| fval_erase_tuple fvs vs :
    length fvs = length vs →
    (∀ k fv v, fvs !! k = Some fv → vs !! k = Some v → fval_erase ρ fv v) →
    fval_erase ρ (FVTuple fvs) (VTuple vs)
| fval_erase_variant t d v : fval_erase ρ d v → fval_erase ρ (FVVariant t d) (VVariant t v)
| fval_erase_cell g fv v : ρ !! g = Some fv → fval_erase ρ fv v → fval_erase ρ (FVCell g) v.

Lemma fval_erase_lift ρ v : fval_erase ρ (fv_lift v) v.
Proof.
  induction v as [| | |vs IH|t d IH] using Value_ind'; simpl; try constructor; try done.
  - by rewrite length_map.
  - intros k fv v. rewrite list_lookup_fmap. intros Hfv Hv.
    destruct (vs !! k) as [v'|] eqn:Hk; simplify_eq/=.
    eapply (Forall_lookup_1 _ _ _ _ IH Hk).
Qed.

Lemma fval_erase_det ρ fv v1 v2 : fval_erase ρ fv v1 → fval_erase ρ fv v2 → v1 = v2.
Proof.
  intros H1. revert v2. induction H1 as [| | |fvs vs Hlen Hk IH|t d v Hd IH|g fv v Hg Hfv IH];
    intros v2 H2; inversion H2; simplify_eq; try done.
  - f_equal. apply list_eq. intros k.
    destruct (fvs !! k) as [fv|] eqn:Hfv.
    + destruct (vs !! k) as [v|] eqn:Hv; [|apply lookup_ge_None in Hv; apply lookup_lt_Some in Hfv; lia].
      match goal with H : ∀ _ _ _, fvs !! _ = _ → ?vs' !! _ = _ → _ |- _ =>
        destruct (vs' !! k) as [v'|] eqn:Hv';
          [|apply lookup_ge_None in Hv'; apply lookup_lt_Some in Hfv; lia];
        rewrite (IH _ _ _ Hfv Hv v') //; by apply (H k) end.
    + have : vs !! k = None by apply lookup_ge_None; apply lookup_ge_None in Hfv; lia.
      intros ->. symmetry. apply lookup_ge_None. apply lookup_ge_None in Hfv. lia.
  - f_equal. by apply IH.
  - by apply IH.
Qed.

(** ** Fancy bytes and their representation *)
Section frepr.
  Context {W : Type}.
  Implicit Types (fbs : list (positive + AbstractByte W)) (bs : list (AbstractByte W)).
  Implicit Types (R : gmap positive (mty * list positive)).

  Definition is_plain (fb : positive + AbstractByte W) : Prop := ∃ b, fb = inr b.

  (** The final bytes of fancy bytes, given the final byte [rv c] of every byte-cell [c]. *)
  Definition fin_bytes (rv : positive → AbstractByte W) fbs : list (AbstractByte W) :=
    (λ fb, match fb with inl c => rv c | inr b => b end) <$> fbs.

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

  Inductive frepr R : mty → list (positive + AbstractByte W) → FValue → Prop :=
  | frepr_cell m g cs : R !! g = Some (m, cs) → frepr R m (inl <$> cs) (FVCell g)
  | frepr_plain m bs v : decode_value m bs = Some v → frepr R m (inr <$> bs) (fv_lift v)
  | frepr_tuple fs sz fbs fvs :
      length fbs = sz → length fvs = length fs →
      (∀ k f fv, fs !! k = Some f → fvs !! k = Some fv →
         frepr R f.2 (list_slice f.1 (mty_size f.2) fbs) fv) →
      (∀ i fb, fbs !! i = Some fb → ¬ in_field fs i → is_plain fb) →
      frepr R (MTuple fs sz) fbs (FVTuple fvs)
  | frepr_enum vars tag sz fbs t vm d bst :
      length fbs = sz →
      take (int_size tag) fbs = inr <$> bst → decode_int tag bst = Some t → (0 ≤ t)%Z →
      vars !! Z.to_nat t = Some vm →
      frepr R vm (list_slice (int_size tag) (mty_size vm) fbs) d →
      (∀ i fb, fbs !! i = Some fb → (int_size tag + mty_size vm ≤ i)%nat → is_plain fb) →
      frepr R (MEnum vars tag sz) fbs (FVVariant t d).

  Lemma frepr_mono R R' m fbs fv : R ⊆ R' → frepr R m fbs fv → frepr R' m fbs fv.
  Proof.
    intros Hsub. induction 1; econstructor; eauto. by eapply lookup_weaken.
  Qed.

  Lemma fin_bytes_slice rv o n fbs :
    fin_bytes rv (list_slice o n fbs) = list_slice o n (fin_bytes rv fbs).
  Proof. by rewrite /fin_bytes /list_slice fmap_take fmap_drop. Qed.

  Lemma length_fin_bytes rv fbs : length (fin_bytes rv fbs) = length fbs.
  Proof. by rewrite /fin_bytes length_fmap. Qed.

  (** One level of compositionality: if the groups embedded in [fv] have final bytes that
      decode to their erasures, so do the final bytes of [fbs]. *)
  Lemma frepr_decode R (ρ : gmap positive FValue) rv m fbs fv :
    frepr R m fbs fv →
    (∀ g m' cs, g ∈ fv_cells fv → R !! g = Some (m', cs) →
       ∃ v', fval_erase ρ (FVCell g) v' ∧ decode_value m' (rv <$> cs) = Some v') →
    ∃ v, fval_erase ρ fv v ∧ decode_value m (fin_bytes rv fbs) = Some v.
  Proof.
    induction 1 as [m g cs Hg|m bs v Hdec|fs sz fbs fvs Hlen Hlenf Hfs IH Hpad
      |vars tag sz fbs t vm d bst Hlen Htag Ht Ht0 Hvm Hd IH Hpad]; intros Hcells.
    - destruct (Hcells g m cs) as (v' & Hv' & Hdec); [by left|done|].
      exists v'. split; [done|]. by rewrite /fin_bytes -list_fmap_compose.
    - exists v. split; [apply fval_erase_lift|]. by rewrite /fin_bytes -list_fmap_compose list_fmap_id.
    - have Hv : ∀ k f fv, fs !! k = Some f → fvs !! k = Some fv →
        ∃ v, fval_erase ρ fv v ∧
          decode_value f.2 (list_slice f.1 (mty_size f.2) (fin_bytes rv fbs)) = Some v.
      { intros k f fv Hf Hfv. rewrite -fin_bytes_slice. apply (IH k f fv Hf Hfv).
        intros g m' cs Hg. apply Hcells. by eapply fv_cells_tuple. }
      assert (∃ vs, length vs = length fs ∧ ∀ k f v, fs !! k = Some f → vs !! k = Some v →
        decode_value f.2 (list_slice f.1 (mty_size f.2) (fin_bytes rv fbs)) = Some v ∧
        ∃ fv, fvs !! k = Some fv ∧ fval_erase ρ fv v) as (vs & Hvs & Hvk).
      { clear IH Hcells Hpad Hfs. revert fvs Hlenf Hv. induction fs as [|f fs IHfs]; intros fvs Hlenf Hv.
        { exists []. split; [done|]. by intros []. }
        destruct fvs as [|fv fvs]; [done|]. simpl in Hlenf.
        destruct (Hv 0%nat f fv) as (v & Hfv & Hdv); [done..|].
        destruct (IHfs fvs ltac:(lia)) as (vs & Hlenv & Hvs).
        { intros k f' fv' ??. by apply (Hv (S k)). }
        exists (v :: vs). split; [by rewrite /= Hlenv|].
        intros [|k] f' v'; simpl; [intros [= <-] [= <-]; eauto|]. eauto. }
      exists (VTuple vs). split.
      + constructor; [lia|]. intros k fv v Hfv Hv'.
        destruct (fs !! k) as [f|] eqn:Hf; [|apply lookup_ge_None in Hf; apply lookup_lt_Some in Hfv; lia].
        destruct (Hvk k f v Hf Hv') as (_ & fv' & Hfv' & ?). by simplify_eq.
      + rewrite decode_value_tuple length_fin_bytes decide_True //. apply fmap_Some_2.
        apply mapM_Some, Forall2_lookup. intros k.
        destruct (fs !! k) as [f|] eqn:Hf, (vs !! k) as [v|] eqn:Hv'; simpl; try constructor.
        * by destruct (Hvk k f v Hf Hv') as [? _].
        * apply lookup_ge_None in Hv'. apply lookup_lt_Some in Hf. lia.
        * apply lookup_ge_None in Hf. apply lookup_lt_Some in Hv'. lia.
    - destruct IH as (v & Hv & Hdec).
      { intros g m' cs Hg. apply Hcells. done. }
      exists (VVariant t v). split; [by constructor|].
      rewrite decode_value_enum length_fin_bytes decide_True //.
      rewrite /fin_bytes -fmap_take Htag -list_fmap_compose list_fmap_id Ht /=.
      rewrite decide_True // Hvm /=. rewrite -/(fin_bytes rv _) -fin_bytes_slice Hdec //.
  Qed.

  (** The compositionality lemma, over the whole registry. [K g] are the contents of the
      group [g] (the fancy bytes that follow its cells), and [rv c] the final byte of the
      cell [c]: the final bytes of [g] are those of its contents. [ok] is a property of
      groups (e.g. "at rest") that holds of the groups embedded in a group with [ok]; the
      contents of the groups with [ok] represent their fancy values. Groups only embed older
      groups, so the nesting is well-founded. *)
  Theorem registry_decode R (ρ : gmap positive FValue)
      (K : positive → list (positive + AbstractByte W)) (rv : positive → AbstractByte W)
      (ok : positive → Prop) :
    (∀ g fv, ρ !! g = Some fv → ok g → ∃ m cs, R !! g = Some (m, cs) ∧ frepr R m (K g) fv ∧
       rv <$> cs = fin_bytes rv (K g) ∧
       ∀ g', g' ∈ fv_cells fv → (g' < g)%positive ∧ g' ∈ dom ρ ∧ ok g') →
    ∀ g fv m cs, ρ !! g = Some fv → R !! g = Some (m, cs) → ok g →
    ∃ v, fval_erase ρ fv v ∧ decode_value m (rv <$> cs) = Some v.
  Proof.
    intros Hinv g. remember (Pos.to_nat g) as n eqn:Hn. revert g Hn.
    induction n as [n IH] using lt_wf_ind. intros g -> fv m cs Hg HR Hok.
    destruct (Hinv g fv Hg Hok) as (m' & cs' & HR' & Hrep & Hrv & Hlt).
    rewrite HR in HR'. simplify_eq. rewrite Hrv. eapply frepr_decode; [done|].
    intros g' m'' cs'' Hg' HR''. destruct (Hlt g' Hg') as (Hlt' & Hdom & Hok').
    apply elem_of_dom in Hdom as [fv' Hfv'].
    destruct (IH (Pos.to_nat g') ltac:(lia) g' eq_refl fv' m'' cs'' Hfv' HR'' Hok')
      as (v' & Hv' & Hdec).
    exists v'. split; [by econstructor|done].
  Qed.
End frepr.

(** ** Sub-values and their replacement

A sub-value of a fancy value [fv] at MiniRust type [m] sits at a tuple field, an enum
payload (of the current variant) or the whole value, at a byte offset [o] and with a
MiniRust type [m'] (alignment requirement A). *)
Inductive fv_sub : mty → FValue → nat → mty → FValue → Prop :=
| fv_sub_here m fv : fv_sub m fv 0 m fv
| fv_sub_field fs sz fvs k off fm fvk o m' fv' :
    fs !! k = Some (off, fm) → fvs !! k = Some fvk → fv_sub fm fvk o m' fv' →
    fv_sub (MTuple fs sz) (FVTuple fvs) (off + o) m' fv'
| fv_sub_payload vars tag sz t d vm o m' fv' :
    vars !! Z.to_nat t = Some vm → fv_sub vm d o m' fv' →
    fv_sub (MEnum vars tag sz) (FVVariant t d) (int_size tag + o) m' fv'.

(** [fv_upd m fv o m' fv' fvn]: [fvn] is [fv] with the sub-value at [o] (of type [m'])
    replaced by [fv']. *)
Inductive fv_upd : mty → FValue → nat → mty → FValue → FValue → Prop :=
| fv_upd_here m fv fv' : fv_upd m fv 0 m fv' fv'
| fv_upd_field fs sz fvs k off fm fvk o m' fv' fvk' :
    fs !! k = Some (off, fm) → fvs !! k = Some fvk → fv_upd fm fvk o m' fv' fvk' →
    fv_upd (MTuple fs sz) (FVTuple fvs) (off + o) m' fv' (FVTuple (<[k := fvk']> fvs))
| fv_upd_payload vars tag sz t d vm o m' fv' d' :
    vars !! Z.to_nat t = Some vm → fv_upd vm d o m' fv' d' →
    fv_upd (MEnum vars tag sz) (FVVariant t d) (int_size tag + o) m' fv' (FVVariant t d').

Lemma fv_sub_bound m fv o m' fv' :
  fv_sub m fv o m' fv' → mty_wf m → (o + mty_size m' ≤ mty_size m)%nat.
Proof.
  induction 1 as [|fs sz fvs k off fm fvk o m' fv' Hk Hfvk Hsub IH|vars tag sz t d vm o m' fv' Hvm Hsub IH];
    intros Hwf; [lia| |].
  - inversion Hwf as [| | |? ? Hdisj Hin Hwfs|]; simplify_eq.
    have := Forall_lookup_1 _ _ _ _ Hin Hk. have := IH (Forall_lookup_1 _ _ _ _ Hwfs Hk).
    simpl. lia.
  - inversion Hwf as [| | | |? ? ? Hvars Htag]; simplify_eq.
    destruct (Forall_lookup_1 _ _ _ _ Hvars Hvm) as [Hsz Hwfvm]. have := IH Hwfvm. simpl. lia.
Qed.

Lemma fv_upd_sub m fv o m' fv' fvn : fv_upd m fv o m' fv' fvn → ∃ fvo, fv_sub m fv o m' fvo.
Proof. induction 1 as [| |]; naive_solver eauto using fv_sub. Qed.

Lemma fv_upd_bound m fv o m' fv' fvn :
  fv_upd m fv o m' fv' fvn → mty_wf m → (o + mty_size m' ≤ mty_size m)%nat.
Proof. intros [fvo Hsub]%fv_upd_sub. by eapply fv_sub_bound. Qed.

Lemma fv_cells_upd m fv o m' fv' fvn g :
  fv_upd m fv o m' fv' fvn → g ∈ fv_cells fvn → g ∈ fv_cells fv ∨ g ∈ fv_cells fv'.
Proof.
  induction 1 as [|fs sz fvs k off fm fvk o m' fv' fvk' Hk Hfvk Hupd IH|]; [by right| |done].
  intros Hg. apply elem_of_list_In in Hg. simpl in Hg. apply in_concat in Hg as (l & Hl & Hg).
  apply in_map_iff in Hl as (fv0 & <- & Hfv0). apply elem_of_list_In in Hfv0.
  apply elem_of_list_lookup_1 in Hfv0 as [j Hj]. apply elem_of_list_In in Hg.
  destruct (decide (j = k)) as [->|Hne].
  - rewrite list_lookup_insert in Hj; [|by eapply lookup_lt_Some]. simplify_eq.
    destruct (IH Hg) as [H|H]; [left|by right]. by eapply (fv_cells_tuple fvs k).
  - rewrite list_lookup_insert_ne in Hj; [|done]. left. by eapply (fv_cells_tuple fvs j).
Qed.

Lemma list_lookup_map {A B} (f : A → B) (l : list A) k : map f l !! k = f <$> l !! k.
Proof. revert k. induction l as [|x l IH]; intros [|k]; simpl; auto. Qed.

Lemma fv_lift_tuple_inv v fvs : fv_lift v = FVTuple fvs → ∃ vs, v = VTuple vs ∧ fvs = map fv_lift vs.
Proof. destruct v; simpl; try done. intros [= <-]. eauto. Qed.
Lemma fv_lift_variant_inv v t d : fv_lift v = FVVariant t d → ∃ dv, v = VVariant t dv ∧ d = fv_lift dv.
Proof. destruct v; simpl; try done. intros [= <- <-]. eauto. Qed.
Lemma fv_lift_cell_inv v g : fv_lift v ≠ FVCell g.
Proof. by destruct v. Qed.

Lemma fval_erase_nocells ρ fv v : fv_cells fv = [] → fval_erase ρ fv v → fv = fv_lift v.
Proof.
  intros Hc H. induction H as [| | |fvs vs Hlen Hk IH| |]; simpl in *; try done.
  - f_equal. apply list_eq. intros k. rewrite list_lookup_fmap.
    destruct (fvs !! k) as [fv|] eqn:Hfv.
    + destruct (vs !! k) as [v|] eqn:Hv; [|apply lookup_ge_None in Hv; apply lookup_lt_Some in Hfv; lia].
      simpl. f_equal. apply (IH k); [done..|].
      apply elem_of_nil_inv. intros g Hg. have : g ∈ fv_cells (FVTuple fvs) by eapply fv_cells_tuple.
      rewrite /= Hc. apply not_elem_of_nil.
    + have Hv : vs !! k = None by apply lookup_ge_None; apply lookup_ge_None in Hfv; lia.
      by rewrite Hv.
  - f_equal. by apply IHfval_erase.
Qed.

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
  Context {W : Type}.
  Implicit Types (fbs : list (positive + AbstractByte W)) (bs : list (AbstractByte W)).
  Implicit Types (R : gmap positive (mty * list positive)).

  (** The registry gives each group as many cells as its type has bytes. *)
  Definition reg_wf R : Prop := ∀ g m cs, R !! g = Some (m, cs) → length cs = mty_size m.

  Lemma frepr_length R m fbs fv : reg_wf R → frepr R m fbs fv → length fbs = mty_size m.
  Proof.
    intros HR. induction 1 as [m g cs Hg|m bs v Hdec|fs sz fbs fvs Hlen|vars tag sz fbs t vm d bst Hlen];
      simpl; try done.
    - rewrite length_fmap. by eapply HR.
    - rewrite length_fmap. by eapply decode_value_length.
  Qed.

  Lemma frepr_plain_of_nocells R m fbs fv :
    frepr R m fbs fv → fv_cells fv = [] → ∀ fb, fb ∈ fbs → is_plain fb.
  Proof.
    induction 1 as [m g cs Hg|m bs v Hdec|fs sz fbs fvs Hlen Hlenf Hfs IH Hpad
      |vars tag sz fbs t vm d bst Hlen Htag Ht Ht0 Hvm Hd IH Hpad]; simpl; try done.
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
      destruct (decide (i < int_size tag)%nat).
      { have : take (int_size tag) fbs !! i = Some fb by rewrite lookup_take.
        rewrite Htag list_lookup_fmap. destruct (bst !! i); simpl; [|done]. intros [= <-]. by eexists. }
      destruct (decide (i < int_size tag + mty_size vm)%nat); [|by eapply Hpad; [done|lia]].
      apply IH; [done|]. apply elem_of_list_lookup. exists (i - int_size tag)%nat.
      rewrite lookup_list_slice decide_True; [|lia]. rewrite -Hi. f_equal. lia.
  Qed.

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
    exists bs. split; [done|].
    destruct (frepr_decode R ∅ (λ _, Uninit) m _ _ Hrep) as (v' & Hv' & Hdec).
    { intros g. rewrite fv_cells_lift. intros ? ? []%not_elem_of_nil. }
    rewrite /fin_bytes -list_fmap_compose list_fmap_id in Hdec.
    have Hvv := fval_erase_det _ _ _ _ Hv' (fval_erase_lift ∅ v). by subst.
  Qed.

  (** Representations of plain tuples and variants, field by field. *)
  Lemma frepr_plain_tuple R fs sz bs vs :
    decode_value (MTuple fs sz) bs = Some (VTuple vs) →
    frepr R (MTuple fs sz) (inr <$> bs) (FVTuple (map fv_lift vs)).
  Proof.
    intros Hdec. move: (Hdec). rewrite decode_value_tuple. case_decide as Hlen; [|done].
    intros (vs' & Hvs & [= <-])%fmap_Some_1. apply mapM_Some in Hvs.
    apply frepr_tuple.
    - by rewrite length_fmap.
    - rewrite length_map. symmetry. by eapply Forall2_length.
    - intros k f fv Hf Hfv. rewrite list_lookup_fmap in Hfv.
      destruct (vs !! k) as [v|] eqn:Hv; simplify_eq/=.
      have := Forall2_lookup_lr _ _ _ _ _ _ Hvs Hf Hv. intros Hd.
      rewrite /list_slice -fmap_drop -fmap_take. by apply frepr_plain.
    - intros i fb Hi _. rewrite list_lookup_fmap in Hi. destruct (bs !! i); simplify_eq/=. by eexists.
  Qed.

  Lemma frepr_plain_variant R vars tag sz bs t d :
    decode_value (MEnum vars tag sz) bs = Some (VVariant t d) →
    frepr R (MEnum vars tag sz) (inr <$> bs) (FVVariant t (fv_lift d)).
  Proof.
    intros Hdec. move: (Hdec). rewrite decode_value_enum. case_decide as Hlen; [|done].
    destruct (decode_int tag (take (int_size tag) bs)) as [t'|] eqn:Ht; simpl; [|done].
    case_decide as Ht0; [|done]. destruct (vars !! Z.to_nat t') as [vm|] eqn:Hvm; simpl; [|done].
    intros (d' & Hd & [= <- <-])%fmap_Some_1.
    eapply (frepr_enum R vars tag sz _ t vm (fv_lift d) (take (int_size tag) bs)); try done.
    - by rewrite length_fmap.
    - by rewrite fmap_take.
    - rewrite /list_slice -fmap_drop -fmap_take. by apply frepr_plain.
    - intros i fb Hi _. rewrite list_lookup_fmap in Hi. destruct (bs !! i); simplify_eq/=. by eexists.
  Qed.

  (** The representation of a field, or of the payload of a variant. *)
  Lemma frepr_field R fs sz fbs fvs k f fv :
    frepr R (MTuple fs sz) fbs (FVTuple fvs) → fs !! k = Some f → fvs !! k = Some fv →
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

  Lemma frepr_payload R vars tag sz fbs t d vm :
    frepr R (MEnum vars tag sz) fbs (FVVariant t d) → vars !! Z.to_nat t = Some vm →
    frepr R vm (list_slice (int_size tag) (mty_size vm) fbs) d.
  Proof.
    intros Hrep Hvm. inversion Hrep as [|m bs v Hdec Hm Hbs Hv| |]; simplify_eq.
    - destruct (fv_lift_variant_inv _ _ _ Hv) as (dv & -> & ->).
      move: Hdec. rewrite decode_value_enum. case_decide; [|done].
      destruct (decode_int tag (take (int_size tag) bs)) as [t'|]; simpl; [|done].
      case_decide; [|done]. destruct (vars !! Z.to_nat t') as [vm'|] eqn:Hvm'; simpl; [|done].
      intros (d' & Hd & [= <- <-])%fmap_Some_1. rewrite Hvm in Hvm'. simplify_eq.
      rewrite /list_slice -fmap_drop -fmap_take. by apply frepr_plain.
    - done.
  Qed.

  Lemma frepr_sub R m fbs fv o m' fv' :
    reg_wf R → frepr R m fbs fv → fv_sub m fv o m' fv' → mty_wf m →
    frepr R m' (list_slice o (mty_size m') fbs) fv'.
  Proof.
    intros HR Hrep Hsub. revert fbs Hrep.
    induction Hsub as [m fv|fs sz fvs k off fm fvk o m' fv' Hk Hfvk Hsub IH
      |vars tag sz t d vm o m' fv' Hvm Hsub IH]; intros fbs Hrep Hwf.
    - rewrite /list_slice drop_0 take_ge //. by erewrite frepr_length.
    - inversion Hwf as [| | |? ? Hdisj Hin Hwfs|]; simplify_eq.
      have Hf := frepr_field _ _ _ _ _ k _ _ Hrep Hk Hfvk.
      have Hwffm := Forall_lookup_1 _ _ _ _ Hwfs Hk. simpl in Hwffm.
      have Hb := fv_sub_bound _ _ _ _ _ Hsub Hwffm.
      rewrite -(list_slice_slice _ _ _ (mty_size fm)) //. by apply IH.
    - inversion Hwf as [| | | |? ? ? Hvars Htag]; simplify_eq.
      destruct (Forall_lookup_1 _ _ _ _ Hvars Hvm) as [Hsz Hwfvm].
      have Hp := frepr_payload _ _ _ _ _ _ _ _ Hrep Hvm.
      have Hb := fv_sub_bound _ _ _ _ _ Hsub Hwfvm.
      rewrite -(list_slice_slice _ _ _ (mty_size vm)) //. by apply IH.
  Qed.
End frepr_ops.
