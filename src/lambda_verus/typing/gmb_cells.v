From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants ghost_map.
From lrust.typing Require Export type.
From lrust.typing Require Import uniq_util.
From lrust.lifetime Require Import lifetime_full guarded_bor.
From guarding Require Import guard tactics.
Set Default Proof Using "Type".

(** * Cells as guarded mutable borrows: the decodability layer

Phase 3 of [design_docs/guarded-mutable-borrows-plan.md] (see "Outcome: phase 3" there).
A cell is an instance [γ] of the GMB library ([lifetime/guarded_bor.v]) over ordinary
memory: the placement is the location [l] of the cell, the logical contents are a fancy
value [fv], and the contents are

  [gcont l m fv := ∃ R fbs, gfbytes l fbs ∗ ⌜frepr R m fbs fv ∧ reg_wf R⌝ ∗ gcells l m fv]

(the _exact fancy bytes_ of [fv] at [l], at the MiniRust type [m] of the cell):
- [gfbytes l fbs] owns the plain bytes of [fbs] at their locations ([inr b] at [l +ₗ i]);
  the positions of nested cells ([inl _]) are not owned there;
- [gcells l m fv] owns the move right [gmb_a γ' (l +ₗ o)] of every cell [FVCell g'] nested
  in [fv] (at its offset [o], following the structure of [m]), with the registry fact
  [gcell_reg g' γ' m'] that names its instance and type.

So the decodability invariant (D3) of the old cell heap is a property of the contents,
held by whoever has them: the instance when idle, the mover during (L1), the borrow during
(L3). [gcont] also is the predicate of a value with cells at [l] that is not itself the
contents of a cell (a typed move moves such values).

A cell id [g] (the fancy value [FVCell g]) is registered in a global _registry_ (a ghost map
[g ↦ (γ, m)] with persistent fragments), kept in the invariant [gcells_ctx] together with
the instance invariants [gmb_inv (gcont_c m) γ] of all cells. A typed move of a value with
cells opens the registry once (one credit for its later): it moves all the cells of the
value, and the cells nested in them, recursively ([gcont_open]), so that the location holds
plain bytes that decode at [m]; the cells travel with the moved value as closers
([gtransit]), which put them back at the new location ([gtransit_close]): the new bytes may
be any bytes that decode to the same value (re-encoding, as in Rust). The recursion is
well-founded because the instances of a chain of nested cells are distinct (each is in the
moving state, [gmb_moving], while its descendants are moved) and registered, and the
registry is finite. *)

(** ** The registry *)
Definition gcellsN : namespace := nroot .@ "gcells".

Class gcellsGS Σ := GCellsGS {
  #[global] gcells_gmbG :: gmbG Σ loc FValue;
  #[global] gcells_regG :: ghost_mapG Σ positive (gmb_name * mty);
  gcells_name : gname
}.

Class gcellsGpreS Σ := GCellsGpreS {
  #[global] gcells_pre_gmbG :: gmbG Σ loc FValue;
  #[global] gcells_pre_regG :: ghost_mapG Σ positive (gmb_name * mty)
}.

Definition gcellsΣ : gFunctors := #[gmbΣ loc FValue; ghost_mapΣ positive (gmb_name * mty)].

Global Instance subG_gcellsGpreS {Σ} : subG gcellsΣ Σ → gcellsGpreS Σ.
Proof. solve_inG. Qed.

(** ** Lists and big separating conjunctions over fields *)

(** The position [i] is in the range of [n] positions at [o]. *)
Definition in_rng (o n i : nat) : Prop := (o ≤ i < o + n)%nat.

Lemma in_field_cons f fs i : in_field (f :: fs) i ↔ in_rng f.1 (mty_size f.2) i ∨ in_field fs i.
Proof.
  rewrite /in_field /in_rng. split.
  - intros (f' & [->|Hf']%elem_of_cons & Hi); [by left|]. right. by exists f'.
  - intros [Hi|(f' & Hf' & Hi)]; [exists f; split; [by left|done]|].
    exists f'. split; [by right|done].
Qed.

Section big_fields.
  Context {PROP : bi}.

  Lemma big_sepL_select {A} (P : nat → Prop) `{!∀ i, Decision (P i)}
      (Φ : nat → A → PROP) (xs : list A) :
    ([∗ list] i ↦ x ∈ xs, Φ i x) ⊣⊢
    ([∗ list] i ↦ x ∈ xs, if decide (P i) then Φ i x else emp) ∗
    ([∗ list] i ↦ x ∈ xs, if decide (P i) then emp else Φ i x).
  Proof.
    rewrite -big_sepL_sep. apply big_sepL_proper=> i x _.
    case_decide; by rewrite ?left_id ?right_id.
  Qed.

  Lemma big_sepL_rng {A} (Φ : nat → A → PROP) (xs : list A) o n :
    (o + n ≤ length xs)%nat →
    ([∗ list] i ↦ x ∈ xs, if decide (in_rng o n i) then Φ i x else emp) ⊣⊢
    ([∗ list] j ↦ x ∈ list_slice o n xs, Φ (o + j)%nat x).
  Proof.
    intros Hlen.
    rewrite -{1}(take_drop o xs) -{1}(take_drop n (drop o xs)) big_sepL_app big_sepL_app.
    have Ho : length (take o xs) = o by rewrite length_take; lia.
    have Hn : length (take n (drop o xs)) = n by rewrite length_take length_drop; lia.
    rewrite Ho Hn. rewrite (big_sepL_proper _ (λ _ _, emp%I) (take o xs)); last first.
    { intros i x Hi. apply lookup_lt_Some in Hi. case_decide as Hc; [|done].
      exfalso. move: Hc. rewrite /in_rng. lia. }
    rewrite (big_sepL_proper _ (λ _ _, emp%I) (drop n (drop o xs))); last first.
    { intros i x _. case_decide as Hc; [|done]. exfalso. move: Hc. rewrite /in_rng. lia. }
    rewrite !big_sepL_emp left_id right_id /list_slice.
    apply big_sepL_proper=> j x Hj. apply lookup_lt_Some in Hj. rewrite Hn in Hj.
    case_decide as Hc; [done|]. exfalso. apply Hc. rewrite /in_rng. lia.
  Qed.

  (** A list splits along disjoint fields into the slices of the fields and the rest. *)
  Lemma big_sepL_fields {A} (Φ : nat → A → PROP) (xs : list A) (fs : list (nat * mty)) :
    fields_disjoint fs → Forall (λ f, f.1 + mty_size f.2 ≤ length xs)%nat fs →
    ([∗ list] i ↦ x ∈ xs, Φ i x) ⊣⊢
    ([∗ list] f ∈ fs, [∗ list] j ↦ x ∈ list_slice f.1 (mty_size f.2) xs, Φ (f.1 + j)%nat x) ∗
    ([∗ list] i ↦ x ∈ xs, if decide (in_field fs i) then emp else Φ i x).
  Proof.
    revert Φ. induction fs as [|f fs IH]; intros Φ Hdisj Hin.
    - rewrite big_sepL_nil left_id. apply big_sepL_proper=> i x _.
      case_decide as Hc; [|done]. by destruct Hc as (f & ?%elem_of_nil & _).
    - apply fields_disjoint_cons in Hdisj as [Hf Hdisj]. inversion Hin as [|? ? Hinf Hins]; subst.
      rewrite (big_sepL_select (in_rng f.1 (mty_size f.2))) big_sepL_rng //.
      rewrite (IH _ Hdisj Hins) big_sepL_cons -assoc. f_equiv. f_equiv.
      + apply big_sepL_proper=> k f' Hk. apply big_sepL_proper=> j x Hj.
        apply lookup_lt_Some in Hj. rewrite /list_slice length_take in Hj.
        have := Forall_lookup_1 _ _ _ _ Hf Hk. simpl. intros Hd.
        case_decide as Hc; [|done]. exfalso. move: Hc. rewrite /in_rng. lia.
      + apply big_sepL_proper=> i x _. pose proof (in_field_cons f fs i) as Hiff.
        destruct (decide (in_field (f :: fs) i)), (decide (in_rng f.1 (mty_size f.2) i)),
          (decide (in_field fs i)); try done; exfalso; naive_solver.
  Qed.

  Lemma big_sepL_same_length {A B} (Φ : nat → A → PROP) (Ψ : nat → B → PROP) xs ys :
    length xs = length ys →
    (∀ i x y, xs !! i = Some x → ys !! i = Some y → Φ i x ⊣⊢ Ψ i y) →
    ([∗ list] i ↦ x ∈ xs, Φ i x) ⊣⊢ ([∗ list] i ↦ y ∈ ys, Ψ i y).
  Proof.
    revert Φ Ψ ys. induction xs as [|x xs IH]; intros Φ Ψ [|y ys] Hlen HΦ; simpl in *; try lia; [done|].
    rewrite (HΦ 0%nat x y) //. f_equiv. apply IH; [lia|]. intros i ???. by apply (HΦ (S i)).
  Qed.

End big_fields.

Section big_fupd.
  Context `{!invGS Σ}.

  Lemma big_sepL_exist_list {A B} (Φ : nat → A → B → iProp Σ) (xs : list A) :
    ([∗ list] i ↦ x ∈ xs, ∃ y, Φ i x y) ⊢
    ∃ ys, ⌜length ys = length xs⌝ ∗ [∗ list] i ↦ x;y ∈ xs;ys, Φ i x y.
  Proof.
    revert Φ. induction xs as [|x xs IH]; intros Φ.
    - iIntros "_". iExists []. by iSplit.
    - rewrite big_sepL_cons. iIntros "[[%y H] Hs]". iDestruct (IH (λ i, Φ (S i)) with "Hs") as "(%ys & %Hl & Hs)".
      iExists (y :: ys). rewrite big_sepL2_cons. iFrame. iPureIntro. simpl. lia.
  Qed.

  (** Running a family of updates over a list, threading a state [S]. *)
  Lemma big_sepL_fupd_thread {A} E (St : iProp Σ) (IN OUT : nat → A → iProp Σ) (xs : list A) :
    (∀ k x, xs !! k = Some x → St ∗ IN k x ⊢ |={E}=> St ∗ OUT k x) →
    St ∗ ([∗ list] k ↦ x ∈ xs, IN k x) ⊢ |={E}=> St ∗ [∗ list] k ↦ x ∈ xs, OUT k x.
  Proof.
    revert IN OUT. induction xs as [|x xs IH]; intros IN OUT Hstep.
    - iIntros "[$ _]". by iModIntro.
    - rewrite !big_sepL_cons. iIntros "[S [I Is]]".
      iMod (Hstep 0%nat x with "[$S $I]") as "[S $]"; [done|].
      iApply (IH (λ k, IN (S k)) (λ k, OUT (S k)) with "[$S $Is]").
      intros k y Hk. by apply (Hstep (S k)).
  Qed.
End big_fupd.

(** Fancy bytes with new plain bytes, on slices. *)
Lemma fb_mix_slice fbs bs o n : list_slice o n (fb_mix fbs bs) = fb_mix (list_slice o n fbs) (list_slice o n bs).
Proof. by rewrite /fb_mix /list_slice -zip_with_take -zip_with_drop. Qed.

(** The plain bytes of fancy bytes (an arbitrary byte at the positions of cells). *)
Definition fb_base (fbs : list (positive + abyte)) : list abyte :=
  (λ fb, match fb with inl _ => Uninit | inr b => b end) <$> fbs.

Lemma length_fb_base fbs : length (fb_base fbs) = length fbs.
Proof. by rewrite /fb_base length_fmap. Qed.

Section gcells_defs.
  Context `{!typeG Σ, !gcellsGS Σ}.
  Implicit Types (l : loc) (m : mty) (fv : FValue) (fbs : list (positive + abyte)).

  (** The move right of a cell (the placement is a location, the contents a fancy value). *)
  Notation gca γ l := (gmb_a (S:=loc) (T:=FValue) γ l).

  (** The registry: the cell [g] is the instance [γ], with contents of MiniRust type [m]. *)
  Definition gcell_reg (g : positive) (γ : gmb_name) (m : mty) : iProp Σ :=
    g ↪[gcells_name]□ (γ, m).

  (** Plain bytes of fancy bytes, at their locations. *)
  Definition gfb l (fb : positive + abyte) : iProp Σ :=
    match fb with inl _ => True | inr b => l ↦b [b] end.
  Definition gfbytes l fbs : iProp Σ := [∗ list] i ↦ fb ∈ fbs, gfb (l +ₗ i) fb.

  (** The move rights of the cells nested in [fv], at their locations (following the
      structure of [m]). *)
  Fixpoint gcells l m fv {struct fv} : iProp Σ :=
    match fv with
    | FVCell g => ∃ γ, gcell_reg g γ m ∗ gca γ l
    | FVTuple fvs =>
        match m with
        | MTuple fs _ =>
            (fix go (k : nat) (fvs : list FValue) : iProp Σ :=
               match fvs with
               | [] => True
               | fv :: fvs =>
                   match fs !! k with Some (o, fm) => gcells (l +ₗ Z.of_nat o) fm fv | None => True end ∗
                   go (S k) fvs
               end) 0%nat fvs
        | _ => True
        end
    | FVVariant t d =>
        match m with
        | MEnum vars tag _ =>
            match vars !! Z.to_nat t with Some vm => gcells (l +ₗ Z.of_nat (int_size tag)) vm d | None => True end
        | _ => True
        end
    | _ => True
    end%I.

  (** The contents of a cell of type [m] at [l]: the exact fancy bytes of [fv]. *)
  Definition gcont l m fv : iProp Σ :=
    ∃ (R : gmap positive (mty * list positive)) fbs,
      gfbytes l fbs ∗ ⌜frepr R m fbs fv ∧ reg_wf R⌝ ∗ gcells l m fv.
  Definition gcont_c m : loc → FValue → iProp Σ := λ l fv, gcont l m fv.

  (** The registry invariant: the authority of the registry, and the instance invariants of
      the registered cells (whose bytes mask is [lazyB]). *)
  Definition gcells_inv : iProp Σ :=
    ∃ Reg : gmap positive (gmb_name * mty), ghost_map_auth gcells_name 1 Reg ∗
      [∗ map] g ↦ e ∈ Reg, gmb_inv (gcont_c e.2) e.1 ∗ ⌜gmb_bmask e.1 = lazyB⌝.
  Definition gcells_ctx : iProp Σ := inv gcellsN gcells_inv.

  Global Instance gcell_reg_persistent g γ m : Persistent (gcell_reg g γ m).
  Proof. apply _. Qed.
  Global Instance gcell_reg_timeless g γ m : Timeless (gcell_reg g γ m).
  Proof. apply _. Qed.
  Global Instance gcells_ctx_persistent : Persistent gcells_ctx.
  Proof. apply _. Qed.
  Global Instance gfb_timeless l fb : Timeless (gfb l fb).
  Proof. destruct fb; apply _. Qed.
  Global Instance gfbytes_timeless l fbs : Timeless (gfbytes l fbs).
  Proof. apply _. Qed.

  Lemma gcells_tuple l fs sz fvs :
    gcells l (MTuple fs sz) (FVTuple fvs) ⊣⊢
    [∗ list] k ↦ fv ∈ fvs, match fs !! k with Some (o, fm) => gcells (l +ₗ Z.of_nat o) fm fv | None => True end.
  Proof.
    assert (∀ k1, (fix go (k : nat) (fvs : list FValue) : iProp Σ :=
               match fvs with
               | [] => True
               | fv :: fvs =>
                   match fs !! k with Some (o, fm) => gcells (l +ₗ Z.of_nat o) fm fv | None => True end ∗
                   go (S k) fvs
               end) k1 fvs ⊣⊢
      [∗ list] k ↦ fv ∈ fvs, match fs !! (k1 + k)%nat with
        Some (o, fm) => gcells (l +ₗ Z.of_nat o) fm fv | None => True end) as Hgo.
    { induction fvs as [|fv fvs IH]; intros k1; simpl; [done|].
      rewrite Nat.add_0_r IH. do 3 f_equiv. by rewrite Nat.add_succ_r. }
    exact (Hgo 0%nat).
  Qed.

  Lemma gcells_enum l vars tag sz t d :
    gcells l (MEnum vars tag sz) (FVVariant t d) ⊣⊢
    match vars !! Z.to_nat t with Some vm => gcells (l +ₗ Z.of_nat (int_size tag)) vm d | None => True end.
  Proof. done. Qed.

  Global Instance gcells_timeless l m fv : Timeless (gcells l m fv).
  Proof.
    revert l m. induction fv as [z|b|lp|fvs IH|t d IH|g] using FValue_ind'; intros l m; simpl;
      try apply _.
    - destruct m as [| | |fs sz|]; try apply _. generalize 0%nat.
      induction IH as [|fv fvs Hfv _ IH']; intros k; [apply _|].
      apply bi.sep_timeless; [|apply IH']. destruct (fs !! k) as [[o fm]|]; [apply Hfv|apply _].
  Qed.

  Global Instance gcont_timeless l m fv : Timeless (gcont l m fv).
  Proof. apply _. Qed.
  Global Instance gcont_c_timeless m l fv : Timeless (gcont_c m l fv).
  Proof. apply _. Qed.

  (** A value without cells has no cells. *)
  Lemma gcells_lift l m v : ⊢ gcells l m (fv_lift v).
  Proof.
    revert l m. induction v as [z|b|lp|vs IH|t d IH] using Value_ind'; intros l m;
      try (by rewrite /=).
    - destruct m as [| | |fs sz|]; try (by rewrite /=).
      rewrite /fv_lift -/fv_lift gcells_tuple. iApply big_sepL_intro. iIntros "!>" (k fv Hk).
      rewrite list_lookup_map in Hk. destruct (vs !! k) as [vk|] eqn:Hvk; [|done].
      simpl in Hk. injection Hk as <-.
      destruct (fs !! k) as [[o fm]|]; [|done]. iApply (Forall_lookup_1 _ _ _ _ IH Hvk).
    - destruct m as [| | | |vars tag sz]; try (by rewrite /=). rewrite /fv_lift -/fv_lift gcells_enum.
      destruct (vars !! _); [iApply IH|done].
  Qed.

  (** ** Bytes at their locations *)
  Lemma heap_mapsto_bytes_pos l bs : l ↦b bs ⊣⊢ [∗ list] i ↦ b ∈ bs, (l +ₗ i) ↦b [b].
  Proof.
    revert l. induction bs as [|b bs IH]; intros l.
    - by rewrite heap_mapsto_bytes_nil.
    - rewrite heap_mapsto_bytes_cons big_sepL_cons shift_loc_0_nat IH. f_equiv.
      apply big_sepL_proper=> i b' _. by rewrite shift_loc_S.
  Qed.

  Lemma gfbytes_bytes l bs : gfbytes l (inr <$> bs) ⊣⊢ l ↦b bs.
  Proof. by rewrite /gfbytes big_sepL_fmap heap_mapsto_bytes_pos. Qed.

  Lemma gfbytes_cells l cs : gfbytes l (inl <$> cs) ⊣⊢ True.
  Proof.
    rewrite /gfbytes big_sepL_fmap /=. iSplit; [by iIntros|]. iIntros "_".
    by iApply big_sepL_intro.
  Qed.

  Lemma heap_mapsto_bytes_pos_shift l (o : nat) bs :
    (l +ₗ o) ↦b bs ⊣⊢ [∗ list] j ↦ b ∈ bs, (l +ₗ (o + j)%nat) ↦b [b].
  Proof. rewrite heap_mapsto_bytes_pos. apply big_sepL_proper=> j b _. by rewrite shift_loc_assoc_nat. Qed.

  Lemma gfbytes_shift l (o : nat) fbs :
    gfbytes (l +ₗ o) fbs ⊣⊢ [∗ list] j ↦ fb ∈ fbs, gfb (l +ₗ (o + j)%nat) fb.
  Proof. apply big_sepL_proper=> j b _. by rewrite shift_loc_assoc_nat. Qed.
End gcells_defs.

(** ** Moving all the cells of a value: the deep opening *)
Section gcells_open.
  Context `{!typeG Σ, !gcellsGS Σ}.
  Implicit Types (l : loc) (m : mty) (fv : FValue) (fbs : list (positive + abyte)).
  Notation gca γ l := (gmb_a (S:=loc) (T:=FValue) γ l).

  Lemma big_sepL2_to_sepL_l {A B} (Φ : nat → A → B → iProp Σ) (Ψ : nat → A → iProp Σ)
      (xs : list A) (ys : list B) :
    (∀ k x y, xs !! k = Some x → ys !! k = Some y → Φ k x y ⊢ Ψ k x) →
    ([∗ list] k ↦ x;y ∈ xs;ys, Φ k x y) ⊢ [∗ list] k ↦ x ∈ xs, Ψ k x.
  Proof.
    iIntros (HΦ) "H". iDestruct (big_sepL2_impl _ (λ k x y, Ψ k x) with "H []") as "H".
    { iIntros "!>" (k x y Hx Hy) "H". by iApply HΦ. }
    rewrite big_sepL2_const_sepL_l. by iDestruct "H" as "[_ $]".
  Qed.

  Lemma big_sepL_zip_fst {A B} (Φ : nat → A → iProp Σ) (xs : list A) (ys : list B) :
    length xs ≤ length ys →
    ([∗ list] k ↦ p ∈ zip xs ys, Φ k p.1) ⊣⊢ [∗ list] k ↦ x ∈ xs, Φ k x.
  Proof. intros. by rewrite -(big_sepL_fmap fst) fst_zip. Qed.

  Lemma big_sepL_zip_snd {A B} (Φ : nat → B → iProp Σ) (xs : list A) (ys : list B) :
    length ys ≤ length xs →
    ([∗ list] k ↦ p ∈ zip xs ys, Φ k p.2) ⊣⊢ [∗ list] k ↦ y ∈ ys, Φ k y.
  Proof. intros. by rewrite -(big_sepL_fmap snd) snd_zip. Qed.

  Lemma gcells_tuple_zip l fs sz fvs :
    length fvs = length fs →
    gcells l (MTuple fs sz) (FVTuple fvs) ⊣⊢
    [∗ list] k ↦ p ∈ zip fs fvs, gcells (l +ₗ Z.of_nat p.1.1) p.1.2 p.2.
  Proof.
    intros Hlen. rewrite gcells_tuple. apply big_sepL_same_length.
    { rewrite length_zip_with. lia. }
    intros k fv p Hfv Hp. apply lookup_zip_with_Some in Hp as ([o fm] & fv' & -> & Hf & Hfv').
    rewrite Hfv in Hfv'. injection Hfv' as <-. by rewrite Hf.
  Qed.

  (** The tokens of the cells that are being moved (the ancestors of the current one). *)
  Definition gtoks (A : list (gmb_name * FValue)) : iProp Σ :=
    [∗ list] a ∈ A, gmb_moving (S:=loc) a.1 a.2.

  Lemma gtoks_excl A γ l : gtoks A -∗ gca γ l -∗ ⌜γ ∉ A.*1⌝.
  Proof.
    iIntros "Toks Ha %Hin". apply elem_of_list_fmap in Hin as ([γ' t] & -> & Hin).
    iDestruct (big_sepL_elem_of with "Toks") as "T"; [done|].
    iApply (gmb_a_moving_excl with "Ha T").
  Qed.

  (** The registered instance invariants. *)
  Definition greg_ctx (Reg : gmap positive (gmb_name * mty)) : iProp Σ :=
    [∗ map] g ↦ e ∈ Reg, gmb_inv (gcont_c e.2) e.1 ∗ ⌜gmb_bmask e.1 = lazyB⌝.
  Global Instance greg_ctx_persistent Reg : Persistent (greg_ctx Reg).
  Proof. apply _. Qed.

  Lemma reg_count (Reg : gmap positive (gmb_name * mty)) (A : list (gmb_name * FValue)) :
    NoDup A.*1 → (∀ a, a ∈ A → ∃ g m', Reg !! g = Some (a.1, m')) → length A ≤ size Reg.
  Proof.
    intros Hnd Hin. rewrite -length_map_to_list -(length_fmap fst A)
      -(length_fmap (λ e : positive * (gmb_name * mty), e.2.1) (map_to_list Reg)).
    apply submseteq_length, NoDup_submseteq; [done|].
    intros γ (a & -> & Ha)%elem_of_list_fmap. destruct (Hin a Ha) as (g & m' & Hg).
    apply elem_of_list_fmap. exists (g, (a.1, m')). split; [done|]. by apply elem_of_map_to_list.
  Qed.

  (** The closer of a deep opening: bytes at [l'] that decode to the same value give the
      fancy bytes of [fv] at [l'] (with the plain bytes of [bs']), the cells at their new
      locations, and the representation. *)
  Definition gclose R m fbs fv (v : Value) : iProp Σ :=
    ∀ l' bs', ⌜decode_value m bs' = Some v⌝ -∗ l' ↦b bs' ={lazyE}=∗
      gfbytes l' (fb_mix fbs bs') ∗ gcells l' m fv ∗ ⌜frepr R m (fb_mix fbs bs') fv⌝.

  (** The statement of the deep opening, with fuel [k] for the depth of the nesting of
      cells. [A] are the cells being moved around the current value (with their tokens),
      [Reg] is the registry. *)
  Definition gopen_stmt Reg (k : nat) R m fbs fv : Prop :=
    ∀ (A : list (gmb_name * FValue)) l, mty_wf m → NoDup A.*1 →
      (∀ a, a ∈ A → ∃ g m', Reg !! g = Some (a.1, m')) → (size Reg ≤ length A + k)%nat →
      ⊢ greg_ctx Reg -∗ ghost_map_auth gcells_name 1 Reg -∗ gtoks A -∗ gfbytes l fbs -∗
        gcells l m fv ={lazyE}=∗ ∃ bs v, ghost_map_auth gcells_name 1 Reg ∗ gtoks A ∗
          l ↦b bs ∗ ⌜decode_value m bs = Some v⌝ ∗ gclose R m fbs fv v.

  (** The deep opening of the fields of a tuple (or of the payload of an enum). *)
  Lemma gopen_fields Reg k R fs (fvs : list FValue) fbs A l :
    fields_disjoint fs → Forall (λ f, f.1 + mty_size f.2 ≤ length fbs)%nat fs →
    Forall (λ f, mty_wf f.2) fs → length fvs = length fs →
    (∀ i fb, fbs !! i = Some fb → ¬ in_field fs i → is_plain fb) →
    (∀ j f fvj, fs !! j = Some f → fvs !! j = Some fvj →
       gopen_stmt Reg k R f.2 (list_slice f.1 (mty_size f.2) fbs) fvj) →
    NoDup A.*1 → (∀ a, a ∈ A → ∃ g m', Reg !! g = Some (a.1, m')) →
    (size Reg ≤ length A + k)%nat →
    greg_ctx Reg -∗ ghost_map_auth gcells_name 1 Reg -∗ gtoks A -∗ gfbytes l fbs -∗
    ([∗ list] j ↦ p ∈ zip fs fvs, gcells (l +ₗ Z.of_nat p.1.1) p.1.2 p.2) ={lazyE}=∗
    ∃ bs vs, ghost_map_auth gcells_name 1 Reg ∗ gtoks A ∗ l ↦b bs ∗
      ⌜length bs = length fbs ∧ length vs = length fs ∧
       (∀ j f vj, fs !! j = Some f → vs !! j = Some vj →
          decode_value f.2 (list_slice f.1 (mty_size f.2) bs) = Some vj) ∧
       (∀ i, ¬ in_field fs i → bs !! i = fb_base fbs !! i)⌝ ∗
      (∀ l' bs', ⌜length bs' = length fbs⌝ -∗
         ⌜∀ j f vj, fs !! j = Some f → vs !! j = Some vj →
            decode_value f.2 (list_slice f.1 (mty_size f.2) bs') = Some vj⌝ -∗
         l' ↦b bs' ={lazyE}=∗
         gfbytes l' (fb_mix fbs bs') ∗ ([∗ list] j ↦ p ∈ zip fs fvs, gcells (l' +ₗ Z.of_nat p.1.1) p.1.2 p.2) ∗
         ⌜∀ j f fvj, fs !! j = Some f → fvs !! j = Some fvj →
            frepr R f.2 (list_slice f.1 (mty_size f.2) (fb_mix fbs bs')) fvj⌝).
  Proof.
    iIntros (Hdisj Hin Hwf Hlenf Hpad IH HA Hrng Hsz) "#Ctx Auth Toks Hfb Hc".
    have Hlz : length (zip fs fvs) = length fs by rewrite length_zip_with; lia.
    have Hzip : ∀ j p, zip fs fvs !! j = Some p → fs !! j = Some p.1 ∧ fvs !! j = Some p.2.
    { intros j p (f & fvj & -> & ? & ?)%lookup_zip_with_Some. done. }
    rewrite /gfbytes (big_sepL_fields _ fbs fs) //. iDestruct "Hfb" as "[Hfbf Hpad]".
    iAssert ([∗ list] j ↦ p ∈ zip fs fvs,
      gfbytes (l +ₗ Z.of_nat p.1.1) (list_slice p.1.1 (mty_size p.1.2) fbs) ∗ gcells (l +ₗ Z.of_nat p.1.1) p.1.2 p.2)%I
      with "[Hfbf Hc]" as "Hin".
    { rewrite big_sepL_sep. iFrame "Hc".
      rewrite (big_sepL_zip_fst (λ _ f, gfbytes (l +ₗ Z.of_nat f.1) (list_slice f.1 (mty_size f.2) fbs))); [|lia].
      iApply (big_sepL_impl with "Hfbf"). iIntros "!>" (j f _) "H". by rewrite gfbytes_shift. }
    iMod (big_sepL_fupd_thread lazyE (greg_ctx Reg ∗ ghost_map_auth gcells_name 1 Reg ∗ gtoks A)
      _ (λ j p, ∃ y : list abyte * Value, (l +ₗ Z.of_nat p.1.1) ↦b y.1 ∗
         ⌜decode_value p.1.2 y.1 = Some y.2⌝ ∗
         gclose R p.1.2 (list_slice p.1.1 (mty_size p.1.2) fbs) p.2 y.2)%I
      with "[$Ctx $Auth $Toks $Hin]") as "[(_ & Auth & Toks) Hout]".
    { intros j p Hp. destruct (Hzip j p Hp) as [Hf Hfv].
      iIntros "[(#Ctx' & Auth & Toks) [Hfb Hc]]".
      iMod (IH j p.1 p.2 Hf Hfv A (l +ₗ Z.of_nat p.1.1) with "Ctx' Auth Toks Hfb Hc")
        as (bs v) "(Auth & Toks & Hbs & %Hd & Cl)"; [|done..|].
      { exact (Forall_lookup_1 _ _ _ _ Hwf Hf). }
      iModIntro. iFrame "Ctx' Auth Toks". iExists (bs, v). by iFrame. }
    iDestruct (big_sepL_exist_list with "Hout") as (ys) "[%Hlys Hout]".
    rewrite Hlz in Hlys.
    iDestruct (big_sepL2_sep with "Hout") as "[Hbs Hout]".
    iDestruct (big_sepL2_sep with "Hout") as "[Hdec Hcl]".
    iDestruct (big_sepL2_pure_1 with "Hdec") as %Hdec.
    set ins := zip_with (λ (p : (nat * mty) * FValue) (y : list abyte * Value), (p.1.1, y.1)) (zip fs fvs) ys.
    set bs := fill_fields ins (fb_base fbs).
    have Hlenbs : length bs = length fbs by rewrite length_fill_fields length_fb_base.
    have Hins : ∀ j p y, zip fs fvs !! j = Some p → ys !! j = Some y → ins !! j = Some (p.1.1, y.1).
    { intros j p y Hp Hy. by rewrite /ins lookup_zip_with Hp /= Hy. }
    have Hslice : ∀ j p y, zip fs fvs !! j = Some p → ys !! j = Some y →
      list_slice p.1.1 (mty_size p.1.2) bs = y.1.
    { intros j p y Hp Hy. have Hly := decode_value_length _ _ _ (Hdec j p y Hp Hy).
      rewrite -Hly. apply (list_slice_fill_fields ins _ j); [by apply Hins| |].
      - intros j' o' e' Hj' (p' & y' & [= -> ->] & Hp' & Hy')%lookup_zip_with_Some.
        destruct (Hzip _ _ Hp) as [Hf _]. destruct (Hzip _ _ Hp') as [Hf' _].
        rewrite (decode_value_length _ _ _ (Hdec j' p' y' Hp' Hy')) Hly.
        destruct p as [[o fm] fvj], p' as [[o2 fm2] fvj']; simpl in *.
        destruct (Hdisj j' j o2 fm2 o fm) as [?|?]; [done|done|done|lia|lia].
      - rewrite Hly length_fb_base. destruct (Hzip _ _ Hp) as [Hf _].
        exact (Forall_lookup_1 _ _ _ _ Hin Hf). }
    have Hpadbs : ∀ i, ¬ in_field fs i → bs !! i = fb_base fbs !! i.
    { intros i Hi. apply lookup_fill_fields_out.
      intros j o e (p & y & [= -> ->] & Hp & Hy)%lookup_zip_with_Some.
      destruct (Hzip _ _ Hp) as [Hf _].
      rewrite (decode_value_length _ _ _ (Hdec j p y Hp Hy)).
      destruct (decide (p.1.1 ≤ i < p.1.1 + mty_size p.1.2)%nat); [|lia].
      exfalso. apply Hi. exists p.1. split; [by eapply elem_of_list_lookup_2|done]. }
    iModIntro. iExists bs, ys.*2. iFrame "Auth Toks". iSplitL "Hbs Hpad"; [|iSplit].
    - rewrite heap_mapsto_bytes_pos (big_sepL_fields _ bs fs) //; last by rewrite Hlenbs.
      iSplitL "Hbs".
      + rewrite -(big_sepL_zip_fst (λ _ f, [∗ list] j ↦ b ∈ list_slice f.1 (mty_size f.2) bs,
          (l +ₗ (f.1 + j)%nat) ↦b [b])%I fs fvs); [|lia].
        iApply (big_sepL2_to_sepL_l with "Hbs"). intros j p y Hp Hy. rewrite (Hslice j p y Hp Hy).
        by rewrite heap_mapsto_bytes_pos_shift.
      + iApply (big_sepL_same_length with "Hpad"); [done|]. intros i b fb Hb Hfb.
        case_decide as Hi; [done|]. destruct (Hpad i fb Hfb Hi) as [b' ->].
        rewrite Hpadbs // /fb_base list_lookup_fmap Hfb /= in Hb. by injection Hb as ->.
    - iPureIntro. split_and!; [done|by rewrite length_fmap|..|done].
      intros j f vj Hf Hvj. rewrite list_lookup_fmap in Hvj.
      destruct (ys !! j) as [y|] eqn:Hy; [|done]. injection Hvj as <-.
      destruct (fvs !! j) as [fvj|] eqn:Hfvj; [|apply lookup_ge_None in Hfvj; apply lookup_lt_Some in Hf; lia].
      have Hp : zip fs fvs !! j = Some (f, fvj) by rewrite lookup_zip_with Hf /= Hfvj.
      by rewrite (Hslice j _ y Hp Hy) (Hdec j _ y Hp Hy).
    - iIntros (l' bs' Hlen' Hdec') "Hbs'".
      rewrite heap_mapsto_bytes_pos (big_sepL_fields _ bs' fs) //; last by rewrite Hlen'.
      iDestruct "Hbs'" as "[Hf' Hp']".
      iAssert ([∗ list] j ↦ p;y ∈ zip fs fvs;ys,
        (l' +ₗ Z.of_nat p.1.1) ↦b list_slice p.1.1 (mty_size p.1.2) bs')%I with "[Hf']" as "Hf'".
      { rewrite big_sepL2_const_sepL_l. iSplit; [iPureIntro; lia|].
        rewrite (big_sepL_zip_fst (λ _ f, (l' +ₗ Z.of_nat f.1) ↦b list_slice f.1 (mty_size f.2) bs')%I); [|lia].
        iApply (big_sepL_impl with "Hf'"). iIntros "!>" (j f _) "H".
        by rewrite heap_mapsto_bytes_pos_shift. }
      iCombine "Hf' Hcl" as "H". rewrite -big_sepL2_sep.
      iMod (big_sepL2_fupd _ (λ j p y, gfbytes (l' +ₗ Z.of_nat p.1.1)
          (fb_mix (list_slice p.1.1 (mty_size p.1.2) fbs) (list_slice p.1.1 (mty_size p.1.2) bs')) ∗
          gcells (l' +ₗ Z.of_nat p.1.1) p.1.2 p.2 ∗
          ⌜frepr R p.1.2 (fb_mix (list_slice p.1.1 (mty_size p.1.2) fbs)
             (list_slice p.1.1 (mty_size p.1.2) bs')) p.2⌝)%I with "[H]") as "H".
      { iApply (big_sepL2_impl with "H"). iIntros "!>" (j p y Hp Hy) "[Hb Cl]".
        destruct (Hzip _ _ Hp) as [Hf _].
        iApply ("Cl" with "[] Hb"). iPureIntro. apply (Hdec' j p.1); [done|].
        by rewrite list_lookup_fmap Hy. }
      iDestruct (big_sepL2_sep with "H") as "[Hfb H]".
      iDestruct (big_sepL2_sep with "H") as "[Hc Hrep]".
      iDestruct (big_sepL2_pure_1 with "Hrep") as %Hrep.
      iModIntro. iSplitL "Hfb Hp'"; [|iSplitL "Hc"].
      + rewrite /gfbytes (big_sepL_fields _ (fb_mix fbs bs') fs) //; last first.
        { rewrite fb_mix_length //. }
        iSplitL "Hfb".
        * rewrite -(big_sepL_zip_fst (λ _ f, [∗ list] j ↦ x ∈ list_slice f.1 (mty_size f.2)
            (fb_mix fbs bs'), gfb (l' +ₗ (f.1 + j)%nat) x)%I fs fvs); [|lia].
          iApply (big_sepL2_to_sepL_l with "Hfb"). intros j p y Hp Hy.
          rewrite fb_mix_slice. apply big_sepL_mono=> ???. by rewrite shift_loc_assoc_nat.
        * iApply (big_sepL_same_length with "Hp'"); [by rewrite fb_mix_length|].
          intros i fb b Hfb Hb. case_decide as Hi; [done|].
          destruct (lookup_lt_is_Some_2 fbs i) as [fb0 Hfb0].
          { rewrite -Hlen'. by eapply lookup_lt_Some. }
          destruct (Hpad i fb0 Hfb0 Hi) as [b0 ->].
          rewrite (fb_mix_lookup _ _ _ _ _ Hfb0 Hb) in Hfb. by injection Hfb as <-.
      + iApply (big_sepL2_to_sepL_l with "Hc"). by intros.
      + iPureIntro. intros j f fvj Hf Hfvj.
        have Hp : zip fs fvs !! j = Some (f, fvj) by rewrite lookup_zip_with Hf /= Hfvj.
        destruct (lookup_lt_is_Some_2 ys j) as [y Hy]; [rewrite Hlys; by eapply lookup_lt_Some|].
        rewrite fb_mix_slice. exact (Hrep j _ y Hp Hy).
  Qed.
  Lemma gtoks_cons a A : gtoks (a :: A) ⊣⊢ gmb_moving (S:=loc) a.1 a.2 ∗ gtoks A.
  Proof. by rewrite /gtoks big_sepL_cons. Qed.

  Lemma fb_mix_plain bs bs' : length bs' = length bs → fb_mix (inr <$> bs) bs' = inr <$> bs'.
  Proof.
    revert bs'. induction bs as [|b bs IH]; intros [|b' bs'] Hlen; simpl in *; try done; try lia.
    f_equal. apply IH. lia.
  Qed.

  Lemma fb_mix_take n fbs bs : take n (fb_mix fbs bs) = fb_mix (take n fbs) (take n bs).
  Proof. by rewrite /fb_mix -zip_with_take. Qed.

  Lemma mty_wf_tuple_inv fs sz :
    mty_wf (MTuple fs sz) → fields_disjoint fs ∧
      Forall (λ f, f.1 + mty_size f.2 ≤ sz)%nat fs ∧ Forall (λ f, mty_wf f.2) fs.
  Proof. by inversion 1. Qed.
  Lemma mty_wf_enum_inv vars tag sz :
    mty_wf (MEnum vars tag sz) →
      Forall (λ vm, int_size tag + mty_size vm ≤ sz ∧ mty_wf vm)%nat vars ∧ (int_size tag ≤ sz)%nat.
  Proof. by inversion 1. Qed.

  (** The deep opening: by induction on the fuel, and on the representation. *)
  Lemma gopen_rec Reg k R m fbs fv : reg_wf R → frepr R m fbs fv → gopen_stmt Reg k R m fbs fv.
  Proof.
    revert R m fbs fv. induction k as [k IHk] using lt_wf_ind. intros R m fbs fv HR Hrep.
    induction Hrep as [m g cs Hg|m bs v Hdec|fs sz fbs fvs Hlen Hlenf Hfs IH Hpad
      |vars tag sz fbs t vm d bst Hlen Htag Ht Ht0 Hvm Hd IH Hpad];
      intros A l Hwf HA Hrng Hsz; iIntros "#Ctx Auth Toks Hfb Hc".
    - (* a cell: move it, and open its contents with less fuel *)
      iEval (simpl) in "Hc". iDestruct "Hc" as (γ) "[#Hreg Ha]".
      iDestruct (ghost_map_lookup with "Auth Hreg") as %Hγ.
      iDestruct (big_sepM_lookup with "Ctx") as "[#GI %Hbm]"; [exact Hγ|]. simpl in Hbm.
      iDestruct (gtoks_excl with "Toks Ha") as %Hnin.
      iMod (gmb_move_tok (gcont_c m) lazyE γ l with "GI Ha") as (t) "(Hct & Tok & Back)".
      { rewrite Hbm. pose proof lazyB_lazyE. rewrite /lazyE. set_solver. }
      have HA' : NoDup ((γ, t) :: A).*1 by constructor.
      have Hrng' : ∀ a, a ∈ (γ, t) :: A → ∃ g m', Reg !! g = Some (a.1, m').
      { intros a [->|Ha]%elem_of_cons; [by exists g, m|by apply Hrng]. }
      have Hcount := reg_count _ _ HA' Hrng'. simpl in Hcount.
      destruct k as [|k']; [lia|].
      iDestruct "Hct" as (R' fbs') "(Hfb' & [%Hrep' %HR'] & Hc')".
      iMod (IHk k' ltac:(lia) R' m fbs' t HR' Hrep' ((γ, t) :: A) l Hwf HA' Hrng' ltac:(simpl; lia)
        with "Ctx Auth [Tok Toks] Hfb' Hc'") as (bs v) "(Auth & Toks' & Hbs & %Hd & Cl)".
      { rewrite gtoks_cons. iFrame. }
      rewrite gtoks_cons. iDestruct "Toks'" as "[Tok Toks]".
      iModIntro. iExists bs, v. iFrame "Auth Toks Hbs". iSplit; [done|].
      iIntros (l' bs' Hd') "Hbs'".
      iMod ("Cl" with "[//] Hbs'") as "(Hfb' & Hc' & %Hrep'')".
      iMod ("Back" $! l' with "Tok [Hfb' Hc']") as "Ha'".
      { rewrite /gcont_c /gcont. iExists R', _. by iFrame. }
      iModIntro. have Hlen := decode_value_length _ _ _ Hd'. have Hcs := HR _ _ _ Hg.
      rewrite fb_mix_cells; [|lia]. iSplitR; [by rewrite gfbytes_cells|]. iSplitL.
      + iEval (simpl). iExists γ. by iFrame "Hreg Ha'".
      + iPureIntro. by constructor.
    - (* plain bytes *)
      rewrite gfbytes_bytes. iModIntro. iExists bs, v. iFrame. iSplit; [done|].
      iIntros (l' bs' Hd') "Hbs'".
      have Hlen := decode_value_length _ _ _ Hd'. have Hlen' := decode_value_length _ _ _ Hdec.
      rewrite fb_mix_plain; [|lia]. rewrite gfbytes_bytes. iModIntro. iFrame.
      iSplit; [iApply gcells_lift|]. iPureIntro. by constructor.
    - (* a tuple: its fields *)
      destruct (mty_wf_tuple_inv _ _ Hwf) as (Hdisj & Hin & Hwfs).
      rewrite gcells_tuple_zip; [|done].
      iMod (gopen_fields Reg k R fs fvs fbs A l with "Ctx Auth Toks Hfb Hc")
        as (bs vs) "(Auth & Toks & Hbs & %Hbsp & Cl)"; [done|by rewrite Hlen|done..|].
      destruct Hbsp as (Hlenbs & Hlenvs & Hdecs & _).
      iModIntro. iExists bs, (VTuple vs). iFrame "Auth Toks Hbs". iSplit.
      { iPureIntro. rewrite decode_value_tuple decide_True; [|lia]. apply fmap_Some_2.
        apply mapM_Some, Forall2_same_length_lookup. split; [done|]. intros ? ? ? ? ?. by eapply Hdecs. }
      iIntros (l' bs' Hd') "Hbs'".
      move: Hd'. rewrite decode_value_tuple. case_decide as Hlen'; [|done].
      intros (vs' & Hvs' & [= <-])%fmap_Some_1. apply mapM_Some, Forall2_same_length_lookup in Hvs'.
      destruct Hvs' as [_ Hvs'].
      iMod ("Cl" with "[%] [%] Hbs'") as "(Hfb & Hc & %Hreps)"; [lia|done|].
      iModIntro. iFrame "Hfb". rewrite gcells_tuple_zip; [|done]. iFrame "Hc".
      iPureIntro. apply frepr_tuple; [rewrite fb_mix_length; lia|done|done|].
      intros i fb Hi Hnf. destruct (lookup_lt_is_Some_2 fbs i) as [fb0 Hfb0].
      { rewrite -(fb_mix_length fbs bs'); [|lia]. by eapply lookup_lt_Some. }
      destruct (Hpad i fb0 Hfb0 Hnf) as [b0 ->].
      destruct (lookup_lt_is_Some_2 bs' i) as [b' Hb'].
      { rewrite Hlen'. rewrite -Hlen. by eapply lookup_lt_Some. }
      rewrite (fb_mix_lookup _ _ _ _ _ Hfb0 Hb') in Hi. injection Hi as <-. by eexists.
    - (* an enum: its payload, as a single field *)
      destruct (mty_wf_enum_inv _ _ _ Hwf) as [Hvars Htagsz].
      destruct (Forall_lookup_1 _ _ _ _ Hvars Hvm) as [Hszvm Hwfvm].
      set fs := [(int_size tag, vm)].
      have Hdisj : fields_disjoint fs.
      { intros [|[]] [|[]] ??????; simpl; intros; simplify_eq; lia. }
      have Hnf : ∀ i, ¬ in_field fs i ↔ (i < int_size tag ∨ int_size tag + mty_size vm ≤ i)%nat.
      { intros i. rewrite /fs /in_field. split.
        - intros Hi. destruct (decide (i < int_size tag)%nat); [by left|]. right.
          destruct (decide (int_size tag + mty_size vm ≤ i)%nat); [done|]. exfalso. apply Hi.
          exists (int_size tag, vm). split; [by left|simpl; lia].
        - intros Hi (f & ->%elem_of_list_singleton & ?). simpl in *. lia. }
      have Htk : ∀ i, (i < int_size tag)%nat → ∃ b, fbs !! i = Some (inr b) ∧ bst !! i = Some b.
      { intros i Hi. have : take (int_size tag) fbs !! i = (inr <$> bst) !! i by rewrite Htag.
        rewrite lookup_take // list_lookup_fmap.
        destruct (fbs !! i) as [fbi|] eqn:Hfbi.
        - destruct (bst !! i); simpl; intros; simplify_eq. eauto.
        - exfalso. apply lookup_ge_None in Hfbi. lia. }
      have Hpad' : ∀ i fb, fbs !! i = Some fb → ¬ in_field fs i → is_plain fb.
      { intros i fb Hi [Hi'|Hi']%Hnf.
        - destruct (Htk i Hi') as (b & Hb & _). rewrite Hb in Hi. injection Hi as <-. by eexists.
        - by eapply Hpad. }
      iEval (rewrite gcells_enum Hvm) in "Hc".
      iMod (gopen_fields Reg k R fs [d] fbs A l with "Ctx Auth Toks Hfb [Hc]")
        as (bs vs) "(Auth & Toks & Hbs & %Hbsp & Cl)"; [done| | |done|done| |done|done|done| |].
      { rewrite /fs Forall_singleton /=. lia. }
      { rewrite /fs Forall_singleton. done. }
      { intros [|[]] f fvj; simpl; intros; simplify_eq. done. }
      { rewrite /= right_id. done. }
      destruct Hbsp as (Hlenbs & Hlenvs & Hdecs & Hpadbs).
      destruct vs as [|vd [|]]; simpl in Hlenvs; try lia.
      have Hvd := Hdecs 0%nat _ vd eq_refl eq_refl. simpl in Hvd.
      have Hbst : take (int_size tag) bs = bst.
      { apply list_eq. intros i. destruct (decide (i < int_size tag)%nat).
        - rewrite lookup_take // Hpadbs; [|apply Hnf; by left].
          destruct (Htk i l0) as (b & Hb & Hbi). by rewrite /fb_base list_lookup_fmap Hb Hbi.
        - rewrite lookup_take_ge; [|lia]. symmetry. apply lookup_ge_None.
          have : length (take (int_size tag) fbs) = length (inr <$> bst : list (positive + abyte)) by rewrite Htag.
          rewrite length_take length_fmap. lia. }
      iModIntro. iExists bs, (VVariant t vd). iFrame "Auth Toks Hbs". iSplit.
      { iPureIntro. rewrite decode_value_enum decide_True; [|lia]. rewrite Hbst Ht /=.
        rewrite decide_True //. by rewrite Hvm /= Hvd. }
      iIntros (l' bs' Hd') "Hbs'".
      move: Hd'. rewrite decode_value_enum. case_decide as Hlen'; [|done].
      destruct (decode_int tag (take (int_size tag) bs')) as [t'|] eqn:Ht'; simpl; [|done].
      case_decide; [|done]. destruct (vars !! Z.to_nat t') as [vm'|] eqn:Hvm'; simpl; [|done].
      intros (vd' & Hvd' & [= <- <-])%fmap_Some_1. rewrite Hvm in Hvm'. injection Hvm' as <-.
      iMod ("Cl" with "[%] [%] Hbs'") as "(Hfb & Hc & %Hreps)"; [lia| |].
      { intros [|[]] f vj; simpl; intros; simplify_eq. done. }
      iModIntro. iFrame "Hfb". iSplitL "Hc".
      { rewrite Hvm. iDestruct "Hc" as "[$ _]". }
      iPureIntro. eapply (frepr_enum R vars tag sz _ t vm d (take (int_size tag) bs')).
      + rewrite fb_mix_length; lia.
      + rewrite fb_mix_take Htag fb_mix_plain //. rewrite length_take.
        have : length (take (int_size tag) fbs) = length (inr <$> bst : list (positive + abyte)) by rewrite Htag.
        rewrite length_take length_fmap. lia.
      + done.
      + done.
      + done.
      + exact (Hreps 0%nat _ d eq_refl eq_refl).
      + intros i fb Hi Hge. destruct (lookup_lt_is_Some_2 fbs i) as [fb0 Hfb0].
        { rewrite -(fb_mix_length fbs bs'); [|lia]. by eapply lookup_lt_Some. }
        destruct (Hpad i fb0 Hfb0 Hge) as [b0 ->].
        destruct (lookup_lt_is_Some_2 bs' i) as [b' Hb'].
        { rewrite Hlen'. rewrite -Hlen. by eapply lookup_lt_Some. }
        rewrite (fb_mix_lookup _ _ _ _ _ Hfb0 Hb') in Hi. injection Hi as <-. by eexists.
  Qed.
End gcells_open.
