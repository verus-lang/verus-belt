From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants ghost_map.
From lrust.typing Require Export type.
From lrust.typing Require Import uniq_util.
From lrust.lifetime Require Import lifetime_full guarded_bor.
From guarding Require Import guard tactics.
From iris.program_logic Require Import ectx_lifting.
From lrust.lang Require tactics.
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

(** ** Replacing a plain sub-value *)

(** [fv_repl m fv o m' fvo fv' fvn]: [fvn] is [fv] with its sub-value [fvo] at [o] (of type
    [m']) replaced by [fv'] (as [fv_upd], remembering the old sub-value). *)
Inductive fv_repl : mty → FValue → nat → mty → FValue → FValue → FValue → Prop :=
| fv_repl_here m fvo fv' : fv_repl m fvo 0 m fvo fv' fv'
| fv_repl_field fs sz fvs k off fm fvk o m' fvo fv' fvk' :
    fs !! k = Some (off, fm) → fvs !! k = Some fvk → fv_repl fm fvk o m' fvo fv' fvk' →
    fv_repl (MTuple fs sz) (FVTuple fvs) (off + o) m' fvo fv' (FVTuple (<[k := fvk']> fvs))
| fv_repl_payload vars tag sz t d vm o m' fvo fv' d' :
    vars !! Z.to_nat t = Some vm → fv_repl vm d o m' fvo fv' d' →
    fv_repl (MEnum vars tag sz) (FVVariant t d) (int_size tag + o) m' fvo fv' (FVVariant t d').

Lemma fv_repl_upd m fv o m' fvo fv' fvn : fv_repl m fv o m' fvo fv' fvn → fv_upd m fv o m' fv' fvn.
Proof. induction 1; econstructor; eauto. Qed.
Lemma fv_repl_sub m fv o m' fvo fv' fvn : fv_repl m fv o m' fvo fv' fvn → fv_sub m fv o m' fvo.
Proof. induction 1; econstructor; eauto. Qed.
Lemma fv_sub_repl m fv o m' fvo fv' : fv_sub m fv o m' fvo → ∃ fvn, fv_repl m fv o m' fvo fv' fvn.
Proof. induction 1; naive_solver eauto using fv_repl. Qed.
Lemma fv_sub_repl_refl m fv o m' fvo : fv_sub m fv o m' fvo → fv_repl m fv o m' fvo fvo fv.
Proof.
  induction 1 as [|fs sz fvs k off fm fvk o m' fv' Hk Hfvk Hsub IH|]; [constructor| |by econstructor].
  rewrite -{2}(list_insert_id fvs k fvk) //. by econstructor.
Qed.

Definition lazyE_gcellsN : lazyE ## ↑gcellsN.
Proof. rewrite /lazyE /gcellsN /gmbN /uniqN /NllftUsr /prophN /Nllft. solve_ndisj. Qed.

Section gcells_api.
  Context `{!typeG Σ, !gcellsGS Σ}.
  Implicit Types (l : loc) (m : mty) (fv : FValue) (fbs : list (positive + abyte)).
  Notation gca γ l := (gmb_a (S:=loc) (T:=FValue) γ l).

  (** *** Cells in transit

  The cells of a value that has been loaded by a typed move ([gcont_open]), with the value
  [v] that the move loaded: bytes at any location [l'] that decode to [v] give back the
  contents at [l'] (with the cells at their new locations). *)
  Definition gtransit m fv (v : Value) : iProp Σ :=
    ⌜val_wf m v⌝ ∗ ∀ l' bs', ⌜decode_value m bs' = Some v⌝ -∗ l' ↦b bs' ={lazyE}=∗ gcont l' m fv.

  (** The deep opening, with the registry: it moves all the cells of [fv] (and the cells
      nested in them); the location [l] then holds plain bytes that decode at [m]. *)
  Lemma gcont_open E l m fv :
    lazyE ∪ ↑gcellsN ⊆ E → mty_wf m →
    gcells_ctx -∗ £ 1 -∗ gcont l m fv ={E}=∗
      ∃ bs v, l ↦b bs ∗ ⌜decode_value m bs = Some v⌝ ∗ gtransit m fv v.
  Proof.
    iIntros (HE Hwf) "#GC Lc (%R & %fbs & Hfb & [%Hrep %HR] & Hc)".
    iInv "GC" as (Reg) "[>Auth Ctx]" "Hcl".
    iMod (lc_fupd_elim_later with "Lc Ctx") as "#Ctx".
    iMod (fupd_mask_subseteq lazyE) as "Hclm".
    { have := lazyE_gcellsN. set_solver. }
    iMod (gopen_rec Reg (size Reg) R m fbs fv HR Hrep [] l Hwf with "Ctx Auth [] Hfb Hc")
      as (bs v) "(Auth & _ & Hbs & %Hd & Cl)".
    { constructor. } { by intros ? ?%elem_of_nil. } { simpl. lia. } { by rewrite /gtoks. }
    iMod "Hclm" as "_". iMod ("Hcl" with "[Auth]") as "_".
    { iNext. iExists Reg. iFrame "Auth Ctx". }
    iModIntro. iExists bs, v. iFrame "Hbs". iSplit; [done|]. iSplit.
    { iPureIntro. by eapply decode_value_wf. }
    iIntros (l' bs' Hd') "Hbs'". iMod ("Cl" with "[//] Hbs'") as "(Hfb & Hc & %Hrep')".
    iModIntro. iExists R, _. by iFrame.
  Qed.

  Lemma gtransit_close E l' m fv v bs' :
    lazyE ⊆ E → decode_value m bs' = Some v →
    gtransit m fv v -∗ l' ↦b bs' ={E}=∗ gcont l' m fv.
  Proof.
    iIntros (HE Hd) "[_ Cl] Hbs". iApply (fupd_mask_mono lazyE); [done|]. by iApply ("Cl" with "[//] Hbs").
  Qed.

  (** *** Cells: create, destroy, access by the owner of both sides *)
  Lemma gcont_cell l m g γ : gcell_reg g γ m -∗ gca γ l -∗ gcont l m (FVCell g).
  Proof.
    iIntros "#Hreg Ha". iExists {[g := (m, replicate (mty_size m) g)]}, (inl <$> replicate (mty_size m) g).
    rewrite gfbytes_cells. iSplit; [done|]. iSplit.
    - iPureIntro. split.
      + constructor. by rewrite lookup_singleton.
      + intros g' m' cs. rewrite lookup_singleton_Some. intros [<- [= <- <-]]. by rewrite length_replicate.
    - iEval (simpl). iExists γ. by iFrame "Hreg Ha".
  Qed.

  Lemma gcont_cell_inv l m g : gcont l m (FVCell g) -∗ ∃ γ, gcell_reg g γ m ∗ gca γ l.
  Proof. iIntros "(%R & %fbs & _ & _ & Hc)". by iEval (simpl) in "Hc". Qed.

  Lemma gcell_reg_agree g γ γ' m m' : gcell_reg g γ m -∗ gcell_reg g γ' m' -∗ ⌜γ = γ' ∧ m = m'⌝.
  Proof. iIntros "H1 H2". by iDestruct (ghost_map_elem_agree with "H1 H2") as %[= -> ->]. Qed.

  (** (L0) Creation ([PCell::new]): the contents at [l] become a cell, an instance of depth
      [0] and bytes mask [lazyB], registered as [g]. The location then holds the cell
      itself ([gcont l m (FVCell g)], i.e. the move right). *)
  Lemma gcell_create E l m fv :
    ↑gcellsN ⊆ E →
    gcells_ctx -∗ gcont l m fv ={E}=∗ ∃ g γ, ⌜gmb_depth γ = 0 ∧ gmb_bmask γ = lazyB⌝ ∗
      gcell_reg g γ m ∗ gmb_inv (gcont_c m) γ ∗ gmb_b γ fv ∗ gcont l m (FVCell g).
  Proof.
    iIntros (HE) "#GC C".
    iMod (gmb_create_mask (gcont_c m) E 0 lazyB l fv with "C") as (γ) "([%Hd %Hb] & #GI & Ha & Hb)".
    { rewrite /lazyB /gmbN /uniqN /NllftUsr /prophN /Nllft. solve_ndisj. }
    iInv "GC" as (Reg) "[>Auth Ctx]" "Hcl".
    set g := fresh (dom Reg).
    have Hg : Reg !! g = None by apply not_elem_of_dom, is_fresh.
    iMod (ghost_map_insert_persist g (γ, m) with "Auth") as "[Auth #Hreg]"; [done|].
    iMod ("Hcl" with "[Auth Ctx]") as "_".
    { iNext. iExists (<[g := (γ, m)]> Reg). iFrame "Auth". rewrite /greg_ctx big_sepM_insert //.
      iFrame "Ctx". by iFrame "GI". }
    iModIntro. iExists g, γ. iSplit; [done|]. iSplitR; [iExact "Hreg"|]. iFrame "GI Hb".
    by iApply (gcont_cell with "Hreg Ha").
  Qed.

  (** (L0) Destruction ([PCell::into_inner]). *)
  Lemma gcell_destroy E l m g γ fv :
    ↑Nllft ⊆ E →
    gcell_reg g γ m -∗ gmb_inv (gcont_c m) γ -∗ gcont l m (FVCell g) -∗ gmb_b γ fv ={E}=∗
      gcont l m fv.
  Proof.
    iIntros (HE) "#Hreg #GI C Hb". iDestruct (gcont_cell_inv with "C") as (γ') "[Hreg' Ha]".
    iDestruct (gcell_reg_agree with "Hreg Hreg'") as %[<- _].
    by iMod (gmb_destroy (gcont_c m) with "GI Ha Hb") as "C".
  Qed.

  (** Access by the owner of the cell and of its permission: the contents can be changed. *)
  Lemma gcell_acc E l m g γ fv :
    ↑NllftUsr ∪ ↑NllftUsr2 ⊆ E →
    gcell_reg g γ m -∗ gmb_inv (gcont_c m) γ -∗ gcont l m (FVCell g) -∗ gmb_b γ fv ={E}=∗
      gcont l m fv ∗ (∀ fv', gcont l m fv' ={E}=∗ gcont l m (FVCell g) ∗ gmb_b γ fv').
  Proof.
    iIntros (HE) "#Hreg #GI C Hb". iDestruct (gcont_cell_inv with "C") as (γ') "[Hreg' Ha]".
    iDestruct (gcell_reg_agree with "Hreg Hreg'") as %[<- _].
    iMod (gmb_acc (gcont_c m) with "GI Ha Hb") as "[$ Cl]"; [done|].
    iIntros "!>" (fv') "C". iMod ("Cl" $! l fv' with "C") as "[Ha $]".
    iModIntro. by iApply (gcont_cell with "Hreg Ha").
  Qed.

  (** (L2) Shared access: guards of the move right and of the permission. *)
  Lemma gcell_share G F n γ l m fv :
    ↑NllftUsr2 ⊆ F →
    gmb_inv (gcont_c m) γ -∗ (G &&{F; n}&&> gca γ l) -∗ (G &&{F; n}&&> gmb_b γ fv) -∗
      (G &&{F; n}&&> gcont l m fv).
  Proof. iIntros (?) "GI Ga Gb". by iApply (gmb_share (gcont_c m) with "GI Ga Gb"). Qed.

  (** (L3) Mutable access: a lend of the contents, for an instance of depth [0] (the lend
      prepays a credit for the moves). *)
  Lemma gcell_lend E γ κ l m :
    ↑Nllft ⊆ E → gmb_depth γ = 0 →
    llft_ctx -∗ gmb_inv (gcont_c m) γ -∗ (@[κ] &&{↑NllftG}&&> gca γ l) -∗ £ 1 -∗
    &{κ} (∃ fv, gmb_b γ fv) -∗ @[κ] ={E}=∗ &{κ} (∃ fv, gcont l m fv) ∗ @[κ].
  Proof.
    iIntros (HE Hd) "#LFT #GI #Ga Lc Bor Alive".
    iApply (gmb_lend (gcont_c m) with "LFT GI Ga [Lc] Bor Alive"); [done|by rewrite Hd].
  Qed.

  Lemma gcell_lend_guarded E G γ κ l m :
    Timeless G → ↑Nllft ⊆ E → gmb_depth γ = 0 →
    llft_ctx -∗ gmb_inv (gcont_c m) γ -∗ (@[κ] &&{↑NllftG}&&> gca γ l) -∗ £ 1 -∗
    &{κ} (∃ fv, gmb_b γ fv) -∗ (G &&{↑NllftG}&&> @[κ]) -∗ G ={E}=∗
      &{κ} (∃ fv, gcont l m fv) ∗ G.
  Proof.
    iIntros (HG HE Hd) "#LFT #GI #Ga Lc Bor #Gk G".
    iApply (gmb_lend_guarded (gcont_c m) with "LFT GI Ga [Lc] Bor Gk G"); [done|by rewrite Hd].
  Qed.

  (** (L3) with a predicate [Φ] of the logical contents, carried by the borrow (e.g. the
      ownership predicate of the type of the contents): the lender gets back the
      permission at the final contents, with [Φ] of them. *)
  Lemma gcell_lend_pred E γ κ l m (Φ : FValue → iProp Σ) :
    ↑Nllft ⊆ E → gmb_depth γ = 0 →
    llft_ctx -∗ gmb_inv (gcont_c m) γ -∗ (@[κ] &&{↑NllftG}&&> gca γ l) -∗ £ 1 -∗
    &{κ} (∃ fv, gmb_b γ fv ∗ Φ fv) -∗ @[κ] ={E}=∗ &{κ} (∃ fv, gcont l m fv ∗ Φ fv) ∗ @[κ].
  Proof.
    iIntros (HE Hd) "#LFT #GI #Ga Lc Bor Alive". iMod lc_zero as "Lc0".
    iMod (llftl_bor_acc_special with "LFT Bor Alive") as "(Fb & Tok & Close)"; first done.
    iMod (bi.later_exist_except_0 with "Fb") as (fv) "[>Fb Φ]".
    iMod (gmb_lend_start (gcont_c m) _ γ κ l fv 0 with "LFT GI Ga Lc0 [Lc] Tok Fb")
      as "[C Lent]"; [done|lia|by rewrite Hd|].
    iApply (fupd_mask_mono (↑Nllft)); first done.
    iApply ("Close" $! (∃ fv', gcont l m fv' ∗ Φ fv')%I with "[Lent C Φ]").
    iSplitR "C Φ"; last first. { iNext. iExists fv. iFrame. }
    iNext. iIntros "[Q _]". iMod (bi.later_exist_except_0 with "Q") as (fv') "[>C Φ]".
    iMod (gmb_lend_stop (gcont_c m) with "GI Lent C") as "[Fb $]".
    iModIntro. iNext. iExists fv'. iFrame.
  Qed.
End gcells_api.

(** ** Access to plain sub-values of owned contents (for borrows and owners) *)
Section gcells_sub.
  Context `{!typeG Σ, !gcellsGS Σ}.
  Implicit Types (l : loc) (m : mty) (fv : FValue) (fbs : list (positive + abyte)).

  Lemma gcells_lift_iff l m v : gcells l m (fv_lift v) ⊣⊢ True.
  Proof. iSplit; [by iIntros|]. iIntros "_". iApply gcells_lift. Qed.

  (** Replacing a plain sub-value by a plain one does not change the cells. *)
  Lemma gcells_repl l m fv o m' vo vn fvn :
    fv_repl m fv o m' (fv_lift vo) (fv_lift vn) fvn → gcells l m fvn ⊣⊢ gcells l m fv.
  Proof.
    intros Hr. remember (fv_lift vo) as fo eqn:Hfo. remember (fv_lift vn) as fnew eqn:Hfn.
    revert l. induction Hr as [m fvo fv'|fs sz fvs k off fm fvk o m' fvo fv' fvk' Hk Hfvk Hr IH
      |vars tag sz t d vm o m' fvo fv' d' Hvm Hr IH]; intros l; subst.
    - by rewrite !gcells_lift_iff.
    - rewrite !gcells_tuple. apply big_sepL_same_length; [by rewrite length_insert|].
      intros j fvj fvj' Hj Hj'. destruct (decide (j = k)) as [->|Hne].
      + rewrite list_lookup_insert in Hj; [|by eapply lookup_lt_Some]. injection Hj as <-.
        rewrite Hfvk in Hj'. injection Hj' as <-. rewrite Hk. by apply IH.
      + rewrite list_lookup_insert_ne in Hj; [|done]. rewrite Hj in Hj'. by injection Hj' as <-.
    - rewrite !gcells_enum Hvm. by apply IH.
  Qed.

  (** The plain sub-value at [o] of owned contents: its bytes, and the contents with any
      new plain sub-value there. *)
  Lemma gcont_sub_acc l m fv o m' vo :
    mty_wf m → fv_sub m fv o m' (fv_lift vo) →
    gcont l m fv ⊢ ∃ bs, ⌜decode_value m' bs = Some vo⌝ ∗ (l +ₗ o) ↦b bs ∗
      (∀ bs' vn fvn, ⌜decode_value m' bs' = Some vn⌝ -∗
         ⌜fv_repl m fv o m' (fv_lift vo) (fv_lift vn) fvn⌝ -∗ (l +ₗ o) ↦b bs' -∗ gcont l m fvn).
  Proof.
    iIntros (Hwf Hsub) "(%R & %fbs & Hfb & [%Hrep %HR] & Hc)".
    destruct (frepr_sub_plain _ _ _ _ _ _ _ HR Hrep Hsub Hwf (fv_cells_lift vo))
      as (bs & v & Hsl & Hd & Hv). apply fv_lift_inj in Hv. subst v.
    have Hb := fv_sub_bound _ _ _ _ _ Hsub Hwf. have Hl := frepr_length _ _ _ _ HR Hrep.
    rewrite /gfbytes (big_sepL_select (in_rng o (mty_size m'))) big_sepL_rng; [|lia].
    rewrite Hsl big_sepL_fmap. iDestruct "Hfb" as "[Hbs Hrest]".
    iExists bs. iSplit; [done|]. iSplitL "Hbs"; [by rewrite heap_mapsto_bytes_pos_shift|].
    iIntros (bs' vn fvn Hd' Hr) "Hbs'".
    have Hl' := decode_value_length _ _ _ Hd'. have Hlb := decode_value_length _ _ _ Hd.
    iExists R, (list_inserts o (inr <$> bs') fbs). iSplitL "Hbs' Hrest"; [|iSplit].
    - have Hsl' : list_slice o (mty_size m') (list_inserts o (inr <$> bs') fbs) = inr <$> bs'.
      { replace (list_inserts o (inr <$> bs') fbs) with (list_inserts (o + 0) (inr <$> bs') fbs)
          by by rewrite Nat.add_0_r.
        rewrite list_slice_inserts_in; [|lia|rewrite length_fmap; lia].
        rewrite list_inserts_all //. rewrite length_fmap /list_slice length_take length_drop. lia. }
      iEval (rewrite /gfbytes). iApply (big_sepL_select (in_rng o (mty_size m'))).
      iSplitL "Hbs'".
      { iApply (big_sepL_rng with "[Hbs']"); [rewrite length_inserts; lia|].
        rewrite Hsl' big_sepL_fmap. by rewrite heap_mapsto_bytes_pos_shift. }
      iApply (big_sepL_same_length with "Hrest"); [by rewrite length_inserts|].
      intros i fb' fb Hi' Hi. case_decide as Hin; [done|].
      rewrite list_lookup_inserts_Some in Hi'. destruct Hi' as [[_ Hi']|[Hr' _]].
      + rewrite Hi in Hi'. by injection Hi' as <-.
      + exfalso. apply Hin. rewrite length_fmap in Hr'. rewrite /in_rng. lia.
    - iPureIntro. split; [|done]. eapply frepr_upd; [done|done|by eapply fv_repl_upd|done|done].
    - by rewrite (gcells_repl _ _ _ _ _ _ _ _ Hr).
  Qed.

  Lemma gcont_sub_view l m fv o m' vo :
    mty_wf m → fv_sub m fv o m' (fv_lift vo) →
    gcont l m fv ⊢ ∃ bs, ⌜decode_value m' bs = Some vo⌝ ∗ (l +ₗ o) ↦b bs ∗
      ((l +ₗ o) ↦b bs -∗ gcont l m fv).
  Proof.
    iIntros (Hwf Hsub) "C". iDestruct (gcont_sub_acc with "C") as (bs Hd) "[Hbs Cl]"; [done..|].
    iExists bs. iFrame "Hbs". iSplit; [done|]. iIntros "Hbs". iApply ("Cl" with "[//] [] Hbs").
    iPureIntro. by apply fv_sub_repl_refl.
  Qed.

  (** Values without cells. *)
  Lemma gcont_of_bytes l m bs v : decode_value m bs = Some v → l ↦b bs -∗ gcont l m (fv_lift v).
  Proof.
    iIntros (Hd) "Hbs". iExists ∅, (inr <$> bs). rewrite gfbytes_bytes. iFrame "Hbs". iSplit.
    - iPureIntro. split; [by constructor|]. by intros ???.
    - iApply gcells_lift.
  Qed.

  Lemma gcont_lift_bytes l m v : gcont l m (fv_lift v) -∗ ∃ bs, l ↦b bs ∗ ⌜decode_value m bs = Some v⌝.
  Proof.
    iIntros "(%R & %fbs & Hfb & [%Hrep _] & _)". destruct (frepr_lift _ _ _ _ Hrep) as (bs & -> & Hd).
    rewrite gfbytes_bytes. iExists bs. by iFrame.
  Qed.
End gcells_sub.

(** ** Program steps *)
Section gcells_wp.
  Context `{!typeG Σ, !gcellsGS Σ}.
  Implicit Types (l : loc) (m : mty) (fv : FValue).
  Notation gca γ l := (gmb_a (S:=loc) (T:=FValue) γ l).

  (** *** Moves: typed [Load]/[Store] and verbatim [MemCopy] of a value with cells *)

  (** A typed [Load] moves the cells of the value (and the cells nested in them) out: the
      location keeps plain bytes, and the cells travel with the loaded value. *)
  Lemma wp_gcont_load_move E l m fv :
    lazyE ∪ ↑gcellsN ⊆ E → mty_wf m →
    {{{ gcells_ctx ∗ £ 1 ∗ gcont l m fv }}} Load Na1Ord m (Lit $ LitLoc l) @ E
    {{{ v bs, RET MLitV v; l ↦b bs ∗ ⌜length bs = mty_size m⌝ ∗ gtransit m fv v }}}.
  Proof.
    iIntros (HE Hwf Φ) "(#GC & Lc & C) HΦ".
    iMod (gcont_open with "GC Lc C") as (bs v) "(Hbs & %Hd & Tr)"; [done..|].
    iApply (wp_load_na with "Hbs"); [done|]. iIntros "!> Hbs". iApply "HΦ". iFrame.
    iPureIntro. by eapply decode_value_length.
  Qed.

  (** A typed [Store] of a value whose cells are in transit puts them at the new location:
      the bytes there are [encode_value m v], which decode to [v] (re-encoding). *)
  Lemma wp_gtransit_store E l' m fv v bs0 :
    lazyE ∪ ↑naN ⊆ E → mty_wf m → length bs0 = mty_size m →
    {{{ ▷ l' ↦b bs0 ∗ gtransit m fv v }}} Store Na1Ord m (Lit $ LitLoc l') (MLit v) @ E
    {{{ RET LitV LitPoison; gcont l' m fv }}}.
  Proof.
    iIntros (HE Hwf Hlen Φ) "[Hbs [%Hvwf Cl]] HΦ". iApply wp_fupd.
    iApply (wp_store_na with "Hbs"); [set_solver|done|done|]. iIntros "!> Hbs".
    iMod (fupd_mask_subseteq lazyE) as "Hclm"; [set_solver|].
    iMod ("Cl" with "[%] Hbs") as "C"; [by apply decode_encode_value|].
    iMod "Hclm" as "_". by iApply "HΦ".
  Qed.

  (** A typed move: [Store m (Load m)]. *)
  Lemma wp_gcont_move E l l' m fv bs0 :
    lazyE ∪ ↑gcellsN ∪ ↑naN ⊆ E → mty_wf m → length bs0 = mty_size m →
    {{{ gcells_ctx ∗ £ 1 ∗ gcont l m fv ∗ ▷ l' ↦b bs0 }}}
      Store Na1Ord m (Lit $ LitLoc l') (Load Na1Ord m (Lit $ LitLoc l)) @ E
    {{{ bs, RET LitV LitPoison; l ↦b bs ∗ gcont l' m fv }}}.
  Proof.
    iIntros (HE Hwf Hlen Φ) "(#GC & Lc & C & Hl') HΦ".
    wp_bind (Load _ _ _). iApply (wp_gcont_load_move with "[$GC $Lc $C]"); [set_solver|done|].
    iIntros "!>" (v bs) "(Hbs & _ & Tr)".
    iApply (wp_gtransit_store with "[$Hl' $Tr]"); [set_solver|done|done|].
    iIntros "!> C". iApply "HΦ". iFrame.
  Qed.

  (** A verbatim move: [MemCopy]. The bytes at the new location are the old ones. *)
  Lemma wp_gcont_memcopy E l l' m fv bs0 :
    lazyE ∪ ↑gcellsN ∪ ↑naN ⊆ E → mty_wf m → length bs0 = mty_size m →
    {{{ gcells_ctx ∗ £ 1 ∗ gcont l m fv ∗ ▷ l' ↦b bs0 }}}
      MemCopy Na1Ord (mty_size m) (Lit $ LitLoc l') (Lit $ LitLoc l) @ E
    {{{ bs, RET LitV LitPoison; l ↦b bs ∗ gcont l' m fv }}}.
  Proof.
    iIntros (HE Hwf Hlen Φ) "(#GC & Lc & C & Hl') HΦ".
    iMod (gcont_open with "GC Lc C") as (bs v) "(Hbs & %Hd & Tr)"; [set_solver|done|].
    iApply wp_fupd. iApply (wp_memcopy with "[$Hl' $Hbs]"); [set_solver|done|by eapply decode_value_length|].
    iIntros "!> [Hl' Hbs]".
    iMod (gtransit_close with "Tr Hl'") as "C"; [set_solver|done|].
    iModIntro. iApply "HΦ". iFrame.
  Qed.

  (** *** Accesses to plain sub-values of owned contents (e.g. through a lend) *)
  Lemma wp_gcont_load_na_sub E l m fv o m' vo :
    mty_wf m → fv_sub m fv o m' (fv_lift vo) →
    {{{ gcont l m fv }}} Load Na1Ord m' (Lit $ LitLoc (l +ₗ o)) @ E
    {{{ RET MLitV vo; gcont l m fv }}}.
  Proof.
    iIntros (Hwf Hsub Φ) "C HΦ". iDestruct (gcont_sub_view with "C") as (bs Hd) "[Hbs Cl]"; [done..|].
    iApply (wp_load_na with "Hbs"); [done|]. iIntros "!> Hbs". iApply "HΦ". by iApply "Cl".
  Qed.

  Lemma wp_gcont_load_sc_sub E l m fv o m' vo :
    mty_wf m → fv_sub m fv o m' (fv_lift vo) →
    {{{ gcont l m fv }}} Load ScOrd m' (Lit $ LitLoc (l +ₗ o)) @ E
    {{{ RET MLitV vo; gcont l m fv }}}.
  Proof.
    iIntros (Hwf Hsub Φ) "C HΦ". iDestruct (gcont_sub_view with "C") as (bs Hd) "[Hbs Cl]"; [done..|].
    iApply (wp_load_sc with "Hbs"); [done|]. iIntros "!> Hbs". iApply "HΦ". by iApply "Cl".
  Qed.

  Lemma wp_gcont_store_na_sub E l m fv o m' vo vn fvn :
    ↑naN ⊆ E → mty_wf m → val_wf m' vn → fv_repl m fv o m' (fv_lift vo) (fv_lift vn) fvn →
    {{{ gcont l m fv }}} Store Na1Ord m' (Lit $ LitLoc (l +ₗ o)) (MLit vn) @ E
    {{{ RET LitV LitPoison; gcont l m fvn }}}.
  Proof.
    iIntros (HE Hwf Hvn Hr Φ) "C HΦ". have Hsub := fv_repl_sub _ _ _ _ _ _ _ Hr.
    have Hwf' := fv_sub_wf _ _ _ _ _ Hsub Hwf.
    iDestruct (gcont_sub_acc with "C") as (bs Hd) "[Hbs Cl]"; [done..|].
    iApply (wp_store_na with "Hbs"); [done|done|by eapply decode_value_length|].
    iIntros "!> Hbs". iApply "HΦ". iApply ("Cl" with "[%] [//] Hbs"). by apply decode_encode_value.
  Qed.

  Lemma wp_gcont_store_sc_sub E l m fv o m' vo vn fvn :
    ↑naN ⊆ E → mty_wf m → val_wf m' vn → fv_repl m fv o m' (fv_lift vo) (fv_lift vn) fvn →
    {{{ gcont l m fv }}} Store ScOrd m' (Lit $ LitLoc (l +ₗ o)) (MLit vn) @ E
    {{{ RET LitV LitPoison; gcont l m fvn }}}.
  Proof.
    iIntros (HE Hwf Hvn Hr Φ) "C HΦ". have Hsub := fv_repl_sub _ _ _ _ _ _ _ Hr.
    have Hwf' := fv_sub_wf _ _ _ _ _ Hsub Hwf.
    iDestruct (gcont_sub_acc with "C") as (bs Hd) "[Hbs Cl]"; [done..|].
    iApply (wp_store_sc with "Hbs"); [done|done|by eapply decode_value_length|].
    iIntros "!> Hbs". iApply "HΦ". iApply ("Cl" with "[%] [//] Hbs"). by apply decode_encode_value.
  Qed.

  (** Compare-and-exchange of a plain sub-value. *)
  Lemma wp_gcont_mcas_sub E l m fv o m' vo v1 v2 fvn :
    ↑naN ⊆ E → mty_wf m → val_wf m' v2 → fv_repl m fv o m' (fv_lift vo) (fv_lift v2) fvn →
    {{{ gcont l m fv }}} MCAS m' (Lit $ LitLoc (l +ₗ o)) (MLit v1) (MLit v2) @ E
    {{{ b, RET MLitV (VBool b);
        (⌜b = true ∧ vo = v1⌝ ∗ gcont l m fvn) ∨ (⌜b = false ∧ vo ≠ v1⌝ ∗ gcont l m fv) }}}.
  Proof.
    iIntros (HE Hwf Hv2 Hr Φ) "C HΦ". have Hsub := fv_repl_sub _ _ _ _ _ _ _ Hr.
    have Hwf' := fv_sub_wf _ _ _ _ _ Hsub Hwf.
    iDestruct (gcont_sub_acc with "C") as (bs Hd) "[Hbs Cl]"; [done..|].
    iApply (wp_mcas with "Hbs"); [done|done|done|].
    iIntros "!>" (b) "[[[-> ->] Hbs]|[[-> %Hne] Hbs]]"; iApply "HΦ".
    - iLeft. iSplit; [done|]. iApply ("Cl" with "[%] [//] Hbs"). by apply decode_encode_value.
    - iRight. iSplit; [done|]. iApply ("Cl" with "[//] [%] Hbs"). by apply fv_sub_repl_refl.
  Qed.

  (** *** Guarded loads of plain sub-values (shared access, through (L2)) *)
  Lemma wp_gcont_load_na_guarded E l m fv o m' vo G d :
    ↑naN ⊆ E → mty_wf m → fv_sub m fv o m' (fv_lift vo) →
    {{{ (G &&{↑naN; d}&&> gcont l m fv) ∗ G ∗ £ (2*d) }}}
      Load Na1Ord m' (Lit $ LitLoc (l +ₗ o)) @ E
    {{{ RET MLitV vo; G }}}.
  Proof.
    iIntros (HE Hwf Hsub Φ) "(#Guard & G & £) HΦ".
    iApply (wp_load_na_guarded_gen _ _ _ _ _ (gcont l m fv) (λ bs, decode_value m' bs = Some vo)
      with "[$Guard $G $£]"); [done|by intros ? ->| |done].
    iIntros "!> C". iDestruct (gcont_sub_view with "C") as (bs Hd) "[Hbs Cl]"; [done..|].
    iExists bs. by iFrame.
  Qed.

  (** The atomic load of a guarded proposition [P] that contains bytes [bs] with [Ψ bs] (as
      [wp_load_na_guarded_gen]; the guard is opened around the single step). *)
  Lemma wp_load_sc_guarded_gen E l m v G P (Ψ : list abyte → Prop) d :
    ↑naN ⊆ E → (∀ bs, Ψ bs → decode_value m bs = Some v) →
    {{{ (G &&{↑naN; d}&&> P) ∗ □ (P -∗ ∃ bs, ⌜Ψ bs⌝ ∗ l ↦b bs ∗ (l ↦b bs -∗ P)) ∗ G ∗ £ d }}}
      Load ScOrd m (Lit $ LitLoc l) @ E
    {{{ RET MLitV v; G }}}.
  Proof.
    iIntros (? HΨ Φ) "(#Guard & #HP & G & £) HΦ".
    iApply wp_lift_atomic_base_step_no_fork; auto.
    iIntros (σ1 stepcnt κ κs n') "[Hσ Ht]". iDestruct "Hσ" as (hF) "(HB & HhF & %REL & ato)".
    iMod (guards_open_later with "Guard G") as "Open"; [done|].
    iMod (lc_fupd_elim_laterN with "£ Open") as ">[P Back]".
    iDestruct ("HP" with "P") as (bs HΨbs) "[Hbs Hcl]".
    have Hdec := HΨ _ HΨbs. have Hlen := decode_value_length _ _ _ Hdec.
    iDestruct (bytes_ctx_lookup with "HB Hbs") as %Hrange.
    iMod ("Back" with "[Hbs Hcl]") as "G"; [by iApply "Hcl"|].
    have Hrange' := Hrange.
    iModIntro. iSplit. { iPureIntro. eexists _, _, _, _. by eapply LoadScS. }
    iNext; iIntros (e2 σ2 efs Hstep) "credit"; lrust.lang.tactics.inv_head_step.
    match goal with H : mem_range _ _ _ ?bs' |- _ =>
      have Heq := mem_range_det _ _ _ _ _ _ Hrange' H ltac:(lia) end. subst.
    match goal with H : decode_value _ _ = Some _ |- _ => rewrite Hdec in H; simplify_eq end.
    iMod (time_interp_step with "Ht") as "$". iModIntro. iSplit; [done|].
    iSplitR "HΦ G"; [by iFrame|]. by iApply "HΦ".
  Qed.

  Lemma wp_gcont_load_sc_guarded E l m fv o m' vo G d :
    ↑naN ⊆ E → mty_wf m → fv_sub m fv o m' (fv_lift vo) →
    {{{ (G &&{↑naN; d}&&> gcont l m fv) ∗ G ∗ £ d }}}
      Load ScOrd m' (Lit $ LitLoc (l +ₗ o)) @ E
    {{{ RET MLitV vo; G }}}.
  Proof.
    iIntros (HE Hwf Hsub Φ) "(#Guard & G & £) HΦ".
    iApply (wp_load_sc_guarded_gen _ _ _ _ _ (gcont l m fv) (λ bs, decode_value m' bs = Some vo)
      with "[$Guard $G $£]"); [done|by intros ? ->| |done].
    iIntros "!> C". iDestruct (gcont_sub_view with "C") as (bs Hd) "[Hbs Cl]"; [done..|].
    iExists bs. by iFrame.
  Qed.

  (** Shared reads through a cell: guards of its move right and of its permission ((L2)). *)
  Lemma wp_gcell_load_na_shared E γ l m fv o m' vo G d :
    ↑naN ⊆ E → mty_wf m → fv_sub m fv o m' (fv_lift vo) →
    {{{ gmb_inv (gcont_c m) γ ∗ (G &&{↑naN; d}&&> gca γ l) ∗ (G &&{↑naN; d}&&> gmb_b γ fv) ∗
        G ∗ £ (2*d) }}}
      Load Na1Ord m' (Lit $ LitLoc (l +ₗ o)) @ E
    {{{ RET MLitV vo; G }}}.
  Proof.
    iIntros (HE Hwf Hsub Φ) "(#GI & #Ga & #Gb & G & £) HΦ".
    iDestruct (gcell_share with "GI Ga Gb") as "Gc".
    { rewrite /naN /NllftUsr2. solve_ndisj. }
    by iApply (wp_gcont_load_na_guarded with "[$Gc $G $£]").
  Qed.

  Lemma wp_gcell_load_sc_shared E γ l m fv o m' vo G d :
    ↑naN ⊆ E → mty_wf m → fv_sub m fv o m' (fv_lift vo) →
    {{{ gmb_inv (gcont_c m) γ ∗ (G &&{↑naN; d}&&> gca γ l) ∗ (G &&{↑naN; d}&&> gmb_b γ fv) ∗
        G ∗ £ d }}}
      Load ScOrd m' (Lit $ LitLoc (l +ₗ o)) @ E
    {{{ RET MLitV vo; G }}}.
  Proof.
    iIntros (HE Hwf Hsub Φ) "(#GI & #Ga & #Gb & G & £) HΦ".
    iDestruct (gcell_share with "GI Ga Gb") as "Gc".
    { rewrite /naN /NllftUsr2. solve_ndisj. }
    by iApply (wp_gcont_load_sc_guarded with "[$Gc $G $£]").
  Qed.
End gcells_wp.

(** ** Allocation of the registry *)
Lemma gcells_ctx_alloc `{!typeG Σ, !gcellsGpreS Σ} E :
  ⊢ |={E}=> ∃ _ : gcellsGS Σ, gcells_ctx.
Proof.
  iMod (ghost_map_alloc_empty (K:=positive) (V:=gmb_name * mty)) as (γr) "Auth".
  set (H := GCellsGS Σ _ _ γr).
  iMod (inv_alloc gcellsN E (@gcells_inv _ _ H) with "[Auth]") as "#GC".
  { iNext. iExists ∅. iFrame "Auth". by rewrite big_sepM_empty. }
  iModIntro. iExists H. done.
Qed.
