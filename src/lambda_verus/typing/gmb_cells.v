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

  Lemma big_sepL_shift_loc {A} (Φ : loc → A → iProp Σ) l (o : nat) (xs : list A) :
    ([∗ list] j ↦ x ∈ xs, Φ (l +ₗ o +ₗ j) x) ⊣⊢ ([∗ list] j ↦ x ∈ xs, Φ (l +ₗ (o + j)%nat) x).
  Proof. apply big_sepL_proper=> j x _. by rewrite shift_loc_assoc_nat. Qed.
End gcells_defs.
