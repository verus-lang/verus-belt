From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants ghost_map.
From lrust.lang Require Export proofmode heap.
From lrust.prophecy Require Import syn_type prophecy.
From lrust.typing Require Import uniq_cmra.
From lrust.lifetime Require Export lifetime_full guarded_bor.
From guarding Require Import guard tactics.
Set Default Proof Using "Type".

(** * The contents of memory as fancy bytes on GMB cells

Phase 4 of [design_docs/guarded-mutable-borrows-plan.md]: the bytes owned by the parent of
a value ([bytes_own] in [typing/own.v]) are the _contents_ [gcont l m fv] of phase 3 (the
exact fancy bytes of the fancy value [fv] at [l], at the MiniRust type [m]):

  [gcont l m fv := ∃ R fbs, gfbytes l fbs ∗ ⌜frepr R m fbs fv ∧ reg_wf R⌝ ∗ gcells l m fv]

- [gfbytes l fbs] owns the plain bytes of [fbs] at their locations ([inr b] at [l +ₗ i]);
  the positions of the cells ([inl _]) are not owned there;
- [gcells l m fv] owns the move right [gmb_a γ (l +ₗ o)] of every cell [FVCell g] embedded
  in [fv] (at its offset [o], following the structure of [m]), with the registry fact
  [gcell_reg g γ m'] that names its instance and type.

The registry of the cells ([gcells_ctx]: a ghost map [g ↦ (γ, m)] with persistent
fragments, and the instance invariants of all cells) is global; its ghost state is part of
[typeG] ([gcellsGS]), and it is allocated at adequacy ([gcells_ctx_alloc]).

The definitions of this file are those of phase 3 ([typing/gmb_cells.v], which has the
moves and the cell laws); they are here because [typeG] and the bytes of the types depend
on them. This file also has the masks of the bytes and ghost layers of the bodies of unique
borrows ([lazyB], [lazyE]), and the layout of the cells of a fancy value ([mcells]), which
the byte-preserving maps of subtyping preserve ([syn_bincl] in [typing/type.v]). *)

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

(** ** Masks

The bodies of unique borrows ([typing/uniq_util.v]) hold the ownership of their contents in
a lazy update with the mask [lazyE] (the _ghost layer_), and the bytes of their contents in
an update with the mask [lazyB] (the _bytes layer_), which can be forced with dead tokens
only. [lazyE] contains [↑gmbN], so that the ghost layer can take the settle lock of a cell;
[lazyB] does not. *)
Definition lazyE : coPset := ↑Nllft ∪ ↑prophN ∪ ↑uniqN ∪ ↑gmbN.

Lemma lazyE_NllftUsr : ↑NllftUsr ∪ ↑NllftUsr2 ⊆ lazyE.
Proof. rewrite /lazyE /NllftUsr /NllftUsr2. solve_ndisj. Qed.

Lemma lazyE_NllftG : ↑NllftG ⊆ lazyE.
Proof. rewrite /lazyE /NllftG. solve_ndisj. Qed.

Definition lazyB : coPset := ↑Nllft ∪ ↑prophN ∪ ↑uniqN.

Lemma lazyB_lazyE : lazyB ⊆ lazyE.
Proof. rewrite /lazyB /lazyE. set_solver. Qed.

Lemma lazyB_Nllft : ↑Nllft ⊆ lazyB.
Proof. rewrite /lazyB. set_solver. Qed.

Lemma lazyB_NllftG : ↑NllftG ⊆ lazyB.
Proof. rewrite /lazyB /NllftG. solve_ndisj. Qed.

Lemma lazyE_gcellsN : lazyE ## ↑gcellsN.
Proof. rewrite /lazyE /gcellsN /gmbN /uniqN /NllftUsr /prophN /Nllft. solve_ndisj. Qed.

Lemma lazyB_gmbN : lazyB ## ↑gmbN.
Proof. rewrite /lazyB /gmbN /uniqN /NllftUsr /prophN /Nllft. solve_ndisj. Qed.

(** ** The layout of the cells of a fancy value

[mcells m fv]: the cells embedded in [fv] at the MiniRust type [m], with their offsets and
their MiniRust types (following the structure of [m], as [gcells]). *)
Definition mshift (o : nat) (cl : list (nat * positive * mty)) : list (nat * positive * mty) :=
  (λ c, ((o + c.1.1)%nat, c.1.2, c.2)) <$> cl.

Fixpoint mcells (m : mty) (fv : FValue) {struct fv} : list (nat * positive * mty) :=
  match fv with
  | FVCell g => [(0%nat, g, m)]
  | FVTuple fvs =>
      match m with
      | MTuple fs _ =>
          (fix go (k : nat) (fvs : list FValue) : list (nat * positive * mty) :=
             match fvs with
             | [] => []
             | fv :: fvs =>
                 match fs !! k with Some (o, fm) => mshift o (mcells fm fv) | None => [] end ++
                 go (S k) fvs
             end) 0%nat fvs
      | _ => []
      end
  | FVVariant t d =>
      match m with
      | MEnum vars tag _ =>
          match vars !! Z.to_nat t with
          | Some vm => mshift (int_size tag) (mcells vm d) | None => []
          end
      | _ => []
      end
  | _ => []
  end.

Lemma mshift_0 cl : mshift 0 cl = cl.
Proof. rewrite /mshift -{2}(list_fmap_id cl). apply list_fmap_ext=> ? [[??]?] _. done. Qed.

Lemma mshift_mshift o o' cl : mshift o (mshift o' cl) = mshift (o + o') cl.
Proof.
  rewrite /mshift -list_fmap_compose. apply list_fmap_ext=> ? [[??]?] _ /=. f_equal. f_equal. lia.
Qed.

Lemma mshift_app o cl1 cl2 : mshift o (cl1 ++ cl2) = mshift o cl1 ++ mshift o cl2.
Proof. by rewrite /mshift fmap_app. Qed.

Lemma mcells_tuple fs sz fvs :
  mcells (MTuple fs sz) (FVTuple fvs) =
  concat (imap (λ k fv, match fs !! k with Some (o, fm) => mshift o (mcells fm fv) | None => [] end) fvs).
Proof.
  assert (∀ k1, (fix go (k : nat) (fvs : list FValue) : list (nat * positive * mty) :=
             match fvs with
             | [] => []
             | fv :: fvs =>
                 match fs !! k with Some (o, fm) => mshift o (mcells fm fv) | None => [] end ++
                 go (S k) fvs
             end) k1 fvs =
    concat (imap (λ k fv, match fs !! (k1 + k)%nat with
      Some (o, fm) => mshift o (mcells fm fv) | None => [] end) fvs)) as Hgo.
  { induction fvs as [|fv fvs IH]; intros k1; simpl; [done|].
    rewrite Nat.add_0_r IH. do 2 f_equal. apply imap_ext=> ? ? _ /=. by rewrite Nat.add_succ_r. }
  exact (Hgo 0%nat).
Qed.

Lemma mcells_enum vars tag sz t d :
  mcells (MEnum vars tag sz) (FVVariant t d) =
  match vars !! Z.to_nat t with Some vm => mshift (int_size tag) (mcells vm d) | None => [] end.
Proof. done. Qed.

Lemma concat_imap_nil {A B} (h : nat → A → list B) (xs : list A) :
  (∀ k x, xs !! k = Some x → h k x = []) → concat (imap h xs) = [].
Proof.
  revert h. induction xs as [|x xs IH]; intros h Hh; [done|]. rewrite imap_cons /= Hh //.
  apply (IH (h ∘ S)). intros k y Hy. by apply (Hh (S k)).
Qed.

Lemma concat_imap_mshift {A} n (h : nat → A → list (nat * positive * mty)) (xs : list A) :
  concat (imap (λ k x, mshift n (h k x)) xs) = mshift n (concat (imap h xs)).
Proof.
  revert h. induction xs as [|x xs IH]; intros h; [done|]. rewrite !imap_cons /= mshift_app.
  f_equal. apply (IH (h ∘ S)).
Qed.

Lemma mcells_lift m v : mcells m (fv_lift v) = [].
Proof.
  revert m. induction v as [z|b|lp|vs IH|t d IH] using Value_ind'; intros m; try done.
  - destruct m as [| | |fs sz|]; try done. rewrite /fv_lift -/fv_lift mcells_tuple.
    apply concat_imap_nil=> k fv Hk. rewrite list_lookup_fmap in Hk.
    destruct (vs !! k) as [vk|] eqn:Hvk; [|done]. simpl in Hk. injection Hk as <-.
    destruct (fs !! k) as [[o fm]|]; [|done]. by rewrite (Forall_lookup_1 _ _ _ _ IH Hvk).
  - destruct m as [| | | |vars tag sz]; try done. rewrite /fv_lift -/fv_lift mcells_enum.
    destruct (vars !! _); [by rewrite IH|done].
Qed.

(** The cells of a tuple laid out in sequence ([seq_tuple]), field by field. *)
Lemma layout_fields_shift o ms : layout_fields o ms = (λ f, ((o + f.1)%nat, f.2)) <$> layout_fields 0 ms.
Proof.
  revert o. induction ms as [|m ms IH]; intros o; [done|]. simpl. f_equal; [by rewrite Nat.add_0_r|].
  rewrite (IH (o + mty_size m)%nat) (IH (0 + mty_size m)%nat).
  change (list_fmap _ _ ?f ?l) with (fmap f l). rewrite -list_fmap_compose.
  apply list_fmap_ext=> ? [??] _ /=. f_equal. lia.
Qed.

Lemma mcells_seq_tuple_cons m ms fv fvs :
  mcells (seq_tuple (m :: ms)) (FVTuple (fv :: fvs)) =
  mcells m fv ++ mshift (mty_size m) (mcells (seq_tuple ms) (FVTuple fvs)).
Proof.
  rewrite /seq_tuple !mcells_tuple imap_cons /= mshift_0. f_equal.
  rewrite -concat_imap_mshift. f_equal. apply imap_ext=> k fvk _.
  rewrite /= layout_fields_shift list_lookup_fmap.
  destruct (layout_fields 0 ms !! k) as [[o fm]|]; simpl; [|done].
  by rewrite mshift_mshift.
Qed.

Lemma mcells_seq_tuple_nil fvs : mcells (seq_tuple []) (FVTuple fvs) = [].
Proof. rewrite /seq_tuple mcells_tuple /=. by apply concat_imap_nil. Qed.

Lemma mcells_seq_enum ms t d :
  mcells (seq_enum ms) (FVVariant t d) =
  match ms !! Z.to_nat t with
  | Some vm => mshift (int_size (enum_tag (length ms))) (mcells vm d) | None => []
  end.
Proof. done. Qed.

Section gcells_defs.
  Context `{!lrustGS Σ, !llft_logicGS Σ, !gcellsGS Σ}.
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
      rewrite list_lookup_fmap in Hk. destruct (vs !! k) as [vk|] eqn:Hvk; [|done].
      simpl in Hk. injection Hk as <-.
      destruct (fs !! k) as [[o fm]|]; [|done]. iApply (Forall_lookup_1 _ _ _ _ IH Hvk).
    - destruct m as [| | | |vars tag sz]; try (by rewrite /=). rewrite /fv_lift -/fv_lift gcells_enum.
      destruct (vars !! _); [iApply IH|done].
  Qed.

  Lemma gcells_lift_iff l m v : gcells l m (fv_lift v) ⊣⊢ True.
  Proof. iSplit; [by iIntros|]. iIntros "_". iApply gcells_lift. Qed.

  (** The cells, as a list ([mcells]). *)
  Definition gcell_at l (c : nat * positive * mty) : iProp Σ :=
    ∃ γ, gcell_reg c.1.2 γ c.2 ∗ gca γ (l +ₗ Z.of_nat c.1.1).

  Lemma gcell_at_shift l o c : gcell_at (l +ₗ Z.of_nat o) c ⊣⊢ gcell_at l ((o + c.1.1)%nat, c.1.2, c.2).
  Proof. rewrite /gcell_at /= shift_loc_assoc_nat. done. Qed.

  Lemma big_sepL_concat_imap {A B} (h : nat → A → list B) (P : B → iProp Σ) (xs : list A) :
    ([∗ list] c ∈ concat (imap h xs), P c) ⊣⊢ [∗ list] k ↦ x ∈ xs, [∗ list] c ∈ h k x, P c.
  Proof.
    revert h. induction xs as [|x xs IH]; intros h; [done|].
    rewrite imap_cons /= big_sepL_app IH. done.
  Qed.

  Lemma gcells_mcells l m fv : gcells l m fv ⊣⊢ [∗ list] c ∈ mcells m fv, gcell_at l c.
  Proof.
    revert l m. induction fv as [z|b|lp|fvs IH|t d IH|g] using FValue_ind'; intros l m.
    1-3: simpl; rewrite ?big_sepL_nil; iSplit; by iIntros.
    - destruct m as [| | |fs sz|]; try (simpl; rewrite ?big_sepL_nil; iSplit; by iIntros).
      rewrite gcells_tuple mcells_tuple big_sepL_concat_imap.
      apply big_sepL_proper=> k fvk Hk. destruct (fs !! k) as [[o fm]|]; [|simpl; rewrite ?big_sepL_nil; iSplit; by iIntros].
      rewrite (Forall_lookup_1 _ _ _ _ IH Hk) /mshift big_sepL_fmap.
      apply big_sepL_proper=> j c _. by rewrite gcell_at_shift.
    - destruct m as [| | | |vars tag sz]; try (simpl; rewrite ?big_sepL_nil; iSplit; by iIntros).
      rewrite gcells_enum mcells_enum.
      destruct (vars !! Z.to_nat t) as [vm|]; [|simpl; rewrite ?big_sepL_nil; iSplit; by iIntros].
      rewrite IH /mshift big_sepL_fmap. apply big_sepL_proper=> j c _. by rewrite gcell_at_shift.
    - rewrite /= /gcell_at /= shift_loc_0 right_id. done.
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

  Lemma gfbytes_app l fbs1 fbs2 :
    gfbytes l (fbs1 ++ fbs2) ⊣⊢ gfbytes l fbs1 ∗ gfbytes (l +ₗ length fbs1) fbs2.
  Proof.
    rewrite /gfbytes big_sepL_app. f_equiv. apply big_sepL_proper=> j fb _.
    by rewrite shift_loc_assoc_nat.
  Qed.

  Lemma heap_mapsto_bytes_pos_shift l (o : nat) bs :
    (l +ₗ o) ↦b bs ⊣⊢ [∗ list] j ↦ b ∈ bs, (l +ₗ (o + j)%nat) ↦b [b].
  Proof. rewrite heap_mapsto_bytes_pos. apply big_sepL_proper=> j b _. by rewrite shift_loc_assoc_nat. Qed.

  Lemma gfbytes_shift l (o : nat) fbs :
    gfbytes (l +ₗ o) fbs ⊣⊢ [∗ list] j ↦ fb ∈ fbs, gfb (l +ₗ (o + j)%nat) fb.
  Proof. apply big_sepL_proper=> j b _. by rewrite shift_loc_assoc_nat. Qed.

  (** ** Values without cells *)
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

  Lemma gcont_lift_iff l m v :
    gcont l m (fv_lift v) ⊣⊢ ∃ bs, l ↦b bs ∗ ⌜decode_value m bs = Some v⌝.
  Proof.
    iSplit; [iApply gcont_lift_bytes|]. iIntros "(%bs & Hbs & %Hd)". by iApply gcont_of_bytes.
  Qed.

  (** ** The cells of the contents are distinct *)

  (** A cell embedded in [fv] (at the structure of [m]) is owned by [gcells]. *)
  Lemma gcells_cell_in R m fbs fv l g :
    frepr R m fbs fv → g ∈ fv_cells fv →
    gcells l m fv -∗ ∃ γ m' (o : nat), gcell_reg g γ m' ∗ gca γ (l +ₗ o).
  Proof.
    intros Hrep. revert l. induction Hrep as [m g' cs Hg'|m bs v Hdec|fs sz fbs fvs Hlen Hlenf Hfs IH Hpad
      |vars tag sz fbs t vm d bst Hlen Htag Ht Ht0 Hvm Hd IH Hpad]; intros l Hg.
    - apply elem_of_list_singleton in Hg as ->. iIntros "(%γ & Hreg & Ha)". iExists γ, m, 0%nat.
      rewrite shift_loc_0_nat. iFrame.
    - rewrite fv_cells_lift in Hg. by apply not_elem_of_nil in Hg.
    - destruct (fv_cells_tuple_inv _ _ Hg) as (k & fvk & Hk & Hgk).
      destruct (fs !! k) as [[o fm]|] eqn:Hf; [|apply lookup_ge_None in Hf; apply lookup_lt_Some in Hk; lia].
      rewrite gcells_tuple. iIntros "H". iDestruct (big_sepL_lookup with "H") as "H"; [done|].
      rewrite Hf. iDestruct (IH k (o, fm) fvk Hf Hk (l +ₗ o) Hgk with "H") as (γ m' o') "[Hreg Ha]".
      iExists γ, m', (o + o')%nat. rewrite shift_loc_assoc_nat. iFrame.
    - rewrite gcells_enum Hvm. iIntros "H".
      iDestruct (IH (l +ₗ int_size tag) Hg with "H") as (γ m' o') "[Hreg Ha]".
      iExists γ, m', (int_size tag + o')%nat. rewrite shift_loc_assoc_nat. iFrame.
  Qed.

  Lemma gcell_reg_agree g γ γ' m m' : gcell_reg g γ m -∗ gcell_reg g γ' m' -∗ ⌜γ = γ' ∧ m = m'⌝.
  Proof. iIntros "H1 H2". by iDestruct (ghost_map_elem_agree with "H1 H2") as %[= -> ->]. Qed.

  (** Two separate contents have no common cell. *)
  Lemma gcells_disj R1 R2 m1 m2 fbs1 fbs2 fv1 fv2 l1 l2 :
    frepr R1 m1 fbs1 fv1 → frepr R2 m2 fbs2 fv2 →
    gcells l1 m1 fv1 -∗ gcells l2 m2 fv2 -∗ ⌜∀ g, g ∈ fv_cells fv1 → g ∉ fv_cells fv2⌝.
  Proof.
    iIntros (H1 H2) "C1 C2 %g %Hg1 %Hg2".
    iDestruct (gcells_cell_in with "C1") as (γ1 m1' o1) "[Hreg1 Ha1]"; [done..|].
    iDestruct (gcells_cell_in with "C2") as (γ2 m2' o2) "[Hreg2 Ha2]"; [done..|].
    iDestruct (gcell_reg_agree with "Hreg1 Hreg2") as %[<- _].
    iApply (gmb_a_excl with "Ha1 Ha2").
  Qed.

  (** ** Contents of products and sums *)

  (** The representation depends only on the registry entries of the cells of the value. *)
  Lemma frepr_restrict R R' m fbs fv :
    frepr R m fbs fv → (∀ g, g ∈ fv_cells fv → R' !! g = R !! g) → frepr R' m fbs fv.
  Proof.
    induction 1 as [m g cs Hg|m bs v Hdec|fs sz fbs fvs Hlen Hlenf Hfs IH Hpad
      |vars tag sz fbs t vm d bst Hlen Htag Ht Ht0 Hvm Hd IH Hpad]; intros HR'.
    - constructor. rewrite HR' //. by left.
    - by constructor.
    - constructor; [done|done| |done]. intros k f fv Hf Hfv. apply (IH k f fv Hf Hfv).
      intros g Hg. apply HR'. by eapply fv_cells_tuple.
    - econstructor; [done|done|done|done|done| |done]. by apply IH.
  Qed.

  (** Two representations with distinct cells have a common registry. *)
  Lemma frepr_union R1 R2 m1 m2 fbs1 fbs2 fv1 fv2 :
    frepr R1 m1 fbs1 fv1 → frepr R2 m2 fbs2 fv2 → reg_wf R1 → reg_wf R2 →
    (∀ g, g ∈ fv_cells fv1 → g ∉ fv_cells fv2) →
    ∃ R, frepr R m1 fbs1 fv1 ∧ frepr R m2 fbs2 fv2 ∧ reg_wf R.
  Proof.
    intros H1 H2 HR1 HR2 Hd.
    set R1' := filter (λ e : positive * (mty * list positive), e.1 ∈ fv_cells fv1) R1.
    exists (R1' ∪ R2). split_and!.
    - eapply frepr_restrict; [done|]. intros g Hg.
      destruct (R1 !! g) as [e|] eqn:He.
      + apply lookup_union_Some_l. by apply map_lookup_filter_Some.
      + rewrite lookup_union_r; [|by apply map_lookup_filter_None; left].
        destruct (frepr_cells_in _ _ _ _ _ H1 Hg) as (? & ? & HR & _). by rewrite He in HR.
    - eapply frepr_restrict; [done|]. intros g Hg.
      rewrite lookup_union_r //. apply map_lookup_filter_None. right. intros e _ Hin.
      by apply (Hd g).
    - intros g m cs [HL|[_ HL]]%lookup_union_Some_raw.
      + apply map_lookup_filter_Some in HL as [HL _]. by eapply HR1.
      + by eapply HR2.
  Qed.

  (** The cells of a tuple laid out in sequence: those of its first field and those of
      the others. *)
  Lemma gcells_seq_tuple_cons l m ms fv fvs :
    gcells l (seq_tuple (m :: ms)) (FVTuple (fv :: fvs)) ⊣⊢
    gcells l m fv ∗ gcells (l +ₗ mty_size m) (seq_tuple ms) (FVTuple fvs).
  Proof.
    rewrite !gcells_mcells mcells_seq_tuple_cons big_sepL_app /mshift big_sepL_fmap.
    f_equiv. apply big_sepL_proper=> k c _. by rewrite gcell_at_shift.
  Qed.

  Lemma gcells_seq_tuple_nil l fvs : gcells l (seq_tuple []) (FVTuple fvs) ⊣⊢ True.
  Proof. rewrite gcells_mcells mcells_seq_tuple_nil big_sepL_nil. by iSplit. Qed.
End gcells_defs.

(** ** Allocation of the registry *)
Lemma gcells_ctx_alloc `{!lrustGS Σ, !llft_logicGS Σ, !gcellsGpreS Σ} E :
  ⊢ |={E}=> ∃ _ : gcellsGS Σ, gcells_ctx.
Proof.
  iMod (ghost_map_alloc_empty (K:=positive) (V:=gmb_name * mty)) as (γr) "Auth".
  set (H := GCellsGS Σ _ _ γr).
  iMod (inv_alloc gcellsN E (@gcells_inv _ _ _ H) with "[Auth]") as "#GC".
  { iNext. iExists ∅. iFrame "Auth". by rewrite big_sepM_empty. }
  iModIntro. iExists H. done.
Qed.
