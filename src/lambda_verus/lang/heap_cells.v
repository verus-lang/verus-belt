Require Import guarding.internal.na_invariants_fork.
From lrust.util Require Import non_atomic_cell_map atomic_lock_counter update.
From lrust.util Require Export cellmap.
From guarding Require Import guard.
From Coq.Arith Require Import PeanoNat.
From stdpp Require Import coPset.
From iris.algebra Require Import big_op gmap frac agree numbers.
From iris.algebra Require Import csum excl auth cmra_big_op.
From iris.algebra.lib Require Import gmap_view.
From iris.bi Require Import fractional.
From iris.base_logic Require Export lib.own.
From iris.proofmode Require Export proofmode.
From iris.base_logic.lib Require Export ghost_map.
From lrust.lang Require Export fvalue.
From lrust.lang Require Export lang.
From lrust.lang Require Export heap.
From iris.prelude Require Import options.
Import uPred.

(** * Cell groups of the byte region

The lemmas about the cell groups of [heap.v] (see the comment on cell groups there, and
[design_docs/pcell-multibyte-cells.md]):
- the compositionality lemma in the byte context ([cells_decode]);
- creating and destroying a group ([bytes_ctx_pcell_create], [bytes_ctx_pcell_destroy]);
- untethering and retethering a group ([bytes_ctx_pcell_untether],
  [bytes_ctx_pcell_retether]), for moves;
- accesses through cells: reads ([bytes_ctx_cell_read_begin_guarded]) and two-phase writes
  ([bytes_ctx_cell_write_begin], [bytes_ctx_cell_write_end]) of a plain sub-value of a group,
  which may be nested in a live group;
- nestings ([bytes_ctx_gnest]). *)

Section cells.
  Context `{!heapGS Σ}.
  Context `{!invGS Σ}.
  Implicit Types 𝛼 : bfull.
  Implicit Types (R : gmap positive (mty * list positive)) (ρ : gmap positive FValue).
  Implicit Types (NS : gmap (positive * positive * nat) ()).

  Global Instance greg_persistent g m cs : Persistent (greg g m cs).
  Proof. apply _. Qed.
  Global Instance gnocell_persistent g : Persistent (gnocell g).
  Proof. apply _. Qed.
  Global Instance gdyn_timeless g fv : Timeless (gdyn g fv).
  Proof. apply _. Qed.
  Global Instance bcells_timeless cs fbs : Timeless (bcells cs fbs).
  Proof. apply _. Qed.
  Global Instance loc_side_timeless l g m cs : Timeless (loc_side l g m cs).
  Proof. apply _. Qed.
  Global Instance brepr_persistent m fbs fv : Persistent (brepr m fbs fv).
  Proof. apply _. Qed.
  Global Instance heap_mapsto_fbytes_timeless l fbs : Timeless (heap_mapsto_fbytes l fbs).
  Proof. apply _. Qed.
  Global Instance gnest_persistent g0 g o : Persistent (gnest g0 g o).
  Proof. apply _. Qed.
  Global Instance gpath_persistent g0 g o : Persistent (gpath g0 g o).
  Proof. apply _. Qed.

  Lemma greg_agree g m cs m' cs' : greg g m cs -∗ greg g m' cs' -∗ ⌜m = m' ∧ cs = cs'⌝.
  Proof. iIntros "A B". by iDestruct (ghost_map_elem_agree with "A B") as %[= -> ->]. Qed.

  Lemma gdyn_excl g fv fv' : gdyn g fv -∗ gdyn g fv' -∗ False.
  Proof. iIntros "A B". by iDestruct (ghost_map_elem_ne with "A B") as %?. Qed.

  Lemma greg_lookup R g m cs :
    ghost_map_auth heap_greg_name 1 R -∗ greg g m cs -∗ ⌜R !! g = Some (m, cs)⌝.
  Proof. iIntros "A B". iApply (ghost_map_lookup with "A B"). Qed.
  Lemma gdyn_lookup ρ g fv :
    ghost_map_auth heap_gdyn_name 1 ρ -∗ gdyn g fv -∗ ⌜ρ !! g = Some fv⌝.
  Proof. iIntros "A B". iApply (ghost_map_lookup with "A B"). Qed.
  Lemma gnocell_lookup (NC : gmap positive ()) g :
    ghost_map_auth heap_gnc_name 1 NC -∗ gnocell g -∗ ⌜g ∈ dom NC⌝.
  Proof.
    iIntros "A B". iDestruct (ghost_map_lookup with "A B") as %Hg. iPureIntro.
    by apply elem_of_dom_2 in Hg.
  Qed.

  Lemma gnest_lookup NS g0 g o :
    ghost_map_auth heap_gnest_name 1 NS -∗ gnest g0 g o -∗ ⌜NS !! (g0, g, o) = Some tt⌝.
  Proof. iIntros "A B". iApply (ghost_map_lookup with "A B"). Qed.

  Lemma nest_path_mono NS NS' g0 g o : NS ⊆ NS' → nest_path NS g0 g o → nest_path NS' g0 g o.
  Proof.
    intros Hsub. induction 1 as [|g0 g1 o1 g o Hk Hp IH]; [constructor|].
    econstructor; [|done]. by eapply lookup_weaken.
  Qed.

  Lemma gpath_lookup NS g0 g o :
    ghost_map_auth heap_gnest_name 1 NS -∗ gpath g0 g o -∗ ⌜nest_path NS g0 g o⌝.
  Proof.
    iIntros "A (%NS' & %Hp & #HNS')". iAssert ⌜NS' ⊆ NS⌝%I as %Hsub.
    { iIntros (k). destruct (NS' !! k) as [[]|] eqn:Hk; [|by destruct (NS !! k)].
      iDestruct (big_sepM_lookup with "HNS'") as "H"; [done|].
      destruct k as [[k1 k2] k3]. iDestruct (gnest_lookup with "A H") as %Hk'.
      simpl in Hk'. by rewrite Hk'. }
    iPureIntro. by eapply nest_path_mono.
  Qed.

  (** A group sits at the offset [0] inside itself, and nestings compose. *)
  Lemma gpath_refl g : ⊢ gpath g g 0.
  Proof. iExists ∅. rewrite big_sepM_empty. iPureIntro. split; [constructor|done]. Qed.

  Lemma gpath_nest g0 g1 o1 g o : gnest g0 g1 o1 -∗ gpath g1 g o -∗ gpath g0 g (o1 + o).
  Proof.
    iIntros "#Hn (%NS & %Hp & #HNS)". destruct (NS !! (g0, g1, o1)) as [[]|] eqn:Hk.
    - iExists NS. iFrame "HNS". iPureIntro. by econstructor.
    - iExists (<[(g0, g1, o1) := ()]> NS). rewrite big_sepM_insert //. iFrame "Hn HNS".
      iPureIntro. econstructor; [apply lookup_insert|]. eapply nest_path_mono; [|done].
      by apply insert_subseteq.
  Qed.

  Lemma brepr_frepr R m fbs fv :
    ghost_map_auth heap_greg_name 1 R -∗ brepr m fbs fv -∗ ⌜frepr R m fbs fv⌝.
  Proof.
    iIntros "A (%R' & %Hrep & #HR')". iAssert ⌜R' ⊆ R⌝%I as %Hsub.
    { iIntros (g). destruct (R' !! g) as [[m' cs']|] eqn:Hg; [|by destruct (R !! g)].
      iDestruct (big_sepM_lookup with "HR'") as "H"; [done|].
      iDestruct (greg_lookup with "A H") as %->. done. }
    iPureIntro. by eapply frepr_mono.
  Qed.

  (** The facts that the authority knows about owned edges. *)
  Lemma bheap_edges 𝛼 (l : loc) (cvs : list (positive + bval)) :
    bheap 𝛼 -∗ ([∗ list] i ↦ cv ∈ cvs, bpt (inl (l +ₗ i)) cv) -∗
    ⌜∀ (i : nat) cv, cvs !! i = Some cv → 𝛼_fine_pair loc positive bval 𝛼 (inl (l +ₗ i)) cv⌝.
  Proof.
    iIntros "H● Hcvs". iApply pure_forall_2. iIntros (i). iApply pure_forall_2.
    iIntros (cv). destruct (cvs !! i) as [cv'|] eqn:Hi; [|by iPureIntro].
    iDestruct (big_sepL_lookup with "Hcvs") as "Hcv"; [done|].
    iDestruct (fheap_fpt with "H● Hcv") as %Hp. iPureIntro. by intros [= <-].
  Qed.

  Lemma bheap_cells 𝛼 cs fbs :
    bheap 𝛼 -∗ bcells cs fbs -∗
    ⌜length cs = length fbs ∧ ∀ (i : nat) c fb, cs !! i = Some c → fbs !! i = Some fb →
       𝛼_fine_pair loc positive bval 𝛼 (inr c) fb⌝.
  Proof.
    iIntros "H● Hcs". iDestruct (big_sepL2_length with "Hcs") as %Hlen.
    iAssert ⌜∀ (i : nat) c fb, cs !! i = Some c → fbs !! i = Some fb →
       𝛼_fine_pair loc positive bval 𝛼 (inr c) fb⌝%I with "[-]" as %H; [|done].
    iApply pure_forall_2. iIntros (i). iApply pure_forall_2. iIntros (c).
    iApply pure_forall_2. iIntros (fb).
    destruct (cs !! i) as [c'|] eqn:Hc, (fbs !! i) as [fb'|] eqn:Hfb; try by iPureIntro.
    iDestruct (big_sepL2_lookup with "Hcs") as "Hc"; [done..|].
    iDestruct (fheap_fpt with "H● Hc") as %Hp. iPureIntro. by intros [= <-] [= <-].
  Qed.

  (** The location side of a group gives the starts of its rows. *)
  Lemma loc_side_rows 𝛼 l g m cs :
    bheap 𝛼 -∗ loc_side l g m cs -∗
    ⌜∀ (i : nat) c, cs !! i = Some c → ∃ rest v, 𝛼 !! inl (l +ₗ i) = Some (c :: rest, v)⌝.
  Proof.
    iIntros "H● [_ Hcs]".
    iDestruct (bheap_edges _ _ (inl <$> cs) with "H● [Hcs]") as %H.
    { by rewrite big_sepL_fmap. }
    iPureIntro. intros i c Hc. move: (H i (inl c)). rewrite list_lookup_fmap Hc /=.
    intros Hp. specialize (Hp eq_refl). rewrite /𝛼_fine_pair in Hp.
    destruct (𝛼 !! inl (l +ₗ i)) as [[[|c' rest] v]|]; try done. subst. eauto.
  Qed.


  (** ** D3 and the compositionality lemma *)

  (** The final byte of a byte-cell: the byte of the value of its row. *)
  Definition cell_final 𝛼 (c : positive) : abyte :=
    match row_of loc positive bval 𝛼 c with Some (_, (_, b)) => b | None => Uninit end.

  (** The contents of cells give their final bytes. *)
  Lemma bcells_final 𝛼 cs fbs :
    bheap 𝛼 -∗ bcells cs fbs -∗
    ⌜cell_final 𝛼 <$> cs = fin_bytes (cell_final 𝛼) (fb_strip <$> fbs)⌝.
  Proof.
    iIntros "H● Hcs". iDestruct (fheap_no_dupes with "H●") as %Hnd.
    iInduction cs as [|c cs] "IH" forall (fbs); destruct fbs as [|fb fbs];
      rewrite /bcells /=; try by iDestruct "Hcs" as "[]".
    { done. }
    iDestruct "Hcs" as "[Hc Hcs]". iDestruct ("IH" with "H● Hcs") as %Hrest.
    iDestruct (fheap_fpt with "H● Hc") as %Hp. iPureIntro. rewrite /fin_bytes /= in Hrest |- *.
    f_equal; [|done]. rewrite /𝛼_fine_pair in Hp. destruct fb as [c2|[ls b]]; simpl.
    - destruct Hp as (k & cs' & v & Hk & Hpair).
      apply list_has_pair_elem_of in Hpair as [Hc Hc2].
      rewrite /cell_final. erewrite row_of_spec; [|done..]. erewrite row_of_spec; [|done..].
      done.
    - destruct Hp as (k & cs' & Hk & Hend). apply list_ends_with_elem_of in Hend.
      rewrite /cell_final. erewrite row_of_spec; [|done..]. done.
  Qed.

  Lemma gcontents_facts 𝛼 R NS CW ρ :
    bheap 𝛼 -∗ ([∗ map] g ↦ fv ∈ ρ, gcontents R NS CW g fv) -∗
    ⌜map_Forall (λ g fv, ∃ m cs fbs, R !! g = Some (m, cs) ∧ frepr R m fbs fv ∧
       cell_final 𝛼 <$> cs = fin_bytes (cell_final 𝛼) fbs) ρ⌝.
  Proof.
    iIntros "H● Hρ". iInduction ρ as [|g fv ρ Hg] "IH" using map_ind.
    { iPureIntro. apply map_Forall_empty. }
    rewrite big_sepM_insert //.
    iDestruct "Hρ" as "[(%m & %cs & %fbs & (%HR & %Hrep & _) & Hcs) Hρ]".
    iDestruct (bcells_final with "H● Hcs") as %Hfin.
    iDestruct ("IH" with "H● Hρ") as %Hrest. iPureIntro.
    apply map_Forall_insert; [done|]. split; [|done]. eauto 10.
  Qed.

  (** The compositionality lemma in the byte context: the final bytes of every live group
      decode to the erasure of its fancy value. *)
  Lemma cells_decode 𝛼 R NS CW ρ NC :
    bheap 𝛼 -∗ ([∗ map] g ↦ fv ∈ ρ, gcontents R NS CW g fv) -∗ ⌜cells_wf R ρ NC NS CW⌝ -∗
    ⌜∀ g fv m cs, ρ !! g = Some fv → R !! g = Some (m, cs) →
       ∃ v, fval_erase ρ fv v ∧ decode_value m (cell_final 𝛼 <$> cs) = Some v⌝.
  Proof.
    iIntros "H● Hρ %Hwf". iDestruct (gcontents_facts with "H● Hρ") as %Hf. iPureIntro.
    intros g fv m cs Hg HR. eapply (registry_decode R ρ (cell_final 𝛼) (λ _, True)); [|done..].
    intros g' fv' Hg' _. destruct (Hf g' fv' Hg') as (m' & cs' & fbs & HR' & Hrep & Hfin).
    exists m', cs', fbs. split_and!; [done..|]. intros g'' Hg''.
    destruct Hwf as (_ & _ & Hlt & _). destruct (Hlt g' fv' Hg' g'' Hg''). done.
  Qed.

  (** ** Helpers *)
  Lemma inl_loc_inj {B} (a b : loc) : (inl a : loc + B) = inl b → a = b.
  Proof. intros H. by inversion H. Qed.

  Lemma fb_strip_rst (fbs : list (positive + abyte)) : fb_strip <$> (fb_rst <$> fbs) = fbs.
  Proof. induction fbs as [|fb fbs IH]; [done|]. rewrite !fmap_cons IH. by destruct fb. Qed.

  Lemma gcontents_mono_R R R' NS CW g fv :
    R ⊆ R' → gcontents R NS CW g fv -∗ gcontents R' NS CW g fv.
  Proof.
    iIntros (Hsub) "(%m & %cs & %fbs & (%HR & %Hrep & %Hls & %Hns) & Hcs)". iExists m, cs, fbs. iFrame.
    iPureIntro. split_and!; [by eapply lookup_weaken|by eapply frepr_mono|done|].
    intros g' o Hg'. destruct (Hns g' o Hg') as (m' & cs' & HR' & Hsl).
    exists m', cs'. split; [by eapply lookup_weaken|done].
  Qed.

  Lemma heap_mapsto_fbytes_bytes l bs : l ↦b bs ⊣⊢ heap_mapsto_fbytes l (inr <$> bs).
  Proof.
    rewrite heap_mapsto_bytes_eq /heap_mapsto_bytes_def /heap_mapsto_st_vec
      /heap_mapsto_fbytes big_sepL_fmap. done.
  Qed.

  Lemma heap_mapsto_fbytes_cons l fb fbs :
    heap_mapsto_fbytes l (fb :: fbs) ⊣⊢
    bpt (inl l) (fb_rst fb) ∗ heap_mapsto_fbytes (l +ₗ 1) fbs.
  Proof.
    rewrite /heap_mapsto_fbytes big_sepL_cons shift_loc_0_nat. f_equiv.
    apply big_sepL_proper. intros i fb' _. by rewrite shift_loc_S.
  Qed.

  Lemma heap_mapsto_fbytes_app l fbs1 fbs2 :
    heap_mapsto_fbytes l (fbs1 ++ fbs2) ⊣⊢
    heap_mapsto_fbytes l fbs1 ∗ heap_mapsto_fbytes (l +ₗ length fbs1) fbs2.
  Proof.
    rewrite /heap_mapsto_fbytes big_sepL_app. f_equiv.
    apply big_sepL_proper. intros i fb _. by rewrite shift_loc_assoc_nat.
  Qed.

  (** Fresh group ids, larger than every registered one. *)
  Definition fresh_gid (R : gmap positive (mty * list positive)) : positive :=
    Pos.succ (foldr Pos.max 1%positive (elements (dom R))).

  Lemma fresh_gid_gt R g : g ∈ dom R → (g < fresh_gid R)%positive.
  Proof.
    rewrite /fresh_gid -elem_of_elements. generalize (elements (dom R)). intros gs Hg.
    cut (g ≤ foldr Pos.max 1 gs)%positive; [lia|].
    induction gs as [|g' gs IH]; [by apply not_elem_of_nil in Hg|].
    apply elem_of_cons in Hg as [->|Hg]; simpl; [lia|]. specialize (IH Hg). lia.
  Qed.

  Lemma fresh_gid_fresh R : R !! fresh_gid R = None.
  Proof.
    destruct (R !! fresh_gid R) eqn:Hg; [|done]. exfalso.
    have Hd : fresh_gid R ∈ dom R by apply elem_of_dom; eauto.
    have Hlt := fresh_gid_gt R _ Hd. exact (Pos.lt_irrefl _ Hlt).
  Qed.

  (** All the byte-cells of the registry. *)
  Definition reg_cells (R : gmap positive (mty * list positive)) : list positive :=
    mjoin ((λ kv : positive * (mty * list positive), kv.2.2) <$> map_to_list R).

  Lemma reg_cells_in R g m cs c : R !! g = Some (m, cs) → c ∈ cs → c ∈ reg_cells R.
  Proof.
    intros Hg Hc. rewrite /reg_cells elem_of_list_join. exists cs. split; [done|].
    apply elem_of_list_fmap. exists (g, (m, cs)). split; [done|]. by apply elem_of_map_to_list.
  Qed.

  (** ** The rows of nested groups *)

  (** The facts that the authority knows about the contents of all live groups. *)
  Definition gfacts 𝛼 R NS (CW : gmap positive cwkey) ρ : Prop :=
    map_Forall (λ g fv, ∃ m cs fbs, gc_pure R NS CW g fv m cs fbs ∧ length cs = length fbs ∧
      ∀ (i : nat) c fb, cs !! i = Some c → fbs !! i = Some fb →
        𝛼_fine_pair loc positive bval 𝛼 (inr c) fb) ρ.

  Lemma gcontents_edges 𝛼 R NS CW ρ :
    bheap 𝛼 -∗ ([∗ map] g ↦ fv ∈ ρ, gcontents R NS CW g fv) -∗ ⌜gfacts 𝛼 R NS CW ρ⌝.
  Proof.
    iIntros "H● Hρ". iInduction ρ as [|g fv ρ Hg] "IH" using map_ind.
    { iPureIntro. apply map_Forall_empty. }
    rewrite big_sepM_insert //.
    iDestruct "Hρ" as "[(%m & %cs & %fbs & %Hgc & Hcs) Hρ]".
    iDestruct (bheap_cells with "H● Hcs") as %[Hlen Hfp].
    iDestruct ("IH" with "H● Hρ") as %Hrest. iPureIntro.
    apply map_Forall_insert; [done|]. split; [|done]. exists m, cs, fbs. done.
  Qed.

  (** A byte-cell in a row belongs to a live group. *)
  Lemma cell_live 𝛼 R ρ (CW : gmap positive cwkey) k cells v c g m cs :
    cells_live 𝛼 R ρ CW →
    (∀ g1 g2 m1 cs1 m2 cs2, g1 ≠ g2 → R !! g1 = Some (m1, cs1) → R !! g2 = Some (m2, cs2) →
       cs1 ## cs2) →
    𝛼 !! k = Some (cells, v) → c ∈ cells → R !! g = Some (m, cs) → c ∈ cs → g ∈ dom ρ.
  Proof.
    intros [Hlive1 _] Hdisj Hk Hc HRg Hcs.
    destruct (Hlive1 _ _ _ c Hk Hc) as (g' & m' & cs' & Hg' & HR' & Hc').
    destruct (decide (g' = g)) as [->|Hne]; [done|]. exfalso.
    by apply (Hdisj _ _ _ _ _ _ Hne HR' HRg c).
  Qed.

  Lemma row_has_same 𝛼 l k cells v c :
    cells_no_dupes loc positive bval 𝛼 → row_has 𝛼 l c → 𝛼 !! k = Some (cells, v) → c ∈ cells →
    k = inl l.
  Proof.
    intros Hnd (cells' & v' & Hl & Hc') Hk Hc. destruct (decide (k = inl l)) as [|Hne]; [done|].
    exfalso. by apply (rows_disjoint loc positive bval 𝛼 k (inl l) cells v cells' v' c).
  Qed.

  (** The last byte-cell of a row points to its value. *)
  Lemma row_has_end 𝛼 l c v :
    cells_no_dupes loc positive bval 𝛼 → row_has 𝛼 l c →
    𝛼_fine_pair loc positive bval 𝛼 (inr c) (inr v) → ∃ pre, 𝛼 !! inl l = Some (pre ++ [c], v).
  Proof.
    intros Hnd Hrow (lu & cs & Hlu & Hend).
    have Hc := Hend. apply list_ends_with_elem_of in Hc.
    have Heq := row_has_same _ _ _ _ _ _ Hnd Hrow Hlu Hc. subst lu.
    apply list_ends_with_snoc in Hend as [pre ->]. eauto.
  Qed.

  (** The byte-cell [c'] that follows a byte-cell [c] is in the same row. *)
  Lemma row_has_next 𝛼 l c c' :
    cells_no_dupes loc positive bval 𝛼 → row_has 𝛼 l c →
    𝛼_fine_pair loc positive bval 𝛼 (inr c) (inl c') → row_has 𝛼 l c'.
  Proof.
    intros Hnd Hrow (lu & cs & v & Hlu & Hpair).
    apply list_has_pair_elem_of in Hpair as [Hc Hc'].
    have Heq := row_has_same _ _ _ _ _ _ Hnd Hrow Hlu Hc. subst lu. by exists cs, v.
  Qed.

  Lemma list_slice_lookup_eq {A} o n (l l' : list A) j x :
    list_slice o n l = l' → l' !! j = Some x → l !! (o + j)%nat = Some x.
  Proof. intros <- Hj. rewrite lookup_list_slice in Hj. by case_decide. Qed.

  Lemma length_list_slice {A} o n (l : list A) :
    length (list_slice o n l) = (n `min` (length l - o))%nat.
  Proof. by rewrite /list_slice length_take length_drop. Qed.

  (** The rows of the byte-cells of a group nested in a live group [g0] are those of the
      byte-cells of [g0] at the same positions. *)
  Lemma nest_path_rows 𝛼 R ρ NC NS (CW : gmap positive cwkey) g0 g o :
    cells_no_dupes loc positive bval 𝛼 → cells_wf R ρ NC NS CW → cells_live 𝛼 R ρ CW →
    gfacts 𝛼 R NS CW ρ → nest_path NS g0 g o → g0 ∈ dom ρ →
    ∀ m0 cs0 m cs, R !! g0 = Some (m0, cs0) → R !! g = Some (m, cs) →
    g ∈ dom ρ ∧ (o + length cs ≤ length cs0)%nat ∧
    ∀ (i : nat) c0 c l', cs0 !! (o + i)%nat = Some c0 → cs !! i = Some c →
      row_has 𝛼 l' c0 → row_has 𝛼 l' c.
  Proof.
    intros Hnd Hwf Hlive Hf. have Hwf' := Hwf.
    destruct Hwf' as (HRwf & HdomR & Hrefs & Hdisj & Hpos & HdomNC & HNC & HCW & Hmwf & HNSd).
    induction 1 as [g|g0 g1 o1 g o Hk Hp IH]; intros Hg0 m0 cs0 m cs HR0 HR.
    { rewrite HR0 in HR. injection HR as <- <-. split; [done|]. split; [lia|].
      intros i c0 c l' Hc0 Hc. simpl in Hc0. rewrite Hc0 in Hc. by injection Hc as ->. }
    apply elem_of_dom in Hg0 as [fv0 Hfv0].
    destruct (Hf g0 fv0 Hfv0) as (m0' & cs0' & fbs0 & (HR0' & _ & _ & Hns) & Hlen0 & Hfp0).
    rewrite HR0 in HR0'. injection HR0' as <- <-.
    destruct (Hns g1 o1) as (m1 & cs1 & HR1 & Hsl); [by apply elem_of_dom_2 in Hk|].
    have Hlen1 := HRwf _ _ _ HR1. have Hpos1 := Hpos _ _ _ HR1.
    have Hb1 : (o1 + length cs1 ≤ length cs0)%nat.
    { have := f_equal length Hsl. rewrite length_list_slice length_fmap length_fmap. lia. }
    (* The contents of [g0] at [o1 + j] point to the byte-cells of [g1]. *)
    have Hnext : ∀ (j : nat) c0 c1, cs0 !! (o1 + j)%nat = Some c0 → cs1 !! j = Some c1 →
      𝛼_fine_pair loc positive bval 𝛼 (inr c0) (inl c1).
    { intros j c0 c1 Hc0 Hc1.
      have Hx : (fb_strip <$> fbs0) !! (o1 + j)%nat = Some (inl c1).
      { eapply list_slice_lookup_eq; [exact Hsl|]. by rewrite list_lookup_fmap Hc1. }
      rewrite list_lookup_fmap in Hx.
      destruct (fbs0 !! (o1 + j)%nat) as [fb|] eqn:Hfb; [|done].
      destruct fb as [c'|[??]]; simpl in Hx; [|done]. injection Hx as ->.
      by apply Hfp0 with (o1 + j)%nat. }
    have Hg1 : g1 ∈ dom ρ.
    { destruct cs1 as [|c1 cs1']; [simpl in *; lia|].
      destruct (lookup_lt_is_Some_2 cs0 (o1 + 0)%nat) as [c0 Hc0]; [simpl in *; lia|].
      destruct (Hnext 0%nat c0 c1 Hc0 eq_refl) as (lu & cells & v & Hlu & Hpair).
      apply list_has_pair_elem_of in Hpair as [_ Hc1].
      eapply cell_live; [done|done|exact Hlu|exact Hc1|exact HR1|set_solver]. }
    destruct (IH Hg1 m1 cs1 m cs HR1 HR) as (Hg & Hb & Hrows).
    split; [done|]. split; [lia|].
    intros i c0 c l' Hc0 Hc Hrow0.
    destruct (lookup_lt_is_Some_2 cs1 (o + i)%nat) as [c1 Hc1].
    { apply lookup_lt_Some in Hc. lia. }
    apply (Hrows i c1 c l' Hc1 Hc). eapply row_has_next; [done|exact Hrow0|].
    apply (Hnext (o + i)%nat); [|done]. by rewrite Nat.add_assoc.
  Qed.

  (** The rows of a plain sub-value of a group [g], nested at [o] inside the group [g0]
      whose byte-cells head the rows of the locations [l0], [l0 +ₗ 1], ...: they end with
      the plain contents of [g]. *)
  Lemma sub_rows 𝛼 R ρ NC NS (CW : gmap positive cwkey) l0 g0 m0 cs0 g o m cs fv o' m' fvs :
    cells_no_dupes loc positive bval 𝛼 → cells_wf R ρ NC NS CW → cells_live 𝛼 R ρ CW →
    gfacts 𝛼 R NS CW ρ →
    R !! g0 = Some (m0, cs0) → (∀ (i : nat) c, cs0 !! i = Some c → row_has 𝛼 (l0 +ₗ i) c) →
    nest_path NS g0 g o → R !! g = Some (m, cs) → ρ !! g = Some fv →
    fv_sub m fv o' m' fvs → fv_cells fvs = [] →
    ∃ fbs bs v, gc_pure R NS CW g fv m cs fbs ∧ length cs = length fbs ∧
      (∀ (i : nat) c fb, cs !! i = Some c → fbs !! i = Some fb →
         𝛼_fine_pair loc positive bval 𝛼 (inr c) fb) ∧
      (o + length cs ≤ length cs0)%nat ∧ (o' + mty_size m' ≤ length cs)%nat ∧
      list_slice o' (mty_size m') (fb_strip <$> fbs) = inr <$> bs ∧
      decode_value m' bs = Some v ∧ fvs = fv_lift v ∧
      (∀ (i : nat) c, cs !! i = Some c → row_has 𝛼 (l0 +ₗ (o + i)%nat) c) ∧
      ∀ (j : nat) c, (j < mty_size m')%nat → cs !! (o' + j)%nat = Some c →
        ∃ ls b pre, fbs !! (o' + j)%nat = Some (inr (ls, b)) ∧ bs !! j = Some b ∧
          𝛼 !! inl (l0 +ₗ (o + o' + j)%nat) = Some (pre ++ [c], (ls, b)).
  Proof.
    intros Hnd Hwf Hlive Hf HR0 Hheads Hp HR Hfv Hsub Hc. have Hwf' := Hwf.
    destruct Hwf' as (HRwf & HdomR & Hrefs & Hdisj & Hpos & HdomNC & HNC & HCW & Hmwf & HNSd).
    have Hg0 : g0 ∈ dom ρ.
    { have Hlen0 := HRwf _ _ _ HR0. have Hpos0 := Hpos _ _ _ HR0.
      destruct cs0 as [|c0 cs0']; [simpl in *; lia|].
      destruct (Hheads 0%nat c0 eq_refl) as (cells & v & Hk & Hc0).
      eapply cell_live; [done|done|exact Hk|exact Hc0|exact HR0|set_solver]. }
    destruct (nest_path_rows _ _ _ _ _ _ _ _ _ Hnd Hwf Hlive Hf Hp Hg0 _ _ _ _ HR0 HR)
      as (_ & Hb & Hrows).
    destruct (Hf g fv Hfv) as (m1 & cs1 & fbs & Hgc & Hlen & Hfp).
    have Hgc' := Hgc. destruct Hgc' as (HR1 & Hrep & Hls & Hns). rewrite HR in HR1.
    injection HR1 as <- <-.
    have Hmw := Hmwf _ _ _ HR.
    have Hb' := fv_sub_bound _ _ _ _ _ Hsub Hmw.
    destruct (frepr_sub_plain _ _ _ _ _ _ _ HRwf Hrep Hsub Hmw Hc) as (bs & v & Hsl & Hd & ->).
    have Hlenm := HRwf _ _ _ HR.
    have Hcsrows : ∀ (i : nat) c, cs !! i = Some c → row_has 𝛼 (l0 +ₗ (o + i)%nat) c.
    { intros i c Hci. destruct (lookup_lt_is_Some_2 cs0 (o + i)%nat) as [c0 Hc0].
      { apply lookup_lt_Some in Hci. lia. }
      apply (Hrows i c0 c _ Hc0 Hci). by apply Hheads. }
    exists fbs, bs, v. split_and!; try done; [lia|].
    intros j c Hj Hcj.
    have Hlenbs : length bs = mty_size m' by eapply decode_value_length.
    destruct (lookup_lt_is_Some_2 bs j) as [b Hbj]; [lia|].
    have Hx : (fb_strip <$> fbs) !! (o' + j)%nat = Some (inr b).
    { eapply list_slice_lookup_eq; [exact Hsl|]. by rewrite list_lookup_fmap Hbj. }
    rewrite list_lookup_fmap in Hx.
    destruct (fbs !! (o' + j)%nat) as [fb|] eqn:Hfb; [|done].
    destruct fb as [c'|[ls b']]; simpl in Hx; [done|]. injection Hx as ->.
    destruct (row_has_end 𝛼 (l0 +ₗ (o + (o' + j))%nat) c (ls, b)) as [pre Hrow].
    { done. } { by apply Hcsrows. } { by apply (Hfp (o' + j)%nat). }
    exists ls, b, pre. split_and!; [done|done|]. by rewrite -Nat.add_assoc.
  Qed.

  (** Inserting fresh byte-cells at the front of the rows of [n] locations. *)
  Lemma bheap_insert_fronts 𝛼 l fbs (X : list positive) :
    bheap 𝛼 -∗ heap_mapsto_fbytes l fbs ==∗ ∃ 𝛼' cs,
      ⌜length cs = length fbs ∧ NoDup cs ∧ (∀ c, c ∈ cs → c ∉ X) ∧ bphi 𝛼' = bphi 𝛼 ∧
       (∀ k cs' v c, 𝛼' !! k = Some (cs', v) → c ∈ cs' →
          c ∈ cs ∨ ∃ cs'', 𝛼 !! k = Some (cs'', v) ∧ c ∈ cs'') ∧
       (∀ k, (∀ i : nat, (i < length fbs)%nat → k ≠ inl (l +ₗ i)) → 𝛼' !! k = 𝛼 !! k)⌝ ∗
      bheap 𝛼' ∗ ([∗ list] i ↦ c ∈ cs, bpt (inl (l +ₗ i)) (inl c)) ∗
      bcells cs (fb_rst <$> fbs).
  Proof.
    iInduction fbs as [|fb fbs] "IH" forall (𝛼 l X); iIntros "H● Hfbs".
    { iModIntro. iExists 𝛼, []. iFrame. rewrite /bcells /=. iSplit; [|done]. iPureIntro.
      split_and!; try done.
      - apply NoDup_nil_2.
      - intros c Hc. by apply not_elem_of_nil in Hc.
      - intros k cs' v c Hk Hc. right. eauto. }
    rewrite heap_mapsto_fbytes_cons. iDestruct "Hfbs" as "[Hfb Hfbs]".
    iDestruct (fheap_fpt with "H● Hfb") as %Hp0.
    assert (∃ cs0 v0, 𝛼 !! inl l = Some (cs0, v0)) as (cs0 & v0 & Hl0).
    { rewrite /𝛼_fine_pair in Hp0. destruct (fb_rst fb) as [c|v];
        destruct (𝛼 !! inl l) as [[[|??]?]|]; naive_solver. }
    iMod (fcmap_insert_front loc positive bval _ _ _ _ _ _ X with "H● Hfb") as (c) "([%Hc %HcX] & H● & Hl & Hc)"; [done|].
    iMod ("IH" $! _ _ (c :: X) with "H● Hfbs")
      as (𝛼' cs) "([%Hlen [%Hnd [%HX [%Hphi [%Hrows %Hsame]]]]] & H● & Hls & Hcs)".
    iModIntro. iExists 𝛼', (c :: cs). rewrite /bcells ?fmap_cons big_sepL2_cons.
    iFrame "H● Hc Hcs". iSplit; last first.
    { rewrite big_sepL_cons shift_loc_0_nat. iFrame "Hl".
      iApply (big_sepL_impl with "Hls"). iIntros "!>" (i c' _) "H". by rewrite shift_loc_S. }
    iPureIntro. split_and!.
    - by rewrite /= Hlen.
    - constructor; [|done]. intros Hin. apply (HX c Hin). by left.
    - intros c' [->|Hin]%elem_of_cons; [done|]. intros HX'. apply (HX c' Hin). by right.
    - by rewrite Hphi phi_insert_loc insert_id // phi_lookup Hl0.
    - intros k cs' v c' Hk Hc'. destruct (Hrows k cs' v c' Hk Hc') as [?|(cs'' & Hk' & Hc'')].
      { left. by right. }
      destruct (decide (k = inl l)) as [->|Hne].
      + rewrite lookup_insert in Hk'. simplify_eq.
        apply elem_of_cons in Hc'' as [->|Hc'']; [by left; left|]. right. eauto.
      + rewrite lookup_insert_ne // in Hk'. right. eauto.
    - intros k Hk. rewrite Hsame.
      + rewrite lookup_insert_ne //. intros Heq. apply (Hk 0%nat); [simpl; lia|].
        by rewrite shift_loc_0_nat Heq.
      + intros i Hi. rewrite -shift_loc_S. apply (Hk (S i)). simpl. lia.
  Qed.

  (** An owned edge from a location in the range of a group with a write in flight gives a
      contradiction. *)
  Lemma cwentry_disj E R g e (p : loc) cv :
    ↑naN ⊆ E →
    ghost_map_auth heap_greg_name 1 R -∗ cwentry g e -∗ bpt (inl p) cv ={E}=∗
      ⌜∀ m cs, R !! g = Some (m, cs) → ∀ j : nat, (j < length cs)%nat → p ≠ e.1.1.1.1 +ₗ j⌝ ∗
      ghost_map_auth heap_greg_name 1 R ∗ cwentry g e ∗ bpt (inl p) cv.
  Proof.
    iIntros (?) "Hreg (%m & %cs & #Hg & Hgd & G & %P & %d & £ & #Guard & #HP) Hp".
    iDestruct (greg_lookup with "Hreg Hg") as %HR.
    destruct (decide (in_rng e.1.1.1.1 (length cs) p)) as [(j & Hj & ->)|Hn]; last first.
    { iModIntro. iFrame "Hreg Hp". iSplitR.
      { iPureIntro. intros m' cs' HR' j Hj ->. rewrite HR in HR'. simplify_eq. apply Hn. by exists j. }
      iExists m, cs. iSplitR; [iExact "Hg"|]. iFrame "Hgd G". iExists P, d. iFrame "£ Guard HP". }
    iMod (guards_open_later with "Guard G") as "Open"; [done|].
    iMod (lc_fupd_elim_laterN with "£ Open") as ">[P _]".
    iDestruct ("HP" with "P") as (l0 g0 m0 cs0 o [Hl0 Hb]) "[_ Hcs]".
    destruct (lookup_lt_is_Some_2 cs0 (o + j)%nat) as [c Hc]; [lia|].
    iDestruct (big_sepL_lookup with "Hcs") as "Hc"; [done|].
    rewrite Hl0 shift_loc_assoc_nat.
    iDestruct (fpt_excl with "Hp Hc") as "[]".
  Qed.

  Lemma cwentries_disj E R (CW : gmap positive (cwkey * iProp Σ)) (p : loc) cv :
    ↑naN ⊆ E →
    ghost_map_auth heap_greg_name 1 R -∗ ([∗ map] g ↦ e ∈ CW, cwentry g e) -∗ bpt (inl p) cv ={E}=∗
      ⌜∀ g e m cs, CW !! g = Some e → R !! g = Some (m, cs) →
         ∀ j : nat, (j < length cs)%nat → p ≠ e.1.1.1.1 +ₗ j⌝ ∗
      ghost_map_auth heap_greg_name 1 R ∗ ([∗ map] g ↦ e ∈ CW, cwentry g e) ∗ bpt (inl p) cv.
  Proof.
    iIntros (?) "Hreg HCW Hp". iInduction CW as [|g e CW Hg] "IH" using map_ind.
    { iFrame. iPureIntro. intros ????. by rewrite lookup_empty. }
    rewrite big_sepM_insert //. iDestruct "HCW" as "[He HCW]".
    iMod (cwentry_disj with "Hreg He Hp") as "(%H1 & Hreg & He & Hp)"; [done|].
    iMod ("IH" with "Hreg HCW Hp") as "(%H2 & $ & HCW & $)". iFrame. iPureIntro.
    intros g' e' m cs. destruct (decide (g = g')) as [<-|].
    - rewrite lookup_insert. intros [= <-]. apply H1.
    - rewrite lookup_insert_ne //. apply H2.
  Qed.

  Lemma cwentries_disj_fbytes E R (CW : gmap positive (cwkey * iProp Σ)) l fbs :
    ↑naN ⊆ E →
    ghost_map_auth heap_greg_name 1 R -∗ ([∗ map] g ↦ e ∈ CW, cwentry g e) -∗
    heap_mapsto_fbytes l fbs ={E}=∗
      ⌜∀ g e m cs, CW !! g = Some e → R !! g = Some (m, cs) →
         ∀ i j : nat, (i < length fbs)%nat → (j < length cs)%nat → l +ₗ i ≠ e.1.1.1.1 +ₗ j⌝ ∗
      ghost_map_auth heap_greg_name 1 R ∗ ([∗ map] g ↦ e ∈ CW, cwentry g e) ∗
      heap_mapsto_fbytes l fbs.
  Proof.
    iIntros (?) "Hreg HCW Hfbs". iInduction fbs as [|fb fbs] "IH" forall (l).
    { iFrame. iPureIntro. simpl. lia. }
    rewrite !heap_mapsto_fbytes_cons. iDestruct "Hfbs" as "[Hfb Hfbs]".
    iMod (cwentries_disj with "Hreg HCW Hfb") as "(%H1 & Hreg & HCW & $)"; [done|].
    iMod ("IH" with "Hreg HCW Hfbs") as "(%H2 & $ & $ & $)". iPureIntro.
    intros g e m cs Hg HR [|i] j Hi Hj.
    - rewrite shift_loc_0_nat. by eapply H1.
    - rewrite shift_loc_S. eapply H2; [done..|simpl in Hi; lia|done].
  Qed.

  (** ** Creating a cell group ([PCellFromOwn]) *)
  Lemma bytes_ctx_pcell_create E σB l m fbs fv :
    ↑naN ⊆ E → (0 < mty_size m)%nat → mty_wf m →
    bytes_ctx σB -∗ heap_mapsto_fbytes l fbs -∗ brepr m fbs fv ={E}=∗ ∃ g cs,
      bytes_ctx σB ∗ loc_side l g m cs ∗ gdyn g fv ∗
      (if bool_decide (fv_cells fv = []) then gnocell g else True).
  Proof.
    iIntros (? Hsz Hmwf) "(%𝛼 & %M & %Hr & %Hwf & H● & Hbank & Entries & Cells) Hfbs #Hrep".
    iDestruct "Cells" as (R ρ NC NS CW) "(Hreg & Hdyn & Hnc & Hns & Hcw & [%Hcwf %Hlive] & #HR & #HNS & Hcwe & Hρ)".
    iDestruct (brepr_frepr with "Hreg Hrep") as %Hfrep.
    have Hlen : length fbs = mty_size m by eapply frepr_length; [apply Hcwf|done].
    iDestruct (fheap_no_dupes with "H●") as %Hnd.
    iDestruct (bheap_edges _ l (fb_rst <$> fbs) with "H● [Hfbs]") as %Hedges.
    { rewrite /heap_mapsto_fbytes big_sepL_fmap. done. }
    iMod (cwentries_disj_fbytes with "Hreg Hcwe Hfbs") as "(%Hcwd & Hreg & Hcwe & Hfbs)"; [done|].
    destruct Hcwf as (HRwf & HdomR & Hrefs & Hdisj & Hpos & HdomNC & HNC & HCW & Hmwfs & HNSd).
    destruct Hlive as [Hlive1 Hlive2].
    (* The groups embedded in [fv] are live. *)
    have Hlive_fv : ∀ g', g' ∈ fv_cells fv → g' ∈ dom ρ.
    { intros g' Hg'. destruct (frepr_cells_in _ _ _ _ _ Hfrep Hg') as (m' & cs' & HR' & Hin).
      have Hpos' := Hpos _ _ _ HR'. have Hlen' := HRwf _ _ _ HR'.
      destruct cs' as [|c cs']; [simpl in Hlen'; lia|].
      destruct (elem_of_list_lookup_1 _ _ (Hin c ltac:(set_solver))) as [i Hi].
      have := Hedges i (inl c). rewrite list_lookup_fmap Hi /=. intros Hp. specialize (Hp eq_refl).
      rewrite /𝛼_fine_pair in Hp. destruct (𝛼 !! inl (l +ₗ i)) as [[[|c0 rest] v]|] eqn:Hrow; try done.
      subst c0. destruct (Hlive1 _ _ _ c Hrow ltac:(set_solver)) as (g'' & m'' & cs'' & Hg'' & HR'' & Hc'').
      destruct (decide (g'' = g')) as [->|Hne]; [done|].
      exfalso. apply (Hdisj _ _ _ _ _ _ Hne HR'' HR' c); [done|set_solver]. }
    iMod (bheap_insert_fronts _ _ _ (reg_cells R) with "H● Hfbs")
      as (𝛼' cs) "([%Hlencs [%Hndcs [%HcsX [%Hphi [%Hrows %Hsame]]]]] & H● & Hls & Hcs)".
    set (g := fresh_gid R).
    have HgR : R !! g = None := fresh_gid_fresh R.
    have Hgρ : ρ !! g = None by apply not_elem_of_dom; intros ?; apply (not_elem_of_dom R g); [done|set_solver].
    have HgNC : NC !! g = None by apply not_elem_of_dom; intros ?; apply (not_elem_of_dom R g); [done|set_solver].
    have HgCW : (fst <$> CW) !! g = None.
    { destruct ((fst <$> CW) !! g) as [k|] eqn:Hk; [|done]. destruct (HCW g k Hk) as [Hρg _].
      by rewrite Hgρ in Hρg. }
    iMod (ghost_map_insert_persist g (m, cs) with "Hreg") as "[Hreg #Hg]"; [done|].
    iMod (ghost_map_insert g fv with "Hdyn") as "[Hdyn Hgd]"; [done|].
    set (NC' := if bool_decide (fv_cells fv = []) then <[g := ()]> NC else NC).
    iAssert (|==> ghost_map_auth heap_gnc_name 1 NC' ∗
      if bool_decide (fv_cells fv = []) then gnocell g else True)%I with "[Hnc]" as ">[Hnc Hgnc]".
    { rewrite /NC'. case_bool_decide; [|by iFrame].
      iMod (ghost_map_insert_persist g () with "Hnc") as "[$ $]"; done. }
    iModIntro. iExists g, cs. iFrame "Hgd Hgnc". iSplitR "Hls"; last by iFrame "Hg".
    iExists 𝛼', M. rewrite Hphi. iFrame "H● Hbank Entries". iSplit; [done|]. iSplit; [done|].
    iExists (<[g := (m, cs)]> R), (<[g := fv]> ρ), NC', NS, CW. iFrame "Hreg Hdyn Hnc Hns Hcw Hcwe HNS".
    have HRsub : R ⊆ <[g := (m, cs)]> R by apply insert_subseteq.
    iSplit; [iPureIntro; split|].
    { (* cells_wf *)
      split_and!.
      - intros g' m' cs' Hg'. destruct (decide (g' = g)) as [->|Hne].
        + rewrite lookup_insert in Hg'. simplify_eq. by rewrite Hlencs.
        + rewrite lookup_insert_ne // in Hg'. by eapply HRwf.
      - rewrite !dom_insert_L. set_solver.
      - intros g' fv' Hg' g'' Hg''. destruct (decide (g' = g)) as [->|Hne].
        + rewrite lookup_insert in Hg'. simplify_eq. have Hd := Hlive_fv g'' Hg''.
          split; [apply fresh_gid_gt; set_solver|]. rewrite dom_insert_L. set_solver.
        + rewrite lookup_insert_ne // in Hg'. destruct (Hrefs g' fv' Hg' g'' Hg'').
          split; [done|]. rewrite dom_insert_L. set_solver.
      - intros g1 g2 m1 cs1 m2 cs2 Hne H1 H2.
        destruct (decide (g1 = g)) as [->|Hne1]; destruct (decide (g2 = g)) as [->|Hne2]; try done.
        + rewrite lookup_insert in H1. rewrite lookup_insert_ne // in H2. simplify_eq.
          intros c Hc1 Hc2. apply (HcsX c Hc1). by eapply reg_cells_in.
        + rewrite lookup_insert in H2. rewrite lookup_insert_ne // in H1. simplify_eq.
          intros c Hc1 Hc2. apply (HcsX c Hc2). by eapply reg_cells_in.
        + rewrite lookup_insert_ne // in H1. rewrite lookup_insert_ne // in H2.
          by apply (Hdisj g1 g2 m1 cs1 m2 cs2).
      - intros g' m' cs' Hg'. destruct (decide (g' = g)) as [->|Hne].
        + rewrite lookup_insert in Hg'. by simplify_eq.
        + rewrite lookup_insert_ne // in Hg'. by eapply Hpos.
      - rewrite /NC' dom_insert_L. case_bool_decide; rewrite ?dom_insert_L; set_solver.
      - intros g' fv' Hg' HNC'. destruct (decide (g' = g)) as [->|Hne].
        + rewrite lookup_insert in Hg'. simplify_eq. rewrite /NC' in HNC'. case_bool_decide; [done|].
          exfalso. by apply (not_elem_of_dom NC g).
        + rewrite lookup_insert_ne // in Hg'. apply (HNC g' fv' Hg').
          rewrite /NC' in HNC'. case_bool_decide; [|done]. rewrite dom_insert_L in HNC'. set_solver.
      - intros g' k Hk. destruct (HCW g' k Hk) as (Hρg & m' & cs' & HR' & Hb).
        have Hne : g' ≠ g by intros ->; rewrite HgCW in Hk.
        rewrite !lookup_insert_ne //. eauto.
      - intros g' m' cs' Hg'. destruct (decide (g' = g)) as [->|Hne].
        + rewrite lookup_insert in Hg'. by simplify_eq.
        + rewrite lookup_insert_ne // in Hg'. by eapply Hmwfs.
      - intros k Hk. rewrite dom_insert_L. apply HNSd in Hk. set_solver. }
    { (* cells_live *)
      split.
      - intros k cs' v c Hk Hc. destruct (Hrows k cs' v c Hk Hc) as [Hcn|(cs'' & Hk' & Hc'')].
        + exists g, m, cs. rewrite dom_insert_L lookup_insert. split_and!; [set_solver|done|done].
        + destruct (Hlive1 k cs'' v c Hk' Hc'') as (g' & m' & cs0 & Hg' & HR' & Hc0).
          exists g', m', cs0. rewrite dom_insert_L. split_and!; [set_solver| |done].
          by eapply lookup_weaken.
      - intros g' k m' cs' Hk HR' i c Hc.
        have Hne : g' ≠ g by intros ->; rewrite HgCW in Hk.
        rewrite lookup_insert_ne // in HR'.
        destruct (Hlive2 g' k m' cs' Hk HR' i c Hc) as (rest & v & Hrow & Hcr).
        exists rest, v. split; [|done]. rewrite Hsame //. intros j Hj Heq.
        move: Hk. rewrite lookup_fmap. destruct (CW !! g') as [e|] eqn:He; [|done]. intros [= <-].
        apply (Hcwd g' e m' cs' He HR' j i); [lia|by eapply lookup_lt_Some|].
        symmetry. by apply inl_loc_inj in Heq. }
    (* the static registry and the contents *)
    iSplitR "Hcs Hρ". { rewrite big_sepM_insert //. by iFrame "HR Hg". }
    rewrite big_sepM_insert //. iSplitL "Hcs".
    - iExists m, cs, (fb_rst <$> fbs). iFrame "Hcs". iPureIntro. split_and!.
      + apply lookup_insert.
      + rewrite fb_strip_rst. by eapply frepr_mono.
      + intros i ls b. rewrite list_lookup_fmap. destruct (fbs !! i) as [[c|b']|]; simpl; try done.
        intros [= <- <-]. rewrite /cw_ls HgCW. done.
      + intros g' o Hk. exfalso. apply HNSd in Hk. simpl in Hk. by apply not_elem_of_dom in HgR.
    - iApply (big_sepM_impl with "Hρ"). iIntros "!>" (g' fv' _) "H". by iApply gcontents_mono_R.
  Qed.

  Lemma has_pair_head_contra (c c' : positive) rest :
    NoDup (c :: rest) → list_has_pair (c :: rest) c' c → False.
  Proof.
    intros Hnd (cs1 & cs2 & Heq)%list_has_pair_destruct.
    destruct cs1 as [|c0 cs1]; simpl in Heq; injection Heq as -> Hrest.
    - subst rest. apply NoDup_cons in Hnd as [Hn _]. apply Hn. set_solver.
    - apply NoDup_cons in Hnd as [Hn _]. apply Hn. rewrite Hrest. set_solver.
  Qed.

  (** Deleting the front cells of rows. *)
  Lemma bheap_delete_fronts 𝛼 l cs fbs :
    bheap 𝛼 -∗ ([∗ list] i ↦ c ∈ cs, bpt (inl (l +ₗ i)) (inl c)) -∗ bcells cs fbs ==∗ ∃ 𝛼',
      ⌜bphi 𝛼' = bphi 𝛼 ∧
       (∀ k cs' v c, 𝛼' !! k = Some (cs', v) → c ∈ cs' →
          c ∉ cs ∧ ∃ cs'', 𝛼 !! k = Some (cs'', v) ∧ c ∈ cs'') ∧
       (∀ k, (∀ i : nat, (i < length cs)%nat → k ≠ inl (l +ₗ i)) → 𝛼' !! k = 𝛼 !! k) ∧
       (∀ (i : nat) c rest v, cs !! i = Some c → 𝛼 !! inl (l +ₗ i) = Some (c :: rest, v) →
          𝛼' !! inl (l +ₗ i) = Some (rest, v))⌝ ∗
      bheap 𝛼' ∗ [∗ list] i ↦ fb ∈ fbs, bpt (inl (l +ₗ i)) fb.
  Proof.
    iInduction cs as [|c cs] "IH" forall (𝛼 l fbs); iIntros "H● Hls Hcs";
      destruct fbs as [|fb fbs]; rewrite /bcells /=; try by iDestruct "Hcs" as "[]".
    { iModIntro. iExists 𝛼. iFrame. iPureIntro. split_and!; [done| |done|done].
      intros k cs' v c Hk Hc. split; [by apply not_elem_of_nil|eauto]. }
    iDestruct "Hcs" as "[Hc Hcs]". iDestruct "Hls" as "[Hl Hls]".
    iEval (rewrite shift_loc_0_nat) in "Hl".
    iDestruct (fheap_no_dupes with "H●") as %Hnd.
    iMod (fcmap_delete_front with "H● Hl Hc") as (cs0 v0) "(%Hk & H● & Hl)".
    have Hnd0 : NoDup (c :: cs0) by eapply row_nodup.
    iMod ("IH" $! _ (l +ₗ 1) fbs with "H● [Hls] Hcs") as (𝛼') "([%Hphi [%Hrows [%Hsame %Hpt]]] & H● & Hfbs)".
    { iApply (big_sepL_impl with "Hls"). iIntros "!>" (i c' _) "H". by rewrite shift_loc_S. }
    iModIntro. iExists 𝛼'. iFrame "H●". iSplit; last first.
    { iSplitL "Hl"; [by rewrite shift_loc_0_nat|].
      iApply (big_sepL_impl with "Hfbs"). iIntros "!>" (i fb' _) "H". by rewrite shift_loc_S. }
    iPureIntro. split_and!.
    - by rewrite Hphi phi_insert_loc insert_id // phi_lookup Hk.
    - intros k cs' v c' Hk' Hc'. destruct (Hrows k cs' v c' Hk' Hc') as [Hn (cs'' & Hk'' & Hc'')].
      destruct (decide (k = inl l)) as [->|Hne].
      + rewrite lookup_insert in Hk''. simplify_eq. split.
        * rewrite elem_of_cons. intros [->|?]; [|done]. apply NoDup_cons in Hnd0 as [Hn0 _]. done.
        * exists (c :: cs''). rewrite Hk. split; [done|set_solver].
      + rewrite lookup_insert_ne // in Hk''. split; [|eauto].
        rewrite elem_of_cons. intros [->|?]; [|done].
        eapply rows_disjoint; [exact Hnd|exact Hne|exact Hk''|exact Hk|exact Hc''|set_solver].
    - intros k Hk'. rewrite Hsame.
      + rewrite lookup_insert_ne //. intros Heq. apply (Hk' 0%nat); [simpl; lia|].
        by rewrite shift_loc_0_nat Heq.
      + intros i Hi. rewrite -shift_loc_S. apply (Hk' (S i)). simpl. lia.
      - intros [|i] c' rest v Hc' Hl.
      + simpl in Hc'. injection Hc' as <-. rewrite shift_loc_0_nat Hk in Hl. injection Hl as <- <-.
        rewrite shift_loc_0_nat Hsame; [by rewrite lookup_insert|].
        intros i _ Heq. apply inl_loc_inj in Heq. by apply (shift_loc_ne_S l i).
      + simpl in Hc'. rewrite shift_loc_S. apply (Hpt i c' rest v Hc').
        rewrite lookup_insert_ne; [by rewrite -shift_loc_S|].
        intros Heq. apply inl_loc_inj in Heq. by apply (shift_loc_ne_S l i).
  Qed.

  (** ** Destroying a cell group ([PCell2Own]) *)
  Lemma bytes_ctx_pcell_destroy σB l g m cs fv :
    bytes_ctx σB -∗ loc_side l g m cs -∗ gdyn g fv ==∗ ∃ fbs,
      bytes_ctx σB ∗ heap_mapsto_fbytes l fbs ∗ brepr m fbs fv.
  Proof.
    iIntros "(%𝛼 & %M & %Hr & %Hwf & H● & Hbank & Entries & Cells) [#Hg Hls] Hgd".
    iDestruct "Cells" as (R ρ NC NS CW) "(Hreg & Hdyn & Hnc & Hns & Hcw & [%Hcwf %Hlive] & #HR & #HNS & Hcwe & Hρ)".
    iDestruct (greg_lookup with "Hreg Hg") as %HRg.
    iDestruct (gdyn_lookup with "Hdyn Hgd") as %Hρg.
    iAssert ⌜CW !! g = None⌝%I as %HgCW.
    { destruct (CW !! g) as [e|] eqn:He; [|done].
      iDestruct (big_sepM_lookup with "Hcwe") as "(%m' & %cs' & _ & Hgd' & _)"; [done|].
      iDestruct (gdyn_excl with "Hgd Hgd'") as "[]". }
    have HgCW' : (fst <$> CW) !! g = None by rewrite lookup_fmap HgCW.
    iDestruct (fheap_no_dupes with "H●") as %Hnd.
    iDestruct (loc_side_rows with "H● [$Hg $Hls]") as %Hrows0.
    iDestruct (gcontents_edges with "H● Hρ") as %Hedges.
    iDestruct (big_sepM_delete with "Hρ") as "[(%m' & %cs' & %fbs & (%HR' & %Hrep & %Hls & %Hns) & Hcs) Hρ]"; [done|].
    rewrite HRg in HR'. injection HR' as <- <-.
    destruct Hcwf as (HRwf & HdomR & Hrefs & Hdisj & Hpos & HdomNC & HNC & HCW & Hmwfs & HNSd).
    destruct Hlive as [Hlive1 Hlive2].
    have Hcs0 : ∃ c0 cs0, cs = c0 :: cs0.
    { have := Hpos _ _ _ HRg. have := HRwf _ _ _ HRg. destruct cs; [simpl; lia|eauto]. }
    destruct Hcs0 as (c0 & cs0 & ->).
    iMod (bheap_delete_fronts with "H● Hls Hcs") as (𝛼') "([%Hphi [%Hrows [%Hsame %Hpt]]] & H● & Hfbs)".
    iMod (ghost_map_delete with "Hdyn Hgd") as "Hdyn".
    iModIntro. iExists (fb_strip <$> fbs).
    iSplitR "Hfbs"; last iSplitL "Hfbs".
    2:{ rewrite /heap_mapsto_fbytes big_sepL_fmap. iApply (big_sepL_impl with "Hfbs").
        iIntros "!>" (i fb Hfb) "H". destruct fb as [c|[ls b]]; [done|].
        rewrite (Hls i ls b Hfb) /cw_ls HgCW'. done. }
    2:{ iExists R. iFrame "HR". done. }
    iExists 𝛼', M. rewrite Hphi. iFrame "H● Hbank Entries".
    iSplit; [done|]. iSplit; [done|].
    iExists R, (delete g ρ), NC, NS, CW. iFrame "Hreg Hdyn Hnc Hns Hcw HR HNS Hcwe Hρ".
    iPureIntro. split; [split_and!|split].
    - done.
    - rewrite dom_delete_L. set_solver.
    - intros g' fv' Hg' g'' Hg''. apply lookup_delete_Some in Hg' as [Hne Hg'].
      destruct (Hrefs g' fv' Hg' g'' Hg'') as [Hlt Hdom]. split; [done|].
      rewrite dom_delete_L elem_of_difference. split; [done|]. rewrite elem_of_singleton.
      intros ->. destruct (Hedges g' fv' Hg') as (m'' & cs'' & fbs'' & (HR'' & Hrep'' & _) & Hlen'' & Hfp'').
      destruct (frepr_cells_in _ _ _ _ _ Hrep'' Hg'') as (m3 & cs3 & HR3 & Hin3).
      rewrite HRg in HR3. simplify_eq.
      destruct (elem_of_list_lookup_1 _ _ (Hin3 c0 ltac:(set_solver))) as [i Hi].
      rewrite list_lookup_fmap in Hi. destruct (fbs'' !! i) as [fbi|] eqn:Hfbi; [|done].
      destruct fbi as [c2|[??]]; simpl in Hi; simplify_eq.
      destruct (lookup_lt_is_Some_2 cs'' i) as [c'' Hc'']; [rewrite Hlen''; by eapply lookup_lt_Some|].
      have Hp := Hfp'' i c'' (inl c0) Hc'' Hfbi. destruct Hp as (k & csk & vk & Hk & Hpair).
      destruct (Hrows0 0%nat c0 eq_refl) as (rest & v & Hrow). rewrite shift_loc_0_nat in Hrow.
      destruct (decide (k = inl l)) as [->|Hne'].
      + rewrite Hrow in Hk. simplify_eq. eapply has_pair_head_contra; [|done].
        by eapply row_nodup.
      + apply (rows_disjoint loc positive bval 𝛼 k (inl l) csk vk (c0 :: rest) v c0 Hnd Hne' Hk Hrow);
          [|set_solver]. by apply list_has_pair_elem_of in Hpair as [_ ?].
    - done.
    - done.
    - done.
    - intros g' fv' Hg' HNC'. apply lookup_delete_Some in Hg' as [_ Hg']. by eapply HNC.
    - intros g' k Hk. destruct (HCW g' k Hk) as [Hρg' Hrest]. split; [|done].
      rewrite lookup_delete_ne //. intros ->. by rewrite HgCW' in Hk.
    - done.
    - done.
    - intros k cs' v c Hk Hc. destruct (Hrows k cs' v c Hk Hc) as (Hnc & cs'' & Hk' & Hc').
      destruct (Hlive1 k cs'' v c Hk' Hc') as (g' & m' & cs3 & Hg' & HR3 & Hc3).
      exists g', m', cs3. split_and!; [|done|done]. rewrite dom_delete_L elem_of_difference.
      split; [done|]. rewrite elem_of_singleton. intros ->. rewrite HRg in HR3. by simplify_eq.
    - intros g' k m' cs' Hk HR' i c Hc.
      destruct (Hlive2 g' k m' cs' Hk HR' i c Hc) as (rest & v & Hrow & Hcr).
      have Hne : g' ≠ g by intros ->; rewrite HgCW' in Hk.
      destruct (decide (∃ j : nat, (j < length (c0 :: cs0))%nat ∧ k.1.1.1 +ₗ i = l +ₗ j))
        as [(j & Hj & Heq)|Hn].
      + destruct (lookup_lt_is_Some_2 (c0 :: cs0) j) as [cj Hcj]; [done|].
        destruct (Hrows0 j cj Hcj) as (rest' & v' & Hrow'). rewrite -Heq Hrow in Hrow'.
        injection Hrow' as -> ->. exists rest', v'. split; [rewrite Heq; by eapply Hpt; [|rewrite -Heq]|].
        apply elem_of_cons in Hcr as [->|Hcr]; [|done]. exfalso.
        apply (Hdisj g' g m' cs' m (c0 :: cs0) Hne HR' HRg cj); [by eapply elem_of_list_lookup_2|].
        by eapply elem_of_list_lookup_2.
      + exists rest, v. split; [|done]. rewrite Hsame //. intros j Hj Heq'.
        apply inl_loc_inj in Heq'. apply Hn. eauto.
  Qed.

  (** ** Untethering and retethering (moving a [PCell]) *)

  Lemma bheap_untethers 𝛼 l cs :
    bheap 𝛼 -∗ ([∗ list] i ↦ c ∈ cs, bpt (inl (l +ₗ i)) (inl c)) ==∗ ∃ 𝛼' (vs : list bval),
      ⌜length vs = length cs ∧ bphi 𝛼' = bphi 𝛼 ∧
       (∀ (i : nat) c v, cs !! i = Some c → vs !! i = Some v →
          ∃ rest, 𝛼 !! inl (l +ₗ i) = Some (c :: rest, v)) ∧
       (∀ k cs' v c, 𝛼' !! k = Some (cs', v) → c ∈ cs' →
          ∃ k' cs'', 𝛼 !! k' = Some (cs'', v) ∧ c ∈ cs'') ∧
       (∀ l', (∀ i : nat, (i < length cs)%nat → l' ≠ l +ₗ i) → 𝛼' !! inl l' = 𝛼 !! inl l')⌝ ∗
      bheap 𝛼' ∗ ([∗ list] i ↦ v ∈ vs, bpt (inl (l +ₗ i)) (inr v)) ∗
      ([∗ list] c; v ∈ cs; vs, ∃ u, bunt u c v).
  Proof.
    iInduction cs as [|c cs] "IH" forall (𝛼 l); iIntros "H● Hls".
    { iModIntro. iExists 𝛼, []. iFrame "H●". iSplit; [|by iSplit]. iPureIntro.
      split_and!; try done. intros k cs' v c Hk Hc. eauto. }
    iDestruct "Hls" as "[Hl Hls]". iEval (rewrite shift_loc_0_nat) in "Hl".
    iMod (fcmap_untether with "H● Hl") as (k cells1 cells2 v u) "([%Hrow %Hu] & H● & Hl & Hu)".
    destruct (is_row_for_lc_loc _ _ _ _ _ _ _ _ _ _ Hrow) as (-> & -> & Hk).
    iMod ("IH" $! _ (l +ₗ 1) with "H● [Hls]") as (𝛼' vs) "([%Hlen [%Hphi [%Hvs [%Hcells %Hsame]]]] & H● & Hvs & Hus)".
    { iApply (big_sepL_impl with "Hls"). iIntros "!>" (i c' _) "H". by rewrite shift_loc_S. }
    have Hu' : 𝛼 !! inr u = None by done.
    iModIntro. iExists 𝛼', (v :: vs). iFrame "H●". iSplit; last iSplitL "Hl Hvs".
    - iPureIntro. split_and!.
      + by rewrite /= Hlen.
      + rewrite Hphi /𝛼_untether phi_insert_loc phi_insert_unt insert_id // phi_lookup Hk //.
      + intros [|i] c' v' Hc' Hv'; simpl in Hc', Hv'; simplify_eq.
        * rewrite shift_loc_0_nat. eauto.
        * destruct (Hvs i c' v' Hc' Hv') as (rest & Hr). exists rest.
          rewrite /𝛼_untether lookup_insert_ne in Hr; [|intros [= Heq]; by apply (shift_loc_ne_S l i)].
          rewrite lookup_insert_ne // -shift_loc_S in Hr. done.
      + intros k' cs' v' c' Hk' Hc'. destruct (Hcells k' cs' v' c' Hk' Hc') as (k'' & cs'' & Hk'' & Hc'').
        rewrite /𝛼_untether in Hk''. destruct (decide (k'' = inl l)) as [->|Hne].
        { rewrite lookup_insert in Hk''. simplify_eq. by apply not_elem_of_nil in Hc''. }
        rewrite lookup_insert_ne // in Hk''. destruct (decide (k'' = inr u)) as [->|Hne'].
        { rewrite lookup_insert in Hk''. simplify_eq. exists (inl l), (c :: cells2). by split. }
        rewrite lookup_insert_ne // in Hk''. eauto.
      + intros l' Hl'. rewrite Hsame; last first.
        { intros i Hi. rewrite -shift_loc_S. apply (Hl' (S i)). simpl. lia. }
        rewrite /𝛼_untether lookup_insert_ne; last first.
        { intros [= ->]. apply (Hl' 0%nat); [simpl; lia|]. by rewrite shift_loc_0_nat. }
        by rewrite lookup_insert_ne.
    - iSplitL "Hl"; [by rewrite shift_loc_0_nat|].
      iApply (big_sepL_impl with "Hvs"). iIntros "!>" (i v' _) "H". by rewrite shift_loc_S.
    - iFrame "Hus". iExists u. by iFrame "Hu".
  Qed.

  Lemma bheap_retethers 𝛼 l cs (vs : list bval) :
    bheap 𝛼 -∗ ([∗ list] i ↦ v ∈ vs, bpt (inl (l +ₗ i)) (inr v)) -∗
    ([∗ list] c; v ∈ cs; vs, ∃ u, bunt u c v) ==∗ ∃ 𝛼',
      ⌜bphi 𝛼' = bphi 𝛼 ∧
       (∀ k cs' v c, 𝛼' !! k = Some (cs', v) → c ∈ cs' →
          ∃ k' cs'', 𝛼 !! k' = Some (cs'', v) ∧ c ∈ cs'') ∧
       (∀ l', (∀ i : nat, (i < length cs)%nat → l' ≠ l +ₗ i) → 𝛼' !! inl l' = 𝛼 !! inl l')⌝ ∗
      bheap 𝛼' ∗ [∗ list] i ↦ c ∈ cs, bpt (inl (l +ₗ i)) (inl c).
  Proof.
    iInduction cs as [|c cs] "IH" forall (𝛼 l vs); iIntros "H● Hvs Hus";
      destruct vs as [|v vs]; try by iDestruct (big_sepL2_length with "Hus") as %?.
    { iModIntro. iExists 𝛼. iFrame "H●". iSplit; [|done]. iPureIntro.
      split_and!; try done. intros k cs' v c Hk Hc. eauto. }
    iDestruct "Hvs" as "[Hv Hvs]". iEval (rewrite shift_loc_0_nat) in "Hv".
    iDestruct "Hus" as "[[%u Hu] Hus]".
    iMod (fcmap_retether with "H● Hv Hu") as (cs0) "([%Hl %Hu] & H● & Hl)".
    iMod ("IH" $! _ (l +ₗ 1) vs with "H● [Hvs] Hus") as (𝛼') "([%Hphi [%Hcells %Hsame]] & H● & Hls)".
    { iApply (big_sepL_impl with "Hvs"). iIntros "!>" (i v' _) "H". by rewrite shift_loc_S. }
    iModIntro. iExists 𝛼'. iFrame "H●". iSplit; last first.
    { iSplitL "Hl"; [by rewrite shift_loc_0_nat|].
      iApply (big_sepL_impl with "Hls"). iIntros "!>" (i c' _) "H". by rewrite shift_loc_S. }
    iPureIntro. split_and!.
    - rewrite Hphi phi_insert_loc phi_delete_unt insert_id // phi_lookup Hl //.
    - intros k cs' v' c' Hk' Hc'. destruct (Hcells k cs' v' c' Hk' Hc') as (k'' & cs'' & Hk'' & Hc'').
      destruct (decide (k'' = inl l)) as [->|Hne].
      { rewrite lookup_insert in Hk''. simplify_eq. exists (inr u), (c :: cs0). by split. }
      rewrite lookup_insert_ne // in Hk''. destruct (decide (k'' = inr u)) as [->|Hne'].
      { by rewrite lookup_delete in Hk''. }
      rewrite lookup_delete_ne // in Hk''. eauto.
    - intros l' Hl'. rewrite Hsame; last first.
      { intros i Hi. rewrite -shift_loc_S. apply (Hl' (S i)). simpl. lia. }
      rewrite lookup_insert_ne; last first.
      { intros [= ->]. apply (Hl' 0%nat); [simpl; lia|]. by rewrite shift_loc_0_nat. }
      by rewrite lookup_delete_ne.
  Qed.

  (** The final byte of a row whose location is not in the range of a group with a write in
      flight is not being written. *)
  Lemma row_end_rst 𝛼 R ρ NC NS (CW : gmap positive cwkey) k cells v :
    cells_no_dupes loc positive bval 𝛼 → cells_wf R ρ NC NS CW → cells_live 𝛼 R ρ CW →
    gfacts 𝛼 R NS CW ρ →
    (∀ g' e m' cs' (j : nat), CW !! g' = Some e → R !! g' = Some (m', cs') →
       (j < length cs')%nat → k ≠ inl (e.1.1.1 +ₗ j)) →
    𝛼 !! k = Some (cells, v) → cells ≠ [] → v.1 = RSt 0.
  Proof.
    intros Hnd Hwf [Hlive1 Hlive2] Hedges Hcwd Hk Hne0.
    destruct Hwf as (HRwf & HdomR & Hrefs & Hdisj & Hpos & HdomNC & HNC & HCW & _).
    destruct (exists_last Hne0) as (pre & cl & Heq).
    have Hcl : cl ∈ cells by rewrite Heq; set_solver.
    destruct (Hlive1 k _ v cl Hk Hcl) as (g' & m' & cs' & Hg' & HR' & Hcl').
    apply elem_of_dom in Hg' as [fv' Hfv'].
    destruct (Hedges g' fv' Hfv') as (m'' & cs'' & fbs & (HR'' & _ & Hls & _) & Hlen & Hfp).
    rewrite HR' in HR''. injection HR'' as <- <-.
    destruct (elem_of_list_lookup_1 _ _ Hcl') as [j Hj].
    destruct (lookup_lt_is_Some_2 fbs j) as [fb Hfb]; [rewrite -Hlen; by eapply lookup_lt_Some|].
    have Hp := Hfp j cl fb Hj Hfb. have Hk' := Hk. rewrite Heq in Hk'.
    have Hfbv := row_end_pair loc positive bval 𝛼 k pre cl v fb Hnd Hk' Hp. rewrite Hfbv in Hfb.
    destruct v as [ls b]. rewrite (Hls j ls b Hfb) /cw_ls.
    destruct (CW !! g') as [e|] eqn:He; [|done]. exfalso.
    have Hrow' := Hlive2 g' e m' cs' He HR' j cl Hj.
    have Hkeq := row_has_same _ _ _ _ _ _ Hnd Hrow' Hk Hcl.
    apply (Hcwd g' e m' cs' j He HR'); [by eapply lookup_lt_Some|done].
  Qed.

  Lemma bytes_ctx_pcell_untether E σB l g m cs :
    ↑naN ⊆ E →
    bytes_ctx σB -∗ loc_side l g m cs ={E}=∗ ∃ bs v,
      bytes_ctx σB ∗ l ↦b bs ∗ ⌜decode_value m bs = Some v⌝ ∗ untethered g m cs bs.
  Proof.
    iIntros (?) "(%𝛼 & %M & %Hr & %Hwf & H● & Hbank & Entries & Cells) [#Hg Hls]".
    iDestruct "Cells" as (R ρ NC NS CW) "(Hreg & Hdyn & Hnc & Hns & Hcw & [%Hcwf %Hlive] & #HR & #HNS & Hcwe & Hρ)".
    iDestruct (greg_lookup with "Hreg Hg") as %HRg.
    iDestruct (fheap_no_dupes with "H●") as %Hnd.
    iDestruct (loc_side_rows with "H● [$Hg $Hls]") as %Hrows0.
    iDestruct (gcontents_edges with "H● Hρ") as %Hedges.
    iDestruct (cells_decode with "H● Hρ []") as %Hdec; [by iPureIntro|].
    iMod (cwentries_disj_fbytes _ _ _ l (inl <$> cs) with "Hreg Hcwe [Hls]")
      as "(%Hcwd & Hreg & Hcwe & Hls)"; [done| |].
    { rewrite /heap_mapsto_fbytes big_sepL_fmap. done. }
    iEval (rewrite /heap_mapsto_fbytes big_sepL_fmap) in "Hls".
    have Hcwf' := Hcwf. have Hlive' := Hlive.
    destruct Hcwf as (HRwf & HdomR & Hrefs & Hdisj & Hpos & HdomNC & HNC & HCW & Hmwfs & HNSd).
    destruct Hlive as [Hlive1 Hlive2].
    have Hcs0 : ∃ c0 cs0, cs = c0 :: cs0.
    { have := Hpos _ _ _ HRg. have := HRwf _ _ _ HRg. destruct cs; [simpl; lia|eauto]. }
    destruct Hcs0 as (c0 & cs0 & Hcs).
    destruct (Hrows0 0%nat c0 ltac:(by rewrite Hcs)) as (rest0 & v0 & Hrow0).
    rewrite shift_loc_0_nat in Hrow0.
    (* The group is live. *)
    have Hgρ : g ∈ dom ρ.
    { destruct (Hlive1 _ _ _ c0 Hrow0 ltac:(set_solver)) as (g' & m' & cs' & Hg' & HR' & Hc').
      destruct (decide (g' = g)) as [->|Hne]; [done|]. exfalso.
      apply (Hdisj _ _ _ _ _ _ Hne HR' HRg c0); [done|rewrite Hcs; set_solver]. }
    apply elem_of_dom in Hgρ as [fv Hfv].
    (* The group has no write in flight. *)
    have HgCW : (fst <$> CW) !! g = None.
    { destruct ((fst <$> CW) !! g) as [k|] eqn:Hk; [|done]. exfalso.
      have Hrow' := Hlive2 g k m cs Hk HRg 0%nat c0 ltac:(by rewrite Hcs).
      rewrite shift_loc_0_nat in Hrow'.
      have Heq := row_has_same _ _ _ _ _ _ Hnd Hrow' Hrow0 ltac:(set_solver).
      apply inl_loc_inj in Heq.
      apply lookup_fmap_Some in Hk as ([k' G] & <- & HkCW). simpl in Heq.
      apply (Hcwd g (k', G) m cs HkCW HRg 0%nat 0%nat);
        [rewrite length_fmap Hcs /=; lia|rewrite Hcs /=; lia|].
      by rewrite /= !shift_loc_0_nat Heq. }
    have Hends : ∀ (i : nat) c rest v, cs !! i = Some c → 𝛼 !! inl (l +ₗ i) = Some (c :: rest, v) →
      v.1 = RSt 0.
    { intros i c rest v Hc Hk. eapply (row_end_rst 𝛼 R ρ NC NS (fst <$> CW)); [done..| |done|done].
      intros g' e m' cs' j He HR' Hj Heq. apply inl_loc_inj in Heq.
      apply lookup_fmap_Some in He as ([k' G] & <- & HkCW).
      apply (Hcwd g' (k', G) m' cs' HkCW HR' i j); [rewrite length_fmap; by eapply lookup_lt_Some|done|done]. }
    iMod (bheap_untethers with "H● Hls")
      as (𝛼' vs) "([%Hlen [%Hphi [%Hvs [%Hcells %Hsame]]]] & H● & Hvs & Hus)".
    have Hvs' : ∀ (i : nat) v, vs !! i = Some v → v.1 = RSt 0.
    { intros i v Hv. destruct (lookup_lt_is_Some_2 cs i) as [c Hc];
        [rewrite -Hlen; by eapply lookup_lt_Some|].
      destruct (Hvs i c v Hc Hv) as [rest Hrow].
      by eapply Hends. }
    have Hfin : cell_final 𝛼 <$> cs = snd <$> vs.
    { apply list_eq. intros i. rewrite !list_lookup_fmap.
      destruct (cs !! i) as [c|] eqn:Hc; destruct (vs !! i) as [v|] eqn:Hv; rewrite ?Hv; simpl; try done.
      - destruct (Hvs i c v Hc Hv) as [rest Hrow]. rewrite /cell_final.
        erewrite row_of_spec; [|done|done|set_solver]. by destruct v.
      - apply lookup_lt_Some in Hc. apply lookup_ge_None in Hv. lia.
      - apply lookup_ge_None in Hc. apply lookup_lt_Some in Hv. lia. }
    destruct (Hdec g fv m cs Hfv HRg) as (v & _ & Hd).
    iModIntro. iExists (snd <$> vs), v.
    iSplitR "Hvs Hus"; last iSplitL "Hvs"; [|..|iSplit].
    - iExists 𝛼', M. rewrite Hphi. iFrame "H● Hbank Entries".
      iSplit; [done|]. iSplit; [done|]. iExists R, ρ, NC, NS, CW.
      iFrame "Hreg Hdyn Hnc Hns Hcw HR HNS Hcwe Hρ". iPureIntro. split; [done|split].
      + intros k cs' v' c Hk Hc. destruct (Hcells k cs' v' c Hk Hc) as (k' & cs'' & Hk' & Hc').
        by eapply Hlive1.
      + intros g' k m' cs' Hk HR' i c Hc.
        destruct (Hlive2 g' k m' cs' Hk HR' i c Hc) as (rest & v' & Hrow & Hcr).
        exists rest, v'. split; [|done]. rewrite Hsame //. intros j Hj Heq.
        apply lookup_fmap_Some in Hk as ([k' G] & <- & HkCW).
        apply (Hcwd g' (k', G) m' cs' HkCW HR' j i);
          [by rewrite length_fmap|by eapply lookup_lt_Some|by rewrite Heq].
    - rewrite heap_mapsto_fbytes_bytes /heap_mapsto_fbytes !big_sepL_fmap.
      iApply (big_sepL_impl with "Hvs"). iIntros "!>" (i [ls b] Hv) "H".
      have /= Hls := Hvs' i _ Hv. by subst.
    - by rewrite -Hfin.
    - iFrame "Hg". rewrite big_sepL2_fmap_r. iApply (big_sepL2_impl with "Hus").
      iIntros "!>" (i c [ls b] Hc Hv) "H". have /= Hls := Hvs' i _ Hv. by subst.
  Qed.

  Lemma untethered_rows 𝛼 cs bs :
    bheap 𝛼 -∗ ([∗ list] c; b ∈ cs; bs, ∃ u, bunt u c (RSt 0, b)) -∗
    ⌜∀ (i : nat) c b, cs !! i = Some c → bs !! i = Some b →
       ∃ u rest, 𝛼 !! inr u = Some (c :: rest, (RSt 0, b))⌝.
  Proof.
    iInduction cs as [|c cs] "IH" forall (bs); iIntros "H● Hus";
      destruct bs as [|b bs]; try by iDestruct (big_sepL2_length with "Hus") as %?.
    iDestruct "Hus" as "[[%u Hu] Hus]". iDestruct (fheap_funt with "H● Hu") as %[rest Hrow].
    iDestruct ("IH" with "H● Hus") as %Hrest. iPureIntro.
    intros [|i] c' b' Hc Hb; simpl in Hc, Hb.
    - injection Hc as <-. injection Hb as <-. eauto.
    - eauto.
  Qed.

  (** Writing the bytes of plain untethered rows. *)
  Lemma bheap_write_unts 𝛼 cs (bs bs' : list abyte) fbs :
    length bs' = length cs → (∀ fb, fb ∈ fbs → ∃ x, fb = inr x) →
    bheap 𝛼 -∗ ([∗ list] c; b ∈ cs; bs, ∃ u, bunt u c (RSt 0, b)) -∗ bcells cs fbs ==∗ ∃ 𝛼',
      ⌜(∀ l, 𝛼' !! inl l = 𝛼 !! inl l) ∧
       (∀ k cs' v c, 𝛼' !! k = Some (cs', v) → c ∈ cs' →
          ∃ k' cs'' v', 𝛼 !! k' = Some (cs'', v') ∧ c ∈ cs'')⌝ ∗
      bheap 𝛼' ∗ ([∗ list] c; b ∈ cs; bs', ∃ u, bunt u c (RSt 0, b)) ∗
      bcells cs ((λ b, inr (RSt 0, b)) <$> bs').
  Proof.
    revert 𝛼 bs bs' fbs. induction cs as [|c cs IH]; intros 𝛼 bs bs' fbs Hlen Hpl;
      iIntros "H● Hus Hcs"; destruct bs' as [|b' bs']; simpl in Hlen; try lia;
      destruct bs as [|b bs]; try (by iDestruct (big_sepL2_length with "Hus") as %?);
      destruct fbs as [|fb fbs]; rewrite /bcells /=; try by iDestruct "Hcs" as "[]".
    { iModIntro. iExists 𝛼. iFrame "H●". iSplit; [|by iSplit]. iPureIntro.
      split; [done|]. intros k cs' v c Hk Hc. eauto. }
    iDestruct "Hus" as "[[%u Hu] Hus]". iDestruct "Hcs" as "[Hc Hcs]".
    iDestruct (fheap_no_dupes with "H●") as %Hnd.
    iDestruct (fheap_funt with "H● Hu") as %[rest Hrow].
    destruct (Hpl fb ltac:(set_solver)) as [x ->].
    iDestruct (fheap_fpt with "H● Hc") as %Hp.
    destruct (row_single loc positive bval 𝛼 (inr u) c rest (RSt 0, b) x Hnd Hrow Hp) as [-> <-].
    iMod (fcmap_write_unt loc positive bval _ _ u c [] _ (RSt 0, b') (inr c)
      with "H● Hu Hc") as "(H● & Hu & Hc)"; [done..|].
    iMod (IH _ bs bs' fbs with "H● Hus Hcs") as (𝛼') "([%Hinl %Hcells] & H● & Hus & Hcs)";
      [lia|set_solver|].
    iModIntro. iExists 𝛼'. iFrame "H● Hus Hcs Hc Hu". iPureIntro. split.
    - intros l. rewrite Hinl lookup_insert_ne //.
    - intros k cs' v c' Hk Hc'. destruct (Hcells k cs' v c' Hk Hc') as (k' & cs'' & v' & Hk' & Hc'').
      destruct (decide (k' = inr u)) as [->|Hne].
      + rewrite lookup_insert in Hk'. injection Hk' as <- <-. eauto.
      + rewrite lookup_insert_ne // in Hk'. eauto.
  Qed.

  (** Writing the bytes of an untethered group without cells. *)
  Lemma bytes_ctx_untethered_write σB g m cs bs bs' :
    decode_value m bs' = decode_value m bs →
    bytes_ctx σB -∗ untethered g m cs bs -∗ gnocell g ==∗ bytes_ctx σB ∗ untethered g m cs bs'.
  Proof.
    iIntros (Hdec') "(%𝛼 & %M & %Hr & %Hwf & H● & Hbank & Entries & Cells) [#Hg Hus] #Hnc'".
    iDestruct "Cells" as (R ρ NC NS CW) "(Hreg & Hdyn & Hnc & Hns & Hcw & [%Hcwf %Hlive] & #HR & #HNS & Hcwe & Hρ)".
    iDestruct (greg_lookup with "Hreg Hg") as %HRg.
    iDestruct (gnocell_lookup with "Hnc Hnc'") as %HgNC.
    iDestruct (fheap_no_dupes with "H●") as %Hnd.
    iDestruct (cells_decode with "H● Hρ []") as %Hdec; [by iPureIntro|].
    iDestruct (big_sepL2_length with "Hus") as %Hlenbs.
    iDestruct (untethered_rows with "H● Hus") as %Hurows.
    destruct Hcwf as (HRwf & HdomR & Hrefs & Hdisj & Hpos & HdomNC & HNC & HCW & Hmwfs & HNSd).
    destruct Hlive as [Hlive1 Hlive2].
    have Hcs0 : ∃ c0 cs0 b0 bs0, cs = c0 :: cs0 ∧ bs = b0 :: bs0.
    { have := Hpos _ _ _ HRg. have := HRwf _ _ _ HRg.
      intros H1 H2. destruct cs as [|c0 cs0], bs as [|b0 bs0]; simpl in *; try lia. by eexists _, _, _, _. }
    destruct Hcs0 as (c0 & cs0 & b0 & bs0 & Hcs & Hbs).
    destruct (Hurows 0%nat c0 b0) as (u0 & rest0 & Hrow0); [by rewrite Hcs|by rewrite Hbs|].
    have Hgρ : g ∈ dom ρ.
    { destruct (Hlive1 _ _ _ c0 Hrow0 ltac:(set_solver)) as (g' & m' & cs' & Hg' & HR' & Hc').
      destruct (decide (g' = g)) as [->|Hne]; [done|]. exfalso.
      apply (Hdisj _ _ _ _ _ _ Hne HR' HRg c0); [done|rewrite Hcs; set_solver]. }
    apply elem_of_dom in Hgρ as [fv Hfv].
    have HgCW : (fst <$> CW) !! g = None.
    { destruct ((fst <$> CW) !! g) as [k|] eqn:Hk; [|done]. exfalso.
      have Hrow' := Hlive2 g k m cs Hk HRg 0%nat c0 ltac:(by rewrite Hcs).
      by have := row_has_same _ _ _ _ _ _ Hnd Hrow' Hrow0 ltac:(set_solver). }
    destruct (Hdec g fv m cs Hfv HRg) as (v & Herase & Hd).
    have Hfin : cell_final 𝛼 <$> cs = bs.
    { apply list_eq. intros i. rewrite !list_lookup_fmap.
      destruct (cs !! i) as [c|] eqn:Hc; destruct (bs !! i) as [b|] eqn:Hb; simpl; try done.
      - destruct (Hurows i c b Hc Hb) as (u & rest & Hrow). rewrite /cell_final.
        erewrite row_of_spec; [|done|done|set_solver]. done.
      - apply lookup_lt_Some in Hc. apply lookup_ge_None in Hb. lia.
      - apply lookup_ge_None in Hc. apply lookup_lt_Some in Hb. lia. }
    rewrite Hfin in Hd. rewrite Hd in Hdec'.
    have Hnocells := HNC g fv Hfv HgNC.
    have Hfv' := fval_erase_nocells _ _ _ Hnocells Herase. subst fv.
    iDestruct (big_sepM_delete with "Hρ") as "[(%m' & %cs' & %fbs & (%HR' & %Hrep & %Hls & %Hns) & Hcs) Hρ]"; [done|].
    rewrite HRg in HR'. injection HR' as <- <-.
    have Hpl : ∀ fb, fb ∈ fbs → ∃ x, fb = inr x.
    { intros fb Hfb. have Hst : fb_strip fb ∈ fb_strip <$> fbs by apply elem_of_list_fmap_1.
      destruct (frepr_plain_of_nocells _ _ _ _ Hrep Hnocells _ Hst) as [b Hb].
      destruct fb as [c|x]; [done|eauto]. }
    have Hlen' : length bs' = length cs.
    { rewrite (decode_value_length _ _ _ Hdec') Hlenbs. symmetry. by eapply decode_value_length. }
    iMod (bheap_write_unts with "H● Hus Hcs") as (𝛼') "([%Hinl %Hcells] & H● & Hus & Hcs)"; [done..|].
    have Hphi : bphi 𝛼' = bphi 𝛼.
    { apply (map_eq (M:=gmap loc)). intros l. by rewrite !phi_lookup Hinl. }
    iModIntro. iSplitR "Hus"; last by iFrame "Hg".
    iExists 𝛼', M. rewrite Hphi. iFrame "H● Hbank Entries".
    iSplit; [done|]. iSplit; [done|]. iExists R, ρ, NC, NS, CW.
    iFrame "Hreg Hdyn Hnc Hns Hcw HR HNS Hcwe". iSplit.
    { iPureIntro. split; [done|split].
      - intros k cs' v' c Hk Hc. destruct (Hcells k cs' v' c Hk Hc) as (k' & cs'' & v'' & Hk' & Hc').
        by eapply Hlive1.
      - intros g' k m' cs' Hk HR' i c Hc.
        destruct (Hlive2 g' k m' cs' Hk HR' i c Hc) as (rest & v' & Hrow & Hcr).
        exists rest, v'. by rewrite Hinl. }
    iApply (big_sepM_delete _ _ g with "[Hcs $Hρ]"); [done|].
    iExists m, cs, ((λ b, inr (RSt 0, b)) <$> bs'). iFrame "Hcs". iPureIntro. split_and!.
    - done.
    - have -> : fb_strip <$> ((λ b, inr (RSt 0, b)) <$> bs') = inr <$> bs'.
      { rewrite -list_fmap_compose. apply list_fmap_ext. by intros. }
      by apply frepr_plain.
    - intros i ls b. rewrite list_lookup_fmap. destruct (bs' !! i); simpl; intros Heq;
        simplify_eq. by rewrite /cw_ls HgCW.
    - intros g' o Hk. destruct (Hns g' o Hk) as (m' & cs' & HR' & Hsl). exfalso.
      have Hlen1 := HRwf _ _ _ HR'. have Hpos1 := Hpos _ _ _ HR'.
      destruct cs' as [|c' cs'']; [simpl in *; lia|].
      have Hx : (fb_strip <$> fbs) !! (o + 0)%nat = Some (inl c').
      { by eapply list_slice_lookup_eq; [exact Hsl|]. }
      rewrite list_lookup_fmap in Hx. destruct (fbs !! (o + 0)%nat) as [fb|] eqn:Hfb; [|done].
      destruct (Hpl fb) as [x ->]; [by eapply elem_of_list_lookup_2|]. by destruct x.
  Qed.

  Lemma bytes_ctx_pcell_retether_eq E σB l g m cs bs :
    ↑naN ⊆ E →
    bytes_ctx σB -∗ untethered g m cs bs -∗ l ↦b bs ={E}=∗ bytes_ctx σB ∗ loc_side l g m cs.
  Proof.
    iIntros (?) "(%𝛼 & %M & %Hr & %Hwf & H● & Hbank & Entries & Cells) [#Hg Hus] Hl".
    iDestruct "Cells" as (R ρ NC NS CW) "(Hreg & Hdyn & Hnc & Hns & Hcw & [%Hcwf %Hlive] & #HR & #HNS & Hcwe & Hρ)".
    iDestruct (big_sepL2_length with "Hus") as %Hlen.
    rewrite heap_mapsto_fbytes_bytes.
    iMod (cwentries_disj_fbytes with "Hreg Hcwe Hl") as "(%Hcwd & Hreg & Hcwe & Hl)"; [done|].
    iMod (bheap_retethers _ l cs ((λ b, (RSt 0, b)) <$> bs) with "H● [Hl] [Hus]")
      as (𝛼') "([%Hphi [%Hcells %Hsame]] & H● & Hls)".
    { rewrite /heap_mapsto_fbytes !big_sepL_fmap. done. }
    { by rewrite big_sepL2_fmap_r. }
    iModIntro. iSplitR "Hls"; last by iFrame "Hg Hls".
    iExists 𝛼', M. rewrite Hphi. iFrame "H● Hbank Entries".
    iSplit; [done|]. iSplit; [done|]. iExists R, ρ, NC, NS, CW.
    iFrame "Hreg Hdyn Hnc Hns Hcw HR HNS Hcwe Hρ". iPureIntro. destruct Hlive as [Hlive1 Hlive2].
    split; [done|split].
    - intros k cs' v c Hk Hc. destruct (Hcells k cs' v c Hk Hc) as (k' & cs'' & Hk' & Hc').
      by eapply Hlive1.
    - intros g' k m' cs' Hk HR' i c Hc.
      destruct (Hlive2 g' k m' cs' Hk HR' i c Hc) as (rest & v' & Hrow & Hcr).
      exists rest, v'. split; [|done]. rewrite Hsame //. intros j Hj Heq.
      apply lookup_fmap_Some in Hk as ([k' G] & <- & HkCW).
      apply (Hcwd g' (k', G) m' cs' HkCW HR' j i);
        [rewrite length_fmap; lia|by eapply lookup_lt_Some|by rewrite Heq].
  Qed.

  (** Retethering a moved group at [l], with bytes [bs'] that decode to the same value. The
      bytes may change only for a group without cells. *)
  Lemma bytes_ctx_pcell_retether E σB l g m cs bs bs' :
    ↑naN ⊆ E → decode_value m bs' = decode_value m bs →
    bytes_ctx σB -∗ untethered g m cs bs -∗ l ↦b bs' -∗ (⌜bs' = bs⌝ ∨ gnocell g) ={E}=∗
      bytes_ctx σB ∗ loc_side l g m cs.
  Proof.
    iIntros (? Hdec) "Hctx Hu Hl [->|#Hnc]".
    - by iApply (bytes_ctx_pcell_retether_eq with "Hctx Hu Hl").
    - iMod (bytes_ctx_untethered_write with "Hctx Hu Hnc") as "[Hctx Hu]"; [done|].
      by iApply (bytes_ctx_pcell_retether_eq with "Hctx Hu Hl").
  Qed.

  (** ** Values of groups, and fancy bytes of plain values and of cells *)
  Lemma brepr_plain m bs v : decode_value m bs = Some v → ⊢ brepr m (inr <$> bs) (fv_lift v).
  Proof.
    iIntros (Hd). iExists ∅. rewrite big_sepM_empty. iSplit; [|done]. iPureIntro.
    by apply frepr_plain.
  Qed.

  Lemma brepr_cell g m cs : greg g m cs -∗ brepr m (inl <$> cs) (FVCell g).
  Proof.
    iIntros "#Hg". iExists {[g := (m, cs)]}. rewrite big_sepM_singleton. iFrame "Hg".
    iPureIntro. apply frepr_cell. by rewrite lookup_singleton.
  Qed.

  Lemma brepr_cell_inv g m m' fbs cs :
    brepr m fbs (FVCell g) -∗ greg g m' cs -∗ ⌜m' = m ∧ fbs = inl <$> cs⌝.
  Proof.
    iIntros "(%R & %Hrep & #HR) #Hg". inversion Hrep as [m0 g0 cs0 Hg0| m0 bs v Hd Hv| |];
      subst.
    - iDestruct (big_sepM_lookup with "HR") as "Hg'"; [done|].
      iDestruct (greg_agree with "Hg Hg'") as %[-> ->]. done.
    - by destruct v.
  Qed.

  Lemma untethered_final 𝛼 cs bs :
    cells_no_dupes loc positive bval 𝛼 → length cs = length bs →
    (∀ (i : nat) c b, cs !! i = Some c → bs !! i = Some b →
       ∃ u rest, 𝛼 !! inr u = Some (c :: rest, (RSt 0, b))) →
    cell_final 𝛼 <$> cs = bs.
  Proof.
    intros Hnd Hlen Hurows. apply list_eq. intros i. rewrite list_lookup_fmap.
    destruct (cs !! i) as [c|] eqn:Hc; destruct (bs !! i) as [b|] eqn:Hb; simpl; try done.
    - destruct (Hurows i c b Hc Hb) as (u & rest & Hrow). rewrite /cell_final.
      erewrite row_of_spec; [|done|done|set_solver]. done.
    - apply lookup_lt_Some in Hc. apply lookup_ge_None in Hb. lia.
    - apply lookup_ge_None in Hc. apply lookup_lt_Some in Hb. lia.
  Qed.

  (** The bytes of a group in transit decode to the erasure of its fancy value. *)
  Lemma bytes_ctx_untethered_val σB g m cs bs fv :
    bytes_ctx σB -∗ untethered g m cs bs -∗ gdyn g fv -∗
    ⌜∃ v, decode_value m bs = Some v ∧ (fv_cells fv = [] → fv = fv_lift v)⌝.
  Proof.
    iIntros "(%𝛼 & %M & %Hr & %Hwf & H● & Hbank & Entries & Cells) [#Hg Hus] Hgd".
    iDestruct "Cells" as (R ρ NC NS CW) "(Hreg & Hdyn & Hnc & Hns & Hcw & [%Hcwf %Hlive] & #HR & #HNS & Hcwe & Hρ)".
    iDestruct (greg_lookup with "Hreg Hg") as %HRg.
    iDestruct (gdyn_lookup with "Hdyn Hgd") as %Hfv.
    iDestruct (fheap_no_dupes with "H●") as %Hnd.
    iDestruct (cells_decode with "H● Hρ []") as %Hdec; [by iPureIntro|].
    iDestruct (big_sepL2_length with "Hus") as %Hlenbs.
    iDestruct (untethered_rows with "H● Hus") as %Hurows. iPureIntro.
    destruct (Hdec g fv m cs Hfv HRg) as (v & Herase & Hd).
    rewrite (untethered_final 𝛼 cs bs Hnd Hlenbs Hurows) in Hd.
    exists v. split; [done|]. intros Hc. by eapply fval_erase_nocells.
  Qed.

  (** Setting the value of a group without cells in transit. *)
  Lemma bytes_ctx_untethered_set σB g m cs bs bs' fv v' :
    decode_value m bs' = Some v' →
    bytes_ctx σB -∗ untethered g m cs bs -∗ gnocell g -∗ gdyn g fv ==∗
      bytes_ctx σB ∗ untethered g m cs bs' ∗ gdyn g (fv_lift v').
  Proof.
    iIntros (Hdec') "(%𝛼 & %M & %Hr & %Hwf & H● & Hbank & Entries & Cells) [#Hg Hus] #Hnc' Hgd".
    iDestruct "Cells" as (R ρ NC NS CW) "(Hreg & Hdyn & Hnc & Hns & Hcw & [%Hcwf %Hlive] & #HR & #HNS & Hcwe & Hρ)".
    iDestruct (greg_lookup with "Hreg Hg") as %HRg.
    iDestruct (gnocell_lookup with "Hnc Hnc'") as %HgNC.
    iDestruct (gdyn_lookup with "Hdyn Hgd") as %Hfv.
    iDestruct (fheap_no_dupes with "H●") as %Hnd.
    iDestruct (big_sepL2_length with "Hus") as %Hlenbs.
    iDestruct (untethered_rows with "H● Hus") as %Hurows.
    destruct Hcwf as (HRwf & HdomR & Hrefs & Hdisj & Hpos & HdomNC & HNC & HCW & Hmwfs & HNSd).
    destruct Hlive as [Hlive1 Hlive2].
    have Hcs0 : ∃ c0 cs0 b0 bs0, cs = c0 :: cs0 ∧ bs = b0 :: bs0.
    { have := Hpos _ _ _ HRg. have := HRwf _ _ _ HRg.
      intros H1 H2. destruct cs as [|c0 cs0], bs as [|b0 bs0]; simpl in *; try lia.
      by eexists _, _, _, _. }
    destruct Hcs0 as (c0 & cs0 & b0 & bs0 & Hcs & Hbs).
    destruct (Hurows 0%nat c0 b0) as (u0 & rest0 & Hrow0); [by rewrite Hcs|by rewrite Hbs|].
    have HgCW : (fst <$> CW) !! g = None.
    { destruct ((fst <$> CW) !! g) as [k|] eqn:Hk; [|done]. exfalso.
      have Hrow' := Hlive2 g k m cs Hk HRg 0%nat c0 ltac:(by rewrite Hcs).
      by have := row_has_same _ _ _ _ _ _ Hnd Hrow' Hrow0 ltac:(set_solver). }
    have Hnocells := HNC g fv Hfv HgNC.
    iDestruct (big_sepM_delete with "Hρ") as "[(%m' & %cs' & %fbs & (%HR' & %Hrep & %Hls & %Hns) & Hcs) Hρ]"; [done|].
    rewrite HRg in HR'. injection HR' as <- <-.
    have Hpl : ∀ fb, fb ∈ fbs → ∃ x, fb = inr x.
    { intros fb Hfb. have Hst : fb_strip fb ∈ fb_strip <$> fbs by apply elem_of_list_fmap_1.
      destruct (frepr_plain_of_nocells _ _ _ _ Hrep Hnocells _ Hst) as [b Hb].
      destruct fb as [c|x]; [done|eauto]. }
    have Hlen' : length bs' = length cs.
    { rewrite (decode_value_length _ _ _ Hdec'). symmetry. by eapply HRwf. }
    iMod (bheap_write_unts with "H● Hus Hcs") as (𝛼') "([%Hinl %Hcells] & H● & Hus & Hcs)"; [done..|].
    iMod (ghost_map_update (fv_lift v') with "Hdyn Hgd") as "[Hdyn Hgd]".
    have Hphi : bphi 𝛼' = bphi 𝛼.
    { apply (map_eq (M:=gmap loc)). intros l. by rewrite !phi_lookup Hinl. }
    have Hgdom : g ∈ dom ρ by apply elem_of_dom_2 in Hfv.
    have Hdom' : dom (<[g := fv_lift v']> ρ) = dom ρ.
    { rewrite dom_insert_L. set_solver. }
    iModIntro. iSplitR "Hus Hgd"; last by iFrame "Hg Hgd".
    iExists 𝛼', M. rewrite Hphi. iFrame "H● Hbank Entries".
    iSplit; [done|]. iSplit; [done|]. iExists R, (<[g := fv_lift v']> ρ), NC, NS, CW.
    iFrame "Hreg Hdyn Hnc Hns Hcw HR HNS Hcwe". iSplit.
    { iPureIntro. split; [split_and!|split].
      - done.
      - by rewrite Hdom'.
      - intros g' fv'' Hg' g'' Hg''. destruct (decide (g' = g)) as [->|Hne].
        + rewrite lookup_insert in Hg'. injection Hg' as <-. rewrite fv_cells_lift in Hg''. by apply not_elem_of_nil in Hg''.
        + rewrite lookup_insert_ne // in Hg'. rewrite Hdom'. by eapply Hrefs.
      - done.
      - done.
      - done.
      - intros g' fv'' Hg' HNC'. destruct (decide (g' = g)) as [->|Hne].
        + rewrite lookup_insert in Hg'. injection Hg' as <-. apply fv_cells_lift.
        + rewrite lookup_insert_ne // in Hg'. by eapply HNC.
      - intros g' k Hk. destruct (HCW g' k Hk) as [Hρg' Hrest]. split; [|done].
        rewrite lookup_insert_ne //. intros ->. by rewrite HgCW in Hk.
      - done.
      - done.
      - intros k cs' v'' c Hk Hc. destruct (Hcells k cs' v'' c Hk Hc) as (k' & cs'' & v3 & Hk' & Hc').
        rewrite Hdom'. by eapply Hlive1.
      - intros g' k m' cs' Hk HR' i c Hc.
        destruct (Hlive2 g' k m' cs' Hk HR' i c Hc) as (rest & v'' & Hrow & Hcr).
        exists rest, v''. by rewrite Hinl. }
    iApply big_sepM_insert_delete. iFrame "Hρ".
    iExists m, cs, ((λ b, inr (RSt 0, b)) <$> bs'). iFrame "Hcs". iPureIntro. split_and!.
    - done.
    - have -> : fb_strip <$> ((λ b, inr (RSt 0, b)) <$> bs') = inr <$> bs'.
      { rewrite -list_fmap_compose. apply list_fmap_ext. by intros. }
      by apply frepr_plain.
    - intros i ls b. rewrite list_lookup_fmap. destruct (bs' !! i); simpl; intros Heq;
        simplify_eq. by rewrite /cw_ls HgCW.
    - intros g' o Hk. destruct (Hns g' o Hk) as (m' & cs' & HR' & Hsl). exfalso.
      have Hlen1 := HRwf _ _ _ HR'. have Hpos1 := Hpos _ _ _ HR'.
      destruct cs' as [|c' cs'']; [simpl in *; lia|].
      have Hx : (fb_strip <$> fbs) !! (o + 0)%nat = Some (inl c').
      { by eapply list_slice_lookup_eq; [exact Hsl|]. }
      rewrite list_lookup_fmap in Hx. destruct (fbs !! (o + 0)%nat) as [fb|] eqn:Hfb; [|done].
      destruct (Hpl fb) as [x ->]; [by eapply elem_of_list_lookup_2|]. by destruct x.
  Qed.

  Lemma brepr_plain_inv m fbs v :
    brepr m fbs (fv_lift v) -∗ ⌜∃ bs, fbs = inr <$> bs ∧ decode_value m bs = Some v⌝.
  Proof.
    iIntros "(%R & %Hrep & _)". iPureIntro.
    have Hpl := frepr_plain_of_nocells _ _ _ _ Hrep (fv_cells_lift v).
    destruct (frepr_decode R ∅ (λ _, Uninit) m fbs (fv_lift v) Hrep) as (v' & Her & Hd).
    { intros g m' cs Hg. rewrite fv_cells_lift in Hg. by apply not_elem_of_nil in Hg. }
    have Heq := fval_erase_det _ _ _ _ (fval_erase_lift ∅ v) Her. subst v'.
    exists (fin_bytes (λ _, Uninit) fbs). split; [|done].
    apply list_eq. intros i. rewrite /fin_bytes !list_lookup_fmap.
    destruct (fbs !! i) as [fb|] eqn:Hfb; [|done].
    destruct (Hpl fb ltac:(by eapply elem_of_list_lookup_2)) as [b ->]. done.
  Qed.

  (** The contents of a byte-cell are determined. *)
  Lemma fine_pair_inr_det 𝛼 c fb1 fb2 :
    cells_no_dupes loc positive bval 𝛼 → 𝛼_fine_pair loc positive bval 𝛼 (inr c) fb1 →
    𝛼_fine_pair loc positive bval 𝛼 (inr c) fb2 → fb1 = fb2.
  Proof.
    intros Hnd H1 H2.
    destruct fb1 as [c1|v1], fb2 as [c2|v2]; simpl in H1, H2.
    - destruct H1 as (k1 & cs1 & w1 & Hk1 & Hp1), H2 as (k2 & cs2 & w2 & Hk2 & Hp2).
      have Hp1' := Hp1. have Hp2' := Hp2.
      apply list_has_pair_elem_of in Hp1' as [Hc1 _]. apply list_has_pair_elem_of in Hp2' as [Hc2 _].
      have Hr1 := row_of_spec loc positive bval 𝛼 k1 cs1 w1 c Hnd Hk1 Hc1.
      have Hr2 := row_of_spec loc positive bval 𝛼 k2 cs2 w2 c Hnd Hk2 Hc2.
      specialize (Hr1 Pos.eq_dec). specialize (Hr2 Pos.eq_dec). rewrite Hr1 in Hr2. injection Hr2 as <- <-.
      have Hnd1 := row_nodup _ _ _ _ _ _ _ Hnd Hk1.
      apply list_has_pair_destruct in Hp1 as (a & b & Ha).
      apply list_has_pair_destruct in Hp2 as (a' & b' & Ha').
      have L1 : cs1 !! length a = Some c by rewrite Ha lookup_app_r // Nat.sub_diag.
      have L2 : cs1 !! length a' = Some c by rewrite Ha' lookup_app_r // Nat.sub_diag.
      have Heq := NoDup_lookup _ _ _ _ Hnd1 L1 L2.
      have M1 : cs1 !! S (length a) = Some c1.
      { rewrite Ha lookup_app_r; [|lia]. by replace (S (length a) - length a)%nat with 1%nat by lia. }
      have M2 : cs1 !! S (length a') = Some c2.
      { rewrite Ha' lookup_app_r; [|lia]. by replace (S (length a') - length a')%nat with 1%nat by lia. }
      rewrite Heq M2 in M1. by injection M1 as ->.
    - exfalso. destruct H1 as (k1 & cs1 & w1 & Hk1 & Hp1), H2 as (k2 & cs2 & Hk2 & Hend).
      have Hp1' := Hp1. apply list_has_pair_elem_of in Hp1' as [Hc1 _].
      have Hc2 := Hend. apply list_ends_with_elem_of in Hc2.
      have Hr1 := row_of_spec loc positive bval 𝛼 k1 cs1 w1 c Hnd Hk1 Hc1.
      have Hr2 := row_of_spec loc positive bval 𝛼 k2 cs2 v2 c Hnd Hk2 Hc2.
      specialize (Hr1 Pos.eq_dec). specialize (Hr2 Pos.eq_dec). rewrite Hr1 in Hr2. injection Hr2 as <- <-.
      apply list_ends_with_snoc in Hend as [pre ->].
      exact (has_pair_last_contra loc positive bval pre c _ ltac:(by eapply row_nodup) Hp1).
    - exfalso. destruct H2 as (k1 & cs1 & w1 & Hk1 & Hp1), H1 as (k2 & cs2 & Hk2 & Hend).
      have Hp1' := Hp1. apply list_has_pair_elem_of in Hp1' as [Hc1 _].
      have Hc2 := Hend. apply list_ends_with_elem_of in Hc2.
      have Hr1 := row_of_spec loc positive bval 𝛼 k1 cs1 w1 c Hnd Hk1 Hc1.
      have Hr2 := row_of_spec loc positive bval 𝛼 k2 cs2 v1 c Hnd Hk2 Hc2.
      specialize (Hr1 Pos.eq_dec). specialize (Hr2 Pos.eq_dec). rewrite Hr1 in Hr2. injection Hr2 as <- <-.
      apply list_ends_with_snoc in Hend as [pre ->].
      exact (has_pair_last_contra loc positive bval pre c _ ltac:(by eapply row_nodup) Hp1).
    - destruct H1 as (k1 & cs1 & Hk1 & Hend1), H2 as (k2 & cs2 & Hk2 & Hend2).
      apply list_ends_with_elem_of in Hend1. apply list_ends_with_elem_of in Hend2.
      have Hr1 := row_of_spec loc positive bval 𝛼 k1 cs1 v1 c Hnd Hk1 Hend1.
      have Hr2 := row_of_spec loc positive bval 𝛼 k2 cs2 v2 c Hnd Hk2 Hend2.
      specialize (Hr1 Pos.eq_dec). specialize (Hr2 Pos.eq_dec). rewrite Hr1 in Hr2. by injection Hr2 as _ ->.
  Qed.

  (** ** Accesses through cells

  An access through a cell reads or writes a _plain sub-value_ (without cells) of the fancy
  value of a group [g] ([fv_sub m fv o' m' fvs] with [fv_cells fvs = []]). The group [g] may
  be nested in a live group: it sits at the offset [o] inside a _root_ group [g0] ([gpath g0
  g o]), whose location side is at [l0]; the access is at [l0 +ₗ (o + o')]. The accessor
  needs the permission of [g] and (a guard of) the location side of [g0]. *)

  Lemma loc_side_row_has 𝛼 l g m cs :
    bheap 𝛼 -∗ loc_side l g m cs -∗ ⌜∀ (i : nat) c, cs !! i = Some c → row_has 𝛼 (l +ₗ i) c⌝.
  Proof.
    iIntros "H● Hls". iDestruct (loc_side_rows with "H● Hls") as %H. iPureIntro.
    intros i c Hc. destruct (H i c Hc) as (rest & v & Hrow). exists (c :: rest), v.
    split; [done|]. set_solver.
  Qed.

  Lemma row_last_snoc (k : loc + untether_id) pre (c : positive) :
    row_last loc positive k (pre ++ [c]) = Some (inr c).
  Proof. by rewrite /row_last list_last_c_app_singleton. Qed.

  (** The row of a location [l'] through the byte-cell of a root [g0] at the position of a
      plain sub-value of a group [g] nested in [g0] ends with the byte-cell of [g]. *)
  Lemma sub_row_end 𝛼 R ρ NC NS (CW : gmap positive cwkey) g0 m0 cs0 g o m cs fv o' m' fvs
      (j : nat) c0 l' :
    cells_no_dupes loc positive bval 𝛼 → cells_wf R ρ NC NS CW → cells_live 𝛼 R ρ CW →
    gfacts 𝛼 R NS CW ρ →
    R !! g0 = Some (m0, cs0) → nest_path NS g0 g o → R !! g = Some (m, cs) → ρ !! g = Some fv →
    fv_sub m fv o' m' fvs → fv_cells fvs = [] → (j < mty_size m')%nat →
    cs0 !! (o + (o' + j))%nat = Some c0 → row_has 𝛼 l' c0 →
    ∃ c pre ls b, cs !! (o' + j)%nat = Some c ∧ 𝛼 !! inl l' = Some (pre ++ [c], (ls, b)) ∧
      ls = cw_ls CW g (o' + j)%nat.
  Proof.
    intros Hnd Hwf Hlive Hf HR0 Hp HR Hfv Hsub Hc Hj Hc0 Hrow0. have Hwf' := Hwf.
    destruct Hwf' as (HRwf & HdomR & Hrefs & Hdisj & Hpos & HdomNC & HNC & HCW & Hmwf & HNSd).
    have Hg0 : g0 ∈ dom ρ.
    { destruct Hrow0 as (cells & v & Hk & Hc0').
      eapply cell_live; [done|done|exact Hk|exact Hc0'|exact HR0|by eapply elem_of_list_lookup_2]. }
    destruct (nest_path_rows _ _ _ _ _ _ _ _ _ Hnd Hwf Hlive Hf Hp Hg0 _ _ _ _ HR0 HR)
      as (_ & Hb & Hrows).
    destruct (Hf g fv Hfv) as (m1 & cs1 & fbs & Hgc & Hlen & Hfp).
    destruct Hgc as (HR1 & Hrep & Hls & _). rewrite HR in HR1. injection HR1 as <- <-.
    have Hmw := Hmwf _ _ _ HR.
    have Hb' := fv_sub_bound _ _ _ _ _ Hsub Hmw.
    have Hlenm := HRwf _ _ _ HR.
    destruct (frepr_sub_plain _ _ _ _ _ _ _ HRwf Hrep Hsub Hmw Hc) as (bs & v & Hsl & Hd & _).
    have Hlenbs := decode_value_length _ _ _ Hd.
    destruct (lookup_lt_is_Some_2 cs (o' + j)%nat) as [c Hcj]; [lia|].
    destruct (lookup_lt_is_Some_2 bs j) as [b Hbj]; [lia|].
    have Hx : (fb_strip <$> fbs) !! (o' + j)%nat = Some (inr b).
    { eapply list_slice_lookup_eq; [exact Hsl|]. by rewrite list_lookup_fmap Hbj. }
    rewrite list_lookup_fmap in Hx.
    destruct (fbs !! (o' + j)%nat) as [fb|] eqn:Hfb; [|done].
    destruct fb as [c'|[ls b']]; simpl in Hx; [done|]. injection Hx as ->.
    have Hrow : row_has 𝛼 l' c by apply (Hrows (o' + j)%nat c0 c l').
    destruct (row_has_end 𝛼 l' c (ls, b) Hnd Hrow (Hfp _ _ _ Hcj Hfb)) as [pre Hpre].
    exists c, pre, ls, b. split_and!; [done|done|]. by eapply Hls.
  Qed.

  (** The reads of a plain sub-value. *)
  Lemma cells_ctx_read_sub 𝛼 l0 g0 m0 cs0 g o m cs fv o' m' fvs :
    fv_sub m fv o' m' fvs → fv_cells fvs = [] →
    bheap 𝛼 -∗ cells_ctx 𝛼 -∗ loc_side l0 g0 m0 cs0 -∗ gpath g0 g o -∗ greg g m cs -∗
    gdyn g fv -∗
    ⌜∃ bs v, mem_range (.= RSt 0) (bphi 𝛼) (l0 +ₗ (o + o')%nat) bs ∧ length bs = mty_size m' ∧
       decode_value m' bs = Some v ∧ fvs = fv_lift v ∧ (o + o' + mty_size m' ≤ length cs0)%nat⌝.
  Proof.
    iIntros (Hsub Hc) "H● Cells Hls #Hp #Hg Hgd".
    iDestruct "Cells" as (R ρ NC NS CW) "(Hreg & Hdyn & Hnc & Hns & Hcw & [%Hcwf %Hlive] & #HR & #HNS & Hcwe & Hρ)".
    iDestruct "Hls" as "[#Hg0 Hls]".
    iDestruct (greg_lookup with "Hreg Hg0") as %HR0.
    iDestruct (greg_lookup with "Hreg Hg") as %HRg.
    iDestruct (gdyn_lookup with "Hdyn Hgd") as %Hfv.
    iDestruct (gpath_lookup with "Hns Hp") as %Hpath.
    iAssert ⌜CW !! g = None⌝%I as %HgCW.
    { destruct (CW !! g) as [e|] eqn:He; [|done].
      iDestruct (big_sepM_lookup with "Hcwe") as "(%m1 & %cs1 & _ & Hgd' & _)"; [done|].
      iDestruct (gdyn_excl with "Hgd Hgd'") as "[]". }
    have HgCW' : (fst <$> CW) !! g = None by rewrite lookup_fmap HgCW.
    iDestruct (fheap_no_dupes with "H●") as %Hnd.
    iDestruct (loc_side_row_has with "H● [$Hg0 $Hls]") as %Hheads.
    iDestruct (gcontents_edges with "H● Hρ") as %Hf.
    iPureIntro.
    destruct (sub_rows 𝛼 R ρ NC NS (fst <$> CW) l0 g0 m0 cs0 g o m cs fv o' m' fvs Hnd Hcwf Hlive
      Hf HR0 Hheads Hpath HRg Hfv Hsub Hc)
      as (fbs & bs & v & (_ & _ & Hls & _) & _ & _ & Hb0 & Hb' & _ & Hd & -> & _ & Hends).
    have Hlenbs := decode_value_length _ _ _ Hd.
    exists bs, v. split_and!; [|done|done|done|lia].
    apply mem_range_lookup. intros j b Hb.
    have Hj : (j < mty_size m')%nat by rewrite -Hlenbs; eapply lookup_lt_Some.
    destruct (lookup_lt_is_Some_2 cs (o' + j)%nat) as [c Hcj]; [lia|].
    destruct (Hends j c Hj Hcj) as (ls & b' & pre & Hfb & Hb'' & Hrow).
    rewrite Hb in Hb''. injection Hb'' as <-.
    exists ls. rewrite shift_loc_assoc_nat phi_lookup Hrow /=. split; [done|].
    rewrite (Hls _ _ _ Hfb) /cw_ls HgCW'. done.
  Qed.

  Lemma bytes_ctx_cell_lookup_sub σB l0 g0 m0 cs0 g o m cs fv o' m' fvs :
    fv_sub m fv o' m' fvs → fv_cells fvs = [] →
    bytes_ctx σB -∗ loc_side l0 g0 m0 cs0 -∗ gpath g0 g o -∗ greg g m cs -∗ gdyn g fv -∗
    ⌜∃ bs v, mem_range is_reading σB (l0 +ₗ (o + o')%nat) bs ∧ length bs = mty_size m' ∧
       decode_value m' bs = Some v ∧ fvs = fv_lift v⌝.
  Proof.
    iIntros (Hsub Hc) "(%𝛼 & %M & %Hr & %Hwf & H● & Hbank & Entries & Cells) Hls Hp Hg Hgd".
    iDestruct (cells_ctx_read_sub with "H● Cells Hls Hp Hg Hgd") as %(bs & v & Hrd & Hlen & Hd & Hfv & _);
      [done..|].
    iPureIntro. exists bs, v. split_and!; [|done|done|done].
    eapply bank_rel_reading; [done|]. eapply mem_range_impl; [|done]. intros ? ->. by eexists.
  Qed.

  Lemma big_sepL_slice {A} (Φ : nat → A → iProp Σ) (l : list A) o n :
    (o + n ≤ length l)%nat →
    ([∗ list] i ↦ x ∈ l, Φ i x) -∗ [∗ list] j ↦ x ∈ list_slice o n l, Φ (o + j)%nat x.
  Proof.
    iIntros (Hn) "H". rewrite -{1}(take_drop o l) big_sepL_app. iDestruct "H" as "[_ H]".
    rewrite length_take Nat.min_l; [|lia].
    rewrite /list_slice -{1}(take_drop n (drop o l)) big_sepL_app. iDestruct "H" as "[H _]".
    done.
  Qed.

  (** A non-atomic read of a plain sub-value through a cell whose location side (of the
      root) and permission are guarded: the guard is deposited in the bank of guarded reads,
      with the edges of the range and the permission as the witness. *)
  Lemma bytes_ctx_cell_read_begin_guarded E σB l0 g0 m0 cs0 g o m cs fv o' m' fvs G P d :
    ↑naN ⊆ E → fv_sub m fv o' m' fvs → fv_cells fvs = [] →
    £(2*d) -∗ (G &&{↑naN; d}&&> P) -∗
    □ (P -∗ (loc_side l0 g0 m0 cs0 ∗ gdyn g fv) ∗ (loc_side l0 g0 m0 cs0 -∗ gdyn g fv -∗ P)) -∗
    gpath g0 g o -∗ greg g m cs -∗ G -∗
    bytes_ctx σB ={E}=∗ ∃ i bs v,
      ⌜decode_value m' bs = Some v ∧ fvs = fv_lift v⌝ ∗
      ⌜mem_range is_reading σB (l0 +ₗ (o + o')%nat) bs⌝ ∗
      bytes_ctx (mem_alter ls_inc (l0 +ₗ (o + o')%nat) (mty_size m') σB) ∗
      bread_tok i (l0 +ₗ (o + o')%nat) bs G.
  Proof.
    iIntros (? Hsub Hc) "[£1 £2] #Guard #HP #Hp #Hg G (%𝛼 & %M & %Hr & %Hwf & H● & Hbank & Entries & Cells)".
    replace (d + 0)%nat with d by lia.
    iMod (guards_open_later with "Guard G") as "Open"; [done|].
    iMod (lc_fupd_elim_laterN with "£1 Open") as ">[P Back]".
    iDestruct ("HP" with "P") as "[[Hls Hgd] Ret]".
    iDestruct (cells_ctx_read_sub with "H● Cells Hls Hp Hg Hgd")
      as %(bs & v & Hrd0 & Hlen & Hd & Hfv & Hb); [done..|].
    iMod ("Back" with "(Ret Hls Hgd)") as "G".
    set l := (l0 +ₗ (o + o')%nat).
    have Hrd : mem_range is_reading (bphi 𝛼) l bs.
    { eapply mem_range_impl; [|done]. intros ? ->. by eexists. }
    set i := fresh (dom M).
    have Hi : M !! i = None by apply not_elem_of_dom, is_fresh.
    iMod (own_update _ _ (gmap_view_auth (DfracOwn 1)
        ((λ e, to_agree (bbank_elt e.1 e.2)) <$> <[i := ((l, bs), G)]> M) ⋅
      gmap_view_frag i (DfracOwn 1) (to_agree (bbank_elt (l, bs) G))) with "Hbank")
      as "[Hbank Tok]".
    { rewrite fmap_insert. apply gmap_view_alloc; [|done..]. by rewrite lookup_fmap Hi. }
    iModIntro. iExists i, bs, v. iFrame "Tok". iSplit; [done|].
    iSplit; [iPureIntro; by eapply bank_rel_reading|].
    iExists 𝛼, (<[i := ((l, bs), G)]> M). iFrame "H● Hbank Cells". iSplit.
    { iPureIntro. rewrite -Hlen fmap_insert. apply bank_rel_add; [done| |done].
      by rewrite lookup_fmap Hi. }
    iSplit. { iPureIntro. rewrite fmap_insert. by apply bank_wf_add. }
    rewrite big_sepM_insert //. iFrame "Entries G". iExists P, d. iFrame "£2 Guard".
    iIntros "!> P". iDestruct ("HP" with "P") as "[[[#Hg0 Hls] Hgd] _]".
    iExists (inl <$> list_slice (o + o') (mty_size m') cs0).
    have Hlsl : length (list_slice (o + o') (mty_size m') cs0) = mty_size m'.
    { rewrite /list_slice length_take length_drop. lia. }
    iSplit; [by rewrite /= length_fmap Hlsl|].
    iSplitL "Hls".
    { rewrite big_sepL_fmap. iDestruct (big_sepL_slice _ _ (o + o') (mty_size m') with "Hls") as "Hls";
        [done|].
      iApply (big_sepL_impl with "Hls"). iIntros "!>" (j c _) "H". by rewrite /l shift_loc_assoc_nat. }
    iRight. iExists l0, g0, m0, cs0, g, o, m, cs, fv, o', m', fvs. iFrame "Hg0 Hp Hg Hgd".
    iPureIntro. split_and!; [done| |done|done|by rewrite length_fmap].
    by rewrite length_fmap Hlsl.
  Qed.


  (** ** Writes through cells *)

  (** An entry of the bank of guarded reads does not overlap the range of [n] bytes at [lw]
      whose rows end with byte-cells of a group [gw] whose permission the writer has. *)
  Lemma bbank_entry_disj_sub E 𝛼 R ρ NC NS (CW : gmap positive cwkey) e lw gw mw csw fvw n :
    ↑naN ⊆ E →
    cells_no_dupes loc positive bval 𝛼 → cells_wf R ρ NC NS CW → cells_live 𝛼 R ρ CW →
    gfacts 𝛼 R NS CW ρ → R !! gw = Some (mw, csw) →
    (∀ j : nat, (j < n)%nat → ∃ pre c v, c ∈ csw ∧ 𝛼 !! inl (lw +ₗ j) = Some (pre ++ [c], v)) →
    bheap 𝛼 -∗ ghost_map_auth heap_greg_name 1 R -∗ ghost_map_auth heap_gdyn_name 1 ρ -∗
    ghost_map_auth heap_gnest_name 1 NS -∗ gdyn gw fvw -∗ bbank_entry e ={E}=∗
      ⌜∀ j : nat, (j < n)%nat → ¬ in_rng e.1.1 (length e.1.2) (lw +ₗ j)⌝ ∗
      bheap 𝛼 ∗ ghost_map_auth heap_greg_name 1 R ∗ ghost_map_auth heap_gdyn_name 1 ρ ∗
      ghost_map_auth heap_gnest_name 1 NS ∗ gdyn gw fvw ∗ bbank_entry e.
  Proof.
    iIntros (? Hnd Hwf Hlive Hf HRw Hrows) "H● Hreg Hdyn Hns Hgd Entry".
    destruct (decide (Exists (λ j : nat, in_rng e.1.1 (length e.1.2) (lw +ₗ j)) (seq 0 n)))
      as [Hex|Hnex]; last first.
    { iModIntro. iFrame. iPureIntro. intros j Hj Hin. apply Hnex.
      apply Exists_exists. exists j. split; [apply elem_of_seq; lia|done]. }
    apply Exists_exists in Hex as (j & Hj%elem_of_seq & (k & Hk & Heq)).
    iDestruct "Entry" as "(G & %P & %d & £ & #Guard & #HP)".
    iMod (guards_open_later with "Guard G") as "Open"; [done|].
    iMod (lc_fupd_elim_laterN with "£ Open") as ">[P _]".
    iDestruct ("HP" with "P") as (cvs Hlen') "[Pt Wit]".
    destruct (lookup_lt_is_Some_2 cvs k) as [cv Hcv]; [lia|].
    iDestruct (big_sepL_lookup with "Pt") as "Pt"; [done|].
    iEval (rewrite -Heq) in "Pt".
    iDestruct (fheap_fpt with "H● Pt") as %Hp.
    destruct (Hrows j ltac:(lia)) as (pre & c & v & Hc & Hrow).
    rewrite /𝛼_fine_pair Hrow in Hp. destruct cv as [c0|v']; last first.
    { exfalso. injection Hp as Hp _. by destruct pre. }
    iDestruct "Wit" as "[%Hall|Wit]".
    { by destruct (Forall_lookup_1 _ _ _ _ Hall Hcv) as [? [=]]. }
    iDestruct "Wit" as (l0 g0 m0 cs0 g o m cs fv o' m' fvs) "(#Hg0 & #Hpath & #Hg & Hgd' & %Hpure)".
    destruct Hpure as (Hl & Hcvs & Hsub & Hplain & Hlenm).
    destruct (decide (g = gw)) as [->|Hne].
    { iDestruct (gdyn_excl with "Hgd Hgd'") as "[]". }
    iDestruct (greg_lookup with "Hreg Hg0") as %HR0.
    iDestruct (greg_lookup with "Hreg Hg") as %HRg.
    iDestruct (gdyn_lookup with "Hdyn Hgd'") as %Hfv.
    iDestruct (gpath_lookup with "Hns Hpath") as %Hnp.
    exfalso.
    have Hc0 : cs0 !! (o + (o' + k))%nat = Some c0.
    { move: Hcv. rewrite Hcvs list_lookup_fmap lookup_list_slice decide_True; [|lia].
      rewrite Nat.add_assoc. destruct (cs0 !! (o + o' + k)%nat); simpl; [|done]. by intros [= ->]. }
    have Hrow0 : row_has 𝛼 (lw +ₗ j) c0.
    { destruct pre as [|c1 pre]; simpl in Hp; [subst; exists [c], v; split; [done|set_solver]|].
      subst c1. exists (c0 :: pre ++ [c]), v. split; [done|set_solver]. }
    destruct (sub_row_end 𝛼 R ρ NC NS CW g0 m0 cs0 g o m cs fv o' m' fvs k c0 (lw +ₗ j)
      Hnd Hwf Hlive Hf HR0 Hnp HRg Hfv Hsub Hplain ltac:(lia) Hc0 Hrow0)
      as (c' & pre' & ls & b & Hc' & Hrow' & _).
    rewrite Hrow in Hrow'. injection Hrow' as Hpre _.
    apply app_inj_tail in Hpre as [_ <-].
    destruct Hwf as (_ & _ & _ & Hdisj & _).
    apply (Hdisj g gw m cs mw csw Hne HRg HRw c); [by eapply elem_of_list_lookup_2|done].
  Qed.

  Lemma bbank_disj_sub E 𝛼 R ρ NC NS (CW : gmap positive cwkey) M lw gw mw csw fvw n :
    ↑naN ⊆ E →
    cells_no_dupes loc positive bval 𝛼 → cells_wf R ρ NC NS CW → cells_live 𝛼 R ρ CW →
    gfacts 𝛼 R NS CW ρ → R !! gw = Some (mw, csw) →
    (∀ j : nat, (j < n)%nat → ∃ pre c v, c ∈ csw ∧ 𝛼 !! inl (lw +ₗ j) = Some (pre ++ [c], v)) →
    bheap 𝛼 -∗ ghost_map_auth heap_greg_name 1 R -∗ ghost_map_auth heap_gdyn_name 1 ρ -∗
    ghost_map_auth heap_gnest_name 1 NS -∗ gdyn gw fvw -∗
    ([∗ map] e ∈ M, bbank_entry e) ={E}=∗
      ⌜bank_disj (fst <$> M) lw n⌝ ∗
      bheap 𝛼 ∗ ghost_map_auth heap_greg_name 1 R ∗ ghost_map_auth heap_gdyn_name 1 ρ ∗
      ghost_map_auth heap_gnest_name 1 NS ∗ gdyn gw fvw ∗ ([∗ map] e ∈ M, bbank_entry e).
  Proof.
    iIntros (? Hnd Hwf Hlive Hf HRw Hrows).
    iInduction M as [|i e M Hi] "IH" using map_ind; iIntros "H● Hreg Hdyn Hns Hgd Entries".
    { iFrame. iPureIntro. intros i e. by rewrite fmap_empty lookup_empty. }
    rewrite big_sepM_insert //. iDestruct "Entries" as "[Entry Entries]".
    iMod (bbank_entry_disj_sub with "H● Hreg Hdyn Hns Hgd Entry")
      as "(%H1 & H● & Hreg & Hdyn & Hns & Hgd & Entry)"; [done..|].
    iMod ("IH" with "H● Hreg Hdyn Hns Hgd Entries") as "(%H2 & $ & $ & $ & $ & $ & Entries)". iFrame.
    iPureIntro. intros i' e'. rewrite fmap_insert. destruct (decide (i = i')) as [<-|].
    - rewrite lookup_insert. intros [= <-]. intros j Hj. by apply H1.
    - rewrite lookup_insert_ne //. apply H2.
  Qed.

  (** No entry of the bank of guarded reads overlaps a range that is being written. *)
  Lemma bank_disj_wst (Rb : gmap nat (loc * list abyte)) σA l bs :
    bank_wf Rb σA → mem_range (.= WSt) σA l bs → bank_disj Rb l (length bs).
  Proof.
    intros Hwf Hw i e Hi j Hj (k & Hk & Heq).
    destruct (mem_range_lookup_1 _ _ _ _ j Hw Hj) as (ls & b & Hl & Hls & _).
    destruct (mem_range_lookup_1 _ _ _ _ k (Hwf i e Hi) Hk) as (ls' & b' & Hl' & Hrd & _).
    rewrite -Heq Hl in Hl'. injection Hl' as <- <-. simpl in Hls. subst ls.
    by destruct Hrd as [? [=]].
  Qed.

  (** Writing the values at the ends of the rows of [l], [l +ₗ 1], ..., which are the
      contents (from the offset [o]) of the byte-cells [cs]. *)
  Lemma bheap_write_ends 𝛼 l cs (fbs : list (positive + bval)) (o : nat) (bs' : list abyte) st' :
    (o + length bs' ≤ length cs)%nat →
    (∀ (j : nat) c, (j < length bs')%nat → cs !! (o + j)%nat = Some c →
       ∃ pre v, fbs !! (o + j)%nat = Some (inr v) ∧ 𝛼 !! inl (l +ₗ j) = Some (pre ++ [c], v)) →
    bheap 𝛼 -∗ bcells cs fbs ==∗ ∃ 𝛼',
      ⌜bphi 𝛼' = mem_set st' l bs' (bphi 𝛼) ∧
       (∀ k cs1 v1, 𝛼 !! k = Some (cs1, v1) → ∃ v1', 𝛼' !! k = Some (cs1, v1')) ∧
       (∀ k cs1 v1, 𝛼' !! k = Some (cs1, v1) → ∃ v1', 𝛼 !! k = Some (cs1, v1')) ∧
       (∀ k, (∀ i : nat, (i < length bs')%nat → k ≠ inl (l +ₗ i)) → 𝛼' !! k = 𝛼 !! k)⌝ ∗
      bheap 𝛼' ∗ bcells cs (list_inserts o ((λ b, inr (st', b)) <$> bs') fbs).
  Proof.
    revert 𝛼 l o fbs. induction bs' as [|b' bs' IH]; intros 𝛼 l o fbs Hb Hends;
      iIntros "H● Hcs".
    { iModIntro. iExists 𝛼. iFrame. iPureIntro. split_and!; eauto. }
    simpl in Hb.
    destruct (lookup_lt_is_Some_2 cs o) as [c Hc]; [lia|].
    destruct (Hends 0%nat c) as (pre & v & Hfb & Hrow); [simpl; lia|by rewrite Nat.add_0_r|].
    rewrite Nat.add_0_r in Hfb. rewrite shift_loc_0_nat in Hrow.
    iMod (IH 𝛼 (l +ₗ 1) (S o) fbs with "H● Hcs")
      as (𝛼1) "([%Hphi [%Hfw [%Hbw %Hsame]]] & H● & Hcs)".
    { lia. }
    { intros j c' Hj Hc'. destruct (Hends (S j) c') as (pre' & v' & Hfb' & Hrow').
      { simpl. lia. } { by replace (o + S j)%nat with (S o + j)%nat by lia. }
      exists pre', v'. replace (S o + j)%nat with (o + S j)%nat by lia. rewrite -shift_loc_S. done. }
    have Hrow1 : 𝛼1 !! inl l = Some (pre ++ [c], v).
    { rewrite Hsame //. intros i _ Heq. apply inl_loc_inj in Heq. by apply (shift_loc_ne_S l i). }
    have Hfb1 : list_inserts (S o) ((λ b, inr (st', b)) <$> bs') fbs !! o = Some (inr v).
    { rewrite list_lookup_inserts_lt //. lia. }
    rewrite /bcells. iDestruct (big_sepL2_insert_acc with "Hcs") as "[Hc Hcs]"; [done..|].
    iMod (fcmap_write_loc loc positive bval _ _ l (pre ++ [c]) v (st', b') (inr c) Hrow1
      with "H● Hc") as "[H● Hc]"; [apply row_last_snoc|].
    iDestruct ("Hcs" with "Hc") as "Hcs". rewrite list_insert_id //.
    iModIntro. iExists _. iFrame "H● Hcs". iPureIntro. split_and!.
    - by rewrite phi_insert_loc Hphi.
    - intros k cs1 v1 Hk. destruct (Hfw k cs1 v1 Hk) as [v1' Hk1].
      destruct (decide (k = inl l)) as [->|Hne].
      + rewrite Hrow1 in Hk1. injection Hk1 as <- <-. rewrite lookup_insert. eauto.
      + rewrite lookup_insert_ne //. eauto.
    - intros k cs1 v1 Hk. destruct (decide (k = inl l)) as [->|Hne].
      + rewrite lookup_insert in Hk. injection Hk as <- <-. eapply Hbw. done.
      + rewrite lookup_insert_ne // in Hk. eauto.
    - intros k Hk. rewrite lookup_insert_ne; last first.
      { intros Heq. apply (Hk 0%nat); [simpl; lia|]. by rewrite shift_loc_0_nat Heq. }
      apply Hsame. intros i Hi. rewrite -shift_loc_S. apply Hk. simpl. lia.
  Qed.

  Lemma fb_strip_inserts (fbs : list (positive + bval)) o (bs : list abyte) st :
    fb_strip <$> list_inserts o ((λ b, inr (st, b)) <$> bs) fbs =
    list_inserts o (inr <$> bs) (fb_strip <$> fbs).
  Proof.
    revert o. induction bs as [|b bs IH]; intros o; [done|].
    by rewrite /= list_fmap_insert IH.
  Qed.

  Lemma list_inserts_same {A} (l : list A) o (e : list A) :
    (∀ (j : nat) x, e !! j = Some x → l !! (o + j)%nat = Some x) → list_inserts o e l = l.
  Proof.
    intros H. apply list_eq. intros i.
    destruct (decide (o ≤ i < o + length e)%nat) as [Hi|Hi].
    - destruct (lookup_lt_is_Some_2 e (i - o)%nat) as [x Hx]; [lia|].
      have Hl := H _ _ Hx. replace (o + (i - o))%nat with i in Hl by lia.
      rewrite list_lookup_inserts; [by rewrite Hx Hl|lia|by eapply lookup_lt_Some].
    - destruct (decide (i < o)%nat).
      + by rewrite list_lookup_inserts_lt.
      + rewrite list_lookup_inserts_ge //. lia.
  Qed.

  (** A plain range and a range of cells in fancy bytes are disjoint. *)
  Lemma slices_disj {A B} (l : list (A + B)) o1 (xs : list B) o2 (ys : list A) :
    list_slice o1 (length xs) l = inr <$> xs → list_slice o2 (length ys) l = inl <$> ys →
    xs ≠ [] → ys ≠ [] → (o1 + length xs ≤ o2 ∨ o2 + length ys ≤ o1)%nat.
  Proof.
    intros H1 H2 Hx Hy. destruct (decide (o1 + length xs ≤ o2 ∨ o2 + length ys ≤ o1)%nat)
      as [|Hn]; [done|]. exfalso.
    have Hlx : length xs ≠ 0%nat by intros ?%nil_length_inv.
    have Hly : length ys ≠ 0%nat by intros ?%nil_length_inv.
    remember (o1 `max` o2)%nat as i eqn:Hi.
    destruct (lookup_lt_is_Some_2 xs (i - o1)%nat) as [x Hxi]; [lia|].
    destruct (lookup_lt_is_Some_2 ys (i - o2)%nat) as [y Hyi]; [lia|].
    have E1 := list_slice_lookup_eq _ _ _ _ (i - o1)%nat (inr x) H1 ltac:(by rewrite list_lookup_fmap Hxi).
    have E2 := list_slice_lookup_eq _ _ _ _ (i - o2)%nat (inl y) H2 ltac:(by rewrite list_lookup_fmap Hyi).
    replace (o1 + (i - o1))%nat with i in E1 by lia.
    replace (o2 + (i - o2))%nat with i in E2 by lia. congruence.
  Qed.

  Lemma gcontents_cw_eq R NS CW1 CW2 g fv :
    CW1 !! g = CW2 !! g → gcontents R NS CW1 g fv -∗ gcontents R NS CW2 g fv.
  Proof.
    iIntros (Heq) "(%m & %cs & %fbs & (%HR & %Hrep & %Hls & %Hns) & Hcs)". iExists m, cs, fbs. iFrame.
    iPureIntro. split_and!; [done|done| |done]. intros i ls b Hi. by rewrite (Hls i ls b Hi) /cw_ls Heq.
  Qed.

  (** The first phase of a non-atomic write of a plain sub-value through a cell whose
      location side (of the root) is only guarded: the permission and the guard go to the
      bank of cell writes, and the written bytes are marked [WSt]. *)
  Lemma bytes_ctx_cell_write_begin E σB l0 g0 m0 cs0 g o m cs fv o' m' fvs G P d :
    ↑naN ⊆ E → fv_sub m fv o' m' fvs → fv_cells fvs = [] →
    £(2*d) -∗ (G &&{↑naN; d}&&> P) -∗
    □ (P -∗ loc_side l0 g0 m0 cs0 ∗ (loc_side l0 g0 m0 cs0 -∗ P)) -∗
    gpath g0 g o -∗ greg g m cs -∗ G -∗ gdyn g fv -∗ bytes_ctx σB ={E}=∗ ∃ bs,
      ⌜mem_range (.= RSt 0) σB (l0 +ₗ (o + o')%nat) bs ∧ length bs = mty_size m'⌝ ∗
      bytes_ctx (mem_alter (λ _, WSt) (l0 +ₗ (o + o')%nat) (mty_size m') σB) ∗
      cwrite_tok g (l0 +ₗ o, o', mty_size m', fv) G.
  Proof.
    iIntros (? Hsub Hplain) "[£1 £2] #Guard #HP #Hp #Hg G Hgd (%𝛼 & %M & %Hr & %Hwf & H● & Hbank & Entries & Cells)".
    replace (d + 0)%nat with d by lia.
    iDestruct "Cells" as (R ρ NC NS CW) "(Hreg & Hdyn & Hnc & Hns & Hcw & [%Hcwf %Hlive] & #HR & #HNS & Hcwe & Hρ)".
    iMod (guards_open_later with "Guard G") as "Open"; [done|].
    iMod (lc_fupd_elim_laterN with "£1 Open") as ">[P Back]".
    iDestruct ("HP" with "P") as "[Hls Ret]".
    iDestruct (loc_side_row_has with "H● Hls") as %Hheads.
    iDestruct "Hls" as "[#Hg0 Hedges]".
    iMod ("Back" with "(Ret [$Hg0 $Hedges])") as "G".
    iDestruct (greg_lookup with "Hreg Hg0") as %HR0.
    iDestruct (greg_lookup with "Hreg Hg") as %HRg.
    iDestruct (gdyn_lookup with "Hdyn Hgd") as %Hfv.
    iDestruct (gpath_lookup with "Hns Hp") as %Hpath.
    iAssert ⌜CW !! g = None⌝%I as %HgCW.
    { destruct (CW !! g) as [e|] eqn:He; [|done].
      iDestruct (big_sepM_lookup with "Hcwe") as "(%m1 & %cs1 & _ & Hgd' & _)"; [done|].
      iDestruct (gdyn_excl with "Hgd Hgd'") as "[]". }
    have HgCW' : (fst <$> CW) !! g = None by rewrite lookup_fmap HgCW.
    iDestruct (fheap_no_dupes with "H●") as %Hnd.
    iDestruct (gcontents_edges with "H● Hρ") as %Hf.
    destruct (sub_rows 𝛼 R ρ NC NS (fst <$> CW) l0 g0 m0 cs0 g o m cs fv o' m' fvs Hnd Hcwf Hlive
      Hf HR0 Hheads Hpath HRg Hfv Hsub Hplain)
      as (fbs0 & bs & v & _ & Hlen0 & Hfp0 & Hb0 & Hb' & _ & Hd & -> & Hgrows & Hends).
    have Hlenbs := decode_value_length _ _ _ Hd.
    set lw := (l0 +ₗ (o + o')%nat).
    have Hwrows : ∀ j : nat, (j < mty_size m')%nat →
      ∃ pre c v, c ∈ cs ∧ 𝛼 !! inl (lw +ₗ j) = Some (pre ++ [c], v).
    { intros j Hj. destruct (lookup_lt_is_Some_2 cs (o' + j)%nat) as [c Hcj]; [lia|].
      destruct (Hends j c Hj Hcj) as (ls & b & pre & _ & _ & Hrow).
      exists pre, c, (ls, b). split; [by eapply elem_of_list_lookup_2|].
      by rewrite /lw shift_loc_assoc_nat. }
    iMod (bbank_disj_sub with "H● Hreg Hdyn Hns Hgd Entries")
      as "(%Hbd & H● & Hreg & Hdyn & Hns & Hgd & Entries)"; [done..|].
    have Hcwf' := Hcwf.
    destruct Hcwf' as (HRwf & HdomR & Hrefs & Hdisj & Hpos & HdomNC & HNC & HCW & Hmwfs & HNSd).
    destruct Hlive as [Hlive1 Hlive2].
    iDestruct (big_sepM_delete with "Hρ") as "[(%m1 & %cs1 & %fbs & %Hgc & Hcs) Hρ]"; [done|].
    have Hgc' := Hgc. destruct Hgc' as (HR1 & Hrep & Hls & Hns').
    rewrite HRg in HR1. injection HR1 as <- <-.
    iDestruct (bheap_cells with "H● Hcs") as %[Hlenfbs Hfp].
    (* [fbs0] and [fbs] are the same contents. *)
    have Hfbs : fbs0 = fbs.
    { apply list_eq. intros i.
      destruct (cs !! i) as [c|] eqn:Hci.
      - destruct (lookup_lt_is_Some_2 fbs0 i) as [fb0 Hfb0]; [rewrite -Hlen0; by eapply lookup_lt_Some|].
        destruct (lookup_lt_is_Some_2 fbs i) as [fb Hfb]; [rewrite -Hlenfbs; by eapply lookup_lt_Some|].
        rewrite Hfb0 Hfb. f_equal. eapply fine_pair_inr_det; [done|by eapply Hfp0|by eapply Hfp].
      - apply lookup_ge_None in Hci. rewrite !lookup_ge_None_2 //; lia. }
    subst fbs0.
    have Hends' : ∀ (j : nat) c, (j < length bs)%nat → cs !! (o' + j)%nat = Some c →
      ∃ pre v, fbs !! (o' + j)%nat = Some (inr v) ∧ 𝛼 !! inl (lw +ₗ j) = Some (pre ++ [c], v).
    { intros j c Hj Hc. destruct (Hends j c ltac:(lia) Hc) as (ls & b & pre & Hfb & _ & Hrow).
      exists pre, (ls, b). split; [done|]. by rewrite /lw shift_loc_assoc_nat. }
    have Hrst : ∀ (j : nat) b, bs !! j = Some b → fbs !! (o' + j)%nat = Some (inr (RSt 0, b)).
    { intros j b Hb. have Hj : (j < mty_size m')%nat by rewrite -Hlenbs; eapply lookup_lt_Some.
      destruct (lookup_lt_is_Some_2 cs (o' + j)%nat) as [c Hcj]; [lia|].
      destruct (Hends j c Hj Hcj) as (ls & b' & pre & Hfb & Hb2 & _).
      rewrite Hb in Hb2. injection Hb2 as <-. rewrite Hfb (Hls _ _ _ Hfb) /cw_ls HgCW'. done. }
    have Hrd : mem_range (.= RSt 0) (bphi 𝛼) lw bs.
    { apply mem_range_lookup. intros j b Hb.
      have Hj : (j < mty_size m')%nat by rewrite -Hlenbs; eapply lookup_lt_Some.
      destruct (lookup_lt_is_Some_2 cs (o' + j)%nat) as [c Hcj]; [lia|].
      destruct (Hends' j c ltac:(lia) Hcj) as (pre & v' & Hfb & Hrow).
      rewrite (Hrst j b Hb) in Hfb. injection Hfb as <-. exists (RSt 0). by rewrite phi_lookup Hrow. }
    iMod (bheap_write_ends _ lw cs fbs o' bs WSt with "H● Hcs")
      as (𝛼') "([%Hphi [%Hfw [%Hbw %Hsame]]] & H● & Hcs)"; [lia|done|].
    set key : cwkey := (l0 +ₗ o, o', mty_size m', fv).
    iMod (own_update _ _ (gmap_view_auth (DfracOwn 1)
        ((λ e : cwkey * iProp Σ, to_agree (cw_elt e.1 e.2)) <$> <[g := (key, G)]> CW) ⋅
      gmap_view_frag g (DfracOwn 1) (to_agree (cw_elt key G))) with "Hcw")
      as "[Hcw Tok]".
    { rewrite fmap_insert. apply gmap_view_alloc; [|done..]. by rewrite lookup_fmap HgCW. }
    have Hrow_has' : ∀ l' c, row_has 𝛼 l' c → row_has 𝛼' l' c.
    { intros l' c (cells & v1 & Hk & Hc). destruct (Hfw _ _ _ Hk) as [v1' Hk']. by exists cells, v1'. }
    iModIntro. iExists bs. iSplit.
    { iPureIntro. split; [|done]. eapply bank_rel_disj; [done|by rewrite Hlenbs|done]. }
    iFrame "Tok". iExists 𝛼', M. iFrame "H● Hbank Entries".
    iSplit.
    { iPureIntro. rewrite Hphi -(mem_set_alter (λ _, WSt) (RSt 0)) // Hlenbs.
      by apply bank_rel_mem_alter_wst. }
    iSplit.
    { iPureIntro. rewrite Hphi -(mem_set_alter (λ _, WSt) (RSt 0)) //.
      apply bank_wf_mem_alter_disj; [by rewrite Hlenbs|done]. }
    iExists R, ρ, NC, NS, (<[g := (key, G)]> CW).
    iFrame "Hreg Hdyn Hnc Hns Hcw HR HNS". iSplitR.
    { iPureIntro. rewrite fmap_insert. split; [split_and!|split]; try done.
      - intros g' k Hk. destruct (decide (g' = g)) as [->|Hne].
        + rewrite lookup_insert in Hk. injection Hk as <-. split; [done|].
          exists m, cs. split; [done|]. simpl. lia.
        + rewrite lookup_insert_ne // in Hk. by apply HCW.
      - intros k cs1 v1 c Hk Hc. destruct (Hbw k cs1 v1 Hk) as [v1' Hk'].
        by eapply Hlive1.
      - intros g' k m2 cs' Hk HR' i c Hc. destruct (decide (g' = g)) as [->|Hne].
        + rewrite lookup_insert in Hk. injection Hk as <-. rewrite HRg in HR'.
          injection HR' as <- <-. simpl. apply Hrow_has'. rewrite shift_loc_assoc_nat.
          by apply Hgrows.
        + rewrite lookup_insert_ne // in Hk. apply Hrow_has'. by eapply Hlive2. }
    iSplitL "Hcwe G £2 Hgd".
    { rewrite big_sepM_insert //. iFrame "Hcwe". iExists m, cs. iFrame "Hg Hgd G".
      iExists P, d. iFrame "£2 Guard". iIntros "!> P". iDestruct ("HP" with "P") as "[H _]".
      iExists l0, g0, m0, cs0, o. iFrame "H". iPureIntro. split; [done|lia]. }
    rewrite (big_sepM_delete _ ρ g fv) //. iSplitL "Hcs".
    - iExists m, cs, _. iFrame "Hcs". iPureIntro.
      have Hstrip : fb_strip <$> list_inserts o' ((λ b, inr (WSt, b)) <$> bs) fbs = fb_strip <$> fbs.
      { rewrite fb_strip_inserts. apply list_inserts_same. intros j x Hx.
        apply list_lookup_fmap_Some in Hx as (b & Hb & ->).
        by rewrite list_lookup_fmap (Hrst j b Hb). }
      split_and!.
      + done.
      + by rewrite Hstrip.
      + intros i ls b Hi. rewrite /cw_ls fmap_insert lookup_insert /=.
        destruct (decide (o' ≤ i < o' + length bs)%nat) as [Hin|Hout].
        * rewrite list_lookup_inserts in Hi; [|rewrite length_fmap; lia|rewrite -Hlenfbs; lia].
          rewrite list_lookup_fmap in Hi. destruct (bs !! (i - o')%nat); simplify_eq/=.
          rewrite decide_True //. lia.
        * rewrite decide_False; [|lia].
          rewrite list_lookup_inserts_Some in Hi.
          destruct Hi as [[_ Hi]|(Hr2 & _ & _)]; [|rewrite length_fmap in Hr2; lia].
          rewrite (Hls _ _ _ Hi) /cw_ls HgCW'. done.
      + intros g' o'' Hk. rewrite Hstrip. by apply Hns'.
    - iApply (big_sepM_impl with "Hρ"). iIntros "!>" (g' fv' Hg') "H".
      iApply (gcontents_cw_eq with "H"). apply lookup_delete_Some in Hg' as [Hne _].
      rewrite fmap_insert lookup_insert_ne //.
  Qed.


  (** The second phase: the new bytes [bs'] (which decode to [v] at [m']) are written at the
      offset [o'] of [g], and the permission (with the fancy value updated at [o']) and the
      guard come back. *)
  Lemma bytes_ctx_cell_write_end E σB l g m cs fv o' m' fvs G bs' v fvn :
    ↑naN ⊆ E → fv_sub m fv o' m' fvs → fv_cells fvs = [] →
    fv_upd m fv o' m' (fv_lift v) fvn → decode_value m' bs' = Some v →
    greg g m cs -∗ bytes_ctx σB -∗ cwrite_tok g (l, o', mty_size m', fv) G ={E}=∗
      ∃ bs, ⌜mem_range (.= WSt) σB (l +ₗ o') bs ∧ length bs = mty_size m'⌝ ∗
      bytes_ctx (mem_write (l +ₗ o') bs' σB) ∗ gdyn g fvn ∗ ▷ G.
  Proof.
    iIntros (? Hsub Hplain Hupd Hdec) "#Hg (%𝛼 & %M & %Hr & %Hwf & H● & Hbank & Entries & Cells) Tok".
    iDestruct "Cells" as (R ρ NC NS CW) "(Hreg & Hdyn & Hnc & Hns & Hcw & [%Hcwf %Hlive] & #HR & #HNS & Hcwe & Hρ)".
    iDestruct (greg_lookup with "Hreg Hg") as %HRg.
    iDestruct (own_valid_2 with "Hcw Tok") as "#Hvalid".
    rewrite gmap_view_both_validI lookup_fmap. iDestruct "Hvalid" as "(_ & _ & Hvalid)".
    destruct (CW !! g) as [[k G']|] eqn:HgCW; last first.
    { rewrite option_equivI. done. }
    rewrite option_equivI /= agree_equivI prod_equivI /=.
    iDestruct "Hvalid" as "[%Heq HGeq]". simplify_eq.
    iMod (own_update_2 with "Hcw Tok") as "Hcw"; [apply gmap_view_delete|].
    rewrite (big_sepM_delete _ CW g) //.
    iDestruct "Hcwe" as "[(%m1 & %cs1 & #Hg' & Hgd & G & %P & %d & £ & #Guard & #HP) Hcwe]".
    iDestruct (greg_agree with "Hg Hg'") as %[<- <-].
    set key : cwkey := (l, o', mty_size m', fv).
    have Hk : (fst <$> CW) !! g = Some key by rewrite lookup_fmap HgCW.
    iDestruct (fheap_no_dupes with "H●") as %Hnd.
    have Hcwf' := Hcwf.
    destruct Hcwf' as (HRwf & HdomR & Hrefs & Hdisj & Hpos & HdomNC & HNC & HCW & Hmwfs & HNSd).
    destruct Hlive as [Hlive1 Hlive2].
    destruct (HCW g _ Hk) as [Hfv (m2 & cs2 & HR2 & Hbnd)]. simpl in Hfv, Hbnd.
    rewrite HRg in HR2. injection HR2 as <- <-.
    have Hrows0 := Hlive2 g _ m cs Hk HRg. simpl in Hrows0.
    iDestruct (big_sepM_delete with "Hρ") as "[(%m2 & %cs2 & %fbs & %Hgc & Hcs) Hρ]"; [done|].
    destruct Hgc as (HR2 & Hrep & Hls & Hns'). rewrite HRg in HR2. injection HR2 as <- <-.
    iDestruct (bheap_cells with "H● Hcs") as %[Hlenfbs Hfp].
    have Hmw := Hmwfs _ _ _ HRg.
    have Hcslen := HRwf _ _ _ HRg.
    have Hb' := fv_sub_bound _ _ _ _ _ Hsub Hmw.
    destruct (frepr_sub_plain _ _ _ _ _ _ _ HRwf Hrep Hsub Hmw Hplain) as (bs & v0 & Hsl & Hd0 & _).
    have Hlenbs := decode_value_length _ _ _ Hd0.
    have Hlenbs' := decode_value_length _ _ _ Hdec.
    (* The written contents are plain bytes being written, at the ends of their rows. *)
    have Hwst : ∀ (j : nat) b, bs !! j = Some b → fbs !! (o' + j)%nat = Some (inr (WSt, b)).
    { intros j b Hb. have Hj : (j < mty_size m')%nat by rewrite -Hlenbs; eapply lookup_lt_Some.
      have Hx : (fb_strip <$> fbs) !! (o' + j)%nat = Some (inr b).
      { eapply list_slice_lookup_eq; [exact Hsl|]. by rewrite list_lookup_fmap Hb. }
      rewrite list_lookup_fmap in Hx.
      destruct (fbs !! (o' + j)%nat) as [fb|] eqn:Hfb; [|done].
      destruct fb as [c'|[ls b']]; simpl in Hx; [done|]. injection Hx as ->.
      rewrite (Hls _ _ _ Hfb) /cw_ls Hk /= decide_True //. lia. }
    have Hends : ∀ (j : nat) c, (j < length bs')%nat → cs !! (o' + j)%nat = Some c →
      ∃ pre v1, fbs !! (o' + j)%nat = Some (inr v1) ∧
        𝛼 !! inl ((l +ₗ o') +ₗ j) = Some (pre ++ [c], v1).
    { intros j c Hj Hc. destruct (lookup_lt_is_Some_2 bs j) as [b Hb]; [lia|].
      have Hfb := Hwst j b Hb.
      destruct (row_has_end 𝛼 _ c (WSt, b) Hnd (Hrows0 (o' + j)%nat c Hc) (Hfp _ _ _ Hc Hfb))
        as [pre Hpre].
      exists pre, (WSt, b). split; [done|]. by rewrite shift_loc_assoc_nat. }
    have Hrd : mem_range (.= WSt) (bphi 𝛼) (l +ₗ o') bs.
    { apply mem_range_lookup. intros j b Hb.
      have Hj : (j < mty_size m')%nat by rewrite -Hlenbs; eapply lookup_lt_Some.
      destruct (lookup_lt_is_Some_2 cs (o' + j)%nat) as [c Hcj]; [lia|].
      destruct (Hends j c ltac:(lia) Hcj) as (pre & v1 & Hfb & Hrow).
      rewrite (Hwst j b Hb) in Hfb. injection Hfb as <-. exists WSt. by rewrite phi_lookup Hrow. }
    have Hbd := bank_disj_wst _ _ _ _ Hwf Hrd.
    iMod (bheap_write_ends _ (l +ₗ o') cs fbs o' bs' (RSt 0) with "H● Hcs")
      as (𝛼') "([%Hphi [%Hfw [%Hbw %Hsame]]] & H● & Hcs)"; [lia|done|].
    iMod (ghost_map_update fvn with "Hdyn Hgd") as "[Hdyn Hgd]".
    have Hgdom : g ∈ dom ρ by apply elem_of_dom_2 in Hfv.
    have Hdom' : dom (<[g := fvn]> ρ) = dom ρ by rewrite dom_insert_L; set_solver.
    have Hcells_fvn : ∀ g'', g'' ∈ fv_cells fvn → g'' ∈ fv_cells fv.
    { intros g'' Hg''. destruct (fv_cells_upd _ _ _ _ _ _ _ Hupd Hg'') as [?|Hl]; [done|].
      rewrite fv_cells_lift in Hl. by apply not_elem_of_nil in Hl. }
    iModIntro. iExists bs. iSplit.
    { iPureIntro. split; [|done]. eapply bank_rel_disj; [done|done|done]. }
    iFrame "Hgd". iSplitR "G HGeq"; last first.
    { rewrite later_equivI. iNext. by iRewrite "HGeq" in "G". }
    iExists 𝛼', M. iFrame "H● Hbank Entries".
    iSplit.
    { iPureIntro. rewrite Hphi mem_set_write. apply (bank_rel_mem_write _ _ _ _ bs); [lia|done|done]. }
    iSplit.
    { iPureIntro. rewrite Hphi mem_set_write. apply bank_wf_mem_write; [by rewrite Hlenbs' -Hlenbs|done]. }
    iExists R, (<[g := fvn]> ρ), NC, NS, (delete g CW).
    rewrite {1}/cwbank_auth fmap_delete. iFrame "Hreg Hdyn Hnc Hns Hcw HR HNS Hcwe". iSplitR.
    { iPureIntro. rewrite fmap_delete. split; [split_and!|split].
      - done.
      - by rewrite Hdom'.
      - intros g' fv'' Hg' g'' Hg''. destruct (decide (g' = g)) as [->|Hne].
        + rewrite lookup_insert in Hg'. injection Hg' as <-. rewrite Hdom'.
          by eapply Hrefs, Hcells_fvn.
        + rewrite lookup_insert_ne // in Hg'. rewrite Hdom'. by eapply Hrefs.
      - done.
      - done.
      - done.
      - intros g' fv'' Hg' HNC'. destruct (decide (g' = g)) as [->|Hne].
        + rewrite lookup_insert in Hg'. injection Hg' as <-.
          have Hc0 := HNC g fv Hfv HNC'. apply elem_of_nil_inv. intros g'' Hg''.
          have := Hcells_fvn g'' Hg''. rewrite Hc0. apply not_elem_of_nil.
        + rewrite lookup_insert_ne // in Hg'. by eapply HNC.
      - intros g' k' Hk'. apply lookup_delete_Some in Hk' as [Hne Hk'].
        destruct (HCW g' k' Hk') as [Hρg' Hrest]. split; [|done]. by rewrite lookup_insert_ne.
      - done.
      - done.
      - intros k' cs1 v1 c Hk' Hc. destruct (Hbw k' cs1 v1 Hk') as [v1' Hk''].
        rewrite Hdom'. by eapply Hlive1.
      - intros g' k' m2 cs' Hk' HR' i c Hc. apply lookup_delete_Some in Hk' as [Hne Hk'].
        destruct (Hlive2 g' k' m2 cs' Hk' HR' i c Hc) as (cells & v1 & Hrow & Hcr).
        destruct (Hfw _ _ _ Hrow) as [v1' Hrow']. by exists cells, v1'. }
    iApply big_sepM_insert_delete. iSplitL "Hcs".
    - iExists m, cs, _. iFrame "Hcs". iPureIntro. split_and!.
      + done.
      + rewrite fb_strip_inserts. by eapply frepr_upd.
      + intros i ls b Hi. rewrite /cw_ls fmap_delete lookup_delete.
        rewrite list_lookup_inserts_Some in Hi.
        destruct Hi as [[Hout Hi]|(Hin & _ & Hi)].
        * rewrite (Hls _ _ _ Hi) /cw_ls Hk /= decide_False //. rewrite length_fmap in Hout. lia.
        * rewrite list_lookup_fmap in Hi. destruct (bs' !! (i - o')%nat); simplify_eq/=. done.
      + intros g' o'' Hkn. destruct (Hns' g' o'' Hkn) as (m3 & cs3 & HR3 & Hsl3).
        exists m3, cs3. split; [done|]. rewrite fb_strip_inserts.
        destruct bs' as [|b0 bs0]; [done|].
        rewrite list_slice_inserts_out; [done|].
        rewrite length_fmap.
        destruct bs as [|b1 bs1]; [simpl in *; lia|].
        have Hpos3 := Hpos _ _ _ HR3. have Hlen3 := HRwf _ _ _ HR3.
        destruct (slices_disj (fb_strip <$> fbs) o' (b1 :: bs1) o'' cs3) as [?|?];
          [by rewrite Hlenbs|done|done|intros ->; simpl in *; lia|..]; simpl in *; lia.
    - iApply (big_sepM_impl with "Hρ"). iIntros "!>" (g' fv' Hg') "H".
      iApply (gcontents_cw_eq with "H"). apply lookup_delete_Some in Hg' as [Hne _].
      rewrite fmap_delete lookup_delete_ne //.
  Qed.


  (** A group has as many byte-cells as its type has bytes. *)
  Lemma bytes_ctx_greg_length σB g m cs :
    bytes_ctx σB -∗ greg g m cs -∗ ⌜length cs = mty_size m⌝.
  Proof.
    iIntros "(%𝛼 & %M & %Hr & %Hwf & H● & Hbank & Entries & Cells) #Hg".
    iDestruct "Cells" as (R ρ NC NS CW) "(Hreg & _ & _ & _ & _ & [%Hcwf _] & _)".
    iDestruct (greg_lookup with "Hreg Hg") as %HRg. iPureIntro. by eapply (proj1 Hcwf).
  Qed.

  (** ** Nestings

  A group [g] that is a cell of the fancy value of a live group [g0] (at the offset [o]) is
  recorded as nested in [g0]. The record is persistent: while [g0] is live, the contents of
  [g0] at [o] stay the byte-cells of [g] (writes through [g0] only replace plain
  sub-values). *)
  Lemma bytes_ctx_gnest σB g0 m0 cs0 fv0 o m g :
    fv_sub m0 fv0 o m (FVCell g) →
    bytes_ctx σB -∗ greg g0 m0 cs0 -∗ gdyn g0 fv0 ==∗ bytes_ctx σB ∗ gdyn g0 fv0 ∗ gnest g0 g o.
  Proof.
    iIntros (Hsub) "(%𝛼 & %M & %Hr & %Hwf & H● & Hbank & Entries & Cells) #Hg0 Hgd".
    iDestruct "Cells" as (R ρ NC NS CW) "(Hreg & Hdyn & Hnc & Hns & Hcw & [%Hcwf %Hlive] & #HR & #HNS & Hcwe & Hρ)".
    iDestruct (greg_lookup with "Hreg Hg0") as %HR0.
    iDestruct (gdyn_lookup with "Hdyn Hgd") as %Hfv.
    destruct (NS !! (g0, g, o)) as [[]|] eqn:Hk.
    { iDestruct (big_sepM_lookup with "HNS") as "Hn"; [done|]. iModIntro. iFrame "Hgd Hn".
      iExists 𝛼, M. iFrame "H● Hbank Entries". iSplit; [done|]. iSplit; [done|]. iExists R, ρ, NC, NS, CW. iFrame "∗ #". done. }
    have Hcwf' := Hcwf.
    destruct Hcwf' as (HRwf & HdomR & Hrefs & Hdisj & Hpos & HdomNC & HNC & HCW & Hmwfs & HNSd).
    iMod (ghost_map_insert_persist (g0, g, o) () with "Hns") as "[Hns #Hn]"; [done|].
    iModIntro. iFrame "Hgd Hn". iExists 𝛼, M. iFrame "H● Hbank Entries". iSplit; [done|].
    iSplit; [done|]. iExists R, ρ, NC, (<[(g0, g, o) := ()]> NS), CW.
    iFrame "Hreg Hdyn Hnc Hns Hcw HR Hcwe". iSplit.
    { iPureIntro. split; [|done]. split_and!; try done.
      intros k. rewrite dom_insert_L elem_of_union elem_of_singleton. intros [->|Hk'].
      - simpl. by apply elem_of_dom_2 in HR0.
      - by apply HNSd. }
    iSplitR. { rewrite big_sepM_insert //. by iFrame "Hn HNS". }
    iApply (big_sepM_impl with "Hρ"). iIntros "!>" (g' fv' Hg') "(%m1 & %cs1 & %fbs & %Hgc & Hcs)".
    iExists m1, cs1, fbs. iFrame "Hcs". iPureIntro.
    destruct Hgc as (HR1 & Hrep & Hls & Hns'). split_and!; [done|done|done|].
    intros g'' o'' Hk'. rewrite dom_insert_L elem_of_union elem_of_singleton in Hk'.
    destruct Hk' as [[= -> -> ->]|Hk']; [|by apply Hns'].
    rewrite HR0 in HR1. injection HR1 as <- <-. rewrite Hfv in Hg'. injection Hg' as <-.
    destruct (frepr_sub_cell _ _ _ _ _ _ _ HRwf Hrep Hsub (Hmwfs _ _ _ HR0)) as (cs & HRg & Hsl).
    exists m, cs. split; [done|]. by rewrite (HRwf _ _ _ HRg).
  Qed.

End cells.
