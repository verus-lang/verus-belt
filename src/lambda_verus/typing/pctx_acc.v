(** * Accessing the hole of a place context below unique borrows

  A place context may contain [PUniq κ K] steps: the hole is in the referent of a unique
  borrow, inside the node of [UniqLty]. Across such a step the ownership of the plugged
  place does not split as a separating conjunction ([ltype_own_plug] needs
  [PctxNoUniq]): the referent is held by the borrow at [κ] (a compound place [cpd_own], or
  a leaf [uniq_body]), which has to be opened. This file gives the generalized split, an
  _access_ to the hole of any context ([pctx_acc]), from the [Owned m] interpretation of the
  plugged place (the root of an owned place is in [Owned 1] mode, see [place_own.v]):

  - the hole is in the mode [pctx_kind K (Owned m) x]: [Owned] with the number of owned
    pointers since the last [PUniq] (or since the root), or [Uniq κ ξi] if the context ends
    with [PUniq κ PHole] (the hole is the whole referent of the innermost borrow);
  - the enclosing borrows are opened one after the other ([cpd_rebody_gen], each with half
    of the remaining lifetime token), their lazy contents are run, and the laters in front
    of the nodes of [UniqLty] are stripped with later credits ([pctx_acc_cost]);
  - the pointer cells on the path ([pctx_ptrs]) and the guards of the cells of the
    referents ([pctx_pguards]) are handed out, so that the address of the hole can be
    computed ([wp_pctx_ptrs], one load per owned pointer or unique borrow, as [pctx_expr]);
  - the closer ([pctx_closer]) takes a new hole (of the same folded type and size, so the
    core may change: the bodies are switched with [cpd_rebody_gen]), whose blocked lifetimes
    are included in all enclosing borrow lifetimes ([pctx_ulfts]), and whose refinement may
    depend on new prophecy variables [ζl']: their tokens are passed through the closers of
    all enclosing borrows (each extends its reservation), from the outermost to the
    innermost, to a view shift that produces the new hole. The root may get larger depths.

  See [~/verus-belt-phase3-design.md], section "PUniq". *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var.
From lrust.lang Require Import proofmode.
From lrust.typing Require Export type ltype lpath.
From lrust.typing Require Import uniq_util uniq_bor.
From lrust.util Require Import proph_bor.
From lrust.lifetime Require Import lifetime_full.
From guarding Require Import guard tactics.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

(** * Functions on contexts *)

Section pctx_fun.
  Context `{!typeG Σ}.

  Definition kind_laters (k: bor_kind) : nat := match k with Owned m => m | Uniq _ _ => 0 end.

  (** The mode of the hole, from a root of mode [k] and value [x]. Inside a unique borrow the
      node is in [Owned 0] mode, so the number of laters restarts after a [PUniq]. *)
  Fixpoint pctx_kind {𝔅 𝔄} (K: pctx 𝔅 𝔄) : bor_kind → ~~𝔄 → bor_kind :=
    match K in pctx 𝔅 𝔄 return bor_kind → ~~𝔄 → bor_kind with
    | PHole => λ k _, k
    | PFst K _ => λ k x, pctx_kind K (Owned (kind_laters k)) x.1
    | PSnd _ K => λ k x, pctx_kind K (Owned (kind_laters k)) x.2
    | POwn _ K => λ k x, pctx_kind K (Owned (kind_laters k + 1)) x.2
    | PSum _ i w K => λ k x, pctx_kind K (Owned (kind_laters k)) (psum_proj_or i x.1 w)
    | PUniq κ K => λ _ x, pctx_kind K (Uniq κ (uniq_bor_ξi x)) (uniq_bor_current x)
    end.

  (** The lifetime of the folded type at the outermost unique borrow on the path (which
      includes all enclosing borrow lifetimes and the lifetimes of their referents), or
      [static] if there is none. *)
  Fixpoint pctx_ulft {𝔅 𝔄} (K: pctx 𝔅 𝔄) : lty 𝔅 → lft :=
    match K in pctx 𝔅 𝔄 return lty 𝔅 → lft with
    | PHole => λ _, static
    | PFst K _ | PSnd _ K | POwn _ K | PSum _ _ _ K => pctx_ulft K
    | PUniq κ K => λ lt, ty_lft (lty_fold (UniqLty (pctx_plug K lt) κ))
    end.

  (** The lifetimes of the enclosing unique borrows, outermost first. *)
  Fixpoint pctx_ulfts {𝔅 𝔄} (K: pctx 𝔅 𝔄) : list lft :=
    match K with
    | PHole => []
    | PFst K _ | PSnd _ K | POwn _ K | PSum _ _ _ K => pctx_ulfts K
    | PUniq κ K => κ :: pctx_ulfts K
    end.

  (** The lifetime at which the hole is reborrowed, for a fresh lifetime [α]: the
      intersection of all enclosing borrow lifetimes and [α] (syntactically, so that
      [[†α]] gives its death without a mask). *)
  Fixpoint pctx_blft {𝔅 𝔄} (K: pctx 𝔅 𝔄) (α: lft) : lft :=
    match K with
    | PHole => α
    | PFst K _ | PSnd _ K | POwn _ K | PSum _ _ _ K => pctx_blft K α
    | PUniq κ K => κ ⊓ pctx_blft K α
    end.

  (** The number of owned pointers and unique borrows on the path (the depth decreases by
      at least one at each). *)
  Fixpoint pctx_dlev {𝔅 𝔄} (K: pctx 𝔅 𝔄) : nat :=
    match K with
    | PHole => 0
    | PFst K _ | PSnd _ K | PSum _ _ _ K => pctx_dlev K
    | POwn _ K | PUniq _ K => S (pctx_dlev K)
    end.

  (** The later credits needed to reach the hole, in a place with [m] laters: the laters
      in front of the contents of each node of [UniqLty], and one for the lazy contents of
      each opened borrow. *)
  Fixpoint pctx_acc_cost {𝔅 𝔄} (K: pctx 𝔅 𝔄) (m: nat) : nat :=
    match K with
    | PHole => 0
    | PFst K _ | PSnd _ K | PSum _ _ _ K => pctx_acc_cost K m
    | POwn _ K => pctx_acc_cost K (m + 1)
    | PUniq _ K => m + 1 + pctx_acc_cost K 0
    end.

  (** The context ends with [PUniq κ PHole] (the hole is the whole referent of the
      innermost unique borrow, in [Uniq] mode). *)
  Fixpoint pctx_uend {𝔅 𝔄} (K: pctx 𝔅 𝔄) : option lft :=
    match K with
    | PHole => None
    | PFst K _ | PSnd _ K | POwn _ K | PSum _ _ _ K => pctx_uend K
    | PUniq κ K => match K with PHole => Some κ | _ => pctx_uend K end
    end.

  (** The number of laters of the hole, if it is in [Owned] mode. *)
  Fixpoint pctx_hmode {𝔅 𝔄} (K: pctx 𝔅 𝔄) (m: nat) : nat :=
    match K with
    | PHole => m
    | PFst K _ | PSnd _ K | PSum _ _ _ K => pctx_hmode K m
    | POwn _ K => pctx_hmode K (m + 1)
    | PUniq _ K => pctx_hmode K 0
    end.

  (** The prophecy id of the innermost unique borrow, if the hole is its whole referent. *)
  Fixpoint pctx_hξi {𝔅 𝔄} (K: pctx 𝔅 𝔄) : ~~𝔄 → positive :=
    match K in pctx 𝔅 𝔄 return ~~𝔄 → positive with
    | PHole => λ _, 1%positive
    | PFst K _ => λ x, pctx_hξi K x.1
    | PSnd _ K | POwn _ K => λ x, pctx_hξi K x.2
    | PSum _ i w K => λ x, pctx_hξi K (psum_proj_or i x.1 w)
    | PUniq _ K => λ x, match K with
        | PHole => uniq_bor_ξi x
        | _ => pctx_hξi K (uniq_bor_current x)
        end
    end.

  (** The pointer cells on the path. *)
  Fixpoint pctx_ptrs {𝔅 𝔄} (K: pctx 𝔅 𝔄) (n: nat) : ~~𝔄 → cloc → iProp Σ :=
    match K in pctx 𝔅 𝔄 return ~~𝔄 → cloc → iProp Σ with
    | PHole => λ _ _, True
    | PFst K _ => λ x l, pctx_ptrs K n x.1 (cloc_take l (pctx_size K n))
    | PSnd lt1 K => λ x l, pctx_ptrs K n x.2 (cloc_skip l (lty_size lt1))
    | POwn _ K => λ x l, l #↦!∗ [FVal (LitV x.1)] ∗
        pctx_ptrs K n x.2 (x.1, repeat [] (pctx_size K n))
    | PSum _ i w K => λ x l,
        pctx_ptrs K n (psum_proj_or i x.1 w) (cloc_take (cloc_skip l 1) (pctx_size K n))
    | PUniq _ K => λ x l, l #↦!∗ [FVal (LitV (uniq_bor_loc x).1)] ∗
        pctx_ptrs K n (uniq_bor_current x) (uniq_bor_loc x)
    end%I.

  (** The guards (by [G], with [k] laters) of the cells of the referents on the path. *)
  Fixpoint pctx_pguards {𝔅 𝔄} (K: pctx 𝔅 𝔄) (n k: nat) (G: iProp Σ) : ~~𝔄 → cloc → iProp Σ :=
    match K in pctx 𝔅 𝔄 return ~~𝔄 → cloc → iProp Σ with
    | PHole => λ _ _, True
    | PFst K _ => λ x l, pctx_pguards K n k G x.1 (cloc_take l (pctx_size K n))
    | PSnd lt1 K => λ x l, pctx_pguards K n k G x.2 (cloc_skip l (lty_size lt1))
    | POwn _ K => λ x l, pctx_pguards K n k G x.2 (x.1, repeat [] (pctx_size K n))
    | PSum _ i w K => λ x l,
        pctx_pguards K n k G (psum_proj_or i x.1 w) (cloc_take (cloc_skip l 1) (pctx_size K n))
    | PUniq _ K => λ x l, (G &&{↑NllftG; k}&&> uniq_bor_loc x #↦∗_) ∗
        pctx_pguards K n k G (uniq_bor_current x) (uniq_bor_loc x)
    end%I.

  Global Instance pctx_pguards_persistent {𝔅 𝔄} (K: pctx 𝔅 𝔄) n k G x l :
    Persistent (pctx_pguards K n k G x l).
  Proof. induction K in x, l |- *; apply _. Qed.

  Lemma pctx_pguards_mono {𝔅 𝔄} (K: pctx 𝔅 𝔄) n k k' G x l :
    k ≤ k' → pctx_pguards K n k G x l ⊢ pctx_pguards K n k' G x l.
  Proof.
    intros ?. induction K in x, l |- *; simpl; [done|auto|auto|auto|auto|].
    iIntros "[#G R]". iSplit; [by iApply (lguards_weaken_later with "G")|]. by iApply IHK.
  Qed.

  Lemma pctx_pguards_transfer {𝔅 𝔄} (K: pctx 𝔅 𝔄) n k G G' x l :
    (G' &&{↑NllftG}&&> G) -∗ pctx_pguards K n k G x l -∗ pctx_pguards K n k G' x l.
  Proof.
    iIntros "#GG'". induction K in x, l |- *; simpl; [done|auto|auto|auto|auto|].
    iIntros "[#G R]". iSplit; [by iApply (guards_transitive_right with "GG' G")|]. by iApply IHK.
  Qed.

  (** ** Laws *)

  Lemma lty_simple_true {𝔄} (lt: lty 𝔄) : lty_simple lt.
  Proof. induction lt; simpl; auto. Qed.

  Lemma lty_is_cpd_plug_nonempty' {𝔅 𝔄} (K: pctx 𝔅 𝔄) lt :
    pctx_nonempty K → lty_is_cpd (pctx_plug K lt).
  Proof. by destruct K. Qed.

  Lemma pctx_kind_nonempty {𝔅 𝔄} (K: pctx 𝔅 𝔄) κ ξi x :
    pctx_nonempty K → pctx_kind K (Uniq κ ξi) x = pctx_kind K (Owned 0) x.
  Proof. by destruct K. Qed.

  Lemma pctx_kind_owned {𝔅 𝔄} (K: pctx 𝔅 𝔄) m x :
    pctx_uend K = None → pctx_kind K (Owned m) x = Owned (pctx_hmode K m).
  Proof.
    induction K in m, x |- *; simpl; [done|auto|auto|auto|auto|].
    destruct K; [done|..]; intros; rewrite pctx_kind_nonempty //; by apply IHK.
  Qed.

  Lemma pctx_kind_uniq {𝔅 𝔄} (K: pctx 𝔅 𝔄) κ m x :
    pctx_uend K = Some κ → pctx_kind K (Owned m) x = Uniq κ (pctx_hξi K x).
  Proof.
    induction K in m, x |- *; simpl; [done|auto|auto|auto|auto|].
    destruct K; [by intros [= ->]|..]; intros; rewrite pctx_kind_nonempty //; by apply IHK.
  Qed.

  Lemma pctx_kind_nouniq {𝔅 𝔄} (K: pctx 𝔅 𝔄) `{!PctxNoUniq K} m x :
    pctx_kind K (Owned m) x = Owned (pctx_mode K m).
  Proof.
    rename select (PctxNoUniq K) into HK. rewrite /PctxNoUniq in HK.
    induction K in HK, m, x |- *; simpl; simpl in HK; auto. done.
  Qed.

  Lemma pctx_kind_set {𝔅 𝔄} (K: pctx 𝔅 𝔄) k x y :
    pctx_in K x → pctx_kind K k (pctx_set K x y) = pctx_kind K k x.
  Proof.
    induction K in k, x, y |- *; simpl; try (intros; by rewrite ?IHK).
    - rewrite psum_proj_or_pinj /psum_proj_or. destruct (psum_proj i x.1); [|done].
      intros. by rewrite IHK.
    - intros. by rewrite uniq_bor_current_set uniq_bor_ξi_set IHK.
  Qed.

  Lemma pctx_hξi_set {𝔅 𝔄} (K: pctx 𝔅 𝔄) x y :
    pctx_in K x → pctx_hξi K (pctx_set K x y) = pctx_hξi K x.
  Proof.
    induction K in x, y |- *; simpl; try (intros; by rewrite ?IHK).
    - rewrite psum_proj_or_pinj /psum_proj_or. destruct (psum_proj i x.1); [|done].
      intros. by rewrite IHK.
    - destruct K; intros; by rewrite ?uniq_bor_current_set ?uniq_bor_ξi_set ?IHK.
  Qed.

  Lemma pctx_ulft_incl {𝔅 𝔄} (K: pctx 𝔅 𝔄) lt :
    ⊢ ty_lft (lty_fold (pctx_plug K lt)) ⊑ pctx_ulft K lt.
  Proof.
    induction K; simpl; [iApply lft_incl_static| | | | |iApply guards_refl];
      (iApply llftl_incl_trans; [|iApply IHK]).
    - rewrite lft_intersect_list_app. iApply llftl_intersect_incl_l.
    - rewrite lft_intersect_list_app. iApply llftl_intersect_incl_r.
    - iApply guards_refl.
    - iApply (lty_lft_sum _ _ (pctx_plug K lt)).
  Qed.

  Lemma pctx_ulft_eq {𝔅 𝔄} (K: pctx 𝔅 𝔄) lt lt' :
    lty_fold lt' = lty_fold lt → pctx_ulft K lt' = pctx_ulft K lt.
  Proof. intros Heq. induction K; simpl; [done..|]. by rewrite (lty_fold_plug_eq' K lt' lt). Qed.

  Lemma pctx_ulft_uniq {𝔅 𝔄} (K: pctx 𝔅 𝔄) κ lt :
    ⊢ pctx_ulft (PUniq κ K) lt ⊑ κ.
  Proof. iApply llftl_intersect_incl_l. Qed.

  Lemma pctx_ulft_uniq_r {𝔅 𝔄} (K: pctx 𝔅 𝔄) κ lt :
    ⊢ pctx_ulft (PUniq κ K) lt ⊑ ty_lft (lty_fold (pctx_plug K lt)).
  Proof. iApply llftl_intersect_incl_r. Qed.

  (** Every enclosing borrow lifetime outlives [pctx_ulft]. *)
  Lemma pctx_ulft_ulfts {𝔅 𝔄} (K: pctx 𝔅 𝔄) lt κ :
    κ ∈ pctx_ulfts K → ⊢ pctx_ulft K lt ⊑ κ.
  Proof.
    induction K; simpl; try by auto. rewrite elem_of_cons. intros [->|Hκ].
    - iApply llftl_intersect_incl_l.
    - iApply llftl_incl_trans; [iApply llftl_intersect_incl_r|].
      iApply llftl_incl_trans; [iApply pctx_ulft_incl|]. by iApply IHK.
  Qed.

  Lemma pctx_blft_incl {𝔅 𝔄} (K: pctx 𝔅 𝔄) α κ :
    κ ∈ pctx_ulfts K → ⊢ pctx_blft K α ⊑ κ.
  Proof.
    induction K; simpl; try by auto. rewrite elem_of_cons. intros [->|Hκ].
    - iApply llftl_intersect_incl_l.
    - iApply llftl_incl_trans; [iApply llftl_intersect_incl_r|]. by iApply IHK.
  Qed.

  Lemma pctx_blft_incl_r {𝔅 𝔄} (K: pctx 𝔅 𝔄) α : ⊢ pctx_blft K α ⊑ α.
  Proof.
    induction K; simpl; try by auto. iApply guards_refl.
    iApply llftl_incl_trans; [iApply llftl_intersect_incl_r|]. iApply IHK.
  Qed.

  Lemma pctx_blft_dead {𝔅 𝔄} (K: pctx 𝔅 𝔄) α : [†α] -∗ [†pctx_blft K α].
  Proof.
    induction K; simpl; try by auto. iIntros "†". rewrite llftl_end_inter. iRight. by iApply IHK.
  Qed.

  (** The new blocked lifetime is below every enclosing borrow lifetime. *)
  Lemma pat_ok_blft {𝔅 𝔄} (K: pctx 𝔅 𝔄) α :
    ⊢ [∗ list] κ ∈ pctx_ulfts K, pat_ok κ (PatBlocked (pctx_blft K α)).
  Proof.
    iApply big_sepL_intro. iIntros "!>" (i κ Hi). iApply pat_ok_blocked.
    iApply pctx_blft_incl. by eapply elem_of_list_lookup_2.
  Qed.

  Lemma pat_ok_ulfts_leaf {𝔅 𝔄} (K: pctx 𝔅 𝔄) :
    ⊢ [∗ list] κ ∈ pctx_ulfts K, pat_ok κ PatLeaf.
  Proof. iApply big_sepL_intro. iIntros "!>" (i κ Hi). iApply pat_ok_leaf. Qed.

  Lemma pctx_dlev_nouniq {𝔅 𝔄} (K: pctx 𝔅 𝔄) `{!PctxNoUniq K} : pctx_dlev K = pctx_mode K 0.
  Proof.
    rename select (PctxNoUniq K) into HK. rewrite /PctxNoUniq in HK.
    induction K in HK |- *; simpl; simpl in HK; auto; [|done].
    rewrite IHK // (pctx_mode_add K (0 + 1)). lia.
  Qed.

  Lemma pctx_acc_cost_nouniq {𝔅 𝔄} (K: pctx 𝔅 𝔄) `{!PctxNoUniq K} m : pctx_acc_cost K m = 0%nat.
  Proof.
    rename select (PctxNoUniq K) into HK. rewrite /PctxNoUniq in HK.
    induction K in HK, m |- *; simpl; simpl in HK; auto. done.
  Qed.

  (** A bound on the credits, by the number of levels. *)
  Lemma pctx_acc_cost_le {𝔅 𝔄} (K: pctx 𝔅 𝔄) m :
    pctx_acc_cost K m ≤ pctx_dlev K * (m + pctx_dlev K + 1).
  Proof. induction K in m |- *; simpl; [lia|auto|auto|..|auto|]; [specialize (IHK (m + 1))|specialize (IHK 0)]; nia. Qed.

  Lemma pctx_ptrs_set {𝔅 𝔄} (K: pctx 𝔅 𝔄) n x y l :
    pctx_in K x → pctx_ptrs K n (pctx_set K x y) l = pctx_ptrs K n x l.
  Proof.
    induction K in x, y, l |- *; simpl; try (intros; by rewrite ?IHK).
    - rewrite psum_proj_or_pinj /psum_proj_or. destruct (psum_proj i x.1); [|done].
      intros. by rewrite IHK.
    - intros. by rewrite uniq_bor_current_set uniq_bor_loc_set IHK.
  Qed.

  Lemma pctx_ulfts_nouniq {𝔅 𝔄} (K: pctx 𝔅 𝔄) `{!PctxNoUniq K} : pctx_ulfts K = [].
  Proof.
    rename select (PctxNoUniq K) into HK. rewrite /PctxNoUniq in HK.
    induction K in HK |- *; simpl; simpl in HK; auto. done.
  Qed.

  Lemma pctx_blft_nouniq {𝔅 𝔄} (K: pctx 𝔅 𝔄) `{!PctxNoUniq K} α : pctx_blft K α = α.
  Proof.
    rename select (PctxNoUniq K) into HK. rewrite /PctxNoUniq in HK.
    induction K in HK |- *; simpl; simpl in HK; auto. done.
  Qed.
End pctx_fun.

(** * The address of the hole *)

Section wp_pctx.
  Context `{!typeG Σ}.

  Lemma wp_pctx_ptrs {𝔅 𝔄} E (K: pctx 𝔅 𝔄) n k (G R: iProp Σ) x (l: cloc) (e: expr) :
    ↑NllftG ⊆ E →
    (G &&{↑NllftG; k}&&> l #↦∗_) -∗ pctx_pguards K n k G x l -∗ £(3 * k * pctx_dlev K) -∗
    WP e @ E {{ v, ⌜v = #(l.1)⌝ ∗ R ∗ G }} -∗ pctx_ptrs K n x l -∗
    WP pctx_expr K e @ E {{ v, ⌜v = #(pctx_loc K n x l).1⌝ ∗ R ∗ G ∗ pctx_ptrs K n x l }}.
  Proof.
    intros HE. induction K in x, l, e, R |- *; simpl.
    - iIntros "_ _ _ WP $". iApply (wp_wand with "WP"). iIntros (v) "($ & $ & $)".
    - iIntros "#Gl #Gs £ WP Ptrs".
      iApply (IHK x.1 (cloc_take l (pctx_size K n)) with "[] Gs £ WP Ptrs").
      rewrite (heap_cloc_mapsto_emp_vec_app l (pctx_size K n)).
      iApply (guards_weaken_rhs_sep_l with "Gl").
    - iIntros "#Gl #Gs £ WP Ptrs".
      iApply (IHK x.2 (cloc_skip l (lty_size lt1)) _ R with "[] Gs £ [WP] Ptrs").
      + rewrite (heap_cloc_mapsto_emp_vec_app l (lty_size lt1)).
        iApply (guards_weaken_rhs_sep_r with "Gl").
      + wp_bind e. iApply (wp_wand with "WP"). iIntros (v) "(-> & R & G)". wp_op.
        iFrame. done.
    - iIntros "#Gl #Gs £ WP (Pt & Ptrs)".
      iDestruct (lc_weaken (3 * k + 3 * k * pctx_dlev K) with "£") as "[£1 £]"; [lia|].
      iApply (wp_wand with "[- ]").
      { iApply (IHK x.2 (x.1, repeat [] (pctx_size K n)) _
          (R ∗ l #↦!∗ [FVal (LitV x.1)])%I with "[] Gs £ [WP Pt £1] Ptrs").
        - rewrite -heap_cloc_mapsto_empty. iApply guards_true.
        - wp_bind e. iApply (wp_wand with "WP"). iIntros (v) "(-> & R & G)".
          iApply (wp_read_na_guarded_cells_singleton _ l.1 l.2 (G ∗ l #↦!∗ [FVal (LitV x.1)])
            #(x.1) k with "[G Pt £1]"); [solve_ndisj| |].
          + iFrame "G Pt £1". iApply guard_cloc_combine.
            * by iApply guards_weaken_lhs_sep_l.
            * iApply (lguards_weaken_later _ _ _ 0); [lia|iApply guards_weaken_sep_r].
          + iIntros "!> [G Pt]". iFrame. done. }
      iIntros (v) "($ & [$ $] & $ & $)".
    - iIntros "#Gl #Gs £ WP Ptrs".
      iApply (IHK (psum_proj_or i x.1 w) (cloc_take (cloc_skip l 1) (pctx_size K n)) _ R
        with "[] Gs £ [WP] Ptrs").
      + rewrite (heap_cloc_mapsto_emp_vec_app l 1).
        iDestruct (guards_weaken_rhs_sep_r with "Gl") as "Gl'".
        rewrite (heap_cloc_mapsto_emp_vec_app (cloc_skip l 1) (pctx_size K n)).
        iApply (guards_weaken_rhs_sep_l with "Gl'").
      + wp_bind e. iApply (wp_wand with "WP"). iIntros (v) "(-> & R & G)". wp_op.
        iFrame. done.
    - iIntros "#Gl [#Gl' #Gs] £ WP (Pt & Ptrs)".
      iDestruct (lc_weaken (3 * k + 3 * k * pctx_dlev K) with "£") as "[£1 £]"; [lia|].
      iApply (wp_wand with "[- ]").
      { iApply (IHK (uniq_bor_current x) (uniq_bor_loc x) _
          (R ∗ l #↦!∗ [FVal (LitV (uniq_bor_loc x).1)])%I with "Gl' Gs £ [WP Pt £1] Ptrs").
        wp_bind e. iApply (wp_wand with "WP"). iIntros (v) "(-> & R & G)".
        iApply (wp_read_na_guarded_cells_singleton _ l.1 l.2
          (G ∗ l #↦!∗ [FVal (LitV (uniq_bor_loc x).1)]) #((uniq_bor_loc x).1) k
          with "[G Pt £1]"); [solve_ndisj| |].
        + iFrame "G Pt £1". iApply guard_cloc_combine.
          * by iApply guards_weaken_lhs_sep_l.
          * iApply (lguards_weaken_later _ _ _ 0); [lia|iApply guards_weaken_sep_r].
        + iIntros "!> [G Pt]". iFrame. done. }
      iIntros (v) "($ & [$ $] & $ & $)".
  Qed.
End wp_pctx.
