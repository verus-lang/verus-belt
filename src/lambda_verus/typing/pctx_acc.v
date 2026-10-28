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
    of the nodes of [UniqLty] are stripped with later credits (a number bounded by the
    depth of the place, [pctx_acc_stmt]);
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
    (* Only meaningful below no shared reference ([PctxNoShr]); as [POwn]. *)
    | PShr _ K => λ k x, pctx_kind K (Owned (kind_laters k + 1)) x.2
    end.

  (** The lifetime of the folded type at the outermost unique borrow on the path (which
      includes all enclosing borrow lifetimes and the lifetimes of their referents), or
      [static] if there is none. *)
  Fixpoint pctx_ulft {𝔅 𝔄} (K: pctx 𝔅 𝔄) : lty 𝔅 → lft :=
    match K in pctx 𝔅 𝔄 return lty 𝔅 → lft with
    | PHole => λ _, static
    | PFst K _ | PSnd _ K | POwn _ K | PSum _ _ _ K | PShr _ K => pctx_ulft K
    | PUniq κ K => λ lt, ty_lft (lty_fold (UniqLty (pctx_plug K lt) κ))
    end.

  (** The lifetimes of the enclosing unique borrows, outermost first. *)
  Fixpoint pctx_ulfts {𝔅 𝔄} (K: pctx 𝔅 𝔄) : list lft :=
    match K with
    | PHole => []
    | PFst K _ | PSnd _ K | POwn _ K | PSum _ _ _ K | PShr _ K => pctx_ulfts K
    | PUniq κ K => κ :: pctx_ulfts K
    end.

  (** The lifetime at which the hole is reborrowed, for a fresh lifetime [α]: the
      intersection of all enclosing borrow lifetimes and [α] (syntactically, so that
      [[†α]] gives its death without a mask). *)
  Fixpoint pctx_blft {𝔅 𝔄} (K: pctx 𝔅 𝔄) (α: lft) : lft :=
    match K with
    | PHole => α
    | PFst K _ | PSnd _ K | POwn _ K | PSum _ _ _ K | PShr _ K => pctx_blft K α
    | PUniq κ K => κ ⊓ pctx_blft K α
    end.

  (** The lifetime whose token guards the cells of the hole, if the cells of the root are
      guarded by [b]: the lifetime of the innermost enclosing unique borrow (the cells of a
      pointee of an owned pointer are not ghost cells). *)
  Fixpoint pctx_hlft {𝔅 𝔄} (K: pctx 𝔅 𝔄) (b: lft) : lft :=
    match K with
    | PHole => b
    | PFst K _ | PSnd _ K | POwn _ K | PSum _ _ _ K | PShr _ K => pctx_hlft K b
    | PUniq κ K => pctx_hlft K κ
    end.

  (** The number of owned pointers and unique borrows on the path (the depth decreases by
      at least one at each). *)
  Fixpoint pctx_dlev {𝔅 𝔄} (K: pctx 𝔅 𝔄) : nat :=
    match K with
    | PHole => 0
    | PFst K _ | PSnd _ K | PSum _ _ _ K => pctx_dlev K
    | POwn _ K | PUniq _ K | PShr _ K => S (pctx_dlev K)
    end.

  (** The later credits for an access ([pctx_acc]), at a depth [d] and with [m] laters:
      none below no unique borrow. *)
  Definition pctx_acc_cred {𝔅 𝔄} (K: pctx 𝔅 𝔄) (m d: nat) : nat :=
    match pctx_ulfts K with [] => 0 | _ => (d + 1) * (m + d + 2) end.

  Lemma pctx_acc_cred_le {𝔅 𝔄} (K: pctx 𝔅 𝔄) m d : pctx_acc_cred K m d ≤ (d + 1) * (m + d + 2).
  Proof. rewrite /pctx_acc_cred. destruct (pctx_ulfts K); lia. Qed.

  (** The context ends with [PUniq κ PHole] (the hole is the whole referent of the
      innermost unique borrow, in [Uniq] mode). *)
  Fixpoint pctx_uend {𝔅 𝔄} (K: pctx 𝔅 𝔄) : option lft :=
    match K with
    | PHole => None
    | PFst K _ | PSnd _ K | POwn _ K | PSum _ _ _ K | PShr _ K => pctx_uend K
    | PUniq κ K => match K with PHole => Some κ | _ => pctx_uend K end
    end.

  (** The number of laters of the hole, if it is in [Owned] mode. *)
  Fixpoint pctx_hmode {𝔅 𝔄} (K: pctx 𝔅 𝔄) (m: nat) : nat :=
    match K with
    | PHole => m
    | PFst K _ | PSnd _ K | PSum _ _ _ K => pctx_hmode K m
    | POwn _ K | PShr _ K => pctx_hmode K (m + 1)
    | PUniq _ K => pctx_hmode K 0
    end.

  (** The prophecy id of the innermost unique borrow, if the hole is its whole referent. *)
  Fixpoint pctx_hξi {𝔅 𝔄} (K: pctx 𝔅 𝔄) : ~~𝔄 → positive :=
    match K in pctx 𝔅 𝔄 return ~~𝔄 → positive with
    | PHole => λ _, 1%positive
    | PFst K _ => λ x, pctx_hξi K x.1
    | PSnd _ K | POwn _ K | PShr _ K => λ x, pctx_hξi K x.2
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
    | PShr _ K => λ x l, l #↦!∗ [FVal (LitV x.1.1)] ∗ pctx_ptrs K n x.2 x.1
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
    | PShr _ K => λ x l, (G &&{↑NllftG; k}&&> x.1 #↦∗_) ∗ pctx_pguards K n k G x.2 x.1
    end%I.

  Global Instance pctx_pguards_persistent {𝔅 𝔄} (K: pctx 𝔅 𝔄) n k G x l :
    Persistent (pctx_pguards K n k G x l).
  Proof. induction K in x, l |- *; apply _. Qed.

  Lemma pctx_pguards_mono {𝔅 𝔄} (K: pctx 𝔅 𝔄) n k k' G x l :
    k ≤ k' → pctx_pguards K n k G x l ⊢ pctx_pguards K n k' G x l.
  Proof.
    intros ?. induction K in x, l |- *; simpl; [done|auto|auto|auto|auto| |];
      iIntros "[#G R]"; (iSplit; [by iApply (lguards_weaken_later with "G")|]); by iApply IHK.
  Qed.

  Lemma pctx_pguards_transfer {𝔅 𝔄} (K: pctx 𝔅 𝔄) n k G G' x l :
    (G' &&{↑NllftG}&&> G) -∗ pctx_pguards K n k G x l -∗ pctx_pguards K n k G' x l.
  Proof.
    induction K in x, l |- *; simpl; iIntros "#GG' Gs";
      [done|iApply (IHK with "GG' Gs")|iApply (IHK with "GG' Gs")|iApply (IHK with "GG' Gs")|
       iApply (IHK with "GG' Gs")| |];
      iDestruct "Gs" as "[#G R]"; (iSplit; [by iApply (guards_transitive_right with "GG' G")|]);
      by iApply (IHK with "GG' R").
  Qed.

  (** ** Laws *)

  Lemma lty_is_cpd_plug_nonempty' {𝔅 𝔄} (K: pctx 𝔅 𝔄) lt :
    pctx_nonempty K → lty_is_cpd (pctx_plug K lt).
  Proof. by destruct K. Qed.

  Lemma pctx_kind_nonempty {𝔅 𝔄} (K: pctx 𝔅 𝔄) κ ξi x :
    pctx_nonempty K → pctx_kind K (Uniq κ ξi) x = pctx_kind K (Owned 0) x.
  Proof. by destruct K. Qed.

  Lemma pctx_kind_owned {𝔅 𝔄} (K: pctx 𝔅 𝔄) m x :
    pctx_uend K = None → pctx_kind K (Owned m) x = Owned (pctx_hmode K m).
  Proof.
    induction K in m, x |- *; simpl; [done|auto|auto|auto|auto| |auto].
    destruct K; [done| | | | | |intros H; exact (IHK 0 _ H)];
      intros; rewrite pctx_kind_nonempty //; by apply IHK.
  Qed.

  Lemma pctx_kind_uniq {𝔅 𝔄} (K: pctx 𝔅 𝔄) κ m x :
    pctx_uend K = Some κ → pctx_kind K (Owned m) x = Uniq κ (pctx_hξi K x).
  Proof.
    induction K in m, x |- *; simpl; [done|auto|auto|auto|auto| |auto].
    destruct K; [by intros [= ->]| | | | | |intros H; exact (IHK 0 _ H)];
      intros; rewrite pctx_kind_nonempty //; by apply IHK.
  Qed.

  Lemma pctx_kind_nouniq {𝔅 𝔄} (K: pctx 𝔅 𝔄) `{!PctxNoUniq K} m x :
    pctx_kind K (Owned m) x = Owned (pctx_mode K m).
  Proof.
    rename select (PctxNoUniq K) into HK. rewrite /PctxNoUniq in HK.
    induction K in HK, m, x |- *; simpl; simpl in HK; auto; done.
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
    induction K; simpl; [iApply lft_incl_static| | | | |iApply guards_refl|
      iApply llftl_incl_trans; [iApply llftl_intersect_incl_r|iApply IHK]];
      (iApply llftl_incl_trans; [|iApply IHK]).
    - rewrite lft_intersect_list_app. iApply llftl_intersect_incl_l.
    - rewrite lft_intersect_list_app. iApply llftl_intersect_incl_r.
    - iApply guards_refl.
    - iApply (lty_lft_sum _ _ (pctx_plug K lt)).
  Qed.

  Lemma pctx_ulft_eq {𝔅 𝔄} (K: pctx 𝔅 𝔄) lt lt' :
    lty_fold lt' = lty_fold lt → pctx_ulft K lt' = pctx_ulft K lt.
  Proof. intros Heq. induction K; simpl; eauto. by rewrite (lty_fold_plug_eq' _ _ _ Heq). Qed.

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
    induction K in lt |- *; simpl; intros Hκ; [by apply not_elem_of_nil in Hκ|by auto|by auto|
      by auto|by auto| |by auto].
    apply elem_of_cons in Hκ as [->|Hκ].
    - iApply llftl_intersect_incl_l.
    - iApply llftl_incl_trans; [iApply llftl_intersect_incl_r|].
      iApply llftl_incl_trans; [iApply pctx_ulft_incl|]. by iApply IHK.
  Qed.

  Lemma pctx_blft_incl {𝔅 𝔄} (K: pctx 𝔅 𝔄) α κ :
    κ ∈ pctx_ulfts K → ⊢ pctx_blft K α ⊑ κ.
  Proof.
    induction K; simpl; intros Hκ; [by apply not_elem_of_nil in Hκ|by auto|by auto|by auto|
      by auto| |by auto].
    apply elem_of_cons in Hκ as [->|Hκ].
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

  Lemma pctx_blft_hlft_meet {𝔅 𝔄} (K: pctx 𝔅 𝔄) α b : ⊢ b ⊓ pctx_blft K α ⊑ pctx_hlft K b.
  Proof.
    induction K in b |- *; simpl; [iApply llftl_intersect_incl_l|iApply IHK|iApply IHK|iApply IHK|
      iApply IHK| |iApply IHK].
    iApply llftl_incl_trans; [iApply llftl_intersect_incl_r|]. iApply IHK.
  Qed.

  Lemma pctx_blft_hlft {𝔅 𝔄} (K: pctx 𝔅 𝔄) α : ⊢ pctx_blft K α ⊑ pctx_hlft K α.
  Proof.
    induction K; simpl; [iApply guards_refl|iApply IHK|iApply IHK|iApply IHK|iApply IHK| |iApply IHK].
    iApply pctx_blft_hlft_meet.
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
    induction K in HK |- *; simpl; simpl in HK; auto; [|done|done].
    rewrite IHK // (pctx_mode_add K (0 + 1)). lia.
  Qed.

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
    induction K in HK |- *; simpl; simpl in HK; auto; done.
  Qed.

  Lemma pctx_blft_nouniq {𝔅 𝔄} (K: pctx 𝔅 𝔄) `{!PctxNoUniq K} α : pctx_blft K α = α.
  Proof.
    rename select (PctxNoUniq K) into HK. rewrite /PctxNoUniq in HK.
    induction K in HK |- *; simpl; simpl in HK; auto; done.
  Qed.
End pctx_fun.

(** * The address of the hole *)

Section wp_pctx.
  Context `{!typeG Σ}.

  Lemma wp_pctx_ptrs {𝔅 𝔄} E (K: pctx 𝔅 𝔄) n k (G: iProp Σ) x (l: cloc) (e: expr) (R: iProp Σ) :
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
    - iIntros "#Gl [#Gl' #Gs] £ WP (Pt & Ptrs)".
      iDestruct (lc_weaken (3 * k + 3 * k * pctx_dlev K) with "£") as "[£1 £]"; [lia|].
      iApply (wp_wand with "[- ]").
      { iApply (IHK x.2 x.1 _ (R ∗ l #↦!∗ [FVal (LitV x.1.1)])%I with "Gl' Gs £ [WP Pt £1] Ptrs").
        wp_bind e. iApply (wp_wand with "WP"). iIntros (v) "(-> & R & G)".
        iApply (wp_read_na_guarded_cells_singleton _ l.1 l.2
          (G ∗ l #↦!∗ [FVal (LitV x.1.1)]) #(x.1.1) k with "[G Pt £1]"); [solve_ndisj| |].
        + iFrame "G Pt £1". iApply guard_cloc_combine.
          * by iApply guards_weaken_lhs_sep_l.
          * iApply (lguards_weaken_later _ _ _ 0); [lia|iApply guards_weaken_sep_r].
        + iIntros "!> [G Pt]". iFrame. done. }
      iIntros (v) "($ & [$ $] & $ & $)".
  Qed.
End wp_pctx.

(** * Opening a compound place, switching to a node chosen when closing *)

Section cpd_gen.
  Context `{!typeG Σ}.

  (** As [cpd_rebody_ext], with the new node chosen by the closer. *)
  Lemma cpd_rebody_gen {𝔄} κ ξi (ty: type 𝔄) p
      (node: lpat → prfn 𝔄 → nat → nat → thread_id → cloc → iProp Σ)
      (r: prfn 𝔄) d g tid l E G :
    Timeless G → ↑Nllft ∪ ↑prophN ⊆ E →
    llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ (G &&{↑NllftG}&&> @[κ]) -∗ G -∗
    cpd_own κ ξi ty p node r d g tid l ={E}=∗ ∃ κp,
      uniq_pat_lft κ κp ∗ ▷ pat_ok κp p ∗
      ▷ guarded_upd lazyE @[ty_lft ty] (⧖(S d `max` g) ∗ node p r d g tid l) ∗
      (∀ (node': lpat → prfn 𝔄 → nat → nat → thread_id → cloc → iProp Σ)
         p' (r': prfn 𝔄) d' g' ζl' q (R: iProp Σ),
         ⌜∀ ζl, prfn_rsv r ζl → prfn_rsv r' (ζl ++ ζl')⌝ -∗
         □ (∀ p2 r2 d2 g2, pat_ok κp p2 -∗ ⧖(S d2 `max` g2) -∗ node' p2 r2 d2 g2 tid l -∗
              leaf_node κp ty p2 r2 d2 g2 tid l) -∗
         q:+[ζl'] -∗
         (q:+[ζl'] ={E}=∗ ▷ pat_ok κp p' ∗
           ▷ guarded_upd lazyE @[ty_lft ty] (⧖(S d' `max` g') ∗ node' p' r' d' g' tid l) ∗ R)
         ={E}=∗ cpd_own κ ξi ty p' node' r' d' g' tid l ∗ G ∗ R).
  Proof.
    iIntros (??) "#LFT #PROPH #UNIQ #Gk G".
    iIntros "(%x₀ & %κp & %γ & %γf & %idx & %ζl & #Incl & %Hr & Tok & Gh & Tf & ⧗ & #Bor)".
    iMod (proph_idx_bor_gen_rsv_acc_rebody_ext with "LFT PROPH UNIQ Gk Tok Bor G")
      as (wπ) "[Body Close]"; [done..|].
    iDestruct (bi.later_or with "Body") as "[Body|[>Tf' _]]"; last first.
    { iDestruct (cpd_tok_excl with "Tf Tf'") as "[]". }
    rewrite cpd_body_cell.
    iMod (bi.later_exist_except_0 with "Body") as (p1) "Body".
    iMod (bi.later_exist_except_0 with "Body") as (r1) "(#Ok & _ & >Gh' & Upd)".
    iDestruct (ghost_var_agree with "Gh Gh'") as %[<- <-]%lstate_inj.
    iModIntro. iExists κp. iFrame "Incl Ok Upd".
    iIntros (node' p' r' d' g' ζl' q R Hr') "#Conv ζl' VS".
    iMod (ghost_var_update_halves (lstate p' r') with "Gh Gh'") as "[Gh Gh']".
    iMod (ghost_var_alloc (lstate_triv (𝔄:=unitₛ) ())) as (γf') "Tf'".
    iMod ("Close" $! (uniq_cell x₀ d' g' γ) (λ π, (prfn_den r' π, (uniq_cell x₀ d' g' γ).2))
      ζl' q (cpd_gbody κp γf' ty node' tid l) R with "[Tf] ζl' [Gh' VS]")
      as (idx') "(Tok & #Bor' & $ & $)".
    { iIntros "!>" (c2 w2) "Q". iModIntro. iNext. iRight. iFrame "Tf".
      iDestruct "Q" as "[Q|[_ $]]". rewrite /uniq_gbody /cpd_body.
      iDestruct "Q" as (p2 r2) "(#Ok2 & % & Gh2 & Upd2)". iExists p2, r2. iFrame "Ok2 Gh2".
      iSplit; [done|]. iApply (guarded_upd_mono with "[] Upd2").
      iIntros "[#⧖ N] !>". iFrame "⧖". iApply ("Conv" with "Ok2 ⧖ N"). }
    { iIntros "ζl'". iMod ("VS" with "ζl'") as "(Ok' & Upd' & $)". iModIntro.
      iNext. iLeft. rewrite cpd_body_cell. iExists p', r'. by iFrame. }
    iModIntro. iExists x₀, κp, γ, γf', idx', (ζl ++ ζl'). iFrame "∗#". iPureIntro. by apply Hr'.
  Qed.
End cpd_gen.

(** * The access *)

Section pctx_acc.
  Context `{!typeG Σ}.

  (** The closer of an access to the hole of [K] (see the head of the file). *)
  Definition pctx_closer {𝔅 𝔄} (K: pctx 𝔅 𝔄) (lt: lty 𝔅) (m: nat) (r: prfn 𝔅) (x: ~~𝔄)
      (ζm: blk_map) (q: lpath) (d g: nat) (tid: thread_id) (l: cloc) (E: coPset)
      (G G': iProp Σ) : iProp Σ :=
    ∀ (lt': lty 𝔅) p' r' dh' gh' dn gn ζl' (qq: Qp) (R: iProp Σ),
      ⌜lty_simple lt'⌝ -∗ ⌜lty_fold lt' = lty_fold lt⌝ -∗ ⌜lty_size lt' = lty_size lt⌝ -∗
      ⌜∀ ζl, prfn_rsv r ζl → prfn_rsv r' (ζl ++ ζl')⌝ -∗
      ⌜d ≤ dn ∧ g ≤ gn ∧ dh' + pctx_dlev K ≤ dn ∧ gh' ≤ gn⌝ -∗
      ([∗ list] κ ∈ pctx_ulfts K, pat_ok κ p') -∗
      ⧖(S dn `max` gn) -∗ G' -∗ pctx_ptrs K (lty_size lt) x l -∗ qq:+[ζl'] -∗
      (qq:+[ζl'] ={E}=∗ ltype_own_cp false lt' (pctx_kind K (Owned m) x) p' r' dh' gh' tid
          (pctx_loc K (lty_size lt) x l) ∗ R) ={E}=∗
      ltype_own_cp false (pctx_plug K lt') (Owned m) (pctx_pat K p') (pctx_rfn K x ζm q r')
        dn gn tid l ∗ G ∗ R.

  (** The result of an access. *)
  Definition pctx_acc_res {𝔅 𝔄} (K: pctx 𝔅 𝔄) (lt: lty 𝔅) (m: nat) (p: lpat) (r: prfn 𝔅)
      (x: ~~𝔄) (ζm: blk_map) (q: lpath) (d g: nat) (tid: thread_id) (l: cloc) (E: coPset)
      (G: iProp Σ) : iProp Σ :=
    ∃ (G': iProp Σ) dh gh, ⌜Timeless G'⌝ ∗ G' ∗ (G' &&{↑NllftG}&&> G) ∗
      ⌜dh + pctx_dlev K ≤ d ∧ gh ≤ g ∧ pctx_in K x⌝ ∗
      ltype_own_cp false lt (pctx_kind K (Owned m) x) p r dh gh tid (pctx_loc K (lty_size lt) x l) ∗
      pctx_ptrs K (lty_size lt) x l ∗ pctx_pguards K (lty_size lt) (g + 1) G' x l ∗
      □ (∀ b k, (@[b] &&{↑NllftG; k}&&> l #↦∗_) -∗
         @[pctx_hlft K b] &&{↑NllftG; k `max` (g + 1)}&&> pctx_loc K (lty_size lt) x l #↦∗_) ∗
      pctx_closer K lt m r x ζm q d g tid l E G G'.

  Definition pctx_acc_stmt {𝔅 𝔄} (K: pctx 𝔅 𝔄) (lt: lty 𝔅) : Prop :=
    ∀ m p r x ζm q d g tid l E G, lazyE ⊆ E → Timeless G →
    ⊢ llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ (G &&{↑NllftG}&&> @[pctx_ulft K lt]) -∗ G -∗
      £(pctx_acc_cred K m d) -∗
      ltype_own_cp false (pctx_plug K lt) (Owned m) (pctx_pat K p) (pctx_rfn K x ζm q r)
        d g tid l ={E}=∗ pctx_acc_res K lt m p r x ζm q d g tid l E G.

  Lemma pctx_acc_hole {𝔅} (lt: lty 𝔅) : pctx_acc_stmt PHole lt.
  Proof.
    iIntros (m p r x ζm q d g tid l E G ??) "_ _ _ _ G _ /= Own".
    iModIntro. iExists G, d, g. iSplitR; [done|]. iSplitL "G"; [done|].
    iSplitR; [iApply guards_refl|]. iSplitR; [iPureIntro; simpl; lia|].
    iSplitL "Own"; [done|]. iSplitR; [done|]. iSplitR; [done|].
    iSplitR. { iIntros "!>" (b k) "Gb". iApply (lguards_weaken_later with "Gb"). lia. }
    iIntros (lt' p' r' dh' gh' dn gn ζl' qq R _ _ _ _ (? & ? & ? & ?)) "_ _ G _ toks VS".
    iMod ("VS" with "toks") as "[Own $]". iFrame "G". iModIntro. simpl.
    iApply (ltype_own_cp_owned_depth_mono with "Own"); lia.
  Qed.

  Lemma pctx_acc_fst {𝔅 𝔄1 𝔄2} (K: pctx 𝔅 𝔄1) (lt2: lty 𝔄2) (lt: lty 𝔅) :
    pctx_acc_stmt K lt → pctx_acc_stmt (PFst K lt2) lt.
  Proof.
    iIntros (IH m p r x ζm q d g tid l E G ??) "#LFT #PROPH #UNIQ #Gk G £ /= [Own1 Own2]".
    rewrite lty_size_plug.
    iMod (IH with "LFT PROPH UNIQ Gk G £ Own1") as (G' dh gh) "(% & G' & #G'G & % & H & P & #Gs & #HG & Cl)";
      [done..|].
    iModIntro. iExists G', dh, gh. iSplitR; [done|]. iSplitL "G'"; [done|]. iSplitR; [done|].
    iSplitR; [iPureIntro; simpl in *; destruct_and!; split_and!; try lia; done|]. iSplitL "H"; [done|]. iSplitL "P"; [done|].
    iSplitR; [done|]. iSplitR.
    { iIntros "!>" (b k) "Gb". iApply ("HG" $! b k).
      rewrite (heap_cloc_mapsto_emp_vec_app l (pctx_size K (lty_size lt))).
      iApply (guards_weaken_rhs_sep_l with "Gb"). }
    iIntros (lt' p' r' dh' gh' dn gn ζl' qq R Hs Hf Hsz Hr (? & ? & ? & ?)) "Oks ⧖ G' P toks VS".
    iMod ("Cl" $! lt' p' r' dh' gh' dn gn ζl' qq R with "[//] [//] [//] [//] [%] Oks ⧖ G' P toks VS")
      as "(Own1 & $ & $)"; [done|].
    iModIntro. rewrite /= /prod_node lty_size_plug Hsz. iFrame "Own1".
    iApply (ltype_own_cp_owned_depth_mono with "Own2"); lia.
  Qed.

  Lemma pctx_acc_snd {𝔅 𝔄1 𝔄2} (lt1: lty 𝔄1) (K: pctx 𝔅 𝔄2) (lt: lty 𝔅) :
    pctx_acc_stmt K lt → pctx_acc_stmt (PSnd lt1 K) lt.
  Proof.
    iIntros (IH m p r x ζm q d g tid l E G ??) "#LFT #PROPH #UNIQ #Gk G £ /= [Own1 Own2]".
    iMod (IH with "LFT PROPH UNIQ Gk G £ Own2") as (G' dh gh) "(% & G' & #G'G & % & H & P & #Gs & #HG & Cl)";
      [done..|].
    iModIntro. iExists G', dh, gh. iSplitR; [done|]. iSplitL "G'"; [done|]. iSplitR; [done|].
    iSplitR; [iPureIntro; simpl in *; destruct_and!; split_and!; try lia; done|]. iSplitL "H"; [done|]. iSplitL "P"; [done|].
    iSplitR; [done|]. iSplitR.
    { iIntros "!>" (b k) "Gb". iApply ("HG" $! b k).
      rewrite (heap_cloc_mapsto_emp_vec_app l (lty_size lt1)).
      iApply (guards_weaken_rhs_sep_r with "Gb"). }
    iIntros (lt' p' r' dh' gh' dn gn ζl' qq R Hs Hf Hsz Hr (? & ? & ? & ?)) "Oks ⧖ G' P toks VS".
    iMod ("Cl" $! lt' p' r' dh' gh' dn gn ζl' qq R with "[//] [//] [//] [//] [%] Oks ⧖ G' P toks VS")
      as "(Own2 & $ & $)"; [done|].
    iModIntro. rewrite /= /prod_node. iFrame "Own2".
    iApply (ltype_own_cp_owned_depth_mono with "Own1"); lia.
  Qed.

  Lemma pctx_acc_own {𝔅 𝔄'} n (K: pctx 𝔅 𝔄') (lt: lty 𝔅) :
    pctx_acc_stmt K lt → pctx_acc_stmt (POwn n K) lt.
  Proof.
    iIntros (IH m p r x ζm q d g tid l E G ??) "#LFT #PROPH #UNIQ #Gk G £ /= (Pt & %Hd & Fr & Own)".
    rewrite lty_size_plug.
    iDestruct (lc_weaken (pctx_acc_cred K (m + 1) (pred d)) with "£") as "£";
      [rewrite /pctx_acc_cred /=; destruct (pctx_ulfts K); nia|].
    iMod (IH with "LFT PROPH UNIQ Gk G £ Own") as (G' dh gh) "(% & G' & #G'G & % & H & P & #Gs & #HG & Cl)";
      [done..|].
    iModIntro. iExists G', dh, gh. iSplitR; [done|]. iSplitL "G'"; [done|]. iSplitR; [done|].
    iSplitR; [iPureIntro; simpl in *; destruct_and!; split_and!; try lia; done|]. iSplitL "H"; [done|]. iSplitL "Pt P"; [iFrame|].
    iSplitR; [iApply (pctx_pguards_mono with "Gs"); lia|]. iSplitR.
    { iIntros "!>" (b k) "_". iApply ("HG" $! b k). iEval (rewrite -heap_cloc_mapsto_empty). iApply guards_true. }
    iIntros (lt' p' r' dh' gh' dn gn ζl' qq R Hs Hf Hsz Hr (? & ? & ? & ?)) "Oks #⧖ G' [Pt P] toks VS".
    iMod ("Cl" $! lt' p' r' dh' gh' (pred dn) gn ζl' qq R with "[//] [//] [//] [//] [%] Oks [] G' P toks VS")
      as "(Own & $ & $)"; [simpl in *; lia|..].
    { iApply (persistent_time_receipt_mono with "⧖"). lia. }
    iModIntro. rewrite /= /own_node lty_size_plug Hsz. iFrame "Pt Fr Own". iPureIntro. simpl in *. lia.
  Qed.

  Lemma pctx_acc_sum {𝔅 𝔄l} (tyl: typel 𝔄l) i w (K: pctx 𝔅 (𝔄l !!ₗ i)) (lt: lty 𝔅) :
    pctx_acc_stmt K lt → pctx_acc_stmt (PSum tyl i w K) lt.
  Proof.
    iIntros (IH m p r x ζm q d g tid l E G ??) "#LFT #PROPH #UNIQ #Gk G £ /= Own".
    rewrite /psum_proj_or. destruct (psum_proj i x.1) as [y|] eqn:Hy; [|by rewrite /sum_node].
    rewrite sum_node_sum lty_size_plug. iDestruct "Own" as "(Tag & Own & Pad)".
    iMod (IH with "LFT PROPH UNIQ Gk G £ Own") as (G' dh gh) "(% & G' & #G'G & % & H & P & #Gs & #HG & Cl)";
      [done..|].
    iModIntro. rewrite /pctx_acc_res /pctx_closer /= /psum_proj_or Hy. iExists G', dh, gh. iSplitR; [done|]. iSplitL "G'"; [done|]. iSplitR; [done|].
    iSplitR; [iPureIntro; simpl in *; destruct_and!; split_and!; try lia; done|]. iSplitL "H"; [done|]. iSplitL "P"; [done|].
    iSplitR; [done|]. iSplitR.
    { iIntros "!>" (b k) "Gb". iApply ("HG" $! b k).
      rewrite (heap_cloc_mapsto_emp_vec_app l 1).
      iDestruct (guards_weaken_rhs_sep_r with "Gb") as "Gb'".
      rewrite (heap_cloc_mapsto_emp_vec_app (cloc_skip l 1) (pctx_size K (lty_size lt))).
      iApply (guards_weaken_rhs_sep_l with "Gb'"). }
    iIntros (lt' p' r' dh' gh' dn gn ζl' qq R Hs Hf Hsz Hr (? & ? & ? & ?)) "Oks ⧖ G' P toks VS".
    iMod ("Cl" $! lt' p' r' dh' gh' dn gn ζl' qq R with "[//] [//] [//] [//] [%] Oks ⧖ G' P toks VS")
      as "(Own & $ & $)"; [done|].
    iModIntro. rewrite sum_node_sum lty_size_plug Hsz. iFrame.
  Qed.

  (** The hole is the whole referent of a unique borrow. *)
  Lemma pctx_acc_uniq_hole {𝔅} κ (lt: lty 𝔅) : pctx_acc_stmt (PUniq κ PHole) lt.
  Proof.
    iIntros (m p r x ζm q d g tid l E G ??) "_ _ _ #Gk G £ /= (Pt & ⧗ & #TIME & N)".
    iDestruct (lc_weaken m with "£") as "£"; [rewrite /pctx_acc_cred /=; nia|].
    iMod (lc_fupd_elim_laterN with "£ N") as "(#Incl & #Gpt & %d' & %g' & %Hle & C)".
    iModIntro. iExists G, d', g'. iSplitR; [done|]. iSplitL "G"; [done|].
    iSplitR; [iApply guards_refl|]. iSplitR; [iPureIntro; simpl in *; destruct_and!; split_and!; try lia; done|].
    iSplitL "C"; [done|]. iSplitL "Pt"; [by iFrame|]. iSplitR.
    { iSplit; [|done]. iApply (guards_transitive_right with "[] Gpt").
      iApply (guards_transitive with "Gk"). iApply llftl_intersect_incl_l. }
    iSplitR. { iIntros "!>" (b k) "_". iApply (lguards_weaken_later with "Gpt"). lia. }
    iIntros (lt' p' r' dh' gh' dn gn ζl' qq R Hs Hf Hsz Hr (? & ? & ? & ?)) "_ _ G [Pt _] toks VS".
    iMod ("VS" with "toks") as "[C $]". iFrame "G". iModIntro.
    rewrite /= /uniq_node Hf. iFrame "Pt ⧗ TIME". iApply bi.laterN_intro.
    iFrame "Incl". iSplit; [iApply (lguards_weaken_later with "Gpt"); lia|].
    iExists dh', gh'. iFrame "C". iPureIntro. simpl in *. lia.
  Qed.
  (** The hole is below a unique borrow whose referent is compound: the borrow is opened
      with half of the token, its contents are run with the other half, which is then used
      for the access to the hole inside the node. *)
  Lemma pctx_acc_uniq_cpd {𝔅 𝔄'} κ (K: pctx 𝔅 𝔄') (lt: lty 𝔅) :
    pctx_nonempty K → pctx_simple K → pctx_acc_stmt K lt → pctx_acc_stmt (PUniq κ K) lt.
  Proof.
    iIntros (HK HKs IH m p r x ζm q d g tid l E G HE ?) "#LFT #PROPH #UNIQ #Gk G £ /=".
    iIntros "(Pt & ⧗ & #TIME & N)".
    iDestruct (lc_weaken (m + (1 + ((d + 1) * (m + d + 2) - m - 1))) with "£") as "[£m [£1 £]]";
      [rewrite /pctx_acc_cred /=; nia|].
    iMod (lc_fupd_elim_laterN with "£m N") as "(#Incl & #Gpt & %d' & %g' & %Hle & C)".
    iDestruct (lc_weaken (pctx_acc_cred K 0 d') with "£") as "£";
      [have := pctx_acc_cred_le K 0 d'; nia|].
    rewrite ltype_own_cp_uniq_plug //.
    have ?: ↑NllftG ⊆ E. { trans lazyE; [apply lazyE_NllftG|done]. }
    have ?: ↑Nllft ∪ ↑prophN ⊆ E. { trans lazyE; [rewrite /lazyE; solve_ndisj|done]. }
    iMod (fractional.frac_split_guard_in_half NllftG G G with "G []")
      as (γh) "[H1 [H2 [#Gh #Back]]]"; [done|iApply guards_refl|].
    iAssert (fractional.half γh &&{↑NllftG}&&> @[κ])%I as "#Hκ".
    { iApply (guards_transitive with "Gh"). iApply (guards_transitive with "Gk").
      iApply llftl_intersect_incl_l. }
    iAssert (fractional.half γh &&{↑NllftG}&&> @[ty_lft (lty_fold (pctx_plug K lt))])%I as "#Hty".
    { iApply (guards_transitive with "Gh"). iApply (guards_transitive with "Gk").
      iApply llftl_intersect_incl_r. }
    iAssert (fractional.half γh &&{↑NllftG}&&> @[pctx_ulft K lt])%I as "#Hu".
    { iApply (guards_transitive with "Hty"). iApply pctx_ulft_incl. }
    iMod (cpd_rebody_gen with "LFT PROPH UNIQ Hκ H1 C") as (κp) "(#Inclp & #Ok & Upd & Close)";
      [done|].
    iMod (lc_fupd_elim_later with "£1 Upd") as "Upd".
    iMod (guarded_upd_run with "Hty H2 Upd") as "(H2 & #⧖' & N)"; [done|].
    iMod (IH with "LFT PROPH UNIQ Hu H2 £ N") as (G' dh gh) "(% & G' & #G'G & % & H & P & #Gs & #HG & Cl)";
      [done..|].
    iModIntro. iExists G', dh, gh. iSplitR; [done|]. iSplitL "G'"; [done|].
    iSplitR; [iApply (guards_transitive with "G'G Gh")|]. iSplitR; [iPureIntro; simpl in *; destruct_and!; split_and!; try lia; done|].
    rewrite /pctx_closer /= pctx_kind_nonempty //. iSplitL "H"; [done|]. iSplitL "Pt P"; [iFrame|]. iSplitR.
    { iSplit.
      - iApply (guards_transitive_right with "[] Gpt").
        iApply (guards_transitive with "G'G Hκ").
      - iApply (pctx_pguards_mono with "Gs"). lia. }
    iSplitR.
    { iIntros "!>" (b k) "_". iApply (lguards_weaken_later with "[]"); last first.
      { iApply ("HG" with "Gpt"). } lia. }
    iIntros (lt' p' r' dh' gh' dn gn ζl' qq R Hs Hf Hsz Hr (? & ? & ? & ?)) "[#Okκ Oks] #⧖ G' [Pt P] toks VS".
    have Hf': lty_fold (pctx_plug K lt') = lty_fold (pctx_plug K lt) by apply lty_fold_plug_eq'.
    iMod ("Close" $! (ltype_own_cp false (pctx_plug K lt') (Owned 0)) (pctx_pat K p')
      (pctx_rfn K (uniq_bor_current x) ζm (false :: q) r') (pred dn) gn ζl' qq
      (fractional.half γh ∗ R)%I with "[%] [] toks [VS G' P Oks Cl]") as "(C' & H1 & H2 & $)".
    { intros ζl. apply pctx_rfn_rsv_mono; [set_solver|]. apply Hr. }
    { iIntros "!>" (p2 r2 d2 g2) "Ok2 ⧖2 N". rewrite -Hf'.
      iApply (ltype_owned_leaf_node with "LFT PROPH UNIQ Ok2 ⧖2 N");
        [by apply lty_is_cpd_plug_nonempty'|by apply lty_simple_plug]. }
    { iIntros "toks".
      iMod ("Cl" $! lt' p' r' dh' gh' (pred dn) gn ζl' qq R with "[//] [//] [//] [//] [%] Oks [] G' P toks VS")
        as "(N' & $ & $)"; [simpl in *; lia|..].
      { iApply (persistent_time_receipt_mono with "⧖"). lia. }
      iModIntro. iSplitR.
      - iNext. iApply (pat_ok_plug with "Ok"). iApply (pat_ok_mono with "Inclp Okκ").
      - iNext. iApply guarded_upd_intro. iModIntro. iFrame "N'".
        iApply (persistent_time_receipt_mono with "⧖"). lia. }
    iMod (fupd_mask_mono with "(Back H1 H2)") as "$"; [done|].
    iModIntro. rewrite /= /uniq_node Hf'. iFrame "Pt ⧗ TIME". iApply bi.laterN_intro.
    iFrame "Incl". iSplit; [iApply (lguards_weaken_later with "Gpt"); lia|].
    iExists (pred dn), gn. iSplit; [iPureIntro; lia|].
    iEval (rewrite (ltype_own_cp_uniq_plug K) // Hf'). iExact "C'".
  Qed.

  (** The hole must be owned: below no shared reference. *)
  Lemma pctx_acc {𝔅 𝔄} (K: pctx 𝔅 𝔄) `{!PctxNoShr K} (lt: lty 𝔅) : pctx_acc_stmt K lt.
  Proof.
    rename select (PctxNoShr K) into HK. rewrite /PctxNoShr in HK.
    induction K; simpl in HK; [apply pctx_acc_hole|apply pctx_acc_fst; by apply IHK|
      apply pctx_acc_snd; by apply IHK|apply pctx_acc_own; by apply IHK|
      apply pctx_acc_sum; by apply IHK| |done].
    destruct HK as [HKs HK].
    destruct K; [apply pctx_acc_uniq_hole|apply pctx_acc_uniq_cpd; [done|done|by apply IHK]..|done].
  Qed.
End pctx_acc.
