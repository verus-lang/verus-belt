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
  - the pointer cells on the path ([pctx_ptrs]) are handed out, so that the address of the hole can be
    computed ([wp_pctx_ptrs], one load per owned pointer or unique borrow, as [pctx_expr]);
  - the closer ([pctx_closer]) takes a new hole (of the same folded type and size, so the
    core may change: the bodies are switched with [cpd_rebody_gen]), whose blocked lifetimes
    are included in all enclosing borrow lifetimes ([pctx_ulfts]), and whose refinement may
    depend on new prophecy variables [ζl']: their tokens are passed through the closers of
    all enclosing borrows (each extends its reservation), from the outermost to the
    innermost, to a view shift that produces the new hole. The root may get larger depths.
    The blocked lifetimes of the new hole need not be included in the enclosing borrow
    lifetimes if its pattern is the one of the old hole (e.g. when the hole is only read).

  See [design_docs/verus-belt-phase3-design.md], section "PUniq". *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var.
From lrust.lang Require Import proofmode.
From lrust.typing Require Export type ltype lpath.
From lrust.typing Require Import uniq_util uniq_bor own shr_bor bytes_layout value_ctx freeable_util.
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
    | PSum _ i w K => λ k x, pctx_kind K (Owned (kind_laters k)) (psum_proj_or i x w)
    | PUniq κ K => λ _ x, pctx_kind K (Uniq κ (uniq_bor_ξi x)) (uniq_bor_current x)
    (* Only meaningful below no shared reference ([PctxNoShr]); as [POwn]. *)
    | PShr _ K => λ k x, pctx_kind K (Owned (kind_laters k + 1)) x.2
    (* Only meaningful below no resolved unique borrow ([PctxNoShr]); as [POwn]. *)
    | PResUniq _ K => λ k x, pctx_kind K (Owned (kind_laters k + 1)) (uniq_bor_current x)
    end.

  (** The lifetime of the folded type at the outermost unique borrow on the path (which
      includes all enclosing borrow lifetimes and the lifetimes of their referents), or
      [static] if there is none. *)
  Fixpoint pctx_ulft {𝔅 𝔄} (K: pctx 𝔅 𝔄) : lty 𝔅 → lft :=
    match K in pctx 𝔅 𝔄 return lty 𝔅 → lft with
    | PHole => λ _, static
    | PFst K _ | PSnd _ K | POwn _ K | PSum _ _ _ K | PShr _ K | PResUniq _ K => pctx_ulft K
    | PUniq κ K => λ lt, ty_lft (lty_fold (UniqLty (pctx_plug K lt) κ))
    end.

  (** The lifetimes of the enclosing unique borrows, outermost first. *)
  Fixpoint pctx_ulfts {𝔅 𝔄} (K: pctx 𝔅 𝔄) : list lft :=
    match K with
    | PHole => []
    | PFst K _ | PSnd _ K | POwn _ K | PSum _ _ _ K | PShr _ K | PResUniq _ K => pctx_ulfts K
    | PUniq κ K => κ :: pctx_ulfts K
    end.

  (** The lifetime of the shared view of the hole of [K], below a shared reference (or a
      resolved unique borrow) at [κ]: a unique borrow at [κ'] gives [κ ⊓ κ'] (its sharing
      predicate), a shared reference at [κ'] gives [κ'] (its ownership predicate is
      persistent). *)
  Fixpoint pctx_slft {𝔅 𝔄} (K: pctx 𝔅 𝔄) (κ: lft) : lft :=
    match K with
    | PHole => κ
    | PFst K _ | PSnd _ K | POwn _ K | PSum _ _ _ K => pctx_slft K κ
    | PUniq κ' K | PResUniq κ' K => pctx_slft K (κ ⊓ κ')
    | PShr κ' K => pctx_slft K κ'
    end.

  (** The lifetimes that must be alive to load the pointers on the path below a shared
      reference (or a resolved unique borrow) at [κ], and the hole: their intersection. *)
  Fixpoint pctx_salv {𝔅 𝔄} (K: pctx 𝔅 𝔄) (κ: lft) : lft :=
    match K with
    | PHole => κ
    | PFst K _ | PSnd _ K | POwn _ K | PSum _ _ _ K => pctx_salv K κ
    | PUniq κ' K | PResUniq κ' K => pctx_salv K (κ ⊓ κ')
    | PShr κ' K => κ ⊓ pctx_salv K κ'
    end.

  (** The lifetimes that must be alive to access the hole of [K] (to read, write, share or
      borrow it): at each unique borrow above the first shared reference or resolved unique
      borrow, the lifetime of its folded type (to open it, [pctx_ulft]); at the first shared
      reference or resolved unique borrow at [κ], [pctx_salv K' κ] (the guarded loads of the
      pointers of the view). [static] for an owned path. *)
  Fixpoint pctx_alv {𝔅 𝔄} (K: pctx 𝔅 𝔄) : lty 𝔅 → lft :=
    match K in pctx 𝔅 𝔄 return lty 𝔅 → lft with
    | PHole => λ _, static
    | PFst K _ | PSnd _ K | POwn _ K | PSum _ _ _ K => pctx_alv K
    | PUniq κ K => λ lt, ty_lft (lty_fold (UniqLty (pctx_plug K lt) κ)) ⊓ pctx_alv K lt
    | PShr κ K | PResUniq κ K => λ _, pctx_salv K κ
    end.

  (** The lifetime of the view of the hole at the first shared reference or resolved unique
      borrow on the path, if any. *)
  Fixpoint pctx_vlft {𝔅 𝔄} (K: pctx 𝔅 𝔄) : option lft :=
    match K with
    | PHole => None
    | PFst K _ | PSnd _ K | POwn _ K | PSum _ _ _ K | PUniq _ K => pctx_vlft K
    | PShr κ K | PResUniq κ K => Some (pctx_slft K κ)
    end.

  (** The bound of the lifetime of a borrow of the hole of [K]: the lifetime of the view of
      the hole below the first shared reference or resolved unique borrow, if any
      ([pctx_vlft]; the unique borrows above it do not matter, e.g. [&**x: &'b T] for
      [x: &'a mut &'b T]); otherwise the intersection of the enclosing unique borrow
      lifetimes ([static] for an owned path). *)
  Fixpoint pctx_blft {𝔅 𝔄} (K: pctx 𝔅 𝔄) : lft :=
    match K with
    | PHole => static
    | PFst K _ | PSnd _ K | POwn _ K | PSum _ _ _ K => pctx_blft K
    | PUniq κ K => match pctx_vlft K with Some β => β | None => κ ⊓ pctx_blft K end
    | PShr κ K | PResUniq κ K => pctx_slft K κ
    end.

  (** The number of owned pointers and unique borrows on the path (the depth decreases by
      at least one at each). *)
  Fixpoint pctx_dlev {𝔅 𝔄} (K: pctx 𝔅 𝔄) : nat :=
    match K with
    | PHole => 0
    | PFst K _ | PSnd _ K | PSum _ _ _ K => pctx_dlev K
    | POwn _ K | PUniq _ K | PShr _ K | PResUniq _ K => S (pctx_dlev K)
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
    | PFst K _ | PSnd _ K | POwn _ K | PSum _ _ _ K | PShr _ K | PResUniq _ K => pctx_uend K
    | PUniq κ K => match K with PHole => Some κ | _ => pctx_uend K end
    end.

  (** The number of laters of the hole, if it is in [Owned] mode. *)
  Fixpoint pctx_hmode {𝔅 𝔄} (K: pctx 𝔅 𝔄) (m: nat) : nat :=
    match K with
    | PHole => m
    | PFst K _ | PSnd _ K | PSum _ _ _ K => pctx_hmode K m
    | POwn _ K | PShr _ K | PResUniq _ K => pctx_hmode K (m + 1)
    | PUniq _ K => pctx_hmode K 0
    end.

  (** The prophecy id of the innermost unique borrow, if the hole is its whole referent. *)
  Fixpoint pctx_hξi {𝔅 𝔄} (K: pctx 𝔅 𝔄) : ~~𝔄 → positive :=
    match K in pctx 𝔅 𝔄 return ~~𝔄 → positive with
    | PHole => λ _, 1%positive
    | PFst K _ => λ x, pctx_hξi K x.1
    | PSnd _ K | POwn _ K | PShr _ K => λ x, pctx_hξi K x.2
    | PResUniq _ K => λ x, pctx_hξi K (uniq_bor_current x)
    | PSum _ i w K => λ x, pctx_hξi K (psum_proj_or i x w)
    | PUniq _ K => λ x, match K with
        | PHole => uniq_bor_ξi x
        | _ => pctx_hξi K (uniq_bor_current x)
        end
    end.

  (** The pointer cells on the path. *)
  Fixpoint pctx_ptrs {𝔅 𝔄} (K: pctx 𝔅 𝔄) (n: nat) : ~~𝔄 → loc → iProp Σ :=
    match K in pctx 𝔅 𝔄 return ~~𝔄 → loc → iProp Σ with
    | PHole => λ _ _, True
    | PFst K _ => λ x l, pctx_ptrs K n x.1 l
    | PSnd lt1 K => λ x l, pctx_ptrs K n x.2 (l +ₗ lty_size lt1)
    | POwn _ K => λ x l, ptr_cell l x.1 ∗
        pctx_ptrs K n x.2 x.1
    | @PSum _ _ _ 𝔄l _ i w K => λ x l,
        pctx_ptrs K n (psum_proj_or i x w) (l +ₗ tag_size 𝔄l)
    | PUniq _ K => λ x l, ptr_cell l (uniq_bor_loc x) ∗
        pctx_ptrs K n (uniq_bor_current x) (uniq_bor_loc x)
    | PShr _ K => λ x l, ptr_cell l x.1 ∗ pctx_ptrs K n x.2 x.1
    | PResUniq _ K => λ x l, ptr_cell l (uniq_bor_loc x) ∗
        pctx_ptrs K n (uniq_bor_current x) (uniq_bor_loc x)
    end%I.

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
    induction K in m, x |- *; simpl; [done|auto|auto|auto|auto| |auto|auto].
    destruct K; [done| | | | | |intros H; exact (IHK 0 _ H)|intros H; exact (IHK 0 _ H)];
      intros; rewrite pctx_kind_nonempty //; by apply IHK.
  Qed.

  Lemma pctx_kind_uniq {𝔅 𝔄} (K: pctx 𝔅 𝔄) κ m x :
    pctx_uend K = Some κ → pctx_kind K (Owned m) x = Uniq κ (pctx_hξi K x).
  Proof.
    induction K in m, x |- *; simpl; [done|auto|auto|auto|auto| |auto|auto].
    destruct K; [by intros [= ->]| | | | | |intros H; exact (IHK 0 _ H)|
      intros H; exact (IHK 0 _ H)];
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
    - rewrite psum_proj_or_pinj /psum_proj_or. destruct (psum_proj i x); [|done].
      intros. by rewrite IHK.
    - intros. by rewrite uniq_bor_current_set uniq_bor_ξi_set IHK.
    - intros. by rewrite uniq_bor_current_set IHK.
  Qed.

  Lemma pctx_hξi_set {𝔅 𝔄} (K: pctx 𝔅 𝔄) x y :
    pctx_in K x → pctx_hξi K (pctx_set K x y) = pctx_hξi K x.
  Proof.
    induction K in x, y |- *; simpl; try (intros; by rewrite ?IHK).
    - rewrite psum_proj_or_pinj /psum_proj_or. destruct (psum_proj i x); [|done].
      intros. by rewrite IHK.
    - destruct K; intros; by rewrite ?uniq_bor_current_set ?uniq_bor_ξi_set ?IHK.
    - intros. by rewrite uniq_bor_current_set IHK.
  Qed.

  Lemma pctx_ulft_incl {𝔅 𝔄} (K: pctx 𝔅 𝔄) lt :
    ⊢ ty_lft (lty_fold (pctx_plug K lt)) ⊑ pctx_ulft K lt.
  Proof.
    induction K; simpl; [iApply lft_incl_static| | | | |iApply guards_refl|
      iApply llftl_incl_trans; [iApply llftl_intersect_incl_r|iApply IHK]..];
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
      by auto|by auto| |by auto|by auto].
    apply elem_of_cons in Hκ as [->|Hκ].
    - iApply llftl_intersect_incl_l.
    - iApply llftl_incl_trans; [iApply llftl_intersect_incl_r|].
      iApply llftl_incl_trans; [iApply pctx_ulft_incl|]. by iApply IHK.
  Qed.

  Lemma pctx_salv_incl {𝔅 𝔄} (K: pctx 𝔅 𝔄) κ : ⊢ pctx_salv K κ ⊑ κ.
  Proof.
    induction K in κ |- *; simpl; [iApply guards_refl|by iApply IHK|by iApply IHK|by iApply IHK|
      by iApply IHK| | |].
    - iApply llftl_incl_trans; [iApply IHK|]. iApply llftl_intersect_incl_l.
    - iApply llftl_intersect_incl_l.
    - iApply llftl_incl_trans; [iApply IHK|]. iApply llftl_intersect_incl_l.
  Qed.

  Lemma pctx_salv_slft {𝔅 𝔄} (K: pctx 𝔅 𝔄) κ : ⊢ pctx_salv K κ ⊑ pctx_slft K κ.
  Proof.
    induction K in κ |- *; simpl; [iApply guards_refl|by iApply IHK|by iApply IHK|by iApply IHK|
      by iApply IHK|by iApply IHK| |by iApply IHK].
    iApply llftl_incl_trans; [iApply llftl_intersect_incl_r|]. iApply IHK.
  Qed.

  Lemma pctx_alv_noshr {𝔅 𝔄} (K: pctx 𝔅 𝔄) lt :
    pctx_noshr K → ⊢ pctx_alv K lt ⊑ pctx_ulft K lt.
  Proof.
    induction K; simpl; [iIntros; iApply guards_refl|auto|auto|auto|auto| |done|done]. intros _.
    iApply llftl_intersect_incl_l.
  Qed.

  Lemma pctx_alv_nouniq {𝔅 𝔄} (K: pctx 𝔅 𝔄) `{!PctxNoUniq K} lt : pctx_alv K lt = static.
  Proof.
    rename select (PctxNoUniq K) into HK. rewrite /PctxNoUniq in HK.
    induction K in HK, lt |- *; simpl; simpl in HK; auto; done.
  Qed.

  Lemma pctx_vlft_noshr {𝔅 𝔄} (K: pctx 𝔅 𝔄) : pctx_noshr K → pctx_vlft K = None.
  Proof. induction K; simpl; [done|auto|auto|auto|auto| |done|done]. intros [_ HK]. auto. Qed.

  Lemma pctx_vlft_app {ℭ 𝔅 𝔄} (K1: pctx 𝔅 𝔄) (K2: pctx ℭ 𝔅) :
    pctx_noshr K1 → pctx_vlft (pctx_app K1 K2) = pctx_vlft K2.
  Proof.
    induction K1 in K2 |- *; simpl; [done|auto|auto|auto|auto| |done|done]. intros [_ HK]. auto.
  Qed.

  (** Below a shared reference or a resolved unique borrow, [pctx_blft] is the lifetime of
      the view. *)
  Lemma pctx_blft_app_view {ℭ 𝔅 𝔄} (K1: pctx 𝔅 𝔄) (K2: pctx ℭ 𝔅) β :
    pctx_noshr K1 → pctx_vlft K2 = Some β → pctx_blft K2 = β →
    pctx_blft (pctx_app K1 K2) = β.
  Proof.
    induction K1 in K2 |- *; simpl; [done|auto|auto|auto|auto| |done|done].
    intros [_ HK] Hv Hb. rewrite pctx_vlft_app // Hv. done.
  Qed.

  (** Every enclosing borrow lifetime, above the first shared reference, outlives
      [pctx_blft]. *)
  Lemma pctx_blft_incl {𝔅 𝔄} (K: pctx 𝔅 𝔄) κ :
    pctx_noshr K → κ ∈ pctx_ulfts K → ⊢ pctx_blft K ⊑ κ.
  Proof.
    induction K; simpl; intros HK Hκ; [by apply not_elem_of_nil in Hκ|by auto|by auto|by auto|
      by auto| |done|done].
    destruct HK as [_ HK]. rewrite pctx_vlft_noshr //. apply elem_of_cons in Hκ as [->|Hκ].
    - iApply llftl_intersect_incl_l.
    - iApply llftl_incl_trans; [iApply llftl_intersect_incl_r|]. by iApply IHK.
  Qed.

  (** A new blocked (or shared-blocked) lifetime [α] below [pctx_blft K] is below every
      enclosing borrow lifetime. *)
  Lemma pat_ok_blft {𝔅 𝔄} (K: pctx 𝔅 𝔄) α p :
    pctx_noshr K → pat_blk_lfts p = [α] →
    α ⊑ pctx_blft K -∗ [∗ list] κ ∈ pctx_ulfts K, pat_ok κ p.
  Proof.
    iIntros (HK Hp) "#Incl". iApply big_sepL_intro. iIntros "!>" (i κ Hi).
    rewrite /pat_ok Hp big_sepL_singleton. iApply (llftl_incl_trans with "Incl").
    iApply pctx_blft_incl; [done|]. by eapply elem_of_list_lookup_2.
  Qed.

  Lemma pat_ok_ulfts_leaf {𝔅 𝔄} (K: pctx 𝔅 𝔄) :
    ⊢ [∗ list] κ ∈ pctx_ulfts K, pat_ok κ PatLeaf.
  Proof. iApply big_sepL_intro. iIntros "!>" (i κ Hi). iApply pat_ok_leaf. Qed.

  Lemma pctx_dlev_nouniq {𝔅 𝔄} (K: pctx 𝔅 𝔄) `{!PctxNoUniq K} : pctx_dlev K = pctx_mode K 0.
  Proof.
    rename select (PctxNoUniq K) into HK. rewrite /PctxNoUniq in HK.
    induction K in HK |- *; simpl; simpl in HK; auto; [|done|done|done].
    rewrite IHK // (pctx_mode_add K (0 + 1)). lia.
  Qed.

  Lemma pctx_ptrs_set {𝔅 𝔄} (K: pctx 𝔅 𝔄) n x y l :
    pctx_in K x → pctx_ptrs K n (pctx_set K x y) l = pctx_ptrs K n x l.
  Proof.
    induction K in x, y, l |- *; simpl; try (intros; by rewrite ?IHK).
    - rewrite psum_proj_or_pinj /psum_proj_or. destruct (psum_proj i x); [|done].
      intros. by rewrite IHK.
    - intros. by rewrite uniq_bor_current_set uniq_bor_loc_set IHK.
    - intros. by rewrite uniq_bor_current_set uniq_bor_loc_set IHK.
  Qed.

  Lemma pctx_ulfts_nouniq {𝔅 𝔄} (K: pctx 𝔅 𝔄) `{!PctxNoUniq K} : pctx_ulfts K = [].
  Proof.
    rename select (PctxNoUniq K) into HK. rewrite /PctxNoUniq in HK.
    induction K in HK |- *; simpl; simpl in HK; auto; done.
  Qed.

End pctx_fun.

(** * The address of the hole *)

Section wp_pctx.
  Context `{!typeG Σ}.

  Lemma wp_pctx_ptrs {𝔅 𝔄} E (K: pctx 𝔅 𝔄) n (G: iProp Σ) x (l: loc) (e: expr) (R: iProp Σ) :
    WP e @ E {{ v, ⌜v = #(l)⌝ ∗ R ∗ G }} -∗ pctx_ptrs K n x l -∗
    WP pctx_expr K e @ E {{ v, ⌜v = #(pctx_loc K n x l)⌝ ∗ R ∗ G ∗ pctx_ptrs K n x l }}.
  Proof.
    induction K in x, l, e, R |- *; simpl.
    - iIntros "WP $". iApply (wp_wand with "WP"). iIntros (v) "($ & $ & $)".
    - iIntros "WP Ptrs". iApply (IHK x.1 l with "WP Ptrs").
    - iIntros "WP Ptrs".
      iApply (IHK x.2 (l +ₗ lty_size lt1) _ R with "[WP] Ptrs").
      wp_bind e. iApply (wp_wand with "WP"). iIntros (v) "(-> & R & G)". wp_op.
      iFrame. done.
    - iIntros "WP (Pt & Ptrs)".
      iApply (wp_wand with "[- ]").
      { iApply (IHK x.2 x.1 _
          (R ∗ ptr_cell l x.1)%I with "[WP Pt] Ptrs").
        wp_bind e. iApply (wp_wand with "WP"). iIntros (v) "(-> & R & G)".
        iDestruct "Pt" as (bs) "[Hbs %Hbs]". wp_bind (Load _ _ _).
        iApply (wp_load_na with "Hbs"); [exact Hbs|].
        iIntros "!> Hbs". wp_pure _. iSplit; [done|]. by iFrame. }
      iIntros (v) "($ & [$ $] & $ & $)".
    - iIntros "WP Ptrs".
      iApply (IHK (psum_proj_or i x w) (l +ₗ tag_size 𝔄l) _ R
        with "[WP] Ptrs").
      wp_bind e. iApply (wp_wand with "WP"). iIntros (v) "(-> & R & G)". wp_op.
      iFrame. done.
    - iIntros "WP (Pt & Ptrs)".
      iApply (wp_wand with "[- ]").
      { iApply (IHK (uniq_bor_current x) (uniq_bor_loc x) _
          (R ∗ ptr_cell l (uniq_bor_loc x))%I with "[WP Pt] Ptrs").
        wp_bind e. iApply (wp_wand with "WP"). iIntros (v) "(-> & R & G)".
        iDestruct "Pt" as (bs) "[Hbs %Hbs]". wp_bind (Load _ _ _).
        iApply (wp_load_na with "Hbs"); [exact Hbs|].
        iIntros "!> Hbs". wp_pure _. iSplit; [done|]. by iFrame. }
      iIntros (v) "($ & [$ $] & $ & $)".
    - iIntros "WP (Pt & Ptrs)".
      iApply (wp_wand with "[- ]").
      { iApply (IHK x.2 x.1 _ (R ∗ ptr_cell l x.1)%I with "[WP Pt] Ptrs").
        wp_bind e. iApply (wp_wand with "WP"). iIntros (v) "(-> & R & G)".
        iDestruct "Pt" as (bs) "[Hbs %Hbs]". wp_bind (Load _ _ _).
        iApply (wp_load_na with "Hbs"); [exact Hbs|].
        iIntros "!> Hbs". wp_pure _. iSplit; [done|]. by iFrame. }
      iIntros (v) "($ & [$ $] & $ & $)".
    - iIntros "WP (Pt & Ptrs)".
      iApply (wp_wand with "[- ]").
      { iApply (IHK (uniq_bor_current x) (uniq_bor_loc x) _
          (R ∗ ptr_cell l (uniq_bor_loc x))%I with "[WP Pt] Ptrs").
        wp_bind e. iApply (wp_wand with "WP"). iIntros (v) "(-> & R & G)".
        iDestruct "Pt" as (bs) "[Hbs %Hbs]". wp_bind (Load _ _ _).
        iApply (wp_load_na with "Hbs"); [exact Hbs|].
        iIntros "!> Hbs". wp_pure _. iSplit; [done|]. by iFrame. }
      iIntros (v) "($ & [$ $] & $ & $)".
  Qed.
End wp_pctx.

(** * Opening a compound place, switching to a node chosen when closing *)

Section cpd_gen.
  Context `{!typeG Σ}.

  (** As [cpd_rebody_ext], with the new node chosen by the closer. *)
  Lemma cpd_rebody_gen {𝔄} κ ξi (ty: type 𝔄) p
      (node: lpat → prfn 𝔄 → nat → nat → thread_id → loc → iProp Σ)
      (r: prfn 𝔄) d g tid l E G :
    Timeless G → ↑Nllft ∪ ↑prophN ⊆ E →
    llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ (G &&{↑NllftG}&&> @[κ]) -∗ G -∗
    cpd_own κ ξi ty p node r d g tid l ={E}=∗ ∃ κp,
      uniq_pat_lft κ κp ∗ ▷ pat_ok κp p ∗
      ▷ guarded_upd lazyE @[ty_lft ty] (⧖(S d `max` g) ∗ node p r d g tid l) ∗
      (∀ (node': lpat → prfn 𝔄 → nat → nat → thread_id → loc → iProp Σ)
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
  Definition pctx_closer {𝔅 𝔄} (K: pctx 𝔅 𝔄) (lt: lty 𝔅) (m: nat) (p: lpat) (r: prfn 𝔅)
      (x: ~~𝔄) (ζm: blk_map) (q: lpath) (d g: nat) (tid: thread_id) (l: loc) (E: coPset)
      (G G': iProp Σ) : iProp Σ :=
    ∀ (lt': lty 𝔅) p' r' dh' gh' dn gn ζl' (qq: Qp) (R: iProp Σ),
      ⌜lty_simple lt'⌝ -∗ ⌜lty_fold lt' = lty_fold lt⌝ -∗ ⌜lty_size lt' = lty_size lt⌝ -∗
      ⌜∀ ζl, prfn_rsv r ζl → prfn_rsv r' (ζl ++ ζl')⌝ -∗
      ⌜d ≤ dn ∧ g ≤ gn ∧ dh' + pctx_dlev K ≤ dn ∧ gh' ≤ gn⌝ -∗
      (⌜p' = p⌝ ∨ [∗ list] κ ∈ pctx_ulfts K, pat_ok κ p') -∗
      ⧖(S dn `max` gn) -∗ G' -∗ pctx_ptrs K (lty_size lt) x l -∗ qq:+[ζl'] -∗
      (qq:+[ζl'] ={E}=∗ ltype_own_cp false lt' (pctx_kind K (Owned m) x) p' r' dh' gh' tid
          (pctx_loc K (lty_size lt) x l) ∗ R) ={E}=∗
      ltype_own_cp false (pctx_plug K lt') (Owned m) (pctx_pat K p') (pctx_rfn K x ζm q r')
        dn gn tid l ∗ G ∗ R.

  (** The result of an access. *)
  Definition pctx_acc_res {𝔅 𝔄} (K: pctx 𝔅 𝔄) (lt: lty 𝔅) (m: nat) (p: lpat) (r: prfn 𝔅)
      (x: ~~𝔄) (ζm: blk_map) (q: lpath) (d g: nat) (tid: thread_id) (l: loc) (E: coPset)
      (G: iProp Σ) : iProp Σ :=
    ∃ (G': iProp Σ) dh gh, ⌜Timeless G'⌝ ∗ G' ∗ (G' &&{↑NllftG}&&> G) ∗
      ⌜dh + pctx_dlev K ≤ d ∧ gh ≤ g ∧ pctx_in K x⌝ ∗
      ltype_own_cp false lt (pctx_kind K (Owned m) x) p r dh gh tid (pctx_loc K (lty_size lt) x l) ∗
      pctx_ptrs K (lty_size lt) x l ∗
      pctx_closer K lt m p r x ζm q d g tid l E G G'.

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
    iSplitL "Own"; [done|]. iSplitR; [done|].
    iIntros (lt' p' r' dh' gh' dn gn ζl' qq R _ _ _ _ (? & ? & ? & ?)) "_ _ G _ toks VS".
    iMod ("VS" with "toks") as "[Own $]". iFrame "G". iModIntro. simpl.
    iApply (ltype_own_cp_owned_depth_mono with "Own"); lia.
  Qed.

  Lemma pctx_acc_fst {𝔅 𝔄1 𝔄2} (K: pctx 𝔅 𝔄1) (lt2: lty 𝔄2) (lt: lty 𝔅) :
    pctx_acc_stmt K lt → pctx_acc_stmt (PFst K lt2) lt.
  Proof.
    iIntros (IH m p r x ζm q d g tid l E G ??) "#LFT #PROPH #UNIQ #Gk G £ /= [Own1 Own2]".
    rewrite lty_size_plug.
    iMod (IH with "LFT PROPH UNIQ Gk G £ Own1") as (G' dh gh) "(% & G' & #G'G & % & H & P & Cl)";
      [done..|].
    iModIntro. iExists G', dh, gh. iSplitR; [done|]. iSplitL "G'"; [done|]. iSplitR; [done|].
    iSplitR; [iPureIntro; simpl in *; destruct_and!; split_and!; try lia; done|]. iSplitL "H"; [done|]. iSplitL "P"; [done|].
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
    iMod (IH with "LFT PROPH UNIQ Gk G £ Own2") as (G' dh gh) "(% & G' & #G'G & % & H & P & Cl)";
      [done..|].
    iModIntro. iExists G', dh, gh. iSplitR; [done|]. iSplitL "G'"; [done|]. iSplitR; [done|].
    iSplitR; [iPureIntro; simpl in *; destruct_and!; split_and!; try lia; done|]. iSplitL "H"; [done|]. iSplitL "P"; [done|].
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
    iMod (IH with "LFT PROPH UNIQ Gk G £ Own") as (G' dh gh) "(% & G' & #G'G & % & H & P & Cl)";
      [done..|].
    iModIntro. iExists G', dh, gh. iSplitR; [done|]. iSplitL "G'"; [done|]. iSplitR; [done|].
    iSplitR; [iPureIntro; simpl in *; destruct_and!; split_and!; try lia; done|]. iSplitL "H"; [done|]. iSplitL "Pt P"; [iFrame|].
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
    rewrite /psum_proj_or. destruct (psum_proj i x) as [y|] eqn:Hy; [|by rewrite /sum_node].
    rewrite sum_node_sum lty_size_plug. iDestruct "Own" as "(Tag & Own & Pad)".
    iMod (IH with "LFT PROPH UNIQ Gk G £ Own") as (G' dh gh) "(% & G' & #G'G & % & H & P & Cl)";
      [done..|].
    iModIntro. rewrite /pctx_acc_res /pctx_closer /= /psum_proj_or Hy. iExists G', dh, gh. iSplitR; [done|]. iSplitL "G'"; [done|]. iSplitR; [done|].
    iSplitR; [iPureIntro; simpl in *; destruct_and!; split_and!; try lia; done|]. iSplitL "H"; [done|]. iSplitL "P"; [done|].
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
    iMod (lc_fupd_elim_laterN with "£ N") as "(#Incl & %d' & %g' & %Hle & C)".
    iModIntro. iExists G, d', g'. iSplitR; [done|]. iSplitL "G"; [done|].
    iSplitR; [iApply guards_refl|]. iSplitR; [iPureIntro; simpl in *; destruct_and!; split_and!; try lia; done|].
    iSplitL "C"; [done|]. iSplitL "Pt"; [by iFrame|].
    iIntros (lt' p' r' dh' gh' dn gn ζl' qq R Hs Hf Hsz Hr (? & ? & ? & ?)) "_ _ G [Pt _] toks VS".
    iMod ("VS" with "toks") as "[C $]". iFrame "G". iModIntro.
    rewrite /= /uniq_node Hf. iFrame "Pt ⧗ TIME". iApply bi.laterN_intro.
    iFrame "Incl". iExists dh', gh'. iFrame "C". iPureIntro. simpl in *. lia.
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
    iMod (lc_fupd_elim_laterN with "£m N") as "(#Incl & %d' & %g' & %Hle & C)".
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
    iMod (IH with "LFT PROPH UNIQ Hu H2 £ N") as (G' dh gh) "(% & G' & #G'G & % & H & P & Cl)";
      [done..|].
    iModIntro. iExists G', dh, gh. iSplitR; [done|]. iSplitL "G'"; [done|].
    iSplitR; [iApply (guards_transitive with "G'G Gh")|]. iSplitR; [iPureIntro; simpl in *; destruct_and!; split_and!; try lia; done|].
    rewrite /pctx_closer /= pctx_kind_nonempty //. iSplitL "H"; [done|]. iSplitL "Pt P"; [iFrame|].
    iIntros (lt' p' r' dh' gh' dn gn ζl' qq R Hs Hf Hsz Hr (? & ? & ? & ?)) "Oks #⧖ G' [Pt P] toks VS".
    iAssert (▷ pat_ok κp (pctx_pat K p'))%I as "#Ok'".
    { iDestruct "Oks" as "[->|[Okκ _]]"; [done|].
      iNext. iApply (pat_ok_plug with "Ok"). iApply (pat_ok_mono with "Inclp Okκ"). }
    iAssert (⌜p' = p⌝ ∨ [∗ list] κ ∈ pctx_ulfts K, pat_ok κ p')%I with "[Oks]" as "Oks".
    { iDestruct "Oks" as "[$|[_ $]]". }
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
      iModIntro. iSplitR; [done|].
      iNext. iApply guarded_upd_intro. iModIntro. iFrame "N'".
      iApply (persistent_time_receipt_mono with "⧖"). lia. }
    iMod (fupd_mask_mono with "(Back H1 H2)") as "$"; [done|].
    iModIntro. rewrite /= /uniq_node Hf'. iFrame "Pt ⧗ TIME". iApply bi.laterN_intro.
    iFrame "Incl". iExists (pred dn), gn. iSplit; [iPureIntro; lia|].
    iEval (rewrite (ltype_own_cp_uniq_plug K) // Hf'). iExact "C'".
  Qed.

  (** The hole must be owned: below no shared reference. *)
  Lemma pctx_acc {𝔅 𝔄} (K: pctx 𝔅 𝔄) `{!PctxNoShr K} (lt: lty 𝔅) : pctx_acc_stmt K lt.
  Proof.
    rename select (PctxNoShr K) into HK. rewrite /PctxNoShr in HK.
    induction K; simpl in HK; [apply pctx_acc_hole|apply pctx_acc_fst; by apply IHK|
      apply pctx_acc_snd; by apply IHK|apply pctx_acc_own; by apply IHK|
      apply pctx_acc_sum; by apply IHK| |done|done].
    destruct HK as [HKs HK].
    destruct K; [apply pctx_acc_uniq_hole|apply pctx_acc_uniq_cpd; [done|done|by apply IHK]..|
      done|done].
  Qed.
End pctx_acc.

(** * Places rooted at a value

  The root of a place rooted at a value ([typing/vplace.v]) is the [nval] of its root
  pointer ([lty_vown], in [Owned 0] mode), at depths below the depth [D] of the receipt of
  the place. A root owned pointer is kept in the form of a place rooted at an owned location
  ([place_own.v]): its pointee at depths [d, g] with [S d ≤ D] and [g ≤ D]. The access to the
  hole of a context [K] whose first step is the root pointer ([vroot_acc]) is the access of
  [pctx_acc] to the hole of the rest of [K] (for a root owned pointer), or opens the root
  unique borrow and its contents as [pctx_acc] does for a nested one. *)

Section vroot.
  Context `{!typeG Σ}.

  Definition vroot_own {𝔄} (lt: lty 𝔄) : prfn 𝔄 → nat → thread_id → val → iProp Σ :=
    match lt in lty 𝔄 return prfn 𝔄 → nat → thread_id → val → iProp Σ with
    | OwnPtrLty n lt' => λ r D tid v, match r with
        | inr (l, r') => ∃ d g, ⌜v = MLitV (VPtr l)⌝ ∗ ⌜S d ≤ D ∧ g ≤ D⌝ ∗ freeable_sz n (lty_size lt') l ∗
            ltype_own (Owned 1) lt' r' d g tid l
        | inl _ => False
        end
    | lt' => λ r D tid v, ∃ d g, ⌜d ≤ D ∧ g ≤ D⌝ ∗ lty_vown lt' r d g tid v
    end%I.

  Lemma vroot_own_depth_mono {𝔄} (lt: lty 𝔄) r D D' tid v :
    D ≤ D' → vroot_own lt r D tid v ⊢ vroot_own lt r D' tid v.
  Proof.
    intros ?. destruct lt; simpl;
      try (iIntros "(%d & %g & %Hle & H)"; iExists d, g; iFrame; iPureIntro; lia).
    destruct r as [|[l r']]; [done|].
    iIntros "(%d & %g & -> & %Hle & H)". iExists d, g. iFrame. iPureIntro. split; [done|lia].
  Qed.

  (** The pointer cells on the path below the root pointer (as [pctx_ptrs]). *)
  Definition pctx_vptrs {𝔅 𝔄} (K: pctx 𝔅 𝔄) (n: nat) : ~~𝔄 → iProp Σ :=
    match K in pctx 𝔅 𝔄 return ~~𝔄 → iProp Σ with
    | POwn _ K' => λ x, pctx_ptrs K' n x.2 x.1
    | PUniq _ K' => λ x, pctx_ptrs K' n (uniq_bor_current x) (uniq_bor_loc x)
    | PShr _ K' => λ x, pctx_ptrs K' n x.2 x.1
    | PResUniq _ K' => λ x, pctx_ptrs K' n (uniq_bor_current x) (uniq_bor_loc x)
    | _ => λ _, True
    end%I.

  Lemma pctx_vptrs_set {𝔅 𝔄} (K: pctx 𝔅 𝔄) n x y :
    pctx_in K x → pctx_vptrs K n (pctx_set K x y) = pctx_vptrs K n x.
  Proof.
    destruct K; simpl; try done; intros; rewrite ?uniq_bor_current_set ?uniq_bor_loc_set;
      by rewrite pctx_ptrs_set.
  Qed.

  (** The address of the hole, from the value of the root pointer. *)
  Lemma wp_pctx_vptrs {𝔅 𝔄} E (K: pctx 𝔅 𝔄) `{!PctxVRoot K} n (G: iProp Σ) x (e: expr)
      (R: iProp Σ) :
    WP e @ E {{ v, ⌜v = MLitV (VPtr (pctx_vrloc K n x))⌝ ∗ R ∗ G }} -∗ pctx_vptrs K n x -∗
    WP pctx_vexpr K e @ E {{ v, ⌜v = #(pctx_vloc K n x)⌝ ∗ R ∗ G ∗ pctx_vptrs K n x }}.
  Proof.
    rename select (PctxVRoot K) into HR.
    iIntros "WP P".
    iAssert (WP ToLit e @ E {{ v, ⌜v = #(pctx_vrloc K n x)⌝ ∗ R ∗ G }})%I with "[WP]" as "WP".
    { wp_bind e. iApply (wp_wand with "WP"). iIntros (v) "(-> & R & G)". wp_pure _. by iFrame. }
    iRevert "WP P".
    destruct K as [| | |𝔅 𝔄' n' K| |𝔅 𝔄' κ K|𝔅 𝔄' κ K|𝔅 𝔄' κ K]; try done; simpl.
    - iIntros "WP P".
      iApply (wp_pctx_ptrs E K n G x.2 x.1 _ R with "WP P").
    - iIntros "WP P".
      iApply (wp_pctx_ptrs E K n G (uniq_bor_current x) (uniq_bor_loc x) _ R with "WP P").
    - iIntros "WP P".
      iApply (wp_pctx_ptrs E K n G x.2 x.1 _ R with "WP P").
    - iIntros "WP P".
      iApply (wp_pctx_ptrs E K n G (uniq_bor_current x) (uniq_bor_loc x) _ R with "WP P").
  Qed.

  Lemma pctx_vroot_dlev {𝔅 𝔄} (K: pctx 𝔅 𝔄) `{!PctxVRoot K} : 1 ≤ pctx_dlev K.
  Proof. rename select (PctxVRoot K) into HR. destruct K; try done; simpl; lia. Qed.


  (** The later credits for an access to the hole below a root pointer, at a depth [D]. *)
  Definition pctx_vacc_cred {𝔅 𝔄} (K: pctx 𝔅 𝔄) (D: nat) : nat :=
    match pctx_ulfts K with [] => 0 | _ => (D + 1) * (D + 1) end.

  Lemma pctx_vacc_cred_le {𝔅 𝔄} (K: pctx 𝔅 𝔄) D : pctx_vacc_cred K D ≤ (D + 1) * (D + 1).
  Proof. rewrite /pctx_vacc_cred. destruct (pctx_ulfts K); lia. Qed.

  (** The closer of an access to the hole below a root pointer: as [pctx_closer], the root
      at a new depth [D'] (with a receipt for it). *)
  Definition pctx_vcloser {𝔅 𝔄} (K: pctx 𝔅 𝔄) (lt: lty 𝔅) (r: prfn 𝔅) (x: ~~𝔄)
      (ζm: blk_map) (D: nat) (tid: thread_id) (v: val) (E: coPset) (G G': iProp Σ) : iProp Σ :=
    ∀ (lt': lty 𝔅) r' dh' gh' D' ζl' (qq: Qp) (R: iProp Σ),
      ⌜lty_simple lt'⌝ -∗ ⌜lty_fold lt' = lty_fold lt⌝ -∗ ⌜lty_size lt' = lty_size lt⌝ -∗
      ⌜∀ ζl, prfn_rsv r ζl → prfn_rsv r' (ζl ++ ζl')⌝ -∗
      ⌜D ≤ D' ∧ dh' + pctx_dlev K ≤ D' ∧ gh' ≤ D'⌝ -∗
      (⌜lty_pat lt' = lty_pat lt⌝ ∨ [∗ list] κ ∈ pctx_ulfts K, pat_ok κ (lty_pat lt')) -∗
      ⧖D' -∗ G' -∗ pctx_vptrs K (lty_size lt) x -∗ qq:+[ζl'] -∗
      (qq:+[ζl'] ={E}=∗ ltype_own (pctx_kind K (Owned 0) x) lt' r' dh' gh' tid
          (pctx_vloc K (lty_size lt) x) ∗ R) ={E}=∗
      vroot_own (pctx_plug K lt') (pctx_vrfn K x ζm r') D' tid v ∗ G ∗ R.

  (** The result of an access to the hole below a root pointer (as [pctx_acc_res]). *)
  Definition pctx_vacc_res {𝔅 𝔄} (K: pctx 𝔅 𝔄) (lt: lty 𝔅) (r: prfn 𝔅) (x: ~~𝔄)
      (ζm: blk_map) (D: nat) (tid: thread_id) (v: val) (E: coPset) (G: iProp Σ) : iProp Σ :=
    ∃ (G': iProp Σ) dh gh, ⌜Timeless G'⌝ ∗ G' ∗ (G' &&{↑NllftG}&&> G) ∗
      ⌜v = MLitV (VPtr (pctx_vrloc K (lty_size lt) x))⌝ ∗
      ⌜dh + pctx_dlev K ≤ D ∧ gh ≤ D ∧ pctx_in K x⌝ ∗
      ltype_own (pctx_kind K (Owned 0) x) lt r dh gh tid (pctx_vloc K (lty_size lt) x) ∗
      pctx_vptrs K (lty_size lt) x ∗
      pctx_vcloser K lt r x ζm D tid v E G G'.

  Lemma vroot_acc_own {𝔅 𝔄'} n (K: pctx 𝔅 𝔄') `{!PctxNoShr K} (lt: lty 𝔅) r x ζm D tid v E G :
    lazyE ⊆ E → Timeless G →
    llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ (G &&{↑NllftG}&&> @[pctx_ulft (POwn n K) lt]) -∗ G -∗
    £(pctx_vacc_cred (POwn n K) D) -∗
    vroot_own (pctx_plug (POwn n K) lt) (pctx_vrfn (POwn n K) x ζm r) D tid v ={E}=∗
    pctx_vacc_res (POwn n K) lt r x ζm D tid v E G.
  Proof.
    iIntros (??) "#LFT #PROPH #UNIQ #Gk G £ /=". iDestruct 1 as (d g -> Hle) "[Fr Own]".
    rewrite /ltype_own lty_pat_plug.
    iDestruct (lc_weaken (pctx_acc_cred K 1 d) with "£") as "£";
      [rewrite /pctx_acc_cred /pctx_vacc_cred /=; destruct (pctx_ulfts K); nia|].
    iMod (pctx_acc K lt 1 with "LFT PROPH UNIQ Gk G £ Own")
      as (G' dh gh) "(% & G' & #G'G & %Hdh & H & P & Cl)"; [done..|].
    destruct Hdh as (Hdh & Hgh & Hin).
    iModIntro. iExists G', dh, gh. iSplitR; [done|]. iSplitL "G'"; [done|]. iSplitR; [done|].
    iSplitR; [done|]. iSplitR; [iPureIntro; simpl; split_and!; [lia|lia|done]|].
    rewrite /pctx_vloc /=. iFrame "H P".
    iIntros (lt' r' dh' gh' D' ζl' qq R Hs Hf Hsz Hr (? & ? & ?)) "Oks #⧖ G' P toks VS".
    iMod ("Cl" $! lt' (lty_pat lt') r' dh' gh' (pred D') D' ζl' qq R
      with "[//] [//] [//] [//] [%] Oks [] G' P toks VS") as "(Own & $ & $)";
      [simpl in *; lia|..].
    { iApply (persistent_time_receipt_mono with "⧖"). simpl in *. lia. }
    iModIntro. iExists (pred D'), D'. iSplit; [done|]. iSplit; [iPureIntro; simpl in *; lia|].
    rewrite /ltype_own lty_pat_plug !lty_size_plug Hsz. iFrame.
  Qed.

  (** The hole is the whole referent of the root unique borrow. *)
  Lemma vroot_acc_uniq_hole {𝔅} κ (lt: lty 𝔅) r x ζm D tid v E G :
    lazyE ⊆ E → Timeless G →
    llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ (G &&{↑NllftG}&&> @[pctx_ulft (PUniq κ (PHole (𝔅:=𝔅))) lt]) -∗ G -∗
    £(pctx_vacc_cred (PUniq κ (PHole (𝔅:=𝔅))) D) -∗
    vroot_own (pctx_plug (PUniq κ (PHole (𝔅:=𝔅))) lt) (pctx_vrfn (PUniq κ (PHole (𝔅:=𝔅))) x ζm r) D tid v ={E}=∗
    pctx_vacc_res (PUniq κ (PHole (𝔅:=𝔅))) lt r x ζm D tid v E G.
  Proof.
    iIntros (??) "_ _ _ #Gk G _ /=".
    iDestruct 1 as (d g Hle) "(-> & ⧗ & #TIME & #Incl & %d' & %g' & %Hle' & C)".
    iModIntro. iExists G, d', g'. iSplitR; [done|]. iSplitL "G"; [done|].
    iSplitR; [iApply guards_refl|]. iSplitR; [done|].
    iSplitR; [iPureIntro; simpl in *; split_and!; [lia|lia|done]|].
    rewrite /pctx_vloc /=. iSplitL "C"; [done|]. iSplitR; [done|].
    iIntros (lt' r' dh' gh' D' ζl' qq R Hs Hf Hsz Hr (? & ? & ?)) "_ _ G _ toks VS".
    iMod ("VS" with "toks") as "[C $]". iFrame "G". iModIntro.
    iExists D', D'. iSplit; [done|]. rewrite /= Hf. iSplit; [done|]. iFrame "⧗ TIME Incl".
    iExists dh', gh'. iFrame "C". iPureIntro. simpl in *. lia.
  Qed.

  (** The hole is below the root unique borrow, whose referent is compound: as
      [pctx_acc_uniq_cpd]. *)
  Lemma vroot_acc_uniq_cpd {𝔅 𝔄'} κ (K: pctx 𝔅 𝔄') `{!PctxNoShr K} (lt: lty 𝔅) r x ζm D tid v E G :
    pctx_nonempty K → pctx_simple K → lazyE ⊆ E → Timeless G →
    llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ (G &&{↑NllftG}&&> @[pctx_ulft (PUniq κ K) lt]) -∗ G -∗
    £(pctx_vacc_cred (PUniq κ K) D) -∗
    vroot_own (pctx_plug (PUniq κ K) lt) (pctx_vrfn (PUniq κ K) x ζm r) D tid v ={E}=∗
    pctx_vacc_res (PUniq κ K) lt r x ζm D tid v E G.
  Proof.
    iIntros (HK HKs HE ?) "#LFT #PROPH #UNIQ #Gk G £ /=".
    iDestruct 1 as (d g Hle) "(-> & ⧗ & #TIME & #Incl & %d' & %g' & %Hle' & C)".
    iDestruct (lc_weaken (1 + pctx_acc_cred K 0 d') with "£") as "[£1 £]";
      [have := pctx_acc_cred_le K 0 d'; rewrite /pctx_vacc_cred /=; nia|].
    rewrite /ltype_own lty_pat_plug ltype_own_cp_uniq_plug //.
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
    iMod (pctx_acc K lt 0 with "LFT PROPH UNIQ Hu H2 £ N")
      as (G' dh gh) "(% & G' & #G'G & %Hdh & H & P & Cl)"; [done..|].
    destruct Hdh as (Hdh & Hgh & Hin).
    iModIntro. iExists G', dh, gh. iSplitR; [done|]. iSplitL "G'"; [done|].
    iSplitR; [iApply (guards_transitive with "G'G Gh")|]. iSplitR; [done|].
    iSplitR; [iPureIntro; simpl in *; split_and!; [lia|lia|done]|].
    rewrite /pctx_vcloser /pctx_vloc /= pctx_kind_nonempty //.
    iSplitL "H"; [done|]. iSplitL "P"; [done|].
    iIntros (lt' r' dh' gh' D' ζl' qq R Hs Hf Hsz Hr (? & ? & ?)) "Oks #⧖ G' P toks VS".
    iAssert (▷ pat_ok κp (pctx_pat K (lty_pat lt')))%I as "#Ok'".
    { iDestruct "Oks" as "[->|[Okκ _]]"; [done|].
      iNext. iApply (pat_ok_plug with "Ok"). iApply (pat_ok_mono with "Inclp Okκ"). }
    iAssert (⌜lty_pat lt' = lty_pat lt⌝ ∨ [∗ list] κ ∈ pctx_ulfts K, pat_ok κ (lty_pat lt'))%I
      with "[Oks]" as "Oks".
    { iDestruct "Oks" as "[$|[_ $]]". }
    have Hf': lty_fold (pctx_plug K lt') = lty_fold (pctx_plug K lt) by apply lty_fold_plug_eq'.
    iMod ("Close" $! (ltype_own_cp false (pctx_plug K lt') (Owned 0)) (pctx_pat K (lty_pat lt'))
      (pctx_rfn K (uniq_bor_current x) ζm [] r') (pred D') D' ζl' qq
      (fractional.half γh ∗ R)%I with "[%] [] toks [VS G' P Oks Cl]") as "(C' & H1 & H2 & $)".
    { intros ζl. apply pctx_rfn_rsv_mono; [set_solver|]. apply Hr. }
    { iIntros "!>" (p2 r2 d2 g2) "Ok2 ⧖2 N". rewrite -Hf'.
      iApply (ltype_owned_leaf_node with "LFT PROPH UNIQ Ok2 ⧖2 N");
        [by apply lty_is_cpd_plug_nonempty'|by apply lty_simple_plug]. }
    { iIntros "toks".
      iMod ("Cl" $! lt' (lty_pat lt') r' dh' gh' (pred D') D' ζl' qq R
        with "[//] [//] [//] [//] [%] Oks [] G' P toks VS") as "(N' & $ & $)";
        [simpl in *; lia|..].
      { iApply (persistent_time_receipt_mono with "⧖"). simpl in *. lia. }
      iModIntro. iSplitR; [done|].
      iNext. iApply guarded_upd_intro. iModIntro. iFrame "N'".
      iApply (persistent_time_receipt_mono with "⧖"). simpl in *. lia. }
    iMod (fupd_mask_mono with "(Back H1 H2)") as "$"; [done|].
    iModIntro. iExists D', D'. iSplit; [iPureIntro; simpl in *; lia|]. rewrite /= Hf'.
    iSplit; [done|]. iFrame "⧗ TIME Incl".
    iExists (pred D'), D'. iSplit; [iPureIntro; simpl in *; lia|].
    rewrite /ltype_own lty_pat_plug (ltype_own_cp_uniq_plug K) // Hf'. iExact "C'".
  Qed.

  (** The access to the hole of a context whose first step is the root pointer. *)
  Lemma vroot_acc {𝔅 𝔄} (K: pctx 𝔅 𝔄) `{!PctxNoShr K} `{!PctxVRoot K} (lt: lty 𝔅) r x ζm D tid v
      E G :
    lazyE ⊆ E → Timeless G →
    llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ (G &&{↑NllftG}&&> @[pctx_ulft K lt]) -∗ G -∗
    £(pctx_vacc_cred K D) -∗
    vroot_own (pctx_plug K lt) (pctx_vrfn K x ζm r) D tid v ={E}=∗
    pctx_vacc_res K lt r x ζm D tid v E G.
  Proof.
    rename select (PctxVRoot K) into HR. rename select (PctxNoShr K) into HK.
    destruct K as [| | |𝔅 𝔄' n K| |𝔅 𝔄' κ K| |]; try done.
    - apply vroot_acc_own. done.
    - destruct HK as [HKs HK]. destruct K; [apply vroot_acc_uniq_hole|
        apply vroot_acc_uniq_cpd; done..|done|done].
  Qed.
End vroot.
