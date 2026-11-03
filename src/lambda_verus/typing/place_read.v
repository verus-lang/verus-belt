(** * Reading a place

  One rule, [type_read_place_instr], copies the value of a [Copy] leaf out of any place
  rooted at a value ([p ◁ₗ pctx_plug K lt], [vplace.v]), with the instruction
  [!ᶜ{ty_mty ty} (pctx_vexpr K p)] ([read_copy], a typed [Load]); the place does not
  change. The context [K] may mix fields, sums, owned pointers, unique borrows, shared
  references and resolved unique borrows in any order and nesting ([PctxRead]: the siblings
  below a unique borrow are simple, down to the first shared reference, so in particular a
  resolved unique borrow is below no unique borrow); its root step is an owned pointer (a
  place rooted at an owned location, [p ◁ₗown{n} …]), a unique borrow, a shared reference or
  a resolved unique borrow ([PctxVRoot]).

  - The readable leaves ([pctx_rleaf K lt ty κs], [lty_rleaf] of [place_res_ops.v]):
    outside a shared reference, an unblocked leaf [OfTy ty] ([κs = static]), a
    shared-blocked leaf [ShrBlocked ty β] ([κs = β], which must be alive) and, below no
    unique borrow or resolved unique borrow, a resolved leaf [OfRes ty] of a type with
    [ResOwn ty]; below a shared reference, any place type [lt], read at its folded type
    [ty = lty_fold lt] (the referent of a shared reference is a read-only view). Blocked
    leaves are not readable.
  - The lifetimes that must be alive ([pctx_alv K lt]): the lifetime of the folded type at
    each unique borrow outside the shared part ([pctx_ulft], to open the borrows), and,
    below the first shared reference or resolved unique borrow at [κ], [pctx_salv K2 κ] (the
    lifetimes of the guarded loads of the pointers of the view, [place_pshr.v]).
  - No [Skip]: the first program step (of the address, or the load itself) gives the
    credits.

  The rule is a guarded typed [Load] ([wp_load_na_guarded_gen]) from the _read access_
  [wp_vplace_racc] (a CPS around the address [pctx_vexpr K p], with the credits of a step at
  the depth of the place): it gives the address of the leaf, a guard of its bytes (the bytes
  themselves for an owned leaf, the sharing of the leaf for a shared one), the persistent
  ownership of its value and a closer ([vplace_rcont]). The byte copies from a readable
  place ([type_memcpy_copy_place_instr] of [place_memcpy.v]) use the same access. It splits
  [K] at its first shared reference or resolved unique borrow ([pctx_read_split], with
  [pctx_app]): the part above it is accessed with [vroot_acc] ([pctx_acc.v]), or split with
  [ltype_own_plug] above a resolved unique borrow; below a shared reference, the shared view
  of the referent is pushed through the rest of the context ([wp_pshr_open],
  [wp_pshr_open_root] of [place_pshr.v]); below a resolved unique borrow, the view of its
  referent is accessed ([view_pctx_acc] of [place_res_ops.v]) down to the hole or to the next
  shared reference ([wp_view_racc]). *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var.
From lrust.lang Require Import proofmode.
From lrust.typing Require Export type ltype lpath pctx_acc vplace place_own shr_bor place_pshr.
From lrust.typing Require Import type_context programs lft_contexts uniq_util uniq_bor own bytes_layout value_ctx product freeable_util place_puniq place_res place_res_view place_res_ops.
From lrust.lifetime Require Import lifetime_full.
From guarding Require Import guard tactics.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

(** * Readable leaves, lifetimes and the shape of the context *)

Section pctx_read.
  Context `{!typeG Σ}.

  (** The readable leaves at the hole of [K] ([lty_rleaf] of [place_res_ops.v]); [b]: the
      hole is in the owned part of the place, so a resolved leaf is readable. Below a
      shared reference, any place type is readable, at its folded type. *)
  Fixpoint pctx_rleafb {𝔅 𝔄} (K: pctx 𝔅 𝔄) : bool → lty 𝔅 → type 𝔅 → lft → Prop :=
    match K in pctx 𝔅 𝔄 return bool → lty 𝔅 → type 𝔅 → lft → Prop with
    | PHole => λ b, lty_rleaf b
    | PFst K _ | PSnd _ K | POwn _ K | PSum _ _ _ K => pctx_rleafb K
    | PUniq _ K | PResUniq _ K => λ _, pctx_rleafb K false
    | PShr _ _ => λ _ lt ty κs, ty = lty_fold lt ∧ κs = static
    end.

  (** The siblings below a unique borrow are simple, down to the first shared reference
      (as [PctxNoShr], whose access is used above the first shared reference; in particular,
      there is no resolved unique borrow below a unique borrow). *)
  Fixpoint pctx_read {𝔅 𝔄} (K: pctx 𝔅 𝔄) : Prop :=
    match K with
    | PHole | PShr _ _ => True
    | PFst K _ | PSnd _ K | POwn _ K | PSum _ _ _ K | PResUniq _ K => pctx_read K
    | PUniq _ K => pctx_simple K ∧ pctx_read K
    end.

  Class PctxRead {𝔅 𝔄} (K: pctx 𝔅 𝔄) : Prop := pctx_read_c : pctx_read K.

  Global Instance pctx_read_hole {𝔅} : PctxRead (PHole (𝔅:=𝔅)).
  Proof. done. Qed.
  Global Instance pctx_read_fst {𝔅 𝔄1 𝔄2} (K: pctx 𝔅 𝔄1) (lt2: lty 𝔄2) :
    PctxRead K → PctxRead (PFst K lt2).
  Proof. done. Qed.
  Global Instance pctx_read_snd {𝔅 𝔄1 𝔄2} (lt1: lty 𝔄1) (K: pctx 𝔅 𝔄2) :
    PctxRead K → PctxRead (PSnd lt1 K).
  Proof. done. Qed.
  Global Instance pctx_read_own {𝔅 𝔄'} n (K: pctx 𝔅 𝔄') : PctxRead K → PctxRead (POwn n K).
  Proof. done. Qed.
  Global Instance pctx_read_sum {𝔅 𝔄l} (tyl: typel 𝔄l) i w (K: pctx 𝔅 (𝔄l !!ₗ i)) :
    PctxRead K → PctxRead (PSum tyl i w K).
  Proof. done. Qed.
  Global Instance pctx_read_uniq {𝔅 𝔄'} κ (K: pctx 𝔅 𝔄') :
    PctxSimple K → PctxRead K → PctxRead (PUniq κ K).
  Proof. done. Qed.
  Global Instance pctx_read_shr {𝔅 𝔄'} κ (K: pctx 𝔅 𝔄') : PctxRead (PShr κ K).
  Proof. done. Qed.
  Global Instance pctx_read_res_uniq {𝔅 𝔄'} κ (K: pctx 𝔅 𝔄') :
    PctxRead K → PctxRead (PResUniq κ K).
  Proof. done. Qed.

  (** A context is below no shared reference and no resolved unique borrow, or it is split
      at the first of them (a resolved unique borrow is below no unique borrow). *)
  Lemma pctx_read_split {𝔅 𝔄} (K: pctx 𝔅 𝔄) :
    pctx_read K →
    pctx_noshr K ∨
    (∃ 𝔅' κ (K1: pctx (at_locₛ 𝔅') 𝔄) (K2: pctx 𝔅 𝔅'),
      K = pctx_app K1 (PShr κ K2) ∧ pctx_noshr K1) ∨
    (∃ 𝔅' κ (K1: pctx (uniq_borₛ 𝔅') 𝔄) (K2: pctx 𝔅 𝔅'),
      K = pctx_app K1 (PResUniq κ K2) ∧ pctx_noshr K1 ∧ pctx_nouniq K1 ∧ pctx_read K2).
  Proof.
    induction K as [|𝔅 𝔄1 𝔄2 K IH lt2|𝔅 𝔄1 𝔄2 lt1 K IH|𝔅 𝔄' n K IH|𝔅 𝔄l tyl i w K IH|
      𝔅 𝔄' κ K IH|𝔅 𝔄' κ K IH|𝔅 𝔄' κ K IH]; simpl.
    - by left.
    - intros H. destruct (IH H) as [?|[(𝔅' & κ & K1 & K2 & -> & ?)|(𝔅' & κ & K1 & K2 & -> & ?)]];
        [by left|right; left|right; right].
      + by exists 𝔅', κ, (PFst K1 lt2), K2.
      + by exists 𝔅', κ, (PFst K1 lt2), K2.
    - intros H. destruct (IH H) as [?|[(𝔅' & κ & K1 & K2 & -> & ?)|(𝔅' & κ & K1 & K2 & -> & ?)]];
        [by left|right; left|right; right].
      + by exists 𝔅', κ, (PSnd lt1 K1), K2.
      + by exists 𝔅', κ, (PSnd lt1 K1), K2.
    - intros H. destruct (IH H) as [?|[(𝔅' & κ & K1 & K2 & -> & ?)|(𝔅' & κ & K1 & K2 & -> & ?)]];
        [by left|right; left|right; right].
      + by exists 𝔅', κ, (POwn n K1), K2.
      + by exists 𝔅', κ, (POwn n K1), K2.
    - intros H. destruct (IH H) as [?|[(𝔅' & κ & K1 & K2 & -> & ?)|(𝔅' & κ & K1 & K2 & -> & ?)]];
        [by left|right; left|right; right].
      + by exists 𝔅', κ, (PSum tyl i w K1), K2.
      + by exists 𝔅', κ, (PSum tyl i w K1), K2.
    - intros [Hs H].
      destruct (IH H) as [?|[(𝔅' & κ' & K1 & K2 & -> & ?)|(𝔅' & κ' & K1 & K2 & -> & HK1 & _)]];
        [by left|right; left|].
      + exists 𝔅', κ', (PUniq κ K1), K2. split; [done|]. split; [|done].
        by eapply pctx_simple_app_l.
      + exfalso. by apply (pctx_simple_app_not K1 (PResUniq κ' K2)); [intros ?|..].
    - intros _. right. left. by exists 𝔄', κ, PHole, K.
    - intros H. right. right. by exists 𝔄', κ, PHole, K.
  Qed.

  Lemma lty_rleaf_cases {𝔄} b (lt: lty 𝔄) ty κs :
    lty_rleaf b lt ty κs → lty_rleaf false lt ty κs ∨ (lt = OfRes ty ∧ ResOwn ty ∧ κs = static).
  Proof. destruct 1; [left; constructor|left; constructor|by right]. Qed.

  Lemma pctx_rleafb_noshr {𝔅 𝔄} (K: pctx 𝔅 𝔄) b lt ty κs :
    pctx_noshr K → pctx_rleafb K b lt ty κs →
    (pctx_nouniq K ∧ lty_rleaf b lt ty κs) ∨ lty_rleaf false lt ty κs.
  Proof.
    induction K in b, lt, ty, κs |- *; simpl; [by left|auto|auto|auto|auto| |done|done].
    intros [_ HK] Hl. right. by destruct (IHK false lt ty κs HK Hl) as [[_ ?]|?].
  Qed.

  Lemma pctx_rleafb_app {ℭ 𝔅 𝔄} (K1: pctx 𝔅 𝔄) (K2: pctx ℭ 𝔅) b lt ty κs :
    pctx_rleafb (pctx_app K1 K2) b lt ty κs →
    (∃ b', pctx_rleafb K2 b' lt ty κs) ∨ (ty = lty_fold lt ∧ κs = static).
  Proof. induction K1 in K2, b |- *; simpl; eauto. Qed.

  Lemma pctx_rleafb_app_shr {ℭ 𝔅 𝔄} (K1: pctx (at_locₛ 𝔅) 𝔄) κ (K2: pctx ℭ 𝔅) b lt ty κs :
    pctx_rleafb (pctx_app K1 (PShr κ K2)) b lt ty κs → ty = lty_fold lt ∧ κs = static.
  Proof. by intros [[? ?]|?]%pctx_rleafb_app. Qed.

  Lemma pctx_rleafb_app_noshr {ℭ 𝔅 𝔄} (K1: pctx 𝔅 𝔄) (K2: pctx ℭ 𝔅) b lt ty κs :
    pctx_noshr K1 → pctx_rleafb (pctx_app K1 K2) b lt ty κs → ∃ b', pctx_rleafb K2 b' lt ty κs.
  Proof.
    induction K1 in K2, b |- *; simpl; [eauto|eauto|eauto|eauto|eauto| |done|done].
    intros [_ HK]. eauto.
  Qed.

  Lemma pctx_alv_app {ℭ 𝔅 𝔄} (K1: pctx 𝔅 𝔄) (K2: pctx ℭ 𝔅) lt :
    pctx_noshr K1 →
    ⊢ pctx_alv (pctx_app K1 K2) lt ⊑ pctx_ulft K1 (pctx_plug K2 lt) ⊓ pctx_alv K2 lt.
  Proof.
    induction K1 as [|? ? ? K1 IH ?|? ? ? ? K1 IH|? ? ? K1 IH|? ? ? ? ? K1 IH|𝔅' 𝔄' κ' K1 IH| |]
      in K2 |- *;
      intros HK; [|exact (IH K2 HK)..| |done|done].
    - iApply llftl_incl_glb; [iApply lft_incl_static|iApply guards_refl].
    - destruct HK as [_ HK]. cbn [pctx_alv pctx_app pctx_ulft]. iApply llftl_incl_glb.
      + rewrite pctx_plug_app. iApply llftl_intersect_incl_l.
      + iApply llftl_incl_trans; [iApply llftl_intersect_incl_r|].
        iApply llftl_incl_trans; [by iApply IH|]. iApply llftl_intersect_incl_r.
  Qed.

  Lemma pctx_alv_app_shr {ℭ 𝔅 𝔄} (K1: pctx (at_locₛ 𝔅) 𝔄) κ (K2: pctx ℭ 𝔅) lt :
    pctx_noshr K1 →
    ⊢ pctx_alv (pctx_app K1 (PShr κ K2)) lt ⊑
      pctx_ulft K1 (ShrLty (pctx_plug K2 lt) κ) ⊓ pctx_salv K2 κ.
  Proof. apply pctx_alv_app. Qed.

  Lemma pctx_salv_app {ℭ 𝔅 𝔄} (K1: pctx 𝔅 𝔄) (K2: pctx ℭ 𝔅) κ :
    pctx_noshr K1 → pctx_salv (pctx_app K1 K2) κ = pctx_salv K2 (pctx_slft K1 κ).
  Proof.
    induction K1 in K2, κ |- *; simpl; [done|auto|auto|auto|auto| |done|done].
    intros [_ HK]. auto.
  Qed.

  Lemma pctx_salv_slft_noshr {𝔅 𝔄} (K: pctx 𝔅 𝔄) κ :
    pctx_noshr K → pctx_salv K κ = pctx_slft K κ.
  Proof.
    induction K in κ |- *; simpl; [done|auto|auto|auto|auto| |done|done].
    intros [_ HK]. auto.
  Qed.

  Lemma pctx_slft_app {ℭ 𝔅 𝔄} (K1: pctx 𝔅 𝔄) (K2: pctx ℭ 𝔅) κ :
    pctx_noshr K1 → pctx_slft (pctx_app K1 K2) κ = pctx_slft K2 (pctx_slft K1 κ).
  Proof.
    induction K1 in K2, κ |- *; simpl; [done|auto|auto|auto|auto| |done|done].
    intros [_ HK]. auto.
  Qed.
  (** The refinement below a root pointer of a context whose hole is a leaf of the
      refinement (e.g. a shared reference). *)
  Lemma pctx_vrfn_app_leaf {ℭ 𝔅 𝔄} (K1: pctx 𝔅 𝔄) `{!PctxVRoot K1} (K2: pctx ℭ 𝔅) x ζm r :
    (∀ y q, pctx_rfn K2 y ζm q r = inl (PlaceIn y)) →
    pctx_vrfn (pctx_app K1 K2) x ζm r = pctx_vrfn K1 x ζm (inl (PlaceIn (pctx_get K1 x))).
  Proof.
    rename select (PctxVRoot K1) into HR. intros H.
    destruct K1; try done; simpl; by rewrite ?pctx_rfn_app ?H.
  Qed.

  Lemma pctx_vrfn_app_shr {ℭ 𝔅 𝔄} (K1: pctx (at_locₛ 𝔅) 𝔄) `{!PctxVRoot K1} κ (K2: pctx ℭ 𝔅)
      x ζm r :
    pctx_vrfn (pctx_app K1 (PShr κ K2)) x ζm r =
      pctx_vrfn K1 x ζm (inl (PlaceIn (pctx_get K1 x))).
  Proof. by apply pctx_vrfn_app_leaf. Qed.
End pctx_read.

Notation pctx_rleaf K := (pctx_rleafb K true).

(** * The read access *)

Section read_acc.
  Context `{!typeG Σ}.

  (** In [Uniq] mode, a shared-blocked leaf is an unblocked leaf. *)
  Lemma lty_rleaf_uniq {𝔄} (lt: lty 𝔄) ty κs κ ξi r d g tid l :
    lty_rleaf false lt ty κs →
    ltype_own (Uniq κ ξi) lt r d g tid l ⊣⊢ ltype_own (Uniq κ ξi) (OfTy ty) r d g tid l.
  Proof. destruct 1 as [| |? [=]]; [done|]. rewrite /ltype_own /=. by destruct r. Qed.

  (** The continuation of a read access to the leaf at the hole of [K], of the place
      [p ◁ₗ pctx_plug K lt] at [(x, ζm)]: the address [l] of the leaf, a guarded access
      (by [G2], with [dd] laters) to the bytes of its value, a value of [ty], the
      (persistent: [Copy]) ownership of the value, and a closer that gives back the place,
      unchanged, from [G2]. *)
  Definition vplace_rcont {𝔅 𝔄} (K: pctx 𝔅 𝔄) (lt: lty 𝔅) (ty: type 𝔅) (x: ~~𝔄)
      (ζm: blk_map) (D: nat) (tid: thread_id) (v: val) (E: coPset) (G: iProp Σ)
      (Φ: val → iProp Σ) : iProp Σ :=
    ∀ (l: loc) (G2: iProp Σ) dd dh gh,
      ⌜is_Some (ty.(ty_val) (pctx_get K x)) ∧ dh ≤ D ∧ gh ≤ D⌝ -∗
      (G2 &&{↑naN; dd}&&> cbytes ty (pctx_get K x) l) -∗ G2 -∗ £(2 * dd) -∗
      ty.(ty_gho_own) (pctx_get K x) dh gh tid -∗
      (G2 ={E}=∗ vplace_own (pctx_plug K lt) (x, ζm) tid v ∗ G) -∗ Φ #l.

  (** Below no shared reference (in [Owned] or [Uniq] mode, below any number of unique
      borrows): the access [vroot_acc]; an unblocked leaf is owned (its bytes are their
      own guard), a shared-blocked leaf in [Owned] mode is read from its sharing. *)
  Lemma wp_vplace_racc_noshr {𝔅 𝔄} E (K: pctx 𝔅 𝔄) `{!PctxNoShr K} `{!PctxVRoot K}
      (lt: lty 𝔅) (ty: type 𝔅) κs `{!Copy ty} x ζm D tid p v (G: iProp Σ) Φ :
    lty_rleaf false lt ty κs → Timeless G → lazyE ⊆ E → eval_path p = Some v →
    llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ (G &&{↑NllftG}&&> @[pctx_alv K lt ⊓ κs]) -∗ G -∗
    £(advance_credits D) -∗ ⧖D -∗ ⧗(lty_vnrc (pctx_plug K lt)) -∗
    vroot_own (pctx_plug K lt) (pctx_vrfn K x ζm (lty_rfn lt (pctx_get K x) ζm (pctx_vpath K)))
      D tid v -∗
    vplace_rcont K lt ty x ζm D tid v E G Φ -∗
    WP pctx_vexpr K p @ E {{ Φ }}.
  Proof.
    assert (NoCell 𝔅) by exact (copy_nocell ty).
    iIntros (Hl ? HE Hp) "#LFT #PROPH #UNIQ #Alv G £ #⧖ ⧗p Own HΦ". rewrite /vplace_rcont.
    have Hdl: 1 ≤ pctx_dlev K by apply pctx_vroot_dlev.
    have ?: ↑NllftG ⊆ E. { trans lazyE; [apply lazyE_NllftG|done]. }
    have ?: ↑Nllft ⊆ E. { trans lazyE; [rewrite /lazyE; solve_ndisj|done]. }
    iAssert (G &&{↑NllftG}&&> @[pctx_ulft K lt])%I as "#Hu".
    { iApply (guards_transitive with "Alv").
      iApply llftl_incl_trans; [iApply llftl_intersect_incl_l|]. by iApply pctx_alv_noshr. }
    iAssert (G &&{↑NllftG}&&> @[κs])%I as "#Hκs".
    { iApply (guards_transitive with "Alv"). iApply llftl_intersect_incl_r. }
    set y := pctx_get K x.
    iDestruct (lc_weaken (pctx_vacc_cred K D + (D + (1 + 4 * (D + 1)))) with "£")
      as "[£a [£k [£1 £r]]]";
      [have := pctx_vacc_cred_le K D; rewrite /advance_credits; nia|].
    iMod (vroot_acc K lt with "LFT PROPH UNIQ Hu G £a Own")
      as (G' dh gh) "(% & G' & #G'G & -> & %Hdh & H & P & Cl)"; [done|].
    destruct Hdh as (Hdh & Hgh & Hin).
    set lK := pctx_vloc K (lty_size lt) x.
    iAssert (G' &&{↑NllftG}&&> @[pctx_ulft K lt])%I as "#G'u".
    { iApply (guards_transitive with "G'G Hu"). }
    iAssert (G' &&{↑NllftG}&&> @[κs])%I as "#G'κs".
    { iApply (guards_transitive with "G'G Hκs"). }
    have Hr: lty_rfn lt y ζm (pctx_vpath K) = inl (PlaceIn y) by destruct Hl.
    rewrite Hr.
    (* The address of the hole. *)
    iApply wp_fupd. iApply (wp_wand with "[P G']").
    { iApply (wp_pctx_vptrs E K (lty_size lt) G' x p True%I with "[G'] P").
      iApply wp_wand; [by iApply wp_eval_path|]. iIntros (?) "->". by iFrame. }
    iIntros (w) "(-> & _ & G' & P)".
    destruct (pctx_uend K) as [κ|] eqn:Hu.
    - (* [Uniq] mode: the whole referent of the innermost unique borrow. *)
      iEval (rewrite (pctx_kind_uniq K κ) //) in "H".
      iEval (rewrite (lty_rleaf_uniq lt ty κs _ _ _ _ _ _ _ Hl)) in "H".
      iEval (rewrite /pctx_vcloser (pctx_kind_uniq K κ) //) in "Cl".
      iDestruct "H" as (? idx ->) "Body".
      iMod (fractional.frac_split_guard_in_half NllftG G' G' with "G' []")
        as (γ2) "[A [B [#Gh2 #Back2]]]"; [done|iApply guards_refl|].
      iAssert (fractional.half γ2 &&{↑NllftG}&&> @[κ])%I as "#Aκ".
      { iApply (guards_transitive with "Gh2"). iApply (guards_transitive with "G'u").
        by iApply pctx_ulft_uend. }
      iAssert (fractional.half γ2 &&{↑NllftG}&&> @[ty_lft ty])%I as "#Aty".
      { iApply (guards_transitive with "Gh2"). iApply (guards_transitive with "G'u").
        iApply llftl_incl_trans; [iApply (pctx_ulft_fold K lt)|].
        { by eapply pctx_uend_ulfts_ne. }
        destruct Hl as [| |? [=]]; iApply guards_refl. }
      iMod (uniq_body_acc with "LFT UNIQ Aκ Body A") as "(Pl & ⧗1 & CloseB)"; [done|].
      iMod (lc_fupd_elim_later with "£1 Pl") as "Pl".
      iMod (uniq_payload_run with "Aty B Pl") as "(B & #⧖' & #Gho1 & Pt1)"; [done|].
      iDestruct (bytes_own_nocell_bytes with "Pt1") as (bs) "[Hbs %Hbs]".
      iDestruct (bytes_own_of_bytes with "Hbs") as "Pt1"; [done|].
      iDestruct (lc_weaken (2 * 0) with "£r") as "£0"; [lia|].
      iModIntro. iApply ("HΦ" $! lK (cbytes ty y lK) 0 dh gh with "[%] [] Pt1 £0 Gho1").
      { split_and!; [by eapply ty_bytes_val|lia|lia]. }
      { iApply guards_refl. }
      iIntros "Pt1".
      iSpecialize ("CloseB" $! y dh gh with "[Pt1] ⧗1").
      { iNext. by iFrame "⧖' Gho1 Pt1". }
      iMod (fupd_mask_mono with "CloseB") as "[Body A]"; [done|].
      iMod (fupd_mask_mono with "(Back2 A B)") as "G'"; [done|].
      iMod ("Cl" $! lt (inl (PlaceIn y)) dh gh D [] 1%Qp True%I
        with "[%] [//] [//] [%] [%] [] ⧖ G' P [] [Body]") as "(Own & G & _)".
      { by destruct Hl as [| |? [=]]. }
      { intros ??. apply prfn_rsv_in. }
      { lia. }
      { by iLeft. }
      { done. }
      { iIntros "_ !>". iSplit; [|done]. rewrite (lty_rleaf_uniq lt ty κs _ _ _ _ _ _ _ Hl).
        iExists y, idx. by iFrame. }
      iModIntro. iFrame "G". iApply (vplace_own_close with "⧖ ⧗p"). by rewrite Hr.
    - (* [Owned] mode. *)
      iEval (rewrite (pctx_kind_owned K) //) in "H".
      iEval (rewrite /pctx_vcloser (pctx_kind_owned K) //) in "Cl".
      have Hm := pctx_hmode_le K 0. set mh := pctx_hmode K 0.
      destruct Hl as [|ty β|? [=]].
      + iDestruct "H" as (? ->) "[Pt1 #Gho1]".
        iDestruct (lc_weaken mh with "£k") as "£k"; [lia|].
        iMod (lc_fupd_elim_laterN with "£k Gho1") as "#Gho1'".
        iDestruct (bytes_own_nocell_bytes with "Pt1") as (bs) "[Hbs %Hbs]".
        iDestruct (bytes_own_of_bytes with "Hbs") as "Pt1"; [done|].
        iDestruct (lc_weaken (2 * 0) with "£r") as "£0"; [lia|].
        iModIntro. iApply ("HΦ" $! lK (cbytes ty y lK) 0 dh gh with "[%] [] Pt1 £0 Gho1'").
        { split_and!; [by eapply ty_bytes_val|lia|lia]. }
        { iApply guards_refl. }
        iIntros "Pt1".
        iMod ("Cl" $! (OfTy ty) (inl (PlaceIn y)) dh gh D [] 1%Qp True%I
          with "[//] [//] [//] [%] [%] [] ⧖ G' P [] [Pt1]") as "(Own & G & _)".
        { intros ??. apply prfn_rsv_in. }
        { lia. }
        { by iLeft. }
        { done. }
        { iIntros "_ !>". iSplit; [|done]. iExists y. iSplit; [done|].
          rewrite /ofty_owned. iFrame "Gho1 Pt1". }
        iModIntro. iFrame "G". by iApply (vplace_own_close with "⧖ ⧗p").
      + (* A shared-blocked leaf: its sharing guards its bytes. *)
        iDestruct "H" as (? ->) "(#GPt & #Shr & #Pers & Inh)".
        iAssert (shr_view β ty y dh D tid lK) as "#V".
        { iApply (shr_view_depth_mono _ _ _ dh gh); [lia|lia|]. by iFrame "GPt Shr Pers". }
        iDestruct (lc_weaken (((D + 1) + (D + 1)) + 2 * (D + 1)) with "£r") as "[£c £l]"; [lia|].
        iMod (shr_view_copy with "G'κs G' £c V") as (wv Hwv) "[#Gho G']"; [done..|].
        iDestruct "V" as "(Pt & _ & _)".
        iModIntro. iApply ("HΦ" $! lK G' (D + 1) dh D with "[%] [] G' £l Gho").
        { split_and!; [by eexists|lia|done]. }
        { iApply (guards_transitive_right with "G'κs Pt"). }
        iIntros "G'".
        iMod ("Cl" $! (ShrBlocked ty β) (inl (PlaceIn y)) dh gh D [] 1%Qp True%I
          with "[//] [//] [//] [%] [%] [] ⧖ G' P [] [Inh]") as "(Own & G & _)".
        { intros ??. apply prfn_rsv_in. }
        { lia. }
        { by iLeft. }
        { done. }
        { iIntros "_ !>". iSplit; [|done]. iExists y. by iFrame "GPt Shr Pers Inh". }
        iModIntro. iFrame "G". by iApply (vplace_own_close with "⧖ ⧗p").
  Qed.

  (** Below a shared reference at the hole of [K1] (below a root owned pointer or unique
      borrow): phase 1 accesses the shared reference ([wp_pshr_open]), phase 2 pushes the
      shared view of its referent through [K2]; the leaf is shared. *)
  Lemma wp_vplace_racc_pshr {ℭ 𝔅 𝔄} E (K1: pctx (at_locₛ 𝔅) 𝔄) `{!PctxNoShr K1}
      `{!PctxVRoot K1} κ (K2: pctx ℭ 𝔅) (lt: lty ℭ) (ty: type ℭ) κs `{!Copy ty} x ζm D tid p v
      (G: iProp Σ) Φ :
    let K := pctx_app K1 (PShr κ K2) in
    pctx_rleaf K lt ty κs → Timeless G → lazyE ⊆ E → eval_path p = Some v →
    llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ (G &&{↑NllftG}&&> @[pctx_alv K lt ⊓ κs]) -∗ G -∗
    £(advance_credits D) -∗ ⧖D -∗ ⧗(lty_vnrc (pctx_plug K lt)) -∗
    vroot_own (pctx_plug K lt) (pctx_vrfn K x ζm (lty_rfn lt (pctx_get K x) ζm (pctx_vpath K)))
      D tid v -∗
    vplace_rcont K lt ty x ζm D tid v E G Φ -∗
    WP pctx_vexpr K p @ E {{ Φ }}.
  Proof.
    intros K [-> ->]%pctx_rleafb_app_shr ? HE Hp.
    have ?: ↑NllftG ⊆ E. { trans lazyE; [apply lazyE_NllftG|done]. }
    rewrite /K /vplace_rcont pctx_plug_app pctx_vexpr_app pctx_get_app pctx_vrfn_app_shr.
    iIntros "#LFT #PROPH #UNIQ #Alv G £ #⧖ ⧗p Own HΦ".
    iAssert (G &&{↑NllftG}&&>
      @[pctx_ulft K1 (ShrLty (pctx_plug K2 lt) κ) ⊓ pctx_salv K2 κ])%I as "#Hus".
    { iApply (guards_transitive with "Alv").
      iApply llftl_incl_trans; [iApply llftl_intersect_incl_l|].
      by iApply pctx_alv_app_shr. }
    iAssert (G &&{↑NllftG}&&> @[pctx_ulft K1 (ShrLty (pctx_plug K2 lt) κ)])%I as "#Hu".
    { iApply (guards_transitive with "Hus"). iApply llftl_intersect_incl_l. }
    iAssert (G &&{↑NllftG}&&> @[pctx_salv K2 κ])%I as "#Hs".
    { iApply (guards_transitive with "Hus"). iApply llftl_intersect_incl_r. }
    iDestruct (lc_weaken (pshr_cred D + 4 * (D + 1)) with "£") as "[£a £r]";
      [apply pshr_cred_step|].
    iApply wp_fupd.
    iApply (wp_pshr_open _ K1 κ K2 lt (pctx_plug K2 lt) x ζm D tid _ p G
      with "LFT PROPH UNIQ Hu Hs G £a ⧖ [] Own"); [done|done|done|..].
    { iApply wp_wand; [by iApply wp_eval_path|]. by iIntros (?) "->". }
    iIntros (dh Hdh [Hin1 [Hin2 Hvin]]) "G Own #V".
    iAssert (G &&{↑NllftG}&&> @[pctx_slft K2 κ])%I as "#Hsl".
    { iApply (guards_transitive with "Hs"). iApply pctx_salv_slft. }
    iDestruct (lc_weaken (((D + 1) + (D + 1)) + 2 * (D + 1)) with "£r") as "[£c £l]"; [lia|].
    iMod (shr_view_copy with "Hsl G £c V") as (wv Hwv) "[#Gho G]"; [done..|].
    iDestruct "V" as "(Pt & _ & _)".
    iModIntro. iApply ("HΦ" $! _ G (D + 1) dh D with "[%] [] G £l Gho").
    { split_and!; [by eexists|lia|done]. }
    { iApply (guards_transitive_right with "Hsl Pt"). }
    iIntros "G !>". iFrame "G".
    by iApply (vplace_own_close with "⧖ ⧗p Own").
  Qed.


  (** ** Reading in a view

      The read access to the hole of [K] in the view of a place at [l] (the referent of a
      resolved unique borrow, at [κ]): the access to a sub-place of the view
      ([view_pctx_acc]) down to the hole or to the first shared reference, whose shared view
      is then pushed through the rest of the context ([shr_pctx_view]). The base address [e]
      is evaluated first; [R] is what its evaluation keeps. The leaf is shared: its bytes
      are guarded by [G], and the view is given back at once. *)
  Definition view_cred (M: nat) : nat := 6 * M * M + 14 * M + 6.

  Lemma wp_view_racc {ℭ 𝔅} E (K: pctx ℭ 𝔅) `{!PctxRead K} κ (lt: lty ℭ) (ty: type ℭ) κs
      `{!Copy ty} b m z ζm q d g tid (l: loc) M (G R: iProp Σ) (e: expr) (Φ: val → iProp Σ) :
    ↑NllftG ⊆ E → Timeless G → pctx_rleafb K b lt ty κs → d ≤ M → g ≤ M →
    let V := lty_view (pctx_plug K lt) κ m (pctx_pat K (lty_pat lt))
      (pctx_rfn K z ζm q (lty_rfn lt (pctx_get K z) ζm (pctx_path K q))) d g tid l in
    (G &&{↑NllftG}&&> @[pctx_salv K κ ⊓ κs]) -∗ G -∗ £(view_cred M) -∗ V -∗
    WP e @ E {{ v, ⌜v = #(l)⌝ ∗ R }} -∗
    (∀ (l': loc) dd dh gh, ⌜is_Some (ty.(ty_val) (pctx_get K z)) ∧ dh ≤ M ∧ gh ≤ M⌝ -∗
      (G &&{↑naN; dd}&&> cbytes ty (pctx_get K z) l') -∗ £(2 * dd) -∗
      ty.(ty_gho_own) (pctx_get K z) dh gh tid -∗ R -∗ G -∗ V -∗ Φ #l') -∗
    WP pctx_expr K e @ E {{ Φ }}.
  Proof.
    intros HE ? Hl Hd Hg V. iIntros "#Gs G £ V WPe HΦ".
    iAssert (G &&{↑NllftG}&&> @[pctx_salv K κ])%I as "#Gs1".
    { iApply (guards_transitive with "Gs"). iApply llftl_intersect_incl_l. }
    iApply wp_fupd.
    destruct (pctx_read_split K pctx_read_c)
      as [HK|[(𝔅' & κ' & K1 & K2 & -> & HK1)|(𝔅' & κ' & K1 & K2 & -> & HK1 & _ & _)]].
    - (* Below no shared reference: the leaf is shared in the view. *)
      have ?: PctxNoShr K by done.
      have [b' Hl'] : ∃ b', lty_rleaf b' lt ty κs.
      { destruct (pctx_rleafb_noshr K b lt ty κs HK Hl) as [[_ ?]|?]; eauto. }
      iDestruct (view_pctx_acc K κ lt m (lty_pat lt) _ z ζm q d g tid l G with "Gs1 V")
        as (dh gh) "([%Hdh [%Hgh %Hin]] & Vh & #Gp & Cl)".
      rewrite (lty_rleaf_rfn _ _ _ _ _ _ _ Hl').
      iDestruct (lty_rleaf_shared with "Vh") as "[Vh #Vs]"; [done|].
      iDestruct (shr_view_depth_mono _ _ _ dh gh dh M with "Vs") as "#Vs'"; [lia|lia|].
      iAssert (G &&{↑NllftG}&&> @[pctx_slft K κ ⊓ κs])%I as "#Gsl".
      { iApply (guards_transitive with "Gs"). iApply llftl_incl_glb;
          [|iApply llftl_intersect_incl_r].
        iApply llftl_incl_trans; [iApply llftl_intersect_incl_l|iApply pctx_salv_slft]. }
      iDestruct (lc_weaken (2 * (g + 1) * pctx_dlev K + (((M + 1) + (M + 1)) + 2 * (M + 1)))
        with "£") as "(£s & £c & £l)"; [rewrite /view_cred; nia|].
      iApply (wp_pctx_sexpr E K (lty_size lt) (g + 1) G z l e); [done|].
      iApply (wp_wand with "WPe"). iIntros (v) "[-> R]".
      iFrame "Gp £s G". iSplit; [done|]. iIntros "G".
      iMod (shr_view_copy with "Gsl G £c Vs'") as (w Hw) "[#Gho G]"; [done..|].
      iDestruct "Vs'" as "(Pt & _ & _)".
      iModIntro. iApply ("HΦ" with "[%] [] £l Gho R G"); [split_and!; [by eexists|lia|lia]| |].
      { iApply (guards_transitive_right with "Gsl Pt"). }
      iApply ("Cl" $! lt (lty_pat lt) _ dh gh d g with "[//] [//] [//] [%] [Vh]"); [lia|].
      by rewrite (lty_rleaf_rfn _ _ _ _ _ _ _ Hl').
    - (* Below a shared reference at the hole of [K1] in the view. *)
      have ?: PctxNoShr K1 by done.
      apply pctx_rleafb_app_shr in Hl as [-> ->].
      rewrite /V pctx_plug_app pctx_pat_app pctx_rfn_app pctx_get_app pctx_path_app_ctx
        pctx_expr_app pctx_salv_app //.
      cbn [pctx_plug pctx_pat pctx_rfn pctx_get pctx_salv pctx_expr].
      iDestruct (view_pctx_acc K1 κ (ShrLty (pctx_plug K2 lt) κ') m PatLeaf
        (inl (PlaceIn (pctx_get K1 z))) z ζm q d g tid l G with "[] V")
        as (dh gh) "([%Hdh [%Hgh %Hin]] & Vh & #Gp & Cl)".
      { iApply (guards_transitive with "Gs1"). rewrite (pctx_salv_slft_noshr K1) //.
        iApply llftl_intersect_incl_l. }
      set y := pctx_get K1 z. set κh := pctx_slft K1 κ.
      set lh := pctx_loc K1 (lty_size (ShrLty (pctx_plug K2 lt) κ')) z l.
      iDestruct "Vh" as "[Vl %Hvin]". iEval (rewrite /= /view_leaf) in "Vl".
      iDestruct "Vl" as (? ->) "#(Gb & Shr & Pers)".
      simpl in Hvin. have Hvin0 := Hvin. apply lty_vin_plug in Hvin as [Hvin2 _].
      iDestruct (lc_weaken (2 * (g + 1) * pctx_dlev K1 + (dh * (gh + 3) +
        (2 * (g + 1) * (M + 1) + (((M + 1) + (M + 1)) + 2 * (M + 1))))) with "£")
        as "(£s & £v & £s2 & £c & £l)".
      { rewrite /view_cred. nia. }
      iMod (shr_pctx_view (PShr κ' K2) κh lt y dh gh tid lh G with "[] £v [$Gb $Shr $Pers]")
        as "[#Gp2 (%dh' & %Hdh' & #Vh2)]".
      { simpl. by apply pctx_vin_in. }
      { iApply (guards_transitive with "Gs"). iApply llftl_intersect_incl_l. }
      iAssert (G &&{↑NllftG}&&> @[pctx_slft K2 κ'])%I as "#Gsl".
      { iApply (guards_transitive with "Gs"). iApply llftl_incl_trans;
          [iApply llftl_intersect_incl_l|].
        iApply llftl_incl_trans; [iApply llftl_intersect_incl_r|iApply pctx_salv_slft]. }
      iDestruct (shr_view_depth_mono _ _ _ dh' gh dh' M with "Vh2") as "#Vh2'"; [lia|lia|].
      iApply (wp_pctx_sexpr E (PShr κ' K2) (lty_size lt) (gh + 1) G y lh (pctx_expr K1 e));
        [done|].
      iApply (wp_pctx_sexpr E K1 (lty_size (ShrLty (pctx_plug K2 lt) κ')) (g + 1) G z l e);
        [done|].
      iApply (wp_wand with "WPe"). iIntros (v) "[-> R]".
      iSplit; [done|]. iSplitR; [iExact "Gp"|]. iSplitL "£s"; [iExact "£s"|].
      iSplitL "G"; [iExact "G"|]. iIntros "G".
      iSplit; [done|]. iSplitR; [iExact "Gp2"|].
      iSplitL "£s2"; [iApply (lc_weaken with "£s2"); simpl in *; nia|].
      iSplitL "G"; [iExact "G"|]. iIntros "G".
      iMod (shr_view_copy with "Gsl G £c Vh2'") as (w Hw) "[#Gho G]"; [done..|].
      iDestruct "Vh2'" as "(Pt & _ & _)".
      iModIntro. iApply ("HΦ" with "[%] [] £l Gho R G");
        [split_and!; [by eexists|simpl in *; lia..]| |].
      { iApply (guards_transitive_right with "Gsl Pt"). }
      iApply ("Cl" $! (ShrLty (pctx_plug K2 lt) κ') PatLeaf (inl (PlaceIn y)) dh gh d g
        with "[//] [//] [//] [%] []"); [lia|].
      rewrite /=. iSplit; [|done]. rewrite /view_leaf. iExists y. by iFrame "Gb Shr Pers".
    - (* A resolved unique borrow in a view: its view is empty. *)
      have ?: PctxNoShr K1 by done.
      rewrite /V pctx_plug_app pctx_pat_app pctx_rfn_app.
      iDestruct (view_pctx_acc K1 κ (ResUniqLty (pctx_plug K2 lt) κ') with "[] V")
        as (dh gh) "(_ & [] & _)".
      iApply (guards_transitive with "Gs1"). rewrite pctx_salv_app // (pctx_salv_slft_noshr K1) //=.
      iApply llftl_incl_trans; [iApply pctx_salv_incl|]. iApply llftl_intersect_incl_l.
  Qed.

  (** Below a resolved unique borrow at the hole of [K1] (in the owned part of a place rooted
      at an owned location): the pointer of the resolved borrow is loaded, and the hole is
      read in the view of its referent. *)
  Lemma wp_vplace_racc_res {ℭ 𝔅 𝔄} E n (K1: pctx (uniq_borₛ 𝔅) 𝔄) `{!PctxNoUniq K1}
      κ (K2: pctx ℭ 𝔅) `{!PctxRead K2} (lt: lty ℭ) (ty: type ℭ) κs `{!Copy ty} x ζm D tid p v
      (G: iProp Σ) Φ :
    let K := POwn n (pctx_app K1 (PResUniq κ K2)) in
    pctx_rleaf K lt ty κs → Timeless G → ↑NllftG ⊆ E → eval_path p = Some v →
    (G &&{↑NllftG}&&> @[pctx_alv K lt ⊓ κs]) -∗ G -∗
    £(advance_credits D) -∗ ⧖D -∗ ⧗(lty_vnrc (pctx_plug K lt)) -∗
    vroot_own (pctx_plug K lt) (pctx_vrfn K x ζm (lty_rfn lt (pctx_get K x) ζm (pctx_vpath K)))
      D tid v -∗
    vplace_rcont K lt ty x ζm D tid v E G Φ -∗
    WP pctx_vexpr K p @ E {{ Φ }}.
  Proof.
    have ?: PctxNoShr K1 by apply _.
    intros K Hl ? HE Hp.
    destruct (pctx_rleafb_app_noshr K1 _ true lt ty κs pctx_no_shr Hl) as [b Hl'].
    iIntros "#Alv G £ #⧖ ⧗p Own HΦ".
    destruct x as [l x₀].
    rewrite /K /vplace_rcont /= pctx_plug_app pctx_expr_app pctx_rfn_app pctx_get_app
      pctx_path_app_ctx /=.
    iDestruct "Own" as (d g -> Hle) "[Fr Own]".
    iAssert (G &&{↑NllftG}&&> @[pctx_salv K2 κ ⊓ κs])%I as "#Hs".
    { iApply (guards_transitive with "Alv").
      iApply llftl_incl_glb; [|iApply llftl_intersect_incl_r].
      iApply llftl_incl_trans; [iApply llftl_intersect_incl_l|].
      iApply llftl_incl_trans; [by iApply (pctx_alv_app K1 (PResUniq κ K2))|].
      iApply llftl_intersect_incl_r. }
    set lt1 := ResUniqLty (pctx_plug K2 lt) κ.
    rewrite /ltype_own lty_pat_plug ltype_own_plug.
    iDestruct "Own" as "[H Rest]".
    iDestruct (pctx_own_mode_le with "Rest") as %Hk.
    set y := pctx_get K1 x₀.
    set q0 := pctx_path K1 [].
    set lK := pctx_loc K1 (lty_size lt1) x₀ l.
    destruct y as [[[[[ly z] ξi] d0] g0] idx0] eqn:Hy.
    rewrite /= /res_node /=. iDestruct "H" as "[Pt N]".
    iDestruct (lc_weaken (pctx_mode K1 1 + view_cred D) with "£") as "[£m £]";
      [rewrite /advance_credits /view_cred pctx_mode_add; nia|].
    iMod (lc_fupd_elim_laterN with "£m N") as "(#Incl & %d' & %g' & %Hle' & V)".
    rewrite lty_pat_plug.
    have ?: pctx_depth K1 d ≤ d by (rewrite pctx_depth_sub; lia).
    iApply (wp_view_racc _ K2 κ lt ty κs false 0 z ζm (false :: q0) d' g' tid ly D G
      (ptr_cell lK ly ∗ pctx_own K1 (lty_size lt1) 1 x₀ ζm [] d g tid l)%I
      with "Hs G £ V [Pt Rest]"); [done|done|lia|lia|..].
    { wp_bind (pctx_expr K1 p).
      iApply (wp_wand with "[Rest]").
      { iApply (wp_pctx_expr_mask _ K1 (lty_size lt1) 1 x₀ ζm [] d g tid l p True True
          with "[] Rest").
        wp_bind p. iApply wp_wand; [by iApply wp_eval_path|]. iIntros (?) "->".
        iFrame; by iPureIntro. }
      iIntros (w) "(-> & _ & _ & Rest)".
      iDestruct "Pt" as (bs) "[Hbs %Hbs]".
      wp_bind (Load _ _ _). iApply (wp_load_na with "Hbs"); [exact Hbs|]. iIntros "!> Hbs".
      iSplit; [done|]. iFrame "Rest". iExists bs. by iFrame. }
    iIntros (l' dd dh gh (Hw & ? & ?)) "#Guard £dd #Gho [Pt Rest] G V".
    iApply ("HΦ" $! l' G dd dh gh with "[%] Guard G £dd Gho"); [done|].
    iIntros "G !>". iFrame "G".
    iApply (vplace_own_close (POwn n K1) _ _ _ D with "⧖ ⧗p"). rewrite /=.
    iExists d, g. iSplit; [done|]. iSplit; [done|]. iFrame "Fr".
    rewrite /ltype_own lty_pat_plug lty_rfn_plug ltype_own_plug -/y Hy. iFrame "Rest".
    rewrite /= /res_node /=. iFrame "Pt".
    iApply bi.laterN_intro. iFrame "Incl".
    iExists d', g'. iSplit; [done|]. by rewrite lty_pat_plug.
  Qed.

  (** Below the resolved unique borrow at the root ([p ◁ₗ ResUniqLty (K2[lt]) κ]). *)
  Lemma wp_vplace_racc_res_root {ℭ 𝔅} E κ (K2: pctx ℭ 𝔅) `{!PctxRead K2} (lt: lty ℭ)
      (ty: type ℭ) κs `{!Copy ty} x ζm D tid p v (G: iProp Σ) Φ :
    pctx_rleaf (PResUniq κ K2) lt ty κs → Timeless G → ↑NllftG ⊆ E → eval_path p = Some v →
    (G &&{↑NllftG}&&> @[pctx_alv (PResUniq κ K2) lt ⊓ κs]) -∗ G -∗
    £(advance_credits D) -∗ ⧖D -∗ ⧗(lty_vnrc (pctx_plug (PResUniq κ K2) lt)) -∗
    vroot_own (pctx_plug (PResUniq κ K2) lt)
      (pctx_vrfn (PResUniq κ K2) x ζm
        (lty_rfn lt (pctx_get (PResUniq κ K2) x) ζm (pctx_vpath (PResUniq κ K2)))) D tid v -∗
    vplace_rcont (PResUniq κ K2) lt ty x ζm D tid v E G Φ -∗
    WP pctx_vexpr (PResUniq κ K2) p @ E {{ Φ }}.
  Proof.
    iIntros (Hl ? HE Hp) "#Alv G £ #⧖ ⧗p Own HΦ". rewrite /vplace_rcont /=.
    destruct x as [[[[[lx z] ξi] d0] g0] idx0].
    iDestruct "Own" as (d g [Hd Hg]) "[-> (#Incl & %d' & %g' & %Hle' & V)]".
    rewrite lty_pat_plug.
    iDestruct (lc_weaken (view_cred D) with "£") as "£";
      [rewrite /advance_credits /view_cred; nia|].
    iApply (wp_view_racc _ K2 κ lt ty κs false 0 z ζm [] d' g' tid lx D G
      True%I with "Alv G £ V [] [-]"); [done|done|lia|lia|..].
    { wp_bind p. iApply wp_wand; [by iApply wp_eval_path|]. iIntros (?) "->". iFrame; by iPureIntro. }
    iIntros (l' dd dh gh (Hw & ? & ?)) "#Guard £dd #Gho _ G V".
    iApply ("HΦ" $! l' G dd dh gh with "[%] Guard G £dd Gho"); [done|].
    iIntros "G !>". iFrame "G".
    iApply (vplace_own_close (PResUniq κ K2) _ _ _ D with "⧖ ⧗p"). rewrite /=.
    iExists d, g. iSplit; [done|]. iSplit; [done|]. iFrame "Incl".
    iExists d', g'. iSplit; [done|]. by rewrite lty_pat_plug.
  Qed.

  (** The read access to the shared reference at the root ([p ◁ₗ ShrLty (K2[lt]) κ]). *)
  Lemma wp_vplace_racc_pshr_root {ℭ 𝔅} E κ (K2: pctx ℭ 𝔅) (lt: lty ℭ) (ty: type ℭ) κs
      `{!Copy ty} x ζm D tid p v (G: iProp Σ) Φ :
    pctx_rleaf (PShr κ K2) lt ty κs → Timeless G → ↑NllftG ⊆ E → eval_path p = Some v →
    (G &&{↑NllftG}&&> @[pctx_alv (PShr κ K2) lt ⊓ κs]) -∗ G -∗
    £(advance_credits D) -∗ ⧖D -∗ ⧗(lty_vnrc (pctx_plug (PShr κ K2) lt)) -∗
    vroot_own (pctx_plug (PShr κ K2) lt)
      (pctx_vrfn (PShr κ K2) x ζm
        (lty_rfn lt (pctx_get (PShr κ K2) x) ζm (pctx_vpath (PShr κ K2)))) D tid v -∗
    vplace_rcont (PShr κ K2) lt ty x ζm D tid v E G Φ -∗
    WP pctx_vexpr (PShr κ K2) p @ E {{ Φ }}.
  Proof.
    intros [-> ->] ? HE Hp. iIntros "#Alv G £ #⧖ ⧗p Own HΦ". rewrite /vplace_rcont /=.
    iAssert (G &&{↑NllftG}&&> @[pctx_salv K2 κ])%I as "#Hs".
    { iApply (guards_transitive with "Alv"). iApply llftl_intersect_incl_l. }
    iDestruct (lc_weaken (pshr_cred D + 4 * (D + 1)) with "£") as "[£a £r]";
      [apply pshr_cred_step|].
    iApply wp_fupd.
    iApply (wp_pshr_open_root _ κ K2 lt (pctx_plug K2 lt) x D tid v p G
      with "Hs G £a [] Own"); [done|done|done|..].
    { iApply wp_wand; [by iApply wp_eval_path|]. by iIntros (?) "->". }
    iIntros (dh Hdh [Hin2 Hvin]) "G Own #V".
    iAssert (G &&{↑NllftG}&&> @[pctx_slft K2 κ])%I as "#Hsl".
    { iApply (guards_transitive with "Hs"). iApply pctx_salv_slft. }
    iDestruct (lc_weaken (((D + 1) + (D + 1)) + 2 * (D + 1)) with "£r") as "[£c £l]"; [lia|].
    iMod (shr_view_copy with "Hsl G £c V") as (wv Hwv) "[#Gho G]"; [done..|].
    iDestruct "V" as "(Pt & _ & _)".
    iModIntro. iApply ("HΦ" $! _ G (D + 1) dh D with "[%] [] G £l Gho").
    { split_and!; [by eexists|lia|done]. }
    { iApply (guards_transitive_right with "Hsl Pt"). }
    iIntros "G !>". iFrame "G".
    by iApply (vplace_own_close (PShr κ K2) _ _ _ D with "⧖ ⧗p Own").
  Qed.

  (** A resolved leaf in the owned part of a place rooted at an owned location (below no
      unique borrow): its bytes are owned, and its resolved ownership is its ownership
      ([ResOwn]), which is persistent ([Copy]). *)
  Lemma wp_vplace_racc_ores {𝔅 𝔄} E n (K: pctx 𝔅 𝔄) `{!PctxNoUniq K} (ty: type 𝔅) `{!Copy ty}
      x ζm D tid p v (G: iProp Σ) Φ :
    ResOwn ty → eval_path p = Some v →
    G -∗ £(advance_credits D) -∗ ⧖D -∗ ⧗(lty_vnrc (pctx_plug (POwn n K) (OfRes ty))) -∗
    vroot_own (pctx_plug (POwn n K) (OfRes ty))
      (pctx_vrfn (POwn n K) x ζm
        (lty_rfn (OfRes ty) (pctx_get (POwn n K) x) ζm (pctx_vpath (POwn n K)))) D tid v -∗
    vplace_rcont (POwn n K) (OfRes ty) ty x ζm D tid v E G Φ -∗
    WP pctx_vexpr (POwn n K) p @ E {{ Φ }}.
  Proof.
    assert (NoCell 𝔅) by exact (copy_nocell ty).
    iIntros (Hres Hp) "G £ #⧖ ⧗p Own HΦ".
    destruct x as [l x₀]. rewrite /vplace_rcont /=.
    iDestruct "Own" as (d g -> Hle) "[Fr Own]".
    rewrite /ltype_own lty_pat_plug ltype_own_plug.
    iDestruct "Own" as "[L1 Rest]". iSimpl in "L1".
    iDestruct "L1" as (? ->) "[Pt1 Gr]".
    iDestruct (pctx_own_mode_le with "Rest") as %Hk.
    set y := pctx_get K x₀.
    set lK := pctx_loc K (lty_size (OfRes ty)) x₀ l.
    iDestruct (lc_weaken (pctx_mode K 1 + 2 * 0) with "£") as "[£ £0]";
      [rewrite /advance_credits pctx_mode_add; nia|].
    iMod (lc_fupd_elim_laterN with "£ Gr") as (d' g' Hdg) "Gr".
    iEval (rewrite res_own) in "Gr". iDestruct "Gr" as "#Gho".
    (* The address of the hole. *)
    iApply (wp_wand with "[Rest]").
    { iApply (wp_pctx_expr_mask E K (lty_size (OfRes ty)) 1 x₀ ζm [] d g tid l (p)
        True True with "[] Rest").
      wp_bind p. iApply wp_wand; [by iApply wp_eval_path|]. iIntros (?) "->".
      iFrame; by iPureIntro. }
    iIntros (w) "(-> & _ & _ & Rest)".
    iDestruct (bytes_own_nocell_bytes with "Pt1") as (bs) "[Hbs %Hbs]".
    iDestruct (bytes_own_of_bytes with "Hbs") as "Pt1"; [done|].
    iApply ("HΦ" $! lK (cbytes ty y lK) 0 d' g' with "[%] [] Pt1 £0 Gho").
    { split_and!; [by eapply ty_bytes_val|rewrite pctx_depth_sub in Hdg; lia|lia]. }
    { iApply guards_refl. }
    iIntros "Pt1 !>". iFrame "G".
    iApply (vplace_own_close (POwn n K) _ _ _ D with "⧖ ⧗p"). rewrite /=.
    iExists d, g. iSplit; [done|]. iSplit; [done|]. iFrame "Fr".
    rewrite /ltype_own lty_pat_plug ltype_own_plug. iFrame "Rest".
    iExists y. iSplit; [done|]. iSplitL "Pt1"; [done|].
    iApply bi.laterN_intro. iExists d', g'. iSplit; [done|]. by rewrite res_own.
  Qed.

  (** ** The read access

      The read access to the hole of [K], for any [K] of the read rule, at the address of
      the hole ([pctx_vexpr K p]), with the credits of a program step at the depth of the
      place. The context is split at its first shared reference or resolved unique borrow
      ([pctx_read_split]). *)
  Lemma wp_vplace_racc {𝔅 𝔄} E (K: pctx 𝔅 𝔄) `{!PctxVRoot K} `{!PctxRead K}
      (lt: lty 𝔅) (ty: type 𝔅) κs `{!Copy ty} x ζm D tid p v (G: iProp Σ) Φ :
    pctx_rleaf K lt ty κs → Timeless G → lazyE ⊆ E → eval_path p = Some v →
    llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ (G &&{↑NllftG}&&> @[pctx_alv K lt ⊓ κs]) -∗ G -∗
    £(advance_credits D) -∗ ⧖D -∗ ⧗(lty_vnrc (pctx_plug K lt)) -∗
    vroot_own (pctx_plug K lt) (pctx_vrfn K x ζm (lty_rfn lt (pctx_get K x) ζm (pctx_vpath K)))
      D tid v -∗
    vplace_rcont K lt ty x ζm D tid v E G Φ -∗
    WP pctx_vexpr K p @ E {{ Φ }}.
  Proof.
    intros Hl ? HE Hp.
    have ?: ↑NllftG ⊆ E. { trans lazyE; [apply lazyE_NllftG|done]. }
    rename select (PctxVRoot K) into HR. rename select (PctxRead K) into HK.
    destruct K as [| | |? ? n K| |? ? κ K|? ? κ K|? ? κ K]; try done;
      rewrite /PctxRead /= in HK.
    - destruct (pctx_read_split K HK) as [HK'|[(𝔅' & κ & K1 & K2 & -> & HK1)|
        (𝔅' & κ & K1 & K2 & -> & HK1 & HKu & HK2)]].
      + have ?: PctxNoShr (POwn n K) by done.
        destruct (pctx_rleafb_noshr (POwn n K) true lt ty κs HK' Hl) as [[Hu Hl']|Hl'].
        * destruct (lty_rleaf_cases _ _ _ _ Hl') as [Hl''|(-> & Hres & ->)].
          -- by apply (wp_vplace_racc_noshr E (POwn n K) lt ty κs).
          -- have ?: PctxNoUniq K by done.
             iIntros "_ _ _ _ G £ ⧖ ⧗p Own HΦ".
             by iApply (wp_vplace_racc_ores with "G £ ⧖ ⧗p Own HΦ").
        * by apply (wp_vplace_racc_noshr E (POwn n K) lt ty κs).
      + have ?: PctxNoShr (POwn n K1) by done.
        by apply (wp_vplace_racc_pshr E (POwn n K1) κ K2 lt ty κs).
      + have ?: PctxNoUniq K1 by done. have ?: PctxRead K2 by done.
        iIntros "_ _ _ Alv G £ ⧖ ⧗p Own HΦ".
        by iApply (wp_vplace_racc_res E n K1 κ K2 lt ty κs with "Alv G £ ⧖ ⧗p Own HΦ").
    - destruct HK as [HKs HK].
      destruct (pctx_read_split K HK) as [HK'|[(𝔅' & κ' & K1 & K2 & -> & HK1)|
        (𝔅' & κ' & K1 & K2 & -> & HK1 & _)]].
      + have ?: PctxNoShr (PUniq κ K) by done.
        apply (wp_vplace_racc_noshr E (PUniq κ K) lt ty κs); [|done..].
        by destruct (pctx_rleafb_noshr (PUniq κ K) true lt ty κs (conj HKs HK') Hl) as [[[] _]|?].
      + have ?: PctxNoShr (PUniq κ K1).
        { split; [by eapply pctx_simple_app_l|done]. }
        by apply (wp_vplace_racc_pshr E (PUniq κ K1) κ' K2 lt ty κs).
      + exfalso. by apply (pctx_simple_app_not K1 (PResUniq κ' K2)); [intros ?|..].
    - iIntros "_ _ _ Alv G £ ⧖ ⧗p Own HΦ".
      by iApply (wp_vplace_racc_pshr_root E κ K lt ty κs with "Alv G £ ⧖ ⧗p Own HΦ").
    - have ?: PctxRead K by done.
      iIntros "_ _ _ Alv G £ ⧖ ⧗p Own HΦ".
      by iApply (wp_vplace_racc_res_root E κ K lt ty κs with "Alv G £ ⧖ ⧗p Own HΦ").
  Qed.
End read_acc.

(** * The rule *)

Section read.
  Context `{!typeG Σ}.

  (** Copying the value of a [Copy] leaf (of any size) out of the hole of [K], in any place
      rooted at a value: a typed [Load] ([!ᶜ{ty_mty ty}]) at the address of the hole, from
      the guarded bytes of the read access ([wp_load_na_guarded_gen]). The place does not
      change. *)
  Lemma type_read_place_instr {𝔅 𝔄} E L I p (K: pctx 𝔅 𝔄) `{!PctxVRoot K} `{!PctxRead K}
      (lt: lty 𝔅) (ty: type 𝔅) κs :
    pctx_rleaf K lt ty κs → Copy ty → lctx_lft_alive E L (pctx_alv K lt ⊓ κs) →
    typed_instr E L I +[p ◁ₗ pctx_plug K lt] (!ᶜ{ty.(ty_mty)} (pctx_vexpr K p))
      (λ v, +[v ◁ᵥ ty; p ◁ₗ pctx_plug K lt])
      (λ post '-[x], post -[pctx_get K x.1; x]).
  Proof.
    intros Hl Hcopy0 Alv. assert (NoCell 𝔅) by exact (copy_nocell ty).
    iIntros (tid post mask iκs [x []]) "#LFT #TIME #PROPH #UNIQ #E L I (Tp & _) Obs".
    destruct x as [x₀ ζm]. rewrite /read_copy.
    iDestruct "Tp" as (v Hp) "Tp". iEval (rewrite vplace_own_open) in "Tp".
    iDestruct "Tp" as (D) "(#⧖ & ⧗p & Own)".
    iDestruct (Alv with "L E") as "#Alv".
    (* The first step gives the credits. *)
    iApply (wp_persistent_time_receipt with "TIME ⧖"); [solve_ndisj|].
    iIntros "£ _". iApply wp_fupd.
    iMod (llctx_interp_make_guarded with "L") as (γh) "[H1 [H2 [#Ghalf #Halfback]]]";
      [solve_ndisj|].
    iAssert (fractional.half γh &&{↑NllftG}&&> @[pctx_alv K lt ⊓ κs])%I as "#Hg".
    { iApply (guards_transitive with "Ghalf Alv"). }
    wp_bind (pctx_vexpr K p).
    iApply (wp_vplace_racc _ K lt ty κs with "LFT PROPH UNIQ Hg H1 £ ⧖ ⧗p Own");
      [done|solve_ndisj|done|].
    rewrite /vplace_rcont.
    iIntros (l G2 dd dh gh ([w Hw] & ? & ?)) "#Guard G2 £ #Gho Cl".
    iApply (wp_load_na_guarded_gen _ _ _ w G2 (cbytes ty (pctx_get K x₀) l)
      (ty_bytes ty (pctx_get K x₀)) dd with "[$G2 $£]");
      [solve_ndisj|intros; by eapply ty_bytes_decode| |].
    { iFrame "Guard". iApply bytes_own_view_nocell. }
    iIntros "!> G2". iMod (fupd_mask_mono with "(Cl G2)") as "[Tp H1]"; [solve_ndisj|].
    iMod (fupd_mask_mono with "(Halfback H1 H2)") as "L"; [solve_ndisj|].
    iModIntro. iExists -[pctx_get K x₀; (x₀, ζm)]. iFrame "L I Obs".
    iSplitR "Tp".
    { iExists _. iSplit; [by rewrite eval_path_of_val|].
      rewrite -(val_own_intro_sep _ _ _ _ w D); [|done|done].
      iFrame "⧖". iDestruct (ty_gho_own_depth_mono _ dh gh D D with "Gho") as "[$ _]"; lia. }
    iSplit; [|done]. iExists _. by iFrame.
  Qed.
End read.
