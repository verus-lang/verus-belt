(** * Resolving and dropping places

  This file adds general rules for giving up a place element (see
  [design_docs/verus-belt-phase3-design.md], section "Resolve and drop").

  The resolution of a place to a readable state (any context, the root unique borrow
  included) is [type_resolve_place_instr] of [place_res_rslv.v]; giving up the resolved
  place afterwards is forgetting it ([tctx_incl_resolve_head]). This file has the program
  steps paid by later credits ([ctask], [skipn]) used by it, and:

  ** Places rooted at a unique borrow

  [tctx_drop_vplace_uniq] gives up [p ◁ₗ{κ} lt] (a place rooted at the value of a unique
  borrow, [vplace.v]) whose leaves are all blocked, without a program step: the prophecy
  variable of the borrow is pre-resolved, through its reservation, to the current value
  of the place.

  ** Places rooted at an owned location

  [resolve_tctx_cons_oplace] resolves (and leaks) [p ◁ₗown{n} lt] in a context (e.g. at a
  jump), with a resolution condition per unblocked leaf ([lty_resolve], from [resolve] of
  the leaf's type; moved-out leaves [Moved ty] and uninitialized leaves [OfTy (↯ n)] need
  nothing); blocked and shared-blocked
  leaves are forgotten (their lender keeps the borrow, and gets the contents back at the
  end of the lifetime). [type_drop_oplace_instr] frees the memory of the place and,
  recursively, the pointees of its unfolded owned pointers ([OwnPtrLty], [drop_boxes]),
  resolving the leaves as above, for places none of whose leaves (outside the pointees) is
  blocked or shared ([lty_freeb]): the memory of such a leaf is lent, so it must not be
  freed (a pointee with a blocked leaf is leaked instead, [own_freeb]). Owned pointers in
  unblocked leaves ([OfTy (own_bytes …)]) are resolved by their type and their pointees
  leaked, as by [type_delete_instr]. [type_uninit_oplace_instr] is the same, but keeps the
  memory of the place, as an uninitialized place [OfTy (↯ n)] (e.g. a box whose fields have
  all been moved out, to be re-used).

  ** Places below shared references

  These are plain [p ◁ &shr{κ} ty] elements (see [place_shr.v]); they are dropped as
  any element ([resolve_just]). *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var.
From lrust.lang Require Import proofmode.
From lrust.lang.lib Require Import new_delete.
From lrust.util Require Import update.
From lrust.typing Require Export type ltype lpath place_own.
From lrust.typing Require Import type_context programs lft_contexts uniq_util uniq_bor own shr_bor bytes_layout value_ctx unit uninit freeable_util gmb_cells.
From lrust.lifetime Require Import lifetime_full.
From guarding Require Import guard tactics.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

(** * Tasks paid by later credits, one batch per program step *)

Section ctask.
  Context `{!typeG Σ}.

  (** [ctask c k R]: [R] can be obtained given [k] batches of [c] later credits. *)
  Fixpoint ctask (c k: nat) (R: iProp Σ) : iProp Σ :=
    match k with
    | O => |={⊤}=> R
    | S k => |={⊤}=> (£c -∗ ctask c k R)
    end%I.

  Lemma ctask_fupd c k R : (|={⊤}=> ctask c k R) ⊢ ctask c k R.
  Proof. destruct k; simpl; iIntros ">$". Qed.

  Lemma ctask_mono c k R R' : (R ={⊤}=∗ R') -∗ ctask c k R -∗ ctask c k R'.
  Proof.
    induction k as [|k IH]; simpl; iIntros "W >T"; [by iApply "W"|].
    iIntros "!> £". iApply (IH with "W"). by iApply "T".
  Qed.

  Lemma ctask_sep c k1 k2 R1 R2 :
    ctask c k1 R1 -∗ ctask c k2 R2 -∗ ctask c (k1 + k2) (R1 ∗ R2).
  Proof.
    induction k1 as [|k1 IH]; simpl.
    - iIntros "R1 T2". iApply (ctask_mono with "[R1] T2"). iIntros "R2". iMod "R1". by iFrame.
    - iIntros "T1 T2". iMod "T1". iIntros "!> £". iApply (IH with "[T1 £] T2"). by iApply "T1".
  Qed.

  Lemma ctask_weaken c c' k R : c ≤ c' → ctask c k R -∗ ctask c' k R.
  Proof.
    intros ?. induction k as [|k IH]; simpl; iIntros ">T !>"; [done|]. iIntros "£".
    iApply IH. iApply "T". by iApply (lc_weaken with "£").
  Qed.

  (** A sequence of [k] program steps. *)
  Fixpoint skipn (k: nat) : expr :=
    match k with O => #☠ | S k => Skip;; skipn k end%E.

  Global Instance skipn_closed k : Closed [] (skipn k).
  Proof. induction k; simpl; [done|]. by apply _. Qed.

  (** Each step gives a batch of later credits (from the persistent time receipt). *)
  Lemma wp_skipn_ctask k c D R Φ :
    c ≤ advance_credits D →
    time_ctx -∗ ⧖D -∗ ctask c k R -∗ (R -∗ Φ #☠) -∗ WP skipn k {{ Φ }}.
  Proof.
    iIntros (Hc) "#TIME ⧖ T HΦ". iInduction k as [|k IH] forall (D Hc); simpl.
    - iMod "T". iApply wp_value. by iApply "HΦ".
    - iMod "T". wp_bind Skip.
      iApply (wp_persistent_time_receipt with "TIME ⧖"); [solve_ndisj|].
      iIntros "£ ⧖S". wp_let. wp_let.
      iApply ("IH" $! (S D) with "[] ⧖S [T £] HΦ").
      { iPureIntro. etrans; [done|]. apply advance_credits_mono. lia. }
      iApply "T". by iApply (lc_weaken with "£").
  Qed.
End ctask.

(** * Resolving a place rooted at a unique borrow value

  A place [p ◁ₗ{κ} lt], i.e. [p ◁ₗ UniqLty lt κ] ([vplace.v]): the root is the node value
  of the borrow ([uniq_nval]), whose referent is in [Uniq κ] mode. *)

Section vplace_uniq.
  Context `{!typeG Σ}.

  (** Give up the root borrow while all leaves of the (compound) referent are blocked: its
      prophecy variable is pre-resolved, through its reservation, to the current value of
      the place. *)
  Lemma tctx_drop_vplace_uniq {𝔄} E L p κ (lt: lty 𝔄) :
    lctx_lft_alive E L κ → lty_is_cpd lt → lty_blk_all lt →
    tctx_incl E L +[p ◁ₗ UniqLty lt κ] +[]
      (λ post '-[x], λ mask π,
        uniq_bor_future x.1 π = prfn_den (lty_rfn lt (uniq_bor_current x.1) x.2 []) π →
        post -[] mask π).
  Proof.
    intros Alv Hc Hb. split.
    { intros ?? Eq [? []] ??. split=> H ?; apply Eq, H; done. }
    iIntros (G tid [x []] mask post ?) "#LFT #PROPH #UNIQ #E #GL G [T _] Obs".
    destruct x as [[[[[[l x₀] ξi] d'] g'] idx] ζm].
    iDestruct "T" as (v ? D) "(_ & _ & %d & %g & %Hle & -> & _ & _ & #Incl & %d1 & %g1 & %Hle1 & Own)".
    leaf_open "GL" with "G" as "[L back]"; [set_solver|].
    iDestruct (Alv with "L E") as "#Lκ". iMod ("back" with "L") as "G".
    iDestruct (guards_transitive with "GL Lκ") as "#Gκ".
    rewrite /ltype_own ltype_own_cp_uniq_cpd //.
    iDestruct "Own" as (x₀' κp γ γf idx' ζl) "(#Inclp & %Hr & Tok & Gh & Tf & ⧗o & #Bor)".
    set r : prfn 𝔄 := lty_rfn lt x₀ ζm [].
    set uπ : proph (uniq_cellₛ 𝔄) :=
      λ π, (prfn_den r π, (1%positive, (1%positive, 1%positive))).
    have Hdep: uπ ./ ζl.
    { apply (proph_dep_constr (λ a, (a, (1%positive, (1%positive, 1%positive))))).
      by apply lty_blk_all_dep. }
    iMod (proph_idx_bor_gen_preresolve_rsv ⊤ κ (uniq_prvar x₀' ξi) (uniq_cell x₀' d1 g1 γ) idx'
      ζl _ uπ G with "LFT PROPH UNIQ Gκ [Gh Tf] G Tok Bor") as "[#Obs' $]";
      [solve_ndisj|done| |].
    { iIntros (wπ) "Body". iNext.
      iDestruct "Body" as "[Body|[Tf' _]]"; [|iDestruct (cpd_tok_excl with "Tf Tf'") as "[]"].
      iLeft. rewrite !cpd_body_cell. iDestruct "Body" as (p1 r1) "(Ok & % & Gh' & Upd)".
      iDestruct (ghost_var_agree with "Gh Gh'") as %[<- <-]%lstate_inj.
      iExists _, _. by iFrame. }
    iModIntro. iExists -[]. iSplit; [done|].
    iCombine "Obs Obs'" as "Obs". iApply (proph_obs_impl with "Obs")=> π [Hπ Heq].
    apply Hπ. rewrite uniq_bor_future_eq (uniq_prvar_app_irrel x₀ x₀') Heq. done.
  Qed.

End vplace_uniq.

(** * Resolving places in [Owned] mode

  [lty_resolve E L lt Φ]: the [Owned m] interpretation of [lt] at the refinement of a
  value [x] can be resolved (consumed) to the condition [Φ x] on the current value, in
  [m + d*(g+1)] steps (as [resolve] for types, plus one step per owned pointer above,
  for the laters of the ghost ownership). Only unblocked leaves contribute; the other
  leaves are forgotten ([lty_resolve_just]): a blocked leaf's lender keeps its borrow,
  and a shared-blocked leaf's value is persistent. The memory owned by the place is
  given back ([lty_omem]: the memory of the place itself if no leaf is blocked, and the
  pointees of its owned pointers), so that it can be freed ([type_drop_oplace_instr]). *)

Section lty_mem.
  Context `{!typeG Σ}.

  (** The memory of a place (outside the pointees of its owned pointers) is owned: no
      leaf is blocked or shared. *)
  Fixpoint lty_freeb {𝔄} (lt: lty 𝔄) : bool :=
    match lt with
    | OfTy _ | OwnPtrLty _ _ | UniqLty _ _ | ShrLty _ _ | OfRes _ | ResUniqLty _ _ | Moved _ => true
    | StructLty _ lts => foldr andb true (hcmap (λ _ lt, lty_freeb lt) lts)
    | SumLty _ _ lt => lty_freeb lt
    | Blocked _ _ | ShrBlocked _ _ => false
    end.

  (** The pointee of an owned pointer [OwnPtrLty n lt] is freed when the place is
      dropped if its memory is owned and its size is [n]. *)
  Definition own_freeb {𝔄} (n: nat) (lt: lty 𝔄) : bool :=
    lty_freeb lt && bool_decide (n = lty_size lt).

  (** [n] bytes of memory at [l], which may embed cells (the memory of a leaf whose value
      embeds cells: the contents ([gcont]) of a value of size [n]); before the memory is
      freed, the cells are dropped ([lty_omem_forget]), which gives plain bytes
      ([mem_bytes]). *)
  Definition mem_cell (l: loc) (n: nat) : iProp Σ :=
    ∃ m fv, ⌜mty_wf m ∧ mty_size m = n⌝ ∗ gcont l m fv.
  Definition mem_bytes (l: loc) (n: nat) : iProp Σ := ∃ bs, l ↦b bs ∗ ⌜length bs = n⌝.

  Lemma mem_bytes_mem_cell l n : mem_bytes l n -∗ mem_cell l n.
  Proof.
    iIntros "(%bs & Hbs & %Hbs)". iExists (MTuple [] n 1), (fv_lift (VTuple [])).
    iSplit; [iPureIntro; split; [by repeat constructor|done]|].
    iApply (gcont_of_bytes with "Hbs"). rewrite decode_value_tuple decide_True //.
  Qed.

  Lemma pad_cell_mem_cell l n : pad_cell l n -∗ mem_cell l n.
  Proof. apply mem_bytes_mem_cell. Qed.

  (** The memory owned by a place in [Owned m] mode: the bytes of the place itself
      (unless a leaf is blocked or shared) and the memory of the pointees of its owned
      pointers that are freed by [drop_boxes]; the right to free a pointee is under [m]
      laters, as in [own_node]. *)
  Fixpoint lty_omem_gen (M: loc → nat → iProp Σ) {𝔄} (m: nat) (lt: lty 𝔄) {struct lt} :
      loc → iProp Σ :=
    match lt in lty 𝔄 return loc → iProp Σ with
    | OfTy _ | OfRes _ | UniqLty _ _ | ShrLty _ _ | ResUniqLty _ _ | Moved _ =>
        λ l, M l (lty_size lt)
    | OwnPtrLty n lt' => λ l, ∃ l': loc, ptr_cell l l' ∗
        if own_freeb n lt' then
          ▷^m freeable_sz n (lty_size lt') l' ∗
          lty_omem_gen M (m + 1) lt' l'
        else True
    | @StructLty _ _ 𝔄l Lay lts => λ l,
        (fix go {𝔅l} (offs: list nat) (lts: hlist lty 𝔅l) {struct lts} : iProp Σ :=
          match lts with
          | +[] => True
          | lt +:: lts' => match offs with
              | [] => False
              | o :: offs' => lty_omem_gen M m lt (l +ₗ o) ∗ go offs' lts'
              end
          end) _ (struct_offs Lay 𝔄l) lts ∗
        pad_own l (struct_fields Lay 𝔄l) (struct_size Lay 𝔄l)
    | @SumLty _ _ 𝔄l tyl i lt' => λ l,
        tag_cell 𝔄l l i ∗
        lty_omem_gen M m lt' (l +ₗ tag_size 𝔄l) ∗
        pad_cell ((l +ₗ tag_size 𝔄l) +ₗ lty_size lt') (sum_max 𝔄l - lty_size lt')
    | Blocked _ _ | ShrBlocked _ _ => λ _, True
    end%I.
  (** The memory of the fields [lts] of a struct (at [l], at the offsets [offs]). *)
  Definition fields_omem (M: loc → nat → iProp Σ) (m: nat) (l: loc) :
      ∀ {𝔅l}, list nat → hlist lty 𝔅l → iProp Σ :=
    fix go {𝔅l} (offs: list nat) (lts: hlist lty 𝔅l) {struct lts} : iProp Σ :=
      match lts with
      | +[] => True
      | lt +:: lts' => match offs with
          | [] => False
          | o :: offs' => lty_omem_gen M m lt (l +ₗ o) ∗ go offs' lts'
          end
      end%I.

  Lemma lty_omem_struct M m {𝔄l} Lay (lts: hlist lty 𝔄l) l :
    lty_omem_gen M m (StructLty Lay lts) l =
      (fields_omem M m l (struct_offs Lay 𝔄l) lts ∗
       pad_own l (struct_fields Lay 𝔄l) (struct_size Lay 𝔄l))%I.
  Proof. done. Qed.

  (** The memory, with leaves that may embed cells ([lty_omem]), or with plain bytes
      ([lty_omemb]). *)
  Local Notation lty_omem := (lty_omem_gen mem_cell).
  Local Notation lty_omemb := (lty_omem_gen mem_bytes).

  Lemma cbytes_mem_cell {𝔄} (ty: type 𝔄) x l : cbytes ty x l -∗ mem_cell l (syn_bsize 𝔄).
  Proof.
    iIntros "Bytes". iDestruct (bytes_own_fval with "Bytes") as %[fv Hfv].
    rewrite /cbytes (bytes_own_gcont _ _ _ fv) //. iExists _, fv. iFrame. iPureIntro.
    split; [apply ty_mty_wf|]. by rewrite -(ty_bsize_eq ty).
  Qed.

  Lemma ptr_cell_mem_bytes l l' : ptr_cell l l' -∗ mem_bytes l PTR_SIZE.
  Proof.
    iIntros "(%bs & Hbs & %Hbs)". iExists bs. iFrame. iPureIntro. by eapply ptr_bytes_length.
  Qed.

  Lemma ptr_cell_pad_cell l l' : ptr_cell l l' -∗ pad_cell l PTR_SIZE.
  Proof.
    iIntros "(%bs & Hbs & %Hbs)". iExists bs. iFrame. iPureIntro. by eapply ptr_bytes_length.
  Qed.

  Lemma ptr_cell_mem_cell l l' : ptr_cell l l' -∗ mem_cell l PTR_SIZE.
  Proof. iIntros "Pt". iApply pad_cell_mem_cell. by iApply ptr_cell_pad_cell. Qed.

  Lemma fields_owned_omem {𝔄l} (lts: hlist lty 𝔄l) m offs rs d g tid l :
    HForall (λ 𝔄 lt, ∀ m r d g l, ltype_own (Owned m) lt r d g tid l ⊢ lty_omem m lt l) lts →
    fields_node offs (hmap (λ _ lt, ltype_own_cp false lt (Owned m)) lts)
      (hcmap (λ _ lt, lty_pat lt) lts) rs d g tid l ⊢ fields_omem mem_cell m l offs lts.
  Proof.
    intros Hall. induction Hall as [|𝔅 𝔅l lt lts Hlt _ IH] in offs, rs |- *; [by iIntros|].
    destruct offs as [|o offs]; [by iIntros "[]"|]. iIntros "[F1 F2]".
    iSplitL "F1"; [by iApply Hlt|by iApply IH].
  Qed.

  (** The memory of any place. *)
  Lemma ltype_owned_omem {𝔄} (lt: lty 𝔄) m r d g tid l :
    ltype_own (Owned m) lt r d g tid l ⊢ lty_omem m lt l.
  Proof.
    revert m r d g l.
    induction 𝔄, lt as [𝔄 ty|𝔄 ty α|𝔄 lt κ' IH|𝔄 n lt IH|𝔄l Lay lts IH|𝔄 ty α|
      𝔄l tyl i lt IH|𝔄 lt κ' IH|𝔄 ty|𝔄 lt κ' IH|𝔄 ty] using lty_ind'; intros m r d g l;
      [..|rewrite /ltype_own /= /leaf_owned_s /leaf_owned;
        destruct r as [lr|]; [|by iIntros "[[] _]"]; iIntros "[(%x & _ & Pt & _) _]";
        rewrite cbytes_at_loc; by iApply ptr_cell_mem_cell
       |rewrite /ltype_own /= /res_leaf; destruct r as [lr|]; [|by iIntros "[]"];
        iIntros "(%x & _ & Pt & _)"; by iApply cbytes_mem_cell
       |rewrite /ltype_own /= /res_node; destruct r as [|[[l' r'] ξi]]; [by iIntros "[]"|];
        iIntros "[Pt _]"; by iApply ptr_cell_mem_cell
       |rewrite /ltype_own /= /moved_leaf; destruct r as [lr|]; [|by iIntros "[]"];
        iIntros "Pt"; iApply pad_cell_mem_cell; by rewrite /lty_size -(ty_bsize_eq ty)];
      try by (rewrite /ltype_own /=; iIntros).
    - rewrite /ltype_own /= /leaf_owned_s /leaf_owned.
      destruct r as [lr|]; [|by iIntros "[]"]. iIntros "(%x & _ & Pt & _)".
      by iApply cbytes_mem_cell.
    - rewrite /ltype_own /= /uniq_node. destruct r as [|[[l' r'] ξi]]; [by iIntros "[]"|].
      iIntros "[Pt _]". by iApply ptr_cell_mem_cell.
    - rewrite /ltype_own /= /own_node. destruct r as [|[l' r']]; [by iIntros "[]"|].
      iIntros "(Pt & _ & Fr & O)". iExists l'. iFrame "Pt".
      destruct (own_freeb n lt); [|done]. iFrame "Fr". by iApply IH.
    - rewrite lty_omem_struct /ltype_own /= /struct_node. destruct r as [|rs]; [by iIntros "[]"|].
      iIntros "[F $]". by iApply (fields_owned_omem with "F").
    - rewrite /ltype_own /=. destruct r as [|s]; [by iIntros "[]"|]. rewrite /sum_node.
      case_match; [|by iIntros "[]"]. iIntros "(Tag & O & Pad)".
      iFrame "Tag Pad". by iApply IH.
  Qed.
End lty_mem.

Notation lty_omem := (lty_omem_gen mem_cell).
Notation lty_omemb := (lty_omem_gen mem_bytes).

Definition lty_resolve `{!typeG Σ} {𝔄} (E: elctx) (L: llctx) (lt: lty 𝔄)
    (Φ: ~~𝔄 → proph_asn → Prop) : Prop :=
  ∀ G F m x ζm q d g tid l, Timeless G → ↑Nllft ∪ ↑prophN ∪ ↑uniqN ∪ ↑gmbN ⊆ F →
    llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ time_ctx -∗ elctx_interp E -∗
    (G &&{↑NllftG}&&> llctx_interp L) -∗ G -∗
    ltype_own (Owned m) lt (lty_rfn lt x ζm q) d g tid l ={F}=∗
      lty_omem m lt l ∗ |={F}▷=>^(m + d*(g+1)) |={F}=> ⟨π, Φ x π⟩ ∗ G.

Section lty_resolve.
  Context `{!typeG Σ}.

  Lemma lty_resolve_impl {𝔄} E L (lt: lty 𝔄) (Φ Φ': ~~𝔄 → proph_asn → Prop) :
    lty_resolve E L lt Φ → (∀ x π, Φ x π → Φ' x π) → lty_resolve E L lt Φ'.
  Proof.
    iIntros (Rslv Imp G F m x ζm q d g tid l ??) "LFT PROPH UNIQ TIME E L G Own".
    iMod (Rslv with "LFT PROPH UNIQ TIME E L G Own") as "[$ Upd]"; [done..|].
    iModIntro. iApply (step_fupdN_wand with "Upd"). iIntros ">[Obs $] !>".
    iApply (proph_obs_impl with "Obs")=> ?. apply Imp.
  Qed.

  (** Any place can be forgotten. *)
  Lemma lty_resolve_just {𝔄} E L (lt: lty 𝔄) : lty_resolve E L lt (λ _ _, True).
  Proof.
    iIntros (G F m x ζm q d g tid l ??) "_ _ _ _ _ _ G Own".
    iDestruct (ltype_owned_omem with "Own") as "$". iModIntro.
    iApply step_fupdN_full_intro. iFrame "G". by iApply proph_obs_true.
  Qed.

  Lemma lty_resolve_ofty {𝔄} E L (ty: type 𝔄) Φ :
    resolve E L ty Φ → lty_resolve E L (OfTy ty) Φ.
  Proof.
    iIntros (Rslv G F m x ζm q d g tid l ??) "LFT PROPH UNIQ TIME E L G Own".
    rewrite /ltype_own /= /leaf_owned_s /leaf_owned /=.
    iDestruct "Own" as (x' Hx) "[Pt Gho]". simpl in Hx. subst x'.
    iSplitL "Pt". { iModIntro. by iApply cbytes_mem_cell. }
    iModIntro. iApply step_fupdN_add.
    iApply (step_fupdN_wand with "[Gho]"); [by iApply step_fupdN_intro|].
    iIntros "Gho". iApply fupd_step_fupdN_front.
    iApply (Rslv with "LFT PROPH UNIQ TIME E L G Gho"); done.
  Qed.

  (** The resolution of the fields of a struct, with a property for each field. *)
  Fixpoint fields_rslv_pred {𝔄l} :
      plist (λ 𝔄, ~~𝔄 → proph_asn → Prop) 𝔄l → plist (~~) 𝔄l → proph_asn → Prop :=
    match 𝔄l with
    | [] => λ _ _ _, True
    | _ :: _ => λ '(Φ -:: Φl) '(x -:: xl) π, Φ x π ∧ fields_rslv_pred Φl xl π
    end.

  Local Lemma fields_resolve {𝔄l} E L (lts: hlist lty 𝔄l) Φl G F m offs xs ζm q j d g tid l :
    HForall_1 (λ _ lt Φ, lty_resolve E L lt Φ) lts Φl → Timeless G →
    ↑Nllft ∪ ↑prophN ∪ ↑uniqN ∪ ↑gmbN ⊆ F →
    ⊢ llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ time_ctx -∗ elctx_interp E -∗
      (G &&{↑NllftG}&&> llctx_interp L) -∗ G -∗
      fields_node offs (hmap (λ _ lt, ltype_own_cp false lt (Owned m)) lts)
        (hcmap (λ _ lt, lty_pat lt) lts) (fields_rfn ζm q lts j xs) d g tid l ={F}=∗
      fields_omem mem_cell m l offs lts ∗
        |={F}▷=>^(m + d*(g+1)) |={F}=> ⟨π, fields_rslv_pred Φl xs π⟩ ∗ G.
  Proof.
    intros Hall. induction Hall as [|𝔅 𝔅l lt Φ lts Φl Hlt _ IH] in offs, xs, j, G |- *;
      intros ??.
    - iIntros "_ _ _ _ _ _ G _ !>". iSplit; [done|]. iApply step_fupdN_full_intro.
      iFrame "G". by iApply proph_obs_true.
    - destruct offs as [|o offs]; [by iIntros "_ _ _ _ _ _ _ []"|]. destruct xs as [x xs].
      iIntros "#LFT #PROPH #UNIQ #TIME #E #L G [Own1 Own2]".
      iMod (fractional.frac_split_guard_in_half with "G L") as (γ) "[H1 [H2 [#Gh #Back]]]";
        [solve_ndisj|].
      iMod (Hlt with "LFT PROPH UNIQ TIME E Gh H1 Own1") as "[M1 Upd1]"; [done..|].
      iMod (IH with "LFT PROPH UNIQ TIME E Gh H2 Own2") as "[M2 Upd2]"; [done..|].
      iSplitL "M1 M2". { iModIntro. iFrame. }
      iCombine "Upd1 Upd2" as "Upd". iModIntro.
      iApply (step_fupdN_wand with "Upd"). iIntros "[>[Obs1 H1] >[Obs2 H2]]".
      iMod (fupd_mask_mono with "(Back H1 H2)") as "$"; [solve_ndisj|].
      iModIntro. by iCombine "Obs1 Obs2" as "?".
  Qed.

  Lemma lty_resolve_struct {𝔄l} E L Lay (lts: hlist lty 𝔄l) Φl :
    HForall_1 (λ _ lt Φ, lty_resolve E L lt Φ) lts Φl →
    lty_resolve E L (StructLty Lay lts) (λ x π, fields_rslv_pred Φl x π).
  Proof.
    iIntros (Rslv G F m x ζm q d g tid l ??) "LFT PROPH UNIQ TIME E L G Own".
    rewrite lty_rfn_struct lty_omem_struct /ltype_own /=. iDestruct "Own" as "[Own $]".
    iApply (fields_resolve with "LFT PROPH UNIQ TIME E L G Own"); done.
  Qed.

  Lemma lty_resolve_own {𝔄} E L n (lt: lty 𝔄) Φ :
    lty_resolve E L lt Φ → lty_resolve E L (OwnPtrLty n lt) (λ x π, Φ x.2 π).
  Proof.
    iIntros (Rslv G F m x ζm q d g tid l ??) "LFT PROPH UNIQ TIME E L G Own".
    rewrite /ltype_own /=. destruct x as [l' x]. iDestruct "Own" as "(Pt & %Hd & Fr & Own)".
    iMod (Rslv with "LFT PROPH UNIQ TIME E L G Own") as "[M Upd]"; [done..|].
    iSplitL "Pt Fr M".
    { iModIntro. iExists l'. iFrame "Pt". destruct (own_freeb n lt); [|done]. iFrame. }
    iModIntro. iApply (step_fupdN_nmono with "Upd"). destruct d; [done|]. simpl. nia.
  Qed.

  Lemma lty_resolve_sum {𝔄l} E L (tyl: typel 𝔄l) i (lt: lty (𝔄l !!ₗ i)) Φ :
    lty_resolve E L lt Φ →
    lty_resolve E L (SumLty tyl i lt) (λ x π, ∀ y, psum_proj i x = Some y → Φ y π).
  Proof.
    iIntros (Rslv G F m x ζm q d g tid l ??) "LFT PROPH UNIQ TIME E L G Own".
    rewrite lty_rfn_sum. destruct (psum_proj i x) as [y|] eqn:Hy; last first.
    { by rewrite /ltype_own /= /prfn_dummy /sum_node /=. }
    rewrite /ltype_own ltype_own_cp_sum_owned sum_node_sum.
    iDestruct "Own" as "(Tag & Own & Pad)".
    iMod (Rslv with "LFT PROPH UNIQ TIME E L G Own") as "[M Upd]"; [done..|].
    iSplitL "Tag M Pad".
    { iModIntro. iFrame. }
    iModIntro. iApply (step_fupdN_wand with "Upd"). iIntros ">[Obs $] !>".
    iApply (proph_obs_impl with "Obs")=> π ? y' [= <-]. done.
  Qed.
End lty_resolve.

(** * Freeing the pointees of the owned pointers of a place *)

Section drop_boxes.
  Context `{!typeG Σ}.

  (** The program that frees the pointees of the owned pointers of a place (whose
      memory starts at the address computed by [e]), innermost first. The address of
      a pointee is computed again from [e] for each access (as [pctx_expr]): the memory
      of the place is only freed afterwards. *)
  Fixpoint drop_boxes {𝔄} (lt: lty 𝔄) (e: expr) : expr :=
    match lt with
    | OwnPtrLty n lt' =>
        if own_freeb n lt' then
          (drop_boxes lt' (Load Na1Ord MPtr e);;
           new_delete.delete [ #(lty_size lt'); (Load Na1Ord MPtr e)])%E
        else #☠%E
    | @StructLty _ _ 𝔄l Lay lts =>
        (fix go {𝔅l} (j: nat) (lts: hlist lty 𝔅l) {struct lts} : expr :=
          match lts with
          | +[] => #☠%E
          | lt +:: lts' => (drop_boxes lt (e +ₗ #(struct_off Lay 𝔄l j));; go (S j) lts')%E
          end) _ 0%nat lts
    | @SumLty _ _ 𝔄l _ _ lt' => drop_boxes lt' (e +ₗ #(tag_size 𝔄l))%E
    | _ => #☠%E
    end.

  (** The program freeing the pointees of the fields [lts] of a struct of layout [Lay] and
      fields [𝔄l] (at the address computed by [e]), the first of them being field [j]. *)
  Definition fields_drop (e: expr) (Lay: struct_layout) (𝔄l: syn_typel) :
      ∀ {𝔅l}, nat → hlist lty 𝔅l → expr :=
    fix go {𝔅l} (j: nat) (lts: hlist lty 𝔅l) {struct lts} : expr :=
      match lts with
      | +[] => #☠%E
      | lt +:: lts' => (drop_boxes lt (e +ₗ #(struct_off Lay 𝔄l j));; go (S j) lts')%E
      end.

  Lemma fields_drop_cons {𝔄 𝔅l} e Lay 𝔄l j (lt: lty 𝔄) (lts: hlist lty 𝔅l) :
    fields_drop e Lay 𝔄l j (lt +:: lts) =
      (drop_boxes lt (e +ₗ #(struct_off Lay 𝔄l j));; fields_drop e Lay 𝔄l (S j) lts)%E.
  Proof. done. Qed.

  Lemma drop_boxes_struct {𝔄l} Lay (lts: hlist lty 𝔄l) e :
    drop_boxes (StructLty Lay lts) e = fields_drop e Lay 𝔄l 0 lts.
  Proof. done. Qed.

  Local Lemma fields_drop_closed_aux e Lay 𝔄l {𝔅l} (lts: hlist lty 𝔅l) j :
    HForall (λ _ lt, ∀ e, Closed [] e → Closed [] (drop_boxes lt e)) lts → Closed [] e →
    Closed [] (fields_drop e Lay 𝔄l j lts).
  Proof.
    intros Hall ?. induction Hall as [|𝔅 𝔅l lt lts Hlt _ IH] in j |- *; [simpl; apply _|].
    rewrite fields_drop_cons.
    have ?: Closed [] (drop_boxes lt (e +ₗ #(struct_off Lay 𝔄l j))%E) by apply Hlt; apply _.
    have ?: Closed [] (fields_drop e Lay 𝔄l (S j) lts) by apply IH.
    apply _.
  Qed.

  Global Instance drop_boxes_closed {𝔄} (lt: lty 𝔄) e :
    Closed [] e → Closed [] (drop_boxes lt e).
  Proof.
    revert e.
    induction 𝔄, lt as [| | | 𝔄 n lt IH|𝔄l Lay lts IH| |𝔄l tyl i lt IH| | | |] using lty_ind';
      intros e ?; simpl; try done.
    - destruct (own_freeb n lt); [|done].
      have ?: Closed [] (drop_boxes lt (Load Na1Ord MPtr e)%E).
      { apply IH. apply _. }
      apply _.
    - rewrite -/(fields_drop e Lay 𝔄l 0 lts). by apply fields_drop_closed_aux.
    - apply IH. apply _.
  Qed.

  Global Instance fields_drop_closed {𝔅l} e Lay 𝔄l j (lts: hlist lty 𝔅l) :
    Closed [] e → Closed [] (fields_drop e Lay 𝔄l j lts).
  Proof.
    intros ?. induction lts as [|𝔅 𝔅l lt lts IH] in j |- *; [simpl; apply _|].
    rewrite fields_drop_cons.
    have ?: Closed [] (fields_drop e Lay 𝔄l (S j) lts) by apply IH.
    have ?: Closed [] (drop_boxes lt (e +ₗ #(struct_off Lay 𝔄l j))%E)
      by apply drop_boxes_closed; apply _.
    apply _.
  Qed.

  Lemma wp_delete_bytes bs (n: Z) l E :
    ↑naN ⊆ E → n = length bs →
    {{{ l ↦b bs ∗ (†l…(length bs) ∨ ⌜n = 0⌝) }}} new_delete.delete [ #n; #l] @ E
    {{{ RET #☠; True }}}.
  Proof.
    iIntros (?? Φ) "(H↦ & H†) HΦ". wp_lam. wp_op. case_bool_decide.
    - wp_if. by iApply "HΦ".
    - wp_if. iDestruct "H†" as "[H†|%]"; [|lia].
      iApply (wp_free_bytes with "[$H↦ $H†]"); [done|done|]. iIntros "!> _". by iApply "HΦ".
  Qed.

  Lemma mem_cell_app (l: loc) n1 n2 :
    mem_cell l n1 ∗ mem_cell (l +ₗ n1) n2 ⊢ mem_cell l (n1 + n2).
  Proof.
    iIntros "[(%m1 & %fv1 & [%Hw1 %H1] & C1) (%m2 & %fv2 & [%Hw2 %H2] & C2)]".
    iExists (seq_tuple [m1; m2]), (FVTuple [fv1; fv2]). iSplit.
    { iPureIntro. split; [apply seq_tuple_wf; by repeat constructor|].
      rewrite mty_size_seq_tuple !seq_size_cons seq_size_nil. lia. }
    rewrite !gcont_seq_tuple_cons gcont_seq_tuple_nil right_id H1. iFrame.
  Qed.

  Lemma mem_bytes_app (l: loc) n1 n2 :
    mem_bytes l n1 ∗ mem_bytes (l +ₗ n1) n2 ⊢ mem_bytes l (n1 + n2).
  Proof.
    iIntros "[(%bs1 & B1 & %H1) (%bs2 & B2 & %H2)]". iExists (bs1 ++ bs2).
    rewrite heap_mapsto_bytes_app H1. iFrame. iPureIntro. rewrite length_app. lia.
  Qed.

  (** Dropping the cells of the memory of a place, with the registry opened. *)
  Lemma mem_cell_forget Reg l n :
    greg_open Reg -∗ mem_cell l n ={lazyE}=∗ greg_open Reg ∗ mem_bytes l n.
  Proof.
    iIntros "O (%m & %fv & [%Hw <-] & C)".
    iMod (gcont_forget_open with "O C") as "[$ (%bs & Hbs & %Hl)]"; [done|].
    iModIntro. iExists bs. by iFrame.
  Qed.

  Local Lemma fields_omem_forget Reg {𝔅l} m (lts: hlist lty 𝔅l) offs l :
    HForall (λ 𝔄 lt, ∀ m l,
      greg_open Reg -∗ lty_omem m lt l ={lazyE}=∗ greg_open Reg ∗ lty_omemb m lt l) lts →
    greg_open Reg -∗ fields_omem mem_cell m l offs lts ={lazyE}=∗
      greg_open Reg ∗ fields_omem mem_bytes m l offs lts.
  Proof.
    intros Hall. induction Hall as [|𝔄 𝔅l lt lts Hlt _ IH] in offs |- *; iIntros "O M";
      [by iFrame|].
    destruct offs as [|o offs]; [done|]. iDestruct "M" as "[M1 M2]".
    iMod (Hlt with "O M1") as "[O $]". by iApply (IH with "O M2").
  Qed.

  Lemma lty_omem_forget Reg {𝔄} m (lt: lty 𝔄) l :
    greg_open Reg -∗ lty_omem m lt l ={lazyE}=∗ greg_open Reg ∗ lty_omemb m lt l.
  Proof.
    revert m l.
    induction 𝔄, lt as [𝔄 ty| |𝔄 lt κ' IH|𝔄 n lt IH|𝔄l Lay lts IH| |𝔄l tyl i lt IH|𝔄 lt κ' IH|𝔄 ty|𝔄 lt κ' IH|𝔄 ty]
      using lty_ind'; intros m l; rewrite ?lty_omem_struct; iIntros "O M"; simpl;
      try (iModIntro; by iFrame).
    all: try by iApply (mem_cell_forget with "O M").
    - iDestruct "M" as (l') "[Pt M]". destruct (own_freeb n lt); [|iModIntro; iFrame; by iExists l'].
      iDestruct "M" as "[Fr M]". iMod (IH with "O M") as "[$ M]". iModIntro.
      iExists l'. iFrame.
    - iDestruct "M" as "[M $]". by iApply (fields_omem_forget with "O M").
    - iDestruct "M" as "(Tag & M & Pad)". iFrame "Tag Pad". by iApply (IH with "O M").
  Qed.

  Lemma lty_omem_forget_gc E {𝔄} m (lt: lty 𝔄) l :
    lazyE ∪ ↑gcellsN ⊆ E →
    gcells_ctx -∗ £ 1 -∗ lty_omem m lt l ={E}=∗ lty_omemb m lt l.
  Proof.
    iIntros (?) "#GC Lc M". iApply (gcells_open_with with "GC Lc [] M"); [done|].
    iIntros (Reg) "O M". by iApply (lty_omem_forget with "O M").
  Qed.

  Lemma mem_bytes_fields l (fs: list (nat * mty)) :
    ([∗ list] f ∈ fs, mem_bytes (l +ₗ Z.of_nat f.1) (mty_size f.2)) ⊢
    ∃ bss, ⌜∀ j f bs, fs !! j = Some f → bss !! j = Some bs → length bs = mty_size f.2⌝ ∗
      [∗ list] f; bs ∈ fs; bss, (l +ₗ Z.of_nat f.1) ↦b bs.
  Proof.
    induction fs as [|f fs IH]; simpl.
    - iIntros "_". iExists []. iSplit; [|done]. iPureIntro. intros ???. by rewrite lookup_nil.
    - iIntros "[(%bs & B & %Hl) Fs]". iDestruct (IH with "Fs") as (bss) "[%Hls Fs]".
      iExists (bs :: bss). iFrame. iPureIntro. intros [|j] f' bs'; simpl; [|apply Hls].
      by intros [= <-] [= <-].
  Qed.

  (** The memory of the fields of a struct and its padding make the memory of the
      struct. *)
  Lemma mem_bytes_struct l Lay 𝔄l :
    ([∗ list] f ∈ struct_fields Lay 𝔄l, mem_bytes (l +ₗ Z.of_nat f.1) (mty_size f.2)) ∗
    pad_own l (struct_fields Lay 𝔄l) (struct_size Lay 𝔄l) ⊢ mem_bytes l (struct_size Lay 𝔄l).
  Proof.
    iIntros "[Fs Pad]". iDestruct (mem_bytes_fields with "Fs") as (bss) "[%Hls Fs]".
    iApply (bytes_fields_pad with "[$Fs $Pad]"); [apply struct_fields_disjoint|
      apply struct_fields_bounds|done].
  Qed.

  (** [drop_boxes lt e] frees the pointees of the owned pointers of the place (those in
      [lty_omem]) and gives back the bytes of the place itself. [e] computes the
      address of the place, using some resource [R], in at least [k] steps; the rights
      to free the pointees are under [m] laters, with [m ≤ k + 1]: the pointee of an
      owned pointer is freed after its address has been computed again, i.e. after
      [k + 1] steps. *)
  Local Lemma wp_fields_drop E {𝔅l} (lts: hlist lty 𝔅l) m k (l: loc) (e: expr) (R: iProp Σ) Ψ
      Lay 𝔄l j :
    ↑naN ⊆ E → j + length 𝔅l ≤ length 𝔄l →
    HForall (λ 𝔄 lt, ∀ m k (l: loc) (e: expr) (R: iProp Σ) Φ,
      lty_freeb lt = true → Closed [] e → m ≤ k + 1 →
      (⊢ ∀ Ψ (P: iProp Σ), R -∗ ▷^k P -∗ (R -∗ P -∗ Ψ #l) -∗ WP e @ E {{ Ψ }}) →
      R -∗ lty_omemb m lt l -∗
      (R -∗ mem_bytes l (lty_size lt) -∗ Φ #☠) -∗
      WP drop_boxes lt e @ E {{ Φ }}) lts →
    foldr andb true (hcmap (λ _ lt, lty_freeb lt) lts) = true → Closed [] e → m ≤ k + 1 →
    (⊢ ∀ Ψ (P: iProp Σ), R -∗ ▷^k P -∗ (R -∗ P -∗ Ψ #l) -∗ WP e @ E {{ Ψ }}) →
    R -∗ fields_omem mem_bytes m l (drop j (struct_offs Lay 𝔄l)) lts -∗
    (R -∗ ([∗ list] f ∈ zip (drop j (struct_offs Lay 𝔄l)) (syn_mty <$> 𝔅l),
        mem_bytes (l +ₗ Z.of_nat f.1) (mty_size f.2)) -∗ Ψ #☠) -∗
    WP fields_drop e Lay 𝔄l j lts @ E {{ Ψ }}.
  Proof.
    intros ? Hj Hall. induction Hall as [|𝔄 𝔅l lt lts Hlt _ IH] in j, Hj, Ψ |- *;
      intros Hf ? Hm Hev; iIntros "R M HΨ".
    - rewrite /fields_drop. iApply wp_value. iApply ("HΨ" with "R").
      by destruct (drop j (struct_offs Lay 𝔄l)).
    - rewrite (drop_S _ (struct_off Lay 𝔄l j)); last first.
      { apply struct_off_lookup. simpl in Hj. lia. }
      set o := struct_off Lay 𝔄l j. simpl in Hf.
      apply andb_true_iff in Hf as [Hf1 Hf2]. iDestruct "M" as "[M1 M2]".
      rewrite fields_drop_cons.
      have Hev': ⊢ ∀ Ψ (P: iProp Σ), R -∗ ▷^(k + 1) P -∗ (R -∗ P -∗ Ψ #(l +ₗ o)) -∗
        WP (e +ₗ #o)%E @ E {{ Ψ }}.
      { iIntros (Ψ' P) "R P HΨ". wp_bind e.
        iApply (Hev $! _ (▷ P)%I with "R [P]"); [by rewrite bi.laterN_add|]. iIntros "R P".
        wp_op. by iApply ("HΨ" with "R P"). }
      wp_bind (drop_boxes _ _).
      iApply (Hlt m (k + 1) (l +ₗ o) (e +ₗ #o)%E R _ Hf1 _ ltac:(lia) Hev' with "R M1 [M2 HΨ]").
      iIntros "R B1". wp_seq.
      iApply (IH with "R M2"); [simpl in Hj; lia|done|done|done|]. iIntros "R Bs".
      iApply ("HΨ" with "R"). simpl. iSplitL "B1"; [done|done].
  Qed.

  Lemma wp_drop_boxes {𝔄} (lt: lty 𝔄) m k (l: loc) (e: expr) (R: iProp Σ) E Φ :
    ↑naN ⊆ E → lty_freeb lt = true → Closed [] e → m ≤ k + 1 →
    (⊢ ∀ Ψ (P: iProp Σ), R -∗ ▷^k P -∗ (R -∗ P -∗ Ψ #l) -∗ WP e @ E {{ Ψ }}) →
    R -∗ lty_omemb m lt l -∗
    (R -∗ mem_bytes l (lty_size lt) -∗ Φ #☠) -∗
    WP drop_boxes lt e @ E {{ Φ }}.
  Proof.
    intros ?. revert m k l e R Φ.
    induction 𝔄, lt as [𝔄 ty| |𝔄 lt κ' IH|𝔄 n lt IH|𝔄l Lay lts IH| |𝔄l tyl i lt IH|𝔄 lt κ' IH|𝔄 ty|𝔄 lt κ' IH|𝔄 ty]
      using lty_ind'; intros m k l e R Φ Hf ? Hm Hev; simpl in Hf; try done;
      rewrite ?lty_omem_struct ?drop_boxes_struct; cbn [drop_boxes];
      iIntros "R M HΦ".
    6: { iApply wp_value. by iApply ("HΦ" with "R M"). }
    6: { iApply wp_value. by iApply ("HΦ" with "R M"). }
    6: { iApply wp_value. by iApply ("HΦ" with "R M"). }
    6: { iApply wp_value. by iApply ("HΦ" with "R M"). }
    - iApply wp_value. by iApply ("HΦ" with "R M").
    - iApply wp_value. by iApply ("HΦ" with "R M").
    - simpl. iDestruct "M" as (l') "[Pt M]". destruct (own_freeb n lt) eqn:Hfb; last first.
      { iApply wp_value. iApply ("HΦ" with "R"). by iApply ptr_cell_mem_bytes. }
      apply andb_true_iff in Hfb as [Hf' Hn%bool_decide_eq_true].
      have Hev': ⊢ ∀ Ψ (P: iProp Σ), (R ∗ ptr_cell l l') -∗
        ▷^(k + 1) P -∗ ((R ∗ ptr_cell l l') -∗ P -∗ Ψ #l') -∗
        WP (Load Na1Ord MPtr e)%E @ E {{ Ψ }}.
      { iIntros (Ψ P) "[R Pt] P HΨ". wp_bind e.
        iApply (Hev $! _ (▷ P)%I with "R [P]"); [by rewrite bi.laterN_add|]. iIntros "R P".
        iDestruct "Pt" as (bs) "[Hbs %Hbs]". wp_bind (Load _ _ _).
        iApply (wp_load_na with "Hbs"); [exact Hbs|]. iIntros "!> Hbs".
        iApply ("HΨ" with "[R Hbs] P"). by iFrame. }
      iDestruct "M" as "[Fr M]".
      wp_bind (drop_boxes lt (Load Na1Ord MPtr e)%E).
      iApply (IH (m + 1) (k + 1) l' (Load Na1Ord MPtr e)%E (R ∗ ptr_cell l l')%I
        _ Hf' _ ltac:(lia) Hev' with "[$R $Pt] M").
      iIntros "[R Pt] (%bs & Pt' & %Hl)". wp_seq.
      wp_bind (Load _ _ _). iApply (Hev' with "[$R $Pt] [Fr]").
      { iApply (bi.laterN_le with "Fr"). lia. }
      iIntros "[R Pt] Fr". iEval (rewrite -Hn freeable_sz_full) in "Fr".
      iApply (wp_delete_bytes bs with "[Pt' Fr]"); [done|by rewrite Hl -Hn|..].
      { iFrame "Pt'". rewrite Hl -Hn. iDestruct "Fr" as "[$|%]"; by iRight. }
      iIntros "!> _". iApply ("HΦ" with "R"). by iApply ptr_cell_mem_bytes.
    - iDestruct "M" as "[M Pad]".
      iApply (wp_fields_drop _ _ _ _ _ _ _ _ Lay 𝔄l 0 with "R M [Pad HΦ]"); [done|lia|done..|].
      iIntros "R Bs". iApply ("HΦ" with "R"). iApply mem_bytes_struct. iFrame.
    - have Hsz: lty_size (SumLty tyl i lt) = (tag_size 𝔄l + (lty_size lt + (sum_max 𝔄l - lty_size lt)))%nat.
      { rewrite /lty_size syn_bsize_sum /tag_size. have := sum_max_ge 𝔄l i. lia. }
      rewrite Hsz. cbn [lty_omem_gen].
      iDestruct "M" as "(Tag & M & Pad)".
      have Hev2: ⊢ ∀ Ψ (P: iProp Σ), R -∗ ▷^(k + 1) P -∗ (R -∗ P -∗ Ψ #(l +ₗ tag_size 𝔄l)) -∗
        WP (e +ₗ #(tag_size 𝔄l))%E @ E {{ Ψ }}.
      { iIntros (Ψ P) "R P HΨ". wp_bind e.
        iApply (Hev $! _ (▷ P)%I with "R [P]"); [by rewrite bi.laterN_add|]. iIntros "R P".
        wp_op. by iApply ("HΨ" with "R P"). }
      iApply (IH m (k + 1) (l +ₗ tag_size 𝔄l) (e +ₗ #(tag_size 𝔄l))%E R _ Hf _ ltac:(lia) Hev2 with "R M [-]").
      iIntros "R Pt". iApply ("HΦ" with "R [-]").
      iApply mem_bytes_app.
      iSplitL "Tag". { iDestruct "Tag" as (bt) "[Bt %Ht]".
        iExists bt. iFrame. iPureIntro. by apply decode_value_length in Ht. }
      iApply mem_bytes_app. iFrame.
  Qed.
End drop_boxes.

(** * Resolving and dropping places rooted at an owned location *)

Section oplace.
  Context `{!typeG Σ}.

  Lemma oplace_resolve_steps {𝔄} E L n (lt: lty 𝔄) Φ x tid v :
    lty_resolve E L lt Φ →
    oplace_own n lt x tid v -∗ ∃ D, ⧖D ∗ ∀ G F, ⌜Timeless G⌝ -∗
      ⌜↑Nllft ∪ ↑prophN ∪ ↑uniqN ∪ ↑gmbN ⊆ F⌝ -∗
      llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ time_ctx -∗ elctx_interp E -∗
      (G &&{↑NllftG}&&> llctx_interp L) -∗ G ={F}=∗
        |={F}▷=>^(D*(D+1)) |={F}=> ⟨π, Φ x.1.2 π⟩ ∗ G.
  Proof.
    iIntros (Rslv) "Own". destruct x as [[l x₀] ζm].
    iDestruct "Own" as (D d g) "(⧖ & _ & _ & %Hle & _ & Own)".
    iExists D. iFrame "⧖". iIntros (G F ??) "LFT PROPH UNIQ TIME E L G".
    iMod (Rslv with "LFT PROPH UNIQ TIME E L G Own") as "[_ Upd]"; [done..|].
    iModIntro. iApply (step_fupdN_nmono with "Upd"). nia.
  Qed.

  (** Resolving (and forgetting) an owned place, e.g. at the end of a function: the
      unblocked leaves are resolved, the memory is leaked. *)
  Lemma resolve_tctx_cons_oplace {𝔄 𝔅l} E L p n (lt: lty 𝔄) Φ (T: tctx 𝔅l) Ψ :
    lty_resolve E L lt Φ → resolve_tctx E L T Ψ →
    resolve_tctx E L (p ◁ₗown{n} lt +:: T) (λ '(x -:: bl) π φ, Φ x.1.2 π → Ψ bl π φ).
  Proof.
    iIntros (Rslv Rslv' G F tid [x xl] ? HF).
    iIntros "#LFT #PROPH #UNIQ #TIME #E #L G /=[(%v & _ & Own) T]".
    iMod (fractional.frac_split_guard_in_half NllftG with "G L")
      as (γ) "[F1 [F2 [#guards #back]]]"; [solve_ndisj|].
    iDestruct (oplace_resolve_steps with "Own") as (D) "[⧖ ToObs]"; [done|].
    iMod ("ToObs" $! _ F with "[%] [//] LFT PROPH UNIQ TIME E guards F1") as "ToObs";
      [apply _|].
    iMod (Rslv' with "LFT PROPH UNIQ TIME E guards F2 T") as (?) "[⧖' ToObs']"; [done|].
    iCombine "⧖ ⧖'" as "⧖". iCombine "ToObs ToObs'" as "ToObs".
    iModIntro. iExists _. iFrame "⧖". rewrite lemma_max_mul.
    iApply (step_fupdN_wand with "ToObs"). iIntros "[>[Obs F1] >[Obs' F2]]".
    iMod (fupd_mask_mono with "(back F1 F2)") as "$"; [solve_ndisj|].
    iCombine "Obs Obs'" as "Obs". iModIntro.
    iApply (proph_obs_impl with "Obs")=>/= ?[? Imp]? Imp'. by apply Imp, Imp'.
  Qed.

  (** Dropping an owned place: the unblocked leaves are resolved, the pointees of the
      owned pointers of the place are freed ([drop_boxes], recursively, if their memory
      is owned, [own_freeb]), and the memory of the place is freed ([Free] of its bytes).
      The pointees of owned pointers in unblocked leaves ([OfTy (own_bytes …)]) are
      leaked. No leaf of the place itself may be blocked or shared ([lty_freeb]): their
      memory is lent. *)
  Lemma type_drop_oplace_instr {𝔄} E L I p n (nz: Z) (lt: lty 𝔄) Φ :
    lty_freeb lt = true → n = lty_size lt → nz = Z.of_nat n → lty_resolve E L lt Φ →
    typed_instr E L I +[p ◁ₗown{n} lt] (drop_boxes lt p;; new_delete.delete [ #nz; p])%E
      (λ _, +[]) (λ post '-[x], λ mask π, Φ x.1.2 π → post -[] mask π).
  Proof.
    iIntros (Hf -> -> Rslv tid post mask iκs [x []])
      "#LFT #TIME #PROPH #UNIQ #E L I [(%v & %Hp & Own) _] Obs".
    destruct x as [[l x₀] ζm].
    iDestruct "Own" as (D d g) "(#⧖ & _ & -> & %Hle & Fr & Own)".
    iMod (llctx_interp_make_guarded with "L") as (γ) "[H1 [H2 [#Ghalf #Halfback]]]";
      [solve_ndisj|].
    iApply (wp_persistent_time_receipt with "TIME ⧖"); [solve_ndisj|]. iIntros "£ _".
    iDestruct (lc_weaken (1 + (advance_credits D - 1)) with "£") as "[£1 £]";
      [rewrite /advance_credits; lia|].
    iMod (Rslv _ (⊤∖↑advN) with "LFT PROPH UNIQ TIME E Ghalf H1 Own") as "[M Upd]";
      [solve_ndisj|].
    iMod (lc_step_fupdN_elim_later with "[£] Upd") as "Upd".
    { iApply (lc_weaken with "£"). rewrite /advance_credits. nia. }
    iDestruct (invctx_interp_gcells with "I") as "[#GC I]".
    iMod (lty_omem_forget_gc with "GC £1 M") as "M"; [solve_ndisj|].
    iMod "Upd" as "[Obs' H1]".
    iMod (fupd_mask_mono with "(Halfback H1 H2)") as "L"; [solve_ndisj|].
    have ?: Closed [] p by eapply eval_path_closed.
    wp_bind (drop_boxes lt p).
    have Hev: ⊢ ∀ Ψ (P: iProp Σ), True -∗ ▷^0 P -∗ (True -∗ P -∗ Ψ #l) -∗
      WP p @ ⊤∖↑advN {{ Ψ }}.
    { iIntros (Ψ P) "_ P HΨ". wp_bind p. iApply wp_wand; [by iApply wp_eval_path|].
      iIntros (?) "->". by iApply ("HΨ" with "[//] P"). }
    iApply (wp_drop_boxes lt 1 0 l p True%I (⊤∖↑advN) _ ltac:(solve_ndisj) Hf _
      ltac:(lia) Hev with "[//] M").
    iIntros "_ (%bs & Pt & %Hl)". wp_seq.
    wp_bind p. iApply wp_wand; [by iApply wp_eval_path|]. iIntros (?) "->".
    iEval (rewrite freeable_sz_full) in "Fr".
    iApply (wp_delete_bytes bs with "[Pt Fr]"); [solve_ndisj|by rewrite Hl|..].
    { iFrame "Pt". rewrite Hl. iDestruct "Fr" as "[$|%]"; by iRight. }
    iIntros "!> _". iExists -[]. iFrame "L I". iSplit; [done|].
    iCombine "Obs Obs'" as "Obs". iApply (proph_obs_impl with "Obs")=>/= ?[Imp ?]. by apply Imp.
  Qed.

  (** Giving up the contents of an owned place, which becomes uninitialized: as
      [type_drop_oplace_instr] (the unblocked leaves are resolved, e.g. moved-out leaves
      [Moved ty] and uninitialized leaves [OfTy (↯ n)] with nothing, [lty_resolve_just];
      the pointees of the unfolded owned pointers are freed), but the memory of the place
      itself is kept, as the bytes of [↯ n] (the tags of the sums of the place are
      forgotten). E.g. a box all of whose fields have been moved out becomes a box of
      [↯ n] again, which can be re-used or freed ([type_drop_oplace_instr]). *)
  Lemma type_uninit_oplace_instr {𝔄} E L I p n (lt: lty 𝔄) Φ :
    lty_freeb lt = true → n = lty_size lt → lty_resolve E L lt Φ →
    typed_instr E L I +[p ◁ₗown{n} lt] (drop_boxes lt p;; Skip)%E
      (λ _, +[p ◁ₗown{n} OfTy (↯ n)])
      (λ post '-[x], λ mask π, Φ x.1.2 π → post -[((x.1.1, ()), [])] mask π).
  Proof.
    iIntros (Hf -> Rslv tid post mask iκs [x []])
      "#LFT #TIME #PROPH #UNIQ #E L I [(%v & %Hp & Own) _] Obs".
    destruct x as [[l x₀] ζm].
    iDestruct "Own" as (D d g) "(#⧖ & _ & -> & %Hle & Fr & Own)".
    iMod (llctx_interp_make_guarded with "L") as (γ) "[H1 [H2 [#Ghalf #Halfback]]]";
      [solve_ndisj|].
    iApply (wp_persistent_time_receipt with "TIME ⧖"); [solve_ndisj|]. iIntros "£ _".
    iDestruct (lc_weaken (1 + (advance_credits D - 1)) with "£") as "[£1 £]";
      [rewrite /advance_credits; lia|].
    iMod (Rslv _ (⊤∖↑advN) with "LFT PROPH UNIQ TIME E Ghalf H1 Own") as "[M Upd]";
      [solve_ndisj|].
    iMod (lc_step_fupdN_elim_later with "[£] Upd") as "Upd".
    { iApply (lc_weaken with "£"). rewrite /advance_credits. nia. }
    iDestruct (invctx_interp_gcells with "I") as "[#GC I]".
    iMod (lty_omem_forget_gc with "GC £1 M") as "M"; [solve_ndisj|].
    iMod "Upd" as "[Obs' H1]".
    iMod (fupd_mask_mono with "(Halfback H1 H2)") as "L"; [solve_ndisj|].
    have ?: Closed [] p by eapply eval_path_closed.
    wp_bind (drop_boxes lt p).
    have Hev: ⊢ ∀ Ψ (P: iProp Σ), True -∗ ▷^0 P -∗ (True -∗ P -∗ Ψ #l) -∗
      WP p @ ⊤∖↑advN {{ Ψ }}.
    { iIntros (Ψ P) "_ P HΨ". wp_bind p. iApply wp_wand; [by iApply wp_eval_path|].
      iIntros (?) "->". by iApply ("HΨ" with "[//] P"). }
    iApply (wp_drop_boxes lt 1 0 l p True%I (⊤∖↑advN) _ ltac:(solve_ndisj) Hf _
      ltac:(lia) Hev with "[//] M").
    iIntros "_ (%bs & Pt & %Hl)". iMod cumulative_time_receipt_0 as "⧗". wp_seq. wp_seq.
    iExists -[((l, ()), [])]. iFrame "L I". iSplitR "Obs Obs'".
    { iSplit; [|done]. iExists _. iSplit; [done|]. iExists D, d, g. iFrame "⧖ ⧗".
      iSplit; [done|]. iSplit; [done|]. iFrame "Fr".
      rewrite /ltype_own /= /ofty_owned. iExists (). iSplit; [done|]. iSplitL; [|done].
      iApply (bytes_own_of_bytes with "Pt"). exists (VTuple []). split; [done|].
      rewrite decode_value_tuple decide_True //. }
    iCombine "Obs Obs'" as "Obs". iApply (proph_obs_impl with "Obs")=>/= ?[Imp ?]. by apply Imp.
  Qed.
End oplace.
