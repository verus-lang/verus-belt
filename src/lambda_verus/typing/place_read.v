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
  - The lifetimes that must be alive ([pctx_ralv K lt]): the lifetime of the folded type at
    each unique borrow outside the shared part ([pctx_ulft], to open the borrows), and,
    below the first shared reference or resolved unique borrow at [κ], [pctx_salv K2 κ] (the
    lifetimes of the guarded loads of the pointers of the view, [place_pshr.v]).
  - No [Skip]: the first program step (of the address, or the load itself) gives the
    credits.

  The proof splits [K] at its first shared reference or resolved unique borrow
  ([pctx_read_split], with [pctx_app]): the part above it is accessed with [vroot_acc]
  ([pctx_acc.v]), or split with [ltype_own_plug] above a resolved unique borrow; below a
  shared reference, the shared view of the referent is pushed through the rest of the
  context ([wp_pshr_open], [wp_pshr_open_root] of [place_pshr.v]); below a resolved unique
  borrow, the view of its referent is accessed ([view_pctx_acc] of [place_res_ops.v]) down
  to the hole or to the next shared reference ([wp_view_read]). *)

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

  (** The lifetimes that must be alive to read the hole of [K]: below a unique borrow, the
      lifetime of its folded type (to open it); below a shared reference or a resolved
      unique borrow, the lifetimes of the guarded loads of the pointers in the view
      ([pctx_salv]). *)
  Fixpoint pctx_ralv {𝔅 𝔄} (K: pctx 𝔅 𝔄) : lty 𝔅 → lft :=
    match K in pctx 𝔅 𝔄 return lty 𝔅 → lft with
    | PHole => λ _, static
    | PFst K _ | PSnd _ K | POwn _ K | PSum _ _ _ K => pctx_ralv K
    | PUniq κ K => λ lt, ty_lft (lty_fold (UniqLty (pctx_plug K lt) κ)) ⊓ pctx_ralv K lt
    | PShr κ K | PResUniq κ K => λ _, pctx_salv K κ
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

  Lemma pctx_ralv_noshr {𝔅 𝔄} (K: pctx 𝔅 𝔄) lt :
    pctx_noshr K → ⊢ pctx_ralv K lt ⊑ pctx_ulft K lt.
  Proof.
    induction K; simpl; [iIntros; iApply guards_refl|auto|auto|auto|auto| |done|done]. intros _.
    iApply llftl_intersect_incl_l.
  Qed.

  Lemma pctx_ralv_app {ℭ 𝔅 𝔄} (K1: pctx 𝔅 𝔄) (K2: pctx ℭ 𝔅) lt :
    pctx_noshr K1 →
    ⊢ pctx_ralv (pctx_app K1 K2) lt ⊑ pctx_ulft K1 (pctx_plug K2 lt) ⊓ pctx_ralv K2 lt.
  Proof.
    induction K1 as [|? ? ? K1 IH ?|? ? ? ? K1 IH|? ? ? K1 IH|? ? ? ? ? K1 IH|𝔅' 𝔄' κ' K1 IH| |]
      in K2 |- *;
      intros HK; [|exact (IH K2 HK)..| |done|done].
    - iApply llftl_incl_glb; [iApply lft_incl_static|iApply guards_refl].
    - destruct HK as [_ HK]. cbn [pctx_ralv pctx_app pctx_ulft]. iApply llftl_incl_glb.
      + rewrite pctx_plug_app. iApply llftl_intersect_incl_l.
      + iApply llftl_incl_trans; [iApply llftl_intersect_incl_r|].
        iApply llftl_incl_trans; [by iApply IH|]. iApply llftl_intersect_incl_r.
  Qed.

  Lemma pctx_ralv_app_shr {ℭ 𝔅 𝔄} (K1: pctx (at_locₛ 𝔅) 𝔄) κ (K2: pctx ℭ 𝔅) lt :
    pctx_noshr K1 →
    ⊢ pctx_ralv (pctx_app K1 (PShr κ K2)) lt ⊑
      pctx_ulft K1 (ShrLty (pctx_plug K2 lt) κ) ⊓ pctx_salv K2 κ.
  Proof. apply pctx_ralv_app. Qed.

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
End pctx_read.

Notation pctx_rleaf K := (pctx_rleafb K true).

(** * The rule *)

Section read.
  Context `{!typeG Σ}.

  (** In [Uniq] mode, a shared-blocked leaf is an unblocked leaf. *)
  Lemma lty_rleaf_uniq {𝔄} (lt: lty 𝔄) ty κs κ ξi r d g tid l :
    lty_rleaf false lt ty κs →
    ltype_own (Uniq κ ξi) lt r d g tid l ⊣⊢ ltype_own (Uniq κ ξi) (OfTy ty) r d g tid l.
  Proof. destruct 1 as [| |? [=]]; [done|]. rewrite /ltype_own /=. by destruct r. Qed.

  (** Below no shared reference (in [Owned] or [Uniq] mode, below any number of unique
      borrows): the access [vroot_acc], a typed [Load] of the leaf (a guarded one for a
      shared-blocked leaf in [Owned] mode), and the access is closed with the same leaf. *)
  Lemma type_read_vplace_noshr {𝔅 𝔄} E L I p (K: pctx 𝔅 𝔄) `{!PctxNoShr K} `{!PctxVRoot K}
      (lt: lty 𝔅) (ty: type 𝔅) κs :
    lty_rleaf false lt ty κs → Copy ty → lctx_lft_alive E L (pctx_ralv K lt ⊓ κs) →
    typed_instr E L I +[p ◁ₗ pctx_plug K lt] (!ᶜ{ty.(ty_mty)} (pctx_vexpr K p))
      (λ v, +[v ◁ᵥ ty; p ◁ₗ pctx_plug K lt])
      (λ post '-[x], post -[pctx_get K x.1; x]).
  Proof.
    iIntros (Hl Hcopy Alv tid post mask iκs [x []]) "#LFT #TIME #PROPH #UNIQ #E L I (Tp & _) Obs".
    destruct x as [x₀ ζm]. rewrite /read_copy.
    iDestruct "Tp" as (v Hp) "Tp". iEval (rewrite vplace_own_open) in "Tp".
    iDestruct "Tp" as (D) "(#⧖ & ⧗p & Own)". have Hdl: 1 ≤ pctx_dlev K by apply pctx_vroot_dlev.
    have ?: Closed [] (pctx_vexpr K p).
    { apply pctx_vexpr_closed. by eapply eval_path_closed. }
    iDestruct (Alv with "L E") as "#Alv".
    (* The first step gives the credits. *)
    iApply (wp_persistent_time_receipt with "TIME ⧖"); [solve_ndisj|].
    iIntros "£ #⧖S". iApply wp_fupd.
    iMod (llctx_interp_make_guarded with "L") as (γh) "[H1 [H2 [#Ghalf #Halfback]]]";
      [solve_ndisj|].
    iAssert (fractional.half γh &&{↑NllftG}&&> @[pctx_ulft K lt])%I as "#Hu".
    { iApply (guards_transitive with "Ghalf"). iApply (guards_transitive with "Alv").
      iApply llftl_incl_trans; [iApply llftl_intersect_incl_l|]. by iApply pctx_ralv_noshr. }
    iAssert (fractional.half γh &&{↑NllftG}&&> @[κs])%I as "#Hκs".
    { iApply (guards_transitive with "Ghalf"). iApply (guards_transitive with "Alv").
      iApply llftl_intersect_incl_r. }
    set y := pctx_get K x₀.
    iDestruct (lc_weaken (pctx_vacc_cred K D + (D + (1 + 4 * (D + 1)))) with "£")
      as "[£a [£k [£1 £r]]]";
      [have := pctx_vacc_cred_le K D; rewrite /advance_credits; nia|].
    iMod (vroot_acc K lt with "LFT PROPH UNIQ Hu H1 £a Own")
      as (G' dh gh) "(% & G' & #G'G & -> & %Hdh & H & P & Cl)"; [solve_ndisj|].
    destruct Hdh as (Hdh & Hgh & Hin).
    set lK := pctx_vloc K (lty_size lt) x₀.
    iAssert (G' &&{↑NllftG}&&> @[pctx_ulft K lt])%I as "#G'u".
    { iApply (guards_transitive with "G'G Hu"). }
    iAssert (G' &&{↑NllftG}&&> @[κs])%I as "#G'κs".
    { iApply (guards_transitive with "G'G Hκs"). }
    (* The address of the hole. *)
    wp_bind (pctx_vexpr K p).
    iApply (wp_wand with "[P G']").
    { iApply (wp_pctx_vptrs _ K (lty_size lt) G' x₀ p True%I with "[G'] P").
      iApply wp_wand; [by iApply wp_eval_path|]. iIntros (?) "->". by iFrame. }
    iIntros (w) "(-> & _ & G' & P)".
    (* The load of the leaf, and the access closed with the same leaf. *)
    have Hr: lty_rfn lt y ζm (pctx_vpath K) = inl (PlaceIn y) by destruct Hl.
    iAssert (|={⊤ ∖ ↑advN}=> WP Load Na1Ord ty.(ty_mty) #lK @ ⊤ ∖ ↑advN {{ u,
      ∃ wv dh' gh', ⌜u = MLitV wv ∧ ty.(ty_val) y = Some wv ∧ dh' ≤ D ∧ gh' ≤ D⌝ ∗
        ty.(ty_gho_own) y dh' gh' tid ∗ |={⊤ ∖ ↑advN}=>
        vroot_own (pctx_plug K lt) (pctx_vrfn K x₀ ζm (lty_rfn lt y ζm (pctx_vpath K))) D tid
          (MLitV (VPtr (pctx_vrloc K (lty_size lt) x₀))) ∗ fractional.half γh }})%I
      with "[H Cl P G' £k £1 £r]" as ">WPl".
    { rewrite Hr. destruct (pctx_uend K) as [κ|] eqn:Hu.
      - (* [Uniq] mode: the whole referent of the innermost unique borrow. *)
        iEval (rewrite (pctx_kind_uniq K κ) //) in "H".
        iEval (rewrite (lty_rleaf_uniq lt ty κs _ _ _ _ _ _ _ Hl)) in "H".
        iEval (rewrite /pctx_vcloser (pctx_kind_uniq K κ) //) in "Cl".
        iDestruct "H" as (? idx ->) "Body".
        iMod (fractional.frac_split_guard_in_half NllftG G' G' with "G' []")
          as (γ2) "[A [B [#Gh2 #Back2]]]"; [solve_ndisj|iApply guards_refl|].
        iAssert (fractional.half γ2 &&{↑NllftG}&&> @[κ])%I as "#Aκ".
        { iApply (guards_transitive with "Gh2"). iApply (guards_transitive with "G'u").
          by iApply pctx_ulft_uend. }
        iAssert (fractional.half γ2 &&{↑NllftG}&&> @[ty_lft ty])%I as "#Aty".
        { iApply (guards_transitive with "Gh2"). iApply (guards_transitive with "G'u").
          iApply llftl_incl_trans; [iApply (pctx_ulft_fold K lt)|].
          { by eapply pctx_uend_ulfts_ne. }
          destruct Hl as [| |? [=]]; iApply guards_refl. }
        iMod (uniq_body_acc with "LFT UNIQ Aκ Body A") as "(Pl & ⧗1 & CloseB)"; [solve_ndisj|].
        iMod (lc_fupd_elim_later with "£1 Pl") as "Pl".
        iMod (uniq_payload_run with "Aty B Pl") as "(B & #⧖' & #Gho1 & Pt1)"; [solve_ndisj|].
        iDestruct (bytes_own_nocell_bytes with "Pt1") as (bs) "[Hbs %Hbs]".
        destruct (ty_bytes_val _ _ _ Hbs) as [wv Hwv].
        iModIntro. iApply (wp_load_na with "Hbs"); [by eapply ty_bytes_decode|].
        iIntros "!> Hbs". iExists wv, dh, gh. iSplit; [iPureIntro; split_and!; [done|done|lia|lia]|].
        iFrame "Gho1".
        iSpecialize ("CloseB" $! y dh gh with "[Hbs] ⧗1").
        { iNext. iFrame "⧖' Gho1". by iApply bytes_own_of_bytes. }
        iMod (fupd_mask_mono with "CloseB") as "[Body A]"; [solve_ndisj|].
        iMod (fupd_mask_mono with "(Back2 A B)") as "G'"; [solve_ndisj|].
        iMod ("Cl" $! lt (inl (PlaceIn y)) dh gh D [] 1%Qp True%I
          with "[%] [//] [//] [%] [%] [] ⧖ G' P [] [Body]") as "(Own & $ & _)".
        { by destruct Hl as [| |? [=]]. }
        { intros ??. apply prfn_rsv_in. }
        { lia. }
        { by iLeft. }
        { done. }
        { iIntros "_ !>". iSplit; [|done]. rewrite (lty_rleaf_uniq lt ty κs _ _ _ _ _ _ _ Hl).
          iExists y, idx. by iFrame. }
        by iFrame.
      - (* [Owned] mode. *)
        iEval (rewrite (pctx_kind_owned K) //) in "H".
        iEval (rewrite /pctx_vcloser (pctx_kind_owned K) //) in "Cl".
        have Hm := pctx_hmode_le K 0. set mh := pctx_hmode K 0.
        destruct Hl as [|ty β|? [=]].
        + iDestruct "H" as (? ->) "[Pt1 #Gho1]".
          iDestruct (lc_weaken mh with "£k") as "£k"; [lia|].
          iMod (lc_fupd_elim_laterN with "£k Gho1") as "#Gho1'".
          iDestruct (bytes_own_nocell_bytes with "Pt1") as (bs) "[Hbs %Hbs]".
          destruct (ty_bytes_val _ _ _ Hbs) as [wv Hwv].
          iModIntro. iApply (wp_load_na with "Hbs"); [by eapply ty_bytes_decode|].
          iIntros "!> Hbs". iExists wv, dh, gh.
          iSplit; [iPureIntro; split_and!; [done|done|lia|lia]|]. iFrame "Gho1'".
          iMod ("Cl" $! (OfTy ty) (inl (PlaceIn y)) dh gh D [] 1%Qp True%I
            with "[//] [//] [//] [%] [%] [] ⧖ G' P [] [Hbs]") as "(Own & $ & _)".
          { intros ??. apply prfn_rsv_in. }
          { lia. }
          { by iLeft. }
          { done. }
          { iIntros "_ !>". iSplit; [|done]. iExists y. iSplit; [done|].
            rewrite /ofty_owned. iFrame "Gho1". by iApply bytes_own_of_bytes. }
          by iFrame.
        + (* A shared-blocked leaf: a guarded typed [Load] from its sharing. *)
          iDestruct "H" as (? ->) "(#GPt & #Shr & #Pers & Inh)".
          iAssert (shr_view β ty y dh D tid lK) as "#V".
          { iApply (shr_view_depth_mono _ _ _ dh gh); [lia|lia|]. by iFrame "GPt Shr Pers". }
          iModIntro. iApply (wp_load_shr_view with "G'κs G' £r V"); [solve_ndisj|].
          iIntros (wv Hwv) "#Gho G'". iExists wv, dh, D.
          iSplit; [iPureIntro; split_and!; [done|done|lia|lia]|]. iFrame "Gho".
          iMod ("Cl" $! (ShrBlocked ty β) (inl (PlaceIn y)) dh gh D [] 1%Qp True%I
            with "[//] [//] [//] [%] [%] [] ⧖ G' P [] [Inh]") as "(Own & $ & _)".
          { intros ??. apply prfn_rsv_in. }
          { lia. }
          { by iLeft. }
          { done. }
          { iIntros "_ !>". iSplit; [|done]. iExists y. by iFrame "GPt Shr Pers Inh". }
          by iFrame. }
    iApply (wp_wand with "WPl").
    iIntros (u) "(%wv & %dh' & %gh' & (-> & %Hwv & % & %) & #Gho & >[Own H1])".
    iMod (fupd_mask_mono with "(Halfback H1 H2)") as "L"; [solve_ndisj|].
    iModIntro. iExists -[y; (x₀, ζm)]. iFrame "L I Obs".
    iSplitR "Own ⧗p".
    { iExists _. iSplit; [by rewrite eval_path_of_val|]. rewrite -(val_own_intro_sep _ _ _ _ wv D); [|done|done].
      iFrame "⧖". iDestruct (ty_gho_own_depth_mono _ dh' gh' D D with "Gho") as "[$ _]"; lia. }
    iSplit; [|done]. iExists _. iSplit; [done|].
    by iApply (vplace_own_close with "⧖ ⧗p").
  Qed.

  (** Below a shared reference at the hole of [K1] (below a root owned pointer or unique
      borrow): phase 1 accesses the shared reference ([wp_pshr_open]), phase 2 pushes the
      shared view of its referent through [K2]; the leaf is read with a guarded typed
      [Load]. *)
  Lemma type_read_vplace_pshr {ℭ 𝔅 𝔄} E L I p (K1: pctx (at_locₛ 𝔅) 𝔄) `{!PctxNoShr K1}
      `{!PctxVRoot K1} κ (K2: pctx ℭ 𝔅) (lt: lty ℭ) (ty: type ℭ) κs :
    let K := pctx_app K1 (PShr κ K2) in
    pctx_rleaf K lt ty κs → Copy ty → lctx_lft_alive E L (pctx_ralv K lt ⊓ κs) →
    typed_instr E L I +[p ◁ₗ pctx_plug K lt] (!ᶜ{ty.(ty_mty)} (pctx_vexpr K p))
      (λ v, +[v ◁ᵥ ty; p ◁ₗ pctx_plug K lt])
      (λ post '-[x], post -[pctx_get K x.1; x]).
  Proof.
    intros K [-> ->]%pctx_rleafb_app_shr Hcopy Alv. rewrite /K /read_copy.
    rewrite pctx_plug_app pctx_vexpr_app /=.
    iIntros (tid post mask iκs [x []]) "#LFT #TIME #PROPH #UNIQ #E L I (Tp & _) Obs".
    destruct x as [x₀ ζm].
    iDestruct "Tp" as (v Hp) "Tp". iEval (rewrite vplace_own_open) in "Tp".
    iDestruct "Tp" as (D) "(#⧖ & ⧗p & Own)".
    iDestruct (Alv with "L E") as "#Alv".
    iApply (wp_persistent_time_receipt with "TIME ⧖"); [solve_ndisj|].
    iIntros "£ #⧖S". iApply wp_fupd.
    iMod (llctx_interp_make_guarded with "L") as (γh) "[H1 [H2 [#Ghalf #Halfback]]]";
      [solve_ndisj|].
    iAssert (fractional.half γh &&{↑NllftG}&&>
      @[pctx_ulft K1 (ShrLty (pctx_plug K2 lt) κ) ⊓ pctx_salv K2 κ])%I as "#Hus".
    { iApply (guards_transitive with "Ghalf"). iApply (guards_transitive with "Alv").
      iApply llftl_incl_trans; [iApply llftl_intersect_incl_l|].
      by iApply pctx_ralv_app_shr. }
    iAssert (fractional.half γh &&{↑NllftG}&&> @[pctx_ulft K1 (ShrLty (pctx_plug K2 lt) κ)])%I
      as "#Hu". { iApply (guards_transitive with "Hus"). iApply llftl_intersect_incl_l. }
    iAssert (fractional.half γh &&{↑NllftG}&&> @[pctx_salv K2 κ])%I as "#Hs".
    { iApply (guards_transitive with "Hus"). iApply llftl_intersect_incl_r. }
    iDestruct (lc_weaken (pshr_cred D + 4 * (D + 1)) with "£") as "[£a £r]";
      [apply pshr_cred_step|].
    set y := pctx_get K1 x₀.
    wp_bind (pctx_expr K2 _).
    iApply (wp_pshr_open _ K1 κ K2 lt (pctx_plug K2 lt) x₀ ζm D tid _ p (fractional.half γh)
      with "LFT PROPH UNIQ Hu Hs H1 £a ⧖ [] Own"); [solve_ndisj|done|done|..].
    { iApply wp_wand; [by iApply wp_eval_path|]. by iIntros (?) "->". }
    iIntros (dh Hdh [Hin1 [Hin2 Hvin]]) "H1 Own #V".
    iAssert (fractional.half γh &&{↑NllftG}&&> @[pctx_slft K2 κ])%I as "#Hsl".
    { iApply (guards_transitive with "Hs"). iApply pctx_salv_slft. }
    iApply (wp_load_shr_view with "Hsl H1 £r V"); [solve_ndisj|].
    iIntros (w Hw) "#Gho H1".
    iMod (fupd_mask_mono with "(Halfback H1 H2)") as "L"; [solve_ndisj|].
    iModIntro. iExists -[pctx_get (pctx_app K1 (PShr κ K2)) x₀; (x₀, ζm)]. iFrame "L I Obs".
    iSplitR "Own ⧗p".
    { rewrite pctx_get_app. iExists _. iSplit; [by rewrite eval_path_of_val|]. rewrite -(val_own_intro_sep _ _ _ _ w D); [|done|done].
      iFrame "⧖". iDestruct (ty_gho_own_depth_mono _ dh D D D with "Gho") as "[$ _]"; lia. }
    iSplit; [|done]. iExists _. iSplit; [done|]. by iApply (vplace_own_close with "⧖ ⧗p").
  Qed.

  (** Below the shared reference at the root ([p ◁ₗ ShrLty (K2[lt]) κ]). *)
  Lemma type_read_vplace_pshr_root {ℭ 𝔅} E L I p κ (K2: pctx ℭ 𝔅) (lt: lty ℭ) (ty: type ℭ) κs :
    pctx_rleaf (PShr κ K2) lt ty κs → Copy ty →
    lctx_lft_alive E L (pctx_ralv (PShr κ K2) lt ⊓ κs) →
    typed_instr E L I +[p ◁ₗ pctx_plug (PShr κ K2) lt]
      (!ᶜ{ty.(ty_mty)} (pctx_vexpr (PShr κ K2) p))
      (λ v, +[v ◁ᵥ ty; p ◁ₗ pctx_plug (PShr κ K2) lt])
      (λ post '-[x], post -[pctx_get (PShr κ K2) x.1; x]).
  Proof.
    intros [-> ->] Hcopy Alv. rewrite /read_copy /=.
    iIntros (tid post mask iκs [x []]) "#LFT #TIME #PROPH #UNIQ #E L I (Tp & _) Obs".
    destruct x as [x ζm].
    iDestruct "Tp" as (v Hp) "Tp". rewrite vplace_own_eq.
    iDestruct "Tp" as (D) "(#⧖ & ⧗p & Own)".
    iDestruct (Alv with "L E") as "#Alv".
    iApply (wp_persistent_time_receipt with "TIME ⧖"); [solve_ndisj|].
    iIntros "£ #⧖S". iApply wp_fupd.
    iMod (llctx_interp_make_guarded with "L") as (γh) "[H1 [H2 [#Ghalf #Halfback]]]";
      [solve_ndisj|].
    iAssert (fractional.half γh &&{↑NllftG}&&> @[pctx_salv K2 κ])%I as "#Hs".
    { iApply (guards_transitive with "Ghalf"). iApply (guards_transitive with "Alv").
      iApply llftl_intersect_incl_l. }
    iDestruct (lc_weaken (pshr_cred D + 4 * (D + 1)) with "£") as "[£a £r]";
      [apply pshr_cred_step|].
    wp_bind (pctx_expr K2 (ToLit p)).
    iApply (wp_pshr_open_root _ κ K2 lt (pctx_plug K2 lt) x D tid v p (fractional.half γh)
      with "Hs H1 £a [] Own"); [solve_ndisj|done|done|..].
    { iApply wp_wand; [by iApply wp_eval_path|]. by iIntros (?) "->". }
    iIntros (dh Hdh [Hin2 Hvin]) "H1 Own #V".
    iAssert (fractional.half γh &&{↑NllftG}&&> @[pctx_slft K2 κ])%I as "#Hsl".
    { iApply (guards_transitive with "Hs"). iApply pctx_salv_slft. }
    iApply (wp_load_shr_view with "Hsl H1 £r V"); [solve_ndisj|].
    iIntros (w Hw) "#Gho H1".
    iMod (fupd_mask_mono with "(Halfback H1 H2)") as "L"; [solve_ndisj|].
    iModIntro. iExists -[pctx_get K2 x.2; (x, ζm)]. iFrame "L I Obs".
    iSplitR "Own ⧗p".
    { iExists _. iSplit; [by rewrite eval_path_of_val|]. rewrite -(val_own_intro_sep _ _ _ _ w D); [|done|done].
      iFrame "⧖". iDestruct (ty_gho_own_depth_mono _ dh D D D with "Gho") as "[$ _]"; lia. }
    iSplit; [|done]. iExists _. iSplit; [done|]. rewrite vplace_own_eq. iExists D. by iFrame.
  Qed.

  (** A resolved leaf in the owned part of a place rooted at an owned location (below no
      unique borrow): its cells are owned, and its resolved ownership is its ownership
      ([ResOwn]), which is persistent ([Copy]). *)
  Lemma type_read_vplace_ores {𝔅 𝔄} E L I p n (K: pctx 𝔅 𝔄) `{!PctxNoUniq K} (ty: type 𝔅) :
    ResOwn ty → Copy ty →
    typed_instr E L I +[p ◁ₗ pctx_plug (POwn n K) (OfRes ty)]
      (!ᶜ{ty.(ty_mty)} (pctx_vexpr (POwn n K) p))
      (λ v, +[v ◁ᵥ ty; p ◁ₗ pctx_plug (POwn n K) (OfRes ty)])
      (λ post '-[x], post -[pctx_get (POwn n K) x.1; x]).
  Proof.
    iIntros (Hres Hcopy tid post mask iκs [x []]) "#LFT #TIME #PROPH #UNIQ #E L I (Tp & _) Obs".
    destruct x as [[l x₀] ζm]. rewrite /read_copy /=.
    rewrite /tctx_elt_interp.
    iDestruct "Tp" as (v Hp D d g) "(#⧖ & ⧗p & -> & %Hle & Fr & Own)".
    have ?: Closed [] (pctx_expr K (ToLit p)).
    { apply pctx_expr_closed. have ?: Closed [] p by eapply eval_path_closed. apply _. }
    rewrite /ltype_own lty_pat_plug lty_rfn_plug ltype_own_plug.
    iDestruct "Own" as "[L1 Rest]". iSimpl in "L1".
    iDestruct "L1" as (? ->) "[Pt1 Gr]".
    iDestruct (pctx_own_mode_le with "Rest") as %Hk.
    set y := pctx_get K x₀.
    set lK := pctx_loc K (lty_size (OfRes ty)) x₀ l.
    set dh := pctx_depth K d.
    have Hdh: dh ≤ d. { rewrite /dh pctx_depth_sub. lia. }
    (* The address of the hole. *)
    wp_bind (pctx_expr K (ToLit p)).
    iApply (wp_wand with "[Rest]").
    { iApply (wp_pctx_expr K (lty_size (OfRes ty)) 1 x₀ ζm [] d g tid l (ToLit p) True True
        with "[] Rest").
      - wp_bind p. iApply wp_wand; [by iApply wp_eval_path|]. iIntros (?) "->".
        by wp_pure _. }
    iIntros (w) "(-> & _ & _ & Rest)".
    iApply (wp_persistent_time_receipt with "TIME ⧖"); [solve_ndisj|].
    iIntros "£ #⧖S". iApply wp_fupd.
    iDestruct (lc_weaken (pctx_mode K 1) with "£") as "£";
      [rewrite /advance_credits pctx_mode_add; nia|].
    iMod (lc_fupd_elim_laterN with "£ Gr") as (d' g' Hdg) "Gr".
    iEval (rewrite res_own) in "Gr". iDestruct "Gr" as "#Gho".
    iDestruct (bytes_own_nocell_bytes with "Pt1") as (bs) "[Hbs %Hbs]".
    destruct (ty_bytes_val _ _ _ Hbs) as [vw Hvw].
    iApply (wp_load_na with "Hbs"); [by eapply ty_bytes_decode|].
    iIntros "!> Hbs". iModIntro.
    iExists -[y; ((l, x₀), ζm)]. iFrame "L I Obs".
    iSplitR "Hbs Rest ⧗p Fr".
    { iExists _. iSplit; [by rewrite eval_path_of_val|]. rewrite -(val_own_intro_sep _ _ _ _ vw D); [|done|done].
      iFrame "⧖". iDestruct (ty_gho_own_depth_mono _ d' g' D D with "Gho") as "[$ _]"; lia. }
    iSplit; [|done]. iExists (MLitV (VPtr l)). iSplit; [done|]. iExists D, d, g.
    iFrame "⧖ ⧗p Fr". iSplit; [done|]. iSplit; [done|].
    rewrite /ltype_own lty_pat_plug lty_rfn_plug ltype_own_plug. iFrame "Rest".
    iExists y. iSplit; [done|]. iSplitL "Hbs"; [by iApply bytes_own_of_bytes|].
    iApply bi.laterN_intro. iExists d', g'. iSplit; [done|]. by rewrite res_own.
  Qed.

  (** ** Reading in a view

      The read of the hole of [K] in the view of a place at [l] (the referent of a resolved
      unique borrow, at [κ]): the access to a sub-place of the view ([view_pctx_acc]) down to
      the hole or to the first shared reference, whose shared view is then pushed through the
      rest of the context ([shr_pctx_view]). The base address [e] is evaluated first; [R] is
      what its evaluation keeps. *)
  Definition view_cred (M: nat) : nat := 6 * M * M + 14 * M + 6.

  Lemma wp_view_read {ℭ 𝔅} E (K: pctx ℭ 𝔅) `{!PctxRead K} κ (lt: lty ℭ) (ty: type ℭ) κs
      `{!Copy ty} b m z ζm q d g tid (l: loc) M (G R: iProp Σ) (e: expr) (Φ: val → iProp Σ) :
    ↑NllftG ⊆ E → Timeless G → pctx_rleafb K b lt ty κs → d ≤ M → g ≤ M →
    let V := lty_view (pctx_plug K lt) κ m (pctx_pat K (lty_pat lt))
      (pctx_rfn K z ζm q (lty_rfn lt (pctx_get K z) ζm (pctx_path K q))) d g tid l in
    (G &&{↑NllftG}&&> @[pctx_salv K κ ⊓ κs]) -∗ G -∗ £(view_cred M) -∗ V -∗
    WP e @ E {{ v, ⌜v = #(l)⌝ ∗ R }} -∗
    (∀ w dh gh, ⌜ty.(ty_val) (pctx_get K z) = Some w ∧ dh ≤ M ∧ gh ≤ M⌝ -∗
      ty.(ty_gho_own) (pctx_get K z) dh gh tid -∗ R -∗ G -∗ V -∗ Φ (MLitV w)) -∗
    WP Load Na1Ord ty.(ty_mty) (pctx_expr K e) @ E {{ Φ }}.
  Proof.
    intros HE ? Hl Hd Hg V. iIntros "#Gs G £ V WPe HΦ".
    iAssert (G &&{↑NllftG}&&> @[pctx_salv K κ])%I as "#Gs1".
    { iApply (guards_transitive with "Gs"). iApply llftl_intersect_incl_l. }
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
      iDestruct (lc_weaken (2 * (g + 1) * pctx_dlev K + 4 * (M + 1)) with "£") as "[£s £l]";
        [rewrite /view_cred; nia|].
      wp_bind (pctx_expr K e).
      iApply (wp_pctx_sexpr E K (lty_size lt) (g + 1) G z l e); [done|].
      iApply (wp_wand with "WPe"). iIntros (v) "[-> R]".
      iFrame "Gp £s G". iSplit; [done|]. iIntros "G".
      iApply (wp_load_shr_view with "Gsl G £l Vs'"); [done|].
      iIntros (w Hw) "Gho G". iApply ("HΦ" with "[%] Gho R G"); [split_and!; [done|lia..]|].
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
        (2 * (g + 1) * (M + 1) + 4 * (M + 1)))) with "£") as "(£s & £v & £s2 & £l)".
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
      wp_bind (pctx_expr K2 _).
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
      iApply (wp_load_shr_view with "Gsl G £l Vh2'"); [done|].
      iIntros (w Hw) "Gho G". iApply ("HΦ" with "[%] Gho R G");
        [split_and!; [done|simpl in *; lia..]|].
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
  Lemma type_read_vplace_res {ℭ 𝔅 𝔄} E L I p n (K1: pctx (uniq_borₛ 𝔅) 𝔄) `{!PctxNoUniq K1}
      κ (K2: pctx ℭ 𝔅) `{!PctxRead K2} (lt: lty ℭ) (ty: type ℭ) κs :
    let K := POwn n (pctx_app K1 (PResUniq κ K2)) in
    pctx_rleaf K lt ty κs → Copy ty → lctx_lft_alive E L (pctx_ralv K lt ⊓ κs) →
    typed_instr E L I +[p ◁ₗ pctx_plug K lt] (!ᶜ{ty.(ty_mty)} (pctx_vexpr K p))
      (λ v, +[v ◁ᵥ ty; p ◁ₗ pctx_plug K lt])
      (λ post '-[x], post -[pctx_get K x.1; x]).
  Proof.
    have ?: PctxNoShr K1 by apply _.
    intros K Hl Hcopy Alv.
    destruct (pctx_rleafb_app_noshr K1 _ true lt ty κs pctx_no_shr Hl) as [b Hl'].
    rewrite /K /read_copy /= pctx_plug_app pctx_expr_app /=.
    iIntros (tid post mask iκs [x []]) "#LFT #TIME #PROPH #UNIQ #E L I (Tp & _) Obs".
    destruct x as [[l x₀] ζm].
    rewrite /tctx_elt_interp.
    iDestruct "Tp" as (v Hp D d g) "(#⧖ & ⧗p & -> & %Hle & Fr & Own)".
    have ?: Closed [] (pctx_expr K1 (ToLit p)).
    { apply pctx_expr_closed. have ?: Closed [] p by eapply eval_path_closed. apply _. }
    iDestruct (Alv with "L E") as "#Alv".
    (* The first step gives the credits. *)
    iApply (wp_persistent_time_receipt with "TIME ⧖"); [solve_ndisj|].
    iIntros "£ #⧖S". iApply wp_fupd.
    iMod (llctx_interp_make_guarded with "L") as (γh) "[H1 [H2 [#Ghalf #Halfback]]]";
      [solve_ndisj|].
    iAssert (fractional.half γh &&{↑NllftG}&&> @[pctx_salv K2 κ ⊓ κs])%I as "#Hs".
    { iApply (guards_transitive with "Ghalf"). iApply (guards_transitive with "Alv").
      iApply llftl_incl_glb; [|iApply llftl_intersect_incl_r].
      iApply llftl_incl_trans; [iApply llftl_intersect_incl_l|].
      iApply llftl_incl_trans; [by iApply (pctx_ralv_app K1 (PResUniq κ K2))|].
      iApply llftl_intersect_incl_r. }
    set lt1 := ResUniqLty (pctx_plug K2 lt) κ.
    rewrite /ltype_own lty_pat_plug lty_rfn_plug ltype_own_plug.
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
    rewrite lty_pat_plug lty_rfn_plug.
    have ?: pctx_depth K1 d ≤ d by (rewrite pctx_depth_sub; lia).
    iApply (wp_view_read _ K2 κ lt ty κs false 0 z ζm (false :: q0) d' g' tid ly D
      (fractional.half γh) (ptr_cell lK ly ∗ pctx_own K1 (lty_size lt1) 1 x₀ ζm [] d g tid l)%I
      with "Hs H1 £ V [Pt Rest]"); [solve_ndisj|done|lia|lia|..].
    { wp_bind (pctx_expr K1 (ToLit p)).
      iApply (wp_wand with "[Rest]").
      { iApply (wp_pctx_expr_mask _ K1 (lty_size lt1) 1 x₀ ζm [] d g tid l (ToLit p) True True
          with "[] Rest").
        wp_bind p. iApply wp_wand; [by iApply wp_eval_path|]. iIntros (?) "->".
        by wp_pure _. }
      iIntros (w) "(-> & _ & _ & Rest)".
      iDestruct "Pt" as (bs) "[Hbs %Hbs]".
      wp_bind (Load _ _ _). iApply (wp_load_na with "Hbs"); [exact Hbs|]. iIntros "!> Hbs".
      wp_pure _. iSplit; [done|]. iFrame "Rest". iExists bs. by iFrame. }
    iIntros (w dh gh (Hw & ? & ?)) "#Gho [Pt Rest] H1 V".
    iMod (fupd_mask_mono with "(Halfback H1 H2)") as "L"; [solve_ndisj|].
    iModIntro. iExists -[pctx_get (pctx_app K1 (PResUniq κ K2)) x₀; ((l, x₀), ζm)].
    iFrame "L I Obs".
    iSplitR "Pt Rest V ⧗p Fr".
    { rewrite pctx_get_app -/y Hy. iExists _. iSplit; [by rewrite eval_path_of_val|]. rewrite -(val_own_intro_sep _ _ _ _ w D); [|done|done].
      iFrame "⧖". iDestruct (ty_gho_own_depth_mono _ dh gh D D with "Gho") as "[$ _]"; lia. }
    iSplit; [|done]. iExists (MLitV (VPtr l)). iSplit; [done|]. iExists D, d, g.
    iFrame "⧖ ⧗p Fr". iSplit; [done|]. iSplit; [done|].
    rewrite /ltype_own lty_pat_plug lty_rfn_plug ltype_own_plug -/y Hy. iFrame "Rest".
    rewrite /= /res_node /=. iFrame "Pt".
    iApply bi.laterN_intro. iFrame "Incl".
    iExists d', g'. iSplit; [done|]. by rewrite lty_pat_plug lty_rfn_plug.
  Qed.

  (** Below the resolved unique borrow at the root ([p ◁ₗ ResUniqLty (K2[lt]) κ]). *)
  Lemma type_read_vplace_res_root {ℭ 𝔅} E L I p κ (K2: pctx ℭ 𝔅) `{!PctxRead K2} (lt: lty ℭ)
      (ty: type ℭ) κs :
    pctx_rleaf (PResUniq κ K2) lt ty κs → Copy ty →
    lctx_lft_alive E L (pctx_ralv (PResUniq κ K2) lt ⊓ κs) →
    typed_instr E L I +[p ◁ₗ pctx_plug (PResUniq κ K2) lt]
      (!ᶜ{ty.(ty_mty)} (pctx_vexpr (PResUniq κ K2) p))
      (λ v, +[v ◁ᵥ ty; p ◁ₗ pctx_plug (PResUniq κ K2) lt])
      (λ post '-[x], post -[pctx_get (PResUniq κ K2) x.1; x]).
  Proof.
    intros Hl Hcopy Alv. rewrite /read_copy /=.
    iIntros (tid post mask iκs [x []]) "#LFT #TIME #PROPH #UNIQ #E L I (Tp & _) Obs".
    destruct x as [x ζm].
    iDestruct "Tp" as (v Hp) "Tp". rewrite vplace_own_eq.
    iDestruct "Tp" as (D) "(#⧖ & ⧗p & Own)".
    iDestruct (Alv with "L E") as "#Alv".
    iApply (wp_persistent_time_receipt with "TIME ⧖"); [solve_ndisj|].
    iIntros "£ #⧖S". iApply wp_fupd.
    iMod (llctx_interp_make_guarded with "L") as (γh) "[H1 [H2 [#Ghalf #Halfback]]]";
      [solve_ndisj|].
    iAssert (fractional.half γh &&{↑NllftG}&&> @[pctx_salv K2 κ ⊓ κs])%I as "#Hs".
    { iApply (guards_transitive with "Ghalf Alv"). }
    destruct x as [[[[[lx z] ξi] d0] g0] idx0].
    iDestruct "Own" as (d g [Hd Hg]) "[-> (#Incl & %d' & %g' & %Hle' & V)]".
    rewrite lty_pat_plug lty_rfn_plug.
    iDestruct (lc_weaken (view_cred D) with "£") as "£";
      [rewrite /advance_credits /view_cred; nia|].
    iApply (wp_view_read _ K2 κ lt ty κs false 0 z ζm [] d' g' tid lx D (fractional.half γh)
      True%I with "Hs H1 £ V [] [-]"); [solve_ndisj|done|lia|lia|..].
    { wp_bind p. iApply wp_wand; [by iApply wp_eval_path|]. iIntros (?) "->". by wp_pure _. }
    iIntros (w dh gh (Hw & ? & ?)) "#Gho _ H1 V".
    iMod (fupd_mask_mono with "(Halfback H1 H2)") as "L"; [solve_ndisj|].
    iModIntro. iExists -[pctx_get K2 z; ((lx, z, ξi, d0, g0, idx0), ζm)]. iFrame "L I Obs".
    iSplitR "V ⧗p".
    { iExists _. iSplit; [by rewrite eval_path_of_val|]. rewrite -(val_own_intro_sep _ _ _ _ w D); [|done|done].
      iFrame "⧖". iDestruct (ty_gho_own_depth_mono _ dh gh D D with "Gho") as "[$ _]"; lia. }
    iSplit; [|done]. iExists _. iSplit; [done|]. rewrite vplace_own_eq. iExists D.
    iFrame "⧖ ⧗p". iExists d, g. iSplit; [done|]. iSplit; [done|]. iFrame "Incl".
    iExists d', g'. iSplit; [done|]. by rewrite lty_pat_plug lty_rfn_plug.
  Qed.

  (** ** The rule

      Copying the value of a [Copy] leaf (of any size) out of the hole of [K], in any place
      rooted at a value: a typed [Load] ([!ᶜ{ty_mty ty}]) at the address of the hole. The
      place does not change. *)
  Lemma type_read_place_instr {𝔅 𝔄} E L I p (K: pctx 𝔅 𝔄) `{!PctxVRoot K} `{!PctxRead K}
      (lt: lty 𝔅) (ty: type 𝔅) κs :
    pctx_rleaf K lt ty κs → Copy ty → lctx_lft_alive E L (pctx_ralv K lt ⊓ κs) →
    typed_instr E L I +[p ◁ₗ pctx_plug K lt] (!ᶜ{ty.(ty_mty)} (pctx_vexpr K p))
      (λ v, +[v ◁ᵥ ty; p ◁ₗ pctx_plug K lt])
      (λ post '-[x], post -[pctx_get K x.1; x]).
  Proof.
    rename select (PctxVRoot K) into HR. rename select (PctxRead K) into HK.
    destruct K as [| | |? ? n K| |? ? κ K|? ? κ K|? ? κ K]; try done;
      rewrite /PctxRead /= in HK.
    - destruct (pctx_read_split K HK) as [HK'|[(𝔅' & κ & K1 & K2 & -> & HK1)|
        (𝔅' & κ & K1 & K2 & -> & HK1 & HKu & HK2)]].
      + intros Hl. have ?: PctxNoShr (POwn n K) by done.
        destruct (pctx_rleafb_noshr (POwn n K) true lt ty κs HK' Hl) as [[Hu Hl']|Hl'].
        * destruct (lty_rleaf_cases _ _ _ _ Hl') as [Hl''|(-> & Hres & ->)].
          -- exact (type_read_vplace_noshr E L I p (POwn n K) lt ty κs Hl'').
          -- have ?: PctxNoUniq K by done. intros Hc _.
             exact (type_read_vplace_ores E L I p n K ty Hres Hc).
        * exact (type_read_vplace_noshr E L I p (POwn n K) lt ty κs Hl').
      + have ?: PctxNoShr (POwn n K1) by done.
        exact (type_read_vplace_pshr E L I p (POwn n K1) κ K2 lt ty κs).
      + have ?: PctxNoUniq K1 by done. have ?: PctxRead K2 by done.
        exact (type_read_vplace_res E L I p n K1 κ K2 lt ty κs).
    - destruct HK as [HKs HK].
      destruct (pctx_read_split K HK) as [HK'|[(𝔅' & κ' & K1 & K2 & -> & HK1)|
        (𝔅' & κ' & K1 & K2 & -> & HK1 & _)]].
      + intros Hl. have ?: PctxNoShr (PUniq κ K) by done.
        apply (type_read_vplace_noshr E L I p (PUniq κ K) lt ty κs).
        by destruct (pctx_rleafb_noshr (PUniq κ K) true lt ty κs (conj HKs HK') Hl) as [[[] _]|?].
      + have ?: PctxNoShr (PUniq κ K1).
        { split; [by eapply pctx_simple_app_l|done]. }
        exact (type_read_vplace_pshr E L I p (PUniq κ K1) κ' K2 lt ty κs).
      + exfalso. by apply (pctx_simple_app_not K1 (PResUniq κ' K2)); [intros ?|..].
    - exact (type_read_vplace_pshr_root E L I p κ K lt ty κs).
    - have ?: PctxRead K by done.
      exact (type_read_vplace_res_root E L I p κ K lt ty κs).
  Qed.
End read.
