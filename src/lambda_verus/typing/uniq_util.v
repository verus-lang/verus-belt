From lrust.typing Require Export type.
From lrust.lifetime Require Import lifetime_full.
From lrust.util Require Export proph_bor.
From guarding Require Import guard tactics.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

(** * Encoding of depths

  The prophecy variable of a unique borrow ranges over the borrowed value
  together with its depth indices [(d, g)], encoded as positives. *)

Definition enc_depth (d: nat) : positive := Pos.of_succ_nat d.
Definition dec_depth (p: positive) : nat := Nat.pred (Pos.to_nat p).

Lemma dec_enc_depth d : dec_depth (enc_depth d) = d.
Proof. rewrite /dec_depth /enc_depth SuccNat2Pos.id_succ. done. Qed.

Lemma enc_dec_depth p : enc_depth (dec_depth p) = p.
Proof.
  rewrite /dec_depth /enc_depth. have ?:= Pos2Nat.is_pos p.
  apply Pos2Nat.inj. rewrite SuccNat2Pos.id_succ. lia.
Qed.

Global Instance enc_depth_inj : Inj (=) (=) enc_depth.
Proof. intros d d' Heq. by rewrite -(dec_enc_depth d) -(dec_enc_depth d') Heq. Qed.

Definition uniq_cell {𝔄} (x: ~~𝔄) (d g: nat) : ~~ (uniq_cellₛ 𝔄) :=
  (x, (enc_depth d, enc_depth g)).

Global Instance uniq_cell_inj {𝔄} : Inj3 (=) (=) (=) (=) (@uniq_cell 𝔄).
Proof. intros ?????? [=]. split; [done|]. split; by eapply enc_depth_inj. Qed.

Lemma uniq_cell_surj {𝔄} (c: ~~ (uniq_cellₛ 𝔄)) :
  c = uniq_cell c.1 (dec_depth c.2.1) (dec_depth c.2.2).
Proof. destruct c as [x [p1 p2]]. by rewrite /uniq_cell !enc_dec_depth. Qed.

Lemma vπ_uniq_cell {𝔄} (x: ~~𝔄) d g π :
  @vπ (uniq_cellₛ 𝔄) (uniq_cell x d g) π = (vπ x π, (enc_depth d, enc_depth g)).
Proof. done. Qed.

Lemma uniq_cell_dep {𝔄} (x: ~~𝔄) d g ζl :
  vπ x ./ ζl → @vπ (uniq_cellₛ 𝔄) (uniq_cell x d g) ./ ζl.
Proof. apply (proph_dep_constr (λ a, (a, (enc_depth d, enc_depth g)))). Qed.

Lemma uniq_cell_dep_rev {𝔄} (c: ~~ (uniq_cellₛ 𝔄)) ζl :
  (λ π, (@vπ 𝔄 c.1 π)) ./ ζl → @vπ (uniq_cellₛ 𝔄) c ./ ζl.
Proof. destruct c as [x [p1 p2]]. apply (proph_dep_constr (λ a, (a, (p1, p2)))). Qed.

Lemma uniq_prvar_app_irrel {𝔄} (x x': ~~𝔄) ξi (π: proph_asn) :
  (π (uniq_prvar x ξi)).1 = (π (uniq_prvar x' ξi)).1.
Proof.
  rewrite /uniq_prvar /uniq_cell_tyi.
  by rewrite (proof_irrel (@to_inh_syn_type (uniq_cellₛ 𝔄) (vπ x inhabitant, (1%positive, 1%positive)))
                         (@to_inh_syn_type (uniq_cellₛ 𝔄) (vπ x' inhabitant, (1%positive, 1%positive)))).
Qed.

Section uniq_util.
  Context `{!typeG Σ}.

  (** ** The payload of a unique borrow

    The payload is lazy: the ownership predicate of the contents and the points-to are
    under a fancy update with the mask [lazyE]. This lets a future lender of blocked
    contents turn them back into the payload inside the update, by firing inheritances
    of the lifetime logic ([[†κ] ={↑Nllft}=∗ …]), which cannot be done in the closing
    view shift of a borrow (whose mask is [↑NllftUsr ∪ ↑NllftUsr2]). Since
    [↑NllftG ⊆ ↑Nllft ⊆ lazyE], the update can never run while a guard is open; it is
    run after opening the borrow non-atomically (with a guard for the lifetime), paying
    for the later in front of the contents with a later credit (e.g. from time
    receipts) or with a program step.

    The time receipt is outside the update. It is persistent, and it is needed in
    places where the update cannot run: when a reborrow ends, [proph_ibor_reborrow] and
    [proph_ibor_unnest] record it as the persistent summary of the final value of the
    reborrow in a closing view shift of the lifetime logic (it is the time receipt of
    the restored borrow); and [resolve_uniq_body] reads it to get the later credits it
    needs. The persistent predicate of the contents is not part of the payload: it is
    implied by their ownership predicate, inside the update. *)
  Definition lazyE : coPset := ↑Nllft ∪ ↑prophN ∪ ↑uniqN.

  Lemma lazyE_NllftUsr : ↑NllftUsr ∪ ↑NllftUsr2 ⊆ lazyE.
  Proof. rewrite /lazyE /NllftUsr /NllftUsr2. solve_ndisj. Qed.

  Definition uniq_payload {𝔄} (ty: type 𝔄) (tid: thread_id) (l: cloc)
      (c: ~~ (uniq_cellₛ 𝔄)) : iProp Σ :=
    ⧖(S (dec_depth c.2.1) `max` dec_depth c.2.2) ∗
    |={lazyE}=> (ty.(ty_gho_own) c.1 (dec_depth c.2.1) (dec_depth c.2.2) tid ∗
      l #↦!∗ ty.(ty_phys) c.1 tid).

  Lemma uniq_payload_cell {𝔄} (ty: type 𝔄) tid l x d g :
    uniq_payload ty tid l (uniq_cell x d g) ⊣⊢
      ⧖(S d `max` g) ∗
      |={lazyE}=> (ty.(ty_gho_own) x d g tid ∗ l #↦!∗ ty.(ty_phys) x tid).
  Proof. by rewrite /uniq_payload /= !dec_enc_depth. Qed.

  Lemma uniq_payload_later_cell {𝔄} (ty: type 𝔄) tid l x d g :
    ▷ uniq_payload ty tid l (uniq_cell x d g) ⊣⊢
      ▷ (⧖(S d `max` g) ∗
        |={lazyE}=> (ty.(ty_gho_own) x d g tid ∗ l #↦!∗ ty.(ty_phys) x tid)).
  Proof. by rewrite uniq_payload_cell. Qed.

  (** A non-lazy payload. *)
  Lemma uniq_payload_intro {𝔄} (ty: type 𝔄) tid l x d g :
    ⧖(S d `max` g) -∗ ty.(ty_gho_own) x d g tid -∗ l #↦!∗ ty.(ty_phys) x tid -∗
    uniq_payload ty tid l (uniq_cell x d g).
  Proof.
    rewrite uniq_payload_cell. iIntros "$ Gho Pt". iModIntro. iFrame.
  Qed.

  Lemma uniq_payload_intro_later {𝔄} (ty: type 𝔄) tid l x d g :
    ▷ (⧖(S d `max` g) ∗ ty.(ty_gho_own) x d g tid ∗ l #↦!∗ ty.(ty_phys) x tid) -∗
    ▷ uniq_payload ty tid l (uniq_cell x d g).
  Proof. iIntros "(⧖ & Gho & Pt) !>". iApply (uniq_payload_intro with "⧖ Gho Pt"). Qed.

  (** Running the lazy update of a payload that is under a later, with a later
      credit. *)
  Lemma uniq_payload_force {𝔄} (ty: type 𝔄) tid l x d g E :
    lazyE ⊆ E →
    £1 -∗ ▷ uniq_payload ty tid l (uniq_cell x d g) ={E}=∗
      ⧖(S d `max` g) ∗ ty.(ty_gho_own) x d g tid ∗ l #↦!∗ ty.(ty_phys) x tid.
  Proof.
    iIntros (?) "£ P". rewrite uniq_payload_cell.
    iMod (lc_fupd_elim_later with "£ P") as "($ & Upd)".
    by iMod (fupd_mask_mono with "Upd") as "$".
  Qed.

  (** Mapping the lazy part of a payload. *)
  Lemma uniq_payload_map {𝔄 𝔅} (ty: type 𝔄) (ty': type 𝔅) tid tid' l l' x x' d g d' g' :
    (⧖(S d `max` g) -∗ ⧖(S d' `max` g')) -∗
    (ty.(ty_gho_own) x d g tid ∗ l #↦!∗ ty.(ty_phys) x tid ={lazyE}=∗
      ty'.(ty_gho_own) x' d' g' tid' ∗ l' #↦!∗ ty'.(ty_phys) x' tid') -∗
    uniq_payload ty tid l (uniq_cell x d g) -∗ uniq_payload ty' tid' l' (uniq_cell x' d' g').
  Proof.
    rewrite !uniq_payload_cell. iIntros "T W (⧖ & Upd)".
    iSplitL "T ⧖"; [by iApply "T"|]. iMod "Upd". by iApply "W".
  Qed.

  Definition uniq_body_pers_component {𝔄} (ty: type 𝔄) (x: ~~ 𝔄) (ξi: positive) (d: nat) (g: nat) (idx: Idx)
  (κ: lft) (tid: thread_id) (l: cloc) : iProp Σ :=
    proph_idx_bor κ (uniq_prvar x ξi) idx (uniq_payload ty tid l).

  Definition uniq_tok {𝔄} (x: ~~ 𝔄) (ξi: positive) (d: nat) (g: nat) (idx: Idx) : iProp Σ :=
    proph_bor_tok (uniq_prvar x ξi) (uniq_cell x d g) idx.

  Definition uniq_body {𝔄} (ty: type 𝔄) (x: ~~ 𝔄) (ξi: positive) (d: nat) (g: nat) (idx: Idx)
      (κ: lft) (tid: thread_id) (l: cloc) : iProp Σ :=
    proph_ibor κ (uniq_prvar x ξi) (uniq_cell x d g) idx (uniq_payload ty tid l) ∗ ⧗1.

  Global Instance uniq_tok_timeless {𝔄} (x: ~~ 𝔄) ξi d g idx : Timeless (uniq_tok x ξi d g idx).
  Proof. apply _. Qed.

  Global Instance uniq_body_pers_component_persistent {𝔄} (ty: type 𝔄) x ξi d g idx κ tid l :
    Persistent (uniq_body_pers_component ty x ξi d g idx κ tid l).
  Proof. apply _. Qed.

  Lemma uniq_body_unfold {𝔄} (ty: type 𝔄) x ξi d g idx κ tid l :
    uniq_body ty x ξi d g idx κ tid l ⊣⊢
      uniq_tok x ξi d g idx ∗ ⧗1 ∗ uniq_body_pers_component ty x ξi d g idx κ tid l.
  Proof.
    rewrite /uniq_body /uniq_tok /uniq_body_pers_component proph_ibor_sep.
    iSplit; [iIntros "[[A B] C]"|iIntros "(A & C & B)"]; iFrame.
  Qed.

  (** ** Non-expansiveness *)

  Lemma uniq_payload_ne {𝔄} n (ty ty': type 𝔄) tid l c :
    (∀ x d g, ty.(ty_gho_own) x d g tid ≡{n}≡ ty'.(ty_gho_own) x d g tid) →
    (∀ x d g, ty.(ty_gho_pers) x d g tid ≡{n}≡ ty'.(ty_gho_pers) x d g tid) →
    (∀ x, ty.(ty_phys) x tid = ty'.(ty_phys) x tid) →
    uniq_payload ty tid l c ≡{n}≡ uniq_payload ty' tid l c.
  Proof.
    intros Hg Hpers Hp. rewrite /uniq_payload Hp. f_equiv. f_equiv. f_equiv. apply Hg.
  Qed.

  Lemma uniq_payload_proper {𝔄} (ty ty': type 𝔄) tid tid' l c :
    (∀ x d g, ty.(ty_gho_own) x d g tid ⊣⊢ ty'.(ty_gho_own) x d g tid') →
    (∀ x d g, ty.(ty_gho_pers) x d g tid ⊣⊢ ty'.(ty_gho_pers) x d g tid') →
    (∀ x, ty.(ty_phys) x tid = ty'.(ty_phys) x tid') →
    uniq_payload ty tid l c ⊣⊢ uniq_payload ty' tid' l c.
  Proof.
    intros Hg Hpers Hp. rewrite /uniq_payload Hp. f_equiv. f_equiv. f_equiv. apply Hg.
  Qed.

  Lemma uniq_body_ne {𝔄} n (ty ty': type 𝔄) x ξi d g idx κ tid l :
    (∀ x d g, ty.(ty_gho_own) x d g tid ≡{n}≡ ty'.(ty_gho_own) x d g tid) →
    (∀ x d g, ty.(ty_gho_pers) x d g tid ≡{n}≡ ty'.(ty_gho_pers) x d g tid) →
    (∀ x, ty.(ty_phys) x tid = ty'.(ty_phys) x tid) →
    uniq_body ty x ξi d g idx κ tid l ≡{n}≡ uniq_body ty' x ξi d g idx κ tid l.
  Proof.
    intros Hg Hpers Hp. rewrite /uniq_body. f_equiv. apply proph_ibor_ne=> c.
    by apply uniq_payload_ne.
  Qed.

  Lemma uniq_body_contractive {𝔄} n (ty ty': type 𝔄) x ξi d g idx κ tid l :
    (∀ x d g, dist_later n (ty.(ty_gho_own) x d g tid) (ty'.(ty_gho_own) x d g tid)) →
    (∀ x d g, dist_later n (ty.(ty_gho_pers) x d g tid) (ty'.(ty_gho_pers) x d g tid)) →
    (∀ x, ty.(ty_phys) x tid = ty'.(ty_phys) x tid) →
    uniq_body ty x ξi d g idx κ tid l ≡{n}≡ uniq_body ty' x ξi d g idx κ tid l.
  Proof.
    intros Hg Hpers Hp. rewrite /uniq_body. f_equiv. apply proph_ibor_contractive=> c.
    destruct n as [|n]; [split; lia|]. apply dist_later_S.
    apply uniq_payload_ne; [| |done]=> x1 d1 g1.
    - have := Hg x1 d1 g1. by rewrite dist_later_S.
    - have := Hpers x1 d1 g1. by rewrite dist_later_S.
  Qed.

  Lemma uniq_body_proper {𝔄} (ty ty': type 𝔄) x ξi d g idx κ tid tid' l :
    (∀ x d g, ty.(ty_gho_own) x d g tid ⊣⊢ ty'.(ty_gho_own) x d g tid') →
    (∀ x d g, ty.(ty_gho_pers) x d g tid ⊣⊢ ty'.(ty_gho_pers) x d g tid') →
    (∀ x, ty.(ty_phys) x tid = ty'.(ty_phys) x tid') →
    uniq_body ty x ξi d g idx κ tid l ⊣⊢ uniq_body ty' x ξi d g idx κ tid' l.
  Proof.
    intros Hg Hpers Hp. rewrite /uniq_body. f_equiv. apply proph_ibor_proper=> c.
    by apply uniq_payload_proper.
  Qed.

  Lemma uniq_pers_component_ne {𝔄} n (ty ty': type 𝔄) x ξi d g idx κ tid l :
    (∀ x d g, ty.(ty_gho_own) x d g tid ≡{n}≡ ty'.(ty_gho_own) x d g tid) →
    (∀ x d g, ty.(ty_gho_pers) x d g tid ≡{n}≡ ty'.(ty_gho_pers) x d g tid) →
    (∀ x, ty.(ty_phys) x tid = ty'.(ty_phys) x tid) →
    uniq_body_pers_component ty x ξi d g idx κ tid l ≡{n}≡
      uniq_body_pers_component ty' x ξi d g idx κ tid l.
  Proof.
    intros Hg Hpers Hp. apply proph_idx_bor_ne=> c. by apply uniq_payload_ne.
  Qed.

  Lemma uniq_pers_component_contractive {𝔄} n (ty ty': type 𝔄) x ξi d g idx κ tid l :
    (∀ x d g, dist_later n (ty.(ty_gho_own) x d g tid) (ty'.(ty_gho_own) x d g tid)) →
    (∀ x d g, dist_later n (ty.(ty_gho_pers) x d g tid) (ty'.(ty_gho_pers) x d g tid)) →
    (∀ x, ty.(ty_phys) x tid = ty'.(ty_phys) x tid) →
    uniq_body_pers_component ty x ξi d g idx κ tid l ≡{n}≡
      uniq_body_pers_component ty' x ξi d g idx κ tid l.
  Proof.
    intros Hg Hpers Hp. apply proph_idx_bor_contractive=> c.
    destruct n as [|n]; [split; lia|]. apply dist_later_S.
    apply uniq_payload_ne; [| |done]=> x1 d1 g1.
    - have := Hg x1 d1 g1. by rewrite dist_later_S.
    - have := Hpers x1 d1 g1. by rewrite dist_later_S.
  Qed.

  Lemma uniq_pers_component_proper {𝔄} (ty ty': type 𝔄) x ξi d g idx κ tid tid' l :
    (∀ x d g, ty.(ty_gho_own) x d g tid ⊣⊢ ty'.(ty_gho_own) x d g tid') →
    (∀ x d g, ty.(ty_gho_pers) x d g tid ⊣⊢ ty'.(ty_gho_pers) x d g tid') →
    (∀ x, ty.(ty_phys) x tid = ty'.(ty_phys) x tid') →
    uniq_body_pers_component ty x ξi d g idx κ tid l ⊣⊢
      uniq_body_pers_component ty' x ξi d g idx κ tid' l.
  Proof.
    intros Hg Hpers Hp. apply proph_idx_bor_proper=> c. by apply uniq_payload_proper.
  Qed.

  Lemma uniq_body_from_parts {𝔄} (ty: type 𝔄) x ξi d g idx κ tid l :
    uniq_tok x ξi d g idx -∗ ⧗1 -∗ uniq_body_pers_component ty x ξi d g idx κ tid l -∗
    uniq_body ty x ξi d g idx κ tid l.
  Proof. rewrite uniq_body_unfold. iIntros "$ $ $". Qed.

  Lemma uniq_body_pers_component_impl {𝔄} (ty: type 𝔄) (x: ~~ 𝔄) (ξi: positive) (d: nat) (g: nat) (idx: Idx) (κ: lft) (tid: thread_id) (l: cloc)
    : uniq_body ty x ξi d g idx κ tid l -∗ uniq_body_pers_component ty x ξi d g idx κ tid l.
  Proof. rewrite uniq_body_unfold. iIntros "(_ & _ & $)". Qed.

  (** The prophecy variable of a unique borrow only depends on the current
      value through an inhabitedness proof; we can thus change it at will. *)
  Lemma uniq_ibor_retarget {𝔄} κ (x x': ~~ 𝔄) ξi c idx P :
    proph_ibor κ (uniq_prvar x ξi) c idx P ⊣⊢ proph_ibor κ (uniq_prvar x' ξi) c idx P.
  Proof.
    rewrite /uniq_prvar /uniq_cell_tyi.
    by rewrite (proof_irrel (@to_inh_syn_type (uniq_cellₛ 𝔄) (vπ x inhabitant, (1%positive, 1%positive)))
                           (@to_inh_syn_type (uniq_cellₛ 𝔄) (vπ x' inhabitant, (1%positive, 1%positive)))).
  Qed.

  Lemma uniq_idx_bor_retarget {𝔄} κ (x x': ~~ 𝔄) ξi idx P :
    proph_idx_bor κ (uniq_prvar x ξi) idx P ⊣⊢ proph_idx_bor κ (uniq_prvar x' ξi) idx P.
  Proof.
    rewrite /uniq_prvar /uniq_cell_tyi.
    by rewrite (proof_irrel (@to_inh_syn_type (uniq_cellₛ 𝔄) (vπ x inhabitant, (1%positive, 1%positive)))
                           (@to_inh_syn_type (uniq_cellₛ 𝔄) (vπ x' inhabitant, (1%positive, 1%positive)))).
  Qed.

  Lemma uniq_bor_tok_retarget {𝔄} (x x': ~~ 𝔄) ξi c idx :
    proph_bor_tok (uniq_prvar x ξi) c idx ⊣⊢ proph_bor_tok (uniq_prvar x' ξi) c idx.
  Proof.
    rewrite /uniq_prvar /uniq_cell_tyi.
    by rewrite (proof_irrel (@to_inh_syn_type (uniq_cellₛ 𝔄) (vπ x inhabitant, (1%positive, 1%positive)))
                           (@to_inh_syn_type (uniq_cellₛ 𝔄) (vπ x' inhabitant, (1%positive, 1%positive)))).
  Qed.

  Lemma uniq_pers_component_retarget {𝔄} (ty: type 𝔄) (x x': ~~ 𝔄) ξi d g d' g' idx κ tid l :
    uniq_body_pers_component ty x ξi d g idx κ tid l ⊣⊢
      uniq_body_pers_component ty x' ξi d' g' idx κ tid l.
  Proof. apply uniq_idx_bor_retarget. Qed.

  Lemma uniq_body_make {𝔄} (ty: type 𝔄) x x' ξi d g idx κ tid l :
    proph_ibor κ (uniq_prvar x' ξi) (uniq_cell x d g) idx (uniq_payload ty tid l) -∗ ⧗1 -∗
    uniq_body ty x ξi d g idx κ tid l.
  Proof. iIntros "B T". rewrite /uniq_body (uniq_ibor_retarget κ x x'). iFrame. Qed.

  Lemma uniq_body_proph_dep {𝔄} (x: ~~𝔄) d g :
    @vπ (uniq_cellₛ 𝔄) (uniq_cell x d g) ./ ξl x.
  Proof. apply uniq_cell_dep, syn_indep. Qed.

  (** ** Allocation *)

  Lemma alloc_uniq_body
      {𝔄} (ty: type 𝔄) (x: ~~ 𝔄) (d: nat) (g: nat)
      (κ: lft) (tid: thread_id) (l: cloc) E
   :
    (↑Nllft ∪ ↑prophN ∪ ↑uniqN ⊆ E) →
    ⊢ llft_ctx -∗
      proph_ctx -∗
      uniq_ctx -∗ ⧖(S d `max` g) -∗
      (▷ ty.(ty_gho_own) x d g tid) -∗
      l #↦!∗ ty.(ty_phys) x tid -∗
      ⧗1
      ={E}=∗
      ∃ ξi ζi idx,
        let ξ := uniq_prvar x ξi in
        let ζ := PrVar (at_locₛ 𝔄 ↾ prval_to_inh (@vπ (at_locₛ 𝔄) (l.1, x))) ζi in
        uniq_body ty x ξi d g idx κ tid l ∗
        ⟨π, π ζ = (l.1, (π ξ).1)⟩ ∗
        ([†κ] ={↑Nllft}=∗
           ▷ ∃ x' (d' g' : nat), ((λ π, (π ξ).1) :== vπ x') ∗ ⧖ (S d' `max` g') ∗
               |={lazyE}=> (ty_gho_own ty x' d' g' tid ∗ l #↦!∗ ty_phys ty x' tid)).
  Proof.
    intros Hmask. iIntros "#LFT #PROPH #UNIQ #⧖ gho pt £".
    iMod (proph_loan_intro (uniq_cell_tyi x) E (uniq_cell x d g) with "PROPH UNIQ")
      as (ξi) "Loan"; [set_solver|].
    set ξ := uniq_prvar x ξi.
    set ζ𝔄i := (at_locₛ 𝔄 ↾ prval_to_inh (@vπ (at_locₛ 𝔄) (l.1, x))).
    iMod (proph_intro ζ𝔄i ∅ with "PROPH") as (ζi) "[_ ζtok]"; [set_solver|].
    set ζ := PrVar ζ𝔄i ζi.
    iDestruct (proph_loan_tok with "Loan") as "[ξtok ToLoan]".
    iMod (proph_resolve_toks _ ζ (λ π, (l.1, (π ξ).1)) [ξ] with "PROPH ζtok [ξtok]")
      as "[ζObs ξtok]".
    { set_solver. }
    { apply (proph_dep_constr (λ a, (l.1, a.1)) (λ π, π ξ)). apply proph_dep_one. }
    { rewrite big_sepL_singleton. iFrame "ξtok". }
    rewrite big_sepL_singleton.
    iDestruct ("ToLoan" with "ξtok") as "Loan".
    iMod (proph_loan_borrow E κ ξ (uniq_cell x d g) (uniq_payload ty tid l)
      with "LFT PROPH Loan [gho pt]") as "[Bor Back]"; [set_solver| |].
    { iApply uniq_payload_intro_later. iNext. iFrame "∗#". }
    rewrite proph_bor_idx. iDestruct "Bor" as (idx) "Bor".
    iModIntro. iExists ξi, ζi, idx. iFrame "ζObs". iSplitL "Bor £".
    { rewrite /uniq_body. iFrame. }
    iIntros "†κ". iMod ("Back" with "†κ") as "Back". iModIntro. iNext.
    iDestruct "Back" as (c) "[Eqz Payload]".
    rewrite {2}(uniq_cell_surj c) uniq_payload_cell.
    iExists c.1, (dec_depth c.2.1), (dec_depth c.2.2).
    iDestruct "Payload" as "($ & $)".
    iApply (proph_eqz_fst_const (λ π, π ξ) (vπ c.1) c.2).
    iApply (proph_eqz_eq with "Eqz"); [done|].
    fun_ext=> π. destruct c as [? [??]]. done.
  Qed.

  (** ** Basically dead lifetimes *)

  (* Similar to [†κ] but we can apply the basically_dead_incl rule immediately instead of
     performing an update.
     TODO should this have been the definition of [†κ'] to begin with?
     It might simplify a lot but has the disadvantage of not being timeless. *)
  Definition basically_dead (κ: lft) : iProp Σ := ∃ κ' , κ ⊑ κ' ∗ [†κ'].

  Definition basically_dead_incl κ κ' :
    κ' ⊑ κ -∗ basically_dead κ -∗ basically_dead κ'.
  Proof.
    iIntros "#Incl bd". iDestruct "bd" as (κ'') "[#Incl2 #Dead]".
    iExists κ''. iFrame "Dead". iApply (guards_transitive with "Incl Incl2").
  Qed.

  Lemma basically_dead_alive_false κ (G: iProp Σ) E :
    ↑NllftG ⊆ E →
    (G &&{↑NllftG}&&> @[κ]) -∗ basically_dead κ -∗ G ={E}=∗ False.
  Proof.
    iIntros (?) "#Gk Dead G". iDestruct "Dead" as (κ') "[#Incl' #Dead']".
    iDestruct (guards_transitive with "Gk Incl'") as "G2".
    leaf_open "G2" with "G" as "[Alive _]"; [done|].
    iExFalso. iApply (llftl_not_own_end with "Alive Dead'").
  Qed.

  (** ** Resolution *)

  (** Resolving a unique borrow to its current value: freeze the borrow, share the
      payload with [ty_share], and get the prophecy tokens from the sharing predicate by
      [ty_shr_guard_proph]. The sharing predicate of the payload and a guard of its
      points-to remain, as well as the persistent predicate. The later credits come from
      the time receipts. *)
  Lemma resolve_uniq_body {𝔄} (ty: type 𝔄) x ξi d g idx κ tid l E L G F :
    Timeless G →
    lctx_lft_alive E L κ → ↑Nllft ∪ ↑prophN ∪ ↑timeN ∪ ↑uniqN ⊆ F →
    llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ time_ctx -∗ κ ⊑ ty_lft ty -∗ elctx_interp E -∗
    (G &&{↑NllftG}&&> llctx_interp L) -∗
    G -∗
    uniq_body ty x ξi d g idx κ tid l ={F}=∗
      ⟨π, (π (uniq_prvar x ξi)).1 = (vπ x π)⟩ ∗ G ∗
      ty.(ty_shr) κ x d g tid ∗ (@[κ] &&{↑NllftG; 1}&&> l #↦!∗ ty_phys ty x tid) ∗
      ty.(ty_gho_pers) x d g tid.
  Proof.
    intro Ti.
    iIntros (Alv ?) "#LFT #PROPH #UNIQ #TIME #In E #Guard G [Bor ⧗] /=".
    leaf_open "Guard" with "G" as "[L Back]". { solve_ndisj. }
    iDestruct (Alv with "L E") as "#Alv".
    iMod ("Back" with "L") as "G".
    iDestruct (guards_transitive with "Guard Alv") as "#Guard_K".
    iMod (proph_ibor_resolve_share F κ (uniq_prvar x ξi) (uniq_cell x d g) idx _ (ξl x)
      (ty.(ty_shr) κ x d g tid ∗ (@[κ] &&{↑NllftG; 1}&&> l #↦!∗ ty_phys ty x tid) ∗
        ty.(ty_gho_pers) x d g tid)%I G
      (0 + (d+1)*(g+1)) with "LFT PROPH UNIQ Guard_K [⧗] G Bor") as "(#Obs & $ & $)".
    { solve_ndisj. } { apply uniq_body_proph_dep. }
    { iIntros (W HW) "#Wκ W Bor". rewrite uniq_payload_cell.
      iMod (llftl_sep_split with "LFT Bor") as "[T Bor]"; [solve_ndisj|].
      iMod (llftl_bor_guarded_pers with "LFT Wκ W T") as "[W >#⧖]"; [solve_ndisj|].
      iMod (cumulative_persistent_time_receipt_get_credits with "TIME ⧗ ⧖") as "[_ £]";
        first by solve_ndisj.
      iDestruct (lc_weaken (1 + 1 + d + d*(g+2) + (0 + (d+1)*(g+1))) with "£") as "£".
      { unfold advance_credits. nia. }
      iDestruct "£" as "[[[[£f £1] £d] £k] $]".
      (* Run the lazy update of the payload inside the borrow. *)
      iMod (llftl_bor_fupd_guarded with "LFT Wκ W £f Bor") as "[Bor W]";
        [solve_ndisj|rewrite /lazyE; solve_ndisj|].
      iMod (llftl_sep_split with "LFT Bor") as "[Gho Pt]"; [solve_ndisj|].
      iMod (llftl_bor_guard with "LFT Pt") as "$"; [solve_ndisj|].
      (* The persistent predicate of the contents, for [ty_share]. *)
      iMod (llftl_bor_guarded_extract _ _ _ _ (ty.(ty_gho_pers) x d g tid)
        with "LFT Wκ W Gho []") as "(W & Gho & Pers)";
        [solve_ndisj| |].
      { iIntros "!> Gho". iApply (ty_gho_pers_impl with "Gho"). }
      iMod (lc_fupd_elim_later with "£1 Pers") as "#Pers'".
      iMod (ty_share with "LFT In Pers' Wκ W Gho") as "Upd"; [solve_ndisj|].
      iMod (lc_step_fupdN_elim_later with "£d Upd") as ">[$ #Shr]". iFrame "Shr Pers'".
      iAssert (▷^(d*(g+2)) (∀ ζ : proph_var, ⌜ζ ∈ ξl x⌝ -∗
          W &&{ ↑NllftG; 0 + (d+1)*(g+1) }&&> 1:[ζ]))%I as "#Hallζlater".
      { iIntros (ζ) "%HIn".
        iDestruct (ty_shr_guard_proph ty κ x 0 d g tid ζ W HIn with "LFT In Pers' Shr") as "X".
        iNext. iApply "X". by iApply lguards_weaken_later; [|iFrame "Wκ"]; lia. }
      iMod (lc_fupd_elim_laterN with "£k Hallζlater") as "#Hallζ".
      by iModIntro. }
    iModIntro. iApply (proph_obs_impl with "Obs")=> π ->. done.
  Qed.

  (** ** Changing the type and lifetime *)

  Lemma incl_uniq_body_pers_component {𝔄} (ty ty': type 𝔄) x ξi d g idx κ κ' tid l :
    κ' ⊑ κ -∗
    □ (∀x d tid vl, ty.(ty_gho_own) x d tid vl ↔ ty'.(ty_gho_own) x d tid vl) -∗
    □ (∀x d tid vl, ty.(ty_gho_pers) x d tid vl ↔ ty'.(ty_gho_pers) x d tid vl) -∗
    (∀x tid, ⌜ ty_phys ty x tid = ty_phys ty' x tid ⌝) -∗
    uniq_body_pers_component ty x ξi d g idx κ tid l -∗ uniq_body_pers_component ty' x ξi d g idx κ' tid l.
  Proof.
    iIntros "#InLft #EqOwn #EqPers %EqPhys Pc". unfold uniq_body_pers_component.
    iApply (proph_idx_bor_shorten with "InLft [] Pc").
    iIntros "!> !>" (c). rewrite /uniq_payload EqPhys.
    iSplit; iIntros "($ & Upd)"; iMod "Upd" as "[Gho $]"; by iApply "EqOwn".
  Qed.

  Lemma incl_uniq_body {𝔄} (ty ty': type 𝔄) x ξi d g idx κ κ' tid l :
    κ' ⊑ κ -∗
    □ (∀x d tid vl, ty.(ty_gho_own) x d tid vl ↔ ty'.(ty_gho_own) x d tid vl) -∗
    □ (∀x d tid vl, ty.(ty_gho_pers) x d tid vl ↔ ty'.(ty_gho_pers) x d tid vl) -∗
    (∀x tid, ⌜ ty_phys ty x tid = ty_phys ty' x tid ⌝) -∗
    uniq_body ty x ξi d g idx κ tid l -∗ uniq_body ty' x ξi d g idx κ' tid l.
  Proof.
    iIntros "#InLft #EqOwn #EqPers %EqPhys". rewrite !uniq_body_unfold.
    iIntros "($ & $ & Pc)".
    iApply (incl_uniq_body_pers_component ty ty' x ξi d g idx κ κ' tid l
      with "InLft EqOwn EqPers"); done.
  Qed.

  (** ** Guards *)

  (** From a guard on the token of a unique borrow, get a guard on the
      prophecy token of its variable. *)
  Lemma uniq_tok_guard_proph_tok {𝔄} (ty: type 𝔄) x ξi d g idx κ tid l R n :
    llft_ctx -∗
    uniq_body_pers_component ty x ξi d g idx κ tid l -∗
    (R &&{↑NllftG; n}&&> @[κ]) -∗
    (R &&{↑NllftG; n}&&> uniq_tok x ξi d g idx) -∗
    (R &&{↑NllftG; n+1}&&> 1:[uniq_prvar x ξi]).
  Proof.
    iIntros "#LFT #Bor #Gk #Gtok".
    iApply (proph_ibor_guard_tok with "LFT Bor Gk Gtok").
  Qed.

  (** ** Accessors *)

  (** Open a unique borrow, keeping the index; closing may change the value
      and the depth. The payload is lazy, and so is the closing payload. *)
  Lemma uniq_body_acc_lazy {𝔄} (ty: type 𝔄) x ξi d g idx κ tid l E G :
    Timeless G → ↑Nllft ⊆ E →
    llft_ctx -∗ uniq_ctx -∗ (G &&{↑NllftG}&&> @[κ]) -∗
    uniq_body ty x ξi d g idx κ tid l -∗ G ={E}=∗
      ▷ uniq_payload ty tid l (uniq_cell x d g) ∗ ⧗1 ∗
      (∀ x1 d1 g1, ▷ uniq_payload ty tid l (uniq_cell x1 d1 g1) -∗ ⧗1
        ={↑Nllft}=∗ uniq_body ty x1 ξi d1 g1 idx κ tid l ∗ G).
  Proof.
    iIntros (??) "#LFT #UNIQ #Gk [Bor ⧗] G".
    iMod (proph_ibor_acc with "LFT UNIQ Gk Bor G") as "[P Close]"; [done|].
    iModIntro. iFrame "P ⧗".
    iIntros (x1 d1 g1) "P ⧗".
    iMod ("Close" $! (uniq_cell x1 d1 g1) with "P") as "[Bor $]".
    iModIntro. iApply (uniq_body_make with "Bor ⧗").
  Qed.

  (** As [uniq_body_acc_lazy], closing with a non-lazy payload. *)
  Lemma uniq_body_acc {𝔄} (ty: type 𝔄) x ξi d g idx κ tid l E G :
    Timeless G → ↑Nllft ⊆ E →
    llft_ctx -∗ uniq_ctx -∗ (G &&{↑NllftG}&&> @[κ]) -∗
    uniq_body ty x ξi d g idx κ tid l -∗ G ={E}=∗
      ▷ (⧖(S d `max` g) ∗
         |={lazyE}=> (ty.(ty_gho_own) x d g tid ∗ l #↦!∗ ty.(ty_phys) x tid)) ∗ ⧗1 ∗
      (∀ x1 d1 g1, ▷ (⧖(S d1 `max` g1) ∗ ty.(ty_gho_own) x1 d1 g1 tid ∗ l #↦!∗ ty.(ty_phys) x1 tid) -∗ ⧗1
        ={↑Nllft}=∗ uniq_body ty x1 ξi d1 g1 idx κ tid l ∗ G).
  Proof.
    iIntros (??) "#LFT #UNIQ #Gk Body G".
    iMod (uniq_body_acc_lazy with "LFT UNIQ Gk Body G") as "(P & $ & Close)"; [done..|].
    iModIntro. rewrite uniq_payload_later_cell. iFrame "P".
    iIntros (x1 d1 g1) "P ⧗". iApply ("Close" with "[P] ⧗").
    by iApply uniq_payload_intro_later.
  Qed.

  (** As [uniq_body_acc], running the lazy update of the payload with a later
      credit. *)
  Lemma uniq_body_acc_forced {𝔄} (ty: type 𝔄) x ξi d g idx κ tid l E G :
    Timeless G → lazyE ⊆ E →
    llft_ctx -∗ uniq_ctx -∗ (G &&{↑NllftG}&&> @[κ]) -∗ £1 -∗
    uniq_body ty x ξi d g idx κ tid l -∗ G ={E}=∗
      ⧖(S d `max` g) ∗ ty.(ty_gho_own) x d g tid ∗ l #↦!∗ ty.(ty_phys) x tid ∗ ⧗1 ∗
      (∀ x1 d1 g1, ▷ (⧖(S d1 `max` g1) ∗ ty.(ty_gho_own) x1 d1 g1 tid ∗ l #↦!∗ ty.(ty_phys) x1 tid) -∗ ⧗1
        ={↑Nllft}=∗ uniq_body ty x1 ξi d1 g1 idx κ tid l ∗ G).
  Proof.
    iIntros (? HE) "#LFT #UNIQ #Gk £ Body G".
    have ?: ↑Nllft ⊆ E. { etrans; [|done]. rewrite /lazyE. set_solver. }
    iMod (uniq_body_acc_lazy with "LFT UNIQ Gk Body G") as "(P & $ & Close)"; [done..|].
    iMod (uniq_payload_force with "£ P") as "($ & $ & $)"; [done|].
    iModIntro. iIntros (x1 d1 g1) "P ⧗". iApply ("Close" with "[P] ⧗").
    by iApply uniq_payload_intro_later.
  Qed.

  (** Open a unique borrow and run the lazy update of its payload, closing it with the
      same value and depth; this needs no [uniq_ctx]. *)
  Lemma uniq_body_acc_keep {𝔄} (ty: type 𝔄) x ξi d g idx κ tid l E G :
    Timeless G → lazyE ⊆ E →
    llft_ctx -∗ (G &&{↑NllftG}&&> @[κ]) -∗ £1 -∗
    uniq_body ty x ξi d g idx κ tid l -∗ G ={E}=∗
      ⧖(S d `max` g) ∗ ty.(ty_gho_own) x d g tid ∗ l #↦!∗ ty.(ty_phys) x tid ∗
      (▷ (ty.(ty_gho_own) x d g tid ∗ l #↦!∗ ty.(ty_phys) x tid)
        ={↑Nllft}=∗ uniq_body ty x ξi d g idx κ tid l ∗ G).
  Proof.
    iIntros (? HE) "#LFT #Gk £ [Bor ⧗] G".
    have ?: ↑Nllft ⊆ E. { etrans; [|done]. rewrite /lazyE. set_solver. }
    iMod (proph_ibor_acc_keep with "LFT Gk Bor G") as "[P Close]"; [done..|].
    iMod (uniq_payload_force with "£ P") as "(#⧖ & $ & $)"; [done|]. iFrame "⧖".
    iModIntro. iIntros "P". iMod ("Close" with "[P]") as "[Bor $]".
    { iApply uniq_payload_intro_later. iNext. iFrame "∗#". }
    iModIntro. iFrame.
  Qed.

  Lemma uniq_body_mono_upd {𝔄} (ty: type 𝔄) (x: ~~ 𝔄) (ξi: positive) (d g d' g': nat) (idx: Idx) (κ: lft) (tid: thread_id) (l: cloc) E G :
    Timeless G →
    ↑Nllft ∪ ↑uniqN ⊆ E →
    d ≤ d' →
    g ≤ g' →
    llft_ctx -∗
    uniq_ctx -∗
    ⧖(S d' `max` g') -∗
    (G &&{↑NllftG}&&> @[κ]) -∗
    G -∗
    uniq_body ty x ξi d g idx κ tid l ={E}=∗
    G ∗ uniq_body ty x ξi d' g' idx κ tid l.
  Proof.
    iIntros (Gtimeless Hmask Hle1 Hle2) "#LFT #UNIQ #⧖ #guards G UniqBody".
    iMod (uniq_body_acc_lazy with "LFT UNIQ guards UniqBody G") as "(Inner & ⧗ & Back)";
        first by solve_ndisj.
    iMod (fupd_mask_subseteq (↑Nllft)) as "Upd"; [solve_ndisj|].
    iMod ("Back" with "[Inner] ⧗") as "[$ $]"; [|done].
    iNext. iApply (uniq_payload_map with "[] [] Inner").
    - iIntros "_". iFrame "⧖".
    - iIntros "[Gho $]". iModIntro.
      iDestruct (ty_gho_own_depth_mono with "Gho") as "[$ _]"; trivial.
  Qed.

  (** Open a unique borrow with a lifetime token, closing with a different
      payload. *)
  Lemma uniq_body_acc_rebody {𝔄} (ty: type 𝔄) x ξi d g idx κ tid l E
      (Q: ~~ (uniq_cellₛ 𝔄) → iProp Σ) :
    ↑Nllft ⊆ E →
    llft_ctx -∗ uniq_ctx -∗ @[κ] -∗
    uniq_body ty x ξi d g idx κ tid l ={E}=∗ ▷ ◇ (
      (⧖(S d `max` g) ∗
        |={lazyE}=> (ty.(ty_gho_own) x d g tid ∗ l #↦!∗ ty.(ty_phys) x tid)) ∗ ⧗1 ∗
      (∀ c1, ▷ Q c1 -∗
         ▷ (∀ c2, ▷ Q c2 ∗ [†κ] ={↑NllftUsr ∪ ↑NllftUsr2}=∗ ▷ uniq_payload ty tid l c2)
         ={↑Nllft}=∗
         ∃ idx', proph_ibor κ (uniq_prvar x ξi) c1 idx' Q ∗ @[κ])).
  Proof.
    iIntros (?) "#LFT #UNIQ κ [Bor ⧗]".
    iMod (proph_ibor_acc_rebody E κ (uniq_prvar x ξi) _ _ _ Q with "LFT UNIQ κ Bor") as "Acc"; [done|].
    iModIntro. iNext. iMod "Acc" as "[P Close]". iModIntro.
    rewrite uniq_payload_cell. iFrame.
  Qed.

  (** ** Transforming the payload *)

  (** Replace a unique borrow by a fresh one at another type and location, given a way
      to transform the payloads in both directions. The old prophecy variable is
      resolved to [f] of the new one. *)
  Lemma uniq_body_transform_gen {𝔄 𝔅} (ty: type 𝔄) (ty': type 𝔅) x x' d g ξi ξidx κ tid l l' E G
    (f: 𝔅 →ₛ 𝔄) (h: nat → nat → nat * nat)
    :
      Timeless G →
      Inj eq eq ((!ₛ) f) →
      ↑Nllft ∪ ↑prophN ∪ ↑uniqN ⊆ E →
      llft_ctx -∗
      proph_ctx -∗
      uniq_ctx -∗
      (▷ uniq_payload ty tid l (uniq_cell x d g) ={E}=∗
        ▷ uniq_payload ty' tid l' (uniq_cell x' d g) ∗
        (∀ x'1 d1 g1, ▷ uniq_payload ty' tid l' (uniq_cell x'1 d1 g1)
          ={↑NllftUsr ∪ ↑NllftUsr2}=∗
            ▷ uniq_payload ty tid l (uniq_cell (f ~~$ₛ x'1) (h d1 g1).1 (h d1 g1).2))
        ) -∗
      (G &&{↑NllftG}&&> @[κ]) -∗
      G -∗
      uniq_body ty x ξi d g ξidx κ tid l
      ={E}=∗ ∃ ζi ζidx ,
      ⟨π, (π (uniq_prvar x ξi)).1 = (!ₛ) f ((π (uniq_prvar x' ζi)).1)⟩ ∗
      uniq_body ty' x' ζi d g ζidx κ tid l' ∗ G.
  Proof.
    intros Htimeless Hinj Hmask. iIntros "#LFT #PROPH #UNIQ wand #GuardsK G [Bor ⧗]".
    iMod (proph_loan_intro (uniq_cell_tyi x') E (uniq_cell x' d g) with "PROPH UNIQ")
      as (ζi) "Loan"; [set_solver|].
    set fv := λ (c: ~~ (uniq_cellₛ 𝔅)),
      uniq_cell (f ~~$ₛ c.1) (h (dec_depth c.2.1) (dec_depth c.2.2)).1
                             (h (dec_depth c.2.1) (dec_depth c.2.2)).2.
    set fp := λ (c: (uniq_cellₛ 𝔅)),
      ((!ₛ) f c.1, (enc_depth (h (dec_depth c.2.1) (dec_depth c.2.2)).1,
                   enc_depth (h (dec_depth c.2.1) (dec_depth c.2.2)).2)).
    iMod (proph_ibor_map E κ (uniq_prvar x ξi) (uniq_cell x d g) ξidx (uniq_payload ty tid l)
      (uniq_prvar x' ζi) (uniq_cell x' d g) (uniq_payload ty' tid l') fv fp G
      with "LFT PROPH UNIQ GuardsK [wand] G Loan Bor") as "(#Obs & Bor' & G)".
    { solve_ndisj. }
    { intros [c [p1 p2]] π. rewrite /fv /fp /=. f_equal.
      by rewrite syn_type_morphism_commutes. }
    { intros [c [p1 p2]] ζl Dep. apply uniq_cell_dep_rev. simpl.
      apply (proph_dep_destr ((!ₛ) f)).
      set k := (enc_depth (h (dec_depth p1) (dec_depth p2)).1,
                enc_depth (h (dec_depth p1) (dec_depth p2)).2).
      have Hi: Inj (=) (=) (λ a: 𝔄, (a, k)) by intros ?? [=].
      by apply (proph_dep_destr (λ a: 𝔄, (a, k))). }
    { iIntros "Payload". iMod ("wand" with "Payload") as "[$ Back]". iModIntro.
      iIntros ([c1 [p1 p2]]) "Payload".
      iMod ("Back" $! c1 (dec_depth p1) (dec_depth p2) with "[Payload]") as "P".
      { by rewrite /uniq_cell !enc_dec_depth. }
      by rewrite /fv /=. }
    iDestruct "Bor'" as (ζidx) "Bor'".
    iModIntro. iExists ζi, ζidx. iFrame "G".
    iSplitR.
    { iApply (proph_obs_impl with "Obs")=> π ->. done. }
    rewrite /uniq_body. iFrame.
  Qed.

  (** [uniq_body_transform_gen] where the old payload is forced with a later credit,
      so that the transformation gets the old contents. The transformation back is
      split into a non-lazy part for the time receipt, and a part that is run inside
      the lazy update of the new payload. *)
  Lemma uniq_body_transform {𝔄 𝔅} (ty: type 𝔄) (ty': type 𝔅) x x' d g ξi ξidx κ tid l l' E G
    (f: 𝔅 →ₛ 𝔄) (h: nat → nat → nat * nat)
    :
      Timeless G →
      Inj eq eq ((!ₛ) f) →
      ↑Nllft ∪ ↑prophN ∪ ↑uniqN ⊆ E →
      llft_ctx -∗
      proph_ctx -∗
      uniq_ctx -∗
      (▷ ty_gho_own ty x d g tid ∗ l #↦!∗ ty_phys ty x tid
        ={E}=∗ ▷ ty_gho_own ty' x' d g tid ∗ l' #↦!∗ ty_phys ty' x' tid ∗
        (∀ x'1 d1 g1, ⧖(S d1 `max` g1) ={↑NllftUsr ∪ ↑NllftUsr2}=∗
          ⧖(S (h d1 g1).1 `max` (h d1 g1).2) ∗
          (ty_gho_own ty' x'1 d1 g1 tid ∗ l' #↦!∗ ty_phys ty' x'1 tid ={lazyE}=∗
            ty_gho_own ty (f ~~$ₛ x'1) (h d1 g1).1 (h d1 g1).2 tid ∗
            l #↦!∗ ty_phys ty (f ~~$ₛ x'1) tid))
        ) -∗
      (G &&{↑NllftG}&&> @[κ]) -∗
      G -∗
      £1 -∗
      uniq_body ty x ξi d g ξidx κ tid l
      ={E}=∗ ∃ ζi ζidx ,
      ⟨π, (π (uniq_prvar x ξi)).1 = (!ₛ) f ((π (uniq_prvar x' ζi)).1)⟩ ∗
      uniq_body ty' x' ζi d g ζidx κ tid l' ∗ G.
  Proof.
    intros Htimeless Hinj Hmask. iIntros "#LFT #PROPH #UNIQ wand #GuardsK G £ Body".
    iApply (uniq_body_transform_gen with "LFT PROPH UNIQ [wand £] GuardsK G Body"); [done..|].
    iIntros "P". iMod (uniq_payload_force with "£ P") as "(#⧖ & Gho & Pt)"; [done|].
    iMod ("wand" with "[$Gho $Pt]") as "(Gho' & Pt' & Back)".
    iModIntro. iSplitL "Gho' Pt'".
    { iApply uniq_payload_intro_later. iNext. iFrame "∗#". }
    iIntros (x'1 d1 g1) "P". rewrite uniq_payload_later_cell.
    iDestruct "P" as "(>#⧖1 & Upd)".
    iMod ("Back" with "⧖1") as "(#⧖2 & BackGho)".
    iModIntro. iNext. rewrite uniq_payload_cell. iFrame "⧖2".
    iMod "Upd". by iApply "BackGho".
  Qed.

  (** [uniq_body_transform_gen] where the transformations do not change the depth and
      are run lazily; this needs no later credit. *)
  Lemma uniq_body_transform_lazy {𝔄 𝔅} (ty: type 𝔄) (ty': type 𝔅) x x' d g ξi ξidx κ tid l l' E G
    (f: 𝔅 →ₛ 𝔄)
    :
      Timeless G →
      Inj eq eq ((!ₛ) f) →
      ↑Nllft ∪ ↑prophN ∪ ↑uniqN ⊆ E →
      llft_ctx -∗
      proph_ctx -∗
      uniq_ctx -∗
      (ty_gho_own ty x d g tid ∗ l #↦!∗ ty_phys ty x tid ={lazyE}=∗
        ty_gho_own ty' x' d g tid ∗ l' #↦!∗ ty_phys ty' x' tid) -∗
      (∀ x'1 d1 g1, ty_gho_own ty' x'1 d1 g1 tid ∗ l' #↦!∗ ty_phys ty' x'1 tid ={lazyE}=∗
        ty_gho_own ty (f ~~$ₛ x'1) d1 g1 tid ∗ l #↦!∗ ty_phys ty (f ~~$ₛ x'1) tid) -∗
      (G &&{↑NllftG}&&> @[κ]) -∗
      G -∗
      uniq_body ty x ξi d g ξidx κ tid l
      ={E}=∗ ∃ ζi ζidx ,
      ⟨π, (π (uniq_prvar x ξi)).1 = (!ₛ) f ((π (uniq_prvar x' ζi)).1)⟩ ∗
      uniq_body ty' x' ζi d g ζidx κ tid l' ∗ G.
  Proof.
    intros Htimeless Hinj Hmask.
    iIntros "#LFT #PROPH #UNIQ FwGho BkGho #GuardsK G Body".
    iApply (uniq_body_transform_gen _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (λ d g, (d, g))
      with "LFT PROPH UNIQ [FwGho BkGho] GuardsK G Body"); [done..|].
    iIntros "P". iModIntro. iSplitL "FwGho P".
    { iNext. iApply (uniq_payload_map with "[] FwGho P"). by iIntros "$". }
    iIntros (x'1 d1 g1) "P". iModIntro. iNext.
    iApply (uniq_payload_map with "[] BkGho P"). by iIntros "$".
  Qed.

  (** ** Reborrowing *)

  Lemma uniq_body_reborrow {𝔄} (ty: type 𝔄) x ξi d g idx κ κ' tid l E :
    ↑Nllft ∪ ↑prophN ∪ ↑uniqN ⊆ E →
    llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ κ' ⊑ κ -∗ ⧗1 -∗
    ⧖(S d `max` g) -∗
    uniq_body ty x ξi d g idx κ tid l ={E}=∗ ∃ ζi idx',
      uniq_body ty x ζi d g idx' κ' tid l ∗
      ([†κ'] ={↑Nllft}=∗ ∃ x' d' g' idx'', uniq_body ty x' ξi d' g' idx'' κ tid l ∗
          ▷ ((λ π, (π (uniq_prvar x ζi)).1) :== vπ x') ∗
          ▷ ⧖(S d' `max` g')).
  Proof.
    iIntros (?) "#LFT #PROPH #UNIQ #κ'⊑κ ⧗ #⧖ [Bor ⧗o]".
    iMod (proph_loan_intro (uniq_cell_tyi x) E (uniq_cell x d g) with "PROPH UNIQ")
      as (ζi) "Loan"; [set_solver|].
    (* The summary of the final value is only its time receipt. *)
    set R := λ (c: ~~ (uniq_cellₛ 𝔄)),
      ⧖(S (dec_depth c.2.1) `max` dec_depth c.2.2)%I.
    have HR: ∀ c, Persistent (R c) by intros c; apply _.
    have Hm: ↑Nllft ⊆ E by solve_ndisj.
    iMod (proph_ibor_reborrow E κ κ' (uniq_prvar x ξi) (uniq_cell x d g) idx
      (uniq_payload ty tid l) R ζi HR Hm with "LFT PROPH UNIQ κ'⊑κ [] [] Loan Bor")
      as "[Bor' Inh]".
    { iIntros "!>" (c) "(#⧖' & _)". iFrame "⧖'". }
    { rewrite /R /= !dec_enc_depth. iFrame "#". }
    iDestruct "Bor'" as (idx') "Bor'".
    iModIntro. iExists ζi, idx'. iSplitL "Bor' ⧗".
    { rewrite /uniq_body. iFrame. }
    iIntros "†κ'". iMod ("Inh" with "†κ'") as (c idx'') "(Bor & #R & Eqz)".
    iModIntro. iExists c.1, (dec_depth c.2.1), (dec_depth c.2.2), idx''.
    iSplitL "Bor ⧗o".
    { iApply (uniq_body_make with "[Bor] ⧗o"). by rewrite -uniq_cell_surj. }
    iSplitL "Eqz".
    { iNext. iApply (proph_eqz_fst_const (λ π, π (uniq_prvar x ζi)) (vπ c.1) c.2).
      iApply (proph_eqz_eq with "Eqz"); [done|].
      fun_ext=> π. destruct c as [? [??]]. done. }
    iFrame "R".
  Qed.

  (* Verus: probably not needed *)
  Lemma split_mt_uniq_bor l' P Φ Ψ :
    (l' ↦∗: (λ vl, P ∗ [loc[l] := vl]
      ∃(d: nat) (ξi: positive), ⌜Ψ d ξi⌝ ∗ Φ l d ξi)) ⊣⊢
    P ∗ ∃(l: loc) d ξi, ⌜Ψ d ξi⌝ ∗ l' ↦ #l ∗ Φ l d ξi.
  Proof.
    iSplit.
    - iDestruct 1 as ([|[[]|][]]) "(↦ &$& big)"=>//. iDestruct "big" as (???) "?".
      iExists _, _, _. rewrite heap_mapsto_vec_singleton. by iFrame.
    - iIntros "($&%&%&%&%& ↦ &?)". iExists [_]. rewrite heap_mapsto_vec_singleton.
      iFrame "↦". iExists _, _. by iFrame.
  Qed.
End uniq_util.
