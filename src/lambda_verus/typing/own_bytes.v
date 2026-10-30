From lrust.typing Require Export type.
From lrust.typing Require Import freeable_util.
From lrust.util Require Export non_atomic_cell_map.
From guarding Require Import guard tactics.
From lrust.lifetime Require Import lifetime_full.
Set Default Proof Using "Type".

(** * Owning pointers to bytes (stage 3 of the MiniRust memory model)

[own_bytes n ty] is an owning pointer whose pointee lives in the byte region of the
heap (see [lang/heap.v]): it owns bytes [bs] that represent the value of the pointee
([ty_bytes ty x bs]: they have the size [ty_bsize ty] and decode to [ty_val ty x] at
[ty_mty ty]), and the freeable token of the [ty_bsize ty] bytes of a block of [n]
bytes. This is the target form of [own_ptr] (see [design_docs/minirust-memory-model.md],
"Outcome: stage 3"): [own_ptr] itself still owns legacy words ([l ↦!∗ ty_phys x]),
because the place machinery reads and writes its leaves with the legacy one-word
operations until stage 4.

The pointee is read and written with the typed [Load] and [Store] of [ty_mty ty]:
[wp_own_bytes_load], [wp_own_bytes_store], [wp_own_bytes_new] and
[wp_own_bytes_delete]. *)

Implicit Type 𝔄 𝔅: syn_type.

Section own_bytes.
  Context `{!typeG Σ}.

  (** The bytes at [l] represent [x]. *)
  Definition bytes_own {𝔄} (ty: type 𝔄) (l: loc) (x: ~~𝔄) : iProp Σ :=
    ∃ bs, l ↦b bs ∗ ⌜ty_bytes ty x bs⌝.

  Global Instance bytes_own_timeless {𝔄} (ty: type 𝔄) l x : Timeless (bytes_own ty l x).
  Proof. apply _. Qed.

  Lemma bytes_own_same {𝔄} (ty ty': type 𝔄) l x : bytes_own ty l x ⊣⊢ bytes_own ty' l x.
  Proof. rewrite /bytes_own. by setoid_rewrite (ty_bytes_same ty ty'). Qed.

  (** The sharing predicate is structural, as for [own_ptr]: a guard of the bytes and
      the sharing predicate of the contents, under one later. *)
  Program Definition own_bytes {𝔄} (n: nat) (ty: type 𝔄) : type (at_locₛ 𝔄) := {|
    ty_size := 1;
    ty_lfts := ty.(ty_lfts);
    ty_E := ty.(ty_E);
    ty_gho_own x d g tid := [S(d') := d]
      bytes_own ty x.1 x.2 ∗ freeable_sz n (ty_bsize ty) x.1 ∗
      ▷ ty.(ty_gho_own) x.2 d' g tid;
    ty_gho_res x d g tid := [S(d') := d]
      bytes_own ty x.1 x.2 ∗ freeable_sz n (ty_bsize ty) x.1 ∗
      ▷ ty.(ty_gho_res) x.2 d' g tid;
    ty_gho_pers x d g tid := [S(d') := d] ▷ ty.(ty_gho_pers) x.2 d' g tid;
    ty_mty := syn_mty _; ty_val := syn_val; ty_mty_eq := eq_refl; ty_val_eq _ := eq_refl;
    ty_phys x tid := [FVal (LitV x.1)];
    ty_shr κ x d g tid :=
      ▷ [S(d') := d]
        (@[κ] &&{↑NllftG; g+1}&&> bytes_own ty x.1 x.2) ∗ ty.(ty_shr) κ x.2 d' g tid;
  |}%I.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation.
    move=> 𝔄 n ty [|d] g d' g' x tid ??; iIntros "H" => //=.
    iDestruct "H" as "(Hown & Hfree & Hgho)". destruct d'; first lia => /=.
    iDestruct (ty.(ty_gho_own_depth_mono) with "Hgho") as "[$ Hwand]" => //; first lia.
    iFrame. iIntros "($ & $ & Hgho)". by iApply "Hwand".
  Qed.
  Next Obligation.
    move=> 𝔄 n ty [|d] g d' g' x tid ??; iIntros "H" => //=.
    destruct d'; first lia => /=.
    iDestruct (ty.(ty_gho_pers_depth_mono) with "H") as "$" => //; first lia.
  Qed.
  Next Obligation.
    intros 𝔄 n ty x d g tid. iIntros "A". destruct d as [|d']; first by done.
    iDestruct "A" as "[_ [_ pers]]". iApply ty_gho_pers_impl. iFrame.
  Qed.
  Next Obligation.
    intros 𝔄 n ty κ κ' x m d g tid. iIntros "#Incl Shr".
    iNext. destruct d as [|d']; [done|]. iDestruct "Shr" as "[Pt Shr]". iSplit.
    - replace (g + m + 1) with (m + (g + 1)) by lia.
      iApply (guards_transitive_additive with "Incl Pt").
    - iApply (ty_shr_lft_mono with "Incl Shr").
  Qed.
  Next Obligation.
    intros 𝔄 n ty κ d g d' g' x tid ??. iIntros "Shr".
    iNext. destruct d as [|d0]; [done|]. destruct d' as [|d0']; [lia|].
    iDestruct "Shr" as "[Pt Shr]". iSplit.
    - leaf_goal laters to (g+1). { lia. } iFrame "Pt".
    - iApply (ty_shr_depth_mono with "Shr"); lia.
  Qed.
  Next Obligation.
    intros 𝔄 n ty E κ x d g tid G ??. iIntros "#LFT #Incl #Pers #Gκ G Bor".
    destruct d as [|d']; [done|]. simpl.
    iMod (llftl_sep_split with "LFT Bor") as "[Pt Bor]"; [solve_ndisj|].
    iMod (llftl_sep_split with "LFT Bor") as "[_ Bor]"; [solve_ndisj|].
    iMod (llftl_bor_guard with "LFT Pt") as "#Pt"; [solve_ndisj|].
    iMod (llftl_bor_later_step with "LFT Gκ G Bor") as "Upd"; [first [apply _ | solve_ndisj]..|].
    iModIntro. iModIntro. iNext. iMod "Upd" as "[G Bor]".
    iMod (ty_share with "LFT Incl Pers Gκ G Bor") as "Shr"; [done..|].
    iModIntro. iApply (step_fupdN_wand with "Shr"). iIntros ">[$ Shr] !> !>".
    iFrame "Shr". leaf_goal laters to 1. { lia. } iFrame "Pt".
  Qed.
  Next Obligation.
    intros 𝔄 n ty κ x n0 d g tid ξ R Hin.
    iIntros "#LFT #Incl #Pers #Shr".
    destruct d as [|d']; first by done. simpl.
    iApply (bi.laterN_le (S (d' * (g + 2)))). { lia. }
    iNext. iDestruct "Shr" as "[_ Shr]".
    iDestruct (ty_shr_guard_proph ty κ x.2 n0 d' g tid ξ R Hin with "LFT Incl Pers Shr")
      as "GP".
    iNext. iIntros "#Rκ".
    leaf_goal laters to (n0 + (d'+1)*(g+1)). { lia. } by iApply "GP".
  Qed.
  Next Obligation.
    intros 𝔄 n ty x [|d] g tid; [by iIntros|]. iIntros "($ & $ & A)".
    iNext. by iApply ty_gho_res_of_own.
  Qed.

  Global Instance own_bytes_ne {𝔄} n : NonExpansive (@own_bytes 𝔄 n).
  Proof.
    move=> m ty ty' Eqv. split=>/=; [done|apply Eqv|apply Eqv| | |done|].
    - move=> [l x] [|d] g tid //=. rewrite /ty_bsize (ty_mty_same ty ty') (bytes_own_same ty ty').
      do 3 f_equiv. apply Eqv.
    - move=> [l x] [|d] g tid //=. do 2 f_equiv. apply Eqv.
    - move=> κ [l x] d g tid. f_equiv. destruct d; [done|]. simpl.
      rewrite (bytes_own_same ty ty'). f_equiv. apply Eqv.
  Qed.
End own_bytes.

Section own_bytes_rules.
  Context `{!typeG Σ}.

  Lemma own_bytes_gho_intro {𝔄} n (ty: type 𝔄) l x d g tid :
    bytes_own ty l x -∗ freeable_sz n (ty_bsize ty) l -∗ ▷ ty.(ty_gho_own) x d g tid -∗
    (own_bytes n ty).(ty_gho_own) (l, x) (S d) g tid.
  Proof. iIntros "$ $ $". Qed.

  (** Reading the pointee: a typed [Load] of [ty_mty ty] returns the value of [x]. *)
  Lemma wp_own_bytes_load {𝔄} n (ty: type 𝔄) l x v d g tid E :
    ty.(ty_val) x = Some v →
    {{{ (own_bytes n ty).(ty_gho_own) (l, x) d g tid }}}
      Load Na1Ord ty.(ty_mty) #l @ E
    {{{ RET MLitV v; (own_bytes n ty).(ty_gho_own) (l, x) d g tid }}}.
  Proof.
    iIntros (Hv Φ) "Own HΦ". destruct d as [|d]; [done|].
    iDestruct "Own" as "((%bs & Hbs & %Hbs) & Free & Gho)".
    iApply (wp_load_na with "Hbs"); [by eapply ty_bytes_decode|].
    iIntros "!> Hbs". iApply "HΦ". iFrame. by iPureIntro.
  Qed.

  (** Writing the pointee: a typed [Store] of the value of [y] replaces [x] by [y];
      the ownership of [x] is given back. *)
  Lemma wp_own_bytes_store {𝔄} n (ty: type 𝔄) l x y v d g tid E :
    ↑naN ⊆ E → ty.(ty_val) y = Some v →
    {{{ (own_bytes n ty).(ty_gho_own) (l, x) (S d) g tid ∗ ▷ ty.(ty_gho_own) y d g tid }}}
      Store Na1Ord ty.(ty_mty) #l (MLit v) @ E
    {{{ RET #☠; (own_bytes n ty).(ty_gho_own) (l, y) (S d) g tid ∗
                ▷ ty.(ty_gho_own) x d g tid }}}.
  Proof.
    iIntros (? Hv Φ) "[Own Gho'] HΦ".
    iDestruct "Own" as "((%bs & Hbs & %Hbs) & Free & Gho)". destruct Hbs as [Hlen _].
    iApply (wp_store_na with "Hbs"); [done|by eapply ty_val_wf|done|].
    iIntros "!> Hbs". iApply "HΦ". iFrame. iPureIntro. by apply ty_bytes_encode.
  Qed.

  (** Allocating a box and initialising it with a typed [Store]. *)
  Lemma wp_own_bytes_new {𝔄} (ty: type 𝔄) x v d g tid E :
    ↑naN ⊆ E → ty.(ty_val) x = Some v → (0 < ty_bsize ty)%nat →
    {{{ ▷ ty.(ty_gho_own) x d g tid }}}
      let: "l" := Alloc #(ty_bsize ty) in Store Na1Ord ty.(ty_mty) "l" (MLit v) ;; "l" @ E
    {{{ l, RET #l; (own_bytes (ty_bsize ty) ty).(ty_gho_own) (l, x) (S d) g tid }}}.
  Proof.
    iIntros (? Hv Hsz Φ) "Gho HΦ".
    wp_apply (wp_alloc_bytes with "[//]"); [rewrite /ty_bsize in Hsz; lia|]. iIntros (l sz) "(%Hn & Free & Hbs)".
    have ? : sz = mty_size (ty_mty ty) by lia. subst sz. wp_let.
    wp_bind (Store _ _ _ _). iApply (wp_store_na with "Hbs"); [done|by eapply ty_val_wf| |].
    { by rewrite length_replicate. }
    iIntros "!> Hbs". wp_seq. iApply "HΦ". iFrame "Gho". iSplitL "Hbs".
    - iExists _. iFrame. iPureIntro. by apply ty_bytes_encode.
    - rewrite freeable_sz_full. by iLeft.
  Qed.

  (** Deallocating a box; the ownership of its contents is given back. *)
  Lemma wp_own_bytes_delete {𝔄} (ty: type 𝔄) l x d g tid E :
    ↑naN ⊆ E → (0 < ty_bsize ty)%nat →
    {{{ (own_bytes (ty_bsize ty) ty).(ty_gho_own) (l, x) (S d) g tid }}}
      Free #(ty_bsize ty) #l @ E
    {{{ RET #☠; ▷ ty.(ty_gho_own) x d g tid }}}.
  Proof.
    iIntros (? Hsz Φ) "((%bs & Hbs & %Hbs) & Free & Gho) HΦ". destruct Hbs as [Hlen _].
    rewrite freeable_sz_full. iDestruct "Free" as "[Free|%Hz]".
    - iApply (wp_free_bytes with "[$Hbs Free]"); [done|by rewrite Hlen|by rewrite Hlen|].
      iIntros "!> _". by iApply "HΦ".
    - lia.
  Qed.
End own_bytes_rules.
