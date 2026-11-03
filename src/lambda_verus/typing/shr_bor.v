From lrust.typing Require Export type.
From lrust.typing Require Import programs lft_contexts own value_ctx.
From lrust.lifetime Require Import lifetime_full.
From guarding Require Import guard tactics.
Set Default Proof Using "Type".

(** * Shared references to bytes (stage 4 of the MiniRust memory model)

[&shr{κ} ty] is the byte form of [&shr{κ} ty]: its ownership is a guard, by [@[κ]], of
bytes at the referent that represent its value ([bytes_own ty l x]: fancy bytes, so the
referent may embed cells; for a type without cells they are plain, [shr_bytes_own_nocell]),
together with the
sharing predicate of [ty] at [κ] and its persistent predicate. A reader loads the bytes
with the guarded byte load [wp_load_na_guarded_gen] ([wp_shr_bytes_load]): the bytes
are only known inside the guard, but all of them decode to the value of [x].
As for [&shr], its sharing predicate is the default one. *)

Implicit Type 𝔄 𝔅: syn_type.

Section shr_bytes.
  Context `{!typeG Σ}.

  (** The bytes at [l] represent [x], under a guard of [@[κ]] with [n] laters. *)
  Definition shr_bytes_own {𝔄} (κ: lft) (n: nat) (ty: type 𝔄) (l: loc) (x: ~~𝔄) : iProp Σ :=
    @[κ] &&{↑NllftG; n}&&> bytes_own ty l x.

  Global Instance shr_bytes_own_persistent {𝔄} κ n (ty: type 𝔄) l x :
    Persistent (shr_bytes_own κ n ty l x).
  Proof. apply _. Qed.

  Lemma shr_bytes_own_same {𝔄} κ n (ty ty': type 𝔄) l x :
    shr_bytes_own κ n ty l x ⊣⊢ shr_bytes_own κ n ty' l x.
  Proof. by rewrite /shr_bytes_own (bytes_own_same ty ty'). Qed.

  (** The reduction lemma: for a type without cells, the referent is plain bytes. *)
  Lemma shr_bytes_own_nocell {𝔄} `{!NoCell 𝔄} κ n (ty: type 𝔄) l x :
    shr_bytes_own κ n ty l x ⊣⊢ (@[κ] &&{↑NllftG; n}&&> ∃ bs, l ↦b bs ∗ ⌜ty_bytes ty x bs⌝).
  Proof. by rewrite /shr_bytes_own bytes_own_nocell. Qed.

  (** A zero-sized value with a MiniRust value: its bytes are trivially owned, so the
      reference can be at any location. *)
  Lemma shr_bytes_own_zst {𝔄} κ n (ty: type 𝔄) l x :
    ty_bsize ty = 0 → is_Some (ty.(ty_val) x) → ⊢ shr_bytes_own κ n ty l x.
  Proof.
    intros. rewrite /shr_bytes_own bytes_own_zst_true //. iApply guards_true.
  Qed.

  Lemma shr_bytes_own_mono {𝔄} κ n n' (ty: type 𝔄) l x :
    n ≤ n' → shr_bytes_own κ n ty l x -∗ shr_bytes_own κ n' ty l x.
  Proof.
    iIntros (?) "G". by iApply (lguards_weaken_later with "G").
  Qed.

  Lemma shr_bytes_own_lft {𝔄} κ κ' n m (ty: type 𝔄) l x :
    (@[κ'] &&{↑NllftG; m}&&> @[κ]) -∗ shr_bytes_own κ n ty l x -∗ shr_bytes_own κ' (m + n) ty l x.
  Proof.
    iIntros "#Incl #G". iApply (guards_transitive_additive with "Incl G").
  Qed.

  Program Definition shr_bytes {𝔄} (κ: lft) (ty: type 𝔄) : type (at_locₛ 𝔄) :=
    @ty_of_st _ _ ((at_locₛ 𝔄)) ({|
    st_lfts := κ :: ty.(ty_lfts);
    st_E := ty.(ty_E) ++ ty_outlives_E ty κ;
    st_gho x d g tid := [S(d') := d]
      shr_bytes_own κ (g+1) ty x.1 x.2 ∗
      ty.(ty_shr) κ (snd x) d' g tid ∗
      ▷^(g+1) (ty.(ty_gho_pers) (snd x) d' g tid);
  |}%I : simple_type (at_locₛ 𝔄)).
  Next Obligation.
    intros. iIntros "#A". destruct d. { done. } unfold by_succ.
    destruct d'. { lia. }
    iDestruct "A" as "[Pt [Shr #Pers]]". iSplit.
    { iApply (shr_bytes_own_mono with "Pt"). lia. }
    iSplit.
    { iApply ty_shr_depth_mono; last by iFrame "Shr". { lia. } { lia. } }
    iApply (bi.laterN_le (g+1) (g'+1)); first by lia. iNext.
    iApply ty_gho_pers_depth_mono; last by iFrame "Pers".
    { lia. } { trivial. }
  Qed.
  Next Obligation.
    intros 𝔄 κ ty κ0 x n d g tid ξ R Hin.
    iIntros "LFT #Incl #Gho".
    destruct d as [|d]; [done|]. rewrite /by_succ.
    iDestruct "Gho" as "[Phys [Shr #InnerPers]]".
    iDestruct (ty_shr_lft_mono0 ty κ κ0 with "[] Shr") as "#Shr0".
    { iApply (llftl_incl_trans with "Incl []"). iApply llftl_intersect_incl_l. }
    iApply (bi.laterN_le (g + 1 + d * (g + 2))); [nia|].
    rewrite (bi.laterN_add (g + 1) (d * (g + 2))). iNext (g + 1).
    iDestruct (ty_shr_guard_proph ty κ0 (snd x) n d g tid ξ R with "LFT [] InnerPers Shr0")
      as "InnerGuardProph"; [done| |].
    { iApply (llftl_incl_trans with "Incl []"). iApply llftl_intersect_incl_r. }
    iNext. iIntros "#Rk #Rg".
    leaf_goal laters to (n + (d + 1) * (g + 1)). { lia. }
    iApply ("InnerGuardProph" with "Rk").
  Qed.

  Global Instance shr_bytes_ne {𝔄} κ : NonExpansive (@shr_bytes 𝔄 κ).
  Proof.
    move=> n ty ty' Eqv. apply ty_of_st_ne. constructor; simpl.
    - f_equal. by eapply ty_lfts_ne.
    - f_equal; [by eapply ty_E_ne|by eapply ty_outlives_E_ne].
    - move=> [l x] [|d] g tid //=. rewrite (shr_bytes_own_same κ _ ty ty'). f_equiv.
      f_equiv; [by eapply ty_shr_ne|]. f_equiv. by eapply ty_gho_pers_ne.
  Qed.
End shr_bytes.

Notation "&shr{ κ }" := (shr_bytes κ) (format "&shr{ κ }") : lrust_type_scope.

Section shr_bytes_rules.
  Context `{!typeG Σ}.

  Lemma shr_bytes_copy {𝔄} κ (ty: type 𝔄) : Copy (&shr{κ} ty).
  Proof.
    split. - apply _. - typeclasses eauto.
    - intros. by apply copy_shr_default.
  Qed.

  (** [&T: Sync] and [&T: Send] when [T: Sync]: the ownership of [&shr{κ} ty] is the guard of
      the bytes (which does not depend on the thread), the sharing predicate and the
      persistent predicate of the referent. *)
  Global Instance shr_sync {𝔄} κ (ty: type 𝔄) : Sync ty → Sync (&shr{κ} ty).
  Proof.
    move=> Hsync. apply sync_default; [done|]. move=> tid tid' [l x] [|d] g; [done|].
    simpl. destruct (Hsync tid tid' x d g) as (_ & Hp & Hs). by rewrite Hp Hs.
  Qed.

  Global Instance shr_send {𝔄} κ (ty: type 𝔄) : Sync ty → Send (&shr{κ} ty).
  Proof. move=> ?. by apply sync_send, shr_sync. Qed.

  (** Loading the referent, given a guard [G] of [@[κ]]: a typed [Load] of [ty_mty ty]
      returns the value of the referent. *)
  Lemma wp_shr_bytes_load {𝔄} κ (ty: type 𝔄) l x v d g tid G E :
    ↑naN ⊆ E → ty.(ty_val) x = Some v →
    {{{ (&shr{κ} ty).(ty_gho_own) (l, x) (S d) g tid ∗ (G &&{↑NllftG}&&> @[κ]) ∗ G ∗
        £(2*(g+1)) }}}
      Load Na1Ord ty.(ty_mty) #l @ E
    {{{ RET MLitV v; G }}}.
  Proof.
    iIntros (? Hv Φ) "(Own & #Gκ & G & £) HΦ". rewrite /= /by_succ.
    iDestruct "Own" as "(#Pt & _)".
    iApply (wp_load_na_guarded_gen _ _ _ v G (bytes_own ty l x) (ty_bytes ty x) (g+1)
      with "[$G $£]"); [done|intros; by eapply ty_bytes_decode| |done].
    iSplit; [iApply (guards_transitive_additive with "Gκ Pt")|]. by iApply bytes_own_view.
  Qed.
  (** Reading the referent of a [Copy] type through a shared reference: a guarded typed
      [Load]. *)
  Lemma type_load_shr_bytes_copy_instr {𝔄} κ (ty: type 𝔄) p E L I :
    Copy ty → lctx_lft_alive E L κ →
    typed_instr E L I +[p ◁ᵥ &shr{κ} ty] (Load Na1Ord ty.(ty_mty) p)
      (λ v, +[p ◁ᵥ &shr{κ} ty; v ◁ᵥ ty]) (λ post '-[a], post -[a; a.2]).
  Proof.
    intros Hcopy0. assert (NoCell 𝔄) by exact (copy_nocell ty). revert Hcopy0.
    iIntros (? Alv tid post mask iκs [[l x] []]) "#LFT #TIME _ _ #E L $ [p _] Obs".
    wp_bind p. iApply (wp_val with "p"). iIntros (w d Hp Hw) "#⧖ #Own".
    simpl in Hw. simplify_eq. cbn [of_val].
    destruct d as [|d]; [done|]. rewrite /= /by_succ.
    iDestruct "Own" as "(#Pt & #Shr & #Pers)".
    iDestruct (copy_shr with "Shr") as "#GOwn".
    iMod (llctx_interp_make_guarded with "L") as (γ) "[H1 [H2 [#Gh #Back]]]"; [solve_ndisj|].
    iAssert (|={⊤}=> fractional.half γ ∗ (fractional.half γ &&{↑NllftG}&&> @[κ]))%I
      with "[H1]" as ">[H1 #Gκ]".
    { leaf_open "Gh" with "H1" as "[InterpL back]". { solve_ndisj. }
      iDestruct (Alv with "InterpL E") as "#Alv".
      iMod ("back" with "InterpL") as "$". iModIntro.
      iApply (guards_transitive with "Gh Alv"). }
    iApply (wp_persistent_time_receipt with "TIME ⧖"); [done|]. iIntros "£ _".
    iDestruct (lc_weaken ((S d + 1) + 2 * (S d + 1)) with "£") as "[£1 £2]";
      [rewrite /advance_credits; lia|].
    iDestruct (guards_transitive_right with "Gκ GOwn") as "GO".
    iAssert (|={⊤ ∖ ↑advN}=> fractional.half γ ∗ ty.(ty_gho_own) x d (S d) tid)%I
      with "[H1 £1]" as ">[H1 #Gho]".
    { iMod (guards_open_later with "GO H1") as "Open"; [solve_ndisj|].
      iMod (lc_fupd_elim_laterN with "£1 Open") as ">[#Gho Close]".
      iMod ("Close" with "Gho") as "$". by iModIntro. }
    destruct (ty_val ty x) as [v|] eqn:Hv; last first.
    { iDestruct (guards_transitive_additive with "Gκ Pt") as "GP".
      iAssert (|={⊤ ∖ ↑advN}=> ⌜False⌝)%I with "[H1 £2]" as ">%Hf"; [|done].
      iMod (guards_open_later with "GP H1") as "Open"; [solve_ndisj|].
      iDestruct (lc_weaken (0 + S (d + 1)) with "£2") as "£2"; [lia|].
      iMod (lc_fupd_elim_laterN with "£2 Open") as ">[Bytes _]".
      iDestruct (bytes_own_val with "Bytes") as %[? ?]. congruence. }
    iApply wp_fupd. iApply (wp_shr_bytes_load κ ty l x v d (S d) tid (fractional.half γ)
      with "[$H1 $£2]"); [solve_ndisj|done| |].
    { iFrame "Gκ". rewrite /= /by_succ. iFrame "Pt Shr Pers". }
    iIntros "!> H1". iMod (fupd_mask_mono with "(Back H1 H2)") as "$"; [solve_ndisj|].
    iModIntro. iExists -[(l, x); x]. iFrame "Obs".
    iDestruct (ty_gho_own_depth_mono _ d (S d) (S d) (S d) with "Gho") as "[#Gho' _]"; [lia..|].
    iSplitR; [|iSplit; [|done]].
    - iExists _. iSplit; [done|]. rewrite -(val_own_intro_sep _ _ _ _ (VPtr l) (S d)); [|done|done]. iFrame "⧖".
      rewrite /= /by_succ. iFrame "Pt Shr Pers".
    - iExists _. iSplit; [done|]. rewrite -(val_own_intro_sep _ _ _ _ v (S d)); [|done|done]. by iFrame "⧖ Gho'".
  Qed.
End shr_bytes_rules.
