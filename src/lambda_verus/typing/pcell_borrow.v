From lrust.lang Require Import heap_cells.
From lrust.typing Require Export pcell.
From lrust.typing Require Import programs uniq_util.
From guarding Require Import guard tactics.
From lrust.lifetime Require Import lifetime_full.
Set Default Proof Using "Type".

(** * Borrows of the contents of a [PCell] on bytes

[PCell::borrow] gives a shared reference to the contents of a cell, given shared references
to the cell and to its permission; [borrow_mut] gives a unique borrow of the contents, given
a shared reference to the cell and a unique borrow of the permission (§10 step 5 of
[design_docs/pcell-multibyte-cells.md]).

The contents of a cell are not reached through location edges (as the referent of
[&shrb]/[&uniqb], [bytes_own]) but through the byte-cells of its group, and an access needs
the location side of the group (guarded) and its permission [gdyn] (owned or guarded), see
[lang/heap_cells.v]. So a borrow of the contents is a borrow of the _permission_ (whose
ownership is [gdyn] and the ownership of the contents), pinned to the location of the cell
by a guard of the location side of its group:
- [cell_shr_ty κ ty] is [&shr{κ} (cell_points_to_ty ty)], at the location of the cell;
- [cell_uniq_ty κ ty] is [&uniq{κ} (cell_points_to_ty ty)], at the location of the cell.
Both are [pinned_ty]: their ownership, persistent predicate and sharing predicate have the
guard of the location side (by [@[κ]]) in addition. Their values are those of the borrows
of the permission: the value [(g, x)] of the permission has the group and the contents.
The rules read and write the whole contents (of a type without cells), through the
sub-position rules of [lang/lifting.v] at the offset [0]. *)

Implicit Type 𝔄 𝔅: syn_type.

(** ** A type with a persistent predicate in addition *)
Class PinPred `{!typeG Σ} {𝔄} (Φ: ~~𝔄 → nat → iProp Σ) := {
  #[global] pin_pred_persistent x n :: Persistent (Φ x n);
  pin_pred_mono x n n' : n ≤ n' → Φ x n ⊢ Φ x n';
}.

Section pinned.
  Context `{!typeG Σ}.

  Program Definition pinned_ty {𝔄} (ty: type 𝔄) (Φ: ~~𝔄 → nat → iProp Σ) `{!PinPred Φ} :
      type 𝔄 := {|
    ty_size := ty.(ty_size); ty_lfts := ty.(ty_lfts); ty_E := ty.(ty_E);
    ty_gho_own x d g tid := ty.(ty_gho_own) x d g tid ∗ Φ x g;
    ty_gho_res x d g tid := ty.(ty_gho_res) x d g tid ∗ Φ x g;
    ty_gho_pers x d g tid := ty.(ty_gho_pers) x d g tid ∗ Φ x g;
    ty_phys := ty.(ty_phys);
    ty_mty := syn_mty _; ty_val := syn_val; ty_mty_eq := eq_refl; ty_val_eq _ := eq_refl;
    ty_fval := syn_fval; ty_fval_eq _ := eq_refl;
    ty_shr κ x d g tid := ty.(ty_shr) κ x d g tid ∗ Φ x g;
  |}%I.
  Next Obligation. intros. first [apply ty_size_eq|apply ty_size_eq2|apply ty_phys_eq2]. Qed.
  Next Obligation. intros. first [apply ty_size_eq|apply ty_size_eq2|apply ty_phys_eq2]. Qed.
  Next Obligation. intros. first [apply ty_size_eq|apply ty_size_eq2|apply ty_phys_eq2]. Qed.
  Next Obligation.
    intros 𝔄 ty Φ ? d g d' g' x tid ??. iIntros "[Own #Φ]".
    iDestruct (ty_gho_own_depth_mono with "Own") as "[$ Back]"; [done..|].
    iSplitR; [by iApply pin_pred_mono|]. iIntros "[Own _]". iFrame "Φ". by iApply "Back".
  Qed.
  Next Obligation.
    intros 𝔄 ty Φ ? d g d' g' x tid ??. iIntros "[Pers #Φ]".
    iSplitL; [by iApply ty_gho_pers_depth_mono|by iApply pin_pred_mono].
  Qed.
  Next Obligation.
    intros. iIntros "[Own $]". by iApply ty_gho_pers_impl.
  Qed.
  Next Obligation.
    intros 𝔄 ty Φ ? κ κ' x n d g tid. iIntros "#Incl [Shr #Φ]".
    iSplitL; [by iApply (ty_shr_lft_mono with "Incl Shr")|]. iApply pin_pred_mono; [|done]. lia.
  Qed.
  Next Obligation.
    intros 𝔄 ty Φ ? κ d g d' g' x tid ??. iIntros "[Shr #Φ]".
    iSplitL; [by iApply ty_shr_depth_mono|by iApply pin_pred_mono].
  Qed.
  Next Obligation.
    intros 𝔄 ty Φ ? E κ x d g tid G ??. iIntros "#LFT #Incl [#Pers #Φ] #Gκ G Bor".
    iMod (llftl_sep_split with "LFT Bor") as "[Bor _]"; [solve_ndisj|].
    iMod (ty_share with "LFT Incl Pers Gκ G Bor") as "Upd"; [done..|].
    iModIntro. iApply (step_fupdN_wand with "Upd"). iIntros ">[$ $] !>". iFrame "Φ".
  Qed.
  Next Obligation.
    intros 𝔄 ty Φ ? κ x n d g tid ξ R Hin. iIntros "#LFT #Incl [Pers _] [Shr _]".
    by iApply (ty_shr_guard_proph with "LFT Incl Pers Shr").
  Qed.
  Next Obligation. intros. iIntros "[Own $]". by iApply ty_gho_res_of_own. Qed.

  Lemma pinned_resolve {𝔄} E L (ty: type 𝔄) Φ `{!PinPred Φ} Ψ :
    resolve E L ty Ψ → resolve E L (pinned_ty ty Φ) Ψ.
  Proof.
    iIntros (Rslv G F x d g tid ??) "LFT PROPH UNIQ TIME E L G [Own _]".
    by iApply (Rslv with "LFT PROPH UNIQ TIME E L G Own").
  Qed.
End pinned.

(** ** The guard of the location side of a cell *)
Section cell_loc.
  Context `{!typeG Σ}.

  (** The location side of the group [g] (with byte-cells [cs]) is at [l], while [κ] is
      alive. *)
  Definition cell_loc (κ: lft) (m: mty) (l: loc) (g: positive) (n: nat) : iProp Σ :=
    ∃ cs, greg g m cs ∗ (@[κ] &&{↑NllftG; n+1}&&> loc_side l g m cs).

  Global Instance cell_loc_persistent κ m l g n : Persistent (cell_loc κ m l g n).
  Proof. apply _. Qed.

  Lemma cell_loc_mono κ m l g n n' : n ≤ n' → cell_loc κ m l g n ⊢ cell_loc κ m l g n'.
  Proof.
    iIntros (?) "(%cs & Hg & G)". iExists cs. iFrame "Hg".
    iApply (lguards_weaken_later with "G"). lia.
  Qed.

  Global Instance cell_loc_shr_pin κ m 𝔄 :
    PinPred (λ (x: ~~(at_clocₛ (trackedₛ (pcellₛ (syn_mty 𝔄) * 𝔄)))) n,
      cell_loc κ m x.1.1 x.2.1 n).
  Proof. split; [apply _|]. intros. by apply cell_loc_mono. Qed.

  Definition cell_uniq_loc κ m {𝔄} (x: ~~(uniq_borₛ (trackedₛ (pcellₛ (syn_mty 𝔄) * 𝔄))))
      (n: nat) : iProp Σ :=
    match x with (l, x0, _, _, _, _) => cell_loc κ m l.1 x0.1 n end.

  Global Instance cell_loc_uniq_pin κ m 𝔄 : PinPred (@cell_uniq_loc κ m 𝔄).
  Proof.
    split.
    - intros [[[[[??]?]?]?]?] ?. apply _.
    - intros [[[[[??]?]?]?]?] ???. by apply cell_loc_mono.
  Qed.
End cell_loc.

(** ** The types of borrows of the contents of a cell *)
Section cell_types.
  Context `{!typeG Σ}.

  Definition cell_shr_ty {𝔄} (κ: lft) (ty: type 𝔄) :
      type (at_clocₛ (trackedₛ (pcellₛ (syn_mty 𝔄) * 𝔄))) :=
    pinned_ty (&shr{κ} (cell_points_to_ty ty)) (λ x n, cell_loc κ ty.(ty_mty) x.1.1 x.2.1 n).

  Definition cell_uniq_ty {𝔄} (κ: lft) (ty: type 𝔄) :
      type (uniq_borₛ (trackedₛ (pcellₛ (syn_mty 𝔄) * 𝔄))) :=
    pinned_ty (&uniq{κ} (cell_points_to_ty ty)) (cell_uniq_loc κ ty.(ty_mty)).

  Lemma cell_uniq_resolve {𝔄} E L κ (ty: type 𝔄) :
    lctx_lft_alive E L κ →
    resolve E L (cell_uniq_ty κ ty) (λ x π, snd (vπ x π) = fst (vπ x π)).
  Proof.
    intros Alv. rewrite /cell_uniq_ty.
    apply (pinned_resolve E L (&uniq{κ} (cell_points_to_ty ty)) (cell_uniq_loc κ ty.(ty_mty))).
    exact (uniq_bor.uniq_resolve E L κ (cell_points_to_ty ty) Alv).
  Qed.

  Lemma cell_points_to_bsize {𝔄} (ty: type 𝔄) : ty_bsize (cell_points_to_ty ty) = 0.
  Proof. by rewrite /ty_bsize -ty_mty_eq. Qed.
End cell_types.

(** ** [PCell::borrow] and reads through it *)
Section cell_shr_rules.
  Context `{!typeG Σ}.

  Definition PCellBorrow : val := (λ: ["pcell"; "perm"], "pcell")%V.

  Lemma type_pcell_borrow_instr {𝔄} κ (ty: type 𝔄) p q E L I :
    typed_instr E L I
      +[p ◁ᵥ &shr{κ} (pcell_ty ty.(ty_mty)); q ◁ᵥ &shr{κ} (cell_points_to_ty ty)]
      (PCellBorrow [p; q]) (λ v, +[v ◁ᵥ cell_shr_ty κ ty])
      (λ post '-[(l, g); (_, (g', x))], λ mask π, g = g' ∧ post -[(l, (g, x))] mask π).
  Proof.
    iIntros (tid post mask iκs [[l g] [[l' [g' x]] []]]) "_ #TIME #PROPH _ _ $ $ (p & q & _) #Obs".
    iMod (proph_obs_sat with "PROPH Obs") as "(% & <- & _)"; [done|].
    iDestruct "p" as (vp Hp wp dp [-> Hwp]) "[#⧖p #Own]". simpl in Hwp. simplify_eq.
    iDestruct "q" as (vq Hq wq dq [-> Hwq]) "[#⧖q #Own']".
    rewrite /PCellBorrow.
    wp_bind p. iApply (wp_wand with "[]"); [by iApply wp_eval_path|]. iIntros (? ->).
    wp_bind q. iApply (wp_wand with "[]"); [by iApply wp_eval_path|]. iIntros (? ->).
    destruct dp as [|dp]; [done|]. destruct dq as [|dq]; [done|].
    set D := dp `max` dq.
    iDestruct (ty_gho_own_depth_mono (&shr{κ} (cell_points_to_ty ty)) (S dq) (S dq) (S D) (S D)
      (l', (g, x)) tid with "Own'") as "[#OwnD _]"; [lia|lia|].
    iDestruct "Own" as "(#Gp & _ & _)". iDestruct "Own'" as "(#Gq & _ & #Pers)".
    iAssert (⧖(S D))%I as "#⧖D".
    { rewrite /D Nat.succ_max_distr persistent_time_receipt_sep. by iFrame "⧖p ⧖q". }
    iApply wp_fupd.
    iApply (wp_persistent_time_receipt with "TIME ⧖q"); [done|]. iIntros "£ _".
    iMod (lc_fupd_elim_laterN with "[£] Pers") as "Pers'".
    { iApply (lc_weaken with "£"). rewrite /advance_credits. lia. }
    destruct dq as [|dq']; [by iDestruct "Pers'" as "[]"|].
    iDestruct "Pers'" as "[(%fv & %cs & %Hfv & #Hg) _]".
    wp_rec. iModIntro. iExists -[(l, (g, x))]. iSplitR "Obs"; last first.
    { iApply (proph_obs_impl with "Obs"). by intros π [_ ?]. }
    iSplit; [|done]. rewrite tctx_val_val. iExists (S D). iSplit; [done|]. iFrame "⧖D".
    iSplit.
    - iDestruct "OwnD" as "(Gq' & $ & $)".
      rewrite /shr_bytes_own (bytes_own_zst_loc (cell_points_to_ty ty) l.1 l'.1);
        [done|apply cell_points_to_bsize].
    - iExists cs. iFrame "Hg". iApply (guard_pcell_loc_side with "Hg"); [apply ty_mty_wf|].
      iApply (lguards_weaken_later with "Gp"). lia.
  Qed.

  (** Reading the contents through a shared borrow of them (non-atomically): a guarded
      typed [Load] through the cell. *)
  Lemma type_cell_shr_load_instr {𝔄} `{!NoCell 𝔄} κ (ty: type 𝔄) p E L I :
    Copy ty → lctx_lft_alive E L κ →
    typed_instr E L I +[p ◁ᵥ cell_shr_ty κ ty] (Load Na1Ord ty.(ty_mty) (ToLit p))
      (λ v, +[v ◁ᵥ ty]) (λ post '-[(_, (_, x))], λ mask π, post -[x] mask π).
  Proof.
    iIntros (? Alv tid post mask iκs [[l [g x]] []]) "#LFT #TIME #PROPH _ #E L $ (p & _) #Obs".
    wp_bind p. iApply (wp_val with "p"). iIntros (w d Hp Hw) "#⧖ #Own".
    simpl in Hw. simplify_eq. wp_pure _.
    destruct d as [|d0]; [by iDestruct "Own" as "[[] _]"|].
    iDestruct "Own" as "[(_ & #Shr & #Pers) (%cs & #Hg & #GL)]".
    iMod (llctx_interp_make_guarded with "L") as (γ) "[H1 [H2 [#Gh #Back]]]"; [solve_ndisj|].
    iAssert (|={⊤}=> fractional.half γ ∗ (fractional.half γ &&{↑NllftG}&&> @[κ]))%I
      with "[H1]" as ">[H1 #Gκ]".
    { leaf_open "Gh" with "H1" as "[InterpL back]". { solve_ndisj. }
      iDestruct (Alv with "InterpL E") as "#Alv".
      iMod ("back" with "InterpL") as "$". iModIntro.
      iApply (guards_transitive with "Gh Alv"). }
    iApply (wp_persistent_time_receipt with "TIME ⧖"); [done|]. iIntros "£ #⧖S".
    iDestruct (lc_weaken (1 + (S d0 + 1) + (S d0 + 1) + 2 * (S d0 + 1)) with "£")
      as "[[[£1 £2] £3] £4]"; [rewrite /advance_credits; lia|].
    iMod (lc_fupd_elim_later with "£1 Shr") as "Shr'".
    destruct d0 as [|d'']; [done|]. iDestruct "Shr'" as "[#G2 #TyShr]".
    iMod (lc_fupd_elim_laterN with "£2 Pers") as "Pers'".
    iDestruct "Pers'" as "[(%fv & %cs' & %Hfv & #Hg') _]".
    iDestruct (greg_agree with "Hg Hg'") as %[_ <-].
    iDestruct (copy_shr with "TyShr") as "#GOwn".
    iDestruct (guards_transitive_right with "Gκ GOwn") as "GO".
    iAssert (|={⊤ ∖ ↑advN}=> fractional.half γ ∗ ty.(ty_gho_own) x d'' (S (S d'')) tid)%I
      with "[H1 £3]" as ">[H1 #Gho]".
    { iMod (guards_open_later with "GO H1") as "Open"; [solve_ndisj|].
      iMod (lc_fupd_elim_laterN with "£3 Open") as ">[#Gho Close]".
      iMod ("Close" with "Gho") as "$". by iModIntro. }
    iDestruct (guards_transitive_right with "Gκ GL") as "G1".
    iDestruct (guards_transitive_right with "Gκ G2") as "G2'".
    iDestruct (guard_cell_own_gdyn with "G2'") as "G2g"; [done|].
    iDestruct (guards_and_point with "G1 G2g") as "GP";
      [apply point_prop_loc_side_gdyn|apply loc_side_and_gdyn|].
    have Hc : fv_cells fv = [] by eapply ty_fval_nocell_cells.
    iApply wp_fupd.
    iApply (wp_pcell_load_na_guarded _ l.1 g ty.(ty_mty) cs fv (fractional.half γ) _
      (S (S d'') + 1) with "[H1 £4]"); [solve_ndisj|done| |].
    { iSplitR; [done|]. iSplitR; [iIntros "!> [Hls Hgd]"; iFrame; by iIntros "$ $"|].
      iFrame "Hg H1 £4". }
    iIntros "!>" (v) "[H1 %Hv]".
    iMod (fupd_mask_mono with "(Back H1 H2)") as "$"; [solve_ndisj|].
    rewrite ty_fval_nocell // in Hfv. apply fmap_Some in Hfv as (v' & Hv' & Hfv').
    rewrite Hv in Hfv'. apply fv_lift_inj in Hfv'. subst v'.
    iModIntro. iExists -[x]. iSplitR "Obs"; last first.
    { iApply (proph_obs_impl with "Obs"). by intros π ?. }
    iSplit; [|done]. rewrite tctx_val_val. iExists (S (S (S d''))). iSplit; [done|].
    iFrame "⧖S".
    iDestruct (ty_gho_own_depth_mono _ d'' (S (S d'')) (S (S (S d''))) (S (S (S d'')))
      with "Gho") as "[$ _]"; lia.
  Qed.
End cell_shr_rules.

(** ** [PCell::borrow_mut] and writes through it *)
Section cell_uniq_rules.
  Context `{!typeG Σ}.

  Definition PCellBorrowMut : val := (λ: ["pcell"; "perm"], "pcell")%V.

  Lemma type_pcell_borrow_mut_instr {𝔄} κ (ty: type 𝔄) p q E L I :
    lctx_lft_alive E L κ →
    typed_instr E L I
      +[p ◁ᵥ &shr{κ} (pcell_ty ty.(ty_mty)); q ◁ᵥ &uniq{κ} (cell_points_to_ty ty)]
      (PCellBorrowMut [p; q]) (λ v, +[v ◁ᵥ cell_uniq_ty κ ty])
      (λ post '-[(l, g); bor], λ mask π,
        let '(_, (g', x), ξi, d, gi, idx) := bor in
        g = g' ∧ post -[((l.1, []), (g, x), ξi, d, gi, idx)] mask π).
  Proof.
    iIntros (Alv tid post mask iκs [[l g] [[[[[[l' [g' x]] ξi] di] gi] ξidx] []]])
      "#LFT #TIME #PROPH _ #E L $ (p & q & _) #Obs".
    iMod (proph_obs_sat with "PROPH Obs") as "(% & <- & _)"; [done|].
    iDestruct "p" as (vp Hp wp dp [-> Hwp]) "[#⧖p #Own]". simpl in Hwp. simplify_eq.
    iDestruct "q" as (vq Hq wq dq [-> Hwq]) "[#⧖q Uniq]".
    iDestruct "Uniq" as "(#Incl & [%Hle1 %Hle2] & Body)".
    rewrite /PCellBorrowMut.
    wp_bind p. iApply (wp_wand with "[]"); [by iApply wp_eval_path|]. iIntros (? ->).
    wp_bind q. iApply (wp_wand with "[]"); [by iApply wp_eval_path|]. iIntros (? ->).
    destruct dp as [|dp]; [done|]. iDestruct "Own" as "(#Gp & _ & _)".
    set D := S dp `max` dq.
    iAssert (⧖D)%I as "#⧖D"; [rewrite persistent_time_receipt_sep; by iFrame "⧖p ⧖q"|].
    iApply wp_fupd.
    iApply (wp_persistent_time_receipt with "TIME ⧖D"); [done|]. iIntros "£ _".
    iMod (llctx_interp_make_guarded with "L") as (γ) "[H1 [H2 [#Gh #Back]]]"; [solve_ndisj|].
    iAssert (|={⊤ ∖ ↑advN}=> fractional.half γ ∗ (fractional.half γ &&{↑NllftG}&&> @[κ]))%I
      with "[H1]" as ">[H1 #Gκ]".
    { leaf_open "Gh" with "H1" as "[InterpL back]". { solve_ndisj. }
      iDestruct (Alv with "InterpL E") as "#Alv".
      iMod ("back" with "InterpL") as "$". iModIntro.
      iApply (guards_transitive with "Gh Alv"). }
    (* The static registry entry of the group, from the location side. *)
    iDestruct (guards_transitive_right with "Gκ Gp") as "G1".
    iAssert (|={⊤ ∖ ↑advN}=> fractional.half γ ∗ ∃ cs, greg g ty.(ty_mty) cs)%I
      with "[H1 £]" as ">[H1 (%cs & #Hg)]".
    { iMod (guards_extract_persistent_later _ _ (∃ cs, greg g ty.(ty_mty) cs)%I (⊤ ∖ ↑advN)
        (↑NllftG) _ ltac:(apply _) ltac:(solve_ndisj) with "G1 H1 []") as "Upd".
      { iIntros "Bytes". rewrite bytes_own_pcell_ty; [|apply ty_mty_wf].
        iDestruct "Bytes" as (cs) "[[Hg _] _]". by iExists cs. }
      iMod (lc_fupd_elim_laterN with "[£] Upd") as "Upd".
      { iApply (lc_weaken with "£"). rewrite /advance_credits. lia. }
      by iMod "Upd". }
    iMod (fupd_mask_mono with "(Back H1 H2)") as "$"; [solve_ndisj|].
    wp_rec. iModIntro. iExists -[((l.1, []), (g, x), ξi, di, gi, ξidx)].
    iSplitR "Obs"; last first. { iApply (proph_obs_impl with "Obs"). by intros π [_ ?]. }
    iSplit; [|done]. rewrite tctx_val_val. iExists D. iSplit; [done|]. iFrame "⧖D".
    iSplitL.
    - iFrame "Incl". iSplit; [iPureIntro; lia|].
      iApply (uniq_body_loc with "Body"). intros ?. rewrite /cbytes.
      apply bytes_own_zst_loc, cell_points_to_bsize.
    - iExists cs. iFrame "Hg". iApply (guard_pcell_loc_side with "Hg"); [apply ty_mty_wf|].
      iApply (lguards_weaken_later with "Gp"). lia.
  Qed.

  (** Writing the contents through a unique borrow of them (non-atomically): a guarded
      typed [Store] through the cell. The borrow stays, with the new contents. *)
  Lemma type_cell_uniq_store_instr {𝔄} `{!NoCell 𝔄} κ (ty: type 𝔄) p r E L I :
    lctx_lft_alive E L κ →
    typed_instr E L I +[p ◁ᵥ cell_uniq_ty κ ty; r ◁ᵥ ty]
      (Store Na1Ord ty.(ty_mty) (ToLit p) r) (λ _, +[p ◁ᵥ cell_uniq_ty κ ty])
      (λ post '-[bor; y], λ mask π, let '(l, (g, _), ξi, _, _, idx) := bor in
         ∀ d gi, post -[(l, (g, y), ξi, d, gi, idx)] mask π).
  Proof.
    iIntros (Alv tid post mask iκs [[[[[[l [g x]] ξi] di] gi] ξidx] [y []]])
      "#LFT #TIME #PROPH #UNIQ #E L $ (p & r & _) Obs".
    iDestruct (Alv with "L E") as "#Alv".
    wp_bind p. iApply (wp_val with "p"). iIntros (w dq Hp Hw) "#⧖q [Uniq #Φ]".
    simpl in Hw. simplify_eq. wp_pure _.
    wp_bind r. iApply (wp_val with "r"). iIntros (v dy Hr Hv) "#⧖y Gy".
    iDestruct "Φ" as (cs) "[#Hg #GL]".
    iDestruct "Uniq" as "(#Incl & [%Hle1 %Hle2] & Body)".
    iApply wp_fupd.
    iApply (wp_cumulative_time_receipt2 with "TIME"); [solve_ndisj|]. iIntros "⧗".
    iDestruct (cumulative_time_receipt_sep 1 1 with "⧗") as "[⧗a ⧗b]".
    set D := dq `max` dy.
    iAssert (⧖D)%I as "#⧖D"; [rewrite persistent_time_receipt_sep; by iFrame "⧖q ⧖y"|].
    iMod (cumulative_persistent_time_receipt_get_credits with "TIME ⧗a ⧖D") as "[#⧖D1 £]";
      [solve_ndisj|].
    iMod (cumulative_persistent_time_receipt_get_credits with "TIME ⧗b ⧖D1") as "[#⧖D2 _]";
      [solve_ndisj|].
    iDestruct (lc_weaken (1 + 2 * (dq + 1)) with "£") as "[£1 £2]";
      [rewrite /advance_credits; lia|].
    iMod (llctx_interp_make_guarded with "L") as (γ) "[H1 [H2 [#Gh #Back]]]"; [solve_ndisj|].
    iDestruct (guards_transitive with "Gh Alv") as "#Gκ".
    iMod (uniq_cell_open κ ty _ _ _ _ _ _ _ dq with "LFT UNIQ Gκ Gκ [Body] H1 H2 £1")
      as "(H2 & ⧗s & _ & _ & Own & Close)".
    { iFrame "Incl Body". iPureIntro. lia. }
    iDestruct "Own" as (di' ->) "[Own _]". iDestruct "Own" as (fv cs' Hfv) "[#Hg' Hgd]".
    iDestruct (greg_agree with "Hg Hg'") as %[_ <-].
    iDestruct (guards_transitive_right with "Gκ GL") as "GL'".
    have Hc : fv_cells fv = [] by eapply ty_fval_nocell_cells.
    iApply (wp_pcell_store_na_guarded _ l.1 g ty.(ty_mty) cs fv _ v (fractional.half γ) _
      (dq + 1) with "[H2 Hgd £2]"); [solve_ndisj|done|apply ty_mty_wf|by eapply ty_val_wf| |].
    { iSplitR; [done|]. iSplitR; [iIntros "!> $"; by iIntros "$"|]. iFrame "Hg H2 Hgd £2". }
    iIntros "!> [H2 Hgd]".
    iMod (fupd_mask_subseteq (↑Nllft)) as "Hback"; [solve_ndisj|].
    iMod ("Close" $! y D D with "[Gy Hgd] ⧗s") as "[UB H1]".
    { iNext. iSplitR.
      { iApply (persistent_time_receipt_mono with "⧖D2"). lia. }
      iSplitL "Gy"; [by iDestruct (ty_gho_own_depth_mono _ dy dy D D with "Gy") as "[$ _]"; lia|].
      iExists (fv_lift v), cs. iFrame "Hg Hgd". iPureIntro.
      rewrite ty_fval_nocell // Hv //. }
    iMod "Hback" as "_".
    iMod (fupd_mask_mono with "(Back H1 H2)") as "$"; [solve_ndisj|].
    iModIntro. iExists -[(l, (g, y), ξi, S D, D, ξidx)]. iSplitR "Obs"; last first.
    { iApply (proph_obs_impl with "Obs"). intros π Hpost. apply Hpost. }
    iSplit; [|done]. iExists _. iSplit; [done|]. iExists (VPtr l.1), (D + 1 + 1).
    iSplit; [done|]. iFrame "⧖D2". iSplitL.
    - iFrame "Incl UB". iPureIntro; lia.
    - iExists cs. iFrame "Hg". iApply (lguards_weaken_later with "GL"). lia.
  Qed.
End cell_uniq_rules.
