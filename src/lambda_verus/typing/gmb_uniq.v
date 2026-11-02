From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var.
From lrust.typing Require Export type.
From lrust.typing Require Import uniq_util.
From lrust.lifetime Require Import lifetime_full guarded_bor guarded_bor_proph.
From lrust.util Require Import proph_bor.
From guarding Require Import guard tactics.
Set Default Proof Using "Type".

(** * Lends of guarded mutable borrows from the bodies of unique borrows

This is (L3p) for the bodies of [&uniq] (phase 2b, step 4, of
[design_docs/guarded-mutable-borrows-plan.md]): from the owner's share guard of the move right
[gmb_a γ l] at [κ] and the body of a unique borrow at [κ] of a _permission type_ [pty] (whose
ownership predicate holds the permission [gmb_b γ] of the instance), we get the body of a
fresh unique borrow at [κ] of the _contents type_ [ty] at the location [l] of the contents
(with pattern lifetime [κ]), and the prophecy variable of the old borrow is resolved to [fp]
of the new one ([fv] maps the values of the contents to values of the permission, e.g.
[x ↦ (g, x)]).

The lend is lazy ([gmb_lend_proph_map_lazy]): when [κ] ends, the final body of the new
borrow is stored in the instance, with a settle law that forces its bytes with the mask
[lazyB] and the dead token of [κ] ([leaf_contents_unblock]); the old body is given back
blocked at [κ], and its lazy ghost update takes the lender's claim ([gmb_claim_take], which
settles the lend if the owner has not moved yet). So the owner can move after [κ] without the
lender, and without a guard for the lifetime of the contents.

The instance and the types are abstract, related by an interface:
- the contents [c l fv] of the instance are the fancy bytes of [ty] at [l] ([Hc], [Hb]);
- the permission type has trivial bytes ([Hpf], [Hpz]);
- its ownership predicate at [fv y] is the permission [gmb_b γ (ty_fval y)] and the ownership
  predicate of [ty] at [y] ([HGf], which may settle a claim, and [HGb]);
- the bytes mask of the instance is [lazyB]. *)

Section gmb_uniq.
  Context `{!typeG Σ}.
  Context `{!gmbG Σ loc FValue}.
  Context (c : loc → FValue → iProp Σ).
  Context `{c_timeless : !∀ l fv, Timeless (c l fv)}.

  Lemma gmb_lend_uniq {𝔄p 𝔄} (pty: type 𝔄p) (ty: type 𝔄) (fv: ~~𝔄 → ~~𝔄p) (fp: 𝔄 → 𝔄p)
      (fvp: FValue) γ (l lp: loc) (y: ~~𝔄) ξi d g idx κ tid E G :
    Timeless G → Inj eq eq fp → (∀ y π, vπ (fv y) π = fp (vπ y π)) →
    lazyE ⊆ E → gmb_bmask γ = lazyB →
    (∀ x fv0, ty.(ty_fval) x = Some fv0 → c l fv0 ⊢ cbytes ty x l) →
    (∀ fv0, fbytes ty l fv0 ⊢ c l fv0) →
    (∀ v, pty.(ty_fval) v = Some fvp) → (∀ v, cbytes pty v lp ⊣⊢ True) →
    (∀ y' d' g', ty_gho_own pty (fv y') d' g' tid ⊢ |={lazyE}=>
       ∃ fv0, ⌜ty.(ty_fval) y' = Some fv0⌝ ∗ gmb_b γ fv0 ∗ ty_gho_own ty y' d' g' tid) →
    (∀ y' d' g' fv0, ty.(ty_fval) y' = Some fv0 →
       gmb_b γ fv0 ∗ ty_gho_own ty y' d' g' tid ⊢ ty_gho_own pty (fv y') d' g' tid) →
    llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ gmb_inv c γ -∗
    (@[κ] &&{↑NllftG}&&> gmb_a γ l) -∗ κ ⊑ ty_lft pty -∗ ty_lft pty ⊑ ty_lft ty -∗
    (G &&{↑NllftG}&&> @[κ]) -∗ G -∗ £ 4 -∗
    uniq_body pty (fv y) ξi d g idx κ tid lp ={E}=∗ ∃ ζi ζidx,
      ⟨π, (π (uniq_prvar (fv y) ξi)).1 = fp ((π (uniq_prvar y ζi)).1)⟩ ∗
      uniq_body ty y ζi d g ζidx κ tid l ∗ G.
  Proof using All.
    iIntros (HT Hinj Hcomm HE Hbm Hc Hb Hfvp Hpz HGf HGb)
      "#LFT #PROPH #UNIQ #GI #Ga #In #Incl #Gk G £".
    iIntros "(%κp & %γo & #Inclp & (Gho & Tok) & ⧗ & #Bor)".
    have ?: ↑Nllft ∪ ↑prophN ⊆ E. { etrans; [|done]. rewrite /lazyE. set_solver. }
    iDestruct (lc_split 1 3 with "£") as "[£1 £3]".
    iMod (ghost_var_alloc (lstate_triv y)) as (γn) "[Ghn Ghn']".
    iMod (proph_loan_intro (uniq_cell_tyi y) E (uniq_cell y d g γn) with "PROPH UNIQ")
      as (ζi) "Loan"; [solve_ndisj|].
    set ζ := uniq_prvar y ζi.
    (* Only the first component of the old controller matters. *)
    set fπ := λ (cc: (uniq_cellₛ 𝔄)),
      ((fp cc.1, (1%positive, (1%positive, 1%positive))) : uniq_cellₛ 𝔄p).
    iMod lc_zero as "Lc0".
    iMod (gmb_lend_proph_map_lazy c E κ (uniq_prvar (fv y) ξi) (uniq_cell (fv y) d g γo) idx
      (uniq_gbody κp pty tid lp) ζ (uniq_cell y d g γn) (uniq_gbody κ ty tid l) fπ G γ l 0
      with "LFT PROPH UNIQ GI Ga Lc0 £3 Gk [Gho Ghn' £1] G Loan Tok Bor")
      as "(#Obs & Bor' & G)"; [done|lia| |].
    { (* the forward direction: force the payload of the permission, split the permission
         off its ownership predicate, and build the new body from the contents *)
      iIntros (G' wπ ?) "#G'k G' Body".
      iMod (uniq_gbody_triv_open with "Gho Body") as "(_ & Gho & Gho' & P)".
      iMod (uniq_payload_force with "[] G' £1 P") as "(G' & #⧖ & GhoP & _)"; [done| |].
      { iApply (guards_transitive with "G'k In"). }
      iDestruct (HGf with "GhoP") as "X".
      iMod (fupd_mask_mono with "X") as (fv0 Hfv0) "[B GhoC]"; [done|].
      iModIntro. iFrame "G'". iExists fv0. iFrame "B". iIntros "C".
      iDestruct (Hc with "C") as "Pt"; [done|].
      iModIntro. iExists (vπ (uniq_cell y d g γn)).
      iSplitL "Ghn' Pt GhoC".
      { iApply (uniq_gbody_triv_close with "Ghn'"); [done|].
        iApply uniq_payload_intro_later. iNext. iFrame "⧖ GhoC Pt". }
      (* the way back, in the back-map: store the final new body lazily *)
      iIntros (y' wζ') "Pc Body #Dead".
      rewrite (uniq_cell_surj y') uniq_gbody_cell.
      iMod (bi.later_exist_except_0 with "Body") as (p) "Body".
      iMod (bi.later_exist_except_0 with "Body") as (r) "(Ok & >%Hw0 & _ & C)".
      set lrn := prfn_place r.
      set d1 := cell_d y'. set g1 := cell_g y'.
      set lr_old : place_rfn 𝔄p := PlaceProph (fv y'.1) (λ π, fp ((π ζ).1)).
      iMod (ghost_var_update_halves (lstate (PatBlocked κ) (inl lr_old)) with "Gho Gho'")
        as "[Gho _]".
      iModIntro.
      iExists (pat_ok κ p ∗ leaf_contents κ ty p r d1 g1 tid l)%I,
        (λ fv', guarded_upd lazyE @[ty_lft ty]
          (∃ d' g', ⧖(S d' `max` g') ∗ ofty_gho 0 ty lrn fv' d' g' tid))%I.
      iSplitL "Ok C". { iNext. iFrame. }
      iSplitR.
      { (* the settle law: force the bytes with the dead token *)
        iIntros "[#Ok C] #D". rewrite Hbm.
        iDestruct "D" as (κ') "[#Incl' #Dead']".
        iMod (llftl_incl_dead_implies_dead with "LFT Incl' Dead'") as "#†κ";
          [apply lazyB_NllftG|].
        iMod (leaf_contents_unblock with "LFT Ok †κ C") as (fv') "[B Upd]".
        iModIntro. iExists fv'. iFrame "Upd". by iApply Hb. }
      (* the old body, blocked at [κ]: its lazy ghost update takes the claim *)
      iIntros "Cl". iNext. iExists (uniq_cell (fv y'.1) d1 g1 γo).
      rewrite uniq_gbody_cell. iExists (PatBlocked κ), (inl lr_old). iFrame "Gho".
      iSplit; [iApply pat_ok_blocked; iExact "Inclp"|].
      iSplit. { iPureIntro. intros π. by rewrite prfn_den_inl. }
      iExists fvp. rewrite /leaf_owned_b /leaf_owned_lz /=. iSplitL; [|done].
      iIntros "#†κ". iModIntro. iExists fvp.
      iSplitR. { iExists (fv y'.1). iSplit; [done|]. by rewrite Hpz. }
      iIntros (G'' ?) "#G''ty G''".
      iMod (gmb_claim_take with "GI Cl") as (fv') "[B R]".
      { rewrite Hbm /lazyE /lazyB. solve_ndisj. }
      iMod (guarded_upd_run with "[] G'' R") as "[$ (%d' & %g' & #⧖' & %x' & %Hx' & Rel & GhoC)]";
        [done| |].
      { iApply (guards_transitive with "G''ty Incl"). }
      iModIntro. iExists d', g'. iFrame "⧖'".
      iExists (fv x'). iSplit; [done|]. iSplitL "Rel Pc".
      { iDestruct (place_rfn_rel_eqz with "Rel") as "Eqz".
        rewrite /place_rfn_rel. iNext.
        iDestruct (uniq_ctrl_eqz_fst with "PROPH Pc [Eqz]") as "Eqz".
        { iApply (proph_eqz_eq with "Eqz"); [|done]. fun_ext=>π /=.
          by rewrite Hw0 prfn_place_den. }
        iDestruct (proph_eqz_constr fp with "Eqz") as "Eqz".
        iApply (proph_eqz_eq with "Eqz"); [done|]. fun_ext=>π /=. by rewrite Hcomm. }
      iApply HGb; [done|]. iFrame. }
    iDestruct "Bor'" as (ζidx) "[Tok' #Bor']".
    iModIntro. iExists ζi, ζidx. iFrame "G".
    iSplitR. { iApply (proph_obs_impl with "Obs")=> π ->. done. }
    iExists κ, γn. iFrame "Tok' Bor' ⧗ Ghn". rewrite /uniq_pat_lft. iApply guards_refl.
  Qed.
End gmb_uniq.
