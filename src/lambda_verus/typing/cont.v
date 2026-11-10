From lrust.typing Require Export type.
From lrust.typing Require Import programs.
From guarding Require Import guard tactics.
Set Default Proof Using "Type".

Class IntoVecVal {n} (el: list expr) (vl: vec val n) :=
  into_vec_val: el = map of_val vl.

Global Instance into_vec_val_nil: IntoVecVal [] [#].
Proof. done. Qed.

Global Instance into_vec_val_cons {n} e v el (vl: _ n) :
  IntoVal e v → IntoVecVal el vl → IntoVecVal (e :: el) (v ::: vl).
Proof. by move=>/= <-->. Qed.

Section typing.
  Context `{!typeG Σ}.

  (** Jumping to and defining a continuation. *)

  Lemma type_jump {𝔄l 𝔅l ℭl 𝔇 n} (T': vec val n → tctx 𝔅l) k el
      (vl: vec val n) tr trx tr_res Φ E L (T: tctx 𝔄l) (Tx: tctx ℭl) (I: invctx) (C: cctx 𝔇) :
    IntoVecVal el vl → k ◁cont{L, I, T'} tr ∈ C →
    tctx_extract_ctx E L (T' vl) T Tx trx → resolve_tctx E L Tx Φ →
    tr_res ≡ trx ∘ (λ post bcl mask π, let '(bl, cl) := psep bcl in Φ cl π (tr post bl mask π)) →
    ⊢ typed_body E L I C T (jump: k el)
        tr_res.
  Proof.
    move=> -> ? TT' Rslv Htr_res.
    iApply typed_body_impl.
    { move => ???? Hpre.
      rewrite /equiv in Htr_res.
      apply Htr_res in Hpre.
      exact Hpre. }
    iApply typed_body_tctx_incl; [done|]. iIntros (? bcπl ?).
    move: (papp_ex bcπl)=> [?[?->]]. iIntros (post ?) "#LFT #TIME #PROPH #UNIQ E L I C /=[T' Tx] Obs".
    iDestruct (Rslv _ (⊤ ∖ ↑advN) with "LFT PROPH UNIQ TIME E [] L Tx") as "Rslv". { solve_ndisj_deep. }
    { iApply guards_refl. }
    iMod (fupd_mask_mono with "Rslv") as (?) "[⧖ ToObs]". { solve_ndisj_deep. }
    wp_bind Skip.
    iApply (wp_fupd).
    iApply (wp_persistent_time_receipt with "TIME ⧖"); [solve_ndisj_deep|].
    iIntros "£ ⧖S".
    iMod (lc_step_fupdN_elim_later with "[£] ToObs") as "ToObs". {
      iApply (lc_weaken with "£"). unfold advance_credits; lia.
    }
    iMod "ToObs" as "[Obs' L]". iCombine "Obs Obs'" as "#?". wp_seq. iModIntro. wp_seq.
    iApply ("C" with "[%//] L I T' []"). iApply proph_obs_impl; [|done]=>/= ?.
    rewrite papp_sepl papp_sepr. case=> ? Imp. by apply Imp.
  Qed.

  Lemma type_cont {𝔄l 𝔅l ℭ} bl (T': vec val (length bl) → tctx 𝔅l) trk L' (I': invctx)
        (T: tctx 𝔄l) kb ec e tr E L (I: invctx) (C: cctx ℭ) :
    Closed (kb :b: bl +b+ []) ec → Closed (kb :b: []) e →
    (∀k: val, typed_body E L I (k ◁cont{L', I', T'} trk :: C) T (subst' kb k e) tr) -∗
    □(∀(k: val) (vl: vec val (length bl)), typed_body E L' I'
      (k ◁cont{L', I', T'} trk :: C) (T' vl) (subst' kb k $ subst_v bl vl ec) trk) -∗
    typed_body E L I C T (letcont: kb bl := ec in e) tr.
  Proof.
    iIntros (??) "e #ec %%%%% #LFT #TIME #PROPH #UNIQ #E L I C T Obs".
    have ->: (rec: kb bl := ec)%E = of_val (rec: _ _ := _) by unlock.
    wp_let. iApply ("e" with "LFT TIME PROPH UNIQ E L I [C] T Obs").
    iLöb as "IH". iIntros (?). rewrite elem_of_cons.
    iIntros ([->|?]); [|by iApply "C"]. iIntros (???) "L' I' T' Obs". wp_rec.
    iApply ("ec" with "LFT TIME PROPH UNIQ E L' I' [C] T' Obs"). by iApply "IH".
  Qed.

  Lemma type_cont_norec {𝔄l 𝔅l ℭ} bl (T': vec val (length bl) → tctx 𝔅l) trk
        L' I' (T: tctx 𝔄l) kb ec e tr E L I (C: cctx ℭ) :
    Closed (kb :b: bl +b+ []) ec → Closed (kb :b: []) e →
    (∀k: val, typed_body E L I (k ◁cont{L', I', T'} trk :: C) T (subst' kb k e) tr) -∗
    (∀(k: val) (vl: vec val (length bl)),
      typed_body E L' I' C (T' vl) (subst' kb k $ subst_v bl vl ec) trk) -∗
    typed_body E L I C T (letcont: kb bl := ec in e) tr.
  Proof.
    iIntros (??) "e ec %%%%% #LFT #TIME #PROPH #UNIQ #E L I C T Obs".
    have ->: (rec: kb bl := ec)%E = of_val (rec: _ _ := _) by unlock.
    wp_let. iApply ("e" with "LFT TIME PROPH UNIQ E L I [ec C] T Obs").
    iIntros (?). rewrite elem_of_cons. iIntros ([->|?]); [|by iApply "C"].
    iIntros (???) "L' I' T' Obs". wp_rec.
    iApply ("ec" with "LFT TIME PROPH UNIQ E L' I' C T' Obs").
  Qed.
End typing.
