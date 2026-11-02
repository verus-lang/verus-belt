From iris.proofmode Require Import proofmode.
From lrust.typing Require Export type.
From lrust.typing Require Import uniq_util gmb_uniq.
From lrust.lifetime Require Import lifetime_full guarded_bor.
From lrust.util Require Import proph_bor.
From guarding Require Import guard tactics.
Set Default Proof Using "Type".

(** Tests of [gmb_lend_uniq] ([typing/gmb_uniq.v]) on a toy instance: the contents of the
    instance are the fancy bytes of the contents type ([cb l fv := fbytes ty l fv]). The
    permission type [pty] and the contents type [ty] are abstract, with the interface of
    [gmb_lend_uniq]; the permission type has the lifetime [static] (every lifetime is
    included in it). *)

Section gmb_uniq_tests.
  Context `{!typeG Σ}.
  Context `{!gmbG Σ loc FValue}.
  Context {𝔄p 𝔄} (pty: type 𝔄p) (ty: type 𝔄) (fv: ~~𝔄 → ~~𝔄p) (fp: 𝔄 → 𝔄p) (fvp: FValue).
  Context (l lp: loc) (tid: thread_id).

  Local Definition cb (l0: loc) (fv0: FValue) : iProp Σ := fbytes ty l0 fv0.
  Local Instance cb_timeless l0 fv0 : Timeless (cb l0 fv0).
  Proof. apply _. Qed.

  Context (Hinj: Inj eq eq fp) (Hcomm: ∀ y π, vπ (fv y) π = fp (vπ y π)).
  Context (Hpf: ∀ v, pty.(ty_fval) v = Some fvp) (Hpz: ∀ v, cbytes pty v lp ⊣⊢ True).
  Context (Hstatic: ∀ κ, ⊢ κ ⊑ ty_lft pty) (Hlft: ⊢ ty_lft pty ⊑ ty_lft ty).
  Context (γ: gmb_name) (Hbm: gmb_bmask γ = lazyB) (Hd: gmb_depth γ = 0).
  Context (HGf: ∀ y' d' g', ty_gho_own pty (fv y') d' g' tid ⊢ |={lazyE}=>
     ∃ fv0, ⌜ty.(ty_fval) y' = Some fv0⌝ ∗ gmb_b γ fv0 ∗ ty_gho_own ty y' d' g' tid).
  Context (HGb: ∀ y' d' g' fv0, ty.(ty_fval) y' = Some fv0 →
     gmb_b γ fv0 ∗ ty_gho_own ty y' d' g' tid ⊢ ty_gho_own pty (fv y') d' g' tid).

  (** The owner shares [gmb_a γ l] at [κ]; the permission is a unique borrow at [κ]; it is
      lent: we get a unique borrow at [κ] of the contents, with the prophecy variable of
      the permission resolved to the new one. The new borrow is then dropped; after [κ]
      ends, the owner gets [gmb_a] back from its share and moves: the move forces the stored
      final contents (the fancy bytes of [ty] at [l]), without the lender and without a
      guard for the lifetime of [ty]. *)
  Lemma test_gmb_uniq_abandoned y d g fv0 :
    ty.(ty_fval) y = Some fv0 →
    llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ gmb_inv cb γ -∗ gmb_a γ l -∗ gmb_b γ fv0 -∗
    ⧖(S d `max` g) -∗ ▷ ty_gho_own ty y d g tid -∗ ⧗1 -∗ £ 5 -∗ £ (1 + gmb_depth γ) -∗
    |={⊤}=> |={↑Nllft}[∅]▷=> |={⊤}=> ∃ fv1, cb l fv1.
  Proof using All.
    iIntros (Hy) "#LFT #PROPH #UNIQ #Inv A B #⧖ Gho ⧗ £ Pre".
    iMod (llftl_begin with "LFT") as (κ) "[Alive #End]"; first solve_ndisj.
    iMod (llftl_borrow_shared _ κ (gmb_a γ l) with "[A]") as "[#Ga InhA]"; [solve_ndisj|by iNext|].
    iDestruct (guards_remove_later_rhs with "Ga") as "#Ga'".
    (* the permission, as a unique borrow at [κ] *)
    iMod (alloc_uniq_body pty (fv y) d g κ tid lp ⊤ with "LFT PROPH UNIQ ⧖ [Gho B] [] ⧗")
      as (ξi ζi idx) "(Body & _ & _)"; [solve_ndisj| |by rewrite Hpz|].
    { iNext. iApply (HGb with "[$B $Gho]"). done. }
    (* the lend *)
    iMod (gmb_lend_uniq cb pty ty fv fp fvp γ l lp y ξi d g idx κ tid ⊤ (@[κ])
      with "LFT PROPH UNIQ Inv Ga' [] [] [] Alive £ Pre Body") as (ζi' ζidx) "(_ & _ & Alive)";
      [exact Hcomm|done|exact Hbm|intros ?? Hx; rewrite /cb; iIntros "B"; by iApply (fbytes_cbytes with "B")|
       intros ?; by rewrite /cb|exact Hpf|exact Hpz|exact HGf|exact HGb| | | |].
    { iApply Hstatic. } { iApply Hlft. } { iApply guards_refl. }
    (* end [κ]; the owner moves *)
    iModIntro. iMod ("End" with "Alive") as "Dead". iModIntro. iNext. iMod "Dead" as "#Dead".
    iModIntro. iMod ("InhA" with "Dead") as ">A".
    iMod (gmb_move cb with "Inv A") as (fv1) "[C _]"; first (rewrite Hbm /lazyB; solve_ndisj).
    iModIntro. by iExists fv1.
  Qed.
End gmb_uniq_tests.
