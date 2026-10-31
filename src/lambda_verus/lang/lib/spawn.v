From iris.program_logic Require Import weakestpre.
From iris.base_logic.lib Require Import invariants.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From lrust.lang Require Import proofmode notation heap lifting.
From lrust.lang Require Export lang.
Set Default Proof Using "Type".

(** A thread whose result is a MiniRust value of type [m]. The shared block [c] holds a
    flag (an [MBool], at [c]) and the result (at [c +ₗ 1]). *)
Definition spawn (m : mty) : val :=
  λ: ["f"],
    let: "c" := Alloc #(Z.of_nat (1 + mty_size m)) in
    Store Na1Ord MBool "c" (MLit (VBool false));; (* Initialize the flag (non-atomically). *)
    Fork ("f" ["c"]);;
    "c".
Definition finish (m : mty) : val :=
  λ: ["c"; "v"],
    Store Na1Ord m ("c" +ₗ #1) "v";; (* Store the result (non-atomically). *)
    Store ScOrd MBool "c" (MLit (VBool true));; (* Signal that we finished (atomically!) *)
    #☠.
Definition join (m : mty) : val :=
  rec: "join" ["c"] :=
    if: ToLit (Load ScOrd MBool "c") then
      (* The thread finished, we can non-atomically load the result. *)
      let: "v" := Load Na1Ord m ("c" +ₗ #1) in
      Free #(Z.of_nat (1 + mty_size m)) "c";;
      "v"
    else
      "join" ["c"].

(** The CMRA & functor we need. *)
Class spawnG Σ := SpawnG { spawn_tokG :: inG Σ (exclR unitO) }.
Definition spawnΣ : gFunctors := #[GFunctor (exclR unitO)].

Global Instance subG_spawnΣ {Σ} : subG spawnΣ Σ → spawnG Σ.
Proof. solve_inG. Qed.

(** Now we come to the Iris part of the proof. *)
Section proof.
Context `{!lrustGS Σ, !spawnG Σ} (N : namespace) (m : mty).

Definition flag_bytes (b : bool) : list abyte := encode_value MBool (VBool b).

Definition spawn_inv (γf γj : gname) (c : loc) (Ψ : val → iProp Σ) : iProp Σ :=
  (own γf (Excl ()) ∗ own γj (Excl ()) ∨
   ∃ b, c ↦b flag_bytes b ∗
        if b then ∃ v, ⌜val_wf m v⌝ ∗ (c +ₗ 1) ↦b encode_value m v ∗ Ψ (MLitV v) ∗
          own γf (Excl ()) else True)%I.

Definition finish_handle (c : loc) (Ψ : val → iProp Σ) : iProp Σ :=
  (∃ γf γj bs, own γf (Excl ()) ∗ (c +ₗ 1) ↦b bs ∗ ⌜length bs = mty_size m⌝ ∗
    inv N (spawn_inv γf γj c Ψ))%I.

Definition join_handle (c : loc) (Ψ : val → iProp Σ) : iProp Σ :=
  (∃ γf γj Ψ', own γj (Excl ()) ∗ † c … (1 + mty_size m) ∗ inv N (spawn_inv γf γj c Ψ') ∗
   □ (∀ v, Ψ' v -∗ Ψ v))%I.

Global Instance spawn_inv_ne n γf γj c :
  Proper (pointwise_relation val (dist n) ==> dist n) (spawn_inv γf γj c).
Proof. solve_proper. Qed.
Global Instance finish_handle_ne n c :
  Proper (pointwise_relation val (dist n) ==> dist n) (finish_handle c).
Proof. solve_proper. Qed.
Global Instance join_handle_ne n c :
  Proper (pointwise_relation val (dist n) ==> dist n) (join_handle c).
Proof. solve_proper. Qed.

Lemma flag_bytes_length b : length (flag_bytes b) = 1%nat.
Proof. by rewrite /flag_bytes length_encode_value. Qed.

Lemma flag_bytes_decode b : decode_value MBool (flag_bytes b) = Some (VBool b).
Proof. apply decode_encode_value; constructor. Qed.

(** The main proofs. *)
Lemma spawn_spec E (Ψ : val → iProp Σ) e (f : val) :
  ↑naN ⊆ E →
  IntoVal e f →
  {{{ ∀ c, finish_handle c Ψ -∗ WP f [ #c] {{ _, True }} }}}
    spawn m [e] @ E {{{ c, RET #c; join_handle c Ψ }}}.
Proof.
  iIntros (? <- Φ) "Hf HΦ". rewrite /spawn /=.
  wp_lam. wp_bind (Alloc _). iApply wp_alloc_bytes; [lia|done|].
  iIntros "!>" (l sz) "(%Hsz & H† & Hl)". wp_let.
  iMod (own_alloc (Excl ())) as (γf) "Hγf"; first done.
  iMod (own_alloc (Excl ())) as (γj) "Hγj"; first done.
  have -> : sz = (1 + mty_size m)%nat by lia.
  rewrite replicate_add heap_mapsto_bytes_app.
  iDestruct "Hl" as "[Hc Hd]".
  wp_bind (Store _ _ _ _).
  iApply (wp_store_na with "Hc"); [done|constructor|done|].
  iNext. iIntros "Hc". wp_seq.
  iMod (inv_alloc N _ (spawn_inv γf γj l Ψ) with "[Hc]") as "#?".
  { iNext. iRight. iExists false. auto. }
  wp_apply (wp_fork with "[Hγf Hf Hd]").
  - iApply "Hf". iExists _, _, _. iFrame. rewrite length_replicate. auto.
  - iIntros "_". wp_seq. iApply "HΦ". iExists _, _, _.
    iFrame. auto.
Qed.
Hypothesis HN : @subseteq coPset set_subseteq_instance ( ↑naN ) (⊤ ∖ ↑N).

Lemma finish_spec E (Ψ : val → iProp Σ) c v :
  ↑naN ∪ ↑N ⊆ E → val_wf m v →
  {{{ finish_handle c Ψ ∗ Ψ (MLitV v) ∗ £1 }}} finish m [ #c; MLitV v] @ E {{{ RET #☠; True }}}.
Proof using HN.
  iIntros (? Hwf Φ) "[Hfin [HΨ £]] HΦ". iDestruct "Hfin" as (γf γj bs) "(Hf & Hd & %Hbs & #?)".
  wp_lam. wp_op.
  wp_bind (Store _ _ _ _).
  iApply (wp_store_na with "Hd"); [set_solver|done|done|].
  iNext. iIntros "Hd". wp_seq.
  wp_bind (Store _ _ _ _). iInv N as "[[>Hf' _]|Hinv]" "Hclose".
  { iExFalso. iCombine "Hf" "Hf'" as "Hf". iDestruct (own_valid with "Hf") as "%".
    auto. }
  iDestruct "Hinv" as (b) "[>Hc _]".
  iApply (wp_store_sc with "Hc"); [set_solver|constructor|by rewrite flag_bytes_length|].
  iNext. iIntros "Hc".
  iMod ("Hclose" with "[-HΦ]").
  - iNext. iRight. iExists true. by iFrame.
  - iModIntro. wp_seq. by iApply "HΦ".
Qed.

Lemma join_spec (Ψ : val → iProp Σ) c :
  mty_wf m →
  {{{ join_handle c Ψ }}} join m [ #c] {{{ v, RET v; Ψ v }}}.
Proof using HN.
  iIntros (Hm Φ) "H HΦ". iDestruct "H" as (γf γj Ψ') "(Hj & H† & #? & #HΨ')".
  iLöb as "IH". wp_rec.
  wp_bind (Load _ _ _). iInv N as "[[_ >Hj']|Hinv]" "Hclose".
  { iExFalso. iCombine "Hj" "Hj'" as "Hj". iDestruct (own_valid with "Hj") as "%".
    auto. }
  iDestruct "Hinv" as (b) "[>Hc Ho]".
  iApply (wp_load_sc with "Hc"); [apply flag_bytes_decode|]. iIntros "!> Hc".
  destruct b; last first.
  { iMod ("Hclose" with "[Hc]").
    - iNext. iRight. iExists _. iFrame.
    - iModIntro. wp_pure _. wp_if. iApply ("IH" with "Hj H†"). auto. }
  iDestruct "Ho" as (v) "(%Hwf & Hd & HΨ & Hf)".
  iMod ("Hclose" with "[Hj Hf]") as "_".
  { iNext. iLeft. iFrame. }
  iModIntro. wp_pure _. wp_if. wp_op.
  wp_bind (Load _ _ _).
  iApply (wp_load_na with "Hd"); [by apply decode_encode_value|]. iIntros "!> Hd". wp_let.
  iAssert (c ↦b (flag_bytes true ++ encode_value m v))%I with "[Hc Hd]" as "Hc".
  { rewrite heap_mapsto_bytes_app flag_bytes_length. iFrame. }
  wp_bind (Free _ _).
  iApply (wp_free_bytes with "[$Hc H†]"); [done|..].
  { by rewrite /= length_encode_value. }
  { rewrite /= length_encode_value. by iFrame. }
  iIntros "!> _". wp_seq.
  iApply "HΦ". iApply "HΨ'". done.
Qed.

Lemma join_handle_impl (Ψ1 Ψ2 : val → iProp Σ) c :
  □ (∀ v, Ψ1 v -∗ Ψ2 v) -∗ join_handle c Ψ1 -∗ join_handle c Ψ2.
Proof.
  iIntros "#HΨ Hhdl". iDestruct "Hhdl" as (γf γj Ψ') "(Hj & H† & #? & #HΨ')".
  iExists γf, γj, Ψ'. iFrame "#∗". iIntros "!> * ?".
  iApply "HΨ". iApply "HΨ'". done.
Qed.

End proof.

Global Typeclasses Opaque finish_handle join_handle.
