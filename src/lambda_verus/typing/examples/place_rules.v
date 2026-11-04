From iris.proofmode Require Import proofmode.
From lrust.typing Require Export type programs cont int product value_ctx own shr_bor uniq_util uniq_bor place_own place_puniq place_resolve place_pshr place_res place_res_rslv place_res_ops place_read place_share.
From lrust.lang Require Import lang notation new_delete.
Set Default Proof Using "Type".

(** * Instances of the unified place rules

Single instructions on places, typed by the unified rules with their side conditions
discharged as in the examples ([solve_typing], the constructors of the leaf relations):
- reading a resolved leaf [OfRes] ([type_read_place_instr], [lty_rleaf]);
- reading through a shared reference in the view of a resolved unique borrow;
- sharing in the view of a resolved unique borrow below an owned pointer
  ([type_share_place_instr], [lty_sleaf_view]);
- sharing a shared-blocked leaf again, in an owned place, below a unique borrow and in the
  view of a resolved unique borrow ([lty_sleaf_shrblk]);
- resolving a unique borrow with a compound referent at the root of a place
  ([type_resolve_place_instr], [pctx_res_root], [vroot_res_uniq_cpd]).

The lifetimes: [κ ⊑ β] (a shared-blocked leaf at [β] is shared again at [κ]). *)

Section place_rules.
  Context `{!typeG Σ}.

  Notation i32t := (int_ty i32).
  (* [P]: a [repr(C)] struct of two [i32]. *)
  Notation Pl := [intₛ i32; intₛ i32].
  Notation PL := (c_layout [MInt i32; MInt i32]).
  Notation Pₛ := (structₛ PL Pl).
  Notation Pt := (struct_ty PL +[i32t; i32t]).

  Local Notation E := ([]: elctx).
  Local Notation L α β κ := ([κ ⊑ₗ [β]; β ⊑ₗ [α]; α ⊑ₗ []]: llctx).

  (** [*x] for [x: Box<i32>] resolved: a resolved leaf is readable. *)
  Lemma read_ofres α β κ I p :
    let K := POwn 4 (PHole (𝔅:=intₛ i32)) in
    typed_instr E (L α β κ) I +[p ◁ₗ pctx_plug K (OfRes i32t)] (!ᶜ{MInt i32} (pctx_vexpr K p))
      (λ v, +[v ◁ᵥ i32t; p ◁ₗ pctx_plug K (OfRes i32t)])
      (λ post '-[x], post -[pctx_get K x.1; x]).
  Proof.
    intros K. apply (type_read_place_instr _ _ _ p K (OfRes i32t) i32t static);
      [by apply lty_rleaf_res; [|apply _]|apply _|solve_typing].
  Qed.

  (** [***x] for [x: Box<&'α mut &'β i32>] whose unique borrow is resolved: through the
      shared reference in the view. *)
  Lemma read_res_shr α β κ I p :
    let K := POwn PTR_SIZE (PResUniq α (PShr β (PHole (𝔅:=intₛ i32)))) in
    typed_instr E (L α β κ) I +[p ◁ₗ pctx_plug K (OfTy i32t)] (!ᶜ{MInt i32} (pctx_vexpr K p))
      (λ v, +[v ◁ᵥ i32t; p ◁ₗ pctx_plug K (OfTy i32t)])
      (λ post '-[x], post -[pctx_get K x.1; x]).
  Proof.
    intros K. apply (type_read_place_instr _ _ _ p K (OfTy i32t) i32t static);
      [by split|apply _|solve_typing].
  Qed.

  (** [&( **x).0] for [x: Box<&'α mut P>] whose unique borrow is resolved: shared
      at [α], the lifetime of the view. *)
  Lemma share_res_own α β κ I p :
    let K := POwn PTR_SIZE (PResUniq α (PField PL +[] (PHole (𝔅:=intₛ i32)) +[OfTy i32t])) in
    typed_instr E (L α β κ) I +[p ◁ₗ pctx_plug K (OfTy i32t)] (&ˢ (pctx_vexpr K p))
      (λ v, +[v ◁ᵥ &shr{α} i32t; p ◁ₗ pctx_plug K (OfTy i32t)])
      (λ post '-[x], post -[(pctx_vloc K (lty_size (OfTy i32t)) x.1, pctx_get K x.1); x]).
  Proof.
    intros K. apply (type_share_place_instr _ _ _ p K α (OfTy i32t) i32t (OfTy i32t));
      [split; [constructor|done]|simpl; solve_typing..].
  Qed.

  (** [&*x] again, for [x: Box<i32>] shared-blocked at [β]: shared at [κ ⊑ β]. *)
  Lemma reshare_own α β κ I p :
    let K := POwn 4 (PHole (𝔅:=intₛ i32)) in
    typed_instr E (L α β κ) I +[p ◁ₗ pctx_plug K (ShrBlocked i32t β)] (&ˢ (pctx_vexpr K p))
      (λ v, +[v ◁ᵥ &shr{κ} i32t; p ◁ₗ pctx_plug K (ShrBlocked i32t β)])
      (λ post '-[x], post -[(pctx_vloc K (lty_size (ShrBlocked i32t β)) x.1,
        pctx_get K x.1); x]).
  Proof.
    intros K. apply (type_share_place_instr _ _ _ p K κ (ShrBlocked i32t β) i32t (ShrBlocked i32t β));
      [constructor; solve_typing|simpl; solve_typing..].
  Qed.

  (** [&( *x).0] again, for [x: &'α mut P] (a place rooted at its value) whose
      field is shared-blocked at [β]. *)
  Lemma reshare_uniq α β κ I p :
    let K := PUniq α (PField PL +[] (PHole (𝔅:=intₛ i32)) +[OfTy i32t]) in
    typed_instr E (L α β κ) I +[p ◁ₗ pctx_plug K (ShrBlocked i32t β)] (&ˢ (pctx_vexpr K p))
      (λ v, +[v ◁ᵥ &shr{κ} i32t; p ◁ₗ pctx_plug K (ShrBlocked i32t β)])
      (λ post '-[x], post -[(pctx_vloc K (lty_size (ShrBlocked i32t β)) x.1,
        pctx_get K x.1); x]).
  Proof.
    intros K. apply (type_share_place_instr _ _ _ p K κ (ShrBlocked i32t β) i32t (ShrBlocked i32t β));
      [constructor; solve_typing|simpl; solve_typing..].
  Qed.

  (** [&( **x).0], for [x: Box<&'α mut P>] whose unique borrow is resolved while
      the field was shared-blocked at [β]: shared at [κ ⊑ α, β]. *)
  Lemma reshare_res α β κ I p :
    let K := POwn PTR_SIZE (PResUniq α (PField PL +[] (PHole (𝔅:=intₛ i32)) +[OfTy i32t])) in
    typed_instr E (L α β κ) I +[p ◁ₗ pctx_plug K (ShrBlocked i32t β)] (&ˢ (pctx_vexpr K p))
      (λ v, +[v ◁ᵥ &shr{κ} i32t; p ◁ₗ pctx_plug K (ShrBlocked i32t β)])
      (λ post '-[x], post -[(pctx_vloc K (lty_size (ShrBlocked i32t β)) x.1,
        pctx_get K x.1); x]).
  Proof.
    intros K. apply (type_share_place_instr _ _ _ p K κ (ShrBlocked i32t β) i32t (ShrBlocked i32t β));
      [split; [constructor; solve_typing|done]|simpl; solve_typing..].
  Qed.

  (** Resolving [x: &'α mut P] at its root, its referent unfolded as a pair
      ([vroot_res_uniq_cpd]): [fin(x)] is the current value of the pair. *)
  Lemma resolve_root_cpd α β κ I p :
    let lt := StructLty PL +[OfTy i32t; OfTy i32t] in
    typed_instr E (L α β κ) I +[p ◁ₗ pctx_plug PHole (UniqLty lt α)] (Skip;; #☠)
      (const +[p ◁ₗ pctx_plug PHole (ResUniqLty lt α)])
      (λ post '-[x], λ mask π,
        (π (uniq_prvar (uniq_bor_current (𝔄:=Pₛ) x.1)
          (uniq_bor_ξi (𝔄:=Pₛ) x.1))).1 =
          prfn_den (lty_rfn lt (uniq_bor_current (𝔄:=Pₛ) x.1) x.2 []) π →
        post -[x] mask π).
  Proof.
    intros lt. eapply typed_instr_tr_impl; last first.
    { eapply (type_resolve_place_instr _ _ _ p PHole (UniqLty lt α));
        [apply pctx_res_root; apply vroot_res_uniq_cpd; [solve_typing|solve_typing|done|done]|done]. }
    by intros post [x []] mask π.
  Qed.
End place_rules.
