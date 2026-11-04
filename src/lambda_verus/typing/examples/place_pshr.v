From iris.proofmode Require Import proofmode.
From lrust.typing Require Export type programs cont int unit sum value_ctx own shr_bor uniq_util uniq_bor place_own place_puniq place_resolve place_pshr place_read place_share.
From lrust.lang Require Import lang notation new_delete.
Set Default Proof Using "Type".

(** * Places below shared references, on bytes

The examples of the deleted legacy example file [place_pshr.v], on bytes ([typing/place_pshr.v]): the
reads, shared borrows and case analyses below shared references are guarded typed [Load]s,
whose addresses are computed by guarded typed loads of the pointers on the path. The
arguments are MiniRust values ([◁ᵥ]): a shared reference ([get_snd], the root of the place
is the reference itself), a box of bytes holding a shared reference ([get_boxed],
[get_or_zero], the root is the box) and a unique borrow of a shared reference
([first_ref], the root is the unique borrow). *)

Section place_pshr.
  Context `{!typeG Σ}.

  Notation i32t := (int_ty i32).
  (* [P]: a [repr(C)] struct of two [i32]. *)
  Notation Pl := [intₛ i32; intₛ i32].
  Notation PL := (c_layout [MInt i32; MInt i32]).
  Notation Pₛ := (structₛ PL Pl).
  Notation Pt := (struct_ty PL +[i32t; i32t]).
  (* [B]: a [repr(C)] struct of an [i32] and a box of an [i32]. *)
  Notation Bl := [intₛ i32; at_locₛ (intₛ i32)].
  Notation BL := (c_layout [MInt i32; MPtr]).
  Notation Bt := (struct_ty BL +[i32t; own_bytes 4 i32t]).

  Definition ret_z : predl_trans' [intₛ i32] (intₛ i32) := λ post '-[z], post z.

  (*
  ```
  fn get_snd<'a, 'b>(x: &'a &'b P) -> i32 { ( **x).1 }
  ```
  The argument is a shared reference value, the root of the place; the view of its
  referent is changed to [ShrLty (StructLty PL +[OfTy i32; OfTy i32]) 'b] (no program
  step), and [( **x).1] is read with [K2 = PShr 'b (PField PL +[_] PHole +[])]: a guarded
  load of the inner
  reference, a field offset, and a guarded typed load of [i32].
  *)
  Definition get_snd_pb : expr := (
    let: "v" := !ᶜ{MInt i32} ((Load Na1Ord MPtr "x") +ₗ #(struct_off PL Pl 1)) in
    jump: "return" ["v"])%E.

  Lemma get_snd_pb_type ϝ α β (k vx: val) :
    ⊢ typed_body [ϝ ⊑ₑ α; α ⊑ₑ β] [ϝ ⊑ₗ []] (InvCtx [] ϝ AtomicClosed)
        [k ◁cont{[ϝ ⊑ₗ []], InvCtx [] ϝ AtomicClosed, λ v: vec val 1, +[vhd v ◁ᵥ i32t] } ret_z]
        +[vx ◁ᵥ &shr{α} (&shr{β} Pt)]
        (subst "return" k (subst "x" vx get_snd_pb))
        (λ post '-[(_, (_, z))], λ mask π, post (phd (ptl z)) mask π).
  Proof.
    rewrite /get_snd_pb. simpl_subst.
    iApply (typed_body_impl with "[]"); last first. {
      iApply typed_body_tctx_incl.
      { eapply tctx_incl_trans; [apply tctx_ty_to_vplace|].
        eapply tctx_incl_trans; [apply tctx_vplace_unfold_shr|].
        apply (tctx_change_vplace_shr _ _ vx α PHole (OfTy (&shr{β} Pt))
          (ShrLty (StructLty PL +[OfTy i32t; OfTy i32t]) β)); [done|done|by intros]. }
      (* ( **x).1 *)
      iApply (type_let with "[]").
      { apply (type_read_place_instr _ _ _ vx (PShr α (PShr β (PField PL +[OfTy i32t] PHole +[])))
          (OfTy i32t) i32t static); [by split|apply _|solve_typing]. }
      { solve_typing. } { reflexivity. }
      iIntros (vv). simpl_subst.
      (* drop x *)
      iApply typed_body_tctx_incl. { eapply tctx_incl_tail. apply tctx_drop_vplace_shr. }
      iApply type_jump.
      { rewrite elem_of_list_singleton. reflexivity. }
      { solve_typing. }
      { solve_typing. }
      { reflexivity. }
    }
    intros post [[l1 [l2 [z1 [z2 []]]]] []] mask π. simpl.
    rewrite /trans_upper /trans_tail /ret_z /=. auto.
  Qed.

  (*
  ```
  fn get_boxed(b: Box<&'a B>) -> i32 { *( **b).1 }
  ```
  The argument is a box of bytes, the root of the place: the shared reference in it is
  unfolded ([K = PHole] of the own-rooted place), the view of its referent is changed to
  [StructLty BL +[OfTy i32; OwnPtrLty 4 (OfTy i32)]], and the leaf is read below [PShr]
  through the inner box ([K2 = PField BL +[_] (POwn 4 PHole) +[]]). Dropping the slot frees the outer box (the
  inner one belongs to the referent of the shared reference).
  *)
  Definition get_boxed_pb : expr := (
    ReBor;;                                                    (* unfold *b *)
    ReBor;;                                                    (* view **b as a pair *)
    let: "v" := !ᶜ{MInt i32}
      (Load Na1Ord MPtr ((Load Na1Ord MPtr "b") +ₗ #(struct_off BL Bl 1))) in  (* *( **b).1 *)
    (#☠;; delete [ #(Z.of_nat PTR_SIZE); "b"]);;         (* drop b *)
    jump: "return" ["v"])%E.

  Lemma get_boxed_pb_type ϝ α (k vb: val) :
    ⊢ typed_body [ϝ ⊑ₑ α] [ϝ ⊑ₗ []] (InvCtx [] ϝ AtomicClosed)
        [k ◁cont{[ϝ ⊑ₗ []], InvCtx [] ϝ AtomicClosed, λ v: vec val 1, +[vhd v ◁ᵥ i32t] } ret_z]
        +[vb ◁ᵥ own_bytes PTR_SIZE (&shr{α} Bt)]
        (subst "return" k (subst "b" vb get_boxed_pb))
        (λ post '-[(_, (_, zs))], λ mask π, post (phd (ptl zs)).2 mask π).
  Proof.
    rewrite /get_boxed_pb. simpl_subst.
    iApply (typed_body_impl with "[]"); last first. {
      iApply typed_body_tctx_incl; [apply tctx_own_to_oplace|].
      (* unfold *b *)
      iApply type_seq.
      { apply (type_unfold_oplace_shr_instr _ _ _ vb PTR_SIZE PHole α Bt).
        solve_typing. }
      { solve_typing. } { reflexivity. }
      (* view **b as a pair with a box *)
      iApply type_seq.
      { apply (type_change_oplace_shr_instr _ _ _ vb PTR_SIZE PHole α PHole
          (OfTy Bt) (StructLty BL +[OfTy i32t; OwnPtrLty 4 (OfTy i32t)]));
          [solve_typing|done|done|by intros]. }
      { solve_typing. } { reflexivity. }
      (* *( **b).1 *)
      iApply (type_let with "[]").
      { apply (type_read_place_instr _ _ _ vb
          (POwn PTR_SIZE (PShr α (PField BL +[OfTy i32t] (POwn 4 PHole) +[]))) (OfTy i32t) i32t static);
          [by split|apply _|solve_typing]. }
      { solve_typing. } { reflexivity. }
      iIntros (vv). simpl_subst.
      (* drop b *)
      iApply type_seq.
      { apply (type_drop_oplace_deep_instr _ _ _ vb PTR_SIZE (Z.of_nat PTR_SIZE)
          (ShrLty (StructLty BL +[OfTy i32t; OwnPtrLty 4 (OfTy i32t)]) α)); [done|done|done|].
        apply lty_rslv_shr. }
      { solve_typing. } { reflexivity. }
      iApply type_jump.
      { rewrite elem_of_list_singleton. reflexivity. }
      { solve_typing. }
      { solve_typing. }
      { reflexivity. }
    }
    intros post [[lb [l1 [z [[lb' w] []]]]] []] mask π. simpl.
    rewrite /trans_upper /trans_tail /ret_z /=. auto.
  Qed.
  (*
  ```
  fn get_or_zero(b: Box<&'a Option<i32>>) -> i32 {
      match **b { Some(v) => v, None => 0 }
  }
  ```
  The discriminant of `**b` is read through the shared reference with a guarded typed load
  ([type_case_oplace_pshr], [K = PHole], [K2 = PHole]); in the branch of `Some`, the view
  of the referent is the enum place [SumLty OL _ 1 (OfTy i32)] and its payload is read
  ([K2 = PSum OL _ 1 _ PHole], at the offset [enum_off OL Ol 1] of the payload). The
  layout is the tagged one ([tagged_layout]), whose discriminator reads once.
  *)
  Notation Ol := [unitₛ; intₛ i32].
  Notation OL := (tagged_layout [zst_mty; MInt i32]).
  Notation opt_i32 := (enum_ty OL +[(); i32t])%T.
  Notation opt_i32ₛ := (enumₛ OL Ol)%ST.

  Definition get_or_zero_pb : expr := (
    ReBor;;                                                    (* unfold *b *)
    case: (GetDiscr (syn_mty opt_i32ₛ) (Load Na1Ord MPtr "b")) of
    [ (#☠;; delete [ #(Z.of_nat PTR_SIZE); "b"]);;       (* None: drop b *)
      let: "z" := MLit (VInt 0) in
      jump: "return" ["z"];
      let: "v" := !ᶜ{MInt i32} ((Load Na1Ord MPtr "b") +ₗ #(enum_off OL Ol 1)) in
      (#☠;; delete [ #(Z.of_nat PTR_SIZE); "b"]);;       (* Some(v): drop b *)
      jump: "return" ["v"]])%E.

  Definition get_or_zero_pb_spec : predl_trans' [at_locₛ (at_locₛ opt_i32ₛ)] (intₛ i32) :=
    λ post '-[(_, m)], λ mask π,
      (m.2 = pinj (Xl:=[unitₛ; intₛ i32]) 0%fin () → post 0%Z mask π) ∧
      (∀ v, m.2 = pinj (Xl:=[unitₛ; intₛ i32]) 1%fin v → post v mask π).

  Lemma get_or_zero_pb_type ϝ α (k vb: val) :
    ⊢ typed_body [ϝ ⊑ₑ α] [ϝ ⊑ₗ []] (InvCtx [] ϝ AtomicClosed)
        [k ◁cont{[ϝ ⊑ₗ []], InvCtx [] ϝ AtomicClosed, λ v: vec val 1, +[vhd v ◁ᵥ i32t] } ret_z]
        +[vb ◁ᵥ own_bytes PTR_SIZE (&shr{α} opt_i32)]
        (subst "return" k (subst "b" vb get_or_zero_pb)) get_or_zero_pb_spec.
  Proof.
    rewrite /get_or_zero_pb. simpl_subst.
    iApply (typed_body_impl with "[]"); last first. {
      iApply typed_body_tctx_incl; [apply tctx_own_to_oplace|].
      (* unfold *b *)
      iApply type_seq.
      { apply (type_unfold_oplace_shr_instr _ _ _ vb PTR_SIZE PHole α opt_i32). solve_typing. }
      { solve_typing. } { reflexivity. }
      (* match **b *)
      iApply (type_case_oplace_pshr _ _ _ _ vb PTR_SIZE PHole α PHole +[(); i32t]%T _ _ _
        -[_; _]); [by vm_compute|solve_typing|solve_typing|].
      iSplitL; [|iSplitL; [|done]].
      - (* None: drop b *)
        iApply type_seq.
        { apply (type_drop_oplace_deep_instr _ _ _ vb PTR_SIZE (Z.of_nat PTR_SIZE)
            (ShrLty (SumLty OL +[(); i32t]%T 0%fin (OfTy ())) α)); [done|done|done|].
          apply lty_rslv_shr. }
        { solve_typing. } { simpl. reflexivity. }
        iApply (type_let with "[]"). { by apply (type_val_int_instr i32 0). }
        { solve_typing. } { reflexivity. }
        iIntros (vz). simpl_subst.
        iApply type_jump.
        { rewrite elem_of_list_singleton. reflexivity. }
        { solve_typing. }
        { solve_typing. }
        { reflexivity. }
      - (* Some(v): read v *)
        iApply (type_let with "[]").
        { apply (type_read_place_instr _ _ _ vb
            (POwn PTR_SIZE (PShr α (PSum OL +[(); i32t]%T 1%fin 0%Z PHole))) (OfTy i32t) i32t static);
            [by split|apply _|solve_typing]. }
        { solve_typing. } { simpl. reflexivity. }
        iIntros (vv). simpl_subst.
        iApply type_seq.
        { apply (type_drop_oplace_deep_instr _ _ _ vb PTR_SIZE (Z.of_nat PTR_SIZE)
            (ShrLty (SumLty OL +[(); i32t]%T 1%fin (OfTy i32t)) α)); [done|done|done|].
          apply lty_rslv_shr. }
        { solve_typing. } { reflexivity. }
        iApply type_jump.
        { rewrite elem_of_list_singleton. reflexivity. }
        { solve_typing. }
        { solve_typing. }
        { reflexivity. }
    }
    intros post [[lb [l1 s]] []] mask π. simpl.
    intros [Hnone Hsome]. destruct s as [[]|[v|[]]]; simpl.
    - intros _. by eapply Hnone.
    - intros _. by eapply Hsome.
  Qed.

  (*
  ```
  fn first_ref<'a, 'b>(x: &'a mut &'b P) -> &'b i32 { &( **x).0 }
  ```
  The argument is a unique borrow value, the root of the place: `**x` (a shared reference,
  below [PUniq 'a], in [Uniq] mode) is unfolded and the view of `***x` is changed to a
  struct; `&( **x).0` is a shared reference at ['b] ([type_share_place_instr],
  [K = PUniq 'a (PShr 'b (PField PL +[] PHole +[_]))]): the shared reference stored in `*x` is
  loaded from the body of the unique borrow, so the result does not depend on ['a] (as in
  Rust); the place is folded back and `x` is resolved to its current value.
  *)
  Definition first_ref_pb : expr := (
    Skip;;                                                     (* x as a place *)
    ReBor;;                                                    (* unfold **x *)
    ReBor;;                                                    (* view ***x as a pair *)
    let: "r" := &ˢ ((Load Na1Ord MPtr "x") +ₗ #(struct_off PL Pl 0)) in (* &( **x).0 *)
    ReBor;; ReBor;;                                            (* fold back *)
    Skip;;                                                     (* resolve x *)
    jump: "return" ["r"])%E.

  Definition ret_ref : predl_trans' [at_locₛ (intₛ i32)] (at_locₛ (intₛ i32)) :=
    λ post '-[r], post r.

  Definition first_ref_pb_spec :
      predl_trans' [uniq_borₛ (at_locₛ Pₛ)] (at_locₛ (intₛ i32)) :=
    λ post '-[m], λ mask π, ∀ r: ~~ (at_locₛ (intₛ i32)),
      r.2 = phd (uniq_bor_current (𝔄:=at_locₛ Pₛ) m).2 →
      uniq_bor_future (𝔄:=at_locₛ Pₛ) m π =
        vπ (uniq_bor_current (𝔄:=at_locₛ Pₛ) m) π →
      post r mask π.

  Lemma first_ref_pb_type ϝ α β (k vx: val) :
    ⊢ typed_body [ϝ ⊑ₑ α; α ⊑ₑ β] [ϝ ⊑ₗ []] (InvCtx [] ϝ AtomicClosed)
        [k ◁cont{[ϝ ⊑ₗ []], InvCtx [] ϝ AtomicClosed,
          λ v: vec val 1, +[vhd v ◁ᵥ &shr{β} i32t] } ret_ref]
        +[vx ◁ᵥ &uniq{α} (&shr{β} Pt)]
        (subst "return" k (subst "x" vx first_ref_pb)) first_ref_pb_spec.
  Proof.
    rewrite /first_ref_pb. simpl_subst.
    iApply (typed_body_impl with "[]"); last first. {
      (* x as a place rooted at its value *)
      iApply type_seq. { apply (type_uniq_to_vplace_instr _ _ _ vx α (&shr{β} Pt)). }
      { solve_typing. } { reflexivity. }
      (* unfold **x *)
      iApply type_seq.
      { apply (type_unfold_vplace_shr_instr _ _ _ vx (PUniq α PHole) β Pt).
        solve_typing. }
      { solve_typing. } { reflexivity. }
      (* view ***x as a pair *)
      iApply type_seq.
      { apply (type_change_vplace_shr_instr _ _ _ vx (PUniq α PHole) β PHole
          (OfTy Pt) (StructLty PL +[OfTy i32t; OfTy i32t])); [solve_typing|done|done|by intros]. }
      { solve_typing. } { reflexivity. }
      (* &( **x).0 *)
      iApply (type_let with "[]").
      { eapply (type_share_place_instr _ _ _ vx (PUniq α (PShr β (PField PL +[] PHole +[OfTy i32t])))
          β (OfTy i32t) i32t); [by split|simpl; solve_typing..]. }
      { solve_typing. } { reflexivity. }
      iIntros (vr). simpl_subst.
      (* fold back *)
      iApply type_seq.
      { apply (type_change_vplace_shr_instr _ _ _ vx (PUniq α PHole) β PHole
          (StructLty PL +[OfTy i32t; OfTy i32t]) (OfTy Pt)); [solve_typing|done|done|by intros]. }
      { solve_typing. } { reflexivity. }
      iApply type_seq.
      { apply (type_fold_vplace_shr_instr _ _ _ vx (PUniq α PHole) β Pt).
        solve_typing. }
      { solve_typing. } { reflexivity. }
      (* resolve x *)
      iApply typed_body_tctx_incl.
      { eapply (tctx_incl_frame_r +[_] +[_]). apply tctx_vplace_to_uniq. }
      iApply type_seq.
      { apply (type_resolve_val_instr vx (&uniq{α} (&shr{β} Pt))).
        apply uniq_bor.uniq_resolve. solve_typing. }
      { solve_typing. } { reflexivity. }
      iApply type_jump.
      { rewrite elem_of_list_singleton. reflexivity. }
      { solve_typing. }
      { solve_typing. }
      { reflexivity. }
    }
    intros post [m []] mask π. simpl.
    destruct m as [[[[[l [l' [z1 [z2 []]]]] ξi] d] g] idx]. simpl.
    intros Hspec. rewrite /trans_upper /trans_tail /ret_ref /=.
    intros d' g' idx' Hres. apply Hspec; [done|]. by rewrite uniq_bor_future_eq.
  Qed.
End place_pshr.

Print Assumptions get_snd_pb_type.
Print Assumptions get_boxed_pb_type.
Print Assumptions get_or_zero_pb_type.
Print Assumptions first_ref_pb_type.
