From iris.proofmode Require Import proofmode.
From lrust.typing Require Export type programs cont int product uninit value_ctx own uniq_util place_own place_resolve place_sum place_write place_memcpy.
From lrust.lang Require Import lang notation new_delete.
Set Default Proof Using "Type".

(** * Moved-out places

Moves leave the moved-out leaf [Moved ty] at the hole ([type_move_place_instr],
[type_memcpy_move_place_instr]); a write re-initializes it ([pctx_wty_moved]), also inside the
payload of a sum place, whose type cannot change; [type_uninit_oplace_instr] turns an owned
place made of moved-out leaves back into an uninitialized one. *)

Section place_moved.
  Context `{!typeG Σ}.

  Notation i32t := (int_ty i32).
  (* [P]: a [repr(C)] struct of two [i32]. *)
  Notation Pl := [intₛ i32; intₛ i32].
  Notation PL := (c_layout [MInt i32; MInt i32]).
  Notation Pₛ := (structₛ PL Pl).
  Notation Pt := (struct_ty PL +[i32t; i32t]).
  Notation boxt := (own_bytes 4 i32t).
  Notation optt := (Σ! +[(); boxt])%T.
  Notation optₛ := (Σ! [()%ST; at_locₛ (intₛ i32)])%ST.

  Local Notation E := ([]: elctx).

  (** The payload of a sum place, moved out: [let v = ( *x).0] for
      [x: Box<Option<Box<i32>>>] at the variant [Some]. *)
  Lemma move_sum_payload L I p :
    let K := POwn 5 (PSum +[(); boxt]%T 1%fin ((1%positive, 0%Z), 0%Z) PHole) in
    typed_instr E L I +[p ◁ₗ pctx_plug K (OfTy boxt)] (!ᵐ{MPtr} (pctx_vexpr K p))
      (λ v, +[v ◁ᵥ boxt; p ◁ₗ pctx_plug K (Moved boxt)])
      (λ post '-[x], post -[pctx_get K x.1; x]).
  Proof. intros K. apply (type_move_place_instr _ _ _ p K boxt). Qed.

  (** Re-initializing the moved-out payload of a sum place, with a value of its type. *)
  Lemma reinit_sum_payload L I p pb :
    let K := POwn 5 (PSum +[(); boxt]%T 1%fin ((1%positive, 0%Z), 0%Z) PHole) in
    typed_instr E L I +[p ◁ₗ pctx_plug K (Moved boxt); pb ◁ᵥ boxt]
      (pctx_vexpr K p <-{MPtr} pb)
      (λ _, +[p ◁ₗ pctx_plug K (OfTy boxt)])
      (λ post '-[x; b], λ mask π, True → post -[(pctx_set K x.1 b, x.2)] mask π).
  Proof.
    intros K. apply (type_write_place_instr _ _ _ p pb K (Moved boxt) boxt K (pctx_set K)
      (λ _ _, True)); [by apply pctx_wty_moved|apply lty_wres_moved|solve_typing].
  Qed.

  (*
  ```
  fn replace_payload(mut x: Box<Option<Box<i32>>>, y: Box<i32>) -> Box<Option<Box<i32>>> {
      // x is Some(_)
      let z = x.0;   // move the payload out: x.0 is moved-out, x is still Some
      x.0 = y;       // re-initialize it
      drop(z);
      x
  }
  ```

  The payload is at offset [tag_size] (1 byte) of the pointee of [x]. *)
  Definition replace_payload : expr := (
    let: "z" := !ᵐ{MPtr} ("x" +ₗ #1) in                (* move ( *x).0 out *)
    ("x" +ₗ #1) <-{MPtr} "y";;                           (* ( *x).0 = y *)
    (#☠;; delete [ #4; "z"]);;                            (* drop z: a box of i32 *)
    jump: "return" ["x"])%E.

  Definition ret_opt : predl_trans' [at_locₛ optₛ] (at_locₛ optₛ) := λ post '-[r], post r.

  Lemma replace_payload_type ϝ (k vx vy: val) :
    ⊢ typed_body [] [ϝ ⊑ₗ []] (InvCtx [] ϝ AtomicClosed)
        [k ◁cont{[ϝ ⊑ₗ []], InvCtx [] ϝ AtomicClosed,
          λ v: vec val 1, +[vhd v ◁ᵥ own_bytes 5 optt] } ret_opt]
        +[vx ◁ₗown{5} SumLty +[(); boxt]%T 1%fin (OfTy boxt); vy ◁ᵥ boxt]
        (subst "return" k (subst "x" vx (subst "y" vy replace_payload)))
        (λ post '-[((l, s), _); b], λ mask π, post (l, pinj (Xl:=[()%ST; at_locₛ (intₛ i32)]) 1%fin b) mask π).
  Proof.
    rewrite /replace_payload. simpl_subst.
    iApply (typed_body_impl with "[]"); last first. {
      (* move ( *x).0 out *)
      iApply (type_let with "[]").
      { apply (type_move_place_instr _ _ _ vx
          (POwn 5 (PSum +[(); boxt]%T 1%fin ((1%positive, 0%Z), 0%Z) PHole)) boxt). }
      { solve_typing. } { reflexivity. }
      iIntros (vz). simpl_subst.
      (* ( *x).0 = y *)
      iApply type_seq.
      { eapply (type_write_place_instr _ _ _ vx vy
          (POwn 5 (PSum +[(); boxt]%T 1%fin ((1%positive, 0%Z), 0%Z) PHole)) (Moved boxt) boxt);
          [by apply pctx_wty_moved|apply lty_wres_moved|solve_typing]. }
      { solve_typing. } { reflexivity. }
      (* drop z *)
      iApply typed_body_tctx_incl.
      { eapply (tctx_incl_frame_l _ _ +[_]). apply tctx_own_to_oplace. }
      iApply type_seq.
      { apply (type_drop_oplace_instr _ _ _ vz 4 4 (OfTy i32t) (const (const True)));
          [done|done|done|apply lty_resolve_just]. }
      { solve_typing. } { reflexivity. }
      (* fold the sum back; return x *)
      iApply typed_body_tctx_incl.
      { eapply tctx_incl_trans; [apply (tctx_fold_oplace_sum _ _ _ _ PHole +[(); boxt]%T 1%fin)|].
        apply tctx_oplace_to_own. }
      iApply type_jump.
      { rewrite elem_of_list_singleton. reflexivity. }
      { solve_typing. }
      { solve_typing. }
      { reflexivity. }
    }
    intros post [[[l s] ζm] [b []]] mask π Hspec.
    rewrite /trans_upper /trans_tail /trans_lower /ret_opt /=. intros _ _. exact Hspec.
  Qed.

  (** A box whose contents have been moved out, field by field, is uninitialized again. *)
  Lemma uninit_moved_pair L I p :
    typed_instr E L I +[p ◁ₗown{8} StructLty PL +[Moved i32t; Moved i32t]]
      (drop_boxes (StructLty PL +[Moved i32t; Moved i32t]) p;; Skip)%E
      (λ _, +[p ◁ₗown{8} OfTy (↯ 8)])
      (λ post '-[x], λ mask π, True → post -[((x.1.1, ()), [])] mask π).
  Proof.
    apply (type_uninit_oplace_instr _ _ _ p 8 (StructLty PL +[Moved i32t; Moved i32t]) (λ _ _, True));
      [done|done|apply lty_resolve_just].
  Qed.
End place_moved.

Print Assumptions replace_payload_type.
