From iris.proofmode Require Import proofmode.
From lrust.typing Require Export type programs cont int product uninit value_ctx own_bytes
  shr_bytes uniq_util uniq_bytes place_own place_shr place_resolve subtype pcell_bytes
  pcell_bytes_borrow.
From lrust.lang Require Import lang notation new_delete.
Set Default Proof Using "Type".

(** * [PCell] on bytes

The example of [typing/examples/pcell_example.v] on the byte layer (§10 step 5 of
[design_docs/pcell-multibyte-cells.md]): a box is initialized with [17], made into a cell
([PCellbFromOwn]: the box holds the pair of the cell and its permission), both fields are
shared, the contents are borrowed through them ([PCellbBorrow]) and read. The body is
stated as a function body ([typed_body], with the return continuation [k]) that returns
the value read, and its specification says that this value is [17] (instead of the call
of [assert] of the legacy example). *)

Section pcell_example_bytes.
  Context `{!typeG Σ}.

  Notation i32t := (int_ty i32).

  (*
  ```
  fn pcell_example() -> i32 {
      let (pcell, Tracked(pointsto)) = PCell::new(17);
      let pcell_shr_ref = &pcell;
      let tracked pointsto_shr_ref = &pointsto;
      let intref = pcell_shr_ref.borrow(Tracked(pointsto_shr_ref));
      *intref
  }
  ```
  *)
  Definition pcell_example_b : expr := (
    let: "p" := OfLit (Alloc #4) in                         (* a box of 4 bytes *)
    let: "seventeen" := MLit (VInt 17) in
    Store Na1Ord (MInt i32) (ToLit "p") "seventeen";;       (* *p = 17 *)
    let: "pair" := PCellbFromOwn ["p"] in                    (* (PCell, PointsTo) *)
    Newlft;;
    let: "pcell_ref" := Share;; OfLit (ToLit "pair") in      (* &pair.0 *)
    let: "perm_ref" := Share;; OfLit (ToLit "pair" +ₗ #4) in  (* &pair.1 *)
    let: "intref" := PCellbBorrow ["pcell_ref"; "perm_ref"] in
    let: "x" := Load Na1Ord (MInt i32) (ToLit "intref") in   (* *intref *)
    Endlft;;
    (#☠;; delete [ #4; ToLit "pair"]);;                       (* drop the pair *)
    jump: "return" ["x"])%E.

  Definition ret_z : predl_trans' [intₛ i32] (intₛ i32) := λ post '-[z], post z.

  Lemma pcell_example_b_type ϝ (k: val) :
    ⊢ typed_body [] [ϝ ⊑ₗ []] (InvCtx [] ϝ AtomicClosed)
        [k ◁cont{[ϝ ⊑ₗ []], InvCtx [] ϝ AtomicClosed, λ v: vec val 1, +[vhd v ◁ᵥ i32t] } ret_z]
        +[] (subst "return" k pcell_example_b)
        (λ post '-[], λ mask π, post 17%Z mask π).
  Proof.
    rewrite /pcell_example_b. simpl_subst.
  Abort.
End pcell_example_bytes.
