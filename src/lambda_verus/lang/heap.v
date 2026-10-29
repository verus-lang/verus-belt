Require Import guarding.internal.na_invariants_fork.
From lrust.util Require Import non_atomic_cell_map atomic_lock_counter.
From guarding Require Import guard.
From Coq.Arith Require Import PeanoNat.
From stdpp Require Import coPset.
From iris.algebra Require Import big_op gmap frac agree numbers.
From iris.algebra Require Import csum excl auth cmra_big_op.
From iris.bi Require Import fractional.
From iris.base_logic Require Export lib.own.
From iris.proofmode Require Export proofmode.
From lrust.lang Require Export lang.
From iris.prelude Require Import options.
Import uPred.

(** * The heap

Physical memory holds abstract bytes ([state' = gmap loc (lock_state * abyte)]).
Its ghost state has two regions, with disjoint domains (see [phys_rel]):
- the legacy region, a [non_atomic_map] of [val]s (with cells), which backs the
  legacy points-to [l ↦ v] and all its fancy and cell variants: a location of
  this region holding [v] holds the byte [word_to_byte v] physically;
- the byte region, a lambda-Rust-style fractional heap of [abyte]s (no cells),
  which backs the byte points-to [l ↦b{q} bs].
The legacy layer cannot simply be defined on top of the byte region: its
untethering lemmas (e.g. [mapsto_vec_untether1]) return the contents of a cell
as a [val], so the cell map must hold [val]s; and multi-byte non-atomic reads
through the cell map would need one later per byte. A location moves between the
regions with [heap_word_to_bytes] and [heap_bytes_to_word] (no physical step). *)

Definition lock_stateR : cmra :=
  csumR (exclR unitO) natR.

Canonical Structure abyteO := leibnizO abyte.

Definition heapUR : ucmra :=
  gmapUR loc (prodR (prodR fracR lock_stateR) (agreeR abyteO)).

Definition heap_freeableUR : ucmra :=
  gmapUR block (prodR fracR (gmapR Z (exclR unitO))).

Class heapGS Σ := HeapGS {
  #[global] heap_inG :: inG Σ (authR heapUR);
  #[global] heap_freeable_inG :: inG Σ (authR heap_freeableUR);
  #[global] heap_na_logicG :: na_logicG loc val Σ;
  heap_name : gname;
  heap_bytes_name : gname;
  heap_freeable_name : gname;
  atomic_threadpool: gname;
  atomic_lock_ctr_name: gname
}.

Definition heap_freeable_rel (σ : state) (hF : heap_freeableUR) : Prop :=
  ∀ blk qs, hF !! blk = Some qs →
    qs.2 ≠ ∅ ∧ ∀ i, is_Some (σ.1 !! (blk, i)) ↔ is_Some (qs.2 !! i).

Section definitions.
  Context `{!heapGS Σ}.
  Context `{!invGS Σ}.
  Context `{!na_invG Σ}.
  Context `{!alc_logicG Σ}.
  
  Definition heap_mapsto'
      (lc: loc + cell_id) (cells: list cell_id) (cv: cell_id + val) : iProp Σ
      := lc @↦[heap_name][^ cells] cv.

  Definition heap_mapsto (l : loc) (v: val) : iProp Σ :=
    (inl l) @↦[heap_name][^ []] (inr v).

  Definition heap_mapsto_vec (l : loc) (vl : list val) : iProp Σ :=
    ([∗ list] i ↦ v ∈ vl, heap_mapsto (l +ₗ i) v)%I.

  Fixpoint inter (i0 : Z) (n : nat) : gmapR Z (exclR unitO) :=
    match n with O => ∅ | S n => <[i0 := Excl ()]>(inter (i0+1) n) end.

  Definition heap_freeable_def (l : loc) (q : Qp) (n: nat) : iProp Σ :=
    own heap_freeable_name (◯ {[ l.1 := (q, inter (l.2) n) ]}).
  Definition heap_freeable_aux : seal (@heap_freeable_def). Proof. by eexists. Qed.
  Definition heap_freeable := unseal heap_freeable_aux.
  Definition heap_freeable_eq : @heap_freeable = @heap_freeable_def :=
    seal_eq heap_freeable_aux.
  
  Definition heap_ato_ctx : iProp Σ := 
      na_invariants_fork.na_own atomic_threadpool ⊤ ∗ atomic_lock_ctr atomic_lock_ctr_name 0 ⊤.

  Definition to_lock_stateR (x : lock_state) : lock_stateR :=
    match x with RSt n => Cinr n | WSt => Cinl (Excl ()) end.
  Definition to_heap : gmap loc (lock_state * abyte) → heapUR :=
    fmap (λ p, (1%Qp, to_lock_stateR (p.1), to_agree (p.2))).

  (** The physical memory [σ] is the union of the legacy region [σL] (whose
      words are stored as [word_to_byte]) and the byte region [σB]. *)
  Definition phys_rel (σ : state') (σL : gmap loc (lock_state * val))
      (σB : gmap loc (lock_state * abyte)) : Prop :=
    ∀ l, match σL !! l, σB !! l with
         | Some (ls, v), None => σ !! l = Some (ls, word_to_byte v)
         | None, Some p => σ !! l = Some p
         | None, None => σ !! l = None
         | Some _, Some _ => False
         end.

  Definition heap_maps_ctx (σ : state') : iProp Σ :=
    ∃ σL σB, ⌜phys_rel σ σL σB⌝ ∗ non_atomic_map heap_name σL
           ∗ own heap_bytes_name (● to_heap σB).

  Definition heap_ctx (σ:state) : iProp Σ :=
    (∃ hF, heap_maps_ctx σ.1
         ∗ own heap_freeable_name (● hF)
         ∗ ⌜heap_freeable_rel σ hF⌝
         ∗ (match σ.2 with true => True | false => heap_ato_ctx end))%I.
         
  Definition cell_id := positive.
  
  Inductive fancy_val :=
    | FVal (v: val)
    | FCell (c: cell_id).
    
  Definition fv2sum (fv: fancy_val) :=
      match fv with | FVal v => inr v | FCell c => inl c end.
      
  Definition sum2fv (cv: cell_id + val) :=
      match cv with | inl c => FCell c | inr v => FVal v end.
  
  Definition cloc1: Type := loc * list cell_id. 
  Definition cloc: Type := loc * list (list cell_id).
  
  Definition of_cloc (l: cloc) : loc := (l.1).
  
  Definition to_cloc (l: loc) : cloc := (l, []).
     
  Definition heap_mapsto_fancy (l: loc) (fv: fancy_val) : iProp Σ :=
      inl l @↦[heap_name] (fv2sum fv).
  
  Definition heap_mapsto_cells_fancy (l: loc) (cells: list cell_id) (fv: fancy_val) : iProp Σ :=
      inl l @↦[heap_name][^ cells] (fv2sum fv).
      
  Fixpoint heap_mapsto_cells_fancy_vec (l: loc) (cells: list (list cell_id)) (fvs: list fancy_val) : iProp Σ :=
      match cells, fvs with
          | [], [] => True%I
          | cell :: cells', fv :: fvs' => inl l @↦[heap_name][^ cell] (fv2sum fv) ∗ heap_mapsto_cells_fancy_vec (l +ₗ 1) cells' fvs'
          | _, _ => False%I
      end.
  
  Definition heap_mapsto_fancy_vec (l: loc) (fv: list fancy_val) : iProp Σ :=
      heap_mapsto_cells_fancy_vec l (repeat [] (length fv)) fv.
  
  Definition heap_mapsto_cells_val_vec (l: loc) (cells: list (list cell_id)) (v: list val) : iProp Σ :=
      heap_mapsto_cells_fancy_vec l cells (FVal <$> v).
  
  Definition split_at_last {A} (l: list A) : option (list A * A) :=
      match List.rev l with
        | [] => None
        | x :: xs => Some (List.rev xs, x)
      end.
  
  Definition heap_complete_mapsto (l: cloc1) : iProp Σ :=
      match split_at_last (snd l) with
          | Some (cells, last_cell) => inl (fst l) @↦[heap_name][^ cells] (inl last_cell)
          | None => True%I
      end.
      
  Definition heap_complete_mapsto_fancy (l: cloc1) (fv: fancy_val) : iProp Σ :=
      (match split_at_last (snd l) with
          | Some (_, last_cell) => inr last_cell 
          | None => inl (fst l) 
      end) @↦[heap_name] (fv2sum fv).
      
  Fixpoint heap_complete_mapsto_vec' (l: loc) (cs: list (list cell_id)) : iProp Σ :=
      match cs with
        | [] => True%I
        | c :: cells =>
            heap_complete_mapsto (l, c) ∗ heap_complete_mapsto_vec' (l +ₗ 1) cells
      end.
  
  Definition heap_complete_mapsto_vec (l: cloc) : iProp Σ :=
      heap_complete_mapsto_vec' (fst l) (snd l).
      
  Fixpoint heap_complete_mapsto_fancy_vec' (l: loc) (cs: list (list cell_id)) (fvs: list fancy_val) : iProp Σ :=
      match cs, fvs with
        | [], [] => True%I
        | c :: cells, fv :: fvs =>
            heap_complete_mapsto_fancy (l, c) fv ∗ heap_complete_mapsto_fancy_vec' (l +ₗ 1) cells fvs
        | _, _ => False%I
      end.
  
  Definition heap_complete_mapsto_fancy_vec (l: cloc) (fvs: list fancy_val) : iProp Σ :=
      heap_complete_mapsto_fancy_vec' (fst l) (snd l) fvs.
  
  Definition heap_complete_mapsto_val_vec (l: cloc) (v: list val) : iProp Σ :=
      heap_complete_mapsto_fancy_vec l (FVal <$> v).
  
  Definition cell_points_to_value (c : cell_id) (v : val) : iProp Σ :=
      inr c @↦[heap_name] (inr v).

  Definition cell_points_to_fancy_value (c : cell_id) (fv : fancy_val) : iProp Σ :=
      inr c @↦[heap_name] (fv2sum fv).
  
  Fixpoint cells_points_to_fancy_value_vec (cells : list cell_id) (fvs : list fancy_val) : iProp Σ := match cells, fvs with
      | [], [] => True%I
      | cell :: cells, fv :: fvs => (inr cell) @↦[heap_name] (fv2sum fv) ∗ cells_points_to_fancy_value_vec cells fvs
      | _, _ => False%I
      end.
      
  Global Instance heap_complete_mapsto_fancy_vec'_timeless l cs fvs : Timeless (heap_complete_mapsto_fancy_vec' l cs fvs). 
  Proof. generalize l, fvs. clear l. clear fvs. induction cs.
    - simpl. apply _. - intros l fvs. simpl. destruct fvs; first by apply _.
      apply sep_timeless; apply _.
  Qed.

  Global Instance heap_complete_mapsto_fancy_vec_timeless l fv : Timeless (heap_complete_mapsto_fancy_vec l fv). 
  Proof. apply _. Qed.

  Global Instance cell_points_to_value_timeless c v : Timeless (cell_points_to_value c v).
  Proof. apply _. Qed.
  Global Instance cell_points_to_fancy_value_timeless c fv : Timeless (cell_points_to_fancy_value c fv). 
  Proof. apply _. Qed.
  Global Instance cells_points_to_fancy_value_vec_timeless cells fv : Timeless (cells_points_to_fancy_value_vec cells fv).
  Proof.
    induction cells in fv |- *.
    - simpl. apply _.
    - simpl. destruct fv; first by apply _. apply sep_timeless; apply _.
  Qed.

End definitions.

Global Typeclasses Opaque heap_mapsto heap_freeable heap_mapsto_vec.
Global Instance: Params (@heap_mapsto) 4 := {}.
Global Instance: Params (@heap_freeable) 5 := {}.

Notation "l ↦ v" := (heap_mapsto l v) (at level 20) : bi_scope.

Notation "c ^↦ v" := (cell_points_to_value c v) (at level 20) : bi_scope.
Notation "c ^↦! fv" := (cell_points_to_fancy_value c fv) (at level 20) : bi_scope.
Notation "cs ^↦!∗ fl" := (cells_points_to_fancy_value_vec cs fl) (at level 20) : bi_scope.

Notation "l #↦_" := (heap_complete_mapsto l) (at level 20) : bi_scope.
Notation "l #↦! fv" := (heap_complete_mapsto_fancy l fv) (at level 20) : bi_scope.
Notation "l #↦ v" := (heap_complete_mapsto_fancy l (FVal v)) (at level 20) : bi_scope.

Notation "l #↦∗_" := (heap_complete_mapsto_vec l) (at level 20) : bi_scope.
Notation "l #↦!∗ fv" := (heap_complete_mapsto_fancy_vec l fv) (at level 20) : bi_scope.
Notation "l #↦∗ v" := (heap_complete_mapsto_val_vec l v) (at level 20) : bi_scope.

Notation "l ↦[^ c ] v" := (heap_mapsto_cells_fancy l c (FVal v)) (at level 20) : bi_scope.
Notation "l ↦[^ c ]! fv" := (heap_mapsto_cells_fancy l c fv) (at level 20) : bi_scope.
Notation "l ↦! fv" := (heap_mapsto_fancy l fv) (at level 20) : bi_scope.

Notation "l ↦[^ c ]∗ v" := (heap_mapsto_cells_val_vec l c v) (at level 20) : bi_scope.
Notation "l ↦[^ c ]!∗ fv" := (heap_mapsto_cells_fancy_vec l c fv) (at level 20) : bi_scope.

Notation "l ↦!∗ fv" := (heap_mapsto_fancy_vec l fv) (at level 20) : bi_scope.

Notation "l ↦∗ vl" := (heap_mapsto_vec l vl) (at level 20) : bi_scope.

Notation "l ↦∗: P " := (∃ vl, l ↦∗ vl ∗ P vl)%I
  (at level 20, format "l  ↦∗:  P") : bi_scope.
Notation "l #↦!∗: P " := (∃ vl, l #↦!∗ vl ∗ P vl)%I
  (at level 20, format "l  #↦!∗:  P") : bi_scope.

Notation "†{ q } l … n" := (heap_freeable l q n)
  (at level 20, q at level 50, format "†{ q } l … n") : bi_scope.
Notation "† l … n" := (heap_freeable l 1 n) (at level 20) : bi_scope.

Section kmap_lemmas.

  Local Unset Default Proof Using.
  Context `{FinMap nat M1} `{FinMap K2 M2}.
  Context (f : nat → K2) `{!Inj (=) (=) f}.
  (* Local Notation kmap := (kmap (M1:=M1) (M2:=M2)). *)
  Lemma kmap_map_seq_shift {A} (n : nat) (l : list A) :
    @kmap K2 M2 _ _ nat M1 _ A f (@map_seq A (M1 A) _ _ n l) = kmap (λ i, f (n + i)%nat) (map_seq 0 l).
  Proof using All.
    apply map_eq. intros i. apply option_eq; intros y.
    rewrite lookup_kmap_Some.
    setoid_rewrite lookup_kmap_Some => //.
    2: { intros a b Heq%Inj0. lia. }
    split.
    - intros [j [-> [? Hlookup]%lookup_map_seq_Some]].
      exists (j - n)%nat.
      replace (n + (j - n))%nat with j by lia.
      split => //.
      rewrite lookup_map_seq_Some.
      split; first lia.
      by rewrite Nat.sub_0_r.
    - intros [j [-> [? Hlookup]%lookup_map_seq_Some]].
      exists (n + j)%nat.
      split => //.
      rewrite lookup_map_seq_Some.
      split; first lia.
      move: Hlookup.
      by rewrite Nat.add_sub' Nat.sub_0_r.
  Qed.

End kmap_lemmas.


(** ** The physical relation *)
Section phys_rel.
  Implicit Types σ : state'.

  Lemma phys_rel_lookup_L σ σL σB l ls v :
    phys_rel σ σL σB → σL !! l = Some (ls, v) → σ !! l = Some (ls, word_to_byte v).
  Proof. intros Hr Hl. specialize (Hr l). rewrite Hl in Hr. by destruct (σB !! l). Qed.

  Lemma phys_rel_lookup_B σ σL σB l p :
    phys_rel σ σL σB → σB !! l = Some p → σ !! l = Some p.
  Proof.
    intros Hr Hl. specialize (Hr l). rewrite Hl in Hr. by destruct (σL !! l) as [[]|].
  Qed.

  Lemma phys_rel_B_not_L σ σL σB l :
    phys_rel σ σL σB → is_Some (σB !! l) → σL !! l = None.
  Proof.
    intros Hr [p Hl]. specialize (Hr l). rewrite Hl in Hr. by destruct (σL !! l) as [[]|].
  Qed.

  Lemma phys_rel_L_not_B σ σL σB l :
    phys_rel σ σL σB → is_Some (σL !! l) → σB !! l = None.
  Proof.
    intros Hr [[ls v] Hl]. specialize (Hr l). rewrite Hl in Hr. by destruct (σB !! l).
  Qed.

  Lemma phys_rel_None σ σL σB l :
    phys_rel σ σL σB → σ !! l = None → σL !! l = None ∧ σB !! l = None.
  Proof.
    intros Hr Hl. specialize (Hr l).
    destruct (σL !! l) as [[]|], (σB !! l); simplify_eq; done.
  Qed.

  (** An update of the byte region, at locations of the byte region. *)
  Lemma phys_rel_B_update σ σ' σL σB σB' :
    phys_rel σ σL σB →
    (∀ l, (σ' !! l = σ !! l ∧ σB' !! l = σB !! l) ∨
          (is_Some (σB !! l) ∧ is_Some (σB' !! l) ∧ σ' !! l = σB' !! l)) →
    phys_rel σ' σL σB'.
  Proof.
    intros Hr Hupd l. specialize (Hr l). destruct (Hupd l) as [[-> ->]|(HB&[p Hp]&->)]; [done|].
    destruct HB as [p0 Hp0]. rewrite Hp0 in Hr. rewrite Hp.
    destruct (σL !! l) as [[]|]; done.
  Qed.

  Lemma phys_rel_L_insert σ σL σB l ls v :
    phys_rel σ σL σB → σB !! l = None →
    phys_rel (<[l:=(ls, word_to_byte v)]> σ) (<[l:=(ls, v)]> σL) σB.
  Proof.
    intros Hr HB l'. destruct (decide (l = l')) as [<-|].
    - by rewrite !lookup_insert HB.
    - rewrite !lookup_insert_ne //. apply Hr.
  Qed.

  Lemma phys_rel_B_insert σ σL σB l p :
    phys_rel σ σL σB → σL !! l = None →
    phys_rel (<[l:=p]> σ) σL (<[l:=p]> σB).
  Proof.
    intros Hr HL l'. destruct (decide (l = l')) as [<-|].
    - by rewrite !lookup_insert HL.
    - rewrite !lookup_insert_ne //. apply Hr.
  Qed.

  Lemma phys_rel_L_delete σ σL σB l :
    phys_rel σ σL σB → σB !! l = None → phys_rel (delete l σ) (delete l σL) σB.
  Proof.
    intros Hr HB l'. destruct (decide (l = l')) as [<-|].
    - by rewrite !lookup_delete HB.
    - rewrite !lookup_delete_ne //. apply Hr.
  Qed.

  Lemma phys_rel_B_delete σ σL σB l :
    phys_rel σ σL σB → σL !! l = None → phys_rel (delete l σ) σL (delete l σB).
  Proof.
    intros Hr HL l'. destruct (decide (l = l')) as [<-|].
    - by rewrite !lookup_delete HL.
    - rewrite !lookup_delete_ne //. apply Hr.
  Qed.

  Lemma phys_rel_L_to_B σ σL σB l ls v :
    phys_rel σ σL σB → σL !! l = Some (ls, v) →
    phys_rel σ (delete l σL) (<[l:=(ls, word_to_byte v)]> σB).
  Proof.
    intros Hr HL l'. destruct (decide (l = l')) as [<-|].
    - rewrite lookup_delete lookup_insert. by eapply phys_rel_lookup_L.
    - rewrite lookup_delete_ne // lookup_insert_ne //. apply Hr.
  Qed.

  Lemma phys_rel_B_to_L σ σL σB l ls v :
    phys_rel σ σL σB → σB !! l = Some (ls, word_to_byte v) →
    phys_rel σ (<[l:=(ls, v)]> σL) (delete l σB).
  Proof.
    intros Hr HB l'. destruct (decide (l = l')) as [<-|].
    - rewrite lookup_delete lookup_insert. by eapply phys_rel_lookup_B.
    - rewrite lookup_delete_ne // lookup_insert_ne //. apply Hr.
  Qed.

  Lemma phys_rel_empty : phys_rel ∅ ∅ ∅.
  Proof. intros l. by rewrite !lookup_empty. Qed.
End phys_rel.

Section heap.
  Context `{!heapGS Σ}.
  Context `{!invGS Σ}.
  Context `{!na_invG Σ}.
  Context `{!alc_logicG Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : state.
  Implicit Types E : coPset.

  (** General properties of mapsto and freeable *)
  Global Instance heap_mapsto_timeless l v : Timeless (l ↦ v).
  Proof. apply points_to_timeless. Qed.

  Global Instance heap_mapsto_vec_timeless l vl : Timeless (l ↦∗ vl).
  Proof. rewrite /heap_mapsto_vec. apply _. Qed.

  Global Instance heap_freeable_timeless q l n : Timeless (†{q}l…n).
  Proof. rewrite heap_freeable_eq /heap_freeable_def. apply _. Qed.

  (*Lemma heap_mapsto_agree l v1 v2 : l ↦ v1 ∗ l ↦ v2 ⊢ ⌜v1 = v2⌝.
  Proof.
    rewrite heap_mapsto_eq -own_op -auth_frag_op own_valid discrete_valid.
    eapply pure_elim; [done|]=> /auth_frag_valid /=.
    rewrite singleton_op -pair_op singleton_valid=> -[? /to_agree_op_inv_L->]; eauto.
  Qed.*)

  Lemma heap_mapsto_vec_nil l : l ↦∗ [] ⊣⊢ True.
  Proof. by rewrite /heap_mapsto_vec. Qed.
  
  Lemma heap_mapsto_fancy_vec_nil l : l ↦!∗ [] ⊣⊢ True.
  Proof. done. Qed.

  Lemma heap_mapsto_vec_app l vl1 vl2 :
    l ↦∗ (vl1 ++ vl2) ⊣⊢ l ↦∗ vl1 ∗ (l +ₗ length vl1) ↦∗ vl2.
  Proof.
    rewrite /heap_mapsto_vec big_sepL_app.
    do 2 f_equiv. intros k v. by rewrite shift_loc_assoc_nat.
  Qed.

  Lemma heap_mapsto_vec_singleton l v : l ↦∗ [v] ⊣⊢ l ↦ v.
  Proof. by rewrite /heap_mapsto_vec /= shift_loc_0 right_id. Qed.

  Lemma heap_mapsto_vec_cons l v vl:
    l ↦∗ (v :: vl) ⊣⊢ l ↦ v ∗ (l +ₗ 1) ↦∗ vl.
  Proof.
    by rewrite (heap_mapsto_vec_app l [v] vl) heap_mapsto_vec_singleton.
  Qed.

(*
  Lemma heap_mapsto_vec_op l vl1 vl2 :
    length vl1 = length vl2 →
    l ↦∗ vl1 ∗ l ↦∗ vl2 ⊣⊢ ⌜vl1 = vl2⌝ ∧ l ↦∗ vl1.
  Proof.
    intros Hlen%Forall2_same_length. apply (anti_symm (⊢)).
    - revert l. induction Hlen as [|v1 v2 vl1 vl2 _ _ IH]=> l.
      { rewrite !heap_mapsto_vec_nil. iIntros "_"; auto. }
      rewrite !heap_mapsto_vec_cons. iIntros "[[Hv1 Hvl1] [Hv2 Hvl2]]".
      iDestruct (IH (l +ₗ 1) with "[$Hvl1 $Hvl2]") as "[% $]"; subst.
      rewrite (inj_iff (.:: vl2)).
      iDestruct (heap_mapsto_agree with "[$Hv1 $Hv2]") as %<-.
      iSplit; first done. iFrame.*)
    (*- by iIntros "[% [$ Hl2]]"; subst.
  Qed.*)

  (*Lemma heap_mapsto_pred_op l q1 q2 n (Φ : list val → iProp Σ) :
    (∀ vl, Φ vl -∗ ⌜length vl = n⌝) →
    l ↦∗{q1}: Φ ∗ l ↦∗{q2}: (λ vl, ⌜length vl = n⌝) ⊣⊢ l ↦∗{q1+q2}: Φ.
  Proof.
    intros Hlen. iSplit.
    - iIntros "[Hmt1 Hmt2]".
      iDestruct "Hmt1" as (vl) "[Hmt1 Hown]". iDestruct "Hmt2" as (vl') "[Hmt2 %]".
      iDestruct (Hlen with "Hown") as %?.
      iCombine "Hmt1" "Hmt2" as "Hmt". rewrite heap_mapsto_vec_op; last congruence.
      iDestruct "Hmt" as "[_ Hmt]". iExists vl. by iFrame.
    - iIntros "Hmt". iDestruct "Hmt" as (vl) "[[Hmt1 Hmt2] Hown]".
      iDestruct (Hlen with "Hown") as %?.
      iSplitL "Hmt1 Hown"; iExists _; by iFrame.
  Qed.*)

  (*Lemma heap_mapsto_pred_wand l q Φ1 Φ2 :
    l ↦∗{q}: Φ1 -∗ (∀ vl, Φ1 vl -∗ Φ2 vl) -∗ l ↦∗{q}: Φ2.
  Proof.
    iIntros "Hm Hwand". iDestruct "Hm" as (vl) "[Hm HΦ]". iExists vl.
    iFrame "Hm". by iApply "Hwand".
  Qed.*)

  (*Lemma heap_mapsto_pred_iff_proper l q Φ1 Φ2 :
    □ (∀ vl, Φ1 vl ↔ Φ2 vl) -∗ □ (l ↦∗{q}: Φ1 ↔ l ↦∗{q}: Φ2).
  Proof.
    iIntros "#HΦ !>". iSplit; iIntros; iApply (heap_mapsto_pred_wand with "[-]"); try done; [|];
    iIntros; by iApply "HΦ".
  Qed.*)

  (*Lemma heap_mapsto_vec_combine l q vl :
    vl ≠ [] →
    l ↦∗{q} vl ⊣⊢ own heap_name (◯ [^op list] i ↦ v ∈ vl,
      {[l +ₗ i := (q, Cinr 0%nat, to_agree v)]}).
  Proof.
    rewrite /heap_mapsto_vec heap_mapsto_eq /heap_mapsto_def /heap_mapsto_st=>?.
    rewrite (big_opL_commute auth_frag) big_opL_commute1 //.
  Qed.*)

  (*Global Instance heap_mapsto_pred_fractional l (P : list val → iProp Σ):
    (∀ vl, Persistent (P vl)) → Fractional (λ q, l ↦∗{q}: P)%I.
  Proof.
    intros p q q'. iSplit.
    - iIntros "H". iDestruct "H" as (vl) "[[Hown1 Hown2] #HP]".
      iSplitL "Hown1"; eauto.
    - iIntros "[H1 H2]". iDestruct "H1" as (vl1) "[Hown1 #HP1]".
      iDestruct "H2" as (vl2) "[Hown2 #HP2]".
      set (ll := min (length vl1) (length vl2)).
      rewrite -[vl1](firstn_skipn ll) -[vl2](firstn_skipn ll) 2!heap_mapsto_vec_app.
      iDestruct "Hown1" as "[Hown1 _]". iDestruct "Hown2" as "[Hown2 _]".
      iCombine "Hown1" "Hown2" as "Hown". rewrite heap_mapsto_vec_op; last first.*)
  (*
      { rewrite !firstn_length. subst ll.
        rewrite -!min_assoc min_idempotent min_comm -min_assoc min_idempotent min_comm. done. }
      iDestruct "Hown" as "[H Hown]". iDestruct "H" as %Hl. iExists (take ll vl1). iFrame.
      destruct (min_spec (length vl1) (length vl2)) as [[Hne Heq]|[Hne Heq]].
      + iClear "HP2". rewrite take_ge; last first.
        { rewrite -Heq /ll. done. }
        rewrite drop_ge; first by rewrite app_nil_r. by rewrite -Heq.
      + iClear "HP1". rewrite Hl take_ge; last first.
        { rewrite -Heq /ll. done. }
        rewrite drop_ge; first by rewrite app_nil_r. by rewrite -Heq.
  Qed. *)
  (*
  Global Instance heap_mapsto_pred_as_fractional l q (P : list val → iProp Σ):
    (∀ vl, Persistent (P vl)) → AsFractional (l ↦∗{q}: P) (λ q, l ↦∗{q}: P)%I q.
  Proof. split; first done. apply _. Qed.*)

  Lemma inter_lookup_Some i j (n : nat):
    i ≤ j < i+n → inter i n !! j = Excl' ().
  Proof.
    revert i. induction n as [|n IH]=>/= i; first lia.
    rewrite lookup_insert_Some. destruct (decide (i = j)); naive_solver lia.
  Qed.
  Lemma inter_lookup_None i j (n : nat):
    j < i ∨ i+n ≤ j → inter i n !! j = None.
  Proof.
    revert i. induction n as [|n IH]=>/= i; first by rewrite lookup_empty.
    rewrite lookup_insert_None. naive_solver lia.
  Qed.
  Lemma inter_op i n n' : inter i n ⋅ inter (i+n) n' ≡ inter i (n+n').
  Proof.
    intros j. rewrite lookup_op.
    destruct (decide (i ≤ j < i+n)); last destruct (decide (i+n ≤ j < i+n+n')).
    - by rewrite (inter_lookup_None (i+n) j n') ?inter_lookup_Some; try lia.
    - by rewrite (inter_lookup_None i j n) ?inter_lookup_Some; try lia.
    - by rewrite !inter_lookup_None; try lia.
  Qed.
  Lemma inter_valid i n : ✓ inter i n.
  Proof. revert i. induction n as [|n IH]=>i; first done. by apply insert_valid. Qed.

  Lemma heap_freeable_op_eq l q1 q2 n n' :
    †{q1}l…n ∗ †{q2}l+ₗ n … n' ⊣⊢ †{q1+q2}l…(n+n').
  Proof.
    by rewrite heap_freeable_eq /heap_freeable_def -own_op -auth_frag_op
      singleton_op -pair_op inter_op.
  Qed.

  (** Properties about heap_freeable_rel and heap_freeable *)
  Lemma heap_freeable_rel_None σ l hF :
    (∀ m : Z, σ.1 !! (l +ₗ m) = None) → heap_freeable_rel σ hF →
    hF !! l.1 = None.
  Proof.
    intros FRESH REL. apply eq_None_not_Some. intros [[q s] [Hsne REL']%REL].
    destruct (map_choose s) as [i []%REL'%not_eq_None_Some]; first done.
    move: (FRESH (i - l.2)). by rewrite /shift_loc Zplus_minus.
  Qed.

  Lemma heap_freeable_is_Some σ hF l n i :
    heap_freeable_rel σ hF →
    hF !! l.1 = Some (1%Qp, inter (l.2) n) →
    is_Some (σ.1 !! (l +ₗ i)) ↔ 0 ≤ i ∧ i < n.
  Proof.
    destruct l as [b j]; rewrite /shift_loc /=. intros REL Hl.
    destruct (REL b (1%Qp, inter j n)) as [_ ->]; simpl in *; auto.
    destruct (decide (0 ≤ i ∧ i < n)).
    - rewrite is_Some_alt inter_lookup_Some; lia.
    - rewrite is_Some_alt inter_lookup_None; lia.
  Qed.

  Lemma heap_freeable_rel_init_mem l h n σ:
    n ≠ O →
    (∀ m : Z, σ.1 !! (l +ₗ m) = None) →
    heap_freeable_rel σ h →
    heap_freeable_rel (init_mem l n $σ σ)
                      (<[l.1 := (1%Qp, inter (l.2) n)]> h).
  Proof.
    move=> Hvlnil FRESH REL blk qs /lookup_insert_Some [[<- <-]|[??]].
    - split.
      { destruct n as [|n]; simpl in *; [done|]. apply: insert_non_empty. }
      intros i. destruct (decide (l.2 ≤ i ∧ i < l.2 + n)).
      + rewrite inter_lookup_Some // lookup_init_mem; naive_solver.
      + rewrite inter_lookup_None; last lia. rewrite lookup_init_mem_ne /=; last lia.
        replace (l.1,i) with (l +ₗ (i - l.2)) by (rewrite /shift_loc; f_equal; lia).
        by rewrite FRESH !is_Some_alt.
    - destruct (REL blk qs) as [? Hs]; auto.
      split; [done|]=> i. by rewrite -Hs lookup_init_mem_ne; last auto.
  Qed.

  Lemma heap_freeable_rel_free_mem σ hF n l :
    hF !! l.1 = Some (1%Qp, inter (l.2) n) →
    heap_freeable_rel σ hF →
    heap_freeable_rel (free_mem l n $σ σ) (delete (l.1) hF).
  Proof.
    intros Hl REL b qs; rewrite lookup_delete_Some=> -[NEQ ?].
    destruct (REL b qs) as [? REL']; auto.
    split; [done|]=> i. by rewrite -REL' lookup_free_mem_ne.
  Qed.

  Lemma heap_freeable_rel_stable σ h l p :
    heap_freeable_rel σ h → is_Some (σ.1 !! l) →
    heap_freeable_rel (<[l := p]>σ.1, σ.2) h.
  Proof.
    intros REL Hσ blk qs Hqs. destruct (REL blk qs) as [? REL']; first done.
    split; [done|]=> i. rewrite -REL' lookup_insert_is_Some.
    destruct (decide (l = (blk, i))); naive_solver.
  Qed.
  
  Lemma lookup_init_mem_prev l n σ :
      init_mem (l +ₗ 1) n σ.1 !! l = σ.1 !! l.
  Proof.
      rewrite lookup_init_mem_ne /=; first by done. right. left. lia.
  Qed.

  (** Weakest precondition *)
  Lemma heap_alloc_vs (σ : state') l n :
    (∀ m : Z, σ !! (l +ₗ m) = None) →
    heap_maps_ctx σ ⊢
    |==> heap_maps_ctx (init_mem l n σ)
       ∗ l ↦∗ (repeat (LitV LitPoison) n).
  Proof.
    generalize l. clear l. induction n.
     - iIntros. iFrame. iModIntro. by rewrite /heap_mapsto_vec.
     - iIntros (l all) "σ". iMod (IHn (l +ₗ 1) with "σ") as "[σ rep]".
        + intros m. rewrite shift_loc_assoc. apply all.
        + iDestruct "σ" as (σL σB) "(%Hr & σ & σB)".
          have Hfresh : init_mem (l +ₗ 1) n σ !! l = None.
          { rewrite lookup_init_mem_ne /=; last lia. rewrite -(shift_loc_0 l). apply all. }
          destruct (phys_rel_None _ _ _ _ Hr Hfresh) as [HL HB].
          iMod (non_atomic_map_insert _ l (LitV LitPoison) with "σ") as "[pt σ]"; first done.
           * iFrame. iSplitR.
             { iPureIntro. by apply (phys_rel_L_insert _ _ _ _ _ (LitV LitPoison)). }
             rewrite /heap_mapsto_vec. simpl. rewrite shift_loc_0.
             rewrite /heap_mapsto. iFrame. setoid_rewrite shift_loc_assoc.
             assert (∀ (i: nat) , (1 + i) = (S i)) as Hi by lia. setoid_rewrite Hi.
             iFrame. done.
  Qed.

  Lemma heap_alloc (σ: state) l n :
    0 < n →
    (∀ m, σ.1 !! (l +ₗ m) = None) →
    heap_ctx σ ==∗
      heap_ctx (init_mem l (Z.to_nat n) $σ σ) ∗ †l…(Z.to_nat n) ∗
      l ↦∗ repeat (LitV LitPoison) (Z.to_nat n).
  Proof.
    intros ??; iDestruct 1 as (hF) "(Hvalσ & HhF & % & ato)".
    assert (Z.to_nat n ≠ O). { rewrite -(Nat2Z.id 0)=>/Z2Nat.inj. lia. }
    iMod (heap_alloc_vs _ _ (Z.to_nat n) with "[$Hvalσ]") as "[Hvalσ Hmapsto]"; first done.
    iMod (own_update _ (● hF) with "HhF") as "[HhF Hfreeable]".
    { apply auth_update_alloc,
        (alloc_singleton_local_update _ (l.1) (1%Qp, inter (l.2) (Z.to_nat n))).
      - eauto using heap_freeable_rel_None.
      - split; first done. apply inter_valid. }
    iModIntro. iSplitL "Hvalσ HhF ato".
    { iExists _. iFrame. iPureIntro.
      auto using heap_freeable_rel_init_mem. }
    rewrite heap_freeable_eq /heap_freeable_def //. iFrame.
  Qed.

  Lemma heap_free_vs (σ : state') l vl E :
    ↑naN ⊆ E →
    heap_maps_ctx σ ∗ l ↦∗ vl
    ⊢ |={E}=> heap_maps_ctx (free_mem l (length vl) σ).
  Proof.
      intros Hmask. generalize l. clear l. induction vl.
     - iIntros (l) "[σ pt]". iFrame. iModIntro. by rewrite /heap_mapsto_vec.
     - rewrite /heap_mapsto_vec. iIntros (l) "[σ [pt ptsep]]".
       iMod (IHvl (l +ₗ 1) with "[σ ptsep]") as "σ".
        { iFrame. rewrite /heap_mapsto_vec.
          assert (∀ (i: nat), (l +ₗ 1 +ₗ i) = (l +ₗ S i)) as Hi.
            { intros i. rewrite shift_loc_assoc. f_equal. lia. }
          setoid_rewrite Hi. iFrame.
        }
       simpl. rewrite shift_loc_0 /heap_mapsto.
       iDestruct "σ" as (σL σB) "(%Hr & σ & σB)".
       iMod (non_atomic_map_delete with "pt σ") as "[%Hst σ]"; first done.
       iModIntro. iFrame. iPureIntro. apply phys_rel_L_delete; [done|].
       by eapply phys_rel_L_not_B.
  Qed.

  Lemma heap_free σ l vl (n : Z) E :
    ↑naN ⊆ E →
    n = length vl →
    heap_ctx σ -∗ l ↦∗ vl -∗ †l…(length vl)
    ={E}=∗ ⌜0 < n⌝ ∗ ⌜∀ m, is_Some (σ.1 !! (l +ₗ m)) ↔ (0 ≤ m < n)⌝ ∗
        heap_ctx (free_mem l (Z.to_nat n) $σ σ).
  Proof.
    iDestruct 1 as (hF) "(Hvalσ & HhF & REL & ato)"; iDestruct "REL" as %REL.
    iIntros "Hmt Hf". rewrite heap_freeable_eq /heap_freeable_def.
    iDestruct (own_valid_2 with "HhF Hf") as % [Hl Hv]%auth_both_valid_discrete.
    move: Hl=> /singleton_included_l [[q qs] [/leibniz_equiv_iff Hl Hq]].
    apply (Some_included_exclusive _ _) in Hq as [=<-<-]%leibniz_equiv; last first.
    { move: (Hv (l.1)). rewrite Hl. by intros [??]. }
    assert (vl ≠ []).
    { intros ->. by destruct (REL (l.1) (1%Qp, ∅)) as [[] ?]. }
    assert (0 < n) by (subst n; by destruct vl).
    iMod (heap_free_vs with "[Hmt Hvalσ]") as "Hvalσ"; first by trivial.
    { iFrame. }
    iMod (own_update_2 with "HhF Hf") as "HhF".
    { apply auth_update_dealloc, (delete_singleton_local_update _ _ _). }
    iModIntro; subst. repeat iSplit;  eauto using heap_freeable_is_Some.
    iExists _. subst. rewrite Nat2Z.id. iFrame.
    eauto using heap_freeable_rel_free_mem.
  Qed.

  (** Legacy operations, through the physical relation *)
  Lemma heap_atomic_read (σ : state') l cells v E G d :
    ↑naN ⊆ E →
    £(d) -∗ (G &&{↑naN;d}&&> (l ↦[^ cells] v)) -∗ G -∗ heap_maps_ctx σ ={E}=∗
      ∃ n, ⌜σ !! l = Some (RSt n, word_to_byte v)⌝ ∗ G ∗ heap_maps_ctx σ.
  Proof.
    iIntros (Hmask) "£ #Gv G (%σL & %σB & %Hr & σ & σB)".
    iMod (atomic_read with "£ [Gv] G σ") as (n) "[%Heq [G σ]]"; [done|by iFrame "Gv"|].
    iModIntro. iExists n. iFrame. iPureIntro. split; [|done]. by eapply phys_rel_lookup_L.
  Qed.

  Lemma heap_na_read_begin (σ : state') l cells v E G d :
    ↑naN ⊆ E →
    £(3*d) -∗ (G &&{↑naN;d}&&> (l ↦[^ cells] v)) -∗ G -∗ heap_maps_ctx σ ={E}=∗
      ∃ n, ⌜σ !! l = Some (RSt n, word_to_byte v)⌝
        ∗ points_to_r_intermediate heap_name l cells v G
        ∗ heap_maps_ctx (<[l := (RSt (n + 1), word_to_byte v)]> σ).
  Proof.
    iIntros (Hmask) "£ #Gv G (%σL & %σB & %Hr & σ & σB)".
    iMod (na_read_begin with "£ [Gv] G σ") as (n) "[%Heq [rim σ]]"; [done|by iFrame "Gv"|].
    iModIntro. iExists n. iFrame. iPureIntro. split; [by eapply phys_rel_lookup_L|].
    apply phys_rel_L_insert; [done|]. by eapply phys_rel_L_not_B.
  Qed.

  Lemma heap_na_read_end (σ : state') l cells v E G :
    ↑naN ⊆ E →
    points_to_r_intermediate heap_name l cells v G -∗ heap_maps_ctx σ -∗ ▷ |={E}=>
      ∃ n, ⌜σ !! l = Some (RSt n, word_to_byte v) ∧ n ≥ 1⌝ ∗ G
        ∗ heap_maps_ctx (<[l := (RSt (n - 1), word_to_byte v)]> σ).
  Proof.
    iIntros (Hmask) "rim (%σL & %σB & %Hr & σ & σB)".
    iDestruct (na_read_end with "rim σ") as "A"; [done|]. iNext.
    iMod "A" as (n) "([%Heq %Hn] & G & σ)". iModIntro. iExists n. iFrame.
    iPureIntro. split; [split; [by eapply phys_rel_lookup_L|done]|].
    apply phys_rel_L_insert; [done|]. by eapply phys_rel_L_not_B.
  Qed.

(*
  Lemma heap_mapsto_lookup σ l ls q v :
    own heap_name (● to_heap σ) -∗
    own heap_name (◯ {[ l := (q, to_lock_stateR ls, to_agree v) ]}) -∗
    ⌜∃ n' : nat,
        σ !! l = Some (match ls with RSt n => RSt (n+n') | WSt => WSt end, v)⌝.
  Proof.
    iIntros "H● H◯".
    iDestruct (own_valid_2 with "H● H◯") as %[Hl?]%auth_both_valid_discrete.
    iPureIntro. move: Hl=> /singleton_included_l [[[q' ls'] dv]].
    rewrite /to_heap lookup_fmap fmap_Some_equiv.
    move=> [[[ls'' v'] [?[[/=??]->]]]]; simplify_eq.
    move=> /Some_pair_included_total_2
      [/Some_pair_included [_ Hincl] /to_agree_included->].
    destruct ls as [|n], ls'' as [|n''],
       Hincl as [[[|n'|]|] [=]%leibniz_equiv]; subst.
    - by exists O.
    - eauto.
    - exists O. by rewrite Nat.add_0_r.
  Qed.

  Lemma heap_mapsto_lookup_1 σ l ls v :
    own heap_name (● to_heap σ) -∗
    own heap_name (◯ {[ l := (1%Qp, to_lock_stateR ls, to_agree v) ]}) -∗
    ⌜σ !! l = Some (ls, v)⌝.
  Proof.
    iIntros "H● H◯".
    iDestruct (own_valid_2 with "H● H◯") as %[Hl?]%auth_both_valid_discrete.
    iPureIntro. move: Hl=> /singleton_included_l [[[q' ls'] dv]].
    rewrite /to_heap lookup_fmap fmap_Some_equiv.
    move=> [[[ls'' v'] [?[[/=??]->]]] Hincl]; simplify_eq.
    apply (Some_included_exclusive _ _) in Hincl as [? Hval]; last by destruct ls''.
    apply (inj to_agree) in Hval. fold_leibniz. subst.
    destruct ls, ls''; rewrite ?Nat.add_0_r; naive_solver.
  Qed.
  *)

  (*Lemma heap_read_vs σ n1 n2 nf l q v:
    σ !! l = Some (RSt (n1 + nf), v) →
    non_atomic_map heap_name σ ⊢ heap_mapsto_st (RSt n1) l q v
    -∗ |==> non_atomic_map heap_name (<[l:=(RSt (n2 + nf), v)]> σ)
        ∗ heap_mapsto_st (RSt n2) l q v.
  Proof.
    intros Hσv. iIntros "H● H◯".
    iMod (own_update_2 _ _ _ (● to_heap (<[l:=(RSt (n2 + nf), b)]> σB) ⋅
      ◯ {[l := (q, to_lock_stateR (RSt n2), to_agree b)]}) with "H● H◯") as "[$ $]"; [|done].
    rewrite to_heap_insert. eapply auth_update, singleton_local_update.
    { by rewrite /to_heap lookup_fmap Hσv. }
    apply prod_local_update_1, prod_local_update_2, csum_local_update_r.
    apply nat_local_update; lia.
  Qed. 
  *)

  Lemma heap_read σ l cells v E :
    ↑naN ⊆ E →
    heap_ctx σ -∗ l ↦[^ cells] v ={E}=∗
    heap_ctx σ ∗ l ↦[^ cells] v ∗ ∃ n, ⌜σ.1 !! l = Some (RSt n, word_to_byte v)⌝.
  Proof.
    iDestruct 1 as (hF) "(Hσ & HhF & REL)". iIntros "Hmt".
    iMod (lc_zero) as "£0".
    iMod (heap_atomic_read with "£0 [] Hmt Hσ") as (n) "[X [Hmt Hσ]]"; first by set_solver.
      { iApply guards_refl. }
    iModIntro. iFrame.
  Qed.

  (*Lemma heap_read_1 σ l cells v E :
    ↑naN ⊆ E →
    heap_ctx σ -∗ l ↦[^ cells] v ={E}=∗
    heap_ctx σ ∗ l ↦[^ cells] v ∗ ⌜σ !! l = Some (RSt 0, v)⌝.
  Proof.
    iDestruct 1 as (hF) "(Hσ & HhF & REL)". iIntros "Hmt".
    iMod (points_to_heap_reading0 with "Hmt Hσ") as "(Hmt & Hσ & Heq0)"; first by trivial.
    iModIntro. iFrame.
  Qed.*)

(*
  Lemma heap_read_na σ l q v :
    heap_ctx σ -∗ l ↦{q} v ==∗ ∃ n,
      ⌜σ !! l = Some (RSt n, v)⌝ ∗
      heap_ctx (<[l:=(RSt (S n), v)]> σ) ∗
      ∀ σ2, heap_ctx σ2 ==∗ ∃ n2, ⌜σ2 !! l = Some (RSt (S n2), v)⌝ ∗
        heap_ctx (<[l:=(RSt n2, v)]> σ2) ∗ l ↦{q} v.
  Proof.
    iDestruct 1 as (hF) "(Hσ & HhF & %)"; iIntros "Hmt".
    rewrite heap_mapsto_eq.
    iDestruct (heap_mapsto_lookup with "Hσ Hmt") as %[n Hσl]; eauto.
    iMod (heap_read_vs _ 0 1 with "Hσ Hmt") as "[Hσ Hmt]"; first done.
    iModIntro. iExists n; iSplit; [done|]. iSplitL "HhF Hσ".
    { iExists hF. iFrame. eauto using heap_freeable_rel_stable. }
    clear dependent n σ hF. iIntros (σ2). iDestruct 1 as (hF) "(Hσ & HhF & %)".
    iDestruct (heap_mapsto_lookup with "Hσ Hmt") as %[n Hσl]; eauto.
    iMod (heap_read_vs _ 1 0 with "Hσ Hmt") as "[Hσ Hmt]"; first done.
    iExists n; iModIntro; iSplit; [done|]. iFrame "Hmt".
    iExists hF. iFrame. eauto using heap_freeable_rel_stable.
  Qed.

  Lemma heap_write_vs σ st1 st2 l v v':
    σ !! l = Some (st1, v) →
    own heap_name (● to_heap σ) ⊢ heap_mapsto_st st1 l 1%Qp v
    ==∗ own heap_name (● to_heap (<[l:=(st2, v')]> σ))
        ∗ heap_mapsto_st st2 l 1%Qp v'.
  Proof.
    intros Hσv. iIntros "H● H◯".
    iMod (own_update_2 _ _ _ (● to_heap (<[l:=(st2, b')]> σB) ⋅
      ◯ {[l := (1%Qp, to_lock_stateR st2, to_agree b')]}) with "H● H◯") as "[$ $]"; [|done].
    rewrite to_heap_insert. eapply auth_update, singleton_local_update.
    { by rewrite /to_heap lookup_fmap Hσv. }
    apply exclusive_local_update. by destruct st2.
  Qed.

  Lemma heap_write σ l v v' :
    heap_ctx σ -∗ l ↦ v ==∗ heap_ctx (<[l:=(RSt 0, v')]> σ) ∗ l ↦ v'.
  Proof.
    iDestruct 1 as (hF) "(Hσ & HhF & %)". iIntros "Hmt".
    rewrite heap_mapsto_eq.
    iDestruct (heap_mapsto_lookup_1 with "Hσ Hmt") as %?; auto.
    iMod (heap_write_vs with "Hσ Hmt") as "[Hσ $]"; first done.
    iModIntro. iExists _. iFrame. eauto using heap_freeable_rel_stable.
  Qed.

  Lemma heap_write_na σ l v v' :
    heap_ctx σ -∗ l ↦ v ==∗
      ⌜σ !! l = Some (RSt 0, v)⌝ ∗
      heap_ctx (<[l:=(WSt, v)]> σ) ∗
      ∀ σ2, heap_ctx σ2 ==∗ ⌜σ2 !! l = Some (WSt, v)⌝ ∗
        heap_ctx (<[l:=(RSt 0, v')]> σ2) ∗ l ↦ v'.
  Proof.
    iDestruct 1 as (hF) "(Hσ & HhF & %)"; iIntros "Hmt".
    rewrite heap_mapsto_eq.
    iDestruct (heap_mapsto_lookup_1 with "Hσ Hmt") as %?; eauto.
    iMod (heap_write_vs with "Hσ Hmt") as "[Hσ Hmt]"; first done.
    iModIntro. iSplit; [done|]. iSplitL "HhF Hσ".
    { iExists hF. iFrame. eauto using heap_freeable_rel_stable. }
    clear dependent σ hF. iIntros (σ2). iDestruct 1 as (hF) "(Hσ & HhF & %)".
    iDestruct (heap_mapsto_lookup with "Hσ Hmt") as %[n Hσl]; eauto.
    iMod (heap_write_vs with "Hσ Hmt") as "[Hσ Hmt]"; first done.
    iModIntro; iSplit; [done|]. iFrame "Hmt".
    iExists hF. iFrame. eauto using heap_freeable_rel_stable.
  Qed.
  *)

    Definition is_concrete (fv: fancy_val) : Prop :=
      match fv with
        | FVal _ => True
        | FCell _ => False
      end.

  Fixpoint all_concrete (l: list fancy_val) : Prop := 
    match l with
      | [] => True
      | v :: l' => is_concrete v ∧ all_concrete l'
    end.
  
  Lemma heap_complete_mapsto_singleton l₀ c₀ :
      ((l₀, [c₀]) #↦∗_) ⊣⊢ ((l₀, c₀) #↦_).
  Proof.
    apply sep_True. apply _.
  Qed.
  
  Lemma heap_complete_mapsto_val_singleton l₀ c₀ v :
      ((l₀, [c₀]) #↦∗ [v]) ⊣⊢ ((l₀, c₀) #↦ v).
  Proof.
    apply sep_True. apply _.
  Qed.
  
  Lemma heap_complete_mapsto_fancy_singleton l₀ c₀ v :
      ((l₀, [c₀]) #↦!∗ [v]) ⊣⊢ ((l₀, c₀) #↦! v).
  Proof.
    apply sep_True. apply _.
  Qed.
  
  Lemma all_concrete_app (l l' : list fancy_val) : all_concrete l ∧ all_concrete l' ↔ all_concrete (l ++ l').
  Proof.
    induction l; simpl; intuition.
  Qed.

  Lemma all_concrete_take l n : all_concrete l → all_concrete (take n l).
  Proof.
    move: l. elim: n=>//= ? IH [|??]//= [??]. split=>//. by apply IH.
  Qed.

  Lemma all_concrete_repeat v n : is_concrete v → all_concrete (repeat v n).
  Proof. move=> ?. by elim: n. Qed.
  
  Definition to_concrete (l: list fancy_val) : list val := (λ fv, match fv with FVal v => v | FCell _ => inhabitant end) <$> l.
  
  Lemma fmap_to_concrete (l: list fancy_val) :
    all_concrete l → fmap FVal (to_concrete l) = l.
  Proof.
    induction l as [|a l]; first done. destruct a.
      - intros [_ Ha]. simpl. unfold fmap in IHl. rewrite IHl; trivial.
      - simpl. intuition.
  Qed.
  
  Lemma length_to_concrete (l: list fancy_val) :
    length (to_concrete l) = length l.
  Proof.
    induction l; first done. simpl. rewrite IHl. trivial.
  Qed.
  
  Lemma heap_mapsto_cells_fancy_fmap_eq l c v
    : l ↦[^ c ]!∗ (fmap FVal v) ⊣⊢ l ↦[^ c ]∗ v.
  Proof. done. Qed.
    
  Lemma heap_complete_mapsto_fancy_fmap_eq l v
    : l #↦!∗ (fmap FVal v) ⊣⊢ l #↦∗ v.
  Proof. done. Qed.

  Lemma all_concrete_fmap_fval vl : all_concrete (FVal <$> vl).
  Proof.
    induction vl; first done. split; first done. apply IHvl.
  Qed.
  
  Lemma heap_mapsto_fancy_vec_cons l fv fvs
    : l ↦!∗ (fv :: fvs) ⊣⊢ l ↦! fv ∗ ((l +ₗ 1) ↦!∗ fvs).
  Proof. done. Qed.
  
  Lemma heap_mapsto_val_vec_cons l fv fvs
    : l ↦∗ (fv :: fvs) ⊣⊢ l ↦ fv ∗ ((l +ₗ 1) ↦∗ fvs).
  Proof. unfold heap_mapsto_vec. rewrite big_sepL_cons.
    rewrite shift_loc_0.
    assert (∀ (i: nat), (l +ₗ 1 +ₗ i) = (l +ₗ S i)) as X. {
      intros i. rewrite shift_loc_assoc. f_equal. lia.
    }
    setoid_rewrite X. done.
  Qed.
  
  Lemma heap_mapsto_cells_fancy_vec_cons l c cs fv fvs
    : l ↦[^ c :: cs ]!∗ (fv :: fvs) ⊣⊢ l ↦[^ c]! fv ∗ ((l +ₗ 1) ↦[^ cs]!∗ fvs).
  Proof. done. Qed.
  
  Lemma heap_mapsto_cells_val_vec_cons l c cs v vs
    : l ↦[^ c :: cs ]∗ (v :: vs) ⊣⊢ l ↦[^ c] v ∗ ((l +ₗ 1) ↦[^ cs]∗ vs).
  Proof. done. Qed.
  
  Lemma heap_mapsto_cloc_fancy_vec_cons l c cs fv fvs
    : (l, c :: cs) #↦!∗ (fv :: fvs) ⊣⊢
        (l, c) #↦! fv ∗ ((l +ₗ 1), cs) #↦!∗ fvs.
  Proof. done. Qed.
  
  Lemma heap_mapsto_cloc_val_vec_cons l c cs v vs
    : (l, c :: cs) #↦∗ (v :: vs) ⊣⊢
        (l, c) #↦ v ∗ ((l +ₗ 1), cs) #↦∗ vs.
  Proof. done. Qed.
  
  Lemma heap_mapsto_cloc_vals_vec_cons l c cs v vs
    : (l, c :: cs) #↦∗ (v :: vs) ⊣⊢
        (l, c) #↦ v ∗ ((l +ₗ 1), cs) #↦∗ vs.
  Proof. done. Qed.
  
  Lemma heap_mapsto_cloc_emp_cons l c cs
    : (l, c :: cs) #↦∗_ ⊣⊢ (l, c) #↦_ ∗ ((l +ₗ 1), cs) #↦∗_.
  Proof. done. Qed.
  
  Lemma heap_cloc_mapsto_fancy_empty l lv :
      l ↦!∗ lv ⊣⊢ (l, repeat [] (length lv)) #↦!∗ lv.
  Proof.
      generalize l. clear l. induction lv; first done. intros l.
      rewrite heap_mapsto_fancy_vec_cons.
      rewrite length_cons.
      replace (repeat [] (S (length lv)) : list (list cell_id)) with (([] :: repeat [] (length lv)) : list (list cell_id)) by done. rewrite heap_mapsto_cloc_fancy_vec_cons.
      rewrite IHlv. done.
  Qed.
  
  Lemma heap_cloc_mapsto_val_empty l lv :
      l ↦∗ lv ⊣⊢ (l, repeat [] (length lv)) #↦∗ lv.
  Proof.
  induction lv in l |- *.
  - rewrite heap_mapsto_vec_nil. 
    rewrite /heap_complete_mapsto_val_vec.
    cbn[fmap list_fmap].
    rewrite -(heap_cloc_mapsto_fancy_empty _ []).
    rewrite heap_mapsto_fancy_vec_nil.
    done.
  - rewrite heap_mapsto_val_vec_cons /=.
    rewrite heap_mapsto_cloc_vals_vec_cons.
    rewrite IHlv.
    rewrite -heap_complete_mapsto_fancy_singleton.
    change [[]] with (@repeat (list cell_id) [] (length [FVal a])).
    rewrite -heap_cloc_mapsto_fancy_empty.
    rewrite heap_mapsto_fancy_vec_cons.
    iSplit => //.
    + iIntros "[Hhead $]". iSplit => //.
    + iIntros "[[? ?] $]" => //.
  Qed.

  Lemma heap_mapsto_cells_fancy_empty l lv :
      l ↦!∗ lv ⊣⊢ l ↦[^ repeat [] (length lv)]!∗ lv.
  Proof. done. Qed.
      
  Lemma heap_mapsto_cells_empty l lv :
      l ↦∗ lv ⊣⊢ l ↦[^ repeat [] (length lv)]∗ lv.
  Proof.
      generalize l. clear l. induction lv; first done. intros l.
      rewrite heap_mapsto_val_vec_cons. rewrite IHlv. done.
  Qed.
  
  Lemma heap_cloc_mapsto_empty l len :
      True ⊣⊢ (l, repeat [] len) #↦∗_.
  Proof.
      generalize l. clear l. induction len; first done.
      intros l. simpl. rewrite heap_mapsto_cloc_emp_cons.
      rewrite <- IHlen. rewrite sep_True. done.
  Qed.
      
  Lemma heap_mapsto_fancy_fmap_eq l v
    : l ↦!∗ (fmap FVal v) ⊣⊢ l ↦∗ v.
  Proof.
      generalize l; clear l; induction v; first done. intros l.
      rewrite heap_mapsto_vec_cons. rewrite <- IHv. done.
  Qed.
  
  Lemma heap_cloc_mapsto_fancy_fmap_eq l v
    : l #↦!∗ (fmap FVal v) ⊣⊢ l #↦∗ v.
  Proof. done. Qed.
    
  Lemma heap_mapsto_cells_fancy_vec_nil l : l ↦[^ []]!∗ [] ⊣⊢ True.
  Proof. done. Qed.

  Definition cloc_take (l: cloc) (n: nat) : cloc := (l.1, take n l.2).
  Definition cloc_skip (l: cloc) (n: nat) : cloc := (l.1 +ₗ n, skipn n l.2).

  Lemma heap_mapsto_fancy_vec_app l vl1 vl2 :
    l ↦!∗ (vl1 ++ vl2) ⊣⊢ l ↦!∗ vl1 ∗ (l +ₗ length vl1) ↦!∗ vl2.
  Proof.
    generalize l. clear l. induction vl1; intros l.
      - simpl. rewrite shift_loc_0. rewrite heap_mapsto_fancy_vec_nil.
        rewrite bi.sep_comm. rewrite bi.sep_True. done.
      - simpl. do 2 rewrite heap_mapsto_fancy_vec_cons.
        rewrite IHvl1. rewrite shift_loc_assoc.
        replace (Z.of_nat (S (length vl1))) with (1 + (length vl1)) by lia.
        iSplit. { iIntros "[a [b c]]". iFrame. } { iIntros "[a b]". iFrame. }
  Qed.
    
  Lemma heap_cloc_mapsto_emp_vec_app (l: cloc) (n: nat) :
    l #↦∗_ ⊣⊢ (cloc_take l n) #↦∗_ ∗ (cloc_skip l n) #↦∗_.
  Proof.
    destruct l as [l cells]. simpl. generalize l, cells. clear l. clear cells. induction n.
       - intros l cells.
         replace (cloc_take (l, cells) 0) with ((l, []) : cloc) by done.
         unfold cloc_skip. rewrite drop_0. rewrite shift_loc_0.
         rewrite bi.sep_comm. rewrite bi.sep_True. done.
       - intros l cells. destruct cells as [|cells].
         { unfold cloc_take, cloc_skip. simpl. iSplit; done. }
         replace (cloc_take (l, cells :: cells0) (S n)) with
                 (l, cells :: take n cells0) by done.
         do 2 rewrite heap_mapsto_cloc_emp_cons.
         replace (cloc_skip (l, cells :: cells0) (S n)) with (cloc_skip (l +ₗ 1, cells0) n).
         2: { simpl. unfold cloc_skip. f_equal. simpl. rewrite shift_loc_assoc. f_equal. lia. }
         rewrite IHn.
         iSplit. { iIntros "[a [b c]]". iFrame. } { iIntros "[a b]". iFrame. }
  Qed.
    
  Lemma heap_cloc_mapsto_fancy_vec_app (l: cloc) vl1 vl2 :
    l #↦!∗ (vl1 ++ vl2) ⊣⊢ (cloc_take l (length vl1)) #↦!∗ vl1 ∗ (cloc_skip l (length vl1)) #↦!∗ vl2.
  Proof.
    destruct l as [l cells]. simpl. generalize l, cells. clear l. clear cells. induction vl1.
       - intros l cells.
         replace (cloc_take (l, cells) 0) with ((l, []) : cloc) by done.
         unfold cloc_skip. rewrite drop_0. rewrite shift_loc_0.
         rewrite bi.sep_comm. rewrite bi.sep_True. done.
       - intros l cells. destruct cells as [|cells].
         { iSplit. { iIntros "a". iExFalso. iFrame. }
           { iIntros "[a b]". iExFalso. iFrame. } }
         replace (cloc_take (l, cells :: cells0) (length (a :: vl1))) with
                 (l, cells :: take (length vl1) cells0) by done.
         rewrite heap_mapsto_cloc_fancy_vec_cons. 
         replace ((a :: vl1) ++ vl2) with (a :: (vl1 ++ vl2)) by done.
         rewrite heap_mapsto_cloc_fancy_vec_cons.
         replace (cloc_skip (l, cells :: cells0) (length (a :: vl1))) with (cloc_skip (l +ₗ 1, cells0) (length vl1)).
         2: { simpl. unfold cloc_skip. f_equal. simpl. rewrite shift_loc_assoc. f_equal. lia. }
         rewrite IHvl1.
         iSplit. { iIntros "[a [b c]]". iFrame. } { iIntros "[a b]". iFrame. }
  Qed.
  
  Lemma heap_mapsto_cells_fancy_vec_app' l vl1 vl2 cells :
    l ↦[^ cells]!∗ (vl1 ++ vl2) ⊣⊢ l ↦[^ take (length vl1) cells]!∗ vl1 ∗ (l +ₗ length vl1) ↦[^ skipn (length vl1) cells]!∗ vl2.
  Proof.
    generalize l. clear l. generalize cells. clear cells. induction vl1; intros cells l.
      - simpl. rewrite shift_loc_0. replace (drop 0 cells) with cells by trivial.
        rewrite bi.sep_comm. rewrite bi.sep_True. done.
      - simpl. destruct cells as [|cells0 cells].
        + simpl. iSplit. { iIntros. done. } { iIntros "[? _]". done. }
        + replace (take (S (length vl1)) (cells0 :: cells)) with (cells0 :: take (length vl1) cells) by trivial.
          do 2 rewrite heap_mapsto_cells_fancy_vec_cons.
          rewrite IHvl1. rewrite shift_loc_assoc.
          replace (Z.of_nat (S (length vl1))) with (Z.add 1 (Z.of_nat (length vl1))) by lia.
          replace ((S (length vl1))) with (1 + (length vl1))%nat by lia.
          replace (drop (1 + length vl1) (cells0 :: cells)) with (drop (length vl1) cells) by trivial.
          iSplit. { iIntros "[a [b c]]". iFrame. } { iIntros "[a b]". iFrame. }
  Qed.
  
  Lemma heap_mapsto_cells_fancy_vec_app l vl1 vl2 :
    l.1 ↦[^ l.2]!∗ (vl1 ++ vl2) ⊣⊢
        (l.1 ↦[^ take (length vl1) l.2]!∗ vl1) ∗ ((l.1 +ₗ length vl1) ↦[^ skipn (length vl1) l.2]!∗ vl2).
  Proof. apply heap_mapsto_cells_fancy_vec_app'. Qed.
  
  Lemma heap_cloc_mapsto_fancy_vec_length_eq l vl :
      l #↦!∗ vl ⊢ ⌜ length l.2 = length vl⌝.
  Proof.
      destruct l as [l c]. simpl. generalize l, c. clear l. clear c. induction vl.
        - intros l c. destruct c.
          + iIntros. iPureIntro. done.
          + iIntros "A". iExFalso. iFrame.
        - intros l c. destruct c.
          + iIntros "A". iExFalso. iFrame.
          + rewrite heap_mapsto_cloc_fancy_vec_cons. iIntros "[A B]".
            iDestruct (IHvl with "B") as "%Hlen".
            iPureIntro. simpl. rewrite Hlen; trivial.
  Qed.

  Lemma cells_points_to_fancy_value_vec_cons γ γs fv fvs
    : (γ :: γs) ^↦!∗ (fv :: fvs) ⊣⊢
        γ ^↦! fv ∗ γs ^↦!∗ fvs.
  Proof. done. Qed.

  Lemma cells_points_to_fancy_vec_length_eq cell_ids vl :
    cell_ids ^↦!∗ vl ⊢ ⌜ length cell_ids = length vl ⌝.
  Proof.
    induction cell_ids as [ | ?? IH ] in vl |- *.
    - destruct vl => //.
      + iIntros. iPureIntro. done.
      + iIntros "A". iExFalso. iFrame.
    - destruct vl.
      + iIntros "A". iExFalso. iFrame.
      + rewrite cells_points_to_fancy_value_vec_cons. iIntros "[A B]".
        iDestruct (IH with "B") as "%Hlen".
        iPureIntro. simpl. rewrite Hlen; trivial.
  Qed.

  Lemma heap_complete_mapsto_val_empty l
    : (l, []) #↦∗ [] ⊣⊢ True. 
  Proof.
    replace [] with (@repeat (list cell_id) [] (@length val [])) by done.
    rewrite -(heap_cloc_mapsto_val_empty).
    rewrite /heap_mapsto_vec.
    rewrite big_sepL_nil.
    done.
  Qed.
  
  Lemma heap_cloc1_mapsto_val l v
    : (l, []) #↦ v ⊣⊢ l ↦ v. 
  Proof. done. Qed.

  Lemma heap_complete_mapsto_fancy_empty l
    : (l, []) #↦!∗ [] ⊣⊢ True. 
  Proof.
    replace [] with (@repeat (list cell_id) [] (@length fancy_val [])) by done.
    rewrite -(heap_cloc_mapsto_fancy_empty).
    done.
  Qed.

  Lemma rev_snoc {A} (a : A) (l : list A) :
    rev (l ++ [a]) = a :: rev l.
  Proof.
    induction l in a |-  *; simpl; first done.
    rewrite IHl.
    done.
  Qed.

  Lemma split_at_last_snoc {A} (a : A) (l : list A) :
    split_at_last (l ++ [a]) = Some (l, a).
  Proof.
    rewrite /split_at_last.
    by rewrite rev_snoc rev_involutive.
  Qed.

  Lemma heap_mapsto_cells_to_complete_mapsto_fancy (l : cloc1) (fv : fancy_val) :
    l.1 ↦[^ l.2 ]! fv ⊣⊢ l #↦_ ∗ l #↦! fv. 
  Proof.
    destruct l as [l cell_ids]. simpl.
    rewrite /heap_mapsto_cells_fancy/heap_complete_mapsto/heap_complete_mapsto_fancy.
    destruct (decide (cell_ids = [])) as [-> | Hnempty].
    (* induction cell_ids as [ | γ cell_ids IH] using rev_ind in l, fv |- *. *)
    - simpl. iSplit. + by iIntros "$". + by iIntros "[_ $]".
    - apply exists_last in Hnempty as (cell_ids' & γ & ->).
      rewrite split_at_last_snoc/=.
      rewrite pt_seq_snoc.
      done.
  Qed.

  Lemma heap_mapsto_cells_to_complete_mapsto_fancy_vec (l : cloc) (fv : list fancy_val) :
    l.1 ↦[^ l.2 ]!∗ fv ⊣⊢ l #↦∗_ ∗ l #↦!∗ fv. 
  Proof.
    destruct l as [l list_cell_ids]. simpl.
    induction list_cell_ids as [| cell_ids list_cell_ids IH] in l, fv |- *.
    - destruct fv => //=.
      + iSplit => //.
      + iSplit => //.
        rewrite /heap_complete_mapsto_fancy_vec/heap_complete_mapsto_fancy_vec'.
        by iIntros "[_ ?]".
    - destruct fv as [| fv fvs]; simpl.
      + iSplit => //.
        * by iIntros.
        * rewrite /heap_complete_mapsto_fancy_vec/heap_complete_mapsto_fancy_vec'.
          by iIntros "[_ ?]".
      + rewrite heap_mapsto_cloc_emp_cons.
        rewrite heap_mapsto_cloc_fancy_vec_cons.
        iSplit.
        * iIntros "[Hfv Hfvs]".
          rewrite IH.
          iDestruct "Hfvs" as "[Hchain Htail]".
          iFrame.
          iPoseProof (heap_mapsto_cells_to_complete_mapsto_fancy (l, cell_ids) fv) as "H".
          iDestruct ("H" with "Hfv") as "[$ $]".
        * iIntros "[[Hchain Hchain'] [Htail Hfvs]]".
          rewrite IH.
          iFrame.
          iPoseProof (heap_mapsto_cells_to_complete_mapsto_fancy (l, cell_ids) fv) as "[_ H]".
          iDestruct ("H" with "[$]") as "?".
          by rewrite /heap_mapsto_cells_fancy/=.
  Qed.

    Lemma cell_alloc2 l fv :
    l ↦!∗ fv ==∗ ∃ γs, ⌜ length γs = length fv ⌝ ∗ l ↦[^ ((λ γ, [γ]) <$> γs) ]!∗ fv.
  Proof.
    induction fv as [ | fv fvs IH] in l |- *.
    - iIntros "? !>"; iExists []; iSplit => //.
    - rewrite heap_mapsto_fancy_vec_cons.
      iIntros "[Hfv Hfvs]".
      iMod (IH with "Hfvs") as "[%γs [%Hlen Hfvs]]".
      rewrite /heap_mapsto_fancy.
      iMod (pt_alloc_cell with "Hfv") as "[%γ Hfv]".
      iModIntro.
      iExists (γ :: γs).
      iSplit.
      1: { iPureIntro. simpl; lia. }
      rewrite fmap_cons heap_mapsto_cells_fancy_vec_cons.
      iFrame.
  Qed.

  Lemma heap_complete_mapsto_vec_eq (l : loc) (γs : list cell_id)  :
    ((l, (λ γ, [γ]) <$> γs) #↦∗_ ⊣⊢ l ↦!∗ (FCell <$> γs))%I . 
  Proof.
    induction γs as [ | γ γs IH] in l |- *; simpl.
    - change (@nil (list cell_id)) with (@repeat (list cell_id) [] 0). 
      rewrite -heap_cloc_mapsto_empty.
      rewrite heap_mapsto_fancy_vec_nil.
      done.
    - rewrite heap_mapsto_cloc_emp_cons heap_mapsto_fancy_vec_cons.
      rewrite IH.
      rewrite /fmap.
      rewrite /heap_complete_mapsto/heap_mapsto_fancy .
      simpl.
      done.
  Qed.

  Lemma heap_complete_mapsto_fancy_val_vec_eq' (l : loc) (γs : list cell_id) (fl : list fancy_val) :
    ((l, (λ γ : cell_id, [γ]) <$> γs) #↦!∗ fl ⊣⊢ γs ^↦!∗ fl).
  Proof.
    induction γs as [ | γ γs IH] in l, fl |- *; simpl.
    - destruct fl as [|fv fvs] => //=.
    - destruct fl as [|fv fvs] => //=.
      rewrite heap_mapsto_cloc_fancy_vec_cons.
      rewrite IH.
      rewrite /heap_complete_mapsto_fancy//=.
  Qed.

  Definition cloc_flat_insert (l : cloc) (γs : list cell_id) :=
    let z := zip_with (λ γ cell_ids, cell_ids ++ [γ]) γs l.2 in
    (l.1, z).

  Lemma heap_complete_mapsto_fancy_val_vec_eq'' γs cl fl :
    length cl.2 = length γs →
    γs ^↦!∗ (fl) ⊣⊢ cloc_flat_insert cl γs #↦!∗ fl.
  Proof.
    move => Hlen.
    destruct cl as [l list_cell_ids].
    induction γs as [ | γ γs IH] in l, list_cell_ids, fl,Hlen |- *; simpl.
    - destruct fl =>//.
    - destruct fl as [ | fv fvs ] => //=.
      + iSplit; first by iIntros.
        destruct list_cell_ids => //.
      + rewrite /cloc_flat_insert/=.
        destruct list_cell_ids as [ | cell_ids list_cell_ids] => //=.
        rewrite heap_mapsto_cloc_fancy_vec_cons.
        replace (_, zip_with _ _ _) with (cloc_flat_insert (l +ₗ 1, list_cell_ids) γs).
        2: by rewrite /cloc_flat_insert.
        rewrite -IH.
        2: naive_solver.
        rewrite /heap_complete_mapsto_fancy/=.
        by rewrite split_at_last_snoc.
  Qed.

  Lemma heap_fancy_mapsto_cells_length l cells fvs :
    l ↦[^ cells ]!∗ fvs ⊢ ⌜ length cells = length fvs ⌝.
  Proof.
    induction cells as [ | cell cells IH] in l, fvs |- * => //=.
    - destruct fvs => //; by iIntros "?".
    - destruct fvs => //; first by iIntros "?".
      iIntros "[head tail]".
      iDestruct (IH with "tail") as "->".
      by iPureIntro.
  Qed.

  Lemma heap_complete_mapsto_combine γs cl :
    length cl.2 = length γs →
    cl #↦∗_ ∗ cl #↦!∗ (FCell <$> γs)  ⊣⊢ cloc_flat_insert cl γs #↦∗_.
  Proof.
    move => Hlen.
    destruct cl as [l list_cell_ids].
    induction γs as [ | γ γs IH] in l, list_cell_ids, Hlen |- *; simpl.
    - destruct list_cell_ids =>//.
      rewrite /heap_complete_mapsto_vec/heap_complete_mapsto_fancy_vec/heap_complete_mapsto_vec//=.
      iSplit => //.
    - destruct list_cell_ids as [ | cell_ids list_cell_ids] => //=.
      rewrite heap_mapsto_cloc_emp_cons heap_mapsto_cloc_fancy_vec_cons.
      rewrite /cloc_flat_insert/=.
      rewrite heap_mapsto_cloc_emp_cons.
      replace (_, zip_with _ _ _) with (cloc_flat_insert (l +ₗ 1, list_cell_ids) γs).
      2: by rewrite /cloc_flat_insert.
      rewrite -IH.
      2: naive_solver.
      iSplit.
      + iIntros "((H1&H2)&H3&H4)".
        iFrame.
        rewrite {2} /heap_complete_mapsto/=. 
        rewrite split_at_last_snoc.
        iDestruct (heap_mapsto_cells_to_complete_mapsto_fancy with "[$H3 $H1]") as "Hfancy". simpl.
        rewrite /heap_mapsto_cells_fancy/=.
        done.
      + iIntros "(H1&H2&H3)".
        iFrame.
        rewrite -heap_mapsto_cells_to_complete_mapsto_fancy.
        rewrite /heap_complete_mapsto/=. 
        rewrite split_at_last_snoc.
        rewrite /heap_mapsto_cells_fancy/=.
        done.
  Qed.

  Lemma heap_mapsto_singleton l cell_ids fv :
    (l ↦[^ [cell_ids]]!∗ [fv]) ⊣⊢ (l ↦[^ cell_ids]! fv).
  Proof.
    iSplit.
    - rewrite heap_mapsto_cells_fancy_vec_cons.
      iIntros "[$ _]".
    - rewrite heap_mapsto_cells_fancy_vec_cons.
      iIntros "$".
  Qed.

  Lemma cell_points_to_fancy_fmap_eq c v
    : c ^↦! (FVal v) ⊣⊢ c ^↦ v. 
  Proof.
    rewrite /cell_points_to_fancy_value/cell_points_to_value//=.
  Qed.
  
  (* conjunction stuff *)
    
  Lemma point_prop_heap_mapsto_cells_fancy_vec l cells vl :
      factoring_props.point_prop (l ↦[^ cells ]!∗ vl).
  Proof using heapGS0 invGS0 Σ.
      generalize l, cells. clear l. clear cells. induction vl.
      - intros. apply factoring_props.point_prop_of_pers. destruct cells; apply _.
      - intros. destruct cells. { apply factoring_props.point_prop_of_pers. apply _. }
        rewrite heap_mapsto_cells_fancy_vec_cons. apply factoring_props.point_prop_sep.
          + apply pt_seq_point_prop. + apply IHvl.
  Qed.
  
  Local Definition loc_cells_fv_map (l: loc) (cells: list (list cell_id)) (fvl: list fancy_val)
      : gmap loc (list cell_id * (cell_id + val)) :=
      kmap (λ (i: nat), l +ₗ i)
        (map_seq 0 (zip_with (λ c fv, (c, fv2sum fv)) cells fvl)).
  
  Local Lemma lookup_loc_cells_fv_map (l: loc) (cells: list (list cell_id)) (fvl: list fancy_val)
      (l0: loc) (cs: list cell_id) (cv: cell_id + val) :
      loc_cells_fv_map l cells fvl !! l0 = Some (cs, cv)
      → ∃ (i: nat), l0 = l +ₗ i ∧ cells !! i = Some cs ∧ fvl !! i = Some (sum2fv cv).
  Proof.
      unfold loc_cells_fv_map. intros Ha.
      rewrite lookup_kmap_Some in Ha. destruct Ha as [i [Hl Ha]]. subst l0.
      rewrite lookup_map_seq_Some in Ha. destruct Ha as [Hi0 Ha].
      replace (i - 0)%nat with i in Ha by lia.
      rewrite lookup_zip_with_Some in Ha. destruct Ha as [cells0 [fv0 [Ha [Hb Hc]]]].
      inversion Ha. subst cs. subst cv. 
      exists i. split; first by trivial. split; first by trivial.
      rewrite Hc. destruct fv0; done.
  Qed.

  
  Local Lemma loc_cells_fv_map_cons l cell cells fv fvl :
      loc_cells_fv_map l (cell :: cells) (fv :: fvl) =
        <[ l := (cell, fv2sum fv) ]> (loc_cells_fv_map (l +ₗ 1) cells fvl).
  Proof.
    rewrite {1} /loc_cells_fv_map.
    simpl.
    rewrite kmap_insert shift_loc_0.
    f_equal.
    rewrite /loc_cells_fv_map.
    rewrite (kmap_map_seq_shift _ 1%nat).
    f_equal.
    apply FunctionalExtensionality.functional_extensionality => i.
    rewrite (shift_loc_assoc).
    f_equal; lia.
    Qed.
  
  Local Lemma loc_cells_fv_map_plus1_not_in l cells fvl :
    loc_cells_fv_map (l +ₗ 1) cells fvl !! l = None.
  Proof.
    unfold loc_cells_fv_map. rewrite lookup_kmap_None. intros i Hl.
    rewrite shift_loc_assoc in Hl.
    assert (l +ₗ 0 = l +ₗ (1 + i)) as Hl2. { rewrite shift_loc_0. trivial. }
    have Hl3 := (shift_loc_inj l _ _ Hl2). lia.
  Qed.
  
  Local Lemma sepM_loc_cells_fv_map_cons l cell cells fv fvl :
      ([∗ map] l0↦'(cells0, cv) ∈ loc_cells_fv_map l (cell :: cells) (fv :: fvl), 
          inl l0 @↦[heap_name][^cells0] cv)
      ⊢ 
      inl l @↦[heap_name][^cell] (fv2sum fv) ∗
      ([∗ map] l0↦'(cells0, cv) ∈ loc_cells_fv_map (l +ₗ 1) (cells) (fvl), 
          inl l0 @↦[heap_name][^cells0] cv).
  Proof using heapGS0 invGS0 Σ.
      rewrite loc_cells_fv_map_cons.
      rewrite big_sepM_insert; first by done.
      apply loc_cells_fv_map_plus1_not_in.
  Qed.
  
  Local Lemma sepM_entails_mapsto_cells_fancy_vec l cells fvl :
      length cells = length fvl →
      ([∗ map] l0 ↦ '(cells, cv) ∈ loc_cells_fv_map l cells fvl, (inl l0) @↦[heap_name][^ cells ] cv)
      ⊢ l ↦[^ cells ]!∗ fvl.
  Proof using heapGS0 invGS0 Σ.
      generalize l, cells. clear l. clear cells. induction fvl.
       - intros l cells Heq. simpl in Heq. rewrite length_zero_iff_nil in Heq. subst cells.
          iIntros. done.
       - intros l cells Heq. destruct cells as [|cell cells]. { simpl in Heq. lia. }
         rewrite heap_mapsto_cells_fancy_vec_cons.
         assert (length cells = length fvl) as Heq'. { simpl in Heq. lia. }
         iIntros "a". iDestruct (sepM_loc_cells_fv_map_cons with "a") as "[a b]".
         iFrame. iDestruct (IHfvl with "b") as "$". trivial.
  Qed.
  
  Lemma cloc_take_app_length l cs1 cs2 :
    cloc_take (l, cs1 ++ cs2) (length cs1) = (l, cs1).
  Proof. by rewrite /cloc_take /= take_app_length. Qed.
  Lemma cloc_skip_app_length l cs1 cs2:
    cloc_skip (l, cs1 ++ cs2) (length cs1) = (l +ₗ length cs1, cs2).
  Proof. by rewrite /cloc_skip /= drop_app_length. Qed.

  Lemma heap_complete_mapsto_fancy_empty_cells l fv :
    (l, []) #↦! fv ⊣⊢ l ↦! fv.
  Proof. by rewrite /heap_complete_mapsto_fancy /heap_mapsto_fancy /=. Qed.

  Local Lemma cloc_get_row_no_cells (l: loc) (cs: list (list cell_id)) (fvl: list fancy_val) (i: nat) (cv: cell_id + val) :
      cs !! i = Some [] →
      fvl !! i = Some (sum2fv cv) →
      (l, cs) #↦!∗ fvl ⊢ inl (l +ₗ i) @↦[heap_name] cv.
  Proof.
    move => Hlookup1 Hlookup2.
    apply elem_of_list_split_length in Hlookup1 as [cs1 [cs2 [-> Hi]]].
    apply elem_of_list_split_length in Hlookup2 as [fvl1 [fvl2 [-> Hi']]].
    rewrite heap_cloc_mapsto_fancy_vec_app.
    rewrite -Hi' Hi cloc_take_app_length cloc_skip_app_length.
    rewrite {1} heap_mapsto_cloc_fancy_vec_cons.
    iIntros "(_ & H & _)".
    rewrite heap_complete_mapsto_fancy_empty_cells/heap_mapsto_fancy/= .
    destruct cv => //.
  Qed.
  

  Local Lemma cloc_get_row_last_cell (l: loc) (cs: list (list cell_id)) (fvl: list fancy_val) (i: nat) (cells: list cell_id) (cell: cell_id) (cv: cell_id + val) :
      cs !! i = Some (cells ++ [cell]) →
      fvl !! i = Some (sum2fv cv) →
      (l, cs) #↦!∗ fvl ⊢ inr cell @↦[heap_name] cv.
  Proof.
    move => Hlookup1 Hlookup2.
    apply elem_of_list_split_length in Hlookup1 as [cs1 [cs2 [-> Hi]]].
    apply elem_of_list_split_length in Hlookup2 as [fvl1 [fvl2 [-> Hi']]].
    rewrite heap_cloc_mapsto_fancy_vec_app.
    rewrite -Hi' Hi cloc_take_app_length cloc_skip_app_length.
    rewrite {1} heap_mapsto_cloc_fancy_vec_cons.
    iIntros "(_ & H & _)".
    rewrite /heap_complete_mapsto_fancy/= .
    rewrite split_at_last_snoc.
    destruct cv => //.
  Qed.

  Local Lemma cloc_get_row_prefix (l: loc) (cs: list (list cell_id)) (i: nat) (cells: list cell_id) (cell: cell_id) :
      cs !! i = Some (cells ++ [cell]) →
      (l, cs) #↦∗_ ⊢ inl (l +ₗ i) @↦[heap_name][^cells] (inl cell).
  Proof.
    move => Hlookup.
    apply elem_of_list_split_length in Hlookup as [cs1 [cs2 [-> Hi]]].
    rewrite (heap_cloc_mapsto_emp_vec_app _ i).
    rewrite Hi cloc_take_app_length cloc_skip_app_length.
    rewrite heap_mapsto_cloc_emp_cons.
    iIntros "(_ & H & _)".
    rewrite /heap_complete_mapsto.
    rewrite split_at_last_snoc //=.
  Qed.
  
  Local Lemma split_at_last_eq_concat_last (c: cell_id) (cells: list cell_id) :
      match split_at_last (c :: cells) with
          | Some (prefix, last_cell) => c :: cells = prefix ++ [last_cell]
          | None => false
      end.
  Proof.
    induction cells as [ | ?? IH ]in c |- * => //=.
    opose proof (@exists_last _ (a :: cells) _) as [a_last [cells' ->]] => //.
    rewrite app_comm_cons split_at_last_snoc //=.
  Qed.
  
  Lemma and_cloc_combine_fancy (l: cloc) (fvl: list fancy_val) :
      l #↦∗_ ∧ l #↦!∗ fvl ⊢ l.1 ↦[^ l.2 ]!∗ fvl.
  Proof using heapGS0 invGS0 Σ.
      iIntros "And".
      iDestruct (heap_cloc_mapsto_fancy_vec_length_eq with "[And]") as "%HLen".
        { iDestruct "And" as "[_ $]". }
      destruct l as [l cs]. simpl.
      iApply sepM_entails_mapsto_cells_fancy_vec; first by trivial.
      iApply pt_seq_andM_sepM. iApply big_andM_intro. iIntros (l0 x) "%IsSome".
      destruct x as [cells cv].
      destruct (lookup_loc_cells_fv_map l cs fvl l0 cells cv IsSome) as [i [Hl [Hc Hv]]].
      subst l0. destruct cells.
       - iApply (cloc_get_row_no_cells _ _ _ _ _ Hc Hv with "[And]").
         iDestruct "And" as "[_ $]".
       - have Hsplit := split_at_last_eq_concat_last c cells.
         destruct (split_at_last (c :: cells)) as [[prefix last_cell]|] eqn:Hsp; last by done.
         rewrite Hsplit. iApply pt_seq_cons_back_and. iSplit.
          + iApply cloc_get_row_prefix. { rewrite <- Hsplit. apply Hc. }
            iDestruct "And" as "[$ _]".
          + iApply (cloc_get_row_last_cell l cs fvl i prefix last_cell).
            { rewrite <- Hsplit. apply Hc. } { apply Hv. }
            iDestruct "And" as "[_ $]".
  Qed.
    
  Lemma and_cloc_combine (l: cloc) (vl: list val) :
      l #↦∗_ ∧ l #↦∗ vl ⊢ l.1 ↦[^ l.2 ]∗ vl.
  Proof using heapGS0 invGS0 Σ.
      apply and_cloc_combine_fancy.
  Qed.
  
  Lemma guard_cloc_combine G E n (l: cloc) (vl: list val) :
      ⊢ (G &&{E;n}&&> l #↦∗_) -∗ (G &&{E;n}&&> l #↦∗ vl) -∗ (G &&{E;n}&&> (l.1 ↦[^ l.2]∗ vl)).
  Proof.
      iApply guards_and_point.
      - apply point_prop_heap_mapsto_cells_fancy_vec. - apply and_cloc_combine.
  Qed.
  
  Lemma guard_cloc_combine_fancy G E n (l: cloc) (vl: list fancy_val) :
      ⊢ (G &&{E;n}&&> l #↦∗_) -∗ (G &&{E;n}&&> l #↦!∗ vl)
          -∗ (G &&{E;n}&&> (l.1 ↦[^ l.2]!∗ vl)).
  Proof.
      iApply guards_and_point.
      - apply point_prop_heap_mapsto_cells_fancy_vec. - apply and_cloc_combine_fancy.
  Qed.

  Lemma heap_mapsto_cells_fancy_vec_length_eq l cells fvl :
      l ↦[^ cells]!∗ fvl ⊢ ⌜length cells = length fvl⌝.
  Proof.
    induction cells as [|c cells IH] in l, fvl |- *; destruct fvl as [|fv fvl];
      simpl; [by iIntros|by iIntros "[]"|by iIntros "[]"|].
    iIntros "[_ H]". by iDestruct (IH with "H") as %->.
  Qed.

  (** A point of a sequence of points. *)
  Lemma heap_mapsto_cells_fancy_vec_lookup l cells fvl (i: nat) cs fv :
      cells !! i = Some cs → fvl !! i = Some fv →
      l ↦[^ cells]!∗ fvl ⊢ inl (l +ₗ i) @↦[heap_name][^ cs] (fv2sum fv).
  Proof.
    induction cells as [|c cells IH] in l, fvl, i |- *; [done|].
    destruct fvl as [|f fvl]; [done|]. destruct i as [|i]; simpl.
    - intros [= ->] [= ->]. rewrite shift_loc_0. iIntros "[$ _]".
    - intros ??. iIntros "[_ H]". iDestruct (IH with "H") as "H"; [done|done|].
      rewrite shift_loc_assoc. by replace (1 + i)%Z with (Z.of_nat (S i)) by lia.
  Qed.

  (** The points of two disjoint consecutive ranges, in a conjunction, are the points of
      their union (as [and_cloc_combine_fancy]; used to combine guards of the two ranges,
      [guard_cells_app_combine_fancy]). *)
  Lemma and_cells_app_combine_fancy l cells (vl1 vl2: list fancy_val) :
      l ↦[^ take (length vl1) cells]!∗ vl1 ∧
        (l +ₗ length vl1) ↦[^ drop (length vl1) cells]!∗ vl2 ⊢
      l ↦[^ cells]!∗ (vl1 ++ vl2).
  Proof using heapGS0 invGS0 Σ.
    iIntros "And".
    iAssert ⌜length (take (length vl1) cells) = length vl1⌝%I as %H1.
    { iDestruct "And" as "[A _]". by iApply heap_mapsto_cells_fancy_vec_length_eq. }
    iAssert ⌜length (drop (length vl1) cells) = length vl2⌝%I as %H2.
    { iDestruct "And" as "[_ A]". by iApply heap_mapsto_cells_fancy_vec_length_eq. }
    rewrite length_take in H1. rewrite length_drop in H2.
    iApply sepM_entails_mapsto_cells_fancy_vec; first by (rewrite length_app; lia).
    iApply pt_seq_andM_sepM. iApply big_andM_intro. iIntros (l0 [cs cv]) "%IsSome".
    destruct (lookup_loc_cells_fv_map l cells (vl1 ++ vl2) l0 cs cv IsSome)
      as [i [-> [Hc Hv]]].
    rewrite (_: cv = fv2sum (sum2fv cv)); [|by destruct cv].
    destruct (decide (i < length vl1)%nat) as [Hi|Hi].
    - iDestruct "And" as "[A _]". iApply (heap_mapsto_cells_fancy_vec_lookup with "A").
      + rewrite lookup_take; [done|lia].
      + rewrite -Hv lookup_app_l; [done|lia].
    - iDestruct "And" as "[_ A]".
      iDestruct (heap_mapsto_cells_fancy_vec_lookup _ _ _ (i - length vl1) cs (sum2fv cv)
        with "A") as "A".
      + rewrite lookup_drop. rewrite -Hc. f_equal. lia.
      + rewrite -Hv lookup_app_r; [done|lia].
      + rewrite shift_loc_assoc. by replace (length vl1 + (i - length vl1)%nat)%Z
          with (Z.of_nat i) by lia.
  Qed.

  Lemma guard_cells_app_combine_fancy G E n l cells (vl1 vl2: list fancy_val) :
      ⊢ (G &&{E;n}&&> l ↦[^ take (length vl1) cells]!∗ vl1) -∗
        (G &&{E;n}&&> (l +ₗ length vl1) ↦[^ drop (length vl1) cells]!∗ vl2) -∗
        (G &&{E;n}&&> l ↦[^ cells]!∗ (vl1 ++ vl2)).
  Proof.
    iApply guards_and_point.
    - apply point_prop_heap_mapsto_cells_fancy_vec. - apply and_cells_app_combine_fancy.
  Qed.

  Lemma cloc_take_app_length' n l cs1 cs2 :
    n = length cs1 →
    cloc_take (l, cs1 ++ cs2) n = (l, cs1).
  Proof. move => ->; by rewrite /cloc_take /= take_app_length. Qed.
  Lemma cloc_skip_app_length' n l cs1 cs2:
    n = length cs1 →
    cloc_skip (l, cs1 ++ cs2) n = (l +ₗ length cs1, cs2).
  Proof. move => ->; by rewrite /cloc_skip /= drop_app_length. Qed.

  Lemma guard_cloc_combine_fancy' G E n (l : cloc) (γs : list cell_id) (vl: list fancy_val) :
      ⊢ (G &&{E;n}&&> l.1 ↦[^ l.2 ]!∗ (FCell <$> γs)) -∗ (G &&{E;n}&&> γs ^↦!∗ vl) -∗ let l' := cloc_flat_insert l γs in (G &&{E;n}&&> (l'.1 ↦[^ l'.2]!∗ vl)).
  Proof.
    iApply guards_and_point.
    - apply point_prop_heap_mapsto_cells_fancy_vec.
    - iIntros "And".
      rewrite -(heap_complete_mapsto_fancy_val_vec_eq' l.1).
      iDestruct (heap_cloc_mapsto_fancy_vec_length_eq with "[And]") as "%HLen".
      { rewrite heap_mapsto_cells_to_complete_mapsto_fancy_vec.
        iDestruct "And" as "[[_ $] _]". }
      iDestruct (heap_cloc_mapsto_fancy_vec_length_eq with "[And]") as "%HLen'".
      { iDestruct "And" as "[_ $]". }
      destruct l as [l cs] => /=; simpl in HLen.
      iApply sepM_entails_mapsto_cells_fancy_vec. 
      { rewrite length_zip_with.
        simpl in HLen'.
        rewrite !length_fmap in HLen, HLen'.
        lia. }
      iApply pt_seq_andM_sepM. 
      iApply big_andM_intro. iIntros (l0 [cells cv]) "%IsSome".
      destruct (lookup_loc_cells_fv_map l _ _ l0 cells cv IsSome) as [i [Hl [Hc Hv]]].
      clear IsSome.
      subst l0. 
      have [γ [Hγs [cells' [Hcs Hcells]]]] : (∃ γ, γs !! i = Some γ ∧ ∃ cells', cs !! i = Some cells' ∧ cells = cells' ++ [γ]).
      { apply lookup_zip_with_Some in Hc.
        destruct Hc as (γ & cells' & ? & ? & ?).
        eexists; split => //.
        eexists; split => //. }
      apply elem_of_list_split_length in Hcs as [cs1 [cs2 [Hcs Hcs1]]].
      apply elem_of_list_split_length in Hγs as [γs1 [γs2 [Hγs Hγs1]]].
      rewrite Hcs Hγs.
      set cl := (l, cs1 ++ cells' :: cs2).
      change l with cl.1.
      change (cs1 ++ cells' :: cs2) with cl.2.
      rewrite fmap_app.
      rewrite heap_mapsto_cells_fancy_vec_app.
      unfold cl; simpl.
      replace (drop (length (FCell <$> γs1)) (cs1 ++ cells' :: cs2)) with (cells' :: cs2).
      2: {
        rewrite drop_app_length' => //.
        rewrite length_fmap; lia.
      }
      replace (take (length (FCell <$> γs1)) (cs1 ++ cells' :: cs2)) with cs1.
      2: {
        rewrite take_app_length' => //.
        rewrite length_fmap; lia.
      }
      rewrite heap_mapsto_cells_fancy_vec_cons.
      iDestruct (and_mono_l with "And") as "And".
      { iIntros "[H1 [H2 H3]]". iExact "H2". }
      apply elem_of_list_split_length in Hv as [vl1 [vl2 [Hvl Hvl1]]].
      rewrite Hvl.
      rewrite heap_cloc_mapsto_fancy_vec_app.
      rewrite -Hvl1 Hγs1.
      rewrite fmap_app.
      rewrite cloc_take_app_length'; first rewrite cloc_skip_app_length'.
      2,3: by rewrite length_fmap.
      rewrite fmap_cons.
      rewrite heap_mapsto_cloc_fancy_vec_cons.
      iDestruct (and_mono_r with "And") as "And".
      { iIntros "[H1 [H2 H3]]". iExact "H2". }
      rewrite Hcells.
      iApply pt_seq_cons_back_and. iSplit.
      + iDestruct "And" as "[H _]".
        rewrite /heap_mapsto_cells_fancy/=.
        by rewrite length_fmap.
      + iDestruct "And" as "[_ H]".
        rewrite /heap_complete_mapsto_fancy.
        simpl.
        destruct cv => //.
  Qed.


  (* untethering *)
  
  Lemma mapsto_vec_untether1 l fv E F :
      l #↦! fv ={E}=∗ ∃ (v: val), l #↦ v
          ∗ (∀ l₁, l₁ #↦_ ∗ l₁ #↦ v ={F}=∗ l₁ #↦_ ∗ l₁ #↦! fv)%I
          ∗ ⌜ match fv with FVal v0 => v0 = v | _ => True end ⌝.
  Proof.
      iIntros "pt". destruct fv.
       - iModIntro. iExists v. iFrame. iSplit. { iIntros. { iModIntro. iFrame. } } done.
       - iMod (pt_untether with "pt") as (v) "[pt back]".
         iModIntro. iExists v. iFrame "pt". iSplit; last by done. iIntros (l₁).
         destruct l₁ as [l0 c0]. iDestruct ("back" $! l0 c0) as "back".
         rewrite <- (heap_mapsto_cells_to_complete_mapsto_fancy (l0, c0) (FVal v)).
         rewrite <- (heap_mapsto_cells_to_complete_mapsto_fancy (l0, c0) (FCell c)).
         iIntros "A". iMod ("back" with "A"). iModIntro. iFrame.
  Qed.
 
  Lemma mapsto_vec_untether' l fv E F :
      l #↦!∗ fv ={E}=∗ ∃ (v: list val), l #↦∗ v ∗ ⌜length v = length fv⌝
          ∗ (∀ l₁, l₁ #↦∗_ ∗ l₁ #↦∗ v ={F}=∗ l₁ #↦∗_ ∗ l₁ #↦!∗ fv)%I
          ∗ ⌜ all_concrete fv → fv = fmap FVal v ⌝.
  Proof.
      destruct l as [l cs]. generalize l, fv. clear l. clear fv. induction cs.
       - intros l fv. iIntros "A". iModIntro. iExists []. 
         rewrite heap_complete_mapsto_val_empty.
         iDestruct (heap_cloc_mapsto_fancy_vec_length_eq with "A") as "%Hlen".
         iSplit; first by done. iSplit; first by iFrame "%".
         simpl in Hlen. symmetry in Hlen. rewrite length_zero_iff_nil in Hlen. subst fv. 
         iSplit; last by done.
         iIntros (l₁). iIntros "[B C]". iModIntro. iFrame. 
       - iIntros (l fv) "pt". destruct fv as [|fv fvs]; first by done.
         rewrite heap_mapsto_cloc_fancy_vec_cons. iDestruct "pt" as "[pt1 pt2]".
         iMod (IHcs with "pt2") as (vs) "[pt2 [%len [back2 %conc2]]]".
         iMod (mapsto_vec_untether1 with "pt1") as (v) "[pt1 [back1 %conc1]]".
         iModIntro. iExists (v :: vs). 
         rewrite heap_mapsto_cloc_vals_vec_cons. iFrame.
         iSplit. { iPureIntro. simpl; rewrite len; trivial. }
         iSplit. {
          iIntros (l₁). destruct l₁ as [l₁ c₁]. iIntros "[prefix pt]".
          destruct c₁ as [|c₁ cs₁]; first by done.
          rewrite heap_mapsto_cloc_emp_cons. rewrite heap_mapsto_cloc_vals_vec_cons.
          iDestruct "prefix" as "[prefix1 prefix2]".
          iDestruct "pt" as "[pt1 pt2]".
          iMod ("back1" with "[pt1 prefix1]") as "[pt1 prefix1]". { iFrame. }
          iMod ("back2" with "[pt2 prefix2]") as "[pt2 prefix2]". { iFrame. }
          iModIntro. iFrame.
         }
         iPureIntro. simpl. intros [conc1' conc2']. rewrite conc2; trivial.
         destruct fv. { subst v. trivial. } simpl in conc1'. contradiction.
  Qed.
  
  Lemma mapsto_vec_untether l fv E F :
      l #↦!∗ fv ={E}=∗ ∃ (v: list val), l #↦∗ v ∗ ⌜length v = length fv⌝
          ∗ (∀ l₁, l₁ #↦∗_ ∗ l₁ #↦∗ v ={F}=∗ l₁ #↦∗_ ∗ l₁ #↦!∗ fv)%I.
  Proof.
      iIntros "pt". iMod (mapsto_vec_untether' _ _ _ F with "pt") as (v) "(A & B & C & D)".
      iExists v. iModIntro. iFrame.
  Qed.
          
  Lemma mapsto_vec_untether_singleton l f E F :
      l #↦!∗ [f] ={E}=∗ ∃ v l₀ c₀, ⌜l = (l₀, [c₀])⌝ ∗ (l₀, c₀) #↦ v
          ∗ (∀ l₁ c₁, (l₁, c₁) #↦_ ∗ (l₁, c₁) #↦ v ={F}=∗ (l₁, c₁) #↦_ ∗ (l₁, [c₁]) #↦!∗ [f]).
  Proof.
    iIntros "pt". iMod (mapsto_vec_untether _ _ _ F with "pt") as (v) "[pt [%Heq Hback]]".
    iModIntro. destruct l as [l cs].
    iDestruct (heap_cloc_mapsto_fancy_vec_length_eq with "pt") as "%Hlen".
    rewrite length_fmap in Hlen. rewrite Heq in Hlen. simpl in Hlen.
    destruct cs as [|c cs]; first by done. destruct cs as [|]; last by done.
    simpl in Heq.
    destruct v as [|v vs]; first by done. destruct vs as [|]; last by done.
    iExists v, l, c. iSplit; first by done. iFrame.
    rewrite heap_complete_mapsto_val_singleton. iFrame.
    iIntros (l₁ c₁). iDestruct ("Hback" $! (l₁, [c₁])) as "Hback".
    rewrite heap_complete_mapsto_val_singleton. 
    rewrite heap_complete_mapsto_singleton. iFrame.
  Qed.
  
  Lemma mapsto_vec_untether_emp l fv E F :
      l ↦!∗ fv ={E}=∗ ∃ (v: list val), l ↦∗ v ∗ ⌜length v = length fv⌝
          ∗ (∀ l₁, l₁ #↦∗_ ∗ l₁ #↦∗ v ={F}=∗ l₁ #↦∗_ ∗ l₁ #↦!∗ fv)
          ∗ ⌜ all_concrete fv → fv = fmap FVal v ⌝.
  Proof. 
      have Ha := (mapsto_vec_untether' (l, repeat [] (length fv)) fv E F).
      rewrite <- heap_cloc_mapsto_fancy_empty in Ha. 
      iIntros "A". iMod (Ha with "A") as (v) "(B & %lens & D & E)".
      rewrite <- lens. rewrite <- heap_cloc_mapsto_val_empty.
      iModIntro. iExists v. iFrame. done.
  Qed.

  Lemma heap_mapsto_fancy_to_heap_complete_mapsto l γ : 
    (l ↦! FCell γ) ⊣⊢ ((l, [γ]) #↦_).
  Proof.
    by rewrite /heap_mapsto_fancy/heap_complete_mapsto/=.
  Qed.
  
  Lemma heap_delete_cell (l : loc) (γs : list cell_id) (fl : list fancy_val) :
    l ↦!∗ (FCell <$> γs) -∗ (l, (λ γ : cell_id, [γ]) <$> γs) #↦!∗ fl ==∗ l ↦!∗ fl.
  Proof.
    induction γs as [ | γ γs IH] in l, fl |- *.
    - simpl. iIntros "_ Hl !>". destruct fl => //.
    - rewrite !fmap_cons.
      destruct fl as [| fv fvs].
      + iIntros "_ H".
        by iDestruct (heap_cloc_mapsto_fancy_vec_length_eq with "H") as "%".
      + iIntros "Hcells Hvals".
        rewrite heap_mapsto_fancy_vec_cons.
        rewrite heap_mapsto_cloc_fancy_vec_cons.
        iDestruct "Hcells" as "(Hγ & Hγs)".
        iDestruct "Hvals" as "(Hfv & Hfvs)".
        rewrite heap_mapsto_fancy_vec_cons.
        iSplitL "Hγ Hfv".
        * rewrite heap_mapsto_fancy_to_heap_complete_mapsto.
          iCombine "Hγ Hfv" as "H".
          rewrite -(heap_mapsto_cells_to_complete_mapsto_fancy).
          rewrite /heap_mapsto_cells_fancy.
          by iMod (pt_delete_cell with "H") as "H".
        * by iMod (IH with "Hγs Hfvs").
  Qed.

  (* writes *)
  Lemma heap_write σ (l: cloc1) v v' E G d :
    ↑naN ⊆ E →
    £(3*d+1) -∗
    heap_ctx σ -∗ (G &&{↑naN;d}&&> l #↦_) -∗ G -∗ l #↦ v ={E}=∗
      ⌜σ.1 !! l.1 = Some (RSt 0, word_to_byte v)⌝ ∗
    heap_ctx (<[l.1 := (RSt 0, word_to_byte v')]> σ.1, σ.2) ∗ G ∗ l #↦ v'.
  Proof.
    iIntros (Hmask) "[£ £1] ctx #guards G pt". iDestruct "ctx" as (hF) "(Hσ & HhF & % & ato)".
    iDestruct "Hσ" as (σL σB) "(%Hr & Hσ & σB)".
    unfold heap_complete_mapsto, heap_complete_mapsto_fancy.
    destruct (split_at_last (snd l)) as [[cells c]|] eqn:Heq.
     - iMod (atomic_write_guarded_cells with "£ guards G pt Hσ") as "A". { apply Hmask. }
       iMod (lc_fupd_elim_later with "£1 A") as "A".
       iMod "A" as "[%res [G [pt Hσ]]]".
       iModIntro. iFrame. iPureIntro.
       have ? := phys_rel_lookup_L _ _ _ _ _ _ Hr res.
       split; [done|]. split; [|eauto using heap_freeable_rel_stable].
       apply phys_rel_L_insert; [done|]. by eapply phys_rel_L_not_B.
     - iMod (atomic_write with "pt Hσ") as "[%res [pt Hσ]]". { trivial. }
       iModIntro. iFrame. iPureIntro.
       have ? := phys_rel_lookup_L _ _ _ _ _ _ Hr res.
       split; [done|]. split; [|eauto using heap_freeable_rel_stable].
       apply phys_rel_L_insert; [done|]. by eapply phys_rel_L_not_B.
  Qed.

  Lemma heap_write_na σ (l: cloc1) v v' E G d :
    ↑naN ⊆ E →
    £(3*d) -∗
    heap_ctx σ -∗ (G &&{↑naN;d}&&> l #↦_) -∗ G -∗ l #↦ v ={E}=∗
      ⌜σ.1 !! l.1 = Some (RSt 0, word_to_byte v)⌝ ∗
      heap_ctx (<[l.1:=(WSt, word_to_byte v)]> σ.1, σ.2) ∗
      ∀ σ', £1 -∗ heap_ctx σ' ={E}=∗ ⌜∃b0, σ'.1 !! l.1 = Some (WSt, b0)⌝ ∗
        heap_ctx (<[l.1:=(RSt 0, word_to_byte v')]> σ'.1, σ'.2) ∗ G ∗ l #↦ v'.
  Proof.
    iIntros (Hmask) "£ ctx #guards G pt". iDestruct "ctx" as (hF) "(Hσ & HhF & % & ato)".
    iDestruct "Hσ" as (σL σB) "(%Hr & Hσ & σB)".
    unfold heap_complete_mapsto, heap_complete_mapsto_fancy.
    destruct (split_at_last (snd l)) as [[cells c]|] eqn:Heq.
     - iMod (na_write_begin_guarded_cells with "£ guards G pt Hσ") as "[%Hres [wim Hσ]]"; first by trivial.
       have ? := phys_rel_lookup_L _ _ _ _ _ _ Hr Hres.
       iModIntro. iFrame "%". iSplitR "wim".
       { iFrame. iPureIntro. split; [|eauto using heap_freeable_rel_stable].
         apply phys_rel_L_insert; [done|]. by eapply phys_rel_L_not_B. }
       iIntros (x) "£1 ctx". iDestruct "ctx" as (hF') "(Hσ & HhF & % & ato)".
       iDestruct "Hσ" as (σL' σB') "(%Hr' & Hσ & σB)".
       iDestruct (na_write_finish_guarded_cells with "wim Hσ") as "A"; first by apply Hmask.
       iMod (lc_fupd_elim_later with "£1 A") as "A".
       iMod "A" as "[%Hres2 [G [pt Hσ]]]".
       destruct Hres2 as [v0 Hres2]. have ? := phys_rel_lookup_L _ _ _ _ _ _ Hr' Hres2.
       iModIntro. iFrame. iPureIntro. split; [by eexists|].
       split; [|eauto using heap_freeable_rel_stable].
       apply phys_rel_L_insert; [done|]. by eapply phys_rel_L_not_B.
     - iMod (na_write_begin with "pt Hσ") as "[%Hres [wim Hσ]]"; first by trivial.
       have ? := phys_rel_lookup_L _ _ _ _ _ _ Hr Hres.
       iModIntro. iFrame "%". iSplitR "G wim".
       { iFrame. iPureIntro. split; [|eauto using heap_freeable_rel_stable].
         apply phys_rel_L_insert; [done|]. by eapply phys_rel_L_not_B. }
       iIntros (x) "£1 ctx". iDestruct "ctx" as (hF') "(Hσ & HhF & % & ato)".
       iDestruct "Hσ" as (σL' σB') "(%Hr' & Hσ & σB)".
       iMod (na_write_finish with "wim Hσ") as "[%Hres2 [pt Hσ]]"; first by trivial.
       destruct Hres2 as [v0 Hres2]. have ? := phys_rel_lookup_L _ _ _ _ _ _ Hr' Hres2.
       iModIntro. iFrame. iPureIntro. split; [by eexists|].
       split; [|eauto using heap_freeable_rel_stable].
       apply phys_rel_L_insert; [done|]. by eapply phys_rel_L_not_B.
  Qed.

End heap.

(** * The byte region *)
Section byte_defs.
  Context `{!heapGS Σ}.

  Definition heap_mapsto_st (st : lock_state) (l : loc) (q : Qp) (b : abyte) : iProp Σ :=
    own heap_bytes_name (◯ {[ l := (q, to_lock_stateR st, to_agree b) ]}).

  Definition heap_mapsto_st_vec (st : lock_state) (l : loc) (q : Qp) (bs : list abyte) : iProp Σ :=
    [∗ list] i ↦ b ∈ bs, heap_mapsto_st st (l +ₗ i) q b.

  (** The byte points-to: [l ↦b{q} bs] owns the fraction [q] of the bytes [bs] at
      [l], [l +ₗ 1], ... *)
  Definition heap_mapsto_bytes_def (l : loc) (q : Qp) (bs : list abyte) : iProp Σ :=
    heap_mapsto_st_vec (RSt 0) l q bs.
  Definition heap_mapsto_bytes_aux : seal (@heap_mapsto_bytes_def). Proof. by eexists. Qed.
  Definition heap_mapsto_bytes := unseal heap_mapsto_bytes_aux.
  Definition heap_mapsto_bytes_eq : @heap_mapsto_bytes = @heap_mapsto_bytes_def :=
    seal_eq heap_mapsto_bytes_aux.
End byte_defs.

Global Instance: Params (@heap_mapsto_bytes) 4 := {}.

Notation "l ↦b{ q } bs" := (heap_mapsto_bytes l q bs)
  (at level 20, q at level 50, format "l  ↦b{ q }  bs") : bi_scope.
Notation "l ↦b bs" := (heap_mapsto_bytes l 1%Qp bs) (at level 20) : bi_scope.

Section bytes.
  Context `{!heapGS Σ}.
  Implicit Types σB : gmap loc (lock_state * abyte).
  Implicit Types bs : list abyte.

  (** ** Structural lemmas *)
  Global Instance heap_mapsto_bytes_timeless l q bs : Timeless (l ↦b{q} bs).
  Proof. rewrite heap_mapsto_bytes_eq /heap_mapsto_bytes_def /heap_mapsto_st_vec. apply _. Qed.

  Lemma heap_mapsto_bytes_nil l q : l ↦b{q} [] ⊣⊢ True.
  Proof. by rewrite heap_mapsto_bytes_eq. Qed.

  Lemma heap_mapsto_st_vec_app st l q bs1 bs2 :
    heap_mapsto_st_vec st l q (bs1 ++ bs2) ⊣⊢
    heap_mapsto_st_vec st l q bs1 ∗ heap_mapsto_st_vec st (l +ₗ length bs1) q bs2.
  Proof.
    rewrite /heap_mapsto_st_vec big_sepL_app.
    do 2 f_equiv. intros k b. by rewrite shift_loc_assoc_nat.
  Qed.

  Lemma heap_mapsto_st_vec_cons st l q b bs :
    heap_mapsto_st_vec st l q (b :: bs) ⊣⊢
    heap_mapsto_st st l q b ∗ heap_mapsto_st_vec st (l +ₗ 1) q bs.
  Proof.
    rewrite (heap_mapsto_st_vec_app _ _ _ [b] bs) /heap_mapsto_st_vec /=.
    by rewrite shift_loc_0 right_id.
  Qed.

  Lemma heap_mapsto_bytes_app l q bs1 bs2 :
    l ↦b{q} (bs1 ++ bs2) ⊣⊢ l ↦b{q} bs1 ∗ (l +ₗ length bs1) ↦b{q} bs2.
  Proof. rewrite heap_mapsto_bytes_eq. apply heap_mapsto_st_vec_app. Qed.

  Lemma heap_mapsto_bytes_cons l q b bs :
    l ↦b{q} (b :: bs) ⊣⊢ l ↦b{q} [b] ∗ (l +ₗ 1) ↦b{q} bs.
  Proof. by rewrite (heap_mapsto_bytes_app l q [b] bs). Qed.

  Global Instance heap_mapsto_bytes_fractional l bs : Fractional (λ q, l ↦b{q} bs)%I.
  Proof.
    rewrite heap_mapsto_bytes_eq /heap_mapsto_bytes_def /heap_mapsto_st_vec.
    intros q1 q2. rewrite -big_sepL_sep. f_equiv. intros i b.
    rewrite /heap_mapsto_st -own_op -auth_frag_op singleton_op -!pair_op.
    by rewrite /= -Cinr_op agree_idemp.
  Qed.
  Global Instance heap_mapsto_bytes_as_fractional l q bs :
    AsFractional (l ↦b{q} bs) (λ q, l ↦b{q} bs)%I q.
  Proof. split; [done|apply _]. Qed.

  (** ** Single locations (as in lambda-Rust) *)
  Lemma to_heap_insert σB l x b :
    to_heap (<[l:=(x, b)]> σB) = <[l:=(1%Qp, to_lock_stateR x, to_agree b)]> (to_heap σB).
  Proof. by rewrite /to_heap fmap_insert. Qed.

  Lemma heap_mapsto_st_lookup σB l ls q b :
    own heap_bytes_name (● to_heap σB) -∗ heap_mapsto_st ls l q b -∗
    ⌜∃ n' : nat, σB !! l = Some (match ls with RSt n => RSt (n+n') | WSt => WSt end, b)⌝.
  Proof.
    iIntros "H● H◯".
    iDestruct (own_valid_2 with "H● H◯") as %[Hl?]%auth_both_valid_discrete.
    iPureIntro. move: Hl=> /singleton_included_l [[[q' ls'] dv]].
    rewrite /to_heap lookup_fmap fmap_Some_equiv.
    move=> [[[ls'' v'] [?[[/=??]->]]]]; simplify_eq.
    move=> /Some_pair_included_total_2
      [/Some_pair_included [_ Hincl] /to_agree_included->].
    destruct ls as [|n], ls'' as [|n''],
       Hincl as [[[|n'|]|] [=]%leibniz_equiv]; subst.
    - by exists O.
    - eauto.
    - exists O. by rewrite Nat.add_0_r.
  Qed.

  Lemma heap_mapsto_st_lookup_1 σB l ls b :
    own heap_bytes_name (● to_heap σB) -∗ heap_mapsto_st ls l 1%Qp b -∗
    ⌜σB !! l = Some (ls, b)⌝.
  Proof.
    iIntros "H● H◯".
    iDestruct (own_valid_2 with "H● H◯") as %[Hl?]%auth_both_valid_discrete.
    iPureIntro. move: Hl=> /singleton_included_l [[[q' ls'] dv]].
    rewrite /to_heap lookup_fmap fmap_Some_equiv.
    move=> [[[ls'' v'] [?[[/=??]->]]] Hincl]; simplify_eq.
    apply (Some_included_exclusive _ _) in Hincl as [? Hval]; last by destruct ls''.
    apply (inj to_agree) in Hval. fold_leibniz. subst.
    destruct ls, ls''; rewrite ?Nat.add_0_r; naive_solver.
  Qed.

  Lemma heap_read_vs σB n1 n2 nf l q b :
    σB !! l = Some (RSt (n1 + nf), b) →
    own heap_bytes_name (● to_heap σB) -∗ heap_mapsto_st (RSt n1) l q b
    ==∗ own heap_bytes_name (● to_heap (<[l:=(RSt (n2 + nf), b)]> σB))
        ∗ heap_mapsto_st (RSt n2) l q b.
  Proof.
    intros Hσv. iIntros "H● H◯".
    iMod (own_update_2 _ _ _ (● to_heap (<[l:=(RSt (n2 + nf), b)]> σB) ⋅
      ◯ {[l := (q, to_lock_stateR (RSt n2), to_agree b)]}) with "H● H◯") as "[$ $]"; [|done].
    rewrite to_heap_insert. eapply auth_update, singleton_local_update.
    { by rewrite /to_heap lookup_fmap Hσv. }
    apply prod_local_update_1, prod_local_update_2, csum_local_update_r.
    apply nat_local_update; lia.
  Qed.

  Lemma heap_write_vs σB st1 st2 l b b' :
    σB !! l = Some (st1, b) →
    own heap_bytes_name (● to_heap σB) -∗ heap_mapsto_st st1 l 1%Qp b
    ==∗ own heap_bytes_name (● to_heap (<[l:=(st2, b')]> σB))
        ∗ heap_mapsto_st st2 l 1%Qp b'.
  Proof.
    intros Hσv. iIntros "H● H◯".
    iMod (own_update_2 _ _ _ (● to_heap (<[l:=(st2, b')]> σB) ⋅
      ◯ {[l := (1%Qp, to_lock_stateR st2, to_agree b')]}) with "H● H◯") as "[$ $]"; [|done].
    rewrite to_heap_insert. eapply auth_update, singleton_local_update.
    { by rewrite /to_heap lookup_fmap Hσv. }
    apply exclusive_local_update. by destruct st2.
  Qed.

  Lemma heap_bytes_alloc_vs σB l b :
    σB !! l = None →
    own heap_bytes_name (● to_heap σB) ==∗
    own heap_bytes_name (● to_heap (<[l:=(RSt 0, b)]> σB)) ∗ heap_mapsto_st (RSt 0) l 1%Qp b.
  Proof.
    intros Hl. iIntros "H●".
    iMod (own_update _ _ (● to_heap (<[l:=(RSt 0, b)]> σB) ⋅
      ◯ {[l := (1%Qp, to_lock_stateR (RSt 0), to_agree b)]}) with "H●") as "[$ $]"; [|done].
    rewrite to_heap_insert. apply auth_update_alloc, alloc_singleton_local_update.
    - by rewrite /to_heap lookup_fmap Hl.
    - split; [split|]; done.
  Qed.

  Lemma heap_bytes_dealloc_vs σB l b :
    own heap_bytes_name (● to_heap σB) -∗ heap_mapsto_st (RSt 0) l 1%Qp b ==∗
    ⌜σB !! l = Some (RSt 0, b)⌝ ∗ own heap_bytes_name (● to_heap (delete l σB)).
  Proof.
    iIntros "H● H◯". iDestruct (heap_mapsto_st_lookup_1 with "H● H◯") as %Hl.
    iMod (own_update_2 with "H● H◯") as "$"; [|done].
    rewrite /to_heap fmap_delete.
    apply auth_update_dealloc, (delete_singleton_local_update _ _ _).
  Qed.

  Lemma alter_insert_Some {A} (m : gmap loc A) l (f : A → A) x :
    m !! l = Some x → alter f l m = <[l := f x]> m.
  Proof.
    intros Hl. apply map_eq. intros l'. destruct (decide (l = l')) as [<-|].
    - by rewrite lookup_alter lookup_insert Hl.
    - by rewrite lookup_alter_ne // lookup_insert_ne.
  Qed.

  (** ** Ranges *)
  Lemma heap_bytes_lookup σB l q bs :
    own heap_bytes_name (● to_heap σB) -∗ l ↦b{q} bs -∗ ⌜mem_range is_reading σB l bs⌝.
  Proof.
    rewrite heap_mapsto_bytes_eq /heap_mapsto_bytes_def.
    iInduction bs as [|b bs] "IH" forall (l); iIntros "H● Hbs"; [done|].
    rewrite heap_mapsto_st_vec_cons. iDestruct "Hbs" as "[Hb Hbs]".
    iDestruct (heap_mapsto_st_lookup with "H● Hb") as %[n Hl].
    iDestruct ("IH" with "H● Hbs") as %?. iPureIntro. split; [|done].
    eexists. split; [done|]. by eexists.
  Qed.

  Lemma heap_bytes_lookup_1 σB l bs :
    own heap_bytes_name (● to_heap σB) -∗ l ↦b bs -∗ ⌜mem_range (.= RSt 0) σB l bs⌝.
  Proof.
    rewrite heap_mapsto_bytes_eq /heap_mapsto_bytes_def.
    iInduction bs as [|b bs] "IH" forall (l); iIntros "H● Hbs"; [done|].
    rewrite heap_mapsto_st_vec_cons. iDestruct "Hbs" as "[Hb Hbs]".
    iDestruct (heap_mapsto_st_lookup_1 with "H● Hb") as %Hl.
    iDestruct ("IH" with "H● Hbs") as %?. iPureIntro. split; [|done]. by eexists.
  Qed.

  Lemma heap_bytes_read_begin σB l q bs :
    own heap_bytes_name (● to_heap σB) -∗ l ↦b{q} bs ==∗
    own heap_bytes_name (● to_heap (mem_alter ls_inc l (length bs) σB))
      ∗ heap_mapsto_st_vec (RSt 1) l q bs.
  Proof.
    rewrite heap_mapsto_bytes_eq /heap_mapsto_bytes_def.
    iInduction bs as [|b bs] "IH" forall (l); iIntros "H● Hbs"; [by iFrame|].
    rewrite !heap_mapsto_st_vec_cons. iDestruct "Hbs" as "[Hb Hbs]".
    iDestruct (heap_mapsto_st_lookup with "H● Hb") as %[n Hl].
    iMod ("IH" with "H● Hbs") as "[H● $]".
    iMod (heap_read_vs _ 0 1 n with "H● Hb") as "[H● $]".
    { rewrite lookup_mem_alter_out //. intros ??; apply shift_loc_ne_S. }
    iModIntro. rewrite /= (alter_insert_Some _ _ _ (RSt n, b)) //.
    rewrite lookup_mem_alter_out //. intros ??; apply shift_loc_ne_S.
  Qed.

  Lemma heap_bytes_read_end σB l q bs :
    own heap_bytes_name (● to_heap σB) -∗ heap_mapsto_st_vec (RSt 1) l q bs ==∗
    ⌜mem_range is_reading_S σB l bs⌝
      ∗ own heap_bytes_name (● to_heap (mem_alter ls_dec l (length bs) σB)) ∗ l ↦b{q} bs.
  Proof.
    rewrite heap_mapsto_bytes_eq /heap_mapsto_bytes_def.
    iInduction bs as [|b bs] "IH" forall (l); iIntros "H● Hbs"; [by iFrame|].
    rewrite !heap_mapsto_st_vec_cons. iDestruct "Hbs" as "[Hb Hbs]".
    iDestruct (heap_mapsto_st_lookup with "H● Hb") as %[n Hl].
    iMod ("IH" with "H● Hbs") as "[%Hr [H● $]]".
    iMod (heap_read_vs _ 1 0 n with "H● Hb") as "[H● $]".
    { rewrite lookup_mem_alter_out //. intros ??; apply shift_loc_ne_S. }
    iModIntro. iSplit.
    { iPureIntro. split; [|done]. eexists. split; [done|]. by eexists. }
    rewrite /= (alter_insert_Some _ _ _ (RSt (1 + n), b)) //.
    rewrite lookup_mem_alter_out //. intros ??; apply shift_loc_ne_S.
  Qed.

  Lemma heap_bytes_write_begin σB l bs :
    own heap_bytes_name (● to_heap σB) -∗ l ↦b bs ==∗
    ⌜mem_range (.= RSt 0) σB l bs⌝
      ∗ own heap_bytes_name (● to_heap (mem_alter (λ _, WSt) l (length bs) σB))
      ∗ heap_mapsto_st_vec WSt l 1%Qp bs.
  Proof.
    rewrite heap_mapsto_bytes_eq /heap_mapsto_bytes_def.
    iInduction bs as [|b bs] "IH" forall (l); iIntros "H● Hbs"; [by iFrame|].
    rewrite !heap_mapsto_st_vec_cons. iDestruct "Hbs" as "[Hb Hbs]".
    iDestruct (heap_mapsto_st_lookup_1 with "H● Hb") as %Hl.
    iMod ("IH" with "H● Hbs") as "[%Hr [H● $]]".
    iMod (heap_write_vs _ _ WSt _ _ b with "H● Hb") as "[H● $]".
    { rewrite lookup_mem_alter_out //. intros ??; apply shift_loc_ne_S. }
    iModIntro. iSplit; [by iPureIntro; split; [eexists|]|].
    rewrite /= (alter_insert_Some _ _ _ (RSt 0, b)) //.
    rewrite lookup_mem_alter_out //. intros ??; apply shift_loc_ne_S.
  Qed.

  Lemma heap_bytes_write_end σB l bs bs' :
    length bs' = length bs →
    own heap_bytes_name (● to_heap σB) -∗ heap_mapsto_st_vec WSt l 1%Qp bs ==∗
    ⌜mem_range (.= WSt) σB l bs⌝
      ∗ own heap_bytes_name (● to_heap (mem_write l bs' σB)) ∗ l ↦b bs'.
  Proof.
    rewrite heap_mapsto_bytes_eq /heap_mapsto_bytes_def.
    iInduction bs as [|b bs] "IH" forall (l bs'); iIntros (Hlen) "H● Hbs";
      destruct bs' as [|b' bs']; try done; [by iFrame|].
    rewrite !heap_mapsto_st_vec_cons. iDestruct "Hbs" as "[Hb Hbs]".
    iDestruct (heap_mapsto_st_lookup_1 with "H● Hb") as %Hl.
    iMod ("IH" $! _ bs' with "[] H● Hbs") as "[%Hr [H● $]]"; [by simplify_eq/=|].
    iMod (heap_write_vs _ _ (RSt 0) _ _ b' with "H● Hb") as "[H● $]".
    { rewrite lookup_mem_write_out //. intros ??; apply shift_loc_ne_S. }
    iModIntro. by iSplit; [iPureIntro; split; [eexists|]|].
  Qed.

  Lemma heap_bytes_write σB l bs bs' :
    length bs' = length bs →
    own heap_bytes_name (● to_heap σB) -∗ l ↦b bs ==∗
    ⌜mem_range (.= RSt 0) σB l bs⌝
      ∗ own heap_bytes_name (● to_heap (mem_write l bs' σB)) ∗ l ↦b bs'.
  Proof.
    rewrite heap_mapsto_bytes_eq /heap_mapsto_bytes_def.
    iInduction bs as [|b bs] "IH" forall (l bs'); iIntros (Hlen) "H● Hbs";
      destruct bs' as [|b' bs']; try done; [by iFrame|].
    rewrite !heap_mapsto_st_vec_cons. iDestruct "Hbs" as "[Hb Hbs]".
    iDestruct (heap_mapsto_st_lookup_1 with "H● Hb") as %Hl.
    iMod ("IH" $! _ bs' with "[] H● Hbs") as "[%Hr [H● $]]"; [by simplify_eq/=|].
    iMod (heap_write_vs _ _ (RSt 0) _ _ b' with "H● Hb") as "[H● $]".
    { rewrite lookup_mem_write_out //. intros ??; apply shift_loc_ne_S. }
    iModIntro. by iSplit; [iPureIntro; split; [eexists|]|].
  Qed.

  Lemma heap_st_vec_lookup_1 σB st l bs :
    own heap_bytes_name (● to_heap σB) -∗ heap_mapsto_st_vec st l 1%Qp bs -∗
    ⌜mem_range (.= st) σB l bs⌝.
  Proof.
    iInduction bs as [|b bs] "IH" forall (l); iIntros "H● Hbs"; [done|].
    rewrite heap_mapsto_st_vec_cons. iDestruct "Hbs" as "[Hb Hbs]".
    iDestruct (heap_mapsto_st_lookup_1 with "H● Hb") as %Hl.
    iDestruct ("IH" with "H● Hbs") as %?. iPureIntro. split; [|done]. by eexists.
  Qed.

  Lemma heap_st_vec_lookup_reading σB l q bs :
    own heap_bytes_name (● to_heap σB) -∗ heap_mapsto_st_vec (RSt 1) l q bs -∗
    ⌜mem_range is_reading_S σB l bs⌝.
  Proof.
    iInduction bs as [|b bs] "IH" forall (l); iIntros "H● Hbs"; [done|].
    rewrite heap_mapsto_st_vec_cons. iDestruct "Hbs" as "[Hb Hbs]".
    iDestruct (heap_mapsto_st_lookup with "H● Hb") as %[n Hl].
    iDestruct ("IH" with "H● Hbs") as %?. iPureIntro. split; [|done].
    eexists. split; [done|]. by eexists.
  Qed.

  Lemma heap_freeable_rel_dom (σ σ' : state) hF :
    (∀ l, is_Some (σ.1 !! l) ↔ is_Some (σ'.1 !! l)) →
    heap_freeable_rel σ hF → heap_freeable_rel σ' hF.
  Proof.
    intros Hdom REL blk qs Hqs. destruct (REL blk qs Hqs) as [? REL'].
    split; [done|]. intros i. by rewrite -Hdom.
  Qed.

  Lemma is_Some_mem_write P (σ : state') l bs0 bs l' :
    mem_range P σ l bs0 → length bs = length bs0 →
    is_Some (mem_write l bs σ !! l') ↔ is_Some (σ !! l').
  Proof.
    intros Hbs Hlen. destruct (loc_range_dec l (length bs0) l') as [[i [Hi ->]]|Hout].
    - destruct (mem_range_lookup_1 _ _ _ _ i Hbs Hi) as (ls & b & Hl & _).
      destruct (lookup_lt_is_Some_2 bs i) as [b' Hb']; [lia|].
      rewrite (lookup_mem_write_in _ _ _ _ b') //; rewrite Hl; split; eauto.
    - rewrite lookup_mem_write_out //. by rewrite Hlen.
  Qed.

  (** ** The physical relation for ranges of the byte region *)
  Lemma phys_rel_mem_range P σ σL σB l bs :
    phys_rel σ σL σB → mem_range P σB l bs → mem_range P σ l bs.
  Proof.
    rewrite !mem_range_lookup. intros Hr H i b Hb.
    destruct (H i b Hb) as (ls & Hl & ?). exists ls. split; [|done].
    by eapply phys_rel_lookup_B.
  Qed.

  Lemma phys_rel_mem_alter P f σ σL σB l bs :
    phys_rel σ σL σB → mem_range P σB l bs →
    phys_rel (mem_alter f l (length bs) σ) σL (mem_alter f l (length bs) σB).
  Proof.
    intros Hr Hbs. apply (phys_rel_B_update σ _ σL σB); [done|]. intros l'.
    destruct (loc_range_dec l (length bs) l') as [[i [Hi ->]]|Hout].
    - right. destruct (mem_range_lookup_1 _ _ _ _ i Hbs Hi) as (ls & b & Hl & _).
      rewrite !lookup_mem_alter_in // Hl (phys_rel_lookup_B _ _ _ _ _ Hr Hl). eauto.
    - left. by rewrite !lookup_mem_alter_out.
  Qed.

  Lemma phys_rel_mem_write P σ σL σB l bs bs' :
    phys_rel σ σL σB → mem_range P σB l bs → length bs' = length bs →
    phys_rel (mem_write l bs' σ) σL (mem_write l bs' σB).
  Proof.
    intros Hr Hbs Hlen. apply (phys_rel_B_update σ _ σL σB); [done|]. intros l'.
    destruct (loc_range_dec l (length bs) l') as [[i [Hi ->]]|Hout].
    - right. destruct (mem_range_lookup_1 _ _ _ _ i Hbs Hi) as (ls & b & Hl & _).
      destruct (lookup_lt_is_Some_2 bs' i) as [b' Hb']; [lia|].
      rewrite !(lookup_mem_write_in _ _ _ _ b') //; rewrite Hl; eauto.
    - left. rewrite !lookup_mem_write_out //; by rewrite Hlen.
  Qed.

  Lemma mem_alter_mem_write f l bs σB :
    mem_write l bs (mem_alter f l (length bs) σB) = mem_write l bs σB.
  Proof.
    apply map_eq. intros l'. destruct (loc_range_dec l (length bs) l') as [[i [Hi ->]]|Hout].
    - destruct (lookup_lt_is_Some_2 bs i) as [b Hb]; [lia|].
      by rewrite !(lookup_mem_write_in _ _ _ _ b).
    - by rewrite !lookup_mem_write_out // lookup_mem_alter_out.
  Qed.
End bytes.

Section bytes_ctx.
  Context `{!heapGS Σ}.
  Context `{!invGS Σ}.
  Context `{!na_invG Σ}.
  Context `{!alc_logicG Σ}.
  Implicit Types bs : list abyte.

  (** ** Allocation and deallocation in the byte region *)
  Lemma heap_alloc_bytes_vs (σ : state') l n :
    (∀ m : Z, σ !! (l +ₗ m) = None) →
    heap_maps_ctx σ ==∗ heap_maps_ctx (init_mem l n σ) ∗ l ↦b (replicate n Uninit).
  Proof.
    revert l. induction n as [|n IH]; iIntros (l Hfresh) "σ".
    { iFrame. by rewrite heap_mapsto_bytes_nil. }
    iMod (IH (l +ₗ 1) with "σ") as "[σ Hl]".
    { intros m. rewrite shift_loc_assoc. apply Hfresh. }
    iDestruct "σ" as (σL σB) "(%Hr & σ & σB)".
    have Hfr : init_mem (l +ₗ 1) n σ !! l = None.
    { rewrite lookup_init_mem_ne /=; last lia. rewrite -(shift_loc_0 l). apply Hfresh. }
    destruct (phys_rel_None _ _ _ _ Hr Hfr) as [HL HB].
    iMod (heap_bytes_alloc_vs _ _ Uninit with "σB") as "[σB Hb]"; [done|].
    iModIntro. rewrite /= (heap_mapsto_bytes_cons _ _ Uninit). iFrame.
    iSplitR; [iPureIntro; by apply phys_rel_B_insert|].
    rewrite heap_mapsto_bytes_eq /heap_mapsto_bytes_def /heap_mapsto_st_vec /=.
    rewrite shift_loc_0. by iFrame.
  Qed.

  Lemma heap_alloc_bytes (σ: state) l n :
    0 < n →
    (∀ m, σ.1 !! (l +ₗ m) = None) →
    heap_ctx σ ==∗
      heap_ctx (init_mem l (Z.to_nat n) $σ σ) ∗ †l…(Z.to_nat n) ∗
      l ↦b replicate (Z.to_nat n) Uninit.
  Proof.
    intros ??; iDestruct 1 as (hF) "(Hvalσ & HhF & % & ato)".
    assert (Z.to_nat n ≠ O). { rewrite -(Nat2Z.id 0)=>/Z2Nat.inj. lia. }
    iMod (heap_alloc_bytes_vs _ _ (Z.to_nat n) with "[$Hvalσ]") as "[Hvalσ Hmapsto]"; first done.
    iMod (own_update _ (● hF) with "HhF") as "[HhF Hfreeable]".
    { apply auth_update_alloc,
        (alloc_singleton_local_update _ (l.1) (1%Qp, inter (l.2) (Z.to_nat n))).
      - eauto using heap_freeable_rel_None.
      - split; first done. apply inter_valid. }
    iModIntro. iSplitL "Hvalσ HhF ato".
    { iExists _. iFrame. iPureIntro.
      auto using heap_freeable_rel_init_mem. }
    rewrite heap_freeable_eq /heap_freeable_def //. iFrame.
  Qed.

  Lemma heap_free_bytes_vs (σ : state') l bs :
    heap_maps_ctx σ -∗ l ↦b bs ==∗ heap_maps_ctx (free_mem l (length bs) σ).
  Proof.
    iInduction bs as [|b bs] "IH" forall (l); iIntros "σ Hbs"; [by iFrame|].
    rewrite heap_mapsto_bytes_cons. iDestruct "Hbs" as "[Hb Hbs]".
    iMod ("IH" with "σ Hbs") as "σ".
    iDestruct "σ" as (σL σB) "(%Hr & σ & σB)".
    rewrite heap_mapsto_bytes_eq /heap_mapsto_bytes_def /heap_mapsto_st_vec /= shift_loc_0.
    iDestruct "Hb" as "[Hb _]".
    iMod (heap_bytes_dealloc_vs with "σB Hb") as "[%Hl σB]".
    iModIntro. iFrame. iPureIntro. apply phys_rel_B_delete; [done|].
    eapply phys_rel_B_not_L; [done|]. by eexists.
  Qed.

  Lemma heap_free_bytes σ l bs (n : Z) E :
    n = length bs →
    heap_ctx σ -∗ l ↦b bs -∗ †l…(length bs)
    ={E}=∗ ⌜0 < n⌝ ∗ ⌜∀ m, is_Some (σ.1 !! (l +ₗ m)) ↔ (0 ≤ m < n)⌝ ∗
        heap_ctx (free_mem l (Z.to_nat n) $σ σ).
  Proof.
    iDestruct 1 as (hF) "(Hvalσ & HhF & REL & ato)"; iDestruct "REL" as %REL.
    iIntros "Hmt Hf". rewrite heap_freeable_eq /heap_freeable_def.
    iDestruct (own_valid_2 with "HhF Hf") as % [Hl Hv]%auth_both_valid_discrete.
    move: Hl=> /singleton_included_l [[q qs] [/leibniz_equiv_iff Hl Hq]].
    apply (Some_included_exclusive _ _) in Hq as [=<-<-]%leibniz_equiv; last first.
    { move: (Hv (l.1)). rewrite Hl. by intros [??]. }
    assert (bs ≠ []).
    { intros ->. by destruct (REL (l.1) (1%Qp, ∅)) as [[] ?]. }
    assert (0 < n) by (subst n; by destruct bs).
    iMod (heap_free_bytes_vs with "Hvalσ Hmt") as "Hvalσ".
    iMod (own_update_2 with "HhF Hf") as "HhF".
    { apply auth_update_dealloc, (delete_singleton_local_update _ _ _). }
    iModIntro; subst. repeat iSplit;  eauto using heap_freeable_is_Some.
    iExists _. subst. rewrite Nat2Z.id. iFrame.
    eauto using heap_freeable_rel_free_mem.
  Qed.

  (** ** Moving locations between the legacy region and the byte region *)
  Lemma heap_word_to_bytes (σ : state') l v E :
    ↑naN ⊆ E →
    heap_maps_ctx σ -∗ l ↦ v ={E}=∗ heap_maps_ctx σ ∗ l ↦b [word_to_byte v].
  Proof.
    iIntros (?) "(%σL & %σB & %Hr & σ & σB) Hl". rewrite /heap_mapsto.
    iMod (non_atomic_map_delete with "Hl σ") as "[%HL σ]"; [done|].
    have HB := phys_rel_L_not_B _ _ _ _ Hr (mk_is_Some _ _ HL).
    iMod (heap_bytes_alloc_vs _ _ (word_to_byte v) with "σB") as "[σB Hb]"; [done|].
    iModIntro. iFrame. iSplitR; [iPureIntro; by apply phys_rel_L_to_B|].
    rewrite heap_mapsto_bytes_eq /heap_mapsto_bytes_def /heap_mapsto_st_vec /=.
    rewrite shift_loc_0. by iFrame.
  Qed.

  Lemma heap_bytes_to_word (σ : state') l v :
    heap_maps_ctx σ -∗ l ↦b [word_to_byte v] ==∗ heap_maps_ctx σ ∗ l ↦ v.
  Proof.
    iIntros "(%σL & %σB & %Hr & σ & σB) Hb".
    rewrite heap_mapsto_bytes_eq /heap_mapsto_bytes_def /heap_mapsto_st_vec /= shift_loc_0.
    iDestruct "Hb" as "[Hb _]".
    iMod (heap_bytes_dealloc_vs with "σB Hb") as "[%HB σB]".
    have HL := phys_rel_B_not_L _ _ _ _ Hr (mk_is_Some _ _ HB).
    iMod (non_atomic_map_insert _ l v with "σ") as "[Hl σ]"; [done|].
    iModIntro. iFrame. iSplitR; [iPureIntro; by apply phys_rel_B_to_L|]. by rewrite /heap_mapsto.
  Qed.

  Lemma heap_words_to_bytes (σ : state') l vl E :
    ↑naN ⊆ E →
    heap_maps_ctx σ -∗ l ↦∗ vl ={E}=∗ heap_maps_ctx σ ∗ l ↦b (word_to_byte <$> vl).
  Proof.
    iIntros (?). iInduction vl as [|v vl] "IH" forall (l); iIntros "σ Hvl".
    { iFrame. by rewrite heap_mapsto_bytes_nil. }
    rewrite heap_mapsto_vec_cons fmap_cons heap_mapsto_bytes_cons.
    iDestruct "Hvl" as "[Hv Hvl]".
    iMod (heap_word_to_bytes with "σ Hv") as "[σ $]"; [done|].
    iApply ("IH" with "σ Hvl").
  Qed.

  Lemma heap_bytes_to_words (σ : state') l vl :
    heap_maps_ctx σ -∗ l ↦b (word_to_byte <$> vl) ==∗ heap_maps_ctx σ ∗ l ↦∗ vl.
  Proof.
    iInduction vl as [|v vl] "IH" forall (l); iIntros "σ Hvl".
    { iFrame. by rewrite heap_mapsto_vec_nil. }
    rewrite heap_mapsto_vec_cons fmap_cons heap_mapsto_bytes_cons.
    iDestruct "Hvl" as "[Hv Hvl]".
    iMod (heap_bytes_to_word with "σ Hv") as "[σ $]".
    iApply ("IH" with "σ Hvl").
  Qed.
End bytes_ctx.
