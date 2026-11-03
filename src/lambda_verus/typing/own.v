From lrust.typing Require Export type.
From lrust.typing Require Import freeable_util bytes_layout gmb_cells.
From guarding Require Import guard tactics.
From lrust.lifetime Require Import lifetime_full.
Set Default Proof Using "Type".

(** * Owning pointers to bytes (stage 3 of the MiniRust memory model)

[own_bytes n ty] is an owning pointer whose pointee lives in the byte region of the
heap (see [lang/heap.v]): it owns the bytes that represent the value of the pointee
([bytes_own ty l x]), and the freeable token of the [ty_bsize ty] bytes of a block of [n]
bytes (see [design_docs/minirust-memory-model.md], "Outcome: stage 3"). It replaced the
legacy word-level [own_ptr] (deleted in stage 5).

The bytes are the _contents_ [gcont l (ty_mty ty) (ty_fval x)] of phase 4 of
[design_docs/guarded-mutable-borrows-plan.md] ([typing/gcont.v]): the plain bytes of the
fancy bytes of the fancy value of [x], and the move rights of the cells that it embeds
(which are GMB instances, [typing/gmb_cells.v]); the bytes at the positions of a cell are the
contents of the cell. A value of a type without cells ([NoCell]), or with a MiniRust value,
owns plain bytes [l ↦b bs] with [ty_bytes ty x bs] ([bytes_own_nocell],
[bytes_own_to_bytes]); the fancy bytes of any value can be turned into plain bytes by
dropping its cells ([bytes_own_forget], which needs the registry of the cells). The fancy
bytes split along the layout of pairs ([bytes_own_pair]).

The pointee is read and written with the typed [Load] and [Store] of [ty_mty ty]:
[wp_own_bytes_load], [wp_own_bytes_store], [wp_own_bytes_new] and
[wp_own_bytes_delete]. *)

Implicit Type 𝔄 𝔅: syn_type.

Section own_bytes.
  Context `{!typeG Σ}.

  (** ** The contents of tuples, for any layout *)

  (** The bytes of a tuple outside its fields (with any contents). *)
  Definition pad_own (l : loc) (fs : list (nat * mty)) (sz : nat) : iProp Σ :=
    ∃ bs : list abyte, ⌜length bs = sz⌝ ∗
      [∗ list] i ↦ b ∈ bs, if decide (in_field fs i) then emp else (l +ₗ i) ↦b [b].

  Global Instance pad_own_timeless l fs sz : Timeless (pad_own l fs sz).
  Proof. apply bi.exist_timeless=> bs. apply _. Qed.

  (** The padding only depends on the offsets and sizes of the fields. *)
  Lemma pad_own_sizes l offs ms ms' sz :
    mty_size <$> ms = mty_size <$> ms' → pad_own l (zip offs ms) sz = pad_own l (zip offs ms') sz.
  Proof.
    intros Hs. have Hin : ∀ i, in_field (zip offs ms) i ↔ in_field (zip offs ms') i.
    { intros i. rewrite /in_field. revert ms ms' Hs.
      induction offs as [|o offs IH]; intros [|m ms] [|m' ms'] Hs; simplify_eq/=;
        try (split; intros (? & Hf & _); by apply elem_of_nil in Hf).
      split; intros (f & [->|Hf]%elem_of_cons & Hi); simpl in *.
      - exists (o, m'). split; [by left|]. simpl. by rewrite -H.
      - destruct (proj1 (IH ms ms' H0) (ex_intro _ f (conj Hf Hi))) as (f' & ? & ?).
        exists f'. split; [by right|done].
      - exists (o, m). split; [by left|]. simpl. by rewrite H.
      - destruct (proj2 (IH ms ms' H0) (ex_intro _ f (conj Hf Hi))) as (f' & ? & ?).
        exists f'. split; [by right|done]. }
    rewrite /pad_own. f_equal. fun_ext=> bs. f_equal. f_equal. fun_ext=> i. fun_ext=> b.
    destruct (decide (in_field (zip offs ms) i)), (decide (in_field (zip offs ms') i));
      naive_solver.
  Qed.

  Lemma pad_own_struct_bsize l L 𝔄l 𝔅l :
    syn_bsize <$> 𝔄l = syn_bsize <$> 𝔅l →
    pad_own l (struct_fields L 𝔄l) (struct_size L 𝔄l) =
      pad_own l (struct_fields L 𝔅l) (struct_size L 𝔅l).
  Proof.
    intros Hs. rewrite /struct_fields (struct_offs_bsize L 𝔄l 𝔅l) // (struct_size_bsize L 𝔄l 𝔅l) //.
    apply pad_own_sizes. by rewrite -!list_fmap_compose.
  Qed.

  (** Byte chunks at the fields [fs] and the padding make the bytes of the tuple. *)
  Lemma bytes_fields_pad l (fs: list (nat * mty)) (bss: list (list abyte)) sz :
    fields_disjoint fs → Forall (λ f, f.1 + mty_size f.2 ≤ sz)%nat fs →
    (∀ j f bs, fs !! j = Some f → bss !! j = Some bs → length bs = mty_size f.2) →
    ([∗ list] f; bs ∈ fs; bss, (l +ₗ Z.of_nat f.1) ↦b bs) ∗ pad_own l fs sz ⊢
    ∃ bs, l ↦b bs ∗ ⌜length bs = sz⌝.
  Proof.
    iIntros (Hdisj Hin Hlj) "[Fs (%bs0 & %Hl0 & Hp)]".
    set ins := zip_with (λ (f: nat * mty) (bs: list abyte), (f.1, bs)) fs bss.
    set bs := fill_fields ins bs0.
    have Hlbs : length bs = sz by rewrite length_fill_fields.
    have Hins : ∀ j f bsj, fs !! j = Some f → bss !! j = Some bsj → ins !! j = Some (f.1, bsj).
    { intros j f bsj Hf Hb. by rewrite /ins lookup_zip_with Hf /= Hb. }
    have Hslice : ∀ j f bsj, fs !! j = Some f → bss !! j = Some bsj →
      list_slice f.1 (mty_size f.2) bs = bsj.
    { intros j f bsj Hf Hb. rewrite -(Hlj j f bsj Hf Hb).
      apply (list_slice_fill_fields ins _ j); [by apply Hins| |].
      - intros j' o' e' Hj' (f' & bsj' & [= -> ->] & Hf' & Hb')%lookup_zip_with_Some.
        rewrite (Hlj j' f' bsj' Hf' Hb') (Hlj j f bsj Hf Hb).
        destruct f as [o fm], f' as [o2 fm2]; simpl in *.
        destruct (Hdisj j' j o2 fm2 o fm) as [?|?]; [done|done|done|lia|lia].
      - rewrite (Hlj j f bsj Hf Hb) Hl0. exact (Forall_lookup_1 _ _ _ _ Hin Hf). }
    have Hpadbs : ∀ i, ¬ in_field fs i → bs !! i = bs0 !! i.
    { intros i Hi. rewrite lookup_fill_fields_out //.
      intros j o e (f & bsj & [= -> ->] & Hf & Hb)%lookup_zip_with_Some.
      rewrite (Hlj j f bsj Hf Hb).
      destruct (decide (f.1 ≤ i < f.1 + mty_size f.2)%nat); [|lia].
      exfalso. apply Hi. exists f. split; [by eapply elem_of_list_lookup_2|done]. }
    iExists bs. iSplit; [|done].
    rewrite heap_mapsto_bytes_pos (big_sepL_fields _ bs fs) //; last first.
    { rewrite Hlbs. eapply Forall_impl; [exact Hin|]. simpl. lia. }
    iSplitL "Fs".
    - iApply (big_sepL2_to_sepL_l with "Fs"). intros j f bsj Hf Hb.
      rewrite (Hslice j f bsj Hf Hb) heap_mapsto_bytes_pos.
      apply big_sepL_mono=> ?? _. by rewrite shift_loc_assoc_nat.
    - iApply (big_sepL_same_length with "Hp"); [by rewrite Hlbs|].
      intros i b b' Hb Hb'. case_decide as Hi; [done|].
      rewrite Hpadbs // Hb' in Hb. by injection Hb as <-.
  Qed.

  (** Separate contents at offsets of [l] have a common registry. *)
  Lemma gconts_union l (ps : list ((nat * mty) * FValue)) :
    ([∗ list] p ∈ ps, gcont (l +ₗ Z.of_nat p.1.1) p.1.2 p.2) ⊢
    ∃ R (fbss : list (list (positive + abyte))), ⌜reg_wf R ∧ length fbss = length ps ∧
      ∀ k p fbs, ps !! k = Some p → fbss !! k = Some fbs → frepr R p.1.2 fbs p.2⌝ ∗
      ([∗ list] p; fbs ∈ ps; fbss, gfbytes (l +ₗ Z.of_nat p.1.1) fbs) ∗
      ([∗ list] p ∈ ps, gcells (l +ₗ Z.of_nat p.1.1) p.1.2 p.2).
  Proof.
    induction ps as [|p ps IH].
    - iIntros "_". iExists ∅, []. iSplit; [|by iSplit]. iPureIntro.
      split_and!; [by intros ???|done|]. intros ???. by rewrite lookup_nil.
    - rewrite big_sepL_cons. iIntros "[(%R1 & %fbs1 & F1 & [%H1 %HR1] & C1) Hs]".
      iDestruct (IH with "Hs") as (R2 fbss) "([%HR2 [%Hlen %Hreps]] & Fs & Cs)".
      iDestruct (gcells_disj_list R1 R2 with "C1 Cs") as %Hd; [done| |].
      { intros k p' Hk. destruct (lookup_lt_is_Some_2 fbss k) as [fbs' Hfbs'].
        { rewrite Hlen. by eapply lookup_lt_Some. }
        exists fbs'. by eapply Hreps. }
      destruct (frepr_union_l _ _ _ _ _ H1 HR1 HR2) as (R & H1' & HR & Htr).
      iExists R, (fbs1 :: fbss). rewrite big_sepL2_cons big_sepL_cons. iFrame.
      iPureIntro. split_and!; [done|simpl; lia|].
      intros [|k] p' fbs; simpl; intros Hk Hf; simplify_eq; [done|].
      apply Htr; [by eapply Hreps|]. intros g Hg. by eapply Hd.
  Qed.

  (** The contents of a tuple: those of its fields, at their offsets, and the bytes outside
      the fields. *)
  Lemma gcont_tuple l fs sz al fvs :
    mty_wf (MTuple fs sz al) → length fvs = length fs →
    gcont l (MTuple fs sz al) (FVTuple fvs) ⊣⊢
      ([∗ list] p ∈ zip fs fvs, gcont (l +ₗ Z.of_nat p.1.1) p.1.2 p.2) ∗ pad_own l fs sz.
  Proof.
    intros Hwf Hlen. destruct (mty_wf_tuple_inv _ _ _ Hwf) as (Hdisj & Hin & Hwfs).
    have Hlz : length (zip fs fvs) = length fs by rewrite length_zip_with; lia.
    have Hzip : ∀ j p, zip fs fvs !! j = Some p → fs !! j = Some p.1 ∧ fvs !! j = Some p.2.
    { intros j p (f & fvj & -> & ? & ?)%lookup_zip_with_Some. done. }
    rewrite /gcont. iSplit.
    - iIntros "(%R & %fbs & Hfb & [%Hrep %HR] & C)".
      apply frepr_tuple_iff in Hrep as (Hlfbs & _ & Hfs & Hpad).
      rewrite gcells_tuple_zip //.
      rewrite /gfbytes (big_sepL_fields _ fbs fs) //; last first.
      { eapply Forall_impl; [exact Hin|]. simpl. lia. }
      iDestruct "Hfb" as "[Hf Hp]". iSplitR "Hp".
      + rewrite -(big_sepL_zip_fst (λ _ f, [∗ list] j ↦ x ∈ list_slice f.1 (mty_size f.2) fbs,
          gfb (l +ₗ (f.1 + j)%nat) x)%I fs fvs); [|lia].
        iCombine "Hf C" as "H". rewrite -big_sepL_sep.
        iApply (big_sepL_impl with "H"). iIntros "!>" (k p Hk) "[F C]".
        destruct (Hzip _ _ Hk) as [Hf Hfv].
        iExists R, (list_slice p.1.1 (mty_size p.1.2) fbs). iSplitL "F".
        { iApply (big_sepL_impl with "F"). iIntros "!>" (j x _) "H". by rewrite shift_loc_assoc_nat. }
        iFrame "C". iPureIntro. split; [by apply (Hfs k p.1 p.2)|done].
      + iExists (fb_erase <$> fbs). rewrite length_fmap. iSplit; [done|].
        rewrite big_sepL_fmap. iApply (big_sepL_impl with "Hp"). iIntros "!>" (i fb Hi) "H".
        case_decide as Hc; [done|]. by destruct (Hpad i fb Hi Hc) as [b ->].
    - iIntros "[Hs (%bs & %Hlbs & Hp)]".
      iDestruct (gconts_union with "Hs") as (R fbss) "([%HR [%Hlf %Hreps]] & Fs & Cs)".
      rewrite Hlz in Hlf.
      set ins := zip_with (λ (p : (nat * mty) * FValue) fbs, (p.1.1, fbs)) (zip fs fvs) fbss.
      set fbs := fill_fields ins (inr <$> bs).
      have Hlfbs : length fbs = sz by rewrite length_fill_fields length_fmap.
      have Hins : ∀ j p fbsj, zip fs fvs !! j = Some p → fbss !! j = Some fbsj →
        ins !! j = Some (p.1.1, fbsj).
      { intros j p fbsj Hp Hf. by rewrite /ins lookup_zip_with Hp /= Hf. }
      have Hlj : ∀ j p fbsj, zip fs fvs !! j = Some p → fbss !! j = Some fbsj →
        length fbsj = mty_size p.1.2.
      { intros j p fbsj Hp Hf. eapply frepr_length; [done|]. by eapply Hreps. }
      have Hslice : ∀ j p fbsj, zip fs fvs !! j = Some p → fbss !! j = Some fbsj →
        list_slice p.1.1 (mty_size p.1.2) fbs = fbsj.
      { intros j p fbsj Hp Hf. rewrite -(Hlj j p fbsj Hp Hf).
        apply (list_slice_fill_fields ins _ j); [by apply Hins| |].
        - intros j' o' e' Hj' (p' & fbsj' & [= -> ->] & Hp' & Hf')%lookup_zip_with_Some.
          destruct (Hzip _ _ Hp) as [Hfj _]. destruct (Hzip _ _ Hp') as [Hfj' _].
          rewrite (Hlj j' p' fbsj' Hp' Hf') (Hlj j p fbsj Hp Hf).
          destruct p as [[o fm] fvj], p' as [[o2 fm2] fvj']; simpl in *.
          destruct (Hdisj j' j o2 fm2 o fm) as [?|?]; [done|done|done|lia|lia].
        - rewrite (Hlj j p fbsj Hp Hf) length_fmap Hlbs. destruct (Hzip _ _ Hp) as [Hfj _].
          exact (Forall_lookup_1 _ _ _ _ Hin Hfj). }
      have Hpadfbs : ∀ i, ¬ in_field fs i → fbs !! i = inr <$> bs !! i.
      { intros i Hi. rewrite lookup_fill_fields_out ?list_lookup_fmap //.
        intros j o e (p & fbsj & [= -> ->] & Hp & Hf)%lookup_zip_with_Some.
        destruct (Hzip _ _ Hp) as [Hfj _]. rewrite (Hlj j p fbsj Hp Hf).
        destruct (decide (p.1.1 ≤ i < p.1.1 + mty_size p.1.2)%nat); [|lia].
        exfalso. apply Hi. exists p.1. split; [by eapply elem_of_list_lookup_2|done]. }
      iExists R, fbs. iSplitL "Fs Hp"; [|iSplit].
      + rewrite /gfbytes (big_sepL_fields _ fbs fs) //; last first.
        { rewrite Hlfbs. eapply Forall_impl; [exact Hin|]. simpl. lia. }
        iSplitL "Fs".
        * rewrite -(big_sepL_zip_fst (λ _ f, [∗ list] j ↦ x ∈ list_slice f.1 (mty_size f.2) fbs,
            gfb (l +ₗ (f.1 + j)%nat) x)%I fs fvs); [|lia].
          iApply (big_sepL2_to_sepL_l with "Fs"). intros j p fbsj Hp Hf.
          rewrite (Hslice j p fbsj Hp Hf). apply big_sepL_mono=> ?? _. by rewrite shift_loc_assoc_nat.
        * iApply (big_sepL_same_length with "Hp"); [by rewrite Hlfbs|].
          intros i b fb Hb Hfb. case_decide as Hi; [done|].
          rewrite Hpadfbs // Hfb in Hb. by injection Hb as <-.
      + iPureIntro. split; [|done]. apply frepr_tuple_iff. split_and!; [done|lia| |].
        * intros k f fv Hf Hfv.
          have Hp : zip fs fvs !! k = Some (f, fv) by rewrite lookup_zip_with Hf /= Hfv.
          destruct (lookup_lt_is_Some_2 fbss k) as [fbsk Hfbsk].
          { rewrite Hlf. by eapply lookup_lt_Some. }
          rewrite (Hslice k _ fbsk Hp Hfbsk). by apply (Hreps k (f, fv)).
        * intros i fb Hi Hnf. rewrite Hpadfbs // in Hi.
          destruct (bs !! i); simplify_eq/=. by eexists.
      + by rewrite gcells_tuple_zip.
  Qed.

  (** The contents of a tuple laid out in sequence: those of its first field and those of
      the others (the cells of the two parts are distinct, so their local registries can be
      merged, [frepr_union]). *)
  Lemma gcont_seq_tuple_cons l m ms fv fvs :
    gcont l (seq_tuple (m :: ms)) (FVTuple (fv :: fvs)) ⊣⊢
    gcont l m fv ∗ gcont (l +ₗ mty_size m) (seq_tuple ms) (FVTuple fvs).
  Proof.
    rewrite /gcont. iSplit.
    - iIntros "(%R & %fbs & Hfb & [%Hrep %HR] & C)".
      iDestruct (gcells_seq_tuple_cons with "C") as "[C1 C2]".
      apply frepr_seq_tuple_cons in Hrep as (f1 & f2 & -> & Hl1 & H1 & H2).
      rewrite gfbytes_app Hl1. iDestruct "Hfb" as "[F1 F2]".
      iSplitL "F1 C1"; iExists R, _; by iFrame.
    - iIntros "[(%R1 & %f1 & F1 & [%H1 %HR1] & C1) (%R2 & %f2 & F2 & [%H2 %HR2] & C2)]".
      iDestruct (gcells_disj with "C1 C2") as %Hd; [done|done|].
      destruct (frepr_union _ _ _ _ _ _ _ _ H1 H2 HR1 HR2 Hd) as (R & H1' & H2' & HR).
      have Hl1 := frepr_length _ _ _ _ HR1 H1.
      iExists R, (f1 ++ f2). rewrite gfbytes_app Hl1. iFrame "F1 F2".
      iSplit; [|iApply gcells_seq_tuple_cons; iFrame]. iPureIntro. split; [|done].
      apply frepr_seq_tuple_cons. by exists f1, f2.
  Qed.

  Lemma gcont_seq_tuple_nil l : gcont l (seq_tuple []) (FVTuple []) ⊣⊢ True.
  Proof.
    iSplit; [by iIntros|]. iIntros "_". iExists ∅, []. rewrite gcells_seq_tuple_nil.
    iSplit; [by rewrite /gfbytes|]. iSplit; [|done]. iPureIntro. split.
    - by apply frepr_seq_tuple_nil.
    - by intros ???.
  Qed.

  (** The fancy bytes at [l] represent [x]: they are the contents ([gcont], [typing/gcont.v])
      of the fancy value of [x] at the MiniRust type of [ty]. It is sealed: unifying it with
      other predicates would unfold the contents and the representation. *)
  Definition bytes_own_def {𝔄} (ty: type 𝔄) (l: loc) (x: ~~𝔄) : iProp Σ :=
    ∃ fv, ⌜ty.(ty_fval) x = Some fv⌝ ∗ gcont l ty.(ty_mty) fv.
  Local Definition bytes_own_aux : seal (@bytes_own_def). Proof. by eexists. Qed.
  Definition bytes_own := bytes_own_aux.(unseal).
  Definition bytes_own_unseal : @bytes_own = @bytes_own_def := bytes_own_aux.(seal_eq).
  Global Arguments bytes_own {_} _ _ _.

  Global Instance bytes_own_timeless {𝔄} (ty: type 𝔄) l x : Timeless (bytes_own ty l x).
  Proof. rewrite bytes_own_unseal. apply _. Qed.

  (** The contents of a value. *)
  Lemma bytes_own_gcont {𝔄} (ty: type 𝔄) l x fv :
    ty.(ty_fval) x = Some fv → bytes_own ty l x ⊣⊢ gcont l ty.(ty_mty) fv.
  Proof.
    intros Hfv. rewrite bytes_own_unseal /bytes_own_def. iSplit.
    - iIntros "(%fv' & %Hfv' & C)". rewrite Hfv in Hfv'. by injection Hfv' as <-.
    - iIntros "C". iExists fv. by iFrame.
  Qed.

  Lemma bytes_own_fval {𝔄} (ty: type 𝔄) l x : bytes_own ty l x -∗ ⌜is_Some (ty.(ty_fval) x)⌝.
  Proof. rewrite bytes_own_unseal. iIntros "(%fv & %Hfv & _)". by iExists fv. Qed.

  (** The fancy bytes of the contents represent the value. *)
  Lemma bytes_own_fbytes {𝔄} (ty: type 𝔄) l x :
    bytes_own ty l x ⊣⊢ ∃ R fbs fv, gfbytes l fbs ∗
      ⌜ty_fbytes R ty x fbs ∧ reg_wf R ∧ ty.(ty_fval) x = Some fv⌝ ∗ gcells l ty.(ty_mty) fv.
  Proof.
    rewrite bytes_own_unseal /bytes_own_def. iSplit.
    - iIntros "(%fv & %Hfv & %R & %fbs & Hfb & [%Hrep %HR] & C)". iExists R, fbs, fv. iFrame.
      iPureIntro. split_and!; [|done|done]. split; [by erewrite frepr_length|eauto].
    - iIntros "(%R & %fbs & %fv & Hfb & ([_ (%fv' & %Hfv' & %Hrep)] & %HR & %Hfv) & C)".
      rewrite Hfv in Hfv'. injection Hfv' as <-. iExists fv. iSplit; [done|].
      iExists R, fbs. by iFrame.
  Qed.

  (** Types with the same fancy bytes and the same cells have the same byte ownership. *)
  Lemma bytes_own_iff {𝔄 𝔅} (ty: type 𝔄) (ty': type 𝔅) l x x' :
    (∀ R fbs, ty_fbytes R ty x fbs ↔ ty_fbytes R ty' x' fbs) →
    (∀ R fbs fv fv', ty_fbytes R ty x fbs → ty.(ty_fval) x = Some fv → ty'.(ty_fval) x' = Some fv' →
       mcells ty.(ty_mty) fv = mcells ty'.(ty_mty) fv') →
    bytes_own ty l x ⊣⊢ bytes_own ty' l x'.
  Proof.
    intros Hb Hc. rewrite !bytes_own_fbytes. iSplit.
    - iIntros "(%R & %fbs & %fv & Hfb & (%Hfb & %HR & %Hfv) & C)".
      have Hfb' := proj1 (Hb R fbs) Hfb. destruct Hfb' as [? (fv' & Hfv' & ?)].
      iExists R, fbs, fv'. iFrame "Hfb". iSplit; [iPureIntro; split_and!; [by apply Hb|done|done]|].
      by rewrite !gcells_mcells (Hc R fbs fv fv').
    - iIntros "(%R & %fbs & %fv' & Hfb & (%Hfb' & %HR & %Hfv') & C)".
      have Hfb := proj2 (Hb R fbs) Hfb'. have Hfb0 := Hfb. destruct Hfb0 as [? (fv & Hfv & ?)].
      iExists R, fbs, fv. iFrame "Hfb". iSplit; [iPureIntro; split_and!; [by apply Hb|done|done]|].
      by rewrite !gcells_mcells (Hc R fbs fv fv').
  Qed.

  Lemma bytes_own_same {𝔄} (ty ty': type 𝔄) l x : bytes_own ty l x ⊣⊢ bytes_own ty' l x.
  Proof.
    apply bytes_own_iff; [intros; apply ty_fbytes_same|].
    intros R fbs fv fv' _ Hfv Hfv'. rewrite (ty_fval_same ty ty') Hfv' in Hfv.
    injection Hfv as ->. by rewrite (ty_mty_same ty ty').
  Qed.

  Lemma ty_fval_val' {𝔄} (ty: type 𝔄) x v : ty.(ty_val) x = Some v → ty.(ty_fval) x = Some (fv_lift v).
  Proof. rewrite -ty_val_eq -ty_fval_eq. apply syn_fval_val. Qed.

  (** Plain bytes. *)
  Lemma bytes_own_of_bytes {𝔄} (ty: type 𝔄) l x bs :
    ty_bytes ty x bs → l ↦b bs -∗ bytes_own ty l x.
  Proof.
    iIntros ((v & Hv & Hd)) "Hbs". rewrite (bytes_own_gcont _ _ _ (fv_lift v)); [|by apply ty_fval_val'].
    by iApply gcont_of_bytes.
  Qed.

  (** The reduction lemmas: the fancy bytes of a value with a MiniRust value, or of a value
      of a type without cells, are plain bytes. *)
  Lemma bytes_own_to_bytes {𝔄} (ty: type 𝔄) l x v :
    ty.(ty_val) x = Some v → bytes_own ty l x -∗ ∃ bs, l ↦b bs ∗ ⌜ty_bytes ty x bs⌝.
  Proof.
    iIntros (Hv) "Bytes". rewrite (bytes_own_gcont _ _ _ (fv_lift v)); [|by apply ty_fval_val'].
    iDestruct (gcont_lift_bytes with "Bytes") as (bs) "[Hbs %Hd]". iExists bs. iFrame.
    iPureIntro. by exists v.
  Qed.

  Lemma bytes_own_nocell {𝔄} `{!NoCell 𝔄} (ty: type 𝔄) l x :
    bytes_own ty l x ⊣⊢ ∃ bs, l ↦b bs ∗ ⌜ty_bytes ty x bs⌝.
  Proof.
    iSplit.
    - iIntros "Bytes". iDestruct (bytes_own_fval with "Bytes") as %[fv Hfv].
      move: (Hfv). rewrite ty_fval_nocell // => /fmap_Some [v [Hv _]].
      by iApply (bytes_own_to_bytes with "Bytes").
    - iIntros "(%bs & Hbs & %Hbs)". by iApply bytes_own_of_bytes.
  Qed.

  (** The view of the bytes of a value with a MiniRust value, for the guarded reads
      ([wp_load_na_guarded_gen]): its plain bytes. *)
  Lemma bytes_own_view {𝔄} (ty: type 𝔄) l x v :
    ty.(ty_val) x = Some v →
    ⊢ □ (bytes_own ty l x -∗ ∃ bs, ⌜ty_bytes ty x bs⌝ ∗ l ↦b bs ∗ (l ↦b bs -∗ bytes_own ty l x)).
  Proof.
    iIntros (Hv) "!> Bytes". iDestruct (bytes_own_to_bytes with "Bytes") as (bs) "[Hbs %Hbs]";
      [done|].
    iExists bs. iFrame "Hbs". iSplit; [done|]. by iApply bytes_own_of_bytes.
  Qed.

  Lemma bytes_own_nocell_bytes {𝔄} `{!NoCell 𝔄} (ty: type 𝔄) l x :
    bytes_own ty l x -∗ ∃ bs, l ↦b bs ∗ ⌜ty_bytes ty x bs⌝.
  Proof. rewrite bytes_own_nocell. iIntros "$". Qed.

  Lemma bytes_own_view_nocell {𝔄} `{!NoCell 𝔄} (ty: type 𝔄) l x :
    ⊢ □ (bytes_own ty l x -∗ ∃ bs, ⌜ty_bytes ty x bs⌝ ∗ l ↦b bs ∗ (l ↦b bs -∗ bytes_own ty l x)).
  Proof.
    iIntros "!> Bytes". iDestruct (bytes_own_nocell_bytes with "Bytes") as (bs) "[Hbs %Hbs]".
    iExists bs. iFrame "Hbs". iSplit; [done|]. by iApply bytes_own_of_bytes.
  Qed.

  (** A value of a type without cells whose bytes are owned has a MiniRust value. *)
  Lemma bytes_own_val {𝔄} `{!NoCell 𝔄} (ty: type 𝔄) l x :
    bytes_own ty l x -∗ ⌜is_Some (ty.(ty_val) x)⌝.
  Proof.
    rewrite bytes_own_nocell. iIntros "(%bs & _ & %Hbs)". iPureIntro. by eapply ty_bytes_val.
  Qed.

  (** Dropping the cells of the bytes (e.g. to overwrite or deallocate them): they are
      moved out ([gcont_forget]), which needs the registry and a credit. *)
  Lemma bytes_own_forget {𝔄} (ty: type 𝔄) l x E :
    lazyE ∪ ↑gcellsN ⊆ E →
    gcells_ctx -∗ £ 1 -∗ bytes_own ty l x ={E}=∗ ∃ bs, l ↦b bs ∗ ⌜length bs = ty_bsize ty⌝.
  Proof.
    iIntros (?) "#GC Lc Bytes". rewrite bytes_own_unseal. iDestruct "Bytes" as (fv _) "C".
    iApply (gcont_forget with "GC Lc C"); [done|apply ty_mty_wf].
  Qed.

  Lemma wp_bytes_own_forget {𝔄} (ty: type 𝔄) l x E e Φ :
    lazyE ∪ ↑gcellsN ⊆ E →
    gcells_ctx -∗ £ 1 -∗ bytes_own ty l x -∗
    (∀ bs, l ↦b bs -∗ ⌜length bs = ty_bsize ty⌝ -∗ WP e @ E {{ Φ }}) -∗ WP e @ E {{ Φ }}.
  Proof.
    iIntros (?) "#GC Lc Bytes Hwp".
    iMod (bytes_own_forget with "GC Lc Bytes") as (bs) "[Hbs %Hlen]"; [done|].
    by iApply ("Hwp" with "Hbs").
  Qed.

  (** The bytes of the fields of a struct, at the offsets [offs]. *)
  Fixpoint fields_bytes_own {𝔄l} (l: loc) (offs: list nat) (tyl: typel 𝔄l) {struct tyl} :
      plist (~~) 𝔄l → iProp Σ :=
    match tyl in hlist _ 𝔄l return plist (~~) 𝔄l → iProp Σ with
    | +[] => λ _, True
    | ty +:: tyl' => λ xs,
        match offs with
        | [] => False
        | o :: offs' => bytes_own ty (l +ₗ o) (phd xs) ∗ fields_bytes_own l offs' tyl' (ptl xs)
        end
    end%I.

  Lemma fields_bytes_own_gcont {𝔄l} l offs (tyl: typel 𝔄l) (xs: plist (~~) 𝔄l) :
    length offs = length 𝔄l →
    fields_bytes_own l offs tyl xs ⊣⊢
      ∃ fvs, ⌜mapM id (plist_to_list (pmap (λ _ x, syn_fval x) xs)) = Some fvs⌝ ∗
        [∗ list] p ∈ zip (zip offs (syn_mty <$> 𝔄l)) fvs, gcont (l +ₗ Z.of_nat p.1.1) p.1.2 p.2.
  Proof.
    revert offs. induction tyl as [|𝔄 𝔄l ty tyl IH]; intros [|o offs] Hlen; simpl in *; try lia.
    - iSplit; [iIntros "_"; iExists []; by iSplit|by iIntros].
    - destruct xs as [x xs]. simpl. rewrite IH; [|lia]. iSplit.
      + iIntros "[B (%fvs & %Hfvs & Hs)]". rewrite bytes_own_unseal.
        iDestruct "B" as (fv Hfv) "C". rewrite -ty_fval_eq -ty_mty_eq in Hfv |- *.
        iExists (fv :: fvs). rewrite Hfv Hfvs /=. iSplit; [done|]. iFrame.
      + iIntros "(%fvs & %Hfvs & Hs)".
        destruct (syn_fval x) as [fv|] eqn:Hfv; [|done]. simpl in Hfvs.
        destruct (mapM id _) as [fvs'|] eqn:Hfvs'; [|done]. injection Hfvs as <-.
        rewrite big_sepL_cons. iDestruct "Hs" as "[C Hs]". iSplitL "C".
        * rewrite bytes_own_unseal. iExists fv. rewrite -ty_fval_eq -ty_mty_eq. by iFrame.
        * iExists fvs'. by iFrame.
  Qed.

  (** The bytes of a struct: those of its fields, at their offsets, and the bytes outside the
      fields. *)
  Lemma bytes_own_struct {𝔄l} L (ty: type (structₛ L 𝔄l)) (tyl: typel 𝔄l) l xs :
    bytes_own ty l xs ⊣⊢
      fields_bytes_own l (struct_offs L 𝔄l) tyl xs ∗
      pad_own l (struct_fields L 𝔄l) (struct_size L 𝔄l).
  Proof.
    rewrite fields_bytes_own_gcont; [|apply length_struct_offs].
    rewrite bytes_own_unseal /bytes_own_def -!ty_fval_eq -!ty_mty_eq syn_mty_struct.
    change (syn_fval (𝔄:=structₛ L 𝔄l) xs) with
      (FVTuple <$> mapM id (plist_to_list (pmap (λ _ x0, syn_fval x0) xs))).
    have Hwf := syn_mty_wf (structₛ L 𝔄l). rewrite syn_mty_struct in Hwf.
    have Hlf : length (struct_fields L 𝔄l) = length 𝔄l.
    { rewrite /struct_fields length_zip_with length_fmap length_struct_offs. lia. }
    iSplit.
    - iIntros "(%fv & %Hfv & C)". apply fmap_Some in Hfv as (fvs & Hfvs & ->).
      rewrite gcont_tuple //; last first.
      { rewrite Hlf. apply mapM_Some, Forall2_length in Hfvs. by rewrite -Hfvs length_plist_to_list. }
      iDestruct "C" as "[Cs $]". iExists fvs. by iFrame.
    - iIntros "[(%fvs & %Hfvs & Cs) Pad]". iExists (FVTuple fvs). rewrite Hfvs.
      iSplit; [done|]. rewrite gcont_tuple //; [by iFrame|].
      rewrite Hlf. apply mapM_Some, Forall2_length in Hfvs. by rewrite -Hfvs length_plist_to_list.
  Qed.

  (** The fancy bytes of a pair: those of its components, one after the other. *)
  Lemma bytes_own_pair {𝔄 𝔅} (ty: type (𝔄 * 𝔅)) (ty1: type 𝔄) (ty2: type 𝔅) l x1 x2 :
    bytes_own ty l (x1, x2) ⊣⊢ bytes_own ty1 l x1 ∗ bytes_own ty2 (l +ₗ ty_bsize ty1) x2.
  Proof.
    rewrite bytes_own_unseal /bytes_own_def -!ty_fval_eq -!ty_mty_eq /ty_bsize -ty_mty_eq.
    change (syn_mty (𝔄 * 𝔅)) with (seq_tuple [syn_mty 𝔄; syn_mty 𝔅]).
    change (syn_fval (𝔄:=𝔄 * 𝔅) (x1, x2)) with
      (fv₀ ← syn_fval x1; fv₁ ← syn_fval x2; Some (FVTuple [fv₀; fv₁])). iSplit.
    - iIntros "(%fv & %Hfv & C)".
      destruct (syn_fval x1) as [fv₀|]; [|done]. destruct (syn_fval x2) as [fv₁|]; [|done].
      simpl in Hfv. injection Hfv as <-.
      rewrite !gcont_seq_tuple_cons gcont_seq_tuple_nil right_id.
      iDestruct "C" as "[C1 C2]". iSplitL "C1"; iExists _; by iFrame.
    - iIntros "[(%fv₀ & %H₀ & C1) (%fv₁ & %H₁ & C2)]". rewrite H₀ H₁ /=.
      iExists _. iSplit; [done|].
      rewrite !gcont_seq_tuple_cons gcont_seq_tuple_nil right_id. iFrame.
  Qed.

  (** Zero-sized values: their fancy bytes are empty. *)
  Lemma bytes_own_zst_emp {𝔄} (ty: type 𝔄) l x :
    ty_bsize ty = 0 → is_Some (ty.(ty_val) x) → ⊢ bytes_own ty l x.
  Proof.
    intros Hz [v Hv]. iApply (bytes_own_of_bytes _ _ _ []).
    - exists v. split; [done|].
      have Hwf := ty_val_wf _ _ _ Hv.
      have Hdec := decode_encode_value _ _ (ty_mty_wf ty) Hwf.
      have Hlen := length_encode_value (ty.(ty_mty)) v.
      rewrite /ty_bsize in Hz. rewrite Hz in Hlen.
      apply nil_length_inv in Hlen. by rewrite Hlen in Hdec.
    - by rewrite heap_mapsto_bytes_eq /heap_mapsto_bytes_def /heap_mapsto_st_vec.
  Qed.

  Lemma bytes_own_zst_true {𝔄} (ty: type 𝔄) l x :
    ty_bsize ty = 0 → is_Some (ty.(ty_val) x) → bytes_own ty l x ⊣⊢ True.
  Proof.
    intros. iSplit; [by iIntros|]. iIntros "_". by iApply bytes_own_zst_emp.
  Qed.

  (** The fancy bytes of a zero-sized value with a MiniRust value do not depend on the
      location. *)
  Lemma bytes_own_zst_loc {𝔄} (ty: type 𝔄) l l' x :
    ty_bsize ty = 0 → is_Some (ty.(ty_val) x) → bytes_own ty l x ⊣⊢ bytes_own ty l' x.
  Proof. intros. by rewrite !bytes_own_zst_true. Qed.

  (** The sharing predicate is structural, as for [own_ptr]: a guard of the bytes and
      the sharing predicate of the contents, under one later. *)
  Program Definition own_bytes {𝔄} (n: nat) (ty: type 𝔄) : type (at_locₛ 𝔄) := {|
    ty_lfts := ty.(ty_lfts);
    ty_E := ty.(ty_E);
    ty_gho_own x d g tid := [S(d') := d]
      bytes_own ty x.1 x.2 ∗ freeable_sz n (ty_bsize ty) x.1 ∗
      ▷ ty.(ty_gho_own) x.2 d' g tid;
    ty_gho_res x d g tid := [S(d') := d]
      bytes_own ty x.1 x.2 ∗ freeable_sz n (ty_bsize ty) x.1 ∗
      ▷ ty.(ty_gho_res) x.2 d' g tid;
    ty_gho_pers x d g tid := [S(d') := d] ▷ ty.(ty_gho_pers) x.2 d' g tid;
    ty_mty := syn_mty _; ty_val := syn_val; ty_mty_eq := eq_refl; ty_val_eq _ := eq_refl;
    ty_fval := syn_fval; ty_fval_eq _ := eq_refl;
    ty_shr κ x d g tid :=
      ▷ [S(d') := d]
        (@[κ] &&{↑NllftG; g+1}&&> bytes_own ty x.1 x.2) ∗ ty.(ty_shr) κ x.2 d' g tid;
  |}%I.
  Next Obligation.
    move=> 𝔄 n ty [|d] g d' g' x tid ??; iIntros "H" => //=.
    iDestruct "H" as "(Hown & Hfree & Hgho)". destruct d'; first lia => /=.
    iDestruct (ty.(ty_gho_own_depth_mono) with "Hgho") as "[$ Hwand]" => //; first lia.
    iFrame. iIntros "($ & $ & Hgho)". by iApply "Hwand".
  Qed.
  Next Obligation.
    move=> 𝔄 n ty [|d] g d' g' x tid ??; iIntros "H" => //=.
    destruct d'; first lia => /=.
    iDestruct (ty.(ty_gho_pers_depth_mono) with "H") as "$" => //; first lia.
  Qed.
  Next Obligation.
    intros 𝔄 n ty x d g tid. iIntros "A". destruct d as [|d']; first by done.
    iDestruct "A" as "[_ [_ pers]]". iApply ty_gho_pers_impl. iFrame.
  Qed.
  Next Obligation.
    intros 𝔄 n ty κ κ' x m d g tid. iIntros "#Incl Shr".
    iNext. destruct d as [|d']; [done|]. iDestruct "Shr" as "[Pt Shr]". iSplit.
    - replace (g + m + 1) with (m + (g + 1)) by lia.
      iApply (guards_transitive_additive with "Incl Pt").
    - iApply (ty_shr_lft_mono with "Incl Shr").
  Qed.
  Next Obligation.
    intros 𝔄 n ty κ d g d' g' x tid ??. iIntros "Shr".
    iNext. destruct d as [|d0]; [done|]. destruct d' as [|d0']; [lia|].
    iDestruct "Shr" as "[Pt Shr]". iSplit.
    - leaf_goal laters to (g+1). { lia. } iFrame "Pt".
    - iApply (ty_shr_depth_mono with "Shr"); lia.
  Qed.
  Next Obligation.
    intros 𝔄 n ty E κ x d g tid G ??. iIntros "#LFT #Incl #Pers #Gκ G Bor".
    destruct d as [|d']; [done|]. simpl.
    iMod (llftl_sep_split with "LFT Bor") as "[Pt Bor]"; [solve_ndisj|].
    iMod (llftl_sep_split with "LFT Bor") as "[_ Bor]"; [solve_ndisj|].
    iMod (llftl_bor_guard with "LFT Pt") as "#Pt"; [solve_ndisj|].
    iMod (llftl_bor_later_step with "LFT Gκ G Bor") as "Upd"; [first [apply _ | solve_ndisj]..|].
    iModIntro. iModIntro. iNext. iMod "Upd" as "[G Bor]".
    iMod (ty_share with "LFT Incl Pers Gκ G Bor") as "Shr"; [done..|].
    iModIntro. iApply (step_fupdN_wand with "Shr"). iIntros ">[$ Shr] !> !>".
    iFrame "Shr". leaf_goal laters to 1. { lia. } iFrame "Pt".
  Qed.
  Next Obligation.
    intros 𝔄 n ty κ x n0 d g tid ξ R Hin.
    iIntros "#LFT #Incl #Pers #Shr".
    destruct d as [|d']; first by done. simpl.
    iApply (bi.laterN_le (S (d' * (g + 2)))). { lia. }
    iNext. iDestruct "Shr" as "[_ Shr]".
    iDestruct (ty_shr_guard_proph ty κ x.2 n0 d' g tid ξ R Hin with "LFT Incl Pers Shr")
      as "GP".
    iNext. iIntros "#Rκ".
    leaf_goal laters to (n0 + (d'+1)*(g+1)). { lia. } by iApply "GP".
  Qed.
  Next Obligation.
    intros 𝔄 n ty x [|d] g tid; [by iIntros|]. iIntros "($ & $ & A)".
    iNext. by iApply ty_gho_res_of_own.
  Qed.

  Global Instance own_bytes_ne {𝔄} n : NonExpansive (@own_bytes 𝔄 n).
  Proof.
    move=> m ty ty' Eqv. split=>/=; [apply Eqv|apply Eqv| | |].
    - move=> [l x] [|d] g tid //=. rewrite /ty_bsize (ty_mty_same ty ty') (bytes_own_same ty ty').
      do 3 f_equiv. apply Eqv.
    - move=> [l x] [|d] g tid //=. do 2 f_equiv. apply Eqv.
    - move=> κ [l x] d g tid. f_equiv. destruct d; [done|]. simpl.
      rewrite (bytes_own_same ty ty'). f_equiv. apply Eqv.
  Qed.

  Global Instance own_bytes_type_contractive 𝔄 n : TypeContractive (@own_bytes 𝔄 n).
  Proof.
    split; [by apply type_lft_morphism_id_like| | |].
    - move=>/= m ty ty' _ _ EqOwn _ _ [l x] [|d] g tid //=.
      rewrite /ty_bsize (ty_mty_same ty ty') (bytes_own_same ty ty').
      do 2 f_equiv. f_contractive. by apply EqOwn.
    - move=>/= m ty ty' _ _ _ EqPers _ [l x] [|d] g tid //=.
      f_contractive. by apply EqPers.
    - move=>/= m ty ty' _ _ _ _ EqShr κ [l x] d g tid.
      apply later_contractive. split=> m' Hm. destruct d as [|d']; [done|]. simpl.
      rewrite (bytes_own_same ty ty'). f_equiv. eapply dist_later_lt; [apply EqShr|lia].
  Qed.
End own_bytes.

Section own_bytes_rules.
  Context `{!typeG Σ}.

  Lemma own_bytes_gho_intro {𝔄} n (ty: type 𝔄) l x d g tid :
    bytes_own ty l x -∗ freeable_sz n (ty_bsize ty) l -∗ ▷ ty.(ty_gho_own) x d g tid -∗
    (own_bytes n ty).(ty_gho_own) (l, x) (S d) g tid.
  Proof. iIntros "$ $ $". Qed.

  (** Reading the pointee: a typed [Load] of [ty_mty ty] returns the value of [x]. *)
  Lemma wp_own_bytes_load {𝔄} n (ty: type 𝔄) l x v d g tid E :
    ty.(ty_val) x = Some v →
    {{{ (own_bytes n ty).(ty_gho_own) (l, x) d g tid }}}
      Load Na1Ord ty.(ty_mty) #l @ E
    {{{ RET MLitV v; (own_bytes n ty).(ty_gho_own) (l, x) d g tid }}}.
  Proof.
    iIntros (Hv Φ) "Own HΦ". destruct d as [|d]; [done|].
    iDestruct "Own" as "(Bytes & Free & Gho)".
    iDestruct (bytes_own_to_bytes with "Bytes") as (bs) "[Hbs %Hbs]"; [done|].
    iApply (wp_load_na with "Hbs"); [by eapply ty_bytes_decode|].
    iIntros "!> Hbs". iApply "HΦ". iFrame. by iApply bytes_own_of_bytes.
  Qed.

  (** Writing the pointee: a typed [Store] of the value of [y] replaces [x] by [y];
      the ownership of [x] is given back. *)
  Lemma wp_own_bytes_store {𝔄} `{!NoCell 𝔄} n (ty: type 𝔄) l x y v d g tid E :
    ↑naN ⊆ E → ty.(ty_val) y = Some v →
    {{{ (own_bytes n ty).(ty_gho_own) (l, x) (S d) g tid ∗ ▷ ty.(ty_gho_own) y d g tid }}}
      Store Na1Ord ty.(ty_mty) #l (MLit v) @ E
    {{{ RET #☠; (own_bytes n ty).(ty_gho_own) (l, y) (S d) g tid ∗
                ▷ ty.(ty_gho_own) x d g tid }}}.
  Proof.
    iIntros (? Hv Φ) "[Own Gho'] HΦ".
    iDestruct "Own" as "(Bytes & Free & Gho)".
    iDestruct (bytes_own_nocell_bytes with "Bytes") as (bs) "[Hbs %Hbs]".
    iApply (wp_store_na with "Hbs"); [done|by eapply ty_val_wf|by eapply ty_bytes_length|].
    iIntros "!> Hbs". iApply "HΦ". iFrame. iApply (bytes_own_of_bytes with "Hbs").
    by apply ty_bytes_encode.
  Qed.

  (** Allocating a box and initialising it with a typed [Store]. *)
  Lemma wp_own_bytes_new {𝔄} (ty: type 𝔄) x v d g tid E :
    ↑naN ⊆ E → ty.(ty_val) x = Some v → (0 < ty_bsize ty)%nat →
    {{{ ▷ ty.(ty_gho_own) x d g tid }}}
      let: "l" := Alloc #(ty_bsize ty) in Store Na1Ord ty.(ty_mty) "l" (MLit v) ;; "l" @ E
    {{{ l, RET #l; (own_bytes (ty_bsize ty) ty).(ty_gho_own) (l, x) (S d) g tid }}}.
  Proof.
    iIntros (? Hv Hsz Φ) "Gho HΦ".
    wp_apply (wp_alloc_bytes with "[//]"); [rewrite /ty_bsize in Hsz; lia|]. iIntros (l sz) "(%Hn & Free & Hbs)".
    have ? : sz = mty_size (ty_mty ty) by lia. subst sz. wp_let.
    wp_bind (Store _ _ _ _). iApply (wp_store_na with "Hbs"); [done|by eapply ty_val_wf| |].
    { by rewrite length_replicate. }
    iIntros "!> Hbs". wp_seq. iApply "HΦ". iFrame "Gho". iSplitL "Hbs".
    - iApply (bytes_own_of_bytes with "Hbs"). by apply ty_bytes_encode.
    - rewrite freeable_sz_full. by iLeft.
  Qed.

  (** Deallocating a box; the ownership of its contents is given back. *)
  Lemma wp_own_bytes_delete {𝔄} `{!NoCell 𝔄} (ty: type 𝔄) l x d g tid E :
    ↑naN ⊆ E → (0 < ty_bsize ty)%nat →
    {{{ (own_bytes (ty_bsize ty) ty).(ty_gho_own) (l, x) (S d) g tid }}}
      Free #(ty_bsize ty) #l @ E
    {{{ RET #☠; ▷ ty.(ty_gho_own) x d g tid }}}.
  Proof.
    iIntros (? Hsz Φ) "(Bytes & Free & Gho) HΦ".
    iDestruct (bytes_own_nocell_bytes with "Bytes") as (bs) "[Hbs %Hbs]".
    have Hlen := ty_bytes_length _ _ _ Hbs.
    rewrite freeable_sz_full. iDestruct "Free" as "[Free|%Hz]".
    - iApply (wp_free_bytes with "[$Hbs Free]"); [done|by rewrite Hlen|by rewrite Hlen|].
      iIntros "!> _". by iApply "HΦ".
    - lia.
  Qed.
  Global Instance own_bytes_send {𝔄} n (ty: type 𝔄) : Send ty → Send (own_bytes n ty).
  Proof. move=> Hsend tid tid' x [|d] g //=. by rewrite (Hsend tid tid'). Qed.

  Global Instance own_bytes_send_upd {𝔄} n (ty: type 𝔄) : SendUpd ty → SendUpd (own_bytes n ty).
  Proof. move=> [Hgho]. split.
       intros tid tid' x d g G H κs d0 Hineq TG TH.
         iIntros "LFT UNIQ TIME Hg H Gg G Hgho #⧖o".
         destruct d => //=.
         iDestruct "Hgho" as "(Hown&Hfree&Hgho)".
         iModIntro. iNext. iModIntro.
         iPoseProof (Hgho with "LFT UNIQ TIME Hg H Gg G Hgho ⧖o") as "X"; first lia.
         iApply (step_fupdN_wand with "X"). iIntros ">X".
         iDestruct "X" as (x' off) "[gho [#⧖off [%Habs [G H]]]]".
         iExists (x.1, x'), (off). iModIntro. iFrame "G H ⧖off gho Hfree".
         iSplitL "Hown".
         + iApply (bytes_own_iff with "Hown").
           * intros R fbs. rewrite /ty_fbytes -!ty_fval_eq. by rewrite (syn_abstract_fval_eq _ _ _ Habs).
           * intros R fbs fv fv' _. rewrite -!ty_fval_eq (syn_abstract_fval_eq _ _ _ Habs). congruence.
         + iPureIntro. simpl. rewrite Habs. trivial.
  Qed.

  Global Instance own_bytes_sync {𝔄} n (ty: type 𝔄) : Sync ty → Sync (own_bytes n ty).
  Proof.
    move=> HSync tid tid' x d g.
    have EqOwn: ∀ d0 g0, (own_bytes n ty).(ty_gho_own) x d0 g0 tid ⊣⊢
        (own_bytes n ty).(ty_gho_own) x d0 g0 tid'.
    { move=> [|d0] g0 //=. destruct (HSync tid tid' x.2 d0 g0) as [Hgho _].
      by rewrite Hgho. }
    split; [apply EqOwn|]. split.
    - destruct d => //=. destruct (HSync tid tid' x.2 d g) as [_ [-> _]]. done.
    - move=> κ /=. f_equiv.
      destruct d as [|d0] => //=. destruct (HSync tid tid' x.2 d0 g) as [_ [_ Hshr]].
      by rewrite Hshr.
  Qed.

  Lemma own_bytes_resolve {𝔄} E L n (ty: type 𝔄) Φ :
    resolve E L ty Φ → resolve E L (own_bytes n ty) (λ '(l, v), Φ v).
  Proof.
    iIntros (Rslv G F x d g tid ??) "LFT PROPH UNIQ TIME E L own //".
    iIntros "Hgho".
    destruct d => //=.
    iDestruct "Hgho" as "(Hown&Hfree&Hgho)".
    iModIntro.
    replace (g + 1 + d * (g + 1)) with (S (g + d * (g + 1))) by lia.
    simpl. iModIntro. iNext.
    iDestruct (Rslv G F (snd x) d g tid _ with "[$] [$] [$] [$] [$] [$] [$] Hgho") as "Hrslv".
      { trivial. }
    iMod "Hrslv". iModIntro.
    iDestruct (step_fupdN_nmono with "Hrslv") as "Hrslv"; last first.
     - iApply (step_fupdN_wand with "Hrslv []").
       iIntros "F". iMod "F" as "[Obs G]".
       iModIntro. iFrame "G".
       iApply (proph_obs_impl with "Obs").
       intros π Ha. destruct x. apply Ha.
     - lia.
  Qed.

  Global Instance own_bytes_res_own {𝔄} n (ty: type 𝔄) : ResOwn ty → ResOwn (own_bytes n ty).
  Proof. move=> ? x [|d] g tid //=. by rewrite res_own. Qed.

  Lemma own_bytes_resolve_keep {𝔄} E L n (ty: type 𝔄) Φ :
    resolve_keep E L ty Φ → resolve_keep E L (own_bytes n ty) (λ '(l, v), Φ v).
  Proof.
    iIntros (Rslv G F x d g tid ??) "LFT PROPH UNIQ TIME E L G Hgho".
    destruct d as [|d] => //=.
    iDestruct "Hgho" as "(Hown & Hfree & Hgho)".
    iModIntro.
    replace (g + 1 + d * (g + 1)) with (S (g + d * (g + 1))) by lia.
    simpl. iModIntro. iNext.
    iMod (Rslv G F (snd x) d g tid with "LFT PROPH UNIQ TIME E L G Hgho") as "Hrslv";
      [done..|].
    iModIntro.
    iDestruct (step_fupdN_nmono with "Hrslv") as "Hrslv"; last first.
    - iApply (step_fupdN_wand with "Hrslv"). iIntros ">(Obs & $ & Res) !>".
      iFrame "Hown Hfree Res". iApply (proph_obs_impl with "Obs").
      intros π Ha. destruct x. apply Ha.
    - lia.
  Qed.
End own_bytes_rules.

Global Hint Resolve own_bytes_resolve : lrust_typing.
