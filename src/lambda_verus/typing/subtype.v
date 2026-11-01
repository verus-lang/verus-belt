From iris.proofmode Require Import proofmode.
From lrust.lang Require Import proofmode.
From lrust.typing Require Export type.
From lrust.typing Require Import programs type_context lft_contexts uniq_util uniq_bor own shr_bor bytes_layout value_ctx uninit freeable_util.
From lrust.lifetime Require Import lifetime_full.
From guarding Require Import guard tactics.
Set Default Proof Using "Type".

(** * Allocation and subtyping on bytes (stage 4f of the MiniRust memory model)

  - [type_new_bytes_instr], [type_new_bytes]: [OfLit (Alloc #n)] gives a box of bytes of
    [n] uninitialized bytes, [v ◁ᵥ own_bytes n (↯ n)] (a pointer value); it is then
    initialized with a typed [Store] ([type_store_own_bytes_instr] of
    [typing/value_ctx.v], or the place rules).
  - Subtyping: [type_incl ty ty' f] ([typing/type.v]) relates the ownership and sharing
    and requires [f] to preserve the (fancy) byte representations ([syn_bincl]): the
    parents own bytes, so a box, a unique borrow or a shared reference can be retyped only
    if the bytes of its referent represent the value at the new type too. Rules:
    [own_bytes_subtype], [shr_bytes_subtype], [uniq_bytes_subtype], and
    [tctx_subtype_val] for MiniRust values (which needs the MiniRust values to agree, as
    for pointers). *)

Implicit Type 𝔄 𝔅: syn_type.

(** * Allocation *)

Section bnew.
  Context `{!typeG Σ}.

  Lemma uninit_bytes n (junk: ~~ (uninitₛ n)) bs :
    length bs = n → ty_bytes (↯ n) junk bs.
  Proof.
    intros Hlen. exists (VTuple []). split; [done|].
    rewrite -(ty_mty_eq (↯ _)) /= decide_True //.
  Qed.

  Lemma type_new_bytes_instr (n: nat) E L I :
    (0 < n)%nat →
    typed_instr E L I +[] (OfLit (Alloc #n)) (λ v, +[v ◁ᵥ own_bytes n (↯ n)])
      (λ post _ mask π, ∀ l junk, post -[(l, junk)] mask π).
  Proof.
    iIntros (Hn tid post mask iκs []) "_ #TIME _ _ _ $$ _ Obs".
    iMod persistent_time_receipt_0 as "⧖".
    iApply wp_fupd.
    iApply (wp_persistent_time_receipt with "TIME ⧖"); [solve_ndisj|].
    iIntros "_ #⧖1".
    wp_bind (Alloc _). iApply (wp_alloc_bytes with "[//]"); [lia|].
    iIntros "!>" (l sz) "(%Hsz & Fr & Hbs)". have ?: sz = n by lia. subst sz.
    wp_pure _. iModIntro.
    set junk := (() : ~~ (uninitₛ n)).
    iExists -[(l, junk)]. iSplitR "Obs".
    - iSplit; [|done]. rewrite tctx_val_val. iExists 1%nat. iSplit; [done|]. iFrame "⧖1".
      rewrite /= /by_succ. iSplitL "Hbs".
      + iApply (bytes_own_of_bytes with "Hbs"). apply uninit_bytes. by rewrite length_replicate.
      + iSplitL "Fr"; [|done].
        rewrite freeable_sz_full. by iLeft.
    - iApply (proph_obs_impl with "Obs")=> π Hπ. apply Hπ.
  Qed.

  Lemma type_new_bytes {𝔄l 𝔅} (n: nat) x e tr E L (I: invctx) (C: cctx 𝔅) (T: tctx 𝔄l) :
    Closed (x :b: []) e → (0 < n)%nat →
    (∀v: val, typed_body E L I C (v ◁ᵥ own_bytes n (↯ n) +:: T) (subst' x v e) tr) -∗
    typed_body E L I C T (let: x := OfLit (Alloc #n) in e)
      (λ post al mask π, forall l junk, tr post ((l, junk) -:: al) mask π).
  Proof.
    iIntros. iApply type_let.
    - by apply type_new_bytes_instr.
    - solve_typing.
    - instantiate (1 := tr). done.
    - done.
  Qed.
End bnew.

(** * Subtyping *)

Section subtype.
  Context `{!typeG Σ}.

  Lemma bytes_own_bincl {𝔄 𝔅} (ty: type 𝔄) (ty': type 𝔅) (f: 𝔄 →ₛ 𝔅) l x :
    syn_bincl f → bytes_own ty l x ⊣⊢ bytes_own ty' l (f ~~$ₛ x).
  Proof.
    intros [_ Hb]. apply bytes_own_iff. intros. rewrite !ty_fbytes_syn. apply Hb.
  Qed.

  (** ** Boxes of bytes *)

  Lemma own_bytes_type_incl {𝔄 𝔅} n (f: 𝔄 →ₛ 𝔅) ty ty' :
    type_incl ty ty' f -∗ type_incl (own_bytes n ty) (own_bytes n ty') (at_loc_mapₛ f).
  Proof.
    iIntros "(%Hb & #Incl & #InOwn & #InOwnPers & #InShr)".
    have Hsz : ty_bsize ty = ty_bsize ty' by rewrite !ty_bsize_eq; apply Hb.
    iSplit; [iPureIntro; apply syn_bincl_at_loc_map|].
    iSplit; [done|].
    iSplit.
    { iIntros "!>" ([l x0] [|d] g tid) "Hown //=".
      iDestruct "Hown" as "(Hown & Hfree & Hgho)".
      iPoseProof ("InOwn" with "Hgho") as "(Hgho & Hwand)".
      rewrite /ty_bsize in Hsz. rewrite (bytes_own_bincl ty ty' f) // Hsz. iFrame.
      iIntros "(Hown & Hfree & Hgho)". rewrite -(bytes_own_bincl ty ty' f) // -Hsz.
      iFrame. iNext. by iApply "Hwand". }
    iSplit.
    { iIntros "!>" ([l x0] [|d] g tid) "Hpers //=". by iApply "InOwnPers". }
    iIntros "!>" (κ [l x0] d g tid) "Shr".
    iNext. destruct d as [|d]; [done|]. simpl. iDestruct "Shr" as "[Pt Shr]".
    rewrite (bytes_own_bincl ty ty' f) //. iFrame "Pt". by iApply "InShr".
  Qed.

  Lemma own_bytes_subtype {𝔄 𝔅} E L n (f: 𝔄 →ₛ 𝔅) ty ty' :
    subtype E L ty ty' f → subtype E L (own_bytes n ty) (own_bytes n ty') (at_loc_mapₛ f).
  Proof.
    move=> Sub. iIntros "L". iDestruct (Sub with "L") as "#Incl".
    iIntros "!> #E". iApply own_bytes_type_incl. by iApply "Incl".
  Qed.

  (** ** Shared references to bytes *)

  Lemma shr_bytes_type_incl {𝔄 𝔅} κ κ' (f: 𝔄 →ₛ 𝔅) ty ty' :
    κ' ⊑ κ -∗ type_incl ty ty' f -∗ type_incl (&shr{κ} ty) (&shr{κ'} ty') (at_loc_mapₛ f).
  Proof.
    iIntros "#Incl (%Hb & #Incl2 & #Sub & #SubPers & #SubShr)".
    iApply (type_incl_simple_type _ _ _ (syn_bincl_at_loc_map f)).
    - unfold ty_lfts, ty_of_st, st_lfts. by iApply lft_intersect_mono.
    - iModIntro. iIntros (x d g tid) "A". destruct x as [l x].
      destruct d as [|d]; [done|].
      rewrite /= /by_succ. iDestruct "A" as "[#Hpt [#Hshr #Hpers]]".
      iSplit.
      { rewrite /shr_bytes_own -(bytes_own_bincl ty ty' f) //.
        iApply (guards_transitive_right with "Incl Hpt"). }
      iSplit.
      { iApply (ty_shr_lft_mono0 with "Incl"). iApply "SubShr". iFrame "Hshr". }
      iNext. iApply "SubPers". iFrame "Hpers".
  Qed.

  Lemma shr_bytes_subtype {𝔄 𝔅} E L κ κ' (f: 𝔄 →ₛ 𝔅) ty ty' :
    lctx_lft_incl E L κ' κ → subtype E L ty ty' f →
    subtype E L (&shr{κ} ty) (&shr{κ'} ty') (at_loc_mapₛ f).
  Proof.
    move=> In Sub. iIntros "L". iDestruct (In with "L") as "#In".
    iDestruct (Sub with "L") as "#Sub". iIntros "!> #E".
    iApply shr_bytes_type_incl; by [iApply "In"|iApply "Sub"].
  Qed.

  (** ** Unique borrows of bytes (invariant in the referent, as [uniq_subtype]) *)

  Lemma uniq_bytes_subtype {𝔄} E L κ κ' (ty ty': type 𝔄) :
    lctx_lft_incl E L κ' κ → eqtype E L ty ty' idₛ idₛ →
    subtype E L (&uniq{κ} ty) (&uniq{κ'} ty') idₛ.
  Proof.
    move=> In.
    intros Eqt. rewrite <-eqtype_id_unfold in Eqt. iIntros "L".
    iDestruct (Eqt with "L") as "#Eqt". iDestruct (In with "L") as "#In". iIntros "!> #E".
    iDestruct ("Eqt" with "E") as "[[Lfts1 Lfts2][#EqOwn [#EqPers #EqShr]]]".
    iSpecialize ("In" with "E").
    iSplit; [iPureIntro; apply syn_bincl_id|].
    iSplit; [by iApply lft_intersect_mono|].
    iSplit. {
      iModIntro. iIntros (x d g tid) "[#Incl gho]".
      destruct x as [[[[[l x0] ξi] d'] g'] idx].
      iDestruct "gho" as "[#Hineq UniqBody]".
      iDestruct (uniq_body_pers_component_impl with "UniqBody") as "#Saved".
      iDestruct (incl_uniq_body ty ty' x0 ξi d' g' with "In [] EqOwn UniqBody") as "UniqBody".
      { iFrame "Lfts1 Lfts2". }
      iDestruct (guards_transitive with "In Incl") as "Incl'".
      iDestruct (guards_transitive with "Incl' Lfts1") as "Incl''".
      iFrame "UniqBody Incl'' Hineq".
      iIntros "[Hincl'' [Hineq'' UniqBody]]".
      iDestruct "UniqBody" as (κp' γ') "(_ & Tok & ⧗ & _)".
      iDestruct "Saved" as (κps) "[Inc P]".
      iSplitR; [iFrame "Incl"|].
      iExists κps, γ'. iFrame "∗#".
    }
    iSplit. {
      iModIntro. iIntros (x d g tid) "#Pers".
      destruct x as [[[[[l x0] ξi] d'] g'] idx].
      iDestruct "Pers" as "[A C]".
      iSplitR; [iFrame "A"|].
      iApply (incl_uniq_body_pers_component with "In [] EqOwn C").
      iFrame "Lfts1 Lfts2".
    }
    iIntros "!>" (κ0 x d g tid) "Shr". destruct x as [[[[[l x0] ξi] d'] g'] idx]. simpl.
    iDestruct "Shr" as "($ & Pt & Tok & Shr & #Pers)".
    iAssert (κ0 ⊓ κ' ⊑ κ0 ⊓ κ)%I as "#Incl'".
    { iApply llftl_incl_glb; [iApply llftl_intersect_incl_l|].
      iApply llftl_incl_trans; [iApply llftl_intersect_incl_r|done]. }
    rewrite (cbytes_same ty ty').
    iSplit; [iApply (guards_transitive_right with "Incl' Pt")|].
    iSplit; [iApply (guards_transitive_right with "Incl' Tok")|].
    iSplitL; [iNext; iApply (ty_shr_lft_mono0 with "Incl'"); by iApply "EqShr"|].
    iNext. iNext. by iApply "EqPers".
  Qed.

  (** ** MiniRust values *)

  (** A value of [ty] is a value of [ty'], if the MiniRust values agree (e.g. pointers:
      boxes, references). *)
  Lemma tctx_subtype_val {𝔄 𝔅 𝔄l} `{!NoCell 𝔄} (ty: type 𝔄) (ty': type 𝔅) (f: 𝔄 →ₛ 𝔅) (T: tctx 𝔄l) p E L :
    subtype E L ty ty' f → (∀ x, ty'.(ty_val) (f ~~$ₛ x) = ty.(ty_val) x) →
    tctx_incl E L (p ◁ᵥ ty +:: T) (p ◁ᵥ ty' +:: T)
      (λ post '(a -:: al), post (f ~~$ₛ a -:: al)).
  Proof.
    intros Sub Hval. split; [by intros ??? [??]|].
    iIntros (??[x wπl]???) "#LFT _ _ E #L G /=[Tp T] Obs".
    iDestruct (tctx_val_elim with "Tp") as "(%v & %Hp & %w & %d & [-> %Hw] & ⧖ & Gho)".
    leaf_open "L" with "G" as "[L1 back]". { set_solver. }
    iDestruct (Sub with "L1 E") as "#(_ & _ & #InOwn & _)".
    iMod ("back" with "L1") as "G".
    iModIntro. iExists (f ~~$ₛ x -:: wπl). iFrame "G T".
    iSplitR "Obs".
    - rewrite -(tctx_val_intro_sep _ _ _ _ w d); [|done|by rewrite Hval]. iFrame "⧖".
      iDestruct ("InOwn" with "Gho") as "[$ _]".
    - iApply (proph_obs_impl with "Obs"). intros. done.
  Qed.

  Lemma tctx_subtype_own_bytes {𝔄 𝔅 𝔄l} n (ty: type 𝔄) (ty': type 𝔅) (f: 𝔄 →ₛ 𝔅)
      (T: tctx 𝔄l) p E L :
    subtype E L ty ty' f →
    tctx_incl E L (p ◁ᵥ own_bytes n ty +:: T) (p ◁ᵥ own_bytes n ty' +:: T)
      (λ post '(a -:: al), post (at_loc_mapₛ f ~~$ₛ a -:: al)).
  Proof.
    intros. apply tctx_subtype_val; [by apply own_bytes_subtype|]. by intros [??].
  Qed.

  Lemma tctx_subtype_shr_bytes {𝔄 𝔅 𝔄l} κ κ' (ty: type 𝔄) (ty': type 𝔅) (f: 𝔄 →ₛ 𝔅)
      (T: tctx 𝔄l) p E L :
    lctx_lft_incl E L κ' κ → subtype E L ty ty' f →
    tctx_incl E L (p ◁ᵥ &shr{κ} ty +:: T) (p ◁ᵥ &shr{κ'} ty' +:: T)
      (λ post '(a -:: al), post (at_loc_mapₛ f ~~$ₛ a -:: al)).
  Proof.
    intros. apply tctx_subtype_val; [by apply shr_bytes_subtype|]. by intros [??].
  Qed.

  Lemma tctx_subtype_uniq_bytes {𝔄 𝔄l} κ κ' (ty ty': type 𝔄) (T: tctx 𝔄l) p E L :
    lctx_lft_incl E L κ' κ → eqtype E L ty ty' idₛ idₛ →
    tctx_incl E L (p ◁ᵥ &uniq{κ} ty +:: T) (p ◁ᵥ &uniq{κ'} ty' +:: T)
      (λ post '(a -:: al), post (a -:: al)).
  Proof.
    intros. apply (tctx_subtype_val _ _ idₛ); [by apply uniq_bytes_subtype|].
    intros x. apply ty_val_same.
  Qed.
End subtype.
