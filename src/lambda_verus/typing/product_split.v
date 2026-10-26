From iris.proofmode Require Import proofmode.
From lrust.typing Require Export type.
From lrust.typing Require Import type_context lft_contexts product own uniq_bor freeable_util programs programs_util.
From lrust.typing Require Import shr_bor mod_ty uninit uniq_util.
From guarding Require Import guard tactics.
From lrust.lifetime Require Import lifetime_full.
Set Default Proof Using "Type".

Implicit Type (𝔄 𝔅: syn_type) (𝔄l 𝔅l ℭl: syn_typel).

Section product_split.
  Context `{!typeG Σ}.
  
  (** * General Split/Merger for Plain Pointer Types *)
  
  Fixpoint spec_ptr_offsets {𝔄l} (al: plist (~~) 𝔄l) (tyl: typel 𝔄l) (l: loc) : plist ~~ (map at_locₛ 𝔄l) :=
    match tyl in hlist _ 𝔄l, al return plist ~~ (map at_locₛ 𝔄l) with
    | +[], -[] => -[]
    | ty +:: tyl', a -:: al' => (l, a) -:: spec_ptr_offsets al' tyl' (l +ₗ ty.(ty_size))
  end.

  Fixpoint hasty_ptr_offsets {𝔄l} (p: path) (ptr: ∀{𝔄}, type 𝔄 → type (at_locₛ 𝔄))
      (tyl: typel 𝔄l) (off: nat) : tctx (map at_locₛ 𝔄l) :=
    match tyl with
    | +[] => +[]
    | ty +:: tyl' =>
      p +ₗ #off ◁ ptr ty +:: hasty_ptr_offsets p (@ptr) tyl' (off + ty.(ty_size))
    end.

  Lemma hasty_ptr_offsets_equiv {𝔄l} ptr p (tyl: typel 𝔄l) (off off': nat) :
    tctx_equiv (hasty_ptr_offsets (p +ₗ #off) ptr tyl off')
      (hasty_ptr_offsets p ptr tyl (off + off')).
  Proof.
    apply get_tctx_equiv=> ? vπl. move: p off off'.
    induction tyl, vπl; [done|]=>/= p ??. f_equiv; [|by rewrite IHtyl Nat.add_assoc].
    apply tctx_elt_interp_hasty_path=>/=. case (eval_path p)=>//.
    (do 2 case=>//)=> ?. by rewrite shift_loc_assoc -Nat2Z.inj_add.
  Qed.

  Definition ptr_homo_sub (ptr: ∀{𝔄}, type 𝔄 → type (at_locₛ 𝔄)) : Prop :=
    ∀E L 𝔄 𝔅 (ty: type 𝔄) (ty': type 𝔅) f,
      subtype E L ty ty' f → subtype E L (ptr ty) (ptr ty') (at_loc_mapₛ f).

  Lemma tctx_split_ptr_xprod {𝔄l} (ptr: ∀{𝔄}, type 𝔄 → type (at_locₛ 𝔄)) (tyl: typel 𝔄l) E L :
    ptr_homo_sub (@ptr) →
    (∀p 𝔄 𝔅 (ty: type 𝔄) (ty': type 𝔅),
        tctx_incl E L +[p ◁ ptr (ty * ty')]
          +[p +ₗ #0 ◁ ptr ty; p +ₗ #ty.(ty_size) ◁ ptr ty']
          (λ post '-[(l, (a, b))], post -[(l, a); (l +ₗ ty.(ty_size), b)])) →
    ∀p, tctx_incl E L +[p ◁ ptr (Π! tyl)] (hasty_ptr_offsets p (@ptr) tyl 0)
                       (λ post '-[(l, al)], post (spec_ptr_offsets al tyl l)).
  Proof.
    move=> HSub Split. elim: tyl.
    { move=> ?. eapply tctx_incl_ext.
      - apply tctx_incl_resolve_head.
      - intros post [[l []] []] π.  done.
    }
    move=>/= X Xl f tyl IH p.
    eapply tctx_incl_ext.
    { eapply tctx_incl_trans. { eapply subtype_tctx_incl, HSub, mod_ty_out. }
      eapply tctx_incl_trans. { apply Split. } apply tctx_incl_tail.
      eapply tctx_incl_trans. { apply IH. } rewrite -{2}[ty_size _]Nat.add_0_r.
      eapply proj1, hasty_ptr_offsets_equiv. }
    by move=>/= ?[[?[??]][]].
  Qed.

  Lemma tctx_merge_ptr_xprod {𝔄l} (ptr: ∀{𝔄}, type 𝔄 → type (at_locₛ 𝔄)) (tyl: typel 𝔄l)
      E L `{∀𝔄 (ty: type 𝔄), JustLoc (ptr ty)} :
    ptr_homo_sub (@ptr) →
    (∀p 𝔄 𝔅 (ty: type 𝔄) (ty': type 𝔅),
        tctx_incl E L +[p +ₗ #0 ◁ ptr ty; p +ₗ #ty.(ty_size) ◁ ptr ty']
          +[p ◁ ptr (ty * ty')] (λ post '-[(l, a); (l2, b)], λ mask π, l2 = l +ₗ ty.(ty_size) → post -[(l, (a, b))] mask π)) →
    𝔄l ≠ [] →
    ∀p, tctx_incl E L (hasty_ptr_offsets p (@ptr) tyl 0) +[p ◁ ptr (Π! tyl)]
                      (λ post al mask π, ∀ l al', al = (spec_ptr_offsets al' tyl l) → post -[(l, al')] mask π).
  Proof.
    move=> HSub Merge. elim: tyl; [done|]=> ?? ty. case=>/=.
    { move=> _ _ ?. eapply tctx_incl_ext.
      { eapply tctx_incl_trans; [apply tctx_of_shift_loc_0|].
        eapply subtype_tctx_incl, HSub, subtype_trans, mod_ty_in.
        eapply subtype_trans; [apply prod_ty_right_id|].
        apply prod_subtype; solve_typing. }
        intros post [[l x][]] ?. simpl.
        split.
        + intros Ha. apply Ha. trivial.
        + intros Ha l0 al0. destruct al0 as [x0 []]. inversion 1. subst. trivial.
    }
    move=> ???? IH _ ?. eapply tctx_incl_ext.
    { eapply tctx_incl_trans; [|by eapply subtype_tctx_incl, HSub, mod_ty_in].
      eapply tctx_incl_trans; [|by apply Merge]. apply tctx_incl_tail.
      eapply tctx_incl_trans; [|by apply IH].
      apply (tctx_incl_app +[_] +[_]); [by apply tctx_to_shift_loc_0, _|].
      eapply proj2, hasty_ptr_offsets_equiv. }
      simpl. intros post [[l x] [[l1 x1] rest]] π. split.
       + intros Ha. simpl. unfold trans_app. simpl.
         intros l2 [a al] Hb Hadd. apply Ha. rewrite Hb. subst l2. trivial.
       + simpl. unfold trans_app. simpl. intros Ha l0 [x2 [x3 rest3]] Hb.
        inversion Hb. subst. apply (Ha (l0 +ₗ ty_size ty)); trivial.
  Qed.
  
  (** * General Split/Merger for Plain Pointer Types (cloc version) *)
   
  Fixpoint spec_ptr_cloc_offsets {𝔄l} (al: plist (~~) 𝔄l) (tyl: typel 𝔄l) (l: cloc) : plist ~~ (map at_clocₛ 𝔄l) :=
    match tyl in hlist _ 𝔄l, al return plist ~~ (map at_clocₛ 𝔄l) with
    | +[], -[] => -[]
    | ty +:: tyl', a -:: al' => (cloc_take l ty.(ty_size), a) -:: spec_ptr_cloc_offsets al' tyl' (cloc_skip l ty.(ty_size))
  end.

  Fixpoint hasty_ptr_cloc_offsets {𝔄l} (p: path) (ptr: ∀{𝔄}, type 𝔄 → type (at_clocₛ 𝔄))
      (tyl: typel 𝔄l) (off: nat) : tctx (map at_clocₛ 𝔄l) :=
    match tyl with
    | +[] => +[]
    | ty +:: tyl' =>
      p +ₗ #off ◁ ptr ty +:: hasty_ptr_cloc_offsets p (@ptr) tyl' (off + ty.(ty_size))
    end.

  Lemma hasty_ptr_cloc_offsets_equiv {𝔄l} ptr p (tyl: typel 𝔄l) (off off': nat) :
    tctx_equiv (hasty_ptr_cloc_offsets (p +ₗ #off) ptr tyl off')
      (hasty_ptr_cloc_offsets p ptr tyl (off + off')).
  Proof.
    apply get_tctx_equiv=> ? vπl. move: p off off'.
    induction tyl, vπl; [done|]=>/= p ??. f_equiv; [|by rewrite IHtyl Nat.add_assoc].
    apply tctx_elt_interp_hasty_path=>/=. case (eval_path p)=>//.
    (do 2 case=>//)=> ?. by rewrite shift_loc_assoc -Nat2Z.inj_add.
  Qed.

  Definition ptr_cloc_homo_sub (ptr: ∀{𝔄}, type 𝔄 → type (at_clocₛ 𝔄)) : Prop :=
    ∀E L 𝔄 𝔅 (ty: type 𝔄) (ty': type 𝔅) f,
      subtype E L ty ty' f → subtype E L (ptr ty) (ptr ty') (at_cloc_mapₛ f).

  Lemma tctx_split_ptr_cloc_xprod {𝔄l} (ptr: ∀{𝔄}, type 𝔄 → type (at_clocₛ 𝔄)) (tyl: typel 𝔄l) E L :
    ptr_cloc_homo_sub (@ptr) →
    (∀p 𝔄 𝔅 (ty: type 𝔄) (ty': type 𝔅),
        tctx_incl E L +[p ◁ ptr (ty * ty')]
          +[p +ₗ #0 ◁ ptr ty; p +ₗ #ty.(ty_size) ◁ ptr ty']
          (λ post '-[(l, (a, b))], post -[(cloc_take l ty.(ty_size), a); (cloc_skip l ty.(ty_size), b)])) →
    ∀p, tctx_incl E L +[p ◁ ptr (Π! tyl)] (hasty_ptr_cloc_offsets p (@ptr) tyl 0)
                       (λ post '-[(l, al)], post (spec_ptr_cloc_offsets al tyl l)).
  Proof.
    move=> HSub Split. elim: tyl.
    { move=> ?. eapply tctx_incl_ext.
      - apply tctx_incl_resolve_head.
      - intros post [[l []] []] π.  done.
    }
    move=>/= X Xl f tyl IH p.
    eapply tctx_incl_ext.
    { eapply tctx_incl_trans. { eapply subtype_tctx_incl, HSub, mod_ty_out. }
      eapply tctx_incl_trans. { apply Split. } apply tctx_incl_tail.
      eapply tctx_incl_trans. { apply IH. } rewrite -{2}[ty_size _]Nat.add_0_r.
      eapply proj1, hasty_ptr_cloc_offsets_equiv. }
    by move=>/= ?[[?[??]][]].
  Qed.
End product_split.

Global Hint Unfold ptr_homo_sub : lrust_typing.
Global Hint Unfold ptr_cloc_homo_sub : lrust_typing.
Notation hasty_own_offsets p n :=
  (hasty_ptr_offsets p (λ 𝔄, own_ptr (𝔄:=𝔄) n)).
Notation hasty_shr_offsets p κ :=
  (hasty_ptr_cloc_offsets p (λ 𝔄, shr_bor (𝔄:=𝔄) κ)).

Section product_split.
  Context `{!typeG Σ}.

  (** * Owning Pointers *)

  Lemma tctx_split_own_prod {𝔄 𝔅} n (ty: type 𝔄) (ty': type 𝔅) p E L :
    tctx_incl E L +[p ◁ own_ptr n (ty * ty')]
      +[p +ₗ #0 ◁ own_ptr n ty; p +ₗ #ty.(ty_size) ◁ own_ptr n ty']
      (λ post '-[(l, (a, b))], post -[(l, a); (l +ₗ ty.(ty_size), b)]).
  Proof.
    split. { intros ?? H [[?[??]][]] ??. rewrite H. done. }
    iIntros (G tid [[l [x y]][]] post mask ?) "#LFT #PROPH #UNIQ #E #GuardsL G [T _] #Obs".
    iDestruct "T" as (v d) "(%path & #⧖ & [gho %phys])".
    destruct d as [|d']; first by done.
    iDestruct "gho" as "[↦ [free [gho1 gho2]]]".
    rewrite heap_mapsto_fancy_vec_app -freeable_sz_split.
    iDestruct "↦" as "[↦ ↦']". iDestruct "free" as "[free free']".
    iModIntro. iExists -[(l, x); (l +ₗ ty.(ty_size), y)]. iFrame "G".
    inversion phys. subst v.
    iSplit. { 
      iSplitL "↦ free gho1". { iExists #l, (S d'). iFrame.
        iSplit. { iPureIntro. simpl. rewrite path. rewrite shift_loc_0. trivial. }
        iFrame "⧖". iPureIntro. trivial. }
      iSplitL "↦' free' gho2". { iExists #(l +ₗ ty_size ty), (S d'). iFrame.
        iSplit. { iPureIntro. simpl. rewrite path. trivial. }
        iFrame "⧖". simpl. rewrite ty_size_eq. iFrame "↦'". iPureIntro. trivial. }
      done.
    }
    iApply proph_obs_eq; [|done]=>/= π. trivial.
  Qed.

  Lemma tctx_merge_own_prod {𝔄 𝔅} n (ty: type 𝔄) (ty': type 𝔅) p E L :
    tctx_incl E L +[p +ₗ #0 ◁ own_ptr n ty; p +ₗ #ty.(ty_size) ◁ own_ptr n ty']
      +[p ◁ own_ptr n (ty * ty')] (λ post '-[(la, a); (lb, b)], λ mask π, lb = la +ₗ ty.(ty_size) → post -[(la, (a, b))] mask π).
  Proof.
    eapply tctx_incl_ext;
      [eapply tctx_incl_trans; [apply tctx_of_shift_loc_0|]
      |by intros; apply (iff_refl _)].
    split. { intros ?? H [[??][[??][]]] ??. setoid_rewrite H. trivial. }
    iIntros (G tid [[lx x][[ly y][]]] post mask ?) "#LFT #PROPH #UNIQ #E #GuardsL G [T1 [T2 _]] #Obs".
    iDestruct "T1" as (v1 d1) "(%path1 & #⧖1 & [gho1 %phys1])".
    iDestruct "T2" as (v2 d2) "(%path2 & #⧖2 & [gho2 %phys2])".
    iCombine "⧖1 ⧖2" as "⧖".
    destruct d1 as [|d1']; first by done.
    destruct d2 as [|d2']; first by done.
    iDestruct "gho1" as "[↦ [free gho1]]".
    iDestruct "gho2" as "[↦' [free' gho2]]".
    iModIntro. iExists -[(lx, (x, y))]. iFrame "G".
    inversion phys1. inversion phys2. subst.
    simpl in path2. rewrite path1 in path2. inversion path2. subst ly.
    iSplit. {
      iSplit; last by done.
      iExists #lx, (S d1' `max` S d2'). iFrame "⧖". iSplit. { done. }
      iDestruct (ty_gho_own_depth_mono _ _ _ (d1' `max` d2') (S d1' `max` S d2') with "gho1") as "[gho1 _]". { lia. } { lia. }
      iDestruct (ty_gho_own_depth_mono _ _ _ (d1' `max` d2') (S d1' `max` S d2') with "gho2") as "[gho2 _]". { lia. } { lia. }
      iFrame.
      rewrite heap_mapsto_fancy_vec_app -freeable_sz_split. rewrite ty_size_eq. iFrame. 
      done.
    }
    iApply proph_obs_impl; [|done]=>/= π. intros Ha. apply Ha. trivial.
  Qed.

  Lemma tctx_split_own_xprod {𝔄l} n (tyl: typel 𝔄l) p E L :
    tctx_incl E L +[p ◁ own_ptr n (Π! tyl)]
      (hasty_own_offsets p n tyl 0) (λ post '-[(l, al)], post (spec_ptr_offsets al tyl l)).
  Proof.
    apply (tctx_split_ptr_xprod (λ _, own_ptr n));
    [solve_typing|move=> *; apply tctx_split_own_prod].
  Qed.

  Lemma tctx_merge_own_xprod {𝔄 𝔄l} n (tyl: typel (𝔄 :: 𝔄l)) p E L :
    tctx_incl E L (hasty_own_offsets p n tyl 0)
      +[p ◁ own_ptr n (Π! tyl)] (λ post al mask π, ∀ l al', al = (spec_ptr_offsets al' tyl l) → post -[(l, al')] mask π).
  Proof.
    apply (tctx_merge_ptr_xprod (λ _, own_ptr n));
    [apply _|solve_typing|move=> *; apply tctx_merge_own_prod|done].
  Qed.

  (** * Shared References *)

  Lemma tctx_split_shr_prod {𝔄 𝔅} κ (ty: type 𝔄) (ty': type 𝔅) p E L :
    tctx_incl E L +[p ◁ &shr{κ} (ty * ty')]
      +[p +ₗ #0 ◁ &shr{κ} ty; p +ₗ #ty.(ty_size) ◁ &shr{κ} ty']
      (λ post '-[(l, (a, b))], post -[(cloc_take l ty.(ty_size), a); (cloc_skip l ty.(ty_size), b)]).
  Proof.
    split. { intros ?? H [[?[??]][]] ??. setoid_rewrite H. trivial. }
    iIntros (G tid [[l [x y]][]] post mask ?) "#LFT #PROPH #UNIQ #E #GuardsL G [T _] #Obs".
    iDestruct "T" as (v d) "(%path & #⧖ & [gho %phys])".
    destruct d as [|d']; first by done.
    iDestruct "gho" as "[#G↦ [[#Shr1 #Shr2] [#InnerPers1 #InnerPers2]]]".
    rewrite heap_mapsto_cells_fancy_vec_app.
    iDestruct (guards_weaken_rhs_sep_l with "G↦") as "G↦1".
    iDestruct (guards_weaken_rhs_sep_r with "G↦") as "G↦2".
    iModIntro. iExists -[(cloc_take l ty.(ty_size), x); (cloc_skip l ty.(ty_size), y)]. iFrame "G".
    inversion phys. subst v.
    iSplit. {
      iSplitL. { iExists #(l.1), (S d'). rewrite ty_size_eq. iFrame "#".
        iSplit. { iPureIntro. simpl. rewrite path. rewrite shift_loc_0. trivial. }
        iPureIntro. trivial.
      }
      iSplitL. { iExists #(l.1 +ₗ ty_size ty), (S d'). iFrame "#".
        iSplit. { iPureIntro. simpl. rewrite path. trivial. }
        rewrite ty_size_eq. iFrame "#". simpl.
        iPureIntro. trivial.
      }
      done.
    }
    iApply proph_obs_eq; [|done]=>/= π. trivial.
  Qed.

  Lemma tctx_split_shr_xprod {𝔄l} κ (tyl: typel 𝔄l) p E L :
    tctx_incl E L +[p ◁ &shr{κ} (Π! tyl)]
      (hasty_shr_offsets p κ tyl 0) (λ post '-[(l, al)], post (spec_ptr_cloc_offsets al tyl l)).
  Proof.
    apply (tctx_split_ptr_cloc_xprod (λ _, &shr{κ}%T));
    [solve_typing|move=> *; apply tctx_split_shr_prod].
  Qed.

  (** * Unique References *)
  
  Lemma type_split_uniq_bor_instr {𝔄 𝔅} κ (ty: type 𝔄) (ty': type 𝔅) E L I p :
    lctx_lft_alive E L κ →
    typed_instr E L I
        +[p ◁ &uniq{κ} (ty * ty')]
        SplitBor
        (const +[p +ₗ #0 ◁ &uniq{κ} ty; p +ₗ #ty.(ty_size) ◁ &uniq{κ} ty'])
        (λ post '-[bor], λ mask π, ∀ bor1 bor2,
            uniq_bor_loc bor1 = cloc_take (uniq_bor_loc bor) ty.(ty_size) →
            uniq_bor_loc bor2 = cloc_skip (uniq_bor_loc bor) ty.(ty_size) →
            (uniq_bor_current bor1) = fst (uniq_bor_current bor) →
            (uniq_bor_future bor1 π) = fst (uniq_bor_future bor π) →
            (uniq_bor_current bor2) = snd (uniq_bor_current bor) →
            (uniq_bor_future bor2 π) = snd (uniq_bor_future bor π) →
            post -[bor1; bor2] mask π).
  Proof.
    intros Alv Out.
    apply typed_instr_of_skip.
    iIntros (x v d tid iκs mask post) "#LFT #TIME #PROPH #UNIQ E L $ %path Own Obs #⧖ ⧗ ⧗' £".
    iDestruct (Alv with "L E") as "#Alv".
    iMod (llctx_interp_make_guarded with "L") as (γ) "[H1 [H2 [#Ghalf #Halfback]]]". { solve_ndisj. }
    destruct x as [[[[[l x0] ξi] d'] g'] idx].
    iDestruct "Own" as "[[#Incl [%Ineqs [UniqBody #PtBase]]] %Phys]".
    iDestruct (guards_transitive with "Ghalf Alv") as "HalfGuardsK".
    iDestruct "UniqBody" as "(ξBor & £2)".
    iDestruct (lc_weaken 1 with "£") as "£f"; [rewrite /advance_credits; lia|].
    destruct x0 as [x0 y0].
    iMod (proph_loan_intro (uniq_cell_tyi x0) ⊤ (uniq_cell x0 d' g') with "PROPH UNIQ")
      as (ζi) "Loan1"; [solve_ndisj|].
    iMod (proph_loan_intro (uniq_cell_tyi y0) ⊤ (uniq_cell y0 d' g') with "PROPH UNIQ")
      as (ζ'i) "Loan2"; [solve_ndisj|].
    set ξ := uniq_prvar (𝔄:=(𝔄 * 𝔅)%ST) (x0, y0) ξi.
    set ζ := uniq_prvar x0 ζi. set ζ' := uniq_prvar y0 ζ'i.
    set f := λ (a: ~~ (uniq_cellₛ 𝔄)) (b: ~~ (uniq_cellₛ 𝔅)),
      uniq_cell (𝔄:=(𝔄 * 𝔅)%ST) (a.1, b.1)
        (dec_depth a.2.1 `max` dec_depth b.2.1) (dec_depth a.2.2 `max` dec_depth b.2.2).
    set fπ := λ (a: uniq_cellₛ 𝔄) (b: uniq_cellₛ 𝔅),
      (((a.1, b.1), (enc_depth (dec_depth a.2.1 `max` dec_depth b.2.1),
                     enc_depth (dec_depth a.2.2 `max` dec_depth b.2.2))) : uniq_cellₛ (𝔄 * 𝔅)).
    have Hcomm: ∀ a b π, vπ (f a b) π = fπ (vπ a π) (vπ b π).
    { intros [a [??]] [b [??]] π. done. }
    have Hrefl: ∀ a b ζl, (λ π, fπ (vπ a π) (vπ b π)) ./ ζl → vπ a ./ ζl ∧ vπ b ./ ζl.
    { intros [a [??]] [b [??]] ζl Dep. split; apply uniq_cell_dep_rev; simpl;
        intros π π' Heq; have := Dep π π' Heq; rewrite /fπ /=; by intros [=]. }
    iMod (proph_ibor_split ⊤ κ ξ (uniq_cell (𝔄:=(𝔄 * 𝔅)%ST) (x0, y0) d' g') idx
      (uniq_payload (ty * ty') tid l)
      ζ (uniq_cell x0 d' g') (uniq_payload ty tid (cloc_take l ty.(ty_size)))
      ζ' (uniq_cell y0 d' g') (uniq_payload ty' tid (cloc_skip l ty.(ty_size)))
      f fπ (fractional.half γ) ltac:(apply _) ltac:(solve_ndisj) Hcomm Hrefl
      with "LFT PROPH UNIQ HalfGuardsK [£f] H1 Loan1 Loan2 ξBor")
      as "(#Obs' & Bor & Bor' & H1)".
    { iIntros "Payload".
      iMod (uniq_payload_force with "£f Payload") as "(#⧖1 & Gho1 & Pt1)";
        [rewrite /lazyE; solve_ndisj|].
      iDestruct (heap_cloc_mapsto_fancy_vec_length_eq with "Pt1") as "%LenEq".
      rewrite heap_cloc_mapsto_fancy_vec_app. rewrite ty_size_eq.
      iDestruct "Pt1" as "[Pt1 Pt2]".
      iDestruct "Gho1" as "[Gho1 Gho2]".
      iModIntro. iSplitL "Gho1 Pt1".
      { iApply uniq_payload_intro_later. iNext. iFrame "∗#". }
      iSplitL "Gho2 Pt2".
      { iApply uniq_payload_intro_later. iNext. iFrame "∗#". }
      iIntros ([x1 [p1 p2]] [x2 [p3 p4]]) "Q1 Q2".
      rewrite /uniq_payload /f /=. rewrite !dec_enc_depth.
      iDestruct "Q1" as "(>#⧖2 & Lazy1)".
      iDestruct "Q2" as "(>#⧖3 & Lazy2)".
      iModIntro. iNext.
      iCombine "⧖2 ⧖3" as "⧖4".
      iSplit. { iApply (persistent_time_receipt_mono with "⧖4"). lia. }
      iMod "Lazy1" as "[Gho1 Pt1]". iMod "Lazy2" as "[Gho2 Pt2]". iModIntro.
      rewrite heap_cloc_mapsto_fancy_vec_app.
      rewrite ty_size_eq. iFrame.
      iDestruct (ty_gho_own_depth_mono with "Gho1") as "[Gho1 _]". 3: {
      iDestruct (ty_gho_own_depth_mono with "Gho2") as "[Gho2 _]". 3: {
        iFrame.
      } { lia. } { lia. } } { lia. } { lia. } }
    iCombine "Obs Obs'" as "#Obs".
    iDestruct ("Halfback" with "H1 H2") as "L".
    iMod (fupd_mask_mono with "L") as "$". { set_solver. }
    iDestruct "Bor" as (ζidx) "Bor".
    iDestruct "Bor'" as (ζ'idx) "Bor'".
    iModIntro.

    rewrite lft_intersect_list_app.

    rewrite (heap_cloc_mapsto_emp_vec_app l (ty_size ty)).
    iDestruct (guards_weaken_rhs_sep_l with "PtBase") as "#PtBase1".
    iDestruct (guards_weaken_rhs_sep_r with "PtBase") as "#PtBase2".

    iExists -[(cloc_take l ty.(ty_size), x0, ζi, d', g', ζidx); (cloc_skip l ty.(ty_size), y0, ζ'i, d', g', ζ'idx)].
    inversion Phys. subst v.
    iSplit. {
      iSplitL "Bor £2". {
         unfold tctx_elt_interp. iExists (#l.1), d.
         iSplit. { iPureIntro. simpl. rewrite path. rewrite shift_loc_0. trivial. }
         iSplit. { iApply (persistent_time_receipt_mono with "⧖"). lia. }
         iSplit; last by done.
         iSplit. { iApply (guards_transitive with "Incl []"). iApply llftl_intersect_incl_l. }
         iSplit. { iPureIntro. lia. }
         iSplitL "Bor £2". { rewrite /uniq_body. iFrame. }
         iFrame "PtBase1".
      }
      iSplitL. {
         unfold tctx_elt_interp. iExists (#(l.1 +ₗ ty_size ty)), d.
         iSplit. { iPureIntro. simpl. rewrite path. trivial. }
         iSplit. { iApply (persistent_time_receipt_mono with "⧖"). lia. }
         iSplit; last by done.
         iSplit. { iApply (guards_transitive with "Incl []"). iApply llftl_intersect_incl_r. }
         iSplit. { iPureIntro. lia. }
         iSplitL "Bor' ⧗". { rewrite /uniq_body. iFrame. }
         iFrame "PtBase2".
      }
      done.
    }
    iApply proph_obs_impl; [|done]=>/= π.
    intros [Ha Hb]. apply Ha; trivial.
    + unfold uniq_bor_future. simpl. rewrite Hb. trivial.
    + unfold uniq_bor_future. simpl. rewrite Hb. trivial.
  Qed.

  (* Unfortunately we can't use these nice automation utilities because of the 
     change that requires borrow-splitting to take a step *)

  (*Lemma tctx_split_uniq_prod {𝔄 𝔅} κ (ty: type 𝔄) (ty': type 𝔅) E L p :
    lctx_lft_alive E L κ →
    tctx_incl E L +[p ◁ &uniq{κ} (ty * ty')]
      +[p +ₗ #0 ◁ &uniq{κ} ty; p +ₗ #ty.(ty_size) ◁ &uniq{κ} ty']
      (λ post '-[((a, b), (a', b'))], post -[(a, a'); (b, b')]).
  *)

(* can't really do this since we need to do individual steps
  Fixpoint hasty_uniq_offsets {𝔄l} (p: path) (κ: lft)
      (tyl: typel 𝔄l) (off: nat) : tctx (map (λ 𝔄, 𝔄 * 𝔄)%ST 𝔄l) :=
    match tyl with
    | +[] => +[]
    | ty +:: tyl' =>
      p +ₗ #off ◁ &uniq{κ} ty +:: hasty_uniq_offsets p κ tyl' (off + ty.(ty_size))
    end.

  Lemma tctx_split_uniq_xprod {𝔄l} κ (tyl: typel 𝔄l) E L p :
    lctx_lft_alive E L κ →
    tctx_incl E L +[p ◁ &uniq{κ} (Π! tyl)] (hasty_uniq_offsets p κ tyl 0)
      (λ post '-[(al, al')], post (ptrans (pzip al al'))).
  Proof.
    move=> ?. move: p. elim: tyl.
    { move=>/= ?. by eapply tctx_incl_ext;
        [apply tctx_incl_resolve_head|]=>/= ?[[][]]_[]. }
    move=>/= 𝔄 𝔅l ty tyl IH p. eapply tctx_incl_ext.
    { eapply tctx_incl_trans.
      { eapply tctx_uniq_eqtype; first apply mod_ty_outin; solve_typing. }
      eapply tctx_incl_trans; [by apply tctx_split_uniq_prod|]. apply tctx_incl_tail.
      eapply tctx_incl_trans; [by apply IH|]. eapply proj1, get_tctx_equiv=> ? vπl.
      move: (ty_size _)=> off. rewrite -{2}(Nat.add_0_r off). move: off 0%nat. clear.
      induction tyl, vπl; [done|]=>/= ??. f_equiv; [|by rewrite IHtyl Nat.add_assoc].
      apply tctx_elt_interp_hasty_path=>/=. case (eval_path p)=>//.
      (do 2 case=>//)=> ?. by rewrite shift_loc_assoc Nat2Z.inj_add. }
    by move=>/= ?[[[??][??]][]].
  Qed.
  *)

  (** * Splitting with [tctx_extract_elt]. *)

  (* We do not state the extraction lemmas directly, because we want the
     automation system to be able to perform e.g., borrowing or splitting after
     splitting. *)
     
  (*

  Lemma tctx_extract_split_own_prod {𝔄 𝔅 ℭ 𝔇l 𝔈l} (t: tctx_elt 𝔄) n
      (ty: type 𝔅) (ty': type ℭ) (T: tctx 𝔇l) (T': tctx 𝔈l) tr p E L :
    tctx_extract_elt E L t
      +[p +ₗ #0 ◁ own_ptr n ty; p +ₗ #ty.(ty_size) ◁ own_ptr n ty'] T' tr →
    tctx_extract_elt E L t (p ◁ own_ptr n (ty * ty') +:: T) (T' h++ T)
      (λ post '((b, c) -:: dl), tr (λ '(a -:: el), post (a -:: el -++ dl)) -[b; c]).
  Proof.
    move=> Extr. eapply tctx_incl_ext.
    { eapply (tctx_incl_frame_r +[_] (_ +:: _)).
      eapply tctx_incl_trans; [apply tctx_split_own_prod|done]. }
    destruct Extr as [Htr _]=>/= ?[[??]?].  by apply Htr=>- [??].
  Qed.

  Lemma tctx_extract_split_own_xprod {𝔄 𝔄l 𝔅l ℭl} (t: tctx_elt 𝔄) n
      (tyl: typel 𝔄l) (T: tctx 𝔅l) (T': tctx ℭl) tr p E L :
    tctx_extract_elt E L t (hasty_own_offsets p n tyl 0) T' tr →
    tctx_extract_elt E L t (p ◁ own_ptr n (Π! tyl) +:: T) (T' h++ T)
      (λ post '(al -:: bl), tr (λ '(a -:: cl), post (a -:: cl -++ bl)) al).
  Proof.
    move=> Extr. eapply tctx_incl_ext.
    { eapply (tctx_incl_frame_r +[_] (_ +:: _)).
      eapply tctx_incl_trans; by [apply tctx_split_own_xprod|]. }
    destruct Extr as [Htr _]=>/= ?[??]. by apply Htr=>- [??].
  Qed.

  Lemma tctx_extract_split_shr_prod {𝔄 𝔅 ℭ 𝔇l 𝔈l} (t: tctx_elt 𝔄) κ
      (ty: type 𝔅) (ty': type ℭ) (T: tctx 𝔇l) (T': tctx 𝔈l) tr p E L :
    tctx_extract_elt E L t
      +[p +ₗ #0 ◁ &shr{κ} ty; p +ₗ #ty.(ty_size) ◁ &shr{κ} ty'] T' tr →
    tctx_extract_elt E L t (p ◁ &shr{κ} (ty * ty') +:: T)
      (p ◁ &shr{κ} (ty * ty') +:: T' h++ T) (λ post '((b, c) -:: dl),
        tr (λ '(a -:: el), post (a -:: (b, c) -:: el -++ dl)) -[b; c]).
  Proof.
    move=> ?. eapply tctx_incl_ext.
    { eapply (tctx_incl_frame_r +[_] (_+::_+::_)).
      eapply tctx_incl_trans; [apply copy_tctx_incl, _|].
      eapply tctx_incl_trans; [|apply tctx_incl_swap].
      apply (tctx_incl_frame_l _ _ +[_]).
      eapply tctx_incl_trans; [apply tctx_split_shr_prod|done]. }
    by move=>/= ?[[??]?].
  Qed.

  Lemma tctx_extract_split_shr_xprod {𝔄 𝔄l 𝔅l ℭl} (t: tctx_elt 𝔄) κ
      (tyl: typel 𝔄l) (T: tctx 𝔅l) (T': tctx ℭl) tr p E L :
    tctx_extract_elt E L t (hasty_shr_offsets p κ tyl 0) T' tr →
    tctx_extract_elt E L t (p ◁ &shr{κ} (Π! tyl) +:: T)
      (p ◁ &shr{κ} (Π! tyl) +:: T' h++ T) (λ post '(al -:: bl),
        tr (λ '(a -:: cl), post (a -:: al -:: cl -++ bl)) al).
  Proof.
    move=> ?. eapply tctx_incl_ext.
    { eapply (tctx_incl_frame_r +[_] (_+::_+::_)).
      eapply tctx_incl_trans; [apply copy_tctx_incl, _|].
      eapply tctx_incl_trans; [|apply tctx_incl_swap].
      apply (tctx_incl_frame_l _ _ +[_]).
      eapply tctx_incl_trans; by [apply tctx_split_shr_xprod|]. }
    by move=>/= ?[??].
  Qed.

  Lemma tctx_extract_split_uniq_prod {𝔄 𝔅 ℭ 𝔇l 𝔈l} (t: tctx_elt 𝔄) κ
      (ty: type 𝔅) (ty': type ℭ) (T: tctx 𝔇l) (T': tctx 𝔈l) tr p E L :
    lctx_lft_alive E L κ →
    tctx_extract_elt E L t
      +[p +ₗ #0 ◁ &uniq{κ} ty; p +ₗ #ty.(ty_size) ◁ &uniq{κ} ty'] T' tr →
    tctx_extract_elt E L t (p ◁ &uniq{κ} (ty * ty') +:: T) (T' h++ T)
      (λ post '(((b, c), (b', c')) -:: dl),
        tr (λ '(a -:: el), post (a -:: el -++ dl)) -[(b, b'); (c, c')]).
  Proof.
    move=> ? Extr. eapply tctx_incl_ext.
    { eapply (tctx_incl_frame_r +[_] (_ +:: _)).
      eapply tctx_incl_trans; [by apply tctx_split_uniq_prod|done]. }
    destruct Extr as [Htr _]=>/= ?[[[??][??]]?]. by apply Htr=>- [??].
  Qed.

  Lemma tctx_extract_split_uniq_xprod {𝔄 𝔄l 𝔅l ℭl} (t: tctx_elt 𝔄) κ
      (tyl: typel 𝔄l) (T: tctx 𝔅l) (T': tctx ℭl) tr p E L :
    lctx_lft_alive E L κ →
    tctx_extract_elt E L t (hasty_uniq_offsets p κ tyl 0) T' tr →
    tctx_extract_elt E L t (p ◁ &uniq{κ} (Π! tyl) +:: T) (T' h++ T)
      (λ post '((al, al') -:: bl),
        tr (λ '(a -:: cl), post (a -:: cl -++ bl)) (ptrans (pzip al al'))).
  Proof.
    move=> ? Extr. eapply tctx_incl_ext.
    { eapply (tctx_incl_frame_r +[_] (_ +:: _)).
      eapply tctx_incl_trans; by [apply tctx_split_uniq_xprod|]. }
    destruct Extr as [Htr _]=>/= ?[[??]?]. by apply Htr=>- [??].
  Qed.

  (** * Merging with [tctx_extract_elt]. *)

  Lemma tctx_extract_merge_own_prod {𝔄 𝔅 ℭl 𝔇l} n (ty: type 𝔄) (ty': type 𝔅)
      (T: tctx ℭl) (T': tctx 𝔇l) tr p E L :
    tctx_extract_ctx E L
      +[p +ₗ #0 ◁ own_ptr n ty; p +ₗ #ty.(ty_size) ◁ own_ptr n ty'] T T' tr →
    tctx_extract_elt E L (p ◁ own_ptr n (ty * ty')) T T'
      (λ post, tr (λ '(a -:: b -:: dl), post ((a, b) -:: dl))).
  Proof.
    move=> Extr. eapply tctx_incl_ext.
    { eapply tctx_incl_trans; [done|]=>/=.
      apply (tctx_incl_frame_r +[_; _] +[_]), tctx_merge_own_prod. }
    destruct Extr as [Htr _]=>/= ??. apply Htr. by case=> [?[??]].
  Qed.

  Lemma tctx_extract_merge_own_xprod {𝔄 𝔄l 𝔅l ℭl} n (tyl: typel (𝔄 :: 𝔄l))
      (T: tctx 𝔅l) (T': tctx ℭl) tr p E L :
    tctx_extract_ctx E L (hasty_own_offsets p n tyl 0) T T' tr →
    tctx_extract_elt E L (p ◁ own_ptr n (Π! tyl)) T T'
      (λ post, tr (λ acl, let '(al, cl) := psep acl in post (al -:: cl))).
  Proof.
    move=> ?. eapply tctx_incl_ext.
    { eapply tctx_incl_trans; [done|].
      apply (tctx_incl_frame_r _ +[_]), tctx_merge_own_xprod. }
    done.
  Qed.
  
  *)
End product_split.

(*

(* We do not want unification to try to unify the definition of these
   types with anything in order to try splitting or merging. *)
Global Hint Opaque tctx_extract_elt : lrust_typing_merge.

(* We make sure that splitting is tried before borrowing, so that not
   the entire product is borrowed when only a part is needed. *)
Global Hint Resolve tctx_extract_split_own_prod tctx_extract_split_own_xprod
  tctx_extract_split_uniq_prod tctx_extract_split_uniq_xprod | 5 : lrust_typing.
(* For shared references we set the cost high,
   because a shared reference to a whole product remains after split. *)
Global Hint Resolve tctx_extract_split_shr_prod tctx_extract_split_shr_xprod
  | 100 : lrust_typing.

(* Merging is also tried after everything, except
   [tctx_extract_elt_further]. Moreover, it is placed in a
   difference hint db. The reason is that it can make the proof search
   diverge if the type is an evar.

   Unfortunately, priorities are not taken into account accross hint
   databases with [typeclasses eauto], so this is useless, and some
   solve_typing get slow because of that. See:
     https://coq.inria.fr/bugs/show_bug.cgi?id=5304
*)
Global Hint Resolve tctx_extract_merge_own_prod tctx_extract_merge_own_xprod
  | 40 : lrust_typing_merge.

*)
