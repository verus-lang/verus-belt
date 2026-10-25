From iris.proofmode Require Import proofmode.
From lrust.prophecy Require Import syn_type.
From lrust.lang Require Import spawn.
From lrust.typing Require Export type function product.
From lrust.typing Require Import uninit type_context programs freeable_util own.
From lrust.lifetime Require Import lifetime_full.
From guarding Require Import guard tactics.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

Definition spawnN := lrustN .@ "spawn".

Section spawn.
  Context `{!typeG Σ, !spawnG Σ}.

  Definition join_future {𝔄} (ty: type 𝔄) (Φ: pred' (~~𝔄)) v : iProp Σ :=
  (*   ∀tid, ∃ (x : ~~𝔄) mask d g, ⟨π, Φ x mask π⟩  ∗ ⧖d ∗ ty.(ty_gho_own) x d g tid. *)
    ∀tid, |={ ⊤ }=> ∃l x x' mask d g,
     ⌜ (box ty).(ty_phys) (l, x') tid = [FVal v] ⌝
    ∗ ⌜syn_abstract x = syn_abstract x'⌝
    ∗ ⟨π, Φ x mask π⟩
    ∗ ⧖d ∗ |={ ⊤ }=> (box ty).(ty_gho_own) (l, x') d g tid.

  (* Rust's thread::JoinHandle<T> *)
  Program Definition join_handle {𝔄 ℭ} (spec: (~~ℭ) → pred' (~~𝔄)) (ty: type 𝔄) : type (at_locₛ (join_handleₛ ℭ))%ST := 
    {| ty_size := 1;
      ty_lfts := ty.(ty_lfts);
      ty_E := ty.(ty_E);
      ty_gho_own (x : ~~ (at_locₛ ℭ)) d g tid :=
        join_handle spawnN x.1 (join_future ty (spec x.2));
      ty_gho_pers (x : ~~ (at_locₛ ℭ)) d g tid :=
        True;
      ty_phys (x : ~~ (at_locₛ ℭ)) tid := 
        [FVal (#x.1)];
      ty_shr := default_shr (λ (x : ~~ (at_locₛ ℭ)) d g tid, join_handle spawnN x.1 (join_future ty (spec x.2)));
  |}%I.
  Next Obligation. iIntros (????) => //=. Qed.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation. iIntros (????????????) "$". iIntros "$". Qed.
  Next Obligation. iIntros (????????????) "$". Qed.
  Next Obligation. iIntros (??????????) => /=. set_solver. Qed.
  Next Obligation. iIntros (𝔄 ty x ) "**". done. Qed.
  Solve All Obligations with solve_default_shr.

  Global Instance join_handle_ne {𝔄 ℭ} spec : NonExpansive (@join_handle 𝔄 ℭ spec).
  Proof. rewrite /join_handle /join_future. solve_ne_type. Qed.

  (*Global Instance join_handle_type_contractive {𝔄 ℭ} spec : TypeContractive (@join_handle 𝔄 ℭ spec).
  Proof.
    split; [by apply type_lft_morphism_id_like|done| |done]=>/= *.
    rewrite /join_future. do 20 f_equiv.
    by apply box_type_contractive.
  Qed.*)

  Global Instance join_handle_send {𝔄 ℭ} (spec: (~~ℭ) → pred' (~~𝔄)) (ty: type 𝔄) : Send (join_handle spec ty).
  Proof.
    intros. split; trivial.
     - intros. unfold syn_abstract in H. inversion H.
       unfold ty_phys, join_handle. by rewrite H1.
     - iIntros. iApply step_fupdN_intro; first done. iNext.
       iExists x, 0%nat. iModIntro. iFrame. simpl.
       replace (d0 + 0)%nat with d0 by lia. iFrame "#". done.
  Qed.
  
  Global Instance join_handle_sync {𝔄 ℭ} (spec: (~~ℭ) → pred' (~~𝔄)) (ty: type 𝔄) : Sync (join_handle spec ty).
  Proof. done. Qed.

  Lemma join_handle_resolve {𝔄 ℭ} (spec: (~~ℭ) → pred' (~~𝔄)) (ty: type 𝔄) E L :
    resolve E L (join_handle spec ty) (const (const True)).
  Proof. apply resolve_just. Qed.

  (* Definition forward_pred {A B} (f: A → B) (Φ: pred' A) (b: B) : Prop := *)
  (*   ∃a, b = f a ∧ Φ a. *)

  (* Lemma join_handle_subtype {𝔄 𝔅} (f: 𝔄 → 𝔅) ty ty' E L : *)
  (*   subtype E L ty ty' f → *)
  (*   subtype E L (join_handle ty) (join_handle ty') (forward_pred f). *)
  (* Proof. *)
  (*   iIntros (Sub ?) "L". iDestruct (Sub with "L") as "#Sub". iIntros "!> E". *)
  (*   iDestruct ("Sub" with "E") as "#Incl". iPoseProof "Incl" as "#(%&?&_)". *)
  (*   do 2 (iSplit; [done|]). iSplit; iModIntro; last first. *)
  (*   { iIntros "* (%&->)". iExists _. iPureIntro. by fun_ext=>/=. } *)
  (*   iIntros (?? tid' [|[[]|][]]) "join //". iDestruct "join" as (?->) "join". *)
  (*   iExists _. iSplit. { iPureIntro. by fun_ext=>/=. } *)
  (*   iApply (join_handle_impl with "[] join"). iIntros "!>% fut %tid". *)
  (*   iDestruct ("fut" $! tid) as (??) "(Obs & ⧖ & box)". iExists _, _. *)
  (*   iFrame "⧖". iSplitL "Obs". *)
  (*   { iApply proph_obs_impl; [|done]=>/= ??. by eexists _. } *)
  (*   iDestruct (box_type_incl with "Incl") as "(_&_& InO &_)". by iApply "InO". *)
  (* Qed. *)

  (* Lemma join_handle_eqtype {𝔄 𝔅} (f: 𝔄 → 𝔅) g ty ty' E L : *)
  (*   eqtype E L ty ty' f g → *)
  (*   eqtype E L (join_handle ty) (join_handle ty') (forward_pred f) (forward_pred g). *)
  (* Proof. move=> [??]. split; by apply join_handle_subtype. Qed. *)

  (* Rust's thread::spawn *)
  Definition spawn (call_once: val) : val :=
    fn: ["f"] :=
      let: "call_once" := call_once in
      let: "j" := spawn
        [λ: ["c"], letcall: "r" := "call_once" ["f"] in finish ["c"; "r"]] in
      letalloc: "r" <- "j" in
      return: ["r"].
      
  Arguments ty_gho_own {_ _ _} _ _ _ _ : simpl never.
  
  Lemma spawn_type {𝔄 𝔅 ℭ} (c: ~~ℭ) (Φ: (~~ℭ) → pred' (~~𝔅)) call_once_val call_once_tr (fty: type 𝔄) (retty: type 𝔅)
      call_once `{!Send fty, !Send retty} :
    typed_val call_once ((fn<()>(∅; fty) → retty) call_once_tr) (call_once_val, c) →
    let E ϝ := ty_outlives_E fty static ++ ty_outlives_E retty static in
    typed_val (spawn call_once) ((fn(E; fty) → join_handle Φ retty)
      (λ c, (λ post '-[(l, a)], λ Mask π, ∀ a', syn_abstract a = syn_abstract a' → call_once_tr c (λ '(_, b) Mask π, Φ c b Mask π) -[(l, a')] ⊤ π ∧ ∀ lo li, post (lo, (li, c)) Mask π)))
      (spawn call_once, c).
  Proof.
    fold indep_interp_of_syn_type.
    move=> Tcall_once E.
    unfold spawn.
    unlock.
    opose proof (@type_fn _ _ _ [𝔄] (at_locₛ (join_handleₛ ℭ)) ℭ c (λ y: (), FP E +[fty] (join_handle Φ retty) AtomicClosed) (λ c, (λ post '-[(l,a)], λ Mask π, ∀ a', syn_abstract a = syn_abstract a' → call_once_tr c (λ '(_, b) mask' π', Φ c b mask' π') -[(l, a')] ⊤ π ∧ ∀ lo li : loc, post (lo, (li, c)) Mask π)) (let: "call_once" := call_once in let: "j" := lib.spawn.spawn [λ: ["c"], letcall: "r" := "call_once" ["f"] in finish ["c"; "r"]] in let: "r" := new (#(LitInt 1) :: []) in "r" <- "j" ;; return: ["r"])%E [BNamed "f"] _ _ _ ).
    unlock in H.
    apply H.
    move => _.
    clear H.
    move => ϝ k wl.
    simpl_subst.
    unfold fp_E. simpl.
    unfold E.
    destruct wl as [x []].
    simpl_subst.

    iApply (@type_let _ _ [] [exec_funₛ ℭ] [at_locₛ 𝔄] [at_locₛ 𝔄] (at_locₛ (at_locₛ (join_handleₛ ℭ))) _ _ _ (λ post '((call_once_val, c) -:: -[(l,x)] ) mask π, ∀ x', syn_abstract x = syn_abstract x' → call_once_tr c (λ '(_, b) mask' π', Φ c b mask' π') -[(l,x')] ⊤ π ∧ ∀ lo li : loc, post (lo, (li, c)) mask π)).
    1: apply Tcall_once.
    1: apply tctx_extract_ctx_nil.
    1: done.
    intro_subst_as (call_once').
    fold indep_interp_of_syn_type in *.

    iApply (@type_let _ _ [(exec_funₛ ℭ) ; at_locₛ 𝔄] [at_locₛ (join_handleₛ ℭ)] [(exec_funₛ ℭ) ; at_locₛ 𝔄] [] (at_locₛ (at_locₛ (join_handleₛ ℭ))) _ (λ c, +[c ◁ join_handle Φ retty]) (λ post '((_, c) -:: -[(l,a)]) mask π, ∀ a', syn_abstract a = syn_abstract a' → call_once_tr c (λ '(_, b) mask' π', Φ c b mask' π') -[(l,a')] ⊤ π ∧ ∀ li, post -[(li, c)] mask π) (λ post '((li, predb) -:: _) mask π, ∀ lo, post (lo, (li, predb)) mask π) ).
    2: {
      eapply tctx_extract_ctx_elt.
      2: eapply tctx_extract_ctx_elt.
      3: apply tctx_extract_ctx_nil.
      1,2: apply tctx_extract_elt_here_exact. 
    }
    - iIntros (tid post mask iκs xl) "#LFT #TIME #PROPH #UNIQ #E L I T #Obs".
      clear Tcall_once call_once call_once_val.
      destruct xl as [[call_once_val c'] [[la a] []]].
      iDestruct "T" as "(T1 & T2 & _)".
      iSimpl in "T1".
      rewrite !tctx_hasty_val /ty_own.
      iDestruct "T1" as "(%d1 & #Hd1 & Hgho1 & %Hphys1)".
      iDestruct "T2" as "(%d2 & #Hd2 & Hgho2 & %Hphys2)".
      iCombine "Hd1 Hd2" as "Hd".
      
      iMod (invctx_alloc ⊤) as (tid') "I'".
      
      rewrite (proj1 (proj2 (@sync_change_tid _ _ _ _ (fn_sync _ _) tid tid' _ _ _ ))). 
      
      iApply fupd_wp.
      iMod (fupd_mask_subseteq (↑Nllft)) as "Hclose"; first solve_ndisj.
      
      iApply (wp_persistent_time_receipt with "TIME Hd"); [trivial|].
      iMod "Hclose". iClear "Hclose".
      iModIntro. iIntros "£ #Hsd".
      rewrite /advance_credits.
      iDestruct (lc_weaken (d1 `max` S d2 + d2) with "£") as "[£1 £2]"; first nia.
      
      (* send the arguments over *)
      pose proof (own_send fty.(ty_size) fty Send0) as Send3.
      destruct Send3 as [SendArgsPhys SendArgsGho].
      iDestruct "I" as (at_mask na_mask) "[I1 [[cna_lifetimes #fnincl] I2]]".
      iDestruct (SendArgsGho tid tid' (la, a) d2 d2 _ _ _ (S d2) with
          "LFT UNIQ TIME [] cna_lifetimes [] L Hgho2 []") as "X"; first lia.
        { iApply guards_refl. }
        { iIntros (κ) "%Hin". rewrite gmultiset_elem_of_disj_union in Hin.
          destruct Hin as [Hin|Hin]; first set_solver.
          rewrite elem_of_list_to_set_disj in Hin.
          iDestruct (lft_intersect_list_elem_of_incl iκs κ Hin) as "G1".
          iApply (guards_transitive with "[] G1").
          iApply (guards_transitive with "[] fnincl").
          unfold llctx_interp. rewrite big_sepL_singleton. unfold llctx_elt_interp.
          leaf_by_sep.
          iDestruct 1 as (κ0) "[%Ha [Hb %Hc]]". simpl in Ha.
          unfold "⊓", lifetime_full.llft_intersect, static, llft_empty in Ha.
          rewrite left_id in Ha. subst ϝ. iFrame.
          iIntros "A". iExists κ0. iFrame. iSplit; last by done.
          iPureIntro. simpl. 
          unfold "⊓", lifetime_full.llft_intersect, static, llft_empty.
          rewrite left_id. trivial.
        }
        { iApply (persistent_time_receipt_mono with "Hsd"); lia. }
      iApply fupd_wp.
      iDestruct (lc_step_fupdN_elim_later with "£2 X") as "X".
      iMod (fupd_mask_mono with "X") as "X". { apply union_least; solve_ndisj. }
      iMod (fupd_mask_mono with "X") as "X". { apply union_least; solve_ndisj. }
      iDestruct "X" as (x' off) "[Hgho2 [#⧖off [%Habs [L cna_lifetimes]]]]".
      
      iApply (spawn_spec _ _ (join_future retty (Φ c')) with "[- L I1 I2 cna_lifetimes]"); [solve_ndisj|..]; last first.
      { iModIntro.
        iIntros "!> %c0 join". iExists -[(c0, c')]. iFrame "L I1 I2 cna_lifetimes fnincl".
        iSplit; last first.
        { iApply (proph_obs_impl with "Obs"). move => π Hpost. 
          assert (syn_abstract a = syn_abstract a) as Heq by trivial.
          have H := Hpost a Heq. destruct H as [H1 H2]. apply H2.
        }
        simpl.
        iSplit => //.
        iExists _, _.
        iSplit => //.
        iFrame "Hsd" => /=.
        rewrite /ty_own.
        unfold ty_gho_own => /=.
        repeat iSplit => //. }

      iIntros (?) "fin".
      do 2 wp_let.

      iApply (type_call_iris (𝔄l:=[_]) () -[_] [] _ _ (λ '(), FP ∅ +[fty] retty AtomicClosed)  with "LFT TIME PROPH UNIQ E [] [] I' [Hgho1] [Hgho2]").
      3: by iApply guards_refl.
      1: apply _.
      + move => ϝ'.
        simpl.
        rewrite /fp_E /=.
        iIntros "_ !> E".
        rewrite !elctx_interp_app.
        iDestruct "E" as "((#H1 & #H2) & (#H3 & #H4) & (#H5 & #H6) & (#H7 & #H8))".
        iFrame "#".
        rewrite !elctx_interp_ty_outlives_E.
        iSplit.
        * iApply (guards_transitive _ _ @[static] ) => //.
          iApply lft_incl_static.
        * iApply (guards_transitive _ _ @[static] ) => //.
          iApply lft_incl_static.
      + simpl. by iApply static_alive_true.
      + rewrite/= !tctx_hasty_val.
        iExists _. iFrame "Hd". 
        iSplitL.
        * iDestruct (ty_gho_own_depth_mono with "Hgho1") as "[H _]"; last iFrame.
          all:lia.
        * iPureIntro. done.
      + rewrite/= !tctx_hasty_val. iSplit => //.
        iExists _. iFrame "⧖off". iSplitL.
        * iDestruct (ty_gho_own_depth_mono with "Hgho2") as "[H _]"; last iFrame.
          all:lia.
        * iPureIntro. rewrite (send_change_tid_phys tid' tid x' (la, a)); trivial.
      + iApply (proph_obs_impl with "Obs"). intros π Hpost. 
        destruct x' as [l' x'].
        unfold syn_abstract in Habs. simpl in Habs. inversion Habs. subst l'.
        destruct (Hpost x') as [Hpost1 Hpost2].
         * done.
         * apply Hpost1.
      + iClear "Obs Hd Hsd". iIntros (???) "_ I ret #Obs". wp_rec.
        rewrite tctx_hasty_val. iDestruct "ret" as (d) "[#Hd ret]".
        iApply (wp_persistent_time_receipt with "TIME Hd"); [trivial|].
        iIntros "£ #Hsd".
        
        iApply (finish_spec with "[$fin ret Obs £ I]"); [solve_ndisj..| | ].
        { iDestruct "£" as "[£ [£1 £']]".
          iFrame. unfold join_future.
          iIntros (tid''). 
          
          (* send ret back to tid *)
          iDestruct "ret" as "[Hgho %Hphys]".
          pose proof (own_send retty.(ty_size) retty Send1) as Send4.
          destruct Send4 as [SendRetPhys SendRetGho].
          clear at_mask. clear na_mask. iClear "fnincl".
          iDestruct "I" as (at_mask na_mask) "[I1 [[cna_lifetimes #fnincl] I2]]".
          iDestruct (SendRetGho tid' tid'' w d d True%I _ _ (S d) with
            "LFT UNIQ TIME [] cna_lifetimes [] [] Hgho Hsd") as "X"; first lia.
          { iApply guards_refl. }
          { iIntros (κ) "%Hin". rewrite gmultiset_elem_of_disj_union in Hin.
            destruct Hin as [Hin|Hin]; set_solver.
          }
          { done. }
          iDestruct (lc_step_fupdN_elim_later with "[£] X") as "X".
              { iApply (lc_weaken with "£"). unfold advance_credits. lia. }
          iMod (fupd_mask_mono with "X") as "X". { apply union_least; solve_ndisj. }
          iMod (fupd_mask_mono with "X") as "X". { apply union_least; solve_ndisj. }
          iDestruct "X" as (x2 off2) "[ret [#⧖off2 [%Habs2 [_ cna_lifetimes]]]]".
          
          iModIntro. iFrame. iExists (w.2), mask'.
          iSplit.
           - destruct x2. iPureIntro. rewrite (send_change_tid_phys tid'' tid' _ w); trivial.
           - iDestruct (persistent_time_receipt_mono with "⧖off2") as "$"; first lia.
             iSplit. { iPureIntro. destruct w, x2. unfold syn_abstract in Habs2.
              inversion Habs2. done. }
             iSplit; last by done.
             iApply (proph_obs_impl with "Obs"). intros π Ha. destruct x2. destruct w.
             apply Ha.
        }
        done.
    - rewrite /compose /id /trans_tail /trans_upper /=.
      move => ? [[? ?] [[? ?] []]] ? ? //.
      naive_solver.
    - iIntros (v).
      Disable Notation "k ◁cont{ L , I , T } tr" .
      simpl_subst.
      iApply (@type_letalloc_1 _ _ (at_locₛ (join_handleₛ ℭ)) [at_locₛ (join_handleₛ ℭ)] [] (at_locₛ (at_locₛ (join_handleₛ ℭ))) (join_handle Φ retty) "r" _ _ _ +[] (λ post '(lpredb -:: _) mask π, post lpredb mask π) id with "[]").
      + apply tctx_incl_refl.
      + by move => ? [[? ?] _] ? ? //.
      + done.
      + iIntros (r).
        simpl_subst.
        iApply (@cont.type_jump _ _ [at_locₛ (at_locₛ (join_handleₛ ℭ))] [at_locₛ (at_locₛ (join_handleₛ ℭ))] [] (at_locₛ (at_locₛ (join_handleₛ ℭ))) _ _ _ _ _ _ (λ post '(l -:: _) mask π, post -[l] mask π) _ _ _ _ _ +[]).
        * by apply elem_of_list_singleton. 
        * eapply tctx_extract_ctx_eq.
          { eapply tctx_extract_ctx_elt.
            1: apply tctx_extract_elt_here_exact.
            apply tctx_extract_ctx_nil. }
          rewrite /id /trans_tail /compose /=.
          fun_ext.
          move => ?.
          fun_ext.
          move => [[? ?] []] //.
        * instantiate (1 := λ _ _ x, x).
          apply resolve_tctx_nil.
        * rewrite /compose /=.
          simpl.
          done.
  Qed.


  (* Global Instance join_handle_ne {𝔄} : NonExpansive (@join_handle 𝔄). *)
  (* Proof. rewrite /join_handle /join_future. solve_ne_type. Qed. *)

  (* Global Instance join_handle_type_contractive {𝔄} : TypeContractive (@join_handle 𝔄). *)
  (* Proof. *)
  (*   split; [by apply type_lft_morphism_id_like|done| |done]=>/= *. *)
  (*   rewrite /join_future /join_handle. *)
  (*   do 15 f_equiv. done. *)
  (* Qed. *)

  (* Global Instance join_handle_send {𝔄} (ty: type 𝔄) : Send (join_handle ty). *)
  (* Proof. done. Qed. *)
  (* Global Instance join_handle_sync {𝔄} (ty: type 𝔄) : Sync (join_handle ty). *)
  (* Proof. done. Qed. *)

  (* Lemma join_handle_resolve {𝔄} (ty: type 𝔄) E L : *)
  (*   resolve E L (join_handle ty) (const True). *)
  (* Proof. apply resolve_just. Qed. *)

  (* Definition forward_pred {A B} (f: A → B) (Φ: pred' A) (b: B) : Prop := *)
  (*   ∃a, b = f a ∧ Φ a. *)

  (* Lemma join_handle_subtype {𝔄 𝔅} (f: 𝔄 → 𝔅) ty ty' E L : *)
  (*   subtype E L ty ty' f → *)
  (*   subtype E L (join_handle ty) (join_handle ty') (forward_pred f). *)
  (* Proof. *)
  (*   iIntros (Sub ?) "L". iDestruct (Sub with "L") as "#Sub". iIntros "!> E". *)
  (*   iDestruct ("Sub" with "E") as "#Incl". iPoseProof "Incl" as "#(%&?&_)". *)
  (*   do 2 (iSplit; [done|]). iSplit; iModIntro; last first. *)
  (*   { iIntros "* (%&->)". iExists _. iPureIntro. by fun_ext=>/=. } *)
  (*   iIntros (?? tid' [|[[]|][]]) "join //". iDestruct "join" as (?->) "join". *)
  (*   iExists _. iSplit. { iPureIntro. by fun_ext=>/=. } *)
  (*   iApply (join_handle_impl with "[] join"). iIntros "!>% fut %tid". *)
  (*   iDestruct ("fut" $! tid) as (??) "(Obs & ⧖ & box)". iExists _, _. *)
  (*   iFrame "⧖". iSplitL "Obs". *)
  (*   { iApply proph_obs_impl; [|done]=>/= ??. by eexists _. } *)
  (*   iDestruct (box_type_incl with "Incl") as "(_&_& InO &_)". by iApply "InO". *)
  (* Qed. *)

  (* Lemma join_handle_eqtype {𝔄 𝔅} (f: 𝔄 → 𝔅) g ty ty' E L : *)
  (*   eqtype E L ty ty' f g → *)
  (*   eqtype E L (join_handle ty) (join_handle ty') (forward_pred f) (forward_pred g). *)
  (* Proof. move=> [??]. split; by apply join_handle_subtype. Qed. *)

  (* Definition join: val := *)
  (*   fn: ["bj"] := *)
  (*     let: "j" := !"bj" in delete [ #1; "bj"];; *)
  (*     let: "r" := spawn.join ["j"] in *)
  (*     return: ["r"]. *)

  (* (* Rust's JoinHandle::join *) *)
  (* Lemma join_type {𝔄} (retty: type 𝔄) : *)
  (*   typed_val join (fn(∅; join_handle retty) → retty) *)
  (*     (λ post '-[Φ], ∀a: 𝔄, Φ a → post a). *)
  (* Proof. *)
  (*   eapply type_fn; [solve_typing|]=> _ ??[?[]]. simpl_subst. via_tr_impl. *)
  (*   { iApply type_deref; [solve_extract|solve_typing..|]. intro_subst_as (j). *)
  (*     iApply type_delete; [solve_extract|done..|]. *)
  (*     iApply (type_let' +[_ ◁ join_handle _] (λ r, +[r ◁ box retty]) *)
  (*       (λ post '-[Φ], ∀a: 𝔄, Φ a → post -[a])). *)
  (*     { iIntros (??[?[]]) "_ _ _ _ _ $$ /=[j _] Obs". rewrite tctx_hasty_val. *)
  (*       iDestruct "j" as (?) "[_ join]". case j as [[|j|]|]=>//. *)
  (*       iDestruct "join" as (?->) "join". iApply (join_spec with "join"). iNext. *)
  (*       iIntros (?) "fut". iDestruct ("fut" $! _) as (??) "(Obs' &?&?)". *)
  (*       iCombine "Obs Obs'" as "?". iExists -[_]. *)
  (*       rewrite right_id tctx_hasty_val. iSplit; [iExists _; by iFrame|]. *)
  (*       iApply proph_obs_impl; [|done]=>/= ?[Imp ?]. by apply Imp. } *)
  (*     intro_subst. iApply type_jump; [solve_typing|solve_extract|solve_typing]. } *)
  (*   by move=>/= ?[?[]]. *)
  (* Qed. *)
End spawn.
