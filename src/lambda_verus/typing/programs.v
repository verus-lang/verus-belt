From iris.proofmode Require Import environments.
From lrust.lang Require Import proofmode.
From lrust.typing Require Export type lft_contexts type_context cont_context inv_context.
From lrust.lifetime Require Import lifetime_full.
From guarding Require Import guard tactics.
Set Default Proof Using "Type".

Implicit Type (𝔄 𝔅: syn_type) (𝔄l 𝔅l: syn_typel).

Section typing.
  Context `{!typeG Σ}.
  
  (** Function Body *)
  (* This is an iProp because it is also used by the function type. *)
  Definition typed_body {𝔄l 𝔅} (E: elctx) (L: llctx) (I: invctx) (C: cctx 𝔅) (T: tctx 𝔄l)
    (e: expr) (tr: predl_trans' 𝔄l 𝔅) : iProp Σ := ∀tid xl mask post iκs,
    llft_ctx -∗ time_ctx -∗ proph_ctx -∗ uniq_ctx -∗ elctx_interp E -∗
    llctx_interp L -∗ invctx_interp tid mask iκs I -∗ cctx_interp tid iκs post C -∗ tctx_interp tid T xl -∗
      ⟨π, tr post xl mask π⟩ -∗ WP e {{ _, cont_postcondition }}.
  Global Arguments typed_body {_ _} _ _ _ _ _ _%E _%type.

  Global Instance typed_body_proper 𝔄l 𝔅 E L I C T e :
    Proper ((≡) ==> (≡)) (@typed_body 𝔄l 𝔅 E L I C T e).
  Proof. intros ?? EQ. unfold typed_body. do 22 f_equiv. apply EQ. Qed.

  Lemma typed_body_impl {𝔄l 𝔅} (tr tr': predl_trans' 𝔄l 𝔅) E L
      (I: invctx) (C: cctx 𝔅) (T: tctx 𝔄l) e :
    (∀post xl mask π, tr post xl mask π → tr' post xl mask π) →
    typed_body E L I C T e tr' -∗ typed_body E L I C T e tr.
  Proof.
    move=> Imp. rewrite /typed_body.
    iIntros "x * A B C D E F G H I J".
    iDestruct ("x" with "A B C D E F G H I") as "X".
    iApply "X". 
    iApply proph_obs_impl. 2: { iFrame "J". }
    intros π Hx. apply Imp. apply Hx.
  Qed.
  
  Lemma typed_body_vacuous {𝔄l 𝔅} E L
      (I: invctx) (C: cctx 𝔅) (T: tctx 𝔄l) e :
    ⊢ typed_body E L I C T e (λ _ _ _ _, False%type).
  Proof.
    rewrite /typed_body.
    iIntros "* A B PROPH D E F G H I Obs".
    iMod (proph_obs_sat with "PROPH Obs") as "%Ha". { solve_ndisj. }
    destruct Ha as [x Ha]. done.
  Qed.

  Lemma typed_body_tctx_incl {𝔄l 𝔅l ℭ} tr' tr (T: tctx 𝔄l) (T': tctx 𝔅l) E L
      (I: invctx) (C: cctx ℭ) e :
    tctx_incl E L T T' tr' →
    typed_body E L I C T' e tr -∗ typed_body E L I C T e (tr' ∘ tr).
  Proof.
    iIntros ([? In]) "e". iIntros (?????) "#LFT TIME #PROPH #UNIQ #E L Ic C T Obs".
    iMod (llctx_interp_make_guarded with "L") as (γ) "[H1 [H2 [#guard #back]]]". { solve_ndisj. }
    iMod (In with "LFT PROPH UNIQ E guard H1 T Obs") as (?) "(H1 & T' & Obs)".
      iDestruct ("back" with "H1 H2") as "back'". iMod (fupd_mask_mono with "back'") as "L". { solve_ndisj. }
    iApply ("e" with "LFT TIME PROPH UNIQ E L Ic C T' Obs").
  Qed.

  (** Instruction *)
  Definition typed_instr {𝔄l 𝔅l} (E: elctx) (L: llctx) (I: invctx)
    (T: tctx 𝔄l) (e: expr) (T': val → tctx 𝔅l) (tr: predl_trans 𝔄l 𝔅l) : Prop :=
    ∀tid post mask iκs xl, llft_ctx -∗ time_ctx -∗ proph_ctx -∗ uniq_ctx -∗ elctx_interp E -∗
      llctx_interp L -∗ invctx_interp tid mask iκs I -∗ tctx_interp tid T xl -∗
      ⟨π, tr post xl mask π⟩ -∗ WP e {{ v, ∃xl',
        llctx_interp L ∗ invctx_interp tid mask iκs I ∗ tctx_interp tid (T' v) xl' ∗ ⟨π, post xl' mask π⟩ }}.
  Global Arguments typed_instr {_ _} _ _ _ _ _%E _ _%type.
  
  Definition typed_inv_instr {𝔄l 𝔅l} (E: elctx) (L: llctx) (I: invctx) 
    (T: tctx 𝔄l) (e: expr) (I': invctx) (T': val → tctx 𝔅l) (tr: predl_trans 𝔄l 𝔅l) : Prop :=
    ∀tid post mask iκs xl, llft_ctx -∗ time_ctx -∗ proph_ctx -∗ uniq_ctx -∗ elctx_interp E -∗
      llctx_interp L -∗ invctx_interp tid mask iκs I -∗ tctx_interp tid T xl -∗
      ⟨π, tr post xl mask π⟩ -∗ WP e {{ v, ∃xl' mask',
        llctx_interp L ∗ invctx_interp tid mask' iκs I' ∗ tctx_interp tid (T' v) xl' ∗ ⟨π, post xl' mask' π⟩ }}.
  Global Arguments typed_instr {_ _} _ _ _ _ _%E _ _%type.

  Definition typed_instr_ty {𝔄l 𝔅} (E: elctx) (L: llctx) (I: invctx)
    (T: tctx 𝔄l) (e: expr) (ty: type 𝔅) (tr: pred' (~~𝔅) → predl 𝔄l) : Prop :=
    typed_instr E L I T e (λ v, +[v ◁ ty]) (λ post al, tr (λ b, post -[b]) al).
  Global Arguments typed_instr_ty {_ _} _ _ _ _ _%E _%T _%type.

  Definition typed_val {𝔄} (v: val) (ty: type 𝔄) (a: ~~𝔄) : Prop :=
    ∀E L I, typed_instr_ty E L I +[] (of_val v) ty (λ post _, post a).
  Global Arguments typed_val {_} _%V _%T _%type.

  (* This lemma is helpful for specifying the predicate transformer. *)
  Lemma type_with_tr 𝔄l 𝔅 tr E L (I: invctx) (C: cctx 𝔅) (T: tctx 𝔄l) e :
    typed_body E L I C T e tr -∗ typed_body E L I C T e tr.
  Proof. iIntros. done. Qed.

  (* This lemma is helpful when switching from proving unsafe code in Iris
     back to proving it in the type system. *)
  Lemma type_type {𝔄l 𝔅} (T: tctx 𝔄l) xl mask tr E L (I: invctx) (C: cctx 𝔅) e tid post iκs :
    typed_body E L I C T e tr -∗
    llft_ctx -∗ time_ctx -∗ proph_ctx -∗ uniq_ctx -∗ elctx_interp E -∗
    llctx_interp L -∗ invctx_interp tid mask iκs I -∗ cctx_interp tid iκs post C -∗ tctx_interp tid T xl -∗
    ⟨π, tr post xl mask π⟩ -∗ WP e {{ _, cont_postcondition }}.
  Proof.
    iIntros "Bd LFT TIME PROPH UNIQ E L I C T Obs".
    iApply ("Bd" with "LFT TIME PROPH UNIQ E L I C T Obs").
  Qed.

  (* TODO: Proof a version of this that substitutes into a compatible context...
     if we really want to do that. *)
  Lemma type_equivalize_lft {𝔄l 𝔅} E L I (C: cctx 𝔅) (T: tctx 𝔄l) κ κ' e tr :
    typed_body (κ ⊑ₑ κ' :: κ' ⊑ₑ κ :: E) L I C T e tr -∗
    typed_body E (κ ⊑ₗ [κ'] :: L) I C T e tr.
  Proof.
    iIntros "e" (?????) "#LFT TIME PROPH UNIQ E [Eq L] I C T".
    iMod (lctx_equalize_lft with "LFT Eq") as "[In In']".
    iApply ("e" with "LFT TIME PROPH UNIQ [$E $In $In'] L I C T").
  Qed.

  (* [type_dep_cond] lets typing deduction depend on dynamic values,
    requiring some precondition on them *)
  (* 
  Lemma type_dep_cond {𝔄l A 𝔅l ℭl 𝔇} (Φ: pred' A) (Tx: tctx 𝔄l) (f: _ → A)
      E L (T: tctx 𝔅l) (T': tctx ℭl) (C: cctx 𝔇) e trx tr :
    Closed [] e → tctx_extract_ctx E L Tx T T' trx → real_tctx E L Tx f →
    (∀a: A, ⌜Φ a⌝ -∗ typed_body E L C (Tx h++ T') e (tr a)) -∗
    typed_body E L C T (Skip;; e) (trx ∘ (λ post acl,
      let a := f (psepl acl) in Φ a ∧ tr a post acl))%type.
  Proof.
    iIntros (?? Rl) "e". iApply (typed_body_tctx_incl trx); [done|].
    iIntros (? acπl ?) "#LFT #TIME #PROPH UNIQ #E L C".
    move: (papp_ex acπl)=> [aπl[cπl->]]. iIntros "[Tx T'] #Obs".
    iMod (Rl with "LFT E L Tx") as (?) "[⧖ Upd]". wp_bind Skip.
    iApply (wp_step_fupdN_persistent_time_receipt _ _ ∅ with "TIME ⧖ [Upd]")=>//.
    { iApply step_fupdN_with_emp. by rewrite difference_empty_L /=. }
    wp_seq. iIntros "(%Eq & L & Tx) !>". move: Eq=> [a Eq]. wp_seq.
    iMod (proph_obs_sat with "PROPH Obs") as %[π₀ Obs]; [done|].
    move: (equal_f Eq π₀) Obs=>/= + [+_]. rewrite papply_app papp_sepl=>/= -> Φa.
    iApply ("e" $! a Φa _ (_-++_)  with "LFT TIME PROPH UNIQ E L C [$Tx $T'] []").
    iApply proph_obs_impl; [|done]=>/= π[_ +]. move: (equal_f Eq π)=>/= <-.
    by rewrite papply_app papp_sepl.
  Qed.

  (* [type_dep] lets typing deduction depend on dynamic values;
    it is derived from [type_dep_cond] *)
  Lemma type_dep {𝔄l A 𝔅l ℭl 𝔇} (Tx: tctx 𝔄l) (f: _ → A)
      E L (T: tctx 𝔅l) (T': tctx ℭl) (C: cctx 𝔇) e trx tr :
    Closed [] e → tctx_extract_ctx E L Tx T T' trx → real_tctx E L Tx f →
    (∀a: A, typed_body E L C (Tx h++ T') e (tr a)) -∗
    typed_body E L C T (Skip;; e) (trx ∘ (λ post acl,
      let a := f (psepl acl) in tr a post acl))%type.
  Proof.
    iIntros (???) "e". iApply (typed_body_tctx_incl trx); [done|].
    iApply typed_body_impl; last first.
    { iApply (type_dep_cond (const True)); [apply tctx_incl_refl|done|].
      iIntros (a ?). iApply ("e" $! a). }
    move=>/= ???. by split.
  Qed.
  *)

  Lemma type_let' {𝔄l 𝔅l ℭl 𝔇} (T1: tctx 𝔄l) (T2: val → tctx 𝔅l) tr tr'
      (T: tctx ℭl) (I: invctx) (C: cctx 𝔇) xb e e' E L :
    Closed (xb :b: []) e' → typed_instr E L I T1 e T2 tr →
    (∀v: val, typed_body E L I C (T2 v h++ T) (subst' xb v e') tr') -∗
    typed_body E L I C (T1 h++ T) (let: xb := e in e')%E (λ post acl,
      let '(al, cl) := psep acl in tr (λ bl, tr' post (bl -++ cl)) al).
  Proof.
    iIntros "% %Inst e'" (? vπl2 ???). move: (papp_ex vπl2)=> [vπl[vπl'->]].
    iIntros "#LFT #TIME #PROPH #UNIQ #E L I C [T1 T] Obs". wp_bind e.
    iApply (wp_wand with "[L I T1 Obs]").
    { iApply (Inst with "LFT TIME PROPH UNIQ E L I T1").
      iApply proph_obs_eq; [|done]=> ?. by rewrite /trans_upper papp_sepl. }
    iIntros (v) "A".
    iDestruct "A" as (xl') "(L & I & T2 &?)". wp_let. iCombine "T2 T" as "T2T".
    iApply ("e'" with "LFT TIME PROPH UNIQ E L I C T2T").
    iApply proph_obs_eq; [|done]=>/= ?. by rewrite papp_sepr.
  Qed.
  
  Lemma type_let'_with_inv {𝔄l 𝔅l ℭl 𝔇} (T1: tctx 𝔄l) (T2: val → tctx 𝔅l) tr tr'
      (T: tctx ℭl) (I1 I2: invctx) (C: cctx 𝔇) xb e e' E L :
    Closed (xb :b: []) e' → typed_inv_instr E L I1 T1 e I2 T2 tr →
    (∀v: val, typed_body E L I2 C (T2 v h++ T) (subst' xb v e') tr') -∗
    typed_body E L I1 C (T1 h++ T) (let: xb := e in e')%E (λ post acl,
      let '(al, cl) := psep acl in tr (λ bl, tr' post (bl -++ cl)) al).
  Proof.
    iIntros "% %Inst e'" (? vπl2 ???). move: (papp_ex vπl2)=> [vπl[vπl'->]].
    iIntros "#LFT #TIME #PROPH #UNIQ #E L I C [T1 T] Obs". wp_bind e.
    iApply (wp_wand with "[L I T1 Obs]").
    { iApply (Inst with "LFT TIME PROPH UNIQ E L I T1").
      iApply proph_obs_eq; [|done]=> ?. by rewrite /trans_upper papp_sepl. }
    iIntros (v) "A".
    iDestruct "A" as (xl' mask') "(L & I & T2 &?)". wp_let. iCombine "T2 T" as "T2T".
    iApply ("e'" with "LFT TIME PROPH UNIQ E L I C T2T").
    iApply proph_obs_eq; [|done]=>/= ?. by rewrite papp_sepr.
  Qed.

  Lemma type_let {𝔄l 𝔅l ℭl 𝔇l 𝔈} (T1: tctx 𝔄l) (T2: val → tctx 𝔅l) tr tr' trx
    (T: tctx ℭl) (T': tctx 𝔇l) E L I (C: cctx 𝔈) xb e e' tr_res :
    Closed (xb :b: []) e' → typed_instr E L I T1 e T2 tr →
    tctx_extract_ctx E L T1 T T' trx → tr_res ≡ trx ∘ (trans_upper tr ∘ tr') →
    (∀v: val, typed_body E L I C (T2 v h++ T') (subst' xb v e') tr') -∗
    typed_body E L I C T (let: xb := e in e')%E tr_res.
  Proof.
    iIntros (???->) "?". iApply (typed_body_tctx_incl trx); [done|].
    by iApply type_let'.
  Qed.
  
  Lemma type_let_with_inv {𝔄l 𝔅l ℭl 𝔇l 𝔈} (T1: tctx 𝔄l) (T2: val → tctx 𝔅l) tr tr' trx
    (T: tctx ℭl) (T': tctx 𝔇l) E L I1 I2 (C: cctx 𝔈) xb e e' tr_res :
    Closed (xb :b: []) e' → typed_inv_instr E L I1 T1 e I2 T2 tr →
    tctx_extract_ctx E L T1 T T' trx → tr_res ≡ trx ∘ (trans_upper tr ∘ tr') →
    (∀v: val, typed_body E L I2 C (T2 v h++ T') (subst' xb v e') tr') -∗
    typed_body E L I1 C T (let: xb := e in e')%E tr_res.
  Proof.
    iIntros (???->) "?". iApply (typed_body_tctx_incl trx); [done|].
    by iApply type_let'_with_inv.
  Qed.

  Lemma type_val {𝔄 𝔅l ℭ} v (a: ~~𝔄) ty (T: tctx 𝔅l) E L (I: invctx) (C: cctx ℭ) xb e tr :
    Closed (xb :b: []) e → typed_val v ty a →
    (∀v': val, typed_body E L I C (v' ◁ ty +:: T) (subst' xb v' e) tr) -∗
    typed_body E L I C T (let: xb := v in e)%E (λ post bl, tr post (a -:: bl)).
  Proof.
    iIntros (? Val) "?". iApply type_let; [apply Val|solve_typing|done..].
  Qed.

  (* [type_val_dep] lets the obtained value depend on dynamic values;
    it is derived from [type_dep] and [type_val] *)
  (* 
  Lemma type_val_dep {𝔄 𝔅l B ℭl 𝔇l 𝔈} (a: B → 𝔄) ty (Tx: tctx 𝔅l)
      E L (C: cctx 𝔈) (T: tctx ℭl) (T': tctx 𝔇l) v xb e trx tr f :
    Closed (xb :b: []) e → (∀b, typed_val v ty (a b)) →
    tctx_extract_ctx E L Tx T T' trx → real_tctx E L Tx f →
    (∀v': val, typed_body E L C (v' ◁ ty +:: Tx h++ T') (subst' xb v' e) tr) -∗
    typed_body E L C T (Skip;; let: xb := v in e) (trx ∘
      (λ post bdl, let '(bl, dl) := psep bdl in tr post (a (f bl) -:: bdl))).
  Proof.
    iIntros (? Val ??) "e". iApply typed_body_impl; last first.
    { iApply type_dep; [ |done|done|].
      (* TODO: make [solve_closed] work here *)
      { rewrite /Closed /= !andb_True. split; [done|]. split; [|done].
        apply is_closed_of_val. }
      iIntros (b). iApply type_val; by [exact (Val b)|]. }
    by move=>/= ??.
  Qed.
  *)

  Lemma type_seq {𝔄l 𝔅l ℭl 𝔇l 𝔈} (T1: tctx 𝔄l) (T2: tctx 𝔅l)
    (T: tctx ℭl) (T': tctx 𝔇l) E L (I: invctx) (C: cctx 𝔈) e e' tr tr' trx tr_res :
    Closed [] e' → typed_instr E L I T1 e (const T2) tr →
    tctx_extract_ctx E L T1 T T' trx → tr_res ≡ trx ∘ (trans_upper tr ∘ tr') →
    typed_body E L I C (T2 h++ T') e' tr' -∗ typed_body E L I C T (e;; e')%E tr_res.
  Proof. iIntros. iApply (type_let _ (const T2))=>//. by iIntros. Qed.
  
  (* this is strictly more general than type_seq,
  should refactor to make this the default one *)
  Lemma type_seq_with_inv {𝔄l 𝔅l ℭl 𝔇l 𝔈} (T1: tctx 𝔄l) (T2: tctx 𝔅l)
    (T: tctx ℭl) (T': tctx 𝔇l) E L (I1 I2: invctx) (C: cctx 𝔈) e e' tr tr' trx tr_res :
    Closed [] e' → typed_inv_instr E L I1 T1 e I2 (const T2) tr →
    tctx_extract_ctx E L T1 T T' trx → tr_res ≡ trx ∘ (trans_upper tr ∘ tr') →
    typed_body E L I2 C (T2 h++ T') e' tr' -∗ typed_body E L I1 C T (e;; e')%E tr_res.
  Proof. iIntros. iApply (type_let_with_inv _ (const T2))=>//. by iIntros. Qed.

  Lemma type_newlft {𝔄l 𝔅} κl E L (I: invctx) (C: cctx 𝔅) (T: tctx 𝔄l) e tr :
    Closed [] e → (∀κ, typed_body E (κ ⊑ₗ κl :: L) I C T e tr) -∗
    typed_body E L I C T (Newlft;; e) tr.
  Proof.
    iIntros (?) "e %%%%% #LFT TIME PROPH UNIQ E L I C T Obs".
    iMod (llftl_begin' with "LFT") as (Λ) "[Λ #Hinh]"; [done|].
    set κ' := lft_intersect_list κl. wp_seq.
    iApply ("e" $! κ' ⊓ Λ with "LFT TIME PROPH UNIQ E [Λ $L] I C T Obs").
    rewrite /llctx_interp. iExists Λ. iFrame "Λ". by iSplit.
  Qed.
  

  Lemma type_endlft {𝔄l 𝔅l ℭ} (T: tctx 𝔄l) (T' T'': tctx 𝔅l)
      (f: proph_asn → plist indep_interp_of_syn_type 𝔅l → plist indep_interp_of_syn_type 𝔅l → Prop)
      κ κl tru tr e E L I (C: cctx ℭ) :
    Closed [] e →
    resolve_unblock_tctx E (κ ⊑ₗ κl :: L) κ T T' tru → unblock_tctx E L κ T' T'' f →
    typed_body E L I C T'' e tr -∗
    typed_body E (κ ⊑ₗ κl :: L) I C T (Endlft;; e)
      (tru ∘ (λ post xl mask π, ∀ xl', f π xl xl' → tr post xl' mask π)%type).
  Proof.
    iIntros (? RslvU Un) "e %tid %xl %mask %post %iκs #LFT #TIME #PROPH #UNIQ #E L' I C T Obs".
    wp_bind Skip.
    iMod (llctx_interp_make_guarded with "L'") as (γ) "[H1 [H2 [#Ghalf #Halfback]]]". { solve_ndisj. }
    iMod (RslvU with "LFT PROPH UNIQ TIME E Ghalf H1 T Obs") as (??) "[⧖ ToT']".
    iApply (wp_step_fupdN_persistent_time_receipt' _ _ ∅ with "TIME ⧖ [ToT']")=>//.
    { iApply step_fupdN_with_emp. 
      iDestruct (step_fupdN_nmono with "ToT'") as "ToT'";
      last by rewrite difference_empty_L. nia. }
    wp_seq. (*iIntros "([(%&%& κ' & To†) L] & T' & Obs) !>".*)
    iIntros "(H1 & T' & Obs) !>".
    iDestruct ("Halfback" with "H1 H2") as "L'". iMod (fupd_mask_mono with "L'") as "L'". { solve_ndisj. }
    iDestruct "L'" as "[(%&%& κ' & %ToDead) L]".
    iDestruct (llftl_end' with "LFT κ'") as "To†". { apply ToDead. }
    wp_seq. wp_bind Skip.
    iApply wp_mask_mono; [|iApply (wp_step_fupd with "To†")]; [set_solver..|].
    wp_seq. iIntros "† !>". wp_seq. wp_bind Skip.
    iMod (llctx_interp_make_guarded with "L") as (γ1) "[H1 [H2 [#Ghalf1 #Halfback1]]]". { solve_ndisj. }
    iMod (Un with "LFT TIME PROPH UNIQ E Ghalf1 H1 [†] T'") as (??) "[⧖ ToT']".
    { simpl in *. subst. rewrite llftl_end_inter. by iRight. }
    iApply (wp_step_fupdN_persistent_time_receipt' _ _ ∅ with "TIME ⧖ [ToT']")=>//.
    { iApply step_fupdN_with_emp.
        iDestruct (step_fupdN_nmono _ (((S d0 * S d0))) with "ToT'") as "ToT'". { nia. }
        rewrite <- step_fupdN_addS. 
        by rewrite difference_empty_L. }
    wp_seq. iIntros "(H1 & T'' & Obs') !>". wp_seq. iCombine "Obs Obs'" as "Obs".
    iDestruct ("Halfback1" with "H1 H2") as "L". iMod (fupd_mask_mono with "L") as "L". { solve_ndisj. }
    iApply ("e" with "LFT TIME PROPH UNIQ E L I C T'' [Obs]").
    iApply (proph_obs_impl with "Obs"). intros π [Ha Hf]. apply Ha. apply Hf.
  Qed.

  (** Explicit resolution of a path *)
  Lemma type_resolve_instr {𝔄} p (ty: type 𝔄) Φ E L I :
    resolve E L ty Φ →
    typed_instr E L I +[p ◁ ty] Skip (λ _, +[]) (λ post '-[a], λ mask π, Φ a π → post -[] mask π).
  Proof.
    iIntros (Rslv ????[?[]]) "LFT #TIME PROPH UNIQ E L I /=[(%&%&%& ⧖ & ty) _] Obs".
    iMod (llctx_interp_make_guarded with "L") as (γ) "[H1 [H2 [#Ghalf #Halfback]]]". { solve_ndisj. }
    iDestruct "ty" as "[tygho typhys]".
    iDestruct (Rslv _ (⊤∖↑advN) with "LFT PROPH UNIQ TIME E Ghalf H1 tygho") as "Upd"; [solve_ndisj|].
    
    iApply (wp_persistent_time_receipt with "TIME ⧖"); [solve_ndisj|]. iIntros "£ ⧖S".
    iMod "Upd".
    iMod (lc_step_fupdN_elim_later with "[£] Upd") as "Upd". { iApply (lc_weaken with "£"). unfold advance_credits. lia. }
    iMod "Upd" as "[Obs' H1]".
    iDestruct ("Halfback" with "H1 H2") as "L". iMod (fupd_mask_mono with "L") as "L". { solve_ndisj. }
    wp_seq.
    iExists -[]. iCombine "Obs Obs'" as "?".
    rewrite left_id. iFrame "L I". iApply proph_obs_impl; [|done]=>/= ?[Imp ?]. apply Imp.
    trivial.
  Qed.

  Lemma type_resolve {𝔄 𝔅l ℭl 𝔇} p (ty: type 𝔄) Φ E L trx e tr
      (T: tctx 𝔅l) (T': tctx ℭl) (I: invctx) (C: cctx 𝔇) :
    Closed [] e → tctx_extract_ctx E L +[p ◁ ty] T T' trx → resolve E L ty Φ →
    typed_body E L I C T' e tr -∗
    typed_body E L I C T (Skip;; e)
      (trx ∘ (λ post '(a -:: cl), λ mask π, Φ a π → tr post cl mask π))%type.
  Proof.
    iIntros (? Extr ?) "?". iApply type_seq; [by eapply type_resolve_instr|done| |done].
    move: Extr=> [Htrx _]??/=. apply Htrx. by case.
  Qed.

  Lemma type_path_instr {𝔄} p (ty: type 𝔄) E L I :
    typed_instr_ty E L I +[p ◁ ty] p ty (λ post '-[v], post v).
  Proof.
    iIntros (????[vπ[]]) "_ _ _ _ _ $$ [T _] Obs". iApply (wp_hasty with "T").
    iIntros (v d _) "??". iExists -[vπ]. do 2 (iSplit; [|done]). iExists v, d.
    rewrite eval_path_of_val. by iFrame.
  Qed.

  Lemma type_letpath {𝔄 𝔅l ℭl 𝔇} (ty: type 𝔄) (T: tctx 𝔅l) (T': tctx ℭl)
    (I: invctx) (C: cctx 𝔇) x p e trx tr E L :
    Closed (x :b: []) e → tctx_extract_ctx E L +[p ◁ ty] T T' trx →
    (∀v: val, typed_body E L I C (v ◁ ty +:: T') (subst' x v e) tr) -∗
    typed_body E L I C T (let: x := p in e) (trx ∘ tr).
  Proof.
    iIntros (? Extr) "?". iApply type_let; [by eapply type_path_instr|done| |done].
    destruct Extr as [Htrx _]=>?? /=. apply Htrx. by case.
  Qed.
  
End typing.

Ltac via_tr_impl :=
  iStartProof;
  match goal with |- envs_entails _ (typed_body _ _ _ ?C ?T _ _) =>
    let TypeT := type of T in let TypeC := type of C in
    match eval hnf in (TypeT, TypeC) with (hlist _ ?𝔄l, list (_ ?𝔅)) =>
      iApply (typed_body_impl (𝔄l:=𝔄l) (𝔅:=𝔅)); last first
    end
  end.

Ltac via_tr_impl_with tr :=
  iStartProof;
  match goal with |- envs_entails _ (typed_body _ _ ?C ?T _ _) =>
    let TypeT := type of T in let TypeC := type of C in
    match eval hnf in (TypeT, TypeC) with (hlist _ ?𝔄l, list (_ ?𝔅)) =>
      evar (tr: predl_trans' 𝔄l 𝔅);
      iApply (typed_body_impl (𝔄l:=𝔄l) (𝔅:=𝔅) tr); last first
    end
  end.

Ltac intro_subst := iIntros (?); simpl_subst.
Ltac intro_subst_as x := iIntros (x); simpl_subst.

Global Hint Opaque typed_instr : lrust_typing.
