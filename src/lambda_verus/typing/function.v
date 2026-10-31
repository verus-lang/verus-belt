Import EqNotations.
From lrust.typing Require Export type.
From lrust.typing Require Import programs cont value_ctx.
From lrust.lifetime Require Import lifetime_full.
From guarding Require Import guard tactics.
Set Default Proof Using "Type".

(** * Function types on MiniRust values (stage 4f of the MiniRust memory model)

[fn fp spec] is the function type: the arguments and the result of a function are
MiniRust values ([w ◁ᵥ ty], [typing/value_ctx.v]) of the types of [fp]. A box of bytes is passed
as a value of type [own_bytes n ty]; a shared reference as a value of type [&shr{κ} ty]
(the root of a shared place, [typing/place_pshr.v]); a unique borrow as a value of type
[&uniq{κ} ty]. The function value itself is still a closure ([RecV]) typed by the
function value element [f ◁ᶠ fn fp spec] ([typing/type_context.v]): closures have no
MiniRust value (decision 3 of the plan). The specification is a predicate transformer on the values of the arguments and
the result ([fn_spec]), not on boxes of them.

Rules: [type_call] ([call: p ql → k]), [type_letcall], [type_fnrec], [type_fn]. *)

Implicit Type (𝔄 𝔅: syn_type) (𝔄l 𝔅l: syn_typel).

Fixpoint subst_plv {𝔄l} (bl: plistc binder 𝔄l) (vl: plistc val 𝔄l) (e: expr) : expr :=
  match 𝔄l, bl, vl with
  | [], _, _ => e
  | _::_, b -:: bl', v -:: vl' => subst' b v (subst_plv bl' vl' e)
  end.

Global Instance do_subst_plv {𝔄l} (bl vl: plistc _ 𝔄l) e :
  DoSubstL bl (map of_val vl) e (subst_plv bl vl e).
Proof.
  rewrite /DoSubstL. induction 𝔄l, bl, vl; [done|]=>/=. by rewrite IH𝔄l.
Qed.

Lemma subst_plv_renew {𝔄l 𝔅l} (bl: plistc binder 𝔄l) (vl': plistc val 𝔅l) eq eq' e :
  subst_plv (plistc_renew eq bl) vl' e =
    subst_plv bl (plistc_renew eq' vl') e.
Proof.
  move: 𝔄l 𝔅l bl vl' eq eq'. fix FIX 1.
  case=> [|??]; case=>//= ??[??][??]??. f_equal. apply FIX.
Qed.

Section fn_params.
  Context `{!typeG Σ} {𝔄l: syn_typel} {𝔅: syn_type}.

  Record fn_params :=
    FP {
      fp_E_ex: lft → elctx;
      fp_ityl: typel 𝔄l;
      fp_oty: type 𝔅;
      fp_atomic_state: invctx_atomic_state
    }.

  Definition fn_params_dist n fp fp' : Prop :=
    (∀ϝ, fp.(fp_E_ex) ϝ = fp'.(fp_E_ex) ϝ) ∧
    fp.(fp_ityl) ≡{n}≡ fp'.(fp_ityl) ∧ fp.(fp_oty) ≡{n}≡ fp'.(fp_oty).

  Definition fp_E (fp: fn_params) ϝ : elctx :=
    fp.(fp_E_ex) ϝ ++ tyl_E fp.(fp_ityl) ++ tyl_outlives_E fp.(fp_ityl) ϝ ++
    fp.(fp_oty).(ty_E) ++ ty_outlives_E fp.(fp_oty) ϝ.

  Global Instance fp_E_ne n : Proper (fn_params_dist n ==> (=) ==> (=)) fp_E.
  Proof.
    rewrite /fp_E. move=> ?? Eq ??->. move: Eq=> [->[Eqi Eqo]].
    f_equiv. do 2 (f_equiv; [by rewrite Eqi|]). by rewrite Eqo.
  Qed.

  Lemma elctx_sat_fp_E (fp: fn_params) ϝ ϝ' L :
    fp_E_ex fp = const [] →
    elctx_sat (ϝ' ⊑ₑ ϝ :: fp_E fp ϝ) L (fp_E fp ϝ').
  Proof.
    move=> Eq. rewrite /fp_E Eq /=. apply elctx_sat_app; [solve_typing|].
    apply elctx_sat_app. { apply (tyl_outlives_E_elctx_sat_mono ϝ'); solve_typing. }
    apply elctx_sat_app; [solve_typing|].
    apply (ty_outlives_E_elctx_sat_mono ϝ'); solve_typing.
  Qed.

  Definition tr_ret {𝔄} : predl_trans' [𝔄] (𝔄) := λ post '-[a], λ mask π, post a mask π.
End fn_params.

Arguments fn_params {_ _} _ _.

Global Instance elctx_empty : Empty (lft → elctx) := λ _, [].

Notation fn_spec 𝔄l 𝔅 ℭ := ((~~ℭ) → predl_trans' 𝔄l 𝔅).

Section fn.
  Context `{!typeG Σ} {A: Type} {𝔄l 𝔅}.

  Program Definition fn {ℭ} (fp: A → fn_params 𝔄l 𝔅) (spec: fn_spec 𝔄l 𝔅 ℭ)
    : type (exec_funₛ ℭ) :=
    {|
      pt_gho (x: ~~ (exec_funₛ ℭ)) tid := tc_opaque
        (∃fb kb (bl: plistc _ _) e H, ⌜fst x = @RecV fb (kb :: bl) e H⌝ ∗
              ▷ □ ∀y ϝ k (wl: plistc _ _),
                typed_body (fp_E (fp y) ϝ) [ϝ ⊑ₗ []] (InvCtx [] ϝ (fp_atomic_state (fp y)))
                  [k ◁cont{[ϝ ⊑ₗ []], (InvCtx [] ϝ (fp_atomic_state (fp y))),
                    λ v: vec _ 1, +[vhd v ◁ᵥ (fp y).(fp_oty)] } tr_ret]
                  (hzip_with (λ _ ty (w: val), w ◁ᵥ ty) (fp y).(fp_ityl) wl)
                  (subst' fb (RecV fb (kb :: bl) e) $ subst' kb k $ subst_plv bl wl e)
                  (spec (snd x))
        );
    |}%I.
  Next Obligation. rewrite /tc_opaque. apply _. Qed.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
End fn.

Notation "fn< p > ( E ; ity , .. , ity' ) → oty" :=
  (fn (λ p, FP E%EL (ity%T +:: .. (+[ity'%T]) ..) oty%T AtomicClosed))
  (at level 99, p pattern, oty at level 200, format
    "fn< p > ( E ;  ity ,  .. ,  ity' )  →  oty") : lrust_type_scope.
Notation "fn< p > ( E ) → oty" := (fn (λ p, FP E%EL +[] oty%T AtomicClosed))
  (at level 99, p pattern, oty at level 200, format
    "fn< p > ( E )  →  oty") : lrust_type_scope.
Notation "fn( E ; ity , .. , ity' ) → oty" :=
  (fn (λ _: (), FP E%EL (ity%T +:: .. (+[ity'%T]) ..) oty%T AtomicClosed))
  (at level 99, oty at level 200, format
    "fn( E ;  ity ,  .. ,  ity' )  →  oty") : lrust_type_scope.
Notation "fn( E ) → oty" := (fn (λ _: (), FP E%EL +[] oty%T AtomicClosed))
  (at level 99, oty at level 200, format "fn( E )  →  oty") : lrust_type_scope.

Section typing.
  Context `{!typeG Σ}.

  Global Instance fn_send {A 𝔄l 𝔅 ℭ} (fp: A → fn_params 𝔄l 𝔅) (spec: fn_spec 𝔄l 𝔅 ℭ) :
    Send (fn fp spec).
  Proof.
    intros. split; trivial.
     - intros. unfold syn_abstract in H. inversion H.
       unfold ty_phys, fn, ty_of_st. simpl. rewrite H1. trivial.
     - iIntros. iApply step_fupdN_intro; first done. iNext.
       iExists x, 0%nat. iModIntro. iFrame. simpl.
       replace (d0 + 0)%nat with d0 by lia. iFrame "#". done.
  Qed.

  Global Instance fn_sync {A 𝔄l 𝔅 ℭ} (fp: A → fn_params 𝔄l 𝔅) (spec: fn_spec 𝔄l 𝔅 ℭ) :
    Sync (fn fp spec).
  Proof. apply sync_default; [done|]. split; iSplit; iIntros "?"; done. Qed.

  Lemma fn_resolve {A 𝔄l 𝔅 ℭ} (fp: A → fn_params 𝔄l 𝔅) (spec: fn_spec 𝔄l 𝔅 ℭ) E L :
    resolve E L (fn fp spec) (const (const True)).
  Proof. apply resolve_just. Qed.

  Local Lemma wp_app_hasty_val {𝔄l} vl r (f: val) (pl: plistc _ 𝔄l) (tyl: typel 𝔄l) vπl tid
      (Φ: val → iProp Σ) :
    tctx_interp tid (hzip_with (λ _ ty q, q ◁ᵥ ty) tyl pl) vπl -∗
    (∀wl: plistc _ _,
      tctx_interp tid (hzip_with (λ _ ty (w: val), w ◁ᵥ ty) tyl wl) vπl -∗
      WP f (of_val r :: map of_val (vl ++ wl))%V {{ Φ }}) -∗
    WP f (of_val r :: map of_val vl ++ pl) {{ Φ }}.
  Proof.
    move: tyl pl vπl vl. elim=> [|???? IH].
    { iIntros "* _ Wp". iSpecialize ("Wp" $! -[] with "[//]"). by rewrite !right_id. }
    iIntros ([p pl'][??]vl) "/= [p pl'] ToWp".
    have ->: App f (of_val r :: map of_val vl ++ p :: pl') =
      fill_item (AppRCtx f (r :: vl) pl') p by done.
    iDestruct "p" as (w Hw) "p".
    iApply wp_bind. iApply (wp_wand with "[]"); [by iApply wp_eval_path|].
    iIntros (? ->).
    have ->: fill_item (AppRCtx f (r :: vl) pl') w =
      App f (of_val r :: map of_val (vl ++ [w]) ++ pl') by rewrite map_app -assoc.
    iApply (IH with "pl'"). iIntros (?) "pl'". rewrite -assoc.
    iApply ("ToWp" $! (_-::_)). iFrame "pl'". iExists w. iFrame "p".
    by rewrite eval_path_of_val.
  Qed.

  Local Lemma invctx_interp_call Il ϝ' 𝛼 tid mask ϝ iκs :
      ϝ ⊑ ϝ' -∗
      ϝ ⊑ lft_intersect_list (fmap invctx_elt_unwrap Il) -∗
      invctx_interp tid mask iκs (InvCtx Il ϝ' 𝛼) -∗ ∃ iκs',
      invctx_interp tid mask iκs' (InvCtx [] ϝ 𝛼) ∗
          (∀ mask', invctx_interp tid mask' iκs' (InvCtx [] ϝ 𝛼) -∗
            invctx_interp tid mask' iκs (InvCtx Il ϝ' 𝛼)).
  Proof.
      unfold invctx_interp.
      iIntros "#Incl1 #InclList".
      iDestruct 1 as (na_mask at_mask) "[#masks [[cna_lifetimes #Incl] [cna_own ato]]]".
      iExists (fmap invctx_elt_unwrap Il ++ iκs).
      iSplitL.
       - iExists na_mask, at_mask. iFrame "masks cna_own ato".
         unfold invctx_to_multiset. simpl. rewrite gmultiset_disj_union_left_id.
         rewrite list_to_set_disj_app. iFrame "cna_lifetimes".
         rewrite lft_intersect_list_app.
         iApply llftl_incl_glb; first by done.
         iApply (guards_transitive with "Incl1 Incl").
       - iDestruct 1 as (na_mask' at_mask') "[#masks' [[cna_lifetimes #Incl'] [cna_own ato]]]".
         iFrame. iFrame "#".
         unfold invctx_to_multiset. simpl. rewrite gmultiset_disj_union_left_id.
         rewrite list_to_set_disj_app. iFrame "cna_lifetimes".
  Qed.

  Lemma type_call_iris' {A 𝔄l 𝔅 ℭ} L κl x (fp: A → fn_params 𝔄l 𝔅) (spec: fn_spec 𝔄l 𝔅 ℭ)
      p ql ql' (k: expr) E xl efun tid
        (post: ~~ 𝔅 → (Mask → (proph_asn → Prop)))
        (mask: Mask) Il ϝ' iκs G :
    AsVal k → IntoPlistc ql ql' → Timeless G →
    lctx_ictx_alive E L (InvCtx Il ϝ' (fp_atomic_state (fp x))) →
    (∀ϝ, elctx_sat (map (λ κ, ϝ ⊑ₑ κ) κl ++ E) L (fp_E (fp x) ϝ)) →
    llft_ctx -∗ time_ctx -∗ proph_ctx -∗ uniq_ctx -∗ elctx_interp E -∗
    (G &&{↑NllftG}&&> llctx_interp L) -∗
    (G &&{↑NllftG}&&> @[lft_intersect_list κl]) -∗ G -∗
    invctx_interp tid mask iκs (InvCtx Il ϝ' (fp_atomic_state (fp x))) -∗
    tctx_elt_interp tid (p ◁ᶠ fn fp spec) efun -∗
    tctx_interp tid (hzip_with (λ _ ty q, q ◁ᵥ ty) (fp x).(fp_ityl) ql') xl -∗
    ⟨π, (spec efun.2) post xl mask π⟩ -∗
    (∀(ret: val) (mask': Mask) w, G -∗
      invctx_interp tid mask' iκs (InvCtx Il ϝ' (fp_atomic_state (fp x))) -∗
      tctx_elt_interp tid (ret ◁ᵥ (fp x).(fp_oty)) w -∗ ⟨π, post w mask' π⟩ -∗
      WP k [of_val ret] {{ _, cont_postcondition }}) -∗
    WP (call: p ql → k) {{ _, cont_postcondition }}.
  Proof.
    move=> [k' <-]-> TimelessG IctxAlv ToEfp.
    iIntros "#LFT TIME PROPH UNIQ E #GguardsL #Gguardsκl G ii p ql Obs k".
    iMod (llftl_begin' with "LFT") as (ϝ) "[ϝ #ϝnonempty]"; [done|].
    iApply fupd_wp.
    leaf_open "GguardsL" with "G" as "[L back]"; first by solve_ndisj.
    iDestruct (ToEfp ϝ with "L") as "#EfpPre".
    iDestruct (lctx_ictx_alive_L_guards_ϝ _ _ _ _ _ IctxAlv with "L E") as "#Lguardsϝ'".
    iDestruct (lctx_ictx_alive_L_guards_list _ _ _ _ _ IctxAlv with "L E") as "#LguardsIl".
    iMod ("back" with "L") as "G".
    iMod (llftl_borrow_shared _ ϝ with "G") as "[fGuardsG' ToG]"; first by solve_ndisj.
    iDestruct (guards_remove_later_rhs with "fGuardsG'") as "#fGuardsG". iClear "fGuardsG'".
    iDestruct (guards_transitive with "fGuardsG Gguardsκl") as "Borκl".
    iDestruct (guards_transitive with "fGuardsG GguardsL") as "fGuardsL".
    iDestruct ("EfpPre" with "[$E]") as "#Efp".
    { clear ToEfp. iClear "EfpPre". iClear "Gguardsκl". iInduction κl as [|κ κl] "IH"; [done|]=>/=.
      iSplit. { iApply (llftl_incl_trans with "Borκl []"). iApply llftl_intersect_incl_l. }
      iApply "IH". iModIntro. iApply llftl_incl_trans; [done|].
      iApply llftl_intersect_incl_r. }
    iModIntro. wp_apply (wp_fun with "p"). iIntros (d) "% _".
    iDestruct 1 as (fb kb bl e Hclosed) "[%Hrec #e]".
    have ->: (λ: ["_r"], Skip;; k' ["_r"])%E = (λ: ["_r"], Skip;; k' ["_r"])%V by unlock.
    iApply (wp_app_hasty_val [] with "ql")=>/=. iIntros (wl) "ityl".
    rewrite Hrec. wp_rec.
    iDestruct (invctx_interp_call Il ϝ' _ tid mask ϝ iκs with "[] [] ii") as (iκs') "[ii iiback]".
      { iApply (guards_transitive with "fGuardsL Lguardsϝ'"). }
      { iApply (guards_transitive with "fGuardsL LguardsIl"). }
    iApply ("e" with "LFT TIME PROPH UNIQ Efp [ϝ] ii [ToG k iiback] ityl Obs").
    { iSplitL; [|done]. iExists _. iSplit; [by rewrite/= left_id|]. by iFrame "ϝ". }
    rewrite cctx_interp_singleton. iIntros (v' [b []] mask'). inv_vec v'=> v'.
    iIntros "[(%& %Eq & ϝ &_) _] Invctx [oty ?] Obs". rewrite/= left_id in Eq.
    rewrite -Eq. wp_rec. wp_bind Skip.
    iDestruct "ϝnonempty" as "%To".
    iDestruct (llftl_end' with "LFT ϝ") as "†ϝ"; first by trivial.
    iApply (wp_mask_mono _ (↑Nllft)); [done|].
    iApply (wp_step_fupd with "†ϝ"); [set_solver|]. wp_seq. iIntros "†ϝ !>".
    wp_seq. iMod ("ToG" with "†ϝ") as "> G".
    iDestruct ("iiback" with "Invctx") as "Invctx".
    iApply ("k" with "G Invctx oty Obs").
  Qed.

  (** A call from a thread with an empty lifetime context and no open invariants (as in a
      new thread, see [typing/spawn.v]). *)
  Lemma type_call_iris {A 𝔄l 𝔅 ℭ} x xl κl post (mask: Mask) (fp: A → fn_params 𝔄l 𝔅)
      (spec: fn_spec 𝔄l 𝔅 ℭ) p ql ql' (k: expr) E efun tid G :
    AsVal k → IntoPlistc ql ql' → Timeless G →
    (∀ϝ, elctx_sat (map (λ κ, ϝ ⊑ₑ κ) κl ++ E) [] (fp_E (fp x) ϝ)) →
    llft_ctx -∗ time_ctx -∗ proph_ctx -∗ uniq_ctx -∗ elctx_interp E -∗
    (G &&{↑NllftG}&&> @[lft_intersect_list κl]) -∗ G -∗
    invctx_interp tid mask [] (InvCtx [] static (fp_atomic_state (fp x))) -∗
    tctx_elt_interp tid (p ◁ᶠ fn fp spec) efun -∗
    tctx_interp tid (hzip_with (λ _ ty q, q ◁ᵥ ty) (fp x).(fp_ityl) ql') xl -∗
    ⟨π, (spec efun.2) post xl mask π⟩ -∗
    (∀(ret: val) (mask': Mask) w, G -∗
      invctx_interp tid mask' [] (InvCtx [] static (fp_atomic_state (fp x))) -∗
      tctx_elt_interp tid (ret ◁ᵥ (fp x).(fp_oty)) w -∗ ⟨π, post w mask' π⟩ -∗
      WP k [of_val ret] {{ _, cont_postcondition }}) -∗
    WP (call: p ql → k) {{ _, cont_postcondition }}.
  Proof.
    iIntros (????) "LFT TIME PROPH UNIQ E #Guardsκl G Invctx p ql Obs k".
    iApply (type_call_iris' [] with "LFT TIME PROPH UNIQ E [] Guardsκl G Invctx p ql Obs").
      - split.
        + unfold lctx_lft_alive. iIntros "_ _". setoid_rewrite static_alive_true.
          iApply guards_true.
        + intros κ Hnotin. simpl in Hnotin. rewrite elem_of_nil in Hnotin. contradiction.
      - done.
      - iApply guards_true.
      - iIntros (???) "G I ret Obs". iApply ("k" with "G I ret Obs").
  Qed.

  Lemma type_call {A 𝔄l 𝔅 ℭl 𝔇l 𝔈l 𝔉 ℭ} x (fp: A → fn_params 𝔄l 𝔅) (spec: fn_spec 𝔄l 𝔅 ℭ)
      p ql ql' k trx trk tri E L (C: cctx 𝔉) Il ϝ' (T: tctx ℭl) (T': tctx 𝔇l)
      (Tk: vec val 1 → tctx 𝔈l) :
    IntoPlistc ql ql' → Forall (lctx_lft_alive E L) L.*1 →
    lctx_ictx_alive E L (InvCtx Il ϝ' (fp_atomic_state (fp x))) →
    tctx_extract_ctx E L (p ◁ᶠ fn fp spec +::
      hzip_with (λ _ ty q, q ◁ᵥ ty) (fp x).(fp_ityl) ql') T T' trx →
    (∀ϝ, elctx_sat (map (λ κ, ϝ ⊑ₑ κ) L.*1 ++ E) L (fp_E (fp x) ϝ)) →
    k ◁cont{L, (InvCtx Il ϝ' (fp_atomic_state (fp x))), Tk} trk ∈ C →
    (∀ret: val, tctx_incl E L (ret ◁ᵥ (fp x).(fp_oty) +:: T') (Tk [#ret]) tri) →
    ⊢ typed_body E L (InvCtx Il ϝ' (fp_atomic_state (fp x))) C T (call: p ql → k) (trx ∘
      (λ post '(trp -:: adl), λ mask π,
      let '(al, dl) := psep adl in
        (spec trp.2) (λ (b: ~~ 𝔅) mask π, tri (trk post) (b -:: dl) mask π) al mask π)).
  Proof.
    move=> ? Alv ???? InTk. iApply typed_body_tctx_incl; [done|].
    iIntros (?[? adπl]mask post iκs). move: (papp_ex adπl)=> [aπl[dπl->]].
    iIntros "#LFT TIME #PROPH #UNIQ #E L I C /=(p & ql & T') Obs".
    iDestruct (lctx_lft_alive_tok_list with "L E") as "#Alv"; [done|].
    iApply (type_call_iris' with "LFT TIME PROPH UNIQ E [] Alv L I p ql [Obs]"); [done|done|..].
    { iApply guards_refl. }
    { iApply proph_obs_eq; [|done]=>/= ?. by rewrite papp_sepl papp_sepr. }
    iIntros (ret mask' ?) "L I ret Obs".
    iMod (proj2 (InTk _) _ _ (_-::_) with "LFT PROPH UNIQ E [] L [$ret $T'] Obs")
      as (?) "(L & Tk & Obs)". { iApply guards_refl. }
    have ->: [ret: expr] = map of_val ([#ret]) by done.
    iApply ("C" with "[%//] L I Tk Obs").
  Qed.

  Lemma type_letcall {A 𝔄l 𝔅 ℭ ℭl 𝔇l 𝔈} x (fp: A → fn_params 𝔄l 𝔅) (spec: fn_spec 𝔄l 𝔅 ℭ)
      p ql ql' Il ϝ' (T: tctx ℭl) (T': tctx 𝔇l) b e trx tr E L (C: cctx 𝔈)
      `{!IntoPlistc ql ql', !Closed (b :b: []) e, !Closed [] p} :
    TCForall (Closed []) ql → Forall (lctx_lft_alive E L) L.*1 →
    lctx_ictx_alive E L (InvCtx Il ϝ' (fp_atomic_state (fp x))) →
    tctx_extract_ctx E L (p ◁ᶠ fn fp spec +::
      hzip_with (λ _ ty q, q ◁ᵥ ty) (fp x).(fp_ityl) ql') T T' trx →
    (∀ϝ, elctx_sat (map (λ κ, ϝ ⊑ₑ κ) L.*1 ++ E) L (fp_E (fp x) ϝ)) →
    (∀ret: val, typed_body E L (InvCtx Il ϝ' (fp_atomic_state (fp x))) C
      (ret ◁ᵥ (fp x).(fp_oty) +:: T') (subst' b ret e) tr) -∗
    typed_body E L (InvCtx Il ϝ' (fp_atomic_state (fp x))) C T (letcall: b := p ql in e)
      (trx ∘ (λ post '(trp -:: adl) mask π,
        let '(al, dl) := psep adl in (spec trp.2) (λ b mask π, tr post (b -:: dl) mask π) al mask π)).
  Proof.
    move=> Clql ????. iIntros "e". iApply type_cont_norec.
    - eapply is_closed_weaken; [done|]. set_solver+.
    - rewrite /Closed /= !andb_True. split.
      + by eapply is_closed_weaken, list_subseteq_nil.
      + eapply Is_true_eq_left, forallb_forall, List.Forall_forall, Forall_impl;
        [by apply TCForall_Forall|]=> ??.
        eapply Is_true_eq_true, is_closed_weaken=>//. set_solver+.
    - iIntros (k).
      have ->: subst' "_k" k (call: p ql → "_k")%E = subst "_k" k p $
        (λ: ["_r"], Skip;; k ["_r"])%E :: map (subst "_k" k) ql by done.
      rewrite is_closed_nil_subst; [|done].
      have ->: map (subst "_k" k) ql = ql.
      { clear -Clql. elim Clql; [done|]=>/= ????->. by rewrite is_closed_nil_subst. }
      iApply typed_body_proper; last first.
      { iApply type_call=>//; [constructor|]=> v.
        have {1}->: v = vhd [#v] by done. move: [#v]=> ?. apply tctx_incl_refl. }
      done.
    - iIntros (? ret). inv_vec ret=> ret. rewrite /subst_v /=.
      rewrite (is_closed_subst []); [| |set_solver+]; last first.
      { apply subst'_is_closed; [|done]. apply is_closed_of_val. }
      iApply "e".
  Qed.

  Lemma type_fnrec {A 𝔄l 𝔅 ℭ} tr (fp: A → fn_params 𝔄l 𝔅) (spec: fn_spec 𝔄l 𝔅 ℭ) fb e bl bl'
      `{Into: !IntoPlistc bl bl', Cl: !Closed (fb :b: ("return" :: bl)%binder +b+ []) e} :
    (∀x ϝ (f: val) k (wl: plistc _ 𝔄l),
        ⊢ typed_body (fp_E (fp x) ϝ) [ϝ ⊑ₗ []] (InvCtx [] ϝ (fp_atomic_state (fp x)))
            [k ◁cont{[ϝ ⊑ₗ []], (InvCtx [] ϝ (fp_atomic_state (fp x))),
              λ v: vec _ 1, +[vhd v ◁ᵥ (fp x).(fp_oty)] } tr_ret]
            (f ◁ᶠ fn fp spec +:: hzip_with (λ _ ty (v: val), v ◁ᵥ ty) (fp x).(fp_ityl) wl)
            (subst' fb f $ subst "return" k $ subst_plv bl' wl e)
            (λ post '(tr' -:: al), λ mask π, tr'.2 = tr ∧ (spec tr) post al mask π)%type) →
    typed_val (fnrec: fb bl := e)%V (fn fp spec) (@RecV fb ("return" :: bl)%binder e Cl, tr).
  Proof.
    move: Cl. rewrite Into. iIntros (? Body ????????) "_ _ _ _ _ $$ _ Obs".
    iMod persistent_time_receipt_0 as "#⧖". iApply wp_value.
    iExists -[((@RecV fb ("return" :: bl')%binder e Cl)%V, tr)].
    iFrame "Obs". iSplit; [|done]. iLöb as "IH". iExists _.
    iSplit; [by rewrite/= decide_True_pi|]. iExists 0%nat. iSplit; [done|]. iFrame "⧖".
    iExists fb, "return", bl', e, _. iSplit; [done|].
    iIntros "!>!> *%%%%% LFT TIME PROPH UNIQ Efp L I C T ?".
    iApply (Body _ _ (RecV _ _ _) $! _ (_-::_) with
        "LFT TIME PROPH UNIQ Efp L I C [T IH]").
    { iSplit; last by iFrame "T". iApply "IH". }
    by iApply proph_obs_impl; [|done]=>/= ??.
  Qed.

  Lemma type_fn {A 𝔄l 𝔅 ℭ} tr (fp: A → fn_params 𝔄l 𝔅) (spec: fn_spec 𝔄l 𝔅 ℭ) e bl bl'
      `{!IntoPlistc bl bl', !Closed ("return" :: bl +b+ []) e} :
    (∀x ϝ k (wl: plistc _ 𝔄l),
        ⊢ typed_body (fp_E (fp x) ϝ) [ϝ ⊑ₗ []] (InvCtx [] ϝ (fp_atomic_state (fp x)))
            [k ◁cont{[ϝ ⊑ₗ []], (InvCtx [] ϝ (fp_atomic_state (fp x))),
              λ v: vec _ 1, +[vhd v ◁ᵥ (fp x).(fp_oty)] } tr_ret]
            (hzip_with (λ _ ty (v: val), v ◁ᵥ ty) (fp x).(fp_ityl) wl)
            (subst "return" k $ subst_plv bl' wl e) (spec tr)) →
    typed_val (fn: bl := e)%V (fn fp spec) (RecV <> ("return" :: bl)%binder e, tr).
  Proof.
    move=> Body.
    eapply type_fnrec; [apply _|]=> *.
    iApply typed_body_impl; last first.
    { iApply typed_body_tctx_incl; [|iApply Body]. apply tctx_incl_resolve_head. }
    by move=>/= ?[??]??[_ ?].
  Qed.
End typing.

Global Hint Resolve fn_resolve : lrust_typing.
