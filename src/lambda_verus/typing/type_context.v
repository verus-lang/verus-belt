From iris.proofmode Require Import proofmode.
From lrust.typing Require Import type lft_contexts.
From lrust.lifetime Require Import lifetime_full.
From guarding Require Import guard tactics.
Set Default Proof Using "Type".

Implicit Type (𝔄 𝔅 ℭ: syn_type) (𝔄l 𝔅l ℭl 𝔇l: syn_typel).

Definition path := expr.
Bind Scope expr_scope with path.

Inductive blocked_type `{!typeG Σ} : syn_type → Type :=
  blocked_type_ctor (𝔄₀: syn_type) (ty: type 𝔄₀) : blocked_type (blockedₛ 𝔄₀).

Definition blocked_type_elim `{!typeG Σ} {𝔄 T} (bty: blocked_type 𝔄) (x: ~~ 𝔄)
    (f: ∀ (𝔄₀ : syn_type) , type 𝔄₀ → ~~ (blockedₛ 𝔄₀) → T)
    : T :=
  match bty in (blocked_type s) return (~~ s → T) with
  | blocked_type_ctor 𝔄₀ ty => f 𝔄₀ ty
  end x.
  
Inductive tctx_elt `{!typeG Σ} 𝔄 : Type :=
| TCtx_hasty (p: path) (ty: type 𝔄)
| TCtx_blocked (p: path) (κ: lft) (ty: blocked_type 𝔄).

Notation tctx := (hlist tctx_elt).

Notation "p ◁ ty" := (TCtx_hasty _ p ty%T) (at level 55).
Notation "p ◁{ κ } ty" := (TCtx_blocked _ p κ ty%T)
   (at level 55, format "p  ◁{ κ }  ty").

(* [pred] is used by [Nat] *)
Notation pred' A := (A → Mask → proph_asn → Prop) (only parsing).
Notation predl 𝔄l := (pred' (plist indep_interp_of_syn_type 𝔄l)).
Notation predl_trans 𝔄l 𝔅l := (predl 𝔅l → predl 𝔄l).
Notation predl_trans' 𝔄l 𝔅 := (pred' (~~𝔅) → predl 𝔄l).

Global Instance pred'_equiv A : Equiv (pred' A) :=
  pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (↔))).
Global Instance predl_trans_equiv 𝔄l 𝔅l : Equiv (predl_trans 𝔄l 𝔅l) :=
  pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (↔)))).
Global Instance predl_trans'_equiv 𝔄l 𝔅 : Equiv (predl_trans' 𝔄l 𝔅) :=
  pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (↔)))).

(*Notation predₛ 𝔄 := (funₛ 𝔄 (funₛ maskₛ (funₛ proph_asnₛ Propₛ)))%ST.
Notation predlₛ 𝔄l := (predₛ (Π! 𝔄l))%ST.
Notation predl_trans'ₛ 𝔄l 𝔅 := (funₛ (predₛ 𝔅) (predlₛ 𝔄l))%ST.*)

Definition trans_app {𝔄l 𝔅l ℭl 𝔇l} (tr: predl_trans 𝔄l 𝔅l) (tr': predl_trans ℭl 𝔇l)
  : predl_trans (𝔄l ++ ℭl) (𝔅l ++ 𝔇l) := λ post acl π,
  let '(al, cl) := psep acl in tr (λ bl π, tr' (λ dl π, post (bl -++ dl) π) cl π) al π.

Global Instance trans_app_proper {𝔄l 𝔅l ℭl 𝔇l} tr tr' :
  Proper ((≡) ==> (≡)) tr →
  Proper ((≡) ==> (≡)) tr' →
  Proper ((≡) ==> (≡)) (@trans_app 𝔄l 𝔅l ℭl 𝔇l tr tr').
Proof. intros Htr Htr' ????. unfold trans_app. apply Htr=>?. apply Htr'=>? //. Qed.

Definition trans_lower {𝔄l 𝔅l ℭl} (tr: predl_trans 𝔄l 𝔅l)
  : predl_trans (ℭl ++ 𝔄l) (ℭl ++ 𝔅l) := λ post cal,
  let '(cl, al) := psep cal in tr (λ bl, post (cl -++ bl)) al.

Definition trans_upper {𝔄l 𝔅l ℭl} (tr: predl_trans 𝔄l 𝔅l)
  : predl_trans (𝔄l ++ ℭl) (𝔅l ++ ℭl) := λ post acl,
  let '(al, cl) := psep acl in tr (λ bl, post (bl -++ cl)) al.

Definition trans_tail {ℭ 𝔄l 𝔅l} (tr: predl_trans 𝔄l 𝔅l)
  : predl_trans (ℭ :: 𝔄l) (ℭ :: 𝔅l) :=
  λ post '(c -:: al), tr (λ bl, post (c -:: bl)) al.

Section type_context.
  Context `{!typeG Σ}.

  Fixpoint eval_path (p: path) : option val := match p with
    | BinOp OffsetOp e (#(LitInt n))%E => match eval_path e with
        Some #(LitLoc l) => Some #(l +ₗ n) | _ => None end
    | e => to_val e end.

  Lemma eval_path_of_val (v: val) : eval_path v = Some v.
  Proof. case v; [done|]=>/= *. by rewrite (decide_True_pi _). Qed.

  Lemma wp_eval_path E p v :
    eval_path p = Some v → ⊢ WP p @ E {{ v', ⌜v' = v⌝ }}.
  Proof.
    move: v. elim: p=>//.
    - move=> > [= ?]. by iApply wp_value.
    - move=> > ?? /of_to_val ?. by iApply wp_value.
    - case=>// e Wp. case=>//. case=>//= ?. move: Wp.
      case (eval_path e)=>//. case=>//. case=>// ? Wp _ ?[=<-].
      wp_bind e. iApply wp_wand; [by iApply Wp|]. iIntros. subst. by wp_op.
  Qed.

  Lemma eval_path_closed p v : eval_path p = Some v → Closed [] p.
  Proof.
    move: v. elim p=>//.
    - move=> >. rewrite /eval_path=> /of_to_val <-. apply is_closed_of_val.
    - case=>// e IH. case=>//. case=>//= ? _. move: IH. case (eval_path e)=>//.
      case=>//. case=>// ? IH ? _. move: (IH _ eq_refl). apply _.
  Qed.

  (** Type Context Element Interpretation *)
  Definition tctx_elt_interp {𝔄} (tid: thread_id) (t: tctx_elt 𝔄) (x: ~~ 𝔄)
    : iProp Σ := match t with
    | p ◁ ty => ∃v d, ⌜eval_path p = Some v⌝ ∗ ⧖d ∗ ty_own ty x d d tid [FVal v]
    | p ◁{κ} bty => blocked_type_elim bty x (λ 𝔄₀ ty x₀ ,
      ∃v, ⌜eval_path p = Some v⌝ ∗
        ([†κ] ={⊤}=∗ ∃x' d, ▷(blockedπ x₀ :== @vπ 𝔄₀ x') ∗ ⧖d ∗ ⧗1 ∗ (ty_own ty x' d d tid [FVal v]))
      ) 
     end%I.

  (* Block tctx_elt_interp from reducing with simpl when t is a constructor. *)
  Global Arguments tctx_elt_interp : simpl never.
End type_context.

(** Type Context Interpretation *)
Notation tctx_interp tid :=
  (big_sepHL_1 (λ 𝔄 t x, tctx_elt_interp (𝔄:=𝔄) tid t x)).

Section lemmas.
  Context `{!typeG Σ}.
  
  Lemma tctx_hasty_val {𝔄} (v: val) (ty: type 𝔄) vπ tid :
    tctx_elt_interp tid (v ◁ ty) vπ ⊣⊢ ∃d, ⧖d ∗ ty_own ty vπ d d tid [FVal v].
  Proof.
    rewrite /tctx_elt_interp eval_path_of_val. iSplit.
    - iIntros "H". iDestruct "H" as (??[=->]) "[??]". iExists _. iFrame.
    - iDestruct 1 as (d) "[??]". iExists _, _. by iFrame.
  Qed.

  Lemma tctx_elt_interp_hasty_path {𝔄} p1 p2 (ty: type 𝔄) tid vπ :
    eval_path p1 = eval_path p2 →
    tctx_elt_interp tid (p1 ◁ ty) vπ ⊣⊢ tctx_elt_interp tid (p2 ◁ ty) vπ.
  Proof. move=> Hp. rewrite /tctx_elt_interp. by setoid_rewrite Hp. Qed.

  Lemma tctx_hasty_val' {𝔄} tid p v (ty: type 𝔄) vπ:
    Some v = eval_path p →
    tctx_elt_interp tid (p ◁ ty) vπ ⊣⊢ ∃d, ⧖d ∗ ty_own ty vπ d d tid [FVal v].
  Proof.
    move=> ?. rewrite -tctx_hasty_val. apply tctx_elt_interp_hasty_path.
    by rewrite eval_path_of_val.
  Qed.

  Lemma wp_hasty {𝔄} E tid p (ty: type 𝔄) vπ Φ :
    tctx_elt_interp tid (p ◁ ty) vπ -∗
    (∀v d, ⌜Some v = eval_path p⌝ -∗ ⧖d -∗ ty_own ty vπ d d tid [FVal v] -∗ Φ v) -∗
    WP p @ E {{ Φ }}.
  Proof.
    iIntros "(%&%&%&#?&?) ToΦ". iApply (wp_wand with "[]"); [by iApply wp_eval_path|].
    iIntros (?->). by iApply "ToΦ".
  Qed.

  Lemma closed_hasty {𝔄} tid p (ty: type 𝔄) vπ :
    tctx_elt_interp tid (p ◁ ty) vπ -∗ ⌜Closed [] p⌝.
  Proof. iIntros "(%&%&%&_)!%". by eapply eval_path_closed. Qed.

  (** resolveing a Type Context *)

  Definition resolve_tctx {𝔄l} (E: elctx) (L: llctx) (T: tctx 𝔄l)
    (Φ: plist indep_interp_of_syn_type 𝔄l → proph_asn → Prop → Prop) : Prop :=
    ∀G F tid xl, Timeless G → ↑Nllft ∪ ↑prophN ∪ ↑timeN ∪ ↑uniqN ⊆ F → llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ time_ctx -∗
      elctx_interp E -∗ (G &&{↑NllftG}&&> llctx_interp L) -∗ G -∗ tctx_interp tid T xl ={F}=∗
        ∃d, ⧖d ∗ |={F}▷=>^(d*(d+1)) |={F}=>
          ⟨ π , ∀φ, Φ xl π φ → φ ⟩ ∗ G.
          (*⟨π, ∀φ, Φ (xl -$ π) φ → φ⟩ ∗ G.*)

  Lemma resolve_tctx_just {𝔄l} E L (T: tctx 𝔄l) : resolve_tctx E L T (const (const id)).
  Proof.
    move=> *. iMod persistent_time_receipt_0 as "⧖". iIntros "_ _ _ _ _ _ $ _!>". iExists _.
    iFrame "⧖". iApply step_fupdN_full_intro. 
    iModIntro. iApply proph_obs_true. done.
  Qed.

  Lemma resolve_tctx_nil E L : resolve_tctx E L +[] (const (const id)).
  Proof. apply resolve_tctx_just. Qed.
  
  Lemma lemma_max_mul (d d0: nat) :
    (d `max` d0) * ((d `max` d0) + 1) = (d * (d+1)) `max` (d0 * (d0+1)).
  Proof. nia. Qed.

  Lemma resolve_tctx_cons_hasty {𝔄 𝔅l} E L p (ty: type 𝔄) Φ (T: tctx 𝔅l) Ψ :
    resolve E L ty Φ → resolve_tctx E L T Ψ →
    resolve_tctx E L (p ◁ ty +:: T) (λ '(a -:: bl) π φ, Φ a π → Ψ bl π φ).
  Proof.
    iIntros (Rslv Rslv' ???[??]??).
    iIntros "#LFT #PROPH #UNIQ #TIME #E #L G /=[(%&%&_& ⧖ & A) T]".
    iDestruct "A" as "[ty #phys]".
    iMod (fractional.frac_split_guard_in_half NllftG with "G L")
        as (γ) "[F1 [F2 [#guards #back]]]". { solve_ndisj. }
    iMod (Rslv with "LFT PROPH UNIQ TIME E guards F1 ty") as "ToObs"; [set_solver|].
    iMod (Rslv' with "LFT PROPH UNIQ TIME E guards F2 T") as (?) "[⧖' ToObs']"; [done|].
    iCombine "⧖ ⧖'" as "⧖". iCombine "ToObs ToObs'" as "ToObs".
    iModIntro. iExists _. iFrame "⧖".
    rewrite lemma_max_mul.
    iApply (step_fupdN_wand with "ToObs").
    iIntros "[>[Obs F1] >[Obs' F2]]".
    iDestruct ("back" with "F1 F2") as "G". iMod (fupd_mask_mono with "G") as "G". { solve_ndisj. }
    iCombine "Obs Obs'" as "?".
    iModIntro. iFrame "G".
    iApply proph_obs_impl; [|done]=>/= ?[? Imp]? Imp'. apply Imp, Imp'. trivial.
  Qed.

  Lemma resolve_tctx_cons_just {𝔄 𝔅l} E L (t: tctx_elt 𝔄) (T: tctx 𝔅l) Φ :
    resolve_tctx E L T Φ → resolve_tctx E L (t +:: T) (λ '(_ -:: bl), Φ bl).
  Proof.
    iIntros (Rslv ???[??]??) "LFT PROPH UNIQ TIME E L G /=[_ T]".
    by iApply (Rslv with "LFT PROPH UNIQ TIME E L G T").
  Qed.

  Lemma resolve_tctx_cons_just_hasty {𝔄 𝔅l} E L p (ty: type 𝔄) (T: tctx 𝔅l) Φ :
    resolve E L ty (const (const True)) → resolve_tctx E L T Φ →
    resolve_tctx E L (p ◁ ty +:: T) (λ '(_ -:: bl), Φ bl).
  Proof. move=> ?. apply resolve_tctx_cons_just. Qed.

  Lemma resolve_tctx_cons_just_blocked {𝔄 𝔅l} E L p κ (ty: type 𝔄) (T: tctx 𝔅l) Φ :
    resolve_tctx E L T Φ → resolve_tctx E L (p ◁{κ} (blocked_type_ctor 𝔄 ty) +:: T) (λ '(_ -:: bl), Φ bl).
  Proof. apply resolve_tctx_cons_just. Qed.

  (** Type Context Inclusion *)

  Definition tctx_incl {𝔄l 𝔅l} (E: elctx) (L: llctx) (T: tctx 𝔄l) (T': tctx 𝔅l)
    (tr: predl_trans 𝔄l 𝔅l) : Prop :=
    Proper ((≡) ==> (≡)) tr ∧
    ∀G tid xl mask post, Timeless G →
      llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ elctx_interp E -∗
      (G &&{↑NllftG}&&> llctx_interp L) -∗ G -∗
      tctx_interp tid T xl -∗ ⟨π, tr post xl mask π⟩
      ={⊤}=∗
      ∃xl', G ∗ tctx_interp tid T' xl' ∗ ⟨π, post xl' mask π⟩.

  Lemma tctx_incl_impl {𝔄l 𝔅l} (T: tctx 𝔄l) (T': tctx 𝔅l)
                       (tr tr': predl_trans 𝔄l 𝔅l) E L :
    tctx_incl E L T T' tr' → (∀post xl mask π, tr post xl mask π → tr' post xl mask π) →
    Proper ((≡) ==> (≡)) tr →
    tctx_incl E L T T' tr.
  Proof.
    move=> [? In] Imp. split; [done|].
    iIntros (??????) "LFT PROPH UNIQ E #L G T #Obs".
    iMod (In with "LFT PROPH UNIQ E L G T []") as "$"; [|done].
    iApply proph_obs_impl; [|done]=>/= ?. apply Imp.
  Qed.

  Lemma tctx_incl_ext {𝔄l 𝔅l} (T: tctx 𝔄l) (T': tctx 𝔅l) tr tr' E L :
    tctx_incl E L T T' tr' → (∀post xl mask π, tr post xl mask π ↔ tr' post xl mask π) →
    tctx_incl E L T T' tr.
  Proof.
    move=> In Eq. eapply tctx_incl_impl; [done| |].
    - move=> ????. by rewrite Eq.
    - move=> ??????. rewrite !Eq. by apply In.
 Qed.

  Lemma tctx_incl_refl {𝔄l} (T: tctx 𝔄l) E L : tctx_incl E L T T id.
  Proof. split; [by apply _|]. move=> ?? vπl ?. iIntros. iExists vπl. by iFrame. Qed.

  Lemma tctx_incl_trans {𝔄l 𝔅l ℭl} tr tr' (T1: tctx 𝔄l) (T2: tctx 𝔅l) (T3: tctx ℭl) E L :
    tctx_incl E L T1 T2 tr → tctx_incl E L T2 T3 tr' → tctx_incl E L T1 T3 (tr ∘ tr').
  Proof.
    move=> In In'. split.
    { eapply compose_proper; [apply In|apply In']. }
    iIntros "*". iIntros (timelessG). iIntros "#LFT #PROPH #UNIQ #E #L G T Obs".
    destruct In as [? In]. destruct In' as [? In'].
    iMod (In with "LFT PROPH UNIQ E L G T Obs") as (?) "(G & T & Obs)".
    iMod (In' with "LFT PROPH UNIQ E L G T Obs") as (vπl'') "(?&?&?)".
    iExists vπl''. by iFrame.
  Qed.

  Lemma tctx_incl_app {𝔄l 𝔅l ℭl 𝔇l}
    (T1: tctx 𝔄l) (T1': tctx 𝔅l) (T2: tctx ℭl) (T2': tctx 𝔇l) tr tr' E L :
    tctx_incl E L T1 T1' tr → tctx_incl E L T2 T2' tr' →
    tctx_incl E L (T1 h++ T2) (T1' h++ T2') (trans_app tr tr').
  Proof.
    move=> [? In1] [? In2]. split; [apply _|].
    move=>?? vπl ??. move: (papp_ex vπl)=> [?[?->]].
    iIntros (timelessG) "#LFT #PROPH #UNIQ #E #L G [T1 T2] Obs".
    iMod (In1 with "LFT PROPH UNIQ E L G T1 [Obs]") as (wπl) "(G & T1' & Obs)".
    { iApply proph_obs_eq; [|done]=> ?.
      rewrite /trans_app.
      (* rewrite papply_app *)
      rewrite papp_sepl.
      rewrite papp_sepr.
      done. }
    iMod (In2 with "LFT PROPH UNIQ E L G T2 Obs") as (wπl') "(G & T2' &?)".
    iExists (wπl -++ wπl'). iFrame "G T1' T2'".
    iApply proph_obs_eq; [|done]=>/= ?. (*by rewrite papply_app.*) done.
  Qed.

  Lemma tctx_incl_frame_l {𝔄l 𝔅l ℭl} (T: tctx 𝔄l) (T': tctx 𝔅l) (Tf: tctx ℭl) tr E L :
    tctx_incl E L T T' tr → tctx_incl E L (Tf h++ T) (Tf h++ T') (trans_lower tr).
  Proof.
    move=> ?. eapply tctx_incl_ext.
    { apply tctx_incl_app; [|done]. apply tctx_incl_refl. }
    done.
  Qed.
  Lemma tctx_incl_frame_r {𝔄l 𝔅l ℭl} (T: tctx 𝔄l) (T': tctx 𝔅l) (Tf: tctx ℭl) tr E L :
    tctx_incl E L T T' tr → tctx_incl E L (T h++ Tf) (T' h++ Tf) (trans_upper tr).
  Proof.
    move=> ?. eapply tctx_incl_ext.
    { apply tctx_incl_app; [done|]. apply tctx_incl_refl. }
    done.
  Qed.
  Lemma tctx_incl_tail {𝔄 𝔄l 𝔅l} (t: tctx_elt 𝔄) (T1: tctx 𝔄l) (T2: tctx 𝔅l) tr E L :
    tctx_incl E L T1 T2 tr → tctx_incl E L (t +:: T1) (t +:: T2) (trans_tail tr).
  Proof.
    move=> ?. eapply tctx_incl_ext. { by apply (tctx_incl_frame_l _ _ +[_]). }
    by move=> ?[??].
  Qed.

  Lemma tctx_incl_swap {𝔄 𝔅 𝔄l} (t: tctx_elt 𝔄) (t': tctx_elt 𝔅) (T: tctx 𝔄l) E L :
    tctx_incl E L (t +:: t' +:: T) (t' +:: t +:: T)
      (λ post '(a -:: b -:: al), post (b -:: a -:: al)).
  Proof.
    split; [by intros ??? [? [? ?]]|].
    iIntros (??(vπ & vπ' & wπl)???) "_ _ _ _ _ $ (?&?&?) ?!>".
    iExists (vπ' -:: vπ -:: wπl). iFrame.
  Qed.

  Lemma tctx_incl_resolve_head {𝔄 𝔅l} (t: tctx_elt 𝔄) (T: tctx 𝔅l) E L :
    tctx_incl E L (t +:: T) T (λ post '(_ -:: bl), post bl).
  Proof.
    split; [by intros ??? [? ?]|].
    iIntros (??[??]???) "_ _ _ _ _ $ [_ T] ? !>". iExists _. by iFrame "T".
  Qed.

  Lemma tctx_incl_resolve_lower {𝔄l 𝔅l} (T: tctx 𝔄l) (T': tctx 𝔅l) E L :
    tctx_incl E L (T h++ T') T (λ post abl, post (psepl abl)).
  Proof.
    split; [by intros ????|].
    move=> ?? abπl ??. move: (papp_ex abπl)=> [aπl[?->]].
    iIntros "_ _ _ _ _ _ $ [T _] ? !>". iExists aπl. iFrame "T".
    iApply proph_obs_eq; [|done]=> ?. by rewrite/= papp_sepl.
  Qed.

  Definition tctx_equiv {𝔄l} (T T': tctx 𝔄l) : Prop :=
    ∀E L, tctx_incl E L T T' id ∧ tctx_incl E L T' T id.

  Lemma get_tctx_equiv {𝔄l} (T T': tctx 𝔄l) :
    (∀tid vπl, tctx_interp tid T vπl ⊣⊢ tctx_interp tid T' vπl) → tctx_equiv T T'.
  Proof.
    move=> Eq ??; split; (split; [apply _|]);
      iIntros (??????) "_ _ _ _ _ $ T Obs !>"; iExists _; rewrite Eq; iFrame.
  Qed.

  Lemma copy_tctx_incl {𝔄 𝔄l} (ty: type 𝔄) `{!Copy ty} (T: tctx 𝔄l) p E L :
    tctx_incl E L (p ◁ ty +:: T) (p ◁ ty +:: p ◁ ty +:: T)
      (λ post '(a -:: al), post (a -:: a -:: al)).
  Proof.
    split; [by intros ??? [??]|].
    iIntros (??[vπ wπl]???) "_ _ _ _ _ $ /=[#? T] Obs !>".
    iExists (vπ -:: vπ -:: wπl). iFrame "Obs T". by iSplit.
  Qed.

  Lemma tctx_to_shift_loc_0 {𝔄 𝔅l} (ty: type 𝔄) p (T: tctx 𝔅l) E L :
    JustLoc ty → tctx_incl E L (p ◁ ty +:: T) (p +ₗ #0 ◁ ty +:: T) id.
  Proof.
    intros JLoc. split; [apply _|].
    - iIntros (??[??]???) "_ _ _ _ _ $ /=[(%&%& %Ev & ⧖ & A) T] Obs !>".
      iDestruct "A" as "[ty %phys1]".
      iExists (_-::_). iDestruct (JLoc with "ty") as (l) "%phys2".
      iFrame "T Obs". iExists v, _. iFrame "⧖ ty". iSplit.
      { iPureIntro. rewrite/= Ev.
        assert (v = #l) as Hvl. { rewrite phys1 in phys2. inversion phys2. trivial. }
        subst v. by rewrite/= shift_loc_0.
      } { iPureIntro. trivial. }
  Qed.

  Lemma tctx_of_shift_loc_0 {𝔄 𝔅l} (ty: type 𝔄) p (T: tctx 𝔅l) E L :
    tctx_incl E L (p +ₗ #0 ◁ ty +:: T) (p ◁ ty +:: T) id.
  Proof.
    split; [apply _|]. iIntros (??[??]???) "_ _ _ _ _ $ /=[(%&%& %Ev & ⧖ty) T] Obs !>".
    iExists (_-::_). iFrame "T Obs". iExists _, _. iFrame "⧖ty". iPureIntro.
    move: Ev=>/=. case (eval_path p)=>//. (do 2 case=>//)=> ?. by rewrite shift_loc_0.
  Qed.

  Lemma tctx_shift_loc_assoc {𝔄 𝔅l} (ty: type 𝔄) p (T: tctx 𝔅l) (z z': Z) :
    tctx_equiv (p +ₗ #z +ₗ #z' ◁ ty +:: T) (p +ₗ #(z + z') ◁ ty +:: T).
  Proof.
    apply get_tctx_equiv=>/= ?[??]. f_equiv.
    rewrite tctx_elt_interp_hasty_path; [done|]=>/=. case (eval_path p)=>//.
    (do 2 case=>//)=> ?. by rewrite shift_loc_assoc.
  Qed.

  Lemma subtype_tctx_incl {𝔄 𝔅 𝔄l} ty ty' (f: 𝔄 →ₛ 𝔅) (T: tctx 𝔄l) p E L :
    subtype E L ty ty' f →
    tctx_incl E L (p ◁ ty +:: T) (p ◁ ty' +:: T)
      (λ post '(a -:: al), post (f ~~$ₛ a -:: al)).
  Proof.
    intros Sub. split; [by intros ??? [??]|].
    iIntros (??[x wπl]???) "#LFT _ _ E #L G /=[(%v & %d &%&?& A) T] Obs /=".
    iDestruct "A" as "[ty %phys]".
    leaf_open "L" with "G" as "[L1 back]". { set_solver. }
    iDestruct (Sub with "L1 E") as "#(_ & _ & #InOwn & #InOwnPers & %InPhys & _)".
    iMod ("back" with "L1") as "G".
    iModIntro.
    iExists (f ~~$ₛ x -:: wπl). iFrame "G T".
    iSplitR "Obs".
    - iExists v, d. do 2 (iSplit; [done|]).
      iDestruct ("InOwn" with "ty") as "[ty1 _]".
      iFrame.
      iPureIntro. rewrite <- InPhys. trivial.
    - iApply (proph_obs_impl with "Obs"). intros. done.
  Qed.

  (* Extracting from a type context. *)

  Definition tctx_extract_elt {𝔄 𝔄l 𝔅l} E L (t: tctx_elt 𝔄)
    (T: tctx 𝔄l) (T': tctx 𝔅l) (tr: predl_trans 𝔄l (𝔄 :: 𝔅l)) : Prop :=
    tctx_incl E L T (t +:: T') tr.

  Lemma tctx_extract_elt_further {𝔄 𝔅 𝔄l 𝔅l}
    (t: tctx_elt 𝔄) (t': tctx_elt 𝔅) (T: tctx 𝔄l) (T': tctx 𝔅l) tr E L :
    tctx_extract_elt E L t T T' tr →
    tctx_extract_elt E L t (t' +:: T) (t' +:: T')
      (λ post '(b -:: al), tr (λ '(a -:: bl), post (a -:: b -:: bl)) al).
  Proof.
    move=> ?. eapply tctx_incl_ext.
    { eapply tctx_incl_trans; by [eapply tctx_incl_tail|apply tctx_incl_swap]. }
    move=> ?[??]/=. f_equal.
  Qed.

  Lemma tctx_extract_elt_here_copy {𝔄 𝔅 𝔄l} ty ty' (f: 𝔅 →ₛ 𝔄) (T: tctx 𝔄l) p p' E L :
    p = p' → Copy ty' → subtype E L ty' ty f →
    tctx_extract_elt E L (p ◁ ty) (p' ◁ ty' +:: T) (p' ◁ ty' +:: T)
      (λ post '(b -:: al), post (f ~~$ₛ b -:: b -:: al)).
  Proof.
    move=> ->??. eapply tctx_incl_ext.
    { by eapply tctx_incl_trans; [apply copy_tctx_incl|apply subtype_tctx_incl]. }
    by move=> ?[??].
  Qed.

  Lemma tctx_extract_elt_here_exact {𝔄 𝔄l} (t: tctx_elt 𝔄) (T: tctx 𝔄l) E L :
    tctx_extract_elt E L t (t +:: T) T id.
  Proof. apply tctx_incl_refl. Qed.

  Lemma tctx_extract_elt_here {𝔄 𝔅 𝔄l} ty ty' (f: 𝔅 →ₛ 𝔄) (T: tctx 𝔄l) p E L :
    subtype E L ty' ty f →
    tctx_extract_elt E L (p ◁ ty) (p ◁ ty' +:: T) T
      (λ post '(b -:: al), post (f ~~$ₛ b -:: al)).
  Proof.
    move=> ?. eapply tctx_incl_ext; [by apply subtype_tctx_incl|]. by move=> ?[??].
  Qed.

  Definition tctx_extract_ctx {𝔄l 𝔅l ℭl} E L (T: tctx 𝔄l)
    (T1: tctx 𝔅l) (T2: tctx ℭl) (tr: predl_trans 𝔅l (𝔄l ++ ℭl)) : Prop :=
    tctx_incl E L T1 (T h++ T2) tr.

  Lemma tctx_extract_ctx_eq {𝔄l 𝔅l ℭl} tr tr' E L
                            (T: tctx 𝔄l) (T1: tctx 𝔅l) (T2: tctx ℭl) :
    tctx_extract_ctx E L T T1 T2 tr' → tr = tr' → tctx_extract_ctx E L T T1 T2 tr.
  Proof. by move=> ?->. Qed.

  Lemma tctx_extract_ctx_nil {𝔄l} (T: tctx 𝔄l) E L :
    tctx_extract_ctx E L +[] T T id.
  Proof. apply tctx_incl_refl. Qed.

  Lemma tctx_extract_ctx_elt {𝔄 𝔄l 𝔅l ℭl 𝔇l}
      (t: tctx_elt 𝔄) (T: tctx 𝔄l) (T1: tctx 𝔅l) (T2: tctx ℭl) (T3: tctx 𝔇l)
      tr tr' E L :
    tctx_extract_elt E L t T1 T2 tr → tctx_extract_ctx E L T T2 T3 tr' →
    tctx_extract_ctx E L (t +:: T) T1 T3 (tr ∘ trans_tail tr').
  Proof. move=> ??. eapply tctx_incl_trans; by [|apply tctx_incl_tail]. Qed.

  Lemma tctx_extract_ctx_incl {𝔄l 𝔅l ℭl} (T: tctx 𝔄l) (T': tctx 𝔅l) (Tx: tctx ℭl) tr E L :
    tctx_extract_ctx E L T' T Tx tr →
    tctx_incl E L T T' (λ post, tr (λ bcl, post (psepl bcl))).
  Proof.
    move=> Ex. eapply tctx_incl_ext.
    { eapply tctx_incl_trans; [apply Ex|apply tctx_incl_resolve_lower]. }
    done.
  Qed.

  (** resolveing for Unblocking *)

  (* [κ] is a dummy parameter for automation *)
  Definition resolve_unblock_tctx {𝔄l 𝔅l} (E: elctx) (L: llctx) (κ: lft)
      (T: tctx 𝔄l) (T': tctx 𝔅l) (tr: predl_trans 𝔄l 𝔅l) : Prop :=
    ∀G tid xl post mask, Timeless G → llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ time_ctx -∗ elctx_interp E -∗ 
      (G &&{↑NllftG}&&> llctx_interp L) -∗ G -∗
      tctx_interp tid T xl -∗ ⟨π, tr post xl mask π⟩ ={⊤}=∗
        ∃d xl', ⧖d ∗ |={⊤}▷=>^(d*(d+1)) |={⊤}=>
          G ∗ tctx_interp tid T' xl' ∗ ⟨π, post xl' mask π⟩.

  Lemma resolve_unblock_tctx_impl {𝔄l 𝔅l} (tr tr': predl_trans 𝔄l 𝔅l) T T' E L κ :
    resolve_unblock_tctx E L κ T T' tr' → (∀post al mask π, tr post al mask π → tr' post al mask π) →
    resolve_unblock_tctx E L κ T T' tr.
  Proof.
    iIntros (RslvU Imp ??????) "LFT PROPH UNIQ TIME E L G T Obs".
    iApply (RslvU with "LFT PROPH UNIQ TIME E L G T [Obs]").
    iApply proph_obs_impl; [|done]=>/= ?. apply Imp.
  Qed.

  Lemma resolve_unblock_tctx_nil κ E L : resolve_unblock_tctx E L κ +[] +[] id.
  Proof.
    iIntros (??[]???) "/= _ _ _ _ _ _ $ _ $". iMod persistent_time_receipt_0 as "⧖".
    iExists 0%nat. by iFrame "⧖".
  Qed.

  Lemma resolve_unblock_tctx_cons_resolve {𝔄 𝔅l ℭl} (ty: type 𝔄) p Φ
      (T: tctx 𝔅l) (T': tctx ℭl) tr κ E L :
    κ ∈ ty_lfts ty → resolve' E L ty Φ → resolve_unblock_tctx E L κ T T' tr →
    resolve_unblock_tctx E L κ (p ◁ ty +:: T) T'
      (λ post '(a -:: bl), tr (λ cl mask π, Φ a π (post cl mask π)) bl).
  Proof.
    iIntros (_ Rslv RslvU ??[vπ ?]???)
      "#LFT #PROPH #UNIQ #TIME #E #L G /=[(%& %d &_& ⧖ & A) T] Obs".
    iDestruct "A" as "[ty %phys]".
    iMod (fractional.frac_split_guard_in_half NllftG with "G L")
        as (γ) "[F1 [F2 [#guards #back]]]". { set_solver. }
    iMod (Rslv with "LFT PROPH UNIQ TIME E guards F1 ty") as "Upd"; [done|].
    iMod (RslvU with "LFT PROPH UNIQ TIME E guards F2 T Obs") as (? vπl') "[⧖' Upd']".
    iCombine "Upd Upd'" as "Upd". iCombine "⧖ ⧖'" as "⧖".
    iExists _, vπl'. iFrame "⧖". iModIntro.
    rewrite lemma_max_mul. iApply (step_fupdN_wand with "Upd").
    iIntros "[>[Obs F1] >(F2&$& Obs')]". iCombine "Obs Obs'" as "?".
    iDestruct ("back" with "F1 F2") as "G".
    iMod (fupd_mask_mono with "G") as "G". { set_solver. }
    iModIntro. iFrame "G".
    iApply proph_obs_impl; [|done]=>/= ?[Imp ?]. apply Imp. trivial.
  Qed.

  Lemma resolve_unblock_tctx_cons_keep {𝔄 𝔅l ℭl} (t: tctx_elt 𝔄)
      (T: tctx 𝔅l) (T': tctx ℭl) tr κ E L :
    resolve_unblock_tctx E L κ T T' tr →
    resolve_unblock_tctx E L κ (t +:: T) (t +:: T') (trans_tail tr).
  Proof.
    iIntros (RslvU ??[vπ ?]???) "LFT PROPH UNIQ TIME E L G /=[t T] Obs".
    iMod (RslvU with "LFT PROPH UNIQ TIME E L G T Obs") as (d vπl') "[⧖ Upd]". iModIntro.
    iExists d, (vπ -:: vπl'). iFrame "⧖". iApply (step_fupdN_wand with "Upd").
    iIntros ">($&$&?) !>". iFrame.
  Qed.

  (** Unblocking a Type Context *)
  
  Definition unblock_tctx {𝔄l 𝔄l'} (E: elctx) (L: llctx) (κ: lft) (T: tctx 𝔄l) (T': tctx 𝔄l')
    (f: proph_asn → plist indep_interp_of_syn_type 𝔄l → plist indep_interp_of_syn_type 𝔄l' → Prop) : Prop :=
    ∀G tid xl, Timeless G → llft_ctx -∗ time_ctx -∗ elctx_interp E -∗ (G &&{↑NllftG}&&> llctx_interp L) -∗ G -∗ [†κ] -∗
      tctx_interp tid T xl ={⊤}=∗ ∃d xl', ⧖d ∗ |={⊤}▷=> |={⊤}▷=>^(d*(d+1)) |={⊤}=>
        G ∗ tctx_interp tid T' xl' ∗ ⟨π, f π xl xl'⟩.

  Lemma unblock_tctx_nil κ E L : unblock_tctx E L κ +[] +[] (λ _ _ _, True).
  Proof.
    iIntros (??[]?) "_ _ _ _ $ _ _". iMod persistent_time_receipt_0 as "⧖". iExists 0%nat, -[].
    iIntros "{$⧖}!>!>!>!>!>". iSplit; [done|]. by iApply proph_obs_true.
  Qed.

  Lemma unblock_tctx_cons_unblock {𝔄 𝔄l 𝔄l'} p (ty: type 𝔄) (T: tctx 𝔄l) (T': tctx 𝔄l') κ E L f :
    lctx_lft_alive E L (ty_lft ty) → unblock_tctx E L κ T T' f →
    unblock_tctx E L κ (p ◁{κ} blocked_type_ctor _ ty +:: T) (p ◁ ty +:: T')
      (λ π '(x -:: xl), λ '(x' -:: xl'), blockedπ x π = vπ x' π ∧ f π xl xl').
  Proof.
    iIntros (Alv Un ??[??]?) "#LFT #TIME #E #L G #†κ /=[(%v &%& Upd) T]".
    iMod ("Upd" with "†κ") as (x' d) "(Eqz & #⧖dp & ⧗ & ty)".
    
    iMod (cumulative_persistent_time_receipt_get_credits with "TIME ⧗ ⧖dp") as "[⧖S £]"; first by solve_ndisj.
    iDestruct (lc_weaken (d * (d + 1) + d * (d + 1) + 1 + 1) with "£") as "£". {
      unfold advance_credits. lia. }
    iDestruct "£" as "[[[£k £k'] £1] £1']".
    
    leaf_open "L" with "G" as "[L1 back]". { set_solver. }
    iDestruct (Alv with "L1 E") as "#Lkg".
    iMod ("back" with "L1") as "G".
    
    iMod (fractional.frac_split_guard_in_half with "G L") as (γ2) "[H1 [H2 [#Ghalf2 #Halfback2]]]"; first by solve_ndisj.
    
    iMod (Un with "LFT TIME E Ghalf2 H1 †κ T") as (dT xl') "[⧖dT >ToT']".
    
    iDestruct "ty" as "[gho phys]".
    iDestruct (ty_gho_pers_impl with "gho") as "#ghoPers".
    iAssert (▷^(d*(d+1)) (∀ ζ , ⌜ζ ∈ ξl x'⌝ -∗ (fractional.half γ2 ∗ ty_gho_own ty x' d d tid &&{↑NllftG; d*(d+1)}&&> 1:[ζ])))%I as "#Hallζlater".
    {
      iIntros (ζ) "%Hin".
      iDestruct (ty_guard_proph _ ty (foldr meet static (ty_lfts ty))%I x' 0 d d tid ζ ((fractional.half γ2 ∗ ty_gho_own ty x' d d tid)) Hin
          with "LFT [] ghoPers") as "A"; first by iApply guards_refl.
      iNext.
      iApply "A".
      - iApply guards_weaken_lhs_sep_l. iApply (guards_transitive with "Ghalf2 Lkg").
      - iApply guards_weaken_sep_r.
    }
    iMod (lc_fupd_elim_laterN with "£k Hallζlater") as "#Hallζ".
    iMod (lc_fupd_elim_later with "£1 Eqz") as "Eqz".
    
    iMod (uniq_cmra.proph_eqz_to_obs_with_guard with "£k' Hallζ [H2 gho] Eqz") as "[#Obs [H2 gho]]"; first by set_solver.
      { apply syn_indep. } { iFrame. }
    
    iMod (lc_fupd_elim_later with "£1' ToT'") as "ToT'".
    iMod "ToT'". iModIntro. iExists dT. iExists (x' -:: xl'). iFrame "⧖dT".
    iModIntro. iNext. iModIntro. iApply (step_fupdN_wand with "ToT'"). iIntros ">[H1 [T #Obs2]]".
    iDestruct ("Halfback2" with "H1 H2") as "G".
    iMod (fupd_mask_mono with "G") as "G"; first by set_solver.
    
    iModIntro. iFrame.
    iSplit. { iSplit; first by done. iApply (persistent_time_receipt_mono with "⧖S"). lia. }
    iCombine "Obs Obs2" as "Obs3".
    iApply "Obs3".
  Qed.

  Lemma unblock_tctx_cons_just {𝔄 𝔄l 𝔄l'} (t: tctx_elt 𝔄) (T: tctx 𝔄l) (T': tctx 𝔄l') κ E L f :
    unblock_tctx E L κ T T' f →
    unblock_tctx E L κ (t +:: T) (t +:: T')
        (λ π '(x -:: xl), λ '(x' -:: xl'), x = x' ∧ f π xl xl').
  Proof.
    iIntros (Un ?? [x xl] ?) "LFT TIME E L G †κ /=[t T]".
    iMod (Un with "LFT TIME E L G †κ T") as (d xl') "[⧖ Upd]". iModIntro.
    iExists d, (x -:: xl'). iFrame "⧖". iApply (step_fupdN_wand with "Upd").
    iIntros "!> >($&$&Obs) !>". iFrame "t". iApply (proph_obs_impl with "Obs"); split; trivial.
  Qed.

  Lemma unblock_tctx_cons_just_hasty {𝔄 𝔄l} p (ty: type 𝔄) (T: tctx 𝔄l) (T': tctx 𝔄l) κ E L f :
    unblock_tctx E L κ T T' f →
    unblock_tctx E L κ (p ◁ ty +:: T) (p ◁ ty +:: T')
        (λ π '(x -:: xl), λ '(x' -:: xl'), x = x' ∧ f π xl xl').
  Proof. apply unblock_tctx_cons_just. Qed.

  Lemma unblock_tctx_cons_just_blocked {𝔄 𝔄l} p (ty: type 𝔄) (T: tctx 𝔄l) (T': tctx 𝔄l) κ κ' E L f :
    κ ≠ κ' → unblock_tctx E L κ T T' f →
    unblock_tctx E L κ (p ◁{κ'} (blocked_type_ctor _ ty) +:: T) (p ◁{κ'} (blocked_type_ctor _ ty) +:: T')
        (λ π '(x -:: xl), λ '(x' -:: xl'), x = x' ∧ f π xl xl').
  Proof. move=> ?. apply unblock_tctx_cons_just. Qed.
End lemmas.

Ltac solve_extract :=
  eapply tctx_extract_ctx_eq; [solve_typing|];
  rewrite /trans_tail /compose /=; by reflexivity.

Ltac solve_resolve_unblock :=
  eapply resolve_unblock_tctx_impl; [solve_typing|]=> ??;
  rewrite /trans_tail /=; by exact id.

Global Hint Resolve resolve_tctx_nil : lrust_typing.
(* Mysteriously, registering [resolve_tctx_cons_*] with [Global Hint Resolve]
  does not help automation in some situations,
  but the following hints let automation work *)
Global Hint Extern 10 (resolve_tctx _ _ _ _) =>
  simple apply resolve_tctx_cons_hasty : lrust_typing.
Global Hint Extern 0 (resolve_tctx _ _ _ _) =>
  simple apply resolve_tctx_cons_just_hasty : lrust_typing.
Global Hint Extern 0 (resolve_tctx _ _ _ _) =>
  simple apply resolve_tctx_cons_just_blocked : lrust_typing.

Global Hint Resolve tctx_extract_elt_here_copy | 1 : lrust_typing.
Global Hint Resolve tctx_extract_elt_here_exact | 2 : lrust_typing.
Global Hint Resolve tctx_extract_elt_here | 20 : lrust_typing.
(* We need [eapply] to use [tctx_extract_elt_further] *)
Global Hint Extern 50 (tctx_extract_elt _ _ _ _ _ _) =>
  eapply tctx_extract_elt_further : lrust_typing.

Global Hint Resolve tctx_extract_ctx_nil tctx_extract_ctx_elt
  tctx_extract_ctx_incl : lrust_typing.

Global Hint Resolve resolve_unblock_tctx_nil resolve_unblock_tctx_cons_resolve
  : lrust_typing.
Global Hint Resolve resolve_unblock_tctx_cons_keep | 20 : lrust_typing.

Global Hint Resolve unblock_tctx_nil unblock_tctx_cons_unblock
  unblock_tctx_cons_just_hasty unblock_tctx_cons_just_blocked : lrust_typing.

Global Hint Opaque resolve_tctx tctx_incl tctx_extract_elt tctx_extract_ctx
  resolve_unblock_tctx unblock_tctx : lrust_typing.
