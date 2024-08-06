Set Warnings "-notation-overridden,-intuition-auto-with-star".

Require Import Preamble.
Require Import Preamble.Tag.

Require Export Defs.AInst.

Require Import Defs.E.
Require Import Defs.ERels.
Require Import Defs.FrA.
Require Import Defs.List.
Require Import Defs.Sub.

Require Import Defs.WfE.
Require Import Defs.WfSTt.

Notation  "{ ψ1 , θ1 } ⊢e ψ2 ⤳ { ψ3 , θ2 }" := (EInst ψ1 θ1 ψ2 ψ3 θ2) (at level 50, format "{ ψ1 ,  θ1 }  ⊢e  ψ2  ⤳  { ψ3 ,  θ2 }" ) : type_scope.

Notation EInst' ψ1 ψ2 := (exists (θ:Sub), {•, []} ⊢e ψ1 ⤳ {ψ2, θ}).
Notation  "ψ1 ⤳' ψ2" := (EInst' ψ1 ψ2) (at level 70(* , format "{ ein ,  subin }  ⊢  ψ1  ⤳  { ψ2 ,  sub }" *) ) : type_scope.

Ltac inv_EInst_ :=
  repeat match goal with
    | [ H : _ ⤳' _ |- _ ] => destruct H as [?θ H]
    | [ H : {_, _}⊢e E__Nil ⤳ {_, _} |- _ ] => inverts H
    | [ H : {_, _}⊢e _ ::a _ ⤳ {_, _} |- _ ] => inverts H
    | [ H : {_, _}⊢e _ ::x _ :- _ ⤳ {_, _} |- _ ] => inverts H
    | [ H : {_, _}⊢e _ ::o ⦇_ ▸ ⟨_⟩ _⦈ ⤳ {_, _} |- _ ] => inverts H
  end.
Ltac inv_EInst := repeat inv_EInst_.
Ltac inv_EInst' := repeat (try inv_EInst; try inv_AInst); autorewrite with appnil in *; cleanhyps.

Lemma EInst_E_lookup : forall ψ ψ__dec θ x σ,
    {•, []} ⊢e ψ ⤳ {ψ__dec, θ}
  -> E_lookup ψ    x = Some σ
  -> E_lookup ψ__dec x = Some ⟦θ ▹ σ⟧.
Proof.
  introv EINST LU. induction EINST.
  - crush.
  - simpl+. (** we need to weaken sub application *)
Admitted.

Lemma AInst_Sub_wf : forall ψ a θ,
    ψ ⊢a a ⤳ θ
  -> ψ ⊢θ θ.
Proof. introv AINST. induction AINST. crush. eapply Sub_wf_cons. eassumption. eassumption. Qed.

Corollary AInst_skvars_codom_Sub : forall ψ a θ,
    ψ ⊢a a ⤳ θ
  -> skvars_codom_Sub θ ⊆ E_A_skvars ψ.
Proof. introv AINST. eauto using AInst_Sub_wf, Sub_wf_codom. Qed.

Lemma AInst_Sub_to_A : forall ψ a θ,
    ψ ⊢a a ⤳ θ
  -> a = Sub_to_A θ.
Proof. introv AINST. induction AINST; crush. Qed.

Lemma EInst_alg_to_dec : forall ψ__in θ__in ψ ψ__dec θ,
    {ψ__in, θ__in} ⊢e ψ ⤳ {ψ__dec, θ}
  -> alg_E ψ
  -> dec_E ψ__in
  -> dec_E ψ__dec
  -> alg_to_dec θ.
Proof.
  introv EINST ALG DEC__in DEC. induction EINST. 1:split; crush. 2,3:eauto.
  apply alg_to_dec_app. 2:eauto. split.
  - rewrite <- varl_Sub_to_A_dom. apply AInst_Sub_to_A in AINST. subst.
    applys alg_L_subset ALG. simpl+. fsetdec.
  - rewrite AInst_skvars_codom_Sub. 2:eassumption.
    rewrite E_A_skvars_E_skvars. applys dec_L_subset.
    + applys dec_union3 DEC__in DEC.
    + simpl+. fsetdec.
Qed.

Corollary EInst_alg_to_dec' : forall ψ ψ__dec θ,
    {•, []} ⊢e ψ ⤳ {ψ__dec, θ}
  -> alg_E ψ
  -> dec_E ψ__dec
  -> alg_to_dec θ.
Proof. intros. eapply EInst_alg_to_dec. eassumption. eassumption. crush. eassumption. Qed.

(*** Props *)
Corollary Sub_wf_app__constr : forall ψ θ1 θ2,
    ψ ⊢θ θ1
  -> ψ ⊢θ θ2
  -> ψ ⊢θ (θ1 ++ θ2).
Proof. intros. forwards>: (Sub_wf_app ψ θ1 θ2). split; eassumption. crush. Qed.

Lemma EInst_Sub_wf : forall ψ__in θ__in ψ ψ' θ,
    {ψ__in, θ__in} ⊢e ψ ⤳ {ψ', θ}
  -> (ψ__in +++ ψ') ⊢θ θ.
Proof.
  introv EINST. induction EINST.
  - crush.
  - eapply Sub_wf_app__constr.
    + eauto using AInst_Sub_wf.
    + eapply Sub_wf_E_sk_sub. eassumption. reldec.
  - eapply Sub_wf_E_sk_sub. eassumption. reldec.
  - eapply Sub_wf_E_sk_sub. eassumption. reldec.
Qed.
Corollary EInst_Sub_wf' : forall ψ ψ' θ,
    {•, []} ⊢e ψ ⤳ {ψ', θ}
  -> ψ' ⊢θ θ.
Proof. intros. forwards WF: EInst_Sub_wf. eassumption. simpl+ in WF. eauto. Qed.
#[export] Hint Resolve EInst_Sub_wf EInst_Sub_wf' : core.

(* Lemma EInst_split : forall L ψ__alg2 ψ__in θ__in ψ__alg1 ψ__dec θ, *)
(*     {L, ψ__in, θ__in} ⊢e ψ__alg1 +++ ψ__alg2 ⤳ {ψ__dec, θ} *)
(*   -> exists ψ__dec1 ψ__dec2 θ1 θ2, *)
(*       ψ__dec = ψ__dec1 +++ ψ__dec2 *)
(*     /\ θ = θ2 ++ θ1 *)
(*     /\ {L, ψ__in, θ__in} ⊢e ψ__alg1 ⤳ {ψ__dec1, θ1} *)
(*     /\ {L \u (E_skvars ψ__dec1), ψ__in +++ ψ__dec1, θ1 ++ θ__in} ⊢e ψ__alg2 ⤳ {ψ__dec2, θ2}. *)
(* Proof. *)
(*   intros L ψ__alg2. induction ψ__alg2; introv INST. *)
(*   1:exists. crush. *)
(*   all: simpl+ in INST; inv_EInst; *)
(*     forwards [ψ__dec1 [ψ__dec2 [θ__l [θ__r [EQ1 [EQ2 [INST__l INST__r]]]]]]]: IHψ__alg2; try eassumption; subst. *)
(*   - exists. splits. 3:eassumption. norm. rewrite <- E_app_assoc. reflexivity. *)
(*     rewrite <- app_assoc. reflexivity. *)
(*     constructor. eassumption. FrA_L_sub. applys_eq AINST. crush. *)
(*   - exists. splits. 3:eassumption. norm. rewrite <- E_app_assoc. reflexivity. *)
(*     reflexivity. *)
(*     simpl+. econstructor. eassumption. *)
(*   - exists. splits. 3:eassumption. norm. rewrite <- E_app_assoc. reflexivity. *)
(*     reflexivity. *)
(*     simpl+. econstructor. eassumption. FrA_L_sub. applys_eq AINST. crush. *)
(* Qed. *)

(* Lemma EInst_merge : forall L ψ__in θ__in ψ__alg1 ψ__alg2 ψ__dec1 ψ__dec2 θ1 θ2, *)
(*     {L, ψ__in, θ__in} ⊢e ψ__alg1 ⤳ {ψ__dec1, θ1} *)
(*   -> {L \u (E_skvars ψ__dec1), ψ__in +++ ψ__dec1, θ1 ++ θ__in} ⊢e ψ__alg2 ⤳ {ψ__dec2, θ2} *)
(*   -> {L, ψ__in, θ__in} ⊢e ψ__alg1 +++ ψ__alg2 ⤳ {ψ__dec1 +++ ψ__dec2, θ2 ++ θ1}. *)
(* Proof. *)
(*   introv INST1 INST2. *)
(*   gen ψ__dec2 θ2. *)
(*   induction ψ__alg2; introv (* INST1 *) INST2 (* SUB *); inv_EInst. *)
(*   - simpl+. eassumption. *)
(*   - forwards IH: IHψ__alg2. eassumption. *)
(*     simpl+. econstructor. eassumption. FrA_L_sub. crush. *)
(*   - simpl+. constructor_eq. simpl+. fequals. eauto. *)
(*   - simpl+. constructor_eq. simpl+. fequals. eauto. *)
(*     FrA_L_sub. applys_eq AINST. simpl+. crush. *)
(* Qed. *)

(* (* Lemma EInst_merge' : forall L1 L2 ψ__in θ__in ψ__alg1 ψ__alg2 ψ__dec1 ψ__dec2 θ1 θ2, *) *)
(* (*     {L1, ψ__in, θ__in} ⊢e ψ__alg1 ⤳ {ψ__dec1, θ1} *) *)
(* (*   -> {L2, ψ__in +++ ψ__dec1, θ1 ++ θ__in} ⊢e ψ__alg2 ⤳ {ψ__dec2, θ2} *) *)
(* (*   -> L1 \u (E_skvars ψ__dec1) ⊆ L2 *) *)
(* (*   -> {L1, ψ__in, θ__in} ⊢e ψ__alg1 +++ ψ__alg2 ⤳ {ψ__dec1 +++ ψ__dec2, θ2 ++ θ1}. *) *)
(* (* Proof. *) *)
(* (*   introv INST1 INST2 SUB. *) *)
(* (*   gen ψ__dec2 θ2. *) *)
(* (*   induction ψ__alg2; introv (* INST1 *) INST2 (* SUB *); inv_EInst. *) *)
(* (*   1:crush. *) *)
(* (*   all: forwards IH: IHψ__alg2; try eassumption; simpl+. *) *)
(* (*   - econstructor. eassumption. crush. (*FrA_L_sub*) admit. *) *)
(* (*   - applys_eq EInst__S. 2:eassumption. all:crush. *) *)
(* (*   - applys_eq EInst__O. crush. eassumption. (*FrA_L_sub*) 2:admit. all:crush. *) *)
(* (* Admitted. *) *)

(* (* Lemma EInst_merge' : forall L ψ__in θ__in ψ__alg1 ψ__alg2 ψ__dec1 ψ__dec2 θ1 θ2, *) *)
(* (*     {L, ψ__in, θ__in} ⊢e ψ__alg1 ⤳ {ψ__dec1, θ1} *) *)
(* (*   -> {L \u E_skvars ψ__dec1, ψ__in +++ ψ__dec1, θ1 ++ θ__in} ⊢e ψ__alg2 ⤳ {ψ__dec2, θ2} *) *)
(* (*   -> {L, ψ__in, θ__in} ⊢e ψ__alg1 +++ ψ__alg2 ⤳ {ψ__dec1 +++ ψ__dec2, θ2 ++ θ1}. *) *)
(* (* Proof. intros. eapply EInst_merge; try eassumption. reflexivity. Qed. *) *)

(* (*** Props *) *)
(* Lemma EInst_props : forall L ψ ψ__in θ__in ψ' θ, *)
(*     {L, ψ__in, θ__in} ⊢e ψ ⤳ {ψ', θ} *)
(*   -> (ψ__in +++ ψ') ⊢θ θ *)
(*   /\ dom_Sub θ ≡ E_A_skvars ψ *)
(*   /\ E_A_skvars ψ' ∐ L. *)
(* Proof. *)
(*   induction ψ; intros; inv_EInst'. *)
(*   1: splits; crush. *)
(*   all: forwards [IH__swf [IH__dom IH__L]]: IHψ; try eassumption. *)
(*   - splits. *)
(*     + apply Sub_wf_app. splits. eauto. *)
(*       eapply Sub_wf_E_sk_sub. eassumption. clfsetdec+. *)
(*     + simpl+. rewrite IH__dom. forwards: AInst_props__aeq. eassumption. subst. *)
(*       simpl+. reflexivity. *)
(*     + simpl+. *)
(*       disj_union. apply FrA_props. FrA_L_sub. crush. *)
(*   - splits. *)
(*     + eapply Sub_wf_E_sk_sub. eassumption. clfsetdec+. *)
(*     + fsetdec+. *)
(*     + crush. *)
(*   - splits. *)
(*     + eapply Sub_wf_E_sk_sub. eassumption. clfsetdec+. *)
(*     + fsetdec+. *)
(*     + simpl+. crush. *)
(* Qed. *)

(* Corollary EInst_props__swf : forall L ψ__in θ__in ψ ψ' θ, *)
(*     {L, ψ__in, θ__in} ⊢e ψ ⤳ {ψ', θ} *)
(*   -> (ψ__in +++ ψ') ⊢θ θ. *)
(* Proof. intros. forwards: EInst_props. eassumption. jauto. Qed. *)
(* Corollary EInst_props__swf' : forall L ψ ψ' θ, *)
(*     {L, •, []} ⊢e ψ ⤳ {ψ', θ} *)
(*   -> ψ' ⊢θ θ. *)
(* Proof. intros. forwards [WF _]: EInst_props. eassumption. simpl+ in WF. eauto. Qed. *)
(* #[export] Hint Resolve EInst_props__swf EInst_props__swf' : core. *)

(* Corollary EInst_props__codom : forall L ψ__in θ__in ψ ψ' θ, *)
(*     {L, ψ__in, θ__in} ⊢e ψ ⤳ {ψ', θ} *)
(*   -> skvars_codom_Sub θ ⊆ E_A_skvars (ψ__in +++ ψ'). *)
(* Proof. introv INST. eauto using Sub_wf_codom. Qed. *)
(* Corollary EInst_props__codom' : forall L ψ ψ' θ, *)
(*     {L, •, []} ⊢e ψ ⤳ {ψ', θ} *)
(*   -> skvars_codom_Sub θ ⊆ E_A_skvars ψ'. *)
(* Proof. introv INST. eauto using Sub_wf_codom. Qed. *)
(* #[export] Hint Resolve EInst_props__codom EInst_props__codom' : core. *)

(* Lemma EInst_props__dom : forall L ψ__in θ__in ψ ψ' θ, *)
(*     {L, ψ__in, θ__in} ⊢e ψ ⤳ {ψ', θ} *)
(*   -> dom_Sub θ ≡ E_A_skvars ψ. *)
(* Proof. intros. eapply EInst_props. eassumption. Qed. *)
(* #[export] Hint Resolve EInst_props__dom : core. *)

(* Corollary EInst_props__domσ : forall L ψ__in θ__in ψ ψ' θ σ, *)
(*     {L, ψ__in, θ__in} ⊢e ψ ⤳ {ψ', θ} *)
(*   -> ψ ⊢wfσ σ *)
(*   -> fv__α(σ) ⊆ dom_Sub θ. *)
(* Proof. introv INST WFT. rewrite EInst_props__dom. 2:eassumption. crush+. Qed. *)
(* #[export] Hint Resolve EInst_props__domσ : core. *)
(* Corollary EInst_props__domτ : forall L ψ__in θ__in ψ ψ' θ τ, *)
(*     {L, ψ__in, θ__in} ⊢e ψ ⤳ {ψ', θ} *)
(*   -> ψ ⊢wfτ τ *)
(*   -> fv__α(τ) ⊆ dom_Sub θ. *)
(* Proof. intros. forwards: EInst_props__domσ (S__T τ). eassumption. crush. simpl+ in H1. crush. Qed. *)
(* #[export] Hint Resolve EInst_props__domτ : core. *)


(* Lemma EInst_props__L : forall L ψ__in θ__in ψ ψ' θ, *)
(*     {L, ψ__in, θ__in} ⊢e ψ ⤳ {ψ', θ} *)
(*   -> E_A_skvars ψ' ∐ L. *)
(* Proof. intros. eapply EInst_props. eassumption. Qed. *)
(* #[export] Hint Resolve EInst_props__L : core. *)

(* Example Sub_app_further_noteffect : forall L ψ__in θ__in ψ__alg ψ__dec θ τ, *)
(*     {L, ψ__in, θ__in} ⊢e ψ__alg ⤳ {ψ__dec, θ} *)
(*   -> ψ__in ⊢wfτ τ *)
(*   -> wf(ψ__in +++ ψ__alg) *)
(*   -> ⟦θ ▹ τ⟧ = τ. *)
(* Proof. *)
(*   introv INST WFT WFE. *)
(*   apply Sub_app_T_notindom. rewrite EInst_props__dom. 2:eassumption. *)
(*   rewrite (WfT_sk _ _ WFT). *)
(*   admit. *)
(*   (* forwards: wf_env_sk_disj. eassumption. *) *)
(*   (* disj_sub_with H. *) *)
(* Abort. *)
