From Stdlib Require Import Strings.String Lists.List ZArith.ZArith Reals.Reals Lia.
From certification Require Export C10_ProgramDeterminism.

Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope R_scope.


Inductive fragmentCertifie : expr -> Prop :=
| CertifieSansPar : forall e,
    contientSomPar e = false -> fragmentCertifie e
| CertifieSomPar : forall i a b corps,
    contientSomPar a = false -> contientSomPar b = false ->
    contientSomPar corps = false -> fragmentCertifie (ESomPar i a b corps).

Definition evalComp (Sigma : list mem) (r : resComp) (v : val) : Prop :=
  exists Sigma', execGlob Sigma (rcCode r) Sigma' /\
    Forall (resCorrespond (rcRes r) v) Sigma'.

Lemma valResUnique :
  forall Sigma x v1 v2,
    Sigma <> [] ->
    Forall (resCorrespond x v1) Sigma ->
    Forall (resCorrespond x v2) Sigma -> v1 = v2.
Proof.
  intros [|sigma suite] x v1 v2 HnonVide H1 H2; [contradiction |].
  inversion H1 as [|? ? Hv1 _]; inversion H2 as [|? ? Hv2 _]; subst.
  unfold resCorrespond in *.
  destruct v1, v2; simpl in *; congruence.
Qed.

Lemma detEvalComp :
  forall Sigma r v1 v2,
    Sigma <> [] ->
    evalComp Sigma r v1 -> evalComp Sigma r v2 ->
    v1 = v2.
Proof.
  intros Sigma r v1 v2 HnonVide [Sigma1 [Hexec1 Hvals1]]
    [Sigma2 [Hexec2 Hvals2]].
  assert (Sigma1 = Sigma2).
  { eapply detProgMPI; eauto. }
  subst Sigma2.
  eapply valResUnique with (Sigma := Sigma1); eauto.
  intros Hvide.
  pose proof (longueurExecGlob _ _ _ Hexec1) as Hnb.
  rewrite Hvide in Hnb.
  destruct Sigma; [contradiction | discriminate].
Qed.

(** Réciproque : existence source + correction directe + unicité cible. *)
Lemma evalSrcDepuisComp :
  forall Gamma U B rho e t Sigma r,
    bienType Gamma U B e t ->
    envCompat Gamma rho -> primSrcTypees U B ->
    Sigma <> [] ->
    (forall v, evalExpr Gamma U B rho e t v -> evalComp Sigma r v) ->
    forall v, evalComp Sigma r v -> evalExpr Gamma U B rho e t v.
Proof.
  intros Gamma U B rho e t Sigma r Htype Henv Hprim HnonVide
    Hdirect v Hcible.
  destruct (evalExprExiste Gamma U B e t Htype Hprim rho Henv)
    as [u Hu].
  assert (u = v).
  { eapply detEvalComp; eauto. }
  now subst u.
Qed.

(** Équivalence pour la version générale du théorème sans SumPar*)
Theorem equivCompSansPar :
  forall Gamma U B e t ctxComp rho Sigma frais,
    bienType Gamma U B e t -> contientSomPar e = false ->
    envCompat Gamma rho -> primSrcTypees U B ->
    repsEnv (ctxRepr ctxComp) rho Sigma ->
    initFraiche Sigma frais -> primCompat U B ->
    Sigma <> [] ->
    forall v,
      evalExpr Gamma U B rho e t v <->
      evalComp Sigma (comp e Gamma U B ctxComp frais) v.
Proof.
  intros Gamma U B e t ctxComp rho Sigma frais Htype Hpar Henv Hprim
    Hrep Hfrais Hcompat HnonVide.
  assert (Hdirect : forall v, evalExpr Gamma U B rho e t v ->
    evalComp Sigma (comp e Gamma U B ctxComp frais) v).
  { intros v Heval.
    destruct (corrCompSansPar
      Gamma U B e t ctxComp rho Sigma frais v [] []
      Htype Hpar Heval Hrep Hfrais Hcompat)
      as [Sigma' [Hexec [Hvals _]]].
    exists Sigma'. split; assumption. }
  intros v. split; [apply Hdirect |].
  eapply evalSrcDepuisComp; eauto.
Qed.

Theorem corrCompCertifie :
  forall Gamma U B e t p rho Sigma frais v,
    fragmentCertifie e -> bienType Gamma U B e t ->
    evalExpr Gamma U B rho e t v ->
    initCoherente p rho Sigma -> initFraiche Sigma frais ->
    primCompat U B ->
    evalComp Sigma (comp e Gamma U B ctx0 frais) v.
Proof.
  intros Gamma U B e t p rho Sigma frais v Hfragment Htype Heval
    Hcoherent Hfrais Hcompat.
  destruct Hfragment as [e Hpar | i a b corps Ha Hb Hcorps].
  - exact (corrCompSansParInit
      Gamma U B e t p rho Sigma frais v [] []
      Htype Hpar Heval Hcoherent Hfrais Hcompat).
  - inversion Htype; subst. inversion Heval; subst.
    eapply corrCompSomPar; eauto.
Qed.

Lemma initCoherenteNonVide :
  forall p rho Sigma, initCoherente p rho Sigma -> Sigma <> [].
Proof.
  intros p rho Sigma [Hp [Hnb _]] Hvide. subst Sigma. simpl in Hnb. lia.
Qed.

Theorem corrCompTouteExec :
  forall Gamma U B e t p rho Sigma frais v Sigma',
    fragmentCertifie e -> bienType Gamma U B e t ->
    evalExpr Gamma U B rho e t v ->
    initCoherente p rho Sigma -> initFraiche Sigma frais ->
    primCompat U B ->
    execGlob Sigma (rcCode (comp e Gamma U B ctx0 frais)) Sigma' ->
    Forall (resCorrespond (rcRes (comp e Gamma U B ctx0 frais)) v)
      Sigma'.
Proof.
  intros Gamma U B e t p rho Sigma frais v Sigma' Hfragment Htype Heval
    Hcoherent Hfrais Hcompat Hexec.
  destruct (corrCompCertifie
    Gamma U B e t p rho Sigma frais v Hfragment Htype Heval Hcoherent Hfrais Hcompat)
    as [Sigma0 [Hexec0 Hvals]].
  assert (Sigma0 = Sigma') by (eapply detProgMPI; eauto).
  now subst Sigma0.
Qed.

Theorem execCompExisteUnique :
  forall Gamma U B e t p rho Sigma frais,
    fragmentCertifie e -> bienType Gamma U B e t ->
    envCompat Gamma rho -> primSrcTypees U B ->
    initCoherente p rho Sigma -> initFraiche Sigma frais ->
    primCompat U B ->
    exists! Sigma', execGlob Sigma (rcCode (comp e Gamma U B ctx0 frais)) Sigma'.
Proof.
  intros Gamma U B e t p rho Sigma frais Hfragment Htype Henv Hprim
    Hcoherent Hfrais Hcompat.
  destruct (evalExprExiste Gamma U B e t Htype Hprim rho Henv)
    as [v Hv].
  destruct (corrCompCertifie
    Gamma U B e t p rho Sigma frais v Hfragment Htype Hv Hcoherent Hfrais Hcompat)
    as [Sigma' [Hexec _]].
  exists Sigma'. split; [exact Hexec |].
  intros Sigma'' Hexec'. eapply detProgMPI; eauto.
Qed.

Theorem recipCorrComp :
  forall Gamma U B e t p rho Sigma frais v,
    fragmentCertifie e -> bienType Gamma U B e t ->
    envCompat Gamma rho -> primSrcTypees U B ->
    initCoherente p rho Sigma -> initFraiche Sigma frais ->
    primCompat U B ->
    evalComp Sigma (comp e Gamma U B ctx0 frais) v ->
    evalExpr Gamma U B rho e t v.
Proof.
  intros Gamma U B e t p rho Sigma frais v Hfragment Htype Henv Hprim
    Hcoherent Hfrais Hcompat Hcible.
  eapply evalSrcDepuisComp; eauto using
    initCoherenteNonVide, corrCompCertifie.
Qed.

Theorem equivComp :
  forall Gamma U B e t p rho Sigma frais,
    fragmentCertifie e -> bienType Gamma U B e t ->
    envCompat Gamma rho -> primSrcTypees U B ->
    initCoherente p rho Sigma -> initFraiche Sigma frais ->
    primCompat U B ->
    forall v,
      evalExpr Gamma U B rho e t v <->
      evalComp Sigma (comp e Gamma U B ctx0 frais) v.
Proof.
  intros Gamma U B e t p rho Sigma frais Hfragment Htype Henv Hprim
    Hcoherent Hfrais Hcompat v. split; intro Heval.
  - eapply corrCompCertifie; eauto.
  - eapply recipCorrComp; eauto.
Qed.
