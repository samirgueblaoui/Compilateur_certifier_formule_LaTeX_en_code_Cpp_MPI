
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Reals.Reals.
From Stdlib Require Import Relations.Relation_Operators.
From Stdlib Require Import Lia.
From certification Require Export C07_SumParSimple.

Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope R_scope.

(** Prouve la correction globale du fragment sans SumPar. *)
Theorem corrCompSansPar :
  forall Gamma U B e t ctxComp rho Sigma frais v q k,
    bienType Gamma U B e t ->
    contientSomPar e = false ->
    evalExpr Gamma U B rho e t v ->
    repsEnv (ctxRepr ctxComp) rho Sigma ->
    initFraiche Sigma frais ->
    primCompat U B ->
    exists Sigma',
      suiteGlob
        (List.app q
          (etatsEnCours Sigma
            (rcCode (comp e Gamma U B ctxComp frais)) k))
        (List.app q (etatsFinaux Sigma' k)) /\
      Forall
        (resCorrespond
          (rcRes (comp e Gamma U B ctxComp frais)) v) Sigma' /\
      repsEnv (ctxRepr ctxComp) rho Sigma' /\
      initFraiche Sigma'
        (rcProchain (comp e Gamma U B ctxComp frais)) /\
      Forall2 presMem Sigma Sigma'.
Proof.
  intros Gamma U B e t ctxComp rho Sigma frais v q k
    Htype Hpar Heval Hrep Hfrais Hcompat.
  destruct (reunirSimsLoc
    (ctxRepr ctxComp) rho Sigma (comp e Gamma U B ctxComp frais) v frais
    (fun sigma HrepSigma HfraisSigma =>
      corrCompLoc
        Gamma U B e t Htype Hpar ctxComp rho sigma frais v
        Heval HrepSigma HfraisSigma Hcompat)
    Hrep Hfrais k) as [Sigma' [Hexecs Hprops]].
  exists Sigma'. split; [now apply reunirExecsLoc | exact Hprops].

Qed.


(** Prouve la correction globale d'un SumPar simple. *)
Theorem corrCompSomPar :
  forall Gamma U B i a b corps tCorps p rho Sigma frais m n total k,
    bienType Gamma U B a TEnt ->
    bienType Gamma U B b TEnt ->
    bienType (lierTypeEnt Gamma i) U B corps tCorps ->
    contientSomPar a = false ->
    contientSomPar b = false ->
    contientSomPar corps = false ->
    evalExpr Gamma U B rho a TEnt (VEnt m) ->
    evalExpr Gamma U B rho b TEnt (VEnt n) ->
    evalSom Gamma U B rho i m n corps tCorps total ->
    initCoherente p rho Sigma ->
    initFraiche Sigma frais ->
    primCompat U B ->
    exists Sigma',
      suiteGlob
        (etatsEnCours Sigma
          (rcCode
            (comp (ESomPar i a b corps)
              Gamma U B ctx0 frais)) k)
        (etatsFinaux Sigma' k) /\
      Forall
        (resCorrespond
          (rcRes
            (comp (ESomPar i a b corps)
              Gamma U B ctx0 frais))
          total) Sigma'.
Proof.
  intros Gamma U B i a b corps tCorps p rho Sigma frais m n total k
    HtypeA HtypeB HtypeCorps
    HparA HparB HparCorps
    HevalA HevalB Hsom Hcoherent Hfrais Hcompat.
  remember (comp a Gamma U B ctx0 frais) as ra eqn:Hra.
  remember
    (comp b Gamma U B ctx0 (rcProchain ra))
    as rb eqn:Hrb.
  set (nf := rcProchain rb).
  set (ru :=
    compCorpsSom Gamma U B ctx0 i corps nf).
  set (res := nomTemp (rcProchain ru)).
  set (queue := finSomPar Gamma U B ctx0 i corps tCorps
    nf (rcRes ra) (rcRes rb)).
  assert (HruType : rcType ru = tCorps).
  { subst ru nf. unfold compCorpsSom.
    apply corrTypeComp. exact HtypeCorps. }
  assert (Hcode :
    rcCode
      (comp (ESomPar i a b corps) Gamma U B ctx0 frais) =
    CSeq (rcCode ra) (CSeq (rcCode rb) queue)).
  { cbn [comp].
    rewrite <- Hra. simpl.
    rewrite <- Hrb. simpl.
    rewrite HparCorps.
    subst queue res ru nf.
    cbn [finSomPar brancheSomPar accSom indSom
      debutCorpsSom compCorpsSom netSom
      corpsBoucleSom testSom incrSomPas].
    unfold compCorpsSom, indSom, debutCorpsSom in HruType.
    rewrite HruType. reflexivity. }
  assert (Hres :
    rcRes
      (comp (ESomPar i a b corps) Gamma U B ctx0 frais) =
    res).
  { cbn [comp].
    rewrite <- Hra. simpl.
    rewrite <- Hrb. simpl.
    rewrite HparCorps.
    subst res ru nf. reflexivity. }
  destruct
    (corrCompSansPar
      Gamma U B a TEnt ctx0 rho Sigma frais (VEnt m) []
      (KCmd (CSeq (rcCode rb) queue) :: k)
      HtypeA HparA HevalA
      (repInitCoherente p rho Sigma Hcoherent)
      Hfrais Hcompat)
    as [SigmaA
      [HexecA
        [HcorrespA [HrepA [HfraisA HpresA]]]]].
  rewrite <- Hra in HexecA, HcorrespA, HfraisA.
  simpl in HexecA.
  destruct
    (corrCompSansPar
      Gamma U B b TEnt ctx0 rho SigmaA
      (rcProchain ra) (VEnt n) []
      (KCmd queue :: k)
      HtypeB HparB HevalB
      HrepA HfraisA Hcompat)
    as [SigmaB
      [HexecB
        [HcorrespB [HrepB [HfraisB HpresB]]]]].
  rewrite <- Hrb in HexecB, HcorrespB, HfraisB.
  simpl in HexecB.
  assert (Hp : (1 <= p)%nat) by (now destruct Hcoherent as [Hp _]).
  destruct
    (partitionSomCyclique
      Gamma U B rho i corps tCorps m n total Hsom p Hp)
    as [vals [HpasSoms HvalsTotal]].
  assert (HvalsNonVide : vals <> []).
  { intros Hvide. subst vals.
    destruct HpasSoms as [Hlongueur _]. simpl in Hlongueur. lia. }
  assert (HpresAb : Forall2 presMem Sigma SigmaB).
  { eapply transPresMems; eauto. }
  assert (Hpret :
    PourTous3
      (pretSomPar Gamma U B ctx0 rho i corps tCorps
        nf (rcRes ra) (rcRes rb) m n p)
      (seq 0 p) vals SigmaB).
  { eapply pretsSomParApresBornes; eauto using
      presResMems. }
  destruct
    (redSomParDepuisPrets
      Gamma U B ctx0 rho i corps tCorps HtypeCorps
      (fun rho' sigma' ctxComp' frais' val Heval Hrep Hfrais Hcompat =>
        corrCompLoc
          (lierTypeEnt Gamma i) U B corps tCorps HtypeCorps
          HparCorps ctxComp' rho' sigma' frais' val
          Heval Hrep Hfrais Hcompat)
      Hcompat nf (rcRes ra) (rcRes rb) m n p
      (seq 0 p) vals SigmaB total k
      Hpret HvalsNonVide HvalsTotal)
    as [SigmaFinal [HexecQueue Hcorresps]].
  exists SigmaFinal. split.
  - rewrite Hcode.
    eapply transSuiteGlob.
    + apply ouvrirSeqGlob.
    + eapply transSuiteGlob.
      * exact HexecA.
      * eapply transSuiteGlob.
        -- apply ouvrirSeqGlob.
        -- eapply transSuiteGlob; eauto.
  - now rewrite Hres.
Qed.

Corollary corrCompSansParInit :
  forall Gamma U B e t p rho Sigma frais v q k,
    bienType Gamma U B e t ->
    contientSomPar e = false ->
    evalExpr Gamma U B rho e t v ->
    initCoherente p rho Sigma ->
    initFraiche Sigma frais ->
    primCompat U B ->
    exists Sigma',
      suiteGlob
        (List.app q
          (etatsEnCours Sigma
            (rcCode (comp e Gamma U B ctx0 frais)) k))
        (List.app q (etatsFinaux Sigma' k)) /\
      Forall
        (resCorrespond
          (rcRes (comp e Gamma U B ctx0 frais)) v) Sigma'.
Proof.
  intros Gamma U B e t p rho Sigma frais v q k
    Htype Hpar Heval Hcoherent Hfrais Hcompat.
  destruct
    (corrCompSansPar
      Gamma U B e t ctx0 rho Sigma frais v q k
      Htype Hpar Heval
      (repInitCoherente p rho Sigma Hcoherent)
      Hfrais Hcompat)
    as [Sigma'
      [Hexec [Hres [Hrep [Hfrais' HpresMems]]]]].
  exists Sigma'. now split.
Qed.
