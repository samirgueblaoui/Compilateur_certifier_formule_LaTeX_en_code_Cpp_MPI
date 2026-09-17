
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Reals.Reals.
From Stdlib Require Import Relations.Relation_Operators.
From Stdlib Require Import Lia.
From certification Require Export C03_Invariants.

Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope R_scope.

(** Nom temporaire de l'accumulateur de somme. *)
Definition accSom (nf : nat) : var :=
  nomTemp nf.

(** Nom temporaire de l'indice de boucle. *)
Definition indSom (nf : nat) : var :=
  nomTemp (S nf).

(** Premier temporaire réservé au corps de somme. *)
Definition debutCorpsSom (nf : nat) : nat :=
  S (S nf).

(** Compile le corps dans le contexte de l'indice. *)
Definition compCorpsSom
  (Gamma : envTypes) (U : envSigsUn) (B : envSigsBin)
  (ctxComp : ctx) (i : var) (corps : expr) (nf : nat) : resComp :=
  comp corps (lierTypeEnt Gamma i) U B
    (lierVarCtx ctxComp i (indSom nf))
    (debutCorpsSom nf).


(** Temporaires nettoyés après une itération. *)
Definition netSom
  (Gamma : envTypes) (U : envSigsUn) (B : envSigsBin)
  (ctxComp : ctx) (i : var) (corps : expr) (nf : nat) : list var :=
  nomsTempEntre (debutCorpsSom nf)
    (rcProchain
      (compCorpsSom Gamma U B ctxComp i corps nf)).

(** Test de poursuite de la boucle séquentielle. *)
Definition testSom (nf : nat) (borne : var) : exprCible :=
  AInfEg (AVar (indSom nf)) (AVar borne).

(** Incrémentation de l'indice séquentiel. *)
Definition incrSomSeq (nf : nat) : cmd :=
  CAffect (indSom nf)
    (APlus (AVar (indSom nf)) (ACstEnt 1)).

(** Commande d'une itération de somme séquentielle. *)
Definition corpsBoucleSom
  (Gamma : envTypes) (U : envSigsUn) (B : envSigsBin)
  (ctxComp : ctx) (i : var) (corps : expr) (nf : nat) : cmd :=
  CSeq
    (rcCode (compCorpsSom Gamma U B ctxComp i corps nf))
    (CAffect (accSom nf)
      (APlus (AVar (accSom nf))
        (AVar
          (rcRes
            (compCorpsSom Gamma U B ctxComp i corps nf))))).

(** Boucle cible complète d'une somme séquentielle. *)
Definition boucleSomSeq
  (Gamma : envTypes) (U : envSigsUn) (B : envSigsBin)
  (ctxComp : ctx) (i : var) (corps : expr) (nf : nat)
  (borne : var) : cmd :=
  CPour CRien (testSom nf borne) (incrSomSeq nf)
    (netSom Gamma U B ctxComp i corps nf)
    (corpsBoucleSom Gamma U B ctxComp i corps nf).

(** Incrémentation de l'indice par un pas donné. *)
Definition incrSomPas (nf : nat) (varPas : var) : cmd :=
  CAffect (indSom nf)
    (APlus (AVar (indSom nf)) (AVar varPas)).

(** Boucle cible d'une contribution par pas. *)
Definition boucleSomPas
  (Gamma : envTypes) (U : envSigsUn) (B : envSigsBin)
  (ctxComp : ctx) (i : var) (corps : expr) (nf : nat)
  (borne varPas : var) : cmd :=
  CPour CRien (testSom nf borne) (incrSomPas nf varPas)
    (netSom Gamma U B ctxComp i corps nf)
    (corpsBoucleSom Gamma U B ctxComp i corps nf).

(** Une variable résultat définie n'est pas fraîche. *)
Lemma resNonFrais :
  forall sigma x v frais n,
    resCorrespond x v sigma ->
    memFraiche sigma frais ->
    (frais <= n)%nat ->
    x <> nomTemp n.
Proof.
  unfold resCorrespond, memFraiche.
  intros sigma x v frais n Hcorresp Hfrais Hle Heq.
  subst x. rewrite Hfrais in Hcorresp; [discriminate | exact Hle].
Qed.

(** Une variable définie avant le seuil n'est pas fraîche. *)
Lemma varDefNonFraiche :
  forall sigma x cv frais n,
    sigma x = Some cv ->
    memFraiche sigma frais ->
    (frais <= n)%nat ->
    x <> nomTemp n.
Proof.
  unfold memFraiche. intros sigma x cv frais n Hdefini Hfrais Hle Heq.
  subst x. rewrite Hfrais in Hdefini; [discriminate | exact Hle].
Qed.

(** Localise un temporaire antérieur au nettoyage. *)
Lemma tempAvantNet :
  forall n debut fin,
    (n < debut)%nat ->
    ~ In (nomTemp n) (nomsTempEntre debut fin).
Proof.
  intros n debut fin Hlt Hin.
  unfold nomsTempEntre in Hin.
  apply dansTempDepuis in Hin. lia.
Qed.

(** Éval positivement le test avant la borne. *)
Lemma testSomVrai :
  forall sigma nf borne m n,
    sigma (indSom nf) = Some (VCEnt m) ->
    sigma borne = Some (VCEnt n) ->
    (m <= n)%Z ->
    evalCible sigma (testSom nf borne) = Some (VCBool true).
Proof.
  intros sigma nf borne m n Hind Hborne Hle.
  unfold testSom. simpl. rewrite Hind, Hborne. simpl.
  f_equal. f_equal. apply Z.leb_le. exact Hle.
Qed.

(** Éval négativement le test après la borne. *)
Lemma testSomFaux :
  forall sigma nf borne m n,
    sigma (indSom nf) = Some (VCEnt m) ->
    sigma borne = Some (VCEnt n) ->
    (n < m)%Z ->
    evalCible sigma (testSom nf borne) = Some (VCBool false).
Proof.
  intros sigma nf borne m n Hind Hborne Hlt.
  unfold testSom. simpl. rewrite Hind, Hborne. simpl.
  f_equal. f_equal. apply Z.leb_gt. lia.
Qed.

(** Justifie l'incrément unitaire de l'indice. *)
Lemma corrIncrSeq :
  forall sigma nf m,
    sigma (indSom nf) = Some (VCEnt m) ->
    evalCible sigma
      (APlus (AVar (indSom nf)) (ACstEnt 1)) =
    Some (VCEnt (m + 1)).
Proof.
  intros sigma nf m Hind. simpl. now rewrite Hind.
Qed.

(** Justifie l'incrément de l'indice par un pas. *)
Lemma corrIncrPas :
  forall sigma nf varPas courant pas,
    sigma (indSom nf) = Some (VCEnt courant) ->
    sigma varPas = Some (VCEnt pas) ->
    evalCible sigma
      (APlus (AVar (indSom nf)) (AVar varPas)) =
    Some (VCEnt (courant + pas)).
Proof.
  intros sigma nf varPas courant pas Hind HpasSom.
  simpl. now rewrite Hind, HpasSom.
Qed.

(** Justifie une accumulation et son nettoyage. *)
Lemma corrAccumSom :
  forall sigma nf resCorps prefixe courant,
    sigma (accSom nf) =
      Some (valVersCible prefixe) ->
    sigma resCorps =
      Some (valVersCible courant) ->
    evalCible sigma
      (APlus (AVar (accSom nf)) (AVar resCorps)) =
    Some (valVersCible (additionVals prefixe courant)).
Proof.
  intros sigma nf resCorps prefixe courant Hacc Hcorps.
  simpl. rewrite Hacc, Hcorps. apply corrAdditionCible.
Qed.

(** Partie commune des boucles : corps, accumulation et nettoyage.
    Toute case déjà définie, sauf l'accumulateur, conserve sa valeur.
    Le pas d'incrémentation reste à la charge du lemme de boucle. *)
Lemma corrIterNetSom :
  forall Gamma U B ctxComp rho i corps tCorps,
    (forall rho' sigma' ctxComp' frais' v,
      evalExpr (lierTypeEnt Gamma i) U B rho' corps tCorps v ->
      repEnv (ctxRepr ctxComp') rho' sigma' ->
      memFraiche sigma' frais' ->
      primCompat U B ->
      simLoc (ctxRepr ctxComp') rho' sigma'
        (comp corps (lierTypeEnt Gamma i) U B ctxComp' frais') v) ->
    forall base sigma frais0 nf prefixe courant v k,
      evalExpr (lierTypeEnt Gamma i) U B
        (majEnv rho i (VEnt courant)) corps tCorps v ->
      (frais0 <= nf)%nat ->
      memFraiche base frais0 ->
      repEnv (ctxRepr ctxComp) rho base ->
      presMem base sigma ->
      memFraiche sigma (debutCorpsSom nf) ->
      sigma (accSom nf) = Some (valVersCible prefixe) ->
      sigma (indSom nf) = Some (VCEnt courant) ->
      primCompat U B ->
      exists sigmaAcc sigmaNet,
        execLoc sigma (corpsBoucleSom Gamma U B ctxComp i corps nf)
          (KEff (netSom Gamma U B ctxComp i corps nf) :: k) sigmaAcc /\
        suiteLoc
          {| elMem := sigmaAcc;
             elCont := KEff (netSom Gamma U B ctxComp i corps nf) :: k |}
          {| elMem := sigmaNet; elCont := k |} /\
        sigmaNet (accSom nf) =
          Some (valVersCible (additionVals prefixe v)) /\
        (forall x cv, sigma x = Some cv -> x <> accSom nf ->
          sigmaNet x = Some cv) /\
        memFraiche sigmaNet (debutCorpsSom nf) /\
        presMem base sigmaNet.
Proof.
  intros Gamma U B ctxComp rho i corps tCorps HcorpsCorr
    base sigma frais0 nf prefixe courant v k
    HcorpsEval HfraisLe HbaseFrais HbaseRep HbasePres Hfrais Hacc Hind Hcompat.
  set (ru := compCorpsSom Gamma U B ctxComp i corps nf).
  set (net := netSom Gamma U B ctxComp i corps nf).
  assert (HborneRep :
    repEnv (ctxRepr (lierVarCtx ctxComp i (indSom nf)))
      (majEnv rho i (VEnt courant)) sigma).
  { apply repEnvLieEnt; [| exact Hind].
    eapply repEnvPres; eauto. }
  destruct (HcorpsCorr (majEnv rho i (VEnt courant)) sigma
    (lierVarCtx ctxComp i (indSom nf)) (debutCorpsSom nf) v
    HcorpsEval HborneRep Hfrais Hcompat
    (KCmd (CAffect (accSom nf)
      (APlus (AVar (accSom nf)) (AVar (rcRes ru)))) ::
      KEff net :: k))
    as [sigmaCorps [HexecCorps [HcorrespCorps [_ [HfraisCorps HpresCorps]]]]].
  set (sigmaAcc := majMem sigmaCorps (accSom nf)
    (valVersCible (additionVals prefixe v))).
  set (sigmaNet := effMem sigmaAcc net).
  assert (Hsuivant : (debutCorpsSom nf <= rcProchain ru)%nat).
  { subst ru. unfold compCorpsSom. apply compFraisMono. }
  assert (HfraisAcc : memFraiche sigmaAcc (rcProchain ru)).
  { subst sigmaAcc. apply memFraicheMajAvant; [exact HfraisCorps |].
    unfold accSom, debutCorpsSom in *. lia. }
  assert (HbasePresAcc : presMem base sigmaAcc).
  { subst sigmaAcc. apply presMemMajBase.
    - eapply memFraicheMono; eauto.
    - eapply presMemTrans; eauto. }
  exists sigmaAcc, sigmaNet. repeat split.
  - unfold corpsBoucleSom. fold ru. eapply execSeq.
    + exact HexecCorps.
    + apply execAffect.
      apply corrAccumSom with (prefixe := prefixe) (courant := v).
      * apply HpresCorps. exact Hacc.
      * exact HcorrespCorps.
  - apply execEff.
  - subst sigmaNet sigmaAcc. rewrite effMemHors.
    + apply majMemMeme.
    + subst net. apply tempAvantNet.
      unfold accSom, debutCorpsSom. lia.
  - intros x cv Hx Hneq. subst sigmaNet sigmaAcc.
    rewrite effMemHors.
    + rewrite majMemAutre; [now apply HpresCorps | exact Hneq].
    + intros Hin. subst net.
      apply dansTempEntreExiste in Hin as [j [Hnom [Hdebut _]]];
        [| exact Hsuivant].
      rewrite Hnom, Hfrais in Hx; [discriminate | exact Hdebut].
  - subst sigmaNet net. apply memFraicheApresNet; assumption.
  - subst sigmaNet net. apply presMemEffTemps.
    + exact Hsuivant.
    + eapply memFraicheMono; [exact HbaseFrais |].
      unfold debutCorpsSom. lia.
    + exact HbasePresAcc.
Qed.

(** Prouve la correction de la boucle séquentielle. *)
Lemma corrBoucleSeq :
  forall Gamma U B ctxComp rho i corps tCorps,
    bienType (lierTypeEnt Gamma i) U B corps tCorps ->
    (forall rho' sigma' ctxComp' frais' v,
      evalExpr (lierTypeEnt Gamma i) U B rho' corps tCorps v ->
      repEnv (ctxRepr ctxComp') rho' sigma' ->
      memFraiche sigma' frais' ->
      primCompat U B ->
      simLoc (ctxRepr ctxComp') rho' sigma'
        (comp corps (lierTypeEnt Gamma i) U B
          ctxComp' frais') v) ->
    forall m n total,
      evalSom Gamma U B rho i m n corps tCorps total ->
    forall base sigma frais0 nf borne prefixe k,
      (frais0 <= nf)%nat ->
      memFraiche base frais0 ->
      repEnv (ctxRepr ctxComp) rho base ->
      presMem base sigma ->
      memFraiche sigma (debutCorpsSom nf) ->
      sigma (accSom nf) =
        Some (valVersCible prefixe) ->
      sigma (indSom nf) = Some (VCEnt m) ->
      sigma borne = Some (VCEnt n) ->
      borne <> accSom nf ->
      borne <> indSom nf ->
      valTypee prefixe tCorps ->
      primCompat U B ->
      exists sigma',
        execLoc sigma
          (boucleSomSeq Gamma U B ctxComp i corps nf borne) k sigma' /\
        sigma' (accSom nf) =
          Some (valVersCible (additionVals prefixe total)) /\
        sigma' borne = Some (VCEnt n) /\
        memFraiche sigma'
          (rcProchain
            (compCorpsSom Gamma U B ctxComp i corps nf)) /\
        presMem base sigma'.
Proof.
  intros Gamma U B ctxComp rho i corps tCorps HcorpsType HcorpsCorr
    m n total Hsom.
  induction Hsom as
      [Gamma0 U0 B0 rho0 i0 m0 n0 corps0 tCorps0 Hvide
      | Gamma0 U0 B0 rho0 i0 m0 n0 corps0 tCorps0 v1 vReste
        Hle HcorpsEval Hreste IHreste];
    intros base sigma frais0 nf borne prefixe k
      HfraisLe HbaseFrais HbaseRep HbasePres Hfrais
      Hacc Hind Hborne HborneDiffAcc HborneDiffInd Hprefixe Hcompat.
  - exists sigma. repeat split.
    + apply execPourFin.
      apply testSomFaux with (m := m0) (n := n0);
        assumption.
    + rewrite zeroDrtVals.
      * exact Hacc.
      * exact Hprefixe.
    + exact Hborne.
    + eapply memFraicheMono.
      * exact Hfrais.
      * unfold debutCorpsSom, compCorpsSom.
        apply compFraisMono.
    + exact HbasePres.
  - destruct (corrIterNetSom
      Gamma0 U0 B0 ctxComp rho0 i0 corps0 tCorps0 HcorpsCorr
      base sigma frais0 nf prefixe m0 v1
      (KCmd (incrSomSeq nf) ::
       KCmd (boucleSomSeq Gamma0 U0 B0 ctxComp i0 corps0 nf borne) :: k)
      HcorpsEval HfraisLe HbaseFrais HbaseRep HbasePres Hfrais Hacc Hind Hcompat)
      as [sigmaAcc [sigmaNet
        [HexecBoucleCorps [Heff [HaccNet [Hgarde [HfraisNet HbasePresNet]]]]]]].
    assert (HaccDiffInd : accSom nf <> indSom nf).
    { unfold accSom, indSom. intros Heq.
      apply nomTempInj in Heq. lia. }
    assert (HindNet : sigmaNet (indSom nf) = Some (VCEnt m0)).
    { apply Hgarde; [exact Hind | now symmetry]. }
    assert (HborneNet : sigmaNet borne = Some (VCEnt n0)).
    { apply Hgarde; assumption. }
    set (sigmaEtape :=
      majMem sigmaNet (indSom nf) (VCEnt (m0 + 1))).
    assert (HexecPas :
      execLoc sigmaNet (incrSomSeq nf)
        (KCmd
          (boucleSomSeq Gamma0 U0 B0 ctxComp i0 corps0 nf borne) :: k)
        sigmaEtape).
    { unfold incrSomSeq. apply execAffect.
      apply corrIncrSeq. exact HindNet. }
    assert (HfraisPas :
      memFraiche sigmaEtape (debutCorpsSom nf)).
    { subst sigmaEtape. apply memFraicheMajAvant.
      - exact HfraisNet.
      - unfold indSom, debutCorpsSom. lia. }
    assert (HbasePresPas : presMem base sigmaEtape).
    { subst sigmaEtape. apply presMemMajBase.
      - eapply memFraicheMono; [exact HbaseFrais |].
        lia.
      - exact HbasePresNet. }
    assert (HaccPas :
      sigmaEtape (accSom nf) =
        Some (valVersCible (additionVals prefixe v1))).
    { subst sigmaEtape. rewrite majMemAutre.
      - exact HaccNet.
      - exact HaccDiffInd. }
    assert (HindPas :
      sigmaEtape (indSom nf) = Some (VCEnt (m0 + 1))).
    { subst sigmaEtape. apply majMemMeme. }
    assert (HbornePas :
      sigmaEtape borne = Some (VCEnt n0)).
    { subst sigmaEtape. rewrite majMemAutre.
      - exact HborneNet.
      - exact HborneDiffInd. }
    assert (Hv1type : valTypee v1 tCorps0).
    { eapply typeValEvalExpr. exact HcorpsEval. }
    assert (HvResteType : valTypee vReste tCorps0).
    { eapply typeValEvalSom. exact Hreste. }
    specialize
      (IHreste HcorpsType HcorpsCorr
        base sigmaEtape frais0 nf borne
        (additionVals prefixe v1) k
        HfraisLe HbaseFrais HbaseRep HbasePresPas HfraisPas
        HaccPas HindPas HbornePas
        HborneDiffAcc HborneDiffInd
        (typeAdditionVals tCorps0 prefixe v1 Hprefixe Hv1type)
        Hcompat).
    destruct IHreste as
      [sigmaFinal
        [HexecReste
          [HaccFinal
            [HborneFinal [HfraisFinal HbasePresFinal]]]]].
    exists sigmaFinal. repeat split.
    + unfold boucleSomSeq.
      eapply execPourIter
        with (sigma1 := sigmaAcc)
             (sigma2 := sigmaNet)
             (sigma3 := sigmaEtape).
      * apply testSomVrai with (m := m0) (n := n0);
          assumption.
      * exact HexecBoucleCorps.
      * exact Heff.
      * exact HexecPas.
      * exact HexecReste.
    + rewrite <- (assocAdditionVals tCorps0 prefixe v1 vReste);
        try assumption.
    + exact HborneFinal.
    + exact HfraisFinal.
    + exact HbasePresFinal.
Qed.

(** Prouve la correction d'une boucle par pas. *)
Lemma corrBouclePas :
  forall Gamma U B ctxComp rho i corps tCorps,
    bienType (lierTypeEnt Gamma i) U B corps tCorps ->
    (forall rho' sigma' ctxComp' frais' v,
      evalExpr (lierTypeEnt Gamma i) U B rho' corps tCorps v ->
      repEnv (ctxRepr ctxComp') rho' sigma' ->
      memFraiche sigma' frais' ->
      primCompat U B ->
      simLoc (ctxRepr ctxComp') rho' sigma'
        (comp corps (lierTypeEnt Gamma i) U B
          ctxComp' frais') v) ->
    forall pas m n total,
      evalSomPas Gamma U B rho i corps tCorps pas
        m n total ->
    forall base sigma frais0 nf borne varPas prefixe k,
      (frais0 <= nf)%nat ->
      memFraiche base frais0 ->
      repEnv (ctxRepr ctxComp) rho base ->
      presMem base sigma ->
      memFraiche sigma (debutCorpsSom nf) ->
      sigma (accSom nf) =
        Some (valVersCible prefixe) ->
      sigma (indSom nf) = Some (VCEnt m) ->
      sigma borne = Some (VCEnt n) ->
      sigma varPas = Some (VCEnt pas) ->
      borne <> accSom nf ->
      borne <> indSom nf ->
      varPas <> accSom nf ->
      varPas <> indSom nf ->
      valTypee prefixe tCorps ->
      primCompat U B ->
      exists sigma',
        execLoc sigma
          (boucleSomPas Gamma U B ctxComp i corps nf
            borne varPas) k sigma' /\
        sigma' (accSom nf) =
          Some (valVersCible (additionVals prefixe total)) /\
        sigma' borne = Some (VCEnt n) /\
        sigma' varPas = Some (VCEnt pas) /\
        memFraiche sigma'
          (rcProchain
            (compCorpsSom Gamma U B ctxComp i corps nf)) /\
        presMem base sigma'.
Proof.
  intros Gamma U B ctxComp rho i corps tCorps HcorpsType HcorpsCorr
    pas m n total Hsom.
  induction Hsom as
      [courant bSup Hvide
      | courant bSup valCourante reste
        Hle HcorpsEval Hreste IHreste];
    intros base sigma frais0 nf borne varPas prefixe k
      HfraisLe HbaseFrais HbaseRep HbasePres Hfrais
      Hacc Hind Hborne HpasSom
      HborneDiffAcc HborneDiffInd HpasSomAcc HpasSomInd
      Hprefixe Hcompat.
  - exists sigma. repeat split.
    + apply execPourFin.
      apply testSomFaux with (m := courant) (n := bSup);
        assumption.
    + rewrite zeroDrtVals; assumption.
    + exact Hborne.
    + exact HpasSom.
    + eapply memFraicheMono.
      * exact Hfrais.
      * unfold debutCorpsSom, compCorpsSom.
        apply compFraisMono.
    + exact HbasePres.
  - destruct (corrIterNetSom
      Gamma U B ctxComp rho i corps tCorps HcorpsCorr
      base sigma frais0 nf prefixe courant valCourante
      (KCmd (incrSomPas nf varPas) ::
       KCmd (boucleSomPas Gamma U B ctxComp i corps nf borne varPas) :: k)
      HcorpsEval HfraisLe HbaseFrais HbaseRep HbasePres Hfrais Hacc Hind Hcompat)
      as [sigmaAcc [sigmaNet
        [HexecBoucleCorps [Heff [HaccNet [Hgarde [HfraisNet HbasePresNet]]]]]]].
    assert (HaccDiffInd : accSom nf <> indSom nf).
    { unfold accSom, indSom. intros Heq.
      apply nomTempInj in Heq. lia. }
    assert (HindNet : sigmaNet (indSom nf) = Some (VCEnt courant)).
    { apply Hgarde; [exact Hind | now symmetry]. }
    assert (HborneNet : sigmaNet borne = Some (VCEnt bSup)).
    { apply Hgarde; assumption. }
    assert (HpasSomNet : sigmaNet varPas = Some (VCEnt pas)).
    { apply Hgarde; assumption. }
    set (sigmaEtape :=
      majMem sigmaNet (indSom nf)
        (VCEnt (courant + pas))).
    assert (HexecPas :
      execLoc sigmaNet (incrSomPas nf varPas)
        (KCmd
          (boucleSomPas Gamma U B ctxComp i corps nf
            borne varPas) :: k)
        sigmaEtape).
    { unfold incrSomPas. apply execAffect.
      apply corrIncrPas; assumption. }
    assert (HfraisPas :
      memFraiche sigmaEtape (debutCorpsSom nf)).
    { subst sigmaEtape. apply memFraicheMajAvant.
      - exact HfraisNet.
      - unfold indSom, debutCorpsSom. lia. }
    assert (HbasePresPas : presMem base sigmaEtape).
    { subst sigmaEtape. apply presMemMajBase.
      - eapply memFraicheMono; [exact HbaseFrais | lia].
      - exact HbasePresNet. }
    assert (HaccPas :
      sigmaEtape (accSom nf) =
        Some (valVersCible (additionVals prefixe valCourante))).
    { subst sigmaEtape. rewrite majMemAutre.
      - exact HaccNet.
      - exact HaccDiffInd. }
    assert (HindPas :
      sigmaEtape (indSom nf) =
        Some (VCEnt (courant + pas))).
    { subst sigmaEtape. apply majMemMeme. }
    assert (HbornePas :
      sigmaEtape borne = Some (VCEnt bSup)).
    { subst sigmaEtape. rewrite majMemAutre.
      - exact HborneNet.
      - exact HborneDiffInd. }
    assert (HpasSomPas :
      sigmaEtape varPas = Some (VCEnt pas)).
    { subst sigmaEtape. rewrite majMemAutre.
      - exact HpasSomNet.
      - exact HpasSomInd. }
    assert (HcourantType : valTypee valCourante tCorps).
    { exact
        (typeValEvalExpr _ _ _ _ _ _ _ HcorpsEval). }
    assert (HresteType : valTypee reste tCorps).
    { exact
        (typeValEvalSomPas
          _ _ _ _ _ _ _ _ _ _ _ Hreste). }
    specialize
      (IHreste base sigmaEtape frais0 nf borne varPas
        (additionVals prefixe valCourante) k
        HfraisLe HbaseFrais HbaseRep HbasePresPas HfraisPas
        HaccPas HindPas HbornePas HpasSomPas
        HborneDiffAcc HborneDiffInd HpasSomAcc HpasSomInd
        (typeAdditionVals tCorps prefixe valCourante
          Hprefixe HcourantType)
        Hcompat).
    destruct IHreste as
      [sigmaFinal
        [HexecReste
          [HaccFinal
            [HborneFinal
              [HpasSomFinal
                [HfraisFinal HbasePresFinal]]]]]].
    exists sigmaFinal. repeat split.
    + unfold boucleSomPas.
      eapply execPourIter
        with (sigma1 := sigmaAcc)
             (sigma2 := sigmaNet)
             (sigma3 := sigmaEtape).
      * apply testSomVrai with
          (m := courant) (n := bSup); assumption.
      * exact HexecBoucleCorps.
      * exact Heff.
      * exact HexecPas.
      * exact HexecReste.
    + rewrite <-
        (assocAdditionVals tCorps prefixe valCourante reste);
        try assumption.
    + exact HborneFinal.
    + exact HpasSomFinal.
    + exact HfraisFinal.
    + exact HbasePresFinal.
Qed.
