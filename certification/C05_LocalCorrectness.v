
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Reals.Reals.
From Stdlib Require Import Relations.Relation_Operators.
From Stdlib Require Import Lia.
From certification Require Export C04_SequentialSum.

Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope R_scope.

(** Construit la branche locale d'un SumPar simple. *)
Definition brancheSomPar
  (Gamma : envTypes) (U : envSigsUn) (B : envSigsBin)
  (ctxComp : ctx) (i : var) (corps : expr) (nf : nat)
  (bInf borne : var) : cmd :=
  CSi (ctxActif ctxComp) []
    (CPour
      (CAffect (indSom nf)
        (APlus (AVar bInf) (AVar (ctxRang ctxComp))))
      (testSom nf borne)
      (incrSomPas nf (ctxNbProc ctxComp))
      (netSom Gamma U B ctxComp i corps nf)
      (corpsBoucleSom Gamma U B ctxComp i corps nf))
    [] CRien.

(** Suffixe commun après le calcul des bornes d'une somme parallèle simple. *)
Definition finSomPar
  (Gamma : envTypes) (U : envSigsUn) (B : envSigsBin)
  (ctxComp : ctx) (i : var) (corps : expr) (tCorps : typeNum)
  (nf : nat) (bInf borne : var) : cmd :=
  let res := nomTemp
    (rcProchain (compCorpsSom Gamma U B ctxComp i corps nf)) in
  CSeq (CAffect (accSom nf) (exprNulle tCorps))
    (CSeq (brancheSomPar Gamma U B ctxComp i corps nf bInf borne)
      (CSeq (CAffect res (exprNulle tCorps))
        (CRedTous (accSom nf) res))).

(** Amène un processus actif jusqu'au Allreduce. *)
Lemma procSomParVersRed :
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
    forall sigma nf bInf borne m n rang p contribution k,
      evalSomPas Gamma U B rho i corps tCorps (Z.of_nat p)
        (m + Z.of_nat rang) n contribution ->
      repEnv (ctxRepr ctxComp) rho sigma ->
      memFraiche sigma nf ->
      sigma bInf = Some (VCEnt m) ->
      sigma borne = Some (VCEnt n) ->
      sigma (ctxRang ctxComp) = Some (VCEnt (Z.of_nat rang)) ->
      sigma (ctxNbProc ctxComp) = Some (VCEnt (Z.of_nat p)) ->
      evalCible sigma (ctxActif ctxComp) = Some (VCBool true) ->
      primCompat U B ->
      exists sigma',
        suiteLoc
          {| elMem := sigma;
             elCont :=
               KCmd
                 (finSomPar Gamma U B ctxComp i corps tCorps nf bInf borne) :: k |}
          {| elMem := sigma';
             elCont :=
               KCmd
                 (CRedTous (accSom nf)
                   (nomTemp
                     (rcProchain
                       (compCorpsSom
                         Gamma U B ctxComp i corps nf)))) :: k |} /\
        sigma' (accSom nf) =
          Some (valVersCible contribution) /\
        sigma'
          (nomTemp
            (rcProchain
              (compCorpsSom Gamma U B ctxComp i corps nf))) =
          Some (valVersCible (valNulle tCorps)) /\
        memFraiche sigma'
          (S
            (rcProchain
              (compCorpsSom Gamma U B ctxComp i corps nf))) /\
        presMem sigma sigma'.
Proof.
  intros Gamma U B ctxComp rho i corps tCorps HcorpsType HcorpsCorr
    sigma nf bInf borne m n rang p contribution k
    Hcontribution Hrep Hfrais HbInf Hborne Hrang HnbProc Hactif Hcompat.
  set (ru := compCorpsSom Gamma U B ctxComp i corps nf).
  set (res := nomTemp (rcProchain ru)).
  set (apresSi := KCmd (CSeq (CAffect res (exprNulle tCorps))
    (CRedTous (accSom nf) res)) :: k).
  set (sigmaAcc :=
    majMem sigma (accSom nf)
      (valVersCible (valNulle tCorps))).
  assert (HexecAcc :
    execLoc sigma
      (CAffect (accSom nf) (exprNulle tCorps))
      (KCmd
        (CSeq
          (brancheSomPar Gamma U B ctxComp i corps nf bInf borne)
          (CSeq (CAffect res (exprNulle tCorps))
            (CRedTous (accSom nf) res))) :: k)
      sigmaAcc).
  { apply execAffect. apply corrExprNulle. }
  assert (HfraisAcc : memFraiche sigmaAcc (S nf)).
  { subst sigmaAcc.
    apply memFraicheMaj with (debut := nf) (ecrit := nf);
      [exact Hfrais | lia]. }
  assert (HpresAcc : presMem sigma sigmaAcc).
  { subst sigmaAcc. apply presMemMajFraiche.
    apply Hfrais. lia. }
  assert (HbInfAcc : sigmaAcc bInf = Some (VCEnt m)).
  { now apply HpresAcc. }
  assert (HrangAcc :
    sigmaAcc (ctxRang ctxComp) = Some (VCEnt (Z.of_nat rang))).
  { now apply HpresAcc. }
  set (sigmaInd :=
    majMem sigmaAcc (indSom nf)
      (VCEnt (m + Z.of_nat rang))).
  assert (HexecInit :
    execLoc sigmaAcc
      (CAffect (indSom nf)
        (APlus (AVar bInf) (AVar (ctxRang ctxComp))))
      (KCmd
        (boucleSomPas Gamma U B ctxComp i corps nf
          borne (ctxNbProc ctxComp)) ::
       KEff [] ::
       apresSi)
      sigmaInd).
  { apply execAffect. simpl. now rewrite HbInfAcc, HrangAcc. }
  assert (HfraisInd :
    memFraiche sigmaInd (debutCorpsSom nf)).
  { subst sigmaInd. unfold debutCorpsSom.
    apply memFraicheMaj
      with (debut := S nf) (ecrit := S nf);
      [exact HfraisAcc | lia]. }
  assert (HpresInd : presMem sigma sigmaInd).
  { subst sigmaInd. eapply presMemTrans; [exact HpresAcc |].
    apply presMemMajFraiche. apply HfraisAcc. lia. }
  assert (HaccApresInd :
    sigmaInd (accSom nf) =
      Some (valVersCible (valNulle tCorps))).
  { subst sigmaInd sigmaAcc. rewrite majMemAutre.
    - apply majMemMeme.
    - unfold accSom, indSom. intros Heq.
      apply nomTempInj in Heq. lia. }
  assert (Hind :
    sigmaInd (indSom nf) =
      Some (VCEnt (m + Z.of_nat rang))).
  { subst sigmaInd. apply majMemMeme. }
  assert (HborneApresInd : sigmaInd borne = Some (VCEnt n)).
  { apply HpresInd. exact Hborne. }
  assert (HnbProcApresInd :
    sigmaInd (ctxNbProc ctxComp) = Some (VCEnt (Z.of_nat p))).
  { apply HpresInd. exact HnbProc. }
  assert (Hprotege : forall x cv, sigma x = Some cv ->
    x <> accSom nf /\ x <> indSom nf).
  { intros x cv Hx. split; unfold accSom, indSom;
      eapply varDefNonFraiche with (sigma := sigma) (frais := nf);
      eauto; lia. }
  destruct (Hprotege _ _ Hborne) as [HborneDiffAcc HborneDiffInd].
  destruct (Hprotege _ _ HnbProc) as [HnbProcDiffAcc HnbProcDiffInd].
  pose proof
    (corrBouclePas Gamma U B ctxComp rho i corps tCorps
      HcorpsType HcorpsCorr
      (Z.of_nat p) (m + Z.of_nat rang) n contribution
      Hcontribution
      sigma sigmaInd nf nf borne (ctxNbProc ctxComp)
      (valNulle tCorps)
      (KEff [] ::
       apresSi)
      (Nat.le_refl nf) Hfrais Hrep HpresInd HfraisInd
      HaccApresInd Hind HborneApresInd HnbProcApresInd
      HborneDiffAcc HborneDiffInd HnbProcDiffAcc HnbProcDiffInd
      (typeValNulle tCorps) Hcompat) as Hboucle.
  destruct Hboucle as
    [sigmaBoucle
      [HexecBoucle
        [HaccBoucle
          [HborneBoucle
            [HnbProcBoucle [HfraisBoucle HpresBoucle]]]]]].
  assert (HexecPour :
    execLoc sigmaAcc
      (CPour
        (CAffect (indSom nf)
          (APlus (AVar bInf) (AVar (ctxRang ctxComp))))
        (testSom nf borne)
        (incrSomPas nf (ctxNbProc ctxComp))
        (netSom Gamma U B ctxComp i corps nf)
        (corpsBoucleSom Gamma U B ctxComp i corps nf))
      (KEff [] ::
       apresSi)
      sigmaBoucle).
  { unfold execLoc in *.
    eapply transSuiteLoc.
    - apply execPourInit.
      + discriminate.
      + exact HexecInit.
    - exact HexecBoucle. }
  assert (HactifAcc :
    evalCible sigmaAcc (ctxActif ctxComp) = Some (VCBool true)).
  { apply evalCiblePres with (sigma := sigma).
    - exact HpresAcc.
    - exact Hactif. }
  assert (HexecIf :
    execLoc sigmaAcc
      (brancheSomPar Gamma U B ctxComp i corps nf bInf borne)
      (apresSi)
      sigmaBoucle).
  { unfold brancheSomPar.
    replace sigmaBoucle with (effMem sigmaBoucle []) by reflexivity.
    apply execSiVrai; assumption. }
  set (sigmaRes :=
    majMem sigmaBoucle res
      (valVersCible (valNulle tCorps))).
  assert (HexecRes :
    execLoc sigmaBoucle (CAffect res (exprNulle tCorps))
      (KCmd (CRedTous (accSom nf) res) :: k)
      sigmaRes).
  { apply execAffect. apply corrExprNulle. }
  assert (HruDebut :
    (debutCorpsSom nf <= rcProchain ru)%nat).
  { subst ru. unfold compCorpsSom. apply compFraisMono. }
  assert (HaccRes :
    sigmaRes (accSom nf) =
      Some (valVersCible contribution)).
  { subst sigmaRes res.
    rewrite majMemAutre.
    - rewrite zeroGchVals in HaccBoucle.
      + exact HaccBoucle.
      + apply
          (typeValEvalSomPas
            Gamma U B rho i corps tCorps (Z.of_nat p)
            (m + Z.of_nat rang) n contribution).
        exact Hcontribution.
    - unfold accSom. intros Heq.
      fold ru in Heq.
      apply nomTempInj in Heq.
      unfold debutCorpsSom in HruDebut. lia. }
  exists sigmaRes. repeat split.
  - subst ru res.
    eapply execPrefixeSeq3; eauto.
  - exact HaccRes.
  - subst sigmaRes. apply majMemMeme.
  - subst sigmaRes res.
    apply memFraicheMaj
      with (debut := rcProchain ru)
           (ecrit := rcProchain ru);
      [exact HfraisBoucle | lia].
  - subst sigmaRes res.
    apply presMemMajBase.
    + apply memFraicheMono with (n := nf).
      * exact Hfrais.
      * unfold debutCorpsSom in HruDebut. lia.
    + exact HpresBoucle.
Qed.


(** Montre que la compilation conserve le type. *)
Lemma corrTypeComp :
  forall Gamma U B e t,
    bienType Gamma U B e t ->
    forall ctxComp frais,
      rcType (comp e Gamma U B ctxComp frais) = t.
Proof.
  intros Gamma U B e t Htype.
  induction Htype; intros ctxComp frais; cbn [comp]; try reflexivity.
  - now rewrite H.
  - rewrite IHHtype. unfold typeResUn. now rewrite H.
  - now rewrite IHHtype1, IHHtype2.
  - apply IHHtype3.
  - destruct (contientSomPar corps); apply IHHtype3.
Qed.

(** Établit l'unicité du type d'une expression. *)
Lemma typeUnique :
  forall Gamma U B e t1 t2,
    bienType Gamma U B e t1 ->
    bienType Gamma U B e t2 ->
    t1 = t2.
Proof.
  intros Gamma U B e t1 t2 H1 H2.
  pose proof (corrTypeComp Gamma U B e t1 H1 ctx0 0%nat) as E1.
  pose proof (corrTypeComp Gamma U B e t2 H2 ctx0 0%nat) as E2.
  congruence.
Qed.

(** Relie le type d'évaluation au type statique. *)
Lemma accordTypeEval :
  forall Gamma U B e t,
    bienType Gamma U B e t ->
    forall rho t' v,
      evalExpr Gamma U B rho e t' v ->
      t' = t.
Proof.
  intros Gamma U B e t Htype.
  induction Htype; intros rho t' v Heval; inversion Heval; subst.
  - reflexivity.
  - reflexivity.
  - congruence.
  - assert (tEntree0 = tEntree).
    { eapply IHHtype. eassumption. }
    subst tEntree0. congruence.
  - assert (t0 = t1).
    { eapply IHHtype1. eassumption. }
    assert (t3 = t2).
    { eapply IHHtype2. eassumption. }
    now subst.
  - eapply typeUnique; eassumption.
  - eapply typeUnique; eassumption.
Qed.

(** Prouve la correction locale du compilateur. *)
Theorem corrCompLoc :
  forall Gamma U B e t,
    bienType Gamma U B e t ->
    contientSomPar e = false ->
    forall ctxComp rho sigma frais v,
      evalExpr Gamma U B rho e t v ->
      repEnv (ctxRepr ctxComp) rho sigma ->
      memFraiche sigma frais ->
      primCompat U B ->
      simLoc (ctxRepr ctxComp) rho sigma
        (comp e Gamma U B ctxComp frais) v.
Proof.
  intros Gamma U B e t Htype.
  induction Htype;
    intros Hpar ctxComp rho sigma frais v
      Heval Hrep Hfrais Hcompat;
    inversion Heval; subst.
  - apply simLocAffect; auto.
  - apply simLocAffect; auto.
  - unfold simLoc. simpl. intros k.
    exists sigma. repeat split.
    + apply execRien.
    + apply Hrep. assumption.
    + exact Hrep.
    + exact Hfrais.
    + apply presMemRefl.
  - remember (comp e Gamma U B ctxComp frais) as r1 eqn:Hr1.
    simpl in Hpar. specialize (IHHtype Hpar).
    destruct r1 as [c1 x1 t1 n1].
    assert (tEntree0 = tEntree).
    { eapply accordTypeEval; [exact Htype | exact H2]. }
    subst tEntree0.
    pose proof
      (IHHtype ctxComp rho sigma frais v0
        H2 Hrep Hfrais Hcompat) as IH.
    rewrite <- Hr1 in IH. simpl in IH.
    unfold simLoc in *. cbn [comp seqCmds].
    rewrite <- Hr1. simpl. intros k.
    specialize
      (IH
        (KCmd
          (CAffect (nomTemp n1)
            (APrimUn op (AVar x1))) :: k)).
    destruct IH as
      [sigma1 [Hexec1 [Hcorresp1 [Hrep1 [Hfrais1 Hpres1]]]]].
    destruct (simLocAffect _ _ _ _ _
      (semUnSrc op v0) tSortie Hrep1 Hfrais1
      (corrEvalUn U B op sigma1 x1 v0 Hcorresp1 Hcompat) k)
      as [sigma2 [Hexec2 [Hcorresp2 [Hrep2 [Hfrais2 Hpres2]]]]].
    exists sigma2. repeat split; try assumption.
    + eapply execSeq; eauto.
    + eapply presMemTrans; eauto.
  - remember (comp e1 Gamma U B ctxComp frais) as r1 eqn:Hr1.
    simpl in Hpar.
    apply Bool.orb_false_iff in Hpar as [Hpar1 Hpar2].
    specialize (IHHtype1 Hpar1).
    specialize (IHHtype2 Hpar2).
    destruct r1 as [c1 x1 ct1 n1].
    remember (comp e2 Gamma U B ctxComp n1) as r2 eqn:Hr2.
    destruct r2 as [c2 x2 ct2 n2].
    assert (t0 = t1).
    { eapply accordTypeEval; [exact Htype1 | exact H5]. }
    assert (t3 = t2).
    { eapply accordTypeEval; [exact Htype2 | exact H6]. }
    subst t0 t3.
    pose proof
      (IHHtype1 ctxComp rho sigma frais v1
        H5 Hrep Hfrais Hcompat) as IH1.
    rewrite <- Hr1 in IH1. simpl in IH1.
    unfold simLoc in *.
    cbn [comp seqCmds]. rewrite <- Hr1. simpl.
    rewrite <- Hr2. simpl. intros k.
    specialize
      (IH1
        (KCmd (CSeq c2
          (CAffect (nomTemp n2) (exprBinCible op x1 x2))) :: k)).
    destruct IH1 as
      [sigma1 [Hexec1 [Hcorresp1 [Hrep1 [Hfrais1 Hpres1]]]]].
    pose proof
      (IHHtype2 ctxComp rho sigma1 n1 v2
        H6 Hrep1 Hfrais1 Hcompat) as IH2.
    rewrite <- Hr2 in IH2. simpl in IH2.
    specialize
      (IH2
        (KCmd
          (CAffect (nomTemp n2) (exprBinCible op x1 x2)) :: k)).
    destruct IH2 as
      [sigma2 [Hexec2 [Hcorresp2 [Hrep2 [Hfrais2 Hpres2]]]]].
    assert (Hcorresp1' : resCorrespond x1 v1 sigma2).
    { eapply resPres; eauto. }
    destruct (simLocAffect _ _ _ _ _
      (valBinSrc op v1 v2) (typeResBin B op t1 t2)
      Hrep2 Hfrais2
      (corrEvalBin U B op sigma2 x1 x2 v1 v2 Hcorresp1' Hcorresp2 Hcompat) k)
      as [sigma3 [Hexec3 [Hcorresp3 [Hrep3 [Hfrais3 Hpres3]]]]].
    exists sigma3. repeat split; try assumption.
    + eapply execSeq; [exact Hexec1 |].
      eapply execSeq; eauto.
    + eapply presMemTrans; [exact Hpres1 |].
      eapply presMemTrans; eauto.
  - remember (comp a Gamma U B ctxComp frais) as ra eqn:Hra.
    simpl in Hpar.
    apply Bool.orb_false_iff in Hpar as
      [HparA HparReste].
    apply Bool.orb_false_iff in HparReste as
      [HparB HparCorps].
    specialize (IHHtype1 HparA).
    specialize (IHHtype2 HparB).
    specialize (IHHtype3 HparCorps).
    destruct ra as [ca xa ta na].
    remember (comp b Gamma U B ctxComp na) as rb eqn:Hrb.
    destruct rb as [cb xb tb nf].
    remember
      (compCorpsSom Gamma U B ctxComp i corps nf)
      as ru eqn:Hru.
    destruct ru as [cu xu tu nu].
    pose proof
      (IHHtype1 ctxComp rho sigma frais (VEnt m)
        H4 Hrep Hfrais Hcompat) as IHa.
    rewrite <- Hra in IHa. simpl in IHa.
    unfold simLoc in *.
    cbn [comp seqCmds]. rewrite <- Hra. simpl.
    rewrite <- Hrb. simpl.
    unfold compCorpsSom, indSom, debutCorpsSom in Hru.
    rewrite <- Hru. simpl.
    intros k.
    set (boucle :=
      boucleSomSeq Gamma U B ctxComp i corps nf xb).
    set (initAcc := CAffect (accSom nf) (exprNulle tu)).
    set (boucleAvecInit := CPour
      (CAffect (indSom nf) (AVar xa))
      (testSom nf xb) (incrSomSeq nf)
      (nomsTempEntre (debutCorpsSom nf) nu)
      (CSeq cu (CAffect (accSom nf)
        (APlus (AVar (accSom nf)) (AVar xu))))).
    specialize (IHa (KCmd (CSeq cb (CSeq initAcc boucleAvecInit)) :: k)).
    destruct IHa as
      [sigmaA [HexecA [HcorrespA [HrepA [HfraisA HpresA]]]]].
    pose proof
      (IHHtype2 ctxComp rho sigmaA na (VEnt n)
        H7 HrepA HfraisA Hcompat) as IHb.
    rewrite <- Hrb in IHb. simpl in IHb.
    specialize (IHb (KCmd (CSeq initAcc boucleAvecInit) :: k)).
    destruct IHb as
      [sigmaB [HexecB [HcorrespB [HrepB [HfraisB HpresB]]]]].
    assert (HcorrespA' :
      resCorrespond xa (VEnt m) sigmaB).
    { eapply resPres; eauto. }
    assert (HtuCorps : tu = tCorps).
    { change
        (rcType
          {| rcCode := cu; rcRes := xu;
             rcType := tu; rcProchain := nu |} = tCorps).
      rewrite Hru.
      apply corrTypeComp. exact Htype3. }
    set (sigmaAcc :=
      majMem sigmaB (accSom nf)
        (valVersCible (valNulle tCorps))).
    assert (HexecAcc :
      execLoc sigmaB initAcc (KCmd boucleAvecInit :: k) sigmaAcc).
    { subst initAcc sigmaAcc. apply execAffect.
      rewrite HtuCorps. apply corrExprNulle. }
    assert (HfraisLe : (frais <= nf)%nat).
    { pose proof
        (compFraisMono a Gamma U B ctxComp frais).
      pose proof
        (compFraisMono b Gamma U B ctxComp na).
      rewrite <- Hra in H. rewrite <- Hrb in H0. simpl in *. lia. }
    assert (HbasePresB : presMem sigma sigmaB).
    { eapply presMemTrans; eauto. }
    assert (HbasePresAcc : presMem sigma sigmaAcc).
    { subst sigmaAcc. apply presMemMajBase.
      - eapply memFraicheMono; [exact Hfrais | lia].
      - exact HbasePresB. }
    assert (HfraisAcc : memFraiche sigmaAcc (S nf)).
    { subst sigmaAcc. eapply memFraicheMaj; [exact HfraisB | lia]. }
    assert (HborneDiffAcc : xb <> accSom nf).
    { unfold accSom.
      eapply resNonFrais; eauto; lia. }
    assert (HborneDiffInd : xb <> indSom nf).
    { unfold indSom.
      eapply resNonFrais; eauto; lia. }
    assert (Haacc : xa <> accSom nf).
    { unfold accSom.
      eapply resNonFrais; eauto; lia. }
    assert (HcorrespAAcc :
      sigmaAcc xa = Some (VCEnt m)).
    { subst sigmaAcc. rewrite majMemAutre.
      - exact HcorrespA'.
      - exact Haacc. }
    set (sigmaInd :=
      majMem sigmaAcc (indSom nf) (VCEnt m)).
    assert (HexecInit :
      execLoc sigmaAcc
        (CAffect (indSom nf) (AVar xa))
        (KCmd boucle :: k) sigmaInd).
    { subst sigmaInd. apply execAffect.
      simpl. exact HcorrespAAcc. }
    assert (HpourInit :
      suiteLoc
        {| elMem := sigmaAcc;
           elCont := KCmd boucleAvecInit :: k |}
        {| elMem := sigmaInd; elCont := KCmd boucle :: k |}).
    { subst boucleAvecInit boucle. unfold boucleSomSeq, netSom,
        corpsBoucleSom, compCorpsSom,
        indSom, accSom, debutCorpsSom.
      rewrite <- Hru. simpl.
      unfold boucleSomSeq, netSom,
        corpsBoucleSom, compCorpsSom,
        indSom, accSom, debutCorpsSom in HexecInit.
      rewrite <- Hru in HexecInit. simpl in HexecInit.
      apply execPourInit.
      - discriminate.
      - exact HexecInit. }
    assert (HfraisInd :
      memFraiche sigmaInd (debutCorpsSom nf)).
    { subst sigmaInd. unfold debutCorpsSom.
      eapply memFraicheMaj; [exact HfraisAcc | lia]. }
    assert (HbasePresInd : presMem sigma sigmaInd).
    { subst sigmaInd. apply presMemMajBase.
      - eapply memFraicheMono; [exact Hfrais | lia].
      - exact HbasePresAcc. }
    assert (HaccApresInd :
      sigmaInd (accSom nf) =
        Some (valVersCible (valNulle tCorps))).
    { subst sigmaInd sigmaAcc. rewrite majMemAutre.
      - apply majMemMeme.
      - unfold accSom, indSom. intros Heq.
        apply nomTempInj in Heq. lia. }
    assert (HindApresInd :
      sigmaInd (indSom nf) = Some (VCEnt m)).
    { subst sigmaInd. apply majMemMeme. }
    assert (HborneApresInd : sigmaInd xb = Some (VCEnt n)).
    { subst sigmaInd sigmaAcc.
      rewrite majMemAutre; [| exact HborneDiffInd].
      rewrite majMemAutre; [exact HcorrespB | exact HborneDiffAcc]. }
    pose proof
      (corrBoucleSeq Gamma U B ctxComp rho i corps tCorps
        Htype3
        (fun rho' sigma' ctxComp' frais' val' Heval' Hrep' Hfrais' Hcompat' =>
          IHHtype3 ctxComp' rho' sigma' frais' val'
            Heval' Hrep' Hfrais' Hcompat')
        m n v H9
        sigma sigmaInd frais nf xb (valNulle tCorps) k)
      as Hboucle.
    specialize
      (Hboucle HfraisLe Hfrais Hrep HbasePresInd HfraisInd
        HaccApresInd HindApresInd HborneApresInd HborneDiffAcc HborneDiffInd
        (typeValNulle tCorps) Hcompat).
    destruct Hboucle as
      [sigmaFinal
        [HexecBoucle
          [HaccFinal
            [HborneFinal [HfraisFinal HpresFinal]]]]].
    assert (HexecPour :
      execLoc sigmaAcc boucleAvecInit k sigmaFinal).
    { unfold execLoc in *. eapply transSuiteLoc; eauto. }
    exists sigmaFinal. repeat split.
    + eapply execSeq.
      * exact HexecA.
      * eapply execSeq.
        -- exact HexecB.
        -- eapply execSeq; eauto.
    + rewrite zeroGchVals in HaccFinal.
      * exact HaccFinal.
      * eapply typeValEvalSom. exact H9.
    + eapply repEnvPres.
      * exact Hrep.
      * exact HpresFinal.
    + unfold compCorpsSom, indSom,
        debutCorpsSom in HfraisFinal.
      rewrite <- Hru in HfraisFinal. exact HfraisFinal.
    + exact HpresFinal.
  - simpl in Hpar. discriminate.
Qed.
