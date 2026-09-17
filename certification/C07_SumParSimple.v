
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Reals.Reals.
From Stdlib Require Import Relations.Relation_Operators.
From Stdlib Require Import Lia.
From certification Require Export C06_GlobalExecution.

Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope R_scope.

(** Décrit un processus prêt à contribuer au SumPar. *)
Definition pretSomPar
  (Gamma : envTypes) (U : envSigsUn) (B : envSigsBin)
  (ctxComp : ctx) (rho : env) (i : var) (corps : expr) (tCorps : typeNum)
  (nf : nat) (bInf borne : var) (m n : Z) (p : nat)
  (rang : nat) (contribution : val) (sigma : mem) : Prop :=
  evalSomPas Gamma U B rho i corps tCorps (Z.of_nat p)
    (m + Z.of_nat rang) n contribution /\
  repEnv (ctxRepr ctxComp) rho sigma /\
  memFraiche sigma nf /\
  sigma bInf = Some (VCEnt m) /\
  sigma borne = Some (VCEnt n) /\
  sigma (ctxRang ctxComp) = Some (VCEnt (Z.of_nat rang)) /\
  sigma (ctxNbProc ctxComp) = Some (VCEnt (Z.of_nat p)) /\
  evalCible sigma (ctxActif ctxComp) = Some (VCBool true).

(** Exécute le SumPar depuis des processus actifs prêts. *)
Lemma redSomParDepuisPrets :
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
    primCompat U B ->
    forall nf bInf borne m n p rangs vals Sigma total k,
      PourTous3
        (pretSomPar Gamma U B ctxComp rho i corps tCorps
          nf bInf borne m n p)
        rangs vals Sigma ->
      vals <> [] ->
      somVals tCorps vals = total ->
      exists Sigma',
        suiteGlob
          (etatsEnCours Sigma
            (finSomPar Gamma U B ctxComp i corps tCorps nf bInf borne) k)
          (etatsFinaux Sigma' k) /\
        Forall
          (resCorrespond
            (nomTemp
              (rcProchain
                (compCorpsSom Gamma U B ctxComp i corps nf)))
            total) Sigma'.
Proof.
  intros Gamma U B ctxComp rho i corps tCorps HcorpsType HcorpsCorr Hcompat
    nf bInf borne m n p rangs vals Sigma total k
    Hpret HnonVide Htotal.
  assert (Htype :
    Forall (fun val => valTypee val tCorps) vals).
  { clear HnonVide Htotal.
    induction Hpret; constructor; auto.
    destruct H as [Heval _]. eapply typeValEvalSomPas; eauto. }
  assert (Hcollect :
    exists SigmaPre,
      Forall2 suiteLoc
        (etatsEnCours Sigma
          (finSomPar Gamma U B ctxComp i corps tCorps nf bInf borne) k)
        (etatsEnCours SigmaPre
          (CRedTous (accSom nf)
            (nomTemp
              (rcProchain
                (compCorpsSom Gamma U B ctxComp i corps nf)))) k) /\
      lireMems (accSom nf) SigmaPre =
        Some (map valVersCible vals)).
  { clear HnonVide Htotal Htype.
    induction Hpret as
        [|rang contribution sigma rangs vals Sigma
          Htete Hqueue IH].
    - exists []. split; constructor.
    - destruct Htete as
        [HpasSom
          [Hrep [Hfrais
            [HbInf [Hborne [Hrang [HnbProc Hactif]]]]]]].
      destruct
        (procSomParVersRed
          Gamma U B ctxComp rho i corps tCorps HcorpsType HcorpsCorr
          sigma nf bInf borne m n rang p contribution k
          HpasSom Hrep Hfrais HbInf Hborne Hrang HnbProc Hactif Hcompat)
        as [sigma' [Hexec [Hacc [Hres [Hfrais' Hpres]]]]].
      destruct IH as [SigmaPre [Hexecs Hvals]].
      exists (sigma' :: SigmaPre). split.
      + constructor; assumption.
      + simpl. now rewrite Hacc, Hvals. }
  destruct Hcollect as [SigmaPre [Hloc Hentrees]].
  set (res :=
    nomTemp
      (rcProchain
        (compCorpsSom Gamma U B ctxComp i corps nf))).
  set (totalCible := valVersCible total).
  set (SigmaFinal :=
    map (fun sigma => majMem sigma res totalCible) SigmaPre).
  exists SigmaFinal. split.
  - eapply transSuiteGlob.
    + apply releverExecsLoc with (q := []) in Hloc.
      simpl in Hloc. exact Hloc.
    + subst res totalCible SigmaFinal.
      apply execRedTous
        with (vals := map valVersCible vals).
      * exact Hentrees.
      * rewrite <- Htotal.
        apply corrSomValsCible; assumption.
  - subst SigmaFinal res totalCible.
    apply Forall_forall. intros sigma Hin.
    apply in_map_iff in Hin as [avant [Heq Hin]].
    subst sigma. unfold resCorrespond.
    apply majMemMeme.
Qed.


(** Décrit une configuration globale initiale cohérente. *)
Definition initCoherente
  (p : nat) (rho : env) (Sigma : list mem) : Prop :=
  (1 <= p)%nat /\
  length Sigma = p /\
  forall rang sigma,
    nth_error Sigma rang = Some sigma ->
    repEnv (fun x => x) rho sigma /\
    sigma "rang" = Some (VCEnt (Z.of_nat rang)) /\
    sigma "nbProc" = Some (VCEnt (Z.of_nat p)) /\
    sigma "actif" = Some (VCBool true).


(** Déduit la représentation depuis la cohérence initiale. *)
Lemma repInitCoherente :
  forall p rho Sigma,
    initCoherente p rho Sigma ->
    repsEnv (ctxRepr ctx0) rho Sigma.
Proof.
  intros p rho Sigma [_ [_ Hcoherent]].
  unfold repsEnv. apply Forall_forall.
  intros sigma Hin.
  apply In_nth_error in Hin as [rang Hrang].
  specialize (Hcoherent rang sigma Hrang).
  simpl. tauto.
Qed.

(** Prépare tous les processus après les bornes. *)
Lemma pretsSomParApresBornes :
  forall Gamma U B rho i corps tCorps nf bInf borne m n p
    vals Sigma0 Sigma,
    initCoherente p rho Sigma0 ->
    valsParPas Gamma U B rho i corps tCorps m n p vals ->
    Forall2 presMem Sigma0 Sigma ->
    repsEnv (ctxRepr ctx0) rho Sigma ->
    initFraiche Sigma nf ->
    Forall (resCorrespond bInf (VEnt m)) Sigma ->
    Forall (resCorrespond borne (VEnt n)) Sigma ->
    PourTous3
      (pretSomPar Gamma U B ctx0 rho i corps tCorps
        nf bInf borne m n p)
      (seq 0 p) vals Sigma.
Proof.
  intros Gamma U B rho i corps tCorps nf bInf borne m n p
    vals Sigma0 Sigma
    Hcoherent HpasSoms HpresMems Hrep Hfrais HbInf Hborne.
  destruct Hcoherent as [Hp [Hnb0 Hinitial]].
  destruct HpasSoms as [HnbVals HpasSoms].
  unfold repsEnv in Hrep.
  unfold initFraiche in Hfrais.
  assert (HnbSigma : length Sigma = p).
  { rewrite <- Hnb0. now apply Forall2_length in HpresMems. }
  apply pourTous3DepuisIndices; [exact HnbVals | exact HnbSigma |].
  intros rang contribution sigma Hcontribution Hsigma.
  assert (HrangBorne : (rang < p)%nat).
  { assert (Hpresent : nth_error Sigma rang <> None).
    { rewrite Hsigma. discriminate. }
    apply nth_error_Some in Hpresent. now rewrite HnbSigma in Hpresent. }
  destruct (nth_error Sigma0 rang) as [sigma0|] eqn:Hsigma0.
  2: { apply nth_error_None in Hsigma0. lia. }
  specialize (Hinitial rang sigma0 Hsigma0).
  destruct Hinitial as
    [Hrep0 [Hrang [HnbProc Hactif]]].
  assert (HpresMem : presMem sigma0 sigma).
  { eapply pourTous2Indice; eauto. }
  apply nth_error_In in Hsigma.
  unfold resCorrespond in HbInf, Hborne.
  rewrite Forall_forall in Hrep, Hfrais, HbInf, Hborne.
  split; [now apply HpasSoms with (rang := rang) |].
  repeat split; auto.

Qed.

(** Compose point à point deux préservations de mémoires. *)
Lemma transPresMems :
  forall Sigma1 Sigma2 Sigma3,
    Forall2 presMem Sigma1 Sigma2 ->
    Forall2 presMem Sigma2 Sigma3 ->
    Forall2 presMem Sigma1 Sigma3.
Proof.
  intros Sigma1 Sigma2 Sigma3 H12. revert Sigma3.
  induction H12; intros Sigma3 H23; inversion H23; subst;
    constructor; eauto using presMemTrans.
Qed.

(** Préserve point à point un résultat compilé. *)
Lemma presResMems :
  forall x val Sigma1 Sigma2,
    Forall (resCorrespond x val) Sigma1 ->
    Forall2 presMem Sigma1 Sigma2 ->
    Forall (resCorrespond x val) Sigma2.
Proof.
  intros x val Sigma1 Sigma2 Hcorresps HpresMems.
  induction HpresMems.
  - constructor.
  - inversion Hcorresps; subst. constructor.
    + eapply resPres; eauto.
    + now apply IHHpresMems.
Qed.


