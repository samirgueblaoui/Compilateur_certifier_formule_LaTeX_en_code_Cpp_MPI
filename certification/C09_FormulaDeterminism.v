From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Reals.Reals.
From Stdlib Require Import Lia.
From certification Require Export C08_Correctness.

Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope R_scope.

(** Les primitives totales abstraites respectent leurs signatures source.
    Cette hypothèse est distincte de l'égalité des interprétations source/cible. *)
Definition primSrcTypees (U : envSigsUn) (B : envSigsBin) : Prop :=
  (forall op tEntree tSortie v,
    U op tEntree = Some tSortie -> valTypee v tEntree ->
    valTypee (semUnSrc op v) tSortie) /\
  (forall op t1 t2 tSortie v1 v2,
    B op t1 t2 = Some tSortie ->
    valTypee v1 t1 -> valTypee v2 t2 ->
    valTypee (semBinSrc op v1 v2) tSortie).

Lemma envCompatLieEnt :
  forall Gamma rho i n,
    envCompat Gamma rho ->
    envCompat (lierTypeEnt Gamma i) (majEnv rho i (VEnt n)).
Proof.
  intros Gamma rho i n Henv x t Htype.
  unfold lierTypeEnt in Htype. unfold majEnv.
  destruct (String.eqb x i).
  - injection Htype as <-. exists (VEnt n). split; [reflexivity | exact I].
  - now apply Henv.
Qed.

Lemma typeValBinSrc :
  forall U B op t1 t2 v1 v2,
    primSrcTypees U B ->
    sigBinValide B op t1 t2 ->
    valTypee v1 t1 -> valTypee v2 t2 ->
    valTypee (valBinSrc op v1 v2)
      (typeResBin B op t1 t2).
Proof.
  intros U B op t1 t2 v1 v2 [_ Hbin] Hsig H1 H2.
  destruct op.
  - destruct t1, t2, v1, v2; simpl in *; tauto.
  - destruct t1, t2, v1, v2; simpl in *; tauto.
  - destruct Hsig as [tSortie Hsig]. simpl. rewrite Hsig.
    eapply Hbin; eauto.
Qed.

(** Une somme finie existe dès que chacune de ses expressions élémentaires existe.
    L'induction porte sur une borne naturelle de la longueur de l'intervalle. *)
Lemma evalSomExiste :
  forall Gamma U B rho i corps t,
    (forall n, exists v,
      evalExpr (lierTypeEnt Gamma i) U B
        (majEnv rho i (VEnt n)) corps t v) ->
    forall m n, exists v, evalSom Gamma U B rho i m n corps t v.
Proof.
  intros Gamma U B rho i corps t Hcorps.
  assert (HborneLong : forall nbIter m n,
    (n - m + 1 <= Z.of_nat nbIter)%Z ->
    exists v, evalSom Gamma U B rho i m n corps t v).
  { induction nbIter as [|nbIter IH]; intros m n Hnb.
    - exists (valNulle t). constructor. simpl in Hnb. lia.
    - destruct (Z_lt_dec n m) as [Hvide | Hintervalle].
      + exists (valNulle t). now constructor.
      + destruct (Hcorps m) as [v Hv].
        destruct (IH (m + 1)%Z n) as [reste Hreste].
        { rewrite Nat2Z.inj_succ in Hnb. lia. }
        exists (additionVals v reste). econstructor; eauto; lia. }
  intros m n. apply (HborneLong (Z.to_nat (n - m + 1)) m n).
  destruct (Z_le_dec 0 (n - m + 1)) as [HnonNeg | Hnegatif].
  - rewrite Z2Nat.id; lia.
  - pose proof (Nat2Z.is_nonneg (Z.to_nat (n - m + 1))). lia.
Qed.

(** Existence source pour tout le langage, indépendamment du fragment compilé certifié. *)
Theorem evalExprExiste :
  forall Gamma U B e t,
    bienType Gamma U B e t ->
    primSrcTypees U B ->
    forall rho, envCompat Gamma rho ->
      exists v, evalExpr Gamma U B rho e t v.
Proof.
  intros Gamma U B e t Htype Hprim.
  induction Htype; intros rho Henv.
  { exists (VEnt n). constructor. }
  { exists (VFlot r). constructor. }
  { destruct (Henv x t H) as [v [Hval Htype]].
    exists v. econstructor; eauto. }
  { destruct (IHHtype Hprim rho Henv) as [v Hv].
    exists (semUnSrc op v). econstructor; eauto.
    destruct Hprim as [Hun _]. eapply Hun; eauto.
    eapply typeValEvalExpr; eauto. }
  { destruct (IHHtype1 Hprim rho Henv) as [v1 Hv1].
    destruct (IHHtype2 Hprim rho Henv) as [v2 Hv2].
    exists (valBinSrc op v1 v2). econstructor; eauto.
    eapply typeValBinSrc; eauto using typeValEvalExpr. }
  (* SumSeq et SumPar partagent exactement la même évaluation source. *)
  all: destruct (IHHtype1 Hprim rho Henv) as [va Ha];
    destruct (IHHtype2 Hprim rho Henv) as [vb Hb];
    pose proof (typeValEvalExpr _ _ _ _ _ _ _ Ha) as Hta;
    pose proof (typeValEvalExpr _ _ _ _ _ _ _ Hb) as Htb;
    destruct va as [m|r]; [| contradiction];
    destruct vb as [n|r]; [| contradiction];
    assert (HcorpsExists : forall j, exists v,
      evalExpr (lierTypeEnt Gamma i) U B
        (majEnv rho i (VEnt j)) corps tCorps v)
      by (intro j; apply IHHtype3; [exact Hprim |
        now apply envCompatLieEnt]);
    destruct (evalSomExiste Gamma U B rho i corps tCorps HcorpsExists m n)
      as [v Hv];
    exists v; econstructor; eauto.
Qed.

(** Le jugement de typage associe au plus un type à une formule. *)
Lemma detTypeExpr :
  forall Gamma U B e t1 t2,
    bienType Gamma U B e t1 ->
    bienType Gamma U B e t2 ->
    t1 = t2.
Proof.
  intros Gamma U B e t1 t2 H1 H2.
  eapply typeUnique; eassumption.
Qed.


Scheme indDetExpr := Induction for evalExpr Sort Prop
with indDetSom := Induction for evalSom Sort Prop.

Combined Scheme indDetExprSom
  from indDetExpr, indDetSom.

Lemma detExprSomMutuel :
  forall Gamma U B,
    (forall rho e t v,
      evalExpr Gamma U B rho e t v ->
      forall t' v',
        evalExpr Gamma U B rho e t' v' ->
        t = t' /\ v = v') /\
    (forall rho i m n corps tCorps v,
      evalSom Gamma U B rho i m n corps tCorps v ->
      forall v',
        evalSom Gamma U B rho i m n corps tCorps v' ->
        v = v').
Proof.
  intros Gamma U B.
  apply (indDetExprSom
    (fun Gamma U B rho e t v _ =>
      forall t' v',
        evalExpr Gamma U B rho e t' v' ->
        t = t' /\ v = v')
    (fun Gamma U B rho i m n corps tCorps v _ =>
      forall v',
        evalSom Gamma U B rho i m n corps tCorps v' ->
        v = v')).
  { intros Gamma0 U0 B0 rho n t' v' Hdeuxieme.
    inversion Hdeuxieme; subst. auto. }
  { intros Gamma0 U0 B0 rho r t' v' Hdeuxieme.
    inversion Hdeuxieme; subst. auto. }
  { intros Gamma0 U0 B0 rho x t v Hgamma Hrho Htype t' v' Hdeuxieme.
    inversion Hdeuxieme; subst.
    split; congruence. }
  { intros Gamma0 U0 B0 rho op e tEntree tSortie v Heval IH HU Htype
      t' v' Hdeuxieme.
    clear Heval.
    inversion Hdeuxieme; subst.
    match goal with
    | HsousExpr : evalExpr Gamma0 U0 B0 rho e _ _ |- _ =>
        specialize (IH _ _ HsousExpr) as [HtEntree Hv]
    end.
    subst. split; congruence. }
  { intros Gamma0 U0 B0 rho op e1 e2 t1 t2 v1 v2 Heval1 IH1
      Heval2 IH2 Hsig Htype t' v' Hdeuxieme.
    clear Heval1 Heval2.
    inversion Hdeuxieme; subst.
    match goal with
    | Hgch : evalExpr Gamma0 U0 B0 rho e1 _ _,
      Hdrt : evalExpr Gamma0 U0 B0 rho e2 _ _ |- _ =>
        specialize (IH1 _ _ Hgch) as [Ht1 Hv1];
        specialize (IH2 _ _ Hdrt) as [Ht2 Hv2]
    end.
    subst. auto. }
  (* Les deux règles de somme ont les mêmes prémisses sémantiques. *)
  all: try solve [
    intros Gamma0 U0 B0 rho i a b corps m n tCorps v HevalA IHa
      HevalB IHb Hcorps Hsom IHsum t' v' Hdeuxieme;
    clear HevalA HevalB Hsom;
    inversion Hdeuxieme; subst;
    match goal with
    | Hsom2 : evalSom Gamma0 U0 B0 rho i ?m2 ?n2 corps ?tCorps2 _,
      Ha2 : evalExpr Gamma0 U0 B0 rho a TEnt (VEnt ?m2),
      Hb2 : evalExpr Gamma0 U0 B0 rho b TEnt (VEnt ?n2),
      Hcorps2 : bienType (lierTypeEnt Gamma0 i) U0 B0 corps ?tCorps2
      |- _ =>
        specialize (IHa _ _ Ha2) as [_ Hm];
        specialize (IHb _ _ Hb2) as [_ Hn];
        injection Hm as Hm; injection Hn as Hn; subst;
        assert (HtCorps : tCorps = tCorps2)
          by (eapply detTypeExpr; eassumption);
        subst tCorps2;
        specialize (IHsum _ Hsom2); auto
    end ].
  - intros Gamma0 U0 B0 rho i m n corps tCorps Hvide v' Hdeuxieme.
    inversion Hdeuxieme; subst; try reflexivity; lia.
  - intros Gamma0 U0 B0 rho i m n corps tCorps v1 vReste Hintervalle
      HevalCorps IHcorps HevalReste IHreste v' Hdeuxieme.
    clear HevalCorps HevalReste.
    inversion Hdeuxieme; subst; try lia.
    match goal with
    | Hcorps2 : evalExpr (lierTypeEnt Gamma0 i) U0 B0
        (majEnv rho i (VEnt m)) corps tCorps _,
      Hreste2 : evalSom Gamma0 U0 B0 rho i (m + 1) n corps tCorps _
      |- _ =>
        specialize (IHcorps _ _ Hcorps2) as [_ Hv1];
        specialize (IHreste _ Hreste2) as Hvrest;
        subst; reflexivity
    end.
Qed.


Theorem detEvalExpr :
  forall Gamma U B rho e t1 v1 t2 v2,
    evalExpr Gamma U B rho e t1 v1 ->
    evalExpr Gamma U B rho e t2 v2 ->
    t1 = t2 /\ v1 = v2.
Proof.
  intros Gamma U B rho e t1 v1 t2 v2 H1 H2.
  destruct (detExprSomMutuel Gamma U B) as [Hdet _].
  eapply Hdet; eassumption.
Qed.

Corollary evalExprExisteUnique :
  forall Gamma U B rho e t,
    bienType Gamma U B e t ->
    envCompat Gamma rho ->
    primSrcTypees U B ->
    exists! v, evalExpr Gamma U B rho e t v.
Proof.
  intros Gamma U B rho e t Htype Henv Hprim.
  destruct (evalExprExiste Gamma U B e t Htype Hprim rho Henv)
    as [v Hv].
  exists v. split; [exact Hv |].
  intros v' Hv'. eapply detEvalExpr; eauto.
Qed.

Corollary detEvalSom :
  forall Gamma U B rho i m n corps tCorps v1 v2,
    evalSom Gamma U B rho i m n corps tCorps v1 ->
    evalSom Gamma U B rho i m n corps tCorps v2 ->
    v1 = v2.
Proof.
  intros Gamma U B rho i m n corps tCorps v1 v2 H1 H2.
  destruct (detExprSomMutuel Gamma U B) as [_ Hdet].
  eapply Hdet; eassumption.
Qed.

Lemma detEvalSomPas :
  forall Gamma U B rho i corps tCorps pas courant bSup v1,
    evalSomPas Gamma U B rho i corps tCorps pas
      courant bSup v1 ->
    forall v2,
      evalSomPas Gamma U B rho i corps tCorps pas
        courant bSup v2 ->
      v1 = v2.
Proof.
  intros Gamma U B rho i corps tCorps pas courant bSup v1 Hpremier.
  induction Hpremier as
      [courant bSup Hvide
      |courant bSup vCourant vReste Hintervalle Hcorps Hreste IHreste];
    intros v2 Hdeuxieme.
  - inversion Hdeuxieme; subst; try reflexivity; lia.
  - inversion Hdeuxieme; subst; try lia.
    match goal with
    | Hcorps2 : evalExpr (lierTypeEnt Gamma i) U B
        (majEnv rho i (VEnt courant)) corps tCorps ?vCourant2,
      Hreste2 : evalSomPas Gamma U B rho i corps tCorps pas
        (courant + pas) bSup ?vReste2
      |- additionVals vCourant vReste = additionVals ?vCourant2 ?vReste2 =>
        pose proof
          (detEvalExpr
            _ _ _ _ _ _ _ _ _ Hcorps Hcorps2) as [_ Hcourant];
        specialize (IHreste _ Hreste2);
        subst; reflexivity
    end.
Qed.

Corollary accordSomSeqPar :
  forall Gamma U B rho i a b corps tSeq vSeq tPar vPar,
    evalExpr Gamma U B rho (ESomSeq i a b corps) tSeq vSeq ->
    evalExpr Gamma U B rho (ESomPar i a b corps) tPar vPar ->
    tSeq = tPar /\ vSeq = vPar.
Proof.
  intros Gamma U B rho i a b corps tSeq vSeq tPar vPar
    Hseq Hpar.
  inversion Hpar; subst.
  eapply detEvalExpr.
  - exact Hseq.
  - econstructor; eassumption.
Qed.
