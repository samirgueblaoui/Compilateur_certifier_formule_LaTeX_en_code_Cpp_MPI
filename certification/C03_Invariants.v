
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Reals.Reals.
From Stdlib Require Import Relations.Relation_Operators.
From Stdlib Require Import Lia.
From certification Require Export C02_SmallStep.

Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope R_scope.


(** Relie une variable cible à la valeur source calculée. *)
Definition resCorrespond
  (x : var) (v : val) (sigma : mem) : Prop :=
  sigma x = Some (valVersCible v).

(** Relie une mémoire cible à un environnement source. *)
Definition repEnv
  (mu : var -> var) (rho : env) (sigma : mem) : Prop :=
  forall x v,
    rho x = Some v ->
    sigma (mu x) = Some (valVersCible v).


Definition repsEnv
  (mu : var -> var) (rho : env) (Sigma : list mem) : Prop :=
  Forall (repEnv mu rho) Sigma.

(** Exprime la fraîcheur des temporaires d'une mémoire. *)
Definition memFraiche (sigma : mem) (frais : nat) : Prop :=
  forall n, (frais <= n)%nat -> sigma (nomTemp n) = None.

Definition initFraiche (Sigma : list mem) (frais : nat) : Prop :=
  Forall (fun sigma => memFraiche sigma frais) Sigma.

(** Relie les valeurs source à leurs types déclarés. *)
Definition envCompat (Gamma : envTypes) (rho : env) : Prop :=
  forall x t,
    Gamma x = Some t ->
    exists v, rho x = Some v /\ valTypee v t.

Definition presMem (avant apres : mem) : Prop :=
  forall x v, avant x = Some v -> apres x = Some v.

(** Préserve l'évaluation cible entre deux mémoires compatibles. *)
Lemma evalCiblePres :
  forall sigma sigma' a val,
    presMem sigma sigma' ->
    evalCible sigma a = Some val ->
    evalCible sigma' a = Some val.
Proof.
  intros sigma sigma' a. induction a; intros val Hpres Heval;
    simpl in Heval |- *; try exact Heval; try solve [now apply Hpres].
  (* Tous les constructeurs suivent le même raisonnement sur leurs arguments. *)
  all: repeat match type of Heval with
       | context [evalCible ?s ?arg] =>
           let Harg := fresh "Harg" in
           destruct (evalCible s arg) eqn:Harg; try discriminate
       end.
  all: repeat match goal with
       | IH : forall v, presMem ?s ?s' ->
                Some ?cv = Some v -> evalCible ?s' ?arg = Some v |- _ =>
           specialize (IH cv Hpres eq_refl); rewrite IH
       end.
  all: try exact Heval.
  all: repeat match goal with v : valCible |- _ => destruct v end;
       simpl in Heval |- *; try discriminate; exact Heval.
Qed.

Definition simLoc
  (mu : var -> var) (rho : env) (sigma : mem)
  (r : resComp) (v : val) : Prop :=
  forall k,
    exists sigma',
      execLoc sigma (rcCode r) k sigma' /\
      resCorrespond (rcRes r) v sigma' /\
      repEnv mu rho sigma' /\
      memFraiche sigma' (rcProchain r) /\
      presMem sigma sigma'.

Lemma majMemMeme :
  forall sigma x v,
    majMem sigma x v x = Some v.
Proof.
  intros. unfold majMem. now rewrite String.eqb_refl.
Qed.

Lemma majMemAutre :
  forall sigma x y v,
    y <> x ->
    majMem sigma x v y = sigma y.
Proof.
  intros sigma x y v Hneq. unfold majMem.
  apply String.eqb_neq in Hneq. now rewrite Hneq.
Qed.


(** Inverse la conversion d'une valeur source. *)
Lemma allerRetourVal :
  forall v, cibleVersVal (valVersCible v) = Some v.
Proof.
  now intros [].
Qed.

Lemma nomNatInj :
  forall n m, nomNat n = nomNat m -> n = m.
Proof.
  induction n as [| n IH]; destruct m as [| m]; simpl; intros H;
    try discriminate.
  - reflexivity.
  - f_equal. apply IH. now injection H.
Qed.

Lemma nomTempInj :
  forall n m, nomTemp n = nomTemp m -> n = m.
Proof.
  intros n m H. apply nomNatInj.
  unfold nomTemp in H. now injection H.
Qed.

Lemma dansTempDepuis :
  forall debut nb n,
    In (nomTemp n) (nomsTempDepuis debut nb) <->
    (debut <= n < debut + nb)%nat.
Proof.
  intros debut nb. revert debut.
  induction nb as [| nb IH]; intros debut n; simpl.
  - lia.
  - split.
    + intros [Heq | Hin].
      * apply nomTempInj in Heq. lia.
      * apply (IH (S debut) n) in Hin. lia.
    + intros Hintervalle.
      destruct (Nat.eq_dec n debut) as [-> | Hneq].
      * now left.
      * right. apply (IH (S debut) n). lia.
Qed.

(** Borne l'indice d'un temporaire intermédiaire. *)
Lemma dansTempEntre :
  forall debut fin n,
    (debut <= fin)%nat ->
    (In (nomTemp n) (nomsTempEntre debut fin) <->
     (debut <= n < fin)%nat).
Proof.
  intros debut fin n Hle. unfold nomsTempEntre.
  rewrite dansTempDepuis.
  replace (debut + (fin - debut))%nat with fin by lia.
  reflexivity.
Qed.

(** Retrouve l'indice d'un temporaire intermédiaire. *)
Lemma dansTempEntreExiste :
  forall debut fin x,
    (debut <= fin)%nat ->
    In x (nomsTempEntre debut fin) ->
    exists n, x = nomTemp n /\ (debut <= n < fin)%nat.
Proof.
  intros debut fin x Hle.
  unfold nomsTempEntre.
  remember (fin - debut)%nat as nb eqn:Hnb.
  revert debut fin Hle Hnb.
  induction nb as [| nb IH]; intros debut fin Hle Hnb Hin; simpl in Hin.
  - contradiction.
  - destruct Hin as [Heq | Hin].
    + exists debut. split; [now symmetry | lia].
    + destruct (IH (S debut) fin) as [n [Hn Hintervalle]]; try lia.
      * exact Hin.
      * exists n. split; [exact Hn | lia].
Qed.

(** Préserve une case absente de la liste supprimée. *)
Lemma effMemHors :
  forall sigma xs x,
    ~ In x xs ->
    effMem sigma xs x = sigma x.
Proof.
  intros sigma xs. revert sigma.
  induction xs as [| y suite IH]; intros sigma x Hnon; simpl.
  - reflexivity.
  - rewrite IH.
    + unfold majMem.
      destruct (String.eqb x y) eqn:Heq; [| reflexivity].
      apply String.eqb_eq in Heq. subst. exfalso.
      apply Hnon. now left.
    + intros Hin. apply Hnon. now right.
Qed.

(** Supprime effectivement une case listée. *)
Lemma effMemDans :
  forall sigma xs x,
    In x xs ->
    effMem sigma xs x = None.
Proof.
  intros sigma xs. revert sigma.
  induction xs as [| y suite IH]; intros sigma x Hin; simpl in *.
  - contradiction.
  - destruct Hin as [-> | Hin].
    + destruct (in_dec String.string_dec x suite) as [Hx | Hx].
      * apply IH. exact Hx.
      * rewrite effMemHors; [| exact Hx].
        now rewrite String.eqb_refl.
    + apply IH. exact Hin.
Qed.

(** Affaiblit un seuil de fraîcheur. *)
Lemma memFraicheMono :
  forall sigma n n',
    memFraiche sigma n ->
    (n <= n')%nat ->
    memFraiche sigma n'.
Proof.
  unfold memFraiche. intros sigma n n' Hfrais Hle k Hk.
  apply Hfrais. lia.
Qed.

(** Préserve la fraîcheur après une écriture fraîche. *)
Lemma memFraicheMaj :
  forall sigma debut ecrit v,
    memFraiche sigma debut ->
    (debut <= ecrit)%nat ->
    memFraiche
      (majMem sigma (nomTemp ecrit) v) (S ecrit).
Proof.
  unfold memFraiche. intros sigma debut ecrit v Hfrais Hle n Hn.
  rewrite majMemAutre.
  - apply Hfrais. lia.
  - intros Heq. apply nomTempInj in Heq. lia.
Qed.

(** Préserve la fraîcheur après une écriture. *)
Lemma memFraicheMajAvant :
  forall sigma debut ecrit v,
    memFraiche sigma debut ->
    (ecrit < debut)%nat ->
    memFraiche
      (majMem sigma (nomTemp ecrit) v) debut.
Proof.
  unfold memFraiche. intros sigma debut ecrit v Hfrais Hlt n Hn.
  rewrite majMemAutre.
  - apply Hfrais. exact Hn.
  - intros Heq. apply nomTempInj in Heq. lia.
Qed.

(** Rétablit la fraîcheur après le nettoyage. *)
Lemma memFraicheApresNet :
  forall sigma debut fin,
    (debut <= fin)%nat ->
    memFraiche sigma fin ->
    memFraiche
      (effMem sigma (nomsTempEntre debut fin)) debut.
Proof.
  unfold memFraiche. intros sigma debut fin Hle Hfrais n Hn.
  destruct (lt_dec n fin) as [Hlt | Hge].
  - apply effMemDans.
    apply dansTempEntre; lia.
  - rewrite effMemHors.
    + apply Hfrais. lia.
    + intros Hin. apply dansTempEntre in Hin; lia.
Qed.

(** Établit la réflexivité de la préservation. *)
Lemma presMemRefl :
  forall sigma, presMem sigma sigma.
Proof.
  intros sigma x v H. exact H.
Qed.

(** Établit la transitivité de la préservation. *)
Lemma presMemTrans :
  forall sigma1 sigma2 sigma3,
    presMem sigma1 sigma2 ->
    presMem sigma2 sigma3 ->
    presMem sigma1 sigma3.
Proof.
  unfold presMem. eauto.
Qed.

(** Préserve l'ancienne mémoire lors d'une écriture fraîche. *)
Lemma presMemMajFraiche :
  forall sigma x v,
    sigma x = None ->
    presMem sigma (majMem sigma x v).
Proof.
  unfold presMem. intros sigma x v Habsent y cv Hy.
  destruct (String.string_dec y x) as [-> | Hneq].
  - rewrite Habsent in Hy. discriminate.
  - now rewrite majMemAutre.
Qed.

(** Propage une préservation après une écriture fraîche. *)
Lemma presMemMajBase :
  forall base sigma n v,
    memFraiche base n ->
    presMem base sigma ->
    presMem base (majMem sigma (nomTemp n) v).
Proof.
  unfold presMem. intros base sigma n v Hfrais Hpres x cv Hx.
  rewrite majMemAutre.
  - apply Hpres. exact Hx.
  - intros Heq. subst x.
    rewrite Hfrais in Hx; [discriminate | lia].
Qed.

(** Préserve la base après nettoyage des temporaires. *)
Lemma presMemEffTemps :
  forall base sigma debut fin,
    (debut <= fin)%nat ->
    memFraiche base debut ->
    presMem base sigma ->
    presMem base
      (effMem sigma (nomsTempEntre debut fin)).
Proof.
  unfold presMem.
  intros base sigma debut fin Hle Hfrais Hpres x cv Hx.
  rewrite effMemHors.
  - apply Hpres. exact Hx.
  - intros Hin.
    apply dansTempEntreExiste in Hin
      as [n [Hxname Hintervalle]]; [| exact Hle].
    subst x. rewrite Hfrais in Hx; [discriminate | lia].
Qed.

(** Conserve la représentation d'un environnement. *)
Lemma repEnvPres :
  forall mu rho sigma sigma',
    repEnv mu rho sigma ->
    presMem sigma sigma' ->
    repEnv mu rho sigma'.
Proof.
  unfold repEnv, presMem. eauto.
Qed.

(** Conserve une valeur compilée déjà calculée. *)
Lemma resPres :
  forall x v sigma sigma',
    resCorrespond x v sigma ->
    presMem sigma sigma' ->
    resCorrespond x v sigma'.
Proof.
  unfold resCorrespond, presMem. eauto.
Qed.

(** Une affectation fraîche fournit les mêmes garanties de simulation,
    quelle que soit l'expression cible qui calcule la valeur. *)
Lemma simLocAffect :
  forall mu rho sigma frais a v t,
    repEnv mu rho sigma -> memFraiche sigma frais ->
    evalCible sigma a = Some (valVersCible v) ->
    simLoc mu rho sigma
      {| rcCode := CAffect (nomTemp frais) a;
         rcRes := nomTemp frais; rcType := t;
         rcProchain := S frais |} v.
Proof.
  intros mu rho sigma frais a v t Hrep Hfrais Heval k.
  assert (Hpres : presMem sigma
    (majMem sigma (nomTemp frais) (valVersCible v))).
  { apply presMemMajFraiche. apply Hfrais. lia. }
  exists (majMem sigma (nomTemp frais) (valVersCible v)).
  cbn. repeat split.
  - now apply execAffect.
  - apply majMemMeme.
  - eapply repEnvPres; eauto.
  - apply memFraicheMaj with (debut := frais); [exact Hfrais | lia].
  - exact Hpres.
Qed.

Lemma repEnvLieEnt :
  forall ctxComp rho sigma i ind n,
    repEnv (ctxRepr ctxComp) rho sigma ->
    sigma ind = Some (VCEnt n) ->
    repEnv (ctxRepr (lierVarCtx ctxComp i ind))
      (majEnv rho i (VEnt n)) sigma.
Proof.
  intros ctxComp rho sigma i ind n Hrep Hind x v Hlecture.
  unfold majEnv in Hlecture. simpl.
  destruct (String.eqb x i) eqn:Heq.
  - apply String.eqb_eq in Heq. subst x.
    inversion Hlecture. subst v. exact Hind.
  - apply Hrep. exact Hlecture.
Qed.

(** Relie le zéro cible au zéro source. *)
Lemma corrExprNulle :
  forall sigma t,
    evalCible sigma (exprNulle t) =
    Some (valVersCible (valNulle t)).
Proof.
  now intros sigma [].
Qed.

(** Relie l'addition cible à l'addition source. *)
Lemma corrAdditionCible :
  forall v1 v2,
    additionCible (valVersCible v1) (valVersCible v2) =
    Some (valVersCible (additionVals v1 v2)).
Proof.
  now intros [] [].
Qed.

(** Relie la multiplication cible à la multiplication source. *)
Lemma corrMultCible :
  forall v1 v2,
    multCible (valVersCible v1) (valVersCible v2) =
    Some (valVersCible (multVals v1 v2)).
Proof.
  now intros [] [].
Qed.

(** Préserve le type lors d'une addition source. *)
Lemma typeAdditionVals :
  forall t v1 v2,
    valTypee v1 t ->
    valTypee v2 t ->
    valTypee (additionVals v1 v2) t.
Proof.
  intros [] [] []; simpl; tauto.
Qed.

(** Donne le type de la valeur nulle. *)
Lemma typeValNulle :
  forall t, valTypee (valNulle t) t.
Proof.
  now intros [].
Qed.

(** Établit que zéro est neutre à gauche. *)
Lemma zeroGchVals :
  forall t v,
    valTypee v t ->
    additionVals (valNulle t) v = v.
Proof.
  intros [] []; simpl; intros H; try contradiction;
    f_equal; ring.
Qed.

(** Établit que zéro est neutre à droite. *)
Lemma zeroDrtVals :
  forall t v,
    valTypee v t ->
    additionVals v (valNulle t) = v.
Proof.
  intros [] []; simpl; intros H; try contradiction;
    f_equal; ring.
Qed.

(** Établit l'associativité de l'addition des valeurs. *)
Lemma assocAdditionVals :
  forall t v1 v2 v3,
    valTypee v1 t ->
    valTypee v2 t ->
    valTypee v3 t ->
    additionVals (additionVals v1 v2) v3 =
    additionVals v1 (additionVals v2 v3).
Proof.
  intros [] [] [] []; simpl; intros H1 H2 H3;
    try contradiction; f_equal; ring.
Qed.

(** Établit la commutativité de l'addition des valeurs. *)
Lemma commAdditionVals :
  forall t v1 v2,
    valTypee v1 t ->
    valTypee v2 t ->
    additionVals v1 v2 = additionVals v2 v1.
Proof.
  intros [] [] []; simpl; intros H1 H2;
    try contradiction; f_equal; ring.
Qed.

(** Additionne une liste de valeurs source. *)
Fixpoint somVals (t : typeNum) (vals : list val) : val :=
  match vals with
  | [] => valNulle t
  | val :: suite => additionVals val (somVals t suite)
  end.

(** Donne le type d'une somme de valeurs. *)
Lemma typeSomVals :
  forall t vals,
    Forall (fun val => valTypee val t) vals ->
    valTypee (somVals t vals) t.
Proof.
  intros t vals Hvals. induction Hvals; simpl.
  - apply typeValNulle.
  - now apply typeAdditionVals.
Qed.

Lemma somValsConcat :
  forall t gch drt,
    Forall (fun val => valTypee val t) gch ->
    Forall (fun val => valTypee val t) drt ->
    somVals t (gch ++ drt) =
    additionVals (somVals t gch) (somVals t drt).
Proof.
  intros t gch drt Hgch Hdrt.
  induction Hgch as [|premier gch Hpremier Hgch IH]; simpl.
  - symmetry. apply zeroGchVals.
    now apply typeSomVals.
  - rewrite IH.
    symmetry.
    apply
      (assocAdditionVals t premier
        (somVals t gch) (somVals t drt)).
    + exact Hpremier.
    + now apply typeSomVals.
    + now apply typeSomVals.
Qed.


(** Déduit le type des résultats d'évaluation source. *)
Lemma typeValEvalExpr :
  forall Gamma U B rho e t v,
    evalExpr Gamma U B rho e t v ->
    valTypee v t
with typeValEvalSom :
  forall Gamma U B rho i m n corps t v,
    evalSom Gamma U B rho i m n corps t v ->
    valTypee v t.
Proof.
  - intros Gamma U B rho e t v Heval. destruct Heval;
      simpl; eauto using typeValEvalSom.
  - intros Gamma U B rho i m n corps t v Heval. destruct Heval;
      eauto using typeValNulle, typeAdditionVals,
        typeValEvalExpr, typeValEvalSom.
Qed.

Lemma typeValEvalSomPas :
  forall Gamma U B rho i corps t pas courant bSup val,
    evalSomPas Gamma U B rho i corps t pas
      courant bSup val ->
    valTypee val t.
Proof.
  intros Gamma U B rho i corps t pas courant bSup val Heval.
  induction Heval.
  - apply typeValNulle.
  - apply typeAdditionVals.
    + eapply typeValEvalExpr. exact H0.
    + exact IHHeval.
Qed.

(** Liste les contributions d'une partition par rang. *)
Definition valsParPas
  (Gamma : envTypes) (U : envSigsUn) (B : envSigsBin)
  (rho : env) (i : var) (corps : expr) (t : typeNum)
  (bInf bSup : Z) (p : nat) (vals : list val) : Prop :=
  length vals = p /\
  forall rang val,
    nth_error vals rang = Some val ->
    evalSomPas Gamma U B rho i corps t (Z.of_nat p)
      (bInf + Z.of_nat rang) bSup val.

(** Calcule la somme d'une répétition de zéros. *)
Lemma somZeros :
  forall t p,
    somVals t (repeat (valNulle t) p) = valNulle t.
Proof.
  intros t p. induction p; simpl.
  - reflexivity.
  - rewrite IHp. apply zeroGchVals.
    apply typeValNulle.
Qed.


(** Décompose une somme en contributions par rang. *)
Lemma partitionSomCyclique :
  forall Gamma U B rho i corps t bInf bSup total,
    evalSom Gamma U B rho i bInf bSup corps t total ->
    forall p,
      (1 <= p)%nat ->
      exists vals,
        valsParPas Gamma U B rho i corps t
          bInf bSup p vals /\
        somVals t vals = total.
Proof.
  intros Gamma U B rho i corps t bInf bSup total Hsom.
  induction Hsom as
      [Gamma0 U0 B0 rho0 i0 bInf0 bSup0 corps0 t0 Hvide
      | Gamma0 U0 B0 rho0 i0 bInf0 bSup0 corps0 t0
        courant reste Hle Hcourant Hreste IH].
  - intros p Hp.
    exists (repeat (valNulle t0) p). split.
    + split; [apply repeat_length |].
      intros rang val Hrang.
      apply nth_error_In in Hrang.
      apply repeat_spec in Hrang. subst val.
      apply EvalPasVide. lia.
    + apply somZeros.
  - intros p Hp.
    destruct (IH p Hp) as [vals [HpasSoms Htotal]].
    destruct HpasSoms as [Hlongueur HpasSoms].
    assert (HvalsNonVide : vals <> []).
    { intros ->. simpl in Hlongueur. lia. }
    apply exists_last in HvalsNonVide as
      [initial [dernier Hvals]].
    subst vals.
    rewrite length_app in Hlongueur. simpl in Hlongueur.
    assert (Hdernier :
      evalSomPas Gamma0 U0 B0 rho0 i0 corps0 t0
        (Z.of_nat p)
        (bInf0 + Z.of_nat p) bSup0 dernier).
    { specialize
        (HpasSoms (length initial) dernier).
      rewrite nth_error_app2 in HpasSoms by lia.
      replace (length initial - length initial)%nat with 0%nat
        in HpasSoms by lia.
      simpl in HpasSoms.
      specialize (HpasSoms eq_refl).
      replace
        ((bInf0 + 1 + Z.of_nat (length initial))%Z)
        with ((bInf0 + Z.of_nat p)%Z) in HpasSoms.
      - exact HpasSoms.
      - assert
          (Z.of_nat p = (Z.of_nat (length initial) + 1)%Z).
        { rewrite <- Hlongueur, Nat2Z.inj_add. simpl. lia. }
        lia. }
    exists (additionVals courant dernier :: initial). split.
    + split.
      * simpl. lia.
      * intros rang val Hrang.
        destruct rang as [|rang].
        -- simpl in Hrang. injection Hrang as <-.
           replace (bInf0 + Z.of_nat 0)%Z with bInf0 by lia.
           apply EvalPasEtape.
           ++ exact Hle.
           ++ exact Hcourant.
           ++ exact Hdernier.
        -- simpl in Hrang.
           assert (HrangInitial :
             nth_error (initial ++ [dernier]) rang = Some val).
           { rewrite nth_error_app1.
             - exact Hrang.
             - apply nth_error_Some. rewrite Hrang. discriminate. }
           specialize (HpasSoms rang val HrangInitial).
           replace
             ((bInf0 + Z.of_nat (S rang))%Z)
             with ((bInf0 + 1 + Z.of_nat rang)%Z) by
             (rewrite Nat2Z.inj_succ; lia).
           exact HpasSoms.
    + assert (HinitialType :
        Forall (fun val => valTypee val t0) initial).
      { apply Forall_forall. intros val Hin.
        apply In_nth_error in Hin as [rang Hrang].
        eapply typeValEvalSomPas.
        apply HpasSoms with (rang := rang).
        rewrite nth_error_app1.
        - exact Hrang.
        - apply nth_error_Some. rewrite Hrang. discriminate. }
      assert (HdernierType : valTypee dernier t0).
      { apply
          (typeValEvalSomPas
            Gamma0 U0 B0 rho0 i0 corps0 t0 (Z.of_nat p)
            (bInf0 + Z.of_nat p) bSup0 dernier).
        exact Hdernier. }
      assert (HcourantBienType : valTypee courant t0).
      { apply
          (typeValEvalExpr
            (lierTypeEnt Gamma0 i0) U0 B0
            (majEnv rho0 i0 (VEnt bInf0)) corps0 t0 courant).
        exact Hcourant. }
      assert (HinitialSomType :
        valTypee (somVals t0 initial) t0).
      { now apply typeSomVals. }
      assert (Hconcat :
        somVals t0 (initial ++ [dernier]) =
        additionVals (somVals t0 initial) dernier).
      { rewrite (somValsConcat t0 initial [dernier]).
        - simpl. now rewrite zeroDrtVals.
        - exact HinitialType.
        - constructor; [exact HdernierType | constructor]. }
      simpl.
      rewrite
        (assocAdditionVals t0 courant dernier (somVals t0 initial)
          HcourantBienType HdernierType HinitialSomType).
      rewrite
        (commAdditionVals t0 dernier (somVals t0 initial)
          HdernierType HinitialSomType).
      rewrite <- Hconcat. now rewrite Htotal.
Qed.

(** Justifie l'évaluation cible d'une primitive unaire. *)
Lemma corrEvalUn :
  forall U B op sigma x v,
    resCorrespond x v sigma ->
    primCompat U B ->
    evalCible sigma (APrimUn op (AVar x)) =
    Some (valVersCible (semUnSrc op v)).
Proof.
  intros U B op sigma x v Hx [Hun _].
  simpl. unfold resCorrespond in Hx.
  rewrite Hx, allerRetourVal, Hun. reflexivity.
Qed.

(** Justifie l'évaluation cible d'une opération binaire. *)
Lemma corrEvalBin :
  forall U B op sigma x y v1 v2,
    resCorrespond x v1 sigma ->
    resCorrespond y v2 sigma ->
    primCompat U B ->
    evalCible sigma (exprBinCible op x y) =
    Some (valVersCible (valBinSrc op v1 v2)).
Proof.
  intros U B op sigma x y v1 v2 Hx Hy Hcompat.
  destruct op; simpl; unfold resCorrespond in *;
    rewrite Hx, Hy.
  - apply corrAdditionCible.
  - apply corrMultCible.
  - destruct Hcompat as [_ Hbin].
    rewrite !allerRetourVal, Hbin. reflexivity.
Qed.

(** Montre que la compilation avance l'indice frais. *)
Lemma compFraisMono :
  forall e Gamma U B ctxComp frais,
    (frais <= rcProchain (comp e Gamma U B ctxComp frais))%nat.
Proof.
  induction e; intros Gamma U B ctxComp frais; cbn [comp]; try lia.
  all: try destruct (contientSomPar e3); cbn.
  (* Chaque appel récursif avance son propre indice ; on compose ces bornes. *)
  all: repeat match goal with
    | IH : forall Gamma U B ctxComp frais,
        (frais <= rcProchain (comp ?corps Gamma U B ctxComp frais))%nat
      |- context [comp ?corps ?Gamma ?U ?B ?ctxComp ?frais] =>
        let H := fresh "Hsuivant" in
        pose proof (IH Gamma U B ctxComp frais) as H; clear IH
    end; lia.
Qed.
