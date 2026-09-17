
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Reals.Reals.
From Stdlib Require Import Relations.Relation_Operators.
From Stdlib Require Import Lia.
From certification Require Export C05_LocalCorrectness.

Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope R_scope.

(** Construit les états exécutant un même code. *)
Definition etatsEnCours
  (Sigma : list mem) (c : cmd) (k : cont) : configGlob :=
  map (fun sigma =>
    {| elMem := sigma; elCont := KCmd c :: k |}) Sigma.

(** Construit les états ayant atteint une continuation. *)
Definition etatsFinaux
  (Sigma : list mem) (k : cont) : configGlob :=
  map (fun sigma =>
    {| elMem := sigma; elCont := k |}) Sigma.

(** Lit une variable dans une liste de mémoires. *)
Fixpoint lireMems
  (x : var) (Sigma : list mem) : option (list valCible) :=
  match Sigma with
  | [] => Some []
  | sigma :: suite =>
      match sigma x, lireMems x suite with
      | Some v, Some vals => Some (v :: vals)
      | _, _ => None
      end
  end.

(** Caractérise les entrées d'un Allreduce global. *)
Lemma entreesRedEnCours :
  forall Sigma x y k,
    entreesRedTous x y
      (etatsEnCours Sigma (CRedTous x y) k) =
    lireMems x Sigma.
Proof.
  induction Sigma as [|sigma suite IH]; intros x y k; simpl.
  - reflexivity.
  - now rewrite !String.eqb_refl, IH.
Qed.

(** Caractérise les états après un Allreduce global. *)
Lemma finRedEnCours :
  forall Sigma x y total k,
    finRedTous y total
      (etatsEnCours Sigma (CRedTous x y) k) =
    etatsFinaux
      (map (fun sigma => majMem sigma y total) Sigma) k.
Proof.
  induction Sigma as [|sigma suite IH]; intros x y total k; simpl.
  - reflexivity.
  - now rewrite IH.
Qed.

(** Relie la réduction cible à la somme source. *)
Lemma corrSomValsCible :
  forall t vals,
    vals <> [] ->
    Forall (fun val => valTypee val t) vals ->
    somValsCible (map valVersCible vals) =
    Some (valVersCible (somVals t vals)).
Proof.
  intros t vals. induction vals as [|val vals IH];
    intros HnonVide Htype.
  - contradiction.
  - inversion Htype as [|? ? Hval Hvals]; subst.
    destruct vals as [|suivant suite].
    + simpl. rewrite zeroDrtVals; [reflexivity | exact Hval].
    + change
        (match
           somValsCible
             (map valVersCible (suivant :: suite))
         with
         | Some reste => additionCible (valVersCible val) reste
         | None => None
         end =
         Some
           (valVersCible
             (additionVals val (somVals t (suivant :: suite))))).
      rewrite (IH ltac:(discriminate) Hvals).
      apply corrAdditionCible.
Qed.

(** Exécute globalement un Allreduce prêt. *)
Lemma execRedTous :
  forall Sigma x y vals total k,
    lireMems x Sigma = Some vals ->
    somValsCible vals = Some total ->
    suiteGlob
      (etatsEnCours Sigma (CRedTous x y) k)
      (etatsFinaux
        (map (fun sigma => majMem sigma y total) Sigma) k).
Proof.
  intros Sigma x y vals total k Hvals Hsom.
  unfold suiteGlob. eapply rt1n_trans.
  - apply PasRedTous
      with (x := x) (y := y) (vals := vals) (total := total).
    + now rewrite entreesRedEnCours.
    + exact Hsom.
  - rewrite finRedEnCours. constructor.
Qed.

(** Lève une exécution locale en exécution globale. *)
Lemma releverExecLoc :
  forall s s',
    suiteLoc s s' ->
    forall q suite,
      suiteGlob
        (List.app q (s :: suite))
        (List.app q (s' :: suite)).
Proof.
  intros s s' HpasSuite.
  induction HpasSuite as [|x y z Hpas Hreste IH];
    intros q suite.
  - constructor.
  - unfold suiteGlob. eapply rt1n_trans.
    + apply PasGlobal. exact Hpas.
    + apply IH.
Qed.

(** Lève toutes les exécutions locales correspondantes. *)
Lemma releverExecsLoc :
  forall etats etats',
    Forall2 suiteLoc etats etats' ->
    forall q,
      suiteGlob
        (List.app q etats)
        (List.app q etats').
Proof.
  intros etats etats' Hetats.
  induction Hetats as [|s s' suite suite' Htete Hqueue IH]; intros q.
  - constructor.
  - eapply transSuiteGlob.
    + apply releverExecLoc. exact Htete.
    + specialize (IH (List.app q [s'])).
      rewrite <- !List.app_assoc in IH. exact IH.
Qed.

(** Ouvre globalement une commande séquentielle. *)
Lemma ouvrirSeqGlob :
  forall Sigma c1 c2 k,
    suiteGlob
      (etatsEnCours Sigma (CSeq c1 c2) k)
      (etatsEnCours Sigma c1 (KCmd c2 :: k)).
Proof.
  intros Sigma c1 c2 k.
  apply releverExecsLoc with (q := []).
  induction Sigma as [|sigma Sigma IH].
  - constructor.
  - constructor.
    + unfold suiteLoc. eapply rt1n_trans.
      * apply PasSeq.
      * constructor.
    + exact IH.
Qed.

(** Relie Forall2 aux éléments de même indice. *)
Lemma pourTous2Indice :
  forall (A B : Type) (P : A -> B -> Prop) xs ys indice x y,
    Forall2 P xs ys ->
    nth_error xs indice = Some x ->
    nth_error ys indice = Some y ->
    P x y.
Proof.
  intros A B P xs ys indice x y Hrelation. revert indice x y.
  induction Hrelation; intros [|indice] x0 y0 Hx Hy;
    simpl in Hx, Hy; try discriminate.
  - now injection Hx as <-; injection Hy as <-.
  - eapply IHHrelation; eauto.
Qed.

(** Relation point à point entre trois listes. *)
Inductive PourTous3 {A B C : Type} (P : A -> B -> C -> Prop)
  : list A -> list B -> list C -> Prop :=
| PourTous3Vide : PourTous3 P [] [] []
| PourTous3Ajout :
    forall x y z xs ys zs,
      P x y z ->
      PourTous3 P xs ys zs ->
      PourTous3 P (x :: xs) (y :: ys) (z :: zs).

(** Construit PourTous3 à partir des éléments indexés. *)
Lemma pourTous3DepuisIndices :
  forall (A B : Type) (P : nat -> A -> B -> Prop)
    p (xs : list A) (ys : list B),
    length xs = p ->
    length ys = p ->
    (forall indice x y,
      nth_error xs indice = Some x ->
      nth_error ys indice = Some y ->
      P indice x y) ->
    PourTous3 P (seq 0 p) xs ys.
Proof.
  intros A B P p. revert P.
  induction p as [|p IH]; intros P xs ys Hxs Hys Hnth.
  - destruct xs, ys; try discriminate. constructor.
  - destruct xs as [|x xs], ys as [|y ys]; try discriminate.
    simpl in Hxs, Hys. injection Hxs as Hxs. injection Hys as Hys.
    simpl. constructor.
    + apply Hnth with (indice := 0%nat); reflexivity.
    + rewrite <- seq_shift.
      assert (Hdecale :
        forall rangs vals mems,
          PourTous3 (fun rang val mem => P (S rang) val mem)
            rangs vals mems ->
          PourTous3 P (map S rangs) vals mems).
      { intros rangs vals mems Hrelation.
        induction Hrelation; simpl; constructor; assumption. }
      apply Hdecale.
      apply (IH (fun rang val mem => P (S rang) val mem)
        xs ys Hxs Hys).
      intros indice val mem Hval Hmem.
      apply Hnth with (indice := S indice);
        assumption.
Qed.


(** Collecte les résultats de toutes les simulations locales. *)
Lemma reunirSimsLoc :
  forall mu rho Sigma r v frais,
    (forall sigma,
      repEnv mu rho sigma ->
      memFraiche sigma frais ->
      simLoc mu rho sigma r v) ->
    repsEnv mu rho Sigma ->
    initFraiche Sigma frais ->
    forall k,
      exists Sigma',
        Forall2
          (fun sigma sigma' =>
            execLoc sigma (rcCode r) k sigma')
          Sigma Sigma' /\
        Forall
          (resCorrespond (rcRes r) v) Sigma' /\
        repsEnv mu rho Sigma' /\
        initFraiche Sigma' (rcProchain r) /\
        Forall2 presMem Sigma Sigma'.
Proof.
  intros mu rho Sigma r v frais Hcorr Hrep Hfrais k.
  unfold repsEnv, initFraiche in *.
  revert Hrep Hfrais.
  induction Sigma as [|sigma suite IHSigma]; intros Hrep Hfrais.
  - exists []. repeat split; constructor.
  - inversion Hrep as [|? ? HrepTete HrepQueue]; subst.
    inversion Hfrais as [|? ? HfraisTete HfraisQueue]; subst.
    pose proof
      (Hcorr sigma HrepTete HfraisTete) as Hloc.
    unfold simLoc in Hloc.
    specialize (Hloc k).
    destruct Hloc as
      [sigma' [Hexec [Hcorresp [Hrep' [Hfrais' Hpres]]]]].
    specialize (IHSigma HrepQueue HfraisQueue).
    destruct IHSigma as
      [Sigma'
        [Hexecs [Hcorresps [Hreps [HfraisS HpresMems]]]]].
    exists (sigma' :: Sigma'). repeat split; constructor; assumption.
Qed.

(** Assemble des exécutions locales en exécution globale. *)
Lemma reunirExecsLoc :
  forall Sigma Sigma' c k,
    Forall2
      (fun sigma sigma' => execLoc sigma c k sigma')
      Sigma Sigma' ->
    forall q,
      suiteGlob
        (List.app q (etatsEnCours Sigma c k))
        (List.app q (etatsFinaux Sigma' k)).
Proof.
  intros Sigma Sigma' c k Hexec q.
  apply releverExecsLoc.
  induction Hexec.
  - constructor.
  - constructor; assumption.
Qed.
