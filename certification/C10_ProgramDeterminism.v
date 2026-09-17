From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Relations.Relation_Operators.
From certification Require Export C09_FormulaDeterminism.

Import ListNotations.
Open Scope string_scope.

(** Une transition d'un processus ne dépend pas de l'ordonnancement global. *)
Theorem detPasLoc :
  forall s s1 s2,
    pasLoc s s1 -> pasLoc s s2 -> s1 = s2.
Proof.
  intros s s1 s2 H1 H2.
  inversion H1; subst; inversion H2; subst; try contradiction; congruence.
Qed.

(** Présentation inductive d'un pas local à une position quelconque de la liste. *)
Inductive pasProc : configGlob -> configGlob -> Prop :=
| PasProcTete : forall s s' suite,
    pasLoc s s' -> pasProc (s :: suite) (s' :: suite)
| PasProcQueue : forall s suite suite',
    pasProc suite suite' -> pasProc (s :: suite) (s :: suite').

Lemma pasProcPosition :
  forall q s s' suite,
    pasLoc s s' ->
    pasProc (List.app q (s :: suite)) (List.app q (s' :: suite)).
Proof.
  induction q; intros; simpl; constructor; auto.
Qed.

Lemma pasProcGlob :
  forall g g', pasProc g g' -> pasGlob g g'.
Proof.
  assert (Hreleve : forall g g', pasProc g g' ->
    forall q, pasGlob (List.app q g) (List.app q g')).
  { intros g g' Hpas. induction Hpas; intros q.
    - now apply PasGlobal.
    - specialize (IHHpas (List.app q [s])).
      rewrite <- !List.app_assoc in IHHpas. exact IHHpas. }
  intros g g' Hpas. exact (Hreleve g g' Hpas []).
Qed.

(** Deux processus distincts avancent indépendamment ; sur le même processus,
    le déterminisme local impose le même successeur. *)
Lemma diamantPasProc :
  forall g g1 g2,
    pasProc g g1 -> pasProc g g2 ->
    g1 = g2 \/ exists commun,
      pasProc g1 commun /\ pasProc g2 commun.
Proof.
  intros g g1 g2 H1. revert g2.
  induction H1; intros g2 H2;
    inversion H2 as [s0 s2 queue Hloc2 | s0 queue queue2 Hqueue2]; subst.
  - left. f_equal. eapply detPasLoc; eauto.
  - right. eexists. split; [apply PasProcQueue | apply PasProcTete]; eauto.
  - right. eexists. split; [apply PasProcTete | apply PasProcQueue]; eauto.
  - destruct (IHpasProc _ Hqueue2) as [Heq | [commun [Hgch Hdrt]]].
    + left. now subst.
    + right. exists (s :: commun). split; now apply PasProcQueue.
Qed.

(** Un collectif prêt bloque tous les pas locaux : aucun processus ne peut
    franchir seul un Allreduce. *)
Lemma redPreteBloqueProc :
  forall g g', pasProc g g' ->
    forall x y vals, entreesRedTous x y g = Some vals -> False.
Proof.
  intros g g' Hpas. induction Hpas; intros x y vals Hentrees;
    destruct s as [sigma k]; destruct k as [|cadre k];
    simpl in Hentrees; try discriminate;
    destruct cadre as [c|xs]; try discriminate;
    destruct c; try discriminate.
  - inversion H.
  - destruct (andb (String.eqb x v) (String.eqb y v0)); try discriminate.
    destruct (sigma x); try discriminate.
    destruct (entreesRedTous x y suite) eqn:Hqueue; try discriminate.
    eapply IHHpas; eauto.
Qed.

Definition pasRedTous
  (g : configGlob) : option configGlob :=
  match g with
  | [] => None
  | {| elMem := _;
       elCont := KCmd (CRedTous x y) :: _ |} :: _ =>
      match entreesRedTous x y g with
      | Some vals =>
          match somValsCible vals with
          | Some total => Some (finRedTous y total g)
          | None => None
          end
      | None => None
      end
  | _ => None
  end.

Lemma pasRedTousComplet :
  forall g x y vals total,
    entreesRedTous x y g = Some vals ->
    somValsCible vals = Some total ->
    pasRedTous g =
      Some (finRedTous y total g).
Proof.
  intros g x y vals total Hentrees Hsom.
  destruct g as [|[sigma k] suite].
  - simpl in Hentrees. injection Hentrees as <-. discriminate.
  - destruct k as [|cadre k]; simpl in Hentrees; try discriminate.
    destruct cadre as [c|xs]; simpl in Hentrees; try discriminate.
    destruct c; simpl in Hentrees; try discriminate.
    destruct (andb (String.eqb x v) (String.eqb y v0))
      eqn:Hnoms; try discriminate.
    apply andb_true_iff in Hnoms as [Hx Hy].
    apply String.eqb_eq in Hx, Hy. subst v v0.
    simpl.
    rewrite Hentrees.
    rewrite !String.eqb_refl. simpl.
    rewrite Hsom. reflexivity.
Qed.

Theorem detRedTous :
  forall g x1 y1 vals1 total1 x2 y2 vals2 total2,
    entreesRedTous x1 y1 g = Some vals1 ->
    somValsCible vals1 = Some total1 ->
    entreesRedTous x2 y2 g = Some vals2 ->
    somValsCible vals2 = Some total2 ->
    finRedTous y1 total1 g = finRedTous y2 total2 g.
Proof.
  intros g x1 y1 vals1 total1 x2 y2 vals2 total2
    Hentrees1 Hsom1 Hentrees2 Hsom2.
  pose proof
    (pasRedTousComplet
      g x1 y1 vals1 total1 Hentrees1 Hsom1) as Hpas1.
  pose proof
    (pasRedTousComplet
      g x2 y2 vals2 total2 Hentrees2 Hsom2) as Hpas2.
  congruence.
Qed.

Lemma casPasGlob :
  forall g g', pasGlob g g' ->
    pasProc g g' \/
    exists x y vals total,
      entreesRedTous x y g = Some vals /\
      somValsCible vals = Some total /\
      g' = finRedTous y total g.
Proof.
  intros g g' Hpas. destruct Hpas.
  - left. now apply pasProcPosition.
  - right. exists x, y, vals, total. auto.
Qed.

(** Les choix d'ordonnancement se rejoignent après au plus un pas de chaque côté.
    Un collectif ne concurrence jamais un pas local. *)
Theorem diamantPasGlob :
  forall g g1 g2,
    pasGlob g g1 -> pasGlob g g2 ->
    g1 = g2 \/ exists commun,
      pasGlob g1 commun /\ pasGlob g2 commun.
Proof.
  intros g g1 g2 H1 H2.
  destruct (casPasGlob _ _ H1) as
    [Hloc1 | [x1 [y1 [vals1 [total1 [Hin1 [Hsom1 Heq1]]]]]]];
  destruct (casPasGlob _ _ H2) as
    [Hloc2 | [x2 [y2 [vals2 [total2 [Hin2 [Hsom2 Heq2]]]]]]].
  - destruct (diamantPasProc _ _ _ Hloc1 Hloc2)
      as [Heq | [commun [Hgch Hdrt]]].
    + now left.
    + right. exists commun. split; now apply pasProcGlob.
  - exfalso. eapply redPreteBloqueProc; eauto.
  - exfalso. eapply redPreteBloqueProc; eauto.
  - left. subst g1 g2. eapply detRedTous; eauto.
Qed.

Definition terminalGlob (g : configGlob) : Prop :=
  forall g', ~ pasGlob g g'.

(** Un choix différent du premier pas conserve l'accès à un état terminal atteint. *)
Lemma pasVersTerminal :
  forall g final,
    suiteGlob g final -> terminalGlob final ->
    forall suivant, pasGlob g suivant -> suiteGlob suivant final.
Proof.
  intros g final Hexec. induction Hexec as [g | g inter final Hpremier Hreste IH];
    intros Hterminal suivant Hsuivant.
  - exfalso. eapply Hterminal; eauto.
  - destruct (diamantPasGlob _ _ _ Hsuivant Hpremier)
      as [Heq | [commun [Hgch Hdrt]]].
    + now subst suivant.
    + eapply rt1n_trans; [exact Hgch |].
      eapply IH; eauto.
Qed.

Theorem configTerminaleUnique :
  forall initial final1 final2,
    suiteGlob initial final1 -> suiteGlob initial final2 ->
    terminalGlob final1 -> terminalGlob final2 ->
    final1 = final2.
Proof.
  intros initial final1 final2 Hexec1. revert final2.
  induction Hexec1 as [g | g suivant final1 Hpremier Hreste IH];
    intros final2 Hexec2 Hterminal1 Hterminal2.
  - inversion Hexec2; subst; [reflexivity |].
    exfalso. eapply Hterminal1; eauto.
  - apply IH; try assumption.
    eapply pasVersTerminal; eauto.
Qed.

Lemma etatsFinauxSansPas :
  forall Sigma g, ~ pasProc (etatsFinaux Sigma []) g.
Proof.
  induction Sigma as [|sigma suite IH]; intros g Hpas;
    inversion Hpas as [s s' queue Hloc | s queue queue' Hqueue]; subst.
  - inversion Hloc.
  - eapply IH; eauto.
Qed.

Lemma etatsFinauxTerminaux :
  forall Sigma, terminalGlob (etatsFinaux Sigma []).
Proof.
  intros Sigma g Hpas.
  destruct (casPasGlob _ _ Hpas) as
    [Hloc | [x [y [vals [total [Hentrees [Hsom _]]]]]]].
  - eapply etatsFinauxSansPas; eauto.
  - destruct Sigma; simpl in Hentrees; try discriminate.
    injection Hentrees as <-. discriminate.
Qed.

(** Même relation que dans C08, avec une continuation vide pour observer
    la fin du programme, plutôt qu'un état intermédiaire de sa continuation. *)
Definition execGlob
  (Sigma : list mem) (c : cmd) (Sigma' : list mem) : Prop :=
  suiteGlob (etatsEnCours Sigma c []) (etatsFinaux Sigma' []).

Theorem detProgMPI :
  forall Sigma c Sigma1 Sigma2,
    execGlob Sigma c Sigma1 ->
    execGlob Sigma c Sigma2 ->
    Sigma1 = Sigma2.
Proof.
  intros Sigma c Sigma1 Sigma2 Hexec1 Hexec2.
  assert (Hfinal : etatsFinaux Sigma1 [] = etatsFinaux Sigma2 []).
  { eapply configTerminaleUnique;
      eauto using etatsFinauxTerminaux. }
  apply (f_equal (map elMem)) in Hfinal.
  unfold etatsFinaux in Hfinal. rewrite !map_map in Hfinal.
  now rewrite !map_id in Hfinal.
Qed.

Lemma longueurPasGlob :
  forall g g', pasGlob g g' -> length g = length g'.
Proof.
  intros g g' Hpas. destruct Hpas.
  - rewrite !length_app. reflexivity.
  - clear H H0. induction g as [|[sigma k] suite IH]; simpl; [reflexivity |].
    destruct k as [|cadre k]; simpl; try now rewrite IH.
    destruct cadre as [c|xs]; simpl; try now rewrite IH.
    destruct c; simpl; now rewrite IH.
Qed.

Lemma longueurExecGlob :
  forall Sigma c Sigma', execGlob Sigma c Sigma' ->
    length Sigma = length Sigma'.
Proof.
  intros Sigma c Sigma' Hexec.
  assert (Hlongueur : forall g g', suiteGlob g g' -> length g = length g').
  { intros g g' HpasSuite. induction HpasSuite; [reflexivity |].
    erewrite longueurPasGlob; eauto. }
  apply Hlongueur in Hexec.
  unfold etatsEnCours, etatsFinaux in Hexec.
  now rewrite !length_map in Hexec.
Qed.
