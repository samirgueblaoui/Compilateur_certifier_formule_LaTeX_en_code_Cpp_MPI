
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Reals.Reals.
From Stdlib Require Import Relations.Relation_Operators.
From Stdlib Require Import Lia.
From certification Require Export C01_TargetCompiler.

Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope R_scope.


(** Convertit une valeur source en valeur cible. *)
Definition valVersCible (v : val) : valCible :=
  match v with
  | VEnt n => VCEnt n
  | VFlot r => VCFlot r
  end.


Definition cibleVersVal (v : valCible) : option val :=
  match v with
  | VCEnt n => Some (VEnt n)
  | VCFlot r => Some (VFlot r)
  | VCBool _ => None
  end.

(** Met à jour une case de la mémoire cible. *)
Definition majMem (sigma : mem) (x : var) (v : valCible) : mem :=
  fun y => if String.eqb y x then Some v else sigma y.

(** Supprime une liste de variables de la mémoire. *)
Fixpoint effMem (sigma : mem) (xs : list var) : mem :=
  match xs with
  | [] => sigma
  | x :: suite =>
      effMem
        (fun y => if String.eqb y x then None else sigma y) suite
  end.

(** Additionne deux valeurs cibles. *)
Definition additionCible (v1 v2 : valCible) : option valCible :=
  match v1, v2 with
  | VCEnt n1, VCEnt n2 => Some (VCEnt (n1 + n2))
  | VCEnt n1, VCFlot r2 => Some (VCFlot (IZR n1 + r2))
  | VCFlot r1, VCEnt n2 => Some (VCFlot (r1 + IZR n2))
  | VCFlot r1, VCFlot r2 => Some (VCFlot (r1 + r2))
  | _, _ => None
  end.

Definition multCible (v1 v2 : valCible) : option valCible :=
  match v1, v2 with
  | VCEnt n1, VCEnt n2 => Some (VCEnt (n1 * n2))
  | VCEnt n1, VCFlot r2 => Some (VCFlot (IZR n1 * r2))
  | VCFlot r1, VCEnt n2 => Some (VCFlot (r1 * IZR n2))
  | VCFlot r1, VCFlot r2 => Some (VCFlot (r1 * r2))
  | _, _ => None
  end.

Definition soustrCible (v1 v2 : valCible) : option valCible :=
  match v1, v2 with
  | VCEnt n1, VCEnt n2 => Some (VCEnt (n1 - n2))
  | VCEnt n1, VCFlot r2 => Some (VCFlot (IZR n1 - r2))
  | VCFlot r1, VCEnt n2 => Some (VCFlot (r1 - IZR n2))
  | VCFlot r1, VCFlot r2 => Some (VCFlot (r1 - r2))
  | _, _ => None
  end.

Definition modCible (v1 v2 : valCible) : option valCible :=
  match v1, v2 with
  | VCEnt n1, VCEnt n2 =>
      if Z.eq_dec n2 0 then None else Some (VCEnt (Z.modulo n1 n2))
  | _, _ => None
  end.

Definition infEgCible (v1 v2 : valCible) : option valCible :=
  match v1, v2 with
  | VCEnt n1, VCEnt n2 => Some (VCBool (Z.leb n1 n2))
  | VCEnt n1, VCFlot r2 =>
      Some (VCBool (if Rle_dec (IZR n1) r2 then true else false))
  | VCFlot r1, VCEnt n2 =>
      Some (VCBool (if Rle_dec r1 (IZR n2) then true else false))
  | VCFlot r1, VCFlot r2 =>
      Some (VCBool (if Rle_dec r1 r2 then true else false))
  | _, _ => None
  end.

Definition egalCible (v1 v2 : valCible) : bool :=
  match v1, v2 with
  | VCEnt n1, VCEnt n2 => Z.eqb n1 n2
  | VCFlot r1, VCFlot r2 =>
      if Req_EM_T r1 r2 then true else false
  | VCBool b1, VCBool b2 => Bool.eqb b1 b2
  | _, _ => false
  end.

(** Calcule le nombre de groupes enfants. *)
Definition semNbGroupes (nbProc : Z) : Z :=
  if Z.gtb nbProc 1 then 2 else 1.

(** Calcule la taille maximale d'un groupe enfant. *)
Definition semTailleGroupe (nbProc nbGroupes : Z) : Z :=
  Z.div (nbProc + nbGroupes - 1) nbGroupes.

(** Calcule le groupe associé à un rang. *)
Definition semCouleur (rang tailleGroupe nbGroupes : Z) : Z :=
  Z.min (Z.div rang tailleGroupe) (nbGroupes - 1).

(** Calcule le rang local dans un groupe enfant. *)
Definition semRangEnfant (rang couleur tailleGroupe : Z) : Z :=
  rang - couleur * tailleGroupe.

(** Calcule la taille d'un groupe enfant. *)
Definition semTailleEnfant (nbProc couleur tailleGroupe : Z) : Z :=
  Z.min tailleGroupe (nbProc - couleur * tailleGroupe).


(** Éval une expression cible dans une mémoire. *)
Fixpoint evalCible (sigma : mem) (a : exprCible) : option valCible :=
  match a with
  | ACstEnt n => Some (VCEnt n)
  | ACstFlot r => Some (VCFlot r)
  | ABool b => Some (VCBool b)
  | AVar x => sigma x
  | APrimUn op a1 =>
      match evalCible sigma a1 with
      | Some cv =>
          match cibleVersVal cv with
          | Some v => Some (valVersCible (semUnCible op v))
          | None => None
          end
      | None => None
      end
  | APlus a1 a2 =>
      match evalCible sigma a1, evalCible sigma a2 with
      | Some v1, Some v2 => additionCible v1 v2
      | _, _ => None
      end
  | AMult a1 a2 =>
      match evalCible sigma a1, evalCible sigma a2 with
      | Some v1, Some v2 => multCible v1 v2
      | _, _ => None
      end
  | AMoins a1 a2 =>
      match evalCible sigma a1, evalCible sigma a2 with
      | Some v1, Some v2 => soustrCible v1 v2
      | _, _ => None
      end
  | AMod a1 a2 =>
      match evalCible sigma a1, evalCible sigma a2 with
      | Some v1, Some v2 => modCible v1 v2
      | _, _ => None
      end
  | APrimBin op a1 a2 =>
      match evalCible sigma a1, evalCible sigma a2 with
      | Some cv1, Some cv2 =>
          match cibleVersVal cv1, cibleVersVal cv2 with
          | Some v1, Some v2 =>
              Some (valVersCible (semBinCible op v1 v2))
          | _, _ => None
          end
      | _, _ => None
      end
  | AInfEg a1 a2 =>
      match evalCible sigma a1, evalCible sigma a2 with
      | Some v1, Some v2 => infEgCible v1 v2
      | _, _ => None
      end
  | AEg a1 a2 =>
      match evalCible sigma a1, evalCible sigma a2 with
      | Some v1, Some v2 => Some (VCBool (egalCible v1 v2))
      | _, _ => None
      end
  | ANon a1 =>
      match evalCible sigma a1 with
      | Some (VCBool b) => Some (VCBool (negb b))
      | _ => None
      end
  | AEt a1 a2 =>
      match evalCible sigma a1, evalCible sigma a2 with
      | Some (VCBool b1), Some (VCBool b2) =>
          Some (VCBool (andb b1 b2))
      | _, _ => None
      end
  | ANbGroupes nbProc =>
      match evalCible sigma nbProc with
      | Some (VCEnt p) => Some (VCEnt (semNbGroupes p))
      | _ => None
      end
  | ATailleGroupe nbProc nbGroupes =>
      match evalCible sigma nbProc, evalCible sigma nbGroupes with
      | Some (VCEnt p), Some (VCEnt g) =>
          Some (VCEnt (semTailleGroupe p g))
      | _, _ => None
      end
  | ACouleur rang tailleGroupe nbGroupes =>
      match evalCible sigma rang, evalCible sigma tailleGroupe,
            evalCible sigma nbGroupes with
      | Some (VCEnt r), Some (VCEnt t), Some (VCEnt g) =>
          Some (VCEnt (semCouleur r t g))
      | _, _, _ => None
      end
  | ARangEnfant rang couleur tailleGroupe =>
      match evalCible sigma rang, evalCible sigma couleur,
            evalCible sigma tailleGroupe with
      | Some (VCEnt r), Some (VCEnt c), Some (VCEnt t) =>
          Some (VCEnt (semRangEnfant r c t))
      | _, _, _ => None
      end
  | ATailleEnfant nbProc couleur tailleGroupe =>
      match evalCible sigma nbProc, evalCible sigma couleur,
            evalCible sigma tailleGroupe with
      | Some (VCEnt p), Some (VCEnt c), Some (VCEnt t) =>
          Some (VCEnt (semTailleEnfant p c t))
      | _, _, _ => None
      end
  end.

(** Relation de transition petit pas locale. *)
Inductive pasLoc : etatLoc -> etatLoc -> Prop :=
| PasAffect :
    forall sigma k x a v,
      evalCible sigma a = Some v ->
      pasLoc
        {| elMem := sigma; elCont := KCmd (CAffect x a) :: k |}
        {| elMem := majMem sigma x v;
           elCont := KCmd CRien :: k |}
| PasSeq :
    forall sigma k c1 c2,
      pasLoc
        {| elMem := sigma; elCont := KCmd (CSeq c1 c2) :: k |}
        {| elMem := sigma;
           elCont := KCmd c1 :: KCmd c2 :: k |}
| PasRien :
    forall sigma k,
      pasLoc
        {| elMem := sigma; elCont := KCmd CRien :: k |}
        {| elMem := sigma; elCont := k |}
| PasEff :
    forall sigma k xs,
      pasLoc
        {| elMem := sigma; elCont := KEff xs :: k |}
        {| elMem := effMem sigma xs; elCont := k |}
| PasSiVrai :
    forall sigma k test netVrai brancheVraie
      netFaux brancheFausse,
      evalCible sigma test = Some (VCBool true) ->
      pasLoc
        {| elMem := sigma;
           elCont :=
             KCmd
               (CSi test netVrai brancheVraie
                 netFaux brancheFausse) :: k |}
        {| elMem := sigma;
           elCont :=
             KCmd brancheVraie :: KEff netVrai :: k |}
| PasSiFaux :
    forall sigma k test netVrai brancheVraie
      netFaux brancheFausse,
      evalCible sigma test = Some (VCBool false) ->
      pasLoc
        {| elMem := sigma;
           elCont :=
             KCmd
               (CSi test netVrai brancheVraie
                 netFaux brancheFausse) :: k |}
        {| elMem := sigma;
           elCont :=
             KCmd brancheFausse :: KEff netFaux :: k |}
| PasPourInit :
    forall sigma k init test etape net corps,
      init <> CRien ->
      pasLoc
        {| elMem := sigma;
           elCont :=
             KCmd (CPour init test etape net corps) :: k |}
        {| elMem := sigma;
           elCont :=
             KCmd init ::
             KCmd (CPour CRien test etape net corps) :: k |}
| PasPourIter :
    forall sigma k test etape net corps,
      evalCible sigma test = Some (VCBool true) ->
      pasLoc
        {| elMem := sigma;
           elCont :=
             KCmd (CPour CRien test etape net corps) :: k |}
        {| elMem := sigma;
           elCont :=
             KCmd corps :: KEff net :: KCmd etape ::
             KCmd (CPour CRien test etape net corps) :: k |}
| PasPourFin :
    forall sigma k test etape net corps,
      evalCible sigma test = Some (VCBool false) ->
      pasLoc
        {| elMem := sigma;
           elCont :=
             KCmd (CPour CRien test etape net corps) :: k |}
        {| elMem := sigma; elCont := KCmd CRien :: k |}.

(** Clôture réflexive transitive des pas locaux. *)
Definition suiteLoc : etatLoc -> etatLoc -> Prop :=
  clos_refl_trans_1n etatLoc pasLoc.

(** Additionne une liste non vide de valeurs cibles. *)
Fixpoint somValsCible (vals : list valCible) : option valCible :=
  match vals with
  | [] => None
  | [v] => Some v
  | v :: suite =>
      match somValsCible suite with
      | Some reste => additionCible v reste
      | None => None
      end
  end.

(** Collecte les contributions d'un Allreduce prêt. *)
Fixpoint entreesRedTous
  (x y : var) (g : configGlob) : option (list valCible) :=
  match g with
  | [] => Some []
  | {| elMem := sigma;
       elCont := KCmd (CRedTous x' y') :: _ |} :: suite =>
      if andb (String.eqb x x') (String.eqb y y') then
        match sigma x, entreesRedTous x y suite with
        | Some v, Some vals => Some (v :: vals)
        | _, _ => None
        end
      else None
  | _ => None
  end.

(** Termine un Allreduce avec sa valeur totale. *)
Fixpoint finRedTous
  (y : var) (total : valCible) (g : configGlob) : configGlob :=
  match g with
  | [] => []
  | {| elMem := sigma;
       elCont := KCmd (CRedTous _ _) :: k |} :: suite =>
      {| elMem := majMem sigma y total;
         elCont := k |} ::
      finRedTous y total suite
  | etat :: suite => etat :: finRedTous y total suite
  end.

(** Relation de transition petit pas globale. *)
Inductive pasGlob : configGlob -> configGlob -> Prop :=
| PasGlobal :
    forall (q : configGlob) s s' suite,
      pasLoc s s' ->
      pasGlob (List.app q (s :: suite)) (List.app q (s' :: suite))
| PasRedTous :
    forall g x y vals total,
      entreesRedTous x y g = Some vals ->
      somValsCible vals = Some total ->
      pasGlob g (finRedTous y total g).

(** Clôture réflexive transitive des pas globaux. *)
Definition suiteGlob : configGlob -> configGlob -> Prop :=
  clos_refl_trans_1n configGlob pasGlob.

(** Exécution complète d'une commande locale. *)
Definition execLoc
  (sigma : mem) (c : cmd) (k : cont) (sigma' : mem) : Prop :=
  suiteLoc
    {| elMem := sigma; elCont := KCmd c :: k |}
    {| elMem := sigma'; elCont := k |}.

(** Compose deux suites de pas locaux. *)
Lemma transSuiteLoc :
  forall s1 s2 s3,
    suiteLoc s1 s2 ->
    suiteLoc s2 s3 ->
    suiteLoc s1 s3.
Proof.
  unfold suiteLoc. intros x y z Hxy. revert z.
  induction Hxy; intros; eauto using rt1n_trans.
Qed.

(** Compose deux suites de pas globaux. *)
Lemma transSuiteGlob :
  forall g1 g2 g3,
    suiteGlob g1 g2 ->
    suiteGlob g2 g3 ->
    suiteGlob g1 g3.
Proof.
  unfold suiteGlob. intros x y z Hxy. revert z.
  induction Hxy; intros; eauto using rt1n_trans.
Qed.

(** Exécute la commande vide. *)
Lemma execRien :
  forall sigma k, execLoc sigma CRien k sigma.
Proof.
  intros sigma k. unfold execLoc, suiteLoc.
  eapply rt1n_trans.
  - apply PasRien.
  - constructor.
Qed.

(** Exécute une affectation. *)
Lemma execAffect :
  forall sigma k x a v,
    evalCible sigma a = Some v ->
    execLoc sigma (CAffect x a) k (majMem sigma x v).
Proof.
  intros sigma k x a v Heval. unfold execLoc, suiteLoc.
  eapply rt1n_trans.
  - apply PasAffect. exact Heval.
  - eapply rt1n_trans.
    + apply PasRien.
    + constructor.
Qed.

(** Compose l'exécution de deux commandes séquentielles. *)
Lemma execSeq :
  forall sigma sigma1 sigma2 c1 c2 k,
    execLoc sigma c1 (KCmd c2 :: k) sigma1 ->
    execLoc sigma1 c2 k sigma2 ->
    execLoc sigma (CSeq c1 c2) k sigma2.
Proof.
  intros sigma sigma1 sigma2 c1 c2 k H1 H2.
  unfold execLoc in *. eapply transSuiteLoc.
  - unfold suiteLoc. eapply rt1n_trans.
    + apply PasSeq.
    + exact H1.
  - exact H2.
Qed.

(** Exécute le nettoyage d'une liste de variables. *)
Lemma execEff :
  forall sigma xs k,
    suiteLoc
      {| elMem := sigma; elCont := KEff xs :: k |}
      {| elMem := effMem sigma xs; elCont := k |}.
Proof.
  intros sigma xs k. unfold suiteLoc.
  eapply rt1n_trans.
  - apply PasEff.
  - constructor.
Qed.

(** Exécute la branche vraie d'une condition. *)
Lemma execSiVrai :
  forall sigma sigma' test netVrai brancheVraie
    netFaux brancheFausse k,
    evalCible sigma test = Some (VCBool true) ->
    execLoc sigma brancheVraie (KEff netVrai :: k) sigma' ->
    execLoc sigma
      (CSi test netVrai brancheVraie netFaux brancheFausse)
      k (effMem sigma' netVrai).
Proof.
  intros sigma sigma' test netVrai brancheVraie
    netFaux brancheFausse k Htest Hbranche.
  unfold execLoc in *. eapply transSuiteLoc.
  - unfold suiteLoc. eapply rt1n_trans.
    + apply PasSiVrai. exact Htest.
    + exact Hbranche.
  - apply execEff.
Qed.

(** Exécute la branche fausse d'une condition. *)
Lemma execSiFaux :
  forall sigma sigma' test netVrai brancheVraie
    netFaux brancheFausse k,
    evalCible sigma test = Some (VCBool false) ->
    execLoc sigma brancheFausse (KEff netFaux :: k) sigma' ->
    execLoc sigma
      (CSi test netVrai brancheVraie netFaux brancheFausse)
      k (effMem sigma' netFaux).
Proof.
  intros sigma sigma' test netVrai brancheVraie
    netFaux brancheFausse k Htest Hbranche.
  unfold execLoc in *. eapply transSuiteLoc.
  - unfold suiteLoc. eapply rt1n_trans.
    + apply PasSiFaux. exact Htest.
    + exact Hbranche.
  - apply execEff.
Qed.

(** Exécute l'initialisation d'une boucle. *)
Lemma execPourInit :
  forall sigma sigma' init test etape net corps k,
    init <> CRien ->
    execLoc sigma init
      (KCmd (CPour CRien test etape net corps) :: k) sigma' ->
    suiteLoc
      {| elMem := sigma;
         elCont := KCmd (CPour init test etape net corps) :: k |}
      {| elMem := sigma';
         elCont := KCmd (CPour CRien test etape net corps) :: k |}.
Proof.
  intros sigma sigma' init test etape net corps k Hinit Hexec.
  unfold execLoc in Hexec. unfold suiteLoc.
  eapply rt1n_trans.
  - apply PasPourInit. exact Hinit.
  - exact Hexec.
Qed.

(** Termine une boucle dont le test est faux. *)
Lemma execPourFin :
  forall sigma test etape net corps k,
    evalCible sigma test = Some (VCBool false) ->
    execLoc sigma (CPour CRien test etape net corps) k sigma.
Proof.
  intros sigma test etape net corps k Htest.
  unfold execLoc, suiteLoc.
  eapply rt1n_trans.
  - apply PasPourFin. exact Htest.
  - eapply rt1n_trans.
    + apply PasRien.
    + constructor.
Qed.

(** Compose une itération complète de boucle. *)
Lemma execPourIter :
  forall sigma sigma1 sigma2 sigma3 sigma4
    test etape net corps k,
    evalCible sigma test = Some (VCBool true) ->
    execLoc sigma corps
      (KEff net :: KCmd etape ::
       KCmd (CPour CRien test etape net corps) :: k) sigma1 ->
    suiteLoc
      {| elMem := sigma1;
         elCont :=
           KEff net :: KCmd etape ::
           KCmd (CPour CRien test etape net corps) :: k |}
      {| elMem := sigma2;
         elCont :=
           KCmd etape ::
           KCmd (CPour CRien test etape net corps) :: k |} ->
    execLoc sigma2 etape
      (KCmd (CPour CRien test etape net corps) :: k) sigma3 ->
    execLoc sigma3
      (CPour CRien test etape net corps) k sigma4 ->
    execLoc sigma
      (CPour CRien test etape net corps) k sigma4.
Proof.
  intros sigma sigma1 sigma2 sigma3 sigma4
    test etape net corps k Htest Hcorps Heff Hpas Hboucle.
  unfold execLoc in *. eapply transSuiteLoc.
  - unfold suiteLoc. eapply rt1n_trans.
    + apply PasPourIter. exact Htest.
    + exact Hcorps.
  - eapply transSuiteLoc; [exact Heff |].
    eapply transSuiteLoc; [exact Hpas | exact Hboucle].
Qed.

(** Exécute les trois premières commandes d'une séquence. *)
Lemma execPrefixeSeq3 :
  forall sigma sigma1 sigma2 sigma3 c1 c2 c3 c4 k,
    execLoc sigma c1
      (KCmd (CSeq c2 (CSeq c3 c4)) :: k) sigma1 ->
    execLoc sigma1 c2
      (KCmd (CSeq c3 c4) :: k) sigma2 ->
    execLoc sigma2 c3 (KCmd c4 :: k) sigma3 ->
    suiteLoc
      {| elMem := sigma;
         elCont := KCmd (CSeq c1 (CSeq c2 (CSeq c3 c4))) :: k |}
      {| elMem := sigma3; elCont := KCmd c4 :: k |}.
Proof.
  intros sigma sigma1 sigma2 sigma3 c1 c2 c3 c4 k
    Hpremier Hdeuxieme Htroisieme.
  unfold execLoc in *.
  eapply transSuiteLoc.
  - unfold suiteLoc. eapply rt1n_trans.
    + apply PasSeq.
    + exact Hpremier.
  - eapply transSuiteLoc.
    + unfold suiteLoc. eapply rt1n_trans.
      * apply PasSeq.
      * exact Hdeuxieme.
    + unfold suiteLoc. eapply rt1n_trans.
      * apply PasSeq.
      * exact Htroisieme.
Qed.
