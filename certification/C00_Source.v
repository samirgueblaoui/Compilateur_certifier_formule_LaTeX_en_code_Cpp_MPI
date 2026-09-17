From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Reals.Reals.
From Stdlib Require Import Relations.Relation_Operators.
From Stdlib Require Import Lia.

Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope R_scope.


(** Nom des variables source et cible. *)
Definition var := string.

(** Types numériques du langage source. *)
Inductive typeNum : Type :=
| TEnt
| TFlot.

(** Valeurs produites par la sémantique source. *)
Inductive val : Type :=
| VEnt : Z -> val
| VFlot : R -> val.

(** Relation entre une valeur source et son type. *)
Definition valTypee (v : val) (t : typeNum) : Prop :=
  match v, t with
  | VEnt _, TEnt | VFlot _, TFlot => True
  | _, _ => False
  end.

(** Valeurs manipulées par la machine cible. *)
Inductive valCible : Type :=
| VCEnt : Z -> valCible
| VCFlot : R -> valCible
| VCBool : bool -> valCible.

Parameter opUn : Type.
Parameter opBinPrim : Type.

Parameter semUnSrc : opUn -> val -> val.
Parameter semUnCible : opUn -> val -> val.
Parameter semBinSrc :
  opBinPrim -> val -> val -> val.
Parameter semBinCible :
  opBinPrim -> val -> val -> val.

(** Environnement de typage des variables. *)
Definition envTypes := var -> option typeNum.
(** Environnement d'exécution du langage source. *)
Definition env := var -> option val.
(** Mémoire locale de la machine cible. *)
Definition mem := var -> option valCible.

Definition envSigsUn := opUn -> typeNum -> option typeNum.
Definition envSigsBin :=
  opBinPrim -> typeNum -> typeNum -> option typeNum.

(** Formes possibles d'une opération binaire. *)
Inductive formeBin : Type :=
| BPlus
| BMult
| BPrim : opBinPrim -> formeBin.

(** Syntaxe des expressions du langage source. *)
Inductive expr : Type :=
| ECstEnt : Z -> expr
| ECstFlot : R -> expr
| EVar : var -> expr
| EUn : opUn -> expr -> expr
| EBin : formeBin -> expr -> expr -> expr
| ESomSeq : var -> expr -> expr -> expr -> expr
| ESomPar : var -> expr -> expr -> expr -> expr.

Definition EPlus (e1 e2 : expr) : expr :=
  EBin BPlus e1 e2.

Definition EMult (e1 e2 : expr) : expr :=
  EBin BMult e1 e2.

Definition EPrimBin (op : opBinPrim) (e1 e2 : expr) : expr :=
  EBin (BPrim op) e1 e2.

(** Type obtenu par promotion de deux types numériques. *)
Definition promouvoir (t1 t2 : typeNum) : typeNum :=
  match t1, t2 with
  | TEnt, TEnt => TEnt
  | _, _ => TFlot
  end.

(** Calcule le type résultat d'une opération binaire. *)
Definition typeResBin
  (B : envSigsBin) (op : formeBin) (t1 t2 : typeNum) : typeNum :=
  match op with
  | BPlus | BMult => promouvoir t1 t2
  | BPrim f =>
      match B f t1 t2 with
      | Some t => t
      | None => promouvoir t1 t2
      end
  end.

(** Vérifie la cohérence d'une signature binaire. *)
Definition sigBinValide
  (B : envSigsBin) (op : formeBin) (t1 t2 : typeNum) : Prop :=
  match op with
  | BPrim f => exists tSortie, B f t1 t2 = Some tSortie
  | BPlus | BMult => True
  end.

(** Calcule le type résultat d'une opération unaire. *)
Definition typeResUn
  (U : envSigsUn) (op : opUn) (t : typeNum) : typeNum :=
  match U op t with
  | Some tSortie => tSortie
  | None => t
  end.

(** Valeur nulle associée à un type numérique. *)
Definition valNulle (t : typeNum) : val :=
  match t with
  | TEnt => VEnt 0
  | TFlot => VFlot 0
  end.

(** Addition de deux valeurs source. *)
Definition additionVals (v1 v2 : val) : val :=
  match v1, v2 with
  | VEnt n1, VEnt n2 => VEnt (n1 + n2)
  | VEnt n1, VFlot r2 => VFlot (IZR n1 + r2)
  | VFlot r1, VEnt n2 => VFlot (r1 + IZR n2)
  | VFlot r1, VFlot r2 => VFlot (r1 + r2)
  end.

(** Multiplication de deux valeurs source. *)
Definition multVals (v1 v2 : val) : val :=
  match v1, v2 with
  | VEnt n1, VEnt n2 => VEnt (n1 * n2)
  | VEnt n1, VFlot r2 => VFlot (IZR n1 * r2)
  | VFlot r1, VEnt n2 => VFlot (r1 * IZR n2)
  | VFlot r1, VFlot r2 => VFlot (r1 * r2)
  end.

(** Interprétation source d'une forme binaire. *)
Definition valBinSrc
  (op : formeBin) (v1 v2 : val) : val :=
  match op with
  | BPlus => additionVals v1 v2
  | BMult => multVals v1 v2
  | BPrim f => semBinSrc f v1 v2
  end.

(** Interprétation cible d'une forme binaire. *)
Definition valBinCible
  (op : formeBin) (v1 v2 : val) : val :=
  match op with
  | BPlus => additionVals v1 v2
  | BMult => multVals v1 v2
  | BPrim f => semBinCible f v1 v2
  end.

(** Étend un contexte de typage par un entier. *)
Definition lierTypeEnt (Gamma : envTypes) (x : var) : envTypes :=
  fun y => if String.eqb y x then Some TEnt else Gamma y.

(** Met à jour une variable de l'environnement source. *)
Definition majEnv (rho : env) (x : var) (v : val) : env :=
  fun y => if String.eqb y x then Some v else rho y.

(** Jugement de typage des expressions source. *)
Inductive bienType
  (Gamma : envTypes) (U : envSigsUn) (B : envSigsBin)
  : expr -> typeNum -> Prop :=
| TyCstEnt :
    forall n, bienType Gamma U B (ECstEnt n) TEnt
| TyCstFlot :
    forall r, bienType Gamma U B (ECstFlot r) TFlot
| TyVar :
    forall x t,
      Gamma x = Some t ->
      bienType Gamma U B (EVar x) t
| TyUn :
    forall op e tEntree tSortie,
      bienType Gamma U B e tEntree ->
      U op tEntree = Some tSortie ->
      bienType Gamma U B (EUn op e) tSortie
| TyBin :
    forall op e1 e2 t1 t2,
      bienType Gamma U B e1 t1 ->
      bienType Gamma U B e2 t2 ->
      sigBinValide B op t1 t2 ->
      bienType Gamma U B
        (EBin op e1 e2)
        (typeResBin B op t1 t2)
| TySomSeq :
    forall i a b corps tCorps,
      bienType Gamma U B a TEnt ->
      bienType Gamma U B b TEnt ->
      bienType (lierTypeEnt Gamma i) U B corps tCorps ->
      bienType Gamma U B (ESomSeq i a b corps) tCorps
| TySomPar :
    forall i a b corps tCorps,
      bienType Gamma U B a TEnt ->
      bienType Gamma U B b TEnt ->
      bienType (lierTypeEnt Gamma i) U B corps tCorps ->
      bienType Gamma U B (ESomPar i a b corps) tCorps.

(** Sémantique grand pas mutuelle des expressions et des sommes. *)
Inductive evalExpr
  (Gamma : envTypes) (U : envSigsUn) (B : envSigsBin)
  : env -> expr -> typeNum -> val -> Prop :=
| EvalCstEnt :
    forall rho n,
      evalExpr Gamma U B rho (ECstEnt n) TEnt (VEnt n)
| EvalCstFlot :
    forall rho r,
      evalExpr Gamma U B rho (ECstFlot r) TFlot (VFlot r)
| EvalVar :
    forall rho x t v,
      Gamma x = Some t ->
      rho x = Some v ->
      valTypee v t ->
      evalExpr Gamma U B rho (EVar x) t v
| EvalUn :
    forall rho op e tEntree tSortie v,
      evalExpr Gamma U B rho e tEntree v ->
      U op tEntree = Some tSortie ->
      valTypee (semUnSrc op v) tSortie ->
      evalExpr Gamma U B rho (EUn op e) tSortie
        (semUnSrc op v)
| EvalBin :
    forall rho op e1 e2 t1 t2 v1 v2,
      evalExpr Gamma U B rho e1 t1 v1 ->
      evalExpr Gamma U B rho e2 t2 v2 ->
      sigBinValide B op t1 t2 ->
      valTypee
        (valBinSrc op v1 v2)
        (typeResBin B op t1 t2) ->
      evalExpr Gamma U B rho
        (EBin op e1 e2)
        (typeResBin B op t1 t2)
        (valBinSrc op v1 v2)
| EvalSomSeq :
    forall rho i a b corps m n tCorps v,
      evalExpr Gamma U B rho a TEnt (VEnt m) ->
      evalExpr Gamma U B rho b TEnt (VEnt n) ->
      bienType (lierTypeEnt Gamma i) U B corps tCorps ->
      evalSom Gamma U B rho i m n corps tCorps v ->
      evalExpr Gamma U B rho (ESomSeq i a b corps) tCorps v
| EvalSomPar :
    forall rho i a b corps m n tCorps v,
      evalExpr Gamma U B rho a TEnt (VEnt m) ->
      evalExpr Gamma U B rho b TEnt (VEnt n) ->
      bienType (lierTypeEnt Gamma i) U B corps tCorps ->
      evalSom Gamma U B rho i m n corps tCorps v ->
      evalExpr Gamma U B rho (ESomPar i a b corps) tCorps v

with evalSom
  (Gamma : envTypes) (U : envSigsUn) (B : envSigsBin)
  : env -> var -> Z -> Z -> expr -> typeNum -> val -> Prop :=
| EvalSomVide :
    forall rho i m n corps tCorps,
      (n < m)%Z ->
      evalSom Gamma U B rho i m n corps tCorps (valNulle tCorps)
| EvalSomEtape :
    forall rho i m n corps tCorps v1 vReste,
      (m <= n)%Z ->
      evalExpr (lierTypeEnt Gamma i) U B
        (majEnv rho i (VEnt m)) corps tCorps v1 ->
      evalSom Gamma U B rho i (m + 1) n corps tCorps vReste ->
      evalSom Gamma U B rho i m n corps tCorps
        (additionVals v1 vReste).

Inductive evalSomPas
  (Gamma : envTypes) (U : envSigsUn) (B : envSigsBin)
  (rho : env) (i : var) (corps : expr) (tCorps : typeNum)
  (pas : Z) : Z -> Z -> val -> Prop :=
| EvalPasVide :
    forall courant bSup,
      (bSup < courant)%Z ->
      evalSomPas Gamma U B rho i corps tCorps pas
        courant bSup (valNulle tCorps)
| EvalPasEtape :
    forall courant bSup vCourant vReste,
      (courant <= bSup)%Z ->
      evalExpr (lierTypeEnt Gamma i) U B
        (majEnv rho i (VEnt courant)) corps tCorps vCourant ->
      evalSomPas Gamma U B rho i corps tCorps pas
        (courant + pas) bSup vReste ->
      evalSomPas Gamma U B rho i corps tCorps pas
        courant bSup (additionVals vCourant vReste).

(** Compatibilité entre source et cible. *)
Definition primCompat
  (_ : envSigsUn) (_ : envSigsBin) : Prop :=
  (forall op v,
      semUnCible op v = semUnSrc op v) /\
  (forall op v1 v2,
      semBinCible op v1 v2 = semBinSrc op v1 v2).

(** Détecte la présence d'une somme parallèle. *)
Fixpoint contientSomPar (e : expr) : bool :=
  match e with
  | ECstEnt _ | ECstFlot _ | EVar _ => false
  | EUn _ e1 => contientSomPar e1
  | EBin _ e1 e2 =>
      orb (contientSomPar e1) (contientSomPar e2)
  | ESomSeq _ a b corps =>
      orb (contientSomPar a)
        (orb (contientSomPar b) (contientSomPar corps))
  | ESomPar _ _ _ _ => true
  end.
