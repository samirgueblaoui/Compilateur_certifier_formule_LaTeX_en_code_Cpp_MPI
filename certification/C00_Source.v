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
Inductive ty : Type :=
| TInt
| TFloat.

(** Valeurs produites par la sémantique source. *)
Inductive value : Type :=
| VInt : Z -> value
| VFloat : R -> value.

(** Relation entre une valeur source et son type. *)
Definition value_has_type (v : value) (t : ty) : Prop :=
  match v, t with
  | VInt _, TInt | VFloat _, TFloat => True
  | _, _ => False
  end.

(** Valeurs manipulées par la machine cible. *)
Inductive cvalue : Type :=
| CVInt : Z -> cvalue
| CVFloat : R -> cvalue
| CVBool : bool -> cvalue.

(** Type abstrait des opérateurs unaires. *)
Parameter unary_op : Type.
(** Type abstrait des opérateurs binaires primitifs. *)
Parameter primitive_binary_op : Type.

(** Sémantique source des opérateurs unaires. *)
Parameter unary_source_sem : unary_op -> value -> value.
(** Sémantique cible des opérateurs unaires. *)
Parameter unary_target_sem : unary_op -> value -> value.
(** Sémantique source des opérateurs binaires primitifs. *)
Parameter binary_source_sem :
  primitive_binary_op -> value -> value -> value.
(** Sémantique cible des opérateurs binaires primitifs. *)
Parameter binary_target_sem :
  primitive_binary_op -> value -> value -> value.

(** Environnement de typage des variables. *)
Definition tyenv := var -> option ty.
(** Environnement d'exécution du langage source. *)
Definition env := var -> option value.
(** Mémoire locale de la machine cible. *)
Definition store := var -> option cvalue.

(** Signatures de type des opérateurs unaires. *)
Definition unary_sig_env := unary_op -> ty -> option ty.
(** Signatures de type des opérateurs binaires. *)
Definition binary_sig_env :=
  primitive_binary_op -> ty -> ty -> option ty.

(** Formes possibles d'une opération binaire source. *)
Inductive binary_form : Type :=
| BAdd
| BMul
| BPrimitive : primitive_binary_op -> binary_form.

(** Syntaxe des expressions du langage source. *)
Inductive expr : Type :=
| EConstInt : Z -> expr
| EConstFloat : R -> expr
| EVar : var -> expr
| EUnary : unary_op -> expr -> expr
| EBinaryForm : binary_form -> expr -> expr -> expr
| ESumSeq : var -> expr -> expr -> expr -> expr
| ESumPar : var -> expr -> expr -> expr -> expr.

(** Constructeur dérivé de l'addition source. *)
Definition EAdd (e1 e2 : expr) : expr :=
  EBinaryForm BAdd e1 e2.

(** Constructeur dérivé de la multiplication source. *)
Definition EMul (e1 e2 : expr) : expr :=
  EBinaryForm BMul e1 e2.

(** Constructeur dérivé d'une primitive binaire. *)
Definition EBinary (op : primitive_binary_op) (e1 e2 : expr) : expr :=
  EBinaryForm (BPrimitive op) e1 e2.

(** Type obtenu par promotion de deux types numériques. *)
Definition promote_ty (t1 t2 : ty) : ty :=
  match t1, t2 with
  | TInt, TInt => TInt
  | _, _ => TFloat
  end.

(** Calcule le type résultat d'une opération binaire. *)
Definition binary_result_type
  (B : binary_sig_env) (op : binary_form) (t1 t2 : ty) : ty :=
  match op with
  | BAdd | BMul => promote_ty t1 t2
  | BPrimitive f =>
      match B f t1 t2 with
      | Some t => t
      | None => promote_ty t1 t2
      end
  end.

(** Vérifie la cohérence d'une signature binaire. *)
Definition binary_signature_valid
  (B : binary_sig_env) (op : binary_form) (t1 t2 : ty) : Prop :=
  match op with
  | BPrimitive f => exists tout, B f t1 t2 = Some tout
  | BAdd | BMul => True
  end.

(** Calcule le type résultat d'une opération unaire. *)
Definition unary_result_type
  (U : unary_sig_env) (op : unary_op) (t : ty) : ty :=
  match U op t with
  | Some tout => tout
  | None => t
  end.

(** Valeur nulle associée à un type numérique. *)
Definition zero_value (t : ty) : value :=
  match t with
  | TInt => VInt 0
  | TFloat => VFloat 0
  end.

(** Addition de deux valeurs source. *)
Definition add_values (v1 v2 : value) : value :=
  match v1, v2 with
  | VInt n1, VInt n2 => VInt (n1 + n2)
  | VInt n1, VFloat r2 => VFloat (IZR n1 + r2)
  | VFloat r1, VInt n2 => VFloat (r1 + IZR n2)
  | VFloat r1, VFloat r2 => VFloat (r1 + r2)
  end.

(** Multiplication de deux valeurs source. *)
Definition mul_values (v1 v2 : value) : value :=
  match v1, v2 with
  | VInt n1, VInt n2 => VInt (n1 * n2)
  | VInt n1, VFloat r2 => VFloat (IZR n1 * r2)
  | VFloat r1, VInt n2 => VFloat (r1 * IZR n2)
  | VFloat r1, VFloat r2 => VFloat (r1 * r2)
  end.

(** Interprétation source d'une forme binaire. *)
Definition binary_source_value
  (op : binary_form) (v1 v2 : value) : value :=
  match op with
  | BAdd => add_values v1 v2
  | BMul => mul_values v1 v2
  | BPrimitive f => binary_source_sem f v1 v2
  end.

(** Interprétation cible d'une forme binaire. *)
Definition binary_target_value
  (op : binary_form) (v1 v2 : value) : value :=
  match op with
  | BAdd => add_values v1 v2
  | BMul => mul_values v1 v2
  | BPrimitive f => binary_target_sem f v1 v2
  end.

(** Étend un contexte de typage par un entier. *)
Definition gamma_bind_int (Gamma : tyenv) (x : var) : tyenv :=
  fun y => if String.eqb y x then Some TInt else Gamma y.

(** Met à jour une variable de l'environnement source. *)
Definition env_update (rho : env) (x : var) (v : value) : env :=
  fun y => if String.eqb y x then Some v else rho y.

(** Jugement de typage des expressions source. *)
Inductive has_type
  (Gamma : tyenv) (U : unary_sig_env) (B : binary_sig_env)
  : expr -> ty -> Prop :=
| TyConstInt :
    forall n, has_type Gamma U B (EConstInt n) TInt
| TyConstFloat :
    forall r, has_type Gamma U B (EConstFloat r) TFloat
| TyVar :
    forall x t,
      Gamma x = Some t ->
      has_type Gamma U B (EVar x) t
| TyUnary :
    forall op e tin tout,
      has_type Gamma U B e tin ->
      U op tin = Some tout ->
      has_type Gamma U B (EUnary op e) tout
| TyBinary :
    forall op e1 e2 t1 t2,
      has_type Gamma U B e1 t1 ->
      has_type Gamma U B e2 t2 ->
      binary_signature_valid B op t1 t2 ->
      has_type Gamma U B
        (EBinaryForm op e1 e2)
        (binary_result_type B op t1 t2)
| TySumSeq :
    forall i a b body tbody,
      has_type Gamma U B a TInt ->
      has_type Gamma U B b TInt ->
      has_type (gamma_bind_int Gamma i) U B body tbody ->
      has_type Gamma U B (ESumSeq i a b body) tbody
| TySumPar :
    forall i a b body tbody,
      has_type Gamma U B a TInt ->
      has_type Gamma U B b TInt ->
      has_type (gamma_bind_int Gamma i) U B body tbody ->
      has_type Gamma U B (ESumPar i a b body) tbody.

(** Sémantique grand pas mutuelle des expressions et des sommes. *)
Inductive eval_expr
  (Gamma : tyenv) (U : unary_sig_env) (B : binary_sig_env)
  : env -> expr -> ty -> value -> Prop :=
| EvalConstInt :
    forall rho n,
      eval_expr Gamma U B rho (EConstInt n) TInt (VInt n)
| EvalConstFloat :
    forall rho r,
      eval_expr Gamma U B rho (EConstFloat r) TFloat (VFloat r)
| EvalVar :
    forall rho x t v,
      Gamma x = Some t ->
      rho x = Some v ->
      value_has_type v t ->
      eval_expr Gamma U B rho (EVar x) t v
| EvalUnary :
    forall rho op e tin tout v,
      eval_expr Gamma U B rho e tin v ->
      U op tin = Some tout ->
      value_has_type (unary_source_sem op v) tout ->
      eval_expr Gamma U B rho (EUnary op e) tout
        (unary_source_sem op v)
| EvalBinary :
    forall rho op e1 e2 t1 t2 v1 v2,
      eval_expr Gamma U B rho e1 t1 v1 ->
      eval_expr Gamma U B rho e2 t2 v2 ->
      binary_signature_valid B op t1 t2 ->
      value_has_type
        (binary_source_value op v1 v2)
        (binary_result_type B op t1 t2) ->
      eval_expr Gamma U B rho
        (EBinaryForm op e1 e2)
        (binary_result_type B op t1 t2)
        (binary_source_value op v1 v2)
| EvalSumSeq :
    forall rho i a b body m n tbody v,
      eval_expr Gamma U B rho a TInt (VInt m) ->
      eval_expr Gamma U B rho b TInt (VInt n) ->
      has_type (gamma_bind_int Gamma i) U B body tbody ->
      eval_sum Gamma U B rho i m n body tbody v ->
      eval_expr Gamma U B rho (ESumSeq i a b body) tbody v
| EvalSumPar :
    forall rho i a b body m n tbody v,
      eval_expr Gamma U B rho a TInt (VInt m) ->
      eval_expr Gamma U B rho b TInt (VInt n) ->
      has_type (gamma_bind_int Gamma i) U B body tbody ->
      eval_sum Gamma U B rho i m n body tbody v ->
      eval_expr Gamma U B rho (ESumPar i a b body) tbody v

with eval_sum
  (Gamma : tyenv) (U : unary_sig_env) (B : binary_sig_env)
  : env -> var -> Z -> Z -> expr -> ty -> value -> Prop :=
| EvalSumEmpty :
    forall rho i m n body tbody,
      (n < m)%Z ->
      eval_sum Gamma U B rho i m n body tbody (zero_value tbody)
| EvalSumStep :
    forall rho i m n body tbody v1 vrest,
      (m <= n)%Z ->
      eval_expr (gamma_bind_int Gamma i) U B
        (env_update rho i (VInt m)) body tbody v1 ->
      eval_sum Gamma U B rho i (m + 1) n body tbody vrest ->
      eval_sum Gamma U B rho i m n body tbody
        (add_values v1 vrest).

(** Évaluation d'une tranche arithmétique de somme. *)
Inductive eval_stride_sum
  (Gamma : tyenv) (U : unary_sig_env) (B : binary_sig_env)
  (rho : env) (i : var) (body : expr) (tbody : ty)
  (stride : Z) : Z -> Z -> value -> Prop :=
| EvalStrideEmpty :
    forall current upper,
      (upper < current)%Z ->
      eval_stride_sum Gamma U B rho i body tbody stride
        current upper (zero_value tbody)
| EvalStrideStep :
    forall current upper vcurrent vrest,
      (current <= upper)%Z ->
      eval_expr (gamma_bind_int Gamma i) U B
        (env_update rho i (VInt current)) body tbody vcurrent ->
      eval_stride_sum Gamma U B rho i body tbody stride
        (current + stride) upper vrest ->
      eval_stride_sum Gamma U B rho i body tbody stride
        current upper (add_values vcurrent vrest).

(** Compatibilité entre les primitives source et cible. *)
Definition primitive_semantics_compatible
  (_ : unary_sig_env) (_ : binary_sig_env) : Prop :=
  (forall op v,
      unary_target_sem op v = unary_source_sem op v) /\
  (forall op v1 v2,
      binary_target_sem op v1 v2 = binary_source_sem op v1 v2).

(** Détecte la présence d'une somme parallèle. *)
Fixpoint has_parallel_sum (e : expr) : bool :=
  match e with
  | EConstInt _ | EConstFloat _ | EVar _ => false
  | EUnary _ e1 => has_parallel_sum e1
  | EBinaryForm _ e1 e2 =>
      orb (has_parallel_sum e1) (has_parallel_sum e2)
  | ESumSeq _ a b body =>
      orb (has_parallel_sum a)
        (orb (has_parallel_sum b) (has_parallel_sum body))
  | ESumPar _ _ _ _ => true
  end.
