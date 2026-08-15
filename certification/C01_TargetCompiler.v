From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Reals.Reals.
From Stdlib Require Import Relations.Relation_Operators.
From Stdlib Require Import Lia.
From Certification2 Require Export C00_Source.

Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope R_scope.

(** Syntaxe des expressions de la machine cible. *)
Inductive aexpr : Type :=
| ANumInt : Z -> aexpr
| ANumFloat : R -> aexpr
| ABool : bool -> aexpr
| AVar : var -> aexpr
| AUnaryPrim : unary_op -> aexpr -> aexpr
| AAdd : aexpr -> aexpr -> aexpr
| AMul : aexpr -> aexpr -> aexpr
| ASub : aexpr -> aexpr -> aexpr
| AMod : aexpr -> aexpr -> aexpr
| ABinaryPrim : primitive_binary_op -> aexpr -> aexpr -> aexpr
| ALe : aexpr -> aexpr -> aexpr
| AEq : aexpr -> aexpr -> aexpr
| ANot : aexpr -> aexpr
| AAnd : aexpr -> aexpr -> aexpr
| ANbGroups : aexpr -> aexpr
| AGroupSize : aexpr -> aexpr -> aexpr
| AColor : aexpr -> aexpr -> aexpr -> aexpr
| AChildRank : aexpr -> aexpr -> aexpr -> aexpr
| AChildSize : aexpr -> aexpr -> aexpr -> aexpr.

(** Contexte utilisé pendant la compilation. *)
Record ctx : Type := {
  ctx_rank : var;
  ctx_size : var;
  ctx_active : aexpr;
  ctx_level : nat;
  ctx_repr : var -> var
}.

(** Contexte initial de compilation. *)
Definition ctx0 : ctx :=
  {| ctx_rank := "rank";
     ctx_size := "size";
     ctx_active := ABool true;
     ctx_level := 0%nat;
     ctx_repr := fun x => x |}.

(** Associe une variable source à une variable cible. *)
Definition ctx_bind_var (c : ctx) (x z : var) : ctx :=
  {| ctx_rank := ctx_rank c;
     ctx_size := ctx_size c;
     ctx_active := ctx_active c;
     ctx_level := ctx_level c;
     ctx_repr := fun y =>
       if String.eqb y x then z else ctx_repr c y |}.

(** Construit le contexte d'un groupe enfant. *)
Definition ctx_child
  (c : ctx) (child_rank child_size color owner : var) : ctx :=
  {| ctx_rank := child_rank;
     ctx_size := child_size;
     ctx_active :=
       AAnd (ctx_active c) (AEq (AVar color) (AVar owner));
     ctx_level := S (ctx_level c);
     ctx_repr := ctx_repr c |}.

(** Syntaxe des commandes de la machine cible. *)
Inductive cmd : Type :=
| CSkip
| CAssign : var -> aexpr -> cmd
| CSeq : cmd -> cmd -> cmd
| CIf : aexpr -> list var -> cmd -> list var -> cmd -> cmd
| CFor : cmd -> aexpr -> cmd -> list var -> cmd -> cmd
| CAllreduce : var -> var -> cmd.

(** Cadres stockés dans une continuation. *)
Inductive frame : Type :=
| KCmd : cmd -> frame
| KDel : list var -> frame.

(** Pile de continuation d'un processus. *)
Definition kont := list frame.

(** État local d'un processus cible. *)
Record local_state : Type := {
  ls_store : store;
  ls_kont : kont
}.

(** Configuration globale de tous les processus. *)
Definition global_config := list local_state.

(** Code, résultat, type et fraîcheur produits par la compilation. *)
Record compile_result : Type := {
  cr_code : cmd;
  cr_result : var;
  cr_type : ty;
  cr_next_fresh : nat
}.

(** Encode un entier naturel dans un nom. *)
Fixpoint nat_tag (n : nat) : string :=
  match n with
  | O => "0"
  | S n' => "S" ++ nat_tag n'
  end.

(** Construit le nom d'une variable temporaire. *)
Definition temp_name (n : nat) : var :=
  "tmp" ++ nat_tag n.

(** Expression cible représentant le zéro d'un type. *)
Definition zero_aexpr (t : ty) : aexpr :=
  match t with
  | TInt => ANumInt 0
  | TFloat => ANumFloat 0
  end.

(** Met une liste de commandes en séquence. *)
Fixpoint seq_list (cs : list cmd) : cmd :=
  match cs with
  | [] => CSkip
  | [c] => c
  | c :: tl => CSeq c (seq_list tl)
  end.

(** Énumère une tranche de variables temporaires. *)
Fixpoint temp_names_from (start len : nat) : list var :=
  match len with
  | O => []
  | S len' => temp_name start :: temp_names_from (S start) len'
  end.

(** Énumère les temporaires entre deux indices. *)
Definition temp_names_between (start stop : nat) : list var :=
  temp_names_from start (stop - start).

(** Traduit une opération binaire en expression cible. *)
Definition binary_aexpr
  (op : binary_form) (x y : var) : aexpr :=
  match op with
  | BAdd => AAdd (AVar x) (AVar y)
  | BMul => AMul (AVar x) (AVar y)
  | BPrimitive f => ABinaryPrim f (AVar x) (AVar y)
  end.

(** Compile récursivement une expression source. *)
Fixpoint compile
  (e : expr) (Gamma : tyenv)
  (U : unary_sig_env) (B : binary_sig_env)
  (cctx : ctx) (fresh : nat) : compile_result :=
  match e with
  | EConstInt n =>
      {| cr_code := CAssign (temp_name fresh) (ANumInt n);
         cr_result := temp_name fresh;
         cr_type := TInt;
         cr_next_fresh := S fresh |}
  | EConstFloat r =>
      {| cr_code := CAssign (temp_name fresh) (ANumFloat r);
         cr_result := temp_name fresh;
         cr_type := TFloat;
         cr_next_fresh := S fresh |}
  | EVar x =>
      {| cr_code := CSkip;
         cr_result := ctx_repr cctx x;
         cr_type :=
           match Gamma x with
           | Some t => t
           | None => TInt
           end;
         cr_next_fresh := fresh |}
  | EUnary op e1 =>
      let r1 := compile e1 Gamma U B cctx fresh in
      let dst := temp_name (cr_next_fresh r1) in
      {| cr_code :=
           seq_list
             [cr_code r1;
              CAssign dst (AUnaryPrim op (AVar (cr_result r1)))];
         cr_result := dst;
         cr_type := unary_result_type U op (cr_type r1);
         cr_next_fresh := S (cr_next_fresh r1) |}
  | EBinaryForm op e1 e2 =>
      let r1 := compile e1 Gamma U B cctx fresh in
      let r2 :=
        compile e2 Gamma U B cctx (cr_next_fresh r1) in
      let dst := temp_name (cr_next_fresh r2) in
      {| cr_code :=
           seq_list
             [cr_code r1;
              cr_code r2;
              CAssign dst
                (binary_aexpr op (cr_result r1) (cr_result r2))];
         cr_result := dst;
         cr_type :=
           binary_result_type B op (cr_type r1) (cr_type r2);
         cr_next_fresh := S (cr_next_fresh r2) |}
  | ESumSeq i a b body =>
      let ra := compile a Gamma U B cctx fresh in
      let rb :=
        compile b Gamma U B cctx (cr_next_fresh ra) in
      let acc := temp_name (cr_next_fresh rb) in
      let idx := temp_name (S (cr_next_fresh rb)) in
      let body_start := S (S (cr_next_fresh rb)) in
      let body_ctx := ctx_bind_var cctx i idx in
      let ru :=
        compile body (gamma_bind_int Gamma i) U B
          body_ctx body_start in
      {| cr_code :=
           seq_list
             [cr_code ra;
              cr_code rb;
              CAssign acc (zero_aexpr (cr_type ru));
              CFor
                (CAssign idx (AVar (cr_result ra)))
                (ALe (AVar idx) (AVar (cr_result rb)))
                (CAssign idx (AAdd (AVar idx) (ANumInt 1)))
                (temp_names_between body_start (cr_next_fresh ru))
                (seq_list
                   [cr_code ru;
                    CAssign acc
                      (AAdd (AVar acc) (AVar (cr_result ru)))])];
         cr_result := acc;
         cr_type := cr_type ru;
         cr_next_fresh := cr_next_fresh ru |}
  | ESumPar i a b body =>
      let ra := compile a Gamma U B cctx fresh in
      let rb :=
        compile b Gamma U B cctx (cr_next_fresh ra) in
      let nf := cr_next_fresh rb in
      if has_parallel_sum body then
        let groups := temp_name nf in
        let group_size := temp_name (S nf) in
        let color := temp_name (S (S nf)) in
        let child_rank := temp_name (S (S (S nf))) in
        let child_size := temp_name (S (S (S (S nf)))) in
        let owner := temp_name (S (S (S (S (S nf))))) in
        let acc := temp_name (S (S (S (S (S (S nf)))))) in
        let idx := temp_name (S (S (S (S (S (S (S nf))))))) in
        let body_start := S (S (S (S (S (S (S (S nf))))))) in
        let child :=
          ctx_child cctx child_rank child_size color owner in
        let body_ctx := ctx_bind_var child i idx in
        let ru :=
          compile body (gamma_bind_int Gamma i) U B
            body_ctx body_start in
        let result := temp_name (cr_next_fresh ru) in
        {| cr_code :=
             seq_list
               [cr_code ra;
                cr_code rb;
                CAssign groups (ANbGroups (AVar (ctx_size cctx)));
                CAssign group_size
                  (AGroupSize (AVar (ctx_size cctx)) (AVar groups));
                CAssign color
                  (AColor (AVar (ctx_rank cctx))
                    (AVar group_size) (AVar groups));
                CAssign child_rank
                  (AChildRank (AVar (ctx_rank cctx))
                    (AVar color) (AVar group_size));
                CAssign child_size
                  (AChildSize (AVar (ctx_size cctx))
                    (AVar color) (AVar group_size));
                CAssign acc (zero_aexpr (cr_type ru));
                CFor
                  (CAssign idx (AVar (cr_result ra)))
                  (ALe (AVar idx) (AVar (cr_result rb)))
                  (CAssign idx (AAdd (AVar idx) (ANumInt 1)))
                  (temp_names_between body_start (cr_next_fresh ru))
                  (seq_list
                    [CAssign owner
                       (AMod
                         (AAdd
                           (AMod
                             (ASub (AVar idx) (AVar (cr_result ra)))
                             (AVar groups))
                           (AVar groups))
                         (AVar groups));
                     cr_code ru;
                     CIf
                       (AAnd
                         (AAnd (ctx_active cctx)
                           (AEq (AVar color) (AVar owner)))
                         (AEq (AVar child_rank) (ANumInt 0)))
                       []
                       (CAssign acc
                         (AAdd (AVar acc) (AVar (cr_result ru))))
                       [] CSkip]);
                CAssign result (zero_aexpr (cr_type ru));
                CAllreduce acc result];
           cr_result := result;
           cr_type := cr_type ru;
           cr_next_fresh := S (cr_next_fresh ru) |}
      else
        let acc := temp_name nf in
        let idx := temp_name (S nf) in
        let body_start := S (S nf) in
        let body_ctx := ctx_bind_var cctx i idx in
        let ru :=
          compile body (gamma_bind_int Gamma i) U B
            body_ctx body_start in
        let result := temp_name (cr_next_fresh ru) in
        {| cr_code :=
             seq_list
               [cr_code ra;
                cr_code rb;
                CAssign acc (zero_aexpr (cr_type ru));
                CIf (ctx_active cctx) []
                  (CFor
                    (CAssign idx
                      (AAdd (AVar (cr_result ra))
                        (AVar (ctx_rank cctx))))
                    (ALe (AVar idx) (AVar (cr_result rb)))
                    (CAssign idx
                      (AAdd (AVar idx) (AVar (ctx_size cctx))))
                    (temp_names_between body_start (cr_next_fresh ru))
                    (seq_list
                      [cr_code ru;
                       CAssign acc
                         (AAdd (AVar acc) (AVar (cr_result ru)))]))
                  [] CSkip;
                CAssign result (zero_aexpr (cr_type ru));
                CAllreduce acc result];
           cr_result := result;
           cr_type := cr_type ru;
           cr_next_fresh := S (cr_next_fresh ru) |}
  end.
