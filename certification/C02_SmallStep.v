
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Reals.Reals.
From Stdlib Require Import Relations.Relation_Operators.
From Stdlib Require Import Lia.
From Certification2 Require Export C01_TargetCompiler.

Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope R_scope.


(** Convertit une valeur source en valeur cible. *)
Definition cvalue_of_value (v : value) : cvalue :=
  match v with
  | VInt n => CVInt n
  | VFloat r => CVFloat r
  end.

(** Convertit partiellement une valeur cible en valeur source. *)
Definition value_of_cvalue (v : cvalue) : option value :=
  match v with
  | CVInt n => Some (VInt n)
  | CVFloat r => Some (VFloat r)
  | CVBool _ => None
  end.

(** Met à jour une case de la mémoire cible. *)
Definition store_update (sigma : store) (x : var) (v : cvalue) : store :=
  fun y => if String.eqb y x then Some v else sigma y.

(** Supprime une liste de variables de la mémoire. *)
Fixpoint store_remove (sigma : store) (xs : list var) : store :=
  match xs with
  | [] => sigma
  | x :: tl =>
      store_remove
        (fun y => if String.eqb y x then None else sigma y) tl
  end.

(** Additionne deux valeurs numériques cibles. *)
Definition add_cvalues (v1 v2 : cvalue) : option cvalue :=
  match v1, v2 with
  | CVInt n1, CVInt n2 => Some (CVInt (n1 + n2))
  | CVInt n1, CVFloat r2 => Some (CVFloat (IZR n1 + r2))
  | CVFloat r1, CVInt n2 => Some (CVFloat (r1 + IZR n2))
  | CVFloat r1, CVFloat r2 => Some (CVFloat (r1 + r2))
  | _, _ => None
  end.

(** Multiplie deux valeurs numériques cibles. *)
Definition mul_cvalues (v1 v2 : cvalue) : option cvalue :=
  match v1, v2 with
  | CVInt n1, CVInt n2 => Some (CVInt (n1 * n2))
  | CVInt n1, CVFloat r2 => Some (CVFloat (IZR n1 * r2))
  | CVFloat r1, CVInt n2 => Some (CVFloat (r1 * IZR n2))
  | CVFloat r1, CVFloat r2 => Some (CVFloat (r1 * r2))
  | _, _ => None
  end.

(** Soustrait deux valeurs numériques cibles. *)
Definition sub_cvalues (v1 v2 : cvalue) : option cvalue :=
  match v1, v2 with
  | CVInt n1, CVInt n2 => Some (CVInt (n1 - n2))
  | CVInt n1, CVFloat r2 => Some (CVFloat (IZR n1 - r2))
  | CVFloat r1, CVInt n2 => Some (CVFloat (r1 - IZR n2))
  | CVFloat r1, CVFloat r2 => Some (CVFloat (r1 - r2))
  | _, _ => None
  end.

(** Calcule le modulo de deux entiers cibles. *)
Definition mod_cvalues (v1 v2 : cvalue) : option cvalue :=
  match v1, v2 with
  | CVInt n1, CVInt n2 =>
      if Z.eq_dec n2 0 then None else Some (CVInt (Z.modulo n1 n2))
  | _, _ => None
  end.

(** Compare deux valeurs numériques cibles. *)
Definition le_cvalues (v1 v2 : cvalue) : option cvalue :=
  match v1, v2 with
  | CVInt n1, CVInt n2 => Some (CVBool (Z.leb n1 n2))
  | CVInt n1, CVFloat r2 =>
      Some (CVBool (if Rle_dec (IZR n1) r2 then true else false))
  | CVFloat r1, CVInt n2 =>
      Some (CVBool (if Rle_dec r1 (IZR n2) then true else false))
  | CVFloat r1, CVFloat r2 =>
      Some (CVBool (if Rle_dec r1 r2 then true else false))
  | _, _ => None
  end.

(** Teste l'égalité de deux valeurs cibles. *)
Definition eq_cvalues (v1 v2 : cvalue) : bool :=
  match v1, v2 with
  | CVInt n1, CVInt n2 => Z.eqb n1 n2
  | CVFloat r1, CVFloat r2 =>
      if Req_EM_T r1 r2 then true else false
  | CVBool b1, CVBool b2 => Bool.eqb b1 b2
  | _, _ => false
  end.

(** Calcule le nombre de groupes enfants. *)
Definition nb_groups_sem (size : Z) : Z :=
  if Z.gtb size 1 then 2 else 1.

(** Calcule la taille maximale d'un groupe enfant. *)
Definition group_size_sem (size groups : Z) : Z :=
  Z.div (size + groups - 1) groups.

(** Calcule le groupe associé à un rang. *)
Definition color_sem (rank group_size groups : Z) : Z :=
  Z.min (Z.div rank group_size) (groups - 1).

(** Calcule le rang local dans un groupe enfant. *)
Definition child_rank_sem (rank color group_size : Z) : Z :=
  rank - color * group_size.

(** Calcule la taille effective d'un groupe enfant. *)
Definition child_size_sem (size color group_size : Z) : Z :=
  Z.min group_size (size - color * group_size).


(** Évalue une expression cible dans une mémoire. *)
Fixpoint aeval (sigma : store) (a : aexpr) : option cvalue :=
  match a with
  | ANumInt n => Some (CVInt n)
  | ANumFloat r => Some (CVFloat r)
  | ABool b => Some (CVBool b)
  | AVar x => sigma x
  | AUnaryPrim op a1 =>
      match aeval sigma a1 with
      | Some cv =>
          match value_of_cvalue cv with
          | Some v => Some (cvalue_of_value (unary_target_sem op v))
          | None => None
          end
      | None => None
      end
  | AAdd a1 a2 =>
      match aeval sigma a1, aeval sigma a2 with
      | Some v1, Some v2 => add_cvalues v1 v2
      | _, _ => None
      end
  | AMul a1 a2 =>
      match aeval sigma a1, aeval sigma a2 with
      | Some v1, Some v2 => mul_cvalues v1 v2
      | _, _ => None
      end
  | ASub a1 a2 =>
      match aeval sigma a1, aeval sigma a2 with
      | Some v1, Some v2 => sub_cvalues v1 v2
      | _, _ => None
      end
  | AMod a1 a2 =>
      match aeval sigma a1, aeval sigma a2 with
      | Some v1, Some v2 => mod_cvalues v1 v2
      | _, _ => None
      end
  | ABinaryPrim op a1 a2 =>
      match aeval sigma a1, aeval sigma a2 with
      | Some cv1, Some cv2 =>
          match value_of_cvalue cv1, value_of_cvalue cv2 with
          | Some v1, Some v2 =>
              Some (cvalue_of_value (binary_target_sem op v1 v2))
          | _, _ => None
          end
      | _, _ => None
      end
  | ALe a1 a2 =>
      match aeval sigma a1, aeval sigma a2 with
      | Some v1, Some v2 => le_cvalues v1 v2
      | _, _ => None
      end
  | AEq a1 a2 =>
      match aeval sigma a1, aeval sigma a2 with
      | Some v1, Some v2 => Some (CVBool (eq_cvalues v1 v2))
      | _, _ => None
      end
  | ANot a1 =>
      match aeval sigma a1 with
      | Some (CVBool b) => Some (CVBool (negb b))
      | _ => None
      end
  | AAnd a1 a2 =>
      match aeval sigma a1, aeval sigma a2 with
      | Some (CVBool b1), Some (CVBool b2) =>
          Some (CVBool (andb b1 b2))
      | _, _ => None
      end
  | ANbGroups size =>
      match aeval sigma size with
      | Some (CVInt p) => Some (CVInt (nb_groups_sem p))
      | _ => None
      end
  | AGroupSize size groups =>
      match aeval sigma size, aeval sigma groups with
      | Some (CVInt p), Some (CVInt g) =>
          Some (CVInt (group_size_sem p g))
      | _, _ => None
      end
  | AColor rank group_size groups =>
      match aeval sigma rank, aeval sigma group_size,
            aeval sigma groups with
      | Some (CVInt r), Some (CVInt t), Some (CVInt g) =>
          Some (CVInt (color_sem r t g))
      | _, _, _ => None
      end
  | AChildRank rank color group_size =>
      match aeval sigma rank, aeval sigma color,
            aeval sigma group_size with
      | Some (CVInt r), Some (CVInt c), Some (CVInt t) =>
          Some (CVInt (child_rank_sem r c t))
      | _, _, _ => None
      end
  | AChildSize size color group_size =>
      match aeval sigma size, aeval sigma color,
            aeval sigma group_size with
      | Some (CVInt p), Some (CVInt c), Some (CVInt t) =>
          Some (CVInt (child_size_sem p c t))
      | _, _, _ => None
      end
  end.

(** Relation de transition petit pas locale. *)
Inductive local_step : local_state -> local_state -> Prop :=
| StepAssign :
    forall sigma k x a v,
      aeval sigma a = Some v ->
      local_step
        {| ls_store := sigma; ls_kont := KCmd (CAssign x a) :: k |}
        {| ls_store := store_update sigma x v;
           ls_kont := KCmd CSkip :: k |}
| StepSeq :
    forall sigma k c1 c2,
      local_step
        {| ls_store := sigma; ls_kont := KCmd (CSeq c1 c2) :: k |}
        {| ls_store := sigma;
           ls_kont := KCmd c1 :: KCmd c2 :: k |}
| StepSkip :
    forall sigma k,
      local_step
        {| ls_store := sigma; ls_kont := KCmd CSkip :: k |}
        {| ls_store := sigma; ls_kont := k |}
| StepDel :
    forall sigma k xs,
      local_step
        {| ls_store := sigma; ls_kont := KDel xs :: k |}
        {| ls_store := store_remove sigma xs; ls_kont := k |}
| StepIfTrue :
    forall sigma k test then_cleanup then_branch
      else_cleanup else_branch,
      aeval sigma test = Some (CVBool true) ->
      local_step
        {| ls_store := sigma;
           ls_kont :=
             KCmd
               (CIf test then_cleanup then_branch
                 else_cleanup else_branch) :: k |}
        {| ls_store := sigma;
           ls_kont :=
             KCmd then_branch :: KDel then_cleanup :: k |}
| StepIfFalse :
    forall sigma k test then_cleanup then_branch
      else_cleanup else_branch,
      aeval sigma test = Some (CVBool false) ->
      local_step
        {| ls_store := sigma;
           ls_kont :=
             KCmd
               (CIf test then_cleanup then_branch
                 else_cleanup else_branch) :: k |}
        {| ls_store := sigma;
           ls_kont :=
             KCmd else_branch :: KDel else_cleanup :: k |}
| StepForInit :
    forall sigma k init test step cleanup body,
      init <> CSkip ->
      local_step
        {| ls_store := sigma;
           ls_kont :=
             KCmd (CFor init test step cleanup body) :: k |}
        {| ls_store := sigma;
           ls_kont :=
             KCmd init ::
             KCmd (CFor CSkip test step cleanup body) :: k |}
| StepForTrue :
    forall sigma k test step cleanup body,
      aeval sigma test = Some (CVBool true) ->
      local_step
        {| ls_store := sigma;
           ls_kont :=
             KCmd (CFor CSkip test step cleanup body) :: k |}
        {| ls_store := sigma;
           ls_kont :=
             KCmd body :: KDel cleanup :: KCmd step ::
             KCmd (CFor CSkip test step cleanup body) :: k |}
| StepForFalse :
    forall sigma k test step cleanup body,
      aeval sigma test = Some (CVBool false) ->
      local_step
        {| ls_store := sigma;
           ls_kont :=
             KCmd (CFor CSkip test step cleanup body) :: k |}
        {| ls_store := sigma; ls_kont := KCmd CSkip :: k |}.

(** Clôture réflexive transitive des pas locaux. *)
Definition local_steps : local_state -> local_state -> Prop :=
  clos_refl_trans_1n local_state local_step.

(** Additionne une liste non vide de valeurs cibles. *)
Fixpoint cvalue_sum_list (values : list cvalue) : option cvalue :=
  match values with
  | [] => None
  | [v] => Some v
  | v :: tl =>
      match cvalue_sum_list tl with
      | Some rest => add_cvalues v rest
      | None => None
      end
  end.

(** Collecte les contributions d'un Allreduce prêt. *)
Fixpoint allreduce_inputs
  (x y : var) (g : global_config) : option (list cvalue) :=
  match g with
  | [] => Some []
  | {| ls_store := sigma;
       ls_kont := KCmd (CAllreduce x' y') :: _ |} :: tl =>
      if andb (String.eqb x x') (String.eqb y y') then
        match sigma x, allreduce_inputs x y tl with
        | Some v, Some values => Some (v :: values)
        | _, _ => None
        end
      else None
  | _ => None
  end.

(** Termine un Allreduce avec sa valeur totale. *)
Fixpoint allreduce_finish
  (y : var) (total : cvalue) (g : global_config) : global_config :=
  match g with
  | [] => []
  | {| ls_store := sigma;
       ls_kont := KCmd (CAllreduce _ _) :: k |} :: tl =>
      {| ls_store := store_update sigma y total;
         ls_kont := k |} ::
      allreduce_finish y total tl
  | state :: tl => state :: allreduce_finish y total tl
  end.

(** Relation de transition petit pas globale. *)
Inductive global_step : global_config -> global_config -> Prop :=
| StepGlobal :
    forall (q : global_config) s s' tl,
      local_step s s' ->
      global_step (List.app q (s :: tl)) (List.app q (s' :: tl))
| StepAllreduce :
    forall g x y values total,
      allreduce_inputs x y g = Some values ->
      cvalue_sum_list values = Some total ->
      global_step g (allreduce_finish y total g).

(** Clôture réflexive transitive des pas globaux. *)
Definition global_steps : global_config -> global_config -> Prop :=
  clos_refl_trans_1n global_config global_step.

(** Lemmes génériques d'exécution. *)

(** Exécution complète d'une commande locale. *)
Definition executes
  (sigma : store) (c : cmd) (k : kont) (sigma' : store) : Prop :=
  local_steps
    {| ls_store := sigma; ls_kont := KCmd c :: k |}
    {| ls_store := sigma'; ls_kont := k |}.

(** Compose deux suites de pas locaux. *)
Lemma local_steps_trans :
  forall s1 s2 s3,
    local_steps s1 s2 ->
    local_steps s2 s3 ->
    local_steps s1 s3.
Proof.
  intros s1 s2 s3 H12. revert s3.
  induction H12 as [|x y z Hxy Hyz IH]; intros s3 H23.
  - exact H23.
  - eapply rt1n_trans.
    + exact Hxy.
    + apply IH. exact H23.
Qed.

(** Compose deux suites de pas globaux. *)
Lemma global_steps_trans :
  forall g1 g2 g3,
    global_steps g1 g2 ->
    global_steps g2 g3 ->
    global_steps g1 g3.
Proof.
  intros g1 g2 g3 H12. revert g3.
  induction H12 as [|x y z Hxy Hyz IH]; intros g3 H23.
  - exact H23.
  - eapply rt1n_trans.
    + exact Hxy.
    + apply IH. exact H23.
Qed.

(** Exécute correctement la commande vide. *)
Lemma executes_skip :
  forall sigma k, executes sigma CSkip k sigma.
Proof.
  intros sigma k. unfold executes, local_steps.
  eapply rt1n_trans.
  - apply StepSkip.
  - constructor.
Qed.

(** Exécute correctement une affectation. *)
Lemma executes_assign :
  forall sigma k x a v,
    aeval sigma a = Some v ->
    executes sigma (CAssign x a) k (store_update sigma x v).
Proof.
  intros sigma k x a v Heval. unfold executes, local_steps.
  eapply rt1n_trans.
  - apply StepAssign. exact Heval.
  - eapply rt1n_trans.
    + apply StepSkip.
    + constructor.
Qed.

(** Compose l'exécution de deux commandes séquentielles. *)
Lemma executes_seq :
  forall sigma sigma1 sigma2 c1 c2 k,
    executes sigma c1 (KCmd c2 :: k) sigma1 ->
    executes sigma1 c2 k sigma2 ->
    executes sigma (CSeq c1 c2) k sigma2.
Proof.
  intros sigma sigma1 sigma2 c1 c2 k H1 H2.
  unfold executes in *. eapply local_steps_trans.
  - unfold local_steps. eapply rt1n_trans.
    + apply StepSeq.
    + exact H1.
  - exact H2.
Qed.

(** Exécute le nettoyage d'une liste de variables. *)
Lemma executes_del :
  forall sigma xs k,
    local_steps
      {| ls_store := sigma; ls_kont := KDel xs :: k |}
      {| ls_store := store_remove sigma xs; ls_kont := k |}.
Proof.
  intros sigma xs k. unfold local_steps.
  eapply rt1n_trans.
  - apply StepDel.
  - constructor.
Qed.

(** Exécute la branche vraie d'une condition. *)
Lemma executes_if_true :
  forall sigma sigma' test then_cleanup then_branch
    else_cleanup else_branch k,
    aeval sigma test = Some (CVBool true) ->
    executes sigma then_branch (KDel then_cleanup :: k) sigma' ->
    executes sigma
      (CIf test then_cleanup then_branch else_cleanup else_branch)
      k (store_remove sigma' then_cleanup).
Proof.
  intros sigma sigma' test then_cleanup then_branch
    else_cleanup else_branch k Htest Hbranch.
  unfold executes in *. eapply local_steps_trans.
  - unfold local_steps. eapply rt1n_trans.
    + apply StepIfTrue. exact Htest.
    + exact Hbranch.
  - apply executes_del.
Qed.

(** Exécute la branche fausse d'une condition. *)
Lemma executes_if_false :
  forall sigma sigma' test then_cleanup then_branch
    else_cleanup else_branch k,
    aeval sigma test = Some (CVBool false) ->
    executes sigma else_branch (KDel else_cleanup :: k) sigma' ->
    executes sigma
      (CIf test then_cleanup then_branch else_cleanup else_branch)
      k (store_remove sigma' else_cleanup).
Proof.
  intros sigma sigma' test then_cleanup then_branch
    else_cleanup else_branch k Htest Hbranch.
  unfold executes in *. eapply local_steps_trans.
  - unfold local_steps. eapply rt1n_trans.
    + apply StepIfFalse. exact Htest.
    + exact Hbranch.
  - apply executes_del.
Qed.

(** Exécute l'initialisation d'une boucle. *)
Lemma executes_for_init :
  forall sigma sigma' init test step cleanup body k,
    init <> CSkip ->
    executes sigma init
      (KCmd (CFor CSkip test step cleanup body) :: k) sigma' ->
    local_steps
      {| ls_store := sigma;
         ls_kont := KCmd (CFor init test step cleanup body) :: k |}
      {| ls_store := sigma';
         ls_kont := KCmd (CFor CSkip test step cleanup body) :: k |}.
Proof.
  intros sigma sigma' init test step cleanup body k Hinit Hexec.
  unfold executes in Hexec. unfold local_steps.
  eapply rt1n_trans.
  - apply StepForInit. exact Hinit.
  - exact Hexec.
Qed.

(** Termine une boucle dont le test est faux. *)
Lemma executes_for_false :
  forall sigma test step cleanup body k,
    aeval sigma test = Some (CVBool false) ->
    executes sigma (CFor CSkip test step cleanup body) k sigma.
Proof.
  intros sigma test step cleanup body k Htest.
  unfold executes, local_steps.
  eapply rt1n_trans.
  - apply StepForFalse. exact Htest.
  - eapply rt1n_trans.
    + apply StepSkip.
    + constructor.
Qed.

(** Compose une itération complète de boucle. *)
Lemma executes_for_iteration :
  forall sigma sigma1 sigma2 sigma3 sigma4
    test step cleanup body k,
    aeval sigma test = Some (CVBool true) ->
    executes sigma body
      (KDel cleanup :: KCmd step ::
       KCmd (CFor CSkip test step cleanup body) :: k) sigma1 ->
    local_steps
      {| ls_store := sigma1;
         ls_kont :=
           KDel cleanup :: KCmd step ::
           KCmd (CFor CSkip test step cleanup body) :: k |}
      {| ls_store := sigma2;
         ls_kont :=
           KCmd step ::
           KCmd (CFor CSkip test step cleanup body) :: k |} ->
    executes sigma2 step
      (KCmd (CFor CSkip test step cleanup body) :: k) sigma3 ->
    executes sigma3
      (CFor CSkip test step cleanup body) k sigma4 ->
    executes sigma
      (CFor CSkip test step cleanup body) k sigma4.
Proof.
  intros sigma sigma1 sigma2 sigma3 sigma4
    test step cleanup body k Htest Hbody Hdel Hstep Hloop.
  unfold executes in *. eapply local_steps_trans.
  - unfold local_steps. eapply rt1n_trans.
    + apply StepForTrue. exact Htest.
    + exact Hbody.
  - eapply local_steps_trans; [exact Hdel |].
    eapply local_steps_trans; [exact Hstep | exact Hloop].
Qed.

(** Exécute les trois premières commandes d'une séquence. *)
Lemma local_steps_seq_prefix3 :
  forall sigma sigma1 sigma2 sigma3 c1 c2 c3 c4 k,
    executes sigma c1
      (KCmd (CSeq c2 (CSeq c3 c4)) :: k) sigma1 ->
    executes sigma1 c2
      (KCmd (CSeq c3 c4) :: k) sigma2 ->
    executes sigma2 c3 (KCmd c4 :: k) sigma3 ->
    local_steps
      {| ls_store := sigma;
         ls_kont := KCmd (CSeq c1 (CSeq c2 (CSeq c3 c4))) :: k |}
      {| ls_store := sigma3; ls_kont := KCmd c4 :: k |}.
Proof.
  intros sigma sigma1 sigma2 sigma3 c1 c2 c3 c4 k
    Hfirst Hsecond Hthird.
  unfold executes in *.
  eapply local_steps_trans.
  - unfold local_steps. eapply rt1n_trans.
    + apply StepSeq.
    + exact Hfirst.
  - eapply local_steps_trans.
    + unfold local_steps. eapply rt1n_trans.
      * apply StepSeq.
      * exact Hsecond.
    + unfold local_steps. eapply rt1n_trans.
      * apply StepSeq.
      * exact Hthird.
Qed.
