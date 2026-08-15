
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Reals.Reals.
From Stdlib Require Import Relations.Relation_Operators.
From Stdlib Require Import Lia.
From Certification2 Require Export C05_LocalCorrectness.

Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope R_scope.

(** Construit les états exécutant un même code. *)
Definition running_states
  (Sigma : list store) (c : cmd) (k : kont) : global_config :=
  map (fun sigma =>
    {| ls_store := sigma; ls_kont := KCmd c :: k |}) Sigma.

(** Construit les états ayant atteint une continuation. *)
Definition final_states
  (Sigma : list store) (k : kont) : global_config :=
  map (fun sigma =>
    {| ls_store := sigma; ls_kont := k |}) Sigma.

(** Lit une variable dans une liste de mémoires. *)
Fixpoint store_values
  (x : var) (Sigma : list store) : option (list cvalue) :=
  match Sigma with
  | [] => Some []
  | sigma :: tl =>
      match sigma x, store_values x tl with
      | Some v, Some values => Some (v :: values)
      | _, _ => None
      end
  end.

(** Caractérise les entrées d'un Allreduce global. *)
Lemma allreduce_inputs_running :
  forall Sigma x y k,
    allreduce_inputs x y
      (running_states Sigma (CAllreduce x y) k) =
    store_values x Sigma.
Proof.
  induction Sigma as [|sigma tl IH]; intros x y k; simpl.
  - reflexivity.
  - now rewrite !String.eqb_refl, IH.
Qed.

(** Caractérise les états après un Allreduce global. *)
Lemma allreduce_finish_running :
  forall Sigma x y total k,
    allreduce_finish y total
      (running_states Sigma (CAllreduce x y) k) =
    final_states
      (map (fun sigma => store_update sigma y total) Sigma) k.
Proof.
  induction Sigma as [|sigma tl IH]; intros x y total k; simpl.
  - reflexivity.
  - now rewrite IH.
Qed.

(** Relie la réduction cible à la somme source. *)
Lemma cvalue_sum_list_correct :
  forall t values,
    values <> [] ->
    Forall (fun value => value_has_type value t) values ->
    cvalue_sum_list (map cvalue_of_value values) =
    Some (cvalue_of_value (value_sum t values)).
Proof.
  intros t values. induction values as [|value values IH];
    intros Hnonempty Htyped.
  - contradiction.
  - inversion Htyped as [|? ? Hvalue Hvalues]; subst.
    destruct values as [|next tl].
    + simpl. rewrite add_values_zero_right; [reflexivity | exact Hvalue].
    + change
        (match
           cvalue_sum_list
             (map cvalue_of_value (next :: tl))
         with
         | Some rest => add_cvalues (cvalue_of_value value) rest
         | None => None
         end =
         Some
           (cvalue_of_value
             (add_values value (value_sum t (next :: tl))))).
      rewrite (IH ltac:(discriminate) Hvalues).
      apply add_cvalues_correct.
Qed.

(** Exécute globalement un Allreduce prêt. *)
Lemma allreduce_global_run :
  forall Sigma x y values total k,
    store_values x Sigma = Some values ->
    cvalue_sum_list values = Some total ->
    global_steps
      (running_states Sigma (CAllreduce x y) k)
      (final_states
        (map (fun sigma => store_update sigma y total) Sigma) k).
Proof.
  intros Sigma x y values total k Hvalues Hsum.
  unfold global_steps. eapply rt1n_trans.
  - apply StepAllreduce
      with (x := x) (y := y) (values := values) (total := total).
    + now rewrite allreduce_inputs_running.
    + exact Hsum.
  - rewrite allreduce_finish_running. constructor.
Qed.

(** Lève une exécution locale en exécution globale. *)
Lemma global_steps_lift_local :
  forall s s',
    local_steps s s' ->
    forall q tl,
      global_steps
        (List.app q (s :: tl))
        (List.app q (s' :: tl)).
Proof.
  intros s s' Hsteps.
  induction Hsteps as [|x y z Hstep Hrest IH];
    intros q tl.
  - constructor.
  - unfold global_steps. eapply rt1n_trans.
    + apply StepGlobal. exact Hstep.
    + apply IH.
Qed.

(** Lève toutes les exécutions locales correspondantes. *)
Lemma global_steps_lift_forall2 :
  forall states states',
    Forall2 local_steps states states' ->
    forall q,
      global_steps
        (List.app q states)
        (List.app q states').
Proof.
  intros states states' Hstates.
  induction Hstates as [|s s' tl tl' Hhead Htail IH]; intros q.
  - constructor.
  - eapply global_steps_trans.
    + apply global_steps_lift_local. exact Hhead.
    + specialize (IH (List.app q [s'])).
      replace (List.app q (s' :: tl))
        with (List.app (List.app q [s']) tl).
      2: { rewrite <- List.app_assoc. reflexivity. }
      replace (List.app q (s' :: tl'))
        with (List.app (List.app q [s']) tl').
      2: { rewrite <- List.app_assoc. reflexivity. }
      exact IH.
Qed.

(** Ouvre globalement une commande séquentielle. *)
Lemma global_steps_open_seq :
  forall Sigma c1 c2 k,
    global_steps
      (running_states Sigma (CSeq c1 c2) k)
      (running_states Sigma c1 (KCmd c2 :: k)).
Proof.
  intros Sigma c1 c2 k.
  apply global_steps_lift_forall2 with (q := []).
  induction Sigma as [|sigma Sigma IH].
  - constructor.
  - constructor.
    + unfold local_steps. eapply rt1n_trans.
      * apply StepSeq.
      * constructor.
    + exact IH.
Qed.

(** Relie Forall2 aux éléments de même indice. *)
Lemma forall2_nth_error :
  forall (A B : Type) (P : A -> B -> Prop) xs ys index x y,
    Forall2 P xs ys ->
    nth_error xs index = Some x ->
    nth_error ys index = Some y ->
    P x y.
Proof.
  intros A B P xs ys index x y Hrelation.
  revert index x y.
  induction Hrelation as
      [|x y xs ys Hhead Htail IH];
    intros index x0 y0 Hx Hy.
  - destruct index; discriminate.
  - destruct index.
    + simpl in Hx, Hy.
      injection Hx as <-. injection Hy as <-. exact Hhead.
    + simpl in Hx, Hy. eapply IH; eauto.
Qed.

(** Relation point à point entre trois listes. *)
Inductive Forall3 {A B C : Type} (P : A -> B -> C -> Prop)
  : list A -> list B -> list C -> Prop :=
| Forall3_nil : Forall3 P [] [] []
| Forall3_cons :
    forall x y z xs ys zs,
      P x y z ->
      Forall3 P xs ys zs ->
      Forall3 P (x :: xs) (y :: ys) (z :: zs).

(** Construit Forall3 à partir des éléments indexés. *)
Lemma forall3_seq_from_nth :
  forall (A B : Type) (P : nat -> A -> B -> Prop)
    p (xs : list A) (ys : list B),
    length xs = p ->
    length ys = p ->
    (forall index x y,
      nth_error xs index = Some x ->
      nth_error ys index = Some y ->
      P index x y) ->
    Forall3 P (seq 0 p) xs ys.
Proof.
  intros A B P p. revert P.
  induction p as [|p IH]; intros P xs ys Hxs Hys Hnth.
  - destruct xs, ys; try discriminate. constructor.
  - destruct xs as [|x xs], ys as [|y ys]; try discriminate.
    simpl in Hxs, Hys. injection Hxs as Hxs. injection Hys as Hys.
    simpl. constructor.
    + apply Hnth with (index := 0%nat); reflexivity.
    + rewrite <- seq_shift.
      assert (Hshift :
        forall ranks values stores,
          Forall3 (fun rank value store => P (S rank) value store)
            ranks values stores ->
          Forall3 P (map S ranks) values stores).
      { intros ranks values stores Hrelation.
        induction Hrelation; simpl; constructor; assumption. }
      apply Hshift.
      apply (IH (fun rank value store => P (S rank) value store)
        xs ys Hxs Hys).
      intros index value store Hvalue Hstore.
      apply Hnth with (index := S index);
        assumption.
Qed.


(** Collecte les résultats de toutes les simulations locales. *)
Lemma collect_local_simulations :
  forall mu rho Sigma r v fresh,
    (forall sigma,
      store_represents mu rho sigma ->
      store_fresh sigma fresh ->
      local_simulation mu rho sigma r v) ->
    stores_represent mu rho Sigma ->
    initially_fresh Sigma fresh ->
    forall k,
      exists Sigma',
        Forall2
          (fun sigma sigma' =>
            executes sigma (cr_code r) k sigma')
          Sigma Sigma' /\
        Forall
          (compiled_result_matches (cr_result r) v) Sigma' /\
        stores_represent mu rho Sigma' /\
        initially_fresh Sigma' (cr_next_fresh r) /\
        Forall2 preserves_store Sigma Sigma'.
Proof.
  intros mu rho Sigma r v fresh Hsound Hrep Hfresh k.
  unfold stores_represent, initially_fresh in *.
  revert Hrep Hfresh.
  induction Sigma as [|sigma tl IHSigma]; intros Hrep Hfresh.
  - exists []. repeat split; constructor.
  - inversion Hrep as [|? ? Hrep_head Hrep_tail]; subst.
    inversion Hfresh as [|? ? Hfresh_head Hfresh_tail]; subst.
    pose proof
      (Hsound sigma Hrep_head Hfresh_head) as Hlocal.
    unfold local_simulation in Hlocal.
    specialize (Hlocal k).
    destruct Hlocal as
      [sigma' [Hexec [Hmatch [Hrep' [Hfresh' Hpres]]]]].
    specialize (IHSigma Hrep_tail Hfresh_tail).
    destruct IHSigma as
      [Sigma'
        [Hexecs [Hmatches [Hreps [Hfreshs Hpreserves]]]]].
    exists (sigma' :: Sigma'). repeat split; constructor; assumption.
Qed.

(** Assemble des exécutions locales en exécution globale. *)
Lemma executions_form_global_run :
  forall Sigma Sigma' c k,
    Forall2
      (fun sigma sigma' => executes sigma c k sigma')
      Sigma Sigma' ->
    forall q,
      global_steps
        (List.app q (running_states Sigma c k))
        (List.app q (final_states Sigma' k)).
Proof.
  intros Sigma Sigma' c k Hexec q.
  apply global_steps_lift_forall2.
  induction Hexec.
  - constructor.
  - constructor; assumption.
Qed.
