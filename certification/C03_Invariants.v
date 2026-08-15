
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Reals.Reals.
From Stdlib Require Import Relations.Relation_Operators.
From Stdlib Require Import Lia.
From Certification2 Require Export C02_SmallStep.

Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope R_scope.


(** Relie une variable cible à la valeur source calculée. *)
Definition compiled_result_matches
  (x : var) (v : value) (sigma : store) : Prop :=
  sigma x = Some (cvalue_of_value v).

(** Relie une mémoire cible à un environnement source. *)
Definition store_represents
  (mu : var -> var) (rho : env) (sigma : store) : Prop :=
  forall x v,
    rho x = Some v ->
    sigma (mu x) = Some (cvalue_of_value v).

(** Étend la représentation à toutes les mémoires. *)
Definition stores_represent
  (mu : var -> var) (rho : env) (Sigma : list store) : Prop :=
  Forall (store_represents mu rho) Sigma.

(** Exprime la fraîcheur des temporaires d'une mémoire. *)
Definition store_fresh (sigma : store) (fresh : nat) : Prop :=
  forall n, (fresh <= n)%nat -> sigma (temp_name n) = None.

(** Exprime la fraîcheur dans toutes les mémoires initiales. *)
Definition initially_fresh (Sigma : list store) (fresh : nat) : Prop :=
  Forall (fun sigma => store_fresh sigma fresh) Sigma.

(** Relie les valeurs source à leurs types déclarés. *)
Definition env_compatible (Gamma : tyenv) (rho : env) : Prop :=
  forall x t,
    Gamma x = Some t ->
    exists v, rho x = Some v /\ value_has_type v t.

(** Exprime la préservation des cases déjà définies. *)
Definition preserves_store (before after : store) : Prop :=
  forall x v, before x = Some v -> after x = Some v.

(** Préserve l'évaluation cible entre deux mémoires compatibles. *)
Lemma aeval_preserved :
  forall sigma sigma' a value,
    preserves_store sigma sigma' ->
    aeval sigma a = Some value ->
    aeval sigma' a = Some value.
Proof.
  intros sigma sigma' a. induction a; intros value Hpres Heval;
    simpl in Heval |- *; try exact Heval.
  - now apply Hpres.
  - destruct (aeval sigma a) eqn:Harg in Heval; try discriminate.
    specialize (IHa _ Hpres Harg). now rewrite IHa.
  - destruct (aeval sigma a1) eqn:Hleft in Heval; try discriminate.
    destruct (aeval sigma a2) eqn:Hright in Heval; try discriminate.
    specialize (IHa1 _ Hpres Hleft).
    specialize (IHa2 _ Hpres Hright).
    rewrite IHa1, IHa2. exact Heval.
  - destruct (aeval sigma a1) eqn:Hleft in Heval; try discriminate.
    destruct (aeval sigma a2) eqn:Hright in Heval; try discriminate.
    specialize (IHa1 _ Hpres Hleft).
    specialize (IHa2 _ Hpres Hright). now rewrite IHa1, IHa2.
  - destruct (aeval sigma a1) eqn:Hleft in Heval; try discriminate.
    destruct (aeval sigma a2) eqn:Hright in Heval; try discriminate.
    specialize (IHa1 _ Hpres Hleft).
    specialize (IHa2 _ Hpres Hright). now rewrite IHa1, IHa2.
  - destruct (aeval sigma a1) eqn:Hleft in Heval; try discriminate.
    destruct (aeval sigma a2) eqn:Hright in Heval; try discriminate.
    specialize (IHa1 _ Hpres Hleft).
    specialize (IHa2 _ Hpres Hright). now rewrite IHa1, IHa2.
  - destruct (aeval sigma a1) eqn:Hleft in Heval; try discriminate.
    destruct (aeval sigma a2) eqn:Hright in Heval; try discriminate.
    specialize (IHa1 _ Hpres Hleft).
    specialize (IHa2 _ Hpres Hright). now rewrite IHa1, IHa2.
  - destruct (aeval sigma a1) eqn:Hleft in Heval; try discriminate.
    destruct (aeval sigma a2) eqn:Hright in Heval; try discriminate.
    specialize (IHa1 _ Hpres Hleft).
    specialize (IHa2 _ Hpres Hright). now rewrite IHa1, IHa2.
  - destruct (aeval sigma a1) eqn:Hleft in Heval; try discriminate.
    destruct (aeval sigma a2) eqn:Hright in Heval; try discriminate.
    specialize (IHa1 _ Hpres Hleft).
    specialize (IHa2 _ Hpres Hright).
    rewrite IHa1, IHa2.
    destruct c, c0; simpl in Heval |- *; try discriminate; exact Heval.
  - destruct (aeval sigma a) eqn:Harg in Heval; try discriminate.
    specialize (IHa _ Hpres Harg). now rewrite IHa.
  - destruct (aeval sigma a1) as [left|] eqn:Hleft in Heval;
      [| discriminate].
    destruct left; try discriminate.
    destruct (aeval sigma a2) as [right|] eqn:Hright in Heval;
      [| discriminate].
    destruct right; try discriminate.
    specialize (IHa1 _ Hpres Hleft).
    specialize (IHa2 _ Hpres Hright).
    now rewrite IHa1, IHa2.
  - destruct (aeval sigma a) eqn:Harg in Heval; try discriminate.
    specialize (IHa _ Hpres Harg). rewrite IHa.
    destruct c; simpl in Heval |- *; try discriminate; exact Heval.
  - destruct (aeval sigma a1) as [left|] eqn:Hleft in Heval;
      [| discriminate].
    destruct left; try discriminate.
    destruct (aeval sigma a2) as [right|] eqn:Hright in Heval;
      [| discriminate].
    destruct right; try discriminate.
    specialize (IHa1 _ Hpres Hleft).
    specialize (IHa2 _ Hpres Hright). now rewrite IHa1, IHa2.
  - destruct (aeval sigma a1) as [first|] eqn:Hfirst in Heval;
      [| discriminate].
    destruct first; try discriminate.
    destruct (aeval sigma a2) as [second|] eqn:Hsecond in Heval;
      [| discriminate].
    destruct second; try discriminate.
    destruct (aeval sigma a3) as [third|] eqn:Hthird in Heval;
      [| discriminate].
    destruct third; try discriminate.
    specialize (IHa1 _ Hpres Hfirst).
    specialize (IHa2 _ Hpres Hsecond).
    specialize (IHa3 _ Hpres Hthird). now rewrite IHa1, IHa2, IHa3.
  - destruct (aeval sigma a1) as [first|] eqn:Hfirst in Heval;
      [| discriminate].
    destruct first; try discriminate.
    destruct (aeval sigma a2) as [second|] eqn:Hsecond in Heval;
      [| discriminate].
    destruct second; try discriminate.
    destruct (aeval sigma a3) as [third|] eqn:Hthird in Heval;
      [| discriminate].
    destruct third; try discriminate.
    specialize (IHa1 _ Hpres Hfirst).
    specialize (IHa2 _ Hpres Hsecond).
    specialize (IHa3 _ Hpres Hthird). now rewrite IHa1, IHa2, IHa3.
  - destruct (aeval sigma a1) as [first|] eqn:Hfirst in Heval;
      [| discriminate].
    destruct first; try discriminate.
    destruct (aeval sigma a2) as [second|] eqn:Hsecond in Heval;
      [| discriminate].
    destruct second; try discriminate.
    destruct (aeval sigma a3) as [third|] eqn:Hthird in Heval;
      [| discriminate].
    destruct third; try discriminate.
    specialize (IHa1 _ Hpres Hfirst).
    specialize (IHa2 _ Hpres Hsecond).
    specialize (IHa3 _ Hpres Hthird). now rewrite IHa1, IHa2, IHa3.
Qed.

(** Résultat attendu d'une simulation locale compilée. *)
Definition local_simulation
  (mu : var -> var) (rho : env) (sigma : store)
  (r : compile_result) (v : value) : Prop :=
  forall k,
    exists sigma',
      executes sigma (cr_code r) k sigma' /\
      compiled_result_matches (cr_result r) v sigma' /\
      store_represents mu rho sigma' /\
      store_fresh sigma' (cr_next_fresh r) /\
      preserves_store sigma sigma'.

(** Lit la valeur qui vient d'être écrite. *)
Lemma store_update_same :
  forall sigma x v,
    store_update sigma x v x = Some v.
Proof.
  intros. unfold store_update. now rewrite String.eqb_refl.
Qed.

(** Préserve les autres cases lors d'une écriture. *)
Lemma store_update_other :
  forall sigma x y v,
    y <> x ->
    store_update sigma x v y = sigma y.
Proof.
  intros sigma x y v Hneq. unfold store_update.
  apply String.eqb_neq in Hneq. now rewrite Hneq.
Qed.

(** Établit l'injectivité de la conversion vers la cible. *)
Lemma cvalue_of_value_injective :
  forall v1 v2,
    cvalue_of_value v1 = cvalue_of_value v2 ->
    v1 = v2.
Proof.
  intros v1 v2 H.
  destruct v1, v2; simpl in H; inversion H; subst; reflexivity.
Qed.

(** Inverse la conversion d'une valeur source. *)
Lemma value_of_cvalue_of_value :
  forall v, value_of_cvalue (cvalue_of_value v) = Some v.
Proof.
  now intros [].
Qed.

(** Établit l'injectivité de l'encodage des naturels. *)
Lemma nat_tag_injective :
  forall n m, nat_tag n = nat_tag m -> n = m.
Proof.
  induction n as [| n IH]; destruct m as [| m]; simpl; intros H;
    try discriminate.
  - reflexivity.
  - f_equal. apply IH. now injection H.
Qed.

(** Établit l'injectivité des noms temporaires. *)
Lemma temp_name_injective :
  forall n m, temp_name n = temp_name m -> n = m.
Proof.
  intros n m H. apply nat_tag_injective.
  unfold temp_name in H. now injection H.
Qed.

(** Caractérise les indices d'une tranche de temporaires. *)
Lemma in_temp_names_from :
  forall start len n,
    In (temp_name n) (temp_names_from start len) <->
    (start <= n < start + len)%nat.
Proof.
  intros start len. revert start.
  induction len as [| len IH]; intros start n; simpl.
  - lia.
  - split.
    + intros [Heq | Hin].
      * apply temp_name_injective in Heq. lia.
      * apply (IH (S start) n) in Hin. lia.
    + intros Hrange.
      destruct (Nat.eq_dec n start) as [-> | Hneq].
      * now left.
      * right. apply (IH (S start) n). lia.
Qed.

(** Borne l'indice d'un temporaire intermédiaire. *)
Lemma in_temp_names_between :
  forall start stop n,
    (start <= stop)%nat ->
    (In (temp_name n) (temp_names_between start stop) <->
     (start <= n < stop)%nat).
Proof.
  intros start stop n Hle. unfold temp_names_between.
  rewrite in_temp_names_from.
  replace (start + (stop - start))%nat with stop by lia.
  reflexivity.
Qed.

(** Retrouve l'indice d'un temporaire intermédiaire. *)
Lemma in_temp_names_between_exists :
  forall start stop x,
    (start <= stop)%nat ->
    In x (temp_names_between start stop) ->
    exists n, x = temp_name n /\ (start <= n < stop)%nat.
Proof.
  intros start stop x Hle.
  unfold temp_names_between.
  remember (stop - start)%nat as len eqn:Hlen.
  revert start stop Hle Hlen.
  induction len as [| len IH]; intros start stop Hle Hlen Hin; simpl in Hin.
  - contradiction.
  - destruct Hin as [Heq | Hin].
    + exists start. split; [now symmetry | lia].
    + destruct (IH (S start) stop) as [n [Hn Hrange]]; try lia.
      * exact Hin.
      * exists n. split; [exact Hn | lia].
Qed.

(** Préserve une case absente de la liste supprimée. *)
Lemma store_remove_not_in :
  forall sigma xs x,
    ~ In x xs ->
    store_remove sigma xs x = sigma x.
Proof.
  intros sigma xs. revert sigma.
  induction xs as [| y tl IH]; intros sigma x Hnot; simpl.
  - reflexivity.
  - rewrite IH.
    + unfold store_update.
      destruct (String.eqb x y) eqn:Heq; [| reflexivity].
      apply String.eqb_eq in Heq. subst. exfalso.
      apply Hnot. now left.
    + intros Hin. apply Hnot. now right.
Qed.

(** Supprime effectivement une case listée. *)
Lemma store_remove_in :
  forall sigma xs x,
    In x xs ->
    store_remove sigma xs x = None.
Proof.
  intros sigma xs. revert sigma.
  induction xs as [| y tl IH]; intros sigma x Hin; simpl in *.
  - contradiction.
  - destruct Hin as [-> | Hin].
    + destruct (in_dec String.string_dec x tl) as [Hx | Hx].
      * apply IH. exact Hx.
      * rewrite store_remove_not_in; [| exact Hx].
        now rewrite String.eqb_refl.
    + apply IH. exact Hin.
Qed.

(** Affaiblit un seuil de fraîcheur. *)
Lemma store_fresh_monotone :
  forall sigma n n',
    store_fresh sigma n ->
    (n <= n')%nat ->
    store_fresh sigma n'.
Proof.
  unfold store_fresh. intros sigma n n' Hfresh Hle k Hk.
  apply Hfresh. lia.
Qed.

(** Préserve la fraîcheur après une écriture fraîche. *)
Lemma store_fresh_update :
  forall sigma start written v,
    store_fresh sigma start ->
    (start <= written)%nat ->
    store_fresh
      (store_update sigma (temp_name written) v) (S written).
Proof.
  unfold store_fresh. intros sigma start written v Hfresh Hle n Hn.
  rewrite store_update_other.
  - apply Hfresh. lia.
  - intros Heq. apply temp_name_injective in Heq. lia.
Qed.

(** Préserve la fraîcheur après une écriture antérieure. *)
Lemma store_fresh_update_below :
  forall sigma start written v,
    store_fresh sigma start ->
    (written < start)%nat ->
    store_fresh
      (store_update sigma (temp_name written) v) start.
Proof.
  unfold store_fresh. intros sigma start written v Hfresh Hlt n Hn.
  rewrite store_update_other.
  - apply Hfresh. exact Hn.
  - intros Heq. apply temp_name_injective in Heq. lia.
Qed.

(** Rétablit la fraîcheur après le nettoyage. *)
Lemma store_fresh_after_cleanup :
  forall sigma start stop,
    (start <= stop)%nat ->
    store_fresh sigma stop ->
    store_fresh
      (store_remove sigma (temp_names_between start stop)) start.
Proof.
  unfold store_fresh. intros sigma start stop Hle Hfresh n Hn.
  destruct (lt_dec n stop) as [Hlt | Hge].
  - apply store_remove_in.
    apply in_temp_names_between; lia.
  - rewrite store_remove_not_in.
    + apply Hfresh. lia.
    + intros Hin. apply in_temp_names_between in Hin; lia.
Qed.

(** Établit la réflexivité de la préservation. *)
Lemma preserves_store_refl :
  forall sigma, preserves_store sigma sigma.
Proof.
  intros sigma x v H. exact H.
Qed.

(** Établit la transitivité de la préservation. *)
Lemma preserves_store_trans :
  forall sigma1 sigma2 sigma3,
    preserves_store sigma1 sigma2 ->
    preserves_store sigma2 sigma3 ->
    preserves_store sigma1 sigma3.
Proof.
  unfold preserves_store. eauto.
Qed.

(** Préserve l'ancienne mémoire lors d'une écriture fraîche. *)
Lemma preserves_store_update_fresh :
  forall sigma x v,
    sigma x = None ->
    preserves_store sigma (store_update sigma x v).
Proof.
  unfold preserves_store. intros sigma x v Hnone y cv Hy.
  destruct (String.string_dec y x) as [-> | Hneq].
  - rewrite Hnone in Hy. discriminate.
  - now rewrite store_update_other.
Qed.

(** Propage une préservation après une écriture fraîche. *)
Lemma preserves_store_update_from_base :
  forall base sigma n v,
    store_fresh base n ->
    preserves_store base sigma ->
    preserves_store base (store_update sigma (temp_name n) v).
Proof.
  unfold preserves_store. intros base sigma n v Hfresh Hpres x cv Hx.
  rewrite store_update_other.
  - apply Hpres. exact Hx.
  - intros Heq. subst x.
    rewrite Hfresh in Hx; [discriminate | lia].
Qed.

(** Préserve la base après nettoyage des temporaires. *)
Lemma preserves_store_remove_fresh_range :
  forall base sigma start stop,
    (start <= stop)%nat ->
    store_fresh base start ->
    preserves_store base sigma ->
    preserves_store base
      (store_remove sigma (temp_names_between start stop)).
Proof.
  unfold preserves_store.
  intros base sigma start stop Hle Hfresh Hpres x cv Hx.
  rewrite store_remove_not_in.
  - apply Hpres. exact Hx.
  - intros Hin.
    apply in_temp_names_between_exists in Hin
      as [n [Hxname Hrange]]; [| exact Hle].
    subst x. rewrite Hfresh in Hx; [discriminate | lia].
Qed.

(** Conserve la représentation d'un environnement. *)
Lemma store_represents_preserved :
  forall mu rho sigma sigma',
    store_represents mu rho sigma ->
    preserves_store sigma sigma' ->
    store_represents mu rho sigma'.
Proof.
  unfold store_represents, preserves_store. eauto.
Qed.

(** Conserve une valeur compilée déjà calculée. *)
Lemma compiled_result_preserved :
  forall x v sigma sigma',
    compiled_result_matches x v sigma ->
    preserves_store sigma sigma' ->
    compiled_result_matches x v sigma'.
Proof.
  unfold compiled_result_matches, preserves_store. eauto.
Qed.

(** Étend la représentation par un indice entier. *)
Lemma store_represents_bind_int :
  forall cctx rho sigma i idx n,
    store_represents (ctx_repr cctx) rho sigma ->
    sigma idx = Some (CVInt n) ->
    store_represents (ctx_repr (ctx_bind_var cctx i idx))
      (env_update rho i (VInt n)) sigma.
Proof.
  intros cctx rho sigma i idx n Hrep Hidx x v Hlookup.
  unfold env_update in Hlookup. simpl.
  destruct (String.eqb x i) eqn:Heq.
  - apply String.eqb_eq in Heq. subst x.
    inversion Hlookup. subst v. exact Hidx.
  - apply Hrep. exact Hlookup.
Qed.

(** Relie le zéro cible au zéro source. *)
Lemma zero_aexpr_correct :
  forall sigma t,
    aeval sigma (zero_aexpr t) =
    Some (cvalue_of_value (zero_value t)).
Proof.
  now intros sigma [].
Qed.

(** Relie l'addition cible à l'addition source. *)
Lemma add_cvalues_correct :
  forall v1 v2,
    add_cvalues (cvalue_of_value v1) (cvalue_of_value v2) =
    Some (cvalue_of_value (add_values v1 v2)).
Proof.
  now intros [] [].
Qed.

(** Relie la multiplication cible à la multiplication source. *)
Lemma mul_cvalues_correct :
  forall v1 v2,
    mul_cvalues (cvalue_of_value v1) (cvalue_of_value v2) =
    Some (cvalue_of_value (mul_values v1 v2)).
Proof.
  now intros [] [].
Qed.

(** Préserve le type lors d'une addition source. *)
Lemma add_values_has_type :
  forall t v1 v2,
    value_has_type v1 t ->
    value_has_type v2 t ->
    value_has_type (add_values v1 v2) t.
Proof.
  intros [] [] []; simpl; tauto.
Qed.

(** Donne le type de la valeur nulle. *)
Lemma zero_value_has_type :
  forall t, value_has_type (zero_value t) t.
Proof.
  now intros [].
Qed.

(** Établit que zéro est neutre à gauche. *)
Lemma add_values_zero_left :
  forall t v,
    value_has_type v t ->
    add_values (zero_value t) v = v.
Proof.
  intros [] []; simpl; intros H; try contradiction;
    f_equal; ring.
Qed.

(** Établit que zéro est neutre à droite. *)
Lemma add_values_zero_right :
  forall t v,
    value_has_type v t ->
    add_values v (zero_value t) = v.
Proof.
  intros [] []; simpl; intros H; try contradiction;
    f_equal; ring.
Qed.

(** Établit l'associativité de l'addition des valeurs. *)
Lemma add_values_assoc :
  forall t v1 v2 v3,
    value_has_type v1 t ->
    value_has_type v2 t ->
    value_has_type v3 t ->
    add_values (add_values v1 v2) v3 =
    add_values v1 (add_values v2 v3).
Proof.
  intros [] [] [] []; simpl; intros H1 H2 H3;
    try contradiction; f_equal; ring.
Qed.

(** Établit la commutativité de l'addition des valeurs. *)
Lemma add_values_comm :
  forall t v1 v2,
    value_has_type v1 t ->
    value_has_type v2 t ->
    add_values v1 v2 = add_values v2 v1.
Proof.
  intros [] [] []; simpl; intros H1 H2;
    try contradiction; f_equal; ring.
Qed.

(** Additionne une liste de valeurs source. *)
Fixpoint value_sum (t : ty) (values : list value) : value :=
  match values with
  | [] => zero_value t
  | value :: tl => add_values value (value_sum t tl)
  end.

(** Donne le type d'une somme de valeurs. *)
Lemma value_sum_has_type :
  forall t values,
    Forall (fun value => value_has_type value t) values ->
    value_has_type (value_sum t values) t.
Proof.
  intros t values Hvalues. induction Hvalues; simpl.
  - apply zero_value_has_type.
  - now apply add_values_has_type.
Qed.

(** Distribue la somme sur la concaténation. *)
Lemma value_sum_app :
  forall t left right,
    Forall (fun value => value_has_type value t) left ->
    Forall (fun value => value_has_type value t) right ->
    value_sum t (left ++ right) =
    add_values (value_sum t left) (value_sum t right).
Proof.
  intros t left right Hleft Hright.
  induction Hleft as [|first left Hfirst Hleft IH]; simpl.
  - symmetry. apply add_values_zero_left.
    now apply value_sum_has_type.
  - rewrite IH.
    symmetry.
    apply
      (add_values_assoc t first
        (value_sum t left) (value_sum t right)).
    + exact Hfirst.
    + now apply value_sum_has_type.
    + now apply value_sum_has_type.
Qed.

(** Préserve une somme après rotation de liste. *)
Lemma value_sum_rotate :
  forall t first rest,
    value_has_type first t ->
    Forall (fun value => value_has_type value t) rest ->
    value_sum t (first :: rest) =
    value_sum t (rest ++ [first]).
Proof.
  intros t first rest Hfirst Hrest. simpl.
  rewrite value_sum_app; try assumption.
  - simpl. rewrite add_values_zero_right; [| exact Hfirst].
    apply (add_values_comm t first (value_sum t rest)).
    + exact Hfirst.
    + now apply value_sum_has_type.
  - constructor; [exact Hfirst | constructor].
Qed.

(** Déduit le type des résultats d'évaluation source. *)
Lemma eval_expr_value_has_type :
  forall Gamma U B rho e t v,
    eval_expr Gamma U B rho e t v ->
    value_has_type v t
with eval_sum_value_has_type :
  forall Gamma U B rho i m n body t v,
    eval_sum Gamma U B rho i m n body t v ->
    value_has_type v t.
Proof.
  - intros Gamma U B rho e t v Heval.
    destruct Heval.
    + simpl. exact I.
    + simpl. exact I.
    + assumption.
    + assumption.
    + assumption.
    + eapply eval_sum_value_has_type. eassumption.
    + eapply eval_sum_value_has_type. eassumption.
  - intros Gamma U B rho i m n body t v Heval.
    destruct Heval.
    + apply zero_value_has_type.
    + apply add_values_has_type.
      * eapply eval_expr_value_has_type. eassumption.
      * eapply eval_sum_value_has_type. eassumption.
Qed.

(** Type le résultat d'une somme par pas. *)
Lemma eval_stride_sum_value_has_type :
  forall Gamma U B rho i body t stride current upper value,
    eval_stride_sum Gamma U B rho i body t stride
      current upper value ->
    value_has_type value t.
Proof.
  intros Gamma U B rho i body t stride current upper value Heval.
  induction Heval.
  - apply zero_value_has_type.
  - apply add_values_has_type.
    + eapply eval_expr_value_has_type. exact H0.
    + exact IHHeval.
Qed.

(** Liste les contributions d'une partition par rang. *)
Definition stride_values
  (Gamma : tyenv) (U : unary_sig_env) (B : binary_sig_env)
  (rho : env) (i : var) (body : expr) (t : ty)
  (lower upper : Z) (p : nat) (values : list value) : Prop :=
  length values = p /\
  forall rank value,
    nth_error values rank = Some value ->
    eval_stride_sum Gamma U B rho i body t (Z.of_nat p)
      (lower + Z.of_nat rank) upper value.

(** Calcule la somme d'une répétition de zéros. *)
Lemma value_sum_repeat_zero :
  forall t p,
    value_sum t (repeat (zero_value t) p) = zero_value t.
Proof.
  intros t p. induction p; simpl.
  - reflexivity.
  - rewrite IHp. apply add_values_zero_left.
    apply zero_value_has_type.
Qed.

(** Type toutes les contributions d'une partition. *)
Lemma stride_values_typed :
  forall Gamma U B rho i body t lower upper p values,
    stride_values Gamma U B rho i body t lower upper p values ->
    Forall (fun value => value_has_type value t) values.
Proof.
  intros Gamma U B rho i body t lower upper p values [_ Hvalues].
  apply Forall_forall. intros value Hin.
  apply In_nth_error in Hin as [rank Hrank].
  eapply eval_stride_sum_value_has_type.
  now apply Hvalues with (rank := rank).
Qed.

(** Décompose une somme en contributions par rang. *)
Lemma eval_sum_partition_stride :
  forall Gamma U B rho i body t lower upper total,
    eval_sum Gamma U B rho i lower upper body t total ->
    forall p,
      (1 <= p)%nat ->
      exists values,
        stride_values Gamma U B rho i body t
          lower upper p values /\
        value_sum t values = total.
Proof.
  intros Gamma U B rho i body t lower upper total Hsum.
  induction Hsum as
      [Gamma0 U0 B0 rho0 i0 lower0 upper0 body0 t0 Hempty
      | Gamma0 U0 B0 rho0 i0 lower0 upper0 body0 t0
        current rest Hle Hcurrent Hrest IH].
  - intros p Hp.
    exists (repeat (zero_value t0) p). split.
    + split; [apply repeat_length |].
      intros rank value Hrank.
      apply nth_error_In in Hrank.
      apply repeat_spec in Hrank. subst value.
      apply EvalStrideEmpty. lia.
    + apply value_sum_repeat_zero.
  - intros p Hp.
    destruct (IH p Hp) as [values [Hstrides Htotal]].
    destruct Hstrides as [Hlength Hstrides].
    assert (Hvalues_nonempty : values <> []).
    { intros ->. simpl in Hlength. lia. }
    apply exists_last in Hvalues_nonempty as
      [initial [last Hvalues]].
    subst values.
    rewrite length_app in Hlength. simpl in Hlength.
    assert (Hlast :
      eval_stride_sum Gamma0 U0 B0 rho0 i0 body0 t0
        (Z.of_nat p)
        (lower0 + Z.of_nat p) upper0 last).
    { specialize
        (Hstrides (length initial) last).
      rewrite nth_error_app2 in Hstrides by lia.
      replace (length initial - length initial)%nat with 0%nat
        in Hstrides by lia.
      simpl in Hstrides.
      specialize (Hstrides eq_refl).
      replace
        ((lower0 + 1 + Z.of_nat (length initial))%Z)
        with ((lower0 + Z.of_nat p)%Z) in Hstrides.
      - exact Hstrides.
      - assert
          (Z.of_nat p = (Z.of_nat (length initial) + 1)%Z).
        { rewrite <- Hlength, Nat2Z.inj_add. simpl. lia. }
        lia. }
    exists (add_values current last :: initial). split.
    + split.
      * simpl. lia.
      * intros rank value Hrank.
        destruct rank as [|rank].
        -- simpl in Hrank. injection Hrank as <-.
           replace (lower0 + Z.of_nat 0)%Z with lower0 by lia.
           apply EvalStrideStep.
           ++ exact Hle.
           ++ exact Hcurrent.
           ++ exact Hlast.
        -- simpl in Hrank.
           assert (Hrank_initial :
             nth_error (initial ++ [last]) rank = Some value).
           { rewrite nth_error_app1.
             - exact Hrank.
             - apply nth_error_Some. rewrite Hrank. discriminate. }
           specialize (Hstrides rank value Hrank_initial).
           replace
             ((lower0 + Z.of_nat (S rank))%Z)
             with ((lower0 + 1 + Z.of_nat rank)%Z) by
             (rewrite Nat2Z.inj_succ; lia).
           exact Hstrides.
    + assert (Hinitial_typed :
        Forall (fun value => value_has_type value t0) initial).
      { apply Forall_forall. intros value Hin.
        apply In_nth_error in Hin as [rank Hrank].
        eapply eval_stride_sum_value_has_type.
        apply Hstrides with (rank := rank).
        rewrite nth_error_app1.
        - exact Hrank.
        - apply nth_error_Some. rewrite Hrank. discriminate. }
      assert (Hlast_typed : value_has_type last t0).
      { apply
          (eval_stride_sum_value_has_type
            Gamma0 U0 B0 rho0 i0 body0 t0 (Z.of_nat p)
            (lower0 + Z.of_nat p) upper0 last).
        exact Hlast. }
      assert (Hcurrent_typed : value_has_type current t0).
      { apply
          (eval_expr_value_has_type
            (gamma_bind_int Gamma0 i0) U0 B0
            (env_update rho0 i0 (VInt lower0)) body0 t0 current).
        exact Hcurrent. }
      assert (Hinitial_sum_typed :
        value_has_type (value_sum t0 initial) t0).
      { now apply value_sum_has_type. }
      assert (Happend :
        value_sum t0 (initial ++ [last]) =
        add_values (value_sum t0 initial) last).
      { rewrite (value_sum_app t0 initial [last]).
        - simpl. now rewrite add_values_zero_right.
        - exact Hinitial_typed.
        - constructor; [exact Hlast_typed | constructor]. }
      simpl.
      rewrite
        (add_values_assoc t0 current last (value_sum t0 initial)
          Hcurrent_typed Hlast_typed Hinitial_sum_typed).
      rewrite
        (add_values_comm t0 last (value_sum t0 initial)
          Hlast_typed Hinitial_sum_typed).
      rewrite <- Happend. now rewrite Htotal.
Qed.

(** Justifie l'évaluation cible d'une primitive unaire. *)
Lemma aeval_unary_correct :
  forall U B op sigma x v,
    compiled_result_matches x v sigma ->
    primitive_semantics_compatible U B ->
    aeval sigma (AUnaryPrim op (AVar x)) =
    Some (cvalue_of_value (unary_source_sem op v)).
Proof.
  intros U B op sigma x v Hx [Hunary _].
  simpl. unfold compiled_result_matches in Hx.
  rewrite Hx, value_of_cvalue_of_value, Hunary. reflexivity.
Qed.

(** Justifie l'évaluation cible d'une opération binaire. *)
Lemma aeval_binary_correct :
  forall U B op sigma x y v1 v2,
    compiled_result_matches x v1 sigma ->
    compiled_result_matches y v2 sigma ->
    primitive_semantics_compatible U B ->
    aeval sigma (binary_aexpr op x y) =
    Some (cvalue_of_value (binary_source_value op v1 v2)).
Proof.
  intros U B op sigma x y v1 v2 Hx Hy Hcompat.
  destruct op; simpl; unfold compiled_result_matches in *;
    rewrite Hx, Hy.
  - apply add_cvalues_correct.
  - apply mul_cvalues_correct.
  - destruct Hcompat as [_ Hbinary].
    rewrite !value_of_cvalue_of_value, Hbinary. reflexivity.
Qed.

(** Montre que la compilation avance l'indice frais. *)
Lemma compile_fresh_monotone :
  forall e Gamma U B cctx fresh,
    (fresh <= cr_next_fresh (compile e Gamma U B cctx fresh))%nat.
Proof.
  induction e as
      [n | r | x | op e IH
      | op e1 IH1 e2 IH2
      | i a IHa b IHb body IHbody
      | i a IHa b IHb body IHbody];
    intros Gamma U B cctx fresh; simpl; try lia.
  - remember (compile e Gamma U B cctx fresh) as re eqn:Hre.
    pose proof (IH Gamma U B cctx fresh) as H.
    rewrite <- Hre in H. simpl. lia.
  - remember (compile e1 Gamma U B cctx fresh) as r1 eqn:Hr1.
    remember
      (compile e2 Gamma U B cctx (cr_next_fresh r1))
      as r2 eqn:Hr2.
    pose proof (IH1 Gamma U B cctx fresh) as H1.
    pose proof
      (IH2 Gamma U B cctx (cr_next_fresh r1)) as H2.
    rewrite <- Hr1 in H1. rewrite <- Hr2 in H2. simpl. lia.
  - remember (compile a Gamma U B cctx fresh) as ra eqn:Hra.
    remember
      (compile b Gamma U B cctx (cr_next_fresh ra))
      as rb eqn:Hrb.
    remember
      (compile body (gamma_bind_int Gamma i) U B
        (ctx_bind_var cctx i (temp_name (S (cr_next_fresh rb))))
        (S (S (cr_next_fresh rb)))) as ru eqn:Hru.
    pose proof (IHa Gamma U B cctx fresh) as Ha.
    pose proof
      (IHb Gamma U B cctx (cr_next_fresh ra)) as Hb.
    pose proof
      (IHbody (gamma_bind_int Gamma i) U B
        (ctx_bind_var cctx i (temp_name (S (cr_next_fresh rb))))
        (S (S (cr_next_fresh rb)))) as Hu.
    rewrite <- Hra in Ha. rewrite <- Hrb in Hb. rewrite <- Hru in Hu.
    simpl. lia.
  - remember (compile a Gamma U B cctx fresh) as ra eqn:Hra.
    remember
      (compile b Gamma U B cctx (cr_next_fresh ra))
      as rb eqn:Hrb.
    pose proof (IHa Gamma U B cctx fresh) as Ha.
    pose proof
      (IHb Gamma U B cctx (cr_next_fresh ra)) as Hb.
    rewrite <- Hra in Ha. rewrite <- Hrb in Hb.
    destruct (has_parallel_sum body) eqn:Hparallel.
    + pose proof
        (IHbody (gamma_bind_int Gamma i) U B
          (ctx_bind_var
            (ctx_child cctx
              (temp_name (S (S (S (cr_next_fresh rb)))))
              (temp_name (S (S (S (S (cr_next_fresh rb))))))
              (temp_name (S (S (cr_next_fresh rb))))
              (temp_name (S (S (S (S (S (cr_next_fresh rb))))))))
            i
            (temp_name
              (S (S (S (S (S (S (S (cr_next_fresh rb))))))))))
          (S (S (S (S (S (S (S (S (cr_next_fresh rb)))))))))) as Hu.
      simpl. lia.
    + pose proof
        (IHbody (gamma_bind_int Gamma i) U B
          (ctx_bind_var cctx i
            (temp_name (S (cr_next_fresh rb))))
          (S (S (cr_next_fresh rb)))) as Hu.
      simpl. lia.
Qed.
