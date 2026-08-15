
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Reals.Reals.
From Stdlib Require Import Relations.Relation_Operators.
From Stdlib Require Import Lia.
From Certification2 Require Export C03_Invariants.

Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope R_scope.

(** Nom temporaire de l'accumulateur de somme. *)
Definition sumseq_acc (nf : nat) : var :=
  temp_name nf.

(** Nom temporaire de l'indice de boucle. *)
Definition sumseq_idx (nf : nat) : var :=
  temp_name (S nf).

(** Premier temporaire réservé au corps de somme. *)
Definition sumseq_body_start (nf : nat) : nat :=
  S (S nf).

(** Compile le corps dans le contexte de l'indice. *)
Definition sumseq_body_compile
  (Gamma : tyenv) (U : unary_sig_env) (B : binary_sig_env)
  (cctx : ctx) (i : var) (body : expr) (nf : nat) : compile_result :=
  compile body (gamma_bind_int Gamma i) U B
    (ctx_bind_var cctx i (sumseq_idx nf))
    (sumseq_body_start nf).


(** Temporaires nettoyés après une itération. *)
Definition sumseq_cleanup
  (Gamma : tyenv) (U : unary_sig_env) (B : binary_sig_env)
  (cctx : ctx) (i : var) (body : expr) (nf : nat) : list var :=
  temp_names_between (sumseq_body_start nf)
    (cr_next_fresh
      (sumseq_body_compile Gamma U B cctx i body nf)).

(** Test de poursuite de la boucle séquentielle. *)
Definition sumseq_test (nf : nat) (bound : var) : aexpr :=
  ALe (AVar (sumseq_idx nf)) (AVar bound).

(** Incrémentation de l'indice séquentiel. *)
Definition sumseq_step (nf : nat) : cmd :=
  CAssign (sumseq_idx nf)
    (AAdd (AVar (sumseq_idx nf)) (ANumInt 1)).

(** Commande d'une itération de somme séquentielle. *)
Definition sumseq_loop_body
  (Gamma : tyenv) (U : unary_sig_env) (B : binary_sig_env)
  (cctx : ctx) (i : var) (body : expr) (nf : nat) : cmd :=
  CSeq
    (cr_code (sumseq_body_compile Gamma U B cctx i body nf))
    (CAssign (sumseq_acc nf)
      (AAdd (AVar (sumseq_acc nf))
        (AVar
          (cr_result
            (sumseq_body_compile Gamma U B cctx i body nf))))).

(** Boucle cible complète d'une somme séquentielle. *)
Definition sumseq_loop
  (Gamma : tyenv) (U : unary_sig_env) (B : binary_sig_env)
  (cctx : ctx) (i : var) (body : expr) (nf : nat)
  (bound : var) : cmd :=
  CFor CSkip (sumseq_test nf bound) (sumseq_step nf)
    (sumseq_cleanup Gamma U B cctx i body nf)
    (sumseq_loop_body Gamma U B cctx i body nf).

(** Incrémentation de l'indice par un pas donné. *)
Definition sumstride_step (nf : nat) (stride_var : var) : cmd :=
  CAssign (sumseq_idx nf)
    (AAdd (AVar (sumseq_idx nf)) (AVar stride_var)).

(** Boucle cible d'une contribution par pas. *)
Definition sumstride_loop
  (Gamma : tyenv) (U : unary_sig_env) (B : binary_sig_env)
  (cctx : ctx) (i : var) (body : expr) (nf : nat)
  (bound stride_var : var) : cmd :=
  CFor CSkip (sumseq_test nf bound) (sumstride_step nf stride_var)
    (sumseq_cleanup Gamma U B cctx i body nf)
    (sumseq_loop_body Gamma U B cctx i body nf).

(** Une variable résultat définie n'est pas fraîche. *)
Lemma matched_result_not_fresh :
  forall sigma x v fresh n,
    compiled_result_matches x v sigma ->
    store_fresh sigma fresh ->
    (fresh <= n)%nat ->
    x <> temp_name n.
Proof.
  unfold compiled_result_matches, store_fresh.
  intros sigma x v fresh n Hmatch Hfresh Hle Heq.
  subst x. rewrite Hfresh in Hmatch; [discriminate | exact Hle].
Qed.

(** Une variable définie avant le seuil n'est pas fraîche. *)
Lemma defined_var_not_fresh :
  forall sigma x cv fresh n,
    sigma x = Some cv ->
    store_fresh sigma fresh ->
    (fresh <= n)%nat ->
    x <> temp_name n.
Proof.
  unfold store_fresh. intros sigma x cv fresh n Hdefined Hfresh Hle Heq.
  subst x. rewrite Hfresh in Hdefined; [discriminate | exact Hle].
Qed.

(** Localise un temporaire antérieur au nettoyage. *)
Lemma temp_before_cleanup :
  forall n start stop,
    (n < start)%nat ->
    ~ In (temp_name n) (temp_names_between start stop).
Proof.
  intros n start stop Hlt Hin.
  unfold temp_names_between in Hin.
  apply in_temp_names_from in Hin. lia.
Qed.

(** Évalue positivement le test avant la borne. *)
Lemma sumseq_test_true :
  forall sigma nf bound m n,
    sigma (sumseq_idx nf) = Some (CVInt m) ->
    sigma bound = Some (CVInt n) ->
    (m <= n)%Z ->
    aeval sigma (sumseq_test nf bound) = Some (CVBool true).
Proof.
  intros sigma nf bound m n Hidx Hbound Hle.
  unfold sumseq_test. simpl. rewrite Hidx, Hbound. simpl.
  f_equal. f_equal. apply Z.leb_le. exact Hle.
Qed.

(** Évalue négativement le test après la borne. *)
Lemma sumseq_test_false :
  forall sigma nf bound m n,
    sigma (sumseq_idx nf) = Some (CVInt m) ->
    sigma bound = Some (CVInt n) ->
    (n < m)%Z ->
    aeval sigma (sumseq_test nf bound) = Some (CVBool false).
Proof.
  intros sigma nf bound m n Hidx Hbound Hlt.
  unfold sumseq_test. simpl. rewrite Hidx, Hbound. simpl.
  f_equal. f_equal. apply Z.leb_gt. lia.
Qed.

(** Justifie l'incrément unitaire de l'indice. *)
Lemma sumseq_step_correct :
  forall sigma nf m,
    sigma (sumseq_idx nf) = Some (CVInt m) ->
    aeval sigma
      (AAdd (AVar (sumseq_idx nf)) (ANumInt 1)) =
    Some (CVInt (m + 1)).
Proof.
  intros sigma nf m Hidx. simpl. now rewrite Hidx.
Qed.

(** Justifie l'incrément de l'indice par un pas. *)
Lemma sumstride_step_correct :
  forall sigma nf stride_var current stride,
    sigma (sumseq_idx nf) = Some (CVInt current) ->
    sigma stride_var = Some (CVInt stride) ->
    aeval sigma
      (AAdd (AVar (sumseq_idx nf)) (AVar stride_var)) =
    Some (CVInt (current + stride)).
Proof.
  intros sigma nf stride_var current stride Hidx Hstride.
  simpl. now rewrite Hidx, Hstride.
Qed.

(** Justifie une accumulation et son nettoyage. *)
Lemma sumseq_accumulate_correct :
  forall sigma nf body_result prefix current,
    sigma (sumseq_acc nf) =
      Some (cvalue_of_value prefix) ->
    sigma body_result =
      Some (cvalue_of_value current) ->
    aeval sigma
      (AAdd (AVar (sumseq_acc nf)) (AVar body_result)) =
    Some (cvalue_of_value (add_values prefix current)).
Proof.
  intros sigma nf body_result prefix current Hacc Hbody.
  simpl. rewrite Hacc, Hbody. apply add_cvalues_correct.
Qed.

(** Prouve la correction de la boucle séquentielle. *)
Lemma sumseq_loop_sound :
  forall Gamma U B cctx rho i body tbody,
    has_type (gamma_bind_int Gamma i) U B body tbody ->
    (forall rho' sigma' cctx' fresh' v,
      eval_expr (gamma_bind_int Gamma i) U B rho' body tbody v ->
      store_represents (ctx_repr cctx') rho' sigma' ->
      store_fresh sigma' fresh' ->
      primitive_semantics_compatible U B ->
      local_simulation (ctx_repr cctx') rho' sigma'
        (compile body (gamma_bind_int Gamma i) U B
          cctx' fresh') v) ->
    forall m n total,
      eval_sum Gamma U B rho i m n body tbody total ->
    forall base sigma fresh0 nf bound prefix k,
      (fresh0 <= nf)%nat ->
      store_fresh base fresh0 ->
      store_represents (ctx_repr cctx) rho base ->
      preserves_store base sigma ->
      store_fresh sigma (sumseq_body_start nf) ->
      sigma (sumseq_acc nf) =
        Some (cvalue_of_value prefix) ->
      sigma (sumseq_idx nf) = Some (CVInt m) ->
      sigma bound = Some (CVInt n) ->
      bound <> sumseq_acc nf ->
      bound <> sumseq_idx nf ->
      value_has_type prefix tbody ->
      primitive_semantics_compatible U B ->
      exists sigma',
        executes sigma
          (sumseq_loop Gamma U B cctx i body nf bound) k sigma' /\
        sigma' (sumseq_acc nf) =
          Some (cvalue_of_value (add_values prefix total)) /\
        sigma' bound = Some (CVInt n) /\
        store_fresh sigma'
          (cr_next_fresh
            (sumseq_body_compile Gamma U B cctx i body nf)) /\
        preserves_store base sigma'.
Proof.
  intros Gamma U B cctx rho i body tbody Hbodytype Hbody_sound
    m n total Hsum.
  induction Hsum as
      [Gamma0 U0 B0 rho0 i0 m0 n0 body0 tbody0 Hempty
      | Gamma0 U0 B0 rho0 i0 m0 n0 body0 tbody0 v1 vrest
        Hle Hbodyeval Hrest IHrest];
    intros base sigma fresh0 nf bound prefix k
      Hfreshle Hbasefresh Hbaserep Hbasepres Hfresh
      Hacc Hidx Hbound Hboundacc Hboundidx Hprefix Hcompat.
  - exists sigma. repeat split.
    + apply executes_for_false.
      apply sumseq_test_false with (m := m0) (n := n0);
        assumption.
    + rewrite add_values_zero_right.
      * exact Hacc.
      * exact Hprefix.
    + exact Hbound.
    + eapply store_fresh_monotone.
      * exact Hfresh.
      * unfold sumseq_body_start, sumseq_body_compile.
        apply compile_fresh_monotone.
    + exact Hbasepres.
  - set (ru :=
      sumseq_body_compile Gamma0 U0 B0 cctx i0 body0 nf).
    set (cleanup :=
      sumseq_cleanup Gamma0 U0 B0 cctx i0 body0 nf).
    assert (Hcurrentrep :
      store_represents (ctx_repr cctx) rho0 sigma).
    { eapply store_represents_preserved; eauto. }
    assert (Hboundrep :
      store_represents
        (ctx_repr (ctx_bind_var cctx i0 (sumseq_idx nf)))
        (env_update rho0 i0 (VInt m0)) sigma).
    { apply store_represents_bind_int; assumption. }
    pose proof Hbody_sound as Hbody_current.
    specialize
      (Hbody_current
        (env_update rho0 i0 (VInt m0)) sigma
        (ctx_bind_var cctx i0 (sumseq_idx nf))
        (sumseq_body_start nf) v1
        Hbodyeval Hboundrep Hfresh Hcompat).
    unfold local_simulation in Hbody_current.
    specialize
      (Hbody_current
        (KCmd
          (CAssign (sumseq_acc nf)
            (AAdd (AVar (sumseq_acc nf))
              (AVar (cr_result ru)))) ::
         KDel cleanup :: KCmd (sumseq_step nf) ::
         KCmd
           (sumseq_loop Gamma0 U0 B0 cctx i0 body0 nf bound) :: k)).
    destruct Hbody_current as
      [sigma_body
        [Hexec_body
          [Hmatch_body
            [Hrep_body
              [Hfresh_body Hpres_body]]]]].
    assert (Hacc_body :
      sigma_body (sumseq_acc nf) =
        Some (cvalue_of_value prefix)).
    { eapply Hpres_body. exact Hacc. }
    assert (Hidx_body :
      sigma_body (sumseq_idx nf) = Some (CVInt m0)).
    { eapply Hpres_body. exact Hidx. }
    assert (Hbound_body :
      sigma_body bound = Some (CVInt n0)).
    { eapply Hpres_body. exact Hbound. }
    set (sigma_acc :=
      store_update sigma_body (sumseq_acc nf)
        (cvalue_of_value (add_values prefix v1))).
    assert (Hexec_acc :
      executes sigma_body
        (CAssign (sumseq_acc nf)
          (AAdd (AVar (sumseq_acc nf))
            (AVar (cr_result ru))))
        (KDel cleanup :: KCmd (sumseq_step nf) ::
         KCmd
           (sumseq_loop Gamma0 U0 B0 cctx i0 body0 nf bound) :: k)
        sigma_acc).
    { apply executes_assign.
      apply sumseq_accumulate_correct with
        (prefix := prefix) (current := v1).
      - exact Hacc_body.
      - exact Hmatch_body. }
    assert (Hexec_loop_body :
      executes sigma
        (sumseq_loop_body Gamma0 U0 B0 cctx i0 body0 nf)
        (KDel cleanup :: KCmd (sumseq_step nf) ::
         KCmd
           (sumseq_loop Gamma0 U0 B0 cctx i0 body0 nf bound) :: k)
        sigma_acc).
    { unfold sumseq_loop_body. fold ru. eapply executes_seq.
      - exact Hexec_body.
      - exact Hexec_acc. }
    assert (Hnext :
      (sumseq_body_start nf <= cr_next_fresh ru)%nat).
    { subst ru. unfold sumseq_body_compile.
      apply compile_fresh_monotone. }
    assert (Hacc_not_cleanup :
      ~ In (sumseq_acc nf) cleanup).
    { subst cleanup. apply temp_before_cleanup.
      unfold sumseq_acc, sumseq_body_start. lia. }
    assert (Hidx_not_cleanup :
      ~ In (sumseq_idx nf) cleanup).
    { subst cleanup. apply temp_before_cleanup.
      unfold sumseq_idx, sumseq_body_start. lia. }
    assert (Hbound_not_cleanup : ~ In bound cleanup).
    { intros Hin.
      subst cleanup.
      apply in_temp_names_between_exists in Hin
        as [j [Hboundname [Hstart _]]]; [| exact Hnext].
      rewrite Hboundname in Hbound.
      rewrite Hfresh in Hbound; [discriminate | exact Hstart]. }
    assert (Haccidx : sumseq_acc nf <> sumseq_idx nf).
    { unfold sumseq_acc, sumseq_idx. intros Heq.
      apply temp_name_injective in Heq. lia. }
    assert (Hfresh_acc_next :
      store_fresh sigma_acc (cr_next_fresh ru)).
    { subst sigma_acc.
      apply store_fresh_update_below.
      - exact Hfresh_body.
      - unfold sumseq_acc, sumseq_body_start in *.
        lia. }
    set (sigma_clean := store_remove sigma_acc cleanup).
    assert (Hdel :
      local_steps
        {| ls_store := sigma_acc;
           ls_kont :=
             KDel cleanup :: KCmd (sumseq_step nf) ::
             KCmd
               (sumseq_loop Gamma0 U0 B0 cctx i0 body0 nf bound) :: k |}
        {| ls_store := sigma_clean;
           ls_kont :=
             KCmd (sumseq_step nf) ::
             KCmd
               (sumseq_loop Gamma0 U0 B0 cctx i0 body0 nf bound) :: k |}).
    { subst sigma_clean. apply executes_del. }
    assert (Hacc_clean :
      sigma_clean (sumseq_acc nf) =
        Some (cvalue_of_value (add_values prefix v1))).
    { subst sigma_clean sigma_acc.
      rewrite store_remove_not_in; [| exact Hacc_not_cleanup].
      apply store_update_same. }
    assert (Hidx_clean :
      sigma_clean (sumseq_idx nf) = Some (CVInt m0)).
    { subst sigma_clean sigma_acc.
      rewrite store_remove_not_in; [| exact Hidx_not_cleanup].
      rewrite store_update_other; [exact Hidx_body |].
      now symmetry. }
    assert (Hbound_clean :
      sigma_clean bound = Some (CVInt n0)).
    { subst sigma_clean sigma_acc.
      rewrite store_remove_not_in; [| exact Hbound_not_cleanup].
      rewrite store_update_other; [exact Hbound_body |].
      exact Hboundacc. }
    assert (Hfresh_clean :
      store_fresh sigma_clean (sumseq_body_start nf)).
    { subst sigma_clean cleanup.
      apply store_fresh_after_cleanup; assumption. }
    assert (Hbasepres_acc : preserves_store base sigma_acc).
    { subst sigma_acc.
      apply preserves_store_update_from_base.
      - eapply store_fresh_monotone; [exact Hbasefresh |].
        exact Hfreshle.
      - eapply preserves_store_trans; eauto. }
    assert (Hbasepres_clean : preserves_store base sigma_clean).
    { subst sigma_clean cleanup.
      apply preserves_store_remove_fresh_range.
      - exact Hnext.
      - eapply store_fresh_monotone; [exact Hbasefresh |].
        unfold sumseq_body_start. lia.
      - exact Hbasepres_acc. }
    set (sigma_step :=
      store_update sigma_clean (sumseq_idx nf) (CVInt (m0 + 1))).
    assert (Hexec_step :
      executes sigma_clean (sumseq_step nf)
        (KCmd
          (sumseq_loop Gamma0 U0 B0 cctx i0 body0 nf bound) :: k)
        sigma_step).
    { unfold sumseq_step. apply executes_assign.
      apply sumseq_step_correct. exact Hidx_clean. }
    assert (Hfresh_step :
      store_fresh sigma_step (sumseq_body_start nf)).
    { subst sigma_step. apply store_fresh_update_below.
      - exact Hfresh_clean.
      - unfold sumseq_idx, sumseq_body_start. lia. }
    assert (Hbasepres_step : preserves_store base sigma_step).
    { subst sigma_step. apply preserves_store_update_from_base.
      - eapply store_fresh_monotone; [exact Hbasefresh |].
        lia.
      - exact Hbasepres_clean. }
    assert (Hacc_step :
      sigma_step (sumseq_acc nf) =
        Some (cvalue_of_value (add_values prefix v1))).
    { subst sigma_step. rewrite store_update_other.
      - exact Hacc_clean.
      - exact Haccidx. }
    assert (Hidx_step :
      sigma_step (sumseq_idx nf) = Some (CVInt (m0 + 1))).
    { subst sigma_step. apply store_update_same. }
    assert (Hbound_step :
      sigma_step bound = Some (CVInt n0)).
    { subst sigma_step. rewrite store_update_other.
      - exact Hbound_clean.
      - exact Hboundidx. }
    assert (Hv1type : value_has_type v1 tbody0).
    { eapply eval_expr_value_has_type. exact Hbodyeval. }
    assert (Hvresttype : value_has_type vrest tbody0).
    { eapply eval_sum_value_has_type. exact Hrest. }
    specialize
      (IHrest Hbodytype Hbody_sound
        base sigma_step fresh0 nf bound
        (add_values prefix v1) k
        Hfreshle Hbasefresh Hbaserep Hbasepres_step Hfresh_step
        Hacc_step Hidx_step Hbound_step
        Hboundacc Hboundidx
        (add_values_has_type tbody0 prefix v1 Hprefix Hv1type)
        Hcompat).
    destruct IHrest as
      [sigma_final
        [Hexec_rest
          [Hacc_final
            [Hbound_final [Hfresh_final Hbasepres_final]]]]].
    exists sigma_final. repeat split.
    + unfold sumseq_loop.
      eapply executes_for_iteration
        with (sigma1 := sigma_acc)
             (sigma2 := sigma_clean)
             (sigma3 := sigma_step).
      * apply sumseq_test_true with (m := m0) (n := n0);
          assumption.
      * exact Hexec_loop_body.
      * exact Hdel.
      * exact Hexec_step.
      * exact Hexec_rest.
    + rewrite <- (add_values_assoc tbody0 prefix v1 vrest);
        try assumption.
    + exact Hbound_final.
    + exact Hfresh_final.
    + exact Hbasepres_final.
Qed.

(** Prouve la correction d'une boucle par pas. *)
Lemma sumstride_loop_sound :
  forall Gamma U B cctx rho i body tbody,
    has_type (gamma_bind_int Gamma i) U B body tbody ->
    (forall rho' sigma' cctx' fresh' v,
      eval_expr (gamma_bind_int Gamma i) U B rho' body tbody v ->
      store_represents (ctx_repr cctx') rho' sigma' ->
      store_fresh sigma' fresh' ->
      primitive_semantics_compatible U B ->
      local_simulation (ctx_repr cctx') rho' sigma'
        (compile body (gamma_bind_int Gamma i) U B
          cctx' fresh') v) ->
    forall stride m n total,
      eval_stride_sum Gamma U B rho i body tbody stride
        m n total ->
    forall base sigma fresh0 nf bound stride_var prefix k,
      (fresh0 <= nf)%nat ->
      store_fresh base fresh0 ->
      store_represents (ctx_repr cctx) rho base ->
      preserves_store base sigma ->
      store_fresh sigma (sumseq_body_start nf) ->
      sigma (sumseq_acc nf) =
        Some (cvalue_of_value prefix) ->
      sigma (sumseq_idx nf) = Some (CVInt m) ->
      sigma bound = Some (CVInt n) ->
      sigma stride_var = Some (CVInt stride) ->
      bound <> sumseq_acc nf ->
      bound <> sumseq_idx nf ->
      stride_var <> sumseq_acc nf ->
      stride_var <> sumseq_idx nf ->
      value_has_type prefix tbody ->
      primitive_semantics_compatible U B ->
      exists sigma',
        executes sigma
          (sumstride_loop Gamma U B cctx i body nf
            bound stride_var) k sigma' /\
        sigma' (sumseq_acc nf) =
          Some (cvalue_of_value (add_values prefix total)) /\
        sigma' bound = Some (CVInt n) /\
        sigma' stride_var = Some (CVInt stride) /\
        store_fresh sigma'
          (cr_next_fresh
            (sumseq_body_compile Gamma U B cctx i body nf)) /\
        preserves_store base sigma'.
Proof.
  intros Gamma U B cctx rho i body tbody Hbodytype Hbody_sound
    stride m n total Hsum.
  induction Hsum as
      [current upper Hempty
      | current upper current_value rest
        Hle Hbodyeval Hrest IHrest];
    intros base sigma fresh0 nf bound stride_var prefix k
      Hfreshle Hbasefresh Hbaserep Hbasepres Hfresh
      Hacc Hidx Hbound Hstride
      Hboundacc Hboundidx Hstrideacc Hstrideidx
      Hprefix Hcompat.
  - exists sigma. repeat split.
    + apply executes_for_false.
      apply sumseq_test_false with (m := current) (n := upper);
        assumption.
    + rewrite add_values_zero_right; assumption.
    + exact Hbound.
    + exact Hstride.
    + eapply store_fresh_monotone.
      * exact Hfresh.
      * unfold sumseq_body_start, sumseq_body_compile.
        apply compile_fresh_monotone.
    + exact Hbasepres.
  - set (ru :=
      sumseq_body_compile Gamma U B cctx i body nf).
    set (cleanup :=
      sumseq_cleanup Gamma U B cctx i body nf).
    assert (Hcurrentrep :
      store_represents (ctx_repr cctx) rho sigma).
    { eapply store_represents_preserved; eauto. }
    assert (Hboundrep :
      store_represents
        (ctx_repr (ctx_bind_var cctx i (sumseq_idx nf)))
        (env_update rho i (VInt current)) sigma).
    { apply store_represents_bind_int; assumption. }
    pose proof Hbody_sound as Hbody_current.
    specialize
      (Hbody_current
        (env_update rho i (VInt current)) sigma
        (ctx_bind_var cctx i (sumseq_idx nf))
        (sumseq_body_start nf) current_value
        Hbodyeval Hboundrep Hfresh Hcompat).
    unfold local_simulation in Hbody_current.
    specialize
      (Hbody_current
        (KCmd
          (CAssign (sumseq_acc nf)
            (AAdd (AVar (sumseq_acc nf))
              (AVar (cr_result ru)))) ::
         KDel cleanup :: KCmd (sumstride_step nf stride_var) ::
         KCmd
           (sumstride_loop Gamma U B cctx i body nf
             bound stride_var) :: k)).
    destruct Hbody_current as
      [sigma_body
        [Hexec_body
          [Hmatch_body
            [Hrep_body
              [Hfresh_body Hpres_body]]]]].
    assert (Hacc_body :
      sigma_body (sumseq_acc nf) =
        Some (cvalue_of_value prefix)).
    { eapply Hpres_body. exact Hacc. }
    assert (Hidx_body :
      sigma_body (sumseq_idx nf) = Some (CVInt current)).
    { eapply Hpres_body. exact Hidx. }
    assert (Hbound_body :
      sigma_body bound = Some (CVInt upper)).
    { eapply Hpres_body. exact Hbound. }
    assert (Hstride_body :
      sigma_body stride_var = Some (CVInt stride)).
    { eapply Hpres_body. exact Hstride. }
    set (sigma_acc :=
      store_update sigma_body (sumseq_acc nf)
        (cvalue_of_value (add_values prefix current_value))).
    assert (Hexec_acc :
      executes sigma_body
        (CAssign (sumseq_acc nf)
          (AAdd (AVar (sumseq_acc nf))
            (AVar (cr_result ru))))
        (KDel cleanup :: KCmd (sumstride_step nf stride_var) ::
         KCmd
           (sumstride_loop Gamma U B cctx i body nf
             bound stride_var) :: k)
        sigma_acc).
    { apply executes_assign.
      apply sumseq_accumulate_correct with
        (prefix := prefix) (current := current_value).
      - exact Hacc_body.
      - exact Hmatch_body. }
    assert (Hexec_loop_body :
      executes sigma
        (sumseq_loop_body Gamma U B cctx i body nf)
        (KDel cleanup :: KCmd (sumstride_step nf stride_var) ::
         KCmd
           (sumstride_loop Gamma U B cctx i body nf
             bound stride_var) :: k)
        sigma_acc).
    { unfold sumseq_loop_body. fold ru. eapply executes_seq.
      - exact Hexec_body.
      - exact Hexec_acc. }
    assert (Hnext :
      (sumseq_body_start nf <= cr_next_fresh ru)%nat).
    { subst ru. unfold sumseq_body_compile.
      apply compile_fresh_monotone. }
    assert (Hacc_not_cleanup :
      ~ In (sumseq_acc nf) cleanup).
    { subst cleanup. apply temp_before_cleanup.
      unfold sumseq_acc, sumseq_body_start. lia. }
    assert (Hidx_not_cleanup :
      ~ In (sumseq_idx nf) cleanup).
    { subst cleanup. apply temp_before_cleanup.
      unfold sumseq_idx, sumseq_body_start. lia. }
    assert (Hbound_not_cleanup : ~ In bound cleanup).
    { intros Hin. subst cleanup.
      apply in_temp_names_between_exists in Hin
        as [j [Hname [Hstart _]]]; [| exact Hnext].
      rewrite Hname in Hbound.
      rewrite Hfresh in Hbound; [discriminate | exact Hstart]. }
    assert (Hstride_not_cleanup : ~ In stride_var cleanup).
    { intros Hin. subst cleanup.
      apply in_temp_names_between_exists in Hin
        as [j [Hname [Hstart _]]]; [| exact Hnext].
      rewrite Hname in Hstride.
      rewrite Hfresh in Hstride; [discriminate | exact Hstart]. }
    assert (Haccidx : sumseq_acc nf <> sumseq_idx nf).
    { unfold sumseq_acc, sumseq_idx. intros Heq.
      apply temp_name_injective in Heq. lia. }
    assert (Hfresh_acc_next :
      store_fresh sigma_acc (cr_next_fresh ru)).
    { subst sigma_acc.
      apply store_fresh_update_below.
      - exact Hfresh_body.
      - unfold sumseq_acc, sumseq_body_start in *; lia. }
    set (sigma_clean := store_remove sigma_acc cleanup).
    assert (Hdel :
      local_steps
        {| ls_store := sigma_acc;
           ls_kont :=
             KDel cleanup :: KCmd (sumstride_step nf stride_var) ::
             KCmd
               (sumstride_loop Gamma U B cctx i body nf
                 bound stride_var) :: k |}
        {| ls_store := sigma_clean;
           ls_kont :=
             KCmd (sumstride_step nf stride_var) ::
             KCmd
               (sumstride_loop Gamma U B cctx i body nf
                 bound stride_var) :: k |}).
    { subst sigma_clean. apply executes_del. }
    assert (Hacc_clean :
      sigma_clean (sumseq_acc nf) =
        Some (cvalue_of_value (add_values prefix current_value))).
    { subst sigma_clean sigma_acc.
      rewrite store_remove_not_in; [| exact Hacc_not_cleanup].
      apply store_update_same. }
    assert (Hidx_clean :
      sigma_clean (sumseq_idx nf) = Some (CVInt current)).
    { subst sigma_clean sigma_acc.
      rewrite store_remove_not_in; [| exact Hidx_not_cleanup].
      rewrite store_update_other; [exact Hidx_body |].
      now symmetry. }
    assert (Hbound_clean :
      sigma_clean bound = Some (CVInt upper)).
    { subst sigma_clean sigma_acc.
      rewrite store_remove_not_in; [| exact Hbound_not_cleanup].
      rewrite store_update_other; [exact Hbound_body |].
      exact Hboundacc. }
    assert (Hstride_clean :
      sigma_clean stride_var = Some (CVInt stride)).
    { subst sigma_clean sigma_acc.
      rewrite store_remove_not_in; [| exact Hstride_not_cleanup].
      rewrite store_update_other; [exact Hstride_body |].
      exact Hstrideacc. }
    assert (Hfresh_clean :
      store_fresh sigma_clean (sumseq_body_start nf)).
    { subst sigma_clean cleanup.
      apply store_fresh_after_cleanup; assumption. }
    assert (Hbasepres_acc : preserves_store base sigma_acc).
    { subst sigma_acc.
      apply preserves_store_update_from_base.
      - eapply store_fresh_monotone; [exact Hbasefresh |].
        exact Hfreshle.
      - eapply preserves_store_trans; eauto. }
    assert (Hbasepres_clean : preserves_store base sigma_clean).
    { subst sigma_clean cleanup.
      apply preserves_store_remove_fresh_range.
      - exact Hnext.
      - eapply store_fresh_monotone; [exact Hbasefresh |].
        unfold sumseq_body_start. lia.
      - exact Hbasepres_acc. }
    set (sigma_step :=
      store_update sigma_clean (sumseq_idx nf)
        (CVInt (current + stride))).
    assert (Hexec_step :
      executes sigma_clean (sumstride_step nf stride_var)
        (KCmd
          (sumstride_loop Gamma U B cctx i body nf
            bound stride_var) :: k)
        sigma_step).
    { unfold sumstride_step. apply executes_assign.
      apply sumstride_step_correct; assumption. }
    assert (Hfresh_step :
      store_fresh sigma_step (sumseq_body_start nf)).
    { subst sigma_step. apply store_fresh_update_below.
      - exact Hfresh_clean.
      - unfold sumseq_idx, sumseq_body_start. lia. }
    assert (Hbasepres_step : preserves_store base sigma_step).
    { subst sigma_step. apply preserves_store_update_from_base.
      - eapply store_fresh_monotone; [exact Hbasefresh | lia].
      - exact Hbasepres_clean. }
    assert (Hacc_step :
      sigma_step (sumseq_acc nf) =
        Some (cvalue_of_value (add_values prefix current_value))).
    { subst sigma_step. rewrite store_update_other.
      - exact Hacc_clean.
      - exact Haccidx. }
    assert (Hidx_step :
      sigma_step (sumseq_idx nf) =
        Some (CVInt (current + stride))).
    { subst sigma_step. apply store_update_same. }
    assert (Hbound_step :
      sigma_step bound = Some (CVInt upper)).
    { subst sigma_step. rewrite store_update_other.
      - exact Hbound_clean.
      - exact Hboundidx. }
    assert (Hstride_step :
      sigma_step stride_var = Some (CVInt stride)).
    { subst sigma_step. rewrite store_update_other.
      - exact Hstride_clean.
      - exact Hstrideidx. }
    assert (Hcurrent_type : value_has_type current_value tbody).
    { exact
        (eval_expr_value_has_type _ _ _ _ _ _ _ Hbodyeval). }
    assert (Hrest_type : value_has_type rest tbody).
    { exact
        (eval_stride_sum_value_has_type
          _ _ _ _ _ _ _ _ _ _ _ Hrest). }
    specialize
      (IHrest base sigma_step fresh0 nf bound stride_var
        (add_values prefix current_value) k
        Hfreshle Hbasefresh Hbaserep Hbasepres_step Hfresh_step
        Hacc_step Hidx_step Hbound_step Hstride_step
        Hboundacc Hboundidx Hstrideacc Hstrideidx
        (add_values_has_type tbody prefix current_value
          Hprefix Hcurrent_type)
        Hcompat).
    destruct IHrest as
      [sigma_final
        [Hexec_rest
          [Hacc_final
            [Hbound_final
              [Hstride_final
                [Hfresh_final Hbasepres_final]]]]]].
    exists sigma_final. repeat split.
    + unfold sumstride_loop.
      eapply executes_for_iteration
        with (sigma1 := sigma_acc)
             (sigma2 := sigma_clean)
             (sigma3 := sigma_step).
      * apply sumseq_test_true with
          (m := current) (n := upper); assumption.
      * exact Hexec_loop_body.
      * exact Hdel.
      * exact Hexec_step.
      * exact Hexec_rest.
    + rewrite <-
        (add_values_assoc tbody prefix current_value rest);
        try assumption.
    + exact Hbound_final.
    + exact Hstride_final.
    + exact Hfresh_final.
    + exact Hbasepres_final.
Qed.
