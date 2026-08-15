
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Reals.Reals.
From Stdlib Require Import Relations.Relation_Operators.
From Stdlib Require Import Lia.
From Certification2 Require Export C04_SequentialSum.

Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope R_scope.

(** Construit la branche locale d'un SumPar simple. *)
Definition sumpar_simple_if
  (Gamma : tyenv) (U : unary_sig_env) (B : binary_sig_env)
  (cctx : ctx) (i : var) (body : expr) (nf : nat)
  (lower bound : var) : cmd :=
  CIf (ctx_active cctx) []
    (CFor
      (CAssign (sumseq_idx nf)
        (AAdd (AVar lower) (AVar (ctx_rank cctx))))
      (sumseq_test nf bound)
      (sumstride_step nf (ctx_size cctx))
      (sumseq_cleanup Gamma U B cctx i body nf)
      (sumseq_loop_body Gamma U B cctx i body nf))
    [] CSkip.

(** Amène un processus actif jusqu'au Allreduce. *)
Lemma sumpar_simple_process_to_allreduce :
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
    forall sigma nf lower bound m n rank p contribution k,
      eval_stride_sum Gamma U B rho i body tbody (Z.of_nat p)
        (m + Z.of_nat rank) n contribution ->
      store_represents (ctx_repr cctx) rho sigma ->
      store_fresh sigma nf ->
      sigma lower = Some (CVInt m) ->
      sigma bound = Some (CVInt n) ->
      sigma (ctx_rank cctx) = Some (CVInt (Z.of_nat rank)) ->
      sigma (ctx_size cctx) = Some (CVInt (Z.of_nat p)) ->
      aeval sigma (ctx_active cctx) = Some (CVBool true) ->
      primitive_semantics_compatible U B ->
      exists sigma',
        local_steps
          {| ls_store := sigma;
             ls_kont :=
               KCmd
                 (CSeq
                   (CAssign (sumseq_acc nf)
                     (zero_aexpr tbody))
                   (CSeq
                     (sumpar_simple_if
                       Gamma U B cctx i body nf lower bound)
                     (CSeq
                       (CAssign
                         (temp_name
                           (cr_next_fresh
                             (sumseq_body_compile
                               Gamma U B cctx i body nf)))
                         (zero_aexpr tbody))
                       (CAllreduce (sumseq_acc nf)
                         (temp_name
                           (cr_next_fresh
                             (sumseq_body_compile
                               Gamma U B cctx i body nf))))))) :: k |}
          {| ls_store := sigma';
             ls_kont :=
               KCmd
                 (CAllreduce (sumseq_acc nf)
                   (temp_name
                     (cr_next_fresh
                       (sumseq_body_compile
                         Gamma U B cctx i body nf)))) :: k |} /\
        sigma' (sumseq_acc nf) =
          Some (cvalue_of_value contribution) /\
        sigma'
          (temp_name
            (cr_next_fresh
              (sumseq_body_compile Gamma U B cctx i body nf))) =
          Some (cvalue_of_value (zero_value tbody)) /\
        store_fresh sigma'
          (S
            (cr_next_fresh
              (sumseq_body_compile Gamma U B cctx i body nf))) /\
        preserves_store sigma sigma'.
Proof.
  intros Gamma U B cctx rho i body tbody Hbodytype Hbody_sound
    sigma nf lower bound m n rank p contribution k
    Hcontribution Hrep Hfresh Hlower Hbound Hrank Hsize Hactive Hcompat.
  set (ru := sumseq_body_compile Gamma U B cctx i body nf).
  set (result := temp_name (cr_next_fresh ru)).
  set (sigma_acc :=
    store_update sigma (sumseq_acc nf)
      (cvalue_of_value (zero_value tbody))).
  assert (Hexec_acc :
    executes sigma
      (CAssign (sumseq_acc nf) (zero_aexpr tbody))
      (KCmd
        (CSeq
          (sumpar_simple_if Gamma U B cctx i body nf lower bound)
          (CSeq (CAssign result (zero_aexpr tbody))
            (CAllreduce (sumseq_acc nf) result))) :: k)
      sigma_acc).
  { apply executes_assign. apply zero_aexpr_correct. }
  assert (Hfresh_acc : store_fresh sigma_acc (S nf)).
  { subst sigma_acc.
    apply store_fresh_update with (start := nf) (written := nf);
      [exact Hfresh | lia]. }
  assert (Hpres_acc : preserves_store sigma sigma_acc).
  { subst sigma_acc. apply preserves_store_update_fresh.
    apply Hfresh. lia. }
  assert (Hlower_acc : sigma_acc lower = Some (CVInt m)).
  { subst sigma_acc. rewrite store_update_other; [exact Hlower |].
    eapply defined_var_not_fresh; eauto; lia. }
  assert (Hrank_acc :
    sigma_acc (ctx_rank cctx) = Some (CVInt (Z.of_nat rank))).
  { subst sigma_acc. rewrite store_update_other; [exact Hrank |].
    eapply defined_var_not_fresh; eauto; lia. }
  set (sigma_idx :=
    store_update sigma_acc (sumseq_idx nf)
      (CVInt (m + Z.of_nat rank))).
  assert (Hexec_init :
    executes sigma_acc
      (CAssign (sumseq_idx nf)
        (AAdd (AVar lower) (AVar (ctx_rank cctx))))
      (KCmd
        (sumstride_loop Gamma U B cctx i body nf
          bound (ctx_size cctx)) ::
       KDel [] ::
       KCmd
         (CSeq (CAssign result (zero_aexpr tbody))
           (CAllreduce (sumseq_acc nf) result)) :: k)
      sigma_idx).
  { apply executes_assign. simpl. now rewrite Hlower_acc, Hrank_acc. }
  assert (Hfresh_idx :
    store_fresh sigma_idx (sumseq_body_start nf)).
  { subst sigma_idx. unfold sumseq_body_start.
    apply store_fresh_update
      with (start := S nf) (written := S nf);
      [exact Hfresh_acc | lia]. }
  assert (Hpres_idx : preserves_store sigma sigma_idx).
  { subst sigma_idx. eapply preserves_store_trans; [exact Hpres_acc |].
    apply preserves_store_update_fresh. apply Hfresh_acc. lia. }
  assert (Hacc_idx :
    sigma_idx (sumseq_acc nf) =
      Some (cvalue_of_value (zero_value tbody))).
  { subst sigma_idx sigma_acc. rewrite store_update_other.
    - apply store_update_same.
    - unfold sumseq_acc, sumseq_idx. intros Heq.
      apply temp_name_injective in Heq. lia. }
  assert (Hidx :
    sigma_idx (sumseq_idx nf) =
      Some (CVInt (m + Z.of_nat rank))).
  { subst sigma_idx. apply store_update_same. }
  assert (Hbound_idx : sigma_idx bound = Some (CVInt n)).
  { apply Hpres_idx. exact Hbound. }
  assert (Hsize_idx :
    sigma_idx (ctx_size cctx) = Some (CVInt (Z.of_nat p))).
  { apply Hpres_idx. exact Hsize. }
  assert (Hboundacc : bound <> sumseq_acc nf).
  { unfold sumseq_acc.
    eapply defined_var_not_fresh
      with (sigma := sigma) (cv := CVInt n) (fresh := nf);
      eauto; lia. }
  assert (Hboundidx : bound <> sumseq_idx nf).
  { unfold sumseq_idx.
    eapply defined_var_not_fresh
      with (sigma := sigma) (cv := CVInt n) (fresh := nf);
      eauto; lia. }
  assert (Hsizeacc : ctx_size cctx <> sumseq_acc nf).
  { unfold sumseq_acc.
    eapply defined_var_not_fresh
      with (sigma := sigma) (cv := CVInt (Z.of_nat p)) (fresh := nf);
      eauto; lia. }
  assert (Hsizeidx : ctx_size cctx <> sumseq_idx nf).
  { unfold sumseq_idx.
    eapply defined_var_not_fresh
      with (sigma := sigma) (cv := CVInt (Z.of_nat p)) (fresh := nf);
      eauto; lia. }
  pose proof
    (sumstride_loop_sound Gamma U B cctx rho i body tbody
      Hbodytype Hbody_sound
      (Z.of_nat p) (m + Z.of_nat rank) n contribution
      Hcontribution
      sigma sigma_idx nf nf bound (ctx_size cctx)
      (zero_value tbody)
      (KDel [] ::
       KCmd
         (CSeq (CAssign result (zero_aexpr tbody))
           (CAllreduce (sumseq_acc nf) result)) :: k)
      (Nat.le_refl nf) Hfresh Hrep Hpres_idx Hfresh_idx
      Hacc_idx Hidx Hbound_idx Hsize_idx
      Hboundacc Hboundidx Hsizeacc Hsizeidx
      (zero_value_has_type tbody) Hcompat) as Hloop.
  destruct Hloop as
    [sigma_loop
      [Hexec_loop
        [Hacc_loop
          [Hbound_loop
            [Hsize_loop [Hfresh_loop Hpres_loop]]]]]].
  assert (Hexec_for :
    executes sigma_acc
      (CFor
        (CAssign (sumseq_idx nf)
          (AAdd (AVar lower) (AVar (ctx_rank cctx))))
        (sumseq_test nf bound)
        (sumstride_step nf (ctx_size cctx))
        (sumseq_cleanup Gamma U B cctx i body nf)
        (sumseq_loop_body Gamma U B cctx i body nf))
      (KDel [] ::
       KCmd
         (CSeq (CAssign result (zero_aexpr tbody))
           (CAllreduce (sumseq_acc nf) result)) :: k)
      sigma_loop).
  { unfold executes in *.
    eapply local_steps_trans.
    - apply executes_for_init.
      + discriminate.
      + exact Hexec_init.
    - exact Hexec_loop. }
  assert (Hactive_acc :
    aeval sigma_acc (ctx_active cctx) = Some (CVBool true)).
  { apply aeval_preserved with (sigma := sigma).
    - exact Hpres_acc.
    - exact Hactive. }
  assert (Hexec_if :
    executes sigma_acc
      (sumpar_simple_if Gamma U B cctx i body nf lower bound)
      (KCmd
        (CSeq (CAssign result (zero_aexpr tbody))
          (CAllreduce (sumseq_acc nf) result)) :: k)
      sigma_loop).
  { unfold sumpar_simple_if.
    replace sigma_loop with (store_remove sigma_loop []) by reflexivity.
    apply executes_if_true; assumption. }
  set (sigma_result :=
    store_update sigma_loop result
      (cvalue_of_value (zero_value tbody))).
  assert (Hexec_result :
    executes sigma_loop (CAssign result (zero_aexpr tbody))
      (KCmd (CAllreduce (sumseq_acc nf) result) :: k)
      sigma_result).
  { apply executes_assign. apply zero_aexpr_correct. }
  assert (Hru_start :
    (sumseq_body_start nf <= cr_next_fresh ru)%nat).
  { subst ru. unfold sumseq_body_compile. apply compile_fresh_monotone. }
  assert (Hacc_result :
    sigma_result (sumseq_acc nf) =
      Some (cvalue_of_value contribution)).
  { subst sigma_result result.
    rewrite store_update_other.
    - rewrite add_values_zero_left in Hacc_loop.
      + exact Hacc_loop.
      + apply
          (eval_stride_sum_value_has_type
            Gamma U B rho i body tbody (Z.of_nat p)
            (m + Z.of_nat rank) n contribution).
        exact Hcontribution.
    - unfold sumseq_acc. intros Heq.
      fold ru in Heq.
      apply temp_name_injective in Heq.
      unfold sumseq_body_start in Hru_start. lia. }
  exists sigma_result. repeat split.
  - subst ru result.
    eapply local_steps_seq_prefix3; eauto.
  - exact Hacc_result.
  - subst sigma_result. apply store_update_same.
  - subst sigma_result result.
    apply store_fresh_update
      with (start := cr_next_fresh ru)
           (written := cr_next_fresh ru);
      [exact Hfresh_loop | lia].
  - subst sigma_result result.
    apply preserves_store_update_from_base.
    + apply store_fresh_monotone with (n := nf).
      * exact Hfresh.
      * unfold sumseq_body_start in Hru_start. lia.
    + exact Hpres_loop.
Qed.

(** Amène un processus inactif jusqu'au Allreduce. *)
Lemma sumpar_simple_inactive_to_allreduce :
  forall Gamma U B cctx i body tbody sigma nf lower bound k,
    has_type (gamma_bind_int Gamma i) U B body tbody ->
    store_fresh sigma nf ->
    aeval sigma (ctx_active cctx) = Some (CVBool false) ->
    exists sigma',
      local_steps
        {| ls_store := sigma;
           ls_kont :=
             KCmd
               (CSeq
                 (CAssign (sumseq_acc nf) (zero_aexpr tbody))
                 (CSeq
                   (sumpar_simple_if
                     Gamma U B cctx i body nf lower bound)
                   (CSeq
                     (CAssign
                       (temp_name
                         (cr_next_fresh
                           (sumseq_body_compile
                             Gamma U B cctx i body nf)))
                       (zero_aexpr tbody))
                     (CAllreduce (sumseq_acc nf)
                       (temp_name
                         (cr_next_fresh
                           (sumseq_body_compile
                             Gamma U B cctx i body nf))))))) :: k |}
        {| ls_store := sigma';
           ls_kont :=
             KCmd
               (CAllreduce (sumseq_acc nf)
                 (temp_name
                   (cr_next_fresh
                     (sumseq_body_compile
                       Gamma U B cctx i body nf)))) :: k |} /\
      sigma' (sumseq_acc nf) =
        Some (cvalue_of_value (zero_value tbody)) /\
      sigma'
        (temp_name
          (cr_next_fresh
            (sumseq_body_compile Gamma U B cctx i body nf))) =
        Some (cvalue_of_value (zero_value tbody)) /\
      store_fresh sigma'
        (S
          (cr_next_fresh
            (sumseq_body_compile Gamma U B cctx i body nf))) /\
      preserves_store sigma sigma'.
Proof.
  intros Gamma U B cctx i body tbody sigma nf lower bound k
    Hbodytype Hfresh Hactive.
  set (ru := sumseq_body_compile Gamma U B cctx i body nf).
  set (result := temp_name (cr_next_fresh ru)).
  set (sigma_acc :=
    store_update sigma (sumseq_acc nf)
      (cvalue_of_value (zero_value tbody))).
  assert (Hexec_acc :
    executes sigma
      (CAssign (sumseq_acc nf) (zero_aexpr tbody))
      (KCmd
        (CSeq
          (sumpar_simple_if Gamma U B cctx i body nf lower bound)
          (CSeq (CAssign result (zero_aexpr tbody))
            (CAllreduce (sumseq_acc nf) result))) :: k)
      sigma_acc).
  { apply executes_assign. apply zero_aexpr_correct. }
  assert (Hpres_acc : preserves_store sigma sigma_acc).
  { subst sigma_acc. apply preserves_store_update_fresh.
    apply Hfresh. lia. }
  assert (Hactive_acc :
    aeval sigma_acc (ctx_active cctx) = Some (CVBool false)).
  { eapply aeval_preserved; eauto. }
  assert (Hexec_if :
    executes sigma_acc
      (sumpar_simple_if Gamma U B cctx i body nf lower bound)
      (KCmd
        (CSeq (CAssign result (zero_aexpr tbody))
          (CAllreduce (sumseq_acc nf) result)) :: k)
      sigma_acc).
  { unfold sumpar_simple_if.
    replace sigma_acc with (store_remove sigma_acc []) by reflexivity.
    apply executes_if_false.
    - exact Hactive_acc.
    - apply executes_skip. }
  set (sigma_result :=
    store_update sigma_acc result
      (cvalue_of_value (zero_value tbody))).
  assert (Hexec_result :
    executes sigma_acc (CAssign result (zero_aexpr tbody))
      (KCmd (CAllreduce (sumseq_acc nf) result) :: k)
      sigma_result).
  { apply executes_assign. apply zero_aexpr_correct. }
  assert (Hnext :
    (sumseq_body_start nf <= cr_next_fresh ru)%nat).
  { subst ru. unfold sumseq_body_compile. apply compile_fresh_monotone. }
  assert (Hfresh_acc : store_fresh sigma_acc (S nf)).
  { subst sigma_acc.
    apply store_fresh_update with (start := nf) (written := nf);
      [exact Hfresh | lia]. }
  exists sigma_result. repeat split.
  - subst ru result. eapply local_steps_seq_prefix3; eauto.
  - subst sigma_result result sigma_acc.
    rewrite store_update_other.
    + apply store_update_same.
    + unfold sumseq_acc, sumseq_body_start in Hnext.
      intros Heq. apply temp_name_injective in Heq. lia.
  - subst sigma_result. apply store_update_same.
  - subst sigma_result result.
    apply store_fresh_update
      with (start := cr_next_fresh ru)
           (written := cr_next_fresh ru).
    + apply store_fresh_monotone with (n := S nf);
        [exact Hfresh_acc |].
      unfold sumseq_body_start in Hnext. lia.
    + lia.
  - subst sigma_result result.
    apply preserves_store_update_from_base.
    + apply store_fresh_monotone with (n := nf);
        [exact Hfresh |].
      unfold sumseq_body_start in Hnext. lia.
    + exact Hpres_acc.
Qed.

(** Décrit les processus prêts pour un Allreduce simple. *)
Inductive simple_sumpar_mixed_ready
  (Gamma : tyenv) (U : unary_sig_env) (B : binary_sig_env)
  (cctx : ctx) (rho : env) (i : var) (body : expr) (tbody : ty)
  (nf : nat) (lower bound : var) (m n : Z) (p : nat)
  : value -> store -> Prop :=
| SimpleSumparReadyActive :
    forall rank contribution sigma,
      eval_stride_sum Gamma U B rho i body tbody (Z.of_nat p)
        (m + Z.of_nat rank) n contribution ->
      store_represents (ctx_repr cctx) rho sigma ->
      store_fresh sigma nf ->
      sigma lower = Some (CVInt m) ->
      sigma bound = Some (CVInt n) ->
      sigma (ctx_rank cctx) = Some (CVInt (Z.of_nat rank)) ->
      sigma (ctx_size cctx) = Some (CVInt (Z.of_nat p)) ->
      aeval sigma (ctx_active cctx) = Some (CVBool true) ->
      simple_sumpar_mixed_ready
        Gamma U B cctx rho i body tbody nf lower bound m n p
        contribution sigma
| SimpleSumparReadyInactive :
    forall sigma,
      store_fresh sigma nf ->
      aeval sigma (ctx_active cctx) = Some (CVBool false) ->
      simple_sumpar_mixed_ready
        Gamma U B cctx rho i body tbody nf lower bound m n p
        (zero_value tbody) sigma.

(** Montre que la compilation conserve le type. *)
Lemma compile_type_correct :
  forall Gamma U B e t,
    has_type Gamma U B e t ->
    forall cctx fresh,
      cr_type (compile e Gamma U B cctx fresh) = t.
Proof.
  intros Gamma U B e t Htype.
  induction Htype; intros cctx fresh; cbn [compile].
  - reflexivity.
  - reflexivity.
  - now rewrite H.
  - remember (compile e Gamma U B cctx fresh) as r eqn:Hr.
    pose proof (IHHtype cctx fresh) as IH.
    rewrite <- Hr in IH. simpl.
    rewrite IH. unfold unary_result_type. now rewrite H.
  - remember (compile e1 Gamma U B cctx fresh) as r1 eqn:Hr1.
    remember
      (compile e2 Gamma U B cctx (cr_next_fresh r1))
      as r2 eqn:Hr2.
    pose proof (IHHtype1 cctx fresh) as IH1.
    pose proof
      (IHHtype2 cctx (cr_next_fresh r1)) as IH2.
    rewrite <- Hr1 in IH1. rewrite <- Hr2 in IH2.
    simpl. now rewrite IH1, IH2.
  - remember (compile a Gamma U B cctx fresh) as ra eqn:Hra.
    remember
      (compile b Gamma U B cctx (cr_next_fresh ra))
      as rb eqn:Hrb.
    pose proof (IHHtype3
      (ctx_bind_var cctx i (temp_name (S (cr_next_fresh rb))))
      (S (S (cr_next_fresh rb)))) as IH.
    simpl. exact IH.
  - remember (compile a Gamma U B cctx fresh) as ra eqn:Hra.
    remember
      (compile b Gamma U B cctx (cr_next_fresh ra))
      as rb eqn:Hrb.
    destruct (has_parallel_sum body) eqn:Hparallel; simpl.
    + apply IHHtype3.
    + apply IHHtype3.
Qed.

(** Établit l'unicité du type d'une expression. *)
Lemma has_type_unique :
  forall Gamma U B e t1 t2,
    has_type Gamma U B e t1 ->
    has_type Gamma U B e t2 ->
    t1 = t2.
Proof.
  intros Gamma U B e t1 t2 H1 H2.
  pose proof (compile_type_correct Gamma U B e t1 H1 ctx0 0%nat) as E1.
  pose proof (compile_type_correct Gamma U B e t2 H2 ctx0 0%nat) as E2.
  congruence.
Qed.

(** Relie le type d'évaluation au type statique. *)
Lemma eval_type_agrees :
  forall Gamma U B e t,
    has_type Gamma U B e t ->
    forall rho t' v,
      eval_expr Gamma U B rho e t' v ->
      t' = t.
Proof.
  intros Gamma U B e t Htype.
  induction Htype; intros rho t' v Heval; inversion Heval; subst.
  - reflexivity.
  - reflexivity.
  - congruence.
  - assert (tin0 = tin).
    { eapply IHHtype. eassumption. }
    subst tin0. congruence.
  - assert (t0 = t1).
    { eapply IHHtype1. eassumption. }
    assert (t3 = t2).
    { eapply IHHtype2. eassumption. }
    now subst.
  - eapply has_type_unique; eassumption.
  - eapply has_type_unique; eassumption.
Qed.

(** Prouve la correction locale du compilateur. *)
Theorem compiler_semantic_correctness_local :
  forall Gamma U B e t,
    has_type Gamma U B e t ->
    has_parallel_sum e = false ->
    forall cctx rho sigma fresh v,
      eval_expr Gamma U B rho e t v ->
      store_represents (ctx_repr cctx) rho sigma ->
      store_fresh sigma fresh ->
      primitive_semantics_compatible U B ->
      local_simulation (ctx_repr cctx) rho sigma
        (compile e Gamma U B cctx fresh) v.
Proof.
  intros Gamma U B e t Htype.
  induction Htype;
    intros Hparallel cctx rho sigma fresh v
      Heval Hrep Hfresh Hcompat;
    inversion Heval; subst.
  - unfold local_simulation. simpl. intros k.
    set (sigma' :=
      store_update sigma (temp_name fresh) (CVInt n)).
    assert (Hpres : preserves_store sigma sigma').
    { subst sigma'. apply preserves_store_update_fresh.
      apply Hfresh. lia. }
    exists sigma'. repeat split.
    + subst sigma'. apply executes_assign. reflexivity.
    + subst sigma'. apply store_update_same.
    + eapply store_represents_preserved; eauto.
    + subst sigma'. eapply store_fresh_update; [exact Hfresh | lia].
    + exact Hpres.
  - unfold local_simulation. simpl. intros k.
    set (sigma' :=
      store_update sigma (temp_name fresh) (CVFloat r)).
    assert (Hpres : preserves_store sigma sigma').
    { subst sigma'. apply preserves_store_update_fresh.
      apply Hfresh. lia. }
    exists sigma'. repeat split.
    + subst sigma'. apply executes_assign. reflexivity.
    + subst sigma'. apply store_update_same.
    + eapply store_represents_preserved; eauto.
    + subst sigma'. eapply store_fresh_update; [exact Hfresh | lia].
    + exact Hpres.
  - unfold local_simulation. simpl. intros k.
    exists sigma. repeat split.
    + apply executes_skip.
    + apply Hrep. assumption.
    + exact Hrep.
    + exact Hfresh.
    + apply preserves_store_refl.
  - remember (compile e Gamma U B cctx fresh) as r1 eqn:Hr1.
    simpl in Hparallel. specialize (IHHtype Hparallel).
    destruct r1 as [c1 x1 t1 n1].
    assert (tin0 = tin).
    { eapply eval_type_agrees; [exact Htype | exact H2]. }
    subst tin0.
    pose proof
      (IHHtype cctx rho sigma fresh v0
        H2 Hrep Hfresh Hcompat) as IH.
    rewrite <- Hr1 in IH. simpl in IH.
    unfold local_simulation in *. cbn [compile seq_list].
    rewrite <- Hr1. simpl. intros k.
    specialize
      (IH
        (KCmd
          (CAssign (temp_name n1)
            (AUnaryPrim op (AVar x1))) :: k)).
    destruct IH as
      [sigma1 [Hexec1 [Hmatch1 [Hrep1 [Hfresh1 Hpres1]]]]].
    set (sigma2 :=
      store_update sigma1 (temp_name n1)
        (cvalue_of_value (unary_source_sem op v0))).
    assert (Hexec2 :
      executes sigma1
        (CAssign (temp_name n1) (AUnaryPrim op (AVar x1)))
        k sigma2).
    { subst sigma2. apply executes_assign.
      eapply aeval_unary_correct; eauto. }
    assert (Hpres2 : preserves_store sigma1 sigma2).
    { subst sigma2. apply preserves_store_update_fresh.
      apply Hfresh1. apply Nat.le_refl. }
    exists sigma2. repeat split.
    + eapply executes_seq; eauto.
    + subst sigma2. apply store_update_same.
    + eapply store_represents_preserved; eauto.
    + subst sigma2.
      apply store_fresh_update with (start := n1);
        [exact Hfresh1 | apply Nat.le_refl].
    + eapply preserves_store_trans; eauto.
  - remember (compile e1 Gamma U B cctx fresh) as r1 eqn:Hr1.
    simpl in Hparallel.
    apply Bool.orb_false_iff in Hparallel as [Hparallel1 Hparallel2].
    specialize (IHHtype1 Hparallel1).
    specialize (IHHtype2 Hparallel2).
    destruct r1 as [c1 x1 ct1 n1].
    remember (compile e2 Gamma U B cctx n1) as r2 eqn:Hr2.
    destruct r2 as [c2 x2 ct2 n2].
    assert (t0 = t1).
    { eapply eval_type_agrees; [exact Htype1 | exact H5]. }
    assert (t3 = t2).
    { eapply eval_type_agrees; [exact Htype2 | exact H6]. }
    subst t0 t3.
    pose proof
      (IHHtype1 cctx rho sigma fresh v1
        H5 Hrep Hfresh Hcompat) as IH1.
    rewrite <- Hr1 in IH1. simpl in IH1.
    unfold local_simulation in *.
    cbn [compile seq_list]. rewrite <- Hr1. simpl.
    rewrite <- Hr2. simpl. intros k.
    specialize
      (IH1
        (KCmd (CSeq c2
          (CAssign (temp_name n2) (binary_aexpr op x1 x2))) :: k)).
    destruct IH1 as
      [sigma1 [Hexec1 [Hmatch1 [Hrep1 [Hfresh1 Hpres1]]]]].
    pose proof
      (IHHtype2 cctx rho sigma1 n1 v2
        H6 Hrep1 Hfresh1 Hcompat) as IH2.
    rewrite <- Hr2 in IH2. simpl in IH2.
    specialize
      (IH2
        (KCmd
          (CAssign (temp_name n2) (binary_aexpr op x1 x2)) :: k)).
    destruct IH2 as
      [sigma2 [Hexec2 [Hmatch2 [Hrep2 [Hfresh2 Hpres2]]]]].
    assert (Hmatch1' : compiled_result_matches x1 v1 sigma2).
    { eapply compiled_result_preserved; eauto. }
    set (sigma3 :=
      store_update sigma2 (temp_name n2)
        (cvalue_of_value (binary_source_value op v1 v2))).
    assert (Hexec3 :
      executes sigma2
        (CAssign (temp_name n2) (binary_aexpr op x1 x2))
        k sigma3).
    { subst sigma3. apply executes_assign.
      eapply aeval_binary_correct; eauto. }
    assert (Hpres3 : preserves_store sigma2 sigma3).
    { subst sigma3. apply preserves_store_update_fresh.
      apply Hfresh2. apply Nat.le_refl. }
    exists sigma3. repeat split.
    + eapply executes_seq.
      * exact Hexec1.
      * eapply executes_seq; eauto.
    + subst sigma3. apply store_update_same.
    + eapply store_represents_preserved; eauto.
    + subst sigma3.
      apply store_fresh_update with (start := n2);
        [exact Hfresh2 | apply Nat.le_refl].
    + eapply preserves_store_trans; [exact Hpres1 |].
      eapply preserves_store_trans; eauto.
  - remember (compile a Gamma U B cctx fresh) as ra eqn:Hra.
    simpl in Hparallel.
    apply Bool.orb_false_iff in Hparallel as
      [Hparallel_a Hparallel_rest].
    apply Bool.orb_false_iff in Hparallel_rest as
      [Hparallel_b Hparallel_body].
    specialize (IHHtype1 Hparallel_a).
    specialize (IHHtype2 Hparallel_b).
    specialize (IHHtype3 Hparallel_body).
    destruct ra as [ca xa ta na].
    remember (compile b Gamma U B cctx na) as rb eqn:Hrb.
    destruct rb as [cb xb tb nf].
    remember
      (sumseq_body_compile Gamma U B cctx i body nf)
      as ru eqn:Hru.
    destruct ru as [cu xu tu nu].
    pose proof
      (IHHtype1 cctx rho sigma fresh (VInt m)
        H4 Hrep Hfresh Hcompat) as IHa.
    rewrite <- Hra in IHa. simpl in IHa.
    unfold local_simulation in *.
    cbn [compile seq_list]. rewrite <- Hra. simpl.
    rewrite <- Hrb. simpl.
    unfold sumseq_body_compile, sumseq_idx, sumseq_body_start in Hru.
    rewrite <- Hru. simpl.
    intros k.
    set (loop :=
      sumseq_loop Gamma U B cctx i body nf xb).
    set (init_acc := CAssign (sumseq_acc nf) (zero_aexpr tu)).
    specialize
      (IHa
        (KCmd (CSeq cb (CSeq init_acc
          (CFor
            (CAssign (sumseq_idx nf) (AVar xa))
            (sumseq_test nf xb) (sumseq_step nf)
            (temp_names_between (sumseq_body_start nf) nu)
            (CSeq cu
              (CAssign (sumseq_acc nf)
                (AAdd (AVar (sumseq_acc nf)) (AVar xu))))))) :: k)).
    destruct IHa as
      [sigma_a [Hexec_a [Hmatch_a [Hrep_a [Hfresh_a Hpres_a]]]]].
    pose proof
      (IHHtype2 cctx rho sigma_a na (VInt n)
        H7 Hrep_a Hfresh_a Hcompat) as IHb.
    rewrite <- Hrb in IHb. simpl in IHb.
    specialize
      (IHb
        (KCmd (CSeq init_acc
          (CFor
            (CAssign (sumseq_idx nf) (AVar xa))
            (sumseq_test nf xb) (sumseq_step nf)
            (temp_names_between (sumseq_body_start nf) nu)
            (CSeq cu
              (CAssign (sumseq_acc nf)
                (AAdd (AVar (sumseq_acc nf)) (AVar xu)))))) :: k)).
    destruct IHb as
      [sigma_b [Hexec_b [Hmatch_b [Hrep_b [Hfresh_b Hpres_b]]]]].
    assert (Hmatch_a' :
      compiled_result_matches xa (VInt m) sigma_b).
    { eapply compiled_result_preserved; eauto. }
    assert (Htubody : tu = tbody).
    { change
        (cr_type
          {| cr_code := cu; cr_result := xu;
             cr_type := tu; cr_next_fresh := nu |} = tbody).
      rewrite Hru.
      apply compile_type_correct. exact Htype3. }
    set (sigma_acc :=
      store_update sigma_b (sumseq_acc nf)
        (cvalue_of_value (zero_value tbody))).
    assert (Hexec_acc :
      executes sigma_b init_acc
        (KCmd
          (CFor
            (CAssign (sumseq_idx nf) (AVar xa))
            (sumseq_test nf xb) (sumseq_step nf)
            (temp_names_between (sumseq_body_start nf) nu)
            (CSeq cu
              (CAssign (sumseq_acc nf)
                (AAdd (AVar (sumseq_acc nf)) (AVar xu))))) :: k)
        sigma_acc).
    { subst init_acc sigma_acc. apply executes_assign.
      rewrite Htubody. apply zero_aexpr_correct. }
    assert (Hbasepres_b : preserves_store sigma sigma_b).
    { eapply preserves_store_trans; eauto. }
    assert (Hbasepres_acc : preserves_store sigma sigma_acc).
    { subst sigma_acc. apply preserves_store_update_from_base.
      - eapply store_fresh_monotone; [exact Hfresh |].
        pose proof
          (compile_fresh_monotone a Gamma U B cctx fresh).
        pose proof
          (compile_fresh_monotone b Gamma U B cctx na).
        rewrite <- Hra in H. rewrite <- Hrb in H0. simpl in *. lia.
      - exact Hbasepres_b. }
    assert (Hfresh_acc : store_fresh sigma_acc (S nf)).
    { subst sigma_acc. eapply store_fresh_update; [exact Hfresh_b | lia]. }
    assert (Hboundacc : xb <> sumseq_acc nf).
    { unfold sumseq_acc.
      eapply matched_result_not_fresh; eauto; lia. }
    assert (Hboundidx : xb <> sumseq_idx nf).
    { unfold sumseq_idx.
      eapply matched_result_not_fresh; eauto; lia. }
    assert (Haacc : xa <> sumseq_acc nf).
    { unfold sumseq_acc.
      eapply matched_result_not_fresh; eauto; lia. }
    assert (Hmatch_a_acc :
      sigma_acc xa = Some (CVInt m)).
    { subst sigma_acc. rewrite store_update_other.
      - exact Hmatch_a'.
      - exact Haacc. }
    set (sigma_idx :=
      store_update sigma_acc (sumseq_idx nf) (CVInt m)).
    assert (Hexec_init :
      executes sigma_acc
        (CAssign (sumseq_idx nf) (AVar xa))
        (KCmd loop :: k) sigma_idx).
    { subst sigma_idx. apply executes_assign.
      simpl. exact Hmatch_a_acc. }
    assert (Hfor_init :
      local_steps
        {| ls_store := sigma_acc;
           ls_kont :=
             KCmd
               (CFor
                 (CAssign (sumseq_idx nf) (AVar xa))
                 (sumseq_test nf xb) (sumseq_step nf)
                 (temp_names_between (sumseq_body_start nf) nu)
                 (CSeq cu
                   (CAssign (sumseq_acc nf)
                     (AAdd (AVar (sumseq_acc nf)) (AVar xu))))) :: k |}
        {| ls_store := sigma_idx; ls_kont := KCmd loop :: k |}).
    { subst loop. unfold sumseq_loop, sumseq_cleanup,
        sumseq_loop_body, sumseq_body_compile,
        sumseq_idx, sumseq_acc, sumseq_body_start.
      rewrite <- Hru. simpl.
      unfold sumseq_loop, sumseq_cleanup,
        sumseq_loop_body, sumseq_body_compile,
        sumseq_idx, sumseq_acc, sumseq_body_start in Hexec_init.
      rewrite <- Hru in Hexec_init. simpl in Hexec_init.
      apply executes_for_init.
      - discriminate.
      - exact Hexec_init. }
    assert (Hfresh_idx :
      store_fresh sigma_idx (sumseq_body_start nf)).
    { subst sigma_idx. unfold sumseq_body_start.
      eapply store_fresh_update; [exact Hfresh_acc | lia]. }
    assert (Hbasepres_idx : preserves_store sigma sigma_idx).
    { subst sigma_idx. apply preserves_store_update_from_base.
      - eapply store_fresh_monotone; [exact Hfresh |].
        pose proof
          (compile_fresh_monotone a Gamma U B cctx fresh).
        pose proof
          (compile_fresh_monotone b Gamma U B cctx na).
        rewrite <- Hra in H. rewrite <- Hrb in H0. simpl in *. lia.
      - exact Hbasepres_acc. }
    assert (Hacc_idx :
      sigma_idx (sumseq_acc nf) =
        Some (cvalue_of_value (zero_value tbody))).
    { subst sigma_idx sigma_acc. rewrite store_update_other.
      - apply store_update_same.
      - unfold sumseq_acc, sumseq_idx. intros Heq.
        apply temp_name_injective in Heq. lia. }
    assert (Hidx_idx :
      sigma_idx (sumseq_idx nf) = Some (CVInt m)).
    { subst sigma_idx. apply store_update_same. }
    assert (Hbound_idx : sigma_idx xb = Some (CVInt n)).
    { subst sigma_idx sigma_acc.
      rewrite store_update_other; [| exact Hboundidx].
      rewrite store_update_other; [exact Hmatch_b | exact Hboundacc]. }
    pose proof
      (sumseq_loop_sound Gamma U B cctx rho i body tbody
        Htype3
        (fun rho' sigma' cctx' fresh' value' Heval' Hrep' Hfresh' Hcompat' =>
          IHHtype3 cctx' rho' sigma' fresh' value'
            Heval' Hrep' Hfresh' Hcompat')
        m n v H9
        sigma sigma_idx fresh nf xb (zero_value tbody) k)
      as Hloop.
    assert (Hfreshle : (fresh <= nf)%nat).
    { pose proof
        (compile_fresh_monotone a Gamma U B cctx fresh).
      pose proof
        (compile_fresh_monotone b Gamma U B cctx na).
      rewrite <- Hra in H. rewrite <- Hrb in H0. simpl in *. lia. }
    specialize
      (Hloop Hfreshle Hfresh Hrep Hbasepres_idx Hfresh_idx
        Hacc_idx Hidx_idx Hbound_idx Hboundacc Hboundidx
        (zero_value_has_type tbody) Hcompat).
    destruct Hloop as
      [sigma_final
        [Hexec_loop
          [Hacc_final
            [Hbound_final [Hfresh_final Hpres_final]]]]].
    assert (Hexec_for :
      executes sigma_acc
        (CFor
          (CAssign (sumseq_idx nf) (AVar xa))
          (sumseq_test nf xb) (sumseq_step nf)
          (temp_names_between (sumseq_body_start nf) nu)
          (CSeq cu
            (CAssign (sumseq_acc nf)
              (AAdd (AVar (sumseq_acc nf)) (AVar xu)))))
        k sigma_final).
    { unfold executes in *. eapply local_steps_trans; eauto. }
    exists sigma_final. repeat split.
    + eapply executes_seq.
      * exact Hexec_a.
      * eapply executes_seq.
        -- exact Hexec_b.
        -- eapply executes_seq; eauto.
    + rewrite add_values_zero_left in Hacc_final.
      * exact Hacc_final.
      * eapply eval_sum_value_has_type. exact H9.
    + eapply store_represents_preserved.
      * exact Hrep.
      * exact Hpres_final.
    + unfold sumseq_body_compile, sumseq_idx,
        sumseq_body_start in Hfresh_final.
      rewrite <- Hru in Hfresh_final. exact Hfresh_final.
    + exact Hpres_final.
  - simpl in Hparallel. discriminate.
Qed.
