
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Reals.Reals.
From Stdlib Require Import Relations.Relation_Operators.
From Stdlib Require Import Lia.
From Certification2 Require Export C07_SumParSimple.

Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope R_scope.

(** Prouve la correction globale du fragment sans SumPar. *)
Theorem compiler_semantic_correctness_parallel_free :
  forall Gamma U B e t cctx rho Sigma fresh v q k,
    has_type Gamma U B e t ->
    has_parallel_sum e = false ->
    eval_expr Gamma U B rho e t v ->
    env_compatible Gamma rho ->
    stores_represent (ctx_repr cctx) rho Sigma ->
    initially_fresh Sigma fresh ->
    primitive_semantics_compatible U B ->
    exists Sigma',
      global_steps
        (List.app q
          (running_states Sigma
            (cr_code (compile e Gamma U B cctx fresh)) k))
        (List.app q (final_states Sigma' k)) /\
      Forall
        (compiled_result_matches
          (cr_result (compile e Gamma U B cctx fresh)) v) Sigma' /\
      stores_represent (ctx_repr cctx) rho Sigma' /\
      initially_fresh Sigma'
        (cr_next_fresh (compile e Gamma U B cctx fresh)) /\
      Forall2 preserves_store Sigma Sigma'.
Proof.
  intros Gamma U B e t cctx rho Sigma fresh v q k
    Htype Hparallel Heval Henv Hrep Hfresh Hcompat.
  pose proof
    (collect_local_simulations
      (ctx_repr cctx) rho Sigma
      (compile e Gamma U B cctx fresh) v fresh) as Hcollect.
  specialize (Hcollect
    (fun sigma Hrep_sigma Hfresh_sigma =>
      compiler_semantic_correctness_local
        Gamma U B e t Htype Hparallel cctx rho sigma fresh v
        Heval Hrep_sigma Hfresh_sigma Hcompat)
    Hrep Hfresh k).
  destruct Hcollect as
    [Sigma'
      [Hexecs [Hmatches [Hreps [Hfreshs Hpreserves]]]]].
  exists Sigma'. repeat split.
  - apply executions_form_global_run. exact Hexecs.
  - exact Hmatches.
  - exact Hreps.
  - exact Hfreshs.
  - exact Hpreserves.
Qed.


(** Prouve la correction globale d'un SumPar simple. *)
Theorem compiler_semantic_correctness_sumpar_simple :
  forall Gamma U B i a b body tbody p rho Sigma fresh m n total k,
    has_type Gamma U B a TInt ->
    has_type Gamma U B b TInt ->
    has_type (gamma_bind_int Gamma i) U B body tbody ->
    has_parallel_sum a = false ->
    has_parallel_sum b = false ->
    has_parallel_sum body = false ->
    eval_expr Gamma U B rho a TInt (VInt m) ->
    eval_expr Gamma U B rho b TInt (VInt n) ->
    eval_sum Gamma U B rho i m n body tbody total ->
    env_compatible Gamma rho ->
    initial_coherent p rho Sigma ->
    initially_fresh Sigma fresh ->
    primitive_semantics_compatible U B ->
    exists Sigma',
      global_steps
        (running_states Sigma
          (cr_code
            (compile (ESumPar i a b body)
              Gamma U B ctx0 fresh)) k)
        (final_states Sigma' k) /\
      Forall
        (compiled_result_matches
          (cr_result
            (compile (ESumPar i a b body)
              Gamma U B ctx0 fresh))
          total) Sigma'.
Proof.
  intros Gamma U B i a b body tbody p rho Sigma fresh m n total k
    Htype_a Htype_b Htype_body
    Hparallel_a Hparallel_b Hparallel_body
    Heval_a Heval_b Hsum Henv Hcoherent Hfresh Hcompat.
  remember (compile a Gamma U B ctx0 fresh) as ra eqn:Hra.
  remember
    (compile b Gamma U B ctx0 (cr_next_fresh ra))
    as rb eqn:Hrb.
  set (nf := cr_next_fresh rb).
  set (ru :=
    sumseq_body_compile Gamma U B ctx0 i body nf).
  set (result := temp_name (cr_next_fresh ru)).
  set (tail :=
    CSeq
      (CAssign (sumseq_acc nf) (zero_aexpr tbody))
      (CSeq
        (sumpar_simple_if Gamma U B ctx0 i body nf
          (cr_result ra) (cr_result rb))
        (CSeq
          (CAssign result (zero_aexpr tbody))
          (CAllreduce (sumseq_acc nf) result)))).
  assert (Hru_type : cr_type ru = tbody).
  { subst ru nf. unfold sumseq_body_compile.
    apply compile_type_correct. exact Htype_body. }
  assert (Hcode :
    cr_code
      (compile (ESumPar i a b body) Gamma U B ctx0 fresh) =
    CSeq (cr_code ra) (CSeq (cr_code rb) tail)).
  { cbn [compile].
    rewrite <- Hra. simpl.
    rewrite <- Hrb. simpl.
    rewrite Hparallel_body.
    subst tail result ru nf.
    cbn [sumpar_simple_if sumseq_acc sumseq_idx
      sumseq_body_start sumseq_body_compile sumseq_cleanup
      sumseq_loop_body sumseq_test sumstride_step].
    unfold sumseq_body_compile, sumseq_idx, sumseq_body_start in Hru_type.
    rewrite Hru_type. reflexivity. }
  assert (Hresult :
    cr_result
      (compile (ESumPar i a b body) Gamma U B ctx0 fresh) =
    result).
  { cbn [compile].
    rewrite <- Hra. simpl.
    rewrite <- Hrb. simpl.
    rewrite Hparallel_body.
    subst result ru nf. reflexivity. }
  destruct
    (compiler_semantic_correctness_parallel_free
      Gamma U B a TInt ctx0 rho Sigma fresh (VInt m) []
      (KCmd (CSeq (cr_code rb) tail) :: k)
      Htype_a Hparallel_a Heval_a Henv
      (initial_coherent_represents p rho Sigma Hcoherent)
      Hfresh Hcompat)
    as [Sigma_a
      [Hrun_a
        [Hmatch_a [Hrep_a [Hfresh_a Hpres_a]]]]].
  rewrite <- Hra in Hrun_a, Hmatch_a, Hfresh_a.
  simpl in Hrun_a.
  destruct
    (compiler_semantic_correctness_parallel_free
      Gamma U B b TInt ctx0 rho Sigma_a
      (cr_next_fresh ra) (VInt n) []
      (KCmd tail :: k)
      Htype_b Hparallel_b Heval_b Henv
      Hrep_a Hfresh_a Hcompat)
    as [Sigma_b
      [Hrun_b
        [Hmatch_b [Hrep_b [Hfresh_b Hpres_b]]]]].
  rewrite <- Hrb in Hrun_b, Hmatch_b, Hfresh_b.
  simpl in Hrun_b.
  destruct
    (eval_sum_partition_stride
      Gamma U B rho i body tbody m n total Hsum p)
    as [values [Hstrides Hvalues_total]].
  { destruct Hcoherent as [Hp _]. exact Hp. }
  assert (Hp : (1 <= p)%nat).
  { now destruct Hcoherent as [Hp _]. }
  assert (Hvalues_nonempty : values <> []).
  { intros Hempty. subst values.
    destruct Hstrides as [Hlength _]. simpl in Hlength. lia. }
  assert (Hpres_ab : Forall2 preserves_store Sigma Sigma_b).
  { eapply forall2_preserves_store_trans; eauto. }
  assert (Hready :
    Forall3
      (simple_sumpar_ready Gamma U B ctx0 rho i body tbody
        nf (cr_result ra) (cr_result rb) m n p)
      (seq 0 p) values Sigma_b).
  { apply simple_sumpar_ready_after_bounds
      with (Sigma0 := Sigma).
    - exact Hcoherent.
    - exact Hstrides.
    - exact Hpres_ab.
    - exact Hrep_b.
    - subst nf. exact Hfresh_b.
    - eapply forall2_compiled_result_preserved; eauto.
    - exact Hmatch_b. }
  destruct
    (sumpar_simple_allreduce_from_ready
      Gamma U B ctx0 rho i body tbody Htype_body
      (fun rho' sigma' cctx' fresh' value Heval Hrep Hfresh Hcompat =>
        compiler_semantic_correctness_local
          (gamma_bind_int Gamma i) U B body tbody Htype_body
          Hparallel_body cctx' rho' sigma' fresh' value
          Heval Hrep Hfresh Hcompat)
      Hcompat nf (cr_result ra) (cr_result rb) m n p
      (seq 0 p) values Sigma_b total k
      Hready Hvalues_nonempty Hvalues_total)
    as [Sigma_final [Hrun_tail Hmatches]].
  exists Sigma_final. split.
  - rewrite Hcode.
    eapply global_steps_trans.
    + apply global_steps_open_seq.
    + eapply global_steps_trans.
      * exact Hrun_a.
      * eapply global_steps_trans.
        -- apply global_steps_open_seq.
        -- eapply global_steps_trans; eauto.
  - now rewrite Hresult.
Qed.


(** Reformule la correction séquentielle comme dans le document. *)
Corollary compiler_semantic_correctness_tex_parallel_free :
  forall Gamma U B e t p rho Sigma fresh v q k,
    has_type Gamma U B e t ->
    has_parallel_sum e = false ->
    eval_expr Gamma U B rho e t v ->
    env_compatible Gamma rho ->
    initial_coherent p rho Sigma ->
    initially_fresh Sigma fresh ->
    primitive_semantics_compatible U B ->
    exists Sigma',
      global_steps
        (List.app q
          (running_states Sigma
            (cr_code (compile e Gamma U B ctx0 fresh)) k))
        (List.app q (final_states Sigma' k)) /\
      Forall
        (compiled_result_matches
          (cr_result (compile e Gamma U B ctx0 fresh)) v) Sigma'.
Proof.
  intros Gamma U B e t p rho Sigma fresh v q k
    Htype Hparallel Heval Henv Hcoherent Hfresh Hcompat.
  destruct
    (compiler_semantic_correctness_parallel_free
      Gamma U B e t ctx0 rho Sigma fresh v q k
      Htype Hparallel Heval Henv
      (initial_coherent_represents p rho Sigma Hcoherent)
      Hfresh Hcompat)
    as [Sigma'
      [Hrun [Hresult [Hrep [Hfresh' Hpreserves]]]]].
  exists Sigma'. now split.
Qed.
