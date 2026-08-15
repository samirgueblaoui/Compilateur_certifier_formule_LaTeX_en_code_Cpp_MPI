
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Reals.Reals.
From Stdlib Require Import Relations.Relation_Operators.
From Stdlib Require Import Lia.
From Certification2 Require Export C06_GlobalExecution.

Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope R_scope.

(** Décrit un processus prêt à contribuer au SumPar. *)
Definition simple_sumpar_ready
  (Gamma : tyenv) (U : unary_sig_env) (B : binary_sig_env)
  (cctx : ctx) (rho : env) (i : var) (body : expr) (tbody : ty)
  (nf : nat) (lower bound : var) (m n : Z) (p : nat)
  (rank : nat) (contribution : value) (sigma : store) : Prop :=
  eval_stride_sum Gamma U B rho i body tbody (Z.of_nat p)
    (m + Z.of_nat rank) n contribution /\
  store_represents (ctx_repr cctx) rho sigma /\
  store_fresh sigma nf /\
  sigma lower = Some (CVInt m) /\
  sigma bound = Some (CVInt n) /\
  sigma (ctx_rank cctx) = Some (CVInt (Z.of_nat rank)) /\
  sigma (ctx_size cctx) = Some (CVInt (Z.of_nat p)) /\
  aeval sigma (ctx_active cctx) = Some (CVBool true).

(** Exécute le SumPar depuis des processus actifs prêts. *)
Lemma sumpar_simple_allreduce_from_ready :
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
    primitive_semantics_compatible U B ->
    forall nf lower bound m n p ranks values Sigma total k,
      Forall3
        (simple_sumpar_ready Gamma U B cctx rho i body tbody
          nf lower bound m n p)
        ranks values Sigma ->
      values <> [] ->
      value_sum tbody values = total ->
      exists Sigma',
        global_steps
          (running_states Sigma
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
                          Gamma U B cctx i body nf))))))) k)
          (final_states Sigma' k) /\
        Forall
          (compiled_result_matches
            (temp_name
              (cr_next_fresh
                (sumseq_body_compile Gamma U B cctx i body nf)))
            total) Sigma'.
Proof.
  intros Gamma U B cctx rho i body tbody Hbodytype Hbody_sound Hcompat
    nf lower bound m n p ranks values Sigma total k
    Hready Hnonempty Htotal.
  assert (Htyped :
    Forall (fun value => value_has_type value tbody) values).
  { clear Hnonempty Htotal.
    induction Hready as
        [|rank contribution sigma ranks values Sigma
          Hhead Htail IH].
    - constructor.
    - constructor.
      + destruct Hhead as [Heval _].
        exact
          (eval_stride_sum_value_has_type
            _ _ _ _ _ _ _ _ _ _ _ Heval).
      + exact IH. }
  assert (Hcollect :
    exists Sigma_pre,
      Forall2 local_steps
        (running_states Sigma
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
                        Gamma U B cctx i body nf))))))) k)
        (running_states Sigma_pre
          (CAllreduce (sumseq_acc nf)
            (temp_name
              (cr_next_fresh
                (sumseq_body_compile Gamma U B cctx i body nf)))) k) /\
      store_values (sumseq_acc nf) Sigma_pre =
        Some (map cvalue_of_value values)).
  { clear Hnonempty Htotal Htyped.
    induction Hready as
        [|rank contribution sigma ranks values Sigma
          Hhead Htail IH].
    - exists []. split; constructor.
    - destruct Hhead as
        [Hstride
          [Hrep [Hfresh
            [Hlower [Hbound [Hrank [Hsize Hactive]]]]]]].
      destruct
        (sumpar_simple_process_to_allreduce
          Gamma U B cctx rho i body tbody Hbodytype Hbody_sound
          sigma nf lower bound m n rank p contribution k
          Hstride Hrep Hfresh Hlower Hbound Hrank Hsize Hactive Hcompat)
        as [sigma' [Hrun [Hacc [Hresult [Hfresh' Hpres]]]]].
      destruct IH as [Sigma_pre [Hruns Hvalues]].
      exists (sigma' :: Sigma_pre). split.
      + constructor; assumption.
      + simpl. now rewrite Hacc, Hvalues. }
  destruct Hcollect as [Sigma_pre [Hlocal Hinputs]].
  set (result :=
    temp_name
      (cr_next_fresh
        (sumseq_body_compile Gamma U B cctx i body nf))).
  set (total_cv := cvalue_of_value total).
  set (Sigma_final :=
    map (fun sigma => store_update sigma result total_cv) Sigma_pre).
  exists Sigma_final. split.
  - eapply global_steps_trans.
    + apply global_steps_lift_forall2 with (q := []) in Hlocal.
      simpl in Hlocal. exact Hlocal.
    + subst result total_cv Sigma_final.
      apply allreduce_global_run
        with (values := map cvalue_of_value values).
      * exact Hinputs.
      * rewrite <- Htotal.
        apply cvalue_sum_list_correct; assumption.
  - subst Sigma_final result total_cv.
    apply Forall_forall. intros sigma Hin.
    apply in_map_iff in Hin as [before [Heq Hin]].
    subst sigma. unfold compiled_result_matches.
    apply store_update_same.
Qed.

(** Exécute le SumPar avec processus actifs et inactifs. *)
Lemma sumpar_simple_allreduce_mixed_ready :
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
    primitive_semantics_compatible U B ->
    forall nf lower bound m n p values Sigma total k,
      Forall2
        (simple_sumpar_mixed_ready
          Gamma U B cctx rho i body tbody nf lower bound m n p)
        values Sigma ->
      values <> [] ->
      value_sum tbody values = total ->
      exists Sigma',
        global_steps
          (running_states Sigma
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
                          Gamma U B cctx i body nf))))))) k)
          (final_states Sigma' k) /\
        Forall
          (compiled_result_matches
            (temp_name
              (cr_next_fresh
                (sumseq_body_compile Gamma U B cctx i body nf)))
            total) Sigma' /\
        initially_fresh Sigma'
          (S
            (cr_next_fresh
              (sumseq_body_compile Gamma U B cctx i body nf))) /\
        Forall2 preserves_store Sigma Sigma'.
Proof.
  intros Gamma U B cctx rho i body tbody
    Hbodytype Hbody_sound Hcompat
    nf lower bound m n p values Sigma total k
    Hready Hnonempty Htotal.
  assert (Htyped :
    Forall (fun value => value_has_type value tbody) values).
  { clear Hnonempty Htotal.
    induction Hready as
        [|contribution sigma values Sigma Hhead Htail IH].
    - constructor.
    - constructor.
      + inversion Hhead; subst.
        * exact
            (eval_stride_sum_value_has_type
              _ _ _ _ _ _ _ _ _ _ _ H).
        * apply zero_value_has_type.
      + exact IH. }
  assert (Hcollect :
    exists Sigma_pre,
      Forall2 local_steps
        (running_states Sigma
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
                        Gamma U B cctx i body nf))))))) k)
        (running_states Sigma_pre
          (CAllreduce (sumseq_acc nf)
            (temp_name
              (cr_next_fresh
                (sumseq_body_compile Gamma U B cctx i body nf)))) k) /\
      store_values (sumseq_acc nf) Sigma_pre =
        Some (map cvalue_of_value values) /\
      initially_fresh Sigma_pre
        (S
          (cr_next_fresh
            (sumseq_body_compile Gamma U B cctx i body nf))) /\
      Forall2
        (fun base after =>
          store_fresh base nf /\ preserves_store base after)
        Sigma Sigma_pre).
  { clear Hnonempty Htotal Htyped.
    induction Hready as
        [|contribution sigma values Sigma Hhead Htail IH].
    - exists []. repeat split; constructor.
    - destruct IH as
        [Sigma_pre
          [Hruns [Hvalues [Hfreshs Hpreserves]]]].
      inversion Hhead; subst.
      + destruct
          (sumpar_simple_process_to_allreduce
            Gamma U B cctx rho i body tbody Hbodytype Hbody_sound
            sigma nf lower bound m n rank p contribution k
            H H0 H1 H2 H3 H4 H5 H6 Hcompat)
          as [sigma' [Hrun [Hacc [Hresult [Hfresh' Hpres]]]]].
        exists (sigma' :: Sigma_pre). repeat split.
        * constructor; assumption.
        * simpl. now rewrite Hacc, Hvalues.
        * constructor; assumption.
        * constructor; [now split | exact Hpreserves].
      + destruct
          (sumpar_simple_inactive_to_allreduce
            Gamma U B cctx i body tbody sigma nf lower bound k
            Hbodytype H H0)
          as [sigma' [Hrun [Hacc [Hresult [Hfresh' Hpres]]]]].
        exists (sigma' :: Sigma_pre). repeat split.
        * constructor; assumption.
        * simpl. now rewrite Hacc, Hvalues.
        * constructor; assumption.
        * constructor; [now split | exact Hpreserves]. }
  destruct Hcollect as
    [Sigma_pre
      [Hlocal [Hinputs [Hfresh_pre Hpreserves_pre]]]].
  set (result :=
    temp_name
      (cr_next_fresh
        (sumseq_body_compile Gamma U B cctx i body nf))).
  set (total_cv := cvalue_of_value total).
  set (Sigma_final :=
    map (fun sigma => store_update sigma result total_cv) Sigma_pre).
  assert (Hnf_result :
    (nf <=
      cr_next_fresh
        (sumseq_body_compile Gamma U B cctx i body nf))%nat).
  { unfold sumseq_body_compile, sumseq_body_start.
    pose proof
      (compile_fresh_monotone body (gamma_bind_int Gamma i) U B
        (ctx_bind_var cctx i (sumseq_idx nf)) (S (S nf))).
    lia. }
  exists Sigma_final. repeat split.
  - eapply global_steps_trans.
    + apply global_steps_lift_forall2 with (q := []) in Hlocal.
      simpl in Hlocal. exact Hlocal.
    + subst result total_cv Sigma_final.
      apply allreduce_global_run
        with (values := map cvalue_of_value values).
      * exact Hinputs.
      * rewrite <- Htotal.
        apply cvalue_sum_list_correct; assumption.
  - subst Sigma_final result total_cv.
    apply Forall_forall. intros sigma Hin.
    apply in_map_iff in Hin as [before [Heq Hin]].
    subst sigma. unfold compiled_result_matches.
    apply store_update_same.
  - subst Sigma_final result total_cv.
    unfold initially_fresh in *.
    clear Hlocal Hinputs Hpreserves_pre Hready Htyped Hnonempty Htotal.
    induction Hfresh_pre as
        [|sigma Sigma_tail Hfresh_sigma Hfresh_tail IH].
    + constructor.
    + simpl. constructor.
      * apply store_fresh_update_below.
        -- exact Hfresh_sigma.
        -- lia.
      * exact IH.
  - subst Sigma_final result total_cv.
    clear Hlocal Hinputs Hfresh_pre Hready Htyped Hnonempty Htotal.
    induction Hpreserves_pre as
        [|base before Sigma_tail Sigma_pre_tail Hhead Htail IH].
    + constructor.
    + destruct Hhead as [Hbasefresh Hpreserve].
      simpl. constructor.
      * apply preserves_store_update_from_base.
        -- apply store_fresh_monotone with (n := nf);
             [exact Hbasefresh | exact Hnf_result].
        -- exact Hpreserve.
      * exact IH.
Qed.


(** Décrit une configuration globale initiale cohérente. *)
Definition initial_coherent
  (p : nat) (rho : env) (Sigma : list store) : Prop :=
  (1 <= p)%nat /\
  length Sigma = p /\
  forall rank sigma,
    nth_error Sigma rank = Some sigma ->
    store_represents (fun x => x) rho sigma /\
    sigma "rank" = Some (CVInt (Z.of_nat rank)) /\
    sigma "size" = Some (CVInt (Z.of_nat p)) /\
    sigma "isactive" = Some (CVBool true).

(** Évalue l'activité d'un contexte dans une mémoire. *)
Definition context_activeb (cctx : ctx) (sigma : store) : bool :=
  match aeval sigma (ctx_active cctx) with
  | Some (CVBool active) => active
  | _ => false
  end.

(** Filtre les mémoires actives d'un contexte. *)
Definition active_stores
  (cctx : ctx) (Sigma : list store) : list store :=
  filter (context_activeb cctx) Sigma.

(** Relie un contexte parallèle aux mémoires actives. *)
Definition parallel_context_coherent
  (cctx : ctx) (Sigma : list store) : Prop :=
  Forall
    (fun sigma =>
      exists active,
        aeval sigma (ctx_active cctx) = Some (CVBool active))
    Sigma /\
  exists p,
    (1 <= p)%nat /\
    Forall2
      (fun local_rank sigma =>
        sigma (ctx_rank cctx) =
          Some (CVInt (Z.of_nat local_rank)) /\
        sigma (ctx_size cctx) =
          Some (CVInt (Z.of_nat p)) /\
        aeval sigma (ctx_active cctx) = Some (CVBool true))
      (seq 0 p) (active_stores cctx Sigma).


(** Construit Forall2 sur une séquence d'indices. *)
Lemma forall2_seq_from_nth :
  forall (A : Type) (P : nat -> A -> Prop) p (xs : list A),
    length xs = p ->
    (forall i x, nth_error xs i = Some x -> P i x) ->
    Forall2 P (seq 0 p) xs.
Proof.
  intros A P p. revert P.
  induction p as [|p IH]; intros P xs Hlen Hnth.
  - destruct xs; [constructor | discriminate].
  - destruct xs as [|x tl]; [discriminate |].
    simpl in Hlen. injection Hlen as Hlen.
    simpl. constructor.
    + apply Hnth with (i := 0%nat). reflexivity.
    + rewrite <- seq_shift.
      assert (Hshift :
        forall ranks ys,
          Forall2 (fun i y => P (S i) y) ranks ys ->
          Forall2 P (map S ranks) ys).
      { intros ranks ys Hrel.
        induction Hrel; simpl; constructor; assumption. }
      apply Hshift.
      apply (IH (fun i y => P (S i) y) tl Hlen).
      intros i y Hi. apply Hnth with (i := S i). exact Hi.
Qed.


(** Préserve les mémoires actives après exécution. *)
Lemma active_stores_preserved :
  forall cctx Sigma Sigma',
    Forall
      (fun sigma =>
        exists active,
          aeval sigma (ctx_active cctx) = Some (CVBool active))
      Sigma ->
    Forall2 preserves_store Sigma Sigma' ->
    Forall2 preserves_store
      (active_stores cctx Sigma) (active_stores cctx Sigma').
Proof.
  intros cctx Sigma Sigma' Hall Hpreserves.
  revert Hall.
  induction Hpreserves as
      [|sigma sigma' Sigma Sigma' Hpreserve Htail IH];
    intros Hall.
  - constructor.
  - inversion Hall as [|? ? Hactive Hall_tail]; subst.
    destruct Hactive as [active Hactive].
    assert (Hactive' :
      aeval sigma' (ctx_active cctx) = Some (CVBool active)).
    { eapply aeval_preserved; eauto. }
    unfold active_stores, context_activeb. simpl.
    rewrite Hactive, Hactive'.
    destruct active; simpl.
    + constructor; [exact Hpreserve | now apply IH].
    + now apply IH.
Qed.

(** Préserve la relation entre rangs et groupes. *)
Lemma context_group_relation_preserved :
  forall cctx p ranks Sigma Sigma',
    Forall2
      (fun rank sigma =>
        sigma (ctx_rank cctx) =
          Some (CVInt (Z.of_nat rank)) /\
        sigma (ctx_size cctx) =
          Some (CVInt (Z.of_nat p)) /\
        aeval sigma (ctx_active cctx) = Some (CVBool true))
      ranks Sigma ->
    Forall2 preserves_store Sigma Sigma' ->
    Forall2
      (fun rank sigma =>
        sigma (ctx_rank cctx) =
          Some (CVInt (Z.of_nat rank)) /\
        sigma (ctx_size cctx) =
          Some (CVInt (Z.of_nat p)) /\
        aeval sigma (ctx_active cctx) = Some (CVBool true))
      ranks Sigma'.
Proof.
  intros cctx p ranks Sigma Sigma' Hgroup.
  revert Sigma'.
  induction Hgroup as
      [|rank sigma ranks Sigma Hhead Htail IH];
    intros Sigma' Hpreserves.
  - inversion Hpreserves. constructor.
  - inversion Hpreserves as
      [|? sigma' ? Sigma'' Hpreserve Hpreserves']; subst.
    destruct Hhead as [Hrank [Hsize Hactive]].
    constructor.
    + repeat split.
      * apply Hpreserve. exact Hrank.
      * apply Hpreserve. exact Hsize.
      * eapply aeval_preserved; eauto.
    + now apply IH.
Qed.

(** Préserve la cohérence d'un contexte parallèle. *)
Lemma parallel_context_coherent_preserved :
  forall cctx Sigma Sigma',
    parallel_context_coherent cctx Sigma ->
    Forall2 preserves_store Sigma Sigma' ->
    parallel_context_coherent cctx Sigma'.
Proof.
  intros cctx Sigma Sigma' [Hall [p [Hp Hgroup]]] Hpreserves.
  split.
  - clear Hgroup Hp p.
    revert Hall.
    induction Hpreserves as
        [|sigma sigma' Sigma Sigma' Hpreserve Htail IH];
      intros Hall.
    + constructor.
    + inversion Hall as [|? ? [active Hactive] Hall_tail]; subst.
      constructor.
      * exists active. eapply aeval_preserved; eauto.
      * apply IH. exact Hall_tail.
  - exists p. split; [exact Hp |].
    eapply context_group_relation_preserved.
    + exact Hgroup.
    + apply active_stores_preserved; assumption.
Qed.

(** Déduit la cohérence parallèle du contexte initial. *)
Lemma initial_coherent_parallel_context :
  forall p rho Sigma,
    initial_coherent p rho Sigma ->
    parallel_context_coherent ctx0 Sigma.
Proof.
  intros p rho Sigma [Hp [Hlen Hcoherent]].
  split.
  - apply Forall_forall. intros sigma Hin.
    exists true. reflexivity.
  - exists p. split; [exact Hp |].
    unfold active_stores, context_activeb. simpl.
    rewrite filter_true.
    + apply forall2_seq_from_nth; [exact Hlen |].
      intros rank sigma Hrank.
      specialize (Hcoherent rank sigma Hrank).
      simpl. tauto.
Qed.


(** Prépare les processus actifs après les bornes. *)
Lemma simple_sumpar_active_ready_after_bounds :
  forall Gamma U B cctx rho i body tbody nf lower bound m n p
    values Sigma,
    Forall2
      (fun rank sigma =>
        sigma (ctx_rank cctx) = Some (CVInt (Z.of_nat rank)) /\
        sigma (ctx_size cctx) = Some (CVInt (Z.of_nat p)) /\
        aeval sigma (ctx_active cctx) = Some (CVBool true))
      (seq 0 p) (active_stores cctx Sigma) ->
    stride_values Gamma U B rho i body tbody m n p values ->
    stores_represent (ctx_repr cctx) rho Sigma ->
    initially_fresh Sigma nf ->
    Forall (compiled_result_matches lower (VInt m)) Sigma ->
    Forall (compiled_result_matches bound (VInt n)) Sigma ->
    Forall3
      (simple_sumpar_ready Gamma U B cctx rho i body tbody
        nf lower bound m n p)
      (seq 0 p) values (active_stores cctx Sigma).
Proof.
  intros Gamma U B cctx rho i body tbody nf lower bound m n p
    values Sigma Hcontext Hstrides Hrep Hfresh Hlower Hbound.
  destruct Hstrides as [Hlen_values Hstrides].
  unfold stores_represent in Hrep.
  unfold initially_fresh in Hfresh.
  assert (Hlen_active : length (active_stores cctx Sigma) = p).
  { pose proof (Forall2_length Hcontext) as Hlength.
    rewrite length_seq in Hlength. now symmetry. }
  apply forall3_seq_from_nth;
    [exact Hlen_values | exact Hlen_active |].
  intros rank contribution sigma Hcontribution Hsigma.
  assert (Hin_active : In sigma (active_stores cctx Sigma)).
  { now apply nth_error_In in Hsigma. }
  unfold active_stores in Hin_active.
  apply filter_In in Hin_active as [Hin_sigma Hselected].
  assert (Hrank_bound : (rank < p)%nat).
  { assert (Hsome : nth_error values rank <> None).
    { rewrite Hcontribution. discriminate. }
    apply nth_error_Some in Hsome. now rewrite Hlen_values in Hsome. }
  assert (Hrank_seq :
    nth_error (seq 0 p) rank = Some rank).
  { rewrite nth_error_seq.
    destruct (Nat.ltb rank p) eqn:Hlt.
    - now rewrite Nat.add_0_l.
    - apply Nat.ltb_ge in Hlt. lia. }
  pose proof
    (forall2_nth_error _ _ _ _ _ _ _ _
      Hcontext Hrank_seq Hsigma) as Hrank_context.
  destruct Hrank_context as [Hrank [Hsize Hactive]].
  repeat split.
  - now apply Hstrides with (rank := rank).
  - rewrite Forall_forall in Hrep. now apply Hrep.
  - rewrite Forall_forall in Hfresh. now apply Hfresh.
  - unfold compiled_result_matches in Hlower.
    rewrite Forall_forall in Hlower. now apply Hlower.
  - unfold compiled_result_matches in Hbound.
    rewrite Forall_forall in Hbound. now apply Hbound.
  - exact Hrank.
  - exact Hsize.
  - exact Hactive.
Qed.

(** Entrelace les préparations locales du SumPar. *)
Lemma interleave_simple_sumpar_ready :
  forall Gamma U B cctx rho i body tbody nf lower bound m n p
    ranks active_values Sigma,
    Forall
      (fun sigma =>
        exists active,
          aeval sigma (ctx_active cctx) = Some (CVBool active))
      Sigma ->
    initially_fresh Sigma nf ->
    Forall (fun value => value_has_type value tbody) active_values ->
    Forall3
      (simple_sumpar_ready Gamma U B cctx rho i body tbody
        nf lower bound m n p)
      ranks active_values (active_stores cctx Sigma) ->
    exists values,
      Forall2
        (simple_sumpar_mixed_ready
          Gamma U B cctx rho i body tbody nf lower bound m n p)
        values Sigma /\
      value_sum tbody values = value_sum tbody active_values.
Proof.
  intros Gamma U B cctx rho i body tbody nf lower bound m n p
    ranks active_values Sigma Hall Hfresh Hactive_typed Hactive_ready.
  unfold initially_fresh in Hfresh.
  revert ranks active_values Hactive_typed Hactive_ready.
  induction Sigma as [|sigma Sigma IH];
    intros ranks active_values Hactive_typed Hactive_ready.
  - inversion Hall; inversion Hfresh.
    unfold active_stores in Hactive_ready. simpl in Hactive_ready.
    inversion Hactive_ready. exists []. split; [constructor | reflexivity].
  - inversion Hall as [|? ? Hactive_eval Hall_tail]; subst.
    inversion Hfresh as [|? ? Hfresh_sigma Hfresh_tail]; subst.
    destruct Hactive_eval as [active Hactive].
    destruct active.
    + assert (Hactive_ready' := Hactive_ready).
      unfold active_stores, context_activeb in Hactive_ready'.
      simpl in Hactive_ready'. rewrite Hactive in Hactive_ready'. simpl in Hactive_ready'.
      inversion Hactive_ready' as
        [|rank contribution sigma' ranks' active_values' active_stores'
          Hhead Htail]; subst.
      inversion Hactive_typed as
        [|? ? Hcontribution_type Hactive_typed_tail]; subst.
      specialize
        (IH Hall_tail Hfresh_tail ranks' active_values'
          Hactive_typed_tail Htail).
      destruct IH as [values [Hmixed Hsum]].
      exists (contribution :: values). split.
      * constructor.
        -- destruct Hhead as
             [Hstride
               [Hrep
                 [Hfresh_head
                   [Hlower
                     [Hbound
                       [Hrank [Hsize Hactive_head]]]]]]].
           apply SimpleSumparReadyActive with (rank := rank);
             assumption.
        -- exact Hmixed.
      * simpl. now rewrite Hsum.
    + assert (Hactive_ready' := Hactive_ready).
      unfold active_stores, context_activeb in Hactive_ready'.
      simpl in Hactive_ready'. rewrite Hactive in Hactive_ready'. simpl in Hactive_ready'.
      specialize
        (IH Hall_tail Hfresh_tail ranks active_values
          Hactive_typed Hactive_ready').
      destruct IH as [values [Hmixed Hsum]].
      exists (zero_value tbody :: values). split.
      * constructor.
        -- apply SimpleSumparReadyInactive; assumption.
        -- exact Hmixed.
      * simpl. rewrite Hsum.
        apply add_values_zero_left.
        now apply value_sum_has_type.
Qed.

(** Déduit la représentation depuis la cohérence initiale. *)
Lemma initial_coherent_represents :
  forall p rho Sigma,
    initial_coherent p rho Sigma ->
    stores_represent (ctx_repr ctx0) rho Sigma.
Proof.
  intros p rho Sigma [_ [_ Hcoherent]].
  unfold stores_represent. apply Forall_forall.
  intros sigma Hin.
  apply In_nth_error in Hin as [rank Hrank].
  specialize (Hcoherent rank sigma Hrank).
  simpl. tauto.
Qed.

(** Prépare tous les processus après les bornes. *)
Lemma simple_sumpar_ready_after_bounds :
  forall Gamma U B rho i body tbody nf lower bound m n p
    values Sigma0 Sigma,
    initial_coherent p rho Sigma0 ->
    stride_values Gamma U B rho i body tbody m n p values ->
    Forall2 preserves_store Sigma0 Sigma ->
    stores_represent (ctx_repr ctx0) rho Sigma ->
    initially_fresh Sigma nf ->
    Forall (compiled_result_matches lower (VInt m)) Sigma ->
    Forall (compiled_result_matches bound (VInt n)) Sigma ->
    Forall3
      (simple_sumpar_ready Gamma U B ctx0 rho i body tbody
        nf lower bound m n p)
      (seq 0 p) values Sigma.
Proof.
  intros Gamma U B rho i body tbody nf lower bound m n p
    values Sigma0 Sigma
    Hcoherent Hstrides Hpreserves Hrep Hfresh Hlower Hbound.
  destruct Hcoherent as [Hp [Hlen0 Hinitial]].
  destruct Hstrides as [Hlen_values Hstrides].
  unfold stores_represent in Hrep.
  unfold initially_fresh in Hfresh.
  assert (Hlen_sigma : length Sigma = p).
  { rewrite <- Hlen0. now apply Forall2_length in Hpreserves. }
  apply forall3_seq_from_nth; [exact Hlen_values | exact Hlen_sigma |].
  intros rank contribution sigma Hcontribution Hsigma.
  assert (Hrank_bound : (rank < p)%nat).
  { assert (Hsome : nth_error Sigma rank <> None).
    { rewrite Hsigma. discriminate. }
    apply nth_error_Some in Hsome. now rewrite Hlen_sigma in Hsome. }
  destruct (nth_error Sigma0 rank) as [sigma0|] eqn:Hsigma0.
  2: { apply nth_error_None in Hsigma0. lia. }
  specialize (Hinitial rank sigma0 Hsigma0).
  destruct Hinitial as
    [Hrep0 [Hrank [Hsize Hactive]]].
  assert (Hpreserve : preserves_store sigma0 sigma).
  { eapply forall2_nth_error; eauto. }
  split.
  - now apply Hstrides with (rank := rank).
  - repeat split.
    + rewrite Forall_forall in Hrep.
      apply Hrep. now apply nth_error_In in Hsigma.
    + rewrite Forall_forall in Hfresh.
      apply Hfresh. now apply nth_error_In in Hsigma.
    + unfold compiled_result_matches in Hlower.
      rewrite Forall_forall in Hlower.
      apply Hlower. now apply nth_error_In in Hsigma.
    + unfold compiled_result_matches in Hbound.
      rewrite Forall_forall in Hbound.
      apply Hbound. now apply nth_error_In in Hsigma.
    + apply Hpreserve. exact Hrank.
    + apply Hpreserve. exact Hsize.
Qed.

(** Compose point à point deux préservations de mémoires. *)
Lemma forall2_preserves_store_trans :
  forall Sigma1 Sigma2 Sigma3,
    Forall2 preserves_store Sigma1 Sigma2 ->
    Forall2 preserves_store Sigma2 Sigma3 ->
    Forall2 preserves_store Sigma1 Sigma3.
Proof.
  intros Sigma1 Sigma2 Sigma3 H12. revert Sigma3.
  induction H12 as
      [|sigma1 sigma2 Sigma1 Sigma2 Hhead12 Htail12 IH];
    intros Sigma3 H23.
  - inversion H23. constructor.
  - inversion H23 as
      [|? sigma3 ? Sigma3' Hhead23 Htail23]; subst.
    constructor.
    + eapply preserves_store_trans; eauto.
    + now apply IH.
Qed.

(** Préserve point à point un résultat compilé. *)
Lemma forall2_compiled_result_preserved :
  forall x value Sigma1 Sigma2,
    Forall (compiled_result_matches x value) Sigma1 ->
    Forall2 preserves_store Sigma1 Sigma2 ->
    Forall (compiled_result_matches x value) Sigma2.
Proof.
  intros x value Sigma1 Sigma2 Hmatches Hpreserves.
  induction Hpreserves.
  - constructor.
  - inversion Hmatches; subst. constructor.
    + eapply compiled_result_preserved; eauto.
    + now apply IHHpreserves.
Qed.

(** Préserve point à point la représentation source. *)
Lemma forall2_stores_represent_preserved :
  forall mu rho Sigma1 Sigma2,
    stores_represent mu rho Sigma1 ->
    Forall2 preserves_store Sigma1 Sigma2 ->
    stores_represent mu rho Sigma2.
Proof.
  intros mu rho Sigma1 Sigma2 Hrep Hpreserves.
  unfold stores_represent in *.
  induction Hpreserves.
  - constructor.
  - inversion Hrep; subst. constructor.
    + eapply store_represents_preserved; eauto.
    + now apply IHHpreserves.
Qed.
