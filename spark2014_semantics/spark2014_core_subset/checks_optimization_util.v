Require Export checks_optimization.
(*
Require Export checks_generator.
Require Export well_typed.
*)

Scheme expression_ind := Induction for expression Sort Prop 
                         with name_ind := Induction for name Sort Prop.

Scheme expression_x_ind := Induction for expression_x Sort Prop 
                         with name_x_ind := Induction for name_x Sort Prop.

(** * ZArith Help Lemmas *)
(**
Coq.ZArith.Zorder: http://coq.inria.fr/V8.1/stdlib/Coq.ZArith.Zorder.html#Zle_ge
                   http://coq.inria.fr/V8.1/stdlib/Coq.ZArith.Zbool.html
                   http://coq.inria.fr/V8.1/stdlib/Coq.ZArith.Zbool.html#Zle_bool
*)

Lemma Zge_le_bool: forall u v b,
  Zge_bool u v = b -> Zle_bool v u = b.
Proof.
  intros;
  unfold Zle_bool; unfold Zge_bool in H;
  rewrite <- Zcompare_antisym;
  destruct (u ?= v)%Z; auto. 
Qed.

Lemma Zle_ge_bool: forall u v b,
  Zle_bool u v = b -> Zge_bool v u = b.
Proof.
  intros;
  unfold Zge_bool; unfold Zle_bool in H;
  rewrite <- Zcompare_antisym;
  destruct (u ?= v)%Z; auto. 
Qed.

(** In run time check semantics, Zge_bool and Zle_bool is used to define overflow check,
    and in eval_expr_value_in_domain, <= and >= are used, the following lemmas are used
    to build their relationships;
*)
Lemma Le_Neg_Ge: forall x y,  
  (x <= y)%Z ->
    (-y <= -x)%Z.
Proof.
  intros.
  apply Zplus_le_reg_l with (p := y). 
  crush. (*omega*)
Qed.

Lemma Lt_Le_Bool_False: forall u v,
  (u < v)%Z ->
    Zle_bool v u = false.
Proof.
  intros;
  apply Zge_le_bool;
  unfold Zge_bool; unfold Zlt in H;
  crush.
Qed.


Lemma Zgele_Bool_Imp_GeLe_T: forall v l u,
  (Zge_bool v l) && (Zle_bool v u) = true ->
    (l <= v)%Z /\ (v <= u)%Z.
Proof.
  intros.
  specialize (andb_prop _ _ H); clear H; intros HZ.
  destruct HZ as [HZ1 HZ2].
  split.
- specialize (Zge_cases v l); intros HZ.
  rewrite HZ1 in HZ; crush.
- apply Zle_bool_imp_le; auto.  
Qed.

Lemma Zgele_Bool_Imp_GeLe_F: forall v l u,
  (Zge_bool v l) && (Zle_bool v u) = false ->
    (v < l)%Z \/ (u < v)%Z.
Proof.
  intros.
  unfold andb in H.
  remember (Zge_bool v l) as b1; 
  remember (Zle_bool v u) as b2.
  symmetry in Heqb1, Heqb2.
  destruct b1, b2; inversion H.
- specialize (Zle_cases v u); intros HZ;
  rewrite Heqb2 in HZ; crush.
- specialize (Zge_cases v l); intros HZ;
  rewrite Heqb1 in HZ; crush.
- specialize (Zge_cases v l); intros HZ;
  rewrite Heqb1 in HZ; crush.  
Qed.


(********************************************************************)
(********************************************************************)


Lemma Zlele_Bool_Imp_LeLe_T: forall v l u,
  (Zle_bool l v) && (Zle_bool v u) = true ->
    (l <= v)%Z /\ (v <= u)%Z.
Proof.
  intros.
  specialize (andb_prop _ _ H); clear H; intros HZ.
  destruct HZ as [HZ1 HZ2].
  split.
- specialize (Zle_cases l v); intros HZ.
  rewrite HZ1 in HZ; crush.
- apply Zle_bool_imp_le; auto.  
Qed.

Lemma Zlele_Bool_Imp_LeLe_F: forall v l u,
  (Zle_bool l v) && (Zle_bool v u) = false ->
    (v < l)%Z \/ (u < v)%Z.
Proof.
  intros.
  unfold andb in H.
  remember (Zle_bool l v) as b1; 
  remember (Zle_bool v u) as b2.
  symmetry in Heqb1, Heqb2.
  destruct b1, b2; inversion H.
- specialize (Zle_cases v u); intros HZ;
  rewrite Heqb2 in HZ; crush.
- specialize (Zle_cases l v); intros HZ;
  rewrite Heqb1 in HZ; crush.
- specialize (Zle_cases l v); intros HZ;
  rewrite Heqb1 in HZ; crush.  
Qed.

Lemma In_Bound_Refl: forall v,
  in_bound v (Interval v v) true.
Proof.
  intros; constructor;
  specialize (Zle_refl v); intros H0.
  specialize (Zle_imp_le_bool _ _ H0); 
    intros H1; rewrite H1; auto.
Qed.

Lemma in_bound_conflict: forall v bound,
  in_bound v bound true ->
    in_bound v bound false ->
      False.
Proof.
  intros.
  inversion H; inversion H0; crush.
Qed.

Ltac apply_in_bound_conflict :=
  match goal with
  | [H1: in_bound ?v ?bound true, 
     H2: in_bound ?v ?bound false |- _] => specialize (in_bound_conflict _ _ H1 H2)
  end.

(** l <= v <= u, l' <= l <= u', l' <= u <= u' => l' <= v <= u', where vBound = (l', u') *)
Lemma In_Bound_Trans: forall v l u vBound,
  in_bound v (Interval l u) true ->
    in_bound l vBound true ->
      in_bound u vBound true ->
        in_bound v vBound true.
Proof.
  intros;
  repeat progress match goal with
  | [H: in_bound _ _ _ |- _] => inversion H; clear H; subst
  end;
  repeat progress match goal with
  | [H: _ && _ = true |- _] => specialize (Zlele_Bool_Imp_LeLe_T _ _ _ H); clear H; crush
  end;
  constructor; apply andb_true_iff; split.
- specialize (Zle_trans _ _ _ H3 H0); intros HZ1;
  specialize (Zle_imp_le_bool _ _ HZ1); auto.
- specialize (Zle_trans _ _ _ H1 H5); intros HZ1;
  specialize (Zle_imp_le_bool _ _ HZ1); auto.
Qed.

Ltac apply_In_Bound_Trans :=
  match goal with
  | [H1: in_bound ?v (Interval ?l ?u) true,
     H2: in_bound ?l _ true,
     H3: in_bound ?u _ true |- _ ] =>
      specialize (In_Bound_Trans _ _ _ _ H1 H2 H3);
      let HZ := fresh "HZ" in intros HZ
  end.


Lemma In_Bound_SubBound_Trans: forall v vBound vBound',
  in_bound v vBound true ->
    sub_bound vBound vBound' true ->
      in_bound v vBound' true.
Proof.
  intros;
  inversion H0; subst;
  apply_In_Bound_Trans; auto.
Qed.

Ltac apply_In_Bound_SubBound_Trans :=
  match goal with
  | [H1: in_bound _ ?b true,
     H2: sub_bound ?b _ true |- _] =>
      specialize (In_Bound_SubBound_Trans _ _ _ H1 H2);
      let HZ := fresh "HZ" in intros HZ
  end.

(** l1 <= v1 <= u1, l2 <= v2 <= u2 => (l1+l2) <= (v1+v2) <= (u1+u2) *)
Lemma In_Bound_Plus_Compat: forall v1 l1 u1 v2 l2 u2,
  in_bound v1 (Interval l1 u1) true ->
    in_bound v2 (Interval l2 u2) true ->
      in_bound (v1+v2) (Interval (l1+l2) (u1+u2)) true.
Proof.
  intros;
  repeat progress match goal with
  | [H: in_bound _ _ _ |- _] => inversion H; clear H; subst
  end;
  repeat progress match goal with
  | [H: _ && _ = true |- _] => specialize (Zlele_Bool_Imp_LeLe_T _ _ _ H); clear H; crush
  end;
  constructor; apply andb_true_iff; split.
- specialize (Zplus_le_compat _ _ _ _ H0 H2); intros HZ1;
  specialize (Zle_imp_le_bool _ _ HZ1); auto.
- specialize (Zplus_le_compat _ _ _ _ H1 H3); intros HZ1;
  specialize (Zle_imp_le_bool _ _ HZ1); auto.
Qed.

Ltac apply_In_Bound_Plus_Compat :=
  match goal with
  | [H1: in_bound ?v1 _ true,
     H2: in_bound ?v2 _ true |- _] => 
      specialize (In_Bound_Plus_Compat _ _ _ _ _ _ H1 H2);
      let HZ := fresh "HZ" in intros HZ
  end.

(** l1 <= v1 <= u1, l2 <= v2 <= u2 => (l1-u2) <= (v1-v2) <= (u1-l2) *)
Lemma In_Bound_Minus_Compat: forall v1 l1 u1 v2 l2 u2,
  in_bound v1 (Interval l1 u1) true ->
    in_bound v2 (Interval l2 u2) true ->
      in_bound (v1-v2) (Interval (l1-u2) (u1-l2)) true.
Proof.
  intros;
  repeat progress match goal with
  | [H: in_bound _ _ _ |- _] => inversion H; clear H; subst
  end;
  repeat progress match goal with
  | [H: _ && _ = true |- _] => specialize (Zlele_Bool_Imp_LeLe_T _ _ _ H); clear H; crush
  end;
  constructor; apply andb_true_iff; split.
- specialize (Le_Neg_Ge _ _ H3); intros HZ1;
  specialize (Zplus_le_compat _ _ _ _ H0 HZ1); intros HZ2;
  specialize (Zle_imp_le_bool _ _ HZ2); auto.
- specialize (Le_Neg_Ge _ _ H2); intros HZ1;
  specialize (Zplus_le_compat _ _ _ _ H1 HZ1); intros HZ2;
  specialize (Zle_imp_le_bool _ _ HZ2); auto.
Qed.

Ltac apply_In_Bound_Minus_Compat :=
  match goal with
  | [H1: in_bound ?v1 _ true,
     H2: in_bound ?v2 _ true |- _] => 
      specialize (In_Bound_Minus_Compat _ _ _ _ _ _ H1 H2);
      let HZ := fresh "HZ" in intros HZ
  end.

Lemma Sub_Bound_Plus_Compat: forall v1 l1 u1 v2 l2 u2 vBound,
  in_bound v1 (Interval l1 u1) true ->
    in_bound v2 (Interval l2 u2) true ->
      in_bound (v1+v2) vBound false ->
        sub_bound (Interval (l1 + l2) (u1 + u2)) vBound false.
Proof.
  intros;
  repeat progress match goal with
  | [H: in_bound _ _ _ |- _] => inversion H; clear H; subst
  end;
  repeat progress match goal with
  | [H: _ && _ = true |- _] => specialize (Zlele_Bool_Imp_LeLe_T _ _ _ H); clear H; crush
  end;
  match goal with
  | [H: _ && _ = false |- _] => specialize (Zlele_Bool_Imp_LeLe_F _ _ _ H); clear H; crush
  end;
  constructor.
- specialize (Zplus_le_compat _ _ _ _ H0 H3); intros HZ1.
  specialize (Zle_lt_trans _ _ _ HZ1 H2); intros HZ2.
  left. constructor.
  apply andb_false_iff; left.
  apply Lt_Le_Bool_False; auto.
- specialize (Zplus_le_compat _ _ _ _ H1 H4); intros HZ1.
  specialize (Zlt_le_trans  _ _ _ H2 HZ1); intros HZ2.
  right; constructor.
  apply andb_false_iff; right.
  apply Lt_Le_Bool_False; auto.
Qed.

Ltac apply_Sub_Bound_Plus_Compat :=
  match goal with
  | [H1: in_bound ?v1 _ true,
     H2: in_bound ?v2 _ true,
     H3: in_bound (?v1+?v2) _ false |- _] => 
      specialize (Sub_Bound_Plus_Compat _ _ _ _ _ _ _ H1 H2 H3);
      let HZ := fresh "HZ" in intros HZ
  end.

Lemma Sub_Bound_Minus_Compat: forall v1 l1 u1 v2 l2 u2 vBound,
  in_bound v1 (Interval l1 u1) true ->
    in_bound v2 (Interval l2 u2) true ->
      in_bound (v1-v2) vBound false ->
        sub_bound (Interval (l1 - u2) (u1 - l2)) vBound false.
Proof.
  intros;
  repeat progress match goal with
  | [H: in_bound _ _ _ |- _] => inversion H; clear H; subst
  end;
  repeat progress match goal with
  | [H: _ && _ = true |- _] => specialize (Zlele_Bool_Imp_LeLe_T _ _ _ H); clear H; crush
  end;
  match goal with
  | [H: _ && _ = false |- _] => specialize (Zlele_Bool_Imp_LeLe_F _ _ _ H); clear H; crush
  end;
  constructor.
- specialize (Le_Neg_Ge _ _ H4); intros HZ1;
  specialize (Zplus_le_compat _ _ _ _ H0 HZ1); intros HZ2;
  specialize (Zle_lt_trans _ _ _ HZ2 H2); intros HZ3;
  left; constructor;
  apply andb_false_iff; left;
  apply Lt_Le_Bool_False; auto.
- specialize (Le_Neg_Ge _ _ H3); intros HZ1;
  specialize (Zplus_le_compat _ _ _ _ H1 HZ1); intros HZ2;
  specialize (Zlt_le_trans  _ _ _ H2 HZ2); intros HZ3;
  right; constructor;
  apply andb_false_iff; right;
  apply Lt_Le_Bool_False; auto.
Qed.

Ltac apply_Sub_Bound_Minus_Compat :=
  match goal with
  | [H1: in_bound ?v1 _ true,
     H2: in_bound ?v2 _ true,
     H3: in_bound (?v1-?v2) _ false |- _] => 
      specialize (Sub_Bound_Minus_Compat _ _ _ _ _ _ _ H1 H2 H3);
      let HZ := fresh "HZ" in intros HZ
  end.

Lemma Sub_Bound_Unary_Minus_Compat: forall v l u vBound,
  in_bound v (Interval l u) true ->
    in_bound (- v) vBound false ->
      sub_bound (Interval (- u) (- l)) vBound false.
Proof.
  intros;
  repeat progress match goal with
  | [H: in_bound _ _ _ |- _] => inversion H; clear H; subst
  end;
 match goal with
  | [H: _ && _ = true |- _] => specialize (Zlele_Bool_Imp_LeLe_T _ _ _ H); clear H; crush
  end;
  match goal with
  | [H: _ && _ = false |- _] => specialize (Zlele_Bool_Imp_LeLe_F _ _ _ H); clear H; crush
  end;
  constructor;
  [left | right];
  constructor.
- apply andb_false_iff; left;
  specialize (Le_Neg_Ge _ _ H2); intros HZ1;
  specialize (Zle_lt_trans _ _ _ HZ1 H1); intros HZ2;
  apply Lt_Le_Bool_False; auto.
- apply andb_false_iff; right;
  specialize (Le_Neg_Ge _ _ H0); intros HZ1;
  specialize (Zlt_le_trans _ _ _ H1 HZ1); intros HZ2;
  apply Lt_Le_Bool_False; auto.
Qed.

Ltac apply_Sub_Bound_Unary_Minus_Compat :=
  match goal with
  | [H1: in_bound ?v _ true,
     H2: in_bound (- ?v) _ false |- _] =>
      specialize (Sub_Bound_Unary_Minus_Compat _ _ _ _ H1 H2);
      let HZ := fresh "HZ" in intros HZ
  end.

Lemma In_Bound_Unary_Minus_Compat: forall v l u,
  in_bound v (Interval l u) true ->
    in_bound (- v) (Interval (- u) (- l)) true.
Proof.
  intros.
  inversion H; clear H; subst.
  constructor.
  specialize (Zlele_Bool_Imp_LeLe_T _ _ _ H2); crush.
  specialize (Le_Neg_Ge _ _ H0); intros HZ1.
  specialize (Le_Neg_Ge _ _ H1); intros HZ2.
  specialize (Zle_imp_le_bool  _ _ HZ1); intros HZ3.
  specialize (Zle_imp_le_bool  _ _ HZ2); intros HZ4.
  crush.
Qed.

Lemma in_bound_value_neq_zero: forall v vBound,
  in_bound v vBound true ->
    in_bound 0 vBound false ->
      Zeq_bool v 0 = false.
Proof.
  intros;
  repeat progress match goal with
  | [H: in_bound _ _ _ |- _] => inversion H; clear H; subst
  end;
  match goal with
  | [H: _ && _ = true |- _] => specialize (Zlele_Bool_Imp_LeLe_T _ _ _ H); clear H; crush
  end;
  match goal with
  | [H: _ && _ = false |- _] => specialize (Zlele_Bool_Imp_LeLe_F _ _ _ H); clear H; crush
  end;
  [ specialize (Zlt_le_trans _ _ _ H1 H0); intros HZ1 |
    specialize (Zle_lt_trans _ _ _ H2 H1); intros HZ1
  ];
  unfold Zeq_bool; 
  destruct v; crush.
Qed.

Ltac apply_in_bound_value_neq_zero :=
  match goal with
  | [H1: in_bound ?v ?b true,
     H2: in_bound 0 ?b false |- _] => 
      specialize (in_bound_value_neq_zero _ _ H1 H2);
      let HZ := fresh "HZ" in intros HZ
  end.

(********************************************************************)
(********************************************************************)

Lemma removed_check_flag_notin: forall ck cks cks',
 remove_check_flag ck cks = cks' ->
   ~(List.In ck cks').
Proof.
  induction cks; crush.
  remember (beq_check_flag ck a) as b;
  destruct b; crush;eauto.
  destruct ck; crush.
Qed.

Ltac apply_removed_check_flag_notin :=
  match goal with
  | [H: remove_check_flag _ _ = _ |- _] => 
      specialize (removed_check_flag_notin _ _ _ H);
      let HZ := fresh "HZ" in intros HZ
  | [H: _ = remove_check_flag _ _ |- _] => 
      symmetry in H; specialize (removed_check_flag_notin _ _ _ H);
      let HZ := fresh "HZ" in intros HZ
  end.

Lemma remove_notin_check_flag: forall ck cks,
  ~(List.In ck cks) ->
    remove_check_flag ck cks = cks.
Proof.
  induction cks; crush.
  remember (beq_check_flag ck a) as b;
  destruct b; crush.
  destruct a; destruct ck; crush.
Qed.

Ltac apply_remove_notin_check_flag :=
  match goal with
  | [H: ~(List.In _ _) |- _] => 
      specialize (remove_notin_check_flag _ _ H); let HZ := fresh "HZ" in intros HZ
  | [H: List.In _ _ -> False |- _] => 
      specialize (remove_notin_check_flag _ _ H); let HZ := fresh "HZ" in intros HZ
  end.

Lemma check_flag_in_reserve: forall ck ck' cks,
  beq_check_flag ck ck' = false ->
    List.In ck (remove_check_flag ck' cks) ->
      List.In ck cks.
Proof.
  induction cks; crush.
  remember (beq_check_flag ck' a) as b;
  destruct b; crush.  
Qed.

Ltac apply_check_flag_in_reserve :=
  match goal with
  | [H1: beq_check_flag ?ck ?ck' = false,
     H2: List.In ?ck (remove_check_flag ?ck' _) |- _] =>
      specialize (check_flag_in_reserve _ _ _ H1 H2);
      let HZ := fresh "HZ" in intros HZ
  end.

Lemma check_flag_in_reserve2: forall ck ck' cks,
  beq_check_flag ck ck' = false ->
    List.In ck cks ->
      List.In ck (remove_check_flag ck' cks).      
Proof.
  induction cks; crush.
  remember (beq_check_flag ck' ck) as b; destruct b; crush.
  destruct ck; destruct ck'; crush.
  remember (beq_check_flag ck' a) as b; destruct b; crush.
Qed.

Ltac apply_check_flag_in_reserve2 :=
  match goal with
  | [ H1: beq_check_flag ?ck _ = false,
      H2: List.In ?ck _ |- _] =>
      specialize (check_flag_in_reserve2 _ _ _ H1 H2);
      let HZ := fresh "HZ" in intros HZ
  end.


(********************************************************************)
(********************************************************************)


Lemma in_bound_unique: forall v vBound b1 b2,
  in_bound v vBound b1 ->
    in_bound v vBound b2 ->
      b1 = b2.
Proof.
  intros;
  inversion H; inversion H0; crush.
Qed. 

Ltac apply_in_bound_unique :=
  match goal with
  | [H1: in_bound ?v _ _,
     H2: in_bound ?v _ _ |- _] =>
      specialize (in_bound_unique _ _ _ _ H1 H2);
      let HZ := fresh "HZ" in intros HZ; inversion HZ
  end.

Lemma sub_bound_unique: forall bound1 bound2 b1 b2,
  sub_bound bound1 bound2 b1 ->
    sub_bound bound1 bound2 b2 ->
      b1 = b2.
Proof.
  intros;
  inversion H; inversion H0; crush;
  apply_in_bound_unique.
Qed.

Ltac apply_sub_bound_unique :=
  match goal with
  | [H1: sub_bound ?bound1 _ _,
     H2: sub_bound ?bound1 _ _ |- _] =>
      specialize (sub_bound_unique _ _ _ _ H1 H2);
      let HZ := fresh "HZ" in intros HZ; inversion HZ
  end.

(********************************************************************)
(********************************************************************)

Lemma optimize_name_ast_num_eq: forall st n n' nBound,
  optimize_name_x st n (n', nBound) ->
    fetch_exp_type_x (name_astnum_x n) st = fetch_exp_type_x (name_astnum_x n') st.
Proof.
  intros;
  inversion H; crush.
Qed.

Ltac apply_optimize_name_ast_num_eq :=
  match goal with
  | [H: optimize_name_x _ _ _ |- _] =>
      specialize (optimize_name_ast_num_eq _ _ _ _ H);
      let HZ := fresh "HZ" in intros HZ
  end.

Lemma optimize_exp_ex_cks_eq: forall st e e' eBound,
  optimize_expression_x st e (e', eBound) ->
    exp_exterior_checks e' = exp_exterior_checks e.
Proof.
  intros;
  inversion H; crush;
  match goal with
  | [H: optimize_name_x _ _ _ |- _] => inversion H; crush
  end.
Qed.

Ltac apply_optimize_exp_ex_cks_eq :=
  match goal with
  | [H: optimize_expression_x _ _ _ |- _] => 
      specialize (optimize_exp_ex_cks_eq _ _ _ _ H);
      let HZ := fresh "HZ" in intros HZ
  end.

Lemma optimize_name_ex_cks_eq: forall st n n' nBound,
  optimize_name_x st n (n', nBound) ->
    name_exterior_checks n' = name_exterior_checks n.
Proof.
  intros;
  inversion H; crush.
Qed.

Ltac apply_optimize_name_ex_cks_eq :=
  match goal with
  | [H: optimize_name_x _ _ _ |- _] => 
      specialize (optimize_name_ex_cks_eq _ _ _ _ H);
      let HZ := fresh "HZ" in intros HZ
  end.


Lemma eval_expr_value_reserve: forall e eBound rBound e' st s v,
  optimize_range_check e eBound rBound e' ->
    eval_expr_x st s e v ->
      eval_expr_x st s e' v.
Proof.
  intros;
  inversion H; subst; auto;
  apply eval_exp_ex_cks_added; auto.
Qed.

Ltac apply_eval_expr_value_reserve :=
  match goal with
  | [H1: optimize_range_check ?e _ _ _,
     H2: eval_expr_x _ _ ?e _ |- _] =>
      specialize (eval_expr_value_reserve _ _ _ _ _ _ _ H1 H2);
      let HZ := fresh "HZ" in intro HZ
  end.
 
Lemma eval_expr_value_copy_out_opt_reserve: forall e eBound rBound e' st s v,
  optimize_range_check_on_copy_out e eBound rBound e' ->
    eval_expr_x st s e v ->
      eval_expr_x st s e' v.
Proof.
  intros;
  inversion H; subst; auto;
  apply eval_exp_ex_cks_added; auto.
Qed.

Ltac apply_eval_expr_value_copy_out_opt_reserve :=
  match goal with
  | [H1: optimize_range_check_on_copy_out ?e _ _ _,
     H2: eval_expr_x _ _ ?e _ |- _] =>
      specialize (eval_expr_value_copy_out_opt_reserve _ _ _ _ _ _ _ H1 H2);
      let HZ := fresh "HZ" in intro HZ
  end.

(*******************************************************************)

Lemma remove_check_on_binop_reserve: forall cks op v1 v2 v ck,
  do_flagged_checks_on_binop cks op v1 v2 (Normal v) ->
    do_flagged_checks_on_binop (remove_check_flag ck cks) op v1 v2 (Normal v).
Proof.
  intros;
  induction cks; crush;
  match goal with
  | [H: do_flagged_checks_on_binop _ _ _ _ _ |- _] => inversion H; crush
  end;
  match goal with
  | [H: do_flagged_check_on_binop _ _ _ _ _ |- _] => inversion H; crush
  end;
  match goal with
  | [|- context[beq_check_flag _ Do_Overflow_Check]] => destruct (beq_check_flag ck Do_Overflow_Check); auto
  | [|- context[beq_check_flag _ Do_Division_Check]] => destruct (beq_check_flag ck Do_Division_Check); auto
  end;
  apply Do_Checks_Binop with (v:=v4); crush.
Qed.

Lemma safe_remove_binop_check: forall cks op v1 v2 v ck v',
  do_flagged_checks_on_binop cks op v1 v2 v ->
    do_flagged_check_on_binop ck op v1 v2 (Normal v') ->
      do_flagged_checks_on_binop (remove_check_flag ck cks) op v1 v2 v.
Proof.
  induction cks; crush;eauto;
  match goal with
  | [H: do_flagged_check_on_binop _ _ _ _ _ |- _] => inversion H; crush;eauto
  end;
  match goal with
  | [H: do_flagged_checks_on_binop _ _ _ _ _ |- _] => inversion H; crush;eauto
  end;
  match goal with
  | [H: do_flagged_check_on_binop ?a _ _ _ _ |- context[?a]] => destruct a; inversion H; crush;eauto
  end;
  match goal with
  | [H1: _ = _, H2: _ = _ |- _] => rewrite H1 in H2; inversion H2; crush;eauto
  | _ => idtac
  end;
  match goal with
  | [H1: do_overflow_check _ _, 
     H2: do_overflow_check _ _ |- _] => inversion H1; inversion H2; clear H1 H2; subst; apply_in_bound_unique
  | [H1: do_division_check _ _ _,
     H2: do_division_check _ _ _ |- _] => inversion H1; inversion H2; clear H1 H2; crush;eauto
  | _ => idtac
  end;
  solve
  [ apply Do_Checks_Binop_RTE; auto |
    apply Do_Checks_Binop with (v:=v5); crush;eauto |
    apply Do_Checks_Binop with (v:=v4); crush;eauto
  ].
Qed.

Ltac apply_safe_remove_binop_check :=
  match goal with
  | [H1: do_flagged_checks_on_binop _ ?op ?v1 ?v2 _,
     H2: do_flagged_check_on_binop _ ?op ?v1 ?v2 (Normal _) |- _] =>
      specialize (safe_remove_binop_check _ _ _ _ _ _ _ H1 H2);
      let HZ := fresh "HZ" in intros HZ; inversion HZ
  end.

Lemma remove_check_on_unop_reserve: forall cks op v v' ck,
  do_flagged_checks_on_unop cks op v (Normal v') ->
    do_flagged_checks_on_unop (remove_check_flag ck cks) op v (Normal v').
Proof.
  intros;
  induction cks; crush;
  match goal with
  | [H: do_flagged_checks_on_unop _ _ _ _ |- _] => inversion H; crush
  end;
  match goal with
  | [H: do_flagged_check_on_unop _ _ _ _ |- _] => inversion H; crush
  end;
  match goal with
  | [|- context[beq_check_flag _ Do_Overflow_Check]] => destruct (beq_check_flag ck Do_Overflow_Check); auto
  end;
  apply Do_Checks_Unop with (v':=v'0); crush.
Qed.

Lemma safe_remove_unop_check: forall cks op v v' ck v'',
  do_flagged_checks_on_unop cks op v v' ->
    do_flagged_check_on_unop ck op v (Normal v'') ->
      do_flagged_checks_on_unop (remove_check_flag ck cks) op v v'.
Proof.
  induction cks; crush;eauto;
  match goal with
  | [H: do_flagged_check_on_unop _ _ _ _ |- _] => inversion H; crush;eauto
  end;
  match goal with
  | [H: do_flagged_checks_on_unop _ _ _ _ |- _] => inversion H; crush;eauto
  end;
  match goal with
  | [H: do_flagged_check_on_unop ?a _ _ _ |- context[?a]] => destruct a; inversion H; crush;eauto
  end. 
  match goal with
  | [H1: Math.unary_minus _ = _, H2: Math.unary_minus _ = _ |- _] => rewrite H1 in H2; inversion H2; subst
  end;
  match goal with
  | [H1: do_overflow_check _ _, 
     H2: do_overflow_check _ _ |- _] => inversion H1; inversion H2; clear H1 H2; subst; apply_in_bound_unique
  end.
Qed .

Ltac apply_safe_remove_unop_check :=
  match goal with
  | [H1: do_flagged_checks_on_unop _ ?op ?v _,
     H2: do_flagged_check_on_unop _ ?op ?v (Normal _) |- _] => 
      specialize (safe_remove_unop_check _ _ _ _ _ _ H1 H2);
      let HZ := fresh "HZ" in intros HZ; inversion HZ
  end.



Lemma do_overflow_checks_reserve: forall v cks v' ck,
  in_bound v int32_bound true ->
    do_overflow_checks cks v v' ->  
      do_overflow_checks (remove_check_flag ck cks) v v'.
Proof.
  intros; inversion H0; crush;eauto;
  inversion H1; crush;eauto.
  repeat progress match goal with
  | [H: in_bound _ _ _ |- _] => inversion H; clear H; crush;eauto
  end.
  match goal with
  | [|- context[beq_check_flag _ Do_Overflow_Check]] => destruct (beq_check_flag ck Do_Overflow_Check); auto
  end;
  constructor.
Qed.

Lemma do_range_checks_reserve: forall cks v l u ck,
  do_range_checks cks v l u (Normal (Int v)) ->
    do_range_checks (remove_check_flag ck cks) v l u (Normal (Int v)).
Proof.
  intros; 
  inversion H; crush;eauto;
  match goal with
  | [|- context[beq_check_flag _ Do_Range_Check]] => destruct (beq_check_flag ck Do_Range_Check); auto
  end;
  constructor.
Qed.

Lemma do_range_check_same_result: forall e eBound rBound e' v l u,
  optimize_range_check e eBound rBound e' ->
    do_range_checks (exp_exterior_checks e) v l u (Normal (Int v)) ->
      do_range_checks (exp_exterior_checks e') v l u (Normal (Int v)).
Proof.
  intros;
  inversion H; crush;eauto;
  rewrite exp_updated_exterior_checks;
  apply do_range_checks_reserve; auto.
Qed.

Ltac apply_do_range_check_same_result :=
  match goal with
  | [H1: optimize_range_check ?e _ _ ?e',
     H2: do_range_checks (exp_exterior_checks ?e) _ _ _ (Normal _) |- _] =>
      specialize (do_range_check_same_result _ _ _ _ _ _ _ H1 H2);
      let HZ := fresh "HZ" in intros HZ
  end.

(********************************************************************)
(********************************************************************)

Lemma optimize_overflow_check_reserve: forall vBound cks retBound cks',
  sub_bound vBound int32_bound false ->
    optimize_overflow_check vBound cks (retBound, cks') ->
      cks = cks'.
Proof.
  intros;
  inversion H0; crush;eauto;
  apply_sub_bound_unique; crush;eauto.
Qed.

Ltac apply_optimize_overflow_check_reserve :=
  match goal with
  | [H1: sub_bound ?b _ false,
     H2: optimize_overflow_check ?b _ _ |- _] =>
      specialize ( optimize_overflow_check_reserve _ _ _ _ H1 H2);
      let HZ := fresh "HZ" in intros HZ
  end.

Lemma optimize_range_check_reserve: forall v vBound vBound' e e',
  in_bound v vBound true ->
    in_bound v vBound' false ->
      optimize_range_check e vBound vBound' e' ->
        e' = e.
Proof.
  intros;
  match goal with
  | [H: optimize_range_check _ _ _ _ |- _] => inversion H; crush;eauto
  end;
  match goal with
  | [H: sub_bound _ _ _ |- _] => inversion H; crush;eauto
  end;
  apply_In_Bound_Trans; crush;eauto;
  repeat progress match goal with
  | [H: in_bound _ _ _ |- _] => inversion H; clear H; crush;eauto
  end.
Qed.

Ltac apply_optimize_range_check_reserve :=
  match goal with
  | [H1: in_bound ?v ?eBound true,
     H2: in_bound ?v ?eBound' false,
     H3: optimize_range_check _ ?eBound ?eBound' _ |- _] =>
      specialize (optimize_range_check_reserve _ _ _ _ _ H1 H2 H3);
      let HZ := fresh "HZ" in intros HZ
  end.

Lemma optimize_range_check_on_copy_out_reserve: forall v vBound vBound' e e',
  in_bound v vBound true ->
    in_bound v vBound' false ->
      optimize_range_check_on_copy_out e vBound vBound' e' ->
        e' = e.
Proof.
  intros;
  match goal with
  | [H: optimize_range_check_on_copy_out _ _ _ _ |- _] => inversion H; crush;eauto
  end;
  match goal with
  | [H: sub_bound _ _ _ |- _] => inversion H; crush;eauto
  end;
  apply_In_Bound_Trans; crush;eauto;
  repeat progress match goal with
  | [H: in_bound _ _ _ |- _] => inversion H; clear H; crush;eauto
  end.
Qed.

Ltac apply_optimize_range_check_on_copy_out_reserve :=
  match goal with
  | [H1: in_bound ?v ?vBound true,
     H2: in_bound ?v ?vBound' false,
     H3: optimize_range_check_on_copy_out _ ?vBound ?vBound' _ |- _] =>
      specialize (optimize_range_check_on_copy_out_reserve _ _ _ _ _ H1 H2 H3);
      let HZ := fresh "HZ" in intros HZ
  end.

(********************************************************************)
(********************************************************************)

Lemma do_flagged_checks_on_binop_reserve: forall v1 v1Bound v2 v2Bound cks bound1 cks' op v,
  in_bound v1 v1Bound true ->
    in_bound v2 v2Bound true ->
      optimize_rtc_binop op v1Bound v2Bound cks (bound1, cks') ->
        do_flagged_checks_on_binop cks op (Int v1) (Int v2) v ->
          do_flagged_checks_on_binop cks' op (Int v1) (Int v2) v.
Proof.
  intros;
  match goal with
  | [H: do_flagged_checks_on_binop _ _ _ _ _ |- _] => inversion H; crush;eauto
  end.
- match goal with 
  | [H: optimize_rtc_binop _ _ _ _ _ |- _] => inversion H; clear H; crush;eauto
  end;
  match goal with
  | [H: optimize_overflow_check _ _ _ |- _] => inversion H; clear H; crush;eauto
  | _ => idtac
  end; constructor; auto.
- match goal with
  | [H: do_flagged_check_on_binop _ _ _ _ _ |- _] => inversion H; crush;eauto
  end;
  match goal with 
  | [H: optimize_rtc_binop _ _ _ _ _ |- _] => inversion H; clear H; crush;eauto
  end;
  try (constructor; auto);
  match goal with
  | [H: do_overflow_check _ _ |- _] => inversion H; subst
  | [H: do_division_check _ _ _ |- _] => inversion H; subst 
  end;
  [ apply_Sub_Bound_Plus_Compat |
    apply_Sub_Bound_Minus_Compat |
    apply_in_bound_value_neq_zero; crush;eauto
  ];
  apply_optimize_overflow_check_reserve; crush;eauto;
  constructor; auto.
- match goal with 
  | [H: optimize_rtc_binop _ _ _ _ _ |- _] => inversion H; clear H; crush;eauto
  end;
  match goal with
  | [H: optimize_overflow_check _ _ _ |- _] => inversion H; clear H; crush;eauto
  | _ => idtac
  end;
  try (apply Do_Checks_Binop with (v:=v); auto);
  destruct ck;
  match goal with
  | [H: do_flagged_check_on_binop _ _ _ _ _ |- _] => inversion H; crush;eauto
  end;
  try (apply_safe_remove_binop_check; crush;eauto);
  match goal with
  | [H: do_overflow_check _ _ |- _] => inversion H; crush;eauto
  end.
  (*1*)
  apply Do_Checks_Binop with (v:=(Int (v1 ÷ v2))); crush;eauto.
  apply safe_remove_binop_check with (v':=(Int (v1 ÷ v2))); crush;eauto.
  constructor. constructor; auto.
  apply_in_bound_value_neq_zero; crush;eauto.
  (*2*)
  match goal with
  | [H: do_flagged_check_on_binop _ Divide _ _ (Run_Time_Error _) |- _] => inversion H; subst
  end.
  match goal with
  | [H: Math.binary_operation Divide _ _ = _ |- _] =>  unfold Math.binary_operation in H; crush;eauto
  end.
  match goal with
  | [H1: do_overflow_check _ _, 
     H2: do_overflow_check _ _ |- _] => inversion H1; inversion H2; clear H1 H2; subst; apply_in_bound_unique
  end.
  match goal with
  | [H: do_division_check _ _ _ |- _] => inversion H; crush;eauto
  end.
  apply_in_bound_value_neq_zero; crush;eauto.
  (*3*)
  apply Do_Checks_Binop with (v:=(Int (v1 ÷ v2))); crush;eauto.
  apply safe_remove_binop_check with (v':=(Int (v1 ÷ v2))); crush;eauto.
  constructor. constructor; auto.
  apply_in_bound_value_neq_zero; crush;eauto.
Qed.

Ltac apply_do_flagged_checks_on_binop_reserve :=
  match goal with
  | [H1: in_bound ?v1 ?bound1 true,
     H2: in_bound ?v2 ?bound2 true,
     H3: optimize_rtc_binop _ ?bound1 ?bound2 _ _,
     H4: do_flagged_checks_on_binop _ _ (Int ?v1) (Int ?v2) _ |- _] =>
      specialize (do_flagged_checks_on_binop_reserve _ _ _ _ _ _ _ _ _ H1 H2 H3 H4);
      let HZ := fresh "HZ" in intros HZ
  end.

Lemma do_flagged_checks_on_unop_reserve: forall v vBound op cks bound1 cks' v',
  in_bound v vBound true ->
    optimize_rtc_unop op vBound cks (bound1, cks') ->
      do_flagged_checks_on_unop cks op (Int v) v' ->
        do_flagged_checks_on_unop cks' op (Int v) v'.
Proof.
  intros;
  match goal with
  | [H: do_flagged_checks_on_unop _ _ _ _ |- _] => inversion H; crush;eauto
  end.
- match goal with 
  | [H: optimize_rtc_unop _ _ _ _ |- _] => inversion H; clear H; crush;eauto
  end;
  match goal with
  | [H: optimize_overflow_check _ _ _ |- _] => inversion H; clear H; crush;eauto
  | _ => idtac
  end; constructor; auto.
- match goal with
  | [H: do_flagged_check_on_unop _ _ _ _ |- _] => inversion H; crush;eauto
  end;
  match goal with 
  | [H: optimize_rtc_unop _ _ _ _ |- _] => inversion H; clear H; crush;eauto
  end;
  match goal with
  | [H: optimize_overflow_check _ _ _ |- _] => inversion H; subst
  end;
  match goal with
  | [H: do_overflow_check _ _ |- _] => inversion H; subst
  end;
  [ apply_Sub_Bound_Unary_Minus_Compat; apply_sub_bound_unique |
    apply Do_Checks_Unop_RTE; auto
  ].
- match goal with 
  | [H: optimize_rtc_unop _ _ _ _ |- _] => inversion H; clear H; crush;eauto
  end;
  match goal with
  | [H: optimize_overflow_check _ _ _ |- _] => inversion H; clear H; crush;eauto
  end;
  destruct ck;
  match goal with
  | [H: do_flagged_check_on_unop _ _ _ _ |- _] => inversion H; crush;eauto
  end;
  apply_safe_remove_unop_check; crush;eauto.
Qed.

Ltac apply_do_flagged_checks_on_unop_reserve :=
  match goal with
  | [H1: in_bound ?v ?bound1 true,
     H2: optimize_rtc_unop _ ?bound1 _ _,
     H3: do_flagged_checks_on_unop _ _ (Int ?v) _ |- _] =>
      specialize (do_flagged_checks_on_unop_reserve _ _ _ _ _ _ _ H1 H2 H3);
      let HZ := fresh "HZ" in intros HZ
  end.

(********************************************************************)
(********************************************************************)

Lemma binop_arithm_in_bound: forall op v1 v2 v v1Bound v2Bound vBound in_cks,
  op = Plus \/ op = Minus \/ op = Multiply ->
  in_bound v1 v1Bound true ->
  in_bound v2 v2Bound true -> 
  do_flagged_checks_on_binop (Do_Overflow_Check :: nil) op (Int v1) (Int v2) (Normal (Int v)) ->
  optimize_rtc_binop op v1Bound v2Bound (Do_Overflow_Check :: nil) (vBound, in_cks) ->
  in_bound v vBound true.
Proof.
  intros.
  inversion H3; clear H3; subst; crush;eauto.
- inversion H12; clear H12; subst;
  inversion H2; clear H2; subst;
  inversion H5; clear H5; subst;
  inversion H11; clear H11; subst.
  + inversion H6; subst.
    Type In_Bound_Plus_Compat.
    specialize (In_Bound_Plus_Compat _ _ _ _ _ _ H0 H1); auto.
  + rewrite H7 in H2; inversion H2; subst.
    inversion H4; subst.
    inversion H7; subst.
    assumption.
- inversion H12; clear H12; subst;
  inversion H2; clear H2; subst;
  inversion H5; clear H5; subst;
  inversion H11; clear H11; subst.
  + inversion H6; subst.
    specialize (In_Bound_Minus_Compat _ _ _ _ _ _ H0 H1); auto.
  + rewrite H7 in H3; inversion H3; subst.
    inversion H4; subst.
    inversion H7; subst.
    assumption.
- inversion H2; clear H2; subst;
  inversion H5; clear H5; subst;
  inversion H10; clear H10; subst.
  rewrite H6 in H3; inversion H3; subst.
  inversion H4; subst.
  assumption.
Qed.

Ltac apply_binop_arithm_in_bound := 
  match goal with
  | [H1: ?op' = Plus \/ ?op' = Minus \/ ?op' = Multiply,
     H2: in_bound ?v1' ?bound1' true,
     H3: in_bound ?v2' ?bound2' true, 
     H4: do_flagged_checks_on_binop (Do_Overflow_Check :: nil) ?op' (Int ?v1') (Int ?v2') (Normal (Int _)),
     H5: optimize_rtc_binop ?op' ?bound1' ?bound2' (Do_Overflow_Check :: nil) _ |- _] =>
      specialize (binop_arithm_in_bound _ _ _ _ _ _ _ _ H1 H2 H3 H4 H5);
      let HZ := fresh "HZ" in intros HZ
  end.

Lemma unop_arithm_in_bound: forall v v' vBound vBound' in_cks,
  in_bound v vBound true ->
  do_flagged_checks_on_unop (Do_Overflow_Check :: nil) Unary_Minus (Int v) (Normal (Int v')) ->
  optimize_rtc_unop Unary_Minus vBound (Do_Overflow_Check :: nil) (vBound', in_cks) ->
  in_bound v' vBound' true.
Proof.
  intros. 
  inversion H0; clear H0; subst.
  inversion H4; clear H4; subst.
  inversion H8; clear H8; subst.
  unfold Math.unary_operation in H4.
  rewrite H4 in H0; inversion H0; subst.
  inversion H4; subst.
  
  inversion H1; clear H1; crush;eauto.
  inversion H10; crush;eauto.
- apply In_Bound_Unary_Minus_Compat; auto.
- inversion H2; crush;eauto.  
Qed.

Ltac apply_unop_arithm_in_bound :=
  match goal with
  | [H1: in_bound ?v ?bound true,
     H2: do_flagged_checks_on_unop (Do_Overflow_Check :: nil) Unary_Minus (Int ?v) (Normal (Int ?v')),
     H3: optimize_rtc_unop Unary_Minus ?bound (Do_Overflow_Check :: nil) _ |- _] =>
      specialize (unop_arithm_in_bound _ _ _ _ _ H1 H2 H3);
      let HZ := fresh "HZ" in intros HZ
  end.

(** * Checks Optimization for Literal *)

Lemma literal_checks_optimization_soundness: forall cks l v lBound cks',
  eval_literal_x cks l v ->
    optimize_literal_x l cks (lBound, cks') ->
      eval_literal_x cks' l v.
Proof.
  intros;
  inversion H; inversion H0; crush;eauto;
  constructor;
  match goal with
  | [H: optimize_overflow_check _ _ _ |- _] => inversion H; crush;eauto
  end;
  match goal with
  | [H: sub_bound _ _ _ |- _] => inversion H; clear H; crush;eauto
  end;
  specialize (do_overflow_checks_reserve _ _ _ Do_Overflow_Check H5 H1); auto.
Qed.

Ltac apply_literal_checks_optimization_soundness :=
  match goal with
  | [H1: eval_literal_x _ ?c _,
     H2: optimize_literal_x ?c _ _ |- _] => 
      specialize (literal_checks_optimization_soundness _ _ _ _ _ H1 H2); auto
  end.

(** * optimize_exp_ex_cks_stripped *)
Lemma optimize_exp_ex_cks_stripped: forall e e' st cks vBound,
  optimize_expression_x st (update_exterior_checks_exp e cks) (e', vBound) ->
    optimize_expression_x st e (update_exterior_checks_exp e' (exp_exterior_checks e), vBound).
Proof.
  apply (expression_x_ind
    (fun e: expression_x =>
       forall (e' : expression_x) (st : symboltable_x) (cks : exterior_checks) (vBound : bound),
      optimize_expression_x st (update_exterior_checks_exp e cks) (e', vBound) ->
      optimize_expression_x st e (update_exterior_checks_exp e' (exp_exterior_checks e), vBound))
    (fun n: name_x =>
       forall (n' : name_x) (st : symboltable_x) (cks : exterior_checks) (vBound : bound),
      optimize_name_x st (update_exterior_checks_name n cks) (n', vBound) ->
      optimize_name_x st n (update_exterior_checks_name n' (name_exterior_checks n), vBound))
    ); intros;
  match goal with
  | [H: optimize_expression_x _ _ _ |- _] => inversion H; subst
  | [H: optimize_name_x _ _ _ |- _] => inversion H; subst
  end.
- constructor; auto.
- constructor.
  specialize (H _ _ _ _ H3); auto.
- apply O_Binary_Operation_X with (e1Bound := e1Bound) (e2Bound := e2Bound); auto.
- apply O_Unary_Operation_X with (eBound := eBound); auto.
- apply O_Identifier_X with (t := t); auto.
- apply O_Indexed_Component_X with (xBound := xBound) (e' := e') (u := u) (v := v) 
                                   (t := t) (u' := u') (v' := v'); auto.
- apply O_Selected_Component_X with (x' := x') (xBound := xBound) (t := t); auto.
Qed.

Lemma optimize_name_ex_cks_stripped: forall n n' st cks vBound,
  optimize_name_x st (update_exterior_checks_name n cks) (n', vBound) ->
    optimize_name_x st n (update_exterior_checks_name n' (name_exterior_checks n), vBound).
Proof.
  induction n; intros; 
  inversion H; subst; simpl.
- apply O_Identifier_X with (t := t); auto.
- apply O_Indexed_Component_X with (xBound := xBound) (e':=e') (u:=u) (v:=v) (t:=t) (u':=u') (v':=v'); auto.
- apply O_Selected_Component_X with (x':=x') (xBound:=xBound) (t:=t); auto.
Qed.




