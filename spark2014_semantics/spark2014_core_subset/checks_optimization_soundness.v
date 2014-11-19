Require Export checks_optimization.
Require Export checks_generator.
Require Export well_typed.
(*
Require Export well_check_flagged.
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
  smack. (*omega*)
Qed.

Lemma Lt_Le_Bool_False: forall u v,
  (u < v)%Z ->
    Zle_bool v u = false.
Proof.
  intros;
  apply Zge_le_bool;
  unfold Zge_bool; unfold Zlt in H;
  smack.
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
  rewrite HZ1 in HZ; smack.
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
  rewrite Heqb2 in HZ; smack.
- specialize (Zge_cases v l); intros HZ;
  rewrite Heqb1 in HZ; smack.
- specialize (Zge_cases v l); intros HZ;
  rewrite Heqb1 in HZ; smack.  
Qed.









Lemma Zlele_Bool_Imp_LeLe_T: forall v l u,
  (Zle_bool l v) && (Zle_bool v u) = true ->
    (l <= v)%Z /\ (v <= u)%Z.
Proof.
  intros.
  specialize (andb_prop _ _ H); clear H; intros HZ.
  destruct HZ as [HZ1 HZ2].
  split.
- specialize (Zle_cases l v); intros HZ.
  rewrite HZ1 in HZ; smack.
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
  rewrite Heqb2 in HZ; smack.
- specialize (Zle_cases l v); intros HZ;
  rewrite Heqb1 in HZ; smack.
- specialize (Zle_cases l v); intros HZ;
  rewrite Heqb1 in HZ; smack.  
Qed.

(** l <= v <= u, l' <= l <= u', l' <= u <= u' => l' <= v <= u' *)
Lemma In_Bound_Trans: forall v l u l' u',
  in_bound v (Interval l u) true ->
    in_bound l (Interval l' u') true ->
      in_bound u (Interval l' u') true ->
        in_bound v (Interval l' u') true.
Proof.
  intros;
  repeat progress match goal with
  | [H: in_bound _ _ _ |- _] => inversion H; clear H; subst
  end;
  repeat progress match goal with
  | [H: _ && _ = true |- _] => specialize (Zlele_Bool_Imp_LeLe_T _ _ _ H); clear H; smack
  end;
  constructor; apply andb_true_iff; split.
- specialize (Zle_trans _ _ _ H2 H0); intros HZ1;
  specialize (Zle_imp_le_bool _ _ HZ1); auto.
- specialize (Zle_trans _ _ _ H1 H5); intros HZ1;
  specialize (Zle_imp_le_bool _ _ HZ1); auto.
Qed.

Ltac apply_In_Bound_Trans :=
  match goal with
  | [H1: in_bound ?v (Interval ?l ?u) true,
     H2: in_bound ?l _ true,
     H3: in_bound ?u _ true |- _ ] =>
      specialize (In_Bound_Trans _ _ _ _ _ H1 H2 H3);
      let HZ := fresh "HZ" in intros HZ
  end.

Lemma In_Bound_SubBound_Trans: forall v l u l' u',
  in_bound v (Interval l u) true ->
    sub_bound (Interval l u) (Interval l' u') true ->
      in_bound v (Interval l' u') true.
Proof.
  intros;
  inversion H0; subst;
  apply_In_Bound_Trans; auto.
Qed.

Ltac apply_In_Bound_SubBound_Trans :=
  match goal with
  | [H1: in_bound _ ?b true,
     H2: sub_bound ?b _ true |- _] =>
      specialize (In_Bound_SubBound_Trans _ _ _ _ _ H1 H2);
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
  | [H: _ && _ = true |- _] => specialize (Zlele_Bool_Imp_LeLe_T _ _ _ H); clear H; smack
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
  | [H: _ && _ = true |- _] => specialize (Zlele_Bool_Imp_LeLe_T _ _ _ H); clear H; smack
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

Lemma Sub_Bound_Plus_Compat: forall v1 l1 u1 v2 l2 u2 l u,
  in_bound v1 (Interval l1 u1) true ->
    in_bound v2 (Interval l2 u2) true ->
      in_bound (v1+v2) (Interval l u) false ->
        sub_bound (Interval (l1 + l2) (u1 + u2)) (Interval l u) false.
Proof.
  intros;
  repeat progress match goal with
  | [H: in_bound _ _ _ |- _] => inversion H; clear H; subst
  end;
  repeat progress match goal with
  | [H: _ && _ = true |- _] => specialize (Zlele_Bool_Imp_LeLe_T _ _ _ H); clear H; smack
  end;
  match goal with
  | [H: _ && _ = false |- _] => specialize (Zlele_Bool_Imp_LeLe_F _ _ _ H); clear H; smack
  end;
  constructor.
- specialize (Zplus_le_compat _ _ _ _ H0 H2); intros HZ1.
  specialize (Zle_lt_trans _ _ _ HZ1 H4); intros HZ2.
  left. constructor.
  apply andb_false_iff; left.
  apply Lt_Le_Bool_False; auto.
- specialize (Zplus_le_compat _ _ _ _ H1 H3); intros HZ1.
  specialize (Zlt_le_trans  _ _ _ H4 HZ1); intros HZ2.
  right; constructor.
  apply andb_false_iff; right.
  apply Lt_Le_Bool_False; auto.
Qed.

Ltac apply_Sub_Bound_Plus_Compat :=
  match goal with
  | [H1: in_bound ?v1 _ true,
     H2: in_bound ?v2 _ true,
     H3: in_bound (?v1+?v2) _ false |- _] => 
      specialize (Sub_Bound_Plus_Compat _ _ _ _ _ _ _ _ H1 H2 H3);
      let HZ := fresh "HZ" in intros HZ
  end.

Lemma Sub_Bound_Minus_Compat: forall v1 l1 u1 v2 l2 u2 l u,
  in_bound v1 (Interval l1 u1) true ->
    in_bound v2 (Interval l2 u2) true ->
      in_bound (v1-v2) (Interval l u) false ->
        sub_bound (Interval (l1 - u2) (u1 - l2)) (Interval l u) false.
Proof.
  intros;
  repeat progress match goal with
  | [H: in_bound _ _ _ |- _] => inversion H; clear H; subst
  end;
  repeat progress match goal with
  | [H: _ && _ = true |- _] => specialize (Zlele_Bool_Imp_LeLe_T _ _ _ H); clear H; smack
  end;
  match goal with
  | [H: _ && _ = false |- _] => specialize (Zlele_Bool_Imp_LeLe_F _ _ _ H); clear H; smack
  end;
  constructor.
- specialize (Le_Neg_Ge _ _ H3); intros HZ1;
  specialize (Zplus_le_compat _ _ _ _ H0 HZ1); intros HZ2;
  specialize (Zle_lt_trans _ _ _ HZ2 H4); intros HZ3;
  left; constructor;
  apply andb_false_iff; left;
  apply Lt_Le_Bool_False; auto.
- specialize (Le_Neg_Ge _ _ H2); intros HZ1;
  specialize (Zplus_le_compat _ _ _ _ H1 HZ1); intros HZ2;
  specialize (Zlt_le_trans  _ _ _ H4 HZ2); intros HZ3;
  right; constructor;
  apply andb_false_iff; right;
  apply Lt_Le_Bool_False; auto.
Qed.

Ltac apply_Sub_Bound_Minus_Compat :=
  match goal with
  | [H1: in_bound ?v1 _ true,
     H2: in_bound ?v2 _ true,
     H3: in_bound (?v1-?v2) _ false |- _] => 
      specialize (Sub_Bound_Minus_Compat _ _ _ _ _ _ _ _ H1 H2 H3);
      let HZ := fresh "HZ" in intros HZ
  end.

Lemma Sub_Bound_Unary_Minus_Compat: forall v l u l' u',
  in_bound v (Interval l u) true ->
    in_bound (- v) (Interval l' u') false ->
      sub_bound (Interval (- u) (- l)) (Interval l' u') false.
Proof.
  intros;
  repeat progress match goal with
  | [H: in_bound _ _ _ |- _] => inversion H; clear H; subst
  end;
 match goal with
  | [H: _ && _ = true |- _] => specialize (Zlele_Bool_Imp_LeLe_T _ _ _ H); clear H; smack
  end;
  match goal with
  | [H: _ && _ = false |- _] => specialize (Zlele_Bool_Imp_LeLe_F _ _ _ H); clear H; smack
  end;
  constructor;
  [left | right];
  constructor.
- apply andb_false_iff; left;
  specialize (Le_Neg_Ge _ _ H1); intros HZ1;
  specialize (Zle_lt_trans _ _ _ HZ1 H2); intros HZ2;
  apply Lt_Le_Bool_False; auto.
- apply andb_false_iff; right;
  specialize (Le_Neg_Ge _ _ H0); intros HZ1;
  specialize (Zlt_le_trans _ _ _ H2 HZ1); intros HZ2;
  apply Lt_Le_Bool_False; auto.
Qed.

Ltac apply_Sub_Bound_Unary_Minus_Compat :=
  match goal with
  | [H1: in_bound ?v _ true,
     H2: in_bound (- ?v) _ false |- _] =>
      specialize (Sub_Bound_Unary_Minus_Compat _ _ _ _ _ H1 H2);
      let HZ := fresh "HZ" in intros HZ
  end.

Lemma in_bound_value_neq_zero: forall v l u,
  in_bound v (Interval l u) true ->
    in_bound 0 (Interval l u) false ->
      Zeq_bool v 0 = false.
Proof.
  intros;
  repeat progress match goal with
  | [H: in_bound _ _ _ |- _] => inversion H; clear H; subst
  end;
  match goal with
  | [H: _ && _ = true |- _] => specialize (Zlele_Bool_Imp_LeLe_T _ _ _ H); clear H; smack
  end;
  match goal with
  | [H: _ && _ = false |- _] => specialize (Zlele_Bool_Imp_LeLe_F _ _ _ H); clear H; smack
  end;
  [ specialize (Zlt_le_trans _ _ _ H2 H0); intros HZ1 |
    specialize (Zle_lt_trans _ _ _ H1 H2); intros HZ1
  ];
  unfold Zeq_bool; 
  destruct v; smack.
Qed.

Ltac apply_in_bound_value_neq_zero :=
  match goal with
  | [H1: in_bound ?v ?b true,
     H2: in_bound 0 ?b false |- _] => 
      specialize (in_bound_value_neq_zero _ _ _ H1 H2);
      let HZ := fresh "HZ" in intros HZ
  end.

(*******************************************************************)

Lemma removed_check_flag_notin: forall ck cks cks',
 remove_check_flag ck cks = cks' ->
   ~(List.In ck cks').
Proof.
  induction cks; smack.
  remember (beq_check_flag ck a) as b;
  destruct b; smack.
  destruct ck; smack.
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
  induction cks; smack.
  remember (beq_check_flag ck a) as b;
  destruct b; smack.
  destruct a; destruct ck; smack.
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
  induction cks; smack.
  remember (beq_check_flag ck' a) as b;
  destruct b; smack.  
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
  induction cks; smack.
  remember (beq_check_flag ck' ck) as b; destruct b; smack.
  destruct ck; destruct ck'; smack.
  remember (beq_check_flag ck' a) as b; destruct b; smack.
Qed.

Ltac apply_check_flag_in_reserve2 :=
  match goal with
  | [ H1: beq_check_flag ?ck _ = false,
      H2: List.In ?ck _ |- _] =>
      specialize (check_flag_in_reserve2 _ _ _ H1 H2);
      let HZ := fresh "HZ" in intros HZ
  end.

(*******************************************************************)


Lemma in_bound_unique: forall v l u b1 b2,
  in_bound v (Interval l u) b1 ->
    in_bound v (Interval l u) b2 ->
      b1 = b2.
Proof.
  intros;
  inversion H; inversion H0; smack.
Qed. 

Ltac apply_in_bound_unique :=
  match goal with
  | [H1: in_bound ?v _ _,
     H2: in_bound ?v _ _ |- _] =>
      specialize (in_bound_unique _ _ _ _ _ H1 H2);
      let HZ := fresh "HZ" in intros HZ; inversion HZ
  end.

Lemma sub_bound_unique: forall bound1 bound2 b1 b2,
  sub_bound bound1 bound2 b1 ->
    sub_bound bound1 bound2 b2 ->
      b1 = b2.
Proof.
  intros;
  inversion H; inversion H0; smack;
  match goal with
  | [H1: in_bound ?v _ _,
     H2: in_bound ?v _ _ |- _] => 
      specialize (in_bound_unique _ _ _ _ _ H1 H2);
      let HZ := fresh "HZ" in intros HZ; inversion HZ
  end.
Qed.

Ltac apply_sub_bound_unique :=
  match goal with
  | [H1: sub_bound ?bound1 _ _,
     H2: sub_bound ?bound1 _ _ |- _] =>
      specialize (sub_bound_unique _ _ _ _ H1 H2);
      let HZ := fresh "HZ" in intros HZ; inversion HZ
  end.

Lemma extract_array_index_range_x_unique: forall st a l u l' u',
  extract_array_index_range_x st a (Range_X l u) ->
    extract_array_index_range_x st a (Range_X l' u') ->
      l = l' /\ u = u'.
Proof.
  intros.
  inversion H; inversion H0; subst.
  repeat progress match goal with
  | [H1: ?x = _, 
     H2: ?x = _ |- _] => rewrite H1 in H2; clear H1; inversion H2; subst
  end; auto.
Qed.

Ltac apply_extract_array_index_range_x_unique := 
  match goal with
  | [H1: extract_array_index_range_x _ ?a (Range_X ?l ?u),
     H2: extract_array_index_range_x _ ?a (Range_X ?l' ?u') |- _] => 
      specialize (extract_array_index_range_x_unique _ _ _ _ _ _ H1 H2);
      let HZ := fresh "HZ" in intros HZ; inversion HZ
  end.

Lemma extract_subtype_range_unique: forall st t l u l' u',
  extract_subtype_range_x st t (Range_X l u) ->
    extract_subtype_range_x st t (Range_X l' u') ->
      l = l' /\ u = u'.
Proof.
  intros;
  inversion H; inversion H0; smack.
Qed.

Ltac apply_extract_subtype_range_unique :=
  match goal with
  | [H1: extract_subtype_range_x _ ?t _, 
     H2: extract_subtype_range_x _ ?t _ |- _] => specialize (extract_subtype_range_unique _ _ _ _ _ _ H1 H2)
  end.

(*******************************************************************)

Lemma optimize_name_ast_num_eq: forall st n n' nBound,
  optimize_name_x st n (n', nBound) ->
    fetch_exp_type_x (name_astnum_x n) st = fetch_exp_type_x (name_astnum_x n') st.
Proof.
  intros;
  inversion H; smack.
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
  inversion H; smack;
  match goal with
  | [H: optimize_name_x _ _ _ |- _] => inversion H; smack
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
  inversion H; smack.
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
  apply eval_exp_with_any_exterior_checks; auto.
Qed.

Ltac apply_eval_expr_value_reserve :=
  match goal with
  | [H1: optimize_range_check ?e _ _ _,
     H2: eval_expr_x _ _ ?e _ |- _] =>
      specialize (eval_expr_value_reserve _ _ _ _ _ _ _ H1 H2);
      let HZ := fresh "HZ" in intros HZ; inversion HZ
  end.

(*******************************************************************)

Lemma remove_check_on_binop_reserve: forall cks op v1 v2 v ck,
  do_flagged_checks_on_binop cks op v1 v2 (Normal v) ->
    do_flagged_checks_on_binop (remove_check_flag ck cks) op v1 v2 (Normal v).
Proof.
  intros;
  induction cks; smack;
  match goal with
  | [H: do_flagged_checks_on_binop _ _ _ _ _ |- _] => inversion H; smack
  end;
  match goal with
  | [H: do_flagged_check_on_binop _ _ _ _ _ |- _] => inversion H; smack
  end;
  match goal with
  | [|- context[beq_check_flag _ Do_Overflow_Check]] => destruct (beq_check_flag ck Do_Overflow_Check); auto
  | [|- context[beq_check_flag _ Do_Division_Check]] => destruct (beq_check_flag ck Do_Division_Check); auto
  end;
  apply Do_Checks_Binop with (v:=v4); smack.
Qed.

Lemma safe_remove_binop_check: forall cks op v1 v2 v ck v',
  do_flagged_checks_on_binop cks op v1 v2 v ->
    do_flagged_check_on_binop ck op v1 v2 (Normal v') ->
      do_flagged_checks_on_binop (remove_check_flag ck cks) op v1 v2 v.
Proof.
  induction cks; smack;
  match goal with
  | [H: do_flagged_check_on_binop _ _ _ _ _ |- _] => inversion H; smack
  end;
  match goal with
  | [H: do_flagged_checks_on_binop _ _ _ _ _ |- _] => inversion H; smack
  end;
  match goal with
  | [H: do_flagged_check_on_binop ?a _ _ _ _ |- context[?a]] => destruct a; inversion H; smack
  end;
  match goal with
  | [H1: _ = _, H2: _ = _ |- _] => rewrite H1 in H2; inversion H2; smack
  | _ => idtac
  end;
  match goal with
  | [H1: do_overflow_check _ _, 
     H2: do_overflow_check _ _ |- _] => inversion H1; inversion H2; clear H1 H2; subst; apply_in_bound_unique
  | [H1: do_division_check _ _ _,
     H2: do_division_check _ _ _ |- _] => inversion H1; inversion H2; clear H1 H2; smack
  | _ => idtac
  end;
  solve
  [ apply Do_Checks_Binop_RTE; auto |
    apply Do_Checks_Binop with (v:=v5); smack |
    apply Do_Checks_Binop with (v:=v4); smack
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
  induction cks; smack;
  match goal with
  | [H: do_flagged_checks_on_unop _ _ _ _ |- _] => inversion H; smack
  end;
  match goal with
  | [H: do_flagged_check_on_unop _ _ _ _ |- _] => inversion H; smack
  end;
  match goal with
  | [|- context[beq_check_flag _ Do_Overflow_Check]] => destruct (beq_check_flag ck Do_Overflow_Check); auto
  end;
  apply Do_Checks_Unop with (v':=v'0); smack.
Qed.

Lemma safe_remove_unop_check: forall cks op v v' ck v'',
  do_flagged_checks_on_unop cks op v v' ->
    do_flagged_check_on_unop ck op v (Normal v'') ->
      do_flagged_checks_on_unop (remove_check_flag ck cks) op v v'.
Proof.
  induction cks; smack;
  match goal with
  | [H: do_flagged_check_on_unop _ _ _ _ |- _] => inversion H; smack
  end;
  match goal with
  | [H: do_flagged_checks_on_unop _ _ _ _ |- _] => inversion H; smack
  end;
  match goal with
  | [H: do_flagged_check_on_unop ?a _ _ _ |- context[?a]] => destruct a; inversion H; smack
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
  intros; inversion H0; smack;
  inversion H1; smack.
  repeat progress match goal with
  | [H: in_bound _ _ _ |- _] => inversion H; clear H; smack
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
  inversion H; smack;
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
  inversion H; smack;
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


(*******************************************************************)

Lemma optimize_overflow_check_reserve: forall l u cks retBound cks',
  sub_bound (Interval l u) int32_bound false ->
    optimize_overflow_check (Interval l u) cks (retBound, cks') ->
      cks = cks'.
Proof.
  intros;
  inversion H0; smack;
  specialize (sub_bound_unique _ _ _ _ H H5); smack.
Qed.

Ltac apply_optimize_overflow_check_reserve :=
  match goal with
  | [H1: sub_bound ?b _ false,
     H2: optimize_overflow_check ?b _ _ |- _] =>
      specialize ( optimize_overflow_check_reserve _ _ _ _ _ H1 H2);
      let HZ := fresh "HZ" in intros HZ
  end.

Lemma optimize_range_check_reserve: forall v l u l' u' e e',
  in_bound v (Interval l u) true ->
    in_bound v (Interval l' u') false ->
      optimize_range_check e (Interval l u) (Interval l' u') e' ->
        e' = e.
Proof.
  intros;
  match goal with
  | [H: optimize_range_check _ _ _ _ |- _] => inversion H; smack
  end;
  match goal with
  | [H: sub_bound _ _ _ |- _] => inversion H; smack
  end;
  specialize (In_Bound_Trans _ _ _ _ _ H H5 H8); smack;
  repeat progress match goal with
  | [H: in_bound _ _ _ |- _] => inversion H; clear H; smack
  end.
Qed.

Ltac apply_optimize_range_check_reserve :=
  match goal with
  | [H1: in_bound ?v (Interval ?l ?u) true,
     H2: in_bound ?v (Interval ?l' ?u') false,
     H3: optimize_range_check _ (Interval ?l ?u) (Interval ?l' ?u') _ |- _] =>
      specialize (optimize_range_check_reserve _ _ _ _ _ _ _ H1 H2 H3);
      let HZ := fresh "HZ" in intros HZ
  end.

Lemma optimize_range_check_on_copy_out_reserve: forall v l u l' u' e e',
  in_bound v (Interval l u) true ->
    in_bound v (Interval l' u') false ->
      optimize_range_check_on_copy_out e (Interval l u) (Interval l' u') e' ->
        e' = e.
Proof.
  intros;
  match goal with
  | [H: optimize_range_check_on_copy_out _ _ _ _ |- _] => inversion H; smack
  end;
  match goal with
  | [H: sub_bound _ _ _ |- _] => inversion H; smack
  end;
  specialize (In_Bound_Trans _ _ _ _ _ H H5 H8); smack;
  repeat progress match goal with
  | [H: in_bound _ _ _ |- _] => inversion H; clear H; smack
  end.
Qed.

Ltac apply_optimize_range_check_on_copy_out_reserve :=
  match goal with
  | [H1: in_bound ?v (Interval ?l ?u) true,
     H2: in_bound ?v (Interval ?l' ?u') false,
     H3: optimize_range_check_on_copy_out _ (Interval ?l ?u) (Interval ?l' ?u') _ |- _] =>
      specialize (optimize_range_check_on_copy_out_reserve _ _ _ _ _ _ _ H1 H2 H3);
      let HZ := fresh "HZ" in intros HZ
  end.


(*******************************************************************)

Lemma do_flagged_checks_on_binop_reserve: forall v1 l1 u1 v2 l2 u2 cks bound1 cks' op v,
  in_bound v1 (Interval l1 u1) true ->
    in_bound v2 (Interval l2 u2) true ->
      optimize_rtc_binop op (Interval l1 u1) (Interval l2 u2) cks (bound1, cks') ->
        do_flagged_checks_on_binop cks op (Int v1) (Int v2) v ->
          do_flagged_checks_on_binop cks' op (Int v1) (Int v2) v.
Proof.
  intros;
  match goal with
  | [H: do_flagged_checks_on_binop _ _ _ _ _ |- _] => inversion H; smack
  end.
- match goal with 
  | [H: optimize_rtc_binop _ _ _ _ _ |- _] => inversion H; clear H; smack
  end;
  match goal with
  | [H: optimize_overflow_check _ _ _ |- _] => inversion H; clear H; smack
  | _ => idtac
  end; constructor; auto.
- match goal with
  | [H: do_flagged_check_on_binop _ _ _ _ _ |- _] => inversion H; smack
  end;
  match goal with 
  | [H: optimize_rtc_binop _ _ _ _ _ |- _] => inversion H; clear H; smack
  end;
  try (constructor; auto);
  match goal with
  | [H: do_overflow_check _ _ |- _] => inversion H; subst
  | [H: do_division_check _ _ _ |- _] => inversion H; subst 
  end;
  [ apply_Sub_Bound_Plus_Compat |
    apply_Sub_Bound_Minus_Compat |
    apply_in_bound_value_neq_zero; smack
  ];
  apply_optimize_overflow_check_reserve; smack;
  constructor; auto.
- match goal with 
  | [H: optimize_rtc_binop _ _ _ _ _ |- _] => inversion H; clear H; smack
  end;
  match goal with
  | [H: optimize_overflow_check _ _ _ |- _] => inversion H; clear H; smack
  | _ => idtac
  end;
  try (apply Do_Checks_Binop with (v:=v); auto);
  destruct ck;
  match goal with
  | [H: do_flagged_check_on_binop _ _ _ _ _ |- _] => inversion H; smack
  end;
  try (apply_safe_remove_binop_check; smack);
  match goal with
  | [H: do_overflow_check _ _ |- _] => inversion H; smack
  end.
  (*1*)
  apply Do_Checks_Binop with (v:=(Int (v1 ÷ v2))); smack.
  apply safe_remove_binop_check with (v':=(Int (v1 ÷ v2))); smack.
  constructor. constructor; auto.
  apply in_bound_value_neq_zero with (l:=l2) (u:=u2); smack.
  (*2*)
  match goal with
  | [H: do_flagged_check_on_binop _ Divide _ _ (Run_Time_Error _) |- _] => inversion H; subst
  end.
  match goal with
  | [H: Math.binary_operation Divide _ _ = _ |- _] =>  unfold Math.binary_operation in H; smack
  end.
  match goal with
  | [H1: do_overflow_check _ _, 
     H2: do_overflow_check _ _ |- _] => inversion H1; inversion H2; clear H1 H2; subst; apply_in_bound_unique
  end.
  match goal with
  | [H: do_division_check _ _ _ |- _] => inversion H; smack
  end.
  apply_in_bound_value_neq_zero; smack.
  (*3*)
  apply Do_Checks_Binop with (v:=(Int (v1 ÷ v2))); smack.
  apply safe_remove_binop_check with (v':=(Int (v1 ÷ v2))); smack.
  constructor. constructor; auto.
  apply in_bound_value_neq_zero with (l:=l2) (u:=u2); smack.
Qed.

Ltac apply_do_flagged_checks_on_binop_reserve :=
  match goal with
  | [H1: in_bound ?v1 ?bound1 true,
     H2: in_bound ?v2 ?bound2 true,
     H3: optimize_rtc_binop _ ?bound1 ?bound2 _ _,
     H4: do_flagged_checks_on_binop _ _ (Int ?v1) (Int ?v2) _ |- _] =>
      specialize (do_flagged_checks_on_binop_reserve _ _ _ _ _ _ _ _ _ _ _ H1 H2 H3 H4);
      let HZ := fresh "HZ" in intros HZ
  end.

Lemma do_flagged_checks_on_unop_reserve: forall v l u op cks bound1 cks' v',
  in_bound v (Interval l u) true ->
    optimize_rtc_unop op (Interval l u) cks (bound1, cks') ->
      do_flagged_checks_on_unop cks op (Int v) v' ->
        do_flagged_checks_on_unop cks' op (Int v) v'.
Proof.
  intros;
  match goal with
  | [H: do_flagged_checks_on_unop _ _ _ _ |- _] => inversion H; smack
  end.
- match goal with 
  | [H: optimize_rtc_unop _ _ _ _ |- _] => inversion H; clear H; smack
  end;
  match goal with
  | [H: optimize_overflow_check _ _ _ |- _] => inversion H; clear H; smack
  | _ => idtac
  end; constructor; auto.
- match goal with
  | [H: do_flagged_check_on_unop _ _ _ _ |- _] => inversion H; smack
  end;
  match goal with 
  | [H: optimize_rtc_unop _ _ _ _ |- _] => inversion H; clear H; smack
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
  | [H: optimize_rtc_unop _ _ _ _ |- _] => inversion H; clear H; smack
  end;
  match goal with
  | [H: optimize_overflow_check _ _ _ |- _] => inversion H; clear H; smack
  end;
  destruct ck;
  match goal with
  | [H: do_flagged_check_on_unop _ _ _ _ |- _] => inversion H; smack
  end;
  apply_safe_remove_unop_check; smack.
Qed.

Ltac apply_do_flagged_checks_on_unop_reserve :=
  match goal with
  | [H1: in_bound ?v ?bound1 true,
     H2: optimize_rtc_unop _ ?bound1 _ _,
     H3: do_flagged_checks_on_unop _ _ (Int ?v) _ |- _] =>
      specialize (do_flagged_checks_on_unop_reserve _ _ _ _ _ _ _ _ H1 H2 H3);
      let HZ := fresh "HZ" in intros HZ
  end.


(*******************************************************************)

(** * Expression Value In Bound *)

Lemma eval_expr_value_in_bound: forall st s e v e' l u,
  eval_expr_x st s e (Normal (Int v)) ->
    optimize_expression_x st e (e', Interval l u) ->
      in_bound v (Interval l u) true.
Proof.
  admit.
Qed.

Ltac apply_eval_expr_value_in_bound :=
  match goal with
  | [H1: eval_expr_x _ _ ?e (Normal (Int ?v)),
     H2: optimize_expression_x _ ?e (?e', Interval ?l ?u) |- _] =>
      specialize (eval_expr_value_in_bound _ _ _ _ _ _ _ H1 H2);
      let HZ := fresh "HZ" in intros HZ
  end.


(** * Checks Optimization for Literal *)

Lemma literal_checks_optimization_soundness: forall cks l v lBound cks',
  eval_literal_x cks l v ->
    optimize_literal_x l cks (lBound, cks') ->
      eval_literal_x cks' l v.
Proof.
  intros;
  inversion H; inversion H0; smack;
  constructor;
  match goal with
  | [H: optimize_overflow_check _ _ _ |- _] => inversion H; smack
  end;
  match goal with
  | [H: sub_bound _ _ _ |- _] => inversion H; clear H; smack
  end;
  specialize (do_overflow_checks_reserve _ _ _ Do_Overflow_Check H5 H1); auto.
Qed.

(** * Checks Optimization for Expression *)

Lemma expression_checks_optimization_soundness: forall e e' st s v eBound,
  well_typed_stack st s ->
    eval_expr_x st s e v ->
      optimize_expression_x st e (e', eBound) ->
        eval_expr_x st s e' v.
Proof.
  apply (expression_x_ind
    (fun e: expression_x =>
       forall (e' : expression_x) (st : symboltable_x) (s : STACK.stack) (v : Return value) 
              (eBound : bound),
      well_typed_stack st s ->
      eval_expr_x st s e v ->
      optimize_expression_x st e (e', eBound) ->
      eval_expr_x st s e' v)
    (fun n: name_x =>
       forall (n' : name_x) (st : symboltable_x) (s : STACK.stack) (v : Return value) 
              (nBound : bound),
      well_typed_stack st s ->
      eval_name_x st s n v ->
      optimize_name_x st n (n', nBound) ->
      eval_name_x st s n' v)
    ); intros.
  - (** E_Literal_X *)
  match goal with
  | [H: optimize_expression_x ?st ?e ?e' |- _] => inversion H; clear H; subst
  end;
  match goal with
  | [H: eval_expr_x _ _ _ _ |- _] => inversion H; clear H; subst
  end;
  constructor; auto;
  match goal with
  | [H1: eval_literal_x _ ?c _,
     H2: optimize_literal_x ?c _ _ |- _] => 
      specialize (literal_checks_optimization_soundness _ _ _ _ _ H1 H2); auto
  end.
  - (** E_Name_X *)
  match goal with
  | [H: optimize_expression_x ?st ?e ?e' |- _] => inversion H; clear H; subst
  end;
  match goal with
  | [H: eval_expr_x _ _ _ _ |- _] => inversion H; clear H; subst
  end; constructor;
  match goal with
  | [H1: well_typed_stack _ _,
     H2: eval_name_x _ _ ?n _,
     H3: optimize_name_x _ ?n _ |- _] => specialize (H _ _ _ _ _ H1 H2 H3); auto
  end.
  - (** E_Binary_Operation_X *)
  match goal with
  | [H: optimize_expression_x ?st ?e ?e' |- _] => inversion H; clear H; subst
  end;
  match goal with
  | [H: eval_expr_x _ _ _ _ |- _] => inversion H; clear H; subst
  end;
  repeat progress match goal with
  | [H: forall (e' : expression_x) (st : symboltable_x) 
               (s : STACK.stack) (v : Return value) (eBound : bound),
      well_typed_stack _ _ ->
      eval_expr_x _ _ ?e _ ->
      optimize_expression_x _ ?e _ -> eval_expr_x _ _ _ _,
     H1: well_typed_stack _ _,
     H2: eval_expr_x _ _ ?e _,
     H3: optimize_expression_x _ ?e _ |- _] => specialize (H _ _ _ _ _ H1 H2 H3)
  end.
  + apply Eval_E_Binary_Operation_e1RTE_X; auto.
  + apply Eval_E_Binary_Operation_e2RTE_X with (v1:=v1); auto.
  + apply Eval_E_Binary_Operation_X with (v1:=v1) (v2:=v2); auto.
    match goal with
    | [H: optimize_rtc_binop _ _ _ _ _ |- _] => inversion H; smack
    end;
    (** Plus | Minus | Divide *)
    match goal with
    | [H: do_flagged_checks_on_binop _ _ _ _ _ |- _] => inversion H; smack
    end;
    match goal with
    | [H: do_flagged_check_on_binop _ _ _ _ _ |- _] => inversion H; smack
    | _ => idtac
    end;
    match goal with
    | [H: optimize_overflow_check _ _ _ |- _] => inversion H; smack
    | _ => idtac
    end;
    match goal with
    | [H: Math.add ?v1 ?v2 = _ |- _] => destruct v1, v2; smack
    | [H: Math.sub ?v1 ?v2 = _ |- _] => destruct v1, v2; smack
    | [H: Math.div ?v1 ?v2 = _ |- _] => destruct v1, v2; smack
    | _ => idtac
    end;
    repeat progress match goal with
    | [H1: eval_expr_x _ _ ?e _, 
       H2: optimize_expression_x _ ?e _ |- _] => 
        specialize (eval_expr_value_in_bound _ _ _ _ _ _ _ H1 H2); clear H1 H2; 
        let HZ := fresh "HZ" in intros HZ 
    end;
    apply_do_flagged_checks_on_binop_reserve; auto. 
  - (** E_Unary_Operation_X *)
  match goal with
  | [H: optimize_expression_x ?st ?e ?e' |- _] => inversion H; clear H; subst
  end;
  match goal with
  | [H: eval_expr_x _ _ _ _ |- _] => inversion H; clear H; subst
  end;
  match goal with
  | [H: forall (e' : expression_x) (st : symboltable_x) 
               (s : STACK.stack) (v : Return value) (eBound : bound),
      well_typed_stack _ _ ->
      eval_expr_x _ _ ?e _ ->
      optimize_expression_x _ ?e _ -> eval_expr_x _ _ _ _,
     H1: well_typed_stack _ _,
     H2: eval_expr_x _ _ ?e _,
     H3: optimize_expression_x _ ?e _ |- _] => specialize (H _ _ _ _ _ H1 H2 H3)
  end.
  + apply Eval_E_Unary_Operation_eRTE_X; auto.
  + apply Eval_E_Unary_Operation_X with (v:=v0); auto.
    match goal with
    | [H: optimize_rtc_unop _ _ _ _ |- _] => inversion H; smack
    end;
    match goal with
    | [H: do_flagged_checks_on_unop _ _ _ _ |- _] => inversion H; smack
    end;
    match goal with
    | [H: do_flagged_check_on_unop _ _ _ _ |- _] => inversion H; smack
    | _ => idtac
    end;
    match goal with
    | [H: optimize_overflow_check _ _ _ |- _] => inversion H; smack
    end;
    match goal with
    | [H: Math.unary_minus ?v = _ |- _] =>  destruct v; smack
    | _ => idtac
    end;
    repeat progress match goal with
    | [H1: eval_expr_x _ _ ?e _, 
       H2: optimize_expression_x _ ?e _ |- _] => 
        specialize (eval_expr_value_in_bound _ _ _ _ _ _ _ H1 H2); clear H1 H2; 
        let HZ := fresh "HZ" in intros HZ 
    end;
    apply_do_flagged_checks_on_unop_reserve; auto.     
  - (** E_Identifier_X *)
  match goal with
  | [H: optimize_name_x ?st ?n ?n' |- _] => inversion H; clear H; subst
  end;
  match goal with
  | [H: eval_name_x _ _ _ _ |- _] => inversion H; clear H; subst
  end;
  constructor; auto.
  - (** E_Indexed_Component_X *)
  match goal with
  | [H: optimize_name_x ?st ?n ?n' |- _] => inversion H; clear H; subst
  end;
  match goal with
  | [H: eval_name_x _ _ _ _ |- _] => inversion H; clear H; subst
  end;
  match goal with
  | [H: forall (n' : name_x) (st : symboltable_x) 
               (s : STACK.stack) (v : Return value) (eBound : bound),
      well_typed_stack _ _ ->
      eval_name_x _ _ ?n _ ->
      optimize_name_x _ ?n _ -> eval_name_x _ _ _ _,
     H1: well_typed_stack _ _,
     H2: eval_name_x _ _ ?n _,
     H3: optimize_name_x _ ?n _ |- _] => specialize (H _ _ _ _ _ H1 H2 H3)
  end;
  match goal with
  | [H: forall (e' : expression_x) (st : symboltable_x) 
               (s : STACK.stack) (v : Return value) (eBound : bound),
      well_typed_stack _ _ ->
      eval_expr_x _ _ ?e _ ->
      optimize_expression_x _ ?e _ -> eval_expr_x _ _ _ _,
     H1: well_typed_stack _ _,
     H2: eval_expr_x _ _ ?e _,
     H3: optimize_expression_x _ ?e _ |- _] => specialize (H _ _ _ _ _ H1 H2 H3)
  | _ => idtac
  end.
  + apply Eval_E_Indexed_Component_xRTE_X; auto.
  + apply Eval_E_Indexed_Component_eRTE_X with (a:=a0); auto.
    apply_eval_expr_value_reserve; smack.
  + apply Eval_E_Indexed_Component_Range_RTE_X with (a:=a0) (i:=i) (t:=t0) (l:=l) (u:=u0); auto.
    apply_eval_expr_value_reserve; smack.
    apply_optimize_name_ast_num_eq; smack.
    match goal with
    | [H1: fetch_exp_type_x _ _ = _ , H2: fetch_exp_type_x _ _ = _ |- _] => 
        rewrite H1 in H2; inversion H2; subst
    end;
    apply_extract_array_index_range_x_unique; smack.
    apply_optimize_exp_ex_cks_eq; rewrite <- HZ in H20.
    apply_eval_expr_value_in_bound.
    match goal with
    | [H: do_range_checks _ _ _ _ (Run_Time_Error RTE_Range) |- _] => inversion H; smack
    end;
    match goal with
    | [H: do_range_check _ _ _ (Run_Time_Error RTE_Range) |- _] => inversion H; smack
    end.
    apply_optimize_range_check_reserve; smack.
  + apply Eval_E_Indexed_Component_X with (a:=a0) (i:=i) (t:=t0) (l:=l) (u:=u0); auto.
    apply_eval_expr_value_reserve; smack.
    apply_optimize_name_ast_num_eq; smack.
    match goal with
    | [H1: fetch_exp_type_x _ _ = _ , H2: fetch_exp_type_x _ _ = _ |- _] => 
        rewrite H1 in H2; inversion H2; subst
    end;
    apply_extract_array_index_range_x_unique; smack.
    apply_optimize_exp_ex_cks_eq; rewrite <- HZ in H20.
    apply_do_range_check_same_result; auto.
  - (** E_Selected_Component_X *)
  match goal with
  | [H: optimize_name_x ?st ?n ?n' |- _] => inversion H; clear H; subst
  end;
  match goal with
  | [H: eval_name_x _ _ _ _ |- _] => inversion H; clear H; subst
  end;
  match goal with
  | [H: forall (n' : name_x) (st : symboltable_x) 
               (s : STACK.stack) (v : Return value) (eBound : bound),
      well_typed_stack _ _ ->
      eval_name_x _ _ ?n _ ->
      optimize_name_x _ ?n _ -> eval_name_x _ _ _ _,
     H1: well_typed_stack _ _,
     H2: eval_name_x _ _ ?n _,
     H3: optimize_name_x _ ?n _ |- _] => specialize (H _ _ _ _ _ H1 H2 H3)
  end.
  + apply Eval_E_Selected_Component_xRTE_X; auto.
  + apply Eval_E_Selected_Component_X with (r:=r); auto.
Qed.

Ltac apply_expression_checks_optimization_soundness :=
  match goal with
  | [H1: well_typed_stack _ _,
     H2: eval_expr_x _ _ ?e _,
     H3: optimize_expression_x _ ?e _ |- _] =>
      specialize (expression_checks_optimization_soundness _ _ _ _ _ _ H1 H2 H3);
      let HZ := fresh "HZ" in intros HZ
  end.


(** * Checks Optimization for Name *)

Lemma name_checks_optimization_soundness: forall n n' st s v nBound,
  well_typed_stack st s ->
    eval_name_x st s n v ->
      optimize_name_x st n (n', nBound) ->
        eval_name_x st s n' v.
Proof.
  induction n; intros.
- (** E_Identifier_X *)
  match goal with
  | [H: optimize_name_x ?st ?n ?n' |- _] => inversion H; clear H; subst
  end;
  match goal with
  | [H: eval_name_x _ _ _ _ |- _] => inversion H; clear H; subst
  end;
  constructor; auto.
- (** E_Indexed_Component_X *)
  match goal with
  | [H: optimize_name_x ?st ?n ?n' |- _] => inversion H; clear H; subst
  end;
  match goal with
  | [H: eval_name_x _ _ _ _ |- _] => inversion H; clear H; subst
  end;
  try (apply_expression_checks_optimization_soundness).   
  apply Eval_E_Indexed_Component_xRTE_X; smack.
  apply Eval_E_Indexed_Component_eRTE_X with (a:=a0); smack.
    apply_eval_expr_value_reserve; smack.

  apply Eval_E_Indexed_Component_Range_RTE_X with (a:=a0) (i:=i) (t:=t0) (l:=l) (u:=u0); smack.
    apply_eval_expr_value_reserve; smack.
    apply_optimize_name_ast_num_eq; smack.
    match goal with
    | [H1: fetch_exp_type_x _ _ = _ , H2: fetch_exp_type_x _ _ = _ |- _] => 
        rewrite H1 in H2; inversion H2; subst
    end;
    apply_extract_array_index_range_x_unique; smack.
    apply_optimize_exp_ex_cks_eq; rewrite <- HZ0 in H18.
    apply_eval_expr_value_in_bound.
    match goal with
    | [H: do_range_checks _ _ _ _ (Run_Time_Error RTE_Range) |- _] => inversion H; smack
    end;
    match goal with
    | [H: do_range_check _ _ _ (Run_Time_Error RTE_Range) |- _] => inversion H; smack
    end.
    apply_optimize_range_check_reserve; smack.

  apply Eval_E_Indexed_Component_X with (a:=a0) (i:=i) (t:=t0) (l:=l) (u:=u0); smack.
    apply_eval_expr_value_reserve; smack.
    apply_optimize_name_ast_num_eq; smack.
    match goal with
    | [H1: fetch_exp_type_x _ _ = _ , H2: fetch_exp_type_x _ _ = _ |- _] => 
        rewrite H1 in H2; inversion H2; subst
    end;
    apply_extract_array_index_range_x_unique; smack.
    apply_optimize_exp_ex_cks_eq; rewrite <- HZ0 in H18.
    apply_do_range_check_same_result; auto.
- (** E_Selected_Component_X *)
  match goal with
  | [H: optimize_name_x _ _ _ |- _] => inversion H; clear H; subst
  end;
  match goal with
  | [H: eval_name_x _ _ _ _ |- _] => inversion H; clear H; subst
  end;
  match goal with
  | [H: forall (n' : name_x) (st : symboltable_x) 
               (s : STACK.stack) (v : Return value) (eBound : bound),
      well_typed_stack _ _ ->
      eval_name_x _ _ ?n _ ->
      optimize_name_x _ ?n _ -> eval_name_x _ _ _ _,
     H1: well_typed_stack _ _,
     H2: eval_name_x _ _ ?n _,
     H3: optimize_name_x _ ?n _ |- _] => specialize (H _ _ _ _ _ H1 H2 H3)
  end.
  + apply Eval_E_Selected_Component_xRTE_X; auto.
  + apply Eval_E_Selected_Component_X with (r:=r); auto.
Qed.  
  
Ltac apply_name_checks_optimization_soundness :=
  match goal with
  | [H1: well_typed_stack _ _,
     H2: eval_name_x _ _ ?n _,
     H3: optimize_name_x _ ?n _ |- _] =>
      specialize (name_checks_optimization_soundness _ _ _ _ _ _ H1 H2 H3);
      let HZ := fresh "HZ" in intros HZ
  end.


(** * Checks Optimization for store update *)

Lemma store_update_optimization_soundness: forall st s x v s' x' v',
  well_typed_stack st s ->
    storeUpdate_x st s x v s' ->
      optimize_name_x st x (x', v') ->
        storeUpdate_x st s x' v s'.
Proof.
  intros st s x v s' x' v' H H0; revert x' v';
  match goal with
  | [H: storeUpdate_x _ _ _ _ _ |- _] => induction H; subst
  end; intros.
- (* 1 *)
  match goal with
  | [H: optimize_name_x _ _ _ |- _] => inversion H; smack
  end;
  constructor; auto.
- (* 2 *)
  match goal with
  | [H: optimize_name_x _ _ _ |- _] => inversion H; smack
  end;
  apply_name_checks_optimization_soundness.
  apply SU_Indexed_Component_xRTE_X; smack.  
- (* 3 *)
  match goal with
  | [H: optimize_name_x _ _ _ |- _] => inversion H; smack
  end;
  apply_name_checks_optimization_soundness;
  apply_expression_checks_optimization_soundness;
  apply SU_Indexed_Component_eRTE_X with (a:=a); smack;
  apply_eval_expr_value_reserve; smack.
- (* 4 *)
  match goal with
  | [H: optimize_name_x _ _ _ |- _] => inversion H; smack
  end;
  apply_name_checks_optimization_soundness;
  apply_expression_checks_optimization_soundness;
  match goal with
  | [H1: fetch_exp_type_x _ _ = _ , H2: fetch_exp_type_x _ _ = _ |- _] => 
      rewrite H1 in H2; inversion H2; subst
  end;
  apply_extract_array_index_range_x_unique; smack;
  apply_eval_expr_value_in_bound;
  apply SU_Indexed_Component_Range_RTE_X with (a:=a) (i:=i) (t:=t0) (l:=l) (u:=u); smack;
  solve[
    apply_eval_expr_value_reserve; smack |
    specialize (optimize_name_ast_num_eq _ _ _ _ H13); smack;
    apply_optimize_exp_ex_cks_eq; smack;
    match goal with
    | [H: do_range_checks _ _ _ _ _ |- _] => inversion H; smack
    end;
    match goal with
    | [H: do_range_check _ _ _ _ |- _] => inversion H; smack
    end;
    apply_optimize_range_check_reserve; smack
  ].
- (* 5 *)
  match goal with
  | [H: optimize_name_x _ _ _ |- _] => inversion H; smack
  end;
  apply_name_checks_optimization_soundness;
  apply_expression_checks_optimization_soundness;
  match goal with
  | [H1: fetch_exp_type_x _ _ = _ , H2: fetch_exp_type_x _ _ = _ |- _] => 
      rewrite H1 in H2; inversion H2; subst
  end;
  apply_extract_array_index_range_x_unique; smack;
  apply_eval_expr_value_in_bound;
  apply_optimize_exp_ex_cks_eq; smack;
  [ apply SU_Indexed_Component_X with 
      (arrObj:=(ArrayV a)) (a:=a) (i:=i) (l:=l) (u:=u) (t:=t0) (a1:=(updateIndexedComp a i v)); smack |
    apply SU_Indexed_Component_X with 
      (arrObj:=Undefined) (i:=i) (a:=nil) (l:=l) (u:=u) (t:=t0) (a1:=((i, v) :: nil)); smack
  ];
  solve [
    apply_eval_expr_value_reserve; smack |
    specialize (optimize_name_ast_num_eq _ _ _ _ H16); smack |
    match goal with
    | [H1: do_range_checks ?cks _ _ _ _, H2: _ = ?cks |- _] => 
        rewrite <- H2 in H1; apply_do_range_check_same_result; smack
    end
  ].
- (* 6 *)
  match goal with
  | [H: optimize_name_x _ _ _ |- _] => inversion H; smack
  end;
  apply_name_checks_optimization_soundness.
  apply SU_Selected_Component_xRTE_X; smack.
- (* 7 *)
  match goal with
  | [H: optimize_name_x _ _ _ |- _] => inversion H; smack
  end;
  apply_name_checks_optimization_soundness.
  
  apply SU_Selected_Component_X with 
    (recObj:=(RecordV r)) (r:=r) (r1:=(updateSelectedComp r f v)); smack.
  apply SU_Selected_Component_X with 
    (recObj:=Undefined) (r:=nil) (r1:=((f, v) :: nil)); smack.
Qed.


(** * Checks Optimization for Copy_In *)
Lemma copy_in_args_checks_optimization_soundness: forall st s params args f f' args',
  well_typed_stack st s ->
    copy_in_x st s f params args f' ->
      optimize_args_x st params args args' ->
        copy_in_x st s f params args' f'.
Proof.
  intros st s params; revert st s;
  induction params; smack.
- match goal with
  | [H: copy_in_x _ _ _ _ _ _ |- _] => inversion H; subst
  end;
  match goal with
  | [H: optimize_args_x _ _ _ _ |- _] => inversion H; subst
  end;
  constructor.
- destruct args, args';
  match goal with 
  | [H: copy_in_x _ _ _ (?a :: ?al) nil _ |- _] => inversion H
  | [H: optimize_args_x _ (?a :: ?al) (?e :: ?el) nil |- _] => inversion H
  | _ => idtac
  end.
  match goal with
  | [H: optimize_args_x _ (?a :: ?al) (?e :: ?el) (?e' :: ?el') |- _ ] => inversion H; subst
  end.
  + (* 1 *)
  match goal with
  | [H: copy_in_x _ _ _ (?a :: ?al) (?e :: ?el) _ |- _] => inversion H; subst
  end;
  match goal with
  | [H1: parameter_mode_x ?x = _,
     H2: parameter_mode_x ?x = _ |- _] => rewrite H1 in H2; inversion H2; clear H2
  end;
  [ apply Copy_In_Mode_In_eRTE_X; auto |
    apply Copy_In_Mode_In_NoRangeCheck_X with (v:=v) (f':=(STACK.push f (parameter_name_x a) v)); auto |
    apply Copy_In_Mode_In_Range_RTE_X with (v:=v) (l:=l) (u:=u); auto |
    apply Copy_In_Mode_In_Range_X with (v:=v) (l:=l) (u:=u) (f':=(STACK.push f (parameter_name_x a) (Int v))); auto
  ];
  solve [
    apply_expression_checks_optimization_soundness; auto |
    apply_optimize_exp_ex_cks_eq; smack |
    apply IHparams with (args := args); smack
  ].
  + (* 2 *)
  match goal with
  | [H: copy_in_x _ _ _ (?a :: ?al) (?e :: ?el) _ |- _] => inversion H; subst
  end;
  match goal with
  | [H1: parameter_mode_x ?x = _,
     H2: parameter_mode_x ?x = _ |- _] => rewrite H1 in H2; inversion H2; clear H2
  end;
  apply_expression_checks_optimization_soundness; auto.

  apply Copy_In_Mode_In_eRTE_X; smack.
    apply_eval_expr_value_reserve; smack.

  apply Copy_In_Mode_In_NoRangeCheck_X with (v:=v0) (f':=(STACK.push f (parameter_name_x a) v0)); smack.
    apply_eval_expr_value_reserve; smack.
    apply_optimize_exp_ex_cks_eq; smack.
      match goal with
      | [H: optimize_range_check _ _ _ _ |- _] => inversion H; smack
      end; apply exp_updated_exterior_checks.
 
  apply Copy_In_Mode_In_Range_RTE_X with (v:=v0) (l:=l) (u:=u0); smack.
    apply_eval_expr_value_reserve; smack.
    apply_optimize_exp_ex_cks_eq; smack.
    apply_eval_expr_value_in_bound.
    apply_extract_subtype_range_unique; smack;
      match goal with
     | [H: do_range_check _ _ _ _ |- _] => inversion H; subst
     end;
     apply_optimize_range_check_reserve; smack.
     
  match goal with
  | [H: optimize_range_check _ _ _ _ |- _] => inversion H; smack
  end;
  apply_optimize_exp_ex_cks_eq; smack.
  apply Copy_In_Mode_In_NoRangeCheck_X with (v:=Int v0) (f':=(STACK.push f (parameter_name_x a) (Int v0))); smack.
    apply eval_exp_with_any_exterior_checks; auto. 
    apply exp_updated_exterior_checks; auto.  
  apply Copy_In_Mode_In_Range_X with (v:=v0) (l:=l) (u:=u0) (f':=(STACK.push f (parameter_name_x a) (Int v0))); smack.
  + (* 3 *)
  match goal with
  | [H: copy_in_x _ _ _ (?a :: ?al) (?e :: ?el) _ |- _] => inversion H; subst
  end;
  match goal with
  | [H1: parameter_mode_x ?x = _,
     H2: parameter_mode_x ?x = _ |- _] => rewrite H1 in H2; inversion H2; clear H2
  end.
  apply Copy_In_Mode_Out_X with (f':=(STACK.push f (parameter_name_x a) Undefined)); smack.
  + (* 4 *)
  match goal with
  | [H: copy_in_x _ _ _ (?a :: ?al) (?e :: ?el) _ |- _] => inversion H; subst
  end;
  match goal with
  | [H1: parameter_mode_x ?x = _,
     H2: parameter_mode_x ?x = _ |- _] => rewrite H1 in H2; inversion H2; clear H2
  end.
  match goal with
  | [H: optimize_range_check _ _ _ _ |- _] => inversion H; smack
  end;
  apply Copy_In_Mode_Out_X with (f':=(STACK.push f (parameter_name_x a) Undefined)); smack.  
  + (* 5 *)
  match goal with
  | [H: copy_in_x _ _ _ (?a :: ?al) (?e :: ?el) _ |- _] => inversion H; subst
  end;
  match goal with
  | [H1: parameter_mode_x ?x = _,
     H2: parameter_mode_x ?x = _ |- _] => rewrite H1 in H2; inversion H2; clear H2
  end;
  apply_name_checks_optimization_soundness;
  [ apply Copy_In_Mode_InOut_eRTE_x; smack |
    apply Copy_In_Mode_InOut_NoRange_X with (v:=v) (f':=(STACK.push f (parameter_name_x a) v)); smack |
    apply Copy_In_Mode_InOut_Range_RTE_X with (v:=v) (l:=l) (u:=u); smack |
    apply Copy_In_Mode_InOut_Range_X with (v:=v) (l:=l) (u:=u) (f':=(STACK.push f (parameter_name_x a) (Int v))); smack
  ];
  apply_optimize_name_ex_cks_eq; smack.
  + (* 6 *)
  match goal with
  | [H: copy_in_x _ _ _ (?a :: ?al) (?e :: ?el) _ |- _] => inversion H; subst
  end;
  match goal with
  | [H1: parameter_mode_x ?x = _,
     H2: parameter_mode_x ?x = _ |- _] => rewrite H1 in H2; inversion H2; clear H2
  end;
  match goal with
  | [H: optimize_expression_x _ _ _ |- _] => inversion H; subst
  end;
  apply_name_checks_optimization_soundness.
  * 
  match goal with
  | [H: optimize_range_check _ _ _ _ |- _] => inversion H; smack
  end;
  match goal with
  | [H: optimize_range_check_on_copy_out _ _ _ _ |- _] => inversion H; smack
  end;
  apply Copy_In_Mode_InOut_eRTE_x; smack;
   repeat progress apply eval_name_with_any_exterior_checks; smack.
  *
  apply_optimize_name_ex_cks_eq; smack;
  match goal with
  | [H: optimize_range_check _ _ _ _ |- _] => inversion H; smack
  end;
  match goal with
  | [H: optimize_range_check_on_copy_out _ _ _ _ |- _] => inversion H; smack
  end;
  apply Copy_In_Mode_InOut_NoRange_X with (v:=v0) (f':=(STACK.push f (parameter_name_x a) v0)); smack;
   repeat progress apply eval_name_with_any_exterior_checks; smack;   
   match goal with
   | [H: List.In _ (name_exterior_checks _) |- _] => repeat progress rewrite name_updated_exterior_checks in H
   end;
   match goal with
   | [H: _ -> False |- False] => apply H
   end;
   remember (remove_check_flag Do_Range_Check (name_exterior_checks n)) as X. 
  
   assert(beq_check_flag Do_Range_Check Do_Range_Check_On_CopyOut = false). smack.
   apply_check_flag_in_reserve.     
   apply_removed_check_flag_notin; smack.
   
   apply_removed_check_flag_notin; smack.
   
   assert(beq_check_flag Do_Range_Check Do_Range_Check_On_CopyOut = false). smack.
   apply_check_flag_in_reserve; smack.
  * 
  assert(HA: eval_expr_x st s (E_Name_X ast_num n) (Normal (Int v0))). constructor; auto.
  apply_optimize_name_ex_cks_eq; smack;
  match goal with
  | [H: optimize_range_check _ _ _ _ |- _] => inversion H; smack
  end;
  match goal with
  | [H: optimize_range_check_on_copy_out _ _ _ _ |- _] => inversion H; smack
  end;
  apply_extract_subtype_range_unique; smack;
  apply Copy_In_Mode_InOut_Range_RTE_X with (v:=v0) (l:=l) (u:=u0); smack;
  repeat progress apply eval_name_with_any_exterior_checks; smack;
  repeat progress rewrite name_updated_exterior_checks;
  solve
  [ apply_eval_expr_value_in_bound; apply_In_Bound_SubBound_Trans;
    inversion H23; subst; apply_in_bound_unique; auto |
    apply check_flag_in_reserve2; smack
  ].
  * 
  apply_optimize_name_ex_cks_eq; smack;
  match goal with
  | [H: optimize_range_check _ _ _ _ |- _] => inversion H; smack
  end;
  match goal with
  | [H: optimize_range_check_on_copy_out _ _ _ _ |- _] => inversion H; smack
  end;
  apply_extract_subtype_range_unique; smack.
  
  
  apply Copy_In_Mode_InOut_NoRange_X with 
    (v:=Int v0) (f':=(STACK.push f (parameter_name_x a) (Int v0))); smack;
   repeat progress apply eval_name_with_any_exterior_checks; smack.
   match goal with
   | [H: List.In _ (name_exterior_checks _) |- _] => repeat progress rewrite name_updated_exterior_checks in H
   end;
   remember (remove_check_flag Do_Range_Check (name_exterior_checks n)) as X.  
   assert(HA: beq_check_flag Do_Range_Check Do_Range_Check_On_CopyOut = false). smack.
   apply_check_flag_in_reserve.
   apply_removed_check_flag_notin; smack.
   
   
   apply Copy_In_Mode_InOut_NoRange_X with 
    (v:=Int v0) (f':=(STACK.push f (parameter_name_x a) (Int v0))); smack;
   repeat progress apply eval_name_with_any_exterior_checks; smack.
   match goal with
   | [H: List.In _ (name_exterior_checks _) |- _] => repeat progress rewrite name_updated_exterior_checks in H
   end.
   remember (remove_check_flag Do_Range_Check (name_exterior_checks n)) as X. 
   apply_removed_check_flag_notin; smack.  
  
  apply Copy_In_Mode_InOut_Range_X with 
    (v:=v0) (l:=l) (u:=u0) (f':=(STACK.push f (parameter_name_x a) (Int v0))); smack;
  repeat progress apply eval_name_with_any_exterior_checks; smack;
  repeat progress rewrite name_updated_exterior_checks.
  assert(HA: beq_check_flag Do_Range_Check Do_Range_Check_On_CopyOut = false). smack.
  apply_check_flag_in_reserve2; auto.

  apply Copy_In_Mode_InOut_Range_X with 
    (v:=v0) (l:=l) (u:=u0) (f':=(STACK.push f (parameter_name_x a) (Int v0))); smack.
Qed.

Ltac apply_copy_in_args_checks_optimization_soundness :=
  match goal with
  | [H1: well_typed_stack _ _,
     H2: copy_in_x _ _ _ ?params ?args _,
     H3: optimize_args_x _ ?params ?args _ |- _] =>
      specialize (copy_in_args_checks_optimization_soundness _ _ _ _ _ _ H1 H2 H3);
      let HZ := fresh "HZ" in intros HZ
  end.


  
(** * Checks Optimization for Copy_Out *)
Lemma copy_out_args_checks_optimization_soundness: forall st s f params args s' args',
  well_typed_stack st s ->
    copy_out_x st s f params args s' ->
      optimize_args_x st params args args' ->
        copy_out_x st s f params args' s'.
Proof.
  intros st s f params; revert st s f;
  induction params; smack.
- match goal with
  | [H: copy_out_x _ _ _ _ _ _ |- _] => inversion H; subst
  end;
  match goal with
  | [H: optimize_args_x _ _ _ _ |- _] => inversion H; subst
  end;
  constructor.
- destruct args, args';
  match goal with
  | [H: copy_out_x _ _ _ (?a :: ?al) nil _ |- _] => inversion H
  | [H: optimize_args_x _ (?a :: ?al) (?e :: ?el) nil |- _] => inversion H
  | _ => idtac
  end;
  match goal with
  | [H: optimize_args_x _ (?a :: ?al) (?e :: ?el) (?e' :: ?el') |- _ ] => inversion H; subst
  end.
  + (* 1 *)
  match goal with
  | [H: copy_out_x _ _ _ (?a :: ?al) (?e :: ?el) _ |- _] => inversion H; smack
  end;
  apply Copy_Out_Mode_In_X; smack.
  + (* 2 *)
  match goal with
  | [H: copy_out_x _ _ _ (?a :: ?al) (?e :: ?el) _ |- _] => inversion H; smack
  end;
  apply Copy_Out_Mode_In_X; smack.
  + (* 3 *)
  match goal with
  | [H: copy_out_x _ _ _ (?a :: ?al) (?e :: ?el) _ |- _] => inversion H; subst
  end;
  match goal with
  | [H1: parameter_mode_x ?x = _,
     H2: parameter_mode_x ?x = _ |- _] => rewrite H1 in H2; inversion H2
  | _ => idtac
  end;
  apply_optimize_name_ex_cks_eq; smack.
  
  apply Copy_Out_Mode_Out_nRTE with (v:=v); smack.
  

  (* continue .... *)
  
  (* the value of variable x, should be in the bound of its type range;
     + E_Identifier ast_num x;
     + during Copy_Out, the value of parameter is compared with the type range of the 
       argument variable in copy_out_x, while in optimize_args_x, the type range of 
       the parameter compared with the type range of the argument variable; we have to
       make sure that the value of parameter should be fall within the type range of
       the argument; 
  *)



    apply_eval_expr_value_reserve; smack.
    apply_optimize_exp_ex_cks_eq; smack.
    apply_eval_expr_value_in_bound.
    apply_extract_subtype_range_unique; smack;

  + (* 4 *)

  + (* 5 *)

  + (* 6 *)


(** * Checks Optimization for Statement *)















(** * Help Lemmas for Checks Optimizations *)

Lemma remove_check_flag_unique: forall ck cks cks' cks'',
  remove_check_flag ck cks cks'  ->
    remove_check_flag ck cks cks'' ->
      cks' = cks''.
Proof.
  intros ck cks; revert ck;
  induction cks; smack.
- inversion H; inversion H0; auto.
- inversion H; inversion H0; smack.  
  specialize (IHcks _ _ _ H6 H12); smack.
Qed.

Ltac apply_remove_check_flag_unique :=
  match goal with
  | [H1: remove_check_flag ?ck ?cks _,
     H2: remove_check_flag ?ck ?cks _ |- _] => specialize (remove_check_flag_unique _ _ _ _ H1 H2)
  end.


Lemma removed_check_flag_notin: forall ck cks cks',
 remove_check_flag ck cks cks' ->
   ~(List.In ck cks').
Proof.
  intros.
  induction H; smack.
  destruct ck; inversion H.  
Qed.

Ltac apply_removed_check_flag_notin :=
  match goal with
  | [H: remove_check_flag ?ck ?cks ?cks' |- _] => specialize (removed_check_flag_notin _ _ _ H)
  end.


Lemma remove_notin_check_flag: forall ck cks,
  ~(List.In ck cks) ->
    remove_check_flag ck cks cks.
Proof.
  intros.
  induction cks.
  constructor.
  destruct a; destruct ck; smack;
  apply R_Check_Flag_Tail; smack.
Qed.

Ltac apply_remove_notin_check_flag :=
  match goal with
  | [H: ~(List.In ?ck ?cks) |- _] => specialize (remove_notin_check_flag _ _ H)
  | [H: List.In ?ck ?cks -> False |- _] => specialize (remove_notin_check_flag _ _ H)
  end.


Lemma remove_a_unique_check: forall cks cks1 ck cks2,
  cks = cks1 ++ ck :: cks2 ->
    ~(List.In ck (cks1 ++ cks2)) ->
      remove_check_flag ck cks (cks1 ++ cks2).
Proof.
  intros cks cks1; revert cks.  
  induction cks1; smack.
  constructor. 
  unfold beq_check_flag; destruct ck; auto.
  specialize (remove_notin_check_flag _ _ H0); auto.
  apply R_Check_Flag_Tail; smack.
  unfold beq_check_flag; destruct ck, a; smack.
Qed.

Ltac apply_remove_a_unique_check :=
  match goal with
  | [H1: ?cks = ?cks1 ++ ?ck :: ?cks2,
     H2: ~(List.In ?ck (?cks1 ++ ?cks2)) |- _] => specialize (remove_a_unique_check _ _ _ _ H1 H2)
  | [H1: ?cks = ?cks1 ++ ?ck :: ?cks2,
     H2: List.In ?ck (?cks1 ++ ?cks2) -> False |- _] => specialize (remove_a_unique_check _ _ _ _ H1 H2)
  end.


Lemma list_components_equal: forall ls1 (e: check_flag) ls2 ls1' ls2',
  ls1 ++ e :: ls2 = ls1' ++ e :: ls2' ->
  ~(List.In e (ls1 ++ ls2)) ->
  ls1 = ls1' /\ ls2 = ls2'.
Proof.
  intro ls1; induction ls1; intros.
- destruct ls1'. 
  + smack.
  + simpl in H. inversion H; subst; smack.
- destruct ls1'.
  + simpl in H; inversion H; subst; smack.
  + inversion H; subst.
    specialize (IHls1 _ _ _ _ H3).
    unfold List.In in H0; smack.
Qed.

Ltac apply_list_components_equal :=
  match goal with
  | [H1: ?ls1 ++ ?e :: ?ls2 = _ ++ ?e :: _, 
     H2: ~(List.In ?e (?ls1 ++ ?ls2)) |- _] => 
      specialize (list_components_equal _ _ _ _ _ H1 H2); 
      let HZ := fresh "HZ" in intros HZ; destruct HZ; subst 
  | [H1: ?ls1 ++ ?e :: ?ls2 = _ ++ ?e :: _, 
     H2: List.In ?e (?ls1 ++ ?ls2) -> False |- _] => 
      specialize (list_components_equal _ _ _ _ _ H1 H2); 
      let HZ := fresh "HZ" in intros HZ; destruct HZ; subst 
  end.


Lemma remove_split: forall ck cks1 cks2 cks,
  remove_check_flag ck (cks1 ++ cks2) cks ->
  exists cks1' cks2',
    remove_check_flag ck cks1 cks1' /\ 
    remove_check_flag ck cks2 cks2' /\
    cks = cks1' ++ cks2'.
Proof.
  intros ck cks1; revert ck;
  induction cks1; smack.
- exists (@nil check_flag) cks; smack.
  constructor.
- inversion H; smack;
  specialize (IHcks1 _ _ _ H5); smack.
  + exists x x0; smack.
    apply R_Check_Flag_Head; auto.
  + exists (a :: x) x0; smack.
    apply R_Check_Flag_Tail; auto.
Qed.

Ltac apply_remove_split :=
  match goal with
  | [H: remove_check_flag ?ck (?cks1 ++ ?cks2) ?cks |- _] => specialize (remove_split _ _ _ _ H)
  end.


Lemma remove_merge: forall ck cks1 cks1' cks2 cks2',
  remove_check_flag ck cks1 cks1' ->
    remove_check_flag ck cks2 cks2' ->
      remove_check_flag ck (cks1 ++ cks2) (cks1' ++ cks2').
Proof.
  intros ck cks1; revert ck;
  induction cks1; smack.
- inversion H; smack.
- inversion H; smack.
  apply R_Check_Flag_Head; auto.
  apply R_Check_Flag_Tail; auto.
Qed.

Ltac apply_remove_merge :=
  match goal with
  | [H1: remove_check_flag ?ck ?cks1 ?cks1',
     H2: remove_check_flag ?ck ?cks2 ?cks2' |- _] => specialize (remove_merge _ _ _ _ _ H1 H2)
  end.


Lemma notin_reserved_by_remove: forall ck cks ck' cks',
  ~(List.In ck cks) ->
    remove_check_flag ck' cks cks' ->
      ~(List.In ck cks').
Proof.
  intros ck cks; revert ck; 
  induction cks; smack.
- inversion H0; smack.
- inversion H0; smack.
Qed.

Ltac apply_notin_reserved_by_remove :=
  match goal with
  | [H1: ~(List.In ?ck ?cks),
     H2: remove_check_flag ?ck' ?cks ?cks' |- _] => specialize (notin_reserved_by_remove _ _ _ _ H1 H2)
  | [H1: List.In ?ck ?cks -> False,
     H2: remove_check_flag ?ck' ?cks ?cks' |- _] => specialize (notin_reserved_by_remove _ _ _ _ H1 H2)
  end.


Lemma in_reserved_by_remove: forall ck cks ck' cks',
  List.In ck cks ->
    beq_check_flag ck' ck = false ->
      remove_check_flag ck' cks cks' ->
        List.In ck cks'.
Proof.
  intros ck cks; revert ck;
  induction cks; intros; smack.
- inversion H1; smack.
- inversion H1; smack.
Qed.

Ltac apply_in_reserved_by_remove :=
  match goal with
  | [H1: List.In ?ck ?cks,
     H2: beq_check_flag ?ck' ?ck = false,
     H3: remove_check_flag ?ck' ?cks ?cks' |- _] => specialize (in_reserved_by_remove _ _ _ _ H1 H2 H3)
  end.


Lemma check_flag_notin_split: forall (ck: check_flag) cks1 cks2,
  ~(List.In ck (cks1 ++ cks2)) ->
    ~(List.In ck cks1) /\ ~(List.In ck cks2).
Proof.
  intros ck cks1; revert ck;
  induction cks1; smack.
Qed.

Ltac apply_check_flag_notin_split :=
  match goal with
  | [H: ~(List.In ?ck (?cks1 ++ ?cks2)) |- _] => specialize (check_flag_notin_split _ _ _ H)
  | [H: List.In ?ck (?cks1 ++ ?cks2) -> False |- _] => specialize (check_flag_notin_split _ _ _ H)
  end.


Lemma check_flag_notin_merge: forall (ck: check_flag) cks1 cks2,
  ~(List.In ck cks1) ->
    ~(List.In ck cks2) ->
      ~(List.In ck (cks1 ++ cks2)).
Proof.
  intros ck cks1; revert ck;
  induction cks1; smack.
Qed.

Ltac apply_check_flag_notin_merge :=
  match goal with
  | [H1: ~(List.In ?ck ?cks1),
     H2: ~(List.In ?ck ?cks2) |- _] => specialize (check_flag_notin_merge _ _ _ H1 H2)
  | [H1: List.In ?ck ?cks1 -> False,
     H2: List.In ?ck ?cks2 -> False |- _] => specialize (check_flag_notin_merge _ _ _ H1 H2)
  end.


(* /////////////////////////////////////////////////////// *)


(** for an expression updated with some new check flags, its resulting check flags should
    be the newly updated check flags;
 *)

Lemma update_exp_with_new_check_flags: forall e newCheckFlags, 
  exp_check_flags (update_exp_check_flags e newCheckFlags) = newCheckFlags.
Proof.
  intros.
  destruct e; auto.
  destruct n; auto.
Qed.

Lemma update_exp_with_same_check_flags: forall e, 
  update_exp_check_flags e (exp_check_flags e) = e.
Proof.
  intros.
  destruct e; auto.
  destruct n; auto.
Qed.

(** for a stand alone expression, which does not appear in any context such 
    as index of array, then it should have no Do_Range_Check flag;
*)
Lemma range_check_not_in_expr: forall e,
  well_check_flagged_expr e ->
    ~(List.In Do_Range_Check (exp_check_flags e)).
Proof.
  intros;
  destruct e; smack;
  match goal with
  | [H: well_check_flagged_expr _ |- _] => inversion H; clear H; smack
  end;
  match goal with
  | [H: well_check_flagged_name _ |- _] => inversion H; clear H; smack
  end.
Qed.

Ltac apply_range_check_not_in_expr := 
  match goal with
  | [H: well_check_flagged_expr ?e |- _] => specialize (range_check_not_in_expr _ H)
  end.


(* TODO: this can be removed and replaced by lemma: remove_notin_check_flag *)
Lemma rm_range_check_return_same_expr_checks: forall e,
  well_check_flagged_expr e ->
    remove_check_flag Do_Range_Check (exp_check_flags e) (exp_check_flags e).
Proof.
  intros.
  specialize (range_check_not_in_expr _ H); smack.
  apply remove_notin_check_flag; auto.
Qed.

Ltac apply_rm_range_check_return_same_expr_checks :=
  match goal with
  | [H: well_check_flagged_expr ?e |- _] => specialize (rm_range_check_return_same_expr_checks _ H)
  end.


(* TODO: this can be removed and replace with lemma: remove_a_unique_check  *)
(** if e is a run-time-check-annotated expression generated by our formalized 
    run-time check generator, then it should have at most one Do_Range_Check if
    there exists Do_Range_Check in expression e;
 *)
Lemma remove_range_check_property: forall e cks1 cks2,
  exp_check_flags e = cks1 ++ Do_Range_Check :: cks2 ->
    well_check_flagged_expr (update_exp_check_flags e (cks1 ++ cks2)) ->
      remove_check_flag Do_Range_Check (exp_check_flags e) (cks1 ++ cks2).
Proof.
  intros.
  specialize (range_check_not_in_expr _ H0); intro HZ.
  rewrite update_exp_with_new_check_flags in HZ.
  specialize (remove_a_unique_check _ _ _ _ H HZ); auto.
Qed.

Ltac apply_remove_range_check_property :=
  match goal with
  | [H1: exp_check_flags ?e = ?cks1 ++ ?ck :: ?cks2,
     H2: well_check_flagged_expr (update_exp_check_flags ?e (?cks1 ++ ?cks2)) |- _] =>
      specialize (remove_range_check_property _ _ _ H1 H2)
  end.


Lemma optimize_expression_reserve_notin: forall st e v e' ck,
  optimize_expression_x st e (v, e') ->
    ~(List.In ck (exp_check_flags e)) ->
      ~(List.In ck (exp_check_flags e')).
Proof.
  intros;
  inversion H; subst; simpl in *; auto;
  match goal with
  | [H: optimize_name_x _ _ _ |- _] => inversion H4; subst; smack
  | _ => idtac
  end;
  match goal with
  | [H1: ~(List.In ?ck ?cks), 
     H2: remove_check_flag _ ?cks ?cks' |- _] => specialize (notin_reserved_by_remove _ _ _ _ H1 H2); auto
  end.  
Qed.

Ltac apply_optimize_expression_reserve_notin := 
  match goal with
  | [H1: optimize_expression_x _ ?e (_, ?e'), 
     H2: ~(List.In ?ck (exp_check_flags ?e)) |- _] => specialize (optimize_expression_reserve_notin _ _ _ _ _ H1 H2)
  | [H1: optimize_expression_x _ ?e (_, ?e'), 
     H2: List.In ?ck (exp_check_flags ?e) -> False |- _] => specialize (optimize_expression_reserve_notin _ _ _ _ _ H1 H2)
  end.


Lemma extract_subtype_range_unique: forall st t l u l' u',
  extract_subtype_range_x st t (Range_X l u) ->
    extract_subtype_range_x st t (Range_X l' u') ->
      l = l' /\ u = u'.
Proof.
  intros;
  inversion H; inversion H0; smack.
Qed.

Ltac apply_extract_subtype_range_unique :=
  match goal with
  | [H1: extract_subtype_range_x _ ?t (Range_X ?l ?u), 
     H2: extract_subtype_range_x _ ?t (Range_X ?l' ?u') |- _] => specialize (extract_subtype_range_unique _ _ _ _ _ _ H1 H2)
  end.

(** the following lemma is used to prove soundness of statement checks optimization *)
Lemma optimized_name_reserve_astnum: forall st x v' x',
  optimize_name_x st x (v', x') ->
    name_astnum_x x = name_astnum_x x'.
Proof.
  intros;
  inversion H; smack.
Qed.

Ltac apply_optimized_name_reserve_astnum :=
  match goal with
  | [H: optimize_name_x _ ?x (?v, ?x') |- _] => specialize (optimized_name_reserve_astnum _ _ _ _ H)
  end.


Lemma optimize_expression_reserve_range_check: forall e cks1 cks2 st v' e',
  exp_check_flags e = cks1 ++ Do_Range_Check :: cks2 ->
    optimize_expression_x st e (v', e') ->
      exists cks1' cks2',
      exp_check_flags e' = cks1' ++ Do_Range_Check :: cks2'.
Proof.
  intros e cks1; revert e;
  induction cks1; smack.
- match goal with
  | [H: optimize_expression_x _ _ _ |- _] => inversion H; subst; auto
  end;
  simpl in *; subst; exists (@nil check_flag);
  match goal with
  | [H: remove_check_flag _ _ _ |- _] => inversion H; smack
  | _ => idtac
  end; smack.
  match goal with
  | [H: optimize_name_x _ _ _ |- _] => inversion H; subst; simpl in *
  end; smack.
- match goal with
  | [H: optimize_expression_x _ _ _ |- _] => inversion H; subst; auto
  end;
  simpl in *; subst;
  match goal with
  | [|- exists cks1' cks2', ?x :: ?cks1 ++ ?ck :: ?cks2 = cks1' ++ ?ck :: cks2'] => exists (x :: cks1) cks2; auto
  | _ => idtac
  end.
  + (* name *)
    match goal with
    | [H: optimize_name_x _ _ _ |- _] => inversion H; subst; simpl in *; subst
    end;
    match goal with
    | [|- exists cks1' cks2', ?x :: ?cks1 ++ ?ck :: ?cks2 = cks1' ++ ?ck :: cks2'] => exists (x :: cks1) cks2; auto
    | _ => idtac
    end.
  + (* Plus *)  
    match goal with
    | [H: remove_check_flag _ ?cks _ |- _] => inversion H; subst
    end;
    match goal with
    | [H: remove_check_flag _ ?cks _ |- _] => specialize (remove_split _ _ _ _ H); smack
    end;
    match goal with
    | [H: remove_check_flag Do_Overflow_Check (Do_Range_Check :: ?cks) _ |- _] => inversion H; smack
    end;
    match goal with
    | [|- exists cks1' cks2', ?x :: ?cks1 ++ ?ck :: ?cks2 = cks1' ++ ?ck :: cks2'] => exists (x :: cks1) cks2; auto
    end.
  + (* Minus *)
    match goal with
    | [H: remove_check_flag _ ?cks _ |- _] => inversion H; subst
    end;
    match goal with
    | [H: remove_check_flag _ ?cks _ |- _] => specialize (remove_split _ _ _ _ H); smack
    end;
    match goal with
    | [H: remove_check_flag Do_Overflow_Check (Do_Range_Check :: ?cks) _ |- _] => inversion H; smack
    end;
    match goal with
    | [|- exists cks1' cks2', ?x :: ?cks1 ++ ?ck :: ?cks2 = cks1' ++ ?ck :: cks2'] => exists (x :: cks1) cks2; auto
    end.
  + (* Unary_Minus *)
    match goal with
    | [H: remove_check_flag _ ?cks _ |- _] => inversion H; subst
    end;
    match goal with
    | [H: remove_check_flag _ ?cks _ |- _] => specialize (remove_split _ _ _ _ H); smack
    end;
    match goal with
    | [H: remove_check_flag Do_Overflow_Check (Do_Range_Check :: ?cks) _ |- _] => inversion H; smack
    end;
    match goal with
    | [|- exists cks1' cks2', ?x :: ?cks1 ++ ?ck :: ?cks2 = cks1' ++ ?ck :: cks2'] => exists (x :: cks1) cks2; auto
    end.
Qed.

Ltac apply_optimize_expression_reserve_range_check :=
  match goal with
  | [H1: exp_check_flags ?e = ?cks1 ++ ?ck :: ?cks2,
     H2: optimize_expression_x _ ?e (?v, ?e') |- _] => specialize (optimize_expression_reserve_range_check _ _ _ _ _ _ H1 H2)
  end.


Lemma optimize_expression_range_check_notin: forall e cks1 cks2 st v' e' cks1' cks2',
  exp_check_flags e = cks1 ++ Do_Range_Check :: cks2 ->
    optimize_expression_x st e (v', e') ->
      exp_check_flags e' = cks1' ++ Do_Range_Check :: cks2' ->
        ~(List.In Do_Range_Check (cks1 ++ cks2)) ->
          ~(List.In Do_Range_Check (cks1' ++ cks2')).
Proof.
  intros.
  inversion H0; subst;
  repeat progress match goal with
  | [H: exp_check_flags _ = _ |- _] => simpl in H
  end;
  match goal with
  | [H1: ?x = _, H2: ?x = _ |- _] => rewrite H1 in H2; auto
  | _ => idtac
  end;
  match goal with
  | [H0: optimize_expression_x _ (_ _ _ ?ck) (_, (_ _ _ ?ck)),
     H1: ?ls1 ++ ?e :: ?ls2 = ?ls1' ++ ?e :: ?ls2',
     H2: ~(List.In ?e (?ls1 ++ ?ls2)) |- _ ] => 
      specialize (list_components_equal _ _ _ _ _ H1 H2); smack
  | [H0: optimize_expression_x _ (_ _ _ ?ck) (_, (_ _ _ ?ck)),
     H1: ?ls1' ++ ?e :: ?ls2' = ?ls1 ++ ?e :: ?ls2,
     H2: ~(List.In ?e (?ls1 ++ ?ls2)) |- _ ] => 
      symmetry in H1; specialize (list_components_equal _ _ _ _ _ H1 H2); smack
  | _ => idtac
  end.
- (* name *)
  inversion H0; subst.
  destruct n; inversion H5; subst;
  repeat progress match goal with
  | [H: name_check_flags _ = _ |- _] => simpl in H
  end;
  match goal with
  | [H1: ?x = _, H2: ?x = _ |- _] => rewrite H1 in H2; auto
  | _ => idtac
  end;
  match goal with
  | [H1: ?ls1 ++ ?e :: ?ls2 = ?ls1' ++ ?e :: ?ls2',
     H2: ~(List.In ?e (?ls1 ++ ?ls2)) |- _ ] => 
      specialize (list_components_equal _ _ _ _ _ H1 H2); smack
  | [H1: ?ls1' ++ ?e :: ?ls2' = ?ls1 ++ ?e :: ?ls2,
     H2: ~(List.In ?e (?ls1 ++ ?ls2)) |- _ ] => 
      symmetry in H1; specialize (list_components_equal _ _ _ _ _ H1 H2); smack
  | _ => idtac
  end.
- (* Plus *)
  match goal with
  | [H1: remove_check_flag _ ?cks _, 
     H2: ?cks = _ |- _] => rewrite H2 in H1; specialize (remove_split _ _ _ _ H1); smack
  end;
  inversion H; smack;
  match goal with
  | [H: List.In _ (?ls1 ++ ?ls2) -> False |- _] => 
      specialize (check_flag_notin_split _ _ _ H); smack
  end;
  repeat progress match goal with
  | [H1: List.In _ ?ls -> False,
     H2: remove_check_flag _ ?ls _ |- _] =>
      specialize (notin_reserved_by_remove _ _ _ _ H1 H2); clear H1; smack
  end.
  specialize (check_flag_notin_merge _ _ _ H9 H3); intros HZ.
  symmetry in H8;
  specialize (list_components_equal _ _ _ _ _ H8 HZ); smack.
- (* Minus *)
  match goal with
  | [H1: remove_check_flag _ ?cks _, 
     H2: ?cks = _ |- _] => rewrite H2 in H1; specialize (remove_split _ _ _ _ H1); smack
  end.
  inversion H; smack.
  match goal with
  | [H: List.In _ (?ls1 ++ ?ls2) -> False |- _] => 
      specialize (check_flag_notin_split _ _ _ H); smack
  end.
  repeat progress match goal with
  | [H1: List.In _ ?ls -> False,
     H2: remove_check_flag _ ?ls _ |- _] =>
      specialize (notin_reserved_by_remove _ _ _ _ H1 H2); clear H1; smack
  end.
  specialize (check_flag_notin_merge _ _ _ H9 H3); intros HZ.
  symmetry in H8;
  specialize (list_components_equal _ _ _ _ _ H8 HZ); smack.
- (* Unary_Minus *)
  match goal with
  | [H1: remove_check_flag _ ?cks _, 
     H2: ?cks = _ |- _] => rewrite H2 in H1; specialize (remove_split _ _ _ _ H1); smack
  end.
  inversion H; smack.
  match goal with
  | [H: List.In _ (?ls1 ++ ?ls2) -> False |- _] => 
      specialize (check_flag_notin_split _ _ _ H); smack
  end.
  repeat progress match goal with
  | [H1: List.In _ ?ls -> False,
     H2: remove_check_flag _ ?ls _ |- _] =>
      specialize (notin_reserved_by_remove _ _ _ _ H1 H2); clear H1; smack
  end.
  specialize (check_flag_notin_merge _ _ _ H7 H3); intros HZ.
  symmetry in H6;
  specialize (list_components_equal _ _ _ _ _ H6 HZ); smack.
Qed.

Ltac apply_optimize_expression_range_check_notin :=
  match goal with
  | [H1: exp_check_flags ?e = ?cks1 ++ ?ck :: ?cks2,
     H2: optimize_expression_x _ ?e (_, ?e'),
     H3: exp_check_flags ?e' = ?cks1' ++ ?ck :: ?cks2',
     H4: ~(List.In ?ck (?cks1 ++ ?cks2)) |- _] => 
      specialize (optimize_expression_range_check_notin _ _ _ _ _ _ _ _ H1 H2 H3 H4)
  | [H1: exp_check_flags ?e = ?cks1 ++ ?ck :: ?cks2,
     H2: optimize_expression_x _ ?e (_, ?e'),
     H3: exp_check_flags ?e' = ?cks1' ++ ?ck :: ?cks2',
     H4: List.In ?ck (?cks1 ++ ?cks2) -> False |- _] => 
      specialize (optimize_expression_range_check_notin _ _ _ _ _ _ _ _ H1 H2 H3 H4)
  end.


(** The way to first optimize the expression and then remove Do_Range_Check from 
    the expression, its resulting expression should be the same as the expression 
    optimized in the reverse way: that's, first remove its Do_Range_Check and then
    optimize the expression;
*)

Lemma optimize_expr_to_same_checkflags: forall st e v e' checkflags cks1 cks2,
  optimize_expression_x st e (v, e') ->
    remove_check_flag Do_Range_Check (exp_check_flags e') checkflags ->
      (* two properties for expression e *)
      exp_check_flags e = cks1 ++ Do_Range_Check :: cks2 ->
        well_check_flagged_expr (update_exp_check_flags e (cks1 ++ cks2)) ->
          optimize_expression_x st (update_exp_check_flags e (cks1 ++ cks2)) 
                                   (v, (update_exp_check_flags e' checkflags)).
Proof.
  intros.
  match goal with
  | [H1: exp_check_flags ?e = _,
     H2: optimize_expression_x _ ?e _ |- _] => 
      specialize (optimize_expression_reserve_range_check _ _ _ _ _ _ H1 H2);
      intros HZ; destruct HZ as [ cks1' [cks2' HE]]
  end.
  match goal with
  | [H: well_check_flagged_expr ?e |- _] => specialize (range_check_not_in_expr _ H); intros HZ1
  end.
  rewrite update_exp_with_new_check_flags in HZ1.  
  match goal with
  | [H1: exp_check_flags ?e = _,
     H2: optimize_expression_x _ ?e (_, ?e'), 
     H3: exp_check_flags ?e' = _, 
     H4: ~(List.In _ _) |- _] => 
      specialize (optimize_expression_range_check_notin _ _ _ _ _ _ _ _ H1 H2 H3 H4); intros HZ2
  end.
  specialize (remove_a_unique_check _ _ _ _ HE HZ2); intros HZ3.
  specialize (remove_check_flag_unique _ _ _ _ H0 HZ3); intros HZ4.
  
  inversion H; smack;
  match goal with
  | [H1: ?ls1 ++ ?e :: ?ls2 = ?ls1' ++ ?e :: ?ls2',
     H2: List.In ?e (?ls1 ++ ?ls2) -> False |- _] => specialize (list_components_equal _ _ _ _ _ H1 H2); smack
  | _ => idtac
  end.
- (* Literal *)
  constructor; auto.
- (* Name *)
  constructor; auto.
  match goal with
  | [H: optimize_name_x _ _ _ |- _] => inversion H; subst
  end;
  repeat progress match goal with
  | [H: name_check_flags _ = _ |- _] => simpl in H; subst
  end;
  match goal with
  | [H1: ?ls1 ++ ?e :: ?ls2 = ?ls1' ++ ?e :: ?ls2',
     H2: List.In ?e (?ls1 ++ ?ls2) -> False |- _] => specialize (list_components_equal _ _ _ _ _ H1 H2); smack
  end.
  apply O_Identifier_X with (t:=t); auto.
  apply O_Indexed_Component_Range_Pass_X with (l:=l) (u:=u) (e':=e') (t:=t) (l':=l') 
                                               (u':=u') (checkflags':=checkflags'); auto.
  apply O_Indexed_Component_Range_Fail_X with (l:=l) (u:=u) (e':=e') (t:=t) (l':=l') (u':=u'); auto.
  apply O_Indexed_Component_Range_Fail_X with (l:=l) (u:=u) (e':=e') (t:=t) (l':=l') (u':=u'); auto.
  apply O_Selected_Component_X with (t:=t); auto.
- (* Binary Operation Plus - overflow check pass *)
  apply O_Binary_Plus_Operation_Overflow_Pass_X; auto.
  
  specialize (remove_split _ _ _ _ H11); intros HZ;
  destruct HZ as [cks1'0 [cks2'0 HZ5]]. destruct HZ5 as [HZ5 [HZ6 HZ7]].
  inversion HZ6; smack.
  match goal with
  | [H1: ?ls1 ++ ?e :: ?ls2 = ?ls1' ++ ?e :: ?ls2',
     H2: List.In ?e (?ls1 ++ ?ls2) -> False |- _] => specialize (list_components_equal _ _ _ _ _ H1 H2); smack
  end.
  apply remove_merge; auto.
- (* Binary Operation Plus - overflow check fail *)
  apply O_Binary_Plus_Operation_Overflow_Fail_X with (l1:=l1) (u1:=u1) (l2:=l2) (u2:=u2); auto.
- (* Binary Operation Plus - overflow check fail *)
  apply O_Binary_Plus_Operation_Overflow_Fail_X with (l1:=l1) (u1:=u1) (l2:=l2) (u2:=u2); auto.
- (* Binary Operation Minus - overflow check pass *)
  apply O_Binary_Minus_Operation_Overflow_Pass_X; auto.
  specialize (remove_split _ _ _ _ H11); intros HZ;
  destruct HZ as [cks1'0 [cks2'0 HZ5]]. destruct HZ5 as [HZ5 [HZ6 HZ7]].
  inversion HZ6; smack.
  match goal with
  | [H1: ?ls1 ++ ?e :: ?ls2 = ?ls1' ++ ?e :: ?ls2',
     H2: List.In ?e (?ls1 ++ ?ls2) -> False |- _] => specialize (list_components_equal _ _ _ _ _ H1 H2); smack
  end.
  apply remove_merge; auto.
- (* Binary Operation Minus - overflow check fail *)
  apply O_Binary_Minus_Operation_Overflow_Fail_X with (l1:=l1) (u1:=u1) (l2:=l2) (u2:=u2); auto.
- (* Binary Operation Minus - overflow check fail *)
  apply O_Binary_Minus_Operation_Overflow_Fail_X with (l1:=l1) (u1:=u1) (l2:=l2) (u2:=u2); auto.
- (* Binary Operation Multiply *)
  apply O_Binary_Multiplying_Operation_X with (l1:=l1) (u1:=u1) (l2:=l2) (u2:=u2); auto.
- (* Binary Operation Divide *)
  apply O_Binary_Multiplying_Operation_X with (l1:=l1) (u1:=u1) (l2:=l2) (u2:=u2); auto.
- (* Binary Logic Operation *)
  apply O_Binary_Logical_Operation_X; auto.
- (* Unary Operation Minus - overflow check pass *)
  apply O_Unary_Minus_Operation_X with (l:=l) (u:=u); auto.
  specialize (remove_split _ _ _ _ H12); intros HZ;
  destruct HZ as [cks1'0 [cks2'0 HZ5]]. destruct HZ5 as [HZ5 [HZ6 HZ7]].
  inversion HZ6; smack.
  match goal with
  | [H1: ?ls1 ++ ?e :: ?ls2 = ?ls1' ++ ?e :: ?ls2',
     H2: List.In ?e (?ls1 ++ ?ls2) -> False |- _] => specialize (list_components_equal _ _ _ _ _ H1 H2); smack
  end.
  apply remove_merge; auto.
- (* Unary Operation Minus - overflow check fail *)
  apply O_Unary_Minus_Operation_Overflow_X with (l:=l) (u:=u) (l':=(Z.opp u)) (u':=(Z.opp l)); auto.
- (* Unary Operation Minus - overflow check fail *)
  apply O_Unary_Minus_Operation_Overflow_X with (l:=l) (u:=u) (l':=(Z.opp u)) (u':=(Z.opp l)); auto.
- (* Unary Operation Plus *)
  apply O_Unary_Plus_Operation_X; auto.
- (* Unary Operation Not *)
  apply O_Unary_Not_Operation_X; auto.
Qed.

Ltac apply_optimize_expr_to_same_checkflags :=
  match goal with
  | [H1: optimize_expression_x _ ?e (_, ?e'),
     H2: remove_check_flag ?ck (exp_check_flags ?e') _,
     H3: exp_check_flags ?e = ?cks1 ++ ?ck :: ?cks2,
     H4: well_check_flagged_expr (update_exp_check_flags ?e (?cks1 ++ ?cks2)) |- _] => 
      specialize (optimize_expr_to_same_checkflags _ _ _ _ _ _ _ H1 H2 H3 H4)
  end.


Lemma extract_array_index_range_x_unique: forall st a l u l' u',
  extract_array_index_range_x st a (Range_X l u) ->
  extract_array_index_range_x st a (Range_X l' u') ->
  l = l' /\ u = u'.
Proof.
  intros.
  inversion H; inversion H0; subst.
  repeat progress match goal with
  | [H1: ?x = _, 
     H2: ?x = _ |- _] => rewrite H1 in H2; clear H1; inversion H2; subst
  end; auto.
Qed.

Ltac apply_extract_array_index_range_x_unique := 
  match goal with
  | [H1: extract_array_index_range_x _ ?a (Range_X ?l ?u),
     H2: extract_array_index_range_x _ ?a (Range_X ?l' ?u') |- _] => 
      specialize (extract_array_index_range_x_unique _ _ _ _ _ _ H1 H2)
  end.


(** when optimize an expression, it returns a range of its all possible
    values according to its sub-expression types, so the value of an expression
    evaluated according to its dynamic semantics should fall within that range; 
*)
Lemma eval_expr_value_in_domain: forall e e' st s v l u,
  well_typed_stack st s ->
    well_check_flagged_expr e ->
      eval_expr_x st s e (Normal (BasicV (Int v))) ->
        optimize_expression_x st e (IntBetween l u, e') ->
          (l <= v)%Z /\ (v <= u)%Z.
Proof.
  apply (expression_x_ind
    (fun e: expression_x => 
       forall (e' : expression_x) (st : symboltable_x) (s : STACK.stack) 
              (v l u : Z),
      well_typed_stack st s ->
      well_check_flagged_expr e ->
      eval_expr_x st s e (Normal (BasicV (Int v))) ->
      optimize_expression_x st e (IntBetween l u, e') ->
      (l <= v)%Z /\ (v <= u)%Z)
    (fun n: name_x => 
       forall (n' : name_x) (st : symboltable_x) (s : STACK.stack) 
              (v l u : Z),
      well_typed_stack st s ->
      well_check_flagged_name n ->
      eval_name_x st s n (Normal (BasicV (Int v))) ->
      optimize_name_x st n (IntBetween l u, n') ->
      (l <= v)%Z /\ (v <= u)%Z)
    ); intros.
- (* Literal *)
  match goal with
  | [H: optimize_expression_x ?st ?e ?e' |- _] => inversion H; clear H; subst
  end.
  match goal with
  | [H: eval_expr_x _ _ _ _ |- _] => inversion H; clear H; subst
  end. 
  repeat progress match goal with
  | [H: eval_literalO _ = _ |- _] => unfold eval_literalO in H
  | [H: eval_literal _ = _ |- _] => unfold eval_literal in H
  end.
  destruct l; inversion H5; inversion H6; subst.
  subst; smack.
- (* name *)
  match goal with
  | [H: optimize_expression_x ?st ?e ?e' |- _] => inversion H; clear H; subst
  end.
  match goal with
  | [H: eval_expr_x _ _ _ _ |- _] => inversion H; clear H; subst
  end.
  match goal with
  | [H: well_check_flagged_expr _ |- _] => inversion H; clear H; subst
  end.
  match goal with
  | [H1: forall (n' : name_x) (st : symboltable_x) (s : STACK.stack) (v l u : Z),
      well_typed_stack _ _ ->
      well_check_flagged_name ?n ->
      eval_name_x _ _ ?n _ ->
      optimize_name_x _ ?n _ -> _ ,
     H2: well_typed_stack _ _,
     H3: well_check_flagged_name ?n,
     H4: eval_name_x _ _ ?n _,
     H5: optimize_name_x _ ?n _ |- _ ] => specialize (H1 _ _ _ _ _ _ H2 H3 H4 H5); auto
  end.
- (* binary expression *)
  match goal with
  | [H: optimize_expression_x ?st ?e ?e' |- _] => inversion H; clear H; subst
  end.
  + (*1*)
  match goal with
  | [H: eval_expr_x _ _ _ _ |- _] => inversion H; clear H; subst
  end.
  match goal with
  | [H: Val.binary_operation ?op ?v1 ?v2 = _ |- _] => 
      destruct v1, v2; inversion H; clear H;
      [ destruct v0, v1 | destruct v0 | destruct v0]; inversion H4; subst
  end.
  match goal with
  | [H: well_check_flagged_expr _ |- _] => inversion H; subst
  end;
  repeat progress match goal with
  | [H1: forall (e' : expression_x) (st : symboltable_x) (s : STACK.stack) (v l u : Z),
      well_typed_stack _ _ ->
      well_check_flagged_expr ?e ->
      eval_expr_x _ _ ?e _ ->
      optimize_expression_x _ ?e _ -> _ ,
     H2: well_typed_stack _ _,
     H3: well_check_flagged_expr ?e,
     H4: eval_expr_x _ _ ?e _,
     H5: optimize_expression_x _ ?e _ |- _ ] => specialize (H1 _ _ _ _ _ _ H2 H3 H4 H5); auto
  end.
  split; apply Zplus_le_compat; smack.
  inversion H17; smack.
  + (*2*)
  match goal with
  | [H: eval_expr_x _ _ _ _ |- _] => inversion H; clear H; subst
  end.
  match goal with
  | [H: Val.binary_operation ?op ?v1 ?v2 = _ |- _] => 
      destruct v1, v2; inversion H; clear H;
      [ destruct v0, v1 | destruct v0 | destruct v0]; inversion H4; subst
  end.
  match goal with
  | [H: well_check_flagged_expr _ |- _] => inversion H; subst
  end;
  repeat progress match goal with
  | [H1: forall (e' : expression_x) (st : symboltable_x) (s : STACK.stack) (v l u : Z),
      well_typed_stack _ _ ->
      well_check_flagged_expr ?e ->
      eval_expr_x _ _ ?e _ ->
      optimize_expression_x _ ?e _ -> _ ,
     H2: well_typed_stack _ _,
     H3: well_check_flagged_expr ?e,
     H4: eval_expr_x _ _ ?e _,
     H5: optimize_expression_x _ ?e _ |- _ ] => specialize (H1 _ _ _ _ _ _ H2 H3 H4 H5); auto
  end.
  repeat progress match goal with
  | [H: do_flagged_checks_on_binop _ ?op ?v1 ?v2 _ |- _] => inversion H; clear H; subst
  | [H: do_flagged_check_on_binop _ ?op ?v1 ?v2 _ |- _] => inversion H; clear H; subst
  | [H: do_overflow_check_on_binop ?op ?v1 ?v2 _ |- _] => inversion H; clear H; subst
  | [H: Val.binary_operation ?op ?v1 ?v2 = _ |- _] => simpl in H; inversion H; subst
  | [H: (Zge_bool ?v ?l) && (Zle_bool ?v ?u) = true |- _] => specialize (Zgele_Bool_Imp_GeLe_T _ _ _ H); auto
  end; auto.
  inversion H7; smack.
  + (*3*)
  match goal with
  | [H: eval_expr_x _ _ _ _ |- _] => inversion H; clear H; subst
  end.
  match goal with
  | [H: Val.binary_operation ?op ?v1 ?v2 = _ |- _] => 
      destruct v1, v2; inversion H; clear H;
      [ destruct v0, v1 | destruct v0 | destruct v0]; inversion H4; subst
  end.
  match goal with
  | [H: well_check_flagged_expr _ |- _] => inversion H; subst
  end;
  repeat progress match goal with
  | [H1: forall (e' : expression_x) (st : symboltable_x) (s : STACK.stack) (v l u : Z),
      well_typed_stack _ _ ->
      well_check_flagged_expr ?e ->
      eval_expr_x _ _ ?e _ ->
      optimize_expression_x _ ?e _ -> _ ,
     H2: well_typed_stack _ _,
     H3: well_check_flagged_expr ?e,
     H4: eval_expr_x _ _ ?e _,
     H5: optimize_expression_x _ ?e _ |- _ ] => specialize (H1 _ _ _ _ _ _ H2 H3 H4 H5); auto
  end.
  (**)
  match goal with
  | [H:  (?l <= n <= ?u)%Z |- _] => destruct H as [HZ1 HZ2]
  end.
  match goal with
  | [H:  (?l <= n0 <= ?u)%Z |- _] => destruct H as [HZ3 HZ4]
  end.
  specialize (le_neg_ge _ _ HZ3); intros HZ5.
  specialize (le_neg_ge _ _ HZ4); intros HZ6.
  specialize (Zplus_le_compat _ _ _ _ HZ3 HZ6); intros HZ7.
  specialize (Zplus_le_compat _ _ _ _ HZ4 HZ5); intros HZ8. smack.
  (**)
  inversion H17; smack.
  + (*4*)
  match goal with
  | [H: eval_expr_x _ _ _ _ |- _] => inversion H; clear H; subst
  end.
  match goal with
  | [H: Val.binary_operation ?op ?v1 ?v2 = _ |- _] => 
      destruct v1, v2; inversion H; clear H;
      [ destruct v0, v1 | destruct v0 | destruct v0]; inversion H4; subst
  end.
  match goal with
  | [H: well_check_flagged_expr _ |- _] => inversion H; subst
  end;
  repeat progress match goal with
  | [H1: forall (e' : expression_x) (st : symboltable_x) (s : STACK.stack) (v l u : Z),
      well_typed_stack _ _ ->
      well_check_flagged_expr ?e ->
      eval_expr_x _ _ ?e _ ->
      optimize_expression_x _ ?e _ -> _ ,
     H2: well_typed_stack _ _,
     H3: well_check_flagged_expr ?e,
     H4: eval_expr_x _ _ ?e _,
     H5: optimize_expression_x _ ?e _ |- _ ] => specialize (H1 _ _ _ _ _ _ H2 H3 H4 H5); auto
  end.
  repeat progress match goal with
  | [H: do_flagged_checks_on_binop _ ?op ?v1 ?v2 _ |- _] => inversion H; clear H; subst
  | [H: do_flagged_check_on_binop _ ?op ?v1 ?v2 _ |- _] => inversion H; clear H; subst
  | [H: do_overflow_check_on_binop ?op ?v1 ?v2 _ |- _] => inversion H; clear H; subst
  | [H: Val.binary_operation ?op ?v1 ?v2 = _ |- _] => simpl in H; inversion H; subst
  | [H: (Zge_bool ?v ?l) && (Zle_bool ?v ?u) = true |- _] => specialize (Zgele_Bool_Imp_GeLe_T _ _ _ H); auto
  end; auto. 
  inversion H7; smack.
  + (*5. Multiply or Divide *)
  match goal with
  | [H: eval_expr_x _ _ _ _ |- _] => inversion H; clear H; subst
  end. 
  match goal with
  | [H: ?op = Multiply \/ ?op = Divide |- _] => inversion H; clear H; subst
  end.
  (* 5.1. Multiply *)
  match goal with
  | [H: Val.binary_operation ?op ?v1 ?v2 = _ |- _] => 
      destruct v1, v2; inversion H; clear H;
      [ destruct v0, v1 | destruct v0 | destruct v0]; inversion H4; subst
  end.
  match goal with
  | [H: well_check_flagged_expr _ |- _] => inversion H; subst
  end;
  repeat progress match goal with
  | [H: do_flagged_checks_on_binop _ ?op ?v1 ?v2 _ |- _] => inversion H; clear H; subst
  | [H: do_flagged_check_on_binop _ ?op ?v1 ?v2 _ |- _] => inversion H; clear H; subst
  | [H: do_overflow_check_on_binop ?op ?v1 ?v2 _ |- _] => inversion H; clear H; subst
  | [H: Val.binary_operation ?op ?v1 ?v2 = _ |- _] => simpl in H; inversion H; subst
  | [H: (Zge_bool ?v ?l) && (Zle_bool ?v ?u) = true |- _] => specialize (Zgele_Bool_Imp_GeLe_T _ _ _ H); auto
  end; auto.
  inversion H7; smack.
  (* 5.2. Divide *)
  match goal with
  | [H: Val.binary_operation ?op ?v1 ?v2 = _ |- _] => 
      destruct v1, v2; inversion H; clear H;
      [ destruct v0, v1 | destruct v0 | destruct v0]; inversion H4; subst
  end.
  match goal with
  | [H: well_check_flagged_expr _ |- _] => inversion H; subst
  end;
  repeat progress match goal with
  | [H: do_flagged_checks_on_binop _ ?op ?v1 ?v2 _ |- _] => inversion H; clear H; subst
  | [H: do_flagged_check_on_binop _ ?op ?v1 ?v2 _ |- _] => inversion H; clear H; subst
  | [H: do_overflow_check_on_binop ?op ?v1 ?v2 _ |- _] => inversion H; clear H; subst
  | [H: Val.binary_operation ?op ?v1 ?v2 = _ |- _] => simpl in H; inversion H; subst
  | [H: (Zge_bool ?v ?l) && (Zle_bool ?v ?u) = true |- _] => specialize (Zgele_Bool_Imp_GeLe_T _ _ _ H); auto
  end; auto.
  inversion H7; smack.
- (* unary expression *)
  match goal with
  | [H: optimize_expression_x ?st ?e ?e' |- _] => inversion H; clear H; subst
  end.
  + (*1. Unary_Minus Pass Overflow Check*)
  match goal with
  | [H: eval_expr_x _ _ _ _ |- _] => inversion H; clear H; subst
  end.
  match goal with
  | [H: Val.unary_operation ?op ?v1 = _ |- _] => 
      destruct v1; inversion H; clear H; subst;
      destruct v0; inversion H3;subst
  end.
  match goal with
  | [H: well_check_flagged_expr _ |- _] => inversion H; subst
  end;
  repeat progress match goal with
  | [H1: forall (e' : expression_x) (st : symboltable_x) (s : STACK.stack) (v l u : Z),
      well_typed_stack _ _ ->
      well_check_flagged_expr ?e ->
      eval_expr_x _ _ ?e _ ->
      optimize_expression_x _ ?e _ -> _ ,
     H2: well_typed_stack _ _,
     H3: well_check_flagged_expr ?e,
     H4: eval_expr_x _ _ ?e _,
     H5: optimize_expression_x _ ?e _ |- _ ] => specialize (H1 _ _ _ _ _ _ H2 H3 H4 H5); auto
  end;

  match goal with
  | [H:  (?l <= n <= ?u)%Z |- _] => destruct H as [HZ1 HZ2]
  end;
  specialize (le_neg_ge _ _ HZ1); intros HZ3;
  specialize (le_neg_ge _ _ HZ2); intros HZ4; smack.
  + (*2. Unary_Minus Fail Overflow Check *)
  match goal with
  | [H: eval_expr_x _ _ _ _ |- _] => inversion H; clear H; subst
  end.
  match goal with
  | [H: Val.unary_operation ?op ?v1 = _ |- _] => 
      destruct v1; inversion H; clear H; subst;
      destruct v0; inversion H3;subst
  end.
  match goal with
  | [H: well_check_flagged_expr _ |- _] => inversion H; subst
  end;
  repeat progress match goal with
  | [H: do_flagged_checks_on_unop _ ?op ?v _ |- _] => inversion H; clear H; subst
  | [H: do_flagged_check_on_unop _ ?op ?v _ |- _] => inversion H; clear H; subst
  | [H: do_overflow_check_on_unop ?op ?v _ |- _] => inversion H; clear H; subst
  | [H: Val.unary_operation ?op ?v = _ |- _] => simpl in H; inversion H; subst
  | [H: (Zge_bool ?v ?l) && (Zle_bool ?v ?u) = true |- _] => specialize (Zgele_Bool_Imp_GeLe_T _ _ _ H); auto
  end; smack.
  + (*3. Unary_Plus*)
  match goal with
  | [H: eval_expr_x _ _ _ _ |- _] => inversion H; clear H; subst
  end.
  match goal with
  | [H: Val.unary_operation ?op ?v1 = _ |- _] => 
      destruct v1; inversion H; clear H; subst;
      destruct v0; inversion H3;subst
  end.
  match goal with
  | [H: well_check_flagged_expr _ |- _] => inversion H; subst
  end;
  repeat progress match goal with
  | [H1: forall (e' : expression_x) (st : symboltable_x) (s : STACK.stack) (v l u : Z),
      well_typed_stack _ _ ->
      well_check_flagged_expr ?e ->
      eval_expr_x _ _ ?e _ ->
      optimize_expression_x _ ?e _ -> _ ,
     H2: well_typed_stack _ _,
     H3: well_check_flagged_expr ?e,
     H4: eval_expr_x _ _ ?e _,
     H5: optimize_expression_x _ ?e _ |- _ ] => specialize (H1 _ _ _ _ _ _ H2 H3 H4 H5); auto
  end.
- (* identifier *)
  match goal with
  | [H: eval_name_x _ _ _ _ |- _] => inversion H; subst
  end.
  match goal with
  | [H: optimize_name_x _ _ _ |- _] => inversion H; clear H; subst
  end.
  specialize (variable_value_in_type_domain _ _ _ _ _ _ _ _ H H1 H7 H12); intros HZ;
  specialize (Zgele_Bool_Imp_GeLe_T _ _ _ HZ); auto.  
- (* indexed component *)
  match goal with
  | [H: optimize_name_x _ _ _ |- _] => inversion H; clear H; subst
  end.
  + (*1*)
  match goal with
  | [H: eval_name_x _ _ _ _ |- _] => inversion H; clear H; subst
  end;
  match goal with
  | [H: well_check_flagged_name _ |- _] => inversion H; clear H; subst
  end.
  match goal with
  | [H1: ~ List.In _ ?ls,
     H2: ?ls = _ |- _] => unfold not in H1; rewrite H2 in H1; smack
  end.
  match goal with
  | [H1: fetch_exp_type_x ?x ?st = _,
     H2: fetch_exp_type_x ?x ?st = _ |- _] => rewrite H1 in H2; clear H1; inversion H2; subst
  end.
  specialize (extract_array_index_range_x_unique _ _ _ _ _ _ H15 H21); 
  let HZ := fresh "HZ" in intro HZ; destruct HZ; subst. 
  (* value of array component should be in the domain of its type, which is enforced by
     well-typed stack;
  *)
  admit.
  + (*2*)
  match goal with
  | [H: eval_name_x _ _ _ _ |- _] => inversion H; clear H; subst
  end;
  match goal with
  | [H: well_check_flagged_name _ |- _] => inversion H; clear H; subst
  end.
  match goal with
  | [H1: ~ List.In _ ?ls,
     H2: ?ls = _ |- _] => unfold not in H1; rewrite H2 in H1; smack
  end.
  match goal with
  | [H1: fetch_exp_type_x ?x ?st = _,
     H2: fetch_exp_type_x ?x ?st = _ |- _] => rewrite H1 in H2; clear H1; inversion H2; subst
  end.
  specialize (extract_array_index_range_x_unique _ _ _ _ _ _ H15 H19); 
  let HZ := fresh "HZ" in intro HZ; destruct HZ; subst. 
  (* value of array component should be in the domain of its type, which is enforced by
     well-typed stack;
  *)
  admit.
- (* selected component *)
  match goal with
  | [H: optimize_name_x _ _ _ |- _] => inversion H; clear H; subst
  end.
  match goal with
  | [H: eval_name_x _ _ _ _ |- _] => inversion H; clear H; subst
  end;
  match goal with
  | [H: well_check_flagged_name _ |- _] => inversion H; clear H; subst
  end.
  (* value of record field should be in the domain of its type, which is enforced by
     well-typed stack;
  *)
  admit.
Qed.

Ltac apply_eval_expr_value_in_domain :=
  match goal with
  | [H1: well_typed_stack ?st ?s,
     H2: well_check_flagged_expr ?e,
     H3: eval_expr_x ?st ?s ?e (Normal (BasicV (Int ?v))),
     H4: optimize_expression_x ?st ?e (_, ?e') |- _] => specialize (eval_expr_value_in_domain _ _ _ _ _ _ _ H1 H2 H3 H4)
  end.


(** TODO: to be proved later ... *)
(** the value of expression returned by optimize_expression_x is a range of possible values 
    when the expression is evaluated dynamically, so this value range should be in the domain
    of the expression type;
*)
Lemma  optimize_exp_value_in_domain: forall e st t l u l' u' e',
  fetch_exp_type_x (expression_astnum_x e) st = Some t ->
    extract_subtype_range_x st t (Range_X l u) ->
      (* need to add well-typed property for expression, in other words, the type 
         of the expression should be the type recorded in the symbol table *)
      optimize_expression_x st e (IntBetween l' u', e') ->
        do_range_check l' l u Success /\ do_range_check u' l u Success.
Proof.
  admit.
Qed.

Lemma  optimize_name_value_in_domain: forall x st t l u l' u' x',
  fetch_exp_type_x (name_astnum_x x) st = Some t ->
    extract_subtype_range_x st t (Range_X l u) ->
      (* need to add well-typed property for expression, in other words, the type 
         of the expression should be the type recorded in the symbol table *)
      optimize_name_x st x (IntBetween l' u', x') ->
        do_range_check l' l u Success /\ do_range_check u' l u Success.
Proof.
  admit.
Qed.


(** 
It's impossible to prove the following theorem directly, as we do induction 
proof on it, the proof will get stuck when e is an indexed_component, e.g. a[e]; 
the induction proof will generate a premise for e in the following theorem form,
where (eval_expr_x st s e v) is impossible to be true as e has Do_Range_Check flag, 
which is not acceptible by the semantics of eval_expr_x;

- Theorem expression_checks_optimization_soundness: forall e e' st s v v',
    eval_expr_x st s e v ->
      optimize_expression_x st e (v', e') ->
        eval_expr_x st s e' v.
*)

Lemma expression_checks_optimization_soundness_help: forall e e' st s checkflags v v',
  well_typed_stack st s ->
    remove_check_flag Do_Range_Check (exp_check_flags e) checkflags ->
      well_check_flagged_expr (update_exp_check_flags e checkflags) ->
        eval_expr_x st s (update_exp_check_flags e checkflags) v ->
          optimize_expression_x st (update_exp_check_flags e checkflags) (v', e') ->
            eval_expr_x st s e' v.
Proof.
  apply (expression_x_ind
    (fun e: expression_x => 
       forall (e' : expression_x) (st : symboltable_x) (s : STACK.stack) (checkflags : check_flags)
              (v : Return value) (v' : valueO),
      well_typed_stack st s ->
      remove_check_flag Do_Range_Check (exp_check_flags e) checkflags ->
      well_check_flagged_expr (update_exp_check_flags e checkflags) ->
      eval_expr_x st s (update_exp_check_flags e checkflags) v ->
      optimize_expression_x st (update_exp_check_flags e checkflags) (v', e') ->
      eval_expr_x st s e' v)
    (fun n: name_x => 
       forall (n' : name_x) (st : symboltable_x) (s : STACK.stack) (checkflags : check_flags)
              (v : Return value) (v' : valueO),
      well_typed_stack st s ->
      remove_check_flag Do_Range_Check (name_check_flags n) checkflags ->
      well_check_flagged_name (update_name_check_flags n checkflags) ->
      eval_name_x st s (update_name_check_flags n checkflags) v ->
      optimize_name_x st (update_name_check_flags n checkflags) (v', n') ->
      eval_name_x st s n' v)
    ); intros.
- (*Literal*)
  match goal with
  | [H: optimize_expression_x ?st ?e ?e' |- _] => inversion H; clear H; subst
  end.
  match goal with
  | [H: eval_expr_x _ _ _ _ |- _] => inversion H; clear H; subst
  end.
  constructor; auto.
- (* Name *)
  match goal with
  | [H: optimize_expression_x ?st ?e ?e' |- _] => inversion H; clear H; subst
  end.
  match goal with
  | [H: eval_expr_x _ _ _ _ |- _] => inversion H; clear H; subst
  end.
  match goal with
  | [H: well_check_flagged_expr _ |- _] => inversion H; clear H; subst
  end.
  match goal with
  | [H: remove_check_flag _ (exp_check_flags (E_Name_X _ _ _)) _ |- _] => simpl in H
  end.
  match goal with
  | [H1: forall (n' : name_x) (st : symboltable_x) (s : STACK.stack) (checkflags : check_flags)
                (v : Return value) (v' : valueO),
      well_typed_stack _ _ ->
      remove_check_flag Do_Range_Check (name_check_flags ?n) _ ->
      well_check_flagged_name (update_name_check_flags ?n _) ->
      eval_name_x _ _ (update_name_check_flags ?n _) _ ->
      optimize_name_x _ (update_name_check_flags ?n _) _ -> _ ,
     H2: well_typed_stack _ _,
     H3: remove_check_flag Do_Range_Check (name_check_flags ?n) _,
     H4: well_check_flagged_name (update_name_check_flags ?n _),
     H5: eval_name_x _ _ (update_name_check_flags ?n _) _,
     H6: optimize_name_x _ (update_name_check_flags ?n _) _ |- _ ] => 
      specialize (H1 _ _ _ _ _ _ H2 H3 H4 H5 H6); auto
  end.
  constructor; auto.
- (* binary expression *)
  simpl in H2, H3, H4, H5.
  match goal with
  | [H: optimize_expression_x _ _ _ |- _] => inversion H; clear H; subst
  end.
  + (*1. Plus Overflow Pass*)
  match goal with
  | [H: eval_expr_x _ _ _ _ |- _] => inversion H; clear H; subst
  end;
  match goal with
  | [H: well_check_flagged_expr _ |- _] => inversion H; subst; [ | smack]
  end;
  match goal with
  | [H: well_check_flagged_expr e |- _] => 
      let H1 := fresh "HZ" in 
      specialize (rm_range_check_return_same_expr_checks _ H); intros H1
  end;
  match goal with
  | [H: well_check_flagged_expr e0 |- _] => 
      let H1 := fresh "HZ" in 
      specialize (rm_range_check_return_same_expr_checks _ H); intros H1
  end;
  repeat progress match goal with
  | [H1: optimize_expression_x _ e _,
     H2: eval_expr_x _ _ e _,
     H3: well_check_flagged_expr e |- _] => 
      let HZ := fresh "HZ" in
      specialize (update_exp_with_same_check_flags e); intro HZ; rewrite <- HZ in H1, H2, H3; clear HZ
  | [H1: optimize_expression_x _ e0 _,
     H2: eval_expr_x _ _ e0 _,
     H3: well_check_flagged_expr e0 |- _] => 
      let HZ := fresh "HZ" in
      specialize (update_exp_with_same_check_flags e0); intro HZ; rewrite <- HZ in H1, H2, H3; clear HZ
  end;
  repeat progress match goal with
  | [H1: forall (e' : expression_x) (st : symboltable_x) (s : STACK.stack) (checkflags : check_flags)
                (v : Return value) (v' : valueO),
      well_typed_stack _ _ ->
      remove_check_flag Do_Range_Check (exp_check_flags ?e) _ ->
      well_check_flagged_expr (update_exp_check_flags ?e _) ->
      eval_expr_x _ _ (update_exp_check_flags ?e _) _ ->
      optimize_expression_x _ (update_exp_check_flags ?e _) _ -> _ ,
     H2: well_typed_stack _ _,
     H3: remove_check_flag Do_Range_Check (exp_check_flags ?e) _,
     H4: well_check_flagged_expr (update_exp_check_flags ?e _),
     H5: eval_expr_x _ _ (update_exp_check_flags ?e _) _,
     H6: optimize_expression_x _ (update_exp_check_flags ?e _) _ |- _ ] => 
      specialize (H1 _ _ _ _ _ _ H2 H3 H4 H5 H6); auto
  end;
  [apply Eval_E_Binary_Operation_RTE_E1_X; auto |
   apply Eval_E_Binary_Operation_RTE_E2_X with (v1 := v1); auto |
   apply Eval_E_Binary_Operation_RTE_Bin_X with (v1 := v1) (v2 := v2); auto |
   apply Eval_E_Binary_Operation_X with (v1 := v1) (v2 := v2); auto
  ].
  (* TODO: use contradiction to prove it: the value of e1 and e2 both fall in the range
           of their type, so (v1 op v2) should have no overflow !
  *)
  admit.
  inversion H18; smack. inversion H12; smack.
  constructor.
  + (*2. Plus Overflow Fail*)
  match goal with
  | [H: eval_expr_x _ _ _ _ |- _] => inversion H; clear H; subst
  end;
  match goal with
  | [H: well_check_flagged_expr _ |- _] => simpl in H; inversion H; subst; [ | smack]
  end;
  match goal with
  | [H: well_check_flagged_expr e |- _] => 
      let H1 := fresh "HZ" in 
      specialize (rm_range_check_return_same_expr_checks _ H); intros H1
  end;
  match goal with
  | [H: well_check_flagged_expr e0 |- _] => 
      let H1 := fresh "HZ" in 
      specialize (rm_range_check_return_same_expr_checks _ H); intros H1
  end;
  repeat progress match goal with
  | [H1: optimize_expression_x _ e _,
     H2: eval_expr_x _ _ e _,
     H3: well_check_flagged_expr e |- _] => 
      let HZ := fresh "HZ" in
      specialize (update_exp_with_same_check_flags e); intro HZ; rewrite <- HZ in H1, H2, H3; clear HZ
  | [H1: optimize_expression_x _ e0 _,
     H2: eval_expr_x _ _ e0 _,
     H3: well_check_flagged_expr e0 |- _] => 
      let HZ := fresh "HZ" in
      specialize (update_exp_with_same_check_flags e0); intro HZ; rewrite <- HZ in H1, H2, H3; clear HZ
  end;
  repeat progress match goal with
  | [H1: forall (e' : expression_x) (st : symboltable_x) (s : STACK.stack) (checkflags : check_flags)
                (v : Return value) (v' : valueO),
      well_typed_stack _ _ ->
      remove_check_flag Do_Range_Check (exp_check_flags ?e) _ ->
      well_check_flagged_expr (update_exp_check_flags ?e _) ->
      eval_expr_x _ _ (update_exp_check_flags ?e _) _ ->
      optimize_expression_x _ (update_exp_check_flags ?e _) _ -> _ ,
     H2: well_typed_stack _ _,
     H3: remove_check_flag Do_Range_Check (exp_check_flags ?e) _,
     H4: well_check_flagged_expr (update_exp_check_flags ?e _),
     H5: eval_expr_x _ _ (update_exp_check_flags ?e _) _,
     H6: optimize_expression_x _ (update_exp_check_flags ?e _) _ |- _ ] => 
      specialize (H1 _ _ _ _ _ _ H2 H3 H4 H5 H6); auto
  end;
  [apply Eval_E_Binary_Operation_RTE_E1_X; auto |
   apply Eval_E_Binary_Operation_RTE_E2_X with (v1 := v1); auto |
   apply Eval_E_Binary_Operation_RTE_Bin_X with (v1 := v1) (v2 := v2); auto |
   apply Eval_E_Binary_Operation_X with (v1 := v1) (v2 := v2); auto
  ].
  + (*3. Minus Overflow Pass *)
  match goal with
  | [H: eval_expr_x _ _ _ _ |- _] => inversion H; clear H; subst
  end;
  match goal with
  | [H: well_check_flagged_expr _ |- _] => inversion H; subst; [ | smack]
  end;
  match goal with
  | [H: well_check_flagged_expr e |- _] => 
      let H1 := fresh "HZ" in 
      specialize (rm_range_check_return_same_expr_checks _ H); intros H1
  end;
  match goal with
  | [H: well_check_flagged_expr e0 |- _] => 
      let H1 := fresh "HZ" in 
      specialize (rm_range_check_return_same_expr_checks _ H); intros H1
  end;
  repeat progress match goal with
  | [H1: optimize_expression_x _ e _,
     H2: eval_expr_x _ _ e _,
     H3: well_check_flagged_expr e |- _] => 
      let HZ := fresh "HZ" in
      specialize (update_exp_with_same_check_flags e); intro HZ; rewrite <- HZ in H1, H2, H3; clear HZ
  | [H1: optimize_expression_x _ e0 _,
     H2: eval_expr_x _ _ e0 _,
     H3: well_check_flagged_expr e0 |- _] => 
      let HZ := fresh "HZ" in
      specialize (update_exp_with_same_check_flags e0); intro HZ; rewrite <- HZ in H1, H2, H3; clear HZ
  end;
  repeat progress match goal with
  | [H1: forall (e' : expression_x) (st : symboltable_x) (s : STACK.stack) (checkflags : check_flags)
                (v : Return value) (v' : valueO),
      well_typed_stack _ _ ->
      remove_check_flag Do_Range_Check (exp_check_flags ?e) _ ->
      well_check_flagged_expr (update_exp_check_flags ?e _) ->
      eval_expr_x _ _ (update_exp_check_flags ?e _) _ ->
      optimize_expression_x _ (update_exp_check_flags ?e _) _ -> _ ,
     H2: well_typed_stack _ _,
     H3: remove_check_flag Do_Range_Check (exp_check_flags ?e) _,
     H4: well_check_flagged_expr (update_exp_check_flags ?e _),
     H5: eval_expr_x _ _ (update_exp_check_flags ?e _) _,
     H6: optimize_expression_x _ (update_exp_check_flags ?e _) _ |- _ ] => 
      specialize (H1 _ _ _ _ _ _ H2 H3 H4 H5 H6); auto
  end;
  [apply Eval_E_Binary_Operation_RTE_E1_X; auto |
   apply Eval_E_Binary_Operation_RTE_E2_X with (v1 := v1); auto |
   apply Eval_E_Binary_Operation_RTE_Bin_X with (v1 := v1) (v2 := v2); auto |
   apply Eval_E_Binary_Operation_X with (v1 := v1) (v2 := v2); auto
  ].
  (* TODO: use contradiction to prove it: the value of e1 and e2 both fall in the range
           of their type, so (v1 op v2) should have no overflow !
  *)
  admit.
  inversion H18; smack. inversion H12; smack.
  constructor.
  + (*4. Minus Overflow Fail*)
  match goal with
  | [H: eval_expr_x _ _ _ _ |- _] => inversion H; clear H; subst
  end;
  match goal with
  | [H: well_check_flagged_expr _ |- _] => simpl in H; inversion H; subst; [ | smack]
  end;
  match goal with
  | [H: well_check_flagged_expr e |- _] => 
      let H1 := fresh "HZ" in 
      specialize (rm_range_check_return_same_expr_checks _ H); intros H1
  end;
  match goal with
  | [H: well_check_flagged_expr e0 |- _] => 
      let H1 := fresh "HZ" in 
      specialize (rm_range_check_return_same_expr_checks _ H); intros H1
  end;
  repeat progress match goal with
  | [H1: optimize_expression_x _ e _,
     H2: eval_expr_x _ _ e _,
     H3: well_check_flagged_expr e |- _] => 
      let HZ := fresh "HZ" in
      specialize (update_exp_with_same_check_flags e); intro HZ; rewrite <- HZ in H1, H2, H3; clear HZ
  | [H1: optimize_expression_x _ e0 _,
     H2: eval_expr_x _ _ e0 _,
     H3: well_check_flagged_expr e0 |- _] => 
      let HZ := fresh "HZ" in
      specialize (update_exp_with_same_check_flags e0); intro HZ; rewrite <- HZ in H1, H2, H3; clear HZ
  end;
  repeat progress match goal with
  | [H1: forall (e' : expression_x) (st : symboltable_x) (s : STACK.stack) (checkflags : check_flags)
                (v : Return value) (v' : valueO),
      well_typed_stack _ _ ->
      remove_check_flag Do_Range_Check (exp_check_flags ?e) _ ->
      well_check_flagged_expr (update_exp_check_flags ?e _) ->
      eval_expr_x _ _ (update_exp_check_flags ?e _) _ ->
      optimize_expression_x _ (update_exp_check_flags ?e _) _ -> _ ,
     H2: well_typed_stack _ _,
     H3: remove_check_flag Do_Range_Check (exp_check_flags ?e) _,
     H4: well_check_flagged_expr (update_exp_check_flags ?e _),
     H5: eval_expr_x _ _ (update_exp_check_flags ?e _) _,
     H6: optimize_expression_x _ (update_exp_check_flags ?e _) _ |- _ ] => 
      specialize (H1 _ _ _ _ _ _ H2 H3 H4 H5 H6); auto
  end;
  [apply Eval_E_Binary_Operation_RTE_E1_X; auto |
   apply Eval_E_Binary_Operation_RTE_E2_X with (v1 := v1); auto |
   apply Eval_E_Binary_Operation_RTE_Bin_X with (v1 := v1) (v2 := v2); auto |
   apply Eval_E_Binary_Operation_X with (v1 := v1) (v2 := v2); auto
  ].
  + (*5. Multiply or Divide *)
  match goal with
  | [H: ?op = Multiply \/ ?op = Divide |- _] => inversion H; clear H; subst
  end.
  * (* 5.1. Multiply *)
  match goal with
  | [H: eval_expr_x _ _ _ _ |- _] => inversion H; clear H; subst
  end;
  match goal with
  | [H: well_check_flagged_expr _ |- _] => inversion H; subst; [ | smack]
  end;
  match goal with
  | [H: well_check_flagged_expr e |- _] => 
      let H1 := fresh "HZ" in 
      specialize (rm_range_check_return_same_expr_checks _ H); intros H1
  end;
  match goal with
  | [H: well_check_flagged_expr e0 |- _] => 
      let H1 := fresh "HZ" in 
      specialize (rm_range_check_return_same_expr_checks _ H); intros H1
  end;
  repeat progress match goal with
  | [H1: optimize_expression_x _ e _,
     H2: eval_expr_x _ _ e _,
     H3: well_check_flagged_expr e |- _] => 
      let HZ := fresh "HZ" in
      specialize (update_exp_with_same_check_flags e); intro HZ; rewrite <- HZ in H1, H2, H3; clear HZ
  | [H1: optimize_expression_x _ e0 _,
     H2: eval_expr_x _ _ e0 _,
     H3: well_check_flagged_expr e0 |- _] => 
      let HZ := fresh "HZ" in
      specialize (update_exp_with_same_check_flags e0); intro HZ; rewrite <- HZ in H1, H2, H3; clear HZ
  end;
  repeat progress match goal with
  | [H1: forall (e' : expression_x) (st : symboltable_x) (s : STACK.stack) (checkflags : check_flags)
                (v : Return value) (v' : valueO),
      well_typed_stack _ _ ->
      remove_check_flag Do_Range_Check (exp_check_flags ?e) _ ->
      well_check_flagged_expr (update_exp_check_flags ?e _) ->
      eval_expr_x _ _ (update_exp_check_flags ?e _) _ ->
      optimize_expression_x _ (update_exp_check_flags ?e _) _ -> _ ,
     H2: well_typed_stack _ _,
     H3: remove_check_flag Do_Range_Check (exp_check_flags ?e) _,
     H4: well_check_flagged_expr (update_exp_check_flags ?e _),
     H5: eval_expr_x _ _ (update_exp_check_flags ?e _) _,
     H6: optimize_expression_x _ (update_exp_check_flags ?e _) _ |- _ ] => 
      specialize (H1 _ _ _ _ _ _ H2 H3 H4 H5 H6); auto
  end;
  [apply Eval_E_Binary_Operation_RTE_E1_X; auto |
   apply Eval_E_Binary_Operation_RTE_E2_X with (v1 := v1); auto |
   apply Eval_E_Binary_Operation_RTE_Bin_X with (v1 := v1) (v2 := v2); auto |
   apply Eval_E_Binary_Operation_X with (v1 := v1) (v2 := v2); auto
  ].
  * (* 5.2. Divide *)
  match goal with
  | [H: eval_expr_x _ _ _ _ |- _] => inversion H; clear H; subst
  end;
  match goal with
  | [H: well_check_flagged_expr _ |- _] => inversion H; subst; [smack | | smack]
  end;
  match goal with
  | [H: well_check_flagged_expr e |- _] => 
      let H1 := fresh "HZ" in 
      specialize (rm_range_check_return_same_expr_checks _ H); intros H1
  end;
  match goal with
  | [H: well_check_flagged_expr e0 |- _] => 
      let H1 := fresh "HZ" in 
      specialize (rm_range_check_return_same_expr_checks _ H); intros H1
  end;
  repeat progress match goal with
  | [H1: optimize_expression_x _ e _,
     H2: eval_expr_x _ _ e _,
     H3: well_check_flagged_expr e |- _] => 
      let HZ := fresh "HZ" in
      specialize (update_exp_with_same_check_flags e); intro HZ; rewrite <- HZ in H1, H2, H3; clear HZ
  | [H1: optimize_expression_x _ e0 _,
     H2: eval_expr_x _ _ e0 _,
     H3: well_check_flagged_expr e0 |- _] => 
      let HZ := fresh "HZ" in
      specialize (update_exp_with_same_check_flags e0); intro HZ; rewrite <- HZ in H1, H2, H3; clear HZ
  end;
  repeat progress match goal with
  | [H1: forall (e' : expression_x) (st : symboltable_x) (s : STACK.stack) (checkflags : check_flags)
                (v : Return value) (v' : valueO),
      well_typed_stack _ _ ->
      remove_check_flag Do_Range_Check (exp_check_flags ?e) _ ->
      well_check_flagged_expr (update_exp_check_flags ?e _) ->
      eval_expr_x _ _ (update_exp_check_flags ?e _) _ ->
      optimize_expression_x _ (update_exp_check_flags ?e _) _ -> _ ,
     H2: well_typed_stack _ _,
     H3: remove_check_flag Do_Range_Check (exp_check_flags ?e) _,
     H4: well_check_flagged_expr (update_exp_check_flags ?e _),
     H5: eval_expr_x _ _ (update_exp_check_flags ?e _) _,
     H6: optimize_expression_x _ (update_exp_check_flags ?e _) _ |- _ ] => 
      specialize (H1 _ _ _ _ _ _ H2 H3 H4 H5 H6); auto
  end;
  [apply Eval_E_Binary_Operation_RTE_E1_X; auto |
   apply Eval_E_Binary_Operation_RTE_E2_X with (v1 := v1); auto |
   apply Eval_E_Binary_Operation_RTE_Bin_X with (v1 := v1) (v2 := v2); auto |
   apply Eval_E_Binary_Operation_X with (v1 := v1) (v2 := v2); auto
  ].
  + (*6. Logical_Operation*)
  match goal with
  | [H: eval_expr_x _ _ _ _ |- _] => inversion H; clear H; subst
  end;
  match goal with
  | [H: well_check_flagged_expr _ |- _] => inversion H; subst; [smack | smack | ]
  end;
  match goal with
  | [H: well_check_flagged_expr e |- _] => 
      let H1 := fresh "HZ" in 
      specialize (rm_range_check_return_same_expr_checks _ H); intros H1
  end;
  match goal with
  | [H: well_check_flagged_expr e0 |- _] => 
      let H1 := fresh "HZ" in 
      specialize (rm_range_check_return_same_expr_checks _ H); intros H1
  end;
  repeat progress match goal with
  | [H1: optimize_expression_x _ e _,
     H2: eval_expr_x _ _ e _,
     H3: well_check_flagged_expr e |- _] => 
      let HZ := fresh "HZ" in
      specialize (update_exp_with_same_check_flags e); intro HZ; rewrite <- HZ in H1, H2, H3; clear HZ
  | [H1: optimize_expression_x _ e0 _,
     H2: eval_expr_x _ _ e0 _,
     H3: well_check_flagged_expr e0 |- _] => 
      let HZ := fresh "HZ" in
      specialize (update_exp_with_same_check_flags e0); intro HZ; rewrite <- HZ in H1, H2, H3; clear HZ
  end;
  repeat progress match goal with
  | [H1: forall (e' : expression_x) (st : symboltable_x) (s : STACK.stack) (checkflags : check_flags)
                (v : Return value) (v' : valueO),
      well_typed_stack _ _ ->
      remove_check_flag Do_Range_Check (exp_check_flags ?e) _ ->
      well_check_flagged_expr (update_exp_check_flags ?e _) ->
      eval_expr_x _ _ (update_exp_check_flags ?e _) _ ->
      optimize_expression_x _ (update_exp_check_flags ?e _) _ -> _ ,
     H2: well_typed_stack _ _,
     H3: remove_check_flag Do_Range_Check (exp_check_flags ?e) _,
     H4: well_check_flagged_expr (update_exp_check_flags ?e _),
     H5: eval_expr_x _ _ (update_exp_check_flags ?e _) _,
     H6: optimize_expression_x _ (update_exp_check_flags ?e _) _ |- _ ] => 
      specialize (H1 _ _ _ _ _ _ H2 H3 H4 H5 H6); auto
  end;
  [apply Eval_E_Binary_Operation_RTE_E1_X; auto |
   apply Eval_E_Binary_Operation_RTE_E2_X with (v1 := v1); auto |
   apply Eval_E_Binary_Operation_RTE_Bin_X with (v1 := v1) (v2 := v2); auto |
   apply Eval_E_Binary_Operation_X with (v1 := v1) (v2 := v2); auto
  ].
- (* unary expression *)
  match goal with
  | [H: optimize_expression_x ?st ?e ?e' |- _] => inversion H; clear H; subst
  end.
  + (*1. Unary_Minus Pass Overflow Check*)
  match goal with
  | [H: eval_expr_x _ _ _ _ |- _] => inversion H; clear H; subst
  end;
  match goal with
  | [H: well_check_flagged_expr _ |- _] => inversion H; subst; [ | smack]
  end;
  match goal with
  | [H: well_check_flagged_expr e |- _] => 
      let H1 := fresh "HZ" in 
      specialize (rm_range_check_return_same_expr_checks _ H); intros H1
  end;
  match goal with
  | [H1: optimize_expression_x _ e _,
     H2: eval_expr_x _ _ e _,
     H3: well_check_flagged_expr e |- _] => 
      let HZ := fresh "HZ" in
      specialize (update_exp_with_same_check_flags e); intro HZ;
      rewrite <- HZ in H1, H2, H3; clear HZ
  end;
  match goal with
  | [H1: forall (e' : expression_x) (st : symboltable_x) (s : STACK.stack) (checkflags : check_flags)
                (v : Return value) (v' : valueO),
      well_typed_stack _ _ ->
      remove_check_flag Do_Range_Check (exp_check_flags ?e) _ ->
      well_check_flagged_expr (update_exp_check_flags ?e _) ->
      eval_expr_x _ _ (update_exp_check_flags ?e _) _ ->
      optimize_expression_x _ (update_exp_check_flags ?e _) _ -> _ ,
     H2: well_typed_stack _ _,
     H3: remove_check_flag Do_Range_Check (exp_check_flags ?e) _,
     H4: well_check_flagged_expr (update_exp_check_flags ?e _),
     H5: eval_expr_x _ _ (update_exp_check_flags ?e _) _,
     H6: optimize_expression_x _ (update_exp_check_flags ?e _) _ |- _ ] => 
      specialize (H1 _ _ _ _ _ _ H2 H3 H4 H5 H6); auto
  end;
  [ apply Eval_E_Unary_Operation_RTE_E_X; auto |
    apply Eval_E_Unary_Operation_RTE_X with (v := v0); auto |
    apply Eval_E_Unary_Operation_X with (v := v0); auto
  ].
  (*TODO: use contradiction to prove it. the value of unary operation
          is in the range of its type, so it should never overflow !
  *)
  admit.
  inversion H17; smack. inversion H9; smack.
  constructor.
  + (*2. Unary_Minus Fail Overflow Check *)
  match goal with
  | [H: eval_expr_x _ _ _ _ |- _] => inversion H; clear H; subst
  end;
  match goal with
  | [H: well_check_flagged_expr _ |- _] => inversion H; subst; [ | smack]
  end;
  match goal with
  | [H: well_check_flagged_expr e |- _] => 
      let H1 := fresh "HZ" in 
      specialize (rm_range_check_return_same_expr_checks _ H); intros H1
  end;
  match goal with
  | [H1: optimize_expression_x _ e _,
     H2: eval_expr_x _ _ e _,
     H3: well_check_flagged_expr e |- _] => 
      let HZ := fresh "HZ" in
      specialize (update_exp_with_same_check_flags e); intro HZ;
      rewrite <- HZ in H1, H2, H3; clear HZ
  end;
  match goal with
  | [H1: forall (e' : expression_x) (st : symboltable_x) (s : STACK.stack) (checkflags : check_flags)
                (v : Return value) (v' : valueO),
      well_typed_stack _ _ ->
      remove_check_flag Do_Range_Check (exp_check_flags ?e) _ ->
      well_check_flagged_expr (update_exp_check_flags ?e _) ->
      eval_expr_x _ _ (update_exp_check_flags ?e _) _ ->
      optimize_expression_x _ (update_exp_check_flags ?e _) _ -> _ ,
     H2: well_typed_stack _ _,
     H3: remove_check_flag Do_Range_Check (exp_check_flags ?e) _,
     H4: well_check_flagged_expr (update_exp_check_flags ?e _),
     H5: eval_expr_x _ _ (update_exp_check_flags ?e _) _,
     H6: optimize_expression_x _ (update_exp_check_flags ?e _) _ |- _ ] => 
      specialize (H1 _ _ _ _ _ _ H2 H3 H4 H5 H6); auto
  end;
  [ apply Eval_E_Unary_Operation_RTE_E_X; auto |
    apply Eval_E_Unary_Operation_RTE_X with (v := v0); auto |
    apply Eval_E_Unary_Operation_X with (v := v0); auto
  ].
  + (*3. Unary_Plus*)
  match goal with
  | [H: eval_expr_x _ _ _ _ |- _] => inversion H; clear H; subst
  end;  
  match goal with
  | [H: well_check_flagged_expr _ |- _] => inversion H; subst
  end;
  match goal with
  | [H: well_check_flagged_expr e |- _] => 
      let H1 := fresh "HZ" in 
      specialize (rm_range_check_return_same_expr_checks _ H); intros H1
  end;
  match goal with
  | [H1: optimize_expression_x _ e _,
     H2: eval_expr_x _ _ e _,
     H3: well_check_flagged_expr e |- _] => 
      let HZ := fresh "HZ" in
      specialize (update_exp_with_same_check_flags e); intro HZ; rewrite <- HZ in H1, H2, H3; clear HZ
  end;
  match goal with
  | [H1: forall (e' : expression_x) (st : symboltable_x) (s : STACK.stack) (checkflags : check_flags)
                (v : Return value) (v' : valueO),
      well_typed_stack _ _ ->
      remove_check_flag Do_Range_Check (exp_check_flags ?e) _ ->
      well_check_flagged_expr (update_exp_check_flags ?e _) ->
      eval_expr_x _ _ (update_exp_check_flags ?e _) _ ->
      optimize_expression_x _ (update_exp_check_flags ?e _) _ -> _ ,
     H2: well_typed_stack _ _,
     H3: remove_check_flag Do_Range_Check (exp_check_flags ?e) _,
     H4: well_check_flagged_expr (update_exp_check_flags ?e _),
     H5: eval_expr_x _ _ (update_exp_check_flags ?e _) _,
     H6: optimize_expression_x _ (update_exp_check_flags ?e _) _ |- _ ] => 
      specialize (H1 _ _ _ _ _ _ H2 H3 H4 H5 H6); auto
  end;
  [ apply Eval_E_Unary_Operation_RTE_E_X; auto |
    apply Eval_E_Unary_Operation_RTE_X with (v := v0); auto |
    apply Eval_E_Unary_Operation_X with (v := v0); auto
  ].
  + (*4. Unary_Not*)
  match goal with
  | [H: eval_expr_x _ _ _ _ |- _] => inversion H; clear H; subst
  end;
  match goal with
  | [H: well_check_flagged_expr _ |- _] => inversion H; subst
  end;  
  match goal with
  | [H: well_check_flagged_expr e |- _] => 
      let H1 := fresh "HZ" in 
      specialize (rm_range_check_return_same_expr_checks _ H); intros H1
  end;
  match goal with
  | [H1: optimize_expression_x _ e _,
     H2: eval_expr_x _ _ e _,
     H3: well_check_flagged_expr e |- _] => 
      let HZ := fresh "HZ" in
      specialize (update_exp_with_same_check_flags e); intro HZ; rewrite <- HZ in H1, H2, H3; clear HZ
  end;
  match goal with
  | [H1: forall (e' : expression_x) (st : symboltable_x) (s : STACK.stack) (checkflags : check_flags)
                (v : Return value) (v' : valueO),
      well_typed_stack _ _ ->
      remove_check_flag Do_Range_Check (exp_check_flags ?e) _ ->
      well_check_flagged_expr (update_exp_check_flags ?e _) ->
      eval_expr_x _ _ (update_exp_check_flags ?e _) _ ->
      optimize_expression_x _ (update_exp_check_flags ?e _) _ -> _ ,
     H2: well_typed_stack _ _,
     H3: remove_check_flag Do_Range_Check (exp_check_flags ?e) _,
     H4: well_check_flagged_expr (update_exp_check_flags ?e _),
     H5: eval_expr_x _ _ (update_exp_check_flags ?e _) _,
     H6: optimize_expression_x _ (update_exp_check_flags ?e _) _ |- _ ] => 
      specialize (H1 _ _ _ _ _ _ H2 H3 H4 H5 H6); auto
  end;
  [ apply Eval_E_Unary_Operation_RTE_E_X; auto |
    apply Eval_E_Unary_Operation_RTE_X with (v := v0); auto |
    apply Eval_E_Unary_Operation_X with (v := v0); auto
  ].
- (* identifier *)
  match goal with
  | [H: eval_name_x _ _ _ _ |- _] => inversion H; subst
  end.
  match goal with
  | [H: optimize_name_x _ _ _ |- _] => inversion H; clear H; subst
  end.
  constructor; auto.
- (* indexed component *)
  simpl in H1, H2, H3, H4.
  match goal with
  | [H: optimize_name_x _ _ _ |- _] => inversion H; clear H; subst
  end.
  + (*1. index range check pass*)
  match goal with
  | [H: eval_name_x _ _ _ _ |- _] => inversion H; clear H; subst
  end;
  match goal with
  | [H: well_check_flagged_name _ |- _] => inversion H; clear H; subst
  end;
  match goal with
  | [H1: ~ List.In _ ?ls,
     H2: ?ls = _ |- _] => unfold not in H1; rewrite H2 in H1; smack
  | _ => idtac
  end;
  
  match goal with
  | [H: well_check_flagged_expr ?e |- _] => 
      specialize (range_check_not_in_expr _ H); let HZ := fresh "HZ" in intro HZ;
      rewrite update_exp_with_new_check_flags in HZ
  end;
  match goal with
  | [H1: fetch_exp_type_x ?x ?st = _,
     H2: fetch_exp_type_x ?x ?st = _ |- _] => rewrite H1 in H2; inversion H2; subst
  | _ => idtac
  end;
  match goal with
  | [H1: exp_check_flags ?e = ?cks1 ++ ?ck :: ?cks2, 
     H2: exp_check_flags ?e = ?cks0 ++ ?ck :: ?cks3,
     H3: ~(List.In ?ck (?cks0 ++ ?cks3)) |- _] => 
      rewrite H2 in H1; specialize (list_components_equal _ _ _ _ _ H1 H3); 
      let HZ := fresh "HZ" in intro HZ; destruct HZ; subst
  end;
  specialize (remove_range_check_property _ _ _ H5 H8);
  (let HZ := fresh "HZ" in intro HZ);
  apply_optimize_expr_to_same_checkflags; (let HZ := fresh "HZ" in intro HZ);
  match goal with
  | [H1: forall (e' : expression_x) (st : symboltable_x) (s : STACK.stack) (checkflags : check_flags)
                (v : Return value) (v' : valueO),
      well_typed_stack _ _ ->
      remove_check_flag Do_Range_Check (exp_check_flags ?e) _ ->
      well_check_flagged_expr (update_exp_check_flags ?e _) ->
      eval_expr_x _ _ (update_exp_check_flags ?e _) _ ->
      optimize_expression_x _ (update_exp_check_flags ?e _) _ -> _ ,
     H2: well_typed_stack _ _,
     H3: remove_check_flag Do_Range_Check (exp_check_flags ?e) _,
     H4: well_check_flagged_expr (update_exp_check_flags ?e _),
     H5: eval_expr_x _ _ (update_exp_check_flags ?e _) _,
     H6: optimize_expression_x _ (update_exp_check_flags ?e _) _ |- _ ] => 
      specialize (H1 _ _ _ _ _ _ H2 H3 H4 H5 H6); auto
  end.
  *
  apply Eval_E_Indexed_Component_RTE_X; auto;
  specialize (update_exp_with_new_check_flags e' checkflags');
  (let HZ := fresh "HZ" in intro HZ; rewrite HZ; clear HZ);
  specialize (removed_check_flag_notin _ _ _ H19); auto.
  *
  specialize (extract_array_index_range_x_unique _ _ _ _ _ _ H15 H22); 
  (let HZ := fresh "HZ" in intro HZ; destruct HZ); subst;
  (* TODO: use contradiction to prove:
           value of array component falls in the domain of the component type *)
  admit.  
  * 
  specialize (extract_array_index_range_x_unique _ _ _ _ _ _ H15 H22); 
  (let HZ := fresh "HZ" in intro HZ; destruct HZ; subst);
  apply Eval_E_Indexed_Component_X with (i:=i0) (a:=a1); auto;
  specialize (update_exp_with_new_check_flags e' checkflags');
  (let HZ := fresh "HZ" in intro HZ; rewrite HZ; clear HZ);
  specialize (removed_check_flag_notin _ _ _ H19); auto.
  + (*2. index range check fail*)
  match goal with
  | [H: eval_name_x _ _ _ _ |- _] => inversion H; clear H; subst
  end;
  match goal with
  | [H: well_check_flagged_name _ |- _] => inversion H; clear H; subst
  end;
  match goal with
  | [H1: ~ List.In _ ?ls,
     H2: ?ls = _ |- _] => unfold not in H1; rewrite H2 in H1; smack
  | _ => idtac
  end;
  match goal with
  | [H: well_check_flagged_expr ?e |- _] => 
      specialize (range_check_not_in_expr _ H); let HZ := fresh "HZ" in intro HZ;
      rewrite update_exp_with_new_check_flags in HZ
  end;
  match goal with
  | [H1: fetch_exp_type_x ?x ?st = _,
     H2: fetch_exp_type_x ?x ?st = _ |- _] => rewrite H1 in H2; inversion H2; subst
  | _ => idtac
  end;
  match goal with
  | [H1: exp_check_flags ?e = ?cks1 ++ ?ck :: ?cks2, 
     H2: exp_check_flags ?e = ?cks0 ++ ?ck :: ?cks3,
     H3: ~(List.In ?ck (?cks0 ++ ?cks3)) |- _] => 
      rewrite H2 in H1; specialize (list_components_equal _ _ _ _ _ H1 H3); 
      let HZ := fresh "HZ" in intro HZ; destruct HZ; subst
  end;
  specialize (remove_range_check_property _ _ _ H5 H8);
  (let HZ := fresh "HZ" in intro HZ);
  specialize (optimize_expression_reserve_range_check _ _ _ _ _ _ H5 H12); intros HZZ;
  destruct HZZ as [cks1' [cks2' HE]];
  specialize (optimize_expression_range_check_notin _ _ _ _ _ _ _ _ H5 H12 HE HZ);
  (let HZ := fresh "HZ" in intros HZ);
  
  [ apply Eval_E_Indexed_Component_E_RTE_X with (cks1:=cks1') (cks2:=cks2'); auto |
    apply Eval_E_Indexed_Component_Range_RTE_X with (cks1:=cks1') (cks2:=cks2') (i:=i0)
                                                    (t:=t0) (l:=l0) (u:=u0); auto |
    apply Eval_E_Indexed_Component_Range_X with (cks1:=cks1') (cks2:=cks2') (i:=i0) (t:=t0)
                                                (l:=l0) (u:=u0) (a:=a1); auto
  ];
  specialize (remove_a_unique_check _ _ _ _ HE HZ1); 
  (let HZ := fresh "HZ" in intros HZ);
  apply_optimize_expr_to_same_checkflags; 
  (let HZ := fresh "HZ" in intros HZ);
  match goal with
  | [H1: forall (e' : expression_x) (st : symboltable_x) (s : STACK.stack) (checkflags : check_flags)
                (v : Return value) (v' : valueO),
      well_typed_stack _ _ ->
      remove_check_flag Do_Range_Check (exp_check_flags ?e) _ ->
      well_check_flagged_expr (update_exp_check_flags ?e _) ->
      eval_expr_x _ _ (update_exp_check_flags ?e _) _ ->
      optimize_expression_x _ (update_exp_check_flags ?e _) _ -> _ ,
     H2: well_typed_stack _ _,
     H3: remove_check_flag Do_Range_Check (exp_check_flags ?e) _,
     H4: well_check_flagged_expr (update_exp_check_flags ?e _),
     H5: eval_expr_x _ _ (update_exp_check_flags ?e _) _,
     H6: optimize_expression_x _ (update_exp_check_flags ?e _) _ |- _ ] => 
      specialize (H1 _ _ _ _ _ _ H2 H3 H4 H5 H6); auto
  end.
- (* selected component *)
  match goal with
  | [H: optimize_name_x _ _ _ |- _] => inversion H; clear H; subst
  end.
  match goal with
  | [H: eval_name_x _ _ _ _ |- _] => inversion H; clear H; subst
  end;
  match goal with
  | [H: well_check_flagged_name _ |- _] => inversion H; clear H; subst
  end.
  apply Eval_E_Selected_Component_X with (r:=r); auto.
Qed.


Lemma expression_checks_optimization_soundness: forall e e' st s v v',
  well_typed_stack st s ->
    well_check_flagged_expr e ->
      eval_expr_x st s e v ->
        optimize_expression_x st e (v', e') ->
          eval_expr_x st s e' v.
Proof.
  intros.
  specialize (rm_range_check_return_same_expr_checks _ H0); intros HZ1.
  specialize (update_exp_with_same_check_flags e); intros HZ.
  rewrite <- HZ in H0, H1, H2; clear HZ.
  specialize (expression_checks_optimization_soundness_help _ _ _ _ _ _ _ H HZ1 H0 H1 H2); 
  auto.
Qed.

Ltac apply_expression_optimization_soundness := 
  match goal with
  | [H1: well_typed_stack _ _, 
     H2: well_check_flagged_expr ?e, 
     H3: eval_expr_x _ _ ?e _, 
     H4: optimize_expression_x _ ?e _ |- _] =>
      specialize (expression_checks_optimization_soundness _ _ _ _ _ _ H1 H2 H3 H4)
  end.


(*
Lemma name_checks_optimization_soundness: forall n n' st s v v',
  well_typed_stack st s ->
    well_check_flagged_name n ->
      eval_name_x st s n v ->
        optimize_name_x st n (v', n') ->
          eval_name_x st s n' v.
Proof.
  intros;
  inversion H2; subst.
- match goal with
  | [H: eval_name_x _ _ _ _ |- _] => inversion H; subst
  end.
  apply Eval_E_Identifier_X; auto.
- match goal with
  | [H: eval_name_x _ _ _ _ |- _] => inversion H; subst
  end;
  match goal with
  | [H: well_check_flagged_name _ |- _] => inversion H; subst
  end;
  match goal with
  | [H1: exp_check_flags ?e = _,
     H2: ~ List.In _ (exp_check_flags ?e) |- _] => rewrite H1 in H2; smack
  | _ => idtac
  end.
  + (* 1 *)
  apply Eval_E_Indexed_Component_RTE_X; auto.
    rewrite update_exp_with_new_check_flags.
    apply removed_check_flag_notin with (cks:=(exp_check_flags e')); auto.
  match goal with
  | [H1: exp_check_flags ?e = _ ,
     H2: exp_check_flags ?e = _ |- _] => rewrite H2 in H1
  end.
  specialize (range_check_not_in_expr _ H15); intros HZ1.
  rewrite update_exp_with_new_check_flags in HZ1.
  apply_list_components_equal.

(*
  match goal with
  | [H1: optimize_expression_x _ ?e (_, ?e'),
     H2: ~(List.In ?x (exp_check_flags ?e)) |- _ ] => 
      specialize (optimize_expression_reserve_notin _ _ _ _ _ H1 H2);
      let HZ := fresh "HZ" in intros HZ
  end.

Lemma optimize_expr_to_same_checkflags: forall st e l u e' checkflags checkflags' cks1 cks2,
  optimize_expression_x st e (IntBetween l u, e') ->
    remove_check_flag Do_Range_Check (exp_check_flags e') checkflags ->
      remove_check_flag Do_Range_Check (exp_check_flags e) checkflags' ->
        (* two additional property for expression e *)
        exp_check_flags e = cks1 ++ Do_Range_Check :: cks2 ->
          well_check_flagged_expr (update_exp_check_flags e (cks1 ++ cks2)) ->
            optimize_expression_x st (update_exp_check_flags e checkflags') 
                                     (IntBetween l u, (update_exp_check_flags e' checkflags)).


Lemma optimize_expression_reserve_notin: forall st e v e' ck,
  optimize_expression_x st e (v, e') ->
    ~(List.In ck (exp_check_flags e)) ->
      ~(List.In ck (exp_check_flags e')).
*)

Qed.
*)


(** * Checks Optimization for Copy_In *)

Lemma copy_in_args_checks_optimization_soundness: forall st s params args f f' args',
  well_typed_stack st s ->
    well_check_flagged_args params args ->
      copy_in_x st s f params args f' ->
        optimize_args_x st params args args' ->
          copy_in_x st s f params args' f'.
Proof.
  intros st s params; revert st s;
  induction params; smack.
- match goal with
  | [H: copy_in_x _ _ _ _ _ _ |- _] => inversion H; subst
  end.
  match goal with
  | [H: optimize_args_x _ _ _ _ |- _] => inversion H; subst
  end.
  constructor.
- destruct args, args';
  match goal with 
  | [H: copy_in_x _ _ _ (?a :: ?al) nil _ |- _] => inversion H
  | [H: optimize_args_x _ (?a :: ?al) (?e :: ?el) nil |- _] => inversion H
  | _ => idtac
  end.
  match goal with
  | [H: optimize_args_x _ (?a :: ?al) (?e :: ?el) (?e' :: ?el') |- _ ] => inversion H; subst
  end.
  + (* 1. Args_Head_In *)
  match goal with
  | [H: copy_in_x _ _ _ (?a :: ?al) (?e :: ?el) _ |- _] => inversion H; subst
  end;
  match goal with
  | [H1: parameter_mode_x ?x = _,
     H2: parameter_mode_x ?x = _ |- _] => rewrite H1 in H2; inversion H2; clear H2
  end;
  match goal with
  | [H: well_check_flagged_args _ _ |- _] => inversion H; smack
  end;
  match goal with
  | [H1: exp_check_flags ?e = _ , H2: List.In _ (exp_check_flags ?e) -> False |- _] => rewrite H1 in H2; smack
  | _ => idtac
  end;
  [ apply Copy_In_Cons_In_RTE_X; auto;
      [ apply_optimize_expression_reserve_notin; auto |
        apply_expression_optimization_soundness; auto ] |
    apply Copy_In_Cons_In_X with (v:=v0) (f':=(STACK.push f (parameter_name_x a) v0)); auto;
      [ apply_optimize_expression_reserve_notin; auto |
        apply_expression_optimization_soundness; auto |
        specialize (IHparams _ _ _ _ _ _ H H14 H19 H13); auto] |
    | |
  ];
  apply_optimize_expression_reserve_range_check; intros HZ; destruct HZ as [cks1' [cks2' HZ1]];
  [ apply Copy_In_Cons_In_E_RTE_X with (cks1:=cks1') (cks2:=cks2'); auto |
    apply Copy_In_Cons_In_Range_RTE_X with (cks1:=cks1') (cks2:=cks2') (v:=v0) (l:=l) (u:=u); auto |
    apply Copy_In_Cons_In_Range_X with (cks1:=cks1') (cks2:=cks2') (v:=v0) (l:=l) (u:=u) 
                                     (f':=(STACK.push f (parameter_name_x a) (BasicV (Int v0)))); auto
  ];
  match goal with
  | [H1: exp_check_flags ?e = _ , H2: exp_check_flags ?e = _ |- _] => rewrite H2 in H1
  end;
  apply_range_check_not_in_expr; rewrite update_exp_with_new_check_flags; intros HZ0;
  apply_list_components_equal;
  apply_optimize_expression_range_check_notin; intros HZ2;
  apply_remove_a_unique_check; intros HZ3;
  apply_optimize_expr_to_same_checkflags; intros HZ4;
  apply_expression_optimization_soundness; auto.  
  specialize (IHparams _ _ _ _ _ _ H H16 H21 H13); auto.
  + (* 2. Args_Head_In_Range_Pass *)
  match goal with
  | [H: copy_in_x _ _ _ (?a :: ?al) (?e :: ?el) _ |- _] => inversion H; subst
  end;
  match goal with
  | [H1: parameter_mode_x ?x = _,
     H2: parameter_mode_x ?x = _ |- _] => rewrite H1 in H2; inversion H2; clear H2
  end;
  match goal with
  | [H: well_check_flagged_args _ _ |- _] => inversion H; smack
  end;
  match goal with
  | [H1: exp_check_flags ?e = _ , H2: List.In _ (exp_check_flags ?e) -> False |- _] => rewrite H1 in H2; smack
  | _ => idtac
  end;
  [ apply Copy_In_Cons_In_RTE_X; auto;
      [ rewrite update_exp_with_new_check_flags; apply_removed_check_flag_notin; auto |
        apply_optimize_expression_reserve_notin; intros HZ0;
        apply_remove_notin_check_flag; intros HZ1; apply_remove_check_flag_unique; intros HZ2; subst;
        rewrite update_exp_with_same_check_flags;
        apply_expression_optimization_soundness; auto
      ] |
    apply Copy_In_Cons_In_X with (v:=v) (f':=(STACK.push f (parameter_name_x a) v)); auto;
      [ rewrite update_exp_with_new_check_flags; apply_removed_check_flag_notin; auto |
        apply_optimize_expression_reserve_notin; intros HZ0;
        apply_remove_notin_check_flag; intros HZ1; apply_remove_check_flag_unique; intros HZ2; subst;
        rewrite update_exp_with_same_check_flags;
        apply_expression_optimization_soundness; auto |
        specialize (IHparams _ _ _ _ _ _ H H16 H22 H17); auto
      ] |
    | | 
  ];
  apply_optimize_expression_reserve_range_check; intros HZ; destruct HZ as [cks1' [cks2' HZ1]];
  [ apply Copy_In_Cons_In_RTE_X; auto |
    (* use contradictionary: possible value of argument is in the domain of its type, so there should be no overflow *)
    apply_extract_subtype_range_unique; intros HZ6; destruct HZ6; subst; admit |
    apply Copy_In_Cons_In_X with (v:=(BasicV (Int v))) (f':=(STACK.push f (parameter_name_x a) (BasicV (Int v)))); auto
  ];
  solve [
    rewrite update_exp_with_new_check_flags; apply_removed_check_flag_notin; auto |
    match goal with
    | [H1: exp_check_flags ?e = _ , H2: exp_check_flags ?e = _ |- _] => rewrite H2 in H1
    end;
    apply_range_check_not_in_expr; rewrite update_exp_with_new_check_flags; intros HZ0;
    apply_list_components_equal;
    apply_optimize_expression_range_check_notin; intros HZ2;
    apply_remove_a_unique_check; intros HZ3;
    apply_optimize_expr_to_same_checkflags; intros HZ4;
    apply_remove_check_flag_unique; intros HZ5; subst;
    apply_expression_optimization_soundness; auto |
    specialize (IHparams _ _ _ _ _ _ H H19 H24 H17); auto
  ].
  + (* 3. Args_Head_In_Range_Fail *)
  match goal with
  | [H: do_range_check _ _ _ (Exception RTE_Range) \/ do_range_check _ _ _ (Exception RTE_Range) |- _] => clear H
  end;
  match goal with
  | [H: copy_in_x _ _ _ (?a :: ?al) (?e :: ?el) _ |- _] => inversion H; subst
  end;
  match goal with
  | [H1: parameter_mode_x ?x = _,
     H2: parameter_mode_x ?x = _ |- _] => rewrite H1 in H2; inversion H2; clear H2
  end;
  match goal with
  | [H: well_check_flagged_args _ _ |- _] => inversion H; smack
  end;
  match goal with
  | [H1: exp_check_flags ?e = _ , H2: List.In _ (exp_check_flags ?e) -> False |- _] => rewrite H1 in H2; smack
  | _ => idtac
  end;
  [ apply Copy_In_Cons_In_RTE_X; auto;
      [ apply_optimize_expression_reserve_notin; auto |
        apply_expression_optimization_soundness; auto ] |
    apply Copy_In_Cons_In_X with (v:=v) (f':=(STACK.push f (parameter_name_x a) v)); auto;
      [ apply_optimize_expression_reserve_notin; auto |
        apply_expression_optimization_soundness; auto |
        specialize (IHparams _ _ _ _ _ _ H H13 H19 H14); auto] |
    | |
  ];
  apply_optimize_expression_reserve_range_check; intros HZ; destruct HZ as [cks1' [cks2' HZ1]];
  [ apply Copy_In_Cons_In_E_RTE_X with (cks1:=cks1') (cks2:=cks2'); auto |
    apply Copy_In_Cons_In_Range_RTE_X with (cks1:=cks1') (cks2:=cks2') (v:=v) (l:=l') (u:=u'); auto |
    apply Copy_In_Cons_In_Range_X with (cks1:=cks1') (cks2:=cks2') (v:=v) (l:=l') (u:=u') 
                                     (f':=(STACK.push f (parameter_name_x a) (BasicV (Int v)))); auto
  ];
  solve [
    match goal with
    | [H1: exp_check_flags ?e = _ , H2: exp_check_flags ?e = _ |- _] => rewrite H2 in H1
    end;
    apply_range_check_not_in_expr; rewrite update_exp_with_new_check_flags; intros HZ0;
    apply_list_components_equal;
    apply_optimize_expression_range_check_notin; intros HZ2;
    apply_remove_a_unique_check; intros HZ3;
    apply_optimize_expr_to_same_checkflags; intros HZ4;
    apply_expression_optimization_soundness; auto |
    apply_extract_subtype_range_unique; smack |
    specialize (IHparams _ _ _ _ _ _ H H16 H21 H14); auto
  ].
  + (* 4. Args_Head_Out_Arg *)  
  match goal with
  | [H: copy_in_x _ _ _ (?a :: ?al) (?e :: ?el) _ |- _] => inversion H; subst
  end;
  match goal with
  | [H1: parameter_mode_x ?x = _,
     H2: parameter_mode_x ?x = _ |- _] => rewrite H1 in H2; inversion H2; clear H2
  end;
  match goal with
  | [H: well_check_flagged_args _ _ |- _] => inversion H; smack
  end;
  apply Copy_In_Cons_Out_X with (f':=(STACK.push f (parameter_name_x a) Undefined)); auto;
  specialize (IHparams _ _ _ _ _ _ H H14 H21 H13); auto.
  + (* 5. Args_Head_Out_Param *)
  match goal with
  | [H: copy_in_x _ _ _ (?a :: ?al) (?e :: ?el) _ |- _] => inversion H; subst
  end;
  match goal with
  | [H1: parameter_mode_x ?x = _,
     H2: parameter_mode_x ?x = _ |- _] => rewrite H1 in H2; inversion H2; clear H2
  end;
  match goal with
  | [H: well_check_flagged_args _ _ |- _] => inversion H; smack
  end;
  apply Copy_In_Cons_Out_X with (f':=(STACK.push f (parameter_name_x a) Undefined)); auto;
  specialize (IHparams _ _ _ _ _ _ H H15 H22 H14); auto.
  + (* 6. Args_Head_Out_Range_Pass *)
  match goal with
  | [H: copy_in_x _ _ _ (?a :: ?al) (?e :: ?el) _ |- _] => inversion H; subst
  end;
  match goal with
  | [H1: parameter_mode_x ?x = _,
     H2: parameter_mode_x ?x = _ |- _] => rewrite H1 in H2; inversion H2; clear H2
  end;
  match goal with
  | [H: well_check_flagged_args _ _ |- _] => inversion H; smack
  end;
  apply Copy_In_Cons_Out_X with (f':=(STACK.push f (parameter_name_x a) Undefined)); auto;
  specialize (IHparams _ _ _ _ _ _ H H18 H25 H17); auto. 
  + (* 7. Args_Head_Out_Range_Fail *)
  match goal with
  | [H: copy_in_x _ _ _ (?a :: ?al) (?e :: ?el) _ |- _] => inversion H; subst
  end;
  match goal with
  | [H1: parameter_mode_x ?x = _,
     H2: parameter_mode_x ?x = _ |- _] => rewrite H1 in H2; inversion H2; clear H2
  end;
  match goal with
  | [H: well_check_flagged_args _ _ |- _] => inversion H; smack
  end;
  apply Copy_In_Cons_Out_X with (f':=(STACK.push f (parameter_name_x a) Undefined)); auto;
  specialize (IHparams _ _ _ _ _ _ H H16 H23 H15); auto.
  + (* 8. Args_Head_InOut_Param *)
  match goal with
  | [H: copy_in_x _ _ _ (?a :: ?al) (?e :: ?el) _ |- _] => inversion H; subst
  end;
  match goal with
  | [H1: parameter_mode_x ?x = _,
     H2: parameter_mode_x ?x = _ |- _] => rewrite H1 in H2; inversion H2; clear H2
  end;
  match goal with
  | [H: well_check_flagged_args _ _ |- _] => inversion H; smack
  end;
  solve [
    apply Copy_In_Cons_InOut_X with (v:=v) (f':=(STACK.push f (parameter_name_x a) v)); auto;
      specialize (IHparams _ _ _ _ _ _ H H14 H22 H12); auto |
    apply Copy_In_Cons_InOut_Range_RTE_X with (v:=v) (l:=l) (u:=u); auto |
    apply Copy_In_Cons_InOut_Range_X with (v:=v) (l:=l) (u:=u) (f':=(STACK.push f (parameter_name_x a) (BasicV (Int v)))); auto;
      try ((specialize (IHparams _ _ _ _ _ _ H H14 H24 H12)) || (specialize (IHparams _ _ _ _ _ _ H H13 H24 H12))); auto
  ].
  + (* 9. Args_Head_InOut_Arg *)
  match goal with
  | [H: copy_in_x _ _ _ (?a :: ?al) (?e :: ?el) _ |- _] => inversion H; subst
  end;
  match goal with
  | [H1: parameter_mode_x ?x = _,
     H2: parameter_mode_x ?x = _ |- _] => rewrite H1 in H2; inversion H2; clear H2
  end;
  match goal with
  | [H: well_check_flagged_args _ _ |- _] => inversion H; smack
  end;
  solve [
    apply Copy_In_Cons_InOut_X with (v:=v) (f':=(STACK.push f (parameter_name_x a) v)); auto;
      specialize (IHparams _ _ _ _ _ _ H H15 H23 H13); auto |
    apply Copy_In_Cons_InOut_Range_RTE_X with (v:=v) (l:=l) (u:=u); auto |
    apply Copy_In_Cons_InOut_Range_X with (v:=v) (l:=l) (u:=u) (f':=(STACK.push f (parameter_name_x a) (BasicV (Int v)))); auto;
      try (specialize (IHparams _ _ _ _ _ _ H H15 H25 H13) || (specialize (IHparams _ _ _ _ _ _ H H14 H25 H13))); auto
  ].
  + (* 10. Args_Head_InOut_Range_Pass *)
  match goal with
  | [H: copy_in_x _ _ _ (?a :: ?al) (?e :: ?el) _ |- _] => inversion H; subst
  end;
  match goal with
  | [H1: parameter_mode_x ?x = _,
     H2: parameter_mode_x ?x = _ |- _] => rewrite H1 in H2; inversion H2; clear H2
  end;
  [ apply Copy_In_Cons_InOut_X with (v:=v) (f':=(STACK.push f (parameter_name_x a) v)); auto |
    apply_extract_subtype_range_unique; smack;
    (* use contradictionary: possible value of argument is in the domain of its type, so there should be no overflow *)
    admit |
    apply Copy_In_Cons_InOut_X with (v:=(BasicV (Int v))) (f':=(STACK.push f (parameter_name_x a) (BasicV (Int v)))); auto
  ];
  solve [
    specialize (removed_check_flag_notin _ _ _ H16); intros HZ0; apply_notin_reserved_by_remove; auto |
    match goal with
    | [H: well_check_flagged_args _ _ |- _] => inversion H; smack
    end
  ].
  + (* 11. Args_Head_InOut_In_Range_Pass *)
  match goal with
  | [H: copy_in_x _ _ _ (?a :: ?al) (?e :: ?el) _ |- _] => inversion H; subst
  end;
  match goal with
  | [H1: parameter_mode_x ?x = _,
     H2: parameter_mode_x ?x = _ |- _] => rewrite H1 in H2; inversion H2; clear H2
  end;
  [ apply Copy_In_Cons_InOut_X with (v:=v) (f':=(STACK.push f (parameter_name_x a) v)); auto |
    apply_extract_subtype_range_unique; intros HZ0; destruct HZ0; subst;
    (* use contradictionary: possible value of argument is in the domain of its type, so there should be no overflow *)
    admit |
    apply Copy_In_Cons_InOut_X with (v:=(BasicV (Int v))) (f':=(STACK.push f (parameter_name_x a) (BasicV (Int v)))); auto
  ];
  solve [
    apply_removed_check_flag_notin; auto |
    match goal with
    | [H: well_check_flagged_args _ _ |- _] => inversion H; smack
    end
  ].
  + (* 12. Args_Head_InOut_Out_Range_Pass *)
  match goal with
  | [H: copy_in_x _ _ _ (?a :: ?al) (?e :: ?el) _ |- _] => inversion H; subst
  end;
  match goal with
  | [H1: parameter_mode_x ?x = _,
     H2: parameter_mode_x ?x = _ |- _] => rewrite H1 in H2; inversion H2; clear H2
  end;
  [ apply Copy_In_Cons_InOut_X with (v:=v) (f':=(STACK.push f (parameter_name_x a) v)); auto |
    apply Copy_In_Cons_InOut_Range_RTE_X with (v:=v) (l:=l) (u:=u); auto |
    apply Copy_In_Cons_InOut_Range_X with (v:=v) (l:=l) (u:=u) (f':=(STACK.push f (parameter_name_x a) (BasicV (Int v)))); auto
  ];
  solve [
    apply_notin_reserved_by_remove; auto |
    match goal with
    | [H: well_check_flagged_args _ _ |- _] => inversion H; smack
    end |
    assert(HZ0: beq_check_flag Do_Range_Check_On_CopyOut Do_Range_Check = false); unfold beq_check_flag; auto;
      apply_in_reserved_by_remove; auto |
    apply_extract_subtype_range_unique; smack
  ].
  + (* 13. Args_Head_InOut_Range_Fail *)
  match goal with
  | [H: copy_in_x _ _ _ (?a :: ?al) (?e :: ?el) _ |- _] => inversion H; subst
  end;
  match goal with
  | [H1: parameter_mode_x ?x = _,
     H2: parameter_mode_x ?x = _ |- _] => rewrite H1 in H2; inversion H2; clear H2
  end;
  [ apply Copy_In_Cons_InOut_X with (v:=v) (f':=(STACK.push f (parameter_name_x a) v)); auto |
    apply Copy_In_Cons_InOut_Range_RTE_X with (v:=v) (l:=l) (u:=u); auto |
    apply Copy_In_Cons_InOut_Range_X with (v:=v) (l:=l) (u:=u) 
                                        (f':=(STACK.push f (parameter_name_x a) (BasicV (Int v)))); auto
  ];
  solve [
    apply_extract_subtype_range_unique; smack |
    match goal with
    | [H: well_check_flagged_args _ _ |- _] => inversion H; smack
    end
  ].
Qed.

Ltac apply_copy_in_args_checks_optimization_soundness :=
  match goal with
  | [H1: well_typed_stack ?st ?s,
     H2: well_check_flagged_args ?params ?args,
     H3: copy_in_x ?st ?s ?f ?params ?args ?f',
     H4: optimize_args_x ?st ?params ?args ?args' |- _] =>
      specialize (copy_in_args_checks_optimization_soundness _ _ _ _ _ _ _ H1 H2 H3 H4)
  end.

(** * Checks Optimization for Copy_Out *)
Lemma copy_out_args_checks_optimization_soundness: forall st s f params args s' args',
  well_typed_stack st s ->    
    copy_out_x st s f params args s' -> 
      optimize_args_x st params args args' ->
        copy_out_x st s f params args' s'.
Proof.
  intros st s f params; revert st s f;
  induction params; smack.
- match goal with
  | [H: copy_out_x _ _ _ _ _ _ |- _] => inversion H; subst
  end.
  match goal with
  | [H: optimize_args_x _ _ _ _ |- _] => inversion H; subst
  end.
  constructor.
- destruct args, args';
  match goal with 
  | [H: copy_out_x _ _ _ (?a :: ?al) nil _ |- _] => inversion H
  | [H: optimize_args_x _ (?a :: ?al) (?e :: ?el) nil |- _] => inversion H
  | _ => idtac
  end.
  match goal with
  | [H: optimize_args_x _ (?a :: ?al) (?e :: ?el) (?e' :: ?el') |- _ ] => inversion H; subst
  end.
  + (* 1. Args_Head_In *)
  match goal with
  | [H: copy_out_x _ _ _ (?a :: ?al) (?e :: ?el) _ |- _] => inversion H; subst
  end;
  match goal with
  | [H: parameter_mode_x ?x = _ |- _] => rewrite H in *
  end;
  match goal with
  | [H: In = Out \/ In = In_Out |- _] => smack
  | _ => idtac
  end.
  apply Copy_Out_Cons_In_X; auto.
    specialize (IHparams _ _ _ _ _ _ H H15 H12); auto.
  + (* 2. Args_Head_In_Range_Pass *)
  match goal with
  | [H: copy_out_x _ _ _ (?a :: ?al) (?e :: ?el) _ |- _] => inversion H; subst
  end;
  match goal with
  | [H: parameter_mode_x ?x = _ |- _] => rewrite H in *
  end;
  match goal with
  | [H: In = Out \/ In = In_Out |- _] => smack
  | _ => idtac
  end.
  apply Copy_Out_Cons_In_X; auto.
    specialize (IHparams _ _ _ _ _ _ H H18 H16); auto.
  + (* 3. Args_Head_In_Range_Fail *)
  match goal with
  | [H: copy_out_x _ _ _ (?a :: ?al) (?e :: ?el) _ |- _] => inversion H; subst
  end;
  match goal with
  | [H: parameter_mode_x ?x = _ |- _] => rewrite H in *
  end;
  match goal with
  | [H: In = Out \/ In = In_Out |- _] => smack
  | _ => idtac
  end.
  apply Copy_Out_Cons_In_X; auto.
    specialize (IHparams _ _ _ _ _ _ H H16 H13); auto.
  + (* 4. Args_Head_Out_Arg *)
  match goal with
  | [H: copy_out_x _ _ _ (?a :: ?al) (?e :: ?el) _ |- _] => inversion H; subst
  end;
  match goal with
  | [H1: parameter_mode_x ?x = _,
     H2: parameter_mode_x ?x = _ |- _] => rewrite H1 in H2; inversion H2
  | _ => idtac
  end.
  apply Copy_Out_Cons_Out_X with (v:=v) (s':=s'0); auto. 
    assert(HE1: well_typed_stack st s'0). admit.
    specialize (IHparams _ _ _ _ _ _ HE1 H22 H12); auto.
  apply Copy_Out_Cons_Out_Range_RTE_X with (v:=v) (t:=t) (l:=l) (u:=u); auto.
    match goal with
    | [H1: fetch_exp_type_x _ _ = _, H2: fetch_exp_type_x _ _ = _ |- _] => rewrite H1 in H2; inversion H2; subst; auto
    end.
  apply Copy_Out_Cons_Out_Range_X with (v:=v) (t:=t) (l:=l) (u:=u) (s':=s'0); auto.
    match goal with
    | [H1: fetch_exp_type_x _ _ = _, H2: fetch_exp_type_x _ _ = _ |- _] => rewrite H1 in H2; inversion H2; subst; auto
    end.
    assert(HE1: well_typed_stack st s'0). admit.
    specialize (IHparams _ _ _ _ _ _ HE1 H25 H12); auto.
  + (* 5. Args_Head_Out_Param *)
  match goal with
  | [H: copy_out_x _ _ _ (?a :: ?al) (?e :: ?el) _ |- _] => inversion H; subst
  end;
  match goal with
  | [H1: parameter_mode_x ?x = _,
     H2: parameter_mode_x ?x = _ |- _] => rewrite H1 in H2; inversion H2
  | _ => idtac
  end.
  apply Copy_Out_Cons_Out_X with (v:=v) (s':=s'0); auto. 
    assert(HE1: well_typed_stack st s'0). admit.
    specialize (IHparams _ _ _ _ _ _ HE1 H23 H13); auto.
  apply Copy_Out_Cons_Out_Range_RTE_X with (v:=v) (t:=t) (l:=l) (u:=u); auto.
    match goal with
    | [H1: fetch_exp_type_x _ _ = _, H2: fetch_exp_type_x _ _ = _ |- _] => rewrite H1 in H2; inversion H2; subst; auto
    end.
  apply Copy_Out_Cons_Out_Range_X with (v:=v) (t:=t) (l:=l) (u:=u) (s':=s'0); auto.
    match goal with
    | [H1: fetch_exp_type_x _ _ = _, H2: fetch_exp_type_x _ _ = _ |- _] => rewrite H1 in H2; inversion H2; subst; auto
    end.
    assert(HE1: well_typed_stack st s'0). admit.
    specialize (IHparams _ _ _ _ _ _ HE1 H26 H13); auto.
  + (* 6. Args_Head_Out_Range_Pass *)
  match goal with
  | [H: copy_out_x _ _ _ (?a :: ?al) (?e :: ?el) _ |- _] => inversion H; subst
  end;
  match goal with
  | [H1: parameter_mode_x ?x = _,
     H2: parameter_mode_x ?x = _ |- _] => rewrite H1 in H2; inversion H2
  | _ => idtac
  end.
  apply Copy_Out_Cons_Out_X with (v:=v) (s':=s'0); auto. 
    apply_removed_check_flag_notin; auto.
    assert(HE1: well_typed_stack st s'0). admit.
    specialize (IHparams _ _ _ _ _ _ HE1 H26 H16); auto.
  match goal with
  | [H1: fetch_exp_type_x _ _ = _ , H2: fetch_exp_type_x _ _ = _ |- _] => rewrite H2 in H1; inversion H1; subst
  end.
  apply_extract_subtype_range_unique; intros HZ0; destruct HZ0; subst.
  (* use contradictionary to prove... *)
  admit.
  apply Copy_Out_Cons_Out_X with (v:=(BasicV (Int v))) (s':=s'0); auto.
    apply_removed_check_flag_notin; auto.
    assert(HE1: well_typed_stack st s'0). admit.
    specialize (IHparams _ _ _ _ _ _ HE1 H29 H16); auto.
  + (* 7. Args_Head_Out_Range_Fail *)
  match goal with
  | [H: copy_out_x _ _ _ (?a :: ?al) (?e :: ?el) _ |- _] => inversion H; subst
  end;
  match goal with
  | [H1: parameter_mode_x ?x = _,
     H2: parameter_mode_x ?x = _ |- _] => rewrite H1 in H2; inversion H2
  | _ => idtac
  end.
  apply Copy_Out_Cons_Out_X with (v:=v) (s':=s'0); auto. 
    assert(HE1: well_typed_stack st s'0). admit.
    specialize (IHparams _ _ _ _ _ _ HE1 H24 H14); auto.
  apply Copy_Out_Cons_Out_Range_RTE_X with (v:=v) (t:=t) (l:=l') (u:=u'); auto.
    match goal with
    | [H1: fetch_exp_type_x _ _ = _, H2: fetch_exp_type_x _ _ = _ |- _] => rewrite H1 in H2; inversion H2; subst; auto
    end. apply_extract_subtype_range_unique; smack.
  apply Copy_Out_Cons_Out_Range_X with (v:=v) (t:=t) (l:=l') (u:=u') (s':=s'0); auto.
    match goal with
    | [H1: fetch_exp_type_x _ _ = _, H2: fetch_exp_type_x _ _ = _ |- _] => rewrite H1 in H2; inversion H2; subst; auto
    end. apply_extract_subtype_range_unique; smack.
    assert(HE1: well_typed_stack st s'0). admit.
    specialize (IHparams _ _ _ _ _ _ HE1 H27 H14); auto.
  + (* 8. Args_Head_InOut_Param *)
  match goal with
  | [H: copy_out_x _ _ _ (?a :: ?al) (?e :: ?el) _ |- _] => inversion H; subst
  end;
  match goal with
  | [H1: parameter_mode_x ?x = _,
     H2: parameter_mode_x ?x = _ |- _] => rewrite H1 in H2; inversion H2
  | _ => idtac
  end.
  apply Copy_Out_Cons_Out_X with (v:=v) (s':=s'0); auto. 
    assert(HE1: well_typed_stack st s'0). admit.
    specialize (IHparams _ _ _ _ _ _ HE1 H21 H11); auto.
  apply Copy_Out_Cons_Out_Range_RTE_X with (v:=v) (t:=t) (l:=l) (u:=u); auto.
  apply Copy_Out_Cons_Out_Range_X with (v:=v) (t:=t) (l:=l) (u:=u) (s':=s'0); auto.
    assert(HE1: well_typed_stack st s'0). admit.
    specialize (IHparams _ _ _ _ _ _ HE1 H24 H11); auto.
  + (* 9. Args_Head_InOut_Arg *)
  match goal with
  | [H: copy_out_x _ _ _ (?a :: ?al) (?e :: ?el) _ |- _] => inversion H; subst
  end;
  match goal with
  | [H1: parameter_mode_x ?x = _,
     H2: parameter_mode_x ?x = _ |- _] => rewrite H1 in H2; inversion H2
  | _ => idtac
  end.
  apply Copy_Out_Cons_Out_X with (v:=v) (s':=s'0); auto. 
    assert(HE1: well_typed_stack st s'0). admit.
    specialize (IHparams _ _ _ _ _ _ HE1 H22 H12); auto.
  apply Copy_Out_Cons_Out_Range_RTE_X with (v:=v) (t:=t) (l:=l) (u:=u); auto.
    match goal with
    | [H1: fetch_exp_type_x _ _ = _, H2: fetch_exp_type_x _ _ = _ |- _] => rewrite H1 in H2; inversion H2; subst; auto
    end.
  apply Copy_Out_Cons_Out_Range_X with (v:=v) (t:=t) (l:=l) (u:=u) (s':=s'0); auto.
    match goal with
    | [H1: fetch_exp_type_x _ _ = _, H2: fetch_exp_type_x _ _ = _ |- _] => rewrite H1 in H2; inversion H2; subst; auto
    end.
    assert(HE1: well_typed_stack st s'0). admit.
    specialize (IHparams _ _ _ _ _ _ HE1 H25 H12); auto.
  + (* 10. Args_Head_InOut_Range_Pass *)
  match goal with
  | [H: copy_out_x _ _ _ (?a :: ?al) (?e :: ?el) _ |- _] => inversion H; subst
  end;
  match goal with
  | [H1: parameter_mode_x ?x = _,
     H2: parameter_mode_x ?x = _ |- _] => rewrite H1 in H2; inversion H2
  | _ => idtac
  end.
  apply Copy_Out_Cons_Out_X with (v:=v) (s':=s'0); auto. 
    apply_removed_check_flag_notin; auto.
    assert(HE1: well_typed_stack st s'0). admit.
    specialize (IHparams _ _ _ _ _ _ HE1 H27 H17); auto.
  match goal with
    | [H1: fetch_exp_type_x _ _ = _, H2: fetch_exp_type_x _ _ = _ |- _] => rewrite H2 in H1; inversion H1; subst; auto
  end.
  apply_extract_subtype_range_unique; intros HZ0; destruct HZ0; subst.
  (* proof by contraditionary ... *)
  admit.
  apply Copy_Out_Cons_Out_X with (v:=(BasicV (Int v))) (s':=s'0); auto.
    apply_removed_check_flag_notin; auto.
    assert(HE1: well_typed_stack st s'0). admit.
    specialize (IHparams _ _ _ _ _ _ HE1 H30 H17); auto.
  + (* 11. Args_Head_InOut_In_Range_Pass *)
  match goal with
  | [H: copy_out_x _ _ _ (?a :: ?al) (?e :: ?el) _ |- _] => inversion H; subst
  end;
  match goal with
  | [H1: parameter_mode_x ?x = _,
     H2: parameter_mode_x ?x = _ |- _] => rewrite H1 in H2; inversion H2
  | _ => idtac
  end.
  apply Copy_Out_Cons_Out_X with (v:=v) (s':=s'0); auto. 
    apply_notin_reserved_by_remove; auto.
    assert(HE1: well_typed_stack st s'0). admit.
    specialize (IHparams _ _ _ _ _ _ HE1 H26 H16); auto.
  apply Copy_Out_Cons_Out_Range_RTE_X with (v:=v) (t:=t) (l:=l') (u:=u'); auto.
    assert(HZ0: beq_check_flag Do_Range_Check Do_Range_Check_On_CopyOut = false); unfold beq_check_flag; auto.
    apply_in_reserved_by_remove; auto.
    match goal with
    | [H1: fetch_exp_type_x _ _ = _, H2: fetch_exp_type_x _ _ = _ |- _] => rewrite H2 in H1; inversion H1; subst
    end. apply_extract_subtype_range_unique; smack.
  apply Copy_Out_Cons_Out_Range_X with (v:=v) (t:=t) (l:=l') (u:=u') (s':=s'0); auto.
    assert(HZ0: beq_check_flag Do_Range_Check Do_Range_Check_On_CopyOut = false); unfold beq_check_flag; auto.
    apply_in_reserved_by_remove; auto.
    match goal with
    | [H1: fetch_exp_type_x _ _ = _, H2: fetch_exp_type_x _ _ = _ |- _] => rewrite H1 in H2; inversion H2; subst; auto
    end. apply_extract_subtype_range_unique; smack.
    assert(HE1: well_typed_stack st s'0). admit.
    specialize (IHparams _ _ _ _ _ _ HE1 H29 H16); auto. 
  + (* 12. Args_Head_InOut_Out_Range_Pass *)
  match goal with
  | [H: copy_out_x _ _ _ (?a :: ?al) (?e :: ?el) _ |- _] => inversion H; subst
  end;
  match goal with
  | [H1: parameter_mode_x ?x = _,
     H2: parameter_mode_x ?x = _ |- _] => rewrite H1 in H2; inversion H2
  | _ => idtac
  end.
  apply Copy_Out_Cons_Out_X with (v:=v) (s':=s'0); auto. 
    apply_notin_reserved_by_remove; auto.
    assert(HE1: well_typed_stack st s'0). admit.
    specialize (IHparams _ _ _ _ _ _ HE1 H26 H16); auto.
  (* proof by contraditionary ... *)
  match goal with
    | [H1: fetch_exp_type_x _ _ = _, H2: fetch_exp_type_x _ _ = _ |- _] => rewrite H1 in H2; inversion H2; subst
  end. apply_extract_subtype_range_unique; intros HZ0; destruct HZ0; subst.
  admit.
  apply Copy_Out_Cons_Out_X with (v:=(BasicV (Int v))) (s':=s'0); auto.
    apply_removed_check_flag_notin; auto.
    assert(HE1: well_typed_stack st s'0). admit.
    specialize (IHparams _ _ _ _ _ _ HE1 H29 H16); auto.
  + (* 13. Args_Head_InOut_InOut_Range_Fail *)
  match goal with
  | [H: copy_out_x _ _ _ (?a :: ?al) (?e :: ?el) _ |- _] => inversion H; subst
  end;
  match goal with
  | [H1: parameter_mode_x ?x = _,
     H2: parameter_mode_x ?x = _ |- _] => rewrite H1 in H2; inversion H2
  | _ => idtac
  end.
  apply Copy_Out_Cons_Out_X with (v:=v) (s':=s'0); auto. 
    assert(HE1: well_typed_stack st s'0). admit.
    specialize (IHparams _ _ _ _ _ _ HE1 H25 H15); auto.
  apply Copy_Out_Cons_Out_Range_RTE_X with (v:=v) (t:=t) (l:=l') (u:=u'); auto.
    match goal with
    | [H1: fetch_exp_type_x _ _ = _, H2: fetch_exp_type_x _ _ = _ |- _] => rewrite H1 in H2; inversion H2; subst; auto
    end. apply_extract_subtype_range_unique; smack.
  apply Copy_Out_Cons_Out_Range_X with (v:=v) (t:=t) (l:=l') (u:=u') (s':=s'0); auto.
    match goal with
    | [H1: fetch_exp_type_x _ _ = _, H2: fetch_exp_type_x _ _ = _ |- _] => rewrite H1 in H2; inversion H2; subst; auto
    end. apply_extract_subtype_range_unique; smack.
    assert(HE1: well_typed_stack st s'0). admit.
    specialize (IHparams _ _ _ _ _ _ HE1 H28 H15); auto.
Qed.

Ltac apply_copy_out_args_checks_optimization_soundness :=
  match goal with
  | [H1: well_typed_stack ?st ?s,
     H2: copy_out_x ?st ?s ?f ?params ?args ?s',
     H3: optimize_args_x ?st ?params ?args ?args' |- _] =>
      specialize (copy_out_args_checks_optimization_soundness _ _ _ _ _ _ _ H1 H2 H3)
  end.

Lemma store_update_optimization_soundness: forall st s x v s' v' x',
  well_typed_stack st s ->
    well_check_flagged_name x -> 
      storeUpdate_x st s x v s' ->
        optimize_name_x st x (v', x') ->
          storeUpdate_x st s x' v s'.
Proof.
  intros.
  inversion H1; subst.
- (* 1. SU_Identifier_X *)
  match goal with
  | [H: optimize_name_x _ _ _ |- _] => inversion H; subst; auto
  end.
- (* 2. SU_Indexed_Component_RTE_X *)
  match goal with
  | [H: well_check_flagged_name _ |- _] => inversion H; subst
  end;
  match goal with
  | [H1: exp_check_flags ?e = _, 
     H2: ~ List.In _ (exp_check_flags ?e) |- _] => rewrite H1 in H2; smack
  end.
- (* 3. SU_Indexed_Component_Undef_X *)
  match goal with
  | [H: well_check_flagged_name _ |- _] => inversion H; subst
  end;
  match goal with
  | [H1: exp_check_flags ?e = _, 
     H2: ~ List.In _ (exp_check_flags ?e) |- _] => rewrite H1 in H2; smack
  end.
- (* 4. SU_Indexed_Component_X *)
  match goal with
  | [H: well_check_flagged_name _ |- _] => inversion H; subst
  end;
  match goal with
  | [H1: exp_check_flags ?e = _, 
     H2: ~ List.In _ (exp_check_flags ?e) |- _] => rewrite H1 in H2; smack
  end.
- (* 5. SU_Indexed_Component_E_RTE_X *)
  match goal with
  | [H: optimize_name_x _ _ _ |- _] => inversion H; subst; auto
  end;
  match goal with
  | [H: well_check_flagged_name _ |- _] => inversion H; subst
  end;
  apply_optimize_expression_reserve_range_check; intros HZ; destruct HZ as [cks1' [cks2' HZ1]];
  [ apply SU_Indexed_Component_RTE_X; auto |
    apply SU_Indexed_Component_E_RTE_X with (cks1:=cks1') (cks2:=cks2'); auto
  ];
  [ rewrite update_exp_with_new_check_flags; apply_removed_check_flag_notin; auto | | ];
  match goal with
  | [H1: exp_check_flags ?e = _ , H2: exp_check_flags ?e = _ |- _] => rewrite H2 in H1
  end;
  apply_range_check_not_in_expr; rewrite update_exp_with_new_check_flags; intros HZ0;
  apply_list_components_equal;
  apply_optimize_expression_range_check_notin; intros HZ2;
  apply_remove_a_unique_check; intros HZ3;
  [ apply_remove_check_flag_unique; intros HZ; subst | ];
  apply_optimize_expr_to_same_checkflags; intros HZ4;
  apply_expression_optimization_soundness; auto.
- (* 6. SU_Indexed_Component_Range_RTE_X *)
  match goal with
  | [H: optimize_name_x _ _ _ |- _] => inversion H; subst; auto
  end;
  match goal with
  | [H1: fetch_exp_type_x _ _ = _, 
     H2: fetch_exp_type_x _ _ = _ |- _] => rewrite H2 in H1; inversion H1; subst
  end;
  match goal with
  | [H: well_check_flagged_name _ |- _] => inversion H; subst
  end;
  apply_extract_array_index_range_x_unique; intros HZ0; destruct HZ0; subst;
  apply_optimize_expression_reserve_range_check; intros HZ; destruct HZ as [cks1' [cks2' HZ1]].
  (* 6.1 *)  
  (* use contradiction to prove it *)
  admit.
  (* 6.2 *)  
  apply SU_Indexed_Component_Range_RTE_X with (cks1:=cks1') (cks2:=cks2') (i:=i) (t:=t) (l:=l') (u:=u'); auto.
  match goal with
  | [H1: exp_check_flags ?e = _ , H2: exp_check_flags ?e = _ |- _] => rewrite H2 in H1
  end;
  apply_range_check_not_in_expr; rewrite update_exp_with_new_check_flags; intros HZ0;
  apply_list_components_equal;
  apply_optimize_expression_range_check_notin; intros HZ2;
  apply_remove_a_unique_check; intros HZ3;
  apply_optimize_expr_to_same_checkflags; intros HZ4;
  apply_expression_optimization_soundness; auto.
- (* 7. SU_Indexed_Component_Range_Undef_X *)
  match goal with
  | [H: optimize_name_x _ _ _ |- _] => inversion H; subst; auto
  end;
  match goal with
  | [H1: fetch_exp_type_x _ _ = _, 
     H2: fetch_exp_type_x _ _ = _ |- _] => rewrite H2 in H1; inversion H1; subst
  end;
  match goal with
  | [H: well_check_flagged_name _ |- _] => inversion H; subst
  end;
  apply_optimize_expression_reserve_range_check; intros HZ; destruct HZ as [cks1' [cks2' HZ1]];
  [ apply SU_Indexed_Component_Undef_X with (i:=i); auto |
    apply SU_Indexed_Component_Range_Undef_X with (cks1:=cks1') (cks2:=cks2') (i:=i) (t:=t) (l:=l') (u:=u'); auto
  ];
  [ rewrite update_exp_with_new_check_flags; apply_removed_check_flag_notin; auto | | | 
    apply_extract_array_index_range_x_unique; smack
  ];
  match goal with
  | [H1: exp_check_flags ?e = _ , H2: exp_check_flags ?e = _ |- _] => rewrite H2 in H1
  end;
  apply_range_check_not_in_expr; rewrite update_exp_with_new_check_flags; intros HZ0;
  apply_list_components_equal;
  apply_optimize_expression_range_check_notin; intros HZ2;
  apply_remove_a_unique_check; intros HZ3;
  [ apply_remove_check_flag_unique; intros HZ; subst | ];
  apply_optimize_expr_to_same_checkflags; intros HZ4;
  apply_expression_optimization_soundness; auto.
- (* 8. SU_Indexed_Component_Range_X *)
  match goal with
  | [H: optimize_name_x _ _ _ |- _] => inversion H; subst; auto
  end;
  match goal with
  | [H1: fetch_exp_type_x _ _ = _, 
     H2: fetch_exp_type_x _ _ = _ |- _] => rewrite H2 in H1; inversion H1; subst
  end;
  match goal with
  | [H: well_check_flagged_name _ |- _] => inversion H; subst
  end;
  apply_optimize_expression_reserve_range_check; intros HZ; destruct HZ as [cks1' [cks2' HZ1]];
  [ apply SU_Indexed_Component_X with (i:=i) (a:=a) (a1:=(arrayUpdate a i v0)); auto |
    apply SU_Indexed_Component_Range_X with (cks1:=cks1') (cks2:=cks2') (i:=i) (t:=t) 
                                          (l:=l) (u:=u) (a:=a) (a1:=(arrayUpdate a i v0)); auto
  ];
  [ rewrite update_exp_with_new_check_flags; apply_removed_check_flag_notin; auto | | ];
  match goal with
  | [H1: exp_check_flags ?e = _ , H2: exp_check_flags ?e = _ |- _] => rewrite H2 in H1
  end;
  apply_range_check_not_in_expr; rewrite update_exp_with_new_check_flags; intros HZ0;
  apply_list_components_equal;
  apply_optimize_expression_range_check_notin; intros HZ2;
  apply_remove_a_unique_check; intros HZ3;
  [ apply_remove_check_flag_unique; intros HZ; subst | ];
  apply_optimize_expr_to_same_checkflags; intros HZ4;
  apply_expression_optimization_soundness; auto.
- (* 9. SU_Selected_Component_Undef_X *)
  match goal with
  | [H: optimize_name_x _ _ _ |- _] => inversion H; subst; auto
  end.
- (* 10. SU_Selected_Component_X *)
  match goal with
  | [H: optimize_name_x _ _ _ |- _] => inversion H; subst; auto
  end.
Qed.

Ltac apply_store_update_optimization_soundness :=
  match goal with
  | [H1: well_typed_stack ?st ?s,
     H2: well_check_flagged_name ?x, 
     H3: storeUpdate_x ?st ?s ?x ?v ?s',
     H4: optimize_name_x ?st ?x (_, ?x') |- _] =>
      specialize (store_update_optimization_soundness _ _ _ _ _ _ _ H1 H2 H3 H4)
  end.


(** * Checks Optimizatioin Soundness for Statement *)

Lemma statement_checks_optimization_soundness: forall st s c s' c',
  eval_stmt_x st s c s' ->
    optimize_statement_x st c c' ->
      well_typed_stack st s ->
        well_check_flagged_stmt st c ->
          eval_stmt_x st s c' s'.
Proof.
  intros st s c s' c' H; revert c';
  induction H; intros.
- (* 1. Eval_S_Null *)
  match goal with
  | [H: optimize_statement_x _ _ _ |- _] => inversion H; subst; auto
  end; constructor.
- (* 2. Eval_S_Assignment_RTE *)
  match goal with
  | [H: optimize_statement_x _ _ _ |- _] => inversion H; subst; auto
  end;
  match goal with
  | [H: well_check_flagged_stmt _ _ |- _] => inversion H; subst
  end;
  match goal with
  | [H1: exp_check_flags ?e = _, 
     H2: ~ List.In _ (exp_check_flags ?e) |- _] => rewrite H1 in H2; smack
  | _ => idtac
  end;
  [ apply Eval_S_Assignment_RTE_X; auto |
    apply Eval_S_Assignment_RTE_X; auto
  ];
  [ rewrite update_exp_with_new_check_flags; apply_removed_check_flag_notin; auto |
    apply_optimize_expression_reserve_notin; intros HZ0;
    apply_remove_notin_check_flag; intros HZ1;
    apply_remove_check_flag_unique; intros HZ2; subst;
    rewrite update_exp_with_same_check_flags;
    apply_expression_optimization_soundness; auto |
    apply_optimize_expression_reserve_notin; auto |
    apply_expression_optimization_soundness; auto
  ].
- (* 3. Eval_S_Assignment *)
  match goal with
  | [H: optimize_statement_x _ _ _ |- _] => inversion H; subst; auto
  end;
  match goal with
  | [H: well_check_flagged_stmt _ _ |- _] => inversion H; subst
  end;
  match goal with
  | [H1: exp_check_flags ?e = _, 
     H2: ~ List.In _ (exp_check_flags ?e) |- _] => rewrite H1 in H2; smack
  | _ => idtac
  end;
  [ apply Eval_S_Assignment_X with (v:=v); auto |
    apply Eval_S_Assignment_X with (v:=v); auto
  ];
  [ rewrite update_exp_with_new_check_flags; apply_removed_check_flag_notin; auto |
    apply_optimize_expression_reserve_notin; intros HZ0;
    apply_remove_notin_check_flag; intros HZ1;
    apply_remove_check_flag_unique; intros HZ2; subst;
    rewrite update_exp_with_same_check_flags;
    apply_expression_optimization_soundness; auto |
    apply_store_update_optimization_soundness; auto |
    apply_optimize_expression_reserve_notin; auto |
    apply_expression_optimization_soundness; auto |
    apply_store_update_optimization_soundness; auto
  ].
- (* 4. Eval_S_Assignment_E_RTE_X *)
  match goal with
  | [H: optimize_statement_x _ _ _ |- _] => inversion H; subst; auto
  end;
  match goal with
  | [H: well_check_flagged_stmt _ _ |- _] => inversion H; subst
  end;
  match goal with
  | [H1: exp_check_flags ?e = _, 
     H2: ~ List.In _ (exp_check_flags ?e) |- _] => rewrite H1 in H2; smack
  | _ => idtac
  end;
  apply_optimize_expression_reserve_range_check; intros HZ; destruct HZ as [cks1' [cks2' HZ1]];
  [ apply Eval_S_Assignment_RTE_X; auto |
    apply Eval_S_Assignment_E_RTE_X with (cks1:=cks1') (cks2:=cks2'); auto
  ];
  [ rewrite update_exp_with_new_check_flags; apply_removed_check_flag_notin; auto |
    match goal with
    | [H1: exp_check_flags ?e = _ , H2: exp_check_flags ?e = _ |- _] => rewrite H2 in H1
    end;
    apply_range_check_not_in_expr; rewrite update_exp_with_new_check_flags; intros HZ0;
    apply_list_components_equal;
    apply_optimize_expr_to_same_checkflags; intros HZ2;
    apply_expression_optimization_soundness; auto |
    match goal with
    | [H1: exp_check_flags ?e = _ , H2: exp_check_flags ?e = _ |- _] => rewrite H2 in H1
    end;
    apply_range_check_not_in_expr; rewrite update_exp_with_new_check_flags; intros HZ0;
    apply_list_components_equal;
    apply_optimize_expression_range_check_notin; intros HZ2;
    apply_remove_a_unique_check; intros HZ3;
    apply_optimize_expr_to_same_checkflags; intros HZ4;
    apply_expression_optimization_soundness; auto
  ].
- (* 5. Eval_S_Assignment_Range_RTE_X *)
  match goal with
  | [H: optimize_statement_x _ _ _ |- _] => inversion H; subst; auto
  end;
  match goal with
  | [H: well_check_flagged_stmt _ _ |- _] => inversion H; subst
  end;
  match goal with
  | [H1: exp_check_flags ?e = _, 
     H2: ~ List.In _ (exp_check_flags ?e) |- _] => rewrite H1 in H2; smack
  | _ => idtac
  end.
  + (* 5.1 Assignment_Range_Pass *)
  (* use contradiction to prove it *)
  admit.
  + (* 5.1 Assignment_Range_Fail *)
  apply_optimize_expression_reserve_range_check; intros HZ; destruct HZ as [cks1' [cks2' HZ1]].
  apply Eval_S_Assignment_Range_RTE_X with (cks1:=cks1') (cks2:=cks2') (v:=v) (t:=t) (l:=l) (u:=u); auto.
    match goal with
    | [H1: exp_check_flags ?e = _ , H2: exp_check_flags ?e = _ |- _] => rewrite H2 in H1
    end;
    apply_range_check_not_in_expr; rewrite update_exp_with_new_check_flags; intros HZ0;
    apply_list_components_equal;
    apply_optimize_expression_range_check_notin; intros HZ2;
    apply_remove_a_unique_check; intros HZ3;
    apply_optimize_expr_to_same_checkflags; intros HZ4;
    apply_expression_optimization_soundness; auto.
    apply_optimized_name_reserve_astnum; intro HZ0; rewrite HZ0 in *; auto.
- (* 6. Eval_S_Assignment_Range_X *)
  match goal with
  | [H: optimize_statement_x _ _ _ |- _] => inversion H; subst; auto
  end;
  match goal with
  | [H: well_check_flagged_stmt _ _ |- _] => inversion H; subst
  end;
  match goal with
  | [H1: exp_check_flags ?e = _, 
     H2: ~ List.In _ (exp_check_flags ?e) |- _] => rewrite H1 in H2; smack
  | _ => idtac
  end;
  apply_optimize_expression_reserve_range_check; intros HZ; destruct HZ as [cks1' [cks2' HZ1]];
  [ apply Eval_S_Assignment_X with (v:=(BasicV (Int v))); auto |
    apply Eval_S_Assignment_Range_X with (cks1:=cks1') (cks2:=cks2') (v:=v) (t:=t) (l:=l) (u:=u); auto
  ];
  [ rewrite update_exp_with_new_check_flags; apply_removed_check_flag_notin; auto |
    match goal with
    | [H1: exp_check_flags ?e = _ , H2: exp_check_flags ?e = _ |- _] => rewrite H2 in H1
    end;
    apply_range_check_not_in_expr; rewrite update_exp_with_new_check_flags; intros HZ0;
    apply_list_components_equal;
    apply_optimize_expr_to_same_checkflags; intros HZ2;
    apply_expression_optimization_soundness; auto |
    apply_store_update_optimization_soundness; auto |
    match goal with
    | [H1: exp_check_flags ?e = _ , H2: exp_check_flags ?e = _ |- _] => rewrite H2 in H1
    end;
    apply_range_check_not_in_expr; rewrite update_exp_with_new_check_flags; intros HZ0;
    apply_list_components_equal;
    apply_optimize_expression_range_check_notin; intros HZ2;
    apply_remove_a_unique_check; intros HZ3;
    apply_optimize_expr_to_same_checkflags; intros HZ4;
    apply_expression_optimization_soundness; auto |
    apply_optimized_name_reserve_astnum; intro HZ; rewrite HZ in *; auto |
    apply_store_update_optimization_soundness; auto
  ].
- (* 7. Eval_S_If_RTE_X *)
  match goal with
  | [H: optimize_statement_x _ _ _ |- _] => inversion H; subst; auto
  end;
  match goal with
  | [H: well_check_flagged_stmt _ _ |- _] => inversion H; subst
  end;
  apply Eval_S_If_RTE_X; auto;
  apply_expression_optimization_soundness; auto.
- (* 8. Eval_S_If_True_X *)
  match goal with
  | [H: optimize_statement_x _ _ _ |- _] => inversion H; subst; auto
  end;
  match goal with
  | [H: well_check_flagged_stmt _ _ |- _] => inversion H; subst
  end;
  apply Eval_S_If_True_X; auto;
  apply_expression_optimization_soundness; auto.
- (* 9. Eval_S_If_False_X *)
  match goal with
  | [H: optimize_statement_x _ _ _ |- _] => inversion H; subst; auto
  end;
  match goal with
  | [H: well_check_flagged_stmt _ _ |- _] => inversion H; subst
  end;
  apply Eval_S_If_False_X; auto;
  apply_expression_optimization_soundness; auto.
- (* 10. Eval_S_While_Loop_RTE_X *)
  match goal with
  | [H: optimize_statement_x _ _ _ |- _] => inversion H; subst; auto
  end;
  match goal with
  | [H: well_check_flagged_stmt _ _ |- _] => inversion H; subst
  end;
  apply Eval_S_While_Loop_RTE_X; auto;
  apply_expression_optimization_soundness; auto.
- (* 11. Eval_S_While_Loop_True_RTE_X *)
  match goal with
  | [H: optimize_statement_x _ _ _ |- _] => inversion H; subst; auto
  end;
  match goal with
  | [H: well_check_flagged_stmt _ _ |- _] => inversion H; subst
  end;
  apply Eval_S_While_Loop_True_RTE_X; auto;
  apply_expression_optimization_soundness; auto.
- (* 12. Eval_S_While_Loop_True_X *)
  match goal with
  | [H: optimize_statement_x _ _ _ |- _] => inversion H; subst; auto
  end;
  match goal with
  | [H: well_check_flagged_stmt _ _ |- _] => inversion H; subst
  end;
  apply Eval_S_While_Loop_True_X with (s1:=s1); auto;
  [ apply_expression_optimization_soundness; auto |
    apply IHeval_stmt_x2; auto; admit
  ].
- (* 13. Eval_S_While_Loop_False_X *)
  match goal with
  | [H: optimize_statement_x _ _ _ |- _] => inversion H; subst; auto
  end;
  match goal with
  | [H: well_check_flagged_stmt _ _ |- _] => inversion H; subst
  end;
  apply Eval_S_While_Loop_False_X; auto;
  apply_expression_optimization_soundness; auto.
- (* 14. Eval_S_Proc_RTE_Args_X *)
  match goal with
  | [H: optimize_statement_x _ _ _ |- _] => inversion H; subst; auto
  end;
  match goal with
  | [H: well_check_flagged_stmt _ _ |- _] => inversion H; subst
  end;
  repeat progress match goal with
  | [H1: fetch_proc_x _ _ = _, H2: fetch_proc_x _ _ = _ |- _] => rewrite H2 in H1; inversion H1; subst
  end;
  apply Eval_S_Proc_RTE_Args_X with (n:=n) (pb:=pb); auto;
  apply_copy_in_args_checks_optimization_soundness; auto.
- (* 15. Eval_S_Proc_RTE_Decl_X *)
  match goal with
  | [H: optimize_statement_x _ _ _ |- _] => inversion H; subst; auto
  end;
  match goal with
  | [H: well_check_flagged_stmt _ _ |- _] => inversion H; subst
  end;
  repeat progress match goal with
  | [H1: fetch_proc_x _ _ = _, H2: fetch_proc_x _ _ = _ |- _] => rewrite H2 in H1; inversion H1; subst
  end;
  apply Eval_S_Proc_RTE_Decl_X with (n:=n) (pb:=pb) (f:=f) (intact_s:=intact_s) (s1:=s1); auto;
  apply_copy_in_args_checks_optimization_soundness; auto.
- (* 16. Eval_S_Proc_RTE_Body_X *)
  match goal with
  | [H: optimize_statement_x _ _ _ |- _] => inversion H; subst; auto
  end;
  match goal with
  | [H: well_check_flagged_stmt _ _ |- _] => inversion H; subst
  end;
  repeat progress match goal with
  | [H1: fetch_proc_x _ _ = _, H2: fetch_proc_x _ _ = _ |- _] => rewrite H2 in H1; inversion H1; subst
  end;
  apply Eval_S_Proc_RTE_Body_X with (n:=n) (pb:=pb) (f:=f) (intact_s:=intact_s) (s1:=s1) (f1:=f1); auto;
  apply_copy_in_args_checks_optimization_soundness; auto.
- (* 17. Eval_S_Proc_X *)
  match goal with
  | [H: optimize_statement_x _ _ _ |- _] => inversion H; subst; auto
  end;
  match goal with
  | [H: well_check_flagged_stmt _ _ |- _] => inversion H; subst
  end;
  repeat progress match goal with
  | [H1: fetch_proc_x _ _ = _, H2: fetch_proc_x _ _ = _ |- _] => rewrite H2 in H1; inversion H1; subst
  end;
  apply Eval_S_Proc_X with (n:=n) (pb:=pb) (f:=f) (intact_s:=intact_s) (s1:=s1) (f1:=f1)
                           (s2:=((n, locals_section ++ params_section) :: s3)) 
                           (locals_section:=locals_section) (params_section:=params_section) (s3:=s3); auto;
  [ apply_copy_in_args_checks_optimization_soundness; auto (* copy_in *) |
    (* apply_copy_out_args_checks_optimization_soundness; auto *) (* copy_out *)
    (****)
    admit
    (****)
  ].
- (* 18. Eval_S_Sequence_RTE_X *)
  match goal with
  | [H: optimize_statement_x _ _ _ |- _] => inversion H; subst; auto
  end;
  match goal with
  | [H: well_check_flagged_stmt _ _ |- _] => inversion H; subst
  end;
  apply Eval_S_Sequence_RTE_X; auto.  
- (* 19. Eval_S_Sequence_X *)
  match goal with
  | [H: optimize_statement_x _ _ _ |- _] => inversion H; subst; auto
  end;
  match goal with
  | [H: well_check_flagged_stmt _ _ |- _] => inversion H; subst
  end;
  apply Eval_S_Sequence_X with (s1:=s1); auto.
  apply IHeval_stmt_x2; auto. 
  admit.
Qed.

Ltac apply_statement_checks_optimization_soundness :=
  match goal with
  | [H1: eval_stmt_x ?st ?s ?c ?s',
     H2: optimize_statement_x ?st ?c ?c',
     H3: well_typed_stack ?st ?s,
     H4: well_check_flagged_stmt ?st ?c |- _] => 
      specialize (statement_checks_optimization_soundness _ _ _ _ _ H1 H2 H3 H4)
  end.

Lemma declaration_checks_optimization_soundness: forall st s f d f' d',
  eval_decl_x st s f d f' ->
    optimize_declaration_x st d d' ->
      well_typed_stack st (f::s) ->
        well_check_flagged_declaration st d ->
          eval_decl_x st s f d' f'.
Proof.
  intros st s f d f' d' H; revert d';
  induction H; intros.
- (* 1. Eval_Decl_Null_X *)
  match goal with
  | [H: optimize_declaration_x _ _ _ |- _] => inversion H; subst; auto
  end;
  constructor.
- (* 2. Eval_Decl_Type_X *)  
  match goal with
  | [H: optimize_declaration_x _ _ _ |- _] => inversion H; subst; auto
  end.
  apply Eval_Decl_Type_X; auto.  
- (* 3. Eval_Decl_Var_None_X *)
  match goal with
  | [H: optimize_declaration_x _ _ _ |- _] => inversion H; subst; auto
  end;
  match goal with
  | [H1: initialization_expression_x _ = _, 
     H2: initialization_expression_x _ = _ |- _] => rewrite H1 in H2; inversion H2; subst
  end.
  apply Eval_Decl_Var_None_X; auto.
- (* 4. Eval_Decl_Var_RTE_X *)
  match goal with
  | [H: optimize_declaration_x _ _ _ |- _] => inversion H; subst; auto
  end;
  match goal with
  | [H1: initialization_expression_x _ = _, 
     H2: initialization_expression_x _ = _ |- _] => rewrite H1 in H2; inversion H2; subst
  end;
  match goal with
  | [H: well_check_flagged_declaration _ _ |- _] => inversion H; subst
  end.
  (* 4.1 O_Object_Declaration_Range_Pass_X *)
  apply Eval_Decl_Var_RTE_X with (e:=(update_exp_check_flags e' checkflags')); simpl; auto.
    rewrite update_exp_with_new_check_flags; apply_removed_check_flag_notin; auto.
    apply_optimize_expression_reserve_notin; intros HZ0;
    apply_remove_notin_check_flag; intros HZ1; 
    apply_remove_check_flag_unique; intros HZ2; subst;
    rewrite update_exp_with_same_check_flags.
    match goal with
    | [H: well_check_flagged_object_declaration _ |- _] => inversion H; subst
    end;
    match goal with
    | [H: initialization_expression_x _ = Some _ |- _] => simpl in H; inversion H; subst
    end;
    match goal with
    | [H1: exp_check_flags ?e = _,
       H2: ~ List.In _ (exp_check_flags ?e) |- _] => rewrite H1 in H2; smack
    | _ => idtac
    end.
    apply_expression_optimization_soundness; auto.
  (* 4.2 O_Object_Declaration_Range_Fail_X *)
  apply Eval_Decl_Var_RTE_X with (e:=e'); auto.
    apply_optimize_expression_reserve_notin; intros HZ0; auto.
    match goal with
    | [H: well_check_flagged_object_declaration _ |- _] => inversion H; subst
    end;
    match goal with
    | [H: initialization_expression_x _ = Some _ |- _] => simpl in H; inversion H; subst
    end;
    match goal with
    | [H1: exp_check_flags ?e = _,
       H2: ~ List.In _ (exp_check_flags ?e) |- _] => rewrite H1 in H2; smack
    | _ => idtac
    end;
    apply_expression_optimization_soundness; auto.
- (* 5. Eval_Decl_Var_X *)
  match goal with
  | [H: optimize_declaration_x _ _ _ |- _] => inversion H; subst; auto
  end;
  match goal with
  | [H1: initialization_expression_x _ = _, 
     H2: initialization_expression_x _ = _ |- _] => rewrite H1 in H2; inversion H2; subst
  end;
  match goal with
  | [H: well_check_flagged_declaration _ _ |- _] => inversion H; subst
  end;
  match goal with
  | [H: well_check_flagged_object_declaration _ |- _] => inversion H; subst
  end;
  match goal with
  | [H: initialization_expression_x _ = Some _ |- _] => simpl in H; inversion H; subst
  end;
  match goal with
  | [H1: exp_check_flags ?e = _,
     H2: ~ List.In _ (exp_check_flags ?e) |- _] => rewrite H1 in H2; smack
  | _ => idtac
  end;
  match goal with
  | [|- eval_decl_x _ _ _ (D_Object_Declaration_X _ ?d) (Normal (STACK.push ?f ?x ?v))] =>
      replace x with (object_name_x d); auto
  end;
  [ apply Eval_Decl_Var_X with (e:=(update_exp_check_flags e' checkflags')); auto |
    apply Eval_Decl_Var_X with (e:=e'); auto
  ];
  [ rewrite update_exp_with_new_check_flags; apply_removed_check_flag_notin; auto |
    apply_optimize_expression_reserve_notin; intros HZ0;
    apply_remove_notin_check_flag; intros HZ1; 
    apply_remove_check_flag_unique; intros HZ2; subst;
    rewrite update_exp_with_same_check_flags |
    apply_optimize_expression_reserve_notin; intros HZ0; auto |
  ];
  apply_expression_optimization_soundness; auto.
- (* 6. Eval_Decl_Var_E_RTE_X *)
  match goal with
  | [H: optimize_declaration_x _ _ _ |- _] => inversion H; subst; auto
  end;
  match goal with
  | [H1: initialization_expression_x _ = _, 
     H2: initialization_expression_x _ = _ |- _] => rewrite H1 in H2; inversion H2; subst
  end;
  match goal with
  | [H: well_check_flagged_declaration _ _ |- _] => inversion H; subst
  end;
  match goal with
  | [H: well_check_flagged_object_declaration _ |- _] => inversion H; subst
  end;
  match goal with
  | [H: initialization_expression_x _ = Some _ |- _] => simpl in H; inversion H; subst
  end;
  match goal with
  | [H1: exp_check_flags ?e = _,
     H2: ~ List.In _ (exp_check_flags ?e) |- _] => rewrite H1 in H2; smack
  | _ => idtac
  end.
  (* 6.1 *)
  apply Eval_Decl_Var_RTE_X with (e:=(update_exp_check_flags e' checkflags')); auto.
    rewrite update_exp_with_new_check_flags; apply_removed_check_flag_notin; auto.
    match goal with
    | [H1: exp_check_flags ?e = _ , H2: exp_check_flags ?e = _ |- _] => rewrite H2 in H1
    end;
    apply_range_check_not_in_expr; rewrite update_exp_with_new_check_flags; intros HZ0;
    apply_list_components_equal;
    apply_optimize_expr_to_same_checkflags; intros HZ1;
    apply_expression_optimization_soundness; auto.  
  (* 6.2 *)
  apply_optimize_expression_reserve_range_check; intros HZ; destruct HZ as [cks1' [cks2' HZ1]].
  apply Eval_Decl_Var_E_RTE_X with (e:=e') (cks1:=cks1') (cks2:=cks2'); auto.
    match goal with
    | [H1: exp_check_flags ?e = _ , H2: exp_check_flags ?e = _ |- _] => rewrite H2 in H1
    end;
    apply_range_check_not_in_expr; rewrite update_exp_with_new_check_flags; intros HZ0;
    apply_list_components_equal;
    apply_optimize_expression_range_check_notin; intros HZ2;
    apply_remove_a_unique_check; intros HZ3;
    apply_optimize_expr_to_same_checkflags; intros HZ4;
    apply_expression_optimization_soundness; auto.  
- (* 7. Eval_Decl_Var_Range_RTE_X *)
  match goal with
  | [H: optimize_declaration_x _ _ _ |- _] => inversion H; subst; auto
  end;
  match goal with
  | [H1: initialization_expression_x _ = _, 
     H2: initialization_expression_x _ = _ |- _] => rewrite H1 in H2; inversion H2; subst
  end;
  match goal with
  | [H: well_check_flagged_declaration _ _ |- _] => inversion H; subst
  end;
  match goal with
  | [H: well_check_flagged_object_declaration _ |- _] => inversion H; subst
  end;
  match goal with
  | [H: initialization_expression_x _ = Some _ |- _] => simpl in H; inversion H; subst
  end;
  match goal with
  | [H1: exp_check_flags ?e = _,
     H2: ~ List.In _ (exp_check_flags ?e) |- _] => rewrite H1 in H2; smack
  | _ => idtac
  end; simpl in *.
  (* 7.1 *)
  apply_extract_subtype_range_unique; intros HZ; destruct HZ; subst.
  clear H2 H4 H6 H11 H15.
  (* use contradiction to prove it *)
  admit.
  (* 7.2 *)
  apply_optimize_expression_reserve_range_check; intros HZ; destruct HZ as [cks1' [cks2' HZ1]].
  apply Eval_Decl_Var_Range_RTE_X with (e:=e') (cks1:=cks1') (cks2:=cks2') (v:=v) (l:=l) (u:=u); auto.
    match goal with
    | [H1: exp_check_flags ?e = _ , H2: exp_check_flags ?e = _ |- _] => rewrite H2 in H1
    end;
    apply_range_check_not_in_expr; rewrite update_exp_with_new_check_flags; intros HZ0;
    apply_list_components_equal;
    apply_optimize_expression_range_check_notin; intros HZ2;
    apply_remove_a_unique_check; intros HZ3;
    apply_optimize_expr_to_same_checkflags; intros HZ4;
    apply_expression_optimization_soundness; auto.
- (* 8. Eval_Decl_Var_Range_X *)
  match goal with
  | [H: optimize_declaration_x _ _ _ |- _] => inversion H; subst; auto
  end;
  match goal with
  | [H1: initialization_expression_x _ = _, 
     H2: initialization_expression_x _ = _ |- _] => rewrite H1 in H2; inversion H2; subst
  end;
  match goal with
  | [H: well_check_flagged_declaration _ _ |- _] => inversion H; subst
  end;
  match goal with
  | [H: well_check_flagged_object_declaration _ |- _] => inversion H; subst
  end;
  match goal with
  | [H: initialization_expression_x _ = Some _ |- _] => simpl in H; inversion H; subst
  end;
  match goal with
  | [H1: exp_check_flags ?e = _,
     H2: ~ List.In _ (exp_check_flags ?e) |- _] => rewrite H1 in H2; smack
  | _ => idtac
  end;
  match goal with
  | [|- eval_decl_x _ _ _ (D_Object_Declaration_X _ ?d) (Normal (STACK.push _ ?x ?v))] => 
      replace x with (d.(object_name_x)); simpl in *; auto
  end;
  apply_optimize_expression_reserve_range_check; intros HZ; destruct HZ as [cks1' [cks2' HZ1]];
  [ apply Eval_Decl_Var_X with (e:=(update_exp_check_flags e' checkflags')); auto |
    apply Eval_Decl_Var_Range_X with (e:=e') (cks1:=cks1') (cks2:=cks2') (l:=l) (u:=u); auto
  ];
  [ rewrite update_exp_with_new_check_flags; apply_removed_check_flag_notin; auto | | ];
    match goal with
    | [H1: exp_check_flags ?e = _ , H2: exp_check_flags ?e = _ |- _] => rewrite H2 in H1
    end;
    apply_range_check_not_in_expr; rewrite update_exp_with_new_check_flags; intros HZ0;
    apply_list_components_equal;
    apply_optimize_expression_range_check_notin; intros HZ2;
    apply_remove_a_unique_check; intros HZ3;
    apply_optimize_expr_to_same_checkflags; intros HZ4;
    [ apply_remove_check_flag_unique; intros HZ5; subst | ];
    apply_expression_optimization_soundness; auto.
- (* 9. Eval_Decl_Proc_X *)
  match goal with
  | [H: optimize_declaration_x _ _ _ |- _] => inversion H; subst; auto
  end.
  apply Eval_Decl_Proc_X; auto.
- (* 10. Eval_Decl_Seq_E_X *)
  match goal with
  | [H: optimize_declaration_x _ _ _ |- _] => inversion H; subst; auto
  end;
  match goal with
  | [H: well_check_flagged_declaration _ _ |- _] => inversion H; subst
  end.
  apply Eval_Decl_Seq_E_X; auto.  
- (* 11. Eval_Decl_Seq_X *)
  match goal with
  | [H: optimize_declaration_x _ _ _ |- _] => inversion H; subst; auto
  end;
  match goal with
  | [H: well_check_flagged_declaration _ _ |- _] => inversion H; subst
  end.
  apply Eval_Decl_Seq_X with (f':=f'); auto.  
Qed.


