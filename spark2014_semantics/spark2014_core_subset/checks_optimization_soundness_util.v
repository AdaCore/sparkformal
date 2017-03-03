Require Export checks_generator.
Require Export checks_optimization_util.
Require Export well_typed_util.


Scheme expression_ind := Induction for expression Sort Prop 
                         with name_ind := Induction for name Sort Prop.

Scheme expression_x_ind := Induction for expression_x Sort Prop 
                         with name_x_ind := Induction for name_x Sort Prop.

(** * Eval Exp_or_Name Value In Bound *)

Lemma eval_expr_value_in_bound: forall e st st' s e' v e'' eBound,
  compile2_flagged_exp st e e' ->
    compile2_flagged_symbol_table st st' ->
      well_typed_stack st' s ->
        well_typed_exp_x st' e' ->
          eval_expr_x st' s e' (Normal (Int v)) ->
            optimize_expression_x st' e' (e'', eBound) ->
              in_bound v eBound true.
Proof.
  apply (expression_ind
    (fun e: expression =>
       forall (st : symboltable) (st' : symboltable_x) (s : STACK.stack) 
              (e' : expression_x) (v : Z) (e'' : expression_x) eBound,
         compile2_flagged_exp st e e' ->
         compile2_flagged_symbol_table st st' ->
         well_typed_stack st' s ->
         well_typed_exp_x st' e' ->
         eval_expr_x st' s e' (Normal (Int v)) ->
         optimize_expression_x st' e' (e'', eBound) ->
         in_bound v eBound true)
    (fun n: name =>
       forall (st : symboltable) (st' : symboltable_x) (s : STACK.stack) 
              (n' : name_x) (v : Z) (n'' : name_x) eBound,
         compile2_flagged_name st n n' ->
         compile2_flagged_symbol_table st st' ->
         well_typed_stack st' s ->
         well_typed_name_x st' n' ->
         eval_name_x st' s n' (Normal (Int v)) ->
         optimize_name_x st' n' (n'', eBound) ->
         in_bound v eBound true)
    ); intros.
- inversion H; subst;
  inversion H3; subst;
  inversion H4; subst.
  + inversion H12; subst.
  + inversion H13; subst.
    inversion H8; subst.
    inversion H7; subst.
    inversion H11; subst.
    apply In_Bound_Refl; auto.
    assumption.
  + inversion H13; subst.
    inversion H8; subst.
    inversion H5; subst.
    apply_in_bound_conflict; crush;eauto.
- inversion H0; subst;
  inversion H3; subst;
  inversion H4; subst;
  inversion H5; subst.
  specialize (H _ _ _ _ _ _ _ H10 H1 H2 H11 H14 H8); assumption.
- inversion H1; subst;
  inversion H4; subst;
  inversion H5; subst;
  inversion H6; subst.
  
  + apply_binop_arithm_operand_format; subst.
    specialize (H _ _ _ _ _ _ _ H14 H2 H3 H17 H25 H11).
    specialize (H0 _ _ _ _ _ _ _ H15 H2 H3 H18 H26 H29).
    apply_binop_arithm_in_bound; auto.
  + inversion H26; subst.
    apply_binop_arithm_typed; intros HZ1;
    specialize (HZ1 st'); inversion HZ1; subst.
    inversion H29; crush;eauto.
  + inversion H30; subst.
    clear - H11 H12 H14 H16 H8.
    destruct b; crush;eauto;
    destruct v1, v2; inversion H8.
- inversion H0; subst;
  inversion H3; subst;
  inversion H4; subst;
  inversion H5; subst.
  + apply_unop_arithm_operand_format; subst.
    specialize (H _ _ _ _ _ _ _ H12 H1 H2 H11 H19 H9).
    apply_unop_arithm_in_bound; auto.
  + inversion H21; subst.
    destruct u; destruct v0; inversion H7; crush;eauto.
    specialize (H _ _ _ _ _ _ _ H12 H1 H2 H13 H20 H9).
    inversion H23; subst; auto.
- inversion H; subst;
  inversion H1; subst;
  inversion H2; subst;
  inversion H3; subst;
  inversion H4; subst.
  specialize (H5 _ _ H10).
  destruct H5 as [md' [t' [HZ1 HZ2]]].
  rewrite HZ1 in H11; inversion H11; subst.
  rewrite H12 in H9; inversion H9; subst.
  inversion HZ2; subst;
  inversion H16; crush;eauto;
  [inversion H5; subst; inversion H13 | | | ];
  apply_extract_subtype_range_unique; crush;eauto.
- apply_eval_name_well_typed_value.
  inversion H1; subst;
  inversion H4; subst;
  inversion H6; subst.
  crush;eauto.
  rewrite H23 in H17; inversion H17; subst.
  rewrite H16 in HZ0; inversion HZ0; subst.
  inversion H26; subst.
  rewrite H7 in H18; inversion H18; subst.

  inversion HZ1; subst;  
  inversion H8; crush;eauto;
  [inversion H9; subst; inversion H20 | | | ];
  apply_extract_subtype_range_unique; crush;eauto.
- apply_eval_name_well_typed_value.
  inversion H0; subst;
  inversion H3; subst;
  inversion H5; crush;eauto.
  rewrite H20 in H14; inversion H14; subst.
  rewrite H13 in HZ0; inversion HZ0; subst.
  inversion H21; subst.
  rewrite H6 in H15; inversion H15; subst.
  rewrite H7 in H16; inversion H16; subst.
  
  inversion HZ1; subst;
  inversion H8; crush;eauto;
  [ inversion H9; subst; inversion H22 | | | ];
  apply_extract_subtype_range_unique; crush;eauto.  
Qed.

Ltac apply_eval_expr_value_in_bound :=
  match goal with
  | [H1: compile2_flagged_exp ?st ?e ?e',
     H2: compile2_flagged_symbol_table ?st ?st',
     H3: well_typed_stack ?st' ?s,
     H4: well_typed_exp_x ?st' ?e',
     H5: eval_expr_x ?st' ?s ?e' (Normal (Int ?v)),
     H6: optimize_expression_x ?st' ?e' _ |- _] =>
      specialize (eval_expr_value_in_bound _ _ _ _ _ _ _ _ H1 H2 H3 H4 H5 H6);
      let HZ := fresh "HZ" in intros HZ
  end.

Lemma eval_name_value_in_bound: forall n st st' s n' v n'' nBound,
  compile2_flagged_name st n n' ->
    compile2_flagged_symbol_table st st' ->
      well_typed_stack st' s ->
        well_typed_name_x st' n' ->
          eval_name_x st' s n' (Normal (Int v)) ->
            optimize_name_x st' n' (n'', nBound) ->
              in_bound v nBound true.
Proof.
  induction n; intros.
- inversion H; subst;
  inversion H2; subst;
  inversion H3; subst;
  inversion H4; subst.
  
  apply_eval_name_well_typed_value. simpl in HZ0.
  repeat progress match goal with
  | [H1: fetch_exp_type_x ?x ?st = _,
     H2: fetch_exp_type_x ?x ?st = _ |- _] => rewrite H1 in H2; inversion H2; subst
  | _ => idtac
  end.
  apply_typed_value_in_bound; auto.
- apply_eval_name_well_typed_value.
  inversion H; subst;
  inversion H2; subst;
  inversion H3; subst;
  inversion H4; subst.
  
  simpl in HZ0.
  clear H H2 H3 H4 IHn.
  repeat progress match goal with
  | [H1: fetch_exp_type_x ?x ?st = _,
     H2: fetch_exp_type_x ?x ?st = _ |- _] => rewrite H1 in H2; inversion H2; subst
  | _ => idtac
  end.
  clear - H30 H16 HZ1. (* H30: bound_of_array_component_type st' t2 nBound*)
  inversion H30; subst.
  match goal with
  | [H1: fetch_type_x ?x ?st = _,
     H2: fetch_type_x ?x ?st = _ |- _] => rewrite H1 in H2; inversion H2; subst
  end.
  apply_typed_value_in_bound; auto.
- apply_eval_name_well_typed_value.
  inversion H; subst;
  inversion H2; subst;
  inversion H3; subst;
  inversion H4; crush;eauto.

  repeat progress match goal with
  | [H1: fetch_exp_type_x ?x ?st = _,
     H2: fetch_exp_type_x ?x ?st = _ |- _] => rewrite H1 in H2; inversion H2; subst
  | _ => idtac
  end.
  clear - H22 H14 H15 HZ1.
  inversion H22; subst.
  repeat progress match goal with
  | [H1: fetch_type_x ?x ?st = _,
     H2: fetch_type_x ?x ?st = _ |- _] => rewrite H1 in H2; inversion H2; subst
  | [H1: record_field_type _ _ = _,
     H2: record_field_type _ _ = _ |- _] => rewrite H1 in H2; inversion H2; subst
  end.
  apply_typed_value_in_bound; auto.
Qed.

Ltac apply_eval_name_value_in_bound :=
  match goal with
  | [H1: compile2_flagged_name ?st ?n ?n',
     H2: compile2_flagged_symbol_table ?st ?st',
     H3: well_typed_stack ?st' ?s,
     H4: well_typed_name_x ?st' ?n',
     H5: eval_name_x ?st' ?s ?n' (Normal (Int ?v)),
     H6: optimize_name_x ?st' ?n' (?n'', ?nBound) |- _] =>
      specialize (eval_name_value_in_bound _ _ _ _ _ _ _ _ H1 H2 H3 H4 H5 H6);
      let HZ := fresh "HZ" in intros HZ
  end.

(** * expression_checks_optimization_soundness *)
Lemma expression_checks_optimization_soundness: forall e st st' s e' e'' eBound v, 
  compile2_flagged_exp st e e' ->
    compile2_flagged_symbol_table st st' ->
      well_typed_stack st' s ->
        well_typed_exp_x st' e' ->
          optimize_expression_x st' e' (e'', eBound) ->
            eval_expr_x st' s e' v ->
              eval_expr_x st' s e'' v.
Proof.
  apply (expression_ind
    (fun e: expression =>
       forall (st : symboltable) (st' : symboltable_x) (s : STACK.stack)
              (e': expression_x) (e'': expression_x) (eBound: bound) (v : Return value),
      compile2_flagged_exp st e e' ->
      compile2_flagged_symbol_table st st' ->
      well_typed_stack st' s ->
      well_typed_exp_x st' e' ->
      optimize_expression_x st' e' (e'', eBound) ->
      eval_expr_x st' s e' v ->
      eval_expr_x st' s e'' v)
    (fun n: name =>
       forall (st : symboltable) (st' : symboltable_x) (s : STACK.stack)
              (n': name_x) (n'': name_x) (nBound: bound) (v : Return value),
      compile2_flagged_name st n n' ->
      compile2_flagged_symbol_table st st' ->
      well_typed_stack st' s ->
      well_typed_name_x st' n' ->
      optimize_name_x st' n' (n'', nBound) ->
      eval_name_x st' s n' v ->
      eval_name_x st' s n'' v)
    ); intros.
- (** E_Literal_X *)
  inversion H; subst;
  inversion H3; subst;
  inversion H4; subst;
  constructor;
  apply_literal_checks_optimization_soundness.
- (** E_Name_X *)
  inversion H0; subst;
  inversion H3; subst;
  inversion H4; subst;
  inversion H5; subst.
  specialize (H _ _ _ _ _ _ _ H10 H1 H2 H11 H8 H15). 
  constructor; auto.
- (** E_Binary_Operation_X *)
  inversion H1; subst;
  inversion H4; subst;
  inversion H5; subst;
  inversion H6; subst;

  repeat progress match goal with
  | [H: forall (st : symboltable) (st' : symboltable_x) 
        (s : STACK.stack) (e' e'' : expression_x) (eBound : bound)
        (v : Return value),
      compile2_flagged_exp st ?e e' ->
      compile2_flagged_symbol_table st st' ->
      well_typed_stack st' s ->
      well_typed_exp_x st' e' ->
      optimize_expression_x st' e' (e'', eBound) ->
      eval_expr_x st' s e' v -> eval_expr_x st' s e'' v,
     H1: compile2_flagged_exp ?st ?e ?e',
     H2: compile2_flagged_symbol_table ?st ?st',
     H3: well_typed_stack ?st' ?s,
     H4: well_typed_exp_x ?st' ?e',
     H5: optimize_expression_x ?st' ?e' _,
     H6: eval_expr_x ?st' ?s ?e' ?v |- _] => specialize (H _ _ _ _ _ _ _ H1 H2 H3 H4 H5 H6)
  end;
  [apply Eval_E_Binary_Operation_e1RTE_X; auto | | | apply Eval_E_Binary_Operation_e1RTE_X; auto | | |
   apply Eval_E_Binary_Operation_e1RTE_X; auto | | ];
  [apply Eval_E_Binary_Operation_e2RTE_X with (v1:=v1); auto | | 
   apply Eval_E_Binary_Operation_e2RTE_X with (v1:=v1); auto | |
   apply Eval_E_Binary_Operation_e2RTE_X with (v1:=v1); auto | ];
  apply Eval_E_Binary_Operation_X with (v1:=v1) (v2:=v2); auto.
  + (* Plus | Minus | Multiply *)
    match goal with
    | [H: do_flagged_checks_on_binop _ _ _ _ _ |- _] => inversion H; crush;eauto
    end;
    match goal with
    | [H: do_flagged_check_on_binop _ _ _ _ _ |- _] => inversion H; crush;eauto
    | _ => idtac
    end;
    destruct v1, v2; inversion H8;
    specialize (eval_expr_value_in_bound _ _ _ _ _ _ _ _ H14 H2 H3 H17 H28 H11);
    apply_eval_expr_value_in_bound; intros;
    apply_do_flagged_checks_on_binop_reserve; auto. 
  + (* Divide *)
    match goal with
    | [H: do_flagged_checks_on_binop _ _ _ _ _ |- _] => inversion H; crush;eauto
    end;
    match goal with
    | [H: do_flagged_check_on_binop _ _ _ _ _ |- _] => inversion H; crush;eauto
    | _ => idtac
    end;
    specialize (eval_expr_value_in_bound _ _ _ _ _ _ _ _ H14 H2 H3 H16 H27 H11);
    apply_eval_expr_value_in_bound; intros;
    apply_do_flagged_checks_on_binop_reserve; auto. 
  + (* Logic Operator *)
  inversion H30; crush;eauto.
- (** E_Unary_Operation_X *)
  inversion H0; subst;
  inversion H3; subst;
  inversion H4; subst;
  inversion H5; subst;
  match goal with
  | [H: forall (st : symboltable) (st' : symboltable_x) 
        (s : STACK.stack) (e' e'' : expression_x) (eBound : bound)
        (v : Return value),
      compile2_flagged_exp st ?e e' ->
      compile2_flagged_symbol_table st st' ->
      well_typed_stack st' s ->
      well_typed_exp_x st' e' ->
      optimize_expression_x st' e' (e'', eBound) ->
      eval_expr_x st' s e' v -> eval_expr_x st' s e'' v,
     H1: compile2_flagged_exp ?st ?e ?e',
     H2: compile2_flagged_symbol_table ?st ?st',
     H3: well_typed_stack ?st' ?s,
     H4: well_typed_exp_x ?st' ?e',
     H5: optimize_expression_x ?st' ?e' _,
     H6: eval_expr_x ?st' ?s ?e' ?v |- _] => specialize (H _ _ _ _ _ _ _ H1 H2 H3 H4 H5 H6)
  end;
  [ apply Eval_E_Unary_Operation_eRTE_X; auto | |
    apply Eval_E_Unary_Operation_eRTE_X; auto | ];
  apply Eval_E_Unary_Operation_X with (v:=v0); auto.
  + match goal with
    | [H: do_flagged_checks_on_unop _ _ _ _ |- _] => inversion H; crush;eauto
    end;
    match goal with
    | [H: do_flagged_check_on_unop _ _ _ _ |- _] => inversion H; crush;eauto
    | _ => idtac
    end;
    destruct v0; inversion H6;
    apply_eval_expr_value_in_bound; intros;
    apply_do_flagged_checks_on_unop_reserve; auto.
  + inversion H21; crush;eauto.  
- (** E_Identifier_X *)
  inversion H; subst;
  inversion H3; subst;
  inversion H4; subst. assumption.
- (** E_Indexed_Component_X *)
  inversion H1; subst;
  inversion H4; subst;
  inversion H5; subst;
  inversion H6; subst;
  match goal with
  | [H: forall (st : symboltable) (st' : symboltable_x) 
        (s : STACK.stack) (n' n'' : name_x) (nBound : bound)
        (v : Return value),
      compile2_flagged_name st ?n n' ->
      compile2_flagged_symbol_table st st' ->
      well_typed_stack st' s ->
      well_typed_name_x st' n' ->
      optimize_name_x st' n' (n'', nBound) ->
      eval_name_x st' s n' v -> eval_name_x st' s n'' v,
    H1: compile2_flagged_name ?st ?n ?n',
    H2: compile2_flagged_symbol_table ?st ?st',
    H3: well_typed_stack ?st' ?s,
    H4: well_typed_name_x ?st' ?n',
    H5: optimize_name_x ?st' ?n' _,
    H6: eval_name_x ?st' ?s ?n' ?v |- _] => 
      specialize (H _ _ _ _ _ _ _ H1 H2 H3 H4 H5 H6)
  end;
  match goal with
  | [H: forall (st : symboltable) (st' : symboltable_x) 
        (s : STACK.stack) (e' e'' : expression_x) (eBound : bound)
        (v : Return value),
      compile2_flagged_exp st ?e e' ->
      compile2_flagged_symbol_table st st' ->
      well_typed_stack st' s ->
      well_typed_exp_x st' e' ->
      optimize_expression_x st' e' (e'', eBound) ->
      eval_expr_x st' s e' v -> eval_expr_x st' s e'' v,
     H1: compile2_flagged_exp ?st ?e ?e',
     H2: compile2_flagged_symbol_table ?st ?st',
     H3: well_typed_stack ?st' ?s,
     H4: well_typed_exp_x ?st' ?e',
     H5: optimize_expression_x ?st' ?e' _,
     H6: eval_expr_x ?st' ?s ?e' ?v |- _] => specialize (H _ _ _ _ _ _ _ H1 H2 H3 H4 H5 H6)
  | _ => idtac
  end.
  + apply Eval_E_Indexed_Component_xRTE_X; auto.
  + apply Eval_E_Indexed_Component_eRTE_X with (a:=a0); auto.
    apply eval_expr_value_reserve with (e := e') (eBound := Interval u v0) (rBound := Interval u' v'); auto.
    apply_well_typed_exp_preserve.
    specialize (optimize_exp_ex_cks_stripped _ _ _ _ _ H22); intro HZ1.
    specialize (eval_exp_ex_cks_stripped _ _ _ _ _ H28); intros HZ2.
    specialize (H0 _ _ _ _ _ _ _ H12 H2 H3 HZ HZ1 HZ2).
    specialize (eval_exp_ex_cks_stripped _ _ _ _ _ H0); auto.
  + apply_well_typed_exp_preserve.
    specialize (optimize_exp_ex_cks_stripped _ _ _ _ _ H22); intro HZ1.
    specialize (eval_exp_ex_cks_stripped _ _ _ _ _ H27); intros HZ2.
    specialize (H0 _ _ _ _ _ _ _ H12 H2 H3 HZ HZ1 HZ2).
    apply Eval_E_Indexed_Component_Range_RTE_X with (a:=a0) (i:=i) (t:=t0) (l:=l) (u:=u0); auto.
    apply eval_expr_value_reserve with (e := e') (eBound := Interval u v0) (rBound := Interval u' v'); auto.
    specialize (eval_exp_ex_cks_stripped _ _ _ _ _ H0); auto.
    specialize (optimize_name_ast_num_eq _ _ _ _ H21); crush;eauto.
    rewrite H29 in H23; inversion H23; subst; assumption.
    rewrite H29 in H23; inversion H23; subst.
    apply_extract_array_index_range_x_unique; subst.
    apply_eval_expr_value_in_bound.
    clear - H12 H22 H25 H29 H30 H31 HZ3.
    
    apply_optimize_exp_ex_cks_eq.
    rewrite exp_updated_exterior_checks in *.
    inversion H31; subst. inversion H; subst.
    apply_optimize_range_check_reserve; crush;eauto.
  + apply_well_typed_exp_preserve.
    specialize (optimize_exp_ex_cks_stripped _ _ _ _ _ H22); intro HZ1.
    specialize (eval_exp_ex_cks_stripped _ _ _ _ _ H19); intros HZ2.
    specialize (H0 _ _ _ _ _ _ _ H12 H2 H3 HZ HZ1 HZ2).
    apply Eval_E_Indexed_Component_X with (a:=a0) (i:=i) (t:=t0) (l:=l) (u:=u0); auto.
    apply eval_expr_value_reserve with (e := e') (eBound := Interval u v0) (rBound := Interval u' v'); auto.
    specialize (eval_exp_ex_cks_stripped _ _ _ _ _ H0); auto.
    specialize (optimize_name_ast_num_eq _ _ _ _ H21); crush;eauto.
    rewrite H28 in H23; inversion H23; subst; assumption.
    rewrite H28 in H23; inversion H23; subst.
    apply_extract_array_index_range_x_unique; subst.
    clear - H12 H22 H25 H28 H30 H31.
    
    apply_optimize_exp_ex_cks_eq.
    rewrite exp_updated_exterior_checks in *.
    rewrite <- HZ in H31;
    apply_do_range_check_same_result; auto.
- (** E_Selected_Component_X *)
  inversion H0; subst;
  inversion H3; subst;
  inversion H4; subst;
  inversion H5; subst;
  match goal with
  | [H: forall (st : symboltable) (st' : symboltable_x) 
        (s : STACK.stack) (n' n'' : name_x) (nBound : bound)
        (v : Return value),
      compile2_flagged_name st ?n n' ->
      compile2_flagged_symbol_table st st' ->
      well_typed_stack st' s ->
      well_typed_name_x st' n' ->
      optimize_name_x st' n' (n'', nBound) ->
      eval_name_x st' s n' v -> eval_name_x st' s n'' v,
    H1: compile2_flagged_name ?st ?n ?n',
    H2: compile2_flagged_symbol_table ?st ?st',
    H3: well_typed_stack ?st' ?s,
    H4: well_typed_name_x ?st' ?n',
    H5: optimize_name_x ?st' ?n' _,
    H6: eval_name_x ?st' ?s ?n' ?v |- _] => 
      specialize (H _ _ _ _ _ _ _ H1 H2 H3 H4 H5 H6)
  end.
  + apply Eval_E_Selected_Component_xRTE_X; auto.
  + apply Eval_E_Selected_Component_X with (r:=r); auto.    
Qed.

Ltac apply_expression_checks_optimization_soundness :=
  match goal with
  | [H1: compile2_flagged_exp ?st ?e ?e',
     H2: compile2_flagged_symbol_table ?st ?st',
     H3: well_typed_stack ?st' ?s,
     H4: well_typed_exp_x ?st' ?e',
     H5: optimize_expression_x ?st' ?e' _,
     H6: eval_expr_x ?st' ?s ?e' ?v |- _] => 
      specialize (expression_checks_optimization_soundness _ _ _ _ _ _ _ _ H1 H2 H3 H4 H5 H6);
      let HZ := fresh "HZ" in
      intro HZ
  end.


(** * name_checks_optimization_soundness *)

Lemma name_checks_optimization_soundness: forall n st st' s n' n'' nBound v, 
  compile2_flagged_name st n n' ->
    compile2_flagged_symbol_table st st' ->
      well_typed_stack st' s ->
        well_typed_name_x st' n' ->
          optimize_name_x st' n' (n'', nBound) ->
            eval_name_x st' s n' v ->
              eval_name_x st' s n'' v.
Proof.
  induction n; intros.
- (** E_Identifier_X *)
  inversion H; subst;
  inversion H3; subst;
  inversion H4; subst. assumption.
- (** E_Indexed_Component_X *)
  inversion H; subst;
  inversion H2; subst;
  inversion H3; subst;
  inversion H4; subst;
  match goal with
  | [H: forall (st : symboltable) (st' : symboltable_x) 
        (s : STACK.stack) (n' n'' : name_x) (nBound : bound)
        (v : Return value),
      compile2_flagged_name st ?n n' ->
      compile2_flagged_symbol_table st st' ->
      well_typed_stack st' s ->
      well_typed_name_x st' n' ->
      optimize_name_x st' n' (n'', nBound) ->
      eval_name_x st' s n' v -> eval_name_x st' s n'' v,
    H1: compile2_flagged_name ?st ?n ?n',
    H2: compile2_flagged_symbol_table ?st ?st',
    H3: well_typed_stack ?st' ?s,
    H4: well_typed_name_x ?st' ?n',
    H5: optimize_name_x ?st' ?n' _,
    H6: eval_name_x ?st' ?s ?n' ?v |- _] => 
      specialize (H _ _ _ _ _ _ _ H1 H2 H3 H4 H5 H6)
  end.
  + apply Eval_E_Indexed_Component_xRTE_X; auto.
  + apply Eval_E_Indexed_Component_eRTE_X with (a:=a0); auto.
    apply eval_expr_value_reserve with (e := e') (eBound := Interval u v0) (rBound := Interval u' v'); auto.
    apply_well_typed_exp_preserve.
    specialize (optimize_exp_ex_cks_stripped _ _ _ _ _ H20); intro HZ1.
    specialize (eval_exp_ex_cks_stripped _ _ _ _ _ H26); intros HZ2.
    apply_expression_checks_optimization_soundness.
    specialize (eval_exp_ex_cks_stripped _ _ _ _ _ HZ0); auto.
  + apply_well_typed_exp_preserve.
    specialize (optimize_exp_ex_cks_stripped _ _ _ _ _ H20); intro HZ1.
    specialize (eval_exp_ex_cks_stripped _ _ _ _ _ H25); intros HZ2.
    apply Eval_E_Indexed_Component_Range_RTE_X with (a:=a0) (i:=i) (t:=t0) (l:=l) (u:=u0); auto.
    apply eval_expr_value_reserve with (e := e') (eBound := Interval u v0) (rBound := Interval u' v'); auto.
    apply_expression_checks_optimization_soundness.
    specialize (eval_exp_ex_cks_stripped _ _ _ _ _ HZ0); auto.
    
    specialize (optimize_name_ast_num_eq _ _ _ _ H19); crush;eauto.
    rewrite H27 in H21; inversion H21; subst; assumption.
    rewrite H27 in H21; inversion H21; subst.
    apply_extract_array_index_range_x_unique; subst.
    apply_eval_expr_value_in_bound.
    clear - H10 H20 H23 H27 H28 H29 HZ3.
    
    apply_optimize_exp_ex_cks_eq.
    rewrite exp_updated_exterior_checks in *.
    inversion H29; subst. inversion H; subst.
    apply_optimize_range_check_reserve; crush;eauto.
  + apply_well_typed_exp_preserve.
    specialize (optimize_exp_ex_cks_stripped _ _ _ _ _ H20); intro HZ1.
    specialize (eval_exp_ex_cks_stripped _ _ _ _ _ H17); intros HZ2.
    apply Eval_E_Indexed_Component_X with (a:=a0) (i:=i) (t:=t0) (l:=l) (u:=u0); auto.
    apply eval_expr_value_reserve with (e := e') (eBound := Interval u v0) (rBound := Interval u' v'); auto.
    apply_expression_checks_optimization_soundness.
    specialize (eval_exp_ex_cks_stripped _ _ _ _ _ HZ0); auto.

    specialize (optimize_name_ast_num_eq _ _ _ _ H19); crush;eauto.
    rewrite H26 in H21; inversion H21; subst; assumption.
    rewrite H26 in H21; inversion H21; subst.
    apply_extract_array_index_range_x_unique; subst.
    clear - H10 H20 H23 H26 H28 H29.
    
    apply_optimize_exp_ex_cks_eq.
    rewrite exp_updated_exterior_checks in *.
    rewrite <- HZ in H29;
    apply_do_range_check_same_result; auto.
- (** E_Selected_Component_X *)
  inversion H; subst;
  inversion H2; subst;
  inversion H3; subst;
  inversion H4; subst;
  match goal with
  | [H: forall (st : symboltable) (st' : symboltable_x) 
        (s : STACK.stack) (n' n'' : name_x) (nBound : bound)
        (v : Return value),
      compile2_flagged_name st ?n n' ->
      compile2_flagged_symbol_table st st' ->
      well_typed_stack st' s ->
      well_typed_name_x st' n' ->
      optimize_name_x st' n' (n'', nBound) ->
      eval_name_x st' s n' v -> eval_name_x st' s n'' v,
    H1: compile2_flagged_name ?st ?n ?n',
    H2: compile2_flagged_symbol_table ?st ?st',
    H3: well_typed_stack ?st' ?s,
    H4: well_typed_name_x ?st' ?n',
    H5: optimize_name_x ?st' ?n' _,
    H6: eval_name_x ?st' ?s ?n' ?v |- _] => 
      specialize (H _ _ _ _ _ _ _ H1 H2 H3 H4 H5 H6)
  end.
  + apply Eval_E_Selected_Component_xRTE_X; auto.
  + apply Eval_E_Selected_Component_X with (r:=r); auto.    
Qed.

Ltac apply_name_checks_optimization_soundness := 
  match goal with
  | [H1: compile2_flagged_name ?st ?n ?n',
     H2: compile2_flagged_symbol_table ?st ?st',
     H3: well_typed_stack ?st' ?s,
     H4: well_typed_name_x ?st' ?n',
     H5: optimize_name_x ?st' ?n' _,
     H6: eval_name_x ?st' ?s ?n' ?v |- _] =>
      specialize (name_checks_optimization_soundness _ _ _ _ _ _ _ _ H1 H2 H3 H4 H5 H6);
      let HZ := fresh "HZ" in
      intro HZ
  end.
 

(** * store_update_optimization_soundness *)

Lemma store_update_optimization_soundness: forall n st st' s s' n' n'' nBound v, 
  compile2_flagged_name st n n' ->
    compile2_flagged_symbol_table st st' ->
      well_typed_stack st' s ->
        well_typed_name_x st' n' ->
          optimize_name_x st' n' (n'', nBound) ->
            storeUpdate_x st' s n' v s' ->
              storeUpdate_x st' s n'' v s'.
Proof.
  induction n; intros.
- inversion H; subst;
  inversion H3; crush;eauto.
- inversion H; subst;
  inversion H2; subst;
  inversion H3; subst;
  inversion H4; subst.
  + apply SU_Indexed_Component_xRTE_X; auto.
    apply_name_checks_optimization_soundness; auto.
  + apply SU_Indexed_Component_eRTE_X with (a:=a0); auto.
    destruct H26; apply_name_checks_optimization_soundness; auto.
    apply eval_expr_value_reserve with (e := e') (eBound := Interval u v0) (rBound := Interval u' v'); auto.
    apply_well_typed_exp_preserve.
    specialize (optimize_exp_ex_cks_stripped _ _ _ _ _ H20); intro HZ1.
    specialize (eval_exp_ex_cks_stripped _ _ _ _ _ H27); intros HZ2.
    apply_expression_checks_optimization_soundness.
    specialize (eval_exp_ex_cks_stripped _ _ _ _ _ HZ0); auto.
  + apply_well_typed_exp_preserve.
    specialize (optimize_exp_ex_cks_stripped _ _ _ _ _ H20); intro HZ1.
    specialize (eval_exp_ex_cks_stripped _ _ _ _ _ H25); intros HZ2.
    apply SU_Indexed_Component_Range_RTE_X with (a:=a0) (i:=i) (t:=t1) (l:=l) (u:=u0); auto.
    destruct H12; apply_name_checks_optimization_soundness; auto.
    apply eval_expr_value_reserve with (e := e') (eBound := Interval u v0) (rBound := Interval u' v'); auto.
    apply_expression_checks_optimization_soundness.
    specialize (eval_exp_ex_cks_stripped _ _ _ _ _ HZ0); auto.
    
    specialize (optimize_name_ast_num_eq _ _ _ _ H19); crush;eauto.
    rewrite H28 in H21; inversion H21; subst.
    apply_extract_array_index_range_x_unique; subst.
    apply_eval_expr_value_in_bound.
    clear - H10 H20 H23 H28 H29 H30 HZ3.
    
    apply_optimize_exp_ex_cks_eq.
    rewrite exp_updated_exterior_checks in *.
    inversion H30; subst. inversion H; subst.
    apply_optimize_range_check_reserve; crush;eauto.    
  + apply_well_typed_exp_preserve.
    specialize (optimize_exp_ex_cks_stripped _ _ _ _ _ H20); intro HZ1.
    specialize (eval_exp_ex_cks_stripped _ _ _ _ _ H18); intros HZ2.
    apply_name_checks_optimization_soundness; auto.
    apply_expression_checks_optimization_soundness.
    specialize (eval_exp_ex_cks_stripped _ _ _ _ _ HZ3); intro HZ4.
    specialize (optimize_name_ast_num_eq _ _ _ _ H19); intro HZ5.
    rewrite H25 in H21; inversion H21; subst.
    apply_extract_array_index_range_x_unique; subst.
    specialize (optimize_exp_ex_cks_eq _ _ _ _ H20); intros HZ7.
    rewrite exp_updated_exterior_checks in *.
    rewrite <- HZ7 in *.

    destruct H17; subst.
 
    apply SU_Indexed_Component_X with 
      (arrObj:=(ArrayV a0)) (a:=a0) (i:=i) (l:=l) (u:=u0) (t:=t0) (a1:=(updateIndexedComp a0 i v)); crush;eauto.
    apply eval_expr_value_reserve with (e := e') (eBound := Interval u v0) (rBound := Interval l u0); auto.
    apply_do_range_check_same_result; auto.

    apply SU_Indexed_Component_X with 
      (arrObj:=Undefined) (i:=i) (a:=nil) (l:=l) (u:=u0) (t:=t0) (a1:=((i, v) :: nil)); crush;eauto.
    apply eval_expr_value_reserve with (e := e') (eBound := Interval u v0) (rBound := Interval l u0); auto.
    apply_do_range_check_same_result; auto.
- inversion H; subst;
  inversion H2; subst;
  inversion H3; subst;
  inversion H4; subst.
  + apply_name_checks_optimization_soundness;
    apply SU_Selected_Component_xRTE_X; crush;eauto.
  + destruct H23;
    [ apply SU_Selected_Component_X with 
        (recObj:=(RecordV r)) (r:=r) (r1:=(updateSelectedComp r i v)); crush;eauto |
      apply SU_Selected_Component_X with 
        (recObj:=Undefined) (r:=nil) (r1:=((i, v) :: nil)); crush;eauto
    ];
    apply_name_checks_optimization_soundness; auto.
Qed.
 
Ltac apply_store_update_optimization_soundness := 
  match goal with
  | [H1: compile2_flagged_name ?st ?n ?n' ,
     H2: compile2_flagged_symbol_table ?st ?st' ,
     H3: well_typed_stack ?st' ?s ,
     H4: well_typed_name_x ?st' ?n' ,
     H5: optimize_name_x ?st' ?n' _ ,
     H6: storeUpdate_x ?st' ?s ?n' ?v ?s' |- _] =>
      specialize (store_update_optimization_soundness _ _ _ _ _ _ _ _ _ H1 H2 H3 H4 H5 H6);
      let HZ := fresh "HZ" in
      intro HZ
  end.


(* back_to_here *)
(*
Lemma store_update_optimization_soundness: forall n st st' s s' n' n'' nBound v, 
  compile2_flagged_name st n n' ->
    compile2_flagged_symbol_table st st' ->
      well_typed_stack st' s ->
        well_typed_name_x st' n' ->
          optimize_name_x st' n' (n'', nBound) ->
            storeUpdate_x st' s n' v s' ->
              storeUpdate_x st' s n'' v s'.

  H0 : copy_in_x st0 s (STACK.newFrame n) (procedure_parameter_profile_x pb)
         args (Run_Time_Error msg)
  H1 : compile2_flagged_symbol_table st st0
  H2 : well_typed_stack st0 s

  H10 : well_typed_exps_x st0 args

  H14 : fetch_proc p st = Some (n1, pb0)

  H17 : compile2_flagged_args st (procedure_parameter_profile pb0) args0 args

  H13 : well_typed_args_x st0 args (procedure_parameter_profile_x pb)
  H18 : optimize_args_x st0 (procedure_parameter_profile_x pb) args args'
  H16 : fetch_proc_x p st0 = Some (n, pb)
  ============================
   copy_in_x st0 s (STACK.newFrame n) (procedure_parameter_profile_x pb)
     args' (Run_Time_Error msg)


Lemma copy_in_args_checks_optimization_soundness:
  compile2_flagged_args st params args args'
  compile2_flagged_symbol_table st st' ->
  compile2_flagged_parameter_specifications params params' ->
  well_typed_stack st' s ->
  well_typed_exps_x st' args' ->
  well_typed_args_x st' args' params' ->
  optimize_args_x st' params' args' args'' ->
  copy_in_x st' s f params' args' f' ->
  copy_in_x st s f params' args'' f'.
*)

Lemma optimize_range_check_preserve: forall st s ast_num n n' n'' v l l' l'' u u' u'',
  optimize_range_check (E_Name_X ast_num n) (Interval l u) (Interval l' u') n' ->
    optimize_range_check_on_copy_out n' (Interval l' u') (Interval l'' u'') n'' ->
      eval_name_x st s n v ->
        eval_expr_x st s n'' v /\ exists n1, n'' = E_Name_X ast_num n1.
Proof.
  intros; constructor.
- apply eval_expr_value_copy_out_opt_reserve with (e:=n') (eBound:=(Interval l' u')) (rBound:=(Interval l'' u'')); auto.
  apply eval_expr_value_reserve with (e:=(E_Name_X ast_num n)) (eBound:=(Interval l u)) (rBound:=(Interval l' u')); auto.
  constructor; auto.
- inversion H; subst; inversion H0; subst; simpl; crush;eauto.
Qed.

Ltac apply_optimize_range_check_preserve :=
  match goal with
  [H1: optimize_range_check (E_Name_X ?ast_num ?n) (Interval ?l ?u) (Interval ?l' ?u') ?n',
   H2: optimize_range_check_on_copy_out ?n' (Interval ?l' ?u') (Interval ?l'' ?u'') ?n'',
   H3: eval_name_x ?st ?s ?n ?v |- _] =>
    specialize (optimize_range_check_preserve _ _ _ _ _ _ _ _ _ _ _ _ _ H1 H2 H3);
    let HA := fresh "HA" in 
    let HA1 := fresh "HA" in 
    let HA := fresh "HA" in intros HA; destruct HA as [HA1 HA2]; inversion HA2; subst
  end.

(** * copy_in_args_checks_optimization_soundness *)
Lemma copy_in_args_checks_optimization_soundness: forall params' st st' s f f' params args args' args'',
  compile2_flagged_args st params args args' ->
  compile2_flagged_symbol_table st st' ->
  compile2_flagged_parameter_specifications params params' ->
  well_typed_stack st' s ->
  well_typed_exps_x st' args' ->
  optimize_args_x st' params' args' args'' ->
  copy_in_x st' s f params' args' f' ->
  copy_in_x st' s f params' args'' f'.
Proof.
 induction params'; intros.
-inversion H4; subst.
 inversion H5; subst; auto.
- destruct args', args'', params, args;
  match goal with 
  | [H: copy_in_x _ _ _ (?a :: ?al) nil _ |- _] => inversion H
  | [H: optimize_args_x _ (?a :: ?al) (?e :: ?el) nil |- _] => inversion H
  | [H: compile2_flagged_parameter_specifications nil (?param :: ?params) |- _] => inversion H
  | [H: compile2_flagged_args _ (?param :: ?params) nil _ |- _] => inversion H
  | _ => idtac
  end.
  inversion H1; subst;
  inversion H3; subst.
  assert(HZ: p.(parameter_mode) = a.(parameter_mode_x)).
  clear - H9. inversion H9; crush;eauto.
  assert(HZ1: (parameter_subtype_mark p) = (parameter_subtype_mark_x a)).
  clear - H9. inversion H9; crush;eauto.
  (*******)
  inversion H; subst;
  inversion H4; subst;
  match goal with
  | [H1: parameter_mode ?p = parameter_mode_x ?a,
     H2: parameter_mode ?p = _ ,
     H3: parameter_mode_x ?a = _ |- _] => 
      rewrite H2 in H1; rewrite H3 in H1; inversion H1
  | [H1: parameter_mode_x ?a = _ ,
     H2: parameter_mode_x ?a = _ |- _] => rewrite H2 in H1; inversion H1
  end;
  match goal with
  | [H: extract_subtype_range_x _ _ (Range_X _ _) |- _] => 
      specialize (range_constrainted_type_true _ _ _ _ H);
      let HZ := fresh "HZ" in intros HZ
  | _ => idtac
  end;
  match goal with
  | [H1: is_range_constrainted_type ?x = false, 
     H2: is_range_constrainted_type ?y = true,
     H3: ?x = ?y |- _] => 
      rewrite H3 in H1; rewrite H1 in H2; inversion H2
  | _ => idtac
  end;
  (*******)
  inversion H5; subst;
  match goal with
  | [H1: parameter_mode_x ?a = _ ,
     H2: parameter_mode_x ?a = _ |- _] => rewrite H2 in H1; inversion H1
  end;
  match goal with
  | [H: extract_subtype_range_x _ _ (Range_X _ _) |- _] => 
      specialize (range_constrainted_type_true _ _ _ _ H);
      let HZ := fresh "HZ" in intros HZ
  | _ => idtac
  end;

  match goal with
  | [H1: compile2_flagged_symbol_table ?st ?st',
     H2: fetch_exp_type _ ?st = _ |- _ ] => 
      specialize (symbol_table_exp_type_rel _ _ _ _ H1 H2);
      let HZ := fresh "HZ" in intros HZ
  | _ => idtac
  end;
  match goal with
  | [H1: fetch_exp_type_x ?x ?st = _, 
     H2: fetch_exp_type_x ?x ?st = _ |- _] => rewrite H1 in H2; inversion H2; subst
  | _ => idtac
  end;

  match goal with
  | [H1: is_range_constrainted_type ?x = false, 
     H2: is_range_constrainted_type ?x = true |- _] => 
      rewrite H1 in H2; inversion H2
  | [H1: is_range_constrainted_type ?x = false, 
     H2: is_range_constrainted_type ?y = true,
     H3: ?x = ?y |- _] => 
      rewrite H3 in H1; rewrite H1 in H2; inversion H2
  | _ => idtac
  end;
  match goal with
  | [H1: ?x = true,
     H2: ?y = true,
     H3: ?x = false \/ ?y = false |- _] => rewrite H1 in H3; rewrite H2 in H3; clear - H3; crush;eauto
  | [H: ~ List.In ?x (name_exterior_checks (update_exterior_checks_name _ (?x :: _))) |- _] =>
      rewrite name_updated_exterior_checks in H; clear - H; crush;eauto
  | [H: ~ List.In ?x (name_exterior_checks (update_exterior_checks_name _ (_ :: ?x :: _))) |- _] =>
      rewrite name_updated_exterior_checks in H; clear - H; crush;eauto
  | _ => idtac
  end;
  (*-------------*)
  match goal with
  | [H: optimize_name_x _ _ _ |- _] => 
      specialize (optimize_name_ex_cks_eq _ _ _ _ H);
      let HZ := fresh "HZ" in intro HZ
  | _ => idtac
  end;
  match goal with
  | [H: optimize_expression_x _ _ _ |- _] => 
      specialize (optimize_exp_ex_cks_stripped _ _ _ _ _ H);
      let HZ := fresh "HZ" in intro HZ
  | _ => idtac
  end;
  match goal with
  | [H: eval_name_x _ _ (update_exterior_checks_name _ _) _ |- _] => 
      specialize (eval_name_ex_cks_stripped _ _ _ _ _ H);
      let HZ := fresh "HZ" in intro HZ
  | _ => idtac
  end;
  match goal with
  | [H: eval_expr_x _ _ (update_exterior_checks_exp _ _) _ |- _] => 
      specialize (eval_exp_ex_cks_stripped _ _ _ _ _ H);
      let HZ := fresh "HZ" in intro HZ
  | _ => idtac
  end;
  match goal with
  | [H: well_typed_exp_x _ (E_Name_X _ _) |- _] => inversion H; subst
  | _ => idtac
  end;
  match goal with
  | [H: well_typed_name_x ?st (update_exterior_checks_name ?n ?cks) |- _] =>
      specialize (well_typed_name_preserve _ _ _ H);
      let HZ := fresh "HZ" in intro HZ
  | _ => idtac
  end;
  match goal with
  | [H: well_typed_exp_x ?st (update_exterior_checks_exp ?e ?cks) |- _] =>
      specialize (well_typed_exp_preserve _ _ _ H);
      let HZ := fresh "HZ" in intro HZ
  | _ => idtac
  end;

  match goal with
  | [H: storeUpdate_x _ _ (update_exterior_checks_name _ _) _ _ |- _] =>
      specialize (store_update_ex_cks_stripped _ _ _ _ _ _ H);
      let HZ := fresh "HZ" in intro HZ
  | _ => idtac
  end;
  match goal with
  | [H: optimize_name_x _ (update_exterior_checks_name _ _) _ |- _] =>
      specialize (optimize_name_ex_cks_stripped _ _ _ _ _ H); 
      let HZ := fresh "HZ" in intros HZ
  | _ => idtac
  end;
  match goal with
  | [H: optimize_expression_x _ (update_exterior_checks_exp _ _) _ |- _] =>
      specialize (optimize_exp_ex_cks_stripped _ _ _ _ _ H); 
      let HZ := fresh "HZ" in intros HZ
  | _ => idtac
  end;
  (*---------------*)
  match goal with
  | [H1: forall (st : symboltable) (st' : symboltable_x)
                (s : STACK.stack) (f : STACK.frame) 
                (f' : Return STACK.frame)
                (params : list parameter_specification)
                (args : list expression) (args' args'' : list expression_x),
              compile2_flagged_args st params args args' ->
              compile2_flagged_symbol_table st st' ->
              compile2_flagged_parameter_specifications params ?params' ->
              well_typed_stack st' s ->
              well_typed_exps_x st' args' ->
              optimize_args_x st' ?params' args' args'' ->
              copy_in_x st' s f ?params' args' f' ->
              copy_in_x st' s f ?params' args'' f',
     H2: compile2_flagged_args ?st ?params ?args ?args', 
     H3: compile2_flagged_symbol_table ?st ?st',
     H4: compile2_flagged_parameter_specifications ?params ?params',
     H5: well_typed_stack ?st' ?s,
     H6: well_typed_exps_x ?st' ?args',
     H7: optimize_args_x ?st' ?params' ?args' ?args'',
     H8: copy_in_x ?st' ?s ?f ?params' ?args' ?f' |- _ ] =>
      specialize (H1 _ _ _ _ _ _ _ _ _ H2 H3 H4 H5 H6 H7 H8)
  | _ => idtac
  end.
  + apply Copy_In_Mode_In_eRTE_X; auto.
    apply_expression_checks_optimization_soundness; auto.
  + apply Copy_In_Mode_In_NoRangeCheck_X with (v := v) (f' := (STACK.push f (parameter_name_x a) v)); auto.
    apply_expression_checks_optimization_soundness; auto.
    apply_optimize_exp_ex_cks_eq; crush;eauto.
  + apply Copy_In_Mode_In_eRTE_X; auto.
    apply_expression_checks_optimization_soundness; auto.
    apply eval_exp_ex_cks_stripped with (cks := (exp_exterior_checks arg_flagged)); auto.
  + rewrite exp_updated_exterior_checks in H27. inversion H27.
  + apply Copy_In_Mode_In_eRTE_X; auto.
    apply eval_expr_value_reserve with (e:=arg') (eBound:=(Interval u' v')) (rBound:=(Interval u v)); auto.
    apply_expression_checks_optimization_soundness; auto.
    apply eval_exp_ex_cks_stripped with (cks := (exp_exterior_checks arg_flagged)); auto.
  + rewrite exp_updated_exterior_checks in H28. inversion H28.
  + apply Copy_In_Mode_In_Range_RTE_X with (v:=v0) (l:=l) (u:=u0); auto.
    apply eval_expr_value_reserve with (e:=arg') (eBound:=(Interval u' v')) (rBound:=(Interval u v)); auto.

    apply_expression_checks_optimization_soundness; auto.
    apply eval_exp_ex_cks_stripped with (cks := (exp_exterior_checks arg_flagged)); auto.
    
    apply_extract_subtype_range_unique; subst. 
    specialize (optimize_exp_ex_cks_eq _ _ _ _ H23); intros HZ7.
    rewrite exp_updated_exterior_checks in HZ7.
    apply_eval_expr_value_in_bound. 
    inversion H31; subst.
    apply_optimize_range_check_reserve. crush;eauto. 

  + inversion H24; subst. (*H24: optimize_range_check arg' (Interval u' v') (Interval u v) e0*)
  * specialize (optimize_exp_ex_cks_eq _ _ _ _ H23); intros HZ7.
    rewrite exp_updated_exterior_checks in HZ7. rewrite HZ7; crush;eauto.
    apply Copy_In_Mode_In_NoRangeCheck_X with (v := Int v0) (f' := (STACK.push f (parameter_name_x a) (Int v0))); auto.
    apply_expression_checks_optimization_soundness.
    specialize (exp_exterior_checks_beq_nil _ _ _ H19); intros HZ9. rewrite HZ9 in HZ8; assumption.
    rewrite exp_updated_exterior_checks; auto.
  * apply Copy_In_Mode_In_Range_X with (v := v0) (l := l) (u := u0) 
                                       (f' := (STACK.push f (parameter_name_x a) (Int v0))); auto.
    apply_expression_checks_optimization_soundness.
    specialize (eval_exp_ex_cks_stripped _ _ _ _ _ HZ7); auto.
    specialize (optimize_exp_ex_cks_eq _ _ _ _ H23); intros HZ7.
    rewrite exp_updated_exterior_checks in HZ7; auto.
  + apply Copy_In_Mode_Out_X with (f' := (STACK.push f (parameter_name_x a) Undefined)); auto.
  + assert (HZ7: exists n1, e0 = E_Name_X ast_num n1).
      clear - H28. inversion H28; subst.
      exists (update_exterior_checks_name n' (remove_check_flag Do_Range_Check (exp_exterior_checks (E_Name_X ast_num n')))).
      simpl; auto. exists n'; auto.
    inversion HZ7; subst.
    apply Copy_In_Mode_Out_X with (f' := (STACK.push f (parameter_name_x a) Undefined)); auto.
  + apply Copy_In_Mode_InOut_eRTE_x; auto.
    apply_name_checks_optimization_soundness; auto.
  + apply Copy_In_Mode_InOut_NoRange_X with (v := v) (f' := (STACK.push f (parameter_name_x a) v)); auto.
    apply_name_checks_optimization_soundness; auto.
    rewrite HZ2; assumption.
  + apply Copy_In_Mode_InOut_eRTE_x; auto.
    apply_name_checks_optimization_soundness.
    apply eval_name_ex_cks_stripped with (cks := (name_exterior_checks n_flagged)); auto.      
  + apply Copy_In_Mode_InOut_Range_RTE_X with (v:=v) (l:=l) (u:=u); auto.
    apply_name_checks_optimization_soundness.
    apply eval_name_ex_cks_stripped with (cks := (name_exterior_checks n_flagged)); auto. 
    rewrite name_updated_exterior_checks in HZ3.
    clear - HZ3. crush;eauto.
  + apply Copy_In_Mode_InOut_Range_X with (v:=v) (l:=l) (u:=u) (f':=(STACK.push f (parameter_name_x a) (Int v))); auto.
    apply_name_checks_optimization_soundness.
    apply eval_name_ex_cks_stripped with (cks := (name_exterior_checks n_flagged)); auto. 
    rewrite name_updated_exterior_checks in HZ3.
    clear - HZ3. crush;eauto.
  + apply Copy_In_Mode_InOut_eRTE_x; auto.
    apply_name_checks_optimization_soundness.
    apply eval_name_ex_cks_stripped with (cks := (name_exterior_checks n_flagged)); auto.
  + apply Copy_In_Mode_InOut_NoRange_X with (v := v) (f' := (STACK.push f (parameter_name_x a) v)); auto.
    apply_name_checks_optimization_soundness.
    apply eval_name_ex_cks_stripped with (cks := (name_exterior_checks n_flagged)); auto. 
    rewrite name_updated_exterior_checks in HZ2.
    clear - HZ2. rewrite HZ2; crush;eauto.
  (*******)
  (* the following two are the cases where do optimization on range check and range check on copy out,
     and prove that the evaluation results are the same after these optimization. 
     n' has checks: (Do_Range_Check_On_CopyOut :: nil)
  *)
  + clear H H3 H4.
    inversion H28; subst. (* optimize_expression_x st' (E_Name_X _ _ _) (E_Name_X _ _ n', _)*)
    match goal with
    | [H: optimize_name_x _ (update_exterior_checks_name _ _) _ |- _] =>
        specialize (optimize_name_ex_cks_stripped _ _ _ _ _ H); 
        let HZ := fresh "HZ" in intros HZ
    end.
    apply_name_checks_optimization_soundness.
    match goal with
    | [H: eval_name_x _ _ (update_exterior_checks_name _ _) _ |- _] => 
        specialize (eval_name_ex_cks_stripped _ _ _ _ _ H);
        let HZ := fresh "HZ" in intro HZ
    end.

    apply_optimize_range_check_preserve.
    apply Copy_In_Mode_InOut_eRTE_x; auto.
    inversion HA0; auto.
  + clear H H3 H4 H5 H35.
    inversion H28; subst.
    match goal with
    | [H: optimize_name_x _ (update_exterior_checks_name _ _) _ |- _] =>
        specialize (optimize_name_ex_cks_stripped _ _ _ _ _ H); 
        let HZ := fresh "HZ" in intros HZ
    end.
    apply_name_checks_optimization_soundness.
    match goal with
    | [H: eval_name_x _ _ (update_exterior_checks_name _ _) _ |- _] => 
        specialize (eval_name_ex_cks_stripped _ _ _ _ _ H);
        let HZ := fresh "HZ" in intro HZ
    end.
    apply_optimize_range_check_preserve.
    apply Copy_In_Mode_InOut_NoRange_X with (v:=v0) (f':=(STACK.push f (parameter_name_x a) v0)); auto.
    inversion HA0; auto.
    specialize (optimize_exp_ex_cks_eq _ _ _ _ H28); intros HZ9. 
    simpl in HZ9. rewrite name_updated_exterior_checks in HZ9.
    clear - H29 H30 HZ9.
      inversion H29; subst; inversion H30; subst; simpl in *; rewrite HZ9 in *;
      match goal with
      | [H: E_Name_X _ _ = E_Name_X _ _ |- _] => clear - H; inversion H; subst
      | _ => idtac
      end;
      repeat progress rewrite name_updated_exterior_checks; crush;eauto.
  + apply Copy_In_Mode_InOut_eRTE_x; auto.
    apply_name_checks_optimization_soundness.
    apply eval_name_ex_cks_stripped with (cks := (name_exterior_checks n_flagged)); auto.    
  (*******)
  (* the following four are the cases where do optimization on range check and range check on copy out,
     and prove that the evaluation results are the same after these optimization. 
     n' has checks: (Do_Range_Check :: Do_Range_Check_On_CopyOut :: nil)
  *)
  + clear H H3 H4.
    inversion H28; subst. (* optimize_expression_x st' (E_Name_X _ _ _) (E_Name_X _ _ n', _)*)
    match goal with
    | [H: optimize_name_x _ (update_exterior_checks_name _ _) _ |- _] =>
        specialize (optimize_name_ex_cks_stripped _ _ _ _ _ H); 
        let HZ := fresh "HZ" in intros HZ
    end.
    apply_name_checks_optimization_soundness.
    match goal with
    | [H: eval_name_x _ _ (update_exterior_checks_name _ _) _ |- _] => 
        specialize (eval_name_ex_cks_stripped _ _ _ _ _ H);
        let HZ := fresh "HZ" in intro HZ
    end.
    apply_optimize_range_check_preserve.    
    apply Copy_In_Mode_InOut_eRTE_x; auto.
    inversion HA0; auto.
  + clear H H3 H4.
    apply_extract_subtype_range_unique.
    inversion H28; subst. (* optimize_expression_x st' (E_Name_X _ _ _) (E_Name_X _ _ n', _)*)
    match goal with
    | [H: optimize_name_x _ (update_exterior_checks_name _ _) _ |- _] =>
        specialize (optimize_name_ex_cks_stripped _ _ _ _ _ H); 
        let HZ := fresh "HZ" in intros HZ
    end.
    apply_name_checks_optimization_soundness.
    match goal with
    | [H: eval_name_x _ _ (update_exterior_checks_name _ _) _ |- _] => 
        specialize (eval_name_ex_cks_stripped _ _ _ _ _ H);
        let HZ := fresh "HZ" in intro HZ
    end.
    apply_optimize_range_check_preserve. 
    apply Copy_In_Mode_InOut_Range_RTE_X with (v:=v0) (l:=l) (u:=u0); auto.
    inversion HA0; auto.
    specialize (optimize_exp_ex_cks_eq _ _ _ _ H28); intros HZ9. 
    simpl in HZ9. rewrite name_updated_exterior_checks in HZ9.
    apply_eval_name_value_in_bound. 
    inversion H37; subst.
    apply_optimize_range_check_reserve.
    clear - H30 HZ11 HZ9.
    inversion H30; crush;eauto.
    rewrite name_updated_exterior_checks; crush;eauto.
  + clear H H3 H4.
    apply_extract_subtype_range_unique.
    inversion H28; subst.
    match goal with
    | [H: optimize_name_x _ (update_exterior_checks_name _ _) _ |- _] =>
        specialize (optimize_name_ex_cks_stripped _ _ _ _ _ H); 
        let HZ := fresh "HZ" in intros HZ
    end.
    apply_name_checks_optimization_soundness.
    match goal with
    | [H: eval_name_x _ _ (update_exterior_checks_name _ _) _ |- _] => 
        specialize (eval_name_ex_cks_stripped _ _ _ _ _ H);
        let HZ := fresh "HZ" in intro HZ
    end.
    apply_optimize_range_check_preserve.
    specialize (optimize_exp_ex_cks_eq _ _ _ _ H28); intros HZ9.
    simpl in HZ9. rewrite name_updated_exterior_checks in HZ9.
    inversion H29; subst. 
    * apply Copy_In_Mode_InOut_NoRange_X with (v:=Int v0) (f':=(STACK.push f (parameter_name_x a) (Int v0))); auto.
      inversion HA0; auto.
      inversion H30; subst; simpl in *; rewrite HZ9 in *;
      match goal with
      | [H: E_Name_X _ _ = E_Name_X _ _ |- _] => clear - H; inversion H; subst
      | _ => idtac
      end;
      repeat progress rewrite name_updated_exterior_checks; crush;eauto.
    * apply Copy_In_Mode_InOut_Range_X with (v:=v0) (l:=l) (u:=u0) (f':=(STACK.push f (parameter_name_x a) (Int v0))); auto.
      inversion HA0; auto.
      inversion H30; subst; simpl in *; rewrite HZ9 in *;
      match goal with
      | [H: E_Name_X _ _ = E_Name_X _ _ |- _] => clear - H; inversion H; subst
      | _ => idtac
      end;
      repeat progress rewrite name_updated_exterior_checks; crush;eauto.
Qed.

Ltac apply_copy_in_args_checks_optimization_soundness :=
  match goal with
  | [H1: compile2_flagged_args ?st ?params ?args ?args',
     H2: compile2_flagged_symbol_table ?st ?st',
     H3: compile2_flagged_parameter_specifications ?params ?params',
     H4: well_typed_stack ?st' ?s,
     H5: well_typed_exps_x ?st' ?args',
     H6: optimize_args_x ?st' ?params' ?args' ?args'',
     H7: copy_in_x ?st' ?s ?f ?params' ?args' ?f' |- _ ] =>
      specialize (copy_in_args_checks_optimization_soundness _ _ _ _ _ _ _ _ _ _ H1 H2 H3 H4 H5 H6 H7);
      let HZ := fresh "HZ" in intro HZ
  end.

(*---------------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------------*)

(** * util version with well_typed_value_in_stack and well_typed_value_in_store *)

Lemma eval_expr_value_in_bound': forall e st st' s e' v e'' eBound,
  compile2_flagged_exp st e e' ->
    compile2_flagged_symbol_table st st' ->
      well_typed_value_in_stack st' s ->
        well_typed_exp_x st' e' ->
          eval_expr_x st' s e' (Normal (Int v)) ->
            optimize_expression_x st' e' (e'', eBound) ->
              in_bound v eBound true.
Proof.
  intros;
  apply_well_typed_stack_infer;
  apply_eval_expr_value_in_bound; auto.
Qed.

Ltac apply_eval_expr_value_in_bound' :=
  match goal with
  | [H1: compile2_flagged_exp ?st ?e ?e',
     H2: compile2_flagged_symbol_table ?st ?st',
     H3: well_typed_value_in_stack ?st' ?s,
     H4: well_typed_exp_x ?st' ?e',
     H5: eval_expr_x ?st' ?s ?e' (Normal (Int ?v)),
     H6: optimize_expression_x ?st' ?e' _ |- _] =>
      specialize (eval_expr_value_in_bound' _ _ _ _ _ _ _ _ H1 H2 H3 H4 H5 H6);
      let HZ := fresh "HZ" in intros HZ
  end.

Lemma eval_name_value_in_bound': forall n st st' s n' v n'' nBound,
  compile2_flagged_name st n n' ->
    compile2_flagged_symbol_table st st' ->
      well_typed_value_in_stack st' s ->
        well_typed_name_x st' n' ->
          eval_name_x st' s n' (Normal (Int v)) ->
            optimize_name_x st' n' (n'', nBound) ->
              in_bound v nBound true.
Proof.
  intros;
  apply_well_typed_stack_infer;
  apply_eval_name_value_in_bound; auto.
Qed.

Ltac apply_eval_name_value_in_bound' :=
  match goal with
  | [H1: compile2_flagged_name ?st ?n ?n',
     H2: compile2_flagged_symbol_table ?st ?st',
     H3: well_typed_value_in_stack ?st' ?s,
     H4: well_typed_name_x ?st' ?n',
     H5: eval_name_x ?st' ?s ?n' (Normal (Int ?v)),
     H6: optimize_name_x ?st' ?n' (?n'', ?nBound) |- _] =>
      specialize (eval_name_value_in_bound' _ _ _ _ _ _ _ _ H1 H2 H3 H4 H5 H6);
      let HZ := fresh "HZ" in intros HZ
  end.

Lemma expression_checks_optimization_soundness': forall e st st' s e' e'' eBound v, 
  compile2_flagged_exp st e e' ->
    compile2_flagged_symbol_table st st' ->
      well_typed_value_in_stack st' s ->
        well_typed_exp_x st' e' ->
          optimize_expression_x st' e' (e'', eBound) ->
            eval_expr_x st' s e' v ->
              eval_expr_x st' s e'' v.
Proof.
  intros;
  apply_well_typed_stack_infer;
  apply_expression_checks_optimization_soundness; auto.
Qed.

Ltac apply_expression_checks_optimization_soundness' :=
  match goal with
  | [H1: compile2_flagged_exp ?st ?e ?e',
     H2: compile2_flagged_symbol_table ?st ?st',
     H3: well_typed_value_in_stack ?st' ?s,
     H4: well_typed_exp_x ?st' ?e',
     H5: optimize_expression_x ?st' ?e' _,
     H6: eval_expr_x ?st' ?s ?e' ?v |- _] => 
      specialize (expression_checks_optimization_soundness' _ _ _ _ _ _ _ _ H1 H2 H3 H4 H5 H6);
      let HZ := fresh "HZ" in
      intro HZ
  end.

Lemma name_checks_optimization_soundness': forall n st st' s n' n'' nBound v, 
  compile2_flagged_name st n n' ->
    compile2_flagged_symbol_table st st' ->
      well_typed_value_in_stack st' s ->
        well_typed_name_x st' n' ->
          optimize_name_x st' n' (n'', nBound) ->
            eval_name_x st' s n' v ->
              eval_name_x st' s n'' v.
Proof.
  intros;
  apply_well_typed_stack_infer;
  apply_name_checks_optimization_soundness; auto.
Qed.

Ltac apply_name_checks_optimization_soundness' := 
  match goal with
  | [H1: compile2_flagged_name ?st ?n ?n',
     H2: compile2_flagged_symbol_table ?st ?st',
     H3: well_typed_value_in_stack ?st' ?s,
     H4: well_typed_name_x ?st' ?n',
     H5: optimize_name_x ?st' ?n' _,
     H6: eval_name_x ?st' ?s ?n' ?v |- _] =>
      specialize (name_checks_optimization_soundness' _ _ _ _ _ _ _ _ H1 H2 H3 H4 H5 H6);
      let HZ := fresh "HZ" in
      intro HZ
  end.

Lemma store_update_optimization_soundness': forall n st st' s s' n' n'' nBound v, 
  compile2_flagged_name st n n' ->
    compile2_flagged_symbol_table st st' ->
      well_typed_value_in_stack st' s ->
        well_typed_name_x st' n' ->
          optimize_name_x st' n' (n'', nBound) ->
            storeUpdate_x st' s n' v s' ->
              storeUpdate_x st' s n'' v s'.
Proof.
  intros;
  apply_well_typed_stack_infer;
  apply_store_update_optimization_soundness; auto.
Qed.

Ltac apply_store_update_optimization_soundness' := 
  match goal with
  | [H1: compile2_flagged_name ?st ?n ?n' ,
     H2: compile2_flagged_symbol_table ?st ?st' ,
     H3: well_typed_value_in_stack ?st' ?s ,
     H4: well_typed_name_x ?st' ?n' ,
     H5: optimize_name_x ?st' ?n' _ ,
     H6: storeUpdate_x ?st' ?s ?n' ?v ?s' |- _] =>
      specialize (store_update_optimization_soundness' _ _ _ _ _ _ _ _ _ H1 H2 H3 H4 H5 H6);
      let HZ := fresh "HZ" in
      intro HZ
  end.

Lemma copy_in_args_checks_optimization_soundness': forall params' st st' s f f' params args args' args'',
  compile2_flagged_args st params args args' ->
  compile2_flagged_symbol_table st st' ->
  compile2_flagged_parameter_specifications params params' ->
  well_typed_value_in_stack st' s ->
  well_typed_exps_x st' args' ->
  optimize_args_x st' params' args' args'' ->
  copy_in_x st' s f params' args' f' ->
  copy_in_x st' s f params' args'' f'.
Proof.
  intros;
  apply_well_typed_stack_infer;
  apply_copy_in_args_checks_optimization_soundness; auto.
Qed.

Ltac apply_copy_in_args_checks_optimization_soundness' :=
  match goal with
  | [H1: compile2_flagged_args ?st ?params ?args ?args',
     H2: compile2_flagged_symbol_table ?st ?st',
     H3: compile2_flagged_parameter_specifications ?params ?params',
     H4: well_typed_value_in_stack ?st' ?s,
     H5: well_typed_exps_x ?st' ?args',
     H6: optimize_args_x ?st' ?params' ?args' ?args'',
     H7: copy_in_x ?st' ?s ?f ?params' ?args' ?f' |- _ ] =>
      specialize (copy_in_args_checks_optimization_soundness' _ _ _ _ _ _ _ _ _ _ H1 H2 H3 H4 H5 H6 H7);
      let HZ := fresh "HZ" in intro HZ
  end.

(*---------------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------------*)
(*---------------------------------  END !  ---------------------------------------*)
(*---------------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------------*)


