(** 
_AUTHOR_

<<
Zhi Zhang
Department of Computer and Information Sciences
Kansas State University
zhangzhi@ksu.edu
>>
*)

Require Export rt_gen.
Require Export rt_opt_util.
Require Export well_typed_util.


Scheme expression_ind := Induction for exp Sort Prop 
                         with name_ind := Induction for name Sort Prop.

Scheme expression_x_ind := Induction for expRT Sort Prop 
                         with name_x_ind := Induction for nameRT Sort Prop.


(** * Eval Expr Value In Bound *)

Lemma eval_expr_value_in_bound: forall e st st' s e' v e'' eBound,
  toExpRT st e e' ->
    toSymTabRT st st' ->
      well_typed_stack st' s ->
        well_typed_exp_x st' e' ->
          evalExpRT st' s e' (OK (Int v)) ->
            optExp st' e' (e'', eBound) ->
              in_bound v eBound true.
Proof.
  apply (expression_ind
    (fun e: exp =>
       forall (st : symTab) (st' : symTabRT) (s : STACK.state) 
              (e' : expRT) (v : Z) (e'' : expRT) eBound,
         toExpRT st e e' ->
         toSymTabRT st st' ->
         well_typed_stack st' s ->
         well_typed_exp_x st' e' ->
         evalExpRT st' s e' (OK (Int v)) ->
         optExp st' e' (e'', eBound) ->
         in_bound v eBound true)
    (fun n: name =>
       forall (st : symTab) (st' : symTabRT) (s : STACK.state) 
              (n' : nameRT) (v : Z) (n'' : nameRT) eBound,
         toNameRT st n n' ->
         toSymTabRT st st' ->
         well_typed_stack st' s ->
         well_typed_name_x st' n' ->
         evalNameRT st' s n' (OK (Int v)) ->
         optName st' n' (n'', eBound) ->
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
    apply In_Bound_Two; auto. 
    apply In_Bound_Refl; auto.
  + inversion H13; subst.
    inversion H8; subst.
    inversion H5; subst.
    apply_in_bound_conflict; smack.
- inversion H0; subst;
  inversion H3; subst;
  inversion H4; subst;
  inversion H5; subst.
  specialize (H _ _ _ _ _ _ _ H10 H1 H2 H11 H14 H8); assumption.
- inversion H1; subst;
  inversion H4; subst;
  inversion H5; subst;
  inversion H6; subst.
  
  + (** b = Plus \/ b = Minus \/ b = Multiply *)
    apply_binop_arithm_operand_format; subst.
    specialize (H _ _ _ _ _ _ _ H14 H2 H3 H17 H25 H11).
    specialize (H0 _ _ _ _ _ _ _ H15 H2 H3 H18 H26 H29).
    apply_plus_result_in_bound; auto.
  + (** Divide *)
    apply_binop_arithm_operand_format; subst.
    specialize (H _ _ _ _ _ _ _ H14 H2 H3 H16 H24 H11).
    specialize (H0 _ _ _ _ _ _ _ H15 H2 H3 H17 H25 H28).
    match goal with
    | [H1: evalBinOpRTS (DivCheck :: _) _ _ _ _ |- _] => inversion H1; subst
    end;
    repeat progress match goal with
    | [H1: evalBinOpRT DivCheck _ _ _ _ |- _] => inversion H1; subst; clear H1
    | [H1: divCheck ?op ?v0 ?v3 (OK ?v4) |- _ ] => inversion H1; subst; clear H1
    end.
    apply_divide_result_in_bound; auto.
  + (** Modulus *)
    apply_binop_arithm_operand_format; subst.
    specialize (H _ _ _ _ _ _ _ H14 H2 H3 H16 H24 H11).
    specialize (H0 _ _ _ _ _ _ _ H15 H2 H3 H17 H25 H28).
    match goal with
    | [H1: evalBinOpRTS (DivCheck :: _) _ _ _ _ |- _] => inversion H1; subst
    end;
    repeat progress match goal with
    | [H1: evalBinOpRT DivCheck _ _ _ _ |- _] => inversion H1; subst; clear H1
    | [H1: divCheck ?op ?v0 ?v3 (OK ?v4) |- _ ] => inversion H1; subst; clear H1
    end.
    apply_modulus_result_in_bound; auto.
  + inversion H31; subst.
    clear - H11 H12 H13 H15 H17 H8.
    destruct b; smack;
    destruct v1, v2; inversion H8.
- inversion H0; subst;
  inversion H3; subst;
  inversion H4; subst;
  inversion H5; subst.
  + apply_unop_arithm_operand_format; subst.
    specialize (H _ _ _ _ _ _ _ H12 H1 H2 H11 H19 H9).
    apply_unop_arithm_in_bound; auto.
  + inversion H21; subst.
    destruct u; destruct v0; inversion H7; smack.
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
  inversion H16; smack;
  [inversion H5; subst; inversion H13 | | | ];
  apply_extract_subtype_range_unique; smack.
- apply_eval_name_well_typed_value.
  inversion H1; subst;
  inversion H4; subst;
  inversion H6; subst.
  smack.
  rewrite H23 in H17; inversion H17; subst.
  rewrite H16 in HZ0; inversion HZ0; subst.
  inversion H26; subst.
  rewrite H7 in H18; inversion H18; subst.

  inversion HZ1; subst;  
  inversion H8; smack;
  [inversion H9; subst; inversion H20 | | | ];
  apply_extract_subtype_range_unique; smack.
- apply_eval_name_well_typed_value.
  inversion H0; subst;
  inversion H3; subst;
  inversion H5; smack.
  rewrite H20 in H14; inversion H14; subst.
  rewrite H13 in HZ0; inversion HZ0; subst.
  inversion H21; subst.
  rewrite H6 in H15; inversion H15; subst.
  rewrite H7 in H16; inversion H16; subst.
  
  inversion HZ1; subst;
  inversion H8; smack;
  [ inversion H9; subst; inversion H22 | | | ];
  apply_extract_subtype_range_unique; smack.  
Qed.

Ltac apply_eval_expr_value_in_bound :=
  match goal with
  | [H1: toExpRT ?st ?e ?e',
     H2: toSymTabRT ?st ?st',
     H3: well_typed_stack ?st' ?s,
     H4: well_typed_exp_x ?st' ?e',
     H5: evalExpRT ?st' ?s ?e' (OK (Int ?v)),
     H6: optExp ?st' ?e' _ |- _] =>
      specialize (eval_expr_value_in_bound _ _ _ _ _ _ _ _ H1 H2 H3 H4 H5 H6);
      let HZ := fresh "HZ" in intros HZ
  end.

(** * Eval Name Value In Bound *)
Lemma eval_name_value_in_bound: forall n st st' s n' v n'' nBound,
  toNameRT st n n' ->
    toSymTabRT st st' ->
      well_typed_stack st' s ->
        well_typed_name_x st' n' ->
          evalNameRT st' s n' (OK (Int v)) ->
            optName st' n' (n'', nBound) ->
              in_bound v nBound true.
Proof.
  induction n; intros.
- inversion H; subst;
  inversion H2; subst;
  inversion H3; subst;
  inversion H4; subst.
  
  apply_eval_name_well_typed_value. simpl in HZ0.
  repeat progress match goal with
  | [H1: fetch_exp_type_rt ?x ?st = _,
     H2: fetch_exp_type_rt ?x ?st = _ |- _] => rewrite H1 in H2; inversion H2; subst
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
  | [H1: fetch_exp_type_rt ?x ?st = _,
     H2: fetch_exp_type_rt ?x ?st = _ |- _] => rewrite H1 in H2; inversion H2; subst
  | _ => idtac
  end.
  clear - H30 H16 HZ1. (* H30: bound_of_array_component_type st' t2 nBound*)
  inversion H30; subst.
  match goal with
  | [H1: fetch_type_rt ?x ?st = _,
     H2: fetch_type_rt ?x ?st = _ |- _] => rewrite H1 in H2; inversion H2; subst
  end.
  apply_typed_value_in_bound; auto.
- apply_eval_name_well_typed_value.
  inversion H; subst;
  inversion H2; subst;
  inversion H3; subst;
  inversion H4; smack.

  repeat progress match goal with
  | [H1: fetch_exp_type_rt ?x ?st = _,
     H2: fetch_exp_type_rt ?x ?st = _ |- _] => rewrite H1 in H2; inversion H2; subst
  | _ => idtac
  end.
  clear - H22 H14 H15 HZ1.
  inversion H22; subst.
  repeat progress match goal with
  | [H1: fetch_type_rt ?x ?st = _,
     H2: fetch_type_rt ?x ?st = _ |- _] => rewrite H1 in H2; inversion H2; subst
  | [H1: record_field_type _ _ = _,
     H2: record_field_type _ _ = _ |- _] => rewrite H1 in H2; inversion H2; subst
  end.
  apply_typed_value_in_bound; auto.
Qed.

Ltac apply_eval_name_value_in_bound :=
  match goal with
  | [H1: toNameRT ?st ?n ?n',
     H2: toSymTabRT ?st ?st',
     H3: well_typed_stack ?st' ?s,
     H4: well_typed_name_x ?st' ?n',
     H5: evalNameRT ?st' ?s ?n' (OK (Int ?v)),
     H6: optName ?st' ?n' (?n'', ?nBound) |- _] =>
      specialize (eval_name_value_in_bound _ _ _ _ _ _ _ _ H1 H2 H3 H4 H5 H6);
      let HZ := fresh "HZ" in intros HZ
  end.

(** * Soundness of RT-OPT Specification *)

(** ** Helper Lemmas *)

Lemma binop_int_operant_exists: forall op cks v1 v2 v, 
  (op = Plus \/ op = Minus \/ op = Multiply) \/ (op = Divide \/ op = Modulus) ->
    evalBinOpRTS cks op v1 v2 v ->
      exists v1' v2', v1 = (Int v1') /\ v2 = (Int v2').
Proof.
  intros.
  destruct H as [[HZ1 | [HZ2 | HZ3]] | [HZ4 | HZ5]]; subst;
  destruct v1, v2;
  inversion H0;
  match goal with
  | [|- exists v1' v2', Int ?n = Int v1' /\ Int ?n0 = Int v2'] => exists n, n0; auto 
  | [H: Math.binary_operation _ _ _ = _ |- _] => inversion H; subst
  | _ => idtac
  end;
  match goal with
  | [H: evalBinOpRT _ _ _ _ _ |- _] => inversion H; subst
  | _ => idtac
  end;
  match goal with
  | [|- exists v1' v2', Int ?n = Int v1' /\ Int ?n0 = Int v2'] => exists n, n0; auto 
  | [H: Math.binary_operation _ _ _ = _ |- _] => inversion H; subst
  | _ => idtac
  end.
Qed.

Ltac apply_binop_int_operant_exists :=
  match goal with
  | [H1: (?op = Plus \/ ?op = Minus \/ ?op = Multiply) |- _] =>
      let HA := fresh "HA" in
      assert (HA: (op = Plus \/ op = Minus \/ op = Multiply) \/ (op = Divide \/ op = Modulus))
  | [H1: evalBinOpRTS _ Divide _ _ _ |- _] =>
      let HA := fresh "HA" in
      assert (HA: (Divide = Plus \/ Divide = Minus \/ Divide = Multiply) \/ (Divide = Divide \/ Divide = Modulus))
  | [H1: evalBinOpRTS _ Modulus _ _ _ |- _] =>
      let HA := fresh "HA" in
      assert (HA: (Modulus = Plus \/ Modulus = Minus \/ Modulus = Multiply) \/ (Modulus = Divide \/ Modulus = Modulus))
  end; auto;
  match goal with
  | [H1: (?op = Plus \/ ?op = Minus \/ ?op = Multiply) \/ (?op = Divide \/ ?op = Modulus),
     H2: evalBinOpRTS ?cks ?op ?v1 ?v2 ?v |- _] =>
      specialize (binop_int_operant_exists _ _ _ _ _ H1 H2);
      let HZ := fresh "HZ" in intros HZ
  end.

Lemma optimize_range_check_reserve_storeUpdate: forall st s n v s' u l u' l' n' ast_num ast_num',
  storeUpdateRT st s n v s' ->
    optimize_range_check (NameRT ast_num n) (Interval l u) (Interval l' u') (NameRT ast_num' n') ->
      storeUpdateRT st s n' v s'.
Proof.
  intros.
  inversion H0; smack.
  apply_store_update_ex_cks_added; auto.  
Qed.

Ltac apply_optimize_range_check_reserve_storeUpdate :=
  match goal with
  | [H1: storeUpdateRT ?st ?s ?n ?v ?s',
     H2: optimize_range_check (NameRT ?ast_num ?n) (Interval ?l ?u) (Interval ?l' ?u') (NameRT ?ast_num' ?n') |- _] =>
    specialize (optimize_range_check_reserve_storeUpdate _ _ _ _ _ _ _ _ _ _ _ _ H1 H2);
    let HZ := fresh "HZ" in intro HZ  
  end.

Lemma optimize_range_check_reserve_storeUpdate_backward: forall st s n v s' u l u' l' n' ast_num ast_num',
  storeUpdateRT st s n' v s' ->
    optimize_range_check (NameRT ast_num n) (Interval l u) (Interval l' u') (NameRT ast_num' n') ->
      storeUpdateRT st s n v s'.
Proof.
  intros.
  inversion H0; smack.
  apply_store_update_ex_cks_stripped; auto.  
Qed.

Ltac apply_optimize_range_check_reserve_storeUpdate_backward :=
  match goal with
  | [H1: storeUpdateRT ?st ?s ?n' ?v ?s',
     H2: optimize_range_check (NameRT ?ast_num ?n) (Interval ?l ?u) (Interval ?l' ?u') (NameRT ?ast_num' ?n') |- _] =>
    specialize (optimize_range_check_reserve_storeUpdate_backward _ _ _ _ _ _ _ _ _ _ _ _ H1 H2);
    let HZ := fresh "HZ" in intro HZ  
  end.

Lemma optimize_range_check_on_copy_out_reserve_storeUpdate: forall st s n v s' u l u' l' n' ast_num ast_num',
  storeUpdateRT st s n v s' ->
    optimize_range_check_on_copy_out (NameRT ast_num n) (Interval u l) (Interval u' l') (NameRT ast_num' n') ->
      storeUpdateRT st s n' v s'.
Proof.
  intros.
  inversion H0; smack.
  apply_store_update_ex_cks_added; auto.  
Qed.

Ltac apply_optimize_range_check_on_copy_out_reserve_storeUpdate :=
  match goal with
  | [H1: storeUpdateRT ?st ?s ?n ?v ?s',
     H2: optimize_range_check_on_copy_out (NameRT ?ast_num ?n) (Interval ?l ?u) (Interval ?l' ?u') (NameRT ?ast_num' ?n') |- _] =>
    specialize (optimize_range_check_on_copy_out_reserve_storeUpdate _ _ _ _ _ _ _ _ _ _ _ _ H1 H2);
    let HZ := fresh "HZ" in intro HZ  
  end.

Lemma optimize_range_check_on_copy_out_reserve_storeUpdate_backward: forall st s n v s' u l u' l' n' ast_num ast_num',
  storeUpdateRT st s n' v s' ->
    optimize_range_check_on_copy_out (NameRT ast_num n) (Interval u l) (Interval u' l') (NameRT ast_num' n') ->
      storeUpdateRT st s n v s'.
Proof.
  intros.
  inversion H0; smack.
  apply_store_update_ex_cks_stripped; auto.  
Qed.

Ltac apply_optimize_range_check_on_copy_out_reserve_storeUpdate_backward :=
  match goal with
  | [H1: storeUpdateRT ?st ?s ?n' ?v ?s',
     H2: optimize_range_check_on_copy_out (NameRT ?ast_num ?n) (Interval ?l ?u) (Interval ?l' ?u') (NameRT ?ast_num' ?n') |- _] =>
    specialize (optimize_range_check_on_copy_out_reserve_storeUpdate_backward _ _ _ _ _ _ _ _ _ _ _ _ H1 H2);
    let HZ := fresh "HZ" in intro HZ  
  end.

Lemma optimize_range_check_both_reserve_storeUpdate: forall st s n v s' u l u' l' n' n'' u1 l1 u1' l1' ast_num ast_num' ast_num'',
  storeUpdateRT st s n v s' ->
    optimize_range_check (NameRT ast_num n) (Interval u l) (Interval u' l') (NameRT ast_num' n') ->
      optimize_range_check_on_copy_out (NameRT ast_num' n') (Interval u1 l1) (Interval u1' l1') (NameRT ast_num'' n'') ->
        storeUpdateRT st s n'' v s'.
Proof.
  intros.
  specialize (optimize_range_check_reserve_storeUpdate _ _ _ _ _ _ _ _ _ _ _ _ H H0); intro.
  specialize (optimize_range_check_on_copy_out_reserve_storeUpdate _ _ _ _ _ _ _ _ _ _ _ _ H2 H1); auto.
Qed.

Ltac apply_optimize_range_check_both_reserve_storeUpdate :=
  match goal with
  | [H1: storeUpdateRT ?st ?s ?n ?v ?s',
     H2: optimize_range_check (NameRT _ ?n) (Interval ?u ?l) (Interval ?u' ?l') (NameRT _ ?n'),
     H3: optimize_range_check_on_copy_out (NameRT _ ?n') (Interval ?u1 ?l1) (Interval ?u1' ?l1') (NameRT _ ?n'')  |- _] =>
    specialize (optimize_range_check_both_reserve_storeUpdate _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H1 H2 H3);
    let HZ := fresh "HZ" in intro HZ  
  end.

Lemma optimize_range_check_both_reserve_storeUpdate_backward: forall st s n v s' u l u' l' n' n'' u1 l1 u1' l1' ast_num ast_num' ast_num'',
  storeUpdateRT st s n'' v s' ->
    optimize_range_check (NameRT ast_num n) (Interval u l) (Interval u' l') (NameRT ast_num' n') ->
      optimize_range_check_on_copy_out (NameRT ast_num' n') (Interval u1 l1) (Interval u1' l1') (NameRT ast_num'' n'') ->
        storeUpdateRT st s n v s'.
Proof.
  intros.
  specialize (optimize_range_check_on_copy_out_reserve_storeUpdate_backward _ _ _ _ _ _ _ _ _ _ _ _ H H1); intro.
  specialize (optimize_range_check_reserve_storeUpdate_backward _ _ _ _ _ _ _ _ _ _ _ _ H2 H0); auto.
Qed.

Ltac apply_optimize_range_check_both_reserve_storeUpdate_backward :=
  match goal with
  | [H1: storeUpdateRT ?st ?s ?n'' ?v ?s',
     H2: optimize_range_check (NameRT _ ?n) (Interval ?u ?l) (Interval ?u' ?l') (NameRT _ ?n'),
     H3: optimize_range_check_on_copy_out (NameRT _ ?n') (Interval ?u1 ?l1) (Interval ?u1' ?l1') (NameRT _ ?n'')  |- _] =>
    specialize (optimize_range_check_both_reserve_storeUpdate_backward _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H1 H2 H3);
    let HZ := fresh "HZ" in intro HZ  
  end.
  
(* toExpRT st0 e0 e: make sure that e is decorated with correct run time checks,
   which is required to call the lemma: eval_expr_well_typed_value, that make sure the the 
   evaluation value of e is well-typed with respect to its type;
   e.g. eval_expr s (Literal 10^100) in_cks out_cks, if in_cks is empty, then its value
        is not well-typed with reespect to integer;
 *)
Lemma optimize_expression_exist_int_value: forall e e0 e' st0 st s v l u,
  toExpRT st0 e0 e ->
    toSymTabRT st0 st ->
      well_typed_stack_and_symboltable st s ->
        well_typed_exp_x st e ->
          evalExpRT st s e (OK v) ->
            v <> Undefined ->
              optExp st e (e', Interval l u) ->
                exists n, v = Int n.
Proof.
  induction e; intros;
  apply_eval_expr_well_typed_value;
  destruct HZ as [t' [HZ1 HZ2]];
  inversion H3; subst; clear H3;
  inversion H5; smack; clear H5.
  - inversion H13; smack.    
    inversion H7; smack.
    inversion H13; smack.
    inversion H8; smack.
    inversion H8; smack. inversion H6; smack.
  - match goal with
    | [H: well_typed_stack_and_symboltable ?st ?s |- _] => destruct H as [st s HStack HSymb]
    end;
    apply_well_typed_stack_infer.
    inversion H; subst;
    inversion HZ; subst;
    inversion H2; smack;
    apply_eval_name_well_typed_value.
    (* inversion H11; smack; *)
    inversion H7; smack.
    (* E_Identifier_X *)
    rewrite H13 in HZ3; inversion HZ3; subst.
    apply_well_typed_int_value_exists; smack.
    (* E_Indexed_Component_X *)
    match goal with
    | [H: well_typed_name_x _ _ |- _] => inversion H; subst
    end.
    match goal with
    | [H: bound_of_array_component_type _ ?t _ |- _] => inversion H; subst
    end.
    repeat progress match goal with
    | [H1: fetch_exp_type_rt ?a ?st = Some ?t1, H2: fetch_exp_type_rt ?a ?st = Some ?t2 |- _]
        => rewrite H1 in H2; inversion H2; subst
    | [H1: fetch_type_rt ?t ?st = Some ?t1, H2: fetch_type_rt ?t ?st = Some ?t2 |- _] 
        => rewrite H1 in H2; inversion H2; subst
    end.
    clear - H5 HZ4 H4.
    apply_well_typed_int_value_exists; smack.
    (* E_Selected_Component_X *)
    match goal with
    | [H: well_typed_name_x _ _ |- _] => inversion H; subst
    end.
    match goal with
    | [H: bound_of_record_field_type _ ?t ?f _ |- _] => inversion H; smack
    end.
    repeat progress match goal with
    | [H1: fetch_exp_type_rt ?a ?st = Some ?t1, H2: fetch_exp_type_rt ?a ?st = Some ?t2 |- _]
        => rewrite H1 in H2; inversion H2; subst
    | [H1: fetch_type_rt ?t ?st = Some ?t1, H2: fetch_type_rt ?t ?st = Some ?t2 |- _] 
        => rewrite H1 in H2; inversion H2; subst
    | [H1: record_field_type ?fields ?f = Some ?t1, H2: record_field_type ?fields ?f = Some ?t2 |- _] 
        => rewrite H1 in H2; inversion H2; subst
    end.
    apply_well_typed_int_value_exists; smack.
  - inversion H2; subst;
    inversion H; subst.
    (* add/minus/multiply *)
    clear - H4 H10 H17 H19.
    repeat progress match goal with
    | [H: evalBinOpRTS _ ?op ?v1 ?v2 (OK ?v) |- _] => inversion H; clear H; smack
    end;
    destruct v1, v2;
    match goal with
    | [H: _ ?v1 ?v2 = Some ?v |- _] => inversion H; smack
    end.
    (* divide *)
    clear - H4 H17 H19.
    repeat progress match goal with
    | [H: evalBinOpRTS _ ?op ?v1 ?v2 (OK ?v) |- _] => inversion H; clear H; smack
    end;
    destruct v1, v2;
    match goal with
    | [H: _ ?v1 ?v2 = Some ?v |- _] => inversion H; smack
    end.
    (* modulus *)
    clear - H4 H17 H19.
    repeat progress match goal with
    | [H: evalBinOpRTS _ ?op ?v1 ?v2 (OK ?v) |- _] => inversion H; clear H; smack
    end;
    destruct v1, v2;
    match goal with
    | [H: _ ?v1 ?v2 = Some ?v |- _] => inversion H; smack
    end.
    (* and/or/... *)
    match goal with
    | [H: optimize_rtc_binop ?op ?bound1 ?bound2 _ _ |- _] => inversion H; smack
    end.
  - inversion H2; subst;
    inversion H; subst.
    (* unary_minus *)
    clear - H15.
    repeat progress match goal with
    | [H: evalUnOpRTS _ ?op ?v (OK ?v') |- _] => inversion H; clear H; smack
    end.
    destruct v0;
    match goal with
    | [H: Math.unary_minus ?v = Some ?v' |- _] => inversion H; smack
    end.
    (* <> Unary_Minus *)
    match goal with
    | [H: evalUnOpRTS _ ?op ?v (OK ?v') |- _] => inversion H; smack
    end.
    destruct u, v0;
    match goal with
    | [H: Math.unary_operation ?op ?v = Some ?v' |- _] => inversion H; smack
    end.
    clear - H9 H15 H16.
    inversion H16; smack.
Qed.

Ltac apply_optimize_expression_exist_int_value :=
  match goal with
  | [H1: toExpRT ?st0 ?e0 ?e,
     H2: toSymTabRT ?st0 ?st,
     H3: well_typed_stack_and_symboltable ?st ?s,
     H4: well_typed_exp_x ?st ?e,
     H5: evalExpRT ?st ?s ?e (OK ?v),
     H6: ?v <> Undefined,
     H7: optExp ?st ?e (?e', Interval ?l ?u) |- _] =>
    specialize (optimize_expression_exist_int_value _ _ _ _ _ _ _ _ _ H1 H2 H3 H4 H5 H6 H7);
    let HZ := fresh "HZ" in 
    let v := fresh "v0" in
    intro HZ; destruct HZ as [v HZ]; subst
  | [H1: toExpRT ?st0 ?e0 ?e,
     H2: toSymTabRT ?st0 ?st,
     H3: well_typed_stack_and_symboltable ?st ?s,
     H4: well_typed_exp_x ?st ?e,
     H5: evalExpRT ?st ?s ?e (OK ?v),
     H6: ?v = Undefined -> False,
     H7: optExp ?st ?e (?e', Interval ?l ?u) |- _] =>
    specialize (optimize_expression_exist_int_value _ _ _ _ _ _ _ _ _ H1 H2 H3 H4 H5 H6 H7);
    let HZ := fresh "HZ" in
    let v := fresh "v0" in
    intro HZ; destruct HZ as [v HZ]; subst
  end.

Lemma optimize_name_exist_int_value: forall n n0 n' st0 st s v l u,
  toNameRT st0 n0 n ->
    toSymTabRT st0 st ->
      well_typed_stack st s ->
        well_typed_name_x st n ->
          evalNameRT st s n (OK v) ->
            v <> Undefined ->
              optName st n (n', Interval l u) ->
                exists n, v = Int n.
Proof.
  induction n; intros;
  apply_eval_name_well_typed_value;
  inversion H3; subst; clear H3;
  inversion H5; smack; clear H5;
  inversion H; subst;
  inversion H1; subst;
  inversion H2; smack.
  (* E_Identifier_X *)
  rewrite H8 in HZ0; inversion HZ0; subst.
  apply_well_typed_int_value_exists; smack.
  (* E_Indexed_Component_X *)
  match goal with
  | [H: bound_of_array_component_type _ ?t _ |- _] => inversion H; subst
  end.
  repeat progress match goal with
  | [H1: fetch_exp_type_rt ?a ?st = Some ?t1, H2: fetch_exp_type_rt ?a ?st = Some ?t2 |- _]
      => rewrite H1 in H2; inversion H2; subst
  | [H1: fetch_type_rt t' st = Some ?t1, H2: fetch_type_rt t' st = Some ?t2 |- _] 
      => rewrite H1 in H2; inversion H2; subst
  end.
  clear - H4 HZ1 H6.
  apply_well_typed_int_value_exists; smack.
  (* E_Selected_Component_X *)
  match goal with
  | [H: bound_of_record_field_type _ ?t ?f _ |- _] => inversion H; smack
  end.
  repeat progress match goal with
  | [H1: fetch_exp_type_rt ?a ?st = Some ?t1, H2: fetch_exp_type_rt ?a ?st = Some ?t2 |- _]
        => rewrite H1 in H2; inversion H2; subst
  | [H1: fetch_type_rt ?t ?st = Some ?t1, H2: fetch_type_rt ?t ?st = Some ?t2 |- _] 
        => rewrite H1 in H2; inversion H2; subst
  | [H1: record_field_type ?fields ?f = Some ?t1, H2: record_field_type ?fields ?f = Some ?t2 |- _] 
        => rewrite H1 in H2; inversion H2; subst
    end.
  apply_well_typed_int_value_exists; smack.
Qed.

Ltac apply_optimize_name_exist_int_value :=
  match goal with
  | [H1: toNameRT ?st0 ?n0 ?n,
     H2: toSymTabRT ?st0 ?st,
     H3: well_typed_stack ?st ?s,
     H4: well_typed_name_x ?st ?n,
     H5: evalNameRT ?st ?s ?n (OK ?v),
     H6: ?v <> Undefined,
     H7: optName ?st ?n (?n', Interval ?l ?u) |- _] =>
    specialize (optimize_name_exist_int_value _ _ _ _ _ _ _ _ _ H1 H2 H3 H4 H5 H6 H7);
    let HZ := fresh "HZ" in
    let v := fresh "v0" in
    intro HZ; destruct HZ as [v HZ]; subst    
  | [H1: toNameRT ?st0 ?n0 ?n,
     H2: toSymTabRT ?st0 ?st,
     H3: well_typed_stack ?st ?s,
     H4: well_typed_name_x ?st ?n,
     H5: evalNameRT ?st ?s ?n (OK ?v),
     H6: ?v = Undefined -> False,
     H7: optName ?st ?n (?n', Interval ?l ?u) |- _] =>
    specialize (optimize_name_exist_int_value _ _ _ _ _ _ _ _ _ H1 H2 H3 H4 H5 H6 H7);
    let HZ := fresh "HZ" in
    let v := fresh "v0" in
    intro HZ; destruct HZ as [v HZ]; subst
  end.


(** ** optExp_soundness *)
Lemma optExp_soundness: forall e st st' s e' e'' eBound v, 
  toExpRT st e e' ->
    toSymTabRT st st' ->
      well_typed_stack st' s ->
        well_typed_exp_x st' e' ->
          optExp st' e' (e'', eBound) ->
            evalExpRT st' s e'' v ->
              evalExpRT st' s e' v.
Proof.
  apply (expression_ind
    (fun e: exp =>
       forall (st : symTab) (st' : symTabRT) (s : STACK.state)
              (e': expRT) (e'': expRT) (eBound: bound) (v : Ret value),
      toExpRT st e e' ->
      toSymTabRT st st' ->
      well_typed_stack st' s ->
      well_typed_exp_x st' e' ->
      optExp st' e' (e'', eBound) ->
      evalExpRT st' s e'' v ->
      evalExpRT st' s e' v)
    (fun n: name =>
       forall (st : symTab) (st' : symTabRT) (s : STACK.state)
              (n': nameRT) (n'': nameRT) (nBound: bound) (v : Ret value),
      toNameRT st n n' ->
      toSymTabRT st st' ->
      well_typed_stack st' s ->
      well_typed_name_x st' n' ->
      optName st' n' (n'', nBound) ->
      evalNameRT st' s n'' v ->
      evalNameRT st' s n' v)
    ); intros.
- (** E_Literal_X *)  
  inversion H; subst;
  inversion H3; subst;
  inversion H4; subst;
  inversion H7; subst; auto;
  constructor; smack;
  inversion H10; smack.
  inversion H12; subst. 
  apply_in_bound_conflict; smack.
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
  | [H: forall (st : symTab) (st' : symTabRT) 
        (s : STACK.state) (e' e'' : expRT) (eBound : bound)
        (v : Ret value),
      toExpRT st ?e e' ->
      toSymTabRT st st' ->
      well_typed_stack st' s ->
      well_typed_exp_x st' e' ->
      optExp st' e' (e'', eBound) ->
      evalExpRT st' s e'' v -> evalExpRT st' s e' v,
     H1: toExpRT ?st ?e ?e',
     H2: toSymTabRT ?st ?st',
     H3: well_typed_stack ?st' ?s,
     H4: well_typed_exp_x ?st' ?e',
     H5: optExp ?st' ?e' (?e'', ?eBound),
     H6: evalExpRT ?st' ?s ?e'' ?v |- _] => specialize (H _ _ _ _ _ _ _ H1 H2 H3 H4 H5 H6)
  end;
  [apply EvalBinOpRTE1_RTE; auto | | | apply EvalBinOpRTE1_RTE; auto | | | apply EvalBinOpRTE1_RTE; auto | | |
   apply EvalBinOpRTE1_RTE; auto | | ];
  [apply EvalBinOpRTE2_RTE with (v1:=v1); auto | | 
   apply EvalBinOpRTE2_RTE with (v1:=v1); auto | |
   apply EvalBinOpRTE2_RTE with (v1:=v1); auto | |
   apply EvalBinOpRTE2_RTE with (v1:=v1); auto | ];
  apply EvalBinOpRT with (v1:=v1) (v2:=v2); auto.
  + (* Plus | Minus | Multiply *)
    apply_binop_int_operant_exists.
    destruct HZ; subst. destruct H7; subst. destruct H7; subst.
    apply_eval_expr_value_in_bound.
    specialize (eval_expr_value_in_bound _ _ _ _ _ _ _ _ H14 H2 H3 H17 H H11); intros.
    apply_plus_result_in_bound_backward; auto.
  + (* Divide *)
    apply_binop_int_operant_exists.
    destruct HZ; subst. destruct H7; subst. destruct H7; subst.
    apply_eval_expr_value_in_bound.
    specialize (eval_expr_value_in_bound _ _ _ _ _ _ _ _ H14 H2 H3 H16 H H11); intros.
    apply_divide_result_in_bound_backward; auto.
  + (* Modulus *)
    apply_binop_int_operant_exists.
    destruct HZ; subst. destruct H7; subst. destruct H7; subst.
    apply_eval_expr_value_in_bound.
    specialize (eval_expr_value_in_bound _ _ _ _ _ _ _ _ H14 H2 H3 H16 H H11); intros.
    apply_modulus_result_in_bound_backward; auto.
  + (* Logic Operator *)
  inversion H31; smack.
- (** E_Unary_Operation_X *)
  inversion H0; subst;
  inversion H3; subst;
  inversion H4; subst;
  inversion H5; subst;
  match goal with
  | [H: forall (st : symTab) (st' : symTabRT) 
        (s : STACK.state) (e' e'' : expRT) (eBound : bound)
        (v : Ret value),
      toExpRT st ?e e' ->
      toSymTabRT st st' ->
      well_typed_stack st' s ->
      well_typed_exp_x st' e' ->
      optExp st' e' (e'', eBound) ->
      evalExpRT st' s e'' v -> evalExpRT st' s e' v,
     H1: toExpRT ?st ?e ?e',
     H2: toSymTabRT ?st ?st',
     H3: well_typed_stack ?st' ?s,
     H4: well_typed_exp_x ?st' ?e',
     H5: optExp ?st' _ (?e'', _),
     H6: evalExpRT ?st' ?s ?e'' ?v |- _] => specialize (H _ _ _ _ _ _ _ H1 H2 H3 H4 H5 H6)
  end;
  [ apply EvalUnOpRT_RTE; auto | |
    apply EvalUnOpRT_RTE; auto | ];
  apply EvalUnOpRT with (v:=v0); auto.
  + 
    inversion H20; smack.
    inversion H18; smack.
    destruct v0; inversion H22; smack.
    apply_eval_expr_value_in_bound.
    specialize (In_Bound_Unary_Minus_Compat _ _ _ HZ); intro.
    apply_In_Bound_SubBound_Trans; auto.
    apply Do_Checks_Unop with (v':=(Int (- n))); auto.
    eapply OverflowCheckUnop; smack. 
    constructor; auto.
  + inversion H21; smack.  
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
  | [H: forall (st : symTab) (st' : symTabRT) 
        (s : STACK.state) (n' n'' : nameRT) (nBound : bound)
        (v : Ret value),
      toNameRT st ?n n' ->
      toSymTabRT st st' ->
      well_typed_stack st' s ->
      well_typed_name_x st' n' ->
      optName st' n' (n'', nBound) ->
      evalNameRT st' s n'' v -> evalNameRT st' s n' v,
    H1: toNameRT ?st ?n ?n',
    H2: toSymTabRT ?st ?st',
    H3: well_typed_stack ?st' ?s,
    H4: well_typed_name_x ?st' ?n',
    H5: optName ?st' ?n' (?n'', _),
    H6: evalNameRT ?st' ?s ?n'' ?v |- _] => 
      specialize (H _ _ _ _ _ _ _ H1 H2 H3 H4 H5 H6)
  end;
  match goal with
  | [H: forall (st : symTab) (st' : symTabRT) 
        (s : STACK.state) (e' e'' : expRT) (eBound : bound)
        (v : Ret value),
      toExpRT st ?e e' ->
      toSymTabRT st st' ->
      well_typed_stack st' s ->
      well_typed_exp_x st' e' ->
      optExp st' e' (e'', eBound) ->
      evalExpRT st' s e'' v -> evalExpRT st' s e' v,
     H1: toExpRT ?st ?e ?e',
     H2: toSymTabRT ?st ?st',
     H3: well_typed_stack ?st' ?s,
     H4: well_typed_exp_x ?st' ?e',
     H5: optExp ?st' ?e' (?e'', _),
     H6: evalExpRT ?st' ?s ?e'' ?v |- _] => specialize (H _ _ _ _ _ _ _ H1 H2 H3 H4 H5 H6)
  | _ => idtac
  end.
  + apply EvalIndexedComponentRTX_RTE; auto.
  + apply EvalIndexedComponentRTE_RTE with (a:=a0); auto.
    apply_well_typed_exp_preserve.
    apply_eval_expr_value_reserve_backward.
    specialize (optimize_exp_ex_cks_stripped _ _ _ _ _ H22); intro HZ1.
    apply eval_exp_ex_cks_added. 
    apply H0 with (st:=st) 
                  (e'':=update_exterior_checks_exp e' (exp_exterior_checks eRT)) 
                  (eBound:=Interval u v0); smack.
    apply eval_exp_ex_cks_added; auto.
  + apply_well_typed_exp_preserve.
    apply_eval_expr_value_reserve_backward.
    specialize (optimize_exp_ex_cks_stripped _ _ _ _ _ H22); intro HZ1.
    apply EvalIndexedComponentRT_Range_RTE with (a:=a0) (i:=i) (t:=t0) (l:=l) (u:=u0); auto.
    apply eval_exp_ex_cks_added; smack.
    apply H0 with (st:=st) 
                  (e'':=update_exterior_checks_exp e' (exp_exterior_checks eRT)) 
                  (eBound:=Interval u v0); smack.
    apply eval_exp_ex_cks_added; auto.
    specialize (optimize_name_ast_num_eq _ _ _ _ H21); smack.
    rewrite exp_updated_exterior_checks.
    clear - H31.
    inversion H31; subst.
    constructor; auto.
  + apply_well_typed_exp_preserve.
    apply_eval_expr_value_reserve_backward.
    specialize (optimize_exp_ex_cks_stripped _ _ _ _ _ H22); intro HZ1.
    apply EvalIndexedComponentRT with (a:=a0) (i:=i) (t:=t0) (l:=l) (u:=u0); auto.
    apply eval_exp_ex_cks_added; smack.
    apply H0 with (st:=st) 
                  (e'':=update_exterior_checks_exp e' (exp_exterior_checks eRT)) 
                  (eBound:=Interval u v0); smack.    
    apply eval_exp_ex_cks_added; auto.
    specialize (optimize_name_ast_num_eq _ _ _ _ H21); smack.
    rewrite exp_updated_exterior_checks.
    specialize (optimize_exp_ex_cks_eq _ _ _ _ H22); intro HZZ1.
    rewrite exp_updated_exterior_checks in HZZ1.
    inversion H25; smack.
    specialize (optimize_name_ast_num_eq _ _ _ _ H21); smack.
    match goal with
    | [H1: fetch_exp_type_rt ?x1 _ = fetch_exp_type_rt ?x2 _,
       H2: fetch_exp_type_rt ?x1 _ = Some _,
       H3: fetch_exp_type_rt ?x2 _ = Some _ |- _ ] => rewrite H2 in H1; rewrite H3 in H1; inversion H1; subst
    end.
    apply_extract_array_index_range_rt_unique; subst.
    assert(HZZ2: evalExpRT st' s (update_exterior_checks_exp e' (exp_exterior_checks eRT)) (OK (Int i))). 
    apply eval_exp_ex_cks_added; auto.
    specialize (H0 _ _ _ _ _ _ _ H12 H2 H3 HZ HZ1 HZZ2). 
    apply_eval_expr_value_in_bound.
    apply_optimize_range_check_backward; auto.
- (** E_Selected_Component_X *)
  inversion H0; subst;
  inversion H3; subst;
  inversion H4; subst;
  inversion H5; subst;
  match goal with
  | [H: forall (st : symTab) (st' : symTabRT) 
        (s : STACK.state) (n' n'' : nameRT) (nBound : bound)
        (v : Ret value),
      toNameRT st ?n n' ->
      toSymTabRT st st' ->
      well_typed_stack st' s ->
      well_typed_name_x st' n' ->
      optName st' n' (n'', nBound) ->
      evalNameRT st' s n'' v -> evalNameRT st' s n' v,
    H1: toNameRT ?st ?n ?n',
    H2: toSymTabRT ?st ?st',
    H3: well_typed_stack ?st' ?s,
    H4: well_typed_name_x ?st' ?n',
    H5: optName ?st' ?n' (?n'', _),
    H6: evalNameRT ?st' ?s ?n'' ?v |- _] => 
      specialize (H _ _ _ _ _ _ _ H1 H2 H3 H4 H5 H6)
  end.
  + apply EvalSelectedComponentRTX_RTE; auto.
  + apply EvalSelectedComponentRT with (r:=r); auto.    
Qed.  

Ltac apply_optExp_soundness :=
  match goal with
  | [H1: toExpRT ?st ?e ?e',
     H2: toSymTabRT ?st ?st',
     H3: well_typed_stack ?st' ?s,
     H4: well_typed_exp_x ?st' ?e',
     H5: optExp ?st' ?e' (?e'', _),
     H6: evalExpRT ?st' ?s ?e'' ?v |- _] => 
      specialize (optExp_soundness _ _ _ _ _ _ _ _ H1 H2 H3 H4 H5 H6);
      let HZ := fresh "HZ" in
      intro HZ
  | [H1: well_typed_stack_and_symboltable ?st' ?s |- _] => 
      inversion H1; subst; apply_well_typed_stack_infer;
      match goal with
      | [H1: toExpRT ?st ?e ?e',
         H2: toSymTabRT ?st ?st',
         H3: well_typed_stack ?st' ?s,
         H4: well_typed_exp_x ?st' ?e',
         H5: optExp ?st' ?e' (?e'', _),
         H6: evalExpRT ?st' ?s ?e'' ?v |- _] => 
          specialize (optExp_soundness _ _ _ _ _ _ _ _ H1 H2 H3 H4 H5 H6);
      let HZ := fresh "HZ" in
      intro HZ
      end
  end.


(** ** optName_soundness *)

Lemma optName_soundness: forall n st st' s n' n'' nBound v, 
  toNameRT st n n' ->
    toSymTabRT st st' ->
      well_typed_stack st' s ->
        well_typed_name_x st' n' ->
          optName st' n' (n'', nBound) ->
            evalNameRT st' s n'' v ->
              evalNameRT st' s n' v.
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
  | [H: forall (st : symTab) (st' : symTabRT) 
        (s : STACK.state) (n' n'' : nameRT) (nBound : bound)
        (v : Ret value),
      toNameRT st ?n n' ->
      toSymTabRT st st' ->
      well_typed_stack st' s ->
      well_typed_name_x st' n' ->
      optName st' n' (n'', nBound) ->
      evalNameRT st' s n'' v -> evalNameRT st' s n' v,
    H1: toNameRT ?st ?n ?n',
    H2: toSymTabRT ?st ?st',
    H3: well_typed_stack ?st' ?s,
    H4: well_typed_name_x ?st' ?n',
    H5: optName ?st' ?n' (?n'', _),
    H6: evalNameRT ?st' ?s ?n'' ?v |- _] => 
      specialize (H _ _ _ _ _ _ _ H1 H2 H3 H4 H5 H6)
  end.
  + apply EvalIndexedComponentRTX_RTE; auto.
  + apply EvalIndexedComponentRTE_RTE with (a:=a0); auto.
    apply_well_typed_exp_preserve.
    apply_eval_expr_value_reserve_backward.
    specialize (optimize_exp_ex_cks_stripped _ _ _ _ _ H20); intro HZ1.
    apply eval_exp_ex_cks_added. 
    apply optExp_soundness with (e:=e) (st:=st) 
        (e'':=update_exterior_checks_exp e' (exp_exterior_checks eRT)) (eBound:=Interval u v0); auto.
    apply eval_exp_ex_cks_added; auto.
  + apply_well_typed_exp_preserve.
    apply_eval_expr_value_reserve_backward.
    specialize (optimize_exp_ex_cks_stripped _ _ _ _ _ H20); intro HZ1.
    apply EvalIndexedComponentRT_Range_RTE with (a:=a0) (i:=i) (t:=t0) (l:=l) (u:=u0); auto.
    apply eval_exp_ex_cks_added; smack.
    apply optExp_soundness with (e:=e) (st:=st) 
        (e'':=update_exterior_checks_exp e' (exp_exterior_checks eRT)) (eBound:=Interval u v0); auto.
    apply eval_exp_ex_cks_added; auto.
    specialize (optimize_name_ast_num_eq _ _ _ _ H19); smack.
    rewrite exp_updated_exterior_checks.
    clear - H29.
    inversion H29; subst.
    constructor; auto.
  + apply_well_typed_exp_preserve.
    apply_eval_expr_value_reserve_backward.
    specialize (optimize_exp_ex_cks_stripped _ _ _ _ _ H20); intro HZ1.
    apply EvalIndexedComponentRT with (a:=a0) (i:=i) (t:=t0) (l:=l) (u:=u0); auto.
    apply eval_exp_ex_cks_added; smack.
    apply optExp_soundness with (e:=e) (st:=st) 
        (e'':=update_exterior_checks_exp e' (exp_exterior_checks eRT)) (eBound:=Interval u v0); auto.
    apply eval_exp_ex_cks_added; auto.
    specialize (optimize_name_ast_num_eq _ _ _ _ H19); smack.
    rewrite exp_updated_exterior_checks.
    specialize (optimize_exp_ex_cks_eq _ _ _ _ H20); intro HZZ1.
    rewrite exp_updated_exterior_checks in HZZ1.
    inversion H23; smack.
    specialize (optimize_name_ast_num_eq _ _ _ _ H19); smack.
    match goal with
    | [H1: fetch_exp_type_rt ?x1 _ = fetch_exp_type_rt ?x2 _,
       H2: fetch_exp_type_rt ?x1 _ = Some _,
       H3: fetch_exp_type_rt ?x2 _ = Some _ |- _ ] => rewrite H2 in H1; rewrite H3 in H1; inversion H1; subst
    end.
    apply_extract_array_index_range_rt_unique; subst.
    assert(HZZ2: evalExpRT st' s (update_exterior_checks_exp e' (exp_exterior_checks eRT)) (OK (Int i))). 
    apply eval_exp_ex_cks_added; auto.
    apply_optExp_soundness.
    apply_eval_expr_value_in_bound.
    apply_optimize_range_check_backward; auto.
- (** E_Selected_Component_X *)
  inversion H; subst;
  inversion H2; subst;
  inversion H3; subst;
  inversion H4; subst;
  match goal with
  | [H: forall (st : symTab) (st' : symTabRT) 
        (s : STACK.state) (n' n'' : nameRT) (nBound : bound)
        (v : Ret value),
      toNameRT st ?n n' ->
      toSymTabRT st st' ->
      well_typed_stack st' s ->
      well_typed_name_x st' n' ->
      optName st' n' (n'', nBound) ->
      evalNameRT st' s n'' v -> evalNameRT st' s n' v,
    H1: toNameRT ?st ?n ?n',
    H2: toSymTabRT ?st ?st',
    H3: well_typed_stack ?st' ?s,
    H4: well_typed_name_x ?st' ?n',
    H5: optName ?st' ?n' (?n'', _),
    H6: evalNameRT ?st' ?s ?n'' ?v |- _] => 
      specialize (H _ _ _ _ _ _ _ H1 H2 H3 H4 H5 H6)
  end.
  + apply EvalSelectedComponentRTX_RTE; auto.
  + apply EvalSelectedComponentRT with (r:=r); auto.   
Qed.

Ltac apply_optName_soundness := 
  match goal with
  | [H1: toNameRT ?st ?n ?n',
     H2: toSymTabRT ?st ?st',
     H3: well_typed_stack ?st' ?s,
     H4: well_typed_name_x ?st' ?n',
     H5: optName ?st' ?n' (?n'', _),
     H6: evalNameRT ?st' ?s ?n'' ?v |- _] =>
      specialize (optName_soundness _ _ _ _ _ _ _ _ H1 H2 H3 H4 H5 H6);
      let HZ := fresh "HZ" in
      intro HZ
  | [H1: well_typed_stack_and_symboltable ?st' ?s |- _] => 
      inversion H1; subst; apply_well_typed_stack_infer;
      match goal with
      | [H1: toNameRT ?st ?n ?n',
         H2: toSymTabRT ?st ?st',
         H3: well_typed_stack ?st' ?s,
         H4: well_typed_name_x ?st' ?n',
         H5: optName ?st' ?n' (?n'', _),
         H6: evalNameRT ?st' ?s ?n'' ?v |- _] =>
           specialize (optName_soundness _ _ _ _ _ _ _ _ H1 H2 H3 H4 H5 H6);
           let HZ := fresh "HZ" in
           intro HZ
      end
  end.

(** ** storeUpdateRT_opt_soundness *)
Lemma storeUpdateRT_opt_soundness: forall n st st' s s' n' n'' nBound v, 
  toNameRT st n n' ->
    toSymTabRT st st' ->
      well_typed_stack st' s ->
        well_typed_name_x st' n' ->
          optName st' n' (n'', nBound) ->
            storeUpdateRT st' s n'' v s' ->
              storeUpdateRT st' s n' v s'.
Proof.
  induction n; intros.
- inversion H; subst;
  inversion H3; smack.
- inversion H; subst;
  inversion H2; subst;
  inversion H3; subst;
  inversion H4; subst.
  + apply SU_Indexed_Component_xRTE_X; auto.
    apply_optName_soundness; auto.
  + apply SU_Indexed_Component_eRTE_X with (a:=a0); auto.
    destruct H26; apply_optName_soundness; auto.
    apply_eval_expr_value_reserve_backward.
    apply_well_typed_exp_preserve.
    specialize (optimize_exp_ex_cks_stripped _ _ _ _ _ H20); intro HZ1.
    apply eval_exp_ex_cks_added.
    apply optExp_soundness with (e:=e) (st:=st) 
        (e'':=update_exterior_checks_exp e' (exp_exterior_checks eRT)) (eBound:=Interval u v0); auto.
    apply eval_exp_ex_cks_added; auto.
  + apply_well_typed_exp_preserve.
    apply_eval_expr_value_reserve_backward.
    specialize (optimize_exp_ex_cks_stripped _ _ _ _ _ H20); intro HZ1.
    apply SU_Indexed_Component_Range_RTE_X with (a:=a0) (i:=i) (t:=t1) (l:=l) (u:=u0); auto.
    destruct H12; apply_optName_soundness; auto.
    apply eval_exp_ex_cks_added; auto.
    apply optExp_soundness with (e:=e) (st:=st) 
        (e'':=update_exterior_checks_exp e' (exp_exterior_checks eRT)) (eBound:=Interval u v0); auto.
    apply eval_exp_ex_cks_added; auto.    
    specialize (optimize_name_ast_num_eq _ _ _ _ H19); smack.
    rewrite exp_updated_exterior_checks.
    inversion H30; smack.   
  + apply_well_typed_exp_preserve.
    apply_eval_expr_value_reserve_backward.
    specialize (optimize_exp_ex_cks_stripped _ _ _ _ _ H20); intro HZ1.
    apply_optName_soundness; auto.
    assert(HZZ1: evalExpRT st' s (update_exterior_checks_exp e' (exp_exterior_checks eRT)) (OK (Int i))). apply eval_exp_ex_cks_added; auto.
    apply_optExp_soundness.
    specialize (optimize_name_ast_num_eq _ _ _ _ H19); intro HZ5.
    match goal with
    | [H1: fetch_exp_type_rt ?x1 _ = fetch_exp_type_rt ?x2 _,
       H2: fetch_exp_type_rt ?x1 _ = Some _,
       H3: fetch_exp_type_rt ?x2 _ = Some _ |- _ ] => rewrite H2 in H1; rewrite H3 in H1; inversion H1; subst
    end.
    apply_extract_array_index_range_rt_unique; subst.
    specialize (optimize_exp_ex_cks_eq _ _ _ _ H20); intros HZ7.
    rewrite exp_updated_exterior_checks in *.
    rewrite <- HZ7 in *.

    destruct H17; subst;
    [ apply SU_Indexed_Component_X with 
        (arrObj:=(ArrayV a0)) (a:=a0) (i:=i) (l:=l) (u:=u0) (t:=t1) (a1:=a1); smack | 
      apply SU_Indexed_Component_X with 
        (arrObj:=Undefined) (i:=i) (a:=nil) (l:=l) (u:=u0) (t:=t1) (a1:=a1); smack
    ];
    [apply eval_exp_ex_cks_added; auto | | apply eval_exp_ex_cks_added; auto | ];
    rewrite exp_updated_exterior_checks;
    apply_eval_expr_value_in_bound;
    apply_optimize_range_check_backward; auto.
- inversion H; subst;
  inversion H2; subst;
  inversion H3; subst;
  inversion H4; subst.
  + apply_optName_soundness;
    apply SU_Selected_Component_xRTE_X; smack.
  + destruct H23;
    [ apply SU_Selected_Component_X with 
        (recObj:=(RecordV r)) (r:=r) (r1:=(updateSelectedComp r i v)); smack |
      apply SU_Selected_Component_X with 
        (recObj:=Undefined) (r:=nil) (r1:=((i, v) :: nil)); smack
    ];
    apply_optName_soundness; auto.
Qed.
 
Ltac apply_storeUpdateRT_opt_soundness := 
  match goal with
  | [H1: toNameRT ?st ?n ?n' ,
     H2: toSymTabRT ?st ?st' ,
     H3: well_typed_stack ?st' ?s ,
     H4: well_typed_name_x ?st' ?n' ,
     H5: optName ?st' ?n' (?n'', _) ,
     H6: storeUpdateRT ?st' ?s ?n'' ?v ?s' |- _] =>
      specialize (storeUpdateRT_opt_soundness _ _ _ _ _ _ _ _ _ H1 H2 H3 H4 H5 H6);
      let HZ := fresh "HZ" in
      intro HZ
  | [H1: well_typed_stack_and_symboltable ?st' ?s |- _] => 
      inversion H1; subst; apply_well_typed_stack_infer;
      match goal with
      | [H1: toNameRT ?st ?n ?n' ,
         H2: toSymTabRT ?st ?st' ,
         H3: well_typed_stack ?st' ?s ,
         H4: well_typed_name_x ?st' ?n' ,
         H5: optName ?st' ?n' (?n'', _) ,
         H6: storeUpdateRT ?st' ?s ?n'' ?v ?s' |- _] =>
            specialize (storeUpdateRT_opt_soundness _ _ _ _ _ _ _ _ _ H1 H2 H3 H4 H5 H6);
            let HZ := fresh "HZ" in
            intro HZ
        end
  end.

(** ** optArgs_copyin_soundness *)
Lemma optArgs_copyin_soundness: forall st params args args' st' s f f' params' args'',
  toArgsRT st params args args' ->
  toSymTabRT st st' ->
  toParamSpecsRT params params' ->
  well_typed_stack_and_symboltable st' s ->
  well_typed_exps_x st' args' ->
  optArgs st' params' args' args'' ->
  copyInRT st' s f params' args'' f' ->
  copyInRT st' s f params' args' f'.
Proof.
 intros st params args args' st' s f f' params' args'' H.
 revert st' s f f' params' args''.
 induction H; intros.
- (* C2_Flagged_Args_Null *)
 inversion H0; subst.
 inversion H3; subst; auto.
- (* C2_Flagged_Args_In *)
 inversion H4; subst;
 inversion H6; subst.
 assert(HZ: param.(parameter_mode) = paramRT.(parameter_mode_rt)).
  clear - H11. inversion H11; smack.
 assert(HZ1: (parameter_subtype_mark param) = (parameter_subtype_mark_rt paramRT)).
  clear - H11. inversion H11; smack.

 inversion H7; subst;
 inversion H8; subst;
  match goal with
  | [H1: parameter_mode ?p = parameter_mode_rt ?a,
     H2: parameter_mode ?p = _ ,
     H3: parameter_mode_rt ?a = _,
     H4: parameter_mode_rt ?a = _ |- _] => 
      rewrite H2 in H1; rewrite H3 in H1; inversion H1; rewrite H3 in H4; inversion H4
  end;
  match goal with
  | [H: extract_subtype_range_rt _ _ (RangeRT _ _) |- _] => 
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
 apply_optExp_soundness; auto.
 apply CopyIn_Mode_In_eRTE_X; auto.

 apply CopyIn_Mode_In_NoRangeCheck_X 
   with (v:=v) (f':=(STACK.push f (parameter_nameRT paramRT) v)); smack.
 apply exp_exterior_checks_beq_nil with (st:=st) (e:=arg); auto.
- (* C2_Flagged_Args_In_RangeCheck *)
 inversion H4; subst;
 inversion H6; subst.
 assert(HZ: param.(parameter_mode) = paramRT.(parameter_mode_rt)).
  clear - H11. inversion H11; smack.
 assert(HZ1: (parameter_subtype_mark param) = (parameter_subtype_mark_rt paramRT)).
  clear - H11. inversion H11; smack.
 apply_well_typed_exp_preserve.
 inversion H7; subst;
 inversion H8; subst;
  match goal with
  | [H1: parameter_mode ?p = parameter_mode_rt ?a,
     H2: parameter_mode ?p = _ ,
     H3: parameter_mode_rt ?a = _,
     H4: parameter_mode_rt ?a = _ |- _] => 
      rewrite H2 in H1; rewrite H3 in H1; inversion H1; rewrite H3 in H4; inversion H4
  end;
  match goal with
  | [H: extract_subtype_range_rt _ _ (RangeRT _ _) |- _] => 
      specialize (range_constrainted_type_true _ _ _ _ H);
      let HZ := fresh "HZ" in intros HZ
  | _ => idtac
  end;
  match goal with
  | [H1: is_range_constrainted_type ?x = false, 
     H2: is_range_constrainted_type ?x = true |- _] => 
      rewrite H2 in H1; inversion H1
  | _ => idtac
  end;
  smack.
 (* case: CopyIn_Mode_In_eRTE_X: eval arg => RTE *)
 apply CopyIn_Mode_In_eRTE_X; auto.
 apply eval_exp_ex_cks_added; auto.
 apply_eval_expr_value_reserve_backward.
 specialize (optimize_exp_ex_cks_stripped _ _ _ _ _ H20); intro HZ4.
 specialize (eval_exp_ex_cks_added _ _ _ _ (exp_exterior_checks argRT) HZ3); intros HZ5.
 
 apply_optExp_soundness; auto.
 (* case: CopyIn_Mode_In_NoRangeCheck_X: eval arg => OK v, optimize the range check *)
 apply_eval_expr_value_reserve_backward.
 specialize (optimize_exp_ex_cks_stripped _ _ _ _ _ H20); intro HZ4.
 specialize (eval_exp_ex_cks_added _ _ _ _ (exp_exterior_checks argRT) HZ3); intros HZ5.
 apply_optExp_soundness; auto.
 apply_optimize_expression_exist_int_value.
 apply CopyIn_Mode_In_Range_X 
   with (v:=v1) (l:=u) (u:=v) (f':=(STACK.push f (parameter_nameRT paramRT) (Int v1))); smack.
 apply eval_exp_ex_cks_added; auto. 
 rewrite exp_updated_exterior_checks; auto.
 apply_eval_expr_value_in_bound.
 specialize (optimize_exp_ex_cks_eq _ _ _ _ H20); let HZ := fresh "HZ" in intro HZ.
 rewrite exp_updated_exterior_checks in HZ9.
 inversion H22; smack.
 apply_In_Bound_SubBound_Trans. constructor; auto.
 (* case:  CopyIn_Mode_In_Range_RTE_X *)
 apply_eval_expr_value_reserve_backward.
 specialize (optimize_exp_ex_cks_stripped _ _ _ _ _ H20); intro HZ4.
 specialize (eval_exp_ex_cks_added _ _ _ _ (exp_exterior_checks argRT) HZ3); intros HZ5.
 apply_optExp_soundness; auto.
 apply CopyIn_Mode_In_Range_RTE_X with (v:=v0) (l:=u) (u:=v); smack.
 apply eval_exp_ex_cks_added; auto. 
 rewrite exp_updated_exterior_checks; auto.
 apply_extract_subtype_range_unique; subst. auto.
 (* case:  CopyIn_Mode_In_Range_X *)
 apply_eval_expr_value_reserve_backward.
 specialize (optimize_exp_ex_cks_stripped _ _ _ _ _ H20); intro HZ4.
 specialize (eval_exp_ex_cks_added _ _ _ _ (exp_exterior_checks argRT) HZ3); intros HZ5.
 apply_optExp_soundness; auto.
 apply CopyIn_Mode_In_Range_X 
   with (v:=v0) (l:=u) (u:=v) (f':=(STACK.push f (parameter_nameRT paramRT) (Int v0))); smack.
 apply eval_exp_ex_cks_added; auto. 
 rewrite exp_updated_exterior_checks; auto.
 apply_extract_subtype_range_unique; subst. auto. 
-(* C2_Flagged_Args_Out *)
 inversion H5; subst;
 inversion H7; subst.
 assert(HZ: param.(parameter_mode) = paramRT.(parameter_mode_rt)).
  clear - H12. inversion H12; smack.
 assert(HZ1: (parameter_subtype_mark param) = (parameter_subtype_mark_rt paramRT)).
  clear - H12. inversion H12; smack.
 inversion H8; subst;
 inversion H9; subst;
  match goal with
  | [H1: parameter_mode ?p = parameter_mode_rt ?a,
     H2: parameter_mode ?p = _ ,
     H3: parameter_mode_rt ?a = _,
     H4: parameter_mode_rt ?a = _ |- _] => 
      rewrite H2 in H1; rewrite H3 in H1; inversion H1; rewrite H3 in H4; inversion H4
  end;
  match goal with
  | [H: extract_subtype_range_rt _ _ (RangeRT _ _) |- _] => 
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
 apply CopyIn_Mode_Out_X with (f' := (STACK.push f (parameter_nameRT paramRT) Undefined)); auto;
 apply IHtoArgsRT with (args'' := args'); smack. 
-(* C2_Flagged_Args_Out_RangeCheck, the proof is the same as C2_Flagged_Args_Out, 
    as the mode is out, so copyInRT is the same constructor: CopyIn_Mode_Out_X. *)
 inversion H5; subst;
 inversion H7; subst.
 assert(HZ: param.(parameter_mode) = paramRT.(parameter_mode_rt)).
  clear - H12. inversion H12; smack.
 assert(HZ1: (parameter_subtype_mark param) = (parameter_subtype_mark_rt paramRT)).
  clear - H12. inversion H12; smack.
 inversion H8; subst;
 inversion H9; subst;
  match goal with
  | [H1: parameter_mode ?p = parameter_mode_rt ?a,
     H2: parameter_mode ?p = _ ,
     H3: parameter_mode_rt ?a = _,
     H4: parameter_mode_rt ?a = _ |- _] => 
      rewrite H2 in H1; rewrite H3 in H1; inversion H1; rewrite H3 in H4; inversion H4
  end;
  match goal with
  | [H: extract_subtype_range_rt _ _ (RangeRT _ _) |- _] => 
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
 apply CopyIn_Mode_Out_X with (f' := (STACK.push f (parameter_nameRT paramRT) Undefined)); auto;
 apply IHtoArgsRT with (args'' := args'); smack. 
-(* C2_Flagged_Args_InOut *)
 inversion H6; subst;
 inversion H8; subst.
 assert(HZ: param.(parameter_mode) = paramRT.(parameter_mode_rt)).
  clear - H13. inversion H13; smack.
 assert(HZ1: (parameter_subtype_mark param) = (parameter_subtype_mark_rt paramRT)).
  clear - H13. inversion H13; smack.
 assert (HA1: name_exterior_checks nRT = nil).
   apply name_exterior_checks_beq_nil with (st:=st) (n:=nm); auto. 
 match goal with
 | [H: well_typed_exp_x _ (NameRT _ _) |- _] => inversion H; subst
 end;
 inversion H9; subst;
 inversion H10; subst;
  match goal with
  | [H1: parameter_mode ?p = parameter_mode_rt ?a,
     H2: parameter_mode ?p = _ ,
     H3: parameter_mode_rt ?a = _,
     H4: parameter_mode_rt ?a = _ |- _] => 
      rewrite H2 in H1; rewrite H3 in H1; inversion H1; rewrite H3 in H4; inversion H4
  end;
  match goal with
  | [H: extract_subtype_range_rt _ _ (RangeRT _ _) |- _] => 
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
  (* conflict: range constraint is both true and false for argument type *)
  match goal with
  | [H1: toSymTabRT ?st ?st',
     H2: fetch_exp_type _ ?st = _ |- _ ] => 
      specialize (symbol_table_exp_type_rel _ _ _ _ H1 H2);
      let HZ := fresh "HZ" in intros HZ
  | _ => idtac
  end;
  match goal with
  | [H1: fetch_exp_type_rt ?x ?st = Some _, 
     H2: fetch_exp_type_rt ?x ?st = Some _ |- _] => rewrite H1 in H2; inversion H2; subst
  | _ => idtac
  end;
  match goal with
  | [H1: is_range_constrainted_type ?x = false, 
     H2: is_range_constrainted_type ?x = true |- _] => 
      rewrite H1 in H2; inversion H2
  | _ => idtac
  end;
 apply_optName_soundness; auto;
 [apply CopyIn_Mode_InOut_eRTE_X; auto | 
  apply CopyIn_Mode_InOut_NoRange_X with (v := v) (f' := (STACK.push f (parameter_nameRT paramRT) v)); auto;
  [ clear - HA1; destruct (name_exterior_checks nRT); smack | 
    apply IHtoArgsRT with (args'' := args'); smack]].
-(* C2_Flagged_Args_InOut_In_RangeCheck *)
 inversion H6; subst;
 inversion H8; subst.
 assert(HZ: param.(parameter_mode) = paramRT.(parameter_mode_rt)).
  clear - H13. inversion H13; smack.
 assert(HZ1: (parameter_subtype_mark param) = (parameter_subtype_mark_rt paramRT)).
  clear - H13. inversion H13; smack.
 assert (HA1: name_exterior_checks nRT = nil). 
   apply name_exterior_checks_beq_nil with (st:=st) (n:=nm); auto. 
 match goal with
 | [H: well_typed_exp_x _ (NameRT _ _) |- _] => inversion H; subst
 end;
 (* apply_well_typed_name_preserve. *)
 inversion H9; subst;
 inversion H10; subst;
  match goal with
  | [H1: parameter_mode ?p = parameter_mode_rt ?a,
     H2: parameter_mode ?p = _ ,
     H3: parameter_mode_rt ?a = _,
     H4: parameter_mode_rt ?a = _ |- _] => 
      rewrite H2 in H1; rewrite H3 in H1; inversion H1; rewrite H3 in H4; inversion H4
  end;
  match goal with
  | [H: extract_subtype_range_rt _ _ (RangeRT _ _) |- _] => 
      specialize (range_constrainted_type_true _ _ _ _ H);
      let HZ := fresh "HZ" in intros HZ
  | _ => idtac
  end;
  match goal with
  | [H1: is_range_constrainted_type ?x = false, 
     H2: is_range_constrainted_type ?x = true |- _] => 
      rewrite H2 in H1; inversion H1; auto
  | _ => idtac
  end;
  (* conflict: range constraint is both true and false for argument type *)
  match goal with
  | [H1: toSymTabRT ?st ?st',
     H2: fetch_exp_type _ ?st = _ |- _ ] => 
      specialize (symbol_table_exp_type_rel _ _ _ _ H1 H2);
      let HZ := fresh "HZ" in intros HZ
  | _ => idtac
  end;
  match goal with
  | [H1: fetch_exp_type_rt ?x ?st = Some _, 
     H2: fetch_exp_type_rt ?x ?st = Some _ |- _] => rewrite H1 in H2; inversion H2; subst
  | _ => idtac
  end;
  match goal with
  | [H1: fetch_exp_type_rt ?astnum ?st' = Some ?t0,
     H2: extract_subtype_range_rt _ ?t0 (RangeRT _ _) |- _] => 
      specialize (range_constrainted_type_true _ _ _ _ H2);
      let HZ := fresh "HZ" in intros HZ
  | _ => idtac
  end;
  match goal with
  | [H1: is_range_constrainted_type ?x = false, 
     H2: is_range_constrainted_type ?x = true |- _] => 
      rewrite H1 in H2; inversion H2
  | _ => idtac
  end.
 (* case: CopyIn_Mode_InOut_eRTE_X: eval arg => RTE *)
 apply CopyIn_Mode_InOut_eRTE_X; auto.
 apply eval_name_ex_cks_added; auto.
 apply_well_typed_name_preserve.
 match goal with
 | [H: optName _ (update_exterior_checks_name _ _) _ |- _] =>
     specialize (optimize_name_ex_cks_stripped _ _ _ _ _ H); 
     let HZ := fresh "HZ" in intros HZ
 | _ => idtac
 end.
 apply optName_soundness 
    with (n:=nm) (st:=st) (n'':=update_exterior_checks_name n' (name_exterior_checks nRT)) (nBound:=nBound); auto.
 inversion H7; subst; apply_well_typed_stack_infer; auto.
 apply eval_name_ex_cks_added; auto.   
 (* case: CopyIn_Mode_InOut_NoRange_X: eval arg => OK v, optimize the range check *)
 (* conflict: n' has Do_Range_Check and n' has no range check *)
 apply_optimize_name_ex_cks_eq.
 rewrite name_updated_exterior_checks in HZ2.
 match goal with
 | [H1: ~ List.In RangeCheck (name_exterior_checks ?n'),
    H2: name_exterior_checks ?n' = RangeCheck :: nil |- _] => rewrite H2 in H1; clear -H1; smack
 end.
 (* case: CopyIn_Mode_InOut_Range_RTE_X *)
 apply_well_typed_name_preserve.
 specialize (optimize_name_ex_cks_stripped _ _ _ _ _ H27); intro HZ4.
 specialize (eval_name_ex_cks_added _ _ _ _ (name_exterior_checks nRT) H31); intros HZ5.
 apply_optName_soundness; auto.
 apply CopyIn_Mode_InOut_Range_RTE_X with (v:=v) (l:=l) (u:=u); auto.
 apply eval_name_ex_cks_added; auto.
 rewrite name_updated_exterior_checks; smack.
 (* case: CopyIn_Mode_InOut_Range_X *)
 apply_well_typed_name_preserve.
 specialize (optimize_name_ex_cks_stripped _ _ _ _ _ H27); intro HZ4.
 specialize (eval_name_ex_cks_added _ _ _ _ (name_exterior_checks nRT) H25); intros HZ5.
 apply_optName_soundness; auto.
 apply CopyIn_Mode_InOut_Range_X with (v:=v) (l:=l) (u:=u) (f':=(STACK.push f (parameter_nameRT paramRT) (Int v))); auto.
 apply eval_name_ex_cks_added; auto.
 rewrite name_updated_exterior_checks; smack.
 apply IHtoArgsRT with (args'' := args'); smack.
-(* C2_Flagged_Args_InOut_Out_RangeCheck *)
 inversion H6; subst;
 inversion H8; subst.
 assert(HZ: param.(parameter_mode) = paramRT.(parameter_mode_rt)).
  clear - H13. inversion H13; smack.
 assert(HZ1: (parameter_subtype_mark param) = (parameter_subtype_mark_rt paramRT)).
  clear - H13. inversion H13; smack.
 match goal with
 | [H: well_typed_exp_x _ (NameRT _ _) |- _] => inversion H; subst
 end;
 inversion H9; subst;
 inversion H10; subst;
  match goal with
  | [H1: parameter_mode ?p = parameter_mode_rt ?a,
     H2: parameter_mode ?p = _ ,
     H3: parameter_mode_rt ?a = _,
     H4: parameter_mode_rt ?a = _ |- _] => 
      rewrite H2 in H1; rewrite H3 in H1; inversion H1; rewrite H3 in H4; inversion H4
  end;
  match goal with
  | [H: extract_subtype_range_rt _ (parameter_subtype_mark_rt _) (RangeRT _ _) |- _] => 
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
 apply_well_typed_name_preserve;
 specialize (optimize_name_ex_cks_stripped _ _ _ _ _ H27); intro HZ4.
 (* case 1: CopyIn_Mode_InOut_eRTE_X, where eval argument to error *)
 apply CopyIn_Mode_InOut_eRTE_X; auto.
 apply eval_name_ex_cks_added; auto.
 apply optName_soundness
    with (n:=nm) (st:=st) (n'':=update_exterior_checks_name n' (name_exterior_checks nRT)) (nBound:=nBound); auto.
 inversion H7; subst; apply_well_typed_stack_infer; auto.
 apply eval_name_ex_cks_added; auto.
 (* case 2: CopyIn_Mode_InOut_NoRange_X *)
 apply CopyIn_Mode_InOut_NoRange_X with (v := v) (f' := (STACK.push f (parameter_nameRT paramRT) v)); auto.
 apply eval_name_ex_cks_added; auto.
 apply optName_soundness
    with (n:=nm) (st:=st) (n'':=update_exterior_checks_name n' (name_exterior_checks nRT)) (nBound:=nBound); auto.
 inversion H7; subst; apply_well_typed_stack_infer; auto.
 apply eval_name_ex_cks_added; auto.
 rewrite name_updated_exterior_checks. smack.
 apply IHtoArgsRT with (args'' := args'); smack.
-(* C2_Flagged_Args_InOut_RangeCheck *)
 inversion H6; subst;
 inversion H8; subst.
 assert(HZ: param.(parameter_mode) = paramRT.(parameter_mode_rt)).
  clear - H13. inversion H13; smack.
 assert(HZ1: (parameter_subtype_mark param) = (parameter_subtype_mark_rt paramRT)).
  clear - H13. inversion H13; smack.
 assert (HA1: name_exterior_checks nRT = nil). 
   apply name_exterior_checks_beq_nil with (st:=st) (n:=nm); auto. 
 match goal with
 | [H: well_typed_exp_x _ (NameRT _ _) |- _] => inversion H; subst
 end;
 (* apply_well_typed_name_preserve. *)
 inversion H9; subst;
 inversion H10; subst;
  match goal with
  | [H1: parameter_mode ?p = parameter_mode_rt ?a,
     H2: parameter_mode ?p = _ ,
     H3: parameter_mode_rt ?a = _,
     H4: parameter_mode_rt ?a = _ |- _] => 
      rewrite H2 in H1; rewrite H3 in H1; inversion H1; rewrite H3 in H4; inversion H4
  end;
  (* conflict: range constraint is both true and false for argument type *)
  match goal with
  | [H1: toSymTabRT ?st ?st',
     H2: fetch_exp_type _ ?st = _ |- _ ] => 
      specialize (symbol_table_exp_type_rel _ _ _ _ H1 H2);
      let HZ := fresh "HZ" in intros HZ
  | _ => idtac
  end;
  match goal with
  | [H1: fetch_exp_type_rt ?x ?st = Some _, 
     H2: fetch_exp_type_rt ?x ?st = Some _ |- _] => rewrite H1 in H2; inversion H2; subst
  | _ => idtac
  end;
  match goal with
  | [H1: is_range_constrainted_type ?param = true, 
     H2: is_range_constrainted_type ?t = true,
     H3: ?param = ?paramRT,
     H4: is_range_constrainted_type ?t = false \/
         is_range_constrainted_type ?paramRT = false |- _] => 
      rewrite H2 in H4; rewrite H3 in H1; rewrite H1 in H4; clear - H4; smack
  | _ => idtac
  end;
 match goal with
 | [H: optExp _ (NameRT _ _) _ |- _] => inversion H; subst
 end;
 apply_well_typed_name_preserve;
 specialize (optimize_name_ex_cks_stripped _ _ _ _ _ H14); intro HZ4.
 (* case: CopyIn_Mode_InOut_eRTE_X: eval arg => RTE *)
 apply CopyIn_Mode_InOut_eRTE_X; auto.
 apply eval_name_ex_cks_added; auto.
 assert(HA2: evalExpRT st' s  (NameRT n0 nm0) (RTE msg)). constructor; auto.
 apply_optimize_range_check_preserve_backward.
 apply optName_soundness
    with (n:=nm) (st:=st) (n'':=update_exterior_checks_name n' (name_exterior_checks nRT)) (nBound:=Interval v1 v2); auto.
 inversion H7; subst; apply_well_typed_stack_infer; auto.
 apply eval_name_ex_cks_added; auto.
 (* case: CopyIn_Mode_InOut_NoRange_X: eval arg => OK v, optimize the range check *)
 assert(HA2: evalExpRT st' s  (NameRT n0 nm0) (OK v0)). constructor; auto.
 apply_optimize_range_check_preserve_backward.
 specialize (eval_name_ex_cks_added _ _ _ _ (name_exterior_checks nRT) HA0); intros HZ5.
 apply_optName_soundness; auto.
 apply_optimize_name_exist_int_value.
 match goal with
 | [H: optimize_range_check _ _ _ _ |- _] => inversion H; subst 
 end.
 (* - subcase 1: optmize the range check *)
 apply CopyIn_Mode_InOut_Range_X with (v:=v3) (l:=u) (u:=v) (f':=(STACK.push f (parameter_nameRT paramRT) (Int v3))); auto.
 apply eval_name_ex_cks_added; auto.
 rewrite name_updated_exterior_checks; smack.
 apply_eval_name_value_in_bound.
 apply_eval_expr_value_copy_out_opt_reserve_backward.
 apply_In_Bound_SubBound_Trans. constructor; auto.
 apply IHtoArgsRT with (args'' := args'); smack.
 (* - subcase 2: not optmize the range check *)
 (* conflict: do_range_check is both in and not in the final optimized name n0 *)
 specialize (optimize_name_ex_cks_eq _ _ _ _ H14). intros HZ7.
 rewrite name_updated_exterior_checks in HZ7.
 match goal with
 | [H1: optimize_range_check_on_copy_out (NameRT n ?n') _ _ (NameRT _ ?n0),
    H2: name_exterior_checks ?n' = RangeCheck :: _,
    H3: ~ List.In RangeCheck (name_exterior_checks ?n0) |- _] => 
     clear - H1 H2 H3; inversion H1; subst; simpl in *; rewrite H2 in *; smack
 end.
 rewrite name_updated_exterior_checks in H35; clear - H35; smack.
 (* case: CopyIn_Mode_InOut_Range_RTE_X *)  
 assert(HA2: evalExpRT st' s  (NameRT n0 nm0) (OK (Int v0))). constructor; auto.
 apply_optimize_range_check_preserve_backward.
 specialize (eval_name_ex_cks_added _ _ _ _ (name_exterior_checks nRT) HA0); intros HZ5.
 apply_optName_soundness; auto.
 match goal with
 | [H: optimize_range_check _ _ _ _ |- _] => inversion H; subst 
 end.
 (* - subcase 1: optmize the range check *)
 (* conflict: do_range_check is both in and not in the final optimized name n0 *)
 specialize (optimize_name_ex_cks_eq _ _ _ _ H14). intros HZ7.
 rewrite name_updated_exterior_checks in HZ7.
 match goal with
 | [H1: optimize_range_check_on_copy_out 
          (update_exterior_checks_exp (NameRT n n') _) _ _ (NameRT _ ?n0),
    H2: name_exterior_checks ?n' = RangeCheck :: _,
    H3: List.In RangeCheck (name_exterior_checks ?n0) |- _] => 
     clear - H1 H2 H3; simpl in *; rewrite H2 in H1;
     inversion H30; smack
 end;
 match goal with
 | [H: List.In _ (name_exterior_checks _) |- _] =>
     repeat progress rewrite name_updated_exterior_checks in H; simpl in H; smack
 end.
 (* - subcase 2: not optmize the range check *)
  apply CopyIn_Mode_InOut_Range_RTE_X with (v:=v0) (l:=l) (u:=u0); auto.
 apply eval_name_ex_cks_added; auto.
 rewrite name_updated_exterior_checks; smack.
 (* case: CopyIn_Mode_InOut_Range_X *)
 assert(HA2: evalExpRT st' s  (NameRT n0 nm0) (OK (Int v0))). constructor; auto.
 apply_optimize_range_check_preserve_backward.
 specialize (eval_name_ex_cks_added _ _ _ _ (name_exterior_checks nRT) HA0); intros HZ5.
 apply_optName_soundness; auto.
 match goal with
 | [H: optimize_range_check _ _ _ _ |- _] => inversion H; subst 
 end.
 (* - subcase 1: optmize the range check *)
 (* conflict: do_range_check is both in and not in the final optimized name n0 *)
 specialize (optimize_name_ex_cks_eq _ _ _ _ H14). intros HZ7.
 rewrite name_updated_exterior_checks in HZ7.
 match goal with
 | [H1: optimize_range_check_on_copy_out 
          (update_exterior_checks_exp (NameRT n n') _) _ _ (NameRT _ ?n0),
    H2: name_exterior_checks ?n' = RangeCheck :: _,
    H3: List.In RangeCheck (name_exterior_checks ?n0) |- _] => 
     clear - H1 H2 H3; simpl in *; rewrite H2 in H1;
     inversion H30; smack
 end;
 match goal with
 | [H: List.In _ (name_exterior_checks _) |- _] =>
     repeat progress rewrite name_updated_exterior_checks in H; simpl in H; smack
 end.
 (* - subcase 2: not optmize the range check *)
 apply CopyIn_Mode_InOut_Range_X with 
   (v:=v0) (l:=l) (u:=u0) (f':=(STACK.push f (parameter_nameRT paramRT) (Int v0))); auto.
 apply eval_name_ex_cks_added; auto.
 rewrite name_updated_exterior_checks; smack.
 apply IHtoArgsRT with (args'' := args'); smack.
Qed.

Ltac apply_optArgs_copyin_soundness :=
  match goal with
  | [H1: toArgsRT ?st ?params ?args ?args',
     H2: toSymTabRT ?st ?st',
     H3: toParamSpecsRT ?params ?params',
     H4: well_typed_stack_and_symboltable ?st' ?s,
     H5: well_typed_exps_x ?st' ?args',
     H6: optArgs ?st' ?params' ?args' ?args'',
     H7: copyInRT ?st' ?s ?f ?params' ?args'' ?f' |- _ ] =>
      specialize (optArgs_copyin_soundness _ _ _ _ _ _ _ _ _ _ H1 H2 H3 H4 H5 H6 H7);
      let HZ := fresh "HZ" in intro HZ
  end.


(** * Completeness of RT-OPT Specification *)

(** ** optExp_completeness *)
Lemma optExp_completeness: forall e st st' s e' e'' eBound v, 
  toExpRT st e e' ->
    toSymTabRT st st' ->
      well_typed_stack st' s ->
        well_typed_exp_x st' e' ->
          optExp st' e' (e'', eBound) ->
            evalExpRT st' s e' v ->
              evalExpRT st' s e'' v.
Proof.
  apply (expression_ind
    (fun e: exp =>
       forall (st : symTab) (st' : symTabRT) (s : STACK.state)
              (e': expRT) (e'': expRT) (eBound: bound) (v : Ret value),
      toExpRT st e e' ->
      toSymTabRT st st' ->
      well_typed_stack st' s ->
      well_typed_exp_x st' e' ->
      optExp st' e' (e'', eBound) ->
      evalExpRT st' s e' v ->
      evalExpRT st' s e'' v)
    (fun n: name =>
       forall (st : symTab) (st' : symTabRT) (s : STACK.state)
              (n': nameRT) (n'': nameRT) (nBound: bound) (v : Ret value),
      toNameRT st n n' ->
      toSymTabRT st st' ->
      well_typed_stack st' s ->
      well_typed_name_x st' n' ->
      optName st' n' (n'', nBound) ->
      evalNameRT st' s n' v ->
      evalNameRT st' s n'' v)
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
  | [H: forall (st : symTab) (st' : symTabRT) 
        (s : STACK.state) (e' e'' : expRT) (eBound : bound)
        (v : Ret value),
      toExpRT st ?e e' ->
      toSymTabRT st st' ->
      well_typed_stack st' s ->
      well_typed_exp_x st' e' ->
      optExp st' e' (e'', eBound) ->
      evalExpRT st' s e' v -> evalExpRT st' s e'' v,
     H1: toExpRT ?st ?e ?e',
     H2: toSymTabRT ?st ?st',
     H3: well_typed_stack ?st' ?s,
     H4: well_typed_exp_x ?st' ?e',
     H5: optExp ?st' ?e' _,
     H6: evalExpRT ?st' ?s ?e' ?v |- _] => specialize (H _ _ _ _ _ _ _ H1 H2 H3 H4 H5 H6)
  end;
  [apply EvalBinOpRTE1_RTE; auto | | | apply EvalBinOpRTE1_RTE; auto | | | apply EvalBinOpRTE1_RTE; auto | | |
   apply EvalBinOpRTE1_RTE; auto | | ];
  [apply EvalBinOpRTE2_RTE with (v1:=v1); auto | | 
   apply EvalBinOpRTE2_RTE with (v1:=v1); auto | |
   apply EvalBinOpRTE2_RTE with (v1:=v1); auto | |
   apply EvalBinOpRTE2_RTE with (v1:=v1); auto | ];
  apply EvalBinOpRT with (v1:=v1) (v2:=v2); auto.
  + (* Plus | Minus | Multiply *)    
    match goal with
    | [H: evalBinOpRTS _ _ _ _ _ |- _] => inversion H; smack
    end;
    match goal with
    | [H: evalBinOpRT _ _ _ _ _ |- _] => inversion H; smack
    | _ => idtac
    end;
    destruct v1, v2; inversion H8;
    specialize (eval_expr_value_in_bound _ _ _ _ _ _ _ _ H14 H2 H3 H17 H28 H11);
    apply_eval_expr_value_in_bound; intros;
    apply do_flagged_checks_on_plus_reserve with 
        (v1Bound:=e1Bound) (v2Bound:=e2Bound) (bound1:=eBound); auto.
  + (* Divide *)
    match goal with
    | [H: evalBinOpRTS _ _ _ _ _ |- _] => inversion H; smack
    end;
    match goal with
    | [H: evalBinOpRT _ _ _ _ _ |- _] => inversion H; smack
    | _ => idtac
    end;
    specialize (eval_expr_value_in_bound _ _ _ _ _ _ _ _ H14 H2 H3 H16 H27 H11);
    apply_eval_expr_value_in_bound; intros;
    apply_do_flagged_checks_on_divide_reserve; auto. 
  + (* Modulus *)
    match goal with
    | [H: evalBinOpRTS _ _ _ _ _ |- _] => inversion H; smack
    end;
    match goal with
    | [H: evalBinOpRT _ _ _ _ _ |- _] => inversion H; smack
    | _ => idtac
    end;
    specialize (eval_expr_value_in_bound _ _ _ _ _ _ _ _ H14 H2 H3 H16 H27 H11);
    apply_eval_expr_value_in_bound; intros;
    apply_do_flagged_checks_on_modulus_reserve; auto. 
  + (* Logic Operator *)
  inversion H31; smack.
- (** E_Unary_Operation_X *)
  inversion H0; subst;
  inversion H3; subst;
  inversion H4; subst;
  inversion H5; subst;
  match goal with
  | [H: forall (st : symTab) (st' : symTabRT) 
        (s : STACK.state) (e' e'' : expRT) (eBound : bound)
        (v : Ret value),
      toExpRT st ?e e' ->
      toSymTabRT st st' ->
      well_typed_stack st' s ->
      well_typed_exp_x st' e' ->
      optExp st' e' (e'', eBound) ->
      evalExpRT st' s e' v -> evalExpRT st' s e'' v,
     H1: toExpRT ?st ?e ?e',
     H2: toSymTabRT ?st ?st',
     H3: well_typed_stack ?st' ?s,
     H4: well_typed_exp_x ?st' ?e',
     H5: optExp ?st' ?e' _,
     H6: evalExpRT ?st' ?s ?e' ?v |- _] => specialize (H _ _ _ _ _ _ _ H1 H2 H3 H4 H5 H6)
  end;
  [ apply EvalUnOpRT_RTE; auto | |
    apply EvalUnOpRT_RTE; auto | ];
  apply EvalUnOpRT with (v:=v0); auto.
  + match goal with
    | [H: evalUnOpRTS _ _ _ _ |- _] => inversion H; smack
    end;
    match goal with
    | [H: evalUnOpRT _ _ _ _ |- _] => inversion H; smack
    | _ => idtac
    end;
    destruct v0; inversion H6;
    apply_eval_expr_value_in_bound; intros;
    apply_evalUnOpRTS_reserve; auto.
  + inversion H21; smack.  
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
  | [H: forall (st : symTab) (st' : symTabRT) 
        (s : STACK.state) (n' n'' : nameRT) (nBound : bound)
        (v : Ret value),
      toNameRT st ?n n' ->
      toSymTabRT st st' ->
      well_typed_stack st' s ->
      well_typed_name_x st' n' ->
      optName st' n' (n'', nBound) ->
      evalNameRT st' s n' v -> evalNameRT st' s n'' v,
    H1: toNameRT ?st ?n ?n',
    H2: toSymTabRT ?st ?st',
    H3: well_typed_stack ?st' ?s,
    H4: well_typed_name_x ?st' ?n',
    H5: optName ?st' ?n' _,
    H6: evalNameRT ?st' ?s ?n' ?v |- _] => 
      specialize (H _ _ _ _ _ _ _ H1 H2 H3 H4 H5 H6)
  end;
  match goal with
  | [H: forall (st : symTab) (st' : symTabRT) 
        (s : STACK.state) (e' e'' : expRT) (eBound : bound)
        (v : Ret value),
      toExpRT st ?e e' ->
      toSymTabRT st st' ->
      well_typed_stack st' s ->
      well_typed_exp_x st' e' ->
      optExp st' e' (e'', eBound) ->
      evalExpRT st' s e' v -> evalExpRT st' s e'' v,
     H1: toExpRT ?st ?e ?e',
     H2: toSymTabRT ?st ?st',
     H3: well_typed_stack ?st' ?s,
     H4: well_typed_exp_x ?st' ?e',
     H5: optExp ?st' ?e' _,
     H6: evalExpRT ?st' ?s ?e' ?v |- _] => specialize (H _ _ _ _ _ _ _ H1 H2 H3 H4 H5 H6)
  | _ => idtac
  end.
  + apply EvalIndexedComponentRTX_RTE; auto.
  + apply EvalIndexedComponentRTE_RTE with (a:=a0); auto.
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
    apply EvalIndexedComponentRT_Range_RTE with (a:=a0) (i:=i) (t:=t0) (l:=l) (u:=u0); auto.
    apply eval_expr_value_reserve with (e := e') (eBound := Interval u v0) (rBound := Interval u' v'); auto.
    specialize (eval_exp_ex_cks_stripped _ _ _ _ _ H0); auto.
    specialize (optimize_name_ast_num_eq _ _ _ _ H21); smack.
    rewrite H29 in H23; inversion H23; subst; assumption.
    rewrite H29 in H23; inversion H23; subst.
    apply_extract_array_index_range_rt_unique; subst.
    apply_eval_expr_value_in_bound.
    clear - H12 H22 H25 H29 H30 H31 HZ3.
    
    apply_optimize_exp_ex_cks_eq.
    rewrite exp_updated_exterior_checks in *.
    inversion H31; subst. inversion H; subst.
    apply_optimize_range_check_reserve; smack.
  + apply_well_typed_exp_preserve.
    specialize (optimize_exp_ex_cks_stripped _ _ _ _ _ H22); intro HZ1.
    specialize (eval_exp_ex_cks_stripped _ _ _ _ _ H19); intros HZ2.
    specialize (H0 _ _ _ _ _ _ _ H12 H2 H3 HZ HZ1 HZ2).
    apply EvalIndexedComponentRT with (a:=a0) (i:=i) (t:=t0) (l:=l) (u:=u0); auto.
    apply eval_expr_value_reserve with (e := e') (eBound := Interval u v0) (rBound := Interval u' v'); auto.
    specialize (eval_exp_ex_cks_stripped _ _ _ _ _ H0); auto.
    specialize (optimize_name_ast_num_eq _ _ _ _ H21); smack.
    rewrite H28 in H23; inversion H23; subst; assumption.
    rewrite H28 in H23; inversion H23; subst.
    apply_extract_array_index_range_rt_unique; subst.
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
  | [H: forall (st : symTab) (st' : symTabRT) 
        (s : STACK.state) (n' n'' : nameRT) (nBound : bound)
        (v : Ret value),
      toNameRT st ?n n' ->
      toSymTabRT st st' ->
      well_typed_stack st' s ->
      well_typed_name_x st' n' ->
      optName st' n' (n'', nBound) ->
      evalNameRT st' s n' v -> evalNameRT st' s n'' v,
    H1: toNameRT ?st ?n ?n',
    H2: toSymTabRT ?st ?st',
    H3: well_typed_stack ?st' ?s,
    H4: well_typed_name_x ?st' ?n',
    H5: optName ?st' ?n' _,
    H6: evalNameRT ?st' ?s ?n' ?v |- _] => 
      specialize (H _ _ _ _ _ _ _ H1 H2 H3 H4 H5 H6)
  end.
  + apply EvalSelectedComponentRTX_RTE; auto.
  + apply EvalSelectedComponentRT with (r:=r); auto.    
Qed.

Ltac apply_optExp_completeness :=
  match goal with
  | [H1: toExpRT ?st ?e ?e',
     H2: toSymTabRT ?st ?st',
     H3: well_typed_stack ?st' ?s,
     H4: well_typed_exp_x ?st' ?e',
     H5: optExp ?st' ?e' _,
     H6: evalExpRT ?st' ?s ?e' ?v |- _] => 
      specialize (optExp_completeness _ _ _ _ _ _ _ _ H1 H2 H3 H4 H5 H6);
      let HZ := fresh "HZ" in
      intro HZ
  | [H1: well_typed_stack_and_symboltable ?st' ?s |- _] => 
      inversion H1; subst; apply_well_typed_stack_infer;
      match goal with
     | [H1: toExpRT ?st ?e ?e',
        H2: toSymTabRT ?st ?st',
        H3: well_typed_stack ?st' ?s,
        H4: well_typed_exp_x ?st' ?e',
        H5: optExp ?st' ?e' _,
        H6: evalExpRT ?st' ?s ?e' ?v |- _] => 
          specialize (optExp_completeness _ _ _ _ _ _ _ _ H1 H2 H3 H4 H5 H6);
          let HZ := fresh "HZ" in
          intro HZ
      end
  end.

(** ** optName_completeness *)
Lemma optName_completeness: forall n st st' s n' n'' nBound v, 
  toNameRT st n n' ->
    toSymTabRT st st' ->
      well_typed_stack st' s ->
        well_typed_name_x st' n' ->
          optName st' n' (n'', nBound) ->
            evalNameRT st' s n' v ->
              evalNameRT st' s n'' v.
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
  | [H: forall (st : symTab) (st' : symTabRT) 
        (s : STACK.state) (n' n'' : nameRT) (nBound : bound)
        (v : Ret value),
      toNameRT st ?n n' ->
      toSymTabRT st st' ->
      well_typed_stack st' s ->
      well_typed_name_x st' n' ->
      optName st' n' (n'', nBound) ->
      evalNameRT st' s n' v -> evalNameRT st' s n'' v,
    H1: toNameRT ?st ?n ?n',
    H2: toSymTabRT ?st ?st',
    H3: well_typed_stack ?st' ?s,
    H4: well_typed_name_x ?st' ?n',
    H5: optName ?st' ?n' _,
    H6: evalNameRT ?st' ?s ?n' ?v |- _] => 
      specialize (H _ _ _ _ _ _ _ H1 H2 H3 H4 H5 H6)
  end.
  + apply EvalIndexedComponentRTX_RTE; auto.
  + apply EvalIndexedComponentRTE_RTE with (a:=a0); auto.
    apply eval_expr_value_reserve with (e := e') (eBound := Interval u v0) (rBound := Interval u' v'); auto.
    apply_well_typed_exp_preserve.
    specialize (optimize_exp_ex_cks_stripped _ _ _ _ _ H20); intro HZ1.
    specialize (eval_exp_ex_cks_stripped _ _ _ _ _ H26); intros HZ2.
    apply_optExp_completeness.
    specialize (eval_exp_ex_cks_stripped _ _ _ _ _ HZ0); auto.
  + apply_well_typed_exp_preserve.
    specialize (optimize_exp_ex_cks_stripped _ _ _ _ _ H20); intro HZ1.
    specialize (eval_exp_ex_cks_stripped _ _ _ _ _ H25); intros HZ2.
    apply EvalIndexedComponentRT_Range_RTE with (a:=a0) (i:=i) (t:=t0) (l:=l) (u:=u0); auto.
    apply eval_expr_value_reserve with (e := e') (eBound := Interval u v0) (rBound := Interval u' v'); auto.
    apply_optExp_completeness.
    specialize (eval_exp_ex_cks_stripped _ _ _ _ _ HZ0); auto.
    
    specialize (optimize_name_ast_num_eq _ _ _ _ H19); smack.
    rewrite H27 in H21; inversion H21; subst; assumption.
    rewrite H27 in H21; inversion H21; subst.
    apply_extract_array_index_range_rt_unique; subst.
    apply_eval_expr_value_in_bound.
    clear - H10 H20 H23 H27 H28 H29 HZ3.
    
    apply_optimize_exp_ex_cks_eq.
    rewrite exp_updated_exterior_checks in *.
    inversion H29; subst. inversion H; subst.
    apply_optimize_range_check_reserve; smack.
  + apply_well_typed_exp_preserve.
    specialize (optimize_exp_ex_cks_stripped _ _ _ _ _ H20); intro HZ1.
    specialize (eval_exp_ex_cks_stripped _ _ _ _ _ H17); intros HZ2.
    apply EvalIndexedComponentRT with (a:=a0) (i:=i) (t:=t0) (l:=l) (u:=u0); auto.
    apply eval_expr_value_reserve with (e := e') (eBound := Interval u v0) (rBound := Interval u' v'); auto.
    apply_optExp_completeness.
    specialize (eval_exp_ex_cks_stripped _ _ _ _ _ HZ0); auto.

    specialize (optimize_name_ast_num_eq _ _ _ _ H19); smack.
    rewrite H26 in H21; inversion H21; subst; assumption.
    rewrite H26 in H21; inversion H21; subst.
    apply_extract_array_index_range_rt_unique; subst.
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
  | [H: forall (st : symTab) (st' : symTabRT) 
        (s : STACK.state) (n' n'' : nameRT) (nBound : bound)
        (v : Ret value),
      toNameRT st ?n n' ->
      toSymTabRT st st' ->
      well_typed_stack st' s ->
      well_typed_name_x st' n' ->
      optName st' n' (n'', nBound) ->
      evalNameRT st' s n' v -> evalNameRT st' s n'' v,
    H1: toNameRT ?st ?n ?n',
    H2: toSymTabRT ?st ?st',
    H3: well_typed_stack ?st' ?s,
    H4: well_typed_name_x ?st' ?n',
    H5: optName ?st' ?n' _,
    H6: evalNameRT ?st' ?s ?n' ?v |- _] => 
      specialize (H _ _ _ _ _ _ _ H1 H2 H3 H4 H5 H6)
  end.
  + apply EvalSelectedComponentRTX_RTE; auto.
  + apply EvalSelectedComponentRT with (r:=r); auto.    
Qed.

Ltac apply_optName_completeness := 
  match goal with
  | [H1: toNameRT ?st ?n ?n',
     H2: toSymTabRT ?st ?st',
     H3: well_typed_stack ?st' ?s,
     H4: well_typed_name_x ?st' ?n',
     H5: optName ?st' ?n' _,
     H6: evalNameRT ?st' ?s ?n' ?v |- _] =>
      specialize (optName_completeness _ _ _ _ _ _ _ _ H1 H2 H3 H4 H5 H6);
      let HZ := fresh "HZ" in
      intro HZ
  | [H1: well_typed_stack_and_symboltable ?st' ?s |- _] => 
      inversion H1; subst; apply_well_typed_stack_infer;
      match goal with
     | [H1: toNameRT ?st ?n ?n',
        H2: toSymTabRT ?st ?st',
        H3: well_typed_stack ?st' ?s,
        H4: well_typed_name_x ?st' ?n',
        H5: optName ?st' ?n' _,
        H6: evalNameRT ?st' ?s ?n' ?v |- _] =>
          specialize (optName_completeness _ _ _ _ _ _ _ _ H1 H2 H3 H4 H5 H6);
          let HZ := fresh "HZ" in
          intro HZ
      end    
  end.


(** ** storeUpdateRT_opt_completeness *)

Lemma storeUpdateRT_opt_completeness: forall n st st' s s' n' n'' nBound v, 
  toNameRT st n n' ->
    toSymTabRT st st' ->
      well_typed_stack st' s ->
        well_typed_name_x st' n' ->
          optName st' n' (n'', nBound) ->
            storeUpdateRT st' s n' v s' ->
              storeUpdateRT st' s n'' v s'.
Proof.
  induction n; intros.
- inversion H; subst;
  inversion H3; smack.
- inversion H; subst;
  inversion H2; subst;
  inversion H3; subst;
  inversion H4; subst.
  + apply SU_Indexed_Component_xRTE_X; auto.
    apply_optName_completeness; auto.
  + apply SU_Indexed_Component_eRTE_X with (a:=a0); auto.
    destruct H26; apply_optName_completeness; auto.
    apply eval_expr_value_reserve with (e := e') (eBound := Interval u v0) (rBound := Interval u' v'); auto.
    apply_well_typed_exp_preserve.
    specialize (optimize_exp_ex_cks_stripped _ _ _ _ _ H20); intro HZ1.
    specialize (eval_exp_ex_cks_stripped _ _ _ _ _ H27); intros HZ2.
    apply_optExp_completeness.
    specialize (eval_exp_ex_cks_stripped _ _ _ _ _ HZ0); auto.
  + apply_well_typed_exp_preserve.
    specialize (optimize_exp_ex_cks_stripped _ _ _ _ _ H20); intro HZ1.
    specialize (eval_exp_ex_cks_stripped _ _ _ _ _ H25); intros HZ2.
    apply SU_Indexed_Component_Range_RTE_X with (a:=a0) (i:=i) (t:=t1) (l:=l) (u:=u0); auto.
    destruct H12; apply_optName_completeness; auto.
    apply eval_expr_value_reserve with (e := e') (eBound := Interval u v0) (rBound := Interval u' v'); auto.
    apply_optExp_completeness.
    specialize (eval_exp_ex_cks_stripped _ _ _ _ _ HZ0); auto.
    
    specialize (optimize_name_ast_num_eq _ _ _ _ H19); smack.
    rewrite H28 in H21; inversion H21; subst.
    apply_extract_array_index_range_rt_unique; subst.
    apply_eval_expr_value_in_bound.
    clear - H10 H20 H23 H28 H29 H30 HZ3.
    
    apply_optimize_exp_ex_cks_eq.
    rewrite exp_updated_exterior_checks in *.
    inversion H30; subst. inversion H; subst.
    apply_optimize_range_check_reserve; smack.    
  + apply_well_typed_exp_preserve.
    specialize (optimize_exp_ex_cks_stripped _ _ _ _ _ H20); intro HZ1.
    specialize (eval_exp_ex_cks_stripped _ _ _ _ _ H18); intros HZ2.
    apply_optName_completeness; auto.
    apply_optExp_completeness.
    specialize (eval_exp_ex_cks_stripped _ _ _ _ _ HZ3); intro HZ4.
    specialize (optimize_name_ast_num_eq _ _ _ _ H19); intro HZ5.
    rewrite H25 in H21; inversion H21; subst.
    apply_extract_array_index_range_rt_unique; subst.
    specialize (optimize_exp_ex_cks_eq _ _ _ _ H20); intros HZ7.
    rewrite exp_updated_exterior_checks in *.
    rewrite <- HZ7 in *.

    destruct H17; subst.
 
    apply SU_Indexed_Component_X with 
      (arrObj:=(ArrayV a0)) (a:=a0) (i:=i) (l:=l) (u:=u0) (t:=t0) (a1:=(updateIndexedComp a0 i v)); smack.
    apply eval_expr_value_reserve with (e := e') (eBound := Interval u v0) (rBound := Interval l u0); auto.
    apply_do_range_check_same_result; auto.

    apply SU_Indexed_Component_X with 
      (arrObj:=Undefined) (i:=i) (a:=nil) (l:=l) (u:=u0) (t:=t0) (a1:=((i, v) :: nil)); smack.
    apply eval_expr_value_reserve with (e := e') (eBound := Interval u v0) (rBound := Interval l u0); auto.
    apply_do_range_check_same_result; auto.
- inversion H; subst;
  inversion H2; subst;
  inversion H3; subst;
  inversion H4; subst.
  + apply_optName_completeness;
    apply SU_Selected_Component_xRTE_X; smack.
  + destruct H23;
    [ apply SU_Selected_Component_X with 
        (recObj:=(RecordV r)) (r:=r) (r1:=(updateSelectedComp r i v)); smack |
      apply SU_Selected_Component_X with 
        (recObj:=Undefined) (r:=nil) (r1:=((i, v) :: nil)); smack
    ];
    apply_optName_completeness; auto.
Qed.
 
Ltac apply_storeUpdateRT_opt_completeness := 
  match goal with
  | [H1: toNameRT ?st ?n ?n' ,
     H2: toSymTabRT ?st ?st' ,
     H3: well_typed_stack ?st' ?s ,
     H4: well_typed_name_x ?st' ?n' ,
     H5: optName ?st' ?n' _ ,
     H6: storeUpdateRT ?st' ?s ?n' ?v ?s' |- _] =>
      specialize (storeUpdateRT_opt_completeness _ _ _ _ _ _ _ _ _ H1 H2 H3 H4 H5 H6);
      let HZ := fresh "HZ" in
      intro HZ
  | [H1: well_typed_stack_and_symboltable ?st' ?s |- _] => 
      inversion H1; subst; apply_well_typed_stack_infer;
      match goal with
      | [H1: toNameRT ?st ?n ?n' ,
         H2: toSymTabRT ?st ?st' ,
         H3: well_typed_stack ?st' ?s ,
         H4: well_typed_name_x ?st' ?n' ,
         H5: optName ?st' ?n' _ ,
         H6: storeUpdateRT ?st' ?s ?n' ?v ?s' |- _] =>
           specialize (storeUpdateRT_opt_completeness _ _ _ _ _ _ _ _ _ H1 H2 H3 H4 H5 H6);
           let HZ := fresh "HZ" in
           intro HZ
       end
  end.

(** ** optArgs_copyin_completeness *)
Lemma optArgs_copyin_completeness: forall params' st st' s f f' params args args' args'',
  toArgsRT st params args args' ->
  toSymTabRT st st' ->
  toParamSpecsRT params params' ->
  well_typed_stack st' s ->
  well_typed_exps_x st' args' ->
  optArgs st' params' args' args'' ->
  copyInRT st' s f params' args' f' ->
  copyInRT st' s f params' args'' f'.
Proof.
 induction params'; intros.
-inversion H4; subst.
 inversion H5; subst; auto.
- destruct args', args'', params, args;
  match goal with 
  | [H: copyInRT _ _ _ (?a :: ?al) nil _ |- _] => inversion H
  | [H: optArgs _ (?a :: ?al) (?e :: ?el) nil |- _] => inversion H
  | [H: toParamSpecsRT nil (?param :: ?params) |- _] => inversion H
  | [H: toArgsRT _ (?param :: ?params) nil _ |- _] => inversion H
  | _ => idtac
  end.
  inversion H1; subst;
  inversion H3; subst.
  assert(HZ: p.(parameter_mode) = a.(parameter_mode_rt)).
  clear - H9. inversion H9; smack.
  assert(HZ1: (parameter_subtype_mark p) = (parameter_subtype_mark_rt a)).
  clear - H9. inversion H9; smack.
  (*******)
  inversion H; subst;
  inversion H4; subst;
  match goal with
  | [H1: parameter_mode ?p = parameter_mode_rt ?a,
     H2: parameter_mode ?p = _ ,
     H3: parameter_mode_rt ?a = _ |- _] => 
      rewrite H2 in H1; rewrite H3 in H1; inversion H1
  | [H1: parameter_mode_rt ?a = _ ,
     H2: parameter_mode_rt ?a = _ |- _] => rewrite H2 in H1; inversion H1
  end;
  match goal with
  | [H: extract_subtype_range_rt _ _ (RangeRT _ _) |- _] => 
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
  | [H1: parameter_mode_rt ?a = _ ,
     H2: parameter_mode_rt ?a = _ |- _] => rewrite H2 in H1; inversion H1
  end;
  match goal with
  | [H: extract_subtype_range_rt _ _ (RangeRT _ _) |- _] => 
      specialize (range_constrainted_type_true _ _ _ _ H);
      let HZ := fresh "HZ" in intros HZ
  | _ => idtac
  end;

  match goal with
  | [H1: toSymTabRT ?st ?st',
     H2: fetch_exp_type _ ?st = _ |- _ ] => 
      specialize (symbol_table_exp_type_rel _ _ _ _ H1 H2);
      let HZ := fresh "HZ" in intros HZ
  | _ => idtac
  end;
  match goal with
  | [H1: fetch_exp_type_rt ?x ?st = _, 
     H2: fetch_exp_type_rt ?x ?st = _ |- _] => rewrite H1 in H2; inversion H2; subst
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
     H3: ?x = false \/ ?y = false |- _] => rewrite H1 in H3; rewrite H2 in H3; clear - H3; smack
  | [H: ~ List.In ?x (name_exterior_checks (update_exterior_checks_name _ (?x :: _))) |- _] =>
      rewrite name_updated_exterior_checks in H; clear - H; smack
  | [H: ~ List.In ?x (name_exterior_checks (update_exterior_checks_name _ (_ :: ?x :: _))) |- _] =>
      rewrite name_updated_exterior_checks in H; clear - H; smack
  | _ => idtac
  end;
  (*-------------*)
  match goal with
  | [H: optName _ _ _ |- _] => 
      specialize (optimize_name_ex_cks_eq _ _ _ _ H);
      let HZ := fresh "HZ" in intro HZ
  | _ => idtac
  end;
  match goal with
  | [H: optExp _ _ _ |- _] => 
      specialize (optimize_exp_ex_cks_stripped _ _ _ _ _ H);
      let HZ := fresh "HZ" in intro HZ
  | _ => idtac
  end;
  match goal with
  | [H: evalNameRT _ _ (update_exterior_checks_name _ _) _ |- _] => 
      specialize (eval_name_ex_cks_stripped _ _ _ _ _ H);
      let HZ := fresh "HZ" in intro HZ
  | _ => idtac
  end;
  match goal with
  | [H: evalExpRT _ _ (update_exterior_checks_exp _ _) _ |- _] => 
      specialize (eval_exp_ex_cks_stripped _ _ _ _ _ H);
      let HZ := fresh "HZ" in intro HZ
  | _ => idtac
  end;
  match goal with
  | [H: well_typed_exp_x _ (NameRT _ _) |- _] => inversion H; subst
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
  | [H: storeUpdateRT _ _ (update_exterior_checks_name _ _) _ _ |- _] =>
      specialize (store_update_ex_cks_stripped _ _ _ _ _ _ H);
      let HZ := fresh "HZ" in intro HZ
  | _ => idtac
  end;
  match goal with
  | [H: optName _ (update_exterior_checks_name _ _) _ |- _] =>
      specialize (optimize_name_ex_cks_stripped _ _ _ _ _ H); 
      let HZ := fresh "HZ" in intros HZ
  | _ => idtac
  end;
  match goal with
  | [H: optExp _ (update_exterior_checks_exp _ _) _ |- _] =>
      specialize (optimize_exp_ex_cks_stripped _ _ _ _ _ H); 
      let HZ := fresh "HZ" in intros HZ
  | _ => idtac
  end;
  (*---------------*)
  match goal with
  | [H1: forall (st : symTab) (st' : symTabRT)
                (s : STACK.state) (f : STACK.frame) 
                (f' : Ret STACK.frame)
                (params : list paramSpec)
                (args : list exp) (args' args'' : list expRT),
              toArgsRT st params args args' ->
              toSymTabRT st st' ->
              toParamSpecsRT params ?params' ->
              well_typed_stack st' s ->
              well_typed_exps_x st' args' ->
              optArgs st' ?params' args' args'' ->
              copyInRT st' s f ?params' args' f' ->
              copyInRT st' s f ?params' args'' f',
     H2: toArgsRT ?st ?params ?args ?args', 
     H3: toSymTabRT ?st ?st',
     H4: toParamSpecsRT ?params ?params',
     H5: well_typed_stack ?st' ?s,
     H6: well_typed_exps_x ?st' ?args',
     H7: optArgs ?st' ?params' ?args' ?args'',
     H8: copyInRT ?st' ?s ?f ?params' ?args' ?f' |- _ ] =>
      specialize (H1 _ _ _ _ _ _ _ _ _ H2 H3 H4 H5 H6 H7 H8)
  | _ => idtac
  end.
  + apply CopyIn_Mode_In_eRTE_X; auto.
    apply_optExp_completeness; auto.
  + apply CopyIn_Mode_In_NoRangeCheck_X with (v := v) (f' := (STACK.push f (parameter_nameRT a) v)); auto.
    apply_optExp_completeness; auto.
    apply_optimize_exp_ex_cks_eq; smack.
  + apply CopyIn_Mode_In_eRTE_X; auto.
    apply_optExp_completeness; auto.
    apply eval_exp_ex_cks_stripped with (cks := (exp_exterior_checks argRT)); auto.
  + rewrite exp_updated_exterior_checks in H28. inversion H28.
  + apply CopyIn_Mode_In_eRTE_X; auto.
    apply eval_expr_value_reserve with (e:=arg') (eBound:=(Interval u' v')) (rBound:=(Interval u v)); auto.
    apply_optExp_completeness; auto.
    apply eval_exp_ex_cks_stripped with (cks := (exp_exterior_checks argRT)); auto.
  + rewrite exp_updated_exterior_checks in H29. inversion H29.
  + apply CopyIn_Mode_In_Range_RTE_X with (v:=v0) (l:=l) (u:=u0); auto.
    apply eval_expr_value_reserve with (e:=arg') (eBound:=(Interval u' v')) (rBound:=(Interval u v)); auto.

    apply_optExp_completeness; auto.
    apply eval_exp_ex_cks_stripped with (cks := (exp_exterior_checks argRT)); auto.
    
    apply_extract_subtype_range_unique; subst. 
    specialize (optimize_exp_ex_cks_eq _ _ _ _ H23); intros HZ7.
    rewrite exp_updated_exterior_checks in HZ7.
    apply_eval_expr_value_in_bound. 
    inversion H31; subst.
    apply_optimize_range_check_reserve. smack. 

  + inversion H24; subst. (*H24: optimize_range_check arg' (Interval u' v') (Interval u v) e0*)
  * specialize (optimize_exp_ex_cks_eq _ _ _ _ H23); intros HZ7.
    rewrite exp_updated_exterior_checks in HZ7. rewrite HZ7; smack.
    apply CopyIn_Mode_In_NoRangeCheck_X with (v := Int v0) (f' := (STACK.push f (parameter_nameRT a) (Int v0))); auto.
    apply_optExp_completeness.
    specialize (exp_exterior_checks_beq_nil _ _ _ H19); intros HZ9. rewrite HZ9 in HZ8; assumption.
    smack.
    rewrite exp_updated_exterior_checks; auto.
  * apply CopyIn_Mode_In_Range_X with (v := v0) (l := l) (u := u0) 
                                       (f' := (STACK.push f (parameter_nameRT a) (Int v0))); auto.
    apply_optExp_completeness.
    specialize (eval_exp_ex_cks_stripped _ _ _ _ _ HZ7); auto.
    specialize (optimize_exp_ex_cks_eq _ _ _ _ H23); intros HZ7.
    rewrite exp_updated_exterior_checks in HZ7; auto.
  + apply CopyIn_Mode_Out_X with (f' := (STACK.push f (parameter_nameRT a) Undefined)); auto.
  + assert (HZ7: exists n1, e0 = NameRT n n1).
      clear - H28. inversion H28; subst.
      exists (update_exterior_checks_name n' (remove_check_flag RangeCheckOnReturn (exp_exterior_checks (NameRT n n')))).
      simpl; auto. exists n'; auto.
    inversion HZ7; subst.
    apply CopyIn_Mode_Out_X with (f' := (STACK.push f (parameter_nameRT a) Undefined)); auto.
  + apply CopyIn_Mode_InOut_eRTE_X; auto.
    apply_optName_completeness; auto.
  + apply CopyIn_Mode_InOut_NoRange_X with (v := v) (f' := (STACK.push f (parameter_nameRT a) v)); auto.
    apply_optName_completeness; auto.
    rewrite HZ2; assumption.
  + apply CopyIn_Mode_InOut_eRTE_X; auto.
    apply_optName_completeness.
    apply eval_name_ex_cks_stripped with (cks := (name_exterior_checks nRT)); auto.      
  + apply CopyIn_Mode_InOut_Range_RTE_X with (v:=v) (l:=l) (u:=u); auto.
    apply_optName_completeness.
    apply eval_name_ex_cks_stripped with (cks := (name_exterior_checks nRT)); auto. 
    rewrite name_updated_exterior_checks in HZ3.
    clear - HZ3. smack.
  + apply CopyIn_Mode_InOut_Range_X with (v:=v) (l:=l) (u:=u) (f':=(STACK.push f (parameter_nameRT a) (Int v))); auto.
    apply_optName_completeness.
    apply eval_name_ex_cks_stripped with (cks := (name_exterior_checks nRT)); auto. 
    rewrite name_updated_exterior_checks in HZ3.
    clear - HZ3. smack.
  + apply CopyIn_Mode_InOut_eRTE_X; auto.
    apply_optName_completeness.
    apply eval_name_ex_cks_stripped with (cks := (name_exterior_checks nRT)); auto.
  + apply CopyIn_Mode_InOut_NoRange_X with (v := v) (f' := (STACK.push f (parameter_nameRT a) v)); auto.
    apply_optName_completeness.
    apply eval_name_ex_cks_stripped with (cks := (name_exterior_checks nRT)); auto. 
    rewrite name_updated_exterior_checks in HZ2.
    clear - HZ2. rewrite HZ2; smack.
  (*******)
  (* the following two are the cases where do optimization on range check and range check on copy out,
     and prove that the evaluation results are the same after these optimization. 
     n' has checks: (RangeCheckOnReturn :: nil)
  *)
  + clear H H3 H4.
    inversion H28; subst. (* optExp st' (NameRT _ _ _) (NameRT _ _ n', _)*)
    match goal with
    | [H: optName _ (update_exterior_checks_name _ _) _ |- _] =>
        specialize (optimize_name_ex_cks_stripped _ _ _ _ _ H); 
        let HZ := fresh "HZ" in intros HZ
    end.
    apply_optName_completeness.
    match goal with
    | [H: evalNameRT _ _ (update_exterior_checks_name _ _) _ |- _] => 
        specialize (eval_name_ex_cks_stripped _ _ _ _ _ H);
        let HZ := fresh "HZ" in intro HZ
    end.
    
    apply_optimize_range_check_preserve.
    apply CopyIn_Mode_InOut_eRTE_X; auto.
    inversion HA0; auto.
  + clear H H3 H4 H5 H10.
    inversion H28; subst.
    match goal with
    | [H: optName _ (update_exterior_checks_name _ _) _ |- _] =>
        specialize (optimize_name_ex_cks_stripped _ _ _ _ _ H); 
        let HZ := fresh "HZ" in intros HZ
    end.
    apply_optName_completeness.
    match goal with
    | [H: evalNameRT _ _ (update_exterior_checks_name _ _) _ |- _] => 
        specialize (eval_name_ex_cks_stripped _ _ _ _ _ H);
        let HZ := fresh "HZ" in intro HZ
    end.
    apply_optimize_range_check_preserve.
    apply CopyIn_Mode_InOut_NoRange_X with (v:=v0) (f':=(STACK.push f (parameter_nameRT a) v0)); auto.
    inversion HA0; auto.
    specialize (optimize_exp_ex_cks_eq _ _ _ _ H28); intros HZ9. 
    simpl in HZ9. rewrite name_updated_exterior_checks in HZ9.
    clear - H29 H30 HZ9.
      inversion H29; subst; inversion H30; subst; simpl in *; rewrite HZ9 in *;
      match goal with
      | [H: NameRT _ _ = NameRT _ _ |- _] => clear - H; inversion H; subst
      | _ => idtac
      end;
      repeat progress rewrite name_updated_exterior_checks; smack.
  + apply CopyIn_Mode_InOut_eRTE_X; auto.
    apply_optName_completeness.
    apply eval_name_ex_cks_stripped with (cks := (name_exterior_checks nRT)); auto.    
  (*******)
  (* the following four are the cases where do optimization on range check and range check on copy out,
     and prove that the evaluation results are the same after these optimization. 
     n' has checks: (Do_Range_Check :: RangeCheckOnReturn :: nil)
  *)
  + clear H H3 H4.
    inversion H28; subst. (* optExp st' (NameRT _ _ _) (NameRT _ _ n', _)*)
    match goal with
    | [H: optName _ (update_exterior_checks_name _ _) _ |- _] =>
        specialize (optimize_name_ex_cks_stripped _ _ _ _ _ H); 
        let HZ := fresh "HZ" in intros HZ
    end.
    apply_optName_completeness.
    match goal with
    | [H: evalNameRT _ _ (update_exterior_checks_name _ _) _ |- _] => 
        specialize (eval_name_ex_cks_stripped _ _ _ _ _ H);
        let HZ := fresh "HZ" in intro HZ
    end.
    apply_optimize_range_check_preserve.    
    apply CopyIn_Mode_InOut_eRTE_X; auto.
    inversion HA0; auto.
  + clear H H3 H4.
    apply_extract_subtype_range_unique.
    inversion H28; subst. (* optExp st' (NameRT _ _ _) (NameRT _ _ n', _)*)
    match goal with
    | [H: optName _ (update_exterior_checks_name _ _) _ |- _] =>
        specialize (optimize_name_ex_cks_stripped _ _ _ _ _ H); 
        let HZ := fresh "HZ" in intros HZ
    end.
    apply_optName_completeness.
    match goal with
    | [H: evalNameRT _ _ (update_exterior_checks_name _ _) _ |- _] => 
        specialize (eval_name_ex_cks_stripped _ _ _ _ _ H);
        let HZ := fresh "HZ" in intro HZ
    end.
    apply_optimize_range_check_preserve. 
    apply CopyIn_Mode_InOut_Range_RTE_X with (v:=v0) (l:=l) (u:=u0); auto.
    inversion HA0; auto.
    specialize (optimize_exp_ex_cks_eq _ _ _ _ H28); intros HZ9. 
    simpl in HZ9. rewrite name_updated_exterior_checks in HZ9.
    apply_eval_name_value_in_bound. 
    inversion H37; subst.
    apply_optimize_range_check_reserve.
    clear - H30 HZ11 HZ9.
    inversion H30; smack.
    rewrite name_updated_exterior_checks; smack.
  + clear H H3 H4.
    apply_extract_subtype_range_unique.
    inversion H28; subst.
    match goal with
    | [H: optName _ (update_exterior_checks_name _ _) _ |- _] =>
        specialize (optimize_name_ex_cks_stripped _ _ _ _ _ H); 
        let HZ := fresh "HZ" in intros HZ
    end.
    apply_optName_completeness.
    match goal with
    | [H: evalNameRT _ _ (update_exterior_checks_name _ _) _ |- _] => 
        specialize (eval_name_ex_cks_stripped _ _ _ _ _ H);
        let HZ := fresh "HZ" in intro HZ
    end.
    apply_optimize_range_check_preserve.
    specialize (optimize_exp_ex_cks_eq _ _ _ _ H28); intros HZ9.
    simpl in HZ9. rewrite name_updated_exterior_checks in HZ9.
    inversion H29; subst.
    * apply CopyIn_Mode_InOut_NoRange_X with (v:=Int v0) (f':=(STACK.push f (parameter_nameRT a) (Int v0))); auto.
      inversion HA0; auto.
      smack.
      inversion H30; subst; simpl in *; rewrite HZ9 in *;
      match goal with
      | [H: NameRT _ _ = NameRT _ _ |- _] => clear - H; inversion H; subst
      | _ => idtac
      end;
      repeat progress rewrite name_updated_exterior_checks; smack.
    * apply CopyIn_Mode_InOut_Range_X with (v:=v0) (l:=l) (u:=u0) (f':=(STACK.push f (parameter_nameRT a) (Int v0))); auto.
      inversion HA0; auto.
      inversion H30; subst; simpl in *; rewrite HZ9 in *;
      match goal with
      | [H: NameRT _ _ = NameRT _ _ |- _] => clear - H; inversion H; subst
      | _ => idtac
      end;
      repeat progress rewrite name_updated_exterior_checks; smack.
Qed.

Ltac apply_optArgs_copyin_completeness :=
  match goal with
  | [H1: toArgsRT ?st ?params ?args ?args',
     H2: toSymTabRT ?st ?st',
     H3: toParamSpecsRT ?params ?params',
     H4: well_typed_stack ?st' ?s,
     H5: well_typed_exps_x ?st' ?args',
     H6: optArgs ?st' ?params' ?args' ?args'',
     H7: copyInRT ?st' ?s ?f ?params' ?args' ?f' |- _ ] =>
      specialize (optArgs_copyin_completeness _ _ _ _ _ _ _ _ _ _ H1 H2 H3 H4 H5 H6 H7);
      let HZ := fresh "HZ" in intro HZ
  end.
  
  
(*---------------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------------*)

(** * help version with well_typed_value_in_stack and well_typed_value_in_store *)

Lemma eval_expr_value_in_bound': forall e st st' s e' v e'' eBound,
  toExpRT st e e' ->
    toSymTabRT st st' ->
      well_typed_value_in_stack st' s ->
        well_typed_exp_x st' e' ->
          evalExpRT st' s e' (OK (Int v)) ->
            optExp st' e' (e'', eBound) ->
              in_bound v eBound true.
Proof.
  intros;
  apply_well_typed_stack_infer;
  apply_eval_expr_value_in_bound; auto.
Qed.

Ltac apply_eval_expr_value_in_bound' :=
  match goal with
  | [H1: toExpRT ?st ?e ?e',
     H2: toSymTabRT ?st ?st',
     H3: well_typed_value_in_stack ?st' ?s,
     H4: well_typed_exp_x ?st' ?e',
     H5: evalExpRT ?st' ?s ?e' (OK (Int ?v)),
     H6: optExp ?st' ?e' _ |- _] =>
      specialize (eval_expr_value_in_bound' _ _ _ _ _ _ _ _ H1 H2 H3 H4 H5 H6);
      let HZ := fresh "HZ" in intros HZ
  end.

Lemma eval_name_value_in_bound': forall n st st' s n' v n'' nBound,
  toNameRT st n n' ->
    toSymTabRT st st' ->
      well_typed_value_in_stack st' s ->
        well_typed_name_x st' n' ->
          evalNameRT st' s n' (OK (Int v)) ->
            optName st' n' (n'', nBound) ->
              in_bound v nBound true.
Proof.
  intros;
  apply_well_typed_stack_infer;
  apply_eval_name_value_in_bound; auto.
Qed.

Ltac apply_eval_name_value_in_bound' :=
  match goal with
  | [H1: toNameRT ?st ?n ?n',
     H2: toSymTabRT ?st ?st',
     H3: well_typed_value_in_stack ?st' ?s,
     H4: well_typed_name_x ?st' ?n',
     H5: evalNameRT ?st' ?s ?n' (OK (Int ?v)),
     H6: optName ?st' ?n' (?n'', ?nBound) |- _] =>
      specialize (eval_name_value_in_bound' _ _ _ _ _ _ _ _ H1 H2 H3 H4 H5 H6);
      let HZ := fresh "HZ" in intros HZ
  end.

Lemma optExp_completeness': forall e st st' s e' e'' eBound v, 
  toExpRT st e e' ->
    toSymTabRT st st' ->
      well_typed_value_in_stack st' s ->
        well_typed_exp_x st' e' ->
          optExp st' e' (e'', eBound) ->
            evalExpRT st' s e' v ->
              evalExpRT st' s e'' v.
Proof.
  intros;
  apply_well_typed_stack_infer;
  apply_optExp_completeness; auto.
Qed.

Ltac apply_optExp_completeness' :=
  match goal with
  | [H1: toExpRT ?st ?e ?e',
     H2: toSymTabRT ?st ?st',
     H3: well_typed_value_in_stack ?st' ?s,
     H4: well_typed_exp_x ?st' ?e',
     H5: optExp ?st' ?e' _,
     H6: evalExpRT ?st' ?s ?e' ?v |- _] => 
      specialize (optExp_completeness' _ _ _ _ _ _ _ _ H1 H2 H3 H4 H5 H6);
      let HZ := fresh "HZ" in
      intro HZ
  end.

Lemma optExp_soundness': forall e st st' s e' e'' eBound v, 
  toExpRT st e e' ->
    toSymTabRT st st' ->
      well_typed_value_in_stack st' s ->
        well_typed_exp_x st' e' ->
          optExp st' e' (e'', eBound) ->
            evalExpRT st' s e'' v ->
              evalExpRT st' s e' v.
Proof.
  intros;
  apply_well_typed_stack_infer;
  apply_optExp_soundness; auto.
Qed.

Ltac apply_optExp_soundness' :=
  match goal with
  | [H1: toExpRT ?st ?e ?e',
     H2: toSymTabRT ?st ?st',
     H3: well_typed_value_in_stack ?st' ?s,
     H4: well_typed_exp_x ?st' ?e',
     H5: optExp ?st' ?e' (?e'', _),
     H6: evalExpRT ?st' ?s ?e'' ?v |- _] => 
      specialize (optExp_soundness' _ _ _ _ _ _ _ _ H1 H2 H3 H4 H5 H6);
      let HZ := fresh "HZ" in
      intro HZ
  end.

Lemma optName_completeness': forall n st st' s n' n'' nBound v, 
  toNameRT st n n' ->
    toSymTabRT st st' ->
      well_typed_value_in_stack st' s ->
        well_typed_name_x st' n' ->
          optName st' n' (n'', nBound) ->
            evalNameRT st' s n' v ->
              evalNameRT st' s n'' v.
Proof.
  intros;
  apply_well_typed_stack_infer;
  apply_optName_completeness; auto.
Qed.

Ltac apply_optName_completeness' := 
  match goal with
  | [H1: toNameRT ?st ?n ?n',
     H2: toSymTabRT ?st ?st',
     H3: well_typed_value_in_stack ?st' ?s,
     H4: well_typed_name_x ?st' ?n',
     H5: optName ?st' ?n' _,
     H6: evalNameRT ?st' ?s ?n' ?v |- _] =>
      specialize (optName_completeness' _ _ _ _ _ _ _ _ H1 H2 H3 H4 H5 H6);
      let HZ := fresh "HZ" in
      intro HZ
  end.

Lemma optName_soundness': forall n st st' s n' n'' nBound v, 
  toNameRT st n n' ->
    toSymTabRT st st' ->
      well_typed_value_in_stack st' s ->
        well_typed_name_x st' n' ->
          optName st' n' (n'', nBound) ->
            evalNameRT st' s n'' v ->
              evalNameRT st' s n' v.
Proof.
  intros;
  apply_well_typed_stack_infer;
  apply_optName_soundness; auto.
Qed.

Ltac apply_optName_soundness' := 
  match goal with
  | [H1: toNameRT ?st ?n ?n',
     H2: toSymTabRT ?st ?st',
     H3: well_typed_value_in_stack ?st' ?s,
     H4: well_typed_name_x ?st' ?n',
     H5: optName ?st' ?n' (?n'', _),
     H6: evalNameRT ?st' ?s ?n'' ?v |- _] =>
      specialize (optName_soundness' _ _ _ _ _ _ _ _ H1 H2 H3 H4 H5 H6);
      let HZ := fresh "HZ" in
      intro HZ
  end.

Lemma storeUpdateRT_opt_completeness': forall n st st' s s' n' n'' nBound v, 
  toNameRT st n n' ->
    toSymTabRT st st' ->
      well_typed_value_in_stack st' s ->
        well_typed_name_x st' n' ->
          optName st' n' (n'', nBound) ->
            storeUpdateRT st' s n' v s' ->
              storeUpdateRT st' s n'' v s'.
Proof.
  intros;
  apply_well_typed_stack_infer;
  apply_storeUpdateRT_opt_completeness; auto.
Qed.

Ltac apply_storeUpdateRT_opt_completeness' := 
  match goal with
  | [H1: toNameRT ?st ?n ?n' ,
     H2: toSymTabRT ?st ?st' ,
     H3: well_typed_value_in_stack ?st' ?s ,
     H4: well_typed_name_x ?st' ?n' ,
     H5: optName ?st' ?n' _ ,
     H6: storeUpdateRT ?st' ?s ?n' ?v ?s' |- _] =>
      specialize (storeUpdateRT_opt_completeness' _ _ _ _ _ _ _ _ _ H1 H2 H3 H4 H5 H6);
      let HZ := fresh "HZ" in
      intro HZ
  end.

Lemma storeUpdateRT_opt_soundness': forall n st st' s s' n' n'' nBound v, 
  toNameRT st n n' ->
    toSymTabRT st st' ->
      well_typed_value_in_stack st' s ->
        well_typed_name_x st' n' ->
          optName st' n' (n'', nBound) ->
            storeUpdateRT st' s n'' v s' ->
              storeUpdateRT st' s n' v s'.
Proof.
  intros;
  apply_well_typed_stack_infer;
  apply_storeUpdateRT_opt_soundness; auto.
Qed.

Ltac apply_storeUpdateRT_opt_soundness' := 
  match goal with
  | [H1: toNameRT ?st ?n ?n' ,
     H2: toSymTabRT ?st ?st' ,
     H3: well_typed_value_in_stack ?st' ?s ,
     H4: well_typed_name_x ?st' ?n' ,
     H5: optName ?st' ?n' (?n'', _) ,
     H6: storeUpdateRT ?st' ?s ?n'' ?v ?s' |- _] =>
      specialize (storeUpdateRT_opt_soundness' _ _ _ _ _ _ _ _ _ H1 H2 H3 H4 H5 H6);
      let HZ := fresh "HZ" in
      intro HZ
  end.

Lemma optArgs_copyin_completeness': forall params' st st' s f f' params args args' args'',
  toArgsRT st params args args' ->
  toSymTabRT st st' ->
  toParamSpecsRT params params' ->
  well_typed_value_in_stack st' s ->
  well_typed_exps_x st' args' ->
  optArgs st' params' args' args'' ->
  copyInRT st' s f params' args' f' ->
  copyInRT st' s f params' args'' f'.
Proof.
  intros;
  apply_well_typed_stack_infer;
  apply_optArgs_copyin_completeness; auto.
Qed.

Ltac apply_optArgs_copyin_completeness' :=
  match goal with
  | [H1: toArgsRT ?st ?params ?args ?args',
     H2: toSymTabRT ?st ?st',
     H3: toParamSpecsRT ?params ?params',
     H4: well_typed_value_in_stack ?st' ?s,
     H5: well_typed_exps_x ?st' ?args',
     H6: optArgs ?st' ?params' ?args' ?args'',
     H7: copyInRT ?st' ?s ?f ?params' ?args' ?f' |- _ ] =>
      specialize (optArgs_copyin_completeness' _ _ _ _ _ _ _ _ _ _ H1 H2 H3 H4 H5 H6 H7);
      let HZ := fresh "HZ" in intro HZ
  end.

Lemma optArgs_copyin_soundness': forall params' st st' s f f' params args args' args'',
  toArgsRT st params args args' ->
  toSymTabRT st st' ->
  toParamSpecsRT params params' ->
  well_typed_value_in_stack st' s -> well_typed_symbol_table st' ->
  well_typed_exps_x st' args' ->
  optArgs st' params' args' args'' ->
  copyInRT st' s f params' args'' f' ->
  copyInRT st' s f params' args' f'.
Proof.
  intros;
  apply_well_typed_stack_infer.
  assert(HA: well_typed_stack_and_symboltable st' s). constructor; auto.
  apply_optArgs_copyin_soundness; auto.
Qed.

Ltac apply_optArgs_copyin_soundness' :=
  match goal with
  | [H1: toArgsRT ?st ?params ?args ?args',
     H2: toSymTabRT ?st ?st',
     H3: toParamSpecsRT ?params ?params',
     H4: well_typed_value_in_stack ?st' ?s,
     H4b: well_typed_symbol_table ?st',
     H5: well_typed_exps_x ?st' ?args',
     H6: optArgs ?st' ?params' ?args' ?args'',
     H7: copyInRT ?st' ?s ?f ?params' ?args'' ?f' |- _ ] =>
      specialize (optArgs_copyin_soundness' _ _ _ _ _ _ _ _ _ _ H1 H2 H3 H4 H4b H5 H6 H7);
      let HZ := fresh "HZ" in intro HZ
  end.

(*---------------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------------*)
(*---------------------------------  END !  ---------------------------------------*)
(*---------------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------------*)


