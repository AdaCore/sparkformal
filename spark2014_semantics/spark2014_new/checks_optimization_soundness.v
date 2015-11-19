Require Export checks_optimization_soundness_util.

Scheme expression_ind := Induction for expression Sort Prop 
                         with name_ind := Induction for name Sort Prop.

Scheme expression_x_ind := Induction for expression_x Sort Prop 
                         with name_x_ind := Induction for name_x Sort Prop.


Ltac apply_copy_out_opt_H :=
  match goal with
  | [H1: forall (st : symboltable) (st' : symboltable_x)
                (s : STACK.stack) (f : STACK.scope_level * STACK.store)
                (s' : Return STACK.stack)
                (params : list parameter_specification)
                (args : list expression) (args' args'' : list expression_x),
              compile2_flagged_args st params args args' ->
              compile2_flagged_symbol_table st st' ->
              compile2_flagged_parameter_specifications params ?params' ->
              well_typed_symbol_table st' ->
              well_typed_value_in_stack st' s ->
              well_typed_value_in_store st' (snd f) ->
              well_typed_exps_x st' args' ->
              well_typed_params_x st' ?params' ->
              well_typed_args_x st' args' ?params' ->
              optimize_args_x st' ?params' args' args'' ->
              copy_out_x st' s f ?params' args' s' ->
              copy_out_x st' s f ?params' args'' s',
     H2: compile2_flagged_args ?st ?params ?args ?args', 
     H3: compile2_flagged_symbol_table ?st ?st',
     H4: compile2_flagged_parameter_specifications ?params ?params',
     H5: well_typed_symbol_table ?st',
     H6: well_typed_value_in_stack ?st' ?s,
     H7: well_typed_value_in_store ?st' (snd ?f),
     H8: well_typed_exps_x ?st' ?args',
     H9: well_typed_params_x ?st' ?params',
     H10: well_typed_args_x ?st' ?args' ?params', 
     H11: optimize_args_x ?st' ?params' ?args' ?args'',
     H12: copy_out_x ?st' ?s ?f ?params' ?args' ?s' |- _ ] =>
      specialize (H1 _ _ _ _ _ _ _ _ _ H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12)
  end.


(** * copy_out_args_checks_optimization_soundness *)
Lemma copy_out_args_checks_optimization_soundness: forall params' st st' s f s' params args args' args'',
  compile2_flagged_args st params args args' ->
  compile2_flagged_symbol_table st st' ->
  compile2_flagged_parameter_specifications params params' ->
  well_typed_symbol_table st' ->
  well_typed_value_in_stack st' s ->
  well_typed_value_in_store st' (snd f) -> (* Definition frame := prod scope_level store. *)
  well_typed_exps_x st' args' ->
  well_typed_params_x st' params' ->
  well_typed_args_x st' args' params' ->
  optimize_args_x st' params' args' args'' ->
  copy_out_x st' s f params' args' s' ->
  copy_out_x st' s f params' args'' s'.
Proof.
 induction params'; intros.
-inversion H8; subst.
 inversion H9; subst; auto.
- destruct args', args'', params, args;
  match goal with 
  | [H: copy_out_x _ _ _ (?a :: ?al) nil _ |- _] => inversion H
  | [H: optimize_args_x _ (?a :: ?al) (?e :: ?el) nil |- _] => inversion H
  | [H: compile2_flagged_parameter_specifications nil (?param :: ?params) |- _] => inversion H
  | [H: compile2_flagged_args _ (?param :: ?params) nil _ |- _] => inversion H
  | _ => idtac
  end.
  specialize (well_typed_stack_infer _ _ H3); intro HB1.
  specialize (well_typed_store_infer _ _ H4); intro HB2.
  
  inversion H1; subst;
  inversion H5; subst; 
  inversion H6; subst;
  inversion H7; subst.
  assert(HZ: p.(parameter_mode) = a.(parameter_mode_x)).
  clear - H13; inversion H13; smack.
  assert(HZ1: (parameter_subtype_mark p) = (parameter_subtype_mark_x a)).
  clear - H13; inversion H13; smack. 
  (*******)
  inversion H; subst;
  inversion H8; subst;
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
  | [H1: is_range_constrainted_type ?x = _, 
     H2: is_range_constrainted_type ?y = _,
     H3: ?x = ?y |- _] => 
      rewrite H3 in H1; rewrite H1 in H2; inversion H2
  | _ => idtac
  end;
  (*******)
  inversion H9; subst;
  match goal with
  | [H1: parameter_mode_x ?a = _ ,
     H2: parameter_mode_x ?a = _ |- _] => rewrite H2 in H1; inversion H1 
  | [H1: parameter_mode_x ?a = In ,
     H2: parameter_mode_x ?a = Out \/ parameter_mode_x ?a = In_Out |- _] => 
      rewrite H1 in H2; clear - H2; smack
  | _ => idtac
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
  repeat progress match goal with
  | [H1: fetch_exp_type_x ?x ?st = _, 
     H2: fetch_exp_type_x ?x ?st = _ |- _] => rewrite H1 in H2; inversion H2; subst
  | _ => idtac
  end;
  match goal with
  | [H1: is_range_constrainted_type ?x = false, 
     H2: is_range_constrainted_type ?x = true |- _] => 
      rewrite H1 in H2; inversion H2
  | [H1: is_range_constrainted_type ?x = _, 
     H2: is_range_constrainted_type ?y = _,
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
  | [H1: extract_subtype_range_x _ ?t _, 
     H2: extract_subtype_range_x _ ?t _ |- _] => 
      specialize (extract_subtype_range_unique _ _ _ _ _ _ H1 H2);
      let HZ := fresh "HZ" in intro HZ; destruct HZ; subst
  | _ => idtac
  end;
  match goal with
  | [H: optimize_name_x _ _ _ |- _] => 
      specialize (optimize_name_ex_cks_eq _ _ _ _ H);
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
  | [H1: forall (st : symboltable) (st' : symboltable_x)
                (s : STACK.stack) (f : STACK.scope_level * STACK.store)
                (s' : Return STACK.stack)
                (params : list parameter_specification)
                (args : list expression) (args' args'' : list expression_x),
              compile2_flagged_args st params args args' ->
              compile2_flagged_symbol_table st st' ->
              compile2_flagged_parameter_specifications params ?params' ->
              well_typed_symbol_table st' ->
              well_typed_value_in_stack st' s ->
              well_typed_value_in_store st' (snd f) ->
              well_typed_exps_x st' args' ->
              well_typed_params_x st' ?params' ->
              well_typed_args_x st' args' ?params' ->
              optimize_args_x st' ?params' args' args'' ->
              copy_out_x st' s f ?params' args' s' ->
              copy_out_x st' s f ?params' args'' s',
     H2: compile2_flagged_args ?st ?params ?args ?args', 
     H3: compile2_flagged_symbol_table ?st ?st',
     H4: compile2_flagged_parameter_specifications ?params ?params',
     H5: well_typed_symbol_table ?st',
     H6: well_typed_value_in_stack ?st' ?s,
     H7: well_typed_value_in_store ?st' (snd ?f),
     H8: well_typed_exps_x ?st' ?args',
     H9: well_typed_params_x ?st' ?params',
     H10: well_typed_args_x ?st' ?args' ?params',
     H11: optimize_args_x ?st' ?params' ?args' ?args'',
     H12: copy_out_x ?st' ?s ?f ?params' ?args' ?s' |- _ ] =>
      specialize (H1 _ _ _ _ _ _ _ _ _ H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12)
  | _ => idtac
  end;
  match goal with
  | [H: parameter_mode_x _ = In |- _] => apply Copy_Out_Mode_In_X; auto
  | _ => idtac
  end. 
  (* 21 sub-proof needs to be proved ! *)
  + apply Copy_Out_Mode_Out_nRTE with (v:=v); auto.
    rewrite HZ2; assumption.
    apply_store_update_optimization_soundness'; auto.
  + assert(HZ3: well_typed_value_in_stack st' s'0). simpl in *.
      repeat progress match goal with
      | [H1: fetch_exp_type_x ?x ?y = _, H2: fetch_exp_type_x ?x ?y = _ |- _] => rewrite H1 in H2; inversion H2; subst
      end.
      apply_well_typed_value_in_store_fetch. 
      apply_value_well_typed_with_matched_type.
      match goal with 
      | [H: Some ?t = fetch_exp_type_x (name_astnum_x ?n_flagged) ?st |- _] => symmetry in H
      end;
      apply_storeUpdate_with_typed_value_preserve_typed_stack; auto.
    apply_copy_out_opt_H.
    apply Copy_Out_Mode_Out_NoRange_X with (v:=v) (s':=s'0); auto.
      rewrite HZ2; auto.
    apply_store_update_optimization_soundness'; auto.
  (***********************************************************************************)
  (***** following 3 cases ****)
  + clear H H5 H7 H8.
    inversion HB2; subst. specialize (H _ _ H40). destruct H as [m1 [t1 [HZ11 HZ12]]].
    match goal with
    | [H1: fetch_var_x _ _ = _, H2: fetch_var_x _ _ = _ |- _] => rewrite H1 in H2; inversion H2
    end. rewrite H7 in *.
    apply_typed_value_in_bound.
    inversion H45; subst. 
    apply_optimize_range_check_on_copy_out_reserve; subst.
    apply Copy_Out_Mode_Out_Range_RTE_X with (v:=v0) (l:=u') (u:=v') (t:=t0); auto.
    rewrite name_updated_exterior_checks in HZ4; rewrite HZ4; smack.
  + apply_store_update_optimization_soundness; apply_store_update_ex_cks_stripped.
    rewrite name_updated_exterior_checks in HZ4.
    match goal with
    | [H: optimize_range_check_on_copy_out _ _ _ _ |- _] => inversion H; subst
    end.
    
    simpl; rewrite HZ4.
    apply Copy_Out_Mode_Out_nRTE with (v:=Int v0); auto.
    (* zz1
    apply Copy_Out_Mode_Out_Range_nRTE_X with (v:=v0) (t:=t0) (l:=u') (u:=v'); auto. *)
    rewrite name_updated_exterior_checks; smack.
    apply_store_update_ex_cks_added.

    apply Copy_Out_Mode_Out_Range_nRTE_X with (v:=v0) (t:=t0) (l:=u') (u:=v'); auto.
    rewrite HZ4; smack.
  + assert(HA: well_typed_value_in_stack st' s'0). 
      rewrite update_exterior_checks_name_astnum_eq in H19. rewrite H19 in H34.
      apply_value_in_range_is_well_typed.
      apply_well_typed_name_preserve.
      apply_storeUpdate_with_typed_value_preserve_typed_stack; auto.
    apply_copy_out_opt_H.
    apply_store_update_optimization_soundness; apply_store_update_ex_cks_stripped.
    rewrite name_updated_exterior_checks in HZ4.
    match goal with
    | [H: optimize_range_check_on_copy_out _ _ _ _ |- _] => inversion H; subst
    end.
    
    simpl; rewrite HZ4.
    apply Copy_Out_Mode_Out_NoRange_X with (v:=Int v0) (s':=s'0); auto.
    (* zz1: 
     apply Copy_Out_Mode_Out_Range_X with (v:=v0) (t:=t0) (l:=u') (u:=v') (s':=s'0); auto. *)
    rewrite name_updated_exterior_checks; smack.
    apply_store_update_ex_cks_added.
    
    apply Copy_Out_Mode_Out_Range_X with (v:=v0) (t:=t0) (l:=u') (u:=v') (s':=s'0); auto.
    rewrite HZ4; smack.
  + apply Copy_Out_Mode_Out_nRTE with (v:=v); auto.
    rewrite HZ2; assumption.
    apply_store_update_optimization_soundness; auto.
  + assert(HZ3: well_typed_value_in_stack st' s'0). simpl in *.
      repeat progress match goal with
      | [H1: fetch_exp_type_x ?x ?y = _, H2: fetch_exp_type_x ?x ?y = _ |- _] => rewrite H1 in H2; inversion H2; subst
      end.
      apply_well_typed_value_in_store_fetch. 
      apply_value_well_typed_with_matched_type.
      match goal with 
      | [H: Some ?t = fetch_exp_type_x (name_astnum_x ?n_flagged) ?st |- _] => symmetry in H
      end;
      apply_storeUpdate_with_typed_value_preserve_typed_stack; auto.

    apply_copy_out_opt_H.
    apply Copy_Out_Mode_Out_NoRange_X with (v:=v) (s':=s'0); auto.
      rewrite HZ2; auto.
    apply_store_update_optimization_soundness; auto.
  + apply Copy_Out_Mode_Out_nRTE with (v:=v); auto.
    rewrite HZ2; assumption.
    apply_store_update_optimization_soundness; auto.
    apply_store_update_ex_cks_stripped; auto.
  + assert(HZ6: well_typed_value_in_stack st' s'0). simpl in *.
      repeat progress match goal with
      | [H1: fetch_exp_type_x ?x ?y = _, H2: fetch_exp_type_x ?x ?y = _ |- _] => rewrite H1 in H2; inversion H2; subst
      end.
      apply_well_typed_value_in_store_fetch. 
      apply_value_well_typed_with_matched_type.
      match goal with 
      | [H: Some ?t = fetch_exp_type_x (name_astnum_x ?n_flagged) ?st |- _] => 
          rewrite update_exterior_checks_name_astnum_eq in H; symmetry in H
      end;
      apply_storeUpdate_with_typed_value_preserve_typed_stack; auto.

    apply_copy_out_opt_H.
    apply Copy_Out_Mode_Out_NoRange_X with (v:=v) (s':=s'0); auto.
      rewrite HZ2; auto.
    apply_store_update_optimization_soundness; auto.
    apply_store_update_ex_cks_stripped; auto.
  + apply Copy_Out_Mode_Out_Range_RTE_X with (v:=v) (l:=l) (u:=u) (t:=t0); auto.
    rewrite HZ3. rewrite name_updated_exterior_checks; smack.
  + apply Copy_Out_Mode_Out_Range_nRTE_X with (v:=v) (l:=l) (u:=u) (t:=t0); auto.
    rewrite HZ3; rewrite name_updated_exterior_checks; smack.
    apply_store_update_optimization_soundness; auto.
    apply_store_update_ex_cks_stripped; auto.
  + assert(HZ7: well_typed_value_in_stack st' s'0). simpl in *.
      rewrite update_exterior_checks_name_astnum_eq in H19. rewrite H19 in H34.
      apply_value_in_range_is_well_typed.
      apply_well_typed_name_preserve.
      apply_storeUpdate_with_typed_value_preserve_typed_stack; auto.

    apply_copy_out_opt_H.
    apply Copy_Out_Mode_Out_Range_X with (v:=v) (t:=t0) (l:=l) (u:=u) (s':=s'0); auto.
    rewrite HZ3; rewrite name_updated_exterior_checks; smack.
    apply_store_update_optimization_soundness; auto.
    apply_store_update_ex_cks_stripped; auto.
  (***********************************************************************************)
  (**** following 3 cases ****)
  (* for n', it only has: (Do_Range_Check_On_CopyOut :: nil) *)
  + clear H H5 H7 H8.
    inversion H37; subst. (* optimize_expression_x st' (E_Name_X _ _ _) (E_Name_X _ _ n', _)*)
    match goal with
    | [H: optimize_name_x _ _ _ |- _] => 
        specialize (optimize_name_ex_cks_eq _ _ _ _ H); 
        let HZ := fresh "HZ" in intro HZ; rewrite name_updated_exterior_checks in HZ
    end.
    match goal with
    | [H: optimize_range_check _ _ _ _ |- _] => inversion H; subst
    end;
    inversion HB2; subst; specialize (H _ _ H42); destruct H as [m1 [t1 [HZ11 HZ12]]];
    match goal with
    | [H1: fetch_var_x _ _ = _, H2: fetch_var_x _ _ = _ |- _] => rewrite H1 in H2; inversion H2; subst
    end;
    apply_typed_value_in_bound;
    inversion H47; subst;
    apply_optimize_range_check_on_copy_out_reserve; subst;

    apply Copy_Out_Mode_Out_Range_RTE_X with (v:=v0) (l:=u') (u:=v') (t:=t); auto;
    try (rewrite name_updated_exterior_checks); smack.
  + clear H H5 H7 H8.
    inversion H37; subst. (* optimize_expression_x st' (E_Name_X _ _ _) (E_Name_X _ _ n', _)*)
    match goal with
    | [H: optimize_name_x _ _ _ |- _] => 
        specialize (optimize_name_ex_cks_eq _ _ _ _ H); 
        let HZ := fresh "HZ" in intro HZ; rewrite name_updated_exterior_checks in HZ
    end.
    match goal with
    | [H: optimize_name_x _ (update_exterior_checks_name _ _) _ |- _] =>
        specialize (optimize_name_ex_cks_stripped _ _ _ _ _ H); let HZ := fresh "HZ" in intros HZ
    end.
    apply_store_update_optimization_soundness. apply_store_update_ex_cks_stripped.

    match goal with
    | [H: optimize_range_check _ _ _ _ |- _] => inversion H; subst
    end;
    match goal with
    | [H: optimize_range_check_on_copy_out _ _ _ _ |- _] => inversion H; subst
    end.
    * apply Copy_Out_Mode_Out_nRTE with (v:=Int v0); auto; simpl.
      rewrite HZ6; repeat progress rewrite name_updated_exterior_checks; smack.
      repeat progress apply_store_update_ex_cks_added. 
    * apply Copy_Out_Mode_Out_Range_nRTE_X with (v:=v0) (t:=t0) (l:=u') (u:=v'); auto; simpl.
      rewrite HZ6; rewrite name_updated_exterior_checks; smack.
      apply_store_update_ex_cks_added. 
    * apply Copy_Out_Mode_Out_nRTE with (v:=Int v0); auto; simpl.
      rewrite HZ6; rewrite name_updated_exterior_checks; smack.
      apply_store_update_ex_cks_added. 
    * apply Copy_Out_Mode_Out_Range_nRTE_X with (v:=v0) (t:=t0) (l:=u') (u:=v'); auto; simpl.
      rewrite HZ6; smack.
  + clear H H5 H7 H8 H9.
    assert(HA: well_typed_value_in_stack st' s'0). simpl in *.
      rewrite update_exterior_checks_name_astnum_eq in H19. rewrite H19 in H35.
      apply_value_in_range_is_well_typed.
      apply_well_typed_name_preserve.
      apply_storeUpdate_with_typed_value_preserve_typed_stack; auto.      
    apply_copy_out_opt_H.
    inversion H37; subst. (* optimize_expression_x st' (E_Name_X _ _ _) (E_Name_X _ _ n', _)*)
    match goal with
    | [H: optimize_name_x _ _ _ |- _] => 
        specialize (optimize_name_ex_cks_eq _ _ _ _ H); 
        let HZ := fresh "HZ" in intro HZ; rewrite name_updated_exterior_checks in HZ
    end.
    match goal with
    | [H: optimize_name_x _ (update_exterior_checks_name _ _) _ |- _] =>
        specialize (optimize_name_ex_cks_stripped _ _ _ _ _ H); let HZ := fresh "HZ" in intros HZ
    end.
    apply_store_update_optimization_soundness. apply_store_update_ex_cks_stripped.

    match goal with
    | [H: optimize_range_check _ _ _ _ |- _] => inversion H; subst
    end;
    match goal with
    | [H: optimize_range_check_on_copy_out _ _ _ _ |- _] => inversion H; subst
    end.
    * apply Copy_Out_Mode_Out_NoRange_X with (v:=Int v0) (s':=s'0); auto; simpl.
      rewrite HZ6; repeat progress rewrite name_updated_exterior_checks; smack.
      repeat progress apply_store_update_ex_cks_added.
    * apply Copy_Out_Mode_Out_Range_X with (v:=v0) (t:=t0) (l:=u') (u:=v') (s':=s'0); auto; simpl.
      rewrite HZ6; rewrite name_updated_exterior_checks; smack.
      apply_store_update_ex_cks_added. 
    * apply Copy_Out_Mode_Out_NoRange_X with (v:=Int v0) (s':=s'0); auto; simpl.
      rewrite HZ6; rewrite name_updated_exterior_checks; smack.
      apply_store_update_ex_cks_added. 
    * apply Copy_Out_Mode_Out_Range_X with (v:=v0) (t:=t0) (l:=u') (u:=v') (s':=s'0); auto; simpl.
      rewrite HZ6; smack.
  + apply Copy_Out_Mode_Out_Range_RTE_X with (v:=v) (l:=l) (u:=u) (t:=t0); auto.
    rewrite HZ3. rewrite name_updated_exterior_checks; smack.
  + apply Copy_Out_Mode_Out_Range_nRTE_X with (v:=v) (l:=l) (u:=u) (t:=t0); auto.
    rewrite HZ3; rewrite name_updated_exterior_checks; smack.
    apply_store_update_optimization_soundness; auto.
    apply_store_update_ex_cks_stripped; auto.
  + assert(HA: well_typed_value_in_stack st' s'0).
      rewrite update_exterior_checks_name_astnum_eq in H19. rewrite H19 in H34.
      apply_value_in_range_is_well_typed.
      apply_well_typed_name_preserve.
      apply_storeUpdate_with_typed_value_preserve_typed_stack; auto.
    apply_copy_out_opt_H.
    apply Copy_Out_Mode_Out_Range_X with (v:=v) (t:=t0) (l:=l) (u:=u) (s':=s'0); auto.
    rewrite HZ3; rewrite name_updated_exterior_checks; smack.
    apply_store_update_optimization_soundness; auto.
    apply_store_update_ex_cks_stripped; auto.
  (***********************************************************************************)
  (**** following 3 cases ****)
  (* for n', it only has: (Do_Range_Check :: Do_Range_Check_On_CopyOut :: nil) *)
  + clear H H5 H7 H8.
    inversion H37; subst. (* optimize_expression_x st' (E_Name_X _ _ _) (E_Name_X _ _ n', _)*)
    match goal with
    | [H: optimize_name_x _ _ _ |- _] => 
        specialize (optimize_name_ex_cks_eq _ _ _ _ H); 
        let HZ := fresh "HZ" in intro HZ; rewrite name_updated_exterior_checks in HZ
    end.
    match goal with
    | [H: optimize_range_check _ _ _ _ |- _] => inversion H; subst
    end;
    inversion HB2; subst; specialize (H _ _ H42); destruct H as [m1 [t1 [HZ11 HZ12]]];
    match goal with
    | [H1: fetch_var_x _ _ = _, H2: fetch_var_x _ _ = _ |- _] => rewrite H1 in H2; inversion H2; subst
    end;
    apply_typed_value_in_bound;
    inversion H47; subst;
    apply_optimize_range_check_on_copy_out_reserve; subst;

    apply Copy_Out_Mode_Out_Range_RTE_X with (v:=v0) (l:=u') (u:=v') (t:=t); auto;
    try (rewrite name_updated_exterior_checks); smack.
  + clear H H5 H7 H8.
    inversion H37; subst. (* optimize_expression_x st' (E_Name_X _ _ _) (E_Name_X _ _ n', _)*)
    match goal with
    | [H: optimize_name_x _ _ _ |- _] => 
        specialize (optimize_name_ex_cks_eq _ _ _ _ H); 
        let HZ := fresh "HZ" in intro HZ; rewrite name_updated_exterior_checks in HZ
    end.
    match goal with
    | [H: optimize_name_x _ (update_exterior_checks_name _ _) _ |- _] =>
        specialize (optimize_name_ex_cks_stripped _ _ _ _ _ H); let HZ := fresh "HZ" in intros HZ
    end.
    apply_store_update_optimization_soundness. apply_store_update_ex_cks_stripped.

    match goal with
    | [H: optimize_range_check _ _ _ _ |- _] => inversion H; subst
    end;
    match goal with
    | [H: optimize_range_check_on_copy_out _ _ _ _ |- _] => inversion H; subst
    end.
    * apply Copy_Out_Mode_Out_nRTE with (v:=Int v0); auto; simpl.
      rewrite HZ6; repeat progress rewrite name_updated_exterior_checks; smack.
      repeat progress apply_store_update_ex_cks_added. 
    * apply Copy_Out_Mode_Out_Range_nRTE_X with (v:=v0) (t:=t0) (l:=u') (u:=v'); auto; simpl.
      rewrite HZ6; rewrite name_updated_exterior_checks; smack.
      apply_store_update_ex_cks_added. 
    * apply Copy_Out_Mode_Out_nRTE with (v:=Int v0); auto; simpl.
      rewrite HZ6; rewrite name_updated_exterior_checks; smack.
      apply_store_update_ex_cks_added. 
    * apply Copy_Out_Mode_Out_Range_nRTE_X with (v:=v0) (t:=t0) (l:=u') (u:=v'); auto; simpl.
      rewrite HZ6; smack.
  + clear H H5 H7 H8 H9.
    assert(HA: well_typed_value_in_stack st' s'0).
      rewrite update_exterior_checks_name_astnum_eq in H19. rewrite H19 in H35.
      apply_value_in_range_is_well_typed.
      apply_well_typed_name_preserve.
      apply_storeUpdate_with_typed_value_preserve_typed_stack; auto.
    apply_copy_out_opt_H.
    inversion H37; subst. (* optimize_expression_x st' (E_Name_X _ _ _) (E_Name_X _ _ n', _)*)
    match goal with
    | [H: optimize_name_x _ _ _ |- _] => 
        specialize (optimize_name_ex_cks_eq _ _ _ _ H); 
        let HZ := fresh "HZ" in intro HZ; rewrite name_updated_exterior_checks in HZ
    end.
    match goal with
    | [H: optimize_name_x _ (update_exterior_checks_name _ _) _ |- _] =>
        specialize (optimize_name_ex_cks_stripped _ _ _ _ _ H); let HZ := fresh "HZ" in intros HZ
    end.
    apply_store_update_optimization_soundness. apply_store_update_ex_cks_stripped.

    match goal with
    | [H: optimize_range_check _ _ _ _ |- _] => inversion H; subst
    end;
    match goal with
    | [H: optimize_range_check_on_copy_out _ _ _ _ |- _] => inversion H; subst
    end.
    * apply Copy_Out_Mode_Out_NoRange_X with (v:=Int v0) (s':=s'0); auto; simpl.
      rewrite HZ6; repeat progress rewrite name_updated_exterior_checks; smack.
      repeat progress apply_store_update_ex_cks_added.
    * apply Copy_Out_Mode_Out_Range_X with (v:=v0) (t:=t0) (l:=u') (u:=v') (s':=s'0); auto; simpl.
      rewrite HZ6; rewrite name_updated_exterior_checks; smack.
      apply_store_update_ex_cks_added. 
    * apply Copy_Out_Mode_Out_NoRange_X with (v:=Int v0) (s':=s'0); auto; simpl.
      rewrite HZ6; rewrite name_updated_exterior_checks; smack.
      apply_store_update_ex_cks_added. 
    * apply Copy_Out_Mode_Out_Range_X with (v:=v0) (t:=t0) (l:=u') (u:=v') (s':=s'0); auto; simpl.
      rewrite HZ6; smack.
Qed.

Ltac apply_copy_out_args_checks_optimization_soundness :=
  match goal with
  | [H1: compile2_flagged_args ?st ?params ?args ?args',
     H2: compile2_flagged_symbol_table ?st ?st',
     H3: compile2_flagged_parameter_specifications ?params ?params',
     H4: well_typed_symbol_table ?st',
     H5: well_typed_value_in_stack ?st' ?s,
     H6: well_typed_value_in_store ?st' (snd ?f),
     H7: well_typed_exps_x ?st' ?args',
     H8: well_typed_params_x ?st' ?params',
     H9: well_typed_args_x ?st' ?args' ?params',
     H10: optimize_args_x ?st' ?params' ?args' ?args'',
     H11: copy_out_x ?st' ?s ?f ?params' ?args' ?s' |- _ ] =>
      specialize (copy_out_args_checks_optimization_soundness _ _ _ _ _ _ _ _ _ _ H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11);
      let HZ := fresh "HZ" in intro HZ
  end.


(** * statement_checks_optimization_soundness *)
Lemma statement_checks_optimization_soundness: forall st st' s s' c c' c'',
  eval_stmt_x st' s c' s' ->
    compile2_flagged_symbol_table st st' ->
      well_typed_stack_and_symboltable st' s ->
        well_typed_statement_x st' c' ->
          compile2_flagged_stmt st c c' ->
            optimize_statement_x st' c' c'' ->
              eval_stmt_x st' s c'' s'.
Proof.
  intros st st' s s' c c' c'' H; revert st c c''.
  induction H; intros;
  match goal with
  | [H: well_typed_stack_and_symboltable ?st ?s |- _] => destruct H as [st s HStack HSymb]
  end;
  specialize (well_typed_stack_infer _ _ HStack); intro HB1.
- inversion H3; subst; auto; constructor.
- inversion H2; subst;
  inversion H3; subst;
  inversion H4; subst;
  match goal with
  | [H: compile2_flagged_name _ _ _ |- _] => 
      specialize (name_ast_num_eq _ _ _ H); let HZ := fresh "HZ" in intro HZ; rewrite HZ in *
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
  | [H: extract_subtype_range_x _ _ (Range_X _ _) |- _] => 
      specialize (range_constrainted_type_true _ _ _ _ H);
      let HZ := fresh "HZ" in intros HZ
  | _ => idtac
  end;
  match goal with
  | [H1: is_range_constrainted_type ?x = true, 
     H2: is_range_constrainted_type ?y = false |- _] => 
      rewrite H1 in H2; inversion H2
  | _ => idtac
  end;

  match goal with
  | [H: well_typed_exp_x _ (update_exterior_checks_exp _ _) |- _] => 
    specialize (well_typed_exp_preserve _ _ _ H); let HZ := fresh "HZ" in intro HZ
  | _ => idtac
  end;
  match goal with
  | [H: optimize_expression_x _ (update_exterior_checks_exp _ _) _ |- _] => 
    specialize (optimize_exp_ex_cks_stripped _ _ _ _ _ H); let HZ := fresh "HZ" in intro HZ
  | _ => idtac
  end;
  match goal with
  | [H: eval_expr_x _ _ (update_exterior_checks_exp _ _) _ |- _] => 
    specialize (eval_exp_ex_cks_stripped _ _ _ _ _ H); let HZ := fresh "HZ" in intro HZ
  | _ => idtac
  end.
  + apply Eval_S_Assignment_eRTE_X; auto.
    apply_expression_checks_optimization_soundness; auto.
  + apply Eval_S_Assignment_eRTE_X; auto.
    apply_expression_checks_optimization_soundness.
    specialize (eval_exp_ex_cks_stripped _ _ _ _ _ HZ5); let HZ := fresh "HZ" in intro HZ.
    apply_eval_expr_value_reserve; auto.
- inversion H4; subst;
  inversion H5; subst;
  inversion H6; subst;
  match goal with
  | [H: compile2_flagged_name _ _ _ |- _] => 
      specialize (name_ast_num_eq _ _ _ H); let HZ := fresh "HZ" in intro HZ; rewrite HZ in *
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
  | [H: extract_subtype_range_x _ _ (Range_X _ _) |- _] => 
      specialize (range_constrainted_type_true _ _ _ _ H);
      let HZ := fresh "HZ" in intros HZ
  | _ => idtac
  end;
  match goal with
  | [H1: is_range_constrainted_type ?x = true, 
     H2: is_range_constrainted_type ?y = false |- _] => 
      rewrite H1 in H2; inversion H2
  | [H: exp_exterior_checks (update_exterior_checks_exp _ _) = _ |- _] 
      => rewrite exp_updated_exterior_checks in H; inversion H; subst
  | _ => idtac
  end.
  + apply Eval_S_Assignment_X with (v:=v); auto.
    apply_expression_checks_optimization_soundness; auto.    
    apply_optimize_exp_ex_cks_eq; smack.
    apply_store_update_optimization_soundness; auto.
- inversion H6; subst;
  inversion H7; subst;
  inversion H8; subst;
  match goal with
  | [H: compile2_flagged_name _ _ _ |- _] => 
      specialize (name_ast_num_eq _ _ _ H); let HZ := fresh "HZ" in intro HZ; rewrite HZ in *
  | _ => idtac
  end;
  match goal with
  | [H1: compile2_flagged_symbol_table ?st ?st',
     H2: fetch_exp_type _ ?st = _ |- _ ] => 
      specialize (symbol_table_exp_type_rel _ _ _ _ H1 H2);
      let HZ := fresh "HZ" in intros HZ
  | _ => idtac
  end; 
  repeat progress match goal with
  | [H1: fetch_exp_type_x ?x ?st = _, 
     H2: fetch_exp_type_x ?x ?st = _ |- _] => rewrite H1 in H2; inversion H2; subst
  | _ => idtac
  end;
  match goal with
  | [H: extract_subtype_range_x _ _ (Range_X _ _) |- _] => 
      specialize (range_constrainted_type_true _ _ _ _ H);
      let HZ := fresh "HZ" in intros HZ
  | _ => idtac
  end;
  match goal with
  | [H1: is_range_constrainted_type ?x = true, 
     H2: is_range_constrainted_type ?y = false |- _] => 
      rewrite H1 in H2; inversion H2
  | _ => idtac
  end;

  match goal with
  | [H: well_typed_exp_x _ (update_exterior_checks_exp _ _) |- _] => 
    specialize (well_typed_exp_preserve _ _ _ H); let HZ := fresh "HZ" in intro HZ
  | _ => idtac
  end;
  match goal with
  | [H: optimize_expression_x _ (update_exterior_checks_exp _ _) _ |- _] => 
    specialize (optimize_exp_ex_cks_stripped _ _ _ _ _ H); let HZ := fresh "HZ" in intro HZ
  | _ => idtac
  end;
  match goal with
  | [H: eval_expr_x _ _ (update_exterior_checks_exp _ _) _ |- _] => 
    specialize (eval_exp_ex_cks_stripped _ _ _ _ _ H); let HZ := fresh "HZ" in intro HZ
  | _ => idtac
  end.
  + apply Eval_S_Assignment_Range_RTE_X with (v:=v) (t:=t1) (l:=l) (u:=u); auto.
    * apply_expression_checks_optimization_soundness; auto.
      specialize (eval_exp_ex_cks_stripped _ _ _ _ _ HZ5); let HZ := fresh "HZ" in intro HZ.
      apply_eval_expr_value_reserve; auto.
    * specialize (optimize_exp_ex_cks_eq _ _ _ _ H25); intros HZ5; rewrite exp_updated_exterior_checks in HZ5.
      apply_extract_subtype_range_unique.
      apply_eval_expr_value_in_bound.
      inversion H3; subst.
      apply_optimize_range_check_reserve; smack.
    * apply_optimize_name_ast_num_eq; smack.
- inversion H7; subst;
  inversion H8; subst;
  inversion H9; subst;
  match goal with
  | [H: compile2_flagged_name _ _ _ |- _] => 
      specialize (name_ast_num_eq _ _ _ H); let HZ := fresh "HZ" in intro HZ; rewrite HZ in *
  | _ => idtac
  end;
  match goal with
  | [H1: compile2_flagged_symbol_table ?st ?st',
     H2: fetch_exp_type _ ?st = _ |- _ ] => 
      specialize (symbol_table_exp_type_rel _ _ _ _ H1 H2);
      let HZ := fresh "HZ" in intros HZ
  | _ => idtac
  end; 
  repeat progress match goal with
  | [H1: fetch_exp_type_x ?x ?st = _, 
     H2: fetch_exp_type_x ?x ?st = _ |- _] => rewrite H1 in H2; inversion H2; subst
  | _ => idtac
  end;
  match goal with
  | [H: extract_subtype_range_x _ _ (Range_X _ _) |- _] => 
      specialize (range_constrainted_type_true _ _ _ _ H);
      let HZ := fresh "HZ" in intros HZ
  | _ => idtac
  end;
  match goal with
  | [H1: is_range_constrainted_type ?x = true, 
     H2: is_range_constrainted_type ?y = false |- _] => 
      rewrite H1 in H2; inversion H2
  | _ => idtac
  end;

  match goal with
  | [H: well_typed_exp_x _ (update_exterior_checks_exp _ _) |- _] => 
    specialize (well_typed_exp_preserve _ _ _ H); let HZ := fresh "HZ" in intro HZ
  | _ => idtac
  end;
  match goal with
  | [H: optimize_expression_x _ (update_exterior_checks_exp _ _) _ |- _] => 
    specialize (optimize_exp_ex_cks_stripped _ _ _ _ _ H); let HZ := fresh "HZ" in intro HZ
  | _ => idtac
  end;
  match goal with
  | [H: eval_expr_x _ _ (update_exterior_checks_exp _ _) _ |- _] => 
    specialize (eval_exp_ex_cks_stripped _ _ _ _ _ H); let HZ := fresh "HZ" in intro HZ
  | _ => idtac
  end.
  apply_expression_checks_optimization_soundness; auto.
  specialize (eval_exp_ex_cks_stripped _ _ _ _ _ HZ5); let HZ := fresh "HZ" in intro HZ.
  apply_eval_expr_value_reserve;
  specialize (optimize_exp_ex_cks_eq _ _ _ _ H26); intro HZ8; rewrite exp_updated_exterior_checks in HZ8.
  
  inversion H27; subst.
  + apply Eval_S_Assignment_X with (v:=Int v); auto.
    rewrite HZ8. rewrite exp_updated_exterior_checks. smack.
    apply_store_update_optimization_soundness; auto.
  + apply Eval_S_Assignment_Range_X with (v:=v) (t:=t1) (l:=l) (u:=u); auto.
    apply_optimize_name_ast_num_eq; smack.
    apply_store_update_optimization_soundness; auto.
- (* 7. Eval_S_If_RTE_X *)
  inversion H2; subst;
  inversion H3; subst;
  inversion H4; subst.
  apply Eval_S_If_RTE_X; auto;
  apply_expression_checks_optimization_soundness; auto.
- (* 8. Eval_S_If_True_X *)
  inversion H3; subst;
  inversion H4; subst;
  inversion H5; subst.
  apply Eval_S_If_True_X; auto;
  apply_expression_checks_optimization_soundness; auto.
  combine_well_typed_stack_and_symboltable.
  specialize (IHeval_stmt_x _ _ _ H1 HZ0 H11 H15 H18); auto.
- (* 9. Eval_S_If_False_X *)
  inversion H3; subst;
  inversion H4; subst;
  inversion H5; subst.
  apply Eval_S_If_False_X; auto;
  apply_expression_checks_optimization_soundness; auto.
  combine_well_typed_stack_and_symboltable.
  specialize (IHeval_stmt_x _ _ _ H1 HZ0 H12 H16 H19); auto.
- (* 10. Eval_S_While_Loop_RTE_X *)
  inversion H2; subst;
  inversion H3; subst;
  inversion H4; subst.
  apply Eval_S_While_Loop_RTE_X; auto;
  apply_expression_checks_optimization_soundness; auto.
- (* 11. Eval_S_While_Loop_True_RTE_X *)
  inversion H3; subst;
  inversion H4; subst;
  inversion H5; subst.
  apply Eval_S_While_Loop_True_RTE_X; auto;
  apply_expression_checks_optimization_soundness; auto.
  combine_well_typed_stack_and_symboltable.
  specialize (IHeval_stmt_x _ _ _ H1 HZ0 H10 H13 H15); auto.
- (* 12. Eval_S_While_Loop_True_X *)
  inversion H4; subst;
  inversion H5; subst;
  inversion H6; subst.
  combine_well_typed_stack_and_symboltable.
  apply Eval_S_While_Loop_True_X with (s1:=s1); auto.
  + apply_expression_checks_optimization_soundness; auto.
  + specialize (IHeval_stmt_x1 _ _ _ H2 HZ H11 H14 H16); auto.
  + specialize (IHeval_stmt_x1 _ _ _ H2 HZ H11 H14 H16); auto.
    apply_eval_statement_preserve_typed_stack.
    specialize (IHeval_stmt_x2 _ _ _ H2 HZ0 H4 H5 H6); auto.
- (* 13. Eval_S_While_Loop_False_X *)
  inversion H2; subst;
  inversion H3; subst;
  inversion H4; subst.
  apply Eval_S_While_Loop_False_X; auto;
  apply_expression_checks_optimization_soundness; auto.
- (* 14. Eval_S_Proc_RTE_Args_X *)
  inversion H3; subst;
  inversion H4; subst;
  inversion H5; subst.
  repeat progress match goal with
  | [H1: fetch_proc_x _ _ = _, H2: fetch_proc_x _ _ = _ |- _] => rewrite H2 in H1; inversion H1; subst
  end;
  apply Eval_S_Proc_RTE_Args_X with (n:=n) (pb:=pb); auto.
  specialize (symbol_table_procedure_rel _ _ _ _ _ H1 H13); intro HZ1.
    destruct HZ1 as [pb' [HZ1 HZ2]]. rewrite H15 in HZ1; inversion HZ1; subst.
    inversion HZ2; subst.
  apply_copy_in_args_checks_optimization_soundness; auto.
- (* 15. Eval_S_Proc_RTE_Decl_X *)
  inversion H5; subst;
  inversion H6; subst;
  inversion H7; subst;
  repeat progress match goal with
  | [H1: fetch_proc_x _ _ = _, H2: fetch_proc_x _ _ = _ |- _] => rewrite H2 in H1; inversion H1; subst
  end;
  apply Eval_S_Proc_RTE_Decl_X with (n:=n) (pb:=pb) (f:=f) (intact_s:=intact_s) (s1:=s1); auto.
  specialize (symbol_table_procedure_rel _ _ _ _ _ H3 H15); intro HZ1.
    destruct HZ1 as [pb' [HZ1 HZ2]]. rewrite H17 in HZ1; inversion HZ1; subst.
    inversion HZ2; subst.
  apply_copy_in_args_checks_optimization_soundness; auto.
- (* 16. Eval_S_Proc_RTE_Body_X *)
  inversion H6; subst;
  inversion H7; subst;
  inversion H8; subst;
  repeat progress match goal with
  | [H1: fetch_proc_x _ _ = _, H2: fetch_proc_x _ _ = _ |- _] => rewrite H2 in H1; inversion H1; subst
  end;
  apply Eval_S_Proc_RTE_Body_X with (n:=n) (pb:=pb) (f:=f) (intact_s:=intact_s) (s1:=s1) (f1:=f1); auto.
  specialize (symbol_table_procedure_rel _ _ _ _ _ H4 H16); intro HZ1.
    destruct HZ1 as [pb' [HZ1 HZ2]]. rewrite H18 in HZ1; inversion HZ1; subst.
    inversion HZ2; subst.
  apply_copy_in_args_checks_optimization_soundness; auto.
- (* 17. Eval_S_Proc_X *)
  apply_cut_until_preserve_typed_stack.
  inversion H9; subst;
  inversion H10; subst;
  inversion H11; subst.
  inversion HSymb; subst. inversion H8; subst. specialize (H12 _ _ _ H20). inversion H12; subst.
  specialize (symbol_table_procedure_rel _ _ _ _ _ H7 H16); intro HZ2. 
  destruct HZ2 as [pb' [HZ2 HZ3]]. 
  repeat progress match goal with
  | [H1: fetch_proc_x _ _ = _, H2: fetch_proc_x _ _ = _ |- _] => rewrite H2 in H1; inversion H1; subst
  end;
  apply Eval_S_Proc_X with (n:=n) (pb:=pb) (f:=f) (intact_s:=intact_s) (s1:=s1) (f1:=f1)
                           (s2:=((n, locals_section ++ params_section) :: s3)) 
                           (locals_section:=locals_section) (params_section:=params_section) (s3:=s3); auto;
  inversion HZ3; subst.
  + apply_copy_in_args_checks_optimization_soundness; auto.
  + simpl in *.
    assert(HA: well_typed_value_in_store st (snd (STACK.newFrame n))).
      smack; constructor.
    apply_copy_in_preserve_typed_store.
    apply_eval_declaration_preserve_typed_store.
    assert(HA1: well_typed_value_in_stack st (f1 :: s1)).
      apply_well_typed_store_stack_merge'; auto.
    combine_well_typed_stack_and_symboltable.
    apply_eval_statement_preserve_typed_stack.
    inversion HZ6; subst.
    apply_well_typed_store_stack_split'. simpl in *.
    apply_well_typed_store_split'.
    assert(HA2: well_typed_value_in_stack st (intact_s ++ s3)). apply well_typed_stacks_merge'; auto.
    apply copy_out_args_checks_optimization_soundness with (st:=st0) (params:=params) (args:=args0) (args':=args); auto; simpl in *.
- (* 18. Eval_S_Sequence_RTE_X *)
  inversion H2; subst;
  inversion H3; subst;
  inversion H4; subst;
  apply Eval_S_Sequence_RTE_X; auto.
  combine_well_typed_stack_and_symboltable.
  specialize (IHeval_stmt_x _ _ _ H0 HZ H7 H10 H13); auto.
- (* 19. Eval_S_Sequence_X *)
  inversion H3; subst;
  inversion H4; subst;
  inversion H5; subst;
  apply Eval_S_Sequence_X with (s1:=s1); auto;
  combine_well_typed_stack_and_symboltable;
  specialize (IHeval_stmt_x1 _ _ _ H1 HZ H8 H11 H14); auto.
  
  assert(HA: well_typed_value_in_stack st s1).
    apply_eval_statement_preserve_typed_stack; auto. inversion HZ0; subst; auto.
  combine_well_typed_stack_and_symboltable.
  specialize (IHeval_stmt_x2 _ _ _ H1 HZ0 H10 H13 H15); auto.
Qed.

Ltac apply_statement_checks_optimization_soundness :=
  match goal with
  | [H1: eval_stmt_x ?st' ?s ?c' ?s',
     H2: compile2_flagged_symbol_table ?st ?st',
     H3: well_typed_stack ?st' ?s,
     H4: well_typed_statement_x ?st' ?c',
     H5: compile2_flagged_stmt ?st ?c ?c',
     H6: optimize_statement_x ?st' ?c' ?c'' |- _] =>
      specialize (statement_checks_optimization_soundness _ _ _ _ _ _ _ H1 H2 H3 H4 H5 H6);
      let HZ := fresh "HZ" in intros HZ
  end.

(*
(** * declaration_checks_optimization_soundness1 *)
Lemma declaration_checks_optimization_soundness1: forall st st' s f f' d d' d'',
  eval_decl_x st' s f d' f' ->
    compile2_flagged_symbol_table st st' ->
      well_typed_stack st' s ->
        well_typed_store st' (snd f) ->
          well_typed_decl_x st' d' ->
            compile2_flagged_declaration st d d' ->
              optimize_declaration_x st' d' d'' ->
                eval_decl_x st' s f d'' f'.
Proof.
  intros st st' s f f' d d' d'' H; revert st d d''.
  assert(HA: well_typed_stack st' (f::s)). admit.
  induction H; intros.  
- (* 1. Eval_Decl_Null_X *)
  match goal with
  | [H: optimize_declaration_x _ _ _ |- _] => inversion H; subst; auto
  end;
  constructor.
- (* 2. Eval_Decl_Var_None_X *)
  inversion H5; subst.
  assert(HZ1: object_name_x d = object_name_x o').
    clear - H10. inversion H10; smack. rewrite HZ1.
  apply Eval_Decl_Var_None_X; auto.
    clear - H H10. inversion H10; smack.
- (* 3. Eval_Decl_Var_RTE_X *)
  inversion H4; subst;
  inversion H5; subst;
  inversion H6; subst;
  match goal with
  | [H1: initialization_expression_x _ = _, 
     H2: initialization_expression_x _ = _ |- _] => rewrite H1 in H2; inversion H2; subst
  end.
  inversion H17; smack;
  
  inversion H15; subst; (*H13: compile2_flagged_object_declaration ...*)
  match goal with
  | [H: extract_subtype_range_x _ _ (Range_X _ _) |- _] => 
      specialize (range_constrainted_type_true _ _ _ _ H);
      let HZ := fresh "HZ" in intros HZ
  | _ => idtac
  end;
  match goal with
  | [H1: is_range_constrainted_type ?x = true, 
     H2: is_range_constrainted_type ?y = false |- _] => 
      rewrite H1 in H2; inversion H2
  | _ => idtac
  end.
  + apply Eval_Decl_Var_eRTE_X with (e:=e'); auto.
    apply_expression_checks_optimization_soundness; auto.
  + apply Eval_Decl_Var_eRTE_X with (e:=e''); auto.
    apply eval_expr_value_reserve with (e:=e') (eBound:=(Interval u' v')) (rBound:=(Interval u v)); auto.
    match goal with
    | [H: optimize_expression_x _ _ _ |- _] => 
        specialize (optimize_exp_ex_cks_stripped _ _ _ _ _ H);
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
    | [H: well_typed_exp_x ?st (update_exterior_checks_exp ?e ?cks) |- _] =>
        specialize (well_typed_exp_preserve _ _ _ H);
        let HZ := fresh "HZ" in intro HZ
    | _ => idtac
    end.
    apply_expression_checks_optimization_soundness.
    specialize (eval_exp_ex_cks_stripped _ _ _ _ _ HZ3); auto.
- (* 4. Eval_Decl_Var_X *)
  inversion H5; subst;
  inversion H6; subst;
  inversion H7; subst;
  match goal with
  | [H1: initialization_expression_x _ = _, 
     H2: initialization_expression_x _ = _ |- _] => rewrite H1 in H2; inversion H2; subst
  end.
  inversion H18; smack;
  inversion H16; subst; (*H13: compile2_flagged_object_declaration ...*)
  match goal with
  | [H: extract_subtype_range_x _ _ (Range_X _ _) |- _] => 
      specialize (range_constrainted_type_true _ _ _ _ H);
      let HZ := fresh "HZ" in intros HZ
  | _ => idtac
  end;
  match goal with
  | [H1: is_range_constrainted_type ?x = true, 
     H2: is_range_constrainted_type ?y = false |- _] => 
      rewrite H1 in H2; inversion H2
  | [H: exp_exterior_checks (update_exterior_checks_exp _ _) = _ |- _] =>
      rewrite exp_updated_exterior_checks in H; inversion H; subst
  | _ => idtac
  end.
  apply Eval_Decl_Var_NoCheck_X with (e:=e'); auto.
  apply_expression_checks_optimization_soundness; auto.
  apply_optimize_exp_ex_cks_eq; smack.
- (* 5. Eval_Decl_Var_E_RTE_X *)
  inversion H7; subst;
  inversion H8; subst;
  inversion H9; subst;
  match goal with
  | [H1: initialization_expression_x _ = _, 
     H2: initialization_expression_x _ = _ |- _] => rewrite H1 in H2; inversion H2; subst
  end.
  inversion H20; smack;
  inversion H18; subst; (*H13: compile2_flagged_object_declaration ...*)
  match goal with
  | [H: extract_subtype_range_x _ _ (Range_X _ _) |- _] => 
      specialize (range_constrainted_type_true _ _ _ _ H);
      let HZ := fresh "HZ" in intros HZ
  | _ => idtac
  end;
  match goal with
  | [H1: is_range_constrainted_type ?x = true, 
     H2: is_range_constrainted_type ?y = false |- _] => 
      rewrite H1 in H2; inversion H2
  | [H: exp_exterior_checks (update_exterior_checks_exp _ _) = _ |- _] =>
      rewrite exp_updated_exterior_checks in H; inversion H; subst
  | _ => idtac
  end.
  apply_extract_subtype_range_unique.
  match goal with
  | [H: optimize_expression_x _ _ _ |- _] => 
      specialize (optimize_exp_ex_cks_stripped _ _ _ _ _ H);
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
  | [H: well_typed_exp_x ?st (update_exterior_checks_exp ?e ?cks) |- _] =>
      specialize (well_typed_exp_preserve _ _ _ H);
      let HZ := fresh "HZ" in intro HZ
  | _ => idtac
  end.

  apply Eval_Decl_Var_Range_RTE_X with (e:=e'') (v:=v) (l:=l) (u:=u); auto.
  apply eval_expr_value_reserve with (e:=e') (eBound:=(Interval u' v')) (rBound:=(Interval l u)); auto.
  apply_expression_checks_optimization_soundness.
  specialize (eval_exp_ex_cks_stripped _ _ _ _ _ HZ3); auto.
  
  apply_eval_expr_value_in_bound.
  inversion H3; subst.
  specialize (optimize_exp_ex_cks_eq _ _ _ _ H11); intro HZ4.
  rewrite exp_updated_exterior_checks in HZ4.
  apply_optimize_range_check_reserve; smack.
- (* 6. Eval_Decl_Var_Range_RTE_X *)
  inversion H7; subst;
  inversion H8; subst;
  inversion H9; subst;
  match goal with
  | [H1: initialization_expression_x _ = _, 
     H2: initialization_expression_x _ = _ |- _] => rewrite H1 in H2; inversion H2; subst
  end.
  inversion H20; smack;
  inversion H18; subst; (*H13: compile2_flagged_object_declaration ...*)
  match goal with
  | [H: extract_subtype_range_x _ _ (Range_X _ _) |- _] => 
      specialize (range_constrainted_type_true _ _ _ _ H);
      let HZ := fresh "HZ" in intros HZ
  | _ => idtac
  end;
  match goal with
  | [H1: is_range_constrainted_type ?x = true, 
     H2: is_range_constrainted_type ?y = false |- _] => 
      rewrite H1 in H2; inversion H2
  | [H: exp_exterior_checks (update_exterior_checks_exp _ _) = _ |- _] =>
      rewrite exp_updated_exterior_checks in H; inversion H; subst
  | _ => idtac
  end.
  apply_extract_subtype_range_unique.
  match goal with
  | [H: optimize_expression_x _ _ _ |- _] => 
      specialize (optimize_exp_ex_cks_stripped _ _ _ _ _ H);
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
  | [H: well_typed_exp_x ?st (update_exterior_checks_exp ?e ?cks) |- _] =>
      specialize (well_typed_exp_preserve _ _ _ H);
      let HZ := fresh "HZ" in intro HZ
  | _ => idtac
  end.
  clear H7 H20 H9 H18 H8.
  inversion H15; subst.
  + specialize (optimize_exp_ex_cks_eq _ _ _ _ H11); intros HZ3.
    rewrite exp_updated_exterior_checks in HZ3. rewrite HZ3; smack.
    apply Eval_Decl_Var_NoCheck_X with (e:=(update_exterior_checks_exp e' nil)); auto.
    apply_expression_checks_optimization_soundness.
    specialize (exp_exterior_checks_beq_nil _ _ _ H26); intros HZ5. rewrite HZ5 in HZ4. assumption.
    rewrite exp_updated_exterior_checks; auto.
  + apply Eval_Decl_Var_X with (e:=e'') (v:=v) (l:=l) (u:=u); auto.
    apply_expression_checks_optimization_soundness.
    specialize (eval_exp_ex_cks_stripped _ _ _ _ _ HZ3); auto.
    specialize (optimize_exp_ex_cks_eq _ _ _ _ H11); intros HZ3.
    rewrite exp_updated_exterior_checks in HZ3; auto.
- (* 7. Eval_Decl_Type_X *)  
  match goal with
  | [H: optimize_declaration_x _ _ _ |- _] => inversion H; subst; auto
  end;
  apply Eval_Decl_Type_X; auto.  
- (* 8. Eval_Decl_Proc_X *)
  match goal with
  | [H: optimize_declaration_x _ _ _ |- _] => inversion H; subst; auto
  end;
  apply Eval_Decl_Proc_X; auto.
- (* 9. Eval_Decl_Seq_E_X *)
  inversion H3; subst;
  inversion H4; subst;
  inversion H5; subst.
  specialize (IHeval_decl_x HA _ _ _ H0 H1 H2 H9 H12 H15).
  apply Eval_Decl_Seq_E_X; auto.  
- (* 10. Eval_Decl_Seq_X *)
  inversion H4; subst;
  inversion H5; subst;
  inversion H6; subst.
  specialize (IHeval_decl_x1 HA _ _ _ H1 H2 H3 H10 H13 H16).
  assert(HA1: well_typed_store st (snd f')). admit.
  assert(HA2: well_typed_stack st (f' :: s)). admit.
  specialize (IHeval_decl_x2 HA2 _ _ _ H1 H2 HA1 H12 H15 H17).
  apply Eval_Decl_Seq_X with (f':=f'); auto.  
Qed.

Ltac apply_declaration_checks_optimization_soundness1 :=
  match goal with
  | [H1: eval_decl_x ?st' ?s ?f ?d' ?f',
     H2: compile2_flagged_symbol_table ?st ?st',
     H3: well_typed_stack ?st' ?s,
     H4: well_typed_store ?st' (snd ?f),
     H5: well_typed_decl_x ?st' ?d',
     H6: compile2_flagged_declaration ?st ?d ?d',
     H7: optimize_declaration_x ?st' ?d' ?d'' |- _] =>
      specialize (declaration_checks_optimization_soundness1 _ _ _ _ _ _ _ _ H1 H2 H3 H4 H5 H6 H7);
      let HZ := fresh "HZ" in intros HZ
  end.
*)

(** * declaration_checks_optimization_soundness2 *)
Lemma declaration_checks_optimization_soundness: forall st st' s f f' d d' d'',
  eval_decl_x st' s f d' f' ->
    compile2_flagged_symbol_table st st' ->
      well_typed_symbol_table st' ->
        well_typed_value_in_stack st' (f::s) ->
          well_typed_decl_x st' d' ->
            compile2_flagged_declaration st d d' ->
              optimize_declaration_x st' d' d'' ->
                eval_decl_x st' s f d'' f'.
Proof.
  intros st st' s f f' d d' d'' H; revert st d d'';
  induction H; intros;
  match goal with
  | [H: well_typed_value_in_stack ?st ?s |- _] =>
      specialize (well_typed_stack_infer _ _ H);
      let HB := fresh "HB" in intros HB
  end.
- (* 1. Eval_Decl_Null_X *)
  match goal with
  | [H: optimize_declaration_x _ _ _ |- _] => inversion H; subst; auto
  end;
  constructor.
- (* 2. Eval_Decl_Var_None_X *)
  inversion H5; subst.
  assert(HZ1: object_name_x d = object_name_x o').
    clear - H10. inversion H10; smack. rewrite HZ1.
  apply Eval_Decl_Var_None_X; auto.
  inversion H10; smack.
- (* 3. Eval_Decl_Var_RTE_X *)
  inversion H4; subst;
  inversion H5; subst;
  inversion H6; subst;
  match goal with
  | [H1: initialization_expression_x _ = _, 
     H2: initialization_expression_x _ = _ |- _] => rewrite H1 in H2; inversion H2; subst
  end.
  inversion H17; smack;
  
  inversion H15; subst; (*H13: compile2_flagged_object_declaration ...*)
  match goal with
  | [H: extract_subtype_range_x _ _ (Range_X _ _) |- _] => 
      specialize (range_constrainted_type_true _ _ _ _ H);
      let HZ := fresh "HZ" in intros HZ
  | _ => idtac
  end;
  match goal with
  | [H1: is_range_constrainted_type ?x = true, 
     H2: is_range_constrainted_type ?y = false |- _] => 
      rewrite H1 in H2; inversion H2
  | _ => idtac
  end.
  + apply Eval_Decl_Var_eRTE_X with (e:=e'); auto.
    apply_expression_checks_optimization_soundness; auto.
  + apply Eval_Decl_Var_eRTE_X with (e:=e''); auto.
    apply eval_expr_value_reserve with (e:=e') (eBound:=(Interval u' v')) (rBound:=(Interval u v)); auto.
    match goal with
    | [H: optimize_expression_x _ _ _ |- _] => 
        specialize (optimize_exp_ex_cks_stripped _ _ _ _ _ H);
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
    | [H: well_typed_exp_x ?st (update_exterior_checks_exp ?e ?cks) |- _] =>
        specialize (well_typed_exp_preserve _ _ _ H);
        let HZ := fresh "HZ" in intro HZ
    | _ => idtac
    end.
    apply_expression_checks_optimization_soundness.
    specialize (eval_exp_ex_cks_stripped _ _ _ _ _ HZ3); auto.
- (* 4. Eval_Decl_Var_X *)
  inversion H5; subst;
  inversion H6; subst;
  inversion H7; subst;
  match goal with
  | [H1: initialization_expression_x _ = _, 
     H2: initialization_expression_x _ = _ |- _] => rewrite H1 in H2; inversion H2; subst
  end.
  inversion H18; smack;
  inversion H16; subst; (*H13: compile2_flagged_object_declaration ...*)
  match goal with
  | [H: extract_subtype_range_x _ _ (Range_X _ _) |- _] => 
      specialize (range_constrainted_type_true _ _ _ _ H);
      let HZ := fresh "HZ" in intros HZ
  | _ => idtac
  end;
  match goal with
  | [H1: is_range_constrainted_type ?x = true, 
     H2: is_range_constrainted_type ?y = false |- _] => 
      rewrite H1 in H2; inversion H2
  | [H: exp_exterior_checks (update_exterior_checks_exp _ _) = _ |- _] =>
      rewrite exp_updated_exterior_checks in H; inversion H; subst
  | _ => idtac
  end.
  apply Eval_Decl_Var_NoCheck_X with (e:=e'); auto.
  apply_expression_checks_optimization_soundness; auto.
  apply_optimize_exp_ex_cks_eq; smack.
- (* 5. Eval_Decl_Var_E_RTE_X *)
  inversion H7; subst;
  inversion H8; subst;
  inversion H9; subst;
  match goal with
  | [H1: initialization_expression_x _ = _, 
     H2: initialization_expression_x _ = _ |- _] => rewrite H1 in H2; inversion H2; subst
  end.
  inversion H20; smack;
  inversion H18; subst; (*H13: compile2_flagged_object_declaration ...*)
  match goal with
  | [H: extract_subtype_range_x _ _ (Range_X _ _) |- _] => 
      specialize (range_constrainted_type_true _ _ _ _ H);
      let HZ := fresh "HZ" in intros HZ
  | _ => idtac
  end;
  match goal with
  | [H1: is_range_constrainted_type ?x = true, 
     H2: is_range_constrainted_type ?y = false |- _] => 
      rewrite H1 in H2; inversion H2
  | [H: exp_exterior_checks (update_exterior_checks_exp _ _) = _ |- _] =>
      rewrite exp_updated_exterior_checks in H; inversion H; subst
  | _ => idtac
  end.
  apply_extract_subtype_range_unique.
  match goal with
  | [H: optimize_expression_x _ _ _ |- _] => 
      specialize (optimize_exp_ex_cks_stripped _ _ _ _ _ H);
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
  | [H: well_typed_exp_x ?st (update_exterior_checks_exp ?e ?cks) |- _] =>
      specialize (well_typed_exp_preserve _ _ _ H);
      let HZ := fresh "HZ" in intro HZ
  | _ => idtac
  end.

  apply Eval_Decl_Var_Range_RTE_X with (e:=e'') (v:=v) (l:=l) (u:=u); auto.
  apply eval_expr_value_reserve with (e:=e') (eBound:=(Interval u' v')) (rBound:=(Interval l u)); auto.
  apply_expression_checks_optimization_soundness.
  specialize (eval_exp_ex_cks_stripped _ _ _ _ _ HZ3); auto.
  
  apply_eval_expr_value_in_bound.
  inversion H3; subst.
  specialize (optimize_exp_ex_cks_eq _ _ _ _ H11); intro HZ4.
  rewrite exp_updated_exterior_checks in HZ4.
  apply_optimize_range_check_reserve; smack.
- (* 6. Eval_Decl_Var_Range_RTE_X *)
  inversion H7; subst;
  inversion H8; subst;
  inversion H9; subst;
  match goal with
  | [H1: initialization_expression_x _ = _, 
     H2: initialization_expression_x _ = _ |- _] => rewrite H1 in H2; inversion H2; subst
  end.
  inversion H20; smack;
  inversion H18; subst; (*H13: compile2_flagged_object_declaration ...*)
  match goal with
  | [H: extract_subtype_range_x _ _ (Range_X _ _) |- _] => 
      specialize (range_constrainted_type_true _ _ _ _ H);
      let HZ := fresh "HZ" in intros HZ
  | _ => idtac
  end;
  match goal with
  | [H1: is_range_constrainted_type ?x = true, 
     H2: is_range_constrainted_type ?y = false |- _] => 
      rewrite H1 in H2; inversion H2
  | [H: exp_exterior_checks (update_exterior_checks_exp _ _) = _ |- _] =>
      rewrite exp_updated_exterior_checks in H; inversion H; subst
  | _ => idtac
  end.
  apply_extract_subtype_range_unique.
  match goal with
  | [H: optimize_expression_x _ _ _ |- _] => 
      specialize (optimize_exp_ex_cks_stripped _ _ _ _ _ H);
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
  | [H: well_typed_exp_x ?st (update_exterior_checks_exp ?e ?cks) |- _] =>
      specialize (well_typed_exp_preserve _ _ _ H);
      let HZ := fresh "HZ" in intro HZ
  | _ => idtac
  end.
  clear H7 H20 H9 H18 H8.
  inversion H15; subst.
  + specialize (optimize_exp_ex_cks_eq _ _ _ _ H11); intros HZ3.
    rewrite exp_updated_exterior_checks in HZ3. rewrite HZ3; smack.
    apply Eval_Decl_Var_NoCheck_X with (e:=(update_exterior_checks_exp e' nil)); auto.
    apply_expression_checks_optimization_soundness.
    specialize (exp_exterior_checks_beq_nil _ _ _ H26); intros HZ5. rewrite HZ5 in HZ4. assumption.
    rewrite exp_updated_exterior_checks; auto.
  + apply Eval_Decl_Var_X with (e:=e'') (v:=v) (l:=l) (u:=u); auto.
    apply_expression_checks_optimization_soundness.
    specialize (eval_exp_ex_cks_stripped _ _ _ _ _ HZ3); auto.
    specialize (optimize_exp_ex_cks_eq _ _ _ _ H11); intros HZ3.
    rewrite exp_updated_exterior_checks in HZ3; auto.
- (* 7. Eval_Decl_Type_X *)  
  match goal with
  | [H: optimize_declaration_x _ _ _ |- _] => inversion H; subst; auto
  end;
  apply Eval_Decl_Type_X; auto.  
- (* 8. Eval_Decl_Proc_X *)
  match goal with
  | [H: optimize_declaration_x _ _ _ |- _] => inversion H; subst; auto
  end;
  apply Eval_Decl_Proc_X; auto.
- (* 9. Eval_Decl_Seq_E_X *)
  inversion H3; subst;
  inversion H4; subst;
  inversion H5; subst.
  specialize (IHeval_decl_x _ _ _ H0 H1 H2 H9 H12 H15).
  apply Eval_Decl_Seq_E_X; auto.  
- (* 10. Eval_Decl_Seq_X *)
  inversion H4; subst;
  inversion H5; subst;
  inversion H6; subst.
  specialize (IHeval_decl_x1 _ _ _ H1 H2 H3 H10 H13 H16).
  assert(HZ: well_typed_value_in_stack st (f' :: s)). 
    apply_well_typed_store_stack_split'.
    apply_eval_declaration_preserve_typed_store.
    apply well_typed_store_stack_merge'; auto.
  specialize (IHeval_decl_x2 _ _ _ H1 H2 HZ H12 H15 H17).
  apply Eval_Decl_Seq_X with (f':=f'); auto.  
Qed.

Ltac apply_declaration_checks_optimization_soundness2 :=
  match goal with
  | [H1: eval_decl_x ?st' ?s ?f ?d' ?f',
     H2: compile2_flagged_symbol_table ?st ?st',
     H3: well_typed_symbol_table ?st', 
     H4: well_typed_stack ?st' (?f::?s),
     H5: well_typed_decl_x ?st' ?d',
     H6: compile2_flagged_declaration ?st ?d ?d',
     H7: optimize_declaration_x ?st' ?d' ?d'' |- _] =>
      specialize (declaration_checks_optimization_soundness _ _ _ _ _ _ _ _ H1 H2 H3 H4 H5 H6 H7);
      let HZ := fresh "HZ" in intros HZ
  end.


(*---------------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------------*)
(*----------------------------------  END ! ---------------------------------------*)
(*---------------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------------*)

