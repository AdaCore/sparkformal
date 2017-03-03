(** 
_AUTHOR_

<<
Zhi Zhang
Department of Computer and Information Sciences
Kansas State University
zhangzhi@ksu.edu
>>
*)

Require Export rt_opt_consistent_util.

Scheme expression_ind := Induction for exp Sort Prop 
                         with name_ind := Induction for name Sort Prop.

Scheme expression_x_ind := Induction for expRT Sort Prop 
                         with name_x_ind := Induction for nameRT Sort Prop.


Ltac apply_copy_out_opt_H :=
  match goal with
  | [H1: forall (st : symTab) (st' : symTabRT)
                (s : STACK.state) (f : STACK.scope_level * STACK.store)
                (s' : Ret STACK.state)
                (params : list paramSpec)
                (args : list exp) (args' args'' : list expRT),
              toArgsRT st params args args' ->
              toSymTabRT st st' ->
              toParamSpecsRT params ?params' ->
              well_typed_symbol_table st' ->
              well_typed_value_in_stack st' s ->
              well_typed_value_in_store st' (snd f) ->
              well_typed_exps_x st' args' ->
              well_typed_params_x st' ?params' ->
              well_typed_args_x st' args' ?params' ->
              optArgs st' ?params' args' args'' ->
              copyOutRT st' s f ?params' args' s' ->
              copyOutRT st' s f ?params' args'' s',
     H2: toArgsRT ?st ?params ?args ?args', 
     H3: toSymTabRT ?st ?st',
     H4: toParamSpecsRT ?params ?params',
     H5: well_typed_symbol_table ?st',
     H6: well_typed_value_in_stack ?st' ?s,
     H7: well_typed_value_in_store ?st' (snd ?f),
     H8: well_typed_exps_x ?st' ?args',
     H9: well_typed_params_x ?st' ?params',
     H10: well_typed_args_x ?st' ?args' ?params', 
     H11: optArgs ?st' ?params' ?args' ?args'',
     H12: copyOutRT ?st' ?s ?f ?params' ?args' ?s' |- _ ] =>
      specialize (H1 _ _ _ _ _ _ _ _ _ H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12)
  end.

(** * Soundness of RT-OPT Specification *)

(** ** optArgs_copyout_soundness *)
Lemma optArgs_copyout_soundness: forall st params args args' params' st' s f s' args'',
  toArgsRT st params args args' ->
  toSymTabRT st st' ->
  toParamSpecsRT params params' ->
  well_typed_symbol_table st' ->
  well_typed_value_in_stack st' s ->
  well_typed_value_in_store st' (snd f) -> (* Definition frame := prod scope_level store. *)
  well_typed_exps_x st' args' ->
  well_typed_params_x st' params' ->
  well_typed_args_x st' args' params' ->
  optArgs st' params' args' args'' ->
  copyOutRT st' s f params' args'' s' ->
  copyOutRT st' s f params' args' s'.
Proof.
 intros st params args args' params' st' s f s' args'' H.
 revert params' st' s f s' args''.
 induction H; intros.
- (* C2_Flagged_Args_Null *)
 inversion H7; subst; auto.
- (* C2_Flagged_Args_In *)
 inversion H4; subst;
 inversion H8; subst;
 inversion H9; subst;
 inversion H10; subst.
 assert(HZ1: param.(parameter_mode) = paramRT.(parameter_mode_rt) /\ 
            (parameter_subtype_mark param) = (parameter_subtype_mark_rt paramRT)).
 match goal with
 | [H: toParamSpecRT ?param ?paramRT |- _] => clear - H; inversion H; smack
 end. destruct HZ1 as [HZ1a HZ1b].
 inversion H11; subst;
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
 | [H1: is_range_constrainted_type ?x = _, 
    H2: is_range_constrainted_type ?y = _,
    H3: ?x = ?y |- _] => 
     rewrite H3 in H1; rewrite H1 in H2; inversion H2
 | _ => idtac
 end.
 inversion H12; subst;
 match goal with
 | [H1: parameter_mode_rt ?a = _ ,
    H2: parameter_mode_rt ?a = _ |- _] => rewrite H2 in H1; inversion H1 
 | [H1: parameter_mode_rt ?a = In ,
    H2: parameter_mode_rt ?a = Out \/ parameter_mode_rt ?a = In_Out |- _] => 
     rewrite H1 in H2; clear - H2; smack
 | _ => idtac
 end.
 apply CopyOut_Mode_In_X; auto;
 apply IHtoArgsRT with (args'' := args'); auto.
- (* C2_Flagged_Args_In_RangeCheck *)
 inversion H4; subst;
 inversion H8; subst;
 inversion H9; subst;
 inversion H10; subst.
 assert(HZ1: param.(parameter_mode) = paramRT.(parameter_mode_rt) /\ 
            (parameter_subtype_mark param) = (parameter_subtype_mark_rt paramRT)).
 match goal with
 | [H: toParamSpecRT ?param ?paramRT |- _] => clear - H; inversion H; smack
 end. destruct HZ1 as [HZ1a HZ1b].
 inversion H11; subst;
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
 | [H1: is_range_constrainted_type ?x = _, 
    H2: is_range_constrainted_type ?y = _,
    H3: ?x = ?y |- _] => 
     rewrite H3 in H1; rewrite H1 in H2; inversion H2
 | _ => idtac
 end.
 inversion H12; subst;
 match goal with
 | [H1: parameter_mode_rt ?a = _ ,
    H2: parameter_mode_rt ?a = _ |- _] => rewrite H2 in H1; inversion H1 
 | [H1: parameter_mode_rt ?a = In ,
    H2: parameter_mode_rt ?a = Out \/ parameter_mode_rt ?a = In_Out |- _] => 
     rewrite H1 in H2; clear - H2; smack
 | _ => idtac
 end.
 apply CopyOut_Mode_In_X; auto;
 apply IHtoArgsRT with (args'' := args'); auto.
-(* C2_Flagged_Args_Out *)
 inversion H5; subst;
 inversion H9; subst;
 inversion H10; subst;
 inversion H11; subst.
 match goal with
 | [H: well_typed_value_in_stack _ _ |- _] => 
     specialize (well_typed_stack_infer _ _ H); let HB := fresh "HB" in intro HB
 end;
 match goal with
 | [H: well_typed_value_in_store _ _ |- _] => 
     specialize (well_typed_store_infer _ _ H); let HB := fresh "HB" in intro HB
 end.
 assert(HZ1: param.(parameter_mode) = paramRT.(parameter_mode_rt) /\ 
            (parameter_subtype_mark param) = (parameter_subtype_mark_rt paramRT)).
 match goal with
 | [H: toParamSpecRT ?param ?paramRT |- _] => clear - H; inversion H; smack
 end. destruct HZ1 as [HZ1a HZ1b].
 inversion H12; subst;
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
 | [H1: is_range_constrainted_type ?x = _, 
    H2: is_range_constrainted_type ?y = _,
    H3: ?x = ?y |- _] => 
     rewrite H3 in H1; rewrite H1 in H2; inversion H2
 | _ => idtac
 end;
 inversion H13; subst;
 match goal with
 | [H1: parameter_mode_rt ?a = _ ,
    H2: parameter_mode_rt ?a = _ |- _] => rewrite H2 in H1; inversion H1 
 | [H1: parameter_mode_rt ?a = In ,
    H2: parameter_mode_rt ?a = Out \/ parameter_mode_rt ?a = In_Out |- _] => 
     rewrite H1 in H2; clear - H2; smack
 | _ => idtac
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
 repeat progress match goal with
 | [H1: fetch_exp_type_rt ?x ?st = _, 
    H2: fetch_exp_type_rt ?x ?st = _ |- _] => rewrite H1 in H2; inversion H2; subst
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
 | [H1: extract_subtype_range_rt _ ?t _, 
    H2: extract_subtype_range_rt _ ?t _ |- _] => 
     specialize (extract_subtype_range_unique _ _ _ _ _ _ H1 H2);
     let HZ := fresh "HZ" in intro HZ; destruct HZ; subst
 | _ => idtac
 end;
 match goal with
 | [H: optName _ _ _ |- _] => 
     specialize (optimize_name_ex_cks_eq _ _ _ _ H);
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
 | [H: parameter_mode_rt _ = In |- _] => apply CopyOut_Mode_In_X; auto
 | _ => idtac
 end; simpl in *. 
 (* - subcase 1: CopyOut_Mode_Out_nRTE_X *)
 apply CopyOut_Mode_Out_nRTE_X with (v:=v); auto.
 rewrite <- HZ0; auto.
 apply_storeUpdateRT_opt_soundness'; auto.
 (* - subcase 2: CopyOut_Mode_Out_NoRange_X *)
 apply CopyOut_Mode_Out_NoRange_X with (v:=v) (s':=s'0); auto.
 rewrite <- HZ0; auto.
 apply_storeUpdateRT_opt_soundness'; auto. 
 apply IHtoArgsRT with (args'' := args'); auto.
   repeat progress match goal with
   | [H1: fetch_exp_type_rt ?x ?y = _, H2: fetch_exp_type_rt ?x ?y = _ |- _] => rewrite H1 in H2; inversion H2; subst
   end.
   apply_well_typed_value_in_store_fetch.
   apply_value_well_typed_with_matched_type.
   match goal with 
   | [H: Some ?t = fetch_exp_type_rt (name_astnum_rt ?n_flagged) ?st |- _] => symmetry in H
   end.
   apply_storeUpdateRT_opt_soundness; auto.
   apply_storeUpdate_with_typed_value_preserve_typed_stack; auto.
-(* C2_Flagged_Args_Out_RangeCheck *)
 inversion H5; subst;
 inversion H9; subst;
 inversion H10; subst;
 inversion H11; subst.
 match goal with
 | [H: well_typed_value_in_stack _ _ |- _] => 
     specialize (well_typed_stack_infer _ _ H); let HB := fresh "HB" in intro HB
 end;
 match goal with
 | [H: well_typed_value_in_store _ _ |- _] => 
     specialize (well_typed_store_infer _ _ H); let HB := fresh "HB" in intro HB
 end.
 assert(HZ1: param.(parameter_mode) = paramRT.(parameter_mode_rt) /\ 
            (parameter_subtype_mark param) = (parameter_subtype_mark_rt paramRT)).
 match goal with
 | [H: toParamSpecRT ?param ?paramRT |- _] => clear - H; inversion H; smack
 end. destruct HZ1 as [HZ1a HZ1b].
 inversion H12; subst;
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
 | [H1: is_range_constrainted_type ?x = _, 
    H2: is_range_constrainted_type ?y = _,
    H3: ?x = ?y |- _] => 
     rewrite H3 in H1; rewrite H1 in H2; inversion H2
 | _ => idtac
 end;
 inversion H13; subst;
 match goal with
 | [H1: parameter_mode_rt ?a = _ ,
    H2: parameter_mode_rt ?a = _ |- _] => rewrite H2 in H1; inversion H1 
 | [H1: parameter_mode_rt ?a = In ,
    H2: parameter_mode_rt ?a = Out \/ parameter_mode_rt ?a = In_Out |- _] => 
     rewrite H1 in H2; clear - H2; smack
 | _ => idtac
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
 repeat progress match goal with
 | [H1: fetch_exp_type_rt ?x ?st = _, 
    H2: fetch_exp_type_rt ?x ?st = _ |- _] => rewrite H1 in H2; inversion H2; subst
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
 | [H1: extract_subtype_range_rt _ ?t _, 
    H2: extract_subtype_range_rt _ ?t _ |- _] => 
     specialize (extract_subtype_range_unique _ _ _ _ _ _ H1 H2);
     let HZ := fresh "HZ" in intro HZ; destruct HZ; subst
 | _ => idtac
 end;
 match goal with
 | [H: optName _ _ _ |- _] => 
     specialize (optimize_name_ex_cks_eq _ _ _ _ H);
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
 | [H: parameter_mode_rt _ = In |- _] => apply CopyOut_Mode_In_X; auto
 | _ => idtac
 end; simpl in *. 
 (* - subcase 1: CopyOut_Mode_Out_nRTE_X *)
 apply_well_typed_bounded_var_exists_int_value.
 assert (HA1: sub_bound (Interval u v) (Interval u' v') true). 
   match goal with
   | [H: optimize_range_check_on_copy_out _ _ _ _ |- _] => inversion H; subst; auto
   end.
   (* not optmize the Do_Range_Check_On_CopyOut *)
   (* conflict: Do_Range_Check_On_CopyOut is in and not in the n0 *)
   match goal with
   | [H1: ~ List.In RangeCheckOnReturn (name_exterior_checks ?n0),
      H2: name_exterior_checks ?n0 = name_exterior_checks _ |- _] => 
       rewrite name_updated_exterior_checks in H2; rewrite H2 in H1; clear - H1; smack
   end.
 assert (HA2: in_bound x (Interval u' v') true). 
    apply_well_typed_var_in_bound.
    apply_In_Bound_SubBound_Trans; auto.

 apply CopyOut_Mode_Out_Range_nRTE_X with (v:=x) (l:=u') (u:=v') (t:=t); auto.
 rewrite name_updated_exterior_checks; smack.
 constructor; auto.
 apply_store_update_ex_cks_added.
 apply_optimize_range_check_on_copy_out_reserve_storeUpdate_backward.
 apply storeUpdateRT_opt_soundness 
   with (n:=nm) (st:=st) (n'':=update_exterior_checks_name n' (name_exterior_checks nRT)) (nBound:=nBound); auto.
 apply_store_update_ex_cks_added; auto.
 (* - subcase 2: CopyOut_Mode_Out_NoRange_X *)
 apply_well_typed_bounded_var_exists_int_value.
 assert (HA1: sub_bound (Interval u v) (Interval u' v') true). 
   match goal with
   | [H: optimize_range_check_on_copy_out _ _ _ _ |- _] => inversion H; subst; auto
   end.
   (* not optmize the RangeCheckOnReturn *)
   (* conflict: RangeCheckOnReturn is in and not in the n0 *)
   match goal with
   | [H1: ~ List.In RangeCheckOnReturn (name_exterior_checks ?n0),
      H2: name_exterior_checks ?n0 = name_exterior_checks _ |- _] => 
       rewrite name_updated_exterior_checks in H2; rewrite H2 in H1; clear - H1; smack
   end.
 assert (HA2: in_bound x (Interval u' v') true). 
    apply_well_typed_var_in_bound.
    apply_In_Bound_SubBound_Trans; auto.
 apply CopyOut_Mode_Out_Range_X with (v:=x) (t:=t) (l:=u') (u:=v') (s':=s'0); auto.
 rewrite name_updated_exterior_checks; smack.
 constructor; auto.
 apply_store_update_ex_cks_added.
 apply_optimize_range_check_on_copy_out_reserve_storeUpdate_backward.
 apply storeUpdateRT_opt_soundness 
   with (n:=nm) (st:=st) (n'':=update_exterior_checks_name n' (name_exterior_checks nRT)) (nBound:=nBound); auto.
 apply_store_update_ex_cks_added; auto.
 apply IHtoArgsRT with (args'' := args'); auto.
 apply_optimize_range_check_on_copy_out_reserve_storeUpdate_backward.
 assert(HA3: storeUpdateRT st' s (update_exterior_checks_name n' (name_exterior_checks nRT)) (Int x) (OK s'0)).
   apply_store_update_ex_cks_added; auto.
 apply_storeUpdateRT_opt_soundness.
 apply storeUpdate_with_typed_value_preserve_typed_stack with (st0:=st) (x0:=nm) (x:=nRT) (s:=s) (t:=t) (v:=Int x); auto.
   match goal with 
   | [H: context[fetch_exp_type_rt (name_astnum_rt ?nRT) ?st] |- _] => 
       rewrite update_exterior_checks_name_astnum_eq in H; smack
   end.
   apply_well_typed_value_of_var.
   apply_well_typed_value_subtype_trans; auto.
 (* - subcase 3: CopyOut_Mode_Out_Range_RTE_X *)
 apply CopyOut_Mode_Out_Range_RTE_X with (v:=v0) (l:=u') (u:=v') (t:=t); auto.
 rewrite name_updated_exterior_checks; smack.
 assert(HA: n = n0). 
   clear -H35; inversion H35; subst; smack.
 subst. rewrite H40 in H31; inversion H31; subst;
 match goal with
  | [H1: extract_subtype_range_rt _ ?t _, 
     H2: extract_subtype_range_rt _ ?t _ |- _] => 
      specialize (extract_subtype_range_unique _ _ _ _ _ _ H1 H2);
      let HZ := fresh "HZ" in intro HZ; destruct HZ; subst; auto
 end.
 (* - subcase 4: CopyOut_Mode_Out_Range_nRTE_X *)
 apply CopyOut_Mode_Out_Range_nRTE_X with (v:=v0) (t:=t) (l:=u') (u:=v'); auto.
 rewrite name_updated_exterior_checks; smack.
 assert(HA: n = n0). 
   clear -H35; inversion H35; subst; smack.
 subst. rewrite H40 in H31; inversion H31; subst;
 match goal with
  | [H1: extract_subtype_range_rt _ ?t _, 
     H2: extract_subtype_range_rt _ ?t _ |- _] => 
      specialize (extract_subtype_range_unique _ _ _ _ _ _ H1 H2);
      let HZ := fresh "HZ" in intro HZ; destruct HZ; subst; auto
 end.
 apply_store_update_ex_cks_added.
 apply_optimize_range_check_on_copy_out_reserve_storeUpdate_backward.
 apply storeUpdateRT_opt_soundness 
   with (n:=nm) (st:=st) (n'':=update_exterior_checks_name n' (name_exterior_checks nRT)) (nBound:=nBound); auto.
 apply_store_update_ex_cks_added; auto.
 (* - subcase 5: CopyOut_Mode_Out_Range_X *)
 assert(HA: n = n0). 
   clear -H35; inversion H35; subst; smack.
 apply CopyOut_Mode_Out_Range_X with (v:=v0) (t:=t) (l:=u') (u:=v') (s':=s'0); subst; auto. 
 rewrite name_updated_exterior_checks; smack.
 rewrite H37 in H31; inversion H31; subst;
 match goal with
  | [H1: extract_subtype_range_rt _ ?t _, 
     H2: extract_subtype_range_rt _ ?t _ |- _] => 
      specialize (extract_subtype_range_unique _ _ _ _ _ _ H1 H2);
      let HZ := fresh "HZ" in intro HZ; destruct HZ; subst; auto
 end.
 apply_store_update_ex_cks_added. 
 apply_optimize_range_check_on_copy_out_reserve_storeUpdate_backward.
 apply storeUpdateRT_opt_soundness 
   with (n:=nm) (st:=st) (n'':=update_exterior_checks_name n' (name_exterior_checks nRT)) (nBound:=nBound); auto.
 apply_store_update_ex_cks_added; auto. 
 
 apply IHtoArgsRT with (args'' := args'); auto.
 apply_optimize_range_check_on_copy_out_reserve_storeUpdate_backward.
 assert(HA3: storeUpdateRT st' s (update_exterior_checks_name n' (name_exterior_checks nRT)) (Int v0) (OK s'0)).
   apply_store_update_ex_cks_added; auto.
 apply_storeUpdateRT_opt_soundness.
 apply storeUpdate_with_typed_value_preserve_typed_stack with (st0:=st) (x0:=nm) (x:=nRT) (s:=s) (t:=t) (v:=Int v0); auto.
   match goal with 
   | [H: context[fetch_exp_type_rt (name_astnum_rt ?nRT) ?st] |- _] => 
       rewrite update_exterior_checks_name_astnum_eq in H; smack
   end.
  match goal with
  | [H1: toSymTabRT ?st ?st',
     H2: fetch_exp_type _ ?st = _ |- _ ] => 
      specialize (symbol_table_exp_type_rel _ _ _ _ H1 H2);
      let HZ := fresh "HZ" in intros HZ
  end.
   rewrite H37 in HZ7; inversion HZ7; subst. 
   apply_value_in_range_is_well_typed; auto. smack.
-(* C2_Flagged_Args_InOut *)
 inversion H6; subst;
 inversion H10; subst;
 inversion H11; subst;
 inversion H12; subst.
 match goal with
 | [H: well_typed_value_in_stack _ _ |- _] => 
     specialize (well_typed_stack_infer _ _ H); let HB := fresh "HB" in intro HB
 end;
 match goal with
 | [H: well_typed_value_in_store _ _ |- _] => 
     specialize (well_typed_store_infer _ _ H); let HB := fresh "HB" in intro HB
 end.
 assert(HZ1: param.(parameter_mode) = paramRT.(parameter_mode_rt) /\ 
            (parameter_subtype_mark param) = (parameter_subtype_mark_rt paramRT)).
 match goal with
 | [H: toParamSpecRT ?param ?paramRT |- _] => clear - H; inversion H; smack
 end. destruct HZ1 as [HZ1a HZ1b].
 inversion H13; subst;
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
 | [H1: is_range_constrainted_type ?x = _, 
    H2: is_range_constrainted_type ?y = _,
    H3: ?x = ?y |- _] => 
     rewrite H3 in H1; rewrite H1 in H2; inversion H2
 | _ => idtac
 end;
 inversion H14; subst;
 match goal with
 | [H1: parameter_mode_rt ?a = _ ,
    H2: parameter_mode_rt ?a = _ |- _] => rewrite H2 in H1; inversion H1 
 | [H1: parameter_mode_rt ?a = In ,
    H2: parameter_mode_rt ?a = Out \/ parameter_mode_rt ?a = In_Out |- _] => 
     rewrite H1 in H2; clear - H2; smack
 | _ => idtac
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
 repeat progress match goal with
 | [H1: fetch_exp_type_rt ?x ?st = _, 
    H2: fetch_exp_type_rt ?x ?st = _ |- _] => rewrite H1 in H2; inversion H2; subst
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
 | [H1: extract_subtype_range_rt _ ?t _, 
    H2: extract_subtype_range_rt _ ?t _ |- _] => 
     specialize (extract_subtype_range_unique _ _ _ _ _ _ H1 H2);
     let HZ := fresh "HZ" in intro HZ; destruct HZ; subst
 | _ => idtac
 end;
 match goal with
 | [H: optName _ _ _ |- _] => 
     specialize (optimize_name_ex_cks_eq _ _ _ _ H);
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
 end; simpl in *. 
 (* - subcase 1: CopyOut_Mode_Out_nRTE_X *)
 apply CopyOut_Mode_Out_nRTE_X with (v:=v); auto.
 rewrite <- HZ0; auto.
 apply_storeUpdateRT_opt_soundness'; auto.
 (* - subcase 2: CopyOut_Mode_Out_NoRange_X *)
 apply CopyOut_Mode_Out_NoRange_X with (v:=v) (s':=s'0); auto.
 rewrite <- HZ0; auto.
 apply_storeUpdateRT_opt_soundness'; auto. 
 apply IHtoArgsRT with (args'' := args'); auto.
   repeat progress match goal with
   | [H1: fetch_exp_type_rt ?x ?y = _, H2: fetch_exp_type_rt ?x ?y = _ |- _] => rewrite H1 in H2; inversion H2; subst
   end.
   apply_well_typed_value_in_store_fetch.
   apply_value_well_typed_with_matched_type.
   match goal with 
   | [H: Some ?t = fetch_exp_type_rt (name_astnum_rt ?nRT) ?st |- _] => symmetry in H
   end.
   apply_storeUpdateRT_opt_soundness; auto.
   apply_storeUpdate_with_typed_value_preserve_typed_stack; auto. 
-(* C2_Flagged_Args_InOut_In_RangeCheck *)
 inversion H6; subst;
 inversion H10; subst;
 inversion H11; subst;
 inversion H12; subst.
 match goal with
 | [H: well_typed_value_in_stack _ _ |- _] => 
     specialize (well_typed_stack_infer _ _ H); let HB := fresh "HB" in intro HB
 end;
 match goal with
 | [H: well_typed_value_in_store _ _ |- _] => 
     specialize (well_typed_store_infer _ _ H); let HB := fresh "HB" in intro HB
 end.
 assert(HZ1: param.(parameter_mode) = paramRT.(parameter_mode_rt) /\ 
            (parameter_subtype_mark param) = (parameter_subtype_mark_rt paramRT)).
 match goal with
 | [H: toParamSpecRT ?param ?paramRT |- _] => clear - H; inversion H; smack
 end. destruct HZ1 as [HZ1a HZ1b].
 inversion H13; subst;
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
 | [H1: is_range_constrainted_type ?x = _, 
    H2: is_range_constrainted_type ?y = _,
    H3: ?x = ?y |- _] => 
     rewrite H3 in H1; rewrite H1 in H2; inversion H2
 | _ => idtac
 end;
 inversion H14; subst;
 match goal with
 | [H1: parameter_mode_rt ?a = _ ,
    H2: parameter_mode_rt ?a = _ |- _] => rewrite H2 in H1; inversion H1 
 | [H1: parameter_mode_rt ?a = In ,
    H2: parameter_mode_rt ?a = Out \/ parameter_mode_rt ?a = In_Out |- _] => 
     rewrite H1 in H2; clear - H2; smack
 | _ => idtac
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
 repeat progress match goal with
 | [H1: fetch_exp_type_rt ?x ?st = _, 
    H2: fetch_exp_type_rt ?x ?st = _ |- _] => rewrite H1 in H2; inversion H2; subst
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
 | [H1: extract_subtype_range_rt _ ?t _, 
    H2: extract_subtype_range_rt _ ?t _ |- _] => 
     specialize (extract_subtype_range_unique _ _ _ _ _ _ H1 H2);
     let HZ := fresh "HZ" in intro HZ; destruct HZ; subst
 | _ => idtac
 end;
 match goal with
 | [H: optName _ _ _ |- _] => 
     specialize (optimize_name_ex_cks_eq _ _ _ _ H);
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
 end; simpl in *. 
 (* - subcase 1: CopyOut_Mode_Out_nRTE_X *)
 apply CopyOut_Mode_Out_nRTE_X with (v:=v); auto.
 rewrite <- HZ0; auto.
 apply_store_update_ex_cks_added.
 apply storeUpdateRT_opt_soundness 
   with (n:=nm) (st:=st) (n'':=update_exterior_checks_name n' (name_exterior_checks nRT)) (nBound:=nBound); auto.
 apply_store_update_ex_cks_added; auto.
 (* - subcase 2: CopyOut_Mode_Out_NoRange_X *)
 apply CopyOut_Mode_Out_NoRange_X with (v:=v) (s':=s'0); auto.
 rewrite <- HZ0; auto.
 apply_store_update_ex_cks_added. 
 apply storeUpdateRT_opt_soundness 
   with (n:=nm) (st:=st) (n'':=update_exterior_checks_name n' (name_exterior_checks nRT)) (nBound:=nBound); auto.
 apply_store_update_ex_cks_added; auto.
 apply IHtoArgsRT with (args'' := args'); auto.
   repeat progress match goal with
   | [H1: fetch_exp_type_rt ?x ?y = _, H2: fetch_exp_type_rt ?x ?y = _ |- _] => rewrite H1 in H2; inversion H2; subst
   end.
   apply_well_typed_value_in_store_fetch.
   apply_value_well_typed_with_matched_type.
   apply_well_typed_name_preserve.
   assert(HA1: storeUpdateRT st' s (update_exterior_checks_name n' (name_exterior_checks nRT)) (v) (OK s'0)).
   apply_store_update_ex_cks_added; auto.
   apply_storeUpdateRT_opt_soundness.
   apply storeUpdate_with_typed_value_preserve_typed_stack with (st0:=st) (x0:=nm) (x:=nRT) (s:=s) (t:=t) (v:=v); auto.
   match goal with 
   | [H: context[fetch_exp_type_rt (name_astnum_rt ?nRT) ?st] |- _] => 
       rewrite update_exterior_checks_name_astnum_eq in H; smack
   end.
-(* C2_Flagged_Args_InOut_Out_RangeCheck *)
 inversion H6; subst;
 inversion H10; subst;
 inversion H11; subst;
 inversion H12; subst.
 match goal with
 | [H: well_typed_value_in_stack _ _ |- _] => 
     specialize (well_typed_stack_infer _ _ H); let HB := fresh "HB" in intro HB
 end;
 match goal with
 | [H: well_typed_value_in_store _ _ |- _] => 
     specialize (well_typed_store_infer _ _ H); let HB := fresh "HB" in intro HB
 end.
 assert(HZ1: param.(parameter_mode) = paramRT.(parameter_mode_rt) /\ 
            (parameter_subtype_mark param) = (parameter_subtype_mark_rt paramRT)).
 match goal with
 | [H: toParamSpecRT ?param ?paramRT |- _] => clear - H; inversion H; smack
 end. destruct HZ1 as [HZ1a HZ1b].
 inversion H13; subst;
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
 | [H1: is_range_constrainted_type ?x = _, 
    H2: is_range_constrainted_type ?y = _,
    H3: ?x = ?y |- _] => 
     rewrite H3 in H1; rewrite H1 in H2; inversion H2
 | _ => idtac
 end;
 inversion H14; subst;
 match goal with
 | [H1: parameter_mode_rt ?a = _ ,
    H2: parameter_mode_rt ?a = _ |- _] => rewrite H2 in H1; inversion H1 
 | [H1: parameter_mode_rt ?a = In ,
    H2: parameter_mode_rt ?a = Out \/ parameter_mode_rt ?a = In_Out |- _] => 
     rewrite H1 in H2; clear - H2; smack
 | _ => idtac
 end;
 match goal with
 | [H: extract_subtype_range_rt _ (parameter_subtype_mark_rt _) (RangeRT _ _) |- _] => 
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
 repeat progress match goal with
 | [H1: fetch_exp_type_rt ?x ?st = _, 
    H2: fetch_exp_type_rt ?x ?st = _ |- _] => rewrite H1 in H2; inversion H2; subst
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
 | [H1: extract_subtype_range_rt _ ?t _, 
    H2: extract_subtype_range_rt _ ?t _ |- _] => 
     specialize (extract_subtype_range_unique _ _ _ _ _ _ H1 H2);
     let HZ := fresh "HZ" in intro HZ; destruct HZ; subst
 | _ => idtac
 end;
 match goal with
 | [H: optName _ _ _ |- _] => 
     specialize (optimize_name_ex_cks_eq _ _ _ _ H);
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
 | [H: parameter_mode_rt _ = In |- _] => apply CopyOut_Mode_In_X; auto
 | _ => idtac
 end; simpl in *. 
 (* - subcase 1: CopyOut_Mode_Out_nRTE *)
 (* conflict: RangeCheckOnReturn is in and not in n' *)
 match goal with
 | [H1: ~ List.In RangeCheckOnReturn (name_exterior_checks ?n'),
    H2: name_exterior_checks ?n' = name_exterior_checks (update_exterior_checks_name _ _) |- _] =>
     rewrite H2 in H1; rewrite name_updated_exterior_checks in H1; clear - H1; smack
 end.
 (* - subcase 2: CopyOut_Mode_Out_NoRange_X *)
 match goal with
 | [H1: ~ List.In RangeCheckOnReturn (name_exterior_checks ?n'),
    H2: name_exterior_checks ?n' = name_exterior_checks (update_exterior_checks_name _ _) |- _] =>
     rewrite H2 in H1; rewrite name_updated_exterior_checks in H1; clear - H1; smack
 end.
 (* - subcase 3: CopyOut_Mode_Out_Range_RTE_X *)
 apply CopyOut_Mode_Out_Range_RTE_X with (v:=v) (l:=l) (u:=u) (t:=t); auto.
 rewrite name_updated_exterior_checks; smack.
 (* - subcase 4: CopyOut_Mode_Out_Range_nRTE_X *)
 apply CopyOut_Mode_Out_Range_nRTE_X with (v:=v) (t:=t) (l:=l) (u:=u); auto.
 rewrite name_updated_exterior_checks; smack.
 apply_store_update_ex_cks_added.
 apply storeUpdateRT_opt_soundness 
   with (n:=nm) (st:=st) (n'':=update_exterior_checks_name n' (name_exterior_checks nRT)) (nBound:=nBound); auto.
 apply_store_update_ex_cks_added; auto. 
 (* - subcase 5: CopyOut_Mode_Out_Range_X *)
 apply CopyOut_Mode_Out_Range_X with (v:=v) (t:=t) (l:=l) (u:=u) (s':=s'0); subst; auto. 
 rewrite name_updated_exterior_checks; smack.
 apply_store_update_ex_cks_added.
 apply storeUpdateRT_opt_soundness 
   with (n:=nm) (st:=st) (n'':=update_exterior_checks_name n' (name_exterior_checks nRT)) (nBound:=nBound); auto.
 apply_store_update_ex_cks_added; auto. 
 apply IHtoArgsRT with (args'' := args'); auto.
   apply_well_typed_value_in_store_fetch.
   assert(HA1: storeUpdateRT st' s (update_exterior_checks_name n' (name_exterior_checks nRT)) (Int v) (OK s'0)).
     apply_store_update_ex_cks_added; auto.
   apply_storeUpdateRT_opt_soundness; auto.
 apply storeUpdate_with_typed_value_preserve_typed_stack with (st0:=st) (x0:=nm) (x:=nRT) (s:=s) (t:=t) (v:=Int v); auto.
   match goal with 
   | [H: context[fetch_exp_type_rt (name_astnum_rt ?nRT) ?st] |- _] => 
       rewrite update_exterior_checks_name_astnum_eq in H; smack
   end.
  apply_value_in_range_is_well_typed; auto. 
  smack.
-(* C2_Flagged_Args_InOut_RangeCheck *)
 inversion H6; subst;
 inversion H10; subst;
 inversion H11; subst;
 inversion H12; subst.
 match goal with
 | [H: well_typed_value_in_stack _ _ |- _] => 
     specialize (well_typed_stack_infer _ _ H); let HB := fresh "HB" in intro HB
 end;
 match goal with
 | [H: well_typed_value_in_store _ _ |- _] => 
     specialize (well_typed_store_infer _ _ H); let HB := fresh "HB" in intro HB
 end.
 assert(HZ1: param.(parameter_mode) = paramRT.(parameter_mode_rt) /\ 
            (parameter_subtype_mark param) = (parameter_subtype_mark_rt paramRT)).
 match goal with
 | [H: toParamSpecRT ?param ?paramRT |- _] => clear - H; inversion H; smack
 end. destruct HZ1 as [HZ1a HZ1b].
 inversion H13; subst;
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
 | [H1: is_range_constrainted_type ?x = _, 
    H2: is_range_constrainted_type ?y = _,
    H3: ?x = ?y |- _] => 
     rewrite H3 in H1; rewrite H1 in H2; inversion H2
 | _ => idtac
 end;
 rewrite HZ1b in *; (* +++ *)
 inversion H14; subst;
 match goal with
 | [H1: parameter_mode_rt ?a = _ ,
    H2: parameter_mode_rt ?a = _ |- _] => rewrite H2 in H1; inversion H1 
 | [H1: parameter_mode_rt ?a = In ,
    H2: parameter_mode_rt ?a = Out \/ parameter_mode_rt ?a = In_Out |- _] => 
     rewrite H1 in H2; clear - H2; smack
 | _ => idtac
 end;
 match goal with
 | [H: extract_subtype_range_rt _ (parameter_subtype_mark_rt _) (RangeRT _ _) |- _] => 
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
 repeat progress match goal with
 | [H1: fetch_exp_type_rt ?x ?st = _, 
    H2: fetch_exp_type_rt ?x ?st = _ |- _] => rewrite H1 in H2; inversion H2; subst
 | _ => idtac
 end;
 match goal with
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
 | [H1: extract_subtype_range_rt _ ?t _, 
    H2: extract_subtype_range_rt _ ?t _ |- _] => 
     specialize (extract_subtype_range_unique _ _ _ _ _ _ H1 H2);
     let HZ := fresh "HZ" in intro HZ; destruct HZ; subst
 | _ => idtac
 end;
 match goal with (* +++ *)
 | [H: optExp ?st (NameRT _ _) _ |- _] => inversion H; subst
 end;
 match goal with
 | [H: optName _ _ _ |- _] => 
     specialize (optimize_name_ex_cks_eq _ _ _ _ H);
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
 simpl in *. 
 (* - subcase 1: CopyOut_Mode_Out_nRTE *)
 assert(HA0: bound_of_type st' (parameter_subtype_mark_rt paramRT) (Interval u v)). constructor; auto.
 apply_well_typed_bounded_var_exists_int_value.
 assert (HA1: sub_bound (Interval u v) (Interval u' v') true). 
   match goal with
   | [H: optimize_range_check_on_copy_out _ _ _ _ |- _] => inversion H; subst; auto
   end.
   (* not optmize the RangeCheckOnReturn *)
   (* conflict: RangeCheckOnReturn is in and not in the n0 *)
   rewrite name_updated_exterior_checks in HZ2. 
   apply_range_check_on_copyout_preserve; smack.
 assert (HA2: in_bound x (Interval u' v') true). 
   apply_well_typed_var_in_bound.
   apply_In_Bound_SubBound_Trans; auto.
 assert(HA3: exists n'', arg = NameRT n n'').
   clear - H36; inversion H36; smack.
 destruct HA3; subst. 

 apply CopyOut_Mode_Out_Range_nRTE_X with (v:=x) (l:=u') (u:=v') (t:=t); auto.
 rewrite name_updated_exterior_checks; smack.
 constructor; auto.
 apply_store_update_ex_cks_added.
 apply_optimize_range_check_on_copy_out_reserve_storeUpdate_backward.
 apply_optimize_range_check_reserve_storeUpdate_backward.
 apply storeUpdateRT_opt_soundness 
   with (n:=nm) (st:=st) (n'':=update_exterior_checks_name n' (name_exterior_checks nRT)) (nBound:=Interval v1 v2); auto.
 apply_store_update_ex_cks_added; auto.
 (* - subcase 2: CopyOut_Mode_Out_NoRange_X *)
 assert(HA0: bound_of_type st' (parameter_subtype_mark_rt paramRT) (Interval u v)). constructor; auto.
 apply_well_typed_bounded_var_exists_int_value.
 assert (HA1: sub_bound (Interval u v) (Interval u' v') true). 
   match goal with
   | [H: optimize_range_check_on_copy_out _ _ _ _ |- _] => inversion H; subst; auto
   end.
   (* not optmize the RangeCheckOnReturn *)
   (* conflict: RangeCheckOnReturn is in and not in the n0 *)
   rewrite name_updated_exterior_checks in HZ2. 
   apply_range_check_on_copyout_preserve; smack.
 assert (HA2: in_bound x (Interval u' v') true). 
   apply_well_typed_var_in_bound.
   apply_In_Bound_SubBound_Trans; auto.
 assert(HA3: exists n'', arg = NameRT n n'').
   clear - H36; inversion H36; smack.
 destruct HA3; subst. 

 apply CopyOut_Mode_Out_Range_X with (v:=x) (t:=t) (l:=u') (u:=v') (s':=s'0); auto.
 rewrite name_updated_exterior_checks; smack.
 constructor; auto.
 apply_store_update_ex_cks_added.
 apply_optimize_range_check_on_copy_out_reserve_storeUpdate_backward.
 apply_optimize_range_check_reserve_storeUpdate_backward.
 apply storeUpdateRT_opt_soundness 
   with (n:=nm) (st:=st) (n'':=update_exterior_checks_name n' (name_exterior_checks nRT)) (nBound:=Interval v1 v2); auto.
 apply_store_update_ex_cks_added; auto.
 apply IHtoArgsRT with (args'' := args'); auto.
 apply_optimize_range_check_on_copy_out_reserve_storeUpdate_backward.
 apply_optimize_range_check_reserve_storeUpdate_backward.
 assert(HA3: storeUpdateRT st' s (update_exterior_checks_name n' (name_exterior_checks nRT)) (Int x) (OK s'0)).
   apply_store_update_ex_cks_added; auto.
 apply_storeUpdateRT_opt_soundness.
 apply storeUpdate_with_typed_value_preserve_typed_stack with (st0:=st) (x0:=nm) (x:=nRT) (s:=s) (t:=t) (v:=Int x); auto.
   match goal with 
   | [H: context[fetch_exp_type_rt (name_astnum_rt ?nRT) ?st] |- _] => 
       rewrite update_exterior_checks_name_astnum_eq in H; smack
   end.
   apply_well_typed_value_of_var.
   apply_well_typed_value_subtype_trans; auto.
 (* - subcase 3: CopyOut_Mode_Out_Range_RTE_X *)
 assert(HA1: exists n'', arg = NameRT n n'').
   clear - H36; inversion H36; smack.
 destruct HA1; subst. 
 apply CopyOut_Mode_Out_Range_RTE_X with (v:=v0) (l:=u') (u:=v') (t:=t); auto.
 rewrite name_updated_exterior_checks; smack.

 assert(HA1: n = n0). 
   clear -H37; inversion H37; subst; smack.
 subst. rewrite H42 in H31; inversion H31; subst;
 match goal with
  | [H1: extract_subtype_range_rt _ ?t _, 
     H2: extract_subtype_range_rt _ ?t _ |- _] => 
      specialize (extract_subtype_range_unique _ _ _ _ _ _ H1 H2);
      let HZ := fresh "HZ" in intro HZ; destruct HZ; subst; auto
 end.
 (* - subcase 4: CopyOut_Mode_Out_Range_nRTE_X *)
 assert(HA1: exists n'', arg = NameRT n n'').
   clear - H36; inversion H36; smack.
 destruct HA1; subst.
 apply CopyOut_Mode_Out_Range_nRTE_X with (v:=v0) (t:=t) (l:=u') (u:=v'); auto.
 rewrite name_updated_exterior_checks; smack.
 assert(HA: n = n0). 
   clear -H37; inversion H37; subst; smack.
 subst. rewrite H42 in H31; inversion H31; subst;
 match goal with
  | [H1: extract_subtype_range_rt _ ?t _, 
     H2: extract_subtype_range_rt _ ?t _ |- _] => 
      specialize (extract_subtype_range_unique _ _ _ _ _ _ H1 H2);
      let HZ := fresh "HZ" in intro HZ; destruct HZ; subst; auto
 end.
 apply_store_update_ex_cks_added.
 apply_optimize_range_check_on_copy_out_reserve_storeUpdate_backward.
 apply_optimize_range_check_reserve_storeUpdate_backward.
 apply storeUpdateRT_opt_soundness 
   with (n:=nm) (st:=st) (n'':=update_exterior_checks_name n' (name_exterior_checks nRT)) (nBound:=Interval v1 v2); auto.
 apply_store_update_ex_cks_added; auto.
 (* - subcase 5: CopyOut_Mode_Out_Range_X *)
 assert(HA1: exists n'', arg = NameRT n n'').
   clear - H36; inversion H36; smack.
 destruct HA1; subst.
 assert(HA2: n = n0). 
   clear -H37; inversion H37; subst; smack.
 apply CopyOut_Mode_Out_Range_X with (v:=v0) (t:=t) (l:=u') (u:=v') (s':=s'0); subst; auto. 
 rewrite name_updated_exterior_checks; smack.
 rewrite H39 in H31; inversion H31; subst;
 match goal with
  | [H1: extract_subtype_range_rt _ ?t _, 
     H2: extract_subtype_range_rt _ ?t _ |- _] => 
      specialize (extract_subtype_range_unique _ _ _ _ _ _ H1 H2);
      let HZ := fresh "HZ" in intro HZ; destruct HZ; subst; auto
 end.
 apply_store_update_ex_cks_added. 
 apply_optimize_range_check_on_copy_out_reserve_storeUpdate_backward.
 apply_optimize_range_check_reserve_storeUpdate_backward.
 apply storeUpdateRT_opt_soundness 
   with (n:=nm) (st:=st) (n'':=update_exterior_checks_name n' (name_exterior_checks nRT)) (nBound:=Interval v1 v2); auto.
 apply_store_update_ex_cks_added; auto. 
 
 apply IHtoArgsRT with (args'' := args'); auto.
 apply_optimize_range_check_on_copy_out_reserve_storeUpdate_backward.
 apply_optimize_range_check_reserve_storeUpdate_backward.
 assert(HA3: storeUpdateRT st' s (update_exterior_checks_name n' (name_exterior_checks nRT)) (Int v0) (OK s'0)).
   apply_store_update_ex_cks_added; auto.
 apply_storeUpdateRT_opt_soundness.
 apply storeUpdate_with_typed_value_preserve_typed_stack with (st0:=st) (x0:=nm) (x:=nRT) (s:=s) (t:=t) (v:=Int v0); auto.
   match goal with 
   | [H: context[fetch_exp_type_rt (name_astnum_rt ?nRT) ?st] |- _] => 
       rewrite update_exterior_checks_name_astnum_eq in H; smack
   end.
  match goal with
  | [H1: toSymTabRT ?st ?st',
     H2: fetch_exp_type _ ?st = _ |- _ ] => 
      specialize (symbol_table_exp_type_rel _ _ _ _ H1 H2);
      let HZ := fresh "HZ" in intros HZ
  end.
   rewrite H39 in HZ8; inversion HZ8; subst. 
   apply_value_in_range_is_well_typed; auto. smack.
Qed.

Ltac apply_optArgs_copyout_soundness :=
  match goal with
  | [H1: toArgsRT ?st ?params ?args ?args',
     H2: toSymTabRT ?st ?st',
     H3: toParamSpecsRT ?params ?params',
     H4: well_typed_symbol_table ?st',
     H5: well_typed_value_in_stack ?st' ?s,
     H6: well_typed_value_in_store ?st' (snd ?f),
     H7: well_typed_exps_x ?st' ?args',
     H8: well_typed_params_x ?st' ?params',
     H9: well_typed_args_x ?st' ?args' ?params',
     H10: optArgs ?st' ?params' ?args' ?args'',
     H11: copyOutRT ?st' ?s ?f ?params' ?args'' ?s' |- _ ] =>
      specialize (optArgs_copyout_soundness _ _ _ _ _ _ _ _ _ _ H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11);
      let HZ := fresh "HZ" in intro HZ
  end.


(** ** optStmt_soundness *)
Lemma optStmt_soundness: forall st st' s s' c c' c'',
  evalStmtRT st' s c'' s' ->
    toSymTabRT st st' ->
      well_typed_stack_and_symboltable st' s ->
        well_typed_statement_x st' c' ->
          toStmtRT st c c' ->
            optStmt st' c' c'' ->
              evalStmtRT st' s c' s'.
Proof.
  intros st st' s s' c c' c'' H; revert st c c'.
  induction H; intros;
  match goal with
  | [H: well_typed_stack_and_symboltable ?st ?s |- _] => inversion H; subst
  end;
  match goal with
  | [H: well_typed_value_in_stack _ _ |- _] => specialize (well_typed_stack_infer _ _ H); intro HB1
  end.  
- (* 1. Eval_S_Null_X*)
  inversion H3; subst; auto; constructor.
- (* 2. EvalAssignRT_RTE *)
  inversion H2; subst;
  inversion H3; subst;
  inversion H4; subst;
  match goal with
  | [H: toNameRT _ _ _ |- _] => 
      specialize (name_ast_num_eq _ _ _ H); let HZ := fresh "HZ" in intro HZ; rewrite HZ in *
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
  | [H: extract_subtype_range_rt _ _ (RangeRT _ _) |- _] => 
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
  | [H: optExp _ (update_exterior_checks_exp _ _) _ |- _] => 
    specialize (optimize_exp_ex_cks_stripped _ _ _ _ _ H); let HZ := fresh "HZ" in intro HZ
  | _ => idtac
  end;
  match goal with
  | [H: evalExpRT _ _ (update_exterior_checks_exp _ _) _ |- _] => 
    specialize (eval_exp_ex_cks_stripped _ _ _ _ _ H); let HZ := fresh "HZ" in intro HZ
  | _ => idtac
  end.
  + apply EvalAssignRT_RTE; auto.
    apply_optExp_soundness; auto.
  + apply EvalAssignRT_RTE; auto.
    apply_eval_expr_value_reserve_backward.
    assert(HA: evalExpRT st s (update_exterior_checks_exp e' (exp_exterior_checks eRT)) (RTE msg)).
      apply eval_exp_ex_cks_added; auto.
    apply_optExp_soundness; auto.
    apply eval_exp_ex_cks_added; auto.
- (* 3. EvalAssignRT *)
  inversion H5; subst;
  inversion H6; subst;
  inversion H7; subst;
  match goal with
  | [H: toNameRT _ _ _ |- _] => 
      specialize (name_ast_num_eq _ _ _ H); let HZ := fresh "HZ" in intro HZ; rewrite HZ in *
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
  | [H: extract_subtype_range_rt _ _ (RangeRT _ _) |- _] => 
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
  end;

  match goal with
  | [H: well_typed_exp_x _ (update_exterior_checks_exp _ _) |- _] => 
    specialize (well_typed_exp_preserve _ _ _ H); let HZ := fresh "HZ" in intro HZ
  | _ => idtac
  end;
  match goal with
  | [H: optExp _ (update_exterior_checks_exp _ _) _ |- _] => 
    specialize (optimize_exp_ex_cks_stripped _ _ _ _ _ H); let HZ := fresh "HZ" in intro HZ
  | _ => idtac
  end;
  match goal with
  | [H: evalExpRT _ _ (update_exterior_checks_exp _ _) _ |- _] => 
    specialize (eval_exp_ex_cks_stripped _ _ _ _ _ H); let HZ := fresh "HZ" in intro HZ
  | _ => idtac
  end.
  + apply EvalAssignRT with (v:=v); auto.
    apply_optExp_soundness; auto.    
    apply_optimize_exp_ex_cks_eq; smack.
    apply_storeUpdateRT_opt_soundness; auto.
  + apply_eval_expr_value_reserve_backward.
    assert(HA: evalExpRT st s (update_exterior_checks_exp e' (exp_exterior_checks eRT)) (OK v)).
      apply eval_exp_ex_cks_added; auto.
    apply_optExp_soundness.
    apply_optimize_expression_exist_int_value.
    apply EvalAssignRT_Range with (v:=v1) (t:=t0) (l:=u) (u:=v0); auto.
    apply eval_exp_ex_cks_added; auto.
    rewrite exp_updated_exterior_checks; auto.
    match goal with
    | [H: optExp st (update_exterior_checks_exp _ _) _ |- _] => 
      specialize (optimize_exp_ex_cks_eq _ _ _ _ H); 
        let HZ := fresh "HZ" in intro HZ; rewrite exp_updated_exterior_checks in HZ
    end.
    apply_range_check_opt_subBound_true.
    apply_eval_expr_value_in_bound. 
    apply_In_Bound_SubBound_Trans.
    constructor; auto.
    apply_storeUpdateRT_opt_soundness; auto.
- (* 4. Copy_In_Mode_In_Range_RTE_X *)
  inversion H6; subst;
  inversion H7; subst;
  inversion H8; subst;
  match goal with
  | [H: toNameRT _ _ _ |- _] => 
      specialize (name_ast_num_eq _ _ _ H); let HZ := fresh "HZ" in intro HZ; rewrite HZ in *
  | _ => idtac
  end;
  match goal with
  | [H1: toSymTabRT ?st ?st',
     H2: fetch_exp_type _ ?st = _ |- _ ] => 
      specialize (symbol_table_exp_type_rel _ _ _ _ H1 H2);
      let HZ := fresh "HZ" in intros HZ
  | _ => idtac
  end; 
  repeat progress match goal with
  | [H1: fetch_exp_type_rt ?x ?st = _, 
     H2: fetch_exp_type_rt ?x ?st = _ |- _] => rewrite H1 in H2; inversion H2; subst
  | _ => idtac
  end;
  match goal with
  | [H: extract_subtype_range_rt _ _ (RangeRT _ _) |- _] => 
      specialize (range_constrainted_type_true _ _ _ _ H);
      let HZ := fresh "HZ" in intros HZ
  | _ => idtac
  end;
  match goal with
  | [H1: is_range_constrainted_type ?x = true, 
     H2: is_range_constrainted_type ?x = false |- _] => 
      rewrite H1 in H2; inversion H2
  | _ => idtac
  end;

  match goal with
  | [H: well_typed_exp_x _ (update_exterior_checks_exp _ _) |- _] => 
    specialize (well_typed_exp_preserve _ _ _ H); let HZ := fresh "HZ" in intro HZ
  | _ => idtac
  end;
  match goal with
  | [H: optExp _ (update_exterior_checks_exp _ _) _ |- _] => 
    specialize (optimize_exp_ex_cks_stripped _ _ _ _ _ H); let HZ := fresh "HZ" in intro HZ
  | _ => idtac
  end;
  match goal with
  | [H: evalExpRT _ _ (update_exterior_checks_exp _ _) _ |- _] => 
    specialize (eval_exp_ex_cks_stripped _ _ _ _ _ H); let HZ := fresh "HZ" in intro HZ
  | _ => idtac
  end.
  + (* conflict: x := e, x is both range constrainted and not *)
    assert(HA: name_astnum_rt x = name_astnum_rt x0).
      clear - H29. inversion H29; smack.
    rewrite HA in *; smack.
  + apply EvalAssignRT_Range_RTE with (v:=v) (t:=t) (l:=l) (u:=u); auto.
    * apply_eval_expr_value_reserve_backward.
      assert(HA: evalExpRT st s (update_exterior_checks_exp e' (exp_exterior_checks eRT)) (OK (Int v))).
      apply eval_exp_ex_cks_added; auto.
      apply_optExp_soundness; auto.
      apply eval_exp_ex_cks_added; auto.
    * rewrite exp_updated_exterior_checks; auto.
    * assert(HA: name_astnum_rt x = name_astnum_rt x0).
        clear - H29. inversion H29; smack.
      rewrite HA in *; smack.
- (* 5. EvalAssignRT_Range *)
  inversion H7; subst;
  inversion H8; subst;
  inversion H9; subst;
  match goal with
  | [H: toNameRT _ _ _ |- _] => 
      specialize (name_ast_num_eq _ _ _ H); let HZ := fresh "HZ" in intro HZ; rewrite HZ in *
  | _ => idtac
  end;
  match goal with
  | [H1: toSymTabRT ?st ?st',
     H2: fetch_exp_type _ ?st = _ |- _ ] => 
      specialize (symbol_table_exp_type_rel _ _ _ _ H1 H2);
      let HZ := fresh "HZ" in intros HZ
  | _ => idtac
  end; 
  repeat progress match goal with
  | [H1: fetch_exp_type_rt ?x ?st = _, 
     H2: fetch_exp_type_rt ?x ?st = _ |- _] => rewrite H1 in H2; inversion H2; subst
  | _ => idtac
  end;
  match goal with
  | [H: extract_subtype_range_rt _ _ (RangeRT _ _) |- _] => 
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
  | [H: optExp _ (update_exterior_checks_exp _ _) _ |- _] => 
    specialize (optimize_exp_ex_cks_stripped _ _ _ _ _ H); let HZ := fresh "HZ" in intro HZ
  | _ => idtac
  end;
  match goal with
  | [H: evalExpRT _ _ (update_exterior_checks_exp _ _) _ |- _] => 
    specialize (eval_exp_ex_cks_stripped _ _ _ _ _ H); let HZ := fresh "HZ" in intro HZ
  | _ => idtac
  end.
  + (* conflict: x := e, x is both range constrainted and not *)
    assert(HA: name_astnum_rt x = name_astnum_rt x0).
      clear - H30. inversion H30; smack.
    rewrite HA in *; smack.
  + apply EvalAssignRT_Range with (v:=v) (t:=t) (l:=l) (u:=u); auto.
    * apply_eval_expr_value_reserve_backward.
      assert(HA: evalExpRT st s (update_exterior_checks_exp e' (exp_exterior_checks eRT)) (OK (Int v))).
      apply eval_exp_ex_cks_added; auto.
      apply_optExp_soundness; auto.
      apply eval_exp_ex_cks_added; auto.
    * rewrite exp_updated_exterior_checks; auto.
    * assert(HA: name_astnum_rt x = name_astnum_rt x0).
        clear - H30. inversion H30; smack.
      rewrite HA in *; smack.
    * apply_storeUpdateRT_opt_soundness; auto.
- (* 7. EvalIfRT_RTE *)
  inversion H2; subst;
  inversion H3; subst;
  inversion H4; subst.
  apply EvalIfRT_RTE; auto;
  apply_optExp_soundness; auto.
- (* 8. EvalIfRT_True *)
  inversion H3; subst;
  inversion H4; subst;
  inversion H5; subst.
  apply EvalIfRT_True; auto;
  apply_optExp_soundness; auto.
  combine_well_typed_stack_and_symboltable.
  apply IHevalStmtRT with (st0:=st0) (c:=c4); auto.
- (* 9. EvalIfRT_False *)
  inversion H3; subst;
  inversion H4; subst;
  inversion H5; subst.
  apply EvalIfRT_False; auto;
  apply_optExp_soundness; auto.
  combine_well_typed_stack_and_symboltable.
  apply IHevalStmtRT with (st0:=st0) (c:=c5); auto.
- (* 10. EvalWhileRT_RTE *)
  inversion H2; subst;
  inversion H3; subst;
  inversion H4; subst.
  apply EvalWhileRT_RTE; auto;
  apply_optExp_soundness; auto.
- (* 11. EvalWhileRT_True_RTE *)
  inversion H3; subst;
  inversion H4; subst;
  inversion H5; subst.
  apply EvalWhileRT_True_RTE; auto;
  apply_optExp_soundness; auto.
  combine_well_typed_stack_and_symboltable.
  apply IHevalStmtRT with (st0:=st0) (c0:=c2); auto.
- (* 12. EvalWhileRT_True *)
  inversion H4; subst;
  inversion H5; subst;
  inversion H6; subst.
  combine_well_typed_stack_and_symboltable.
  apply EvalWhileRT_True with (s1:=s1); auto.
  + apply_optExp_soundness; auto.
  + apply IHevalStmtRT1 with (st0:=st0) (c0:=c2); auto.
  + specialize (IHevalStmtRT1 _ _ _ H2 HZ H10 H17 H21); auto.
    apply_eval_statement_preserve_typed_stack.
    specialize (IHevalStmtRT2 _ _ _ H2 HZ0 H4 H5 H6); auto.
- (* 13. EvalWhileRT_False *)
  inversion H2; subst;
  inversion H3; subst;
  inversion H4; subst.
  apply EvalWhileRT_False; auto;
  apply_optExp_soundness; auto.
- (* 14. EvalCallRT_Args_RTE *)
  inversion H3; subst;
  inversion H4; subst;
  inversion H5; subst.
  repeat progress match goal with
  | [H1: fetch_proc_rt _ _ = _, H2: fetch_proc_rt _ _ = _ |- _] => rewrite H2 in H1; inversion H1; subst
  end;
  apply EvalCallRT_Args_RTE with (n0:=n0) (pb:=pb); auto.
  specialize (symbol_table_procedure_rel _ _ _ _ _ H1 H16); intro HZ1.
    destruct HZ1 as [pb' [HZ1 HZ2]]. rewrite H14 in HZ1; inversion HZ1; subst.
    inversion HZ2; subst.
  apply_optArgs_copyin_soundness; auto.
- (* 15. EvalCallRT_Decl_RTE *)
  inversion H5; subst;
  inversion H6; subst;
  inversion H7; subst;
  repeat progress match goal with
  | [H1: fetch_proc_rt _ _ = _, H2: fetch_proc_rt _ _ = _ |- _] => rewrite H2 in H1; inversion H1; subst
  end;
  apply EvalCallRT_Decl_RTE with (n0:=n0) (pb:=pb) (f:=f) (intact_s:=intact_s) (s1:=s1); auto.
  specialize (symbol_table_procedure_rel _ _ _ _ _ H3 H18); intro HZ1.
    destruct HZ1 as [pb' [HZ1 HZ2]]. rewrite H16 in HZ1; inversion HZ1; subst.
    inversion HZ2; subst.
  apply_optArgs_copyin_soundness; auto.
- (* 16. EvalCallRT_Body_RTE *)
  inversion H6; subst;
  inversion H7; subst;
  inversion H8; subst;
  repeat progress match goal with
  | [H1: fetch_proc_rt _ _ = _, H2: fetch_proc_rt _ _ = _ |- _] => rewrite H2 in H1; inversion H1; subst
  end;
  apply EvalCallRT_Body_RTE with (n0:=n0) (pb:=pb) (f:=f) (intact_s:=intact_s) (s1:=s1) (f1:=f1); auto.
  specialize (symbol_table_procedure_rel _ _ _ _ _ H4 H19); intro HZ1.
    destruct HZ1 as [pb' [HZ1 HZ2]]. rewrite H17 in HZ1; inversion HZ1; subst.
    inversion HZ2; subst.
  apply_optArgs_copyin_soundness; auto.
- (* 17. EvalCallRT *)
  apply_cut_until_preserve_typed_stack.
  inversion H9; subst;
  inversion H10; subst;
  inversion H11; subst.
  inversion H13; subst. 
  match goal with
  | [H: well_typed_proc_declaration ?st |- _] => inversion H; subst
  end.
  match goal with
  | [H1: forall (f0 : procnum) (n3 : Symbol_Table_Module_RT.level) (p0 : Symbol_Table_Module_RT.proc_decl),
        fetch_proc_rt f0 ?st = Some (n3, p0) -> well_typed_proc_body_x ?st p0,
     H2: fetch_proc_rt ?p ?st = Some (?n2, ?pb1) |- _] => specialize (H1 _ _ _ H2); inversion H1; subst
  end.
  specialize (symbol_table_procedure_rel _ _ _ _ _ H7 H21); intro HZ2. 
  destruct HZ2 as [pb' [HZ2 HZ3]]. 
  repeat progress match goal with
  | [H1: fetch_proc_rt _ _ = _, H2: fetch_proc_rt _ _ = _ |- _] => rewrite H2 in H1; inversion H1; subst
  end;
  apply EvalCallRT with (n0:=n0) (pb:=pb) (f:=f) (intact_s:=intact_s) (s1:=s1) (f1:=f1)
                        (s2:=((n, locals_section ++ params_section) :: s3)) 
                        (locals_section:=locals_section) (params_section:=params_section) (s3:=s3); auto;
  inversion HZ3; subst.
  + apply_optArgs_copyin_soundness; auto.
  + simpl in *.
    assert(HA: well_typed_value_in_store st (snd (STACK.newFrame n))).
      smack; constructor.
    apply_optArgs_copyin_soundness.
    apply_copy_in_preserve_typed_store.
    apply_eval_declaration_preserve_typed_store.
    assert(HA1: well_typed_value_in_stack st (f1 :: s1)).
      apply_well_typed_store_stack_merge'; auto.
    combine_well_typed_stack_and_symboltable.
    apply_eval_statement_preserve_typed_stack.
    inversion HZ7; subst.
    apply_well_typed_store_stack_split'. simpl in *.
    apply_well_typed_store_split'.
    assert(HA2: well_typed_value_in_stack st (intact_s ++ s3)). apply well_typed_stacks_merge'; auto.
    apply optArgs_copyout_soundness with (st:=st0) (params:=params) (args:=args1) (args'':=args); auto; simpl in *.
- (* 18. EvalSeqRT_RTE *)
  inversion H2; subst;
  inversion H3; subst;
  inversion H4; subst;
  apply EvalSeqRT_RTE; auto.
  combine_well_typed_stack_and_symboltable.
  specialize (IHevalStmtRT _ _ _ H0 HZ H7 H13 H12); auto.
- (* 19. EvalSeqRT *)
  inversion H3; subst;
  inversion H4; subst;
  inversion H5; subst;
  apply EvalSeqRT with (s1:=s1); auto;
  combine_well_typed_stack_and_symboltable;
  specialize (IHevalStmtRT1 _ _ _ H1 HZ H8 H14 H13); auto.
  
  assert(HA: well_typed_value_in_stack st s1).
    apply_eval_statement_preserve_typed_stack; auto. inversion HZ0; subst; auto.
  combine_well_typed_stack_and_symboltable.
  specialize (IHevalStmtRT2 _ _ _ H1 HZ0 H9 H16 H20); auto.
Qed.

Ltac apply_optStmt_soundness :=
  match goal with
  | [H1: evalStmtRT ?st' ?s ?c'' ?s',
     H2: toSymTabRT ?st ?st',
     H3: well_typed_stack ?st' ?s,
     H4: well_typed_statement_x ?st' ?c',
     H5: toStmtRT ?st ?c ?c',
     H6: optStmt ?st' ?c' ?c'' |- _] =>
      specialize (optStmt_soundness _ _ _ _ _ _ _ H1 H2 H3 H4 H5 H6);
      let HZ := fresh "HZ" in intros HZ
  end.


(** ** optDecl_soundness *)
Lemma optDecl_soundness: forall st st' s f f' d d' d'',
  evalDeclRT st' s f d'' f' ->
    toSymTabRT st st' ->
      well_typed_symbol_table st' ->
        well_typed_value_in_stack st' (f::s) ->
          well_typed_decl_x st' d' ->
            toDeclRT st d d' ->
              optDecl st' d' d'' ->
                evalDeclRT st' s f d' f'.
Proof.
  intros st st' s f f' d d' d'' H; revert st d d';
  induction H; intros;
  match goal with
  | [H: well_typed_value_in_stack ?st ?s |- _] =>
      specialize (well_typed_stack_infer _ _ H);
      let HB := fresh "HB" in intros HB
  end.
- (* 1. Eval_Decl_Null_X *)
  match goal with
  | [H: optDecl _ _ _ |- _] => inversion H; subst; auto
  end;
  constructor.
- (* 2. EvalDeclRT_Var_None *)
  inversion H5; subst.
  assert(HZ1: object_nameRT d = object_nameRT o).
    clear - H9. inversion H9; smack. rewrite HZ1.
  apply EvalDeclRT_Var_None; auto.
  inversion H9; smack.
- (* 3. Eval_Decl_Var_RTE_X *)
  inversion H4; subst;
  inversion H5; subst;
  inversion H6; subst;
  match goal with
  | [H1: optObjDecl _ ?d ?d', 
     H2: initialization_expRT ?d = None,
     H3: initialization_expRT ?d' = Some _ |- _] =>
    clear - H1 H2 H3; inversion H1; smack
  | _ => idtac
  end.
  match goal with
  | [H: optObjDecl _ ?d1 ?d |- _] => inversion H; subst
  end;
  match goal with
  | [H: toObjDeclRT _ ?o ?d |- _] => inversion H; smack
  end;
  match goal with
  | [H: extract_subtype_range_rt _ _ (RangeRT _ _) |- _] => 
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
  | [H: optExp _ (update_exterior_checks_exp _ _) _ |- _] => 
    specialize (optimize_exp_ex_cks_stripped _ _ _ _ _ H); let HZ := fresh "HZ" in intro HZ
  | _ => idtac
  end.
  + apply EvalDeclRT_Var_RTE with (e:=e0); auto.
    apply_optExp_soundness; auto.
  + apply EvalDeclRT_Var_RTE with (e:=(update_exterior_checks_exp eRT (RangeCheck :: nil))); auto.
    apply eval_exp_ex_cks_added; auto.
    apply_eval_expr_value_reserve_backward.
    assert(HA: evalExpRT st (f :: s) (update_exterior_checks_exp e' (exp_exterior_checks eRT)) (RTE msg)).
      apply eval_exp_ex_cks_added; auto.
    apply_optExp_soundness; auto.
- (* 4. EvalDeclRT_Var_NoCheck *)
  inversion H6; subst;
  inversion H7; subst;
  inversion H8; subst;
  match goal with
  | [H1: optObjDecl _ ?d ?d', 
     H2: initialization_expRT ?d = None,
     H3: initialization_expRT ?d' = Some _ |- _] =>
    clear - H1 H2 H3; inversion H1; smack
  | _ => idtac
  end.
  match goal with
  | [H: optObjDecl _ ?d1 ?d |- _] => inversion H; subst
  end;
  match goal with
  | [H: toObjDeclRT _ ?o ?d |- _] => inversion H; smack
  end;
  match goal with
  | [H: extract_subtype_range_rt _ _ (RangeRT _ _) |- _] => 
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
  end;
  match goal with
  | [H: well_typed_exp_x _ (update_exterior_checks_exp _ _) |- _] => 
    specialize (well_typed_exp_preserve _ _ _ H); let HZ := fresh "HZ" in intro HZ
  | _ => idtac
  end;
  match goal with
  | [H: optExp _ (update_exterior_checks_exp _ _) _ |- _] => 
    specialize (optimize_exp_ex_cks_stripped _ _ _ _ _ H); let HZ := fresh "HZ" in intro HZ
  | _ => idtac
  end.
  (* case 1: x := e, x is not range constrainted *)
  * apply EvalDeclRT_Var_NoCheck with (e:=e0); auto.
    apply_optExp_soundness; auto.
    apply_optimize_exp_ex_cks_eq; smack.
  (* case 2: x := e, x is range constrainted, and optimized *)
  * apply_eval_expr_value_reserve_backward.
    assert(HA: evalExpRT st (f :: s) (update_exterior_checks_exp e' (exp_exterior_checks eRT)) (OK v)).
      apply eval_exp_ex_cks_added; auto.
    apply_optExp_soundness; auto.
    
    assert(HAZ: well_typed_stack_and_symboltable st (f::s)).
      constructor; auto.
    apply_optimize_expression_exist_int_value. (* it should be Int v in order to use EvalDeclRT_Var *)
    specialize (optimize_exp_ex_cks_eq _ _ _ _ H15); intro HZ4.
    rewrite exp_updated_exterior_checks in HZ4; auto.
    apply_range_check_opt_subBound_true.
    apply EvalDeclRT_Var with (e:=(update_exterior_checks_exp eRT (RangeCheck :: nil))) (l:=u) (u:=v0); auto.
    apply eval_exp_ex_cks_added; auto.
    rewrite exp_updated_exterior_checks; auto.  
    apply_eval_expr_value_in_bound. 
    apply_In_Bound_SubBound_Trans.
    constructor; auto.
- (* 5. EvalDeclRT_Var_Range_RTE *)
  inversion H7; subst;
  inversion H8; subst;
  inversion H9; subst;
  match goal with
  | [H1: optObjDecl _ ?d ?d', 
     H2: initialization_expRT ?d = None,
     H3: initialization_expRT ?d' = Some _ |- _] =>
    clear - H1 H2 H3; inversion H1; smack
  | _ => idtac
  end.
  match goal with
  | [H: optObjDecl _ ?d1 ?d |- _] => inversion H; subst
  end;
  match goal with
  | [H: toObjDeclRT _ ?o ?d |- _] => inversion H; smack
  end;
  match goal with
  | [H: extract_subtype_range_rt _ _ (RangeRT _ _) |- _] => 
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
  | [H: well_typed_exp_x _ (update_exterior_checks_exp _ _) |- _] => 
    specialize (well_typed_exp_preserve _ _ _ H); let HZ := fresh "HZ" in intro HZ
  | _ => idtac
  end;
  match goal with
  | [H: optExp _ (update_exterior_checks_exp _ _) _ |- _] => 
    specialize (optimize_exp_ex_cks_stripped _ _ _ _ _ H); let HZ := fresh "HZ" in intro HZ
  | _ => idtac
  end.
  apply_eval_expr_value_reserve_backward.
  assert(HA: evalExpRT st (f :: s) (update_exterior_checks_exp e' (exp_exterior_checks eRT)) (OK (Int v))).
    apply eval_exp_ex_cks_added; auto.
  apply_optExp_soundness; auto.
  eapply EvalDeclRT_Var_Range_RTE with (e:=(update_exterior_checks_exp eRT (RangeCheck :: nil))) ; eauto.
  apply eval_exp_ex_cks_added; auto.
  rewrite exp_updated_exterior_checks; auto.
- (* 6. EvalDeclRT_Var *)
  inversion H7; subst;
  inversion H8; subst;
  inversion H9; subst;
  match goal with
  | [H1: optObjDecl _ ?d ?d', 
     H2: initialization_expRT ?d = None,
     H3: initialization_expRT ?d' = Some _ |- _] =>
    clear - H1 H2 H3; inversion H1; smack
  | _ => idtac
  end.
  match goal with
  | [H: optObjDecl _ ?d1 ?d |- _] => inversion H; subst
  end;
  match goal with
  | [H: toObjDeclRT _ ?o ?d |- _] => inversion H; smack
  end;
  match goal with
  | [H: extract_subtype_range_rt _ _ (RangeRT _ _) |- _] => 
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
  | [H: well_typed_exp_x _ (update_exterior_checks_exp _ _) |- _] => 
    specialize (well_typed_exp_preserve _ _ _ H); let HZ := fresh "HZ" in intro HZ
  | _ => idtac
  end;
  match goal with
  | [H: evalExpRT _ _ (update_exterior_checks_exp _ _) _ |- _] => 
      specialize (eval_exp_ex_cks_stripped _ _ _ _ _ H);
      let HZ := fresh "HZ" in intro HZ
  | _ => idtac
  end;
  match goal with
  | [H: optExp _ (update_exterior_checks_exp _ _) _ |- _] => 
    specialize (optimize_exp_ex_cks_stripped _ _ _ _ _ H); let HZ := fresh "HZ" in intro HZ
  | _ => idtac
  end.
  apply_eval_expr_value_reserve_backward.
  assert(HA: evalExpRT st (f :: s) (update_exterior_checks_exp e' (exp_exterior_checks eRT)) (OK (Int v))).
    apply eval_exp_ex_cks_added; auto.
  apply_optExp_soundness; auto.
  eapply EvalDeclRT_Var with (e:=(update_exterior_checks_exp eRT (RangeCheck :: nil))); eauto.
  apply eval_exp_ex_cks_added; auto.
  rewrite exp_updated_exterior_checks; auto.
- (* 7. EvalDeclRT_Type *)  
  match goal with
  | [H: optDecl _ _ _ |- _] => inversion H; subst; auto
  end;
  apply EvalDeclRT_Type; auto.  
- (* 8. EvalDeclRT_Proc *)
  match goal with
  | [H: optDecl _ _ _ |- _] => inversion H; subst; auto
  end;
  apply EvalDeclRT_Proc; auto.
- (* 9. EvalDeclRT_Seq_E *)
  inversion H3; subst;
  inversion H4; subst;
  inversion H5; subst.
  apply EvalDeclRT_Seq_E.
  apply IHevalDeclRT with (st0:=st0) (d:=d4); auto.
- (* 10. EvalDeclRT_Seq *)
  inversion H4; subst;
  inversion H5; subst;
  inversion H6; subst.
  specialize (IHevalDeclRT1 _ _ _ H1 H2 H3 H7 H13 H12).
  apply EvalDeclRT_Seq with (f':=f'); auto. 
  assert(HZ: well_typed_value_in_stack st (f' :: s)). 
    apply_well_typed_store_stack_split'.
    apply_eval_declaration_preserve_typed_store.
    apply well_typed_store_stack_merge'; auto.
  apply IHevalDeclRT2 with (st0:=st0) (d:=d5); auto. 
Qed.

Ltac apply_optDecl_soundness :=
  match goal with
  | [H1: evalDeclRT ?st' ?s ?f ?d'' ?f',
     H2: toSymTabRT ?st ?st',
     H3: well_typed_symbol_table ?st', 
     H4: well_typed_stack ?st' (?f::?s),
     H5: well_typed_decl_x ?st' ?d',
     H6: toDeclRT ?st ?d ?d',
     H7: optDecl ?st' ?d' ?d'' |- _] =>
      specialize (optDecl_soundness _ _ _ _ _ _ _ _ H1 H2 H3 H4 H5 H6 H7);
      let HZ := fresh "HZ" in intros HZ
  end.

(** ** optProgram_soundness *)
Lemma optProgram_soundness: forall st st' s s' p p' p'',
  evalProgramRT st' s p'' s' ->
    toSymTabRT st st' ->
      well_typed_symbol_table st' ->
        well_typed_value_in_stack st' s ->
          well_typed_program_x st' p' ->
            toProgramRT st p p' ->
              optProgram st' p' p'' ->
                evalProgramRT st' s p' s'.
Proof.
  intros.
  destruct p, p', p''.
  inversion H3; inversion H4; inversion H5; inversion H; subst.
  simpl in *.
  apply EvalProgramRT with (n:=n) (pn := pn); auto.
(*
  apply toStmtRT_soundness with (stmt':=(CallRT n pn (ast_rt.mainRT {| declsRT := declsRT; mainRT := mainRT |}) nil)) (st':=st'); smack.
  inversion H2; subst;
  match goal with
  | [H1: toSymTabRT _ _, H2: fetch_proc_rt _ _ = Some _ |- _ ] =>
      specialize (symbol_table_procedure_rel_backward _ _ _ _ _ H1 H2); smack
  end;
  match goal with
  | [H: fetch_proc ?p ?st = Some (?n1, ?p1) |- _] => 
      apply ToCall with (n0:=n1) (pb:=p1) (params:=procedure_parameter_profile p1); auto
  end;
  match goal with
  | [H1: toProcBodyDeclRT _ _ _, H2: copyInRT _ _ _ _ nil _ |- _] => 
      clear - H1 H2; inversion H2; subst; inversion H5; smack
  end;
  match goal with
  | [H: toParamSpecsRT ?params nil |- _] => inversion H; subst; constructor; auto
  end.  
*)
Qed.

(** * Completeness of RT-OPT Specification *)

(** ** optArgs_copyout_completeness *)
Lemma optArgs_copyout_completeness: forall params' st st' s f s' params args args' args'',
  toArgsRT st params args args' ->
  toSymTabRT st st' ->
  toParamSpecsRT params params' ->
  well_typed_symbol_table st' ->
  well_typed_value_in_stack st' s ->
  well_typed_value_in_store st' (snd f) -> 
  well_typed_exps_x st' args' ->
  well_typed_params_x st' params' ->
  well_typed_args_x st' args' params' ->
  optArgs st' params' args' args'' ->
  copyOutRT st' s f params' args' s' ->
  copyOutRT st' s f params' args'' s'.
Proof.
 induction params'; intros.
-inversion H8; subst.
 inversion H9; subst; auto.
- destruct args', args'', params, args;
  match goal with 
  | [H: copyOutRT _ _ _ (?a :: ?al) nil _ |- _] => inversion H
  | [H: optArgs _ (?a :: ?al) (?e :: ?el) nil |- _] => inversion H
  | [H: toParamSpecsRT nil (?param :: ?params) |- _] => inversion H
  | [H: toArgsRT _ (?param :: ?params) nil _ |- _] => inversion H
  | _ => idtac
  end.
  specialize (well_typed_stack_infer _ _ H3); intro HB1.
  specialize (well_typed_store_infer _ _ H4); intro HB2.

  inversion H1; subst;
  inversion H5; subst; 
  inversion H6; subst;
  inversion H7; subst.
  assert(HZ: p.(parameter_mode) = a.(parameter_mode_rt)).
  clear - H13; inversion H13; smack.
  assert(HZ1: (parameter_subtype_mark p) = (parameter_subtype_mark_rt a)).
  clear - H13; inversion H13; smack.
  (*******)
  inversion H; subst;
  inversion H8; subst;
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
  | [H1: is_range_constrainted_type ?x = _, 
     H2: is_range_constrainted_type ?y = _,
     H3: ?x = ?y |- _] => 
      rewrite H3 in H1; rewrite H1 in H2; inversion H2
  | _ => idtac
  end;
  (*******)
  inversion H9; subst;
  match goal with
  | [H1: parameter_mode_rt ?a = _ ,
     H2: parameter_mode_rt ?a = _ |- _] => rewrite H2 in H1; inversion H1 
  | [H1: parameter_mode_rt ?a = In ,
     H2: parameter_mode_rt ?a = Out \/ parameter_mode_rt ?a = In_Out |- _] => 
      rewrite H1 in H2; clear - H2; smack
  | _ => idtac
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
  repeat progress match goal with
  | [H1: fetch_exp_type_rt ?x ?st = _, 
     H2: fetch_exp_type_rt ?x ?st = _ |- _] => rewrite H1 in H2; inversion H2; subst
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
  | [H1: extract_subtype_range_rt _ ?t _, 
     H2: extract_subtype_range_rt _ ?t _ |- _] => 
      specialize (extract_subtype_range_unique _ _ _ _ _ _ H1 H2);
      let HZ := fresh "HZ" in intro HZ; destruct HZ; subst
  | _ => idtac
  end;
  match goal with
  | [H: optName _ _ _ |- _] => 
      specialize (optimize_name_ex_cks_eq _ _ _ _ H);
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
  | [H1: forall (st : symTab) (st' : symTabRT)
                (s : STACK.state) (f : STACK.scope_level * STACK.store)
                (s' : Ret STACK.state)
                (params : list paramSpec)
                (args : list exp) (args' args'' : list expRT),
              toArgsRT st params args args' ->
              toSymTabRT st st' ->
              toParamSpecsRT params ?params' ->
              well_typed_symbol_table st' ->
              well_typed_value_in_stack st' s ->
              well_typed_value_in_store st' (snd f) ->
              well_typed_exps_x st' args' ->
              well_typed_params_x st' ?params' ->
              well_typed_args_x st' args' ?params' ->
              optArgs st' ?params' args' args'' ->
              copyOutRT st' s f ?params' args' s' ->
              copyOutRT st' s f ?params' args'' s',
     H2: toArgsRT ?st ?params ?args ?args', 
     H3: toSymTabRT ?st ?st',
     H4: toParamSpecsRT ?params ?params',
     H5: well_typed_symbol_table ?st',
     H6: well_typed_value_in_stack ?st' ?s,
     H7: well_typed_value_in_store ?st' (snd ?f),
     H8: well_typed_exps_x ?st' ?args',
     H9: well_typed_params_x ?st' ?params',
     H10: well_typed_args_x ?st' ?args' ?params',
     H11: optArgs ?st' ?params' ?args' ?args'',
     H12: copyOutRT ?st' ?s ?f ?params' ?args' ?s' |- _ ] =>
      specialize (H1 _ _ _ _ _ _ _ _ _ H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12)
  | _ => idtac
  end;
  match goal with
  | [H: parameter_mode_rt _ = In |- _] => apply CopyOut_Mode_In_X; auto
  | _ => idtac
  end. 
  (* 21 sub-proof needs to be proved ! *)
  + apply CopyOut_Mode_Out_nRTE_X with (v:=v); auto.
    rewrite HZ2; assumption.
    apply_storeUpdateRT_opt_completeness; auto.
  + assert(HZ3: well_typed_value_in_stack st' s'0). simpl in *.
      repeat progress match goal with
      | [H1: fetch_exp_type_rt ?x ?y = _, H2: fetch_exp_type_rt ?x ?y = _ |- _] => rewrite H1 in H2; inversion H2; subst
      end.
      apply_well_typed_value_in_store_fetch. 
      apply_value_well_typed_with_matched_type.
      match goal with 
      | [H: Some ?t = fetch_exp_type_rt (name_astnum_rt ?n_flagged) ?st |- _] => symmetry in H
      end;
      apply_storeUpdate_with_typed_value_preserve_typed_stack; auto.
      
    apply_copy_out_opt_H.
    apply CopyOut_Mode_Out_NoRange_X with (v:=v) (s':=s'0); auto. 
      rewrite HZ2; auto.
    apply_storeUpdateRT_opt_completeness; auto.

  (***********************************************************************************)
  (***** following 3 cases ****)
  + clear H H5 H7 H8.
    inversion HB2; subst. specialize (H _ _ H40). destruct H as [m1 [t1 [HZ11 HZ12]]].
    match goal with
    | [H1: fetch_var_rt _ _ = _, H2: fetch_var_rt _ _ = _ |- _] => rewrite H1 in H2; inversion H2
    end. rewrite H7 in *.
    apply_typed_value_in_bound.
    inversion H45; subst. 
    apply_optimize_range_check_on_copy_out_reserve; subst.
    apply CopyOut_Mode_Out_Range_RTE_X with (v:=v0) (l:=l) (u:=u0) (t:=t0); auto.
    rewrite name_updated_exterior_checks in HZ4; rewrite HZ4; smack.
  + apply_storeUpdateRT_opt_completeness; apply_store_update_ex_cks_stripped.
    rewrite name_updated_exterior_checks in HZ4.
    match goal with
    | [H: optimize_range_check_on_copy_out _ _ _ _ |- _] => inversion H; subst
    end.
    
    simpl; rewrite HZ4.
    apply CopyOut_Mode_Out_nRTE_X with (v:=Int v0); auto. smack.
    (* zz1
    apply CopyOut_Mode_Out_Range_nRTE_X with (v:=v0) (t:=t0) (l:=u') (u:=v'); auto. *)
    rewrite name_updated_exterior_checks; smack.
    apply_store_update_ex_cks_added.

    apply CopyOut_Mode_Out_Range_nRTE_X with (v:=v0) (t:=t0) (l:=l) (u:=u0); auto.
    rewrite HZ4; smack.
  + assert(HA: well_typed_value_in_stack st' s'0). 
      rewrite update_exterior_checks_name_astnum_eq in H19. rewrite H19 in H34.
      apply_value_in_range_is_well_typed.
      apply_well_typed_name_preserve.
      assert(HA1: Int v0 <> Undefined). smack.
      apply_storeUpdate_with_typed_value_preserve_typed_stack; auto.
    apply_copy_out_opt_H.
    apply_storeUpdateRT_opt_completeness; apply_store_update_ex_cks_stripped.
    rewrite name_updated_exterior_checks in HZ4.
    match goal with
    | [H: optimize_range_check_on_copy_out _ _ _ _ |- _] => inversion H; subst
    end.
    
    simpl; rewrite HZ4.
    apply CopyOut_Mode_Out_NoRange_X with (v:=Int v0) (s':=s'0); auto.
    smack.
    (* zz1: 
     apply CopyOut_Mode_Out_Range_X with (v:=v0) (t:=t0) (l:=u') (u:=v') (s':=s'0); auto. *)
    rewrite name_updated_exterior_checks; smack.
    apply_store_update_ex_cks_added.
    
    apply CopyOut_Mode_Out_Range_X with (v:=v0) (t:=t0) (l:=l) (u:=u0) (s':=s'0); auto.
    rewrite HZ4; smack.
  + apply CopyOut_Mode_Out_nRTE_X with (v:=v); auto.
    rewrite HZ2; assumption.
    apply_storeUpdateRT_opt_completeness; auto.
  + assert(HZ3: well_typed_value_in_stack st' s'0). simpl in *.
      repeat progress match goal with
      | [H1: fetch_exp_type_rt ?x ?y = _, H2: fetch_exp_type_rt ?x ?y = _ |- _] => rewrite H1 in H2; inversion H2; subst
      end.
      apply_well_typed_value_in_store_fetch. 
      apply_value_well_typed_with_matched_type.
      match goal with 
      | [H: Some ?t = fetch_exp_type_rt (name_astnum_rt ?n_flagged) ?st |- _] => symmetry in H
      end;
      apply_storeUpdate_with_typed_value_preserve_typed_stack; auto.

    apply_copy_out_opt_H.
    apply CopyOut_Mode_Out_NoRange_X with (v:=v) (s':=s'0); auto.
      rewrite HZ2; auto.
    apply_storeUpdateRT_opt_completeness; auto.
  + apply CopyOut_Mode_Out_nRTE_X with (v:=v); auto.
    rewrite HZ2; assumption.
    apply_storeUpdateRT_opt_completeness; auto.
    apply_store_update_ex_cks_stripped; auto.
  + assert(HZ6: well_typed_value_in_stack st' s'0). simpl in *.
      repeat progress match goal with
      | [H1: fetch_exp_type_rt ?x ?y = _, H2: fetch_exp_type_rt ?x ?y = _ |- _] => rewrite H1 in H2; inversion H2; subst
      end.
      apply_well_typed_value_in_store_fetch. 
      apply_value_well_typed_with_matched_type.
      match goal with 
      | [H: Some ?t = fetch_exp_type_rt (name_astnum_rt ?n_flagged) ?st |- _] => 
          rewrite update_exterior_checks_name_astnum_eq in H; symmetry in H
      end;
      apply_storeUpdate_with_typed_value_preserve_typed_stack; auto.

    apply_copy_out_opt_H.
    apply CopyOut_Mode_Out_NoRange_X with (v:=v) (s':=s'0); auto.
      rewrite HZ2; auto.
    apply_storeUpdateRT_opt_completeness; auto.
    apply_store_update_ex_cks_stripped; auto.
  + apply CopyOut_Mode_Out_Range_RTE_X with (v:=v) (l:=l) (u:=u) (t:=t0); auto.
    rewrite HZ3. rewrite name_updated_exterior_checks; smack.
  + apply CopyOut_Mode_Out_Range_nRTE_X with (v:=v) (l:=l) (u:=u) (t:=t0); auto.
    rewrite HZ3; rewrite name_updated_exterior_checks; smack.
    apply_storeUpdateRT_opt_completeness; auto.
    apply_store_update_ex_cks_stripped; auto.
  + assert(HZ7: well_typed_value_in_stack st' s'0). simpl in *.
      rewrite update_exterior_checks_name_astnum_eq in H19. rewrite H19 in H34.
      apply_value_in_range_is_well_typed.
      apply_well_typed_name_preserve.
      assert(HA1: Int v <> Undefined). smack.
      apply_storeUpdate_with_typed_value_preserve_typed_stack; auto.

    apply_copy_out_opt_H.
    apply CopyOut_Mode_Out_Range_X with (v:=v) (t:=t0) (l:=l) (u:=u) (s':=s'0); auto.
    rewrite HZ3; rewrite name_updated_exterior_checks; smack.
    apply_storeUpdateRT_opt_completeness; auto.
    apply_store_update_ex_cks_stripped; auto.
  (***********************************************************************************)
  (**** following 3 cases ****)
  (* for n', it only has: (Do_Range_Check_On_CopyOut :: nil) *)
  + clear H H5 H7 H8.
    inversion H37; subst. (* optimize_expression_x st' (NameRT _ _ _) (NameRT _ _ n', _)*)
    match goal with
    | [H: optName _ _ _ |- _] => 
        specialize (optimize_name_ex_cks_eq _ _ _ _ H); 
        let HZ := fresh "HZ" in intro HZ; rewrite name_updated_exterior_checks in HZ
    end.
    match goal with
    | [H: optimize_range_check _ _ _ _ |- _] => inversion H; subst
    end;
    inversion HB2; subst; specialize (H _ _ H42); destruct H as [m1 [t1 [HZ11 HZ12]]];
    match goal with
    | [H1: fetch_var_rt _ _ = _, H2: fetch_var_rt _ _ = _ |- _] => rewrite H1 in H2; inversion H2; subst
    end;
    apply_typed_value_in_bound;
    inversion H47; subst;
    apply_optimize_range_check_on_copy_out_reserve; subst;

    apply CopyOut_Mode_Out_Range_RTE_X with (v:=v0) (l:=l) (u:=u0) (t:=t); auto;
    try (rewrite name_updated_exterior_checks); smack.
  + clear H H5 H7 H8.
    inversion H37; subst. (* optimize_expression_x st' (NameRT _ _ _) (NameRT _ _ n', _)*)
    match goal with
    | [H: optName _ _ _ |- _] => 
        specialize (optimize_name_ex_cks_eq _ _ _ _ H); 
        let HZ := fresh "HZ" in intro HZ; rewrite name_updated_exterior_checks in HZ
    end.
    match goal with
    | [H: optName _ (update_exterior_checks_name _ _) _ |- _] =>
        specialize (optimize_name_ex_cks_stripped _ _ _ _ _ H); let HZ := fresh "HZ" in intros HZ
    end.
    apply_storeUpdateRT_opt_completeness. apply_store_update_ex_cks_stripped.

    match goal with
    | [H: optimize_range_check _ _ _ _ |- _] => inversion H; subst
    end;
    match goal with
    | [H: optimize_range_check_on_copy_out _ _ _ _ |- _] => inversion H; subst
    end.
    * apply CopyOut_Mode_Out_nRTE_X with (v:=Int v0); auto; simpl. smack.
      rewrite HZ6; repeat progress rewrite name_updated_exterior_checks; smack.
      repeat progress apply_store_update_ex_cks_added. 
    * apply CopyOut_Mode_Out_Range_nRTE_X with (v:=v0) (t:=t0) (l:=l) (u:=u0); auto; simpl.
      rewrite HZ6; rewrite name_updated_exterior_checks; smack.
      apply_store_update_ex_cks_added. 
    * apply CopyOut_Mode_Out_nRTE_X with (v:=Int v0); auto; simpl. smack.
      rewrite HZ6; rewrite name_updated_exterior_checks; smack.
      apply_store_update_ex_cks_added. 
    * apply CopyOut_Mode_Out_Range_nRTE_X with (v:=v0) (t:=t0) (l:=l) (u:=u0); auto; simpl.
      rewrite HZ6; smack.
  + clear H H5 H7 H8 H9.
    assert(HA: well_typed_value_in_stack st' s'0). simpl in *.
      rewrite update_exterior_checks_name_astnum_eq in H19. rewrite H19 in H35.
      apply_value_in_range_is_well_typed.
      apply_well_typed_name_preserve.
      assert(HA1: Int v0 <> Undefined). smack.
      apply_storeUpdate_with_typed_value_preserve_typed_stack; auto.      
    apply_copy_out_opt_H.
    inversion H37; subst. (* optimize_expression_x st' (NameRT _ _ _) (NameRT _ _ n', _)*)
    match goal with
    | [H: optName _ _ _ |- _] => 
        specialize (optimize_name_ex_cks_eq _ _ _ _ H); 
        let HZ := fresh "HZ" in intro HZ; rewrite name_updated_exterior_checks in HZ
    end.
    match goal with
    | [H: optName _ (update_exterior_checks_name _ _) _ |- _] =>
        specialize (optimize_name_ex_cks_stripped _ _ _ _ _ H); let HZ := fresh "HZ" in intros HZ
    end.
    apply_storeUpdateRT_opt_completeness. apply_store_update_ex_cks_stripped.

    match goal with
    | [H: optimize_range_check _ _ _ _ |- _] => inversion H; subst
    end;
    match goal with
    | [H: optimize_range_check_on_copy_out _ _ _ _ |- _] => inversion H; subst
    end.
    * apply CopyOut_Mode_Out_NoRange_X with (v:=Int v0) (s':=s'0); auto; simpl. smack.
      rewrite HZ6; repeat progress rewrite name_updated_exterior_checks; smack.
      repeat progress apply_store_update_ex_cks_added.
    * apply CopyOut_Mode_Out_Range_X with (v:=v0) (t:=t0) (l:=l) (u:=u0) (s':=s'0); auto; simpl.
      rewrite HZ6; rewrite name_updated_exterior_checks; smack.
      apply_store_update_ex_cks_added. 
    * apply CopyOut_Mode_Out_NoRange_X with (v:=Int v0) (s':=s'0); auto; simpl. smack.
      rewrite HZ6; rewrite name_updated_exterior_checks; smack.
      apply_store_update_ex_cks_added. 
    * apply CopyOut_Mode_Out_Range_X with (v:=v0) (t:=t0) (l:=l) (u:=u0) (s':=s'0); auto; simpl.
      rewrite HZ6; smack.
  + apply CopyOut_Mode_Out_Range_RTE_X with (v:=v) (l:=l) (u:=u) (t:=t0); auto.
    rewrite HZ3. rewrite name_updated_exterior_checks; smack.
  + apply CopyOut_Mode_Out_Range_nRTE_X with (v:=v) (l:=l) (u:=u) (t:=t0); auto.
    rewrite HZ3; rewrite name_updated_exterior_checks; smack.
    apply_storeUpdateRT_opt_completeness; auto.
    apply_store_update_ex_cks_stripped; auto.
  + assert(HA: well_typed_value_in_stack st' s'0).
      rewrite update_exterior_checks_name_astnum_eq in H19. rewrite H19 in H34.
      apply_value_in_range_is_well_typed.
      apply_well_typed_name_preserve.
      assert(HA1: Int v <> Undefined). smack.
      apply_storeUpdate_with_typed_value_preserve_typed_stack; auto.
    apply_copy_out_opt_H.
    apply CopyOut_Mode_Out_Range_X with (v:=v) (t:=t0) (l:=l) (u:=u) (s':=s'0); auto.
    rewrite HZ3; rewrite name_updated_exterior_checks; smack.
    apply_storeUpdateRT_opt_completeness; auto.
    apply_store_update_ex_cks_stripped; auto.
  (***********************************************************************************)
  (**** following 3 cases ****)
  (* for n', it only has: (Do_Range_Check :: Do_Range_Check_On_CopyOut :: nil) *)
  + clear H H5 H7 H8.
    inversion H37; subst. (* optimize_expression_x st' (NameRT _ _ _) (NameRT _ _ n', _)*)
    match goal with
    | [H: optName _ _ _ |- _] => 
        specialize (optimize_name_ex_cks_eq _ _ _ _ H); 
        let HZ := fresh "HZ" in intro HZ; rewrite name_updated_exterior_checks in HZ
    end.
    match goal with
    | [H: optimize_range_check _ _ _ _ |- _] => inversion H; subst
    end;
    inversion HB2; subst; specialize (H _ _ H42); destruct H as [m1 [t1 [HZ11 HZ12]]];
    match goal with
    | [H1: fetch_var_rt _ _ = _, H2: fetch_var_rt _ _ = _ |- _] => rewrite H1 in H2; inversion H2; subst
    end;
    apply_typed_value_in_bound;
    inversion H47; subst;
    apply_optimize_range_check_on_copy_out_reserve; subst;

    apply CopyOut_Mode_Out_Range_RTE_X with (v:=v0) (l:=l) (u:=u0) (t:=t); auto;
    try (rewrite name_updated_exterior_checks); smack.
  + clear H H5 H7 H8.
    inversion H37; subst. (* optimize_expression_x st' (NameRT _ _ _) (NameRT _ _ n', _)*)
    match goal with
    | [H: optName _ _ _ |- _] => 
        specialize (optimize_name_ex_cks_eq _ _ _ _ H); 
        let HZ := fresh "HZ" in intro HZ; rewrite name_updated_exterior_checks in HZ
    end.
    match goal with
    | [H: optName _ (update_exterior_checks_name _ _) _ |- _] =>
        specialize (optimize_name_ex_cks_stripped _ _ _ _ _ H); let HZ := fresh "HZ" in intros HZ
    end.
    apply_storeUpdateRT_opt_completeness. apply_store_update_ex_cks_stripped.

    match goal with
    | [H: optimize_range_check _ _ _ _ |- _] => inversion H; subst
    end;
    match goal with
    | [H: optimize_range_check_on_copy_out _ _ _ _ |- _] => inversion H; subst
    end.
    * apply CopyOut_Mode_Out_nRTE_X with (v:=Int v0); auto; simpl. smack.
      rewrite HZ6; repeat progress rewrite name_updated_exterior_checks; smack.
      repeat progress apply_store_update_ex_cks_added. 
    * apply CopyOut_Mode_Out_Range_nRTE_X with (v:=v0) (t:=t0) (l:=l) (u:=u0); auto; simpl.
      rewrite HZ6; rewrite name_updated_exterior_checks; smack.
      apply_store_update_ex_cks_added. 
    * apply CopyOut_Mode_Out_nRTE_X with (v:=Int v0); auto; simpl. smack.
      rewrite HZ6; rewrite name_updated_exterior_checks; smack.
      apply_store_update_ex_cks_added. 
    * apply CopyOut_Mode_Out_Range_nRTE_X with (v:=v0) (t:=t0) (l:=l) (u:=u0); auto; simpl.
      rewrite HZ6; smack.
  + clear H H5 H7 H8 H9.
    assert(HA: well_typed_value_in_stack st' s'0).
      rewrite update_exterior_checks_name_astnum_eq in H19. rewrite H19 in H35.
      apply_value_in_range_is_well_typed.
      apply_well_typed_name_preserve.
      assert(HA1: Int v0 <> Undefined). smack.
      apply_storeUpdate_with_typed_value_preserve_typed_stack; auto.
    apply_copy_out_opt_H.
    inversion H37; subst. (* optimize_expression_x st' (NameRT _ _ _) (NameRT _ _ n', _)*)
    match goal with
    | [H: optName _ _ _ |- _] => 
        specialize (optimize_name_ex_cks_eq _ _ _ _ H); 
        let HZ := fresh "HZ" in intro HZ; rewrite name_updated_exterior_checks in HZ
    end.
    match goal with
    | [H: optName _ (update_exterior_checks_name _ _) _ |- _] =>
        specialize (optimize_name_ex_cks_stripped _ _ _ _ _ H); let HZ := fresh "HZ" in intros HZ
    end.
    apply_storeUpdateRT_opt_completeness. apply_store_update_ex_cks_stripped.

    match goal with
    | [H: optimize_range_check _ _ _ _ |- _] => inversion H; subst
    end;
    match goal with
    | [H: optimize_range_check_on_copy_out _ _ _ _ |- _] => inversion H; subst
    end.
    * apply CopyOut_Mode_Out_NoRange_X with (v:=Int v0) (s':=s'0); auto; simpl. smack.
      rewrite HZ6; repeat progress rewrite name_updated_exterior_checks; smack.
      repeat progress apply_store_update_ex_cks_added.
    * apply CopyOut_Mode_Out_Range_X with (v:=v0) (t:=t0) (l:=l) (u:=u0) (s':=s'0); auto; simpl.
      rewrite HZ6; rewrite name_updated_exterior_checks; smack.
      apply_store_update_ex_cks_added. 
    * apply CopyOut_Mode_Out_NoRange_X with (v:=Int v0) (s':=s'0); auto; simpl. smack.
      rewrite HZ6; rewrite name_updated_exterior_checks; smack.
      apply_store_update_ex_cks_added. 
    * apply CopyOut_Mode_Out_Range_X with (v:=v0) (t:=t0) (l:=l) (u:=u0) (s':=s'0); auto; simpl.
      rewrite HZ6; smack.
Qed.

Ltac apply_optArgs_copyout_completeness :=
  match goal with
  | [H1: toArgsRT ?st ?params ?args ?args',
     H2: toSymTabRT ?st ?st',
     H3: toParamSpecsRT ?params ?params',
     H4: well_typed_symbol_table ?st',
     H5: well_typed_value_in_stack ?st' ?s,
     H6: well_typed_value_in_store ?st' (snd ?f),
     H7: well_typed_exps_x ?st' ?args',
     H8: well_typed_params_x ?st' ?params',
     H9: well_typed_args_x ?st' ?args' ?params',
     H10: optArgs ?st' ?params' ?args' ?args'',
     H11: copyOutRT ?st' ?s ?f ?params' ?args' ?s' |- _ ] =>
      specialize (optArgs_copyout_completeness _ _ _ _ _ _ _ _ _ _ H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11);
      let HZ := fresh "HZ" in intro HZ
  end.


(** ** optStmt_completeness *)
Lemma optStmt_completeness: forall st st' s s' c c' c'',
  evalStmtRT st' s c' s' ->
    toSymTabRT st st' ->
      well_typed_stack_and_symboltable st' s ->
        well_typed_statement_x st' c' ->
          toStmtRT st c c' ->
            optStmt st' c' c'' ->
              evalStmtRT st' s c'' s'.
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
  | [H: toNameRT _ _ _ |- _] => 
      specialize (name_ast_num_eq _ _ _ H); let HZ := fresh "HZ" in intro HZ; rewrite HZ in *
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
  | [H: extract_subtype_range_rt _ _ (RangeRT _ _) |- _] => 
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
  | [H: optExp _ (update_exterior_checks_exp _ _) _ |- _] => 
    specialize (optimize_exp_ex_cks_stripped _ _ _ _ _ H); let HZ := fresh "HZ" in intro HZ
  | _ => idtac
  end;
  match goal with
  | [H: evalExpRT _ _ (update_exterior_checks_exp _ _) _ |- _] => 
    specialize (eval_exp_ex_cks_stripped _ _ _ _ _ H); let HZ := fresh "HZ" in intro HZ
  | _ => idtac
  end.
  + apply EvalAssignRT_RTE; auto.
    apply_optExp_completeness; auto.
  + apply EvalAssignRT_RTE; auto.
    apply_optExp_completeness.
    specialize (eval_exp_ex_cks_stripped _ _ _ _ _ HZ5); let HZ := fresh "HZ" in intro HZ.
    apply_eval_expr_value_reserve; auto.
- inversion H5; subst;
  inversion H6; subst;
  inversion H7; subst;
  match goal with
  | [H: toNameRT _ _ _ |- _] => 
      specialize (name_ast_num_eq _ _ _ H); let HZ := fresh "HZ" in intro HZ; rewrite HZ in *
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
  | [H: extract_subtype_range_rt _ _ (RangeRT _ _) |- _] => 
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
  + apply EvalAssignRT with (v:=v); auto.
    apply_optExp_completeness; auto.    
    apply_optimize_exp_ex_cks_eq; smack.
    apply_storeUpdateRT_opt_completeness; auto.
- inversion H6; subst;
  inversion H7; subst;
  inversion H8; subst;
  match goal with
  | [H: toNameRT _ _ _ |- _] => 
      specialize (name_ast_num_eq _ _ _ H); let HZ := fresh "HZ" in intro HZ; rewrite HZ in *
  | _ => idtac
  end;
  match goal with
  | [H1: toSymTabRT ?st ?st',
     H2: fetch_exp_type _ ?st = _ |- _ ] => 
      specialize (symbol_table_exp_type_rel _ _ _ _ H1 H2);
      let HZ := fresh "HZ" in intros HZ
  | _ => idtac
  end; 
  repeat progress match goal with
  | [H1: fetch_exp_type_rt ?x ?st = _, 
     H2: fetch_exp_type_rt ?x ?st = _ |- _] => rewrite H1 in H2; inversion H2; subst
  | _ => idtac
  end;
  match goal with
  | [H: extract_subtype_range_rt _ _ (RangeRT _ _) |- _] => 
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
  | [H: optExp _ (update_exterior_checks_exp _ _) _ |- _] => 
    specialize (optimize_exp_ex_cks_stripped _ _ _ _ _ H); let HZ := fresh "HZ" in intro HZ
  | _ => idtac
  end;
  match goal with
  | [H: evalExpRT _ _ (update_exterior_checks_exp _ _) _ |- _] => 
    specialize (eval_exp_ex_cks_stripped _ _ _ _ _ H); let HZ := fresh "HZ" in intro HZ
  | _ => idtac
  end.
  + apply EvalAssignRT_Range_RTE with (v:=v) (t:=t1) (l:=l) (u:=u); auto.
    * apply_optExp_completeness; auto.
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
  | [H: toNameRT _ _ _ |- _] => 
      specialize (name_ast_num_eq _ _ _ H); let HZ := fresh "HZ" in intro HZ; rewrite HZ in *
  | _ => idtac
  end;
  match goal with
  | [H1: toSymTabRT ?st ?st',
     H2: fetch_exp_type _ ?st = _ |- _ ] => 
      specialize (symbol_table_exp_type_rel _ _ _ _ H1 H2);
      let HZ := fresh "HZ" in intros HZ
  | _ => idtac
  end; 
  repeat progress match goal with
  | [H1: fetch_exp_type_rt ?x ?st = _, 
     H2: fetch_exp_type_rt ?x ?st = _ |- _] => rewrite H1 in H2; inversion H2; subst
  | _ => idtac
  end;
  match goal with
  | [H: extract_subtype_range_rt _ _ (RangeRT _ _) |- _] => 
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
  | [H: optExp _ (update_exterior_checks_exp _ _) _ |- _] => 
    specialize (optimize_exp_ex_cks_stripped _ _ _ _ _ H); let HZ := fresh "HZ" in intro HZ
  | _ => idtac
  end;
  match goal with
  | [H: evalExpRT _ _ (update_exterior_checks_exp _ _) _ |- _] => 
    specialize (eval_exp_ex_cks_stripped _ _ _ _ _ H); let HZ := fresh "HZ" in intro HZ
  | _ => idtac
  end.
  apply_optExp_completeness; auto.
  specialize (eval_exp_ex_cks_stripped _ _ _ _ _ HZ5); let HZ := fresh "HZ" in intro HZ.
  apply_eval_expr_value_reserve;
  specialize (optimize_exp_ex_cks_eq _ _ _ _ H26); intro HZ8; rewrite exp_updated_exterior_checks in HZ8.
  
  inversion H27; subst.
  + apply EvalAssignRT with (v:=Int v); auto. smack.
    rewrite HZ8. rewrite exp_updated_exterior_checks. smack.
    apply_storeUpdateRT_opt_completeness; auto.
  + apply EvalAssignRT_Range with (v:=v) (t:=t1) (l:=l) (u:=u); auto.
    apply_optimize_name_ast_num_eq; smack.
    apply_storeUpdateRT_opt_completeness; auto.
- (* 7. Eval_S_If_RTE_X *)
  inversion H2; subst;
  inversion H3; subst;
  inversion H4; subst.
  apply EvalIfRT_RTE; auto;
  apply_optExp_completeness; auto.
- (* 8. Eval_S_If_True_X *)
  inversion H3; subst;
  inversion H4; subst;
  inversion H5; subst.
  apply EvalIfRT_True; auto;
  apply_optExp_completeness; auto.
  combine_well_typed_stack_and_symboltable.
  specialize (IHevalStmtRT _ _ _ H1 HZ0 H11 H15 H18); auto.
- (* 9. Eval_S_If_False_X *)
  inversion H3; subst;
  inversion H4; subst;
  inversion H5; subst.
  apply EvalIfRT_False; auto;
  apply_optExp_completeness; auto.
  combine_well_typed_stack_and_symboltable.
  specialize (IHevalStmtRT _ _ _ H1 HZ0 H12 H16 H19); auto.
- (* 10. Eval_S_While_Loop_RTE_X *)
  inversion H2; subst;
  inversion H3; subst;
  inversion H4; subst.
  apply EvalWhileRT_RTE; auto;
  apply_optExp_completeness; auto.
- (* 11. Eval_S_While_Loop_True_RTE_X *)
  inversion H3; subst;
  inversion H4; subst;
  inversion H5; subst.
  apply EvalWhileRT_True_RTE; auto;
  apply_optExp_completeness; auto.
  combine_well_typed_stack_and_symboltable.
  specialize (IHevalStmtRT _ _ _ H1 HZ0 H10 H13 H15); auto.
- (* 12. Eval_S_While_Loop_True_X *)
  inversion H4; subst;
  inversion H5; subst;
  inversion H6; subst.
  combine_well_typed_stack_and_symboltable.
  apply EvalWhileRT_True with (s1:=s1); auto.
  + apply_optExp_completeness; auto.
  + specialize (IHevalStmtRT1 _ _ _ H2 HZ H11 H14 H16); auto.
  + specialize (IHevalStmtRT1 _ _ _ H2 HZ H11 H14 H16); auto.
    apply_eval_statement_preserve_typed_stack.
    specialize (IHevalStmtRT2 _ _ _ H2 HZ0 H4 H5 H6); auto.
- (* 13. Eval_S_While_Loop_False_X *)
  inversion H2; subst;
  inversion H3; subst;
  inversion H4; subst.
  apply EvalWhileRT_False; auto;
  apply_optExp_completeness; auto.
- (* 14. Eval_S_Proc_RTE_Args_X *)
  inversion H3; subst;
  inversion H4; subst;
  inversion H5; subst.
  repeat progress match goal with
  | [H1: fetch_proc_rt _ _ = _, H2: fetch_proc_rt _ _ = _ |- _] => rewrite H2 in H1; inversion H1; subst
  end;
  apply EvalCallRT_Args_RTE with (n0:=n0) (pb:=pb); auto.
  specialize (symbol_table_procedure_rel _ _ _ _ _ H1 H13); intro HZ1.
    destruct HZ1 as [pb' [HZ1 HZ2]]. rewrite H15 in HZ1; inversion HZ1; subst.
    inversion HZ2; subst.
  apply_optArgs_copyin_completeness; auto.
- (* 15. Eval_S_Proc_RTE_Decl_X *)
  inversion H5; subst;
  inversion H6; subst;
  inversion H7; subst;
  repeat progress match goal with
  | [H1: fetch_proc_rt _ _ = _, H2: fetch_proc_rt _ _ = _ |- _] => rewrite H2 in H1; inversion H1; subst
  end;
  apply EvalCallRT_Decl_RTE with (n0:=n0) (pb:=pb) (f:=f) (intact_s:=intact_s) (s1:=s1); auto.
  specialize (symbol_table_procedure_rel _ _ _ _ _ H3 H15); intro HZ1.
    destruct HZ1 as [pb' [HZ1 HZ2]]. rewrite H17 in HZ1; inversion HZ1; subst.
    inversion HZ2; subst.
  apply_optArgs_copyin_completeness; auto.
- (* 16. Eval_S_Proc_RTE_Body_X *)
  inversion H6; subst;
  inversion H7; subst;
  inversion H8; subst;
  repeat progress match goal with
  | [H1: fetch_proc_rt _ _ = _, H2: fetch_proc_rt _ _ = _ |- _] => rewrite H2 in H1; inversion H1; subst
  end;
  apply EvalCallRT_Body_RTE with (n0:=n0) (pb:=pb) (f:=f) (intact_s:=intact_s) (s1:=s1) (f1:=f1); auto.
  specialize (symbol_table_procedure_rel _ _ _ _ _ H4 H16); intro HZ1.
    destruct HZ1 as [pb' [HZ1 HZ2]]. rewrite H18 in HZ1; inversion HZ1; subst.
    inversion HZ2; subst.
  apply_optArgs_copyin_completeness; auto.
- (* 17. Eval_S_Proc_X *)
  apply_cut_until_preserve_typed_stack.
  inversion H9; subst;
  inversion H10; subst;
  inversion H11; subst.
  inversion HSymb; subst. inversion H8; subst. specialize (H12 _ _ _ H20). inversion H12; subst.
  specialize (symbol_table_procedure_rel _ _ _ _ _ H7 H16); intro HZ2. 
  destruct HZ2 as [pb' [HZ2 HZ3]]. 
  repeat progress match goal with
  | [H1: fetch_proc_rt _ _ = _, H2: fetch_proc_rt _ _ = _ |- _] => rewrite H2 in H1; inversion H1; subst
  end;
  apply EvalCallRT with (n0:=n0) (pb:=pb) (f:=f) (intact_s:=intact_s) (s1:=s1) (f1:=f1)
                        (s2:=((n, locals_section ++ params_section) :: s3)) 
                        (locals_section:=locals_section) (params_section:=params_section) (s3:=s3); auto;
  inversion HZ3; subst.
  + apply_optArgs_copyin_completeness; auto.
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
    apply optArgs_copyout_completeness with (st:=st0) (params:=params) (args:=args0) (args':=args); auto; simpl in *.
- (* 18. Eval_S_Sequence_RTE_X *)
  inversion H2; subst;
  inversion H3; subst;
  inversion H4; subst;
  apply EvalSeqRT_RTE; auto.
  combine_well_typed_stack_and_symboltable.
  specialize (IHevalStmtRT _ _ _ H0 HZ H7 H10 H13); auto.
- (* 19. Eval_S_Sequence_X *)
  inversion H3; subst;
  inversion H4; subst;
  inversion H5; subst;
  apply EvalSeqRT with (s1:=s1); auto;
  combine_well_typed_stack_and_symboltable;
  specialize (IHevalStmtRT1 _ _ _ H1 HZ H8 H11 H14); auto.
  
  assert(HA: well_typed_value_in_stack st s1).
    apply_eval_statement_preserve_typed_stack; auto. inversion HZ0; subst; auto.
  combine_well_typed_stack_and_symboltable.
  specialize (IHevalStmtRT2 _ _ _ H1 HZ0 H10 H13 H15); auto.
Qed.

Ltac apply_optStmt_completeness :=
  match goal with
  | [H1: evalStmtRT ?st' ?s ?c' ?s',
     H2: toSymTabRT ?st ?st',
     H3: well_typed_stack ?st' ?s,
     H4: well_typed_statement_x ?st' ?c',
     H5: toStmtRT ?st ?c ?c',
     H6: optStmt ?st' ?c' ?c'' |- _] =>
      specialize (optStmt_completeness _ _ _ _ _ _ _ H1 H2 H3 H4 H5 H6);
      let HZ := fresh "HZ" in intros HZ
  end.



(*
(** * Declaration Checks Optimization Soundness *)
Lemma optDecl_soundness: forall st st' s f f' d d' d'',
  eval_decl_x st' s f d' f' ->
    toSymTabRT st st' ->
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
  | [H: extract_subtype_range_rt _ _ (RangeRT _ _) |- _] => 
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
    apply_optExp_completeness; auto.
  + apply Eval_Decl_Var_eRTE_X with (e:=e''); auto.
    apply eval_expr_value_reserve with (e:=e') (eBound:=(Interval u' v')) (rBound:=(Interval u v)); auto.
    match goal with
    | [H: optExp _ _ _ |- _] => 
        specialize (optimize_exp_ex_cks_stripped _ _ _ _ _ H);
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
    | [H: well_typed_exp_x ?st (update_exterior_checks_exp ?e ?cks) |- _] =>
        specialize (well_typed_exp_preserve _ _ _ H);
        let HZ := fresh "HZ" in intro HZ
    | _ => idtac
    end.
    apply_optExp_completeness.
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
  | [H: extract_subtype_range_rt _ _ (RangeRT _ _) |- _] => 
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
  apply_optExp_completeness; auto.
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
  | [H: extract_subtype_range_rt _ _ (RangeRT _ _) |- _] => 
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
  | [H: optExp _ _ _ |- _] => 
      specialize (optimize_exp_ex_cks_stripped _ _ _ _ _ H);
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
  | [H: well_typed_exp_x ?st (update_exterior_checks_exp ?e ?cks) |- _] =>
      specialize (well_typed_exp_preserve _ _ _ H);
      let HZ := fresh "HZ" in intro HZ
  | _ => idtac
  end.

  apply Eval_Decl_Var_Range_RTE_X with (e:=e'') (v:=v) (l:=l) (u:=u); auto.
  apply eval_expr_value_reserve with (e:=e') (eBound:=(Interval u' v')) (rBound:=(Interval l u)); auto.
  apply_optExp_completeness.
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
  | [H: extract_subtype_range_rt _ _ (RangeRT _ _) |- _] => 
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
  | [H: optExp _ _ _ |- _] => 
      specialize (optimize_exp_ex_cks_stripped _ _ _ _ _ H);
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
    apply_optExp_completeness.
    specialize (exp_exterior_checks_beq_nil _ _ _ H26); intros HZ5. rewrite HZ5 in HZ4. assumption.
    rewrite exp_updated_exterior_checks; auto.
  + apply Eval_Decl_Var_X with (e:=e'') (v:=v) (l:=l) (u:=u); auto.
    apply_optExp_completeness.
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

Ltac apply_optDecl_soundness :=
  match goal with
  | [H1: eval_decl_x ?st' ?s ?f ?d' ?f',
     H2: toSymTabRT ?st ?st',
     H3: well_typed_stack ?st' ?s,
     H4: well_typed_store ?st' (snd ?f),
     H5: well_typed_decl_x ?st' ?d',
     H6: compile2_flagged_declaration ?st ?d ?d',
     H7: optimize_declaration_x ?st' ?d' ?d'' |- _] =>
      specialize (optDecl_soundness _ _ _ _ _ _ _ _ H1 H2 H3 H4 H5 H6 H7);
      let HZ := fresh "HZ" in intros HZ
  end.
*)

(** ** optDecl_completeness *)
Lemma optDecl_completeness: forall st st' s f f' d d' d'',
  evalDeclRT st' s f d' f' ->
    toSymTabRT st st' ->
      well_typed_symbol_table st' ->
        well_typed_value_in_stack st' (f::s) ->
          well_typed_decl_x st' d' ->
            toDeclRT st d d' ->
              optDecl st' d' d'' ->
                evalDeclRT st' s f d'' f'.
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
  | [H: optDecl _ _ _ |- _] => inversion H; subst; auto
  end;
  constructor.
- (* 2. Eval_Decl_Var_None_X *)
  inversion H5; subst.
  assert(HZ1: object_nameRT d = object_nameRT o').
    clear - H10. inversion H10; smack. rewrite HZ1.
  apply EvalDeclRT_Var_None; auto.
  inversion H10; smack.
- (* 3. Eval_Decl_Var_RTE_X *)
  inversion H4; subst;
  inversion H5; subst;
  inversion H6; subst;
  match goal with
  | [H1: initialization_expRT _ = _, 
     H2: initialization_expRT _ = _ |- _] => rewrite H1 in H2; inversion H2; subst
  end.
  inversion H17; smack; (* H17 : optimize_object_declaration_x st d o' *)
  
  inversion H15; subst; (* H15 : compile2_flagged_object_declaration st0 o d *)
  match goal with
  | [H: extract_subtype_range_rt _ _ (RangeRT _ _) |- _] => 
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
  + apply EvalDeclRT_Var_RTE with (e:=e'); auto.
    apply_optExp_completeness; auto.
  + apply EvalDeclRT_Var_RTE with (e:=e''); auto.
    apply eval_expr_value_reserve with (e:=e') (eBound:=(Interval u' v')) (rBound:=(Interval u v)); auto.
    match goal with
    | [H: optExp _ _ _ |- _] => 
        specialize (optimize_exp_ex_cks_stripped _ _ _ _ _ H);
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
    | [H: well_typed_exp_x ?st (update_exterior_checks_exp ?e ?cks) |- _] =>
        specialize (well_typed_exp_preserve _ _ _ H);
        let HZ := fresh "HZ" in intro HZ
    | _ => idtac
    end.
    apply_optExp_completeness.
    specialize (eval_exp_ex_cks_stripped _ _ _ _ _ HZ3); auto.
- (* 4. Eval_Decl_Var_X *)
  inversion H6; subst;
  inversion H7; subst;
  inversion H8; subst;
  match goal with
  | [H1: initialization_expRT _ = _, 
     H2: initialization_expRT _ = _ |- _] => rewrite H1 in H2; inversion H2; subst
  end.
  inversion H19; smack;
  inversion H17; subst; (*H13: compile2_flagged_object_declaration ...*)
  match goal with
  | [H: extract_subtype_range_rt _ _ (RangeRT _ _) |- _] => 
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
  apply EvalDeclRT_Var_NoCheck with (e:=e'); auto.
  apply_optExp_completeness; auto.
  apply_optimize_exp_ex_cks_eq; smack.
- (* 5. Eval_Decl_Var_E_RTE_X *)
  inversion H7; subst;
  inversion H8; subst;
  inversion H9; subst;
  match goal with
  | [H1: initialization_expRT _ = _, 
     H2: initialization_expRT _ = _ |- _] => rewrite H1 in H2; inversion H2; subst
  end.
  inversion H20; smack;
  inversion H18; subst; (*H13: compile2_flagged_object_declaration ...*)
  match goal with
  | [H: extract_subtype_range_rt _ _ (RangeRT _ _) |- _] => 
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
  | [H: optExp _ _ _ |- _] => 
      specialize (optimize_exp_ex_cks_stripped _ _ _ _ _ H);
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
  | [H: well_typed_exp_x ?st (update_exterior_checks_exp ?e ?cks) |- _] =>
      specialize (well_typed_exp_preserve _ _ _ H);
      let HZ := fresh "HZ" in intro HZ
  | _ => idtac
  end.

  eapply EvalDeclRT_Var_Range_RTE with (e:=e'') (v:=v) (l:=u0) (u:=v0); auto.
  + apply eval_expr_value_reserve with (1:=H15); auto.
    apply_optExp_completeness.
    specialize (eval_exp_ex_cks_stripped _ _ _ _ _ HZ3); auto.
  
  + apply_eval_expr_value_in_bound.
    inversion H3; subst.
    specialize (optimize_exp_ex_cks_eq _ _ _ _ H11); intro HZ4.
  rewrite exp_updated_exterior_checks in HZ4.
  apply_optimize_range_check_reserve; smack.
- (* 6. EvalDeclRT_Var_Range_RTE *)
  inversion H7; subst;
  inversion H8; subst;
  inversion H9; subst;
  match goal with
  | [H1: initialization_expRT _ = _, 
     H2: initialization_expRT _ = _ |- _] => rewrite H1 in H2; inversion H2; subst
  end.
  inversion H20; smack;
  inversion H18; subst; (*H13: compile2_flagged_object_declaration ...*)
  match goal with
  | [H: extract_subtype_range_rt _ _ (RangeRT _ _) |- _] => 
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
  | [H: optExp _ _ _ |- _] => 
      specialize (optimize_exp_ex_cks_stripped _ _ _ _ _ H);
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
  | [H: well_typed_exp_x ?st (update_exterior_checks_exp ?e ?cks) |- _] =>
      specialize (well_typed_exp_preserve _ _ _ H);
      let HZ := fresh "HZ" in intro HZ
  | _ => idtac
  end.
  clear H7 H20 H9 H18 H8.
  inversion H15; subst.
  + specialize (optimize_exp_ex_cks_eq _ _ _ _ H11); intros HZ3.
    rewrite exp_updated_exterior_checks in HZ3. rewrite HZ3; smack.
    apply EvalDeclRT_Var_NoCheck with (e:=(update_exterior_checks_exp e' nil)); auto.
    apply_optExp_completeness.
    specialize (exp_exterior_checks_beq_nil _ _ _ H26); intros HZ5. rewrite HZ5 in HZ4. assumption. smack.
    rewrite exp_updated_exterior_checks; auto.
  + eapply EvalDeclRT_Var with (e:=e'');eauto.
    * apply_optExp_completeness.
      specialize (eval_exp_ex_cks_stripped _ _ _ _ _ HZ3); auto.
    * specialize (optimize_exp_ex_cks_eq _ _ _ _ H11); intros HZ4.
      rewrite exp_updated_exterior_checks in HZ4; eauto.
- (* 7. Eval_Decl_Type_X *)  
  match goal with
  | [H: optDecl _ _ _ |- _] => inversion H; subst; auto
  end;
  apply EvalDeclRT_Type; auto.  
- (* 8. Eval_Decl_Proc_X *)
  match goal with
  | [H: optDecl _ _ _ |- _] => inversion H; subst; auto
  end;
  apply EvalDeclRT_Proc; auto.
- (* 9. Eval_Decl_Seq_E_X *)
  inversion H3; subst;
  inversion H4; subst;
  inversion H5; subst.
  specialize (IHevalDeclRT _ _ _ H0 H1 H2 H9 H12 H15).
  apply EvalDeclRT_Seq_E; auto.  
- (* 10. Eval_Decl_Seq_X *)
  inversion H4; subst;
  inversion H5; subst;
  inversion H6; subst.
  specialize (IHevalDeclRT1 _ _ _ H1 H2 H3 H10 H13 H16).
  assert(HZ: well_typed_value_in_stack st (f' :: s)). 
    apply_well_typed_store_stack_split'.
    apply_eval_declaration_preserve_typed_store.
    apply well_typed_store_stack_merge'; auto.
  specialize (IHevalDeclRT2 _ _ _ H1 H2 HZ H12 H15 H17).
  apply EvalDeclRT_Seq with (f':=f'); auto.  
Qed.

Ltac apply_optDecl_completeness :=
  match goal with
  | [H1: evalDeclRT ?st' ?s ?f ?d' ?f',
     H2: toSymTabRT ?st ?st',
     H3: well_typed_symbol_table ?st', 
     H4: well_typed_stack ?st' (?f::?s),
     H5: well_typed_decl_x ?st' ?d',
     H6: toDeclRT ?st ?d ?d',
     H7: optDecl ?st' ?d' ?d'' |- _] =>
      specialize (optDecl_completeness _ _ _ _ _ _ _ _ H1 H2 H3 H4 H5 H6 H7);
      let HZ := fresh "HZ" in intros HZ
  end.

(** ** optProgram_completeness *)
Lemma optProgram_completeness: forall st st' s s' p p' p'',
  evalProgramRT st' s p' s' ->
    toSymTabRT st st' ->
      well_typed_symbol_table st' ->
        well_typed_value_in_stack st' s ->
          well_typed_program_x st' p' ->
            toProgramRT st p p' ->
              optProgram st' p' p'' ->
                evalProgramRT st' s p'' s'.
Proof.
  intros.
  destruct p, p', p''.
  inversion H3; inversion H4; inversion H5; inversion H; subst.
  simpl in *.
  apply EvalProgramRT with (n:=n) (pn := pn); auto.
(*
  apply toStmtRT_soundness with (stmt':=(CallRT n pn (ast_rt.mainRT {| declsRT := declsRT; mainRT := mainRT |}) nil)) (st':=st'); smack.
  inversion H2; subst;
  match goal with
  | [H1: toSymTabRT _ _, H2: fetch_proc_rt _ _ = Some _ |- _ ] =>
      specialize (symbol_table_procedure_rel_backward _ _ _ _ _ H1 H2); smack
  end;
  match goal with
  | [H: fetch_proc ?p ?st = Some (?n1, ?p1) |- _] => 
      apply ToCall with (n0:=n1) (pb:=p1) (params:=procedure_parameter_profile p1); auto
  end;
  match goal with
  | [H1: toProcBodyDeclRT _ _ _, H2: copyInRT _ _ _ _ nil _ |- _] => 
      clear - H1 H2; inversion H2; subst; inversion H5; smack
  end;
  match goal with
  | [H: toParamSpecsRT ?params nil |- _] => inversion H; subst; constructor; auto
  end.  
*)
Qed.

(** * Consistency of RT-OPT Spec *)

(** ** optExpConsistent *)
Lemma optExpConsistent: forall e st st' s e' e'' eBound v, 
  toExpRT st e e' ->
    toSymTabRT st st' ->
      well_typed_stack st' s ->
        well_typed_exp_x st' e' ->
          optExp st' e' (e'', eBound) ->
            (evalExpRT st' s e' v <-> evalExpRT st' s e'' v).
Proof.
  intros;
  split; intro;
  [eapply optExp_completeness; smack |
   eapply optExp_soundness; smack
  ].
Qed.

(** ** optStmtConsistent *)
Lemma optStmtConsistent: forall st st' s s' c c' c'',
  toStmtRT st c c' ->
    toSymTabRT st st' ->
      well_typed_stack_and_symboltable st' s ->
        well_typed_statement_x st' c' ->
          optStmt st' c' c'' -> 
            (evalStmtRT st' s c' s' <-> evalStmtRT st' s c'' s').
Proof.
  intros;
  split; intro;
  [eapply optStmt_completeness; smack |
   eapply optStmt_soundness; smack
  ].
Qed.

(** ** optDeclConsistent *)
Lemma optDeclConsistent: forall st st' s f f' d d' d'',
  toDeclRT st d d' ->
    toSymTabRT st st' ->
      well_typed_symbol_table st' ->
        well_typed_value_in_stack st' (f::s) ->
          well_typed_decl_x st' d' ->
            optDecl st' d' d'' ->
              (evalDeclRT st' s f d' f' <-> evalDeclRT st' s f d'' f').
Proof.
  intros;
  split; intro;
  [eapply optDecl_completeness; smack |
   eapply optDecl_soundness; smack
  ].
Qed.

(** ** optProgramConsistent *)
Lemma optProgramConsistent: forall st st' s s' p p' p'',
  toProgramRT st p p' ->
    toSymTabRT st st' ->
      well_typed_symbol_table st' ->
        well_typed_value_in_stack st' s ->
          well_typed_program_x st' p' ->
            optProgram st' p' p'' ->
              (evalProgramRT st' s p' s' <-> evalProgramRT st' s p'' s').
Proof.
  intros;
  split; intro;
  [eapply optProgram_completeness; smack |
   eapply optProgram_soundness; smack
  ].
Qed.

(*---------------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------------*)
(*----------------------------------  END ! ---------------------------------------*)
(*---------------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------------*)

