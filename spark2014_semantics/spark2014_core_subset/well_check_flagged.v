Require Export semantics_flagged.
Require Export checks_generator.

(** * Well-Check_Flagged *)

(** the well-formedness of run-time check flagged expressions that 
    are generated by expression check generator;
 *)
Inductive well_check_flagged_expr: expression_x -> Prop :=
  | WCF_Literal: forall ast_num l,
      well_check_flagged_expr (E_Literal_X ast_num l nil)
  | WCF_Name: forall ast_num n,
      well_check_flagged_name n ->
      well_check_flagged_expr (E_Name_X ast_num n nil)
  | WCF_Binary_Operation_Overflow: forall op e1 e2 ast_num,
      op = Plus \/ op = Minus \/ op = Multiply ->
      well_check_flagged_expr e1 ->
      well_check_flagged_expr e2 ->
      well_check_flagged_expr (E_Binary_Operation_X ast_num op e1 e2 (Do_Overflow_Check :: nil))
  | WCF_Binary_Operation_Division: forall e1 e2 ast_num,
      well_check_flagged_expr e1 ->
      well_check_flagged_expr e2 ->
      well_check_flagged_expr (E_Binary_Operation_X ast_num Divide e1 e2 (Do_Division_Check :: Do_Overflow_Check :: nil))
  | WCF_Binary_Operation_Others: forall op e1 e2 ast_num,
      op <> Plus /\ op <> Minus /\ op <> Multiply /\ op <> Divide ->
      well_check_flagged_expr e1 ->
      well_check_flagged_expr e2 ->
      well_check_flagged_expr (E_Binary_Operation_X ast_num op e1 e2 nil)
  | WCF_Unary_Operation_Overflow: forall e ast_num,
      well_check_flagged_expr e ->
      well_check_flagged_expr (E_Unary_Operation_X ast_num Unary_Minus e (Do_Overflow_Check :: nil))
  | WCF_Unary_Operation_Others: forall op e ast_num,
      op <> Unary_Minus ->
      well_check_flagged_expr e ->
      well_check_flagged_expr (E_Unary_Operation_X ast_num op e nil)

with well_check_flagged_name: name_x -> Prop :=
  | WCF_Identifier: forall ast_num x,
      well_check_flagged_name (E_Identifier_X ast_num x nil)
  | WCF_Indexed_Component: forall e cks1 cks2 ast_num x_ast_num x,
      exp_check_flags e = cks1 ++ Do_Range_Check :: cks2 ->
      well_check_flagged_expr (update_exp_check_flags e (cks1 ++ cks2)) ->
      well_check_flagged_name (E_Indexed_Component_X ast_num x_ast_num x e nil)
  | WCF_Selected_Component: forall ast_num x_ast_num x f,
      well_check_flagged_name (E_Selected_Component_X ast_num x_ast_num x f nil).

Inductive well_check_flagged_args: list parameter_specification_x -> list expression_x -> Prop :=
  | WCF_Args_Nil:
      well_check_flagged_args nil nil
  | WCF_Args_Head_In: forall param arg params args,
      parameter_mode_x param = In ->
      ~(List.In Do_Range_Check (exp_check_flags arg)) ->
      well_check_flagged_expr arg ->
      well_check_flagged_args params args ->
      well_check_flagged_args (param :: params) (arg :: args)
  | WCF_Args_Head_In_CopyIn_Range: forall param arg cks1 cks2 params args,
      parameter_mode_x param = In ->
      exp_check_flags arg = cks1 ++ Do_Range_Check :: cks2 ->
      well_check_flagged_expr (update_exp_check_flags arg (cks1 ++ cks2)) ->
      well_check_flagged_args params args ->
      well_check_flagged_args (param :: params) (arg :: args)
  | WCF_Args_Head_Out: forall param arg params args,
      parameter_mode_x param = Out ->
      ~(List.In Do_Range_Check_On_CopyOut (exp_check_flags arg)) ->
      well_check_flagged_expr arg ->
      well_check_flagged_args params args ->
      well_check_flagged_args (param :: params) (arg :: args)
  | WCF_Args_Head_Out_CopyOut_Range: forall param arg cks1 cks2 params args,
      parameter_mode_x param = Out ->
      exp_check_flags arg = cks1 ++ Do_Range_Check_On_CopyOut :: cks2 ->
      well_check_flagged_expr (update_exp_check_flags arg (cks1 ++ cks2)) ->
      well_check_flagged_args params args ->
      well_check_flagged_args (param :: params) (arg :: args)
  | WCF_Args_Head_InOut: forall param arg params args,
      parameter_mode_x param = In_Out ->
      ~(List.In Do_Range_Check (exp_check_flags arg)) ->
      ~(List.In Do_Range_Check_On_CopyOut (exp_check_flags arg)) ->
      well_check_flagged_expr arg ->
      well_check_flagged_args params args ->
      well_check_flagged_args (param :: params) (arg :: args)
  | WCF_Args_Head_InOut_CopyIn_Range: forall param arg cks1 cks2 params args,
      parameter_mode_x param = In_Out ->
      exp_check_flags arg = cks1 ++ Do_Range_Check :: cks2 ->
      ~(List.In Do_Range_Check_On_CopyOut (exp_check_flags arg)) ->
      well_check_flagged_expr (update_exp_check_flags arg (cks1 ++ cks2)) ->
      well_check_flagged_args params args ->
      well_check_flagged_args (param :: params) (arg :: args)
  | WCF_Args_Head_InOut_CopyOut_Range: forall param arg cks1 cks2 params args,
      parameter_mode_x param = In_Out ->
      ~(List.In Do_Range_Check (exp_check_flags arg)) ->
      exp_check_flags arg = cks1 ++ Do_Range_Check_On_CopyOut :: cks2 ->
      well_check_flagged_expr (update_exp_check_flags arg (cks1 ++ cks2)) ->
      well_check_flagged_args params args ->
      well_check_flagged_args (param :: params) (arg :: args)
  | WCF_Args_Head_InOut_CopyIn_CopyOut_Range: forall param arg cks1 cks2 params args,
      parameter_mode_x param = In_Out ->
      exp_check_flags arg = cks1 ++ Do_Range_Check :: Do_Range_Check_On_CopyOut :: cks2 ->
      well_check_flagged_expr (update_exp_check_flags arg (cks1 ++ cks2)) ->
      well_check_flagged_args params args ->
      well_check_flagged_args (param :: params) (arg :: args).

Inductive well_check_flagged_stmt: symboltable_x -> statement_x -> Prop :=
  | WCF_Null_X: forall st,
      well_check_flagged_stmt st S_Null_X
  | WCF_Assignment_X: forall x e st ast_num,
      ~(List.In Do_Range_Check (exp_check_flags e)) ->
      well_check_flagged_name x ->
      well_check_flagged_expr e ->
      well_check_flagged_stmt st (S_Assignment_X ast_num x e)
  | WCF_Assignment_X_Range: forall x cks1 cks2 e st ast_num,
      exp_check_flags e = cks1 ++ Do_Range_Check :: cks2 ->
      well_check_flagged_name x ->
      well_check_flagged_expr (update_exp_check_flags e (cks1 ++ cks2)) ->
      well_check_flagged_stmt st (S_Assignment_X ast_num x e)
  | WCF_If_X: forall b st c1 c2 ast_num,
      well_check_flagged_expr b ->
      well_check_flagged_stmt st c1 -> 
      well_check_flagged_stmt st c2 ->
      well_check_flagged_stmt st (S_If_X ast_num b c1 c2)
  | WCF_While_Loop_X: forall b st c ast_num,
      well_check_flagged_expr b ->
      well_check_flagged_stmt st c ->
      well_check_flagged_stmt st (S_While_Loop_X ast_num b c)
  | WCF_Procedure_Call_X: forall p st n pb args ast_num p_ast_num,
      fetch_proc_x p st = Some (n, pb) ->
      well_check_flagged_args (procedure_parameter_profile_x pb) args ->
      well_check_flagged_stmt st (S_Procedure_Call_X ast_num p_ast_num p args)
  | WCF_Sequence_X: forall st c1 c2 ast_num,
      well_check_flagged_stmt st c1 ->
      well_check_flagged_stmt st c2 ->
      well_check_flagged_stmt st (S_Sequence_X ast_num c1 c2).

(** for object declaration with initialization expression, run-time checks on the 
    initialization expression should be well-checked;
*)
Inductive well_check_flagged_object_declaration: object_declaration_x -> Prop :=
  | WCF_Object_Declaration_NoneInit: forall ast_num x t,
      well_check_flagged_object_declaration (mkobject_declaration_x ast_num x t None)
  | WCF_Object_Declaration: forall e ast_num x t,
      ~(List.In Do_Range_Check (exp_check_flags e)) ->
      well_check_flagged_expr e ->
      well_check_flagged_object_declaration (mkobject_declaration_x ast_num x t (Some e))
  | WCF_Object_Declaration_Range: forall e cks1 cks2 ast_num x t,
      exp_check_flags e = cks1 ++ Do_Range_Check :: cks2 ->
      well_check_flagged_expr (update_exp_check_flags e (cks1 ++ cks2)) ->
      well_check_flagged_object_declaration (mkobject_declaration_x ast_num x t (Some e)).

Inductive well_check_flagged_object_declarations: list object_declaration_x -> Prop :=
  | WCF_Object_Declaration_Nil:
      well_check_flagged_object_declarations nil
  | WCF_Object_Declaration_List: forall o lo,
      well_check_flagged_object_declaration o ->
      well_check_flagged_object_declarations lo ->
      well_check_flagged_object_declarations (o :: lo).

Inductive well_check_flagged_declaration: symboltable_x -> declaration_x -> Prop :=
  | WCF_Null_Declaration_X: forall st,
      well_check_flagged_declaration st D_Null_Declaration_X
  | WCF_Type_Declaration_X: forall st ast_num t,
      well_check_flagged_declaration st (D_Type_Declaration_X ast_num t)
  | WCF_Object_Declaration_X: forall o st ast_num,
      well_check_flagged_object_declaration o ->
      well_check_flagged_declaration st (D_Object_Declaration_X ast_num o)
  | WCF_Procedure_Body_X: forall st p ast_num,
      well_check_flagged_procedure_body st p ->
      well_check_flagged_declaration st (D_Procedure_Body_X ast_num p) 
  | WCF_Seq_Declaration_X: forall st d1 d2 ast_num,
      well_check_flagged_declaration st d1 ->
      well_check_flagged_declaration st d2 ->
      well_check_flagged_declaration st (D_Seq_Declaration_X ast_num d1 d2)

with well_check_flagged_procedure_body: symboltable_x -> procedure_body_x -> Prop :=
  | WCF_Procedure_Declaration: forall st decls stmt ast_num p params,
      well_check_flagged_declaration st decls ->
      well_check_flagged_stmt st stmt ->
      well_check_flagged_procedure_body st (mkprocedure_body_x ast_num p params decls stmt).


(** * Checks Generator Produces Well-Check-Flagged AST Node *)

Lemma context_check_flags_in: forall st cks e e',
  compile2_flagged_exp st cks e e' ->
    exists cks', 
      exp_check_flags e' = cks' ++ cks /\ 
      compile2_flagged_exp st nil e (update_exp_check_flags e' (cks' ++ nil)).
Proof.
  intros;
  inversion H; crush;eauto;
  match goal with
  | [|- exists cks', ?cks = cks' ++ ?cks /\ _] => exists (@nil check_flag); crush;eauto
  | [|- exists cks', ?ck :: ?cks = cks' ++ ?cks /\ _] => exists (ck :: nil); crush;eauto
  | [|- exists cks', ?ck1 :: ?ck2 :: ?cks = cks' ++ ?cks /\ _] => exists (ck1 :: ck2 :: nil); crush;eauto (*Division*)
  | _ => idtac
  end;
  match goal with
  | [|- compile2_flagged_exp _ _ _ _ ] => constructor; crush;eauto
  | _ => idtac
  end.
- (* Name *)
  match goal with
  | [H: compile2_flagged_name _ _ _ _ |- _] => inversion H; crush;eauto
  end;
  match goal with
  | [|- exists cks', ?cks = cks' ++ ?cks /\ _ ] => exists (@nil check_flag); crush;eauto
  end;
  repeat progress constructor; crush;eauto.
Qed.

Lemma context_check_flag_in: forall st ck e e',
  compile2_flagged_exp st (ck :: nil) e e' ->
    List.In ck (exp_check_flags e').
Proof.
  intros;
  inversion H; crush;eauto.
- (* Name *)
  match goal with
  | [H: compile2_flagged_name _ _ _ _ |- _] => inversion H; crush;eauto
  end.  
Qed.

Lemma well_check_flagged_generated_expr: forall e st e',
  compile2_flagged_exp st nil e e' ->
    well_check_flagged_expr e'.
Proof.
  apply (expression_ind
    (fun e: expression => 
       forall (st : symboltable) (e' : expression_x),
      compile2_flagged_exp st nil e e' ->
      well_check_flagged_expr e')
    (fun n: name => 
       forall (st : symboltable) (n' : name_x),
      compile2_flagged_name st nil n n' ->
      well_check_flagged_name n')
    ); intros;
  match goal with
  | [H: compile2_flagged_exp _ _ _ _ |- _] => inversion H; subst; constructor; crush;eauto
  | _ => idtac
  end;
  match goal with
  | [H: compile2_flagged_name _ _ _ _ |- _] => inversion H; subst
  end;
  try constructor.
  specialize (context_check_flags_in _ _ _ _ H8); intros HZ.
  destruct HZ as [cks HZ1].
  apply WCF_Indexed_Component with (cks1:=cks) (cks2:=nil); crush;eauto.
Qed.

Lemma well_check_flagged_generated_name: forall n n' st,
  compile2_flagged_name st nil n n' ->
    well_check_flagged_name n'.
Proof.
  intros.
  match goal with
  | [H: compile2_flagged_name _ _ _ _ |- _] => inversion H; subst
  end; 
  try constructor.
  specialize (context_check_flags_in _ _ _ _ H0); intros HZ.
  destruct HZ as [cks [HZ1 HZ2]].
  apply WCF_Indexed_Component with (cks1 := cks) (cks2:=nil); auto.
  apply well_check_flagged_generated_expr with (e:=e) (st:=st); auto.  
Qed.
