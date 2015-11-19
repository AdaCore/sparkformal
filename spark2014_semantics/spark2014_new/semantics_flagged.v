Require Export checks.
Require Export language_flagged.
Require Export language_util.
Require Export semantics.

Import STACK.

(** * Do Flagged Checks *)
(** do run time checks according to the check flags  *)

Inductive do_flagged_check_on_binop: check_flag -> binary_operator -> value -> value -> Return value -> Prop :=
    | Do_Overflow_Check_Binop: forall op v1 v2 v v',
        op = Plus \/ op = Minus \/ op = Multiply \/ op = Divide ->
        Math.binary_operation op v1 v2 = Some (Int v) ->
        do_overflow_check v v' ->
        do_flagged_check_on_binop Do_Overflow_Check op v1 v2 v'
    | Do_Division_By_Zero_Check_Binop: forall v1 v2 v,
        do_division_check v1 v2 v ->
        do_flagged_check_on_binop Do_Division_Check Divide (Int v1) (Int v2) v.

Inductive do_flagged_check_on_unop: check_flag -> unary_operator -> value -> Return value -> Prop :=
    | Do_Overflow_Check_Unop: forall v v' v'',
        Math.unary_minus v = Some (Int v') ->
        do_overflow_check v' v'' ->
        do_flagged_check_on_unop Do_Overflow_Check Unary_Minus v v''.

Inductive do_flagged_checks_on_binop: check_flags -> binary_operator -> value -> value -> Return value -> Prop :=
    | Do_Check_Binop_Nil: forall op v1 v2 v,
        Math.binary_operation op v1 v2 = Some v ->
        do_flagged_checks_on_binop nil op v1 v2 (Normal v)
    | Do_Checks_Binop_RTE: forall ck op v1 v2 msg cks,
        do_flagged_check_on_binop ck op v1 v2 (Run_Time_Error msg) ->
        do_flagged_checks_on_binop (ck :: cks) op v1 v2 (Run_Time_Error msg)
    | Do_Checks_Binop: forall ck op v1 v2 v cks v',
        do_flagged_check_on_binop ck op v1 v2 (Normal v) ->
        do_flagged_checks_on_binop cks op v1 v2 v' ->
        do_flagged_checks_on_binop (ck :: cks) op v1 v2 v'.

Inductive do_flagged_checks_on_unop: check_flags -> unary_operator -> value -> Return value -> Prop :=
    | Do_Check_Unop_Nil: forall op v v',
        Math.unary_operation op v = Some v' ->
        do_flagged_checks_on_unop nil op v (Normal v')
    | Do_Checks_Unop_RTE: forall ck op v msg cks,
        do_flagged_check_on_unop ck op v (Run_Time_Error msg) ->
        do_flagged_checks_on_unop (ck :: cks) op v (Run_Time_Error msg)
    | Do_Checks_Unop: forall ck op v v' cks v'',
        do_flagged_check_on_unop ck op v (Normal v') ->
        do_flagged_checks_on_unop cks op v v'' ->
        do_flagged_checks_on_unop (ck :: cks) op v v''.

Inductive do_overflow_checks: check_flags -> Z -> Return value -> Prop :=
    | Do_Overflow_Check_Nil: forall v, 
        do_overflow_checks nil v (Normal (Int v))
    | Do_Overflow_Check_List: forall v v',
        do_overflow_check v v' ->
        do_overflow_checks (Do_Overflow_Check :: nil) v v'.

Inductive do_range_checks: check_flags -> Z -> Z -> Z -> Return value -> Prop :=
    | Do_Range_Check_Nil: forall v l u,
        do_range_checks nil v l u (Normal (Int v))
    | Do_Range_Check_List: forall v l u v',
        do_range_check v l u v' ->
        do_range_checks (Do_Range_Check :: nil) v l u v'.


(** * Relational Semantics *)

(** ** Expression Evaluation Semantics *)
(**
    for binary expression and unary expression, if a run-time error 
    is detected in any of its child expressions, then return a run-time
    error; for binary expression (e1 op e2), if both e1 and e2 
    are evaluated to some normal value, then run-time checks are
    performed according to the checking rules specified for the 
    operator 'op', whenever the check fails, a run-time error is 
    detected and the program is terminated, otherwise, normal binary 
    operation result is returned;

   - in name evaluation eval_name_x, the check flags for name are all nil, e.g.
     (E_Indexed_Component_X ast_num x_ast_num x e nil), because if there is a
     Do_Range_Check on the name expression, this range check should be enforced
     by the context where the name expression appears, that's why it's invisible 
     during the evaluation of name expression;

     take the assignment (y := x) as an example, if y is a variable of integer 
     subtype, and x is a variable of integer, then there should be a Do_Range_Check
     flag on the right side (x) of the assignment; during the evaluation of the 
     assignment, first evaluate the value of x, and then do the range check on the
     value of x against the target subtype range of y, but the Do_Range_Check should
     be invisible when evaluate the value of x even though the Do_Range_Check is set
     on the variable x, this range check should be enforced at the assignment level; 
     that's why in name evaluation eval_name_x, the check flags for name are all nil;
*)

Inductive eval_literal_x: check_flags -> literal -> Return value -> Prop :=
    | Eval_Literal_Bool_X: forall cks v,
        eval_literal_x cks (Boolean_Literal v) (Normal (Bool v))
    | Eval_Literal_Int_X: forall cks v v',
        do_overflow_checks cks v v' -> 
        eval_literal_x cks (Integer_Literal v) v'.

Inductive eval_expr_x: symboltable_x -> stack -> expression_x -> Return value -> Prop :=
    | Eval_E_Literal_X: forall l v st s ast_num in_cks ex_cks,
        eval_literal_x in_cks l v ->
        eval_expr_x st s (E_Literal_X ast_num l in_cks ex_cks) v
    | Eval_E_Name_X: forall st s n v ast_num,
        eval_name_x st s n v ->
        eval_expr_x st s (E_Name_X ast_num n) v
    | Eval_E_Binary_Operation_e1RTE_X: forall st s e1 msg ast_num op e2 in_cks ex_cks,
        eval_expr_x st s e1 (Run_Time_Error msg) ->
        eval_expr_x st s (E_Binary_Operation_X ast_num op e1 e2 in_cks ex_cks) (Run_Time_Error msg)
    | Eval_E_Binary_Operation_e2RTE_X: forall st s e1 v1 e2 msg ast_num op in_cks ex_cks,
        eval_expr_x st s e1 (Normal v1) ->
        eval_expr_x st s e2 (Run_Time_Error msg) ->
        eval_expr_x st s (E_Binary_Operation_X ast_num op e1 e2 in_cks ex_cks) (Run_Time_Error msg)
    | Eval_E_Binary_Operation_X: forall st s e1 v1 e2 v2 in_cks op v ast_num ex_cks,
        eval_expr_x st s e1 (Normal v1) ->
        eval_expr_x st s e2 (Normal v2) ->
        do_flagged_checks_on_binop in_cks op v1 v2 v ->
        eval_expr_x st s (E_Binary_Operation_X ast_num op e1 e2 in_cks ex_cks) v
    | Eval_E_Unary_Operation_eRTE_X: forall st s e msg ast_num op in_cks ex_cks,
        eval_expr_x st s e (Run_Time_Error msg) ->
        eval_expr_x st s (E_Unary_Operation_X ast_num op e in_cks ex_cks) (Run_Time_Error msg)
    | Eval_E_Unary_Operation_X: forall st s e v in_cks op v' ast_num ex_cks,
        eval_expr_x st s e (Normal v) ->
        do_flagged_checks_on_unop in_cks op v v' ->
        eval_expr_x st s (E_Unary_Operation_X ast_num op e in_cks ex_cks) v'

with eval_name_x: symboltable_x -> stack -> name_x -> Return value -> Prop :=
    | Eval_E_Identifier_X: forall x s v st ast_num ex_cks, 
        fetchG x s = Some v ->
        eval_name_x st s (E_Identifier_X ast_num x ex_cks) (Normal v)
    | Eval_E_Indexed_Component_xRTE_X: forall st s x msg ast_num e ex_cks, 
        eval_name_x st s x (Run_Time_Error msg) ->
        eval_name_x st s (E_Indexed_Component_X ast_num x e ex_cks) (Run_Time_Error msg)
    | Eval_E_Indexed_Component_eRTE_X: forall st s x a e msg ast_num ex_cks,
        eval_name_x st s x (Normal (ArrayV a)) ->
        eval_expr_x st s e (Run_Time_Error msg) ->
        eval_name_x st s (E_Indexed_Component_X ast_num x e ex_cks) (Run_Time_Error msg)
    | Eval_E_Indexed_Component_Range_RTE_X: forall st s x a e i t l u ast_num ex_cks,
        eval_name_x st s x (Normal (ArrayV a)) ->
        eval_expr_x st s e (Normal (Int i)) ->
        fetch_exp_type_x (name_astnum_x x) st = Some (Array_Type t) ->
        extract_array_index_range_x st t (Range_X l u) ->
        do_range_checks (exp_exterior_checks e) i l u (Run_Time_Error RTE_Range) ->
        eval_name_x st s (E_Indexed_Component_X ast_num x e ex_cks) (Run_Time_Error RTE_Range)
    | Eval_E_Indexed_Component_X: forall st s x a e i t l u v ast_num ex_cks,
        eval_name_x st s x (Normal (ArrayV a)) ->
        eval_expr_x st s e (Normal (Int i)) ->
        fetch_exp_type_x (name_astnum_x x) st = Some (Array_Type t) ->
        extract_array_index_range_x st t (Range_X l u) ->
        do_range_checks (exp_exterior_checks e) i l u (Normal (Int i)) ->
        array_select a i = Some v ->
        eval_name_x st s (E_Indexed_Component_X ast_num x e ex_cks) (Normal v)
    | Eval_E_Selected_Component_xRTE_X: forall st s x msg ast_num f ex_cks,
        eval_name_x st s x (Run_Time_Error msg) ->
        eval_name_x st s (E_Selected_Component_X ast_num x f ex_cks) (Run_Time_Error msg)
    | Eval_E_Selected_Component_X: forall st s x r f v ast_num ex_cks,
        eval_name_x st s x (Normal (RecordV r)) ->
        record_select r f = Some v ->
        eval_name_x st s (E_Selected_Component_X ast_num x f ex_cks) (Normal v).


(** Inductive semantic of declarations. [eval_decl_x st s f decl f'] 
    means that [f'] is the frame to be pushed on s after evaluating decl, 
    [f] is used as an accumulator for building the frame.
*)

(** ** Declaration Evaluation Semantics *)

Inductive eval_decl_x: symboltable_x -> stack -> frame -> declaration_x -> Return frame -> Prop :=
    | Eval_Decl_Null_X: forall st s f,
        eval_decl_x st s f D_Null_Declaration_X (Normal f)
    | Eval_Decl_Var_None_X: forall d st s f ast_num,
        d.(initialization_expression_x) = None ->
        eval_decl_x st s f (D_Object_Declaration_X ast_num d) (Normal (push f d.(object_name_x) Undefined))
    | Eval_Decl_Var_eRTE_X: forall d e st f s msg ast_num,
        d.(initialization_expression_x) = Some e ->
        eval_expr_x st (f :: s) e (Run_Time_Error msg) ->
        eval_decl_x st s f (D_Object_Declaration_X ast_num d) (Run_Time_Error msg)
    | Eval_Decl_Var_NoCheck_X: forall d e st f s v ast_num,
        d.(initialization_expression_x) = Some e ->
        eval_expr_x st (f :: s) e (Normal v) ->
        exp_exterior_checks e = nil ->
        eval_decl_x st s f (D_Object_Declaration_X ast_num d) (Normal (push f d.(object_name_x) v))
    | Eval_Decl_Var_Range_RTE_X: forall d e st f s v l u ast_num,
        d.(initialization_expression_x) = Some e ->
        eval_expr_x st (f :: s) e (Normal (Int v)) ->
        exp_exterior_checks e = Do_Range_Check :: nil ->
        extract_subtype_range_x st (d.(object_nominal_subtype_x)) (Range_X l u) ->
        do_range_check v l u (Run_Time_Error RTE_Range) ->
        eval_decl_x st s f (D_Object_Declaration_X ast_num d) (Run_Time_Error RTE_Range)
    | Eval_Decl_Var_X: forall d e st f s v l u ast_num,
        d.(initialization_expression_x) = Some e ->
        eval_expr_x st (f :: s) e (Normal (Int v)) ->
        exp_exterior_checks e = Do_Range_Check :: nil ->
        extract_subtype_range_x st (d.(object_nominal_subtype_x)) (Range_X l u) ->
        do_range_check v l u (Normal (Int v)) ->
        eval_decl_x st s f (D_Object_Declaration_X ast_num d) (Normal (push f d.(object_name_x) (Int v)))
    | Eval_Decl_Type_X: forall st s f ast_num t,
        eval_decl_x st s f (D_Type_Declaration_X ast_num t) (Normal f)
    | Eval_Decl_Proc_X: forall st s f ast_num p,
        eval_decl_x st s f (D_Procedure_Body_X ast_num p) (Normal f)
    | Eval_Decl_Seq_E_X: forall st s f d1 msg ast_num d2,
        eval_decl_x st s f d1 (Run_Time_Error msg) ->
        eval_decl_x st s f (D_Seq_Declaration_X ast_num d1 d2) (Run_Time_Error msg)
    | Eval_Decl_Seq_X: forall st s f d1 f' d2 f'' ast_num,
        eval_decl_x st s f d1 (Normal f') ->
        eval_decl_x st s f' d2 f'' ->
        eval_decl_x st s f (D_Seq_Declaration_X ast_num d1 d2) f''.


(** update name with new value in the stack and return newly updated stack 
 
    the run-time check flags on the name expression will not affect the store update,
    they are only used when the expression is used on the right hand side of assignment;
*)

Inductive storeUpdate_x: symboltable_x -> stack -> name_x -> value -> Return stack -> Prop := 
    | SU_Identifier_X: forall s x v s1 st ast_num cks,
        updateG s x v = Some s1 ->
        storeUpdate_x st s (E_Identifier_X ast_num x cks) v (Normal s1)
    | SU_Indexed_Component_xRTE_X: forall st s x msg ast_num e cks v,
        eval_name_x st s x (Run_Time_Error msg) ->
        storeUpdate_x st s (E_Indexed_Component_X ast_num x e cks) v (Run_Time_Error msg)
    | SU_Indexed_Component_eRTE_X: forall st s x a e msg ast_num cks v,
        eval_name_x st s x (Normal (ArrayV a)) \/ eval_name_x st s x (Normal Undefined) ->
        eval_expr_x st s e (Run_Time_Error msg) ->
        storeUpdate_x st s (E_Indexed_Component_X ast_num x e cks) v (Run_Time_Error msg)
    | SU_Indexed_Component_Range_RTE_X: forall st s x a e i t l u ast_num cks v,
        eval_name_x st s x (Normal (ArrayV a)) \/ eval_name_x st s x (Normal Undefined) ->
        eval_expr_x st s e (Normal (Int i)) ->
        fetch_exp_type_x (name_astnum_x x) st = Some (Array_Type t) ->
        extract_array_index_range_x st t (Range_X l u) ->
        do_range_checks (exp_exterior_checks e) i l u (Run_Time_Error RTE_Range) ->
        storeUpdate_x st s (E_Indexed_Component_X ast_num x e cks) v (Run_Time_Error RTE_Range)
    | SU_Indexed_Component_X: forall st s x arrObj a e i t l u v a1 s1 ast_num cks,
        eval_name_x st s x (Normal arrObj) ->
        arrObj = (ArrayV a) \/ arrObj = Undefined ->
        eval_expr_x st s e (Normal (Int i)) ->
        fetch_exp_type_x (name_astnum_x x) st = Some (Array_Type t) ->
        extract_array_index_range_x st t (Range_X l u) ->
        do_range_checks (exp_exterior_checks e) i l u (Normal (Int i)) ->
        arrayUpdate arrObj i v = (Some (ArrayV a1)) -> 
        storeUpdate_x st s x (ArrayV a1) s1 ->
        storeUpdate_x st s (E_Indexed_Component_X ast_num x e cks) v s1
    | SU_Selected_Component_xRTE_X: forall st s x msg ast_num f cks v,
        eval_name_x st s x (Run_Time_Error msg) ->
        storeUpdate_x st s (E_Selected_Component_X ast_num x f cks) v (Run_Time_Error msg)
    | SU_Selected_Component_X: forall st s x recObj r f v r1 s1 ast_num cks,
        eval_name_x st s x (Normal recObj) ->
        recObj = (RecordV r) \/ recObj = Undefined ->
        recordUpdate recObj f v = Some (RecordV r1) ->
        storeUpdate_x st s x (RecordV r1) s1 ->
        storeUpdate_x st s (E_Selected_Component_X ast_num x f cks) v s1.


(** ** Statement Evaluation Semantics *)

(** Stack manipulation for procedure calls and return *)

(** *** Copy In *)

Inductive copy_in_x: symboltable_x -> stack -> frame -> list parameter_specification_x -> list expression_x -> Return frame -> Prop :=
    | Copy_In_Nil_X : forall st s f, 
        copy_in_x st s f nil nil (Normal f)
    | Copy_In_Mode_In_eRTE_X: forall param st s e msg f lparam le,
        param.(parameter_mode_x) = In ->
        eval_expr_x st s e (Run_Time_Error msg) ->
        copy_in_x st s f (param :: lparam) (e :: le) (Run_Time_Error msg)
    | Copy_In_Mode_In_NoRangeCheck_X: forall param st s e v f f' lparam le f'',
        param.(parameter_mode_x) = In ->
        eval_expr_x st s e (Normal v) ->
        exp_exterior_checks e = nil ->
        push f param.(parameter_name_x) v = f' ->
        copy_in_x st s f' lparam le f'' ->
        copy_in_x st s f (param :: lparam) (e :: le) f''
    | Copy_In_Mode_In_Range_RTE_X: forall param st s e v l u f lparam le,
        param.(parameter_mode_x) = In ->
        eval_expr_x st s e (Normal (Int v)) ->
        exp_exterior_checks e = Do_Range_Check :: nil ->
        extract_subtype_range_x st (param.(parameter_subtype_mark_x)) (Range_X l u) ->
        do_range_check v l u (Run_Time_Error RTE_Range) ->
        copy_in_x st s f (param :: lparam) (e :: le) (Run_Time_Error RTE_Range)
    | Copy_In_Mode_In_Range_X: forall param st s e v l u f f' lparam le f'',
        param.(parameter_mode_x) = In ->
        eval_expr_x st s e (Normal (Int v)) ->
        exp_exterior_checks e = Do_Range_Check :: nil ->
        extract_subtype_range_x st (param.(parameter_subtype_mark_x)) (Range_X l u) ->
        do_range_check v l u (Normal (Int v)) ->
        push f param.(parameter_name_x) (Int v) = f' ->
        copy_in_x st s f' lparam le f'' ->
        copy_in_x st s f (param :: lparam) (e :: le) f''
    | Copy_In_Mode_InOut_eRTE_x: forall param st s n msg f lparam ast_num le,
        param.(parameter_mode_x) = In_Out ->
        eval_name_x st s n (Run_Time_Error msg) ->
        copy_in_x st s f (param :: lparam) ((E_Name_X ast_num n) :: le) (Run_Time_Error msg)
    | Copy_In_Mode_InOut_NoRange_X: forall param st s n v f f' lparam le f'' ast_num,
        param.(parameter_mode_x) = In_Out ->
        eval_name_x st s n (Normal v) ->
        ~(List.In Do_Range_Check (name_exterior_checks n)) ->
        push f param.(parameter_name_x) v = f' ->
        copy_in_x st s f' lparam le f'' ->
        copy_in_x st s f (param :: lparam) ((E_Name_X ast_num n) :: le) f''
    | Copy_In_Mode_InOut_Range_RTE_X: forall param st s n v l u f lparam le ast_num,
        param.(parameter_mode_x) = In_Out ->
        eval_name_x st s n (Normal (Int v)) ->
        List.In Do_Range_Check (name_exterior_checks n) -> (*n may have both Do_Range_Check and Do_Range_Check_On_CopyOut*)
        extract_subtype_range_x st (param.(parameter_subtype_mark_x)) (Range_X l u) ->
        do_range_check v l u (Run_Time_Error RTE_Range) ->
        copy_in_x st s f (param :: lparam) ((E_Name_X ast_num n) :: le) (Run_Time_Error RTE_Range)
    | Copy_In_Mode_InOut_Range_X: forall param st s n v l u f f' lparam le f'' ast_num,
        param.(parameter_mode_x) = In_Out ->
        eval_name_x st s n (Normal (Int v)) ->
        List.In Do_Range_Check (name_exterior_checks n) ->
        extract_subtype_range_x st (param.(parameter_subtype_mark_x)) (Range_X l u) ->
        do_range_check v l u (Normal (Int v)) ->
        push f param.(parameter_name_x) (Int v) = f' ->
        copy_in_x st s f' lparam le f'' ->
        copy_in_x st s f (param :: lparam) ((E_Name_X ast_num n) :: le) f''
    | Copy_In_Mode_Out_X: forall param f f' st s lparam le f'' ast_num n,
        param.(parameter_mode_x) = Out ->
        push f param.(parameter_name_x) Undefined = f' ->
        copy_in_x st s f' lparam le f'' ->
        copy_in_x st s f (param :: lparam) ((E_Name_X ast_num n) :: le) f''.


(** *** Copy Out *)

Inductive copy_out_x: symboltable_x -> stack -> frame -> list parameter_specification_x -> list expression_x -> Return stack -> Prop :=
    | Copy_Out_Nil_X : forall st s f, 
        copy_out_x st s f nil nil (Normal s)
    | Copy_Out_Mode_Out_nRTE: forall param f v n st s msg lparam lexp ast_num,
        param.(parameter_mode_x) = Out \/ param.(parameter_mode_x) = In_Out ->
        fetch param.(parameter_name_x) f = Some v ->
        ~(List.In Do_Range_Check_On_CopyOut (name_exterior_checks n)) ->
        storeUpdate_x st s n v (Run_Time_Error msg) ->
        copy_out_x st s f (param :: lparam) ((E_Name_X ast_num n) :: lexp) (Run_Time_Error msg)
    | Copy_Out_Mode_Out_NoRange_X: forall param f v n st s s' lparam lexp s'' ast_num,
        param.(parameter_mode_x) = Out \/ param.(parameter_mode_x) = In_Out ->
        fetch param.(parameter_name_x) f = Some v ->
        ~(List.In Do_Range_Check_On_CopyOut (name_exterior_checks n)) ->
        storeUpdate_x st s n v (Normal s') ->
        copy_out_x st s' f lparam lexp s'' ->
        copy_out_x st s f (param :: lparam) ((E_Name_X ast_num n) :: lexp) s''
    | Copy_Out_Mode_Out_Range_RTE_X: forall param f v n ast_num st t l u s lparam lexp,
        param.(parameter_mode_x) = Out \/ param.(parameter_mode_x) = In_Out ->
        fetch param.(parameter_name_x) f = Some (Int v) ->
        List.In Do_Range_Check_On_CopyOut (name_exterior_checks n) ->
        fetch_exp_type_x ast_num st = Some t ->
        extract_subtype_range_x st t (Range_X l u) ->
        do_range_check v l u (Run_Time_Error RTE_Range) ->
        copy_out_x st s f (param :: lparam) ((E_Name_X ast_num n) :: lexp) (Run_Time_Error RTE_Range)
    | Copy_Out_Mode_Out_Range_nRTE_X: forall param f v n ast_num st t l u s msg lparam lexp,
        param.(parameter_mode_x) = Out \/ param.(parameter_mode_x) = In_Out ->
        fetch param.(parameter_name_x) f = Some (Int v) ->
        List.In Do_Range_Check_On_CopyOut (name_exterior_checks n) ->
        fetch_exp_type_x ast_num st = Some t ->
        extract_subtype_range_x st t (Range_X l u) ->
        do_range_check v l u (Normal (Int v)) ->
        storeUpdate_x st s n (Int v) (Run_Time_Error msg) ->
        copy_out_x st s f (param :: lparam) ((E_Name_X ast_num n) :: lexp) (Run_Time_Error msg)
    | Copy_Out_Mode_Out_Range_X: forall param f v n ast_num st t l u s s' lparam lexp s'',
        param.(parameter_mode_x) = Out \/ param.(parameter_mode_x) = In_Out ->
        fetch param.(parameter_name_x) f = Some (Int v) ->
        List.In Do_Range_Check_On_CopyOut (name_exterior_checks n) ->
        fetch_exp_type_x ast_num st = Some t ->
        extract_subtype_range_x st t (Range_X l u) ->
        do_range_check v l u (Normal (Int v)) ->
        storeUpdate_x st s n (Int v) (Normal s') ->
        copy_out_x st s' f lparam lexp s'' ->
        copy_out_x st s f (param :: lparam) ((E_Name_X ast_num n) :: lexp) s''
    | Copy_Out_Mode_In_X: forall param st s f lparam lexp s' e,
        param.(parameter_mode_x) = In ->
        copy_out_x st s f lparam lexp s' ->
        copy_out_x st s f (param :: lparam) (e :: lexp) s'.


(** Inductive semantic of statement and declaration

   in a statement evaluation, whenever a run time error is detected in
   the evaluation of its sub-statements or sub-component, the
   evaluation is terminated and return a run-time error; otherwise,
   evaluate the statement into a normal state.

   - in the evaluation for assignment statement (S_Assignment_X ast_num x e),

     first, check if there is a Do_Range_Check flag on the right side (e) of 
     the assignment, 
     case 1: ~(List.In Do_Range_Check (exp_check_flags e)) means
     no range check needed for the value of expression e, 
     case 2: (exp_check_flags e = cks1 ++ Do_Range_Check :: cks2) means
     a range check required on the value of expression e;

     second, if there is no range check required for e, then do expression 
     evaluation directly on e and update the value of x if there is no run-time
     errors during their evaluation;
     if there is a range check required for e, then a range check should be 
     performed on the evaluation value of e before it's assigned to the left side
     (x) of the assignment; 
     
     please note that the range check for the value of expression e is verified 
     against the target type taken from the left side (x) of the assignment, that's
     why the range check for expression e is enforced at the level of assignment 
     statement even though the Do_Range_Check flag is set on the expression e, and
     that's also why we remove the Do_Range_Check flag from e's run-time check flag
     set before the evaluation of e;

   - in the store update storeUpdate_x for indexed component (e.g. a(i):=v) or selected
     component (e.g. r.f := v), 
     
     if the value of array a (or value of record r) is Undefined, then create a new 
     aggregate array value with its ith element having value v (or create a new record 
     value with its field f having value v), and assign this new aggregate value to array 
     variable a (or record variable r);
     
     if the value of array a (or value of record r) is already defined, then update the
     ith element of its array value (or update the filed f of its record value), and assign
     the updated aggregate value to array variable a (or record variable r);

   - in the store update storeUpdate_x for indexed component (e.g. a(i):=v), a
     range check may be required on the value of index expression i if Do_Range_Check
     is set for it, and the range check should be performed for the value of i before
     it's used to update the array value;
 *)

Inductive eval_stmt_x: symboltable_x -> stack -> statement_x -> Return stack -> Prop := 
    | Eval_S_Null_X: forall st s,
        eval_stmt_x st s S_Null_X (Normal s)
    | Eval_S_Assignment_eRTE_X: forall st s e msg ast_num x,
        eval_expr_x st s e (Run_Time_Error msg) ->
        eval_stmt_x st s (S_Assignment_X ast_num x e) (Run_Time_Error msg)
    | Eval_S_Assignment_X: forall st s e v x s1 ast_num,
        eval_expr_x st s e (Normal v) ->
        exp_exterior_checks e = nil ->
        storeUpdate_x st s x v s1 ->
        eval_stmt_x st s (S_Assignment_X ast_num x e) s1
    | Eval_S_Assignment_Range_RTE_X: forall st s e v x t l u ast_num,
        eval_expr_x st s e (Normal (Int v)) ->
        exp_exterior_checks e = Do_Range_Check :: nil ->
        fetch_exp_type_x (name_astnum_x x) st = Some t ->
        extract_subtype_range_x st t (Range_X l u) ->
        do_range_check v l u (Run_Time_Error RTE_Range) ->
        eval_stmt_x st s (S_Assignment_X ast_num x e) (Run_Time_Error RTE_Range)
    | Eval_S_Assignment_Range_X: forall st s e v x t l u s1 ast_num,
        eval_expr_x st s e (Normal (Int v)) ->
        exp_exterior_checks e = Do_Range_Check :: nil ->
        fetch_exp_type_x (name_astnum_x x) st = Some t ->
        extract_subtype_range_x st t (Range_X l u) ->
        do_range_check v l u (Normal (Int v)) ->
        storeUpdate_x st s x (Int v) s1 ->
        eval_stmt_x st s (S_Assignment_X ast_num x e) s1
    | Eval_S_If_RTE_X: forall st s b msg ast_num c1 c2,
        eval_expr_x st s b (Run_Time_Error msg) ->
        eval_stmt_x st s (S_If_X ast_num b c1 c2) (Run_Time_Error msg)
    | Eval_S_If_True_X: forall st s b c1 s1 ast_num c2,
        eval_expr_x st s b (Normal (Bool true)) ->
        eval_stmt_x st s c1 s1 ->
        eval_stmt_x st s (S_If_X ast_num b c1 c2) s1
    | Eval_S_If_False_X: forall st s b c2 s1 ast_num c1,
        eval_expr_x st s b (Normal (Bool false)) ->
        eval_stmt_x st s c2 s1 ->
        eval_stmt_x st s (S_If_X ast_num b c1 c2) s1
    | Eval_S_While_Loop_RTE_X: forall st s b msg ast_num c,
        eval_expr_x st s b (Run_Time_Error msg) ->
        eval_stmt_x st s (S_While_Loop_X ast_num b c) (Run_Time_Error msg)
    | Eval_S_While_Loop_True_RTE_X: forall st s b c msg ast_num,
        eval_expr_x st s b (Normal (Bool true)) ->
        eval_stmt_x st s c (Run_Time_Error msg) ->
        eval_stmt_x st s (S_While_Loop_X ast_num b c) (Run_Time_Error msg)
    | Eval_S_While_Loop_True_X: forall st s b c s1 ast_num s2,
        eval_expr_x st s b (Normal (Bool true)) ->
        eval_stmt_x st s c (Normal s1) ->
        eval_stmt_x st s1 (S_While_Loop_X ast_num b c) s2 ->
        eval_stmt_x st s (S_While_Loop_X ast_num b c) s2
    | Eval_S_While_Loop_False_X: forall st s b ast_num c,
        eval_expr_x st s b (Normal (Bool false)) ->
        eval_stmt_x st s (S_While_Loop_X ast_num b c) (Normal s)
    | Eval_S_Proc_RTE_Args_X: forall p st n pb s args msg ast_num p_ast_num,
        fetch_proc_x p st = Some (n, pb) ->
        copy_in_x st s (newFrame n) (procedure_parameter_profile_x pb) args (Run_Time_Error msg) ->
        eval_stmt_x st s (S_Procedure_Call_X ast_num p_ast_num p args) (Run_Time_Error msg)
    | Eval_S_Proc_RTE_Decl_X: forall p st n pb s args f intact_s s1 msg ast_num p_ast_num,
        fetch_proc_x p st = Some (n, pb) ->
        copy_in_x st s (newFrame n) (procedure_parameter_profile_x pb) args (Normal f) ->
        cut_until s n intact_s s1 -> (* s = intact_s ++ s1 *)
        eval_decl_x st s1 f (procedure_declarative_part_x pb) (Run_Time_Error msg) ->
        eval_stmt_x st s (S_Procedure_Call_X ast_num p_ast_num p args) (Run_Time_Error msg)
    | Eval_S_Proc_RTE_Body_X: forall p st n pb s args f intact_s s1 f1 msg ast_num p_ast_num,
        fetch_proc_x p st = Some (n, pb) ->
        copy_in_x st s (newFrame n) (procedure_parameter_profile_x pb) args (Normal f) ->
        cut_until s n intact_s s1 -> (* s = intact_s ++ s1 *)
        eval_decl_x st s1 f (procedure_declarative_part_x pb) (Normal f1) ->
        eval_stmt_x st (f1 :: s1) (procedure_statements_x pb) (Run_Time_Error msg) ->
        eval_stmt_x st s (S_Procedure_Call_X ast_num p_ast_num p args) (Run_Time_Error msg)
    | Eval_S_Proc_X: forall p st n pb s args f intact_s s1 f1 s2 locals_section params_section s3 s4 ast_num p_ast_num,
        fetch_proc_x p st = Some (n, pb) ->
        copy_in_x st s (newFrame n) (procedure_parameter_profile_x pb) args (Normal f) ->
        cut_until s n intact_s s1 -> (* s = intact_s ++ s1 *)
        eval_decl_x st s1 f (procedure_declarative_part_x pb) (Normal f1) ->          
        eval_stmt_x st (f1 :: s1) (procedure_statements_x pb) (Normal s2) ->
        s2 = (n, locals_section ++ params_section) :: s3 -> (* extract parameters from local frame *)
        List.length (store_of f) = List.length params_section ->
        copy_out_x st (intact_s ++ s3) (n, params_section) (procedure_parameter_profile_x pb) args s4 ->
        eval_stmt_x st s (S_Procedure_Call_X ast_num p_ast_num p args) s4
    | Eval_S_Sequence_RTE_X: forall st s c1 msg ast_num c2,
        eval_stmt_x st s c1 (Run_Time_Error msg) ->
        eval_stmt_x st s (S_Sequence_X ast_num c1 c2) (Run_Time_Error msg)
    | Eval_S_Sequence_X: forall st s c1 s1 c2 s2 ast_num,
        eval_stmt_x st s c1 (Normal s1) ->
        eval_stmt_x st s1 c2 s2 ->
        eval_stmt_x st s (S_Sequence_X ast_num c1 c2) s2.



(** * Help Lemmas *)

Lemma eval_exp_ex_cks_added: forall st s e v cks, 
  eval_expr_x st s e v ->
    eval_expr_x st s (update_exterior_checks_exp e cks) v.
Proof.
  intros; destruct e; 
  inversion H; smack;
  match goal with
  | [H: eval_literal_x _ _ _ |- _] => constructor; smack
  | _ => idtac
  end;
  [ |
    apply Eval_E_Binary_Operation_e1RTE_X; auto |
    apply Eval_E_Binary_Operation_e2RTE_X with (v1:=v1); auto |
    apply Eval_E_Binary_Operation_X with (v1:=v1) (v2:=v2); auto |
    apply Eval_E_Unary_Operation_eRTE_X; auto |
    apply Eval_E_Unary_Operation_X with (v := v0); auto
  ];
  match goal with
  | [H: eval_name_x _ _ ?n _ |- _] => inversion H; smack; constructor
  end;
  [ apply Eval_E_Identifier_X; auto |
    apply Eval_E_Indexed_Component_xRTE_X; auto |
    apply Eval_E_Indexed_Component_eRTE_X with (a := a0); auto |
    apply Eval_E_Indexed_Component_Range_RTE_X with (a:=a0) (i:=i) (t:=t) (l:=l) (u:=u); auto |
    apply Eval_E_Indexed_Component_X with (a:=a0) (i:=i) (t:=t) (l:=l) (u:=u); auto |
    apply Eval_E_Selected_Component_xRTE_X; auto |
    apply Eval_E_Selected_Component_X with (r:=r); auto
  ].
Qed.

Lemma eval_name_ex_cks_added: forall st s n v cks, 
  eval_name_x st s n v ->
    eval_name_x st s (update_exterior_checks_name n cks) v.
Proof.
  intros; destruct n; 
  inversion H; smack;
  [ apply Eval_E_Identifier_X; auto |
    apply Eval_E_Indexed_Component_xRTE_X; auto |
    apply Eval_E_Indexed_Component_eRTE_X with (a:=a0); auto |
    apply Eval_E_Indexed_Component_Range_RTE_X with (a:=a0) (i:=i) (t:=t) (l:=l) (u:=u); auto |
    apply Eval_E_Indexed_Component_X with (a:=a0) (i:=i) (t:=t) (l:=l) (u:=u); auto |
    apply Eval_E_Selected_Component_xRTE_X; auto |
    apply Eval_E_Selected_Component_X with (r:=r); auto
  ].
Qed.

Scheme expression_ind := Induction for expression Sort Prop 
                         with name_ind := Induction for name Sort Prop.

Scheme expression_x_ind := Induction for expression_x Sort Prop 
                         with name_x_ind := Induction for name_x Sort Prop.

Lemma eval_exp_ex_cks_stripped: forall e st s cks v,
  eval_expr_x st s (update_exterior_checks_exp e cks) v ->
    eval_expr_x st s e v.
Proof.
  apply (expression_x_ind
    (fun e: expression_x =>
       forall (st : symboltable_x) (s : STACK.stack) (cks : exterior_checks) (v : Return value),
      eval_expr_x st s (update_exterior_checks_exp e cks) v ->
      eval_expr_x st s e v)
    (fun n: name_x =>
       forall (st : symboltable_x) (s : STACK.stack) (cks : exterior_checks) (v : Return value),
      eval_name_x st s (update_exterior_checks_name n cks) v ->
      eval_name_x st s n v)
    ); intros;
  match goal with
  | [H: eval_expr_x _ _ _ _ |- _] => inversion H; subst
  | [H: eval_name_x _ _ _ _ |- _] => inversion H; subst
  end.
- constructor; auto.
- constructor; auto.
  specialize (H _ _ _ _ H6); auto.
- apply Eval_E_Binary_Operation_e1RTE_X.
  rewrite <- (exp_exterior_checks_refl e) in H11.
  specialize (H _ _ _ _ H11); auto.
- apply Eval_E_Binary_Operation_e2RTE_X with (v1 := v1);
  rewrite <- (exp_exterior_checks_refl e) in H11;
  rewrite <- (exp_exterior_checks_refl e0) in H12;
  specialize (H _ _ _ _ H11); auto;
  specialize (H0 _ _ _ _ H12); auto.
- apply Eval_E_Binary_Operation_X with (v1 := v1) (v2 := v2); auto.
- apply Eval_E_Unary_Operation_eRTE_X; auto.
- apply Eval_E_Unary_Operation_X with (v := v0); auto.
- constructor; auto.
- apply Eval_E_Indexed_Component_xRTE_X.
  rewrite <- (name_exterior_checks_refl n) in H9;
  specialize (H _ _ _ _ H9); auto.
- apply Eval_E_Indexed_Component_eRTE_X with (a := a0); auto.
- apply Eval_E_Indexed_Component_Range_RTE_X with (a := a0) (i := i) (t := t) (l := l) (u := u); auto.
- apply Eval_E_Indexed_Component_X with (a := a0) (i := i) (t := t) (l := l) (u := u); auto.
- apply Eval_E_Selected_Component_xRTE_X; auto.
- apply Eval_E_Selected_Component_X with (r := r); auto.
Qed.

Lemma eval_name_ex_cks_stripped: forall n st s cks v,
  eval_name_x st s (update_exterior_checks_name n cks) v ->
      eval_name_x st s n v.
Proof.
  induction n; intros;
  inversion H; subst.
- constructor; auto.
- apply Eval_E_Indexed_Component_xRTE_X; auto.
- apply Eval_E_Indexed_Component_eRTE_X with (a := a0); auto.
- apply Eval_E_Indexed_Component_Range_RTE_X with (a := a0) (i := i) (t := t) (l := l) (u := u); auto.
- apply Eval_E_Indexed_Component_X with (a := a0) (i := i) (t := t) (l := l) (u := u); auto.
- apply Eval_E_Selected_Component_xRTE_X; auto.
- apply Eval_E_Selected_Component_X with (r := r); auto.  
Qed.

(** when the name expression is used as an address to update the store, then its exterior run-time
    check flags will not affect the store update; the run-time check flags are only used when the 
    name expression is to be evaluated as a value on the right hand side of assignment;
*)

Lemma store_update_ex_cks_added: forall st s n cks v s',
  storeUpdate_x st s n v s' ->
    storeUpdate_x st s (update_exterior_checks_name n cks) v s'.
Proof.
  induction n; intros;
  inversion H; subst.
- apply SU_Identifier_X; auto.
- apply SU_Indexed_Component_xRTE_X; auto.
- apply SU_Indexed_Component_eRTE_X with (a := a0); auto.
- apply SU_Indexed_Component_Range_RTE_X with (a := a0) (i := i) (t := t) (l := l) (u := u); auto.
- apply SU_Indexed_Component_X with (arrObj := arrObj) (a := a0) 
                                    (i := i) (t := t) (l := l) (u := u) (a1 := a1); auto.
- apply SU_Selected_Component_xRTE_X; auto.
- apply SU_Selected_Component_X with (recObj := recObj) (r := r) (r1 :=r1); auto.
Qed.

Ltac apply_store_update_ex_cks_added :=
  match goal with
  | [|- storeUpdate_x _ _ (update_exterior_checks_name _ _) _ _] =>
      apply store_update_ex_cks_added; auto
  end.

Lemma store_update_ex_cks_stripped: forall st s n cks v s',
  storeUpdate_x st s (update_exterior_checks_name n cks) v s' ->
    storeUpdate_x st s n v s'.
Proof.
  induction n; intros;
  inversion H; subst.
- apply SU_Identifier_X; auto.
- apply SU_Indexed_Component_xRTE_X; auto.
- apply SU_Indexed_Component_eRTE_X with (a := a0); auto.
- apply SU_Indexed_Component_Range_RTE_X with (a := a0) (i := i) (t := t) (l := l) (u := u); auto.
- apply SU_Indexed_Component_X with (arrObj := arrObj) (a := a0) 
                                    (i := i) (t := t) (l := l) (u := u) (a1 := a1); auto.
- apply SU_Selected_Component_xRTE_X; auto.
- apply SU_Selected_Component_X with (recObj := recObj) (r := r) (r1 :=r1); auto.
Qed.

Ltac apply_store_update_ex_cks_stripped :=
  match goal with
  | [H: storeUpdate_x _ _ (update_exterior_checks_name _ _) _ _ |- _] =>
      specialize (store_update_ex_cks_stripped _ _ _ _ _ _ H);
      let HZ := fresh "HZ" in intro HZ
  end.

(***********************************************************)

Lemma binop_arithm_operand_format: forall cks op v1 v2 v,
  do_flagged_checks_on_binop cks op v1 v2 (Normal (Int v)) ->
    exists n1 n2, v1 = Int n1 /\ v2 = Int n2.
Proof.
  intros.
  inversion H; subst.
  clear H.
  destruct op; smack;
  destruct v1, v2; smack.
  clear H H1.
  inversion H0; subst.
  destruct op; smack;
  destruct v1, v2; smack.
  destruct v0; destruct v3; inversion H; smack.
Qed.

Ltac apply_binop_arithm_operand_format :=
  match goal with
  | [H: do_flagged_checks_on_binop _ _ _ _ (Normal (Int _)) |- _] =>
      specialize (binop_arithm_operand_format _ _ _ _ _ H);
      let HZ := fresh "HZ" in
      let HZ1 := fresh "HZ" in 
      let HZ2 := fresh "HZ" in
      let n1 := fresh "n" in 
      let n2 := fresh "n" in 
      intros HZ;
      destruct HZ as [n1 [n2 [HZ1 HZ2]]]
  end.

Lemma unop_arithm_operand_format: forall cks op v v',
  do_flagged_checks_on_unop cks op v (Normal (Int v')) ->
    exists n, v = Int n.
Proof.
  intros.
  inversion H; subst.
  clear H.
  destruct op; destruct v; smack.
  clear H H1.
  inversion H0; subst.
  destruct v; inversion H; smack.
Qed.

Ltac apply_unop_arithm_operand_format :=
  match goal with
  | [H: do_flagged_checks_on_unop _ _ _ (Normal (Int _)) |- _] =>
      specialize (unop_arithm_operand_format _ _ _ _ H);
      let HZ := fresh "HZ" in
      let HZ1 := fresh "HZ" in 
      let n := fresh "n" in 
      intros HZ; destruct HZ as [n HZ1]
  end.










