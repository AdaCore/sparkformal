Require Export environment.
Require Export checks.
Require Export language_flagged.
Require Export semantics_flagged.


Inductive bound_of_type: symboltable_x -> type -> bound -> Prop :=
  | Bound_Of_Boolean: forall st,
      bound_of_type st Boolean Boolval
  | Bound_Of_Integer: forall st,
      bound_of_type st Integer int32_bound
  | Bound_Of_Subtype: forall st t l u,
      extract_subtype_range_x st t (Range_X l u) ->
      bound_of_type st t (Interval l u)
  | Bound_Of_Composite_Type: forall t t1 st,
      t = Array_Type t1 \/ t = Record_Type t1 ->
      bound_of_type st t Aggregate.

(** t: type id of the array type; (l, u) is the domain of the array component type *)
Inductive bound_of_array_component_type : symboltable_x -> typenum -> bound -> Prop :=
  | Array_Component_Value : forall t st ast_num tn indexSubtypeMark componentType boundValue,
      fetch_type_x t st = Some (Array_Type_Declaration_X ast_num tn indexSubtypeMark componentType) ->
      bound_of_type st componentType boundValue ->
      bound_of_array_component_type st t boundValue.

Function record_field_type (r: list (idnum * type)) (f: idnum): option type :=
  match r with 
  | (f1, t1) :: r1 =>
      if beq_nat f1 f then 
        Some t1
      else
        record_field_type r1 f
  | nil => None 
  end.

(** t: type id of the record type; f: field id; ft: field type id *)
Inductive bound_of_record_field_type : symboltable_x -> typenum -> idnum -> bound -> Prop :=
  | Record_Field_Value : forall t st ast_num tn fields f ft boundValue,
      fetch_type_x t st = Some (Record_Type_Declaration_X ast_num tn fields) ->
      record_field_type fields f = Some ft ->
      bound_of_type st ft boundValue ->
      bound_of_record_field_type st t f boundValue.

(** during run-time check optimization, a check flag "ck" will be removed from a set of check
    flags "(ck' :: cks)" once the check is unnecessary;
*)
Function remove_check_flag (ck: check_flag) (cks: check_flags): check_flags :=
  match cks with
  | (x :: cks') =>
      let y := remove_check_flag ck cks' in
      if beq_check_flag ck x then
        y
      else
        x :: y
  | nil => nil
  end.

(*
Inductive remove_check_flag: check_flag -> check_flags -> check_flags -> Prop :=
  | R_Check_Flag_Nil: forall ck,
      remove_check_flag ck nil nil
  | R_Check_Flag_Head: forall ck ck' cks cks',
      beq_check_flag ck ck' = true ->
      remove_check_flag ck cks cks' ->
      remove_check_flag ck (ck' :: cks) cks'
  | R_Check_Flag_Tail: forall ck ck' cks cks',
      beq_check_flag ck ck' = false ->
      remove_check_flag ck cks cks' ->
      remove_check_flag ck (ck' :: cks) (ck' :: cks').
*)

(** check whether a bound is sub-bound of another one *)
Inductive sub_bound: bound -> bound -> bool -> Prop :=
  | SB_True: forall u u' v' v,
      in_bound u (Interval u' v') true ->
      in_bound v (Interval u' v') true ->
      sub_bound (Interval u v) (Interval u' v') true
  | SB_False: forall u u' v' v,
      in_bound u (Interval u' v') false \/ in_bound v (Interval u' v') false ->
      sub_bound (Interval u v) (Interval u' v') false.

(** if the bound (Interval u v) is within the bound of the integer type,
    then optimize away the overflow check from the check set "cks", return 
    the optimized run-time check flags, and return the resulting bound 
    (Interval u v) if it's within integer bound, otherwise, return int32_bound;
*)
Inductive optimize_overflow_check: bound -> check_flags -> (bound * check_flags) -> Prop :=
  | OOC_True: forall u v cks' cks,
      sub_bound (Interval u v) int32_bound true ->
      cks' = remove_check_flag Do_Overflow_Check cks ->
      optimize_overflow_check (Interval u v) cks ((Interval u v), cks')
  | OOC_False: forall u v cks,
      sub_bound (Interval u v) int32_bound false ->
      optimize_overflow_check (Interval u v) cks (int32_bound, cks).

(** given an expression and its possible value bound, if it's used in a context where
    a range constraint is enforced, then check whether the value bound of the expression 
    is within the range constraint required by the context, if it's so, the range check 
    can be optimized away; 
*)
Inductive optimize_range_check: expression_x -> bound -> bound -> expression_x -> Prop :=
  | ORC_True: forall u v u' v' cks e e',
      sub_bound (Interval u v) (Interval u' v') true ->
      cks = remove_check_flag Do_Range_Check (exp_exterior_checks e) ->
      e' = update_exterior_checks_exp e cks ->
      optimize_range_check e (Interval u v) (Interval u' v') e'
  | ORC_False: forall u v u' v' e,
      sub_bound (Interval u v) (Interval u' v') false ->
      optimize_range_check e (Interval u v) (Interval u' v') e.

Inductive optimize_range_check_on_copy_out: expression_x -> bound -> bound -> expression_x -> Prop :=
  | ORCOCO_True: forall u v u' v' cks e e',
      sub_bound (Interval u v) (Interval u' v') true ->
      cks = remove_check_flag Do_Range_Check_On_CopyOut (exp_exterior_checks e) ->
      e' = update_exterior_checks_exp e cks ->
      optimize_range_check_on_copy_out e (Interval u v) (Interval u' v') e'
  | ORCOCO_False: forall u v u' v' e,
      sub_bound (Interval u v) (Interval u' v') false ->
      optimize_range_check_on_copy_out e (Interval u v) (Interval u' v') e.

(*
(** if the bound (Interval u v) is within the bound (Interval u' v'), then optimize 
    away the run-time check flag "ck" from the check set "cks", return the optimized
    run-time check flags, and return the resulting bound (Interval u v) if it's within
    the bound (Interval u' v'), otherwise, return bound (Interval u' v');
*)
Inductive optimize_run_time_check: check_flag -> check_flags -> bound -> bound -> (bound * check_flags) -> Prop :=
  | O_RTC_True: forall u v u' v' cks' ck cks,
      sub_bound (Interval u v) (Interval u' v') true ->
      cks' = remove_check_flag ck cks ->
      optimize_run_time_check ck cks (Interval u v) (Interval u' v') ((Interval u v), cks')
  | O_RTC_False: forall u v u' v' ck cks,
      sub_bound (Interval u v) (Interval u' v') false ->
      optimize_run_time_check ck cks (Interval u v) (Interval u' v') ((Interval u' v'), cks).
*)

(** optimization for binary operation, in the following rule: 
    optimize_rtc_binop op (Interval u v) (Interval u' v') ck (Interval x y, cks'),
    op: the binary operator;
    cks: the run-time checks enforced on the binary operation;
    (Interval u v): the bound of possible values of the left hand side of binary operator;
    (Interval u' v'): the bound of possible values of the right hand side of binary operator;
    Interval x y: the result bound of binary operation;
    cks': the result run-time check flags after the optimization;
*)
Inductive optimize_rtc_binop: binary_operator -> bound -> bound -> check_flags -> (bound * check_flags) -> Prop :=
  | O_RTC_Plus: forall u u' x v v' y cks retBound cks',
      Math.add (Int u) (Int u') = Some (Int x) -> 
      Math.add (Int v) (Int v') = Some (Int y) ->
      optimize_overflow_check (Interval x y) cks (retBound, cks') ->
      optimize_rtc_binop Plus (Interval u v) (Interval u' v') cks (retBound, cks')
  | O_RTC_Minus: forall u v' x v u' y cks retBound cks',
      Math.sub (Int u) (Int v') = Some (Int x) -> 
      Math.sub (Int v) (Int u') = Some (Int y) ->
      optimize_overflow_check (Interval x y) cks (retBound, cks') ->
      optimize_rtc_binop Minus (Interval u v) (Interval u' v') cks (retBound, cks')
  | O_RTC_Multiply: forall u v u' v' cks, (* no optimization for multiplication now *)
      optimize_rtc_binop Multiply (Interval u v) (Interval u' v') cks (int32_bound, cks)
  | O_RTC_Divide_T: forall u' v' u v cks,  (* only division by zero optimization for division now *)
      in_bound 0 (Interval u' v') true ->
      optimize_rtc_binop Divide (Interval u v) (Interval u' v') cks (int32_bound, cks)
  | O_RTC_Divide_F: forall u' v' u v cks' cks,  (* only division by zero optimization for division now *)
      in_bound 0 (Interval u' v') false ->
      cks' = remove_check_flag Do_Division_Check cks ->
      optimize_rtc_binop Divide (Interval u v) (Interval u' v') cks (int32_bound, cks')
  | O_RTC_Logic_Binop: forall op cks x y,
      op <> Plus /\ op <> Minus /\ op <> Multiply /\ op <> Divide ->
      optimize_rtc_binop op x y cks (Boolval, cks).


(** optimization for unary operation *)
Inductive optimize_rtc_unop: unary_operator -> bound -> check_flags -> (bound * check_flags) -> Prop :=
  | O_RTC_Unary_Minus: forall v x u y cks retBound cks',
      Math.unary_minus (Int v) = Some (Int x) ->
      Math.unary_minus (Int u) = Some (Int y) ->
      optimize_overflow_check (Interval x y) cks (retBound, cks') ->
      optimize_rtc_unop Unary_Minus (Interval u v) cks (retBound, cks')
  | O_RTC_Unop_Others: forall op boundVal cks,
      op <> Unary_Minus ->
      optimize_rtc_unop op boundVal cks (boundVal, cks).


(** for a literal with run-time check flags, if it's an int literal and its value falls 
    in the integer range, then optimize away the overflow check
*)
Inductive optimize_literal_x: literal -> check_flags -> (bound * check_flags) -> Prop :=
  | O_Literal_Bool_X: forall cks v,
      optimize_literal_x (Boolean_Literal v) cks (Boolval, cks)
  | O_Literal_Int_X: forall v cks retBound cks',
      optimize_overflow_check (Interval v v) cks (retBound, cks') ->
      optimize_literal_x (Integer_Literal v) cks (retBound, cks').


(** * Run-Time Checks Optimization For Expression *)
(** given an expression, optimize its run time checks, and return the optimized expression
    and its possible value bound, which will be used later to optimize other checks;
*)

Inductive optimize_expression_x: symboltable_x -> expression_x -> (expression_x * bound) -> Prop :=
  | O_Literal_X: forall l in_cks lBound in_cks' st ast_num ex_cks,
      optimize_literal_x l in_cks (lBound, in_cks') -> 
      optimize_expression_x st (E_Literal_X ast_num l in_cks ex_cks) ((E_Literal_X ast_num l in_cks' ex_cks), lBound)
  | O_Name_X: forall st n n' nBound ast_num,
      optimize_name_x st n (n', nBound) ->
      optimize_expression_x st (E_Name_X ast_num n) ((E_Name_X ast_num n'), nBound)
  | O_Binary_Operation_X: forall st e1 e1' e1Bound e2 e2' e2Bound in_cks retBound in_cks' ast_num op ex_cks,
      optimize_expression_x st e1 (e1', e1Bound) ->
      optimize_expression_x st e2 (e2', e2Bound) ->
      optimize_rtc_binop op e1Bound e2Bound in_cks (retBound, in_cks') ->
      optimize_expression_x st (E_Binary_Operation_X ast_num op e1 e2 in_cks ex_cks) 
                               ((E_Binary_Operation_X ast_num op e1' e2' in_cks' ex_cks), retBound)
  | O_Unary_Operation_X: forall st e e' eBound op in_cks retBound in_cks' ast_num ex_cks,
      optimize_expression_x st e (e', eBound) ->
      optimize_rtc_unop op eBound in_cks (retBound, in_cks') ->
      optimize_expression_x st (E_Unary_Operation_X ast_num op e in_cks ex_cks) 
                               ((E_Unary_Operation_X ast_num op e' in_cks' ex_cks), retBound)
      
with optimize_name_x: symboltable_x -> name_x -> (name_x * bound) -> Prop :=
  | O_Identifier_X: forall ast_num st t xBound x ex_cks,
      fetch_exp_type_x ast_num st = Some t ->
      bound_of_type st t xBound ->
      optimize_name_x st (E_Identifier_X ast_num x ex_cks) ((E_Identifier_X ast_num x ex_cks), xBound)
  | O_Indexed_Component_X: forall st x x' xBound e e' u v t u' v' e'' componentBound ast_num ex_cks,
      optimize_name_x st x (x', xBound) ->
      optimize_expression_x st e (e', Interval u v) ->
      fetch_exp_type_x (name_astnum_x x) st = Some (Array_Type t) ->
      extract_array_index_range_x st t (Range_X u' v') -> (* range value of array index type *)
      optimize_range_check e' (Interval u v) (Interval u' v') e'' ->
      bound_of_array_component_type st t componentBound ->
      optimize_name_x st (E_Indexed_Component_X ast_num x e ex_cks) 
                         ((E_Indexed_Component_X ast_num x' e'' ex_cks), componentBound)
  | O_Selected_Component_X: forall st x x' xBound t f fieldBound ast_num ex_cks,
      optimize_name_x st x (x', xBound) ->
      fetch_exp_type_x (name_astnum_x x) st = Some (Record_Type t) ->
      bound_of_record_field_type st t f fieldBound ->
      optimize_name_x st (E_Selected_Component_X ast_num x f ex_cks)
                         ((E_Selected_Component_X ast_num x' f ex_cks), fieldBound).


(** optimize run-time checks for arguments during procedure call;
    for a procedure call, given a list of arguments and its corresponding formal parameters,
    optimize its run-time checks (that's range check);
*)

Inductive optimize_args_x: symboltable_x -> list parameter_specification_x -> list expression_x -> list expression_x -> Prop :=
  | O_Args_Nil: forall st,
      optimize_args_x st nil nil nil
  | O_Args_Mode_In: forall param st arg arg' argBound params args args',
      param.(parameter_mode_x) = In -> 
      is_range_constrainted_type (param.(parameter_subtype_mark_x)) = false ->
      optimize_expression_x st arg (arg', argBound) ->
      optimize_args_x st params args args' ->
      optimize_args_x st (param :: params) (arg :: args) (arg' :: args')
  | O_Args_Mode_In_RangeCheck: forall param st u v arg arg' u' v' arg'' params args args',
      param.(parameter_mode_x) = In -> 
      extract_subtype_range_x st (param.(parameter_subtype_mark_x)) (Range_X u v) ->
      optimize_expression_x st arg (arg', Interval u' v') ->
      optimize_range_check arg' (Interval u' v') (Interval u v) arg'' ->
      optimize_args_x st params args args' ->
      optimize_args_x st (param :: params) (arg :: args) (arg'' :: args')
  | O_Args_Mode_Out: forall param ast_num st t n n' nBound params args args',
      param.(parameter_mode_x) = Out ->
      fetch_exp_type_x ast_num st = Some t ->
      is_range_constrainted_type t = false ->
      optimize_name_x st n (n', nBound) ->
      optimize_args_x st params args args' ->
      optimize_args_x st (param :: params) ((E_Name_X ast_num n) :: args) 
                                           ((E_Name_X ast_num n') :: args')
  | O_Args_Mode_Out_RangeCheck: forall param st u v ast_num t u' v' n n' nBound arg' params args args',
      param.(parameter_mode_x) = Out ->
      bound_of_type st (param.(parameter_subtype_mark_x)) (Interval u v) ->
      fetch_exp_type_x ast_num st = Some t ->
      extract_subtype_range_x st t (Range_X u' v') ->
      optimize_name_x st n (n', nBound) ->
      optimize_range_check_on_copy_out (E_Name_X ast_num n') (Interval u v) (Interval u' v') arg' ->
      optimize_args_x st params args args' ->
      optimize_args_x st (param :: params) ((E_Name_X ast_num n) :: args) 
                                           (arg' :: args')
  | O_Args_Mode_InOut: forall param ast_num st t n n' nBound params args args', 
      param.(parameter_mode_x) = In_Out ->
      fetch_exp_type_x ast_num st = Some t ->
      is_range_constrainted_type t = false \/ is_range_constrainted_type (param.(parameter_subtype_mark_x)) = false ->
      optimize_name_x st n (n', nBound) ->
      optimize_args_x st params args args' ->
      optimize_args_x st (param :: params) ((E_Name_X ast_num n) :: args) 
                                           ((E_Name_X ast_num n') :: args')
  | O_Args_Mode_InOut_In_RangeCheck: forall param u v ast_num st t u' v' n n' v1 v2 arg arg' params args args', 
      param.(parameter_mode_x) = In_Out ->
      extract_subtype_range_x st (param.(parameter_subtype_mark_x)) (Range_X u v) ->
      fetch_exp_type_x ast_num st = Some t ->
      extract_subtype_range_x st t (Range_X u' v') ->
      optimize_expression_x st (E_Name_X ast_num n) ((E_Name_X ast_num n'), Interval v1 v2) ->
      optimize_range_check (E_Name_X ast_num n') (Interval v1 v2) (Interval u v) arg ->
      optimize_range_check_on_copy_out arg (Interval u v) (Interval u' v') arg' ->
      optimize_args_x st params args args' ->
      optimize_args_x st (param :: params) ((E_Name_X ast_num n) :: args) 
                                           (arg' :: args').



(** * Run-Time Checks Optimization For Statement *)
(** given a statement, optimize its run-time check flags and return a new optimized statement *)
Inductive optimize_statement_x: symboltable_x -> statement_x -> statement_x -> Prop :=
  | O_Null_X: forall st, 
      optimize_statement_x st S_Null_X S_Null_X
  | O_Assignment_X: forall x st t x' xBound e e' eBound ast_num,
      fetch_exp_type_x (name_astnum_x x) st = Some t ->
      is_range_constrainted_type t = false -> 
      optimize_name_x st x (x', xBound) ->
      optimize_expression_x st e (e', eBound) ->
      optimize_statement_x st (S_Assignment_X ast_num x e) (S_Assignment_X ast_num x' e')
  | O_Assignment_RangeCheck_X: forall x st t u v x' xBound e e' u' v' e'' ast_num,
      fetch_exp_type_x (name_astnum_x x) st = Some t ->
      extract_subtype_range_x st t (Range_X u v) ->
      optimize_name_x st x (x', xBound) ->
      optimize_expression_x st e (e', Interval u' v') ->
      optimize_range_check e' (Interval u' v') (Interval u v) e'' ->
      optimize_statement_x st (S_Assignment_X ast_num x e) (S_Assignment_X ast_num x' e'')
  | O_If_X: forall st e e' eBound c1 c1' c2 c2' ast_num,
      optimize_expression_x st e (e', eBound) ->
      optimize_statement_x st c1 c1' ->
      optimize_statement_x st c2 c2' ->
      optimize_statement_x st (S_If_X ast_num e c1 c2) (S_If_X ast_num e' c1' c2')
  | O_While_Loop_X: forall st e e' eBound c c' ast_num,
      optimize_expression_x st e (e', eBound) ->
      optimize_statement_x st c c' ->
      optimize_statement_x st (S_While_Loop_X ast_num e c) (S_While_Loop_X ast_num e' c')
  | O_Procedure_Call_X: forall p st n pb args args' ast_num p_ast_num,
      fetch_proc_x p st = Some (n, pb) ->
      optimize_args_x st (procedure_parameter_profile_x pb) args args' ->
      optimize_statement_x st (S_Procedure_Call_X ast_num p_ast_num p args) (S_Procedure_Call_X ast_num p_ast_num p args')
  | O_Sequence_X: forall st c1 c1' c2 c2' ast_num,
      optimize_statement_x st c1 c1' ->
      optimize_statement_x st c2 c2' ->
      optimize_statement_x st (S_Sequence_X ast_num c1 c2) (S_Sequence_X ast_num c1' c2').

(** * Run-Time Checks Optimization For Declaration *)

Inductive optimize_object_declaration_x: symboltable_x -> object_declaration_x -> object_declaration_x -> Prop :=
  | O_Object_Declaration_NoneInit_X: forall st ast_num x t,
      optimize_object_declaration_x st (mkobject_declaration_x ast_num x t None) 
                                       (mkobject_declaration_x ast_num x t None)
  | O_Object_Declaration_NoRangeCheck_X: forall t st e e' eBound ast_num x,
      is_range_constrainted_type t = false ->
      optimize_expression_x st e (e', eBound) -> 
      optimize_object_declaration_x st (mkobject_declaration_x ast_num x t (Some e)) 
                                       (mkobject_declaration_x ast_num x t (Some e'))
  | O_Object_Declaration_RangeCheck_X: forall st t u v e e' u' v' e'' ast_num x,
      extract_subtype_range_x st t (Range_X u v) ->
      optimize_expression_x st e (e', Interval u' v') ->
      optimize_range_check e' (Interval u' v') (Interval u v) e'' ->
      optimize_object_declaration_x st (mkobject_declaration_x ast_num x t (Some e)) 
                                       (mkobject_declaration_x ast_num x t (Some e'')).


Inductive optimize_declaration_x: symboltable_x -> declaration_x -> declaration_x -> Prop :=
  | O_Null_Declaration_X: forall st,
      optimize_declaration_x st D_Null_Declaration_X D_Null_Declaration_X
  | O_Type_Declaration_X: forall st ast_num t,
      optimize_declaration_x st (D_Type_Declaration_X ast_num t) (D_Type_Declaration_X ast_num t)
  | O_Object_Declaration_X: forall st o o' ast_num,
      optimize_object_declaration_x st o o' ->
      optimize_declaration_x st (D_Object_Declaration_X ast_num o) (D_Object_Declaration_X ast_num o')
  | O_Procedure_Body_X: forall st p p' ast_num,
      optimize_procedure_body_x st p p' ->
      optimize_declaration_x st (D_Procedure_Body_X ast_num p) (D_Procedure_Body_X ast_num p')
  | O_Seq_Declaration_X: forall st d1 d1' d2 d2' ast_num,
      optimize_declaration_x st d1 d1' ->
      optimize_declaration_x st d2 d2' ->
      optimize_declaration_x st (D_Seq_Declaration_X ast_num d1 d2) (D_Seq_Declaration_X ast_num d1' d2')

with optimize_procedure_body_x: symboltable_x -> procedure_body_x -> procedure_body_x -> Prop :=
  | O_Procedure_Body: forall st decls decls' stmt stmt' ast_num p params,
      optimize_declaration_x st decls decls' ->
      optimize_statement_x st stmt stmt' ->
      optimize_procedure_body_x st (mkprocedure_body_x ast_num p params decls stmt)
                                   (mkprocedure_body_x ast_num p params decls' stmt').







