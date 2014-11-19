Require Export language_flagged.
Require Export language_util.
Require Export symboltable.

(* ***************************************************************
   generate and insert run-time check flags into SPARK AST nodes 
   according to the run-time check rules;
   *************************************************************** *)

(** * Compile To Check-Flagged Program *)
(** run-time checks to be verified for an expression depend on both the
    types of its operations and the context where it appears, e.g. if
    it's used as an index, then Do_Range_Check should be set for it;
    in the following formalization, check_flags are the check flags
    that are enforced by the context of the expression, for example,
    in C2_Flagged_Indexed_Component, Do_Range_Check will be enforced
    on the expression e as it's used as an index of array;

    in the formalization for expression as defined in language_flagged.v 
    and language.v, the constructor E_Name_X (E_Name) is introduced to 
    incorporate type name_x (name) into type expression_x (expression),
    for example, variable x is represented as a name expression with 
    (E_Name_X ast_num (E_Identifier_X x_ast_num x checkflags) nil), and
    we enforce that the run-time check flags are put in the constructor
    E_Identifier_X instead of E_Name_X, that's why the check flags for
    E_Name_X is nil;
*)

(*
  cases of possible run-time checks optimization:
  - range check for literal index can be removed, similarly, 
    overflow check and division check for literal can be optimized away;
  - range check for varialbe index, whose type is the same as index type,
    can be optimized away;
  - subtype T is Integer range 1 .. 10; subtype U is Integer range 2 .. 12; 
    X: T; Y: U;
    Y = X + 1; (the range check for this assignment can also be optimized away)
               (the overflow check can also be removed, as X + 1 is in the range of integer)
    Y = Y / (X + 1);
               (the division check can also be removed, as (X + 1) > 0 )
*)

Inductive compile2_flagged_exp: symboltable -> expression -> expression_x -> Prop :=
    | C2_Flagged_Literal_Bool: forall st ast_num b,
        compile2_flagged_exp st (E_Literal ast_num (Boolean_Literal b)) 
                                (E_Literal_X ast_num (Boolean_Literal b) nil nil)
    | C2_Flagged_Literal_Int_T: forall st v ast_num,
        in_bound v int32_bound true -> (*simple optimization: if v is in the range of Integer, then no overflow check*)
        compile2_flagged_exp st (E_Literal ast_num (Integer_Literal v)) 
                                (E_Literal_X ast_num (Integer_Literal v) nil nil)
    | C2_Flagged_Literal_Int_F: forall st v ast_num,
        in_bound v int32_bound false ->
        compile2_flagged_exp st (E_Literal ast_num (Integer_Literal v)) 
                                (E_Literal_X ast_num (Integer_Literal v) (Do_Overflow_Check :: nil) nil)
    | C2_Flagged_Name: forall st n n_flagged ast_num,
        compile2_flagged_name st n n_flagged ->
        compile2_flagged_exp st (E_Name ast_num n) 
                                (E_Name_X ast_num n_flagged)
    | C2_Flagged_Binary_Operation_O: forall st op e1 e1_flagged e2 e2_flagged ast_num,
        op = Plus \/ op = Minus \/ op = Multiply ->
        compile2_flagged_exp st e1 e1_flagged ->
        compile2_flagged_exp st e2 e2_flagged ->
        compile2_flagged_exp st (E_Binary_Operation ast_num op e1 e2)
                                (E_Binary_Operation_X ast_num op e1_flagged e2_flagged (Do_Overflow_Check :: nil) nil)
    | C2_Flagged_Binary_Operation_OD: forall st op e1 e1_flagged e2 e2_flagged ast_num,
        op = Divide ->
        compile2_flagged_exp st e1 e1_flagged ->
        compile2_flagged_exp st e2 e2_flagged ->
        compile2_flagged_exp st (E_Binary_Operation ast_num op e1 e2)
                                (E_Binary_Operation_X ast_num op e1_flagged e2_flagged (Do_Division_Check :: Do_Overflow_Check :: nil) nil)
    | C2_Flagged_Binary_Operation_Others: forall st op e1 e1_flagged e2 e2_flagged ast_num,
        op <> Plus ->
        op <> Minus ->
        op <> Multiply ->
        op <> Divide ->
        compile2_flagged_exp st e1 e1_flagged ->
        compile2_flagged_exp st e2 e2_flagged ->
        compile2_flagged_exp st (E_Binary_Operation ast_num op e1 e2)
                                (E_Binary_Operation_X ast_num op e1_flagged e2_flagged nil nil)
    | C2_Flagged_Unary_Operation_O: forall st op e e_flagged ast_num,
        op = Unary_Minus ->
        compile2_flagged_exp st e e_flagged ->
        compile2_flagged_exp st (E_Unary_Operation ast_num op e) 
                                (E_Unary_Operation_X ast_num op e_flagged (Do_Overflow_Check :: nil) nil)
    | C2_Flagged_Unary_Operation_Others: forall st op e e_flagged ast_num,
        op <> Unary_Minus ->
        compile2_flagged_exp st e e_flagged ->
        compile2_flagged_exp st (E_Unary_Operation ast_num op e) 
                                (E_Unary_Operation_X ast_num op e_flagged nil nil)

with compile2_flagged_name: symboltable -> name -> name_x -> Prop :=
    | C2_Flagged_Identifier: forall st ast_num x,
        compile2_flagged_name st (E_Identifier ast_num x) (* the value of x should be already checked before it's stored in memory, so no check is needed when it's read *)
                                 (E_Identifier_X ast_num x nil) 
    | C2_Flagged_Indexed_Component: forall st e e_flagged x x_flagged ast_num,
        compile2_flagged_exp st e e_flagged ->
        compile2_flagged_name st x x_flagged -> (* x itself can be an indexed/selected component *)
        compile2_flagged_name st (E_Indexed_Component ast_num x e) 
                                 (E_Indexed_Component_X ast_num x_flagged (update_exterior_checks_exp e_flagged (Do_Range_Check :: nil)) nil) 
    | C2_Flagged_Selected_Component: forall st x x_flagged ast_num f,
        compile2_flagged_name st x x_flagged ->
        compile2_flagged_name st (E_Selected_Component ast_num x f) 
                                 (E_Selected_Component_X ast_num x_flagged f nil).


(**
   for a procedure call, during its copy in, Do_Range_Check should be performed 
   on input argument if its corresponding formal parameter is a value of range 
   constrainted type; 
   similarly, during its copy out, Do_Range_Check should be performed on output 
   parameter if its corresponding actual argument is a value of range constrainted 
   type; 
   To distinguish the range checks performed on copy in and copy out,
   Do_Range_Check_On_CopyOut is used to denote the range check on copy out, and
   Do_Range_Check is used to denote the range check on copy in by default;

   compile2_flagged_args formalizes how to insert run-time check flags for arguments
   according to its corresponding formal parameters;
*)

Inductive compile2_flagged_args: symboltable -> list parameter_specification -> list expression -> list expression_x -> Prop :=
    | C2_Flagged_Args_Null: forall st,
        compile2_flagged_args st nil nil nil
    | C2_Flagged_Args_In: forall st param arg arg_flagged lparam larg larg_flagged,
        param.(parameter_mode) = In ->
        is_range_constrainted_type (param.(parameter_subtype_mark)) = false ->
        compile2_flagged_exp  st arg arg_flagged ->
        compile2_flagged_args st lparam larg larg_flagged -> 
        compile2_flagged_args st (param :: lparam) (arg :: larg) (arg_flagged :: larg_flagged)
    | C2_Flagged_Args_In_RangeCheck: forall st param arg arg_flagged lparam larg larg_flagged,
        param.(parameter_mode) = In ->
        is_range_constrainted_type (param.(parameter_subtype_mark)) = true ->
        compile2_flagged_exp  st arg arg_flagged ->
        compile2_flagged_args st lparam larg larg_flagged -> 
        compile2_flagged_args st (param :: lparam) (arg :: larg) ((update_exterior_checks_exp arg_flagged (Do_Range_Check :: nil)) :: larg_flagged)
    | C2_Flagged_Args_Out: forall st param ast_num t n_flagged lparam larg larg_flagged n,
        param.(parameter_mode) = Out ->
        fetch_exp_type ast_num st = Some t ->
        is_range_constrainted_type t = false ->
        compile2_flagged_name st n n_flagged ->
        compile2_flagged_args st lparam larg larg_flagged -> 
        compile2_flagged_args st (param :: lparam) ((E_Name ast_num n) :: larg) ((E_Name_X ast_num n_flagged) :: larg_flagged)
    | C2_Flagged_Args_Out_RangeCheck: forall st param ast_num t n_flagged lparam larg larg_flagged n,
        param.(parameter_mode) = Out ->
        fetch_exp_type ast_num st = Some t ->
        is_range_constrainted_type t = true ->
        compile2_flagged_name st n n_flagged ->
        compile2_flagged_args st lparam larg larg_flagged -> 
        compile2_flagged_args st (param :: lparam) ((E_Name ast_num n) :: larg) 
                                                   ((E_Name_X ast_num (update_exterior_checks_name n_flagged (Do_Range_Check_On_CopyOut :: nil))) :: larg_flagged)
    | C2_Flagged_Args_InOut: forall st param ast_num t n_flagged lparam larg larg_flagged n,
        param.(parameter_mode) = In_Out ->
        is_range_constrainted_type (param.(parameter_subtype_mark)) = false ->
        fetch_exp_type ast_num st = Some t ->
        is_range_constrainted_type t = false ->
        compile2_flagged_name st n n_flagged ->
        compile2_flagged_args st lparam larg larg_flagged -> 
        compile2_flagged_args st (param :: lparam) ((E_Name ast_num n) :: larg) ((E_Name_X ast_num n_flagged) :: larg_flagged)
    | C2_Flagged_Args_InOut_In_RangeCheck: forall st param ast_num t n_flagged lparam larg larg_flagged n,
        param.(parameter_mode) = In_Out ->
        is_range_constrainted_type (param.(parameter_subtype_mark)) = true ->
        fetch_exp_type ast_num st = Some t ->
        is_range_constrainted_type t = false ->
        compile2_flagged_name st n n_flagged ->
        compile2_flagged_args st lparam larg larg_flagged -> 
        compile2_flagged_args st (param :: lparam) ((E_Name ast_num n) :: larg) 
                                                   ((E_Name_X ast_num (update_exterior_checks_name n_flagged (Do_Range_Check :: nil))) :: larg_flagged)
    | C2_Flagged_Args_InOut_Out_RangeCheck: forall st param ast_num t n_flagged lparam larg larg_flagged n,
        param.(parameter_mode) = In_Out ->
        is_range_constrainted_type (param.(parameter_subtype_mark)) = false ->
        fetch_exp_type ast_num st = Some t ->
        is_range_constrainted_type t = true ->
        compile2_flagged_name st n n_flagged ->
        compile2_flagged_args st lparam larg larg_flagged -> 
        compile2_flagged_args st (param :: lparam) ((E_Name ast_num n) :: larg) 
                                                   ((E_Name_X ast_num (update_exterior_checks_name n_flagged (Do_Range_Check_On_CopyOut :: nil))) :: larg_flagged)
    | C2_Flagged_Args_InOut_RangeCheck: forall st param ast_num t n_flagged lparam larg larg_flagged n,
        param.(parameter_mode) = In_Out ->
        is_range_constrainted_type (param.(parameter_subtype_mark)) = true ->
        fetch_exp_type ast_num st = Some t ->
        is_range_constrainted_type t = true ->
        compile2_flagged_name st n n_flagged ->
        compile2_flagged_args st lparam larg larg_flagged -> 
        compile2_flagged_args st (param :: lparam) ((E_Name ast_num n) :: larg) 
                                                   ((E_Name_X ast_num (update_exterior_checks_name n_flagged (Do_Range_Check :: Do_Range_Check_On_CopyOut :: nil))) :: larg_flagged).


(**
    given a statement, insert run-time check flags according to the
    run-time checking rules enforced on the semantics of SPARK language 
    and return a run-time checks-flagged statement;
*)
Inductive compile2_flagged_stmt: symboltable -> statement -> statement_x -> Prop := 
    | C2_Flagged_Null: forall st,
        compile2_flagged_stmt st S_Null S_Null_X
    | C2_Flagged_Assignment: forall x st t x_flagged e e_flagged ast_num,
        fetch_exp_type (name_astnum x) st = Some t ->
        is_range_constrainted_type t = false ->        
        compile2_flagged_name st x x_flagged ->
        compile2_flagged_exp  st e e_flagged ->
        compile2_flagged_stmt st
                              (S_Assignment   ast_num x e) 
                              (S_Assignment_X ast_num x_flagged e_flagged)
    | C2_Flagged_Assignment_RangeCheck: forall x st t x_flagged e e_flagged ast_num,
        fetch_exp_type (name_astnum x) st = Some t ->
        is_range_constrainted_type t = true ->
        compile2_flagged_name st x x_flagged ->
        compile2_flagged_exp  st e e_flagged ->
        compile2_flagged_stmt st
                              (S_Assignment   ast_num x e)
                              (S_Assignment_X ast_num x_flagged (update_exterior_checks_exp e_flagged (Do_Range_Check :: nil)))
    | C2_Flagged_If: forall e e_flagged st c1 c1_flagged c2 c2_flagged ast_num,
        compile2_flagged_exp  st e e_flagged ->
        compile2_flagged_stmt st c1 c1_flagged ->
        compile2_flagged_stmt st c2 c2_flagged ->
        compile2_flagged_stmt st
                              (S_If   ast_num e c1 c2) 
                              (S_If_X ast_num e_flagged c1_flagged c2_flagged)
    | C2_Flagged_While: forall e e_flagged st c c_flagged ast_num,
        compile2_flagged_exp  st e e_flagged ->
        compile2_flagged_stmt st c c_flagged ->
        compile2_flagged_stmt st 
                              (S_While_Loop   ast_num e c) 
                              (S_While_Loop_X ast_num e_flagged c_flagged)
    | C2_Flagged_Procedure_Call: forall p st n pb params args args_flagged ast_num p_ast_num,
        fetch_proc p st = Some (n, pb) ->
        procedure_parameter_profile pb = params ->
        compile2_flagged_args st params args args_flagged ->
        compile2_flagged_stmt st
                              (S_Procedure_Call   ast_num p_ast_num p args) 
                              (S_Procedure_Call_X ast_num p_ast_num p args_flagged)
    | C2_Flagged_Sequence: forall st c1 c1_flagged c2 c2_flagged ast_num,
        compile2_flagged_stmt st c1 c1_flagged ->
        compile2_flagged_stmt st c2 c2_flagged ->
        compile2_flagged_stmt st
                              (S_Sequence ast_num   c1 c2)
                              (S_Sequence_X ast_num c1_flagged c2_flagged).


Inductive compile2_flagged_type_declaration: type_declaration -> type_declaration_x -> Prop :=
    | C2_Flagged_Subtype_Decl: forall ast_num tn t l u,
        compile2_flagged_type_declaration (Subtype_Declaration   ast_num tn t (Range l u))
                                          (Subtype_Declaration_X ast_num tn t (Range_X l u))
    | C2_Flagged_Derived_Type_Decl: forall ast_num tn t l u,
        compile2_flagged_type_declaration (Derived_Type_Declaration   ast_num tn t (Range l u))
                                          (Derived_Type_Declaration_X ast_num tn t (Range_X l u))
    | C2_Flagged_Integer_Type_Decl: forall ast_num tn l u,
        compile2_flagged_type_declaration (Integer_Type_Declaration   ast_num tn (Range l u))
                                          (Integer_Type_Declaration_X ast_num tn (Range_X l u))
    | C2_Flagged_Array_Type_Decl: forall ast_num tn tm t,
        compile2_flagged_type_declaration (Array_Type_Declaration   ast_num tn tm t) (* tn: array type name, tm: index type mark, t: component type *)
                                          (Array_Type_Declaration_X ast_num tn tm t)
    | C2_Flagged_Record_Type_Decl: forall ast_num tn fs,
        compile2_flagged_type_declaration (Record_Type_Declaration   ast_num tn fs)  (* tn: record type name, fs: list of field types *)
                                          (Record_Type_Declaration_X ast_num tn fs).

(** insert run-time check flags on the initialization expression 
    for a newly declared object;
*)
Inductive compile2_flagged_object_declaration: symboltable -> object_declaration -> object_declaration_x -> Prop :=
    | C2_Flagged_Object_Declaration_NoneInit: forall st ast_num x t,
        compile2_flagged_object_declaration st 
                                            (mkobject_declaration   ast_num x t None) 
                                            (mkobject_declaration_x ast_num x t None) 
    | C2_Flagged_Object_Declaration: forall st t e e_flagged ast_num x,
        is_range_constrainted_type t = false ->
        compile2_flagged_exp st e e_flagged ->
        compile2_flagged_object_declaration st 
                                            (mkobject_declaration   ast_num x t (Some e)) (* declare a variable x of type t with initialization e *)
                                            (mkobject_declaration_x ast_num x t (Some e_flagged))
    | C2_Flagged_Object_Declaration_RangeCheck: forall st t e e_flagged ast_num x,
        is_range_constrainted_type t = true ->
        compile2_flagged_exp st e e_flagged ->
        compile2_flagged_object_declaration st 
                                            (mkobject_declaration   ast_num x t (Some e)) 
                                            (mkobject_declaration_x ast_num x t (Some (update_exterior_checks_exp e_flagged (Do_Range_Check :: nil)))).

Inductive compile2_flagged_object_declarations: symboltable -> list object_declaration -> list object_declaration_x -> Prop :=
    | C2_Flagged_Object_Declarations_Null: forall st,
        compile2_flagged_object_declarations st nil nil 
    | C2_Flagged_Object_Declarations_List: forall st o o_flagged lo lo_flagged,
        compile2_flagged_object_declaration  st o o_flagged ->
        compile2_flagged_object_declarations st lo lo_flagged ->
        compile2_flagged_object_declarations st (o :: lo) (o_flagged :: lo_flagged).


Inductive compile2_flagged_parameter_specification: parameter_specification -> parameter_specification_x -> Prop :=
    | C2_Flagged_Parameter_Spec: forall ast_num x t m,
        compile2_flagged_parameter_specification (mkparameter_specification   ast_num x t m) (* a parameter x of type t of in/out mode m *)
                                                 (mkparameter_specification_x ast_num x t m).

Inductive compile2_flagged_parameter_specifications: list parameter_specification -> list parameter_specification_x -> Prop :=
    | C2_Flagged_Parameter_Specs_Null:
        compile2_flagged_parameter_specifications nil nil
    | C2_Flagged_Parameter_Specs_List: forall param param_flagged lparam lparam_flagged,
        compile2_flagged_parameter_specification  param  param_flagged ->
        compile2_flagged_parameter_specifications lparam lparam_flagged ->
        compile2_flagged_parameter_specifications (param :: lparam) (param_flagged :: lparam_flagged).


Inductive compile2_flagged_declaration: symboltable -> declaration -> declaration_x -> Prop :=
    | C2_Flagged_D_Null_Declaration: forall st,
        compile2_flagged_declaration st D_Null_Declaration D_Null_Declaration_X
    | C2_Flagged_D_Type_Declaration: forall t t_flagged st ast_num,
        compile2_flagged_type_declaration t t_flagged ->
        compile2_flagged_declaration st
                                     (D_Type_Declaration   ast_num t) 
                                     (D_Type_Declaration_X ast_num t_flagged)
    | C2_Flagged_D_Object_Declaration: forall st o o_flagged ast_num,
        compile2_flagged_object_declaration st o o_flagged ->
        compile2_flagged_declaration st 
                                     (D_Object_Declaration   ast_num o)
                                     (D_Object_Declaration_X ast_num o_flagged) 
    | C2_Flagged_D_Procedure_Declaration: forall st p p_flagged ast_num,
        compile2_flagged_procedure_body st p p_flagged ->
        compile2_flagged_declaration st 
                                     (D_Procedure_Body   ast_num p)
                                     (D_Procedure_Body_X ast_num p_flagged) 
    | C2_Flagged_D_Seq_Declaration: forall st d1 d1_flagged d2 d2_flagged ast_num,
        compile2_flagged_declaration st d1 d1_flagged ->
        compile2_flagged_declaration st d2 d2_flagged ->
        compile2_flagged_declaration st 
                                     (D_Seq_Declaration   ast_num d1 d2) 
                                     (D_Seq_Declaration_X ast_num d1_flagged d2_flagged)

with compile2_flagged_procedure_body: symboltable -> procedure_body -> procedure_body_x -> Prop :=
       | C2_Flagged_Procedure_Declaration: forall params params_flagged st decls decls_flagged
                                                  stmt stmt_flagged ast_num p,
           compile2_flagged_parameter_specifications params params_flagged ->
           compile2_flagged_declaration st decls decls_flagged ->
           compile2_flagged_stmt st stmt stmt_flagged ->
           compile2_flagged_procedure_body st 
                                           (mkprocedure_body   ast_num p params decls stmt)
                                           (mkprocedure_body_x ast_num p params_flagged decls_flagged stmt_flagged).


(* ***************************************************************
                          Funtion Version
   *************************************************************** *)

(** * Functions for Inserting Run-Time Checks *)

Function compile2_flagged_exp_f (st: symboltable) (e: expression): expression_x :=
  match e with
  | E_Literal ast_num (Boolean_Literal b) => 
      E_Literal_X ast_num (Boolean_Literal b) nil nil
  | E_Literal ast_num (Integer_Literal v) =>
      match (Zle_bool min_signed v) && (Zle_bool v max_signed) with
      | true  => E_Literal_X ast_num (Integer_Literal v) nil nil (* optimization *)
      | false => E_Literal_X ast_num (Integer_Literal v) (Do_Overflow_Check :: nil) nil
      end
  | E_Name ast_num n => 
      let n_flagged := compile2_flagged_name_f st n in
        E_Name_X ast_num n_flagged
  | E_Binary_Operation ast_num op e1 e2 =>
      let e1_flagged := compile2_flagged_exp_f st e1 in
      let e2_flagged := compile2_flagged_exp_f st e2 in
        match op with
        | Plus     => E_Binary_Operation_X ast_num op e1_flagged e2_flagged (Do_Overflow_Check :: nil) nil
        | Minus    => E_Binary_Operation_X ast_num op e1_flagged e2_flagged (Do_Overflow_Check :: nil) nil
        | Multiply => E_Binary_Operation_X ast_num op e1_flagged e2_flagged (Do_Overflow_Check :: nil) nil
        | Divide   => E_Binary_Operation_X ast_num op e1_flagged e2_flagged (Do_Division_Check :: Do_Overflow_Check :: nil) nil
        | _        => E_Binary_Operation_X ast_num op e1_flagged e2_flagged nil nil
        end
  | E_Unary_Operation ast_num op e => 
      let e_flagged := compile2_flagged_exp_f st e in
        match op with
        | Unary_Minus => E_Unary_Operation_X ast_num op e_flagged (Do_Overflow_Check :: nil) nil
        | _           => E_Unary_Operation_X ast_num op e_flagged nil nil
        end
  end

with compile2_flagged_name_f (st: symboltable) (n: name): name_x :=
  match n with
  | E_Identifier ast_num x =>
      E_Identifier_X ast_num x nil
  | E_Indexed_Component ast_num x e =>
      let x_flagged := compile2_flagged_name_f st x in
      let e_flagged := compile2_flagged_exp_f st e in
        E_Indexed_Component_X ast_num x_flagged (update_exterior_checks_exp e_flagged (Do_Range_Check :: nil)) nil
  | E_Selected_Component ast_num x f =>
      let x_flagged := compile2_flagged_name_f st x in
        E_Selected_Component_X ast_num x_flagged f nil
  end.

Function compile2_flagged_args_f (st: symboltable) (params: list parameter_specification) (args: list expression): option (list expression_x) :=
  match params, args with
  | nil, nil => Some nil
  | param :: lparam, arg :: larg =>
      match (compile2_flagged_args_f st lparam larg) with
      | Some larg_flagged => 
          match param.(parameter_mode) with
          | In =>
            let arg_flagged := compile2_flagged_exp_f st arg in
            if is_range_constrainted_type (param.(parameter_subtype_mark)) then
              Some ((update_exterior_checks_exp arg_flagged (Do_Range_Check :: nil)) :: larg_flagged)
            else
              Some (arg_flagged :: larg_flagged)
          | Out =>
            match arg with
            | E_Name ast_num n =>
                match fetch_exp_type ast_num st with
                | Some t =>
                    let n_flagged := compile2_flagged_name_f st n in
                    if is_range_constrainted_type t then
                      Some ((E_Name_X ast_num (update_exterior_checks_name n_flagged (Do_Range_Check_On_CopyOut :: nil))) :: larg_flagged)
                    else
                      Some ((E_Name_X ast_num n_flagged) :: larg_flagged)
                | None => None
                end
            | _ => None
            end
          | In_Out =>
            match arg with
            | E_Name ast_num n =>
                match fetch_exp_type ast_num st with
                | Some t =>
                    let n_flagged := compile2_flagged_name_f st n in
                    if is_range_constrainted_type (param.(parameter_subtype_mark)) then 
                      if is_range_constrainted_type t then
                        Some ((E_Name_X ast_num (update_exterior_checks_name n_flagged (Do_Range_Check :: Do_Range_Check_On_CopyOut :: nil))) :: larg_flagged)
                      else
                        Some ((E_Name_X ast_num (update_exterior_checks_name n_flagged (Do_Range_Check :: nil))) :: larg_flagged)
                    else
                      if is_range_constrainted_type t then
                        Some ((E_Name_X ast_num (update_exterior_checks_name n_flagged (Do_Range_Check_On_CopyOut :: nil))) :: larg_flagged)
                      else
                        Some ((E_Name_X ast_num n_flagged) :: larg_flagged)
                | _ => None
                end
            | _ => None
            end
          end
      | _ => None
      end
  | _, _ => None
  end.

Function compile2_flagged_stmt_f (st: symboltable) (c: statement): option statement_x :=
  match c with
  | S_Null => Some S_Null_X
  | S_Assignment ast_num x e =>
      let x_flagged := compile2_flagged_name_f st x in
      let e_flagged := compile2_flagged_exp_f  st e in
        match fetch_exp_type (name_astnum x) st with
        | Some t =>
          if is_range_constrainted_type t then
            Some (S_Assignment_X ast_num x_flagged (update_exterior_checks_exp e_flagged (Do_Range_Check :: nil)))
          else
            Some (S_Assignment_X ast_num x_flagged e_flagged)
        | None   => None
        end
  | S_If ast_num e c1 c2 =>
      let e_flagged  := compile2_flagged_exp_f st e in
      let c1' := compile2_flagged_stmt_f st c1 in
      let c2' := compile2_flagged_stmt_f st c2 in
        match (c1', c2') with 
        | (Some c1_flagged, Some c2_flagged) => 
            Some (S_If_X ast_num e_flagged c1_flagged c2_flagged)
        | _ => None
        end
  | S_While_Loop ast_num e c =>
      let e_flagged := compile2_flagged_exp_f st e in
      let c' := compile2_flagged_stmt_f st c in
        match c' with 
        | Some c_flagged => 
            Some (S_While_Loop_X ast_num e_flagged c_flagged)
        | _ => None
        end
  | S_Procedure_Call ast_num p_ast_num p args =>
      match fetch_proc p st with
      | Some (n, pb) => 
          match compile2_flagged_args_f st (procedure_parameter_profile pb) args with
          | Some args_flagged => Some (S_Procedure_Call_X ast_num p_ast_num p args_flagged)
          | None              => None
          end
      | None         => None
      end
  | S_Sequence ast_num c1 c2 =>
      let c1' := compile2_flagged_stmt_f st c1 in
      let c2' := compile2_flagged_stmt_f st c2 in
      match (c1', c2') with
      | (Some c1_flagged, Some c2_flagged) =>
          Some (S_Sequence_X ast_num c1_flagged c2_flagged)
      | _ => None
      end
  end.

Function compile2_flagged_type_declaration_f (t: type_declaration): type_declaration_x :=
  match t with
  | Subtype_Declaration ast_num tn t (Range l u) =>
      Subtype_Declaration_X ast_num tn t (Range_X l u)
  | Derived_Type_Declaration ast_num tn t (Range l u) =>
      Derived_Type_Declaration_X ast_num tn t (Range_X l u)
  | Integer_Type_Declaration ast_num tn (Range l u) =>
      Integer_Type_Declaration_X ast_num tn (Range_X l u)
  | Array_Type_Declaration ast_num tn tm t => (* tn: array type name, tm: index type mark, t: component type *)
      Array_Type_Declaration_X ast_num tn tm t
  | Record_Type_Declaration ast_num tn fs =>  (* tn: record type name, fs: list of field types *)
      Record_Type_Declaration_X ast_num tn fs
  end.

Function compile2_flagged_object_declaration_f (st: symboltable) (o: object_declaration): object_declaration_x :=
  match o with
  | mkobject_declaration ast_num x t None =>
      mkobject_declaration_x ast_num x t None
  | mkobject_declaration ast_num x t (Some e) => 
      let e_flagged := compile2_flagged_exp_f st e in
        if is_range_constrainted_type t then
          mkobject_declaration_x ast_num x t (Some (update_exterior_checks_exp e_flagged (Do_Range_Check :: nil)))
        else
          mkobject_declaration_x ast_num x t (Some e_flagged)
  end.

Function compile2_flagged_object_declarations_f (st: symboltable) (lo: list object_declaration): list object_declaration_x :=
  match lo with
  | nil => nil
  | o :: lo' => 
      let o_flagged  := compile2_flagged_object_declaration_f st o in
      let lo_flagged := compile2_flagged_object_declarations_f st lo' in
        o_flagged :: lo_flagged
  end.

Function compile2_flagged_parameter_specification_f (param: parameter_specification): parameter_specification_x :=
  match param with
  | mkparameter_specification ast_num x t m =>
      mkparameter_specification_x ast_num x t m
  end.

Function compile2_flagged_parameter_specifications_f (lparam: list parameter_specification): list parameter_specification_x :=
  match lparam with
  | nil => nil
  | param :: lparam' =>
      let param_flagged := compile2_flagged_parameter_specification_f param in
      let lparam_flagged := compile2_flagged_parameter_specifications_f lparam' in
        param_flagged :: lparam_flagged
  end.


Function compile2_flagged_declaration_f (st: symboltable) (d: declaration): option declaration_x :=
  match d with
  | D_Null_Declaration => Some D_Null_Declaration_X
  | D_Type_Declaration ast_num t =>
      let t_flagged := compile2_flagged_type_declaration_f t in
        Some (D_Type_Declaration_X ast_num t_flagged)
  | D_Object_Declaration ast_num o =>
      let o_flagged := compile2_flagged_object_declaration_f st o in 
        Some (D_Object_Declaration_X ast_num o_flagged)
  | D_Procedure_Body ast_num p =>
      match compile2_flagged_procedure_body_f st p with
      | Some p_flagged => Some (D_Procedure_Body_X ast_num p_flagged)
      | None           => None
      end
  | D_Seq_Declaration ast_num d1 d2 =>
      let d1' := compile2_flagged_declaration_f st d1 in
      let d2' := compile2_flagged_declaration_f st d2 in
      match (d1', d2') with 
      | (Some d1_flagged, Some d2_flagged) => Some (D_Seq_Declaration_X ast_num d1_flagged d2_flagged)
      | _ => None
      end
  end

with compile2_flagged_procedure_body_f (st: symboltable) (p: procedure_body): option procedure_body_x :=
  match p with
  | mkprocedure_body ast_num p params decls stmt =>
      let params_flagged := compile2_flagged_parameter_specifications_f params in
      let decls' := compile2_flagged_declaration_f st decls in
      let stmt' := compile2_flagged_stmt_f st stmt in
      match (decls', stmt') with 
      | (Some decls_flagged, Some stmt_flagged) => Some (mkprocedure_body_x ast_num p params_flagged decls_flagged stmt_flagged)
      | _ => None
      end
  end.


(* ***************************************************************
                 Semantics Equivalence Proof
   *************************************************************** *)

(** * Semantics Equivalence Proof For Run-Time Checks Generation *)

Scheme expression_ind := Induction for expression Sort Prop 
                         with name_ind := Induction for name Sort Prop.

Section Checks_Generator_Function_Correctness_Proof.

  Lemma compile2_flagged_exp_f_correctness: forall e e' st,
    compile2_flagged_exp_f st e = e' ->
      compile2_flagged_exp st e e'.
  Proof.
    apply (expression_ind
      (fun e: expression => forall (e' : expression_x) (st: symboltable),
        compile2_flagged_exp_f st e = e' ->
        compile2_flagged_exp   st e e')
      (fun n: name => forall (n': name_x) (st: symboltable),
        compile2_flagged_name_f st n = n' ->
        compile2_flagged_name   st n n')
      ); smack;
    [ (*E_Literal*) 
      destruct l;
      [ remember ((min_signed <=? z)%Z && (z <=? max_signed)%Z) as b; destruct b;
        smack; constructor; smack |
        smack; constructor
      ] | 
      (*E_Name*) | 
      (*E_Binary_Operation a b e e0*) destruct b |
      (*E_Unary_Operation a u e*) destruct u |
      (*E_Identifier a i*) |
      (*E_Indexed_Component a n e*) |
      (*E_Selected_Component a n i*)
    ];
    match goal with
    | [H: _ = ?b |- in_bound _ _ ?b] => rewrite <- H; constructor; smack
    | _ => constructor; smack
    end.
  Qed.

  Lemma compile2_flagged_name_f_correctness: forall st n n',
    compile2_flagged_name_f st n = n' ->
      compile2_flagged_name st n n'.
  Proof.
    intros st n;
    induction n; smack; constructor; smack;
    apply compile2_flagged_exp_f_correctness; auto.
  Qed.

  Lemma compile2_flagged_args_f_correctness: forall st params args args',
    compile2_flagged_args_f st params args = Some args' ->
      compile2_flagged_args st params args args'.
  Proof.
    induction params; smack.
  - destruct args; smack;
    constructor.
  - destruct args; smack.
    remember (compile2_flagged_args_f st params args) as b1;
    remember (parameter_mode a) as b2; 
    destruct b1, b2; smack.
    + (*In Mode*)
      remember (is_range_constrainted_type (parameter_subtype_mark a)) as x;
      destruct x; smack;
      [ apply C2_Flagged_Args_In_RangeCheck |
        apply C2_Flagged_Args_In
      ]; smack; 
      apply compile2_flagged_exp_f_correctness; auto.
    + (*Out Mode*)
      destruct e; smack;
      remember (fetch_exp_type a0 st) as b3;
      destruct b3; smack;
      remember (is_range_constrainted_type t) as b4; destruct b4; smack;
      [ apply C2_Flagged_Args_Out_RangeCheck with (t := t) |
        apply C2_Flagged_Args_Out with (t := t)
      ]; smack;
      apply compile2_flagged_name_f_correctness; auto.
    + (*In_Out Mode*)
      destruct e; smack;
      remember (is_range_constrainted_type (parameter_subtype_mark a)) as b3;
      remember (fetch_exp_type a0 st) as b4;
      destruct b3, b4; smack;
      remember (is_range_constrainted_type t) as b5;
      destruct b5; smack;
      [ apply C2_Flagged_Args_InOut_RangeCheck with (t:=t) |
        apply C2_Flagged_Args_InOut_In_RangeCheck with (t:=t) |
        apply C2_Flagged_Args_InOut_Out_RangeCheck with (t:=t) |
        apply C2_Flagged_Args_InOut with (t:=t)
      ]; auto;
      apply compile2_flagged_name_f_correctness; auto.
  Qed.

  Lemma compile2_flagged_stmt_f_correctness: forall st c c',
    compile2_flagged_stmt_f st c = Some c' ->
      compile2_flagged_stmt st c c'.
  Proof.
    induction c; smack.
  - (*S_Null*)
    constructor.
  - (*S_Assignment*)
    remember (fetch_exp_type (name_astnum n) st ) as b1;
    destruct b1; smack;
    remember (is_range_constrainted_type t) as b2;
    destruct b2; smack;
    [ apply C2_Flagged_Assignment_RangeCheck with (t := t) |
      apply C2_Flagged_Assignment with (t := t)
    ]; auto;
    solve 
    [ apply compile2_flagged_name_f_correctness; auto |
      apply compile2_flagged_exp_f_correctness; auto
    ].
  - (*S_If*)
    remember (compile2_flagged_stmt_f st c1) as b1;
    remember (compile2_flagged_stmt_f st c2) as b2;
    destruct b1, b2; smack;
    constructor; smack;
    apply compile2_flagged_exp_f_correctness; auto.
  - (*S_While_Loop*)
    remember (compile2_flagged_stmt_f st c) as b1;
    destruct b1; smack;
    constructor; smack;
    apply compile2_flagged_exp_f_correctness; auto.
  - (*S_Procedure_Call*)
    remember (fetch_proc p st) as b1;
    destruct b1; smack;
    destruct t;
    remember (compile2_flagged_args_f st (procedure_parameter_profile p0) l) as b2;
    destruct b2; smack;
    apply C2_Flagged_Procedure_Call with (n := l0) (pb := p0) (params := (procedure_parameter_profile p0)); smack;
    apply compile2_flagged_args_f_correctness; auto.
  - (*S_Sequence*)
    remember (compile2_flagged_stmt_f st c1) as b1;
    remember (compile2_flagged_stmt_f st c2) as b2;
    destruct b1, b2; smack;
    constructor; auto.
  Qed.

  Lemma compile2_flagged_type_declaration_f_correctness: forall t t',
    compile2_flagged_type_declaration_f t = t' ->
        compile2_flagged_type_declaration t t'.
  Proof.
    destruct t; smack;
    try (destruct r); constructor.
  Qed.

  Lemma compile2_flagged_object_declaration_f_correctness: forall st o o',
    compile2_flagged_object_declaration_f st o = o' ->
      compile2_flagged_object_declaration st o o'.
  Proof.
    intros;
    functional induction compile2_flagged_object_declaration_f st o; smack;
    [ constructor |
      apply C2_Flagged_Object_Declaration_RangeCheck |
      apply C2_Flagged_Object_Declaration 
    ]; auto; apply compile2_flagged_exp_f_correctness; auto.
  Qed.

  Lemma compile2_flagged_object_declarations_f_correctness: forall st lo lo',
    compile2_flagged_object_declarations_f st lo = lo' ->
      compile2_flagged_object_declarations st lo lo'.
  Proof.
    induction lo; smack;
    constructor; smack;
    apply compile2_flagged_object_declaration_f_correctness; auto.
  Qed.

  Lemma compile2_flagged_parameter_specification_f_correctness: forall param param',
    compile2_flagged_parameter_specification_f param = param' ->
      compile2_flagged_parameter_specification param param'.
  Proof.
    smack;
    destruct param;
    constructor.  
  Qed.

  Lemma compile2_flagged_parameter_specifications_f_correctness: forall lparam lparam',
    compile2_flagged_parameter_specifications_f lparam = lparam' ->
      compile2_flagged_parameter_specifications lparam lparam'.
  Proof.
    induction lparam; smack;
    constructor; smack;
    apply compile2_flagged_parameter_specification_f_correctness; auto.
  Qed.


  Scheme declaration_ind := Induction for declaration Sort Prop 
                            with procedure_body_ind := Induction for procedure_body Sort Prop.

  Lemma compile2_flagged_declaration_f_correctness: forall d d' st,
    compile2_flagged_declaration_f st d = Some d' ->
      compile2_flagged_declaration st d d'.
  Proof.
    apply (declaration_ind
      (fun d: declaration => forall (d' : declaration_x) (st: symboltable),
        compile2_flagged_declaration_f st d = Some d' ->
        compile2_flagged_declaration st d d')
      (fun p: procedure_body => forall (p': procedure_body_x) (st: symboltable),
        compile2_flagged_procedure_body_f st p = Some p' ->
        compile2_flagged_procedure_body st p p')
      ); smack.
  - constructor.
  - constructor;
    apply compile2_flagged_type_declaration_f_correctness; auto.
  - constructor;
    apply compile2_flagged_object_declaration_f_correctness; auto.
  - remember (compile2_flagged_procedure_body_f st p) as x; 
    destruct x; smack;
    constructor; auto.
  - remember (compile2_flagged_declaration_f st d) as x;
    remember (compile2_flagged_declaration_f st d0) as y;
    destruct x, y; smack;
    constructor; smack.
  - remember (compile2_flagged_declaration_f st procedure_declarative_part) as x;
    remember (compile2_flagged_stmt_f st procedure_statements) as y;
    destruct x, y; smack;
    constructor;
    [ apply compile2_flagged_parameter_specifications_f_correctness | |
      apply compile2_flagged_stmt_f_correctness
    ]; auto.
  Qed.

  Lemma compile2_flagged_procedure_declaration_f_correctness: forall st p p',
    compile2_flagged_procedure_body_f st p = Some p' ->
      compile2_flagged_procedure_body st p p'.
  Proof.
    intros;
    destruct p; smack.
    remember (compile2_flagged_declaration_f st procedure_declarative_part) as x;
    remember (compile2_flagged_stmt_f st procedure_statements) as y;
    destruct x, y; smack;
    constructor;
    [ apply compile2_flagged_parameter_specifications_f_correctness |
      apply compile2_flagged_declaration_f_correctness |
      apply compile2_flagged_stmt_f_correctness 
    ]; auto.
  Qed.

End Checks_Generator_Function_Correctness_Proof.


Section Checks_Generator_Function_Completeness_Proof.

  Lemma compile2_flagged_exp_f_completeness: forall e e' st,
    compile2_flagged_exp st e e' ->
      compile2_flagged_exp_f st e = e'.
  Proof.
    apply (expression_ind
      (fun e: expression => forall (e' : expression_x) (st: symboltable),
        compile2_flagged_exp   st e e' ->
        compile2_flagged_exp_f st e = e')
      (fun n: name => forall (n': name_x) (st: symboltable),
        compile2_flagged_name   st n n' ->
        compile2_flagged_name_f st n = n')
      ); smack;
    match goal with
    | [H: compile2_flagged_exp  _ ?e ?e' |- _] => inversion H; clear H; smack
    | [H: compile2_flagged_name _ ?n ?n' |- _] => inversion H; clear H; smack
    end;
    repeat progress match goal with
    | [H1:forall (e' : expression_x) (st : symboltable),
          compile2_flagged_exp _ ?e e' ->
          compile2_flagged_exp_f _ ?e = e',
       H2:compile2_flagged_exp _ ?e ?e1_flagged |- _] => specialize (H1 _ _ H2); smack
    | [H1:forall (n' : name_x) (st : symboltable),
          compile2_flagged_name _ ?n n' ->
          compile2_flagged_name_f _ ?n = n',
       H2:compile2_flagged_name _ ?n ?n_flagged |- _] => specialize (H1 _ _ H2); smack
    end;
    match goal with
    | [H: in_bound _ _ _ |- _] => inversion H; smack
    | _ => idtac
    end;
    [ destruct b | 
      destruct u 
    ]; smack.
  Qed.

  Lemma compile2_flagged_name_f_completeness: forall st n n',
    compile2_flagged_name st n n' ->
      compile2_flagged_name_f st n = n'.
  Proof.
    intros;
    induction H; smack;
    match goal with
    | [H: compile2_flagged_exp ?st ?e ?e' |- _] => 
        specialize (compile2_flagged_exp_f_completeness _ _ _ H); smack
    end; auto.
  Qed.

  Lemma compile2_flagged_args_f_completeness: forall st params args args',
    compile2_flagged_args st params args args' ->
      compile2_flagged_args_f st params args = Some args'.
  Proof.
    induction params; smack;
    match goal with
    | [H: compile2_flagged_args _ _ ?args ?args' |- _] => inversion H; clear H; smack
    end;
    match goal with
    | [H1: forall (args : list expression) (args' : list expression_x),
           compile2_flagged_args _ ?params _ _ ->
           compile2_flagged_args_f _ ?params _ = Some _,
       H2: compile2_flagged_args _ ?params _ _ |- _] => specialize (H1 _ _ H2)
    end;
    match goal with
    | [H: compile2_flagged_args_f ?st ?params ?larg = Some _ |- _] => rewrite H; simpl
    end;
    match goal with
    | [H: compile2_flagged_exp _ ?e ?e' |- _] => specialize (compile2_flagged_exp_f_completeness _ _ _ H); smack
    | [H: compile2_flagged_name _ ?n ?n' |- _] => specialize (compile2_flagged_name_f_completeness _ _ _ H); smack
    | _ => idtac
    end; auto.
  Qed.

  Lemma compile2_flagged_stmt_f_completeness: forall st c c',
    compile2_flagged_stmt st c c' ->
      compile2_flagged_stmt_f st c = Some c'.
  Proof.
    induction c; smack;
    match goal with
    | [H: compile2_flagged_stmt _ ?c ?c' |- _] => inversion H; clear H; smack
    end;
    repeat progress match goal with
    | [H: compile2_flagged_exp  _ ?e ?e' |- _] => specialize (compile2_flagged_exp_f_completeness  _ _ _ H); clear H
    | [H: compile2_flagged_name _ ?n ?n' |- _] => specialize (compile2_flagged_name_f_completeness _ _ _ H); clear H
    | [H1: forall c' : statement_x,
           compile2_flagged_stmt _ ?c _ ->
           compile2_flagged_stmt_f _ ?c = Some _,
       H2: compile2_flagged_stmt _ ?c _ |- _ ] => specialize (H1 _ H2)
    end; smack;
    match goal with
    | [H: compile2_flagged_args _ _ _ _ |- _ ] => specialize (compile2_flagged_args_f_completeness _ _ _ _ H); smack
    end.
  Qed.

  Lemma compile2_flagged_type_declaration_f_completeness: forall t t',
    compile2_flagged_type_declaration t t' ->
      compile2_flagged_type_declaration_f t = t'.
  Proof.
    destruct t; intros;
    match goal with
    | [H: compile2_flagged_type_declaration _ _ |- _] => inversion H; smack
    end.
  Qed.

  Lemma compile2_flagged_object_declaration_f_completeness: forall st o o',
    compile2_flagged_object_declaration st o o' ->
      compile2_flagged_object_declaration_f st o = o'.
  Proof.
    intros;
    functional induction compile2_flagged_object_declaration_f st o;
    match goal with
    | [H: compile2_flagged_object_declaration _ _ _ |- _] => inversion H; smack
    end;
    match goal with
    | [H: compile2_flagged_exp _ _ _ |- _] => 
        specialize (compile2_flagged_exp_f_completeness _ _ _ H); smack
    end. 
  Qed.

  Lemma compile2_flagged_object_declarations_f_completeness: forall st lo lo',
    compile2_flagged_object_declarations st lo lo' ->
      compile2_flagged_object_declarations_f st lo = lo'.
  Proof.
    induction lo; smack;
    match goal with
    | [H: compile2_flagged_object_declarations _ _ _ |- _] => inversion H; clear H; smack
    end;
    match goal with
    | [H: compile2_flagged_object_declaration _ ?o ?o' |- _] => 
        specialize (compile2_flagged_object_declaration_f_completeness _ _ _ H); smack
    end;
    specialize (IHlo _ H5); smack.
  Qed.

  Lemma compile2_flagged_parameter_specification_f_completeness: forall param param',
    compile2_flagged_parameter_specification param param' ->
      compile2_flagged_parameter_specification_f param = param'.
  Proof.
    intros;
    inversion H; auto.
  Qed.

  Lemma compile2_flagged_parameter_specifications_f_completeness: forall lparam lparam',
    compile2_flagged_parameter_specifications lparam lparam' ->
      compile2_flagged_parameter_specifications_f lparam = lparam'.
  Proof.
    induction lparam; intros;
    inversion H; auto;
    specialize (IHlparam _ H4);
    match goal with
    | [H: compile2_flagged_parameter_specification _ _ |- _] => 
        specialize (compile2_flagged_parameter_specification_f_completeness _ _ H); smack
    end.
  Qed.

  Lemma compile2_flagged_declaration_f_completeness: forall d d' st,
    compile2_flagged_declaration st d d' ->
      compile2_flagged_declaration_f st d = Some d'.
  Proof.
    apply (declaration_ind
      (fun d: declaration => forall (d' : declaration_x) (st: symboltable),
        compile2_flagged_declaration st d d' ->
        compile2_flagged_declaration_f st d = Some d')
      (fun p: procedure_body => forall (p': procedure_body_x) (st: symboltable),
        compile2_flagged_procedure_body st p p' ->
        compile2_flagged_procedure_body_f st p = Some p')
      ); smack;
    match goal with
    | [H: compile2_flagged_declaration _ _ _ |- _] => inversion H; clear H; smack
    | [H: compile2_flagged_procedure_body _ _ _ |- _] => inversion H; clear H; smack
    end;
    repeat progress match goal with
    | [H: compile2_flagged_type_declaration _ _ |- _] => 
        specialize (compile2_flagged_type_declaration_f_completeness _ _ H); smack
    | [H: compile2_flagged_object_declaration _ _ _ |- _] =>
        specialize (compile2_flagged_object_declaration_f_completeness _ _ _ H); smack
    | [H: compile2_flagged_parameter_specifications _ _ |- _] =>
        specialize (compile2_flagged_parameter_specifications_f_completeness _ _ H); clear H; smack
    | [H: compile2_flagged_stmt _ _ _ |- _] =>
        specialize (compile2_flagged_stmt_f_completeness _ _ _ H); clear H; smack
    | [H1: forall (p' : procedure_body_x) (st : symboltable),
           compile2_flagged_procedure_body _ ?p _ ->
           compile2_flagged_procedure_body_f _ ?p = Some _,
       H2: compile2_flagged_procedure_body _ ?p _ |- _] =>
        specialize (H1 _ _ H2); smack
    | [H1: forall (d' : declaration_x) (st : symboltable),
           compile2_flagged_declaration _ ?d _ ->
           compile2_flagged_declaration_f _ ?d = Some _,
       H2: compile2_flagged_declaration _ ?d _ |- _] => 
        specialize (H1 _ _ H2); clear H2; smack
    end.
  Qed.

  Lemma compile2_flagged_procedure_declaration_f_completeness: forall st p p',
    compile2_flagged_procedure_body st p p' ->
      compile2_flagged_procedure_body_f st p = Some p'.
  Proof.
    intros;
    destruct p;
    match goal with
    [H: compile2_flagged_procedure_body _ _ _ |- _] => inversion H; clear H; smack
    end;
    repeat progress match goal with
    | [H: compile2_flagged_parameter_specifications _ _ |- _] =>
        specialize (compile2_flagged_parameter_specifications_f_completeness _ _ H); clear H; smack
    | [H: compile2_flagged_stmt _ _ _ |- _] =>
        specialize (compile2_flagged_stmt_f_completeness _ _ _ H); clear H; smack
    | [H: compile2_flagged_declaration _ _ _ |- _] => 
        specialize (compile2_flagged_declaration_f_completeness _ _ _ H); clear H; smack
    end.
  Qed.

End Checks_Generator_Function_Completeness_Proof.


(** * Lemmas *)

Require Import CpdtTactics.

Lemma exp_ast_num_eq: forall st e e',
  compile2_flagged_exp st e e' ->
    expression_astnum e = expression_astnum_x e'.
Proof.
  intros; inversion H; smack.
Qed.

Lemma name_ast_num_eq: forall st n n',
  compile2_flagged_name st n n' ->
    name_astnum n = name_astnum_x n'.
Proof.
  intros; inversion H; smack.
Qed.

Lemma exp_exterior_checks_beq_nil: forall st e e',
  compile2_flagged_exp st e e' ->
    exp_exterior_checks e' = nil.
Proof.
  intros; 
  inversion H; smack;
  inversion H; subst;
  destruct n; 
  match goal with
  | [H: compile2_flagged_name _ _ _ |- _] => inversion H; smack
  end.
Qed.

Lemma name_exterior_checks_beq_nil: forall st n n',
  compile2_flagged_name st n n' ->
    name_exterior_checks n' = nil.
Proof.
  intros; 
  inversion H; smack.
Qed.


Lemma procedure_components_rel: forall st p p',
  compile2_flagged_procedure_body st p p' ->
  compile2_flagged_parameter_specifications (procedure_parameter_profile p) (procedure_parameter_profile_x p') /\
  compile2_flagged_declaration st (procedure_declarative_part p) (procedure_declarative_part_x p') /\
  compile2_flagged_stmt st (procedure_statements p) (procedure_statements_x p').
Proof.
  intros.
  inversion H; smack.
Qed.


(** * Compile To Flagged Symbol Table *)


Inductive compile2_flagged_proc_declaration_map: symboltable ->
                                                 list (idnum * (level * procedure_body)) -> 
                                                 list (idnum * (level * procedure_body_x)) -> Prop :=
    | C2_Flagged_Proc_Declaration_Map_Null: forall st,
        compile2_flagged_proc_declaration_map st nil nil
    | C2_Flagged_Proc_Declaration_Map: forall st pb pb' pl pl' p l,
        compile2_flagged_procedure_body st pb pb' ->
        compile2_flagged_proc_declaration_map st pl pl' ->
        compile2_flagged_proc_declaration_map st ((p, (l, pb)) :: pl) ((p, (l, pb')) :: pl').

Inductive compile2_flagged_type_declaration_map: list (idnum * type_declaration) -> 
                                                 list (idnum * type_declaration_x) -> Prop :=
    | C2_Flagged_Type_Declaration_Map_Null:
        compile2_flagged_type_declaration_map nil nil
    | C2_Flagged_Type_Declaration_Map: forall t t' tl tl' x,
        compile2_flagged_type_declaration t t' ->
        compile2_flagged_type_declaration_map tl tl' ->
        compile2_flagged_type_declaration_map ((x, t) :: tl) ((x, t') :: tl').

Inductive compile2_flagged_symbol_table: symboltable -> symboltable_x -> Prop := 
  | C2_Flagged_SymTable: forall p p' t t' x e srcloc nametable,
      compile2_flagged_proc_declaration_map (mkSymbolTable x p t e srcloc nametable) p p' ->
      compile2_flagged_type_declaration_map t t' ->
      compile2_flagged_symbol_table (mkSymbolTable x p t e srcloc nametable) (mkSymbolTable_x x p' t' e srcloc nametable).


(** ** Lemmas *)

Lemma procedure_declaration_rel: forall st pm pm' p n pb,
  compile2_flagged_proc_declaration_map st pm pm' ->
    Symbol_Table_Module.SymTable_Procs.fetches p pm = Some (n, pb) ->
      exists pb',
        Symbol_Table_Module_X.SymTable_Procs.fetches p pm' = Some (n, pb') /\ 
        compile2_flagged_procedure_body st pb pb'.
Proof.
  intros st pm pm' p n pb H; revert p n pb.
  induction H; intros.
- inversion H; inversion H0; auto.
- unfold Symbol_Table_Module.SymTable_Procs.fetches in H1.
  unfold Symbol_Table_Module_X.SymTable_Procs.fetches.
  remember (beq_nat p0 p) as Beq.
  destruct Beq. 
  + smack.
  + specialize (IHcompile2_flagged_proc_declaration_map _ _ _ H1).
    auto.
Qed.

Lemma symbol_table_procedure_rel: forall st st' p n pb,
  compile2_flagged_symbol_table st st' ->  
    fetch_proc p st = Some (n, pb) ->
      exists pb',
        fetch_proc_x p st' = Some (n, pb') /\
        compile2_flagged_procedure_body st pb pb'.
Proof.
  intros.
  inversion H; subst; clear H.
  unfold fetch_proc_x;
  unfold fetch_proc in H0;
  simpl in *.
  specialize (procedure_declaration_rel _ _ _ _ _ _ H1 H0);
  auto.
Qed.

Lemma symbol_table_var_rel: forall st st' x t,
  compile2_flagged_symbol_table st st' ->
    fetch_var x st = t ->
      fetch_var_x x st' = t.
Proof.
  intros.
  inversion H; smack.
Qed.

Lemma type_declaration_rel: forall tm tm' t td,
  compile2_flagged_type_declaration_map tm tm' ->
    Symbol_Table_Module.SymTable_Types.fetches t tm = Some td ->
    exists td',
      Symbol_Table_Module_X.SymTable_Types.fetches t tm' = Some td' /\
      compile2_flagged_type_declaration td td'.
Proof.
  intros tm tm' t td H; revert t td.
  induction H; smack.
  destruct (beq_nat t0 x).
- inversion H; smack.
- apply IHcompile2_flagged_type_declaration_map; auto.
Qed.

Lemma symbol_table_type_rel: forall st st' t td,
  compile2_flagged_symbol_table st st' ->
    fetch_type t st = Some td ->
      exists td',
        fetch_type_x t st' = Some td' /\ compile2_flagged_type_declaration td td'.
Proof.
  intros.
  inversion H; smack.
  unfold fetch_type, Symbol_Table_Module.fetch_type in H0; 
  unfold fetch_type_x, Symbol_Table_Module_X.fetch_type; smack.
  apply type_declaration_rel with (tm := t0); auto.
Qed.

Lemma symbol_table_exp_type_rel: forall st st' e t,
  compile2_flagged_symbol_table st st' ->
    fetch_exp_type e st = t ->
      fetch_exp_type_x e st' = t.
Proof.
  intros.
  inversion H; smack.  
Qed.

Lemma subtype_range_rel: forall st st' t l u,
  compile2_flagged_symbol_table st st' ->
    extract_subtype_range st t (Range l u) ->
      extract_subtype_range_x st' t (Range_X l u).
Proof.
  intros.
  inversion H0; clear H0; smack.
  specialize (symbol_table_type_rel _ _ _ _ H H6); clear H6; smack.
  apply Extract_Range_X with (tn := tn) (td := x); smack.
  destruct td; inversion H7; subst;
  inversion H2; auto.
Qed.

Lemma index_range_rel: forall st st' t l u,
  compile2_flagged_symbol_table st st' ->
    extract_array_index_range st t (Range l u) ->
      extract_array_index_range_x st' t (Range_X l u).
Proof.
  intros.
  inversion H0; clear H0; smack.
  specialize (symbol_table_type_rel _ _ _ _ H H3); clear H3; smack.
  specialize (symbol_table_type_rel _ _ _ _ H H7); clear H7; smack.  
  apply Extract_Index_Range_X with (a_ast_num := a_ast_num) (tn := tn) (tm := tm) 
                                   (typ := typ) (tn' := tn') (td := x0); smack.
  inversion H2; auto.
  destruct td; inversion H8; subst;
  inversion H5; auto.
Qed.
