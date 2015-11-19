Require Export checks_generator.

(** * Count the number of check flags *) 

Section Check_Count.
  
  Function count_list_len (l: list check_flag): nat :=
    match l with
    | nil => 0
    | hd :: tl => (count_list_len tl) + 1
    end.
  
  (** ** Count Check Flags For Expression *)

  Function count_exp_check_flags (e: expression_x): nat :=
    match e with
    | E_Literal_X ast_num l in_cks ex_cks =>
        (count_list_len in_cks) + (count_list_len ex_cks)
    | E_Name_X ast_num n =>
        count_name_check_flags n
    | E_Binary_Operation_X ast_num op e1 e2 in_cks ex_cks =>
        (count_list_len in_cks) + (count_list_len ex_cks) + (count_exp_check_flags e1) + (count_exp_check_flags e2)
    | E_Unary_Operation_X ast_num op e in_cks ex_cks =>
        (count_list_len in_cks) + (count_list_len ex_cks) + (count_exp_check_flags e)
     end

  (** ** Check Flags Comparison Function For Name *)

  with count_name_check_flags (n: name_x): nat :=
    match n with
    | E_Identifier_X ast_num x ex_cks =>
        count_list_len ex_cks
    | E_Indexed_Component_X ast_num x e ex_cks =>
        (count_list_len ex_cks) + (count_name_check_flags x) + (count_exp_check_flags e)
    | E_Selected_Component_X ast_num x f ex_cks =>
        (count_list_len ex_cks) + (count_name_check_flags x)
    end.

  Function count_args_check_flags (le: list expression_x): nat :=
    match le with
    | nil => 0
    | (e1 :: le1') =>
        (count_exp_check_flags e1) + (count_args_check_flags le1')
    end.


  (** ** Count Check Flags For Statement *)

  Function count_stmt_check_flags (c: statement_x): nat :=
    match c with
    | S_Null_X => 0
    | S_Assignment_X ast_num x e =>
        (count_name_check_flags x) + (count_exp_check_flags e)
    | S_If_X ast_num e c1 c2 =>
        (count_exp_check_flags e) + (count_stmt_check_flags c1) + (count_stmt_check_flags c2)
    | S_While_Loop_X ast_num e c =>
        (count_exp_check_flags e) + (count_stmt_check_flags c)
    | S_Procedure_Call_X ast_num p_ast_num p args =>
        (count_args_check_flags args)
    | S_Sequence_X ast_num c1 c2 =>
        (count_stmt_check_flags c1) + (count_stmt_check_flags c2)
    end.

  Function count_type_decl_check_flags (t: type_declaration_x): nat :=
    match t with
    | Subtype_Declaration_X ast_num tn t (Range_X l u) =>
        0
    | Derived_Type_Declaration_X ast_num tn t (Range_X l u) =>
        0
    | Integer_Type_Declaration_X ast_num tn (Range_X l u) =>  
        0
    | Array_Type_Declaration_X ast_num tn tm t =>
        0
    | Record_Type_Declaration_X ast_num tn fs =>
        0
    end.

  Function count_object_decl_check_flags (o: object_declaration_x): nat :=
    match o with
    | mkobject_declaration_x ast_num x t None =>
        0
    | mkobject_declaration_x ast_num x t (Some e) =>
        count_exp_check_flags e
    end.

  Function count_object_decls_check_flags (lo: list object_declaration_x): nat :=
    match lo with
    | nil => 0
    | o1 :: lo1' => 
        (count_object_decl_check_flags o1) + (count_object_decls_check_flags lo1')
    end.

  Function count_param_spec_check_flags (param: parameter_specification_x): nat :=
    match param with
    | mkparameter_specification_x ast_num x m t =>
        0
    end.

  Function count_param_specs_check_flags (lparam: list parameter_specification_x): nat :=
    match lparam with
    | nil => 0
    | param1 :: lparam1' => 
        (count_param_spec_check_flags param1) + (count_param_specs_check_flags lparam1')
    end.

  (** ** Count Check Flags For Declaration *)

  Function count_declaration_check_flags (d: declaration_x): nat :=
    match d with
    | D_Null_Declaration_X => 0
    | D_Type_Declaration_X ast_num t => 
        count_type_decl_check_flags t
    | D_Object_Declaration_X ast_num o =>
        count_object_decl_check_flags o
    | D_Procedure_Body_X ast_num p =>
        count_procedure_body_check_flags p
    | D_Seq_Declaration_X ast_num d1 d2 =>
        (count_declaration_check_flags d1) + (count_declaration_check_flags d2)
    end

  with count_procedure_body_check_flags (p: procedure_body_x): nat :=
    match p with
    | mkprocedure_body_x ast_num p params decls stmt =>
        (count_param_specs_check_flags params) + 
            (count_declaration_check_flags decls) + 
                (count_stmt_check_flags stmt)
    end.

  Definition count_option_declaration_check_flags (x: option declaration_x): nat :=
    match x with
    | Some ast => count_declaration_check_flags ast
    | None => 0
    end.

End Check_Count.









