Require Export checks_optimization.

(**********************************************)
(** * executable check optimization functions *)
(**********************************************)

Function extract_subtype_range_f (st: symboltable_x) (t: type): option range_x :=
  match subtype_num t with
  | Some tn => 
    match fetch_type_x tn st with
    | Some td =>
        match subtype_range_x td with
        | Some (Range_X l u) => Some (Range_X l u) 
        | None => None 
        end 
    | None => None 
    end
  | None => None
  end.

Function bound_of_type_f (st: symboltable_x) (t: type): option bound :=
  match t with
  | Boolean => Some Boolval
  | Integer => Some int32_bound
  | Array_Type t => Some Aggregate
  | Record_Type t => Some Aggregate 
  | _ => 
    match extract_subtype_range_f st t with 
    | Some (Range_X l u) => Some (Interval l u)
    | None => None 
    end
  end.

Function bound_of_array_component_type_f (st: symboltable_x) (t: typenum): option bound :=
  match fetch_type_x t st with
  | Some (Array_Type_Declaration_X ast_num tn indexSubtypeMark componentType) =>
    match bound_of_type_f st componentType with
    | Some boundValue => Some boundValue
    | None => None 
    end
  | _ => None
  end.

Function bound_of_record_field_type_f (st: symboltable_x) (t: typenum) (f: idnum): option bound :=
  match fetch_type_x t st with
  | Some (Record_Type_Declaration_X ast_num tn fields) => 
    match record_field_type fields f with 
    | Some ft => 
      match bound_of_type_f st ft with 
      | Some boundValue => Some boundValue
      | None => None 
      end
    | None => None 
    end
  | _ => None 
  end.

Function in_bound_f (v: Z) (bd: bound): option bool :=
  match bd with
  | Interval l u => Some ((l <=? v)%Z && (v <=? u)%Z)
  | _ => None 
  end.

Function sub_bound_f (bd1: bound) (bd2: bound): option bool :=
  match bd1, bd2 with 
  | Interval u v, Interval u' v' =>
    match in_bound_f u (Interval u' v'), in_bound_f v (Interval u' v') with
    | Some true, Some true => Some true
    | Some _, Some _ => Some false
    | _, _ => None
    end
  | _, _ => None
  end.

Function optimize_overflow_check_f (bd: bound) (cks: check_flags): option (bound * check_flags) :=
  match sub_bound_f bd int32_bound with
  | Some true => Some (bd, remove_check_flag Do_Overflow_Check cks)
  | Some false => Some (int32_bound, cks)
  | None => None 
  end.

Function optimize_range_check_f (e: expression_x) (bd1: bound) (bd2: bound): option expression_x :=
  match sub_bound_f bd1 bd2 with
  | Some true => Some (update_exterior_checks_exp e (remove_check_flag Do_Range_Check (exp_exterior_checks e)))
  | Some false => Some e
  | None => None 
  end.

Function optimize_range_check_on_copy_out_f (e: expression_x) (bd1: bound) (bd2: bound): option expression_x :=
  match sub_bound_f bd1 bd2 with
  | Some true => Some (update_exterior_checks_exp e (remove_check_flag Do_Range_Check_On_CopyOut (exp_exterior_checks e)))
  | Some false => Some e
  | None => None
  end.

Function optimize_rtc_binop_f (op: binary_operator) (bd1: bound) (bd2: bound) (cks: check_flags): option (bound * check_flags) :=
  match op with
  | Plus => 
    match bd1, bd2 with
    | (Interval u v), (Interval u' v') => 
      match Math.add (Int u) (Int u'), Math.add (Int v) (Int v') with 
      | Some (Int x), Some (Int y) =>
        match optimize_overflow_check_f (Interval x y) cks with 
        | Some (retBound, cks') => Some (retBound, cks')
        | None => None
        end
      | _, _ => None
      end
    | _, _ => None
    end
  | Minus => 
    match bd1, bd2 with
    | (Interval u v), (Interval u' v') => 
      match Math.sub (Int u) (Int v'), Math.sub (Int v) (Int u') with 
      | Some (Int x), Some (Int y) =>
        match optimize_overflow_check_f (Interval x y) cks with 
        | Some (retBound, cks') => Some (retBound, cks')
        | None => None
        end
      | _, _ => None
      end
    | _, _ => None
    end
  | Multiply => 
    match bd1, bd2 with
    | (Interval u v), (Interval u' v') =>  Some (int32_bound, cks)
    | _, _ => None
    end
  | Divide => 
    match bd1, bd2 with
    | (Interval u v), (Interval u' v') =>
      match in_bound_f 0 (Interval u' v') with 
      | Some true => Some (int32_bound, cks)
      | Some false => Some (int32_bound, remove_check_flag Do_Division_Check cks)
      | None => None
      end
    | _, _ => None
    end
  | _ =>
    Some (Boolval, cks) 
  end.

Function optimize_rtc_unop_f (op: unary_operator) (bd: bound) (cks: check_flags): option (bound * check_flags) :=
  match op with
  | Unary_Minus => 
    match bd with
    | Interval u v => 
      match Math.unary_minus (Int v), Math.unary_minus (Int u) with 
      | Some (Int x), Some (Int y) =>
        match optimize_overflow_check_f (Interval x y) cks with 
        | Some (retBound, cks') => Some (retBound, cks') 
        | None => None 
        end
      | _, _ => None
      end
    | _ => None
    end
  | _ => Some (bd, cks) 
  end.

Function optimize_literal_f (l: literal) (cks: check_flags): option (bound * check_flags) :=
  match l with
  | Boolean_Literal v => Some (Boolval, cks)
  | Integer_Literal v => 
    match optimize_overflow_check_f (Interval v v) cks with
    | Some (retBound, cks') => Some (retBound, cks')
    | None => None 
    end
  end.

Function extract_array_index_range_f (st: symboltable_x) (t: typenum): option range_x :=
  match fetch_type_x t st with
  | Some (Array_Type_Declaration_X a_ast_num tn tm typ) =>
    match subtype_num tm with 
    | Some tn' => 
      match fetch_type_x tn' st with 
      | Some td => 
        match subtype_range_x td with 
        | Some (Range_X l u) => Some (Range_X l u)
        | None => None 
        end
      | None => None 
      end
    | None => None 
    end
  | _ => None
  end.

(** ** Run-Time Checks Optimization For Expression *)

Function optimize_expression_f (st: symboltable_x) (e: expression_x): option (expression_x * bound) :=
  match e with
  | E_Literal_X ast_num l in_cks ex_cks => 
    match optimize_literal_f l in_cks with 
    | Some (lBound, in_cks') => Some ((E_Literal_X ast_num l in_cks' ex_cks), lBound)
    | None => None 
    end
  | E_Name_X ast_num n => 
    match optimize_name_f st n with 
    | Some (n', nBound) => Some ((E_Name_X ast_num n'), nBound)
    | None => None 
    end
  | E_Binary_Operation_X ast_num op e1 e2 in_cks ex_cks => 
    match optimize_expression_f st e1, optimize_expression_f st e2 with 
    | Some (e1', e1Bound), Some (e2', e2Bound) => 
      match optimize_rtc_binop_f op e1Bound e2Bound in_cks with
      | Some (retBound, in_cks') => Some ((E_Binary_Operation_X ast_num op e1' e2' in_cks' ex_cks), retBound)
      | None => None 
      end
    | _, _ => None
    end
  | E_Unary_Operation_X ast_num op e in_cks ex_cks =>
    match optimize_expression_f st e with 
    | Some (e', eBound) => 
      match optimize_rtc_unop_f op eBound in_cks with
      | Some (retBound, in_cks') => Some ((E_Unary_Operation_X ast_num op e' in_cks' ex_cks), retBound)
      | None => None
      end
    | None => None 
    end
  end

with optimize_name_f (st: symboltable_x) (n: name_x): option (name_x * bound) :=
  match n with 
  | E_Identifier_X ast_num x ex_cks => 
    match fetch_exp_type_x ast_num st with 
    | Some t => 
      match bound_of_type_f st t with 
      | Some xBound => Some ((E_Identifier_X ast_num x ex_cks), xBound)
      | None => None
      end
    | None => None 
    end
  | E_Indexed_Component_X ast_num x e ex_cks =>
    match optimize_name_f st x, optimize_expression_f st e, fetch_exp_type_x (name_astnum_x x) st with
    | Some (x', xBound), Some (e', Interval u v), Some (Array_Type t) =>
      match extract_array_index_range_f st t with
      | Some (Range_X u' v') => 
        match optimize_range_check_f e' (Interval u v) (Interval u' v') with
        | Some e'' => 
          match bound_of_array_component_type_f st t with 
          | Some componentBound => Some ((E_Indexed_Component_X ast_num x' e'' ex_cks), componentBound)
          | None => None
          end
        | None => None 
        end
      | None => None 
      end
    | _, _, _ => None
    end
  | E_Selected_Component_X ast_num x f ex_cks => 
    match optimize_name_f st x, fetch_exp_type_x (name_astnum_x x) st with
    | Some (x', xBound), Some (Record_Type t) => 
      match bound_of_record_field_type_f st t f with 
      | Some fieldBound => Some ((E_Selected_Component_X ast_num x' f ex_cks), fieldBound)
      | None => None 
      end
    | _, _ => None 
    end
  end.


Function optimize_args_f (st: symboltable_x) (params: list parameter_specification_x) (args: list expression_x): option (list expression_x) :=
  match params, args with
  | nil, nil => Some nil
  | param :: lparam, arg :: larg =>
    match optimize_args_f st lparam larg with
    | Some args' => 
      match param.(parameter_mode_x) with
      | In =>
        match is_range_constrainted_type (param.(parameter_subtype_mark_x)) with
        | false =>
          match optimize_expression_f st arg with
          | Some (arg', argBound) => Some (arg' :: args')
          | None => None 
          end
        | true =>
          match extract_subtype_range_f st (param.(parameter_subtype_mark_x)), optimize_expression_f st arg with
          | Some (Range_X u v), Some (arg', Interval u' v') => 
            match optimize_range_check_f arg' (Interval u' v') (Interval u v) with 
            | Some arg'' => Some (arg'' :: args')
            | None => None 
            end
          | _, _ => None 
          end 
        end
      | Out => 
        match arg with
        | E_Name_X ast_num n =>
          match fetch_exp_type_x ast_num st with
          | Some t => 
            match is_range_constrainted_type t with
            | false =>
              match optimize_name_f st n with 
              | Some (n', nBound) => Some ((E_Name_X ast_num n') :: args')
              | None => None 
              end
            | true =>
              match bound_of_type_f st (param.(parameter_subtype_mark_x)), extract_subtype_range_f st t, optimize_name_f st n with
              | Some (Interval u v), Some (Range_X u' v'), Some (n', nBound) =>
                match optimize_range_check_on_copy_out_f (E_Name_X ast_num n') (Interval u v) (Interval u' v') with
                | Some arg' => Some (arg' :: args')
                | None => None 
                end
              | _, _, _ => None 
              end 
            end
          | None => None 
          end
        | _ => None
        end 
      | In_Out => 
        match arg with
        | E_Name_X ast_num n =>
          match fetch_exp_type_x ast_num st with 
          | Some t => 
            match is_range_constrainted_type t, is_range_constrainted_type (param.(parameter_subtype_mark_x)) with
            | true, true => 
              match extract_subtype_range_f st (param.(parameter_subtype_mark_x)), extract_subtype_range_f st t, optimize_expression_f st (E_Name_X ast_num n) with
              | Some (Range_X u v), Some (Range_X u' v'), Some ((E_Name_X ast_num n'), Interval v1 v2) =>
                match optimize_range_check_f (E_Name_X ast_num n') (Interval v1 v2) (Interval u v) with
                | Some arg' => 
                  match optimize_range_check_on_copy_out_f arg' (Interval u v) (Interval u' v') with
                  | Some arg'' => Some (arg'' :: args')
                  | None => None 
                  end
                | None => None 
                end
              | _, _, _ => None
              end
            | _, _ => 
              match optimize_name_f st n with
              | Some (n', nBound) => Some ((E_Name_X ast_num n') :: args')
              | None => None 
              end
            end
          | None => None 
          end
        | _ => None 
        end
      end
    | None => None 
    end
  | _, _ => None 
  end.

(** ** Run-Time Checks Optimization For Statement *)
(** given a statement, optimize its run-time check flags and return a new optimized statement *)
Function optimize_statement_f (st: symboltable_x) (stmt: statement_x): option statement_x :=
  match stmt with
  | S_Null_X => Some S_Null_X
  | S_Assignment_X ast_num x e =>
    match optimize_name_f st x, optimize_expression_f st e with
    | Some (x', xBound), Some (e', eBound) =>
      match fetch_exp_type_x (name_astnum_x x) st with
      | Some t => 
        match is_range_constrainted_type t with
        | false => Some (S_Assignment_X ast_num x' e')
        | true => 
          match extract_subtype_range_f st t with
          | Some (Range_X u v) => 
            match eBound with 
            | Interval u' v' => 
              match optimize_range_check_f e' (Interval u' v') (Interval u v) with
              | Some e'' => Some (S_Assignment_X ast_num x' e'')
              | None => None 
              end
            | _ => None 
            end
          | None => None 
          end 
        end
      | None => None
      end
    | _, _ => None
    end
  | S_If_X ast_num e c1 c2 =>
    match optimize_expression_f st e, optimize_statement_f st c1, optimize_statement_f st c2 with
    | Some (e', eBound), Some c1', Some c2' => Some (S_If_X ast_num e' c1' c2')
    | _, _, _ => None
    end
  | S_While_Loop_X ast_num e c =>
    match optimize_expression_f st e, optimize_statement_f st c with 
    | Some (e', eBound), Some c' => Some (S_While_Loop_X ast_num e' c')
    | _, _ => None
    end
  | S_Procedure_Call_X ast_num p_ast_num p args => 
    match fetch_proc_x p st with
    | Some (n, pb) => 
      match optimize_args_f st (procedure_parameter_profile_x pb) args with
      | Some args' => Some (S_Procedure_Call_X ast_num p_ast_num p args')
      | None => None
      end
    | None => None 
    end
  | S_Sequence_X ast_num c1 c2 => 
    match optimize_statement_f st c1, optimize_statement_f st c2 with
    | Some c1', Some c2' => Some (S_Sequence_X ast_num c1' c2')
    | _, _ => None
    end 
  end.
    

(** ** Run-Time Checks Optimization For Declaration *)

Function optimize_object_declaration_f (st: symboltable_x) (o: object_declaration_x) : option object_declaration_x :=
  match o with
  | mkobject_declaration_x ast_num x t None => Some (mkobject_declaration_x ast_num x t None) 
  | mkobject_declaration_x ast_num x t (Some e) => 
    match is_range_constrainted_type t with
    | false => 
      match optimize_expression_f st e with  
      | Some (e', eBound) => Some (mkobject_declaration_x ast_num x t (Some e'))
      | None => None
      end
    | true => 
      match extract_subtype_range_f st t, optimize_expression_f st e  with 
      | Some (Range_X u v), Some (e', Interval u' v') => 
        match optimize_range_check_f e' (Interval u' v') (Interval u v) with
        | Some e'' => Some (mkobject_declaration_x ast_num x t (Some e''))
        | None => None
        end 
      | _, _ => None
      end
    end  
  end.

Function optimize_declaration_f (st: symboltable_x) (d: declaration_x): option declaration_x :=
  match d with
  | D_Null_Declaration_X => Some D_Null_Declaration_X 
  | D_Type_Declaration_X ast_num t => Some (D_Type_Declaration_X ast_num t)
  | D_Object_Declaration_X ast_num o => 
    match optimize_object_declaration_f st o with 
    | Some o' => Some (D_Object_Declaration_X ast_num o')
    | None => None 
    end
  | D_Procedure_Body_X ast_num p => 
    match optimize_procedure_body_f st p with 
    | Some p' => Some (D_Procedure_Body_X ast_num p')
    | None => None 
    end
  | D_Seq_Declaration_X ast_num d1 d2 => 
    match optimize_declaration_f st d1, optimize_declaration_f st d2 with 
    | Some d1', Some d2' => Some (D_Seq_Declaration_X ast_num d1' d2')
    | _, _ => None
    end
  end

with optimize_procedure_body_f (st: symboltable_x) (pb: procedure_body_x): option procedure_body_x :=
  match pb with
  | mkprocedure_body_x ast_num p params decls stmt => 
    match optimize_declaration_f st decls, optimize_statement_f st stmt with 
    | Some decls', Some stmt' => Some (mkprocedure_body_x ast_num p params decls' stmt')
    | _, _ => None 
    end
  end.

