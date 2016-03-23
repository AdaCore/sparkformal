(** 
_AUTHOR_

<<
Zhi Zhang
Department of Computer and Information Sciences
Kansas State University
zhangzhi@ksu.edu
>>
*)

Require Export checks_optimization.

(**********************************************)
(** * executable check optimization functions *)
(**********************************************)

Function extract_subtype_range_f (st: symTabRT) (t: type): option rangeRT :=
  match subtype_num t with
  | Some tn => 
    match fetch_type_rt tn st with
    | Some td =>
        match subtype_range_rt td with
        | Some (RangeRT l u) => Some (RangeRT l u) 
        | None => None 
        end 
    | None => None 
    end
  | None => None
  end.

Function bound_of_type_f (st: symTabRT) (t: type): option bound :=
  match t with
  | Boolean => Some Boolval
  | Integer => Some int32_bound
  | Array_Type t => Some Aggregate
  | Record_Type t => Some Aggregate 
  | _ => 
    match extract_subtype_range_f st t with 
    | Some (RangeRT l u) => Some (Interval l u)
    | None => None 
    end
  end.

Function bound_of_array_component_type_f (st: symTabRT) (t: typenum): option bound :=
  match fetch_type_rt t st with
  | Some (ArrayTypeDeclRT n tn indexSubtypeMark componentType) =>
    match bound_of_type_f st componentType with
    | Some boundValue => Some boundValue
    | None => None 
    end
  | _ => None
  end.

Function bound_of_record_field_type_f (st: symTabRT) (t: typenum) (f: idnum): option bound :=
  match fetch_type_rt t st with
  | Some (RecordTypeDeclRT n tn fields) => 
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
  | Some true => Some (bd, remove_check_flag OverflowCheck cks)
  | Some false => 
      match bd with
      | Interval u v => Some (Interval (Z.max min_signed u) (Z.min max_signed v), cks)   (* +++ new *)
      | _ => None
      end
  | None => None 
  end.

Function optimize_range_check_f (e: expRT) (bd1: bound) (bd2: bound): option expRT :=
  match sub_bound_f bd1 bd2 with
  | Some true => Some (update_exterior_checks_exp e (remove_check_flag RangeCheck (exp_exterior_checks e)))
  | Some false => Some e
  | None => None 
  end.

Function optimize_range_check_on_copy_out_f (e: expRT) (bd1: bound) (bd2: bound): option expRT :=
  match sub_bound_f bd1 bd2 with
  | Some true => Some (update_exterior_checks_exp e (remove_check_flag RangeCheckOnReturn (exp_exterior_checks e)))
  | Some false => Some e
  | None => None
  end.

Function optimize_rtc_binop_f (op: binary_operator) (bd1: bound) (bd2: bound) (cks: check_flags): option (bound * check_flags) :=
  match op with
  | Plus => 
    match bd1, bd2 with
    | (Interval u v), (Interval u' v') => 
      match Math.add (Int u) (Int u'), Math.add (Int v) (Int v') with 
      | Some (Int x), Some (Int y) => optimize_overflow_check_f (Interval x y) cks (* ++ *)
      | _, _ => None
      end
    | _, _ => None
    end
  | Minus => 
    match bd1, bd2 with
    | (Interval u v), (Interval u' v') => 
      match Math.sub (Int u) (Int v'), Math.sub (Int v) (Int u') with 
      | Some (Int x), Some (Int y) => optimize_overflow_check_f (Interval x y) cks (* ++ *)
      | _, _ => None
      end
    | _, _ => None
    end
  | Multiply => (* +++ new *)
    match bd1, bd2 with
    | (Interval u v), (Interval u' v') =>
        optimize_overflow_check_f (Interval (multiply_min_f u v u' v') (multiply_max_f u v u' v')) cks
    | _, _ => None
    end
  | Divide => (* +++ new *)
    match bd1, bd2 with
    | (Interval u v), (Interval u' v') =>
      let (div_min, div_max) := divide_min_max_f u v u' v' in
      match in_bound_f 0 (Interval u' v') with
      | Some true => 
          optimize_overflow_check_f (Interval div_min div_max) cks
      | Some false => 
          optimize_overflow_check_f (Interval div_min div_max) (remove_check_flag DivCheck cks)
      | None => None
      end
    | _, _ => None
    end
  | Modulus => (* +++ new *)
    match bd1, bd2 with
    | (Interval u v), (Interval u' v') =>
      let (mod_min, mod_max) := modulus_min_max_f u v u' v' in
      match in_bound_f 0 (Interval u' v') with
      | Some true => Some (Interval mod_min mod_max, cks)
      | Some false => Some (Interval mod_min mod_max, remove_check_flag DivCheck cks)
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
      | Some (Int x), Some (Int y) => optimize_overflow_check_f (Interval x y) cks (* ++ *)
      | _, _ => None
      end
    | _ => None
    end
  | Not => 
    match bd with
    | Boolval => Some (Boolval, cks) 
    | _ => None
    end
  end.

Function optLiteralImpl (l: literal) (cks: check_flags): option (bound * check_flags) :=
  match l with
  | Boolean_Literal v => Some (Boolval, cks)
  | Integer_Literal v => optimize_overflow_check_f (Interval v v) cks (* ++ *)
  end.

Function extract_array_index_range_f (st: symTabRT) (t: typenum): option rangeRT :=
  match fetch_type_rt t st with
  | Some (ArrayTypeDeclRT a_n tn tm typ) =>
    match subtype_num tm with 
    | Some tn' => 
      match fetch_type_rt tn' st with 
      | Some td => 
        match subtype_range_rt td with 
        | Some (RangeRT l u) => Some (RangeRT l u)
        | None => None 
        end
      | None => None 
      end
    | None => None 
    end
  | _ => None
  end.

(** ** Run-Time Checks Optimization For Expression *)

Function optExpImpl (st: symTabRT) (e: expRT): option (expRT * bound) :=
  match e with
  | LiteralRT n l in_cks ex_cks => 
    match optLiteralImpl l in_cks with 
    | Some (lBound, in_cks') => Some ((LiteralRT n l in_cks' ex_cks), lBound)
    | None => None 
    end
  | NameRT n0 n => 
    match optNameImpl st n with 
    | Some (n', nBound) => Some ((NameRT n0 n'), nBound)
    | None => None 
    end
  | BinOpRT n op e1 e2 in_cks ex_cks => 
    match optExpImpl st e1, optExpImpl st e2 with 
    | Some (e1', e1Bound), Some (e2', e2Bound) => 
      match optimize_rtc_binop_f op e1Bound e2Bound in_cks with
      | Some (retBound, in_cks') => Some ((BinOpRT n op e1' e2' in_cks' ex_cks), retBound)
      | None => None 
      end
    | _, _ => None
    end
  | UnOpRT n op e in_cks ex_cks =>
    match optExpImpl st e with 
    | Some (e', eBound) => 
      match optimize_rtc_unop_f op eBound in_cks with
      | Some (retBound, in_cks') => Some ((UnOpRT n op e' in_cks' ex_cks), retBound)
      | None => None
      end
    | None => None 
    end
  end

with optNameImpl (st: symTabRT) (n: nameRT): option (nameRT * bound) :=
  match n with 
  | IdentifierRT n x ex_cks => 
    match fetch_exp_type_rt n st with 
    | Some t => 
      match bound_of_type_f st t with 
      | Some xBound => Some ((IdentifierRT n x ex_cks), xBound)
      | None => None
      end
    | None => None 
    end
  | IndexedComponentRT n x e ex_cks =>
    match optNameImpl st x, optExpImpl st e, fetch_exp_type_rt (name_astnum_rt x) st with
    | Some (x', xBound), Some (e', Interval u v), Some (Array_Type t) =>
      match extract_array_index_range_f st t with
      | Some (RangeRT u' v') => 
        match optimize_range_check_f e' (Interval u v) (Interval u' v') with
        | Some e'' => 
          match bound_of_array_component_type_f st t with 
          | Some componentBound => Some ((IndexedComponentRT n x' e'' ex_cks), componentBound)
          | None => None
          end
        | None => None 
        end
      | None => None 
      end
    | _, _, _ => None
    end
  | SelectedComponentRT n x f ex_cks => 
    match optNameImpl st x, fetch_exp_type_rt (name_astnum_rt x) st with
    | Some (x', xBound), Some (Record_Type t) => 
      match bound_of_record_field_type_f st t f with 
      | Some fieldBound => Some ((SelectedComponentRT n x' f ex_cks), fieldBound)
      | None => None 
      end
    | _, _ => None 
    end
  end.


Function optArgsImpl (st: symTabRT) (params: list paramSpecRT) (args: list expRT): option (list expRT) :=
  match params, args with
  | nil, nil => Some nil
  | param :: lparam, arg :: larg =>
    match optArgsImpl st lparam larg with
    | Some args' => 
      match param.(parameter_mode_rt) with
      | In =>
        match is_range_constrainted_type (param.(parameter_subtype_mark_rt)) with
        | false =>
          match optExpImpl st arg with
          | Some (arg', argBound) => Some (arg' :: args')
          | None => None 
          end
        | true =>
          match extract_subtype_range_f st (param.(parameter_subtype_mark_rt)), optExpImpl st arg with
          | Some (RangeRT u v), Some (arg', Interval u' v') => 
            match optimize_range_check_f arg' (Interval u' v') (Interval u v) with 
            | Some arg'' => Some (arg'' :: args')
            | None => None 
            end
          | _, _ => None 
          end 
        end
      | Out => 
        match arg with
        | NameRT n0 n =>
          match fetch_exp_type_rt n0 st with
          | Some t => 
            match is_range_constrainted_type t with
            | false =>
              match optNameImpl st n with 
              | Some (n', nBound) => Some ((NameRT n0 n') :: args')
              | None => None 
              end
            | true =>
              match bound_of_type_f st (param.(parameter_subtype_mark_rt)), extract_subtype_range_f st t, optNameImpl st n with
              | Some (Interval u v), Some (RangeRT u' v'), Some (n', nBound) =>
                match optimize_range_check_on_copy_out_f (NameRT n0 n') (Interval u v) (Interval u' v') with
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
        | NameRT n0 n =>
          match fetch_exp_type_rt n0 st with 
          | Some t => 
            match is_range_constrainted_type t, is_range_constrainted_type (param.(parameter_subtype_mark_rt)) with
            | true, true => 
              match extract_subtype_range_f st (param.(parameter_subtype_mark_rt)), extract_subtype_range_f st t, optExpImpl st (NameRT n0 n) with
              | Some (RangeRT u v), Some (RangeRT u' v'), Some ((NameRT n0 n'), Interval v1 v2) =>
                match optimize_range_check_f (NameRT n0 n') (Interval v1 v2) (Interval u v) with
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
              match optNameImpl st n with
              | Some (n', nBound) => Some ((NameRT n0 n') :: args')
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
Function optStmtImpl (st: symTabRT) (stmt: stmtRT): option stmtRT :=
  match stmt with
  | NullRT => Some NullRT
  | AssignRT n x e =>
    match optNameImpl st x, optExpImpl st e with
    | Some (x', xBound), Some (e', eBound) =>
      match fetch_exp_type_rt (name_astnum_rt x) st with
      | Some t => 
        match is_range_constrainted_type t with
        | false => Some (AssignRT n x' e')
        | true => 
          match extract_subtype_range_f st t with
          | Some (RangeRT u v) => 
            match eBound with 
            | Interval u' v' => 
              match optimize_range_check_f e' (Interval u' v') (Interval u v) with
              | Some e'' => Some (AssignRT n x' e'')
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
  | IfRT n e c1 c2 =>
    match optExpImpl st e, optStmtImpl st c1, optStmtImpl st c2 with
    | Some (e', eBound), Some c1', Some c2' => Some (IfRT n e' c1' c2')
    | _, _, _ => None
    end
  | WhileRT n e c =>
    match optExpImpl st e, optStmtImpl st c with 
    | Some (e', eBound), Some c' => Some (WhileRT n e' c')
    | _, _ => None
    end
  | CallRT n pn p args => 
    match fetch_proc_rt p st with
    | Some (n0, pb) => 
      match optArgsImpl st (procedure_parameter_profile_rt pb) args with
      | Some args' => Some (CallRT n pn p args')
      | None => None
      end
    | None => None 
    end
  | SeqRT n c1 c2 => 
    match optStmtImpl st c1, optStmtImpl st c2 with
    | Some c1', Some c2' => Some (SeqRT n c1' c2')
    | _, _ => None
    end 
  end.
    

(** ** Run-Time Checks Optimization For Declaration *)

Function optObjDeclImpl (st: symTabRT) (o: objDeclRT) : option objDeclRT :=
  match o with
  | mkobjDeclRT n x t None => Some (mkobjDeclRT n x t None) 
  | mkobjDeclRT n x t (Some e) => 
    match is_range_constrainted_type t with
    | false => 
      match optExpImpl st e with  
      | Some (e', eBound) => Some (mkobjDeclRT n x t (Some e'))
      | None => None
      end
    | true => 
      match extract_subtype_range_f st t, optExpImpl st e  with 
      | Some (RangeRT u v), Some (e', Interval u' v') => 
        match optimize_range_check_f e' (Interval u' v') (Interval u v) with
        | Some e'' => Some (mkobjDeclRT n x t (Some e''))
        | None => None
        end 
      | _, _ => None
      end
    end  
  end.

Function optDeclImpl (st: symTabRT) (d: declRT): option declRT :=
  match d with
  | NullDeclRT => Some NullDeclRT 
  | TypeDeclRT n t => Some (TypeDeclRT n t)
  | ObjDeclRT n o => 
    match optObjDeclImpl st o with 
    | Some o' => Some (ObjDeclRT n o')
    | None => None 
    end
  | ProcBodyDeclRT n p => 
    match optProcBodyDeclImpl st p with 
    | Some p' => Some (ProcBodyDeclRT n p')
    | None => None 
    end
  | SeqDeclRT n d1 d2 => 
    match optDeclImpl st d1, optDeclImpl st d2 with 
    | Some d1', Some d2' => Some (SeqDeclRT n d1' d2')
    | _, _ => None
    end
  end

with optProcBodyDeclImpl (st: symTabRT) (pb: procBodyDeclRT): option procBodyDeclRT :=
  match pb with
  | mkprocBodyDeclRT n p params decls stmt => 
    match optDeclImpl st decls, optStmtImpl st stmt with 
    | Some decls', Some stmt' => Some (mkprocBodyDeclRT n p params decls' stmt')
    | _, _ => None 
    end
  end.



