(** 
_AUTHOR_

<<
Zhi Zhang
Department of Computer and Information Sciences
Kansas State University
zhangzhi@ksu.edu
>>
*)

Require Export environment.
Require Export rt.
Require Export ast_rt.
Require Export eval_rt.
Require Export rt_opt_ZArith.


Inductive bound_of_type: symTabRT -> type -> bound -> Prop :=
  | Bound_Of_Boolean: forall st,
      bound_of_type st Boolean Boolval
  | Bound_Of_Integer: forall st,
      bound_of_type st Integer int32_bound
  | Bound_Of_Subtype: forall st t l u,
      extract_subtype_range_rt st t (RangeRT l u) ->
      bound_of_type st t (Interval l u)
  | Bound_Of_Composite_Type: forall t t1 st,
      t = Array_Type t1 \/ t = Record_Type t1 ->
      bound_of_type st t Aggregate.

(** t: type id of the array type; (l, u) is the domain of the array component type *)
Inductive bound_of_array_component_type : symTabRT -> typenum -> bound -> Prop :=
  | Array_Component_Value : forall t st n tn indexSubtypeMark componentType boundValue,
      fetch_type_rt t st = Some (ArrayTypeDeclRT n tn indexSubtypeMark componentType) ->
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
Inductive bound_of_record_field_type : symTabRT -> typenum -> idnum -> bound -> Prop :=
  | Record_Field_Value : forall t st n tn fields f ft boundValue,
      fetch_type_rt t st = Some (RecordTypeDeclRT n tn fields) ->
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

(** check whether a bound is sub-bound of another one *)
Inductive sub_bound: bound -> bound -> bool -> Prop :=
  | SB_True: forall u u' v' v,
      in_bound u (Interval u' v') true ->
      in_bound v (Interval u' v') true ->
      sub_bound (Interval u v) (Interval u' v') true
  | SB_False: forall u u' v' v,
      in_bound u (Interval u' v') false \/ in_bound v (Interval u' v') false ->
      sub_bound (Interval u v) (Interval u' v') false.

(** * Run-Time Checks Optimization Rule *)

(** ** optimize_overflow_check *)

(** if the bound (Interval u v) is within the bound of the integer type,
    then optimize away the overflow check from the check set "cks", return 
    the optimized run-time check flags, and return the resulting bound 
    (Interval u v) if it's within integer bound, otherwise, return int32_bound;
*)
Inductive optimize_overflow_check: bound -> check_flags -> (bound * check_flags) -> Prop :=
  | OOC_True: forall u v cks' cks,
      sub_bound (Interval u v) int32_bound true ->
      cks' = remove_check_flag OverflowCheck cks ->
      optimize_overflow_check (Interval u v) cks ((Interval u v), cks')
  | OOC_False: forall u v cks,
      sub_bound (Interval u v) int32_bound false ->
      optimize_overflow_check (Interval u v) cks (Interval (Z.max min_signed u) (Z.min max_signed v), cks).

(** ** optimize_range_check *)

(** given an expression and its possible value bound, if it's used in a context where
    a range constraint is enforced, then check whether the value bound of the expression 
    is within the range constraint required by the context, if it's so, the range check 
    can be optimized away; 
*)
Inductive optimize_range_check: expRT -> bound -> bound -> expRT -> Prop :=
  | ORC_True: forall u v u' v' cks e e',
      sub_bound (Interval u v) (Interval u' v') true ->
      cks = remove_check_flag RangeCheck (exp_exterior_checks e) ->
      e' = update_exterior_checks_exp e cks ->
      optimize_range_check e (Interval u v) (Interval u' v') e'
  | ORC_False: forall u v u' v' e,
      sub_bound (Interval u v) (Interval u' v') false ->
      optimize_range_check e (Interval u v) (Interval u' v') e.

(** ** optimize_range_check_on_copy_out *)
Inductive optimize_range_check_on_copy_out: expRT -> bound -> bound -> expRT -> Prop :=
  | ORCOCO_True: forall u v u' v' cks e e',
      sub_bound (Interval u v) (Interval u' v') true ->
      cks = remove_check_flag RangeCheckOnReturn (exp_exterior_checks e) ->
      e' = update_exterior_checks_exp e cks ->
      optimize_range_check_on_copy_out e (Interval u v) (Interval u' v') e'
  | ORCOCO_False: forall u v u' v' e,
      sub_bound (Interval u v) (Interval u' v') false ->
      optimize_range_check_on_copy_out e (Interval u v) (Interval u' v') e.


(** ** optimize_rtc_binop *)

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
  | O_RTC_Multiply: forall u v u' v' cks retBound cks',
      optimize_overflow_check (Interval (multiply_min_f u v u' v') (multiply_max_f u v u' v')) cks (retBound, cks') ->
      optimize_rtc_binop Multiply (Interval u v) (Interval u' v') cks (retBound, cks')
  | O_RTC_Divide_OverflowRTC: forall u' v' u v cks div_min div_max retBound cks',
      in_bound 0 (Interval u' v') true ->
      (div_min, div_max) = divide_min_max_f u v u' v' ->
      optimize_overflow_check (Interval div_min div_max) cks (retBound, cks') ->
      optimize_rtc_binop Divide (Interval u v) (Interval u' v') cks (retBound, cks')
  | O_RTC_Divide_DivisionRTC: forall u' v' u v cks cks' div_min div_max retBound cks'',
      in_bound 0 (Interval u' v') false ->
      cks' = remove_check_flag DivCheck cks ->
      (div_min, div_max) = divide_min_max_f u v u' v' ->
      optimize_overflow_check (Interval div_min div_max) cks' (retBound, cks'') ->
      optimize_rtc_binop Divide (Interval u v) (Interval u' v') cks (retBound, cks'')
(* (=== old version ===)
  | O_RTC_Divide: forall u' v' u v cks div_min div_max,  (* optimize overflow check *)
      in_bound 0 (Interval u' v') true ->
      in_bound min_signed (Interval u v) true -> in_bound (-1) (Interval u' v') true ->
      (div_min, div_max) = divide_min_max_f u v u' v' ->
      optimize_rtc_binop Divide (Interval u v) (Interval u' v') cks (Interval (max_f div_min min_signed) (min_f div_max max_signed), cks)
  | O_RTC_Divide_DivisionRTC: forall u' v' u v cks' cks div_min div_max,  (* optimize division-by-zero check *)
      in_bound 0 (Interval u' v') false ->
      in_bound min_signed (Interval u v) true -> in_bound (-1) (Interval u' v') true ->
      cks' = remove_check_flag DivCheck cks ->
      (div_min, div_max) = divide_min_max_f u v u' v' ->
      optimize_rtc_binop Divide (Interval u v) (Interval u' v') cks (Interval (max_f div_min min_signed) (min_f div_max max_signed), cks')
  | O_RTC_Divide_OverflowRTC: forall u' v' u v cks cks' div_min div_max,  (* optimize overflow check *)
      in_bound 0 (Interval u' v') true ->
      in_bound min_signed (Interval u v) false \/ in_bound (-1) (Interval u' v') false ->
      (div_min, div_max) = divide_min_max_f u v u' v' ->
      cks' = remove_check_flag OverflowCheck cks ->
      optimize_rtc_binop Divide (Interval u v) (Interval u' v') cks (Interval (max_f div_min min_signed) (min_f div_max max_signed), cks')
  | O_RTC_Divide_DivisionOverflowRTC: forall u' v' u v cks cks' div_min div_max,  (* optimize overflow check *)
      in_bound 0 (Interval u' v') false ->
      in_bound min_signed (Interval u v) false \/ in_bound (-1) (Interval u' v') false ->
      (div_min, div_max) = divide_min_max_f u v u' v' ->
      cks' = remove_check_flag OverflowCheck (remove_check_flag DivCheck cks) ->
      optimize_rtc_binop Divide (Interval u v) (Interval u' v') cks (Interval (max_f div_min min_signed) (min_f div_max max_signed), cks')
*)
  | O_RTC_Modulus: forall u' v' u v cks mod_min mod_max,  (* optimize overflow check *)
      in_bound 0 (Interval u' v') true ->
      (mod_min, mod_max) = modulus_min_max_f u v u' v' ->
      optimize_rtc_binop Modulus (Interval u v) (Interval u' v') cks (Interval mod_min mod_max, cks)
  | O_RTC_Modulus_DivisionRTC: forall u' v' u v cks' cks mod_min mod_max,  (* optimize division-by-zero check *)
      in_bound 0 (Interval u' v') false ->
      cks' = remove_check_flag DivCheck cks ->
      (mod_min, mod_max) = modulus_min_max_f u v u' v' ->
      optimize_rtc_binop Modulus (Interval u v) (Interval u' v') cks (Interval mod_min mod_max, cks')
  | O_RTC_Logic_Binop: forall op cks x y,
      op <> Plus /\ op <> Minus /\ op <> Multiply /\ op <> Divide /\ op <> Modulus ->
      optimize_rtc_binop op x y cks (Boolval, cks).


(** ** optimize_rtc_unop *)

(** optimization for unary operation *)
Inductive optimize_rtc_unop: unary_operator -> bound -> check_flags -> (bound * check_flags) -> Prop :=
  | O_RTC_Unary_Minus: forall v x u y cks retBound cks',
      Math.unary_minus (Int v) = Some (Int x) ->
      Math.unary_minus (Int u) = Some (Int y) ->
      optimize_overflow_check (Interval x y) cks (retBound, cks') ->
      optimize_rtc_unop Unary_Minus (Interval u v) cks (retBound, cks')
  | O_RTC_Unop_Others: forall cks,
      (* op <> Unary_Minus -> *)
      optimize_rtc_unop Not Boolval cks (Boolval, cks).

(** * Run-Time Checks Optimization *)

(** ** Checks Optimization for Literal *)

(** for a literal with run-time check flags, if it's an int literal and its value falls 
    in the integer range, then optimize away the overflow check
*)
Inductive optLiteral: literal -> check_flags -> (bound * check_flags) -> Prop :=
  | O_Literal_Bool: forall cks v,
      optLiteral (Boolean_Literal v) cks (Boolval, cks)
  | O_Literal_Int: forall v cks retBound cks',
      optimize_overflow_check (Interval v v) cks (retBound, cks') ->
      optLiteral (Integer_Literal v) cks (retBound, cks').


(** ** Checks Optimization for Expression *)

(** given an expression, optimize its run time checks, and return the optimized expression
    and its possible value bound, which will be used later to optimize other checks;
*)

Inductive optExp: symTabRT -> expRT -> (expRT * bound) -> Prop :=
  | O_Literal: forall l in_cks lBound in_cks' st n ex_cks,
      optLiteral l in_cks (lBound, in_cks') -> 
      optExp st (LiteralRT n l in_cks ex_cks) ((LiteralRT n l in_cks' ex_cks), lBound)
  | O_Name: forall st n n' nBound n0,
      optName st n (n', nBound) ->
      optExp st (NameRT n0 n) ((NameRT n0 n'), nBound)
  | O_BinOp: forall st e1 e1' e1Bound e2 e2' e2Bound in_cks retBound in_cks' n op ex_cks,
      optExp st e1 (e1', e1Bound) ->
      optExp st e2 (e2', e2Bound) ->
      optimize_rtc_binop op e1Bound e2Bound in_cks (retBound, in_cks') ->
      optExp st (BinOpRT n op e1 e2 in_cks ex_cks) 
                ((BinOpRT n op e1' e2' in_cks' ex_cks), retBound)
  | O_UnOp: forall st e e' eBound op in_cks retBound in_cks' n ex_cks,
      optExp st e (e', eBound) ->
      optimize_rtc_unop op eBound in_cks (retBound, in_cks') ->
      optExp st (UnOpRT n op e in_cks ex_cks) 
                ((UnOpRT n op e' in_cks' ex_cks), retBound)
      
(** ** Checks Optimization for Name *)

with optName: symTabRT -> nameRT -> (nameRT * bound) -> Prop :=
  | O_Identifier: forall n st t xBound x ex_cks,
      fetch_exp_type_rt n st = Some t ->
      bound_of_type st t xBound ->
      optName st (IdentifierRT n x ex_cks) ((IdentifierRT n x ex_cks), xBound)
  | O_IndexedComponent: forall st x x' xBound e e' u v t u' v' e'' componentBound n ex_cks,
      optName st x (x', xBound) ->
      optExp st e (e', Interval u v) ->
      fetch_exp_type_rt (name_astnum_rt x) st = Some (Array_Type t) ->
      extract_array_index_range_rt st t (RangeRT u' v') -> (* range value of array index type *)
      optimize_range_check e' (Interval u v) (Interval u' v') e'' ->
      bound_of_array_component_type st t componentBound ->
      optName st (IndexedComponentRT n x e ex_cks) 
                         ((IndexedComponentRT n x' e'' ex_cks), componentBound)
  | O_SelectedComponent: forall st x x' xBound t f fieldBound n ex_cks,
      optName st x (x', xBound) ->
      fetch_exp_type_rt (name_astnum_rt x) st = Some (Record_Type t) ->
      bound_of_record_field_type st t f fieldBound ->
      optName st (SelectedComponentRT n x f ex_cks)
                         ((SelectedComponentRT n x' f ex_cks), fieldBound).


(** ** Checks Optimization for Arguments *)

(** optimize run-time checks for arguments during procedure call;
    for a procedure call, given a list of arguments and its corresponding formal parameters,
    optimize its run-time checks (that's range check);
*)

Inductive optArgs: symTabRT -> list paramSpecRT -> list expRT -> list expRT -> Prop :=
  | O_Args_Nil: forall st,
      optArgs st nil nil nil
  | O_Args_Mode_In: forall param st arg arg' argBound params args args',
      param.(parameter_mode_rt) = In -> 
      is_range_constrainted_type (param.(parameter_subtype_mark_rt)) = false ->
      optExp st arg (arg', argBound) ->
      optArgs st params args args' ->
      optArgs st (param :: params) (arg :: args) (arg' :: args')
  | O_Args_Mode_In_RangeCheck: forall param st u v arg arg' u' v' arg'' params args args',
      param.(parameter_mode_rt) = In -> 
      extract_subtype_range_rt st (param.(parameter_subtype_mark_rt)) (RangeRT u v) ->
      optExp st arg (arg', Interval u' v') ->
      optimize_range_check arg' (Interval u' v') (Interval u v) arg'' ->
      optArgs st params args args' ->
      optArgs st (param :: params) (arg :: args) (arg'' :: args')
  | O_Args_Mode_Out: forall param n0 st t n n' nBound params args args',
      param.(parameter_mode_rt) = Out ->
      fetch_exp_type_rt n0 st = Some t ->
      is_range_constrainted_type t = false ->
      optName st n (n', nBound) ->
      optArgs st params args args' ->
      optArgs st (param :: params) ((NameRT n0 n) :: args) 
                                           ((NameRT n0 n') :: args')
  | O_Args_Mode_Out_RangeCheck: forall param st u v n0 t u' v' n n' nBound arg' params args args',
      param.(parameter_mode_rt) = Out ->
      bound_of_type st (param.(parameter_subtype_mark_rt)) (Interval u v) ->
      fetch_exp_type_rt n0 st = Some t ->
      extract_subtype_range_rt st t (RangeRT u' v') ->
      optName st n (n', nBound) ->
      optimize_range_check_on_copy_out (NameRT n0 n') (Interval u v) (Interval u' v') arg' ->
      optArgs st params args args' ->
      optArgs st (param :: params) ((NameRT n0 n) :: args) 
                                           (arg' :: args')
  | O_Args_Mode_InOut: forall param n0 st t n n' nBound params args args', 
      param.(parameter_mode_rt) = In_Out ->
      fetch_exp_type_rt n0 st = Some t ->
      is_range_constrainted_type t = false \/ is_range_constrainted_type (param.(parameter_subtype_mark_rt)) = false ->
      optName st n (n', nBound) ->
      optArgs st params args args' ->
      optArgs st (param :: params) ((NameRT n0 n) :: args) 
                                           ((NameRT n0 n') :: args')
  | O_Args_Mode_InOut_In_RangeCheck: forall param u v n0 st t u' v' n n' v1 v2 arg arg' params args args', 
      param.(parameter_mode_rt) = In_Out ->
      extract_subtype_range_rt st (param.(parameter_subtype_mark_rt)) (RangeRT u v) ->
      fetch_exp_type_rt n0 st = Some t ->
      extract_subtype_range_rt st t (RangeRT u' v') ->
      optExp st (NameRT n0 n) ((NameRT n0 n'), Interval v1 v2) ->
      optimize_range_check (NameRT n0 n') (Interval v1 v2) (Interval u v) arg ->
      optimize_range_check_on_copy_out arg (Interval u v) (Interval u' v') arg' ->
      optArgs st params args args' ->
      optArgs st (param :: params) ((NameRT n0 n) :: args) 
                                           (arg' :: args').



(** ** Checks Optimization for Statement *)

(** given a statement, optimize its run-time check flags and return a new optimized statement *)
Inductive optStmt: symTabRT -> stmtRT -> stmtRT -> Prop :=
  | O_Null: forall st, 
      optStmt st NullRT NullRT
  | O_Assign: forall x st t x' xBound e e' eBound n,
      fetch_exp_type_rt (name_astnum_rt x) st = Some t ->
      is_range_constrainted_type t = false -> 
      optName st x (x', xBound) ->
      optExp st e (e', eBound) ->
      optStmt st (AssignRT n x e) (AssignRT n x' e')
  | O_Assign_RangeCheck: forall x st t u v x' xBound e e' u' v' e'' n,
      fetch_exp_type_rt (name_astnum_rt x) st = Some t ->
      extract_subtype_range_rt st t (RangeRT u v) ->
      optName st x (x', xBound) ->
      optExp st e (e', Interval u' v') ->
      optimize_range_check e' (Interval u' v') (Interval u v) e'' ->
      optStmt st (AssignRT n x e) (AssignRT n x' e'')
  | O_If: forall st e e' eBound c1 c1' c2 c2' n,
      optExp st e (e', eBound) ->
      optStmt st c1 c1' ->
      optStmt st c2 c2' ->
      optStmt st (IfRT n e c1 c2) (IfRT n e' c1' c2')
  | O_While: forall st e e' eBound c c' n,
      optExp st e (e', eBound) ->
      optStmt st c c' ->
      optStmt st (WhileRT n e c) (WhileRT n e' c')
  | O_Call: forall p st n0 pb args args' n pn,
      fetch_proc_rt p st = Some (n0, pb) ->
      optArgs st (procedure_parameter_profile_rt pb) args args' ->
      optStmt st (CallRT n pn p args) (CallRT n pn p args')
  | O_Seq: forall st c1 c1' c2 c2' n,
      optStmt st c1 c1' ->
      optStmt st c2 c2' ->
      optStmt st (SeqRT n c1 c2) (SeqRT n c1' c2').

Inductive optObjDecl: symTabRT -> objDeclRT -> objDeclRT -> Prop :=
  | O_ObjDecl_NoneInit: forall st n x t,
      optObjDecl st (mkobjDeclRT n x t None) 
                                       (mkobjDeclRT n x t None)
  | O_ObjDecl_NoRangeCheck: forall t st e e' eBound n x,
      is_range_constrainted_type t = false ->
      optExp st e (e', eBound) -> 
      optObjDecl st (mkobjDeclRT n x t (Some e)) 
                                       (mkobjDeclRT n x t (Some e'))
  | O_ObjDecl_RangeCheck: forall st t u v e e' u' v' e'' n x,
      extract_subtype_range_rt st t (RangeRT u v) ->
      optExp st e (e', Interval u' v') ->
      optimize_range_check e' (Interval u' v') (Interval u v) e'' ->
      optObjDecl st (mkobjDeclRT n x t (Some e)) 
                                       (mkobjDeclRT n x t (Some e'')).


(** ** Checks Optimization for Declaration *)

Inductive optDecl: symTabRT -> declRT -> declRT -> Prop :=
  | O_NullDecl: forall st,
      optDecl st NullDeclRT NullDeclRT
  | O_TypeDecl: forall st n t,
      optDecl st (TypeDeclRT n t) (TypeDeclRT n t)
  | O_ObjDecl: forall st o o' n,
      optObjDecl st o o' ->
      optDecl st (ObjDeclRT n o) (ObjDeclRT n o')
  | O_ProcBody: forall st p p' n,
      optProcBodyDecl st p p' ->
      optDecl st (ProcBodyDeclRT n p) (ProcBodyDeclRT n p')
  | O_SeqDecl: forall st d1 d1' d2 d2' n,
      optDecl st d1 d1' ->
      optDecl st d2 d2' ->
      optDecl st (SeqDeclRT n d1 d2) (SeqDeclRT n d1' d2')

(** ** Checks Optimization for Procedure *)

with optProcBodyDecl: symTabRT -> procBodyDeclRT -> procBodyDeclRT -> Prop :=
  | O_ProcBodyDecl: forall st decls decls' stmt stmt' n p params,
      optDecl st decls decls' ->
      optStmt st stmt stmt' ->
      optProcBodyDecl st (mkprocBodyDeclRT n p params decls stmt)
                         (mkprocBodyDeclRT n p params decls' stmt').


(** ** Checks Optimization for Program *)

Inductive optProgram: symTabRT -> programRT -> programRT -> Prop :=
  | OptProgram: forall st p declsRT',
      optDecl st p.(declsRT) declsRT' ->
      optProgram st p (mkprogramRT declsRT' p.(mainRT)).

Import Symbol_Table_Module_RT.

Inductive optSymTab: symTabRT -> symTabRT -> Prop :=
  | OptSymTab: forall st st',
      (forall p n pb, 
        fetch_proc_rt p st = Some (n, pb) -> 
          exists pb', fetch_proc_rt p st' = Some (n, pb') /\ optProcBodyDecl st pb pb') ->
      (forall p n pb', 
        fetch_proc_rt p st' = Some (n, pb') -> 
          exists pb, fetch_proc_rt p st = Some (n, pb) /\ optProcBodyDecl st pb pb') ->  
      (st.(vars) = st'.(vars) /\ st.(types) = st'.(types) /\ st.(exps) = st'.(exps) /\
       st.(sloc) = st'.(sloc) /\ st.(names) = st'.(names) ) ->
      optSymTab st st'.

