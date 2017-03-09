(** 
_AUTHOR_

<<
Zhi Zhang
Department of Computer and Information Sciences
Kansas State University
zhangzhi@ksu.edu
>>
*)

Require Export list_util.
Require Export store_util.
Require Export values.
Require Export environment.
Require Export symboltable.
Require Export CpdtTactics.

Module Entry_Value_Stored <: ENTRY.
  Definition T := value.
End Entry_Value_Stored.

Module STACK := STORE_PROP(Entry_Value_Stored).
Import STACK.
Import STACK.ST.


(** * Run-Time Check Evaluation *)

(** ** Overflow Check *)
(** check whether a value falls into the bound of basic integer type *)
Inductive overflowCheck: Z -> Ret value -> Prop :=
    | OverflowCheck_Fail: forall v,
        in_bound v int32_bound false ->
        overflowCheck v (RTE OverflowError)
    | OverflowCheck_OK: forall v,
        in_bound v int32_bound true ->
        overflowCheck v (OK (Int v)).

(** ** Division Check *)
Inductive divCheck: binary_operator -> Z -> Z -> Ret value -> Prop :=
    | DivCheck_RTE: forall op dividend divisor,
        op = Divide \/ op = Modulus ->
        (Zeq_bool divisor 0) = true -> (* divisor is zero *)
        divCheck op dividend divisor (RTE DivByZero)
    | DivCheck_D: forall dividend divisor v,
        (Zeq_bool divisor 0) = false -> (* divisor is not zero *)
        Math.div (Int dividend) (Int divisor) = Some v ->
        divCheck Divide dividend divisor (OK v)
    | DivCheck_M: forall dividend divisor v,
        (Zeq_bool divisor 0) = false -> (* divisor is not zero *)
        Math.mod' (Int dividend) (Int divisor) = Some v ->
        divCheck Modulus dividend divisor (OK v).

(** ** Range Check *)
Inductive rangeCheck: Z -> Z -> Z -> Ret value -> Prop :=
    | RangeCheck_Fail: forall v l u,
        in_bound v (Interval l u) false ->
        rangeCheck v l u (RTE RangeError)
    | RangeCheck_OK: forall v l u,
        in_bound v (Interval l u) true ->
        rangeCheck v l u (OK (Int v)).


(** ** Run-Time Check for Binary Operator *)
(* verify run time checks on binary / unary operations *)
Inductive do_run_time_check_on_binop: binary_operator -> value -> value -> Ret value -> Prop :=
    | DoCheckOnBinops: forall op v1 v2 v v',
        op = Plus \/ op = Minus \/ op = Multiply ->
        Math.binary_operation op v1 v2 = Some (Int v) ->
        overflowCheck v v' ->
        do_run_time_check_on_binop op v1 v2 v'
    | DoCheckOnDivide_RTE: forall v1 v2,
        divCheck Divide v1 v2 (RTE DivByZero) ->
        do_run_time_check_on_binop Divide (Int v1) (Int v2) (RTE DivByZero)
    | DoCheckOnDivide: forall v1 v2 v v',
        divCheck Divide v1 v2 (OK (Int v)) ->
        overflowCheck v v' ->
        do_run_time_check_on_binop Divide (Int v1) (Int v2) v'
    | DoCheckOnModulus: forall v1 v2 v',
        divCheck Modulus v1 v2 v' ->
        do_run_time_check_on_binop Modulus (Int v1) (Int v2) v'
    | DoCheckOnBinOp_Others: forall op v1 v2 v,
        op <> Plus ->
        op <> Minus ->
        op <> Multiply ->
        op <> Divide ->
        op <> Modulus ->
        Math.binary_operation op v1 v2 = Some v ->
        do_run_time_check_on_binop op v1 v2 (OK v).

(** ** Run-Time Check for Unary Operator *)
Inductive do_run_time_check_on_unop: unary_operator -> value -> Ret value -> Prop :=
    | DoCheckOnUnary_Minus: forall v v' v'',
        Math.unary_minus v = Some (Int v') ->
        overflowCheck v' v'' ->
        do_run_time_check_on_unop Unary_Minus v v''
    | DoCheckOnUnOp_Others: forall op v v',
        op <> Unary_Minus ->
        Math.unary_operation op v = Some v' ->
        do_run_time_check_on_unop op v (OK v').

(** given a record value r, get the value of its field f *)
Function record_select (r: list (idnum * value)) (f: idnum): option value :=
    match r with 
    | (f1, v1) :: r1 =>
        if beq_nat f1 f then 
          Some v1
        else
          record_select r1 f
    | nil => None 
    end.

(** given an array value a, get its component value indexed by i *)
Function array_select (a: list (arrindex * value)) (i: Z): option value :=
    match a with 
    | (i0, v0) :: a1 =>
        if Zeq_bool i0 i then
          Some v0
        else
          array_select a1 i
    | nil => None
    end.


(** * Relational Semantics *)

(** ** Literal Evaluation *)
(** interpret the literal expressions *)
Inductive evalLiteral: literal -> Ret value -> Prop :=
    | EvalLiteral_Bool: forall v,
        evalLiteral (Boolean_Literal v) (OK (Bool v))
    | EvalLiteral_Int: forall v v',
        overflowCheck v v' ->
        evalLiteral (Integer_Literal v) v'.

(** ** Expression Evaluation *)
(**
    for binary expression and unary expression, if a run time error 
    is detected in any of its child expressions, then return a run
    time error; for binary expression (e1 op e2), if both e1 and e2 
    are evaluated to some normal values, then run-time checks are
    performed according to the checking rules specified for the 
    operator 'op'; Whenever the check fails, a run-time error is 
    detected and the program is terminated, otherwise, normal binary 
    operation result is returned;
*)

Inductive evalExp: symTab -> state -> exp -> Ret value -> Prop :=
    | EvalLiteral: forall l v st s n,
        evalLiteral l v ->
        evalExp st s (Literal n l) v
    | EvalName: forall s nm v st n,
        evalName st s nm v ->
        evalExp st s (Name n nm) v
    | EvalBinOpE1_RTE: forall st s e1 msg n op e2,
        evalExp st s e1 (RTE msg) ->
        evalExp st s (BinOp n op e1 e2) (RTE msg)
    | EvalBinOpE2_RTE: forall st s e1 v1 e2 msg n op,
        evalExp st s e1 (OK v1) ->
        evalExp st s e2 (RTE msg) ->
        evalExp st s (BinOp n op e1 e2) (RTE msg)
    | EvalBinOp: forall st s e1 v1 e2 v2 op v n,
        evalExp st s e1 (OK v1) ->
        evalExp st s e2 (OK v2) ->
        do_run_time_check_on_binop op v1 v2 v ->
        evalExp st s (BinOp n op e1 e2) v
    | EvalUnOp_RTE: forall st s e msg n op,
        evalExp st s e (RTE msg) ->
        evalExp st s (UnOp n op e) (RTE msg)
    | EvalUnOp: forall st s e v op v' n,
        evalExp st s e (OK v) ->
        do_run_time_check_on_unop op v v' ->
        evalExp st s (UnOp n op e) v'

(** ** Name Evaluation *)
with evalName: symTab -> state -> name -> Ret value -> Prop :=
    | EvalIdentifier: forall x s v st n, 
        fetchG x s = Some v ->
        evalName st s (Identifier n x) (OK v)
    | EvalIndexedComponentX_RTE: forall st s x msg n e,
        evalName st s x (RTE msg) ->
        evalName st s (IndexedComponent n x e) (RTE msg)
    | EvalIndexedComponentE_RTE: forall st s x a e msg n,
        evalName st s x (OK (ArrayV a)) ->
        evalExp st s e (RTE msg) ->
        evalName st s (IndexedComponent n x e) (RTE msg)
    | EvalIndexedComponent_Range_RTE: forall st s x a e i t l u n, 
        evalName st s x (OK (ArrayV a)) ->
        evalExp st s e (OK (Int i)) ->
        fetch_exp_type (name_astnum x) st = Some (Array_Type t) ->
        extract_array_index_range st t (Range l u) ->
        rangeCheck i l u (RTE RangeError) ->
        evalName st s (IndexedComponent n x e) (RTE RangeError)
    | EvalIndexedComponent: forall st s x a e i t l u v n, 
        evalName st s x (OK (ArrayV a)) ->
        evalExp st s e (OK (Int i)) ->
        fetch_exp_type (name_astnum x) st = Some (Array_Type t) -> (*get the array type of x from the symbol table with its ast number x_n *)
        extract_array_index_range st t (Range l u) -> (*given array type t, get its array type declaration from symbol table and extract its range*)
        rangeCheck i l u (OK (Int i)) -> (*do range check on the index exp i against the range of the array index type*)
        array_select a i = Some v -> (*get the component value indexed by i from array value a*)
        evalName st s (IndexedComponent n x e) (OK v)
    | EvalSelectedComponentX_RTE: forall st s x msg n f,
        evalName st s x (RTE msg) ->
        evalName st s (SelectedComponent n x f) (RTE msg)
    | EvalSelectedComponent: forall st s x r f v n,
        evalName st s x (OK (RecordV r)) ->
        record_select r f = Some v ->
        evalName st s (SelectedComponent n x f) (OK v).


(** ** Declaration Evaluation *)
(** Inductive semantic of declarations [eval_decl st s sto decl rsto] 
    means that rsto is the frame to be pushed on s after evaluating 
    decl, sto is used as an accumulator for building the frame;
 *)

Inductive evalDecl: symTab -> state -> frame -> decl -> Ret frame -> Prop :=
    | EvalDecl_Null: forall st s f,
        evalDecl st s f NullDecl (OK f)
    | EvalDecl_Type: forall st s f n t,
        evalDecl st s f (TypeDecl n t) (OK f)
    | EvalDecl_Var_None: forall d st s f n,
        d.(initialization_exp) = None ->
        evalDecl st s f (ObjDecl n d) (OK (push f d.(object_name) Undefined))
    | EvalDecl_Var_RTE: forall d e st f s msg n,
        d.(initialization_exp) = Some e ->
        evalExp st (f :: s) e (RTE msg) ->
        evalDecl st s f (ObjDecl n d) (RTE msg)
    | EvalDecl_Var: forall d e st f s v n,
        d.(initialization_exp) = Some e ->
        evalExp st (f :: s) e (OK v) ->
        v <> Undefined ->
        is_range_constrainted_type (d.(object_nominal_subtype)) = false ->
        evalDecl st s f (ObjDecl n d) (OK (push f d.(object_name) v))
    | EvalDecl_Var_Range_RTE: forall d e st f s v l u n,
        d.(initialization_exp) = Some e ->
        evalExp st (f :: s) e (OK (Int v)) ->
        extract_subtype_range st (d.(object_nominal_subtype)) (Range l u) ->
        rangeCheck v l u (RTE RangeError) ->        
        evalDecl st s f (ObjDecl n d) (RTE RangeError)
    | EvalDecl_Var_Range: forall d e st f s v l u n,
        d.(initialization_exp) = Some e ->
        evalExp st (f :: s) e (OK (Int v)) ->
        extract_subtype_range st (d.(object_nominal_subtype)) (Range l u) ->
        rangeCheck v l u (OK (Int v)) -> (*for a declared variable, do range check on value of its initialization expression if its declared type is range constrainted type*)
        evalDecl st s f (ObjDecl n d) (OK (push f d.(object_name) (Int v)))
    | EvalDecl_Proc: forall st s f n p,
        evalDecl st s f (ProcBodyDecl n p) (OK f)
    | EvalDecl_Seq_RTE: forall st s f d1 msg n d2,
        evalDecl st s f d1 (RTE msg) ->
        evalDecl st s f (SeqDecl n d1 d2) (RTE msg)
    | EvalDecl_Seq: forall st s f d1 f' d2 f'' n,
        evalDecl st s f d1 (OK f') ->
        evalDecl st s f' d2 f'' ->
        evalDecl st s f (SeqDecl n d1 d2) f''.


(** update the ith element of array a by value v: a[i] := v *)
Function updateIndexedComp (a: list (arrindex * value)) (i: arrindex) (v: value): list (arrindex * value) :=
    match a with
    | (i0, v0)::a1 => 
        if Zeq_bool i0 i then
          (i0, v) :: a1
        else
          (i0, v0) :: (updateIndexedComp a1 i v)
    | nil => (i, v) :: nil
    end.

(** update the field f of record r by value v: r.f := v *)
Function updateSelectedComp (r: list (idnum * value)) (f : idnum) (v: value): list (idnum * value) := 
    match r with 
    | (f1, v1) :: r1 => 
      if beq_nat f1 f then 
        (f1,v) :: r1
      else 
        (f1, v1) :: (updateSelectedComp r1 f v)
   | nil => (f, v) :: nil
   end.

Function arrayUpdate (a: value) (i: arrindex) (v: value): option value :=
    match a with
    | Undefined => Some (ArrayV (updateIndexedComp nil i v))
    | ArrayV arrObj => Some (ArrayV (updateIndexedComp arrObj i v))
    | _ => None
    end.

(** update the field f of record r by value v: r.f := v *)
Function recordUpdate (r: value) (f : idnum) (v: value): option value := 
    match r with
    | Undefined => Some (RecordV (updateSelectedComp nil f v))
    | RecordV recObj => Some (RecordV (updateSelectedComp recObj f v))  
    | _ => None
    end.

(** update name with new value in the state and return newly updated state *)
Inductive storeUpdate: symTab -> state -> name -> value -> Ret state -> Prop := 
    | SU_Identifier: forall s x v s1 st n,
        updateG s x v = Some s1 ->
        storeUpdate st s (Identifier n x) v (OK s1)
    | SU_Indexed_Component_xRTE: forall st s x msg n e v,
        evalName st s x (RTE msg) ->
        storeUpdate st s (IndexedComponent n x e) v (RTE msg)
    | SU_Indexed_Component_eRTE: forall st s x a e msg n v,
        evalName st s x (OK (ArrayV a)) \/ evalName st s x (OK Undefined) ->
        evalExp st s e (RTE msg) ->
        storeUpdate st s (IndexedComponent n x e) v (RTE msg)
    | SU_Indexed_Component_Range_RTE: forall st s x a e i t l u n v,
        evalName st s x (OK (ArrayV a)) \/ evalName st s x (OK Undefined) ->
        evalExp st s e (OK (Int i)) ->
        fetch_exp_type (name_astnum x) st = Some (Array_Type t) ->
        extract_array_index_range st t (Range l u) ->
        rangeCheck i l u (RTE RangeError) ->
        storeUpdate st s (IndexedComponent n x e) v (RTE RangeError)
    | SU_Indexed_Component: forall st s x arrObj a e i t l u v a1 s1 n,
        evalName st s x (OK arrObj) ->
        arrObj = (ArrayV a) \/ arrObj = Undefined ->
        evalExp st s e (OK (Int i)) ->
        fetch_exp_type (name_astnum x) st = Some (Array_Type t) ->
        extract_array_index_range st t (Range l u) ->
        rangeCheck i l u (OK (Int i)) ->
        arrayUpdate arrObj i v = (Some (ArrayV a1)) -> (* a[i] := v *)
        storeUpdate st s x (ArrayV a1) s1 ->
        storeUpdate st s (IndexedComponent n x e) v s1
    | SU_Selected_Component_xRTE: forall st s x msg n f v,
        evalName st s x (RTE msg) ->
        storeUpdate st s (SelectedComponent n x f) v (RTE msg)
    | SU_Selected_Component: forall st s x recObj r f v r1 s1 n,
        evalName st s x (OK recObj) ->
        recObj = (RecordV r) \/ recObj = Undefined ->
        recordUpdate recObj f v = Some (RecordV r1) -> (* x.f := v *)
        storeUpdate st s x (RecordV r1) s1 ->
        storeUpdate st s (SelectedComponent n x f) v s1.


(** ** Statement Evaluation *)

(** State Manipulation For Procedure Calls And Return *)

(** [Copy_in st s f lparams lexp frame] means the frame is the portion
    of stack to push on the stack to start evaluating the procedure
    having [lparams] as parameters spcification. More precisely,
    [frame] contains the value of the formal parameters described by
    [lpamrams]. These values are computed from the list of arguments
    [lexp] starting from the initial frame f. Only "In" and "In Out" 
    parameters are evaluated, "Out" parameters are set to [Undefined]. 
*)

(** start from an empty frame and then push the values of arguments into it *)

(** *** Copy In *)
Inductive copyIn: symTab -> state -> frame -> list paramSpec -> list exp -> Ret frame -> Prop :=
    | CopyIn_Nil : forall st s f, 
        copyIn st s f nil nil (OK f)
    | CopyIn_Mode_In_eRTE: forall param st s e msg f lparam le,
        param.(parameter_mode) = In ->
        evalExp st s e (RTE msg) ->
        copyIn st s f (param :: lparam) (e :: le) (RTE msg)
    | CopyIn_Mode_In_NoRange: forall param st s e v f f' lparam le f'',
        param.(parameter_mode) = In ->
        evalExp st s e (OK v) ->
        v <> Undefined ->
        is_range_constrainted_type (param.(parameter_subtype_mark)) = false -> (*there's no need to do range check if the parameter's type is not range constrainted type*)
        push f param.(parameter_name) v = f' ->
        copyIn st s f' lparam le f'' ->
        copyIn st s f (param :: lparam) (e :: le) f''
    | CopyIn_Mode_In_Range_RTE: forall param st s e v l u f lparam le,
        param.(parameter_mode) = In ->
        evalExp st s e (OK (Int v)) ->
        extract_subtype_range st (param.(parameter_subtype_mark)) (Range l u) ->
        rangeCheck v l u (RTE RangeError) ->
        copyIn st s f (param :: lparam) (e :: le) (RTE RangeError)
    | CopyIn_Mode_In_Range: forall param st s e v l u f f' lparam le f'',
        param.(parameter_mode) = In ->
        evalExp st s e (OK (Int v)) ->
        extract_subtype_range st (param.(parameter_subtype_mark)) (Range l u) -> (*if the parameter's type is a range constrainted type, get its type's range*)
        rangeCheck v l u (OK (Int v)) -> (*do range check on the value of argument against its corresponding parameter's type range*)
        push f param.(parameter_name) (Int v) = f' ->
        copyIn st s f' lparam le f'' ->
        copyIn st s f (param :: lparam) (e :: le) f''
    | CopyIn_Mode_InOut_eRTE: forall param st s nm msg f lparam n le,
        param.(parameter_mode) = In_Out ->
        evalName st s nm (RTE msg) ->
        copyIn st s f (param :: lparam) ((Name n nm) :: le) (RTE msg)
    | CopyIn_Mode_InOut_NoRange: forall param st s nm v f f' lparam le f'' n,
        param.(parameter_mode) = In_Out ->
        evalName st s nm (OK v) ->
        v <> Undefined ->
        is_range_constrainted_type (param.(parameter_subtype_mark)) = false -> (*there's no need to do range check if the parameter's type is not range constrainted type*)
        push f param.(parameter_name) v = f' ->
        copyIn st s f' lparam le f'' ->
        copyIn st s f (param :: lparam) ((Name n nm) :: le) f''
    | CopyIn_Mode_InOut_Range_RTE: forall param st s nm v l u f lparam le n,
        param.(parameter_mode) = In_Out ->
        evalName st s nm (OK (Int v)) ->
        extract_subtype_range st (param.(parameter_subtype_mark)) (Range l u) ->
        rangeCheck v l u (RTE RangeError) ->
        copyIn st s f (param :: lparam) ((Name n nm) :: le) (RTE RangeError)
    | CopyIn_Mode_InOut_Range: forall param st s nm v l u f f' lparam le f'' n,
        param.(parameter_mode) = In_Out ->
        evalName st s nm (OK (Int v)) ->
        extract_subtype_range st (param.(parameter_subtype_mark)) (Range l u) -> (*if the parameter's type is a range constrainted type, get its type's range*)
        rangeCheck v l u (OK (Int v)) -> (*do range check on the value of argument against its corresponding parameter's type range*)
        push f param.(parameter_name) (Int v) = f' ->
        copyIn st s f' lparam le f'' ->
        copyIn st s f (param :: lparam) ((Name n nm) :: le) f''
    | CopyIn_Mode_Out: forall param f f' st s lparam le f'' n nm,
        param.(parameter_mode) = Out ->
        push f param.(parameter_name) Undefined = f' ->
        copyIn st s f' lparam le f'' ->
        copyIn st s f (param :: lparam) ((Name n nm) :: le) f''.


(** [Copy_out st s prefix lparams lexp s'] means that s' is the result of
    copying Out params of the currently finished procedure of prefix
    into there output variables. More precisely:
  - [prefix] is a portion of stack where only the parameters of the
    procedure are stored;
  - [lparams] is the static specification of the parameters of the
    procedure;
  - [lexp] is the list of original expressions given as parameter of
    the procedure (this is where one can find in which variables "out"
    parameters must be copied);
  - [s] is the portion of the stack which needs to be updated and
    returned by the procedure, more precisely: it contains the global
    parameters + the local environment of the colling procedure;
  - [s'] is the resulting state. *)

(** *** Copy Out *)
Inductive copyOut: symTab -> state -> frame -> list paramSpec -> list exp -> Ret state -> Prop :=
    | CopyOut_Nil : forall st s f, 
        copyOut st s f nil nil (OK s)
    | CopyOut_Mode_Out_nRTE: forall param f v n st t s nm msg lparam lexp,
        param.(parameter_mode) = Out \/ param.(parameter_mode) = In_Out ->
        fetch param.(parameter_name) f = Some v ->
        v <> Undefined ->
        fetch_exp_type n st = Some t -> (*get the type of output argument x from the symbol table with its ast number*)
        is_range_constrainted_type t = false -> (*if it's not a range constrainted scalar type, then no range check is needed*)
        storeUpdate st s nm v (RTE msg) ->
        copyOut st s f (param :: lparam) ((Name n nm) :: lexp) (RTE msg)
    | CopyOut_Mode_Out_NoRange: forall param f v n st t s nm s' lparam lexp s'',
        param.(parameter_mode) = Out \/ param.(parameter_mode) = In_Out ->
        fetch param.(parameter_name) f = Some v ->
        v <> Undefined ->
        fetch_exp_type n st = Some t -> (*get the type of output argument x from the symbol table with its ast number*)
        is_range_constrainted_type t = false -> (*if it's not a range constrainted scalar type, then no range check is needed*)
        storeUpdate st s nm v (OK s') ->
        copyOut st s' f lparam lexp s'' ->
        copyOut st s f (param :: lparam) ((Name n nm) :: lexp) s''
    | CopyOut_Mode_Out_Range_RTE: forall param f v n st t l u s lparam nm lexp,
        param.(parameter_mode) = Out \/ param.(parameter_mode) = In_Out ->
        fetch param.(parameter_name) f = Some (Int v) ->
        fetch_exp_type n st = Some t -> (*get the type of output argument x from the symbol table with its ast number*)
        extract_subtype_range st t (Range l u) -> (*if it's a range constrainted scalar type, then get its range and do range check before copy out*)
        rangeCheck v l u (RTE RangeError) ->
        copyOut st s f (param :: lparam) ((Name n nm) :: lexp) (RTE RangeError)
    | CopyOut_Mode_Out_Range_nRTE: forall param f v n st t l u s nm msg lparam lexp,
        param.(parameter_mode) = Out \/ param.(parameter_mode) = In_Out ->
        fetch param.(parameter_name) f = Some (Int v) ->
        fetch_exp_type n st = Some t ->
        extract_subtype_range st t (Range l u) ->
        rangeCheck v l u (OK (Int v)) ->
        storeUpdate st s nm (Int v) (RTE msg) ->
        copyOut st s f (param :: lparam) ((Name n nm) :: lexp) (RTE msg)
    | CopyOut_Mode_Out_Range: forall param f v n st t l u s nm s' lparam lexp s'',
        param.(parameter_mode) = Out \/ param.(parameter_mode) = In_Out ->
        fetch param.(parameter_name) f = Some (Int v) ->
        fetch_exp_type n st = Some t ->
        extract_subtype_range st t (Range l u) ->
        rangeCheck v l u (OK (Int v)) ->
        storeUpdate st s nm (Int v) (OK s') ->
        copyOut st s' f lparam lexp s'' ->
        copyOut st s f (param :: lparam) ((Name n nm) :: lexp) s''
    | CopyOut_Mode_In: forall param st s f lparam lexp s' e,
        param.(parameter_mode) = In ->
        copyOut st s f lparam lexp s' ->
        copyOut st s f (param :: lparam) (e :: lexp) s'.



(** [cut_until s n s' s''] means cutting the stack s until to a frame 
    whose corresponding procedure's nested declaration level is less 
    than n, and s' is a stack with all its frame's corresponding procedure's 
    nested declaration level greater or equal n, and s'' is a stack holds 
    frames whose procedure's nested declaration levels are less than n, 
    and s = s' ++ s'';
*)
Inductive cutUntil: state -> scope_level -> state -> state -> Prop :=
    | CutUntil_Nil: forall n,
        cutUntil nil n nil nil
    | CutUntil_Head: forall f n s,
        (level_of f) < n ->
        cutUntil (f :: s) n nil (f :: s) 
    | CutUntil_Tail: forall f n s s' s'',
        ~ (level_of f < n) ->
        cutUntil s n s' s'' -> 
        cutUntil (f :: s) n (f :: s') s''.

Lemma cut_until_uniqueness: forall s n intact_s' s' intact_s'' s'',
  cutUntil s n intact_s' s' ->
  cutUntil s n intact_s'' s'' ->
  intact_s' = intact_s'' /\ s' = s''.
Proof.
  intros s n intact_s' s' intact_s'' s'' H; revert intact_s'' s''.
  induction H; intros;
  match goal with
    | [H: cutUntil nil _ _ _ |- _] => inversion H
    | [H: cutUntil (?f :: ?s) _ _ _ |- _] => inversion H
  end; smack;
  specialize (IHcutUntil _ _ H8); smack.
Qed.

(** in a statement evaluation, whenever a run time error is detected in
    the evaluation of its sub-statements or sub-component, the
    evaluation is terminated and return a run-time error; otherwise,
    evaluate the statement into a normal state.

   - in the evaluation for assignment statement (Assign n x e),

     first, check if it's needed to do range check on the right side (e) 
     of the assignment,
     case 1: (is_range_constrainted_type t = false) means no range check 
     needed for the value of expression e as the type of the left side of
     the assignment is not a range constrainted type, 
     case 2: (extract_subtype_range st t (Range l u)) means left side of
     the assignment is a name expression of range constrainted type whose 
     range is between l and u, so a range check is required on the value 
     of expression e;

     second, if there is no range check required for e, then do expression 
     evaluation directly on e and update the value of x if there is no run-time
     errors during their evaluation;
     if there is a range check required for e, then a range check should be 
     performed on the evaluation value of e before it's assigned to the left side
     (x) of the assignment; 
     
     please note that the range check for the value of expression e is verified 
     against the target type taken from the left side (x) of the assignment, that's
     why the range check for expression e is enforced at the level of assignment 
     statement even though the RangeCheck flag is set on the expression e;

   - in the store update storeUpdate_rt for indexed component (e.g. a(i):=v) or selected
     component (e.g. r.f := v), 
     
     if the value of array a (or value of record r) is Undefined, then create a new 
     aggregate array value with its ith element having value v (or create a new record 
     value with its field f having value v), and assign this new aggregate value to array 
     variable a (or record variable r);
     
     if the value of array a (or value of record r) is already defined, then update the
     ith element of its array value (or update the filed f of its record value), and assign
     the updated aggregate value to array variable a (or record variable r);

   - in the store update storeUpdate_rt for indexed component (e.g. a(i):=v), a
     range check is required to be performed on the value of index expression i
     before it's used to update the array value;
 *)

(** ** evalStmt *)
Inductive evalStmt: symTab -> state -> stmt -> Ret state -> Prop := 
    | EvalNull: forall st s,
        evalStmt st s Null (OK s)
    | EvalAssign_RTE: forall st s e msg n x,
        evalExp st s e (RTE msg) ->
        evalStmt st s (Assign n x e) (RTE msg)
    | EvalAssign: forall st s e v x t s1 n,
        evalExp st s e (OK v) ->
        v <> Undefined ->
        fetch_exp_type (name_astnum x) st = Some t ->
        is_range_constrainted_type t = false ->
        storeUpdate st s x v s1 ->
        evalStmt st s (Assign n x e) s1
    | EvalAssign_Range_RTE: forall st s e v x t l u n,
        evalExp st s e (OK (Int v)) ->
        fetch_exp_type (name_astnum x) st = Some t -> (*get the type of the left hand side of the assignment*)
        extract_subtype_range st t (Range l u) -> (*if left hand side is an expression of range constrainted type, then get its range from symbol table*)
        rangeCheck v l u (RTE RangeError) -> (*do range check on the value of the right hand side expression of the assignment*)
        evalStmt st s (Assign n x e) (RTE RangeError)
    | EvalAssign_Range: forall st s e v x t l u s1 n,
        evalExp st s e (OK (Int v)) ->
        fetch_exp_type (name_astnum x) st = Some t ->
        extract_subtype_range st t (Range l u) ->
        rangeCheck v l u (OK (Int v)) ->
        storeUpdate st s x (Int v) s1 ->
        evalStmt st s (Assign n x e) s1
    | EvalIf_RTE: forall st s b msg n c1 c2,
        evalExp st s b (RTE msg) ->
        evalStmt st s (If n b c1 c2) (RTE msg)
    | EvalIf_True: forall st s b c1 s1 n c2,
        evalExp st s b (OK (Bool true)) ->
        evalStmt st s c1 s1 ->
        evalStmt st s (If n b c1 c2) s1
    | EvalIf_False: forall st s b c2 s1 n c1,
        evalExp st s b (OK (Bool false)) ->
        evalStmt st s c2 s1 ->
        evalStmt st s (If n b c1 c2) s1
    | EvalWhile_RTE: forall st s b msg n c,
        evalExp st s b (RTE msg) ->
        evalStmt st s (While n b c) (RTE msg)
    | EvalWhile_True_RTE: forall st s b c msg n,
        evalExp st s b (OK (Bool true)) ->
        evalStmt st s c (RTE msg) ->
        evalStmt st s (While n b c) (RTE msg)
    | EvalWhile_True: forall st s b c s1 n s2,
        evalExp st s b (OK (Bool true)) ->
        evalStmt st s c (OK s1) ->
        evalStmt st s1 (While n b c) s2 ->
        evalStmt st s (While n b c) s2
    | EvalWhile_False: forall st s b n c,
        evalExp st s b (OK (Bool false)) ->
        evalStmt st s (While n b c) (OK s)
    | EvalCall_Args_RTE: forall p st n0 pb s args msg n pn,
        fetch_proc p st = Some (n0, pb) ->
        copyIn st s (newFrame n) (procedure_parameter_profile pb) args (RTE msg) ->
        evalStmt st s (Call n pn p args) (RTE msg)
    | EvalCall_Decl_RTE: forall p st n0 pb s args f intact_s s1 msg n pn,
        fetch_proc p st = Some (n0, pb) ->
        copyIn st s (newFrame n) (procedure_parameter_profile pb) args (OK f) ->
        cutUntil s n intact_s s1 -> (* s = intact_s ++ s1 *)
        evalDecl st s1 f (procedure_declarative_part pb) (RTE msg) ->
        evalStmt st s (Call n pn p args) (RTE msg)
    | EvalCall_Body_RTE: forall p st n0 pb s args f intact_s s1 f1 msg n pn,
        fetch_proc p st = Some (n0, pb) ->
        copyIn st s (newFrame n) (procedure_parameter_profile pb) args (OK f) ->
        cutUntil s n intact_s s1 -> (* s = intact_s ++ s1 *)
        evalDecl st s1 f (procedure_declarative_part pb) (OK f1) ->
        evalStmt st (f1 :: s1) (procedure_statements pb) (RTE msg) ->
        evalStmt st s (Call n pn p args) (RTE msg)
    | EvalCall: forall p st n0 pb s args f intact_s s1 f1 s2 locals_section params_section s3 s4 n pn,
        fetch_proc p st = Some (n0, pb) ->
        copyIn st s (newFrame n) (procedure_parameter_profile pb) args (OK f) ->
        cutUntil s n intact_s s1 -> (* s = intact_s ++ s1 *)
        evalDecl st s1 f (procedure_declarative_part pb) (OK f1) ->          
        evalStmt st (f1 :: s1) (procedure_statements pb) (OK s2) ->
        s2 = (n, locals_section ++ params_section) :: s3 -> (* extract parameters from local frame *)
        List.length (store_of f) = List.length params_section ->
        copyOut st (intact_s ++ s3) (n, params_section) (procedure_parameter_profile pb) args s4 ->
        evalStmt st s (Call n pn p args) s4
    | EvalSeq_RTE: forall st s c1 msg n c2,
        evalStmt st s c1 (RTE msg) ->
        evalStmt st s (Seq n c1 c2) (RTE msg)
    | EvalSeq: forall st s c1 s1 c2 s2 n,
        evalStmt st s c1 (OK s1) ->
        evalStmt st s1 c2 s2 ->
        evalStmt st s (Seq n c1 c2) s2.


(** ** evalProgram *)
(** the main procedure (with empty parameters) is working as the entry point of the whole program 
    - p: is the program
    - p.(main): the main procedure of the program
    - mainProc: the declaration of the main procedure
    - the arguments of the main procedure is nil
    - the initial state of the program is nil
*)

Inductive evalProgram: symTab -> state -> program -> Ret state -> Prop := 
    | EvalProgram: forall st s p n pn,
        evalStmt st nil (Call n pn p.(main) nil) s ->
        evalProgram st nil p s.

(**********************************************************************************************************

(** ** examples *)

Module ExampleProcedures.
(* EXAMPLE 1, v102 is a variable in the scope.
------------------------
procedure P2 () is
  V4 : TYPE5 := 34;
begin
  V102 := 56;
end 
-----------------------
*)
Definition proc1:procedure_declaration := (mkprocedure_declaration
           1 101 nil nil
             (D_Object_declaration
                {|
                  declaration_astnum := 3;
                  object_name := 4;
                  object_nominal_subtype :=  5;
                  initialization_exp := Some (Literal 6 (Integer_Literal(34)))
                |}
             )
             (Assign 12 102 (Literal 8 (Integer_Literal(56))))).

Definition s1:state := ((101,Procedure proc1) :: (102, Value (Int(77))) :: nil)::nil.

Definition s2:state := ((101,Procedure proc1) :: (102, Value (Int(56)))  :: nil)::nil.


Lemma essai: evalStmt s1 (S_ProcCall 13 101 nil) (Normal s2).
Proof.
  eapply eval_S_Proc; try now (simpl; eauto).
  - simpl.
    instantiate (1 := nil).
    constructor.
  - constructor 1.
    reflexivity.
    
  - econstructor 2.
    + reflexivity.
    + simpl.
      reflexivity.
    + constructor.
      simpl.
      reflexivity.
  - simpl.
    econstructor.
    + econstructor.
      simpl.
      eauto.
    + simpl.
      rewrite app_nil_r.
      reflexivity.
  - simpl.
    constructor 1.
Qed.



(* v102 is a variable in the scope.
procedure P2 () is
  V4 : TYPE5 := 34;
  V5 : TYPE5 := 37;
begin
  V5 := V4 + V5;
  V102 := V5*2;
end 
*)
Definition proc2:procedure_declaration := (mkprocedure_declaration
           1 101 nil nil
             (D_Sequence
                (D_Object_declaration
                   {|
                     declaration_astnum := 3;
                     object_name := 4;
                     object_nominal_subtype :=  5;
                     initialization_exp := Some (Literal 6 (Integer_Literal(34)))
                   |}
                )
                (D_Object_declaration
                   {|
                     declaration_astnum := 4;
                     object_name := 5;
                     object_nominal_subtype :=  5;
                     initialization_exp := Some (Literal 6 (Integer_Literal(37)))
                   |}
                )
             )
             (Seq 13
                (Assign 14 5
                              (BinOp 9 Plus
                                                  (Identifier 10 5)
                                                  (Identifier 10 4)))
                (Assign
                   12
                   102
                   (BinOp 9 Multiply
                                       (Identifier 10 5)
                                       (Literal 8 (Integer_Literal(2))))))).

Definition sto3:store := (101,Procedure proc2) :: (102, Value (Int(77))) :: nil.

Definition sto4:store := (101,Procedure proc2) :: (102, Value (Int(142)))  :: nil.



Lemma essai2: eval_stmt (sto3::nil) (S_ProcCall 13 101 nil) (Normal (sto4::nil)).
Proof.
  eapply eval_S_Proc; try now (simpl; eauto).
  - simpl.
    constructor.
  - constructor 1.
    reflexivity.
  - 
(*     instantiate (1:= ((5, Value (Int 37))::(4, Value (Int 34))::s3)). *)
    unfold sto3, sto4, proc1.
    simpl.
    econstructor 4;simpl.
    + econstructor 2;simpl.
      * econstructor;eauto.
      * reflexivity.
      * constructor.
        simpl.
        reflexivity.
    + econstructor 2;simpl.
      * econstructor;eauto.
      * reflexivity.
      * constructor.
        simpl.
        reflexivity.
  - simpl.
    + { econstructor.
        - econstructor.
          + econstructor.
            * econstructor.
              simpl.
              eauto.
            * constructor.
              simpl.
              eauto.
            * constructor.
              vm_compute.
              reflexivity.
            * econstructor.
              simpl.
              eauto.
          + simpl.
            reflexivity.
        - econstructor.
          + econstructor.
            * econstructor.
              simpl.
              eauto.
            * econstructor.
              simpl.
              eauto.
            * econstructor.
              vm_compute.
              reflexivity.
            * econstructor.
            simpl.
            eauto.
        + simpl.
          rewrite app_nil_r.
          reflexivity. }
  - simpl.
    constructor 1.
Qed.


End ExampleProcedures.
(* END EXAMPLE *)  

(** ** Functional Semantics of expressions *)

(** for relational semantics of expression and statement, we also 
    provide its corresponding version of functional semantics, and 
    prove that they are semantics equivalent;
    relational semantics encode the formal semantics rules, while
    functional semantics is useful to familiarize oneself with the 
    SPARK 2014 semantics, and validate it experimentally by testing, 
    and it also helps to fix the program if the program exhibits 
    undefined behavior;
    
    Bisimulation between relational and functional semantics are
    proved for the following pairs of evaluations: 
    
    - f_eval_binexpr <-> eval_binexpr;
    
    - f_eval_unaryexpr <-> eval_unaryexpr;
    
    - f_evalExp <-> evalExp;

    - f_eval_stmt <-> eval_stmt;
*)

(** *** semantic of operators *)

(** interpret the binary operation for each binary operator *)
Definition f_eval_bin_expr (op: binary_operator) (v1: value) (v2: value): Return value :=
    match op with
    | Equal => Val.eq v1 v2
    | Not_Equal => Val.ne v1 v2
    | Greater_Than => Val.gt v1 v2
    | Greater_Than_Or_Equal => Val.ge v1 v2
    | Less_Than => Val.lt v1 v2
    | Less_Than_Or_Equal => Val.le v1 v2
    | And => Val.and v1 v2
    | Or => Val.or v1 v2
    | Plus => Val.add v1 v2
    | Minus => Val.sub v1 v2
    | Multiply => Val.mul v1 v2
    | Divide => Val.div v1 v2
    end.

(** interpret the unary operation *)
Definition f_eval_unary_expr (op: unary_operator) (v: value): Return value :=
    match op with
    | Not => Val.not v
    | Unary_Plus => Val.unary_add v
    end.

(** *** Expression semantics *)

(** in functional semantics for expression, it returns either a
    normal value or a run time error or go abnormal, the run time 
    checks (for example, division by zero check) are encoded inside 
    the semantics; *)
Function f_evalExp (s: state) (e: expression): Return value :=
    match e with
    | Literal _ v => Normal (evalLiteral v)
    | Identifier _ x =>
        match (fetchG x s) with
        | Some (Value v) => Normal v
        | _ => Abnormal (* None or not a value *)
        end
    | BinOp _ op e1 e2 =>
        match f_evalExp s e1 with
        | Normal v1 => 
            match f_evalExp s e2 with
            | Normal v2 => 
                match f_do_check op v1 v2 with
                | Some true => f_eval_bin_expr op v1 v2
                | Some false => Run_Time_Error
                | _ => Abnormal
                end
            | Run_Time_Error => Run_Time_Error
            | Abnormal => Abnormal
            | Unterminated => Unterminated
            end
        | Run_Time_Error => Run_Time_Error
        | Abnormal => Abnormal
        | Unterminated => Unterminated
        end   
    | UnOp _ op e => 
        match f_evalExp s e with
        | Normal v => f_eval_unary_expr op v
        | Run_Time_Error => Run_Time_Error
        | Abnormal => Abnormal
        | Unterminated => Unterminated
        end
    end.

(** ** Functional Statement semantics *)


(** *** Functional manipulation of the state for procedure call and
    retrun *)

(** functional version of copyOut
  [copyOut prefx params lexp s'] returns s' updated in the following
  way: for each param in params that is Out, pick the correponding
  variable name in lexp and update s' with the value of the param that
  is stored in prefix. *)
Function copyOut (prefx:store) (params: list paramSpec)
         (lexp:list expression) (s: state) {struct params}:  Return state :=
  match params, lexp with
    | nil , nil => Normal s
    | (prm::params') , (e::lexp') =>
      match prm.(parameter_mode) with
         | Out =>
           match e with
             | Identifier _ x =>
               match (fetch (prm.(parameter_name)) prefx) with
                   Some v =>
                   match updateG s x v with
                     | Some s' => copyOut prefx params' lexp' s'
                     | None => Abnormal
                   end
                 | None => Abnormal
               end
             | _ => Abnormal
           end
         | In => copyOut prefx params' lexp' s
         | _ => Abnormal
       end
    | _ , _ => Abnormal
  end.

(** Functional version of copyIn.
   [copyIn s lparams lexp] returns the prefix to push on the state
   before evaluationg procedure body (i.e. declaration block +
   statement). "Out" parameters values are copied into there output
   variables (stored in lexp). *)
Function copyIn (s:state) lparams lexp: Return store :=
  match lparams,lexp with
  | (prm :: lparams') , (exp:: lexp') =>
    match prm.(parameter_mode) with
      | Out => if is_var exp
               then match copyIn s lparams' lexp' with
                      | Normal res => Normal ((prm.(parameter_name), Undefined) :: res)
                      | res => res
                    end
               else Abnormal
      | In =>
        let v := f_evalExp s exp in
        match v with
          | Normal v' =>
            match copyIn s lparams' lexp' with
              | Normal res => Normal ((prm.(parameter_name), Value v') :: res)
              | res => res
            end
          | Run_Time_Error => Run_Time_Error
          | Abnormal => Abnormal
          | Unterminated => Unterminated
        end
      | In_Out => Abnormal (* not yet implemented *)
    end
  | nil , nil => Normal nil
  | _ , _ => Abnormal
  end.

(** *** functional semantic of declarations *)

Function f_eval_decl (s: state) (sto:store) (c: declaration) {struct c}: Return store :=
  match c with
    | D_Object_declaration d =>
      match d.(initialization_exp) with
        | Some e =>
          match f_evalExp (sto::s) e with
            | Run_Time_Error => Run_Time_Error
            | Normal v =>
              (Normal ((d.(object_name), Value v)::sto))
            | Abnormal => Abnormal
            | Unterminated => Unterminated
          end
        | None => (Normal ((d.(object_name), Undefined) :: sto))
      end
    | D_Sequence dcl1 dcl2 =>
      match f_eval_decl s sto dcl1 with
        | Normal s' => f_eval_decl s s' dcl2
        | err => err
      end
    | D_Procedure_declaration pbody =>
      Normal((procedure_name pbody,Procedure pbody)::sto)
  end.

(** *** functional semantic of statements *)

(** 
   in the functional semantics for statement, 'k' denotes the execution 
   steps, whenever it reaches 0, an untermination state is returned;
   otherwise, it returns either a normal state, or a run time error 
   or an abnormal state; run time checks (for example, division by 
   zero check) are encoded inside the functional semantics;
*)





Function f_eval_stmt k (s: state) (c: statement) {struct k}: Return state := 
  match k with
  | 0 => Unterminated
  | S k' => 
    match c with
    | Assign n x e =>
        match f_evalExp s e with
        | Normal v => 
            match updateG s x (Value v) with
            | Some s1 => Normal s1
            | None => Abnormal
            end
        | Run_Time_Error => Run_Time_Error
        | Abnormal => Abnormal
        | Unterminated => Unterminated
        end
    | S_Sequence n c1 c2 =>
        match f_eval_stmt k' s c1 with
        | Normal s1 => f_eval_stmt k' s1 c2
        | Run_Time_Error => Run_Time_Error
        | Unterminated => Unterminated
        | Abnormal => Abnormal
        end
    | If n b c =>
        match f_evalExp s b with
        | Normal (Bool true) => f_eval_stmt k' s c
        | Normal (Bool false) => Normal s
        | Run_Time_Error => Run_Time_Error
        | Unterminated => Unterminated
        | _ => Abnormal
        end
    | While n b c => 
        match f_evalExp s b with
        | Normal (Bool true) => 
            match f_eval_stmt k' s c with
            | Normal s1 => f_eval_stmt k' s1 (While n b c)
            | Run_Time_Error => Run_Time_Error
            | Unterminated => Unterminated
            | Abnormal => Abnormal
            end
        | Normal (Bool false) => Normal s
        | Run_Time_Error => Run_Time_Error
        | Unterminated => Unterminated
        | _ => Abnormal
        end
    | S_ProcCall n pbname lexp =>
      match fetchG pbname s with
        | Some (Procedure pb) => 
          match copyIn s (procedure_parameter_profile pb) lexp with
            | Normal prefx => 
              match cutUntil s pbname with
                | Some (s_forget, s_called) =>
                  match f_eval_decl s_called prefx (procedure_declarative_part pb) with
                    | Normal s2 =>
                      match f_eval_stmt k' (s2::s_called) (procedure_statements pb) with
                        | Normal (frame::s') =>
                          match split1 _ (List.length frame - List.length prefx) frame with
                            | Some (slocal,prefx') =>
                              (copyOut prefx' (procedure_parameter_profile pb) lexp (s_forget++s'))
                            | None => Abnormal (* erronous store size *)
                          end
                        | Run_Time_Error => Run_Time_Error
                        | _ => Abnormal (* erronous state size or abnormal result *)
                      end
                    | Run_Time_Error => Run_Time_Error
                    | _ => Abnormal
                  end
                | None => Abnormal (* procedure doesn't exist *)
              end
            (* left and right are not of the same type (return_state
               store) and (return_state state) *)
            | Run_Time_Error => Run_Time_Error
            | Abnormal => Abnormal
            | Unterminated => Unterminated
          end
        | _ => (* None or non-procedure *) Abnormal
      end
    end
  end.

(* My renaming heuristic. Not perfect. *)
Ltac semantic_rename_hyp th :=
  match th with
    | (do_check _ _ _ _) => fresh "hdo_check"
    | (evalExp _ _ Run_Time_Error) => fresh "hevalExp_rte"
    | (evalExp _ _ _) => fresh "hevalExp"
    | (eval_decl _ _ _ _) => fresh "heval_decl"
    | (eval_stmt _ _ _) => fresh "heval_stmt"
    | (eval_bin_expr _ _ _ _) => fresh "heval_bin_expr"
    | (eval_unary_expr _ _ _) => fresh "heval_unary_expr"
    | (evalLiteral _ = _) => fresh "heqevalLiteral"
    | (updateG _ _ _ = _) => fresh "hupdateG"
    | (update _ _ _ = _) => fresh "hupdate"
    | (fetchG _ _ = _) => fresh "heqfetchG"
    | (fetch _ _ = _) => fresh "heqfetch"
    | (copyIn _ _ _ _) => fresh "hcopyIn"
    | (cutUntil _ _ _ _) => fresh "hcutUntil"
    | (f_evalExp _ _ = Run_Time_Error) => fresh "heqevalExp_rte"
    | (f_evalExp _ _ = _) => fresh "heqevalExp"
    | (f_eval_decl _ _ _ = _) => fresh "heqeval_decl"
    | (f_eval_stmt _ _ _ = _ ) => fresh "heqeval_stmt"
    | (f_eval_bin_expr _ _ _ = _) => fresh "heqeval_bin_expr"
    | (f_do_check _ _ _ = _) => fresh "heqdo_check"
    | (state_eq_length _ _) => fresh "hstack_eq_length"
    | _ => default_rename_hyp th
  end.
Ltac rename_hyp ::= semantic_rename_hyp.

Lemma evalExp_unique: forall s e v1 v2,
    evalExp s e v1 ->
    evalExp s e v2 ->
    v1 = v2.
Proof.
  intros s e v1 v2 hv1.
  revert v2.
  !induction hv1;!intros.
  - subst.
    !inversion hevalExp.
    reflexivity.
  - !inversion hevalExp; !intros.
    Rinversion fetchG.    
  - !inversion hevalExp;auto;!intros.
    apply IHhv1 in hevalExp1.
    discriminate.
  - !inversion hevalExp0; !intros ; auto.
    apply IHhv1_2 in hevalExp1.
    discriminate.
  - !inversion hevalExp1;auto;!intros.
    apply f_do_check_complete in hdo_check.
    apply f_do_check_complete in hdo_check0.
    apply IHhv1_2 in hevalExp2.
    apply IHhv1_1 in hevalExp3.
    injection hevalExp2.
    injection hevalExp3.
    intros; subst.
    rewrite hdo_check in hdo_check0.
    discriminate.
  - !inversion hevalExp1;!intros.
    + apply IHhv1_1 in hevalExp_rte.
      discriminate.
    + apply IHhv1_2 in hevalExp_rte.
      discriminate.
    + apply f_do_check_complete in hdo_check0.
      apply f_do_check_complete in hdo_check.
      apply IHhv1_1 in hevalExp3.
      apply IHhv1_2 in hevalExp2.
      injection hevalExp3.
      injection hevalExp2.
      intros ; subst.
      rewrite hdo_check in hdo_check0.
      discriminate.
    + apply IHhv1_1 in hevalExp3.
      apply IHhv1_2 in hevalExp2.
      injection hevalExp3.
      injection hevalExp2.
      intros ;subst.
      rewrite (eval_bin_unique _ _ _ _ _ heval_bin_expr heval_bin_expr0) .
      reflexivity.
  - !inversion hevalExp;auto;!intros.
    apply IHhv1 in hevalExp0.
    discriminate.
  - !inversion hevalExp;!intros.
    + apply IHhv1 in hevalExp_rte.
      discriminate.
    + apply IHhv1 in hevalExp0.
      injection hevalExp0.
      intros ;subst.
      rewrite (eval_unary_unique _ _ _ _ heval_unary_expr0 heval_unary_expr) .
      reflexivity.
Qed.    


(** 
    for any expression e evaluated under the state s, if it can be 
    evaluated to a value v with respect to the relational semantics 
    evalExp, then the result value v should be either a normal 
    value or a run time error;
*)
Lemma evalExp_state : forall s e v,
        evalExp s e v -> (* v should be either a normal value or a run time error *)
            (exists v0, v = Normal v0) \/ v = Run_Time_Error.
Proof.
    intros s e v h.
    induction h;
    try match goal with
    | [ |- (exists v, Normal ?v1 = Normal v) \/ _ ]
      => left; exists v1; reflexivity
    | [ |- context [ _ \/ ?A = ?A ] ] => right; reflexivity
    end; auto.
Qed.

(** 
    for any statement c starting from the initial state s, if it 
    terminates in a state s' with respect to the relational semantics 
    eval_stmt, then the result state s' should be either a normal 
    state or a run time error. In relational semantics eval_stmt, 
    all statements that can go abnormal are excluded;
*)
Lemma eval_stmt_state : forall s c s',
        eval_stmt s c s' -> (* s' is either a normal state or a run time error *)
            (exists v, s' = Normal v) \/ s' = Run_Time_Error.
Proof.
    intros s c s' h.
    induction h;
    try match goal with
    | [ |- (exists v, Normal ?v1 = Normal v) \/ _ ] => left; exists v1; reflexivity
    | [ |- context [ _ \/ ?A = ?A ] ] => right; reflexivity
    end; auto.
Qed.

(** * Bisimulation Between Relational And Functional Semantics *)

(** bisimulation proof between f_eval_binexpr and eval_binexpr:
    - f_eval_bin_expr_correct
    - f_eval_bin_expr_complete
*)
Lemma f_eval_bin_expr_correct: forall op v1 v2 v,
    f_eval_bin_expr op v1 v2 = Normal v ->
    eval_bin_expr op v1 v2 v.
Proof.
    intros op v1 v2 v h1.
    destruct op;
    match goal with 
    |[|- eval_bin_expr Divide _ _ _] => idtac
    |[|- eval_bin_expr ?op _ _ _] =>
        destruct v1, v2;
        simpl in h1; inversion h1; subst;
        constructor; auto
    end.
    destruct v1, v2; simpl in h1; inversion h1.
    constructor.
    remember (Zeq_bool n0 0) as x.
    reflexivity.
Qed.

Lemma f_eval_bin_expr_complete: forall op v1 v2 v,
    eval_bin_expr op v1 v2 v ->
    f_eval_bin_expr op v1 v2 = Normal v.
Proof.
    intros op v1 v2 v h1.
    induction h1;
    rewrite <- H;
    simpl; auto.
Qed.

(** bisimulation proof between f_eval_unaryexpr and eval_unaryexpr: 
    - f_eval_unary_expr_correct
    - f_eval_unary_expr_complete
*)
Lemma f_eval_unary_expr_correct: forall op v v',
    f_eval_unary_expr op v = Normal v' ->
    eval_unary_expr op v v'.
Proof.
  intros op v v' heq.
  !destruct op ; simpl in heq.
  - destruct v; inversion heq; subst.
    constructor; auto.
  - destruct v;destruct v';simpl in *;try discriminate.
    injection heq.
    intro.
    subst.
    constructor 2.      
Qed.

Lemma f_eval_unary_expr_complete: forall op v v',
    eval_unary_expr op v v' ->
    f_eval_unary_expr op v = Normal v'.
Proof.
  intros op v v' h1.
  induction h1;simpl;subst;auto.
Qed.

(** ** Bisimulation between f_evalExp and evalExp for expression Semantics *)
(** a help lemma to prove the theorem: f_evalExp_correct *)
Lemma f_evalExp_correct1 : forall s e v,
                        f_evalExp s e = Normal v ->
                            evalExp s e (Normal v).
Proof.
  intros s e.
  !!(functional induction (f_evalExp s e); intros v0 h1; try inverts h1 as; subst).
  - constructor;
    reflexivity.
  - constructor;
    assumption.
  - specialize (IHr _ heqevalExp0).
    specialize (IHr0 _ heqevalExp).
    introv h.
    rewrite h.
    econstructor.
    + exact IHr.
    + exact IHr0.
    + apply f_do_check_correct.
      auto.
    + apply f_eval_bin_expr_correct; 
      auto.
  - specialize (IHr _ heqevalExp).
    introv h.
    rewrite h.
    econstructor. 
    + exact IHr.
    + destruct op. 
      * simpl in h. 
        destruct v; inversion h; subst.
        constructor; auto.
      * simpl in h. 
        destruct v; inversion h; subst.
        constructor; auto.
Qed.


(** another help lemma to prove the theorem: f_evalExp_correct *)
Lemma f_evalExp_correct2 : forall s e,
                        f_evalExp s e = Run_Time_Error ->
                            evalExp s e Run_Time_Error.
Proof.
    intros s e.
    (!! functional induction (f_evalExp s e)); intro h;inversion h;simpl. 
  - destruct op, v1, v2; simpl in h; inversion h.
  - specialize (f_evalExp_correct1 _ _ _ heqevalExp0); intros hz1.
    specialize (f_evalExp_correct1 _ _ _ heqevalExp); intros hz2.
    eapply eval_E_Binary_Operation3.
    apply hz1. apply hz2.
    apply f_do_check_correct; auto.
  - specialize (f_evalExp_correct1 _ _ _ heqevalExp); intros hz1.
    specialize (IHr0 heqevalExp_rte).
    eapply eval_E_Binary_Operation2 with v1; auto.
  - specialize (IHr heqevalExp_rte).
    constructor; assumption.
  - destruct op;
    destruct v; inversion h. 
  - specialize (IHr heqevalExp_rte).
    constructor; assumption.
Qed.

(** *** f_evalExp_correct *)
(** 
    for an expression e evaluated under the state s with respect to
    the functional semantics f_evalExp, whenever it returns a 
    normal value v or terminates in a run time error, 
    the relation between s, e and evaluation result should also be 
    satisfied with respect to the relational semantics 'evalExp';
*)
Theorem f_evalExp_correct : forall s e v,
                        (f_evalExp s e = Normal v ->
                            evalExp s e (Normal v)) /\
                        (f_evalExp s e = Run_Time_Error ->
                            evalExp s e Run_Time_Error).
Proof.
    split.
  - apply f_evalExp_correct1.
  - apply f_evalExp_correct2.
Qed.


(** *** f_evalExp_complete *)
(** 
   for any expression e, if it can be evaluated to a value v under
   state s with respect to the relational semantics 'evalExp', 
   then when we evalute e under the same state s in functional
   semantics 'f_evalExp', it should return the same result v;
*)
Theorem f_evalExp_complete : forall e s v,  
                        evalExp e s v -> 
                            (f_evalExp e s) = v.
Proof.
    intros e s v h.
    !induction h; simpl; !intros;
    repeat match goal with
    | h: fetchG _ _ = _  |- _ => progress rewrite h
    | h: f_evalExp _ _ = _ |- _ => progress rewrite h
    end;auto.
  - rewrite heqevalLiteral; reflexivity.
  - specialize (f_do_check_complete _ _ _ _ hdo_check); intros hz1.
    rewrite hz1.
    reflexivity.
  - !destruct v1; !destruct v2;
    !destruct op;
    !inversion heval_bin_expr; subst; simpl; auto.
    + (* overflow check for Plus *)
      !inversion hdo_check; !intros; subst.
      * rewrite heq; auto.
      * rm_false_hyp.
    + (* overflow check for Minus *)
      !inversion hdo_check;!intros; subst.
      * rewrite heq; auto.
      * rm_false_hyp.
    + (* overflow check for Multiply *)
      !inversion hdo_check;!intros; subst.
      * inversion heq; subst.
        rewrite H0; auto.
      * rm_false_hyp.
    + (* both division by zero check and overflow check *)
      !inversion hdo_check;!intros; subst.
      * inversion heq; subst.
        rewrite H0; auto.
      * rm_false_hyp.
  - destruct op.
    + !inversion heval_unary_expr.
      auto.
    + !inversion heval_unary_expr.
      auto.
Qed.






Ltac apply_inv :=
  try discriminate; try Rdiscriminate;
  match goal with
    | H:Normal _ = Normal _ |- _ => inversion H;clear H;subst 
    | H:update _ _ (Value _) = _ |- _ => rewrite H
    | H:updateG _ _ (Value _) = _ |- _ => rewrite H
    | H:f_eval_stmt _ _ _ = _ |- _ => rewrite H
    | H:f_evalExp _ _ = _ |- _ => rewrite H
    | H:f_eval_decl _ _ _ = _ |- _ => rewrite H
    | H:copyOut _ _ _ _ = _ |- _ => rewrite H
    | H:copyIn _ _ _ = _ |- _ => rewrite H
    | H:fetch _ _ = _ |- _ => rewrite H
    | H:fetchG _ _ = _ |- _ => rewrite H
    | H:split2 _ _ _ = _ |- _ => rewrite H
    | H:split1 _ _ _ = _ |- _ => rewrite H
    | H:cutUntil _ _ = _ |- _ => rewrite H
  end;subst;simpl;auto.

Ltac invle := match goal with
    | H: (S _ <= _)%nat |- _ => (inversion H; clear H; subst; simpl)
  end.

(** a help lemma to prove the theorem: 'f_eval_stmt_complete',
    it means that: for any statement c, starting from initial state s, 
    if it terminates in a normal state s' within k execution steps, 
    then for any k' greater and equal than k, it should also terminate 
    in the same state s';
*)
Lemma f_eval_stmt_fixpoint: forall k s c s', 
        f_eval_stmt k s c = Normal s' ->
        forall k':nat, (k <= k')%nat -> 
            f_eval_stmt k' s c = Normal s'.
Proof.
    intros k s c.
    rename_after (fun _ => functional induction (f_eval_stmt k s c); simpl; intros; subst; simpl; auto;
    repeat progress apply_inv) c.
  - invle; repeat apply_inv.
  - invle.
    + repeat apply_inv.
    + rewrite (IHr _ heqeval_stmt0);auto with arith.
  - invle; repeat apply_inv. rewrite (IHr _ heqeval_stmt);auto with arith.
  - invle; repeat apply_inv.
  - invle; repeat apply_inv. rewrite (IHr _ heqeval_stmt0); auto with arith.
  - invle; repeat apply_inv.
  - invle; repeat apply_inv.
    rewrite (IHr _ heqeval_stmt).
    repeat apply_inv.
    auto with arith.
Qed.

(** another help lemma to prove the theorem: 'f_eval_stmt_complete' *)
Lemma f_eval_stmt_fixpoint_E: forall k s p, 
        f_eval_stmt k s p = Run_Time_Error ->
        forall k':nat, (k <= k')%nat -> 
            f_eval_stmt k' s p = Run_Time_Error.
Proof.
    intros k s p.
    rename_after (fun _ => functional induction (f_eval_stmt k s p)
                  ; simpl; intros; subst; simpl; auto;
                  repeat progress apply_inv) p.
  - invle;
    apply_inv.
  - invle;
    repeat apply_inv.
    rewrite (f_eval_stmt_fixpoint _ _ _ _ heqeval_stmt0); auto with arith.
  - invle;
    repeat apply_inv.
    specialize (IHr heqeval_stmt). 
    rewrite IHr; auto with arith. 
  - invle; 
    repeat apply_inv.
    rewrite IHr; auto with arith.
  - invle;
    repeat apply_inv.
  - invle; 
    repeat apply_inv. 
    rewrite (f_eval_stmt_fixpoint _ _ _ _ heqeval_stmt0); auto with arith.
  - invle; 
    repeat apply_inv.
    rewrite (IHr heqeval_stmt); auto with arith.    
  - invle; 
    repeat apply_inv.   
  - invle; repeat apply_inv.
    rewrite (f_eval_stmt_fixpoint _ _ _ _ heqeval_stmt); auto with arith.
    rewrite heq0.
    assumption.
  - invle; repeat apply_inv.
    rewrite  (IHr heqeval_stmt m);auto with arith.
  - invle; repeat apply_inv.
  - invle; repeat apply_inv.
Qed.



Ltac rm_evalExp :=
  match goal with 
    | [ h: evalExp ?s ?b ?X, h': f_evalExp ?s ?b = ?X |- _ ] => clear h
    | [ h: evalExp ?s ?b ?X, h': ?X = f_evalExp ?s ?b |- _ ] => clear h; symmetry in h'
    | [ h: evalExp ?s ?b ?X |- _ ] => apply f_evalExp_complete in h
  end; auto.


Lemma copyIn_correct:
  forall s prm lexp prefx,
    copy_in s prm lexp = (Normal prefx) <->  Copy_in s prm lexp (Normal prefx).
Proof.
  intros s prm lexp.
  rename_after
    (fun _ =>
       functional induction copy_in s prm lexp;intros;split;simpl in *;intro heq
     ; try (inversion heq;subst;clear heq)
     ; repeat rm_evalExp
     ; try repeat progress match goal with (* Rewrite induction hyp if you can *)
                             | H: (forall _, ?X = _ <-> _)  |- _ =>
                               rewrite <- H in *
                           end
     ; try (now repeat progress
                first [ Rdiscriminate
                      | Rinversion copy_in;auto
                      | Rinversion f_evalExp;auto ])) lexp.
  - inversion_is_var heq0.
    econstructor 2.
    + apply IHr;auto.
    + assumption.

  - apply Copy_in_cons_in.
    + apply IHr.
      assumption.
    + assumption.
    + apply f_evalExp_correct1.
      assumption.
  - constructor 1.
Qed.



Lemma copy_in_correct2:
  forall s prm lexp,
    copy_in s prm lexp = Run_Time_Error <->  Copy_in s prm lexp Run_Time_Error.
Proof.
  intros s prm lexp.
  rename_after
    (fun _ => functional induction copy_in s prm lexp;intros;split;simpl in *;intro heq
     ; try (inversion heq;subst;clear heq)
     ; repeat try rm_evalExp
     ; try repeat progress (* Rewrite with induction hyp as much as we can *)
           match goal with
             | H: (?X = _ <-> _)  |- _ =>
               rewrite <- H in *
           end
     ; try (now repeat progress
                first [ Rdiscriminate
                      | Rinversion copy_in;auto
                      | Rinversion f_evalExp;auto ])) lexp.
  - inversion_is_var heq0.
    rewrite heq.
    econstructor;auto.
    rewrite <- IHr.
    assumption.
  - rewrite heq.
    apply Copy_in_cons_in_rte2 with (v:=v');auto.
    + rewrite <- IHr.
      assumption.
    + apply f_evalExp_correct1.
      assumption.
  - apply Copy_in_cons_in_rte1;auto.
    apply f_evalExp_correct2.
    assumption.
Qed.

Lemma Copy_out_stack_eq_length :
  forall prefx prm lexp s s',
    Copy_out prefx prm lexp s s'
    -> stack_eq_length s s'.
Proof.
  intros prefx prm lexp s s' H.
  induction H;auto.
  - apply stack_eq_length_refl.
    reflexivity.
  - transitivity  σ'.
    + eapply updateG_stack_eq_length;eauto.
    + assumption.
Qed.

Lemma Copy_out_length :
  forall prefx prm lexp s s',
    Copy_out prefx prm lexp s s'
    -> List.length s = List.length s'.
Proof.
  intros prefx prm lexp s s' H.
  induction H;auto.
  transitivity (List.length σ');auto.
  eapply updateG_length;eauto.
Qed.



Lemma copy_out_no_rte:
  forall prefx lprm lexp s,
    ~ copy_out prefx lprm lexp s = Run_Time_Error.
Proof.
  intros prefx lprm lexp s.
  functional induction copy_out prefx lprm lexp s;try assumption;try discriminate.
Qed.


Lemma copy_out_correct:
  forall prefx s (prm:list paramSpec) lexp x,
    copy_out prefx prm lexp s = Normal x <-> Copy_out prefx prm lexp s x.
Proof.
  intros prefx s prm lexp.
  rename_after
    (fun _ =>
       functional induction copy_out prefx prm lexp s;intros;split;simpl in *;intro heq
     ; try (now (inversion heq;subst;clear heq);auto;try now (econstructor;eauto))) lexp.
  - apply Copy_out_cons_out with (σ':=s') (v:=v)(id:=parameter_name prm);auto.
    apply IHr.
    assumption.
  - !inversion heq;!intros.
    + Rinversion fetch.
      Rinversion updateG. 
      apply IHr;assumption.
    + Rdiscriminate.
  - !inversion heq;!intros.
    + Rinversion fetch.
      Rdiscriminate.
    + Rdiscriminate.
  - !inversion heq; !intros.
    + Rdiscriminate.
    + Rdiscriminate.
  - !inversion heq; !intros.
    + contradiction.
    + Rdiscriminate.
  - constructor 3;auto.
    apply IHr.
    assumption.
  - !inversion heq;!intros.
    + Rdiscriminate.
    + apply IHr.
      assumption.
  - !inversion heq;!intros.
    + rewrite heq0 in y.
      contradiction.
    + rewrite heq0 in y.
      contradiction.
Qed.





Lemma eval_decl_store_length:
  forall s sto s' decl,
    eval_decl s sto decl s'
    -> forall st, s' = Normal st
                  -> exists prfx, st = prfx ++ sto.
Proof.
  intros s sto s' decl h.
  !induction h;intros st heq';!inversion heq';subst.
  - exists ((object_name d, Value v)::nil).
    simpl.
    reflexivity.
  - exists ((object_name d, Undefined)::nil);simpl.
    reflexivity.
  - destruct (IHh2 st).
    { reflexivity. }
    destruct (IHh1 s').
    { reflexivity. }
    subst.
    exists (x ++ x0).
    apply app_assoc.
  - exists ((procedure_name pbody, Procedure pbody)::nil);simpl.
    reflexivity.
Qed.


Lemma eval_stmt_store_length:
  forall s s' stm,    
    eval_stmt s stm s'
    -> forall st, s' = Normal st
                  -> stack_eq_length s st.
Proof.
  intros s s' stm H.
  (*    !! (induction H;intros st heq';inversion heq';clear heq'; subst;auto). *)
  (!!induction H; intros st heq'; inversion heq';clear heq'; subst;auto).
  - apply updateG_stack_eq_length in hupdateG.
    assumption.
  - apply stack_eq_length_trans with s1.
    + apply IHeval_stmt1.
      reflexivity.
    + apply IHeval_stmt2.
      reflexivity.
  - apply stack_eq_length_refl.
    reflexivity.
  - apply stack_eq_length_trans with s1.
    + apply IHeval_stmt1.
      reflexivity.
    + apply IHeval_stmt2.
      reflexivity.
  - apply stack_eq_length_refl.
    reflexivity.
  - generalize (cutUntil_def _ _ _ _ hcutUntil).
    intros hcutin.
    subst.
    specialize (IHeval_stmt ((slocal ++ prefix') :: s') eq_refl).
    !inversion IHeval_stmt;!intros.
    rewrite hstack_eq_length.
    eapply Copy_out_stack_eq_length;eauto.
Qed.

Lemma f_eval_decl_correct :
  forall s sto d s',
    f_eval_decl s sto d = Normal s' ->
    eval_decl s sto d (Normal s').
Proof.
  intros s sto d.
  functional induction f_eval_decl s sto d;simpl;intros;try discriminate
  ; try match goal with
        | H: Normal _ = Normal _ |- _ =>
          inversion H;subst;clear H
      end;try now( (econstructor;eauto;try apply f_evalExp_correct1;auto)).
  - rewrite H in y.
    contradiction.
Qed.

Lemma f_eval_decl_correct2 :
  forall s sto d,
    f_eval_decl s sto d = Run_Time_Error ->
    eval_decl s sto d Run_Time_Error.
Proof.
  intros s sto d.
  functional induction f_eval_decl s sto d;simpl;intros;try discriminate;
  try match goal with
        | H: Normal _ = Run_Time_Error |- _ =>
          inversion H;subst;clear H
      end;try now( (econstructor;eauto);try apply f_evalExp_correct2;auto).
  
  eapply eval_decl_Seq_err2 with s';auto.
  apply f_eval_decl_correct.
  assumption.
Qed.

Ltac use_determinism :=
  match goal with
    | H : ?X = ?X |- _ => clear H
    | H: None = ?y, H': ?y = Some ?z |- _ => rewrite H' in H; !invclear H
    | H: Some ?z = ?y, H': ?y = None |- _ => rewrite H' in H; !invclear H
    | H: Some ?x = ?y, H': ?y = Some ?z |- _ => rewrite H' in H; !invclear H
    | H : evalExp ?s ?e ?X,
          H': f_evalExp ?s ?e = ?Y |- _ => rewrite (f_evalExp_complete s e X H) in H'
    | H:  evalExp ?s ?e ?X,
          H': evalExp ?s ?e ?Y |- _ => apply (f_evalExp_complete s e X) in H
         ;apply (f_evalExp_complete s e) in H'
    | H : f_evalExp ?s ?e = ?X,
          H': f_evalExp ?s ?e = ?Y |- _ => rewrite H in H'; !invclear H'
    | H : (Normal ?v) = (Normal ?v') |- _ => !invclear H
  end.

Ltac crush := repeat progress use_determinism;try reflexivity;try discriminate.


Lemma f_eval_decl_complete :
  forall d sto s s',
    eval_decl s sto d s' ->
    f_eval_decl s sto d = s'.
Proof.
  intros d sto s.
  (!!functional induction f_eval_decl s sto d);simpl;!intros;try discriminate;crush;
  try now (!inversion heval_decl;!intros;crush).
  - !inversion heval_decl;!intros.
    + apply IHr in heval_decl1.
      Rinversion f_eval_decl.
    + apply IHr in heval_decl0.
      Rinversion f_eval_decl.
    + apply IHr in heval_decl1.
      Rinversion f_eval_decl.
  - !inversion heval_decl;!intros.
    + apply IHr in heval_decl1.
      Rinversion f_eval_decl.
    + apply IHr in heval_decl0.
      assumption.
    + apply IHr in heval_decl1.
      rewrite heval_decl1 in y.
      contradiction.
Qed.


(** ** Bisimulation between f_eval_stmt and eval_stmt for statement semantics *)


Ltac rm_f_evalExp :=
  match goal with 
    | [ h: f_evalExp ?s ?b = Run_Time_Error |- _ ] => 
      specialize (f_evalExp_correct2 _ _ h);
        !intros
    | [ h: f_evalExp ?s ?b = Normal ?v |- _ ] => 
      specialize (f_evalExp_correct1 _ _ _ h);
        !intros
  end; auto.



(** a help lemma to prove the theorem: 'f_eval_stmt_complete' *)
Lemma f_eval_stmt_correct1 : forall k s p s',
        f_eval_stmt k s p = Normal s' ->
          eval_stmt s p (Normal s').
Proof.
    intros k s p.
    !!(functional induction (f_eval_stmt k s p);
       intros; try inversion H; subst).
  - (* Assign *)
    econstructor.
    rm_f_evalExp.
    apply hevalExp.
    assumption.
  - (* S_Sequence *)
    specialize (IHr _ heqeval_stmt1).
    specialize (IHr0 _ heqeval_stmt).
    econstructor.
    apply IHr.
    apply_inv.
  - (* If_True *)
    specialize (IHr _ heqeval_stmt).
    econstructor.
    rm_f_evalExp. 
    apply_inv.
  - (* If_False *)
    eapply eval_If_False.
    rm_f_evalExp.
  - (* While_True *)
    specialize (IHr _ heqeval_stmt1).
    specialize (IHr0 _ heqeval_stmt).
    econstructor.
    rm_f_evalExp.
    apply IHr. 
    apply_inv.
  - (* While_False *)
    eapply eval_While_False.
    rm_f_evalExp.
  - (* S_ProcCall *)
    clear heq0.
    (* cleaning by going to inductive defs *)
    apply split1_correct in heq1.
    destruct heq1 as [hsplit1 hsplit2].
    rewrite heq.
    subst.
    apply f_eval_decl_correct in heqeval_decl.    
    apply IHr in heqeval_stmt.
    apply copy_in_correct in heq3.
    apply copy_out_correct in heq.
    (* ******* *)
    eapply eval_S_Proc with (s':=s') (prefix':=prefx')(prefix:=prefx)(slocal:=slocal);eauto.
    + apply cutUntil_complete1.
      assumption.
    + eapply eval_decl_store_length with (st:=s2) in heqeval_decl;auto.
      destruct heqeval_decl as [slocal' ?].
      subst.
      apply eval_stmt_store_length with (st:=((slocal ++ prefx') :: s')) in heqeval_stmt;auto.
      !invclear heqeval_stmt.
      rewrite <- heq0 in hsplit1.
      setoid_rewrite app_length in heq0.
      setoid_rewrite app_length in hsplit1.
      omega.
Qed.


Ltac rm_f_eval_stmt :=
    match goal with 
    | [ h: f_eval_stmt ?k ?s ?c = Normal ?s1 |- _ ] => 
        specialize (f_eval_stmt_correct1 _ _ _ _ h);
        !intros
    end; auto.

(** a help lemma to prove the theorem: 'f_eval_stmt_complete' *)
Lemma f_eval_stmt_correct2 : forall k s p,
        f_eval_stmt k s p = Run_Time_Error ->
          eval_stmt s p Run_Time_Error.
Proof.
    intros k s p.
    !!(functional induction (f_eval_stmt k s p);intros;try discriminate).
(*     !!(functional induction (f_eval_stmt k s p)); intros H ; try inversion H; subst. *)
  - (* Assign *)
    econstructor.
    rm_f_evalExp.
  - (* S_Sequence*)
    eapply eval_S_Sequence2.
    + rm_f_eval_stmt.
      eauto.
    + apply IHr0.
      assumption.
  - specialize (IHr heqeval_stmt).
    econstructor.
    assumption.    
  - (* C_If *)
    specialize (IHr heqeval_stmt).
    eapply eval_S_If_True.
    rm_f_evalExp.
    assumption.
  - eapply eval_S_If .
    rm_f_evalExp.
  (* S_While_Loop *)
  - eapply eval_S_While_Loop_True2.
    + apply f_evalExp_correct1.
      assumption.
    + rm_f_eval_stmt.
      eauto.
    + apply IHr0.
      assumption.
  - eapply eval_S_While_Loop_True1;auto.
    rm_f_evalExp.

  - (* S_While_Loop *)
    apply eval_S_While_Loop.
    rm_f_evalExp.
  - elim (copy_out_no_rte _ _ _ _ heq).
  - apply eval_S_Proc_rtebody with 
    (prefix:=prefx)
      (s2:=s2)
      (s:=s_called)
      (s_forget:=s_forget)
      (pb:=pb);auto. 
    + apply copy_in_correct.
      assumption.
    + apply cutUntil_complete1.
      assumption.
    + apply f_eval_decl_correct.
      assumption.
  - apply eval_S_Proc_rtedecl
    with (prefix:=prefx) (pb:=pb) (s_forget:=s_forget) (s:=s_called)
    ;eauto.
    + apply copy_in_correct.
      assumption.
    + apply cutUntil_complete1.
      assumption.
    + eapply f_eval_decl_correct2.
      assumption.
  - eapply eval_S_Proc_rteargs with pb;auto.
    apply copy_in_correct2.
    assumption.
Qed.
    
    

Ltac rm_f_eval :=
    match goal with 
    | [ h: f_evalExp ?s ?b = Run_Time_Error |- _ ] => specialize (f_evalExp_correct2 _ _ h); intros hz1
    | [ h: f_evalExp ?s ?b = Normal ?v |- _ ] => specialize (f_evalExp_correct1 _ _ _ h); intros hz1   
    | [ h: f_eval_stmt ?k ?s ?c = Run_Time_Error |- _ ] => specialize (f_eval_stmt_correct2 _ _ _ h); intros hz1
    | [ h: f_eval_stmt ?k ?s ?c = Normal ?s1 |- _ ] => specialize (f_eval_stmt_correct1 _ _ _ _ h); intros hz1
    end; auto.

(** *** f_eval_stmt_correct *)
(** 
   for any statement c starting from initial state s, if it returns 
   a normal state s' or terminates in a run time error within k steps
   with respect to the functional semantics 'f_eval_stmt', then the 
   relation between s, c and the resulting state should also be 
   satisfied with respect to the relational semantics 'eval_stmt';
*)
Theorem f_eval_stmt_correct : forall k s c s',
        (f_eval_stmt k s c = Normal s' ->
          eval_stmt s c (Normal s')) /\ 
        (f_eval_stmt k s c = Run_Time_Error ->
          eval_stmt s c Run_Time_Error).
Proof.
    intros.
    split; intros;
    rm_f_eval.
Qed.

(** *** f_eval_stmt_complete *)
(** 
   the reverse direction is also satisfied: for any statement c, 
   whenever it's executed starting from initial state s and return 
   a new state s' with regard to the relational semantics 'eval_stmt', 
   then there should exist a constant k that statement c starting from 
   s will terminate in state s' within k steps with respect to the 
   functional semantics 'f_eval_stmt';
*)

Ltac apply_rewrite := 
    match goal with
    | h: evalExp ?s ?e ?s' |- _ => 
        rewrite (f_evalExp_complete _ _ _ h)
    | h: update _ _ _ = _ |- _ => rewrite h
    | h: updateG _ _ _ = _ |- _ => rewrite h
    | h: f_eval_stmt _ _ _ = _ |- _ => rewrite h
    | h: f_evalExp _ _ = _ |- _ => rewrite h
    | h: fetch _ _ = _ |- _ => rewrite h
    | h: fetchG _ _ = _ |- _ => rewrite h
    | h: copy_in _ _ _ = _ |- _ => rewrite h
    | h: Copy_in _ _ _ Run_Time_Error |- _ => rewrite <- copy_in_correct2 in h;rewrite h
    | h: Copy_in _ _ _ (Normal _) |- _ => rewrite <- copy_in_correct in h;rewrite h
    | h: cutUntil _ _ = Some(_, _) |- _ => rewrite h
    | h: cutUntil _ _ = None |- _ => rewrite h
    | h: cutUntil _ _ _ _ |- _ => apply cutUntil_correct in h;rewrite h
    end; auto.


Ltac kgreater :=
  repeat
    match goal with
      | h:f_eval_stmt ?k ?s ?p = Normal ?s' |- context [f_eval_stmt (?k + _) ?s ?p] =>
        rewrite (@f_eval_stmt_fixpoint _ _ _ _ h);auto with arith
      | h:f_eval_stmt ?k ?s ?p = Normal ?s' |- context [f_eval_stmt (_ + ?k) ?s ?p] =>
        rewrite (@f_eval_stmt_fixpoint _ _ _ _ h);auto with arith
      | h:f_eval_stmt ?k ?s ?p = Run_Time_Error |- context [f_eval_stmt (?k + _) ?s ?p] =>
        rewrite (@f_eval_stmt_fixpoint_E _ _ _ h);auto with arith
      | h:f_eval_stmt ?k ?s ?p = Run_Time_Error |- context [f_eval_stmt (_ + ?k) ?s ?p] =>
        rewrite (@f_eval_stmt_fixpoint_E _ _ _ h);auto with arith
         end.



Theorem f_eval_stmt_complete : forall s c s',
        eval_stmt s c s' -> (* s' is either a normal state or a run time error *)
            exists k, f_eval_stmt k s c = s'.
Proof. 
  !intros.
  !induction heval_stmt;
  try match goal with
  [ h: evalExp ?s ?e Run_Time_Error |- exists k, _ = Run_Time_Error] => 
          exists 1%nat; simpl;
          rewrite (f_evalEx_complete _ _ _ h);
          reflexivity
  end.
  (* 1. Assign *)
  - exists 1%nat; simpl.
    repeat apply_rewrite.
  (* 2. S_Sequence *)
  - destrEx.
    exists (S k); simpl.
    apply_rewrite.
  - destrEx.
    exists (S (k0+k)); simpl.
    kgreater.
    specialize (eval_stmt_state _ _ _ heval_stmt); intros hz1.
    destruct hz1 as [hz2 | hz2]; try rm_exists; subst;
    kgreater.
  (* 3. S_If *)
  - destrEx.
    exists (S k); simpl.
    apply_rewrite.
  - exists 1%nat; simpl.
    apply_rewrite.
  (* 4. S_While_Loop *)
  - destrEx.
    exists (S k); simpl.
    repeat apply_rewrite.
  - destrEx.
    exists (S (k0+k)); simpl.
    apply_rewrite.
    kgreater.
    specialize (eval_stmt_state _ _ _ heval_stmt); intros hz1.
    destruct hz1 as [hz2 | hz2]; try rm_exists; subst;
    kgreater.
  - exists 1%nat; simpl.
    apply_rewrite.
  - exists 1%nat; simpl.
    repeat progress apply_rewrite.
  - exists 1%nat; simpl.
    subst.
    repeat apply_rewrite.
    apply f_eval_decl_complete in heval_decl.
    rewrite heval_decl.
    reflexivity.
  - destruct IHheval_stmt as [k IH].
    exists (S k).
    simpl.
    repeat apply_rewrite.
    apply f_eval_decl_complete in heval_decl.
    rewrite heval_decl.
    apply_rewrite.
  - destruct IHheval_stmt as [k IH].
    exists (S k).
    simpl.
    subst.
    repeat apply_rewrite.
    apply f_eval_decl_complete in heval_decl.
    rewrite heval_decl.
    repeat apply_rewrite.
    repeat setoid_rewrite app_length.
    rewrite heq.
    assert (heq':Datatypes.length slocal + Datatypes.length prefix' -
        Datatypes.length prefix' = Datatypes.length slocal) by omega.
    rewrite heq'.
    rewrite split1_complete with (l2:=prefix') (l1:=slocal).
    + apply copy_out_correct.
      assumption.
    + reflexivity.
    + reflexivity.
Qed.

(**********************************************************************)
(**********************************************************************)

(** * Subprogram Semantics *)

(** In the current SPARK subset, there is no procedure call, 
    so right now we only define the semantics for the main procedure.
    And it can be used to test the tool chain from SPARK source code 
    to Coq evaluation; Later, we will add the procedure call and 
    modify the following procedure semantics;
*)

(** all declared variables in the same procedure should have unique 
    names; 
*)

(** relational (eval_decl) and functional (f_eval_decl) semantics for 
    variable declaration;
*)

(** for any initial state s, after executing the declaration d, 
    it either returns a normal state s' or a run time error;
    (for any variable declaration, if its initialization expression 
     fails the run time checks, for example division by zero or overflow, 
     then it returns an exception)
*)

Lemma eval_decl_state : forall s sto d s',
        eval_decl s sto d s' -> (* s' is either a normal state or a run time error *)
            (exists t, s' = Normal t) \/ s' = Run_Time_Error.
Proof.
    intros s sto d s' h.
    induction h;
    try match goal with
    | [ |- (exists t, Normal ?t1 = Normal t) \/ _ ] => left; exists t1; reflexivity
    | [ |- context [ _ \/ ?A = ?A ] ] => right; reflexivity
    end; auto.
Qed.


(** f_eval_decl completeness and correctness proofs *)

(** bisimulation proof between f_eval_decl and eval_decl: 
    - f_eval_decl_correct
    - f_eval_decl_complete
*)

Lemma f_eval_decl_correct_: forall d s sto s',
    (f_eval_decl s sto d = (Normal s') -> eval_decl s sto d (Normal s')) /\
    (f_eval_decl s sto d = Run_Time_Error -> eval_decl s sto d Run_Time_Error).
Proof.
    intros d s sto.
    intros s'.
    split;intro h.
    - apply f_eval_decl_correct.
      assumption.
    - apply f_eval_decl_correct2.
      assumption.
Qed.


(* = = = = = = Subprogram Body = = = = = =  *)
(** relational and functional semantics for procedure body; *)
(* Is this still needed for global procedures? probably not. *)
(* main procedure has no argument, so we give the nil store as
   parameter store *)
Inductive eval_proc: stack -> procedure_declaration -> Return stack -> Prop :=
    | eval_Proc_E: forall f s,
        eval_decl s nil (procedure_declarative_part f) Run_Time_Error ->
        eval_proc s f Run_Time_Error
    | eval_Proc: forall f s1 s2 s3,
        eval_decl s1 nil (procedure_declarative_part f) (Normal s2) ->
        eval_stmt (s2::s1) (procedure_statements f) s3 ->
        eval_proc s1 f s3.

Function f_eval_proc k (s: stack) (f: procedure_declaration): Return stack :=
    match (f_eval_decl s nil (procedure_declarative_part f)) with
    | Normal s' => f_eval_stmt k (s'::s) (procedure_statements f)
    | Run_Time_Error => Run_Time_Erro
    | Abnormal => Abnormal
    | Unterminated => Unterminated
    end.


(** ** Main Procedure Evaluation Without Parameters *)

(** relational and functional semantics for main procedure; *)

Inductive eval_subprogram: stack -> subprogram -> Return stack -> Prop :=
    | eval_Procedure: forall s s' n f,
        eval_proc s f s' ->
        eval_subprogram s (Global_Procedure n f) s'.

Function f_eval_subprogram k (s: stack) (f: subprogram): Return stack := 
    match f with 
    | Global_Procedure n f' => f_eval_proc k s f'
    end.

(** ** Bisimulation Between Relational And Functional Semantics For Main Procedure *)

(** *** f_eval_subprogram_correct *)
Theorem f_eval_subprogram_correct: forall k s f s',
    (f_eval_subprogram k s f = Normal s' -> 
        eval_subprogram s f (Normal s')) /\
    (f_eval_subprogram k s f = Run_Time_Error -> 
        eval_subprogram s f Run_Time_Error).
Proof.
    intros.
    !! (split; intros;
        destruct f;
        simpl in H;
        constructor;
        unfold f_eval_proc in H ;
        remember (f_eval_decl s nil (procedure_declarative_part p)) as x;
        symmetry in Heqx).
  - (* normal state *)
    destruct x; !invclear heq.
    econstructor.
    + apply f_eval_decl_correct.
      apply heqeval_decl.
    + rewrite heqeval_stmt.
      apply f_eval_stmt_correct in heqeval_stmt;assumption.
  - (* run time error *)
    destruct x; !invclear heq; subst.
    + econstructor.
       * apply f_eval_decl_correct in heqeval_decl.
         apply heqeval_decl.
       * rewrite heqeval_stmt.
         apply f_eval_stmt_correct in heqeval_stmt; assumption.
    + econstructor.
      apply f_eval_decl_correct2 in heqeval_decl; assumption.
Qed.

(** *** f_eval_subprogram_complete *)
Theorem f_eval_subprogram_complete: forall s f s',
    eval_subprogram s f s' ->
    exists k, f_eval_subprogram k s f = s'.
Proof.
  intros s f s' h.
  unfold f_eval_subprogram.
  unfold f_eval_proc.
  !invclear h.
  !invclear H;simpl.
  - exists 0.
    apply f_eval_decl_complete in heval_decl.
    rewrite heval_decl.
    reflexivity.
  - apply f_eval_decl_complete in heval_decl.
    rewrite heval_decl.
    apply f_eval_stmt_complete in heval_stmt.
    assumption.
Qed.

(** * Replaying examples using the correctness of functional semantics *)
Module ExampleProcedures2.
(* EXAMPLE 1, v102 is a variable in the scope.
------------------------
procedure P2 () is
  V4 : TYPE5 := 34;
begin
  V102 := 56;
end 
-----------------------
*)
Definition proc1:procedure_declaration := (mkprocedure_declaration
           1 2 nil nil
             (D_Object_declaration
                {|
                  declaration_astnum := 3;
                  object_name := 4;
                  object_nominal_subtype :=  5;
                  initialization_exp := Some (E_Literal 6 (Integer_Literal(34)))
                |}
             )
             (Assign 12 102 (E_Literal 8 (Integer_Literal(56))))).

Definition s1:store := (101,Procedure proc1) :: (102, Value (Int(77))) :: nil.

Definition s2:store := (101,Procedure proc1) :: (102, Value (Int(56)))  :: nil.

Eval vm_compute in f_eval_stmt 200 (s1::nil) (S_ProcCall 13 101 nil).

Lemma essai: eval_stmt (s1::nil) (S_ProcCall 13 101 nil) (Normal (s2::nil)).
Proof.
  apply f_eval_stmt_correct1 with (k:=2).
  compute.f_eval_proc k s f'
    end.

(** ** Bisimulation Between Relational And Functional Semantics For Main Procedure *)

(** *** f_eval_subprogram_correct *)
Theorem f_eval_subprogram_correct: forall k s f s',
    (f_eval_subprogram k s f = Normal s' -> 
        eval_subprogram s f (Normal s')) /\
    (f_eval_subprogram k s f = Run_Time_Error -> 
        eval_subprogram s f Run_Time_Error).
Proof.
    intros.
    !! (split; intros;
        destruct f;
        simpl in H;
        constructor;
        unfold f_eval_proc in H ;
        remember (f_eval_decl s nil (procedure_declarative_part p)) as x;
        symmetry in Heqx).
  - (* normal state *)
    destruct x; !invclear heq.
    econstructor.
    + apply f_eval_decl_correct.
      apply heqeval_decl.
    + rewrite heqeval_stmt.
      apply f_eval_stmt_correct in heqeval_stmt;assumption.
  - (* run time error *)
    destruct x; !invclear heq; subst.
    + econstructor.
       * apply f_eval_decl_correct in heqeval_decl.
         apply heqeval_decl.
       * rewrite heqeval_stmt.
         apply f_eval_stmt_correct in heqeval_stmt; assumption.
    + econstructor.
      apply f_eval_decl_correct2 in heqeval_decl; assumption.
Qed.

(** *** f_eval_subprogram_complete *)
Theorem f_eval_subprogram_complete: forall s f s',
    eval_subprogram s f s' ->
    exists k, f_eval_subprogram k s f = s'.
Proof.
  intros s f s' h.
  unfold f_eval_subprogram.
  unfold f_eval_proc.
  !invclear h.
  !invclear H;simpl.
  - exists 0.
    apply f_eval_decl_complete in heval_decl.
    rewrite heval_decl.
    reflexivity.
  - apply f_eval_decl_complete in heval_decl.
    rewrite heval_decl.
    apply f_eval_stmt_complete in heval_stmt.
    assumption.
Qed.


  reflexivity.
Qed.



(* v102 is a variable in the scope.
procedure P2 () is
  V4 : TYPE5 := 34;
  V5 : TYPE5 := 37;
begin
  V5 := V4 + V5;
  V102 := V5*2;
end 
*)
Definition proc2:procedure_declaration := (mkprocedure_declaration
           1 2 nil nil
             (D_Sequence
                (D_Object_declaration
                   {|
                     declaration_astnum := 3;
                     object_name := 4;
                     object_nominal_subtype :=  5;
                     initialization_exp := Some (E_Literal 6 (Integer_Literal(34)))
                   |}
                )
                (D_Object_declaration
                   {|
                     declaration_astnum := 4;
                     object_name := 5;
                     object_nominal_subtype :=  5;
                     initialization_exp := Some (E_Literal 6 (Integer_Literal(37)))
                   |}
                )
             )
             (S_Sequence 13
                (Assign 14 5
                              (E_Binary_Operation 9 Plus
                                                  (Identifier 10 5)
                                                  (Identifier 10 4)))
                (Assign
                   12
                   102
                   (E_Binary_Operation 9 Multiply
                                       (Identifier 10 5)
                                       (E_Literal 8 (Integer_Literal(2))))))).

Definition s3:store := (101,Procedure proc2) :: (102, Value (Int(77))) :: nil.

Definition s4:store := (101,Procedure proc2) :: (102, Value (Int(142)))  :: nil.


Lemma essai2: eval_stmt (s3::nil) (S_ProcCall 13 101 nil) (Normal (s4::nil)).
Proof.
  apply f_eval_stmt_correct1 with (k:=200).
  vm_compute.
  reflexivity.
Qed.


End ExampleProcedures2.
(* END EXAMPLE *)

**********************************************************************************************************)
