(** 
_AUTHOR_

<<
Zhi Zhang
Department of Computer and Information Sciences
Kansas State University
zhangzhi@ksu.edu
>>
*)

Require Export rt.
Require Export ast_rt.
Require Export ast_util.
Require Export eval.

Import STACK.

(** * Run-Time Check Evaluation + RT *)
(** do run time checks according to the run-time check decorations  *)
(*
Inductive do_flagged_check_on_binop: check_flag -> binary_operator -> value -> value -> Ret value -> Prop :=
    | OverflowCheckBinop: forall op v1 v2 v v',
        op = Plus \/ op = Minus \/ op = Multiply \/ op = Divide ->
        Math.binary_operation op v1 v2 = Some (Int v) ->
        overflowCheck v v' ->
        do_flagged_check_on_binop OverflowCheck op v1 v2 v'
    | DivCheckBinop: forall op v1 v2 v,
        op = Divide \/ op = Modulus ->
        divCheck op v1 v2 v ->
        do_flagged_check_on_binop DivCheck op (Int v1) (Int v2) v.

Inductive do_flagged_check_on_unop: check_flag -> unary_operator -> value -> Ret value -> Prop :=
    | OverflowCheckUnop: forall v v' v'',
        Math.unary_minus v = Some (Int v') ->
        overflowCheck v' v'' ->
        do_flagged_check_on_unop OverflowCheck Unary_Minus v v''.

Inductive do_flagged_checks_on_binop: check_flags -> binary_operator -> value -> value -> Ret value -> Prop :=
    | Do_Check_Binop_Nil: forall op v1 v2 v,
        Math.binary_operation op v1 v2 = Some v ->
        do_flagged_checks_on_binop nil op v1 v2 (OK v)
    | Do_Checks_Binop_RTE: forall ck op v1 v2 msg cks,
        do_flagged_check_on_binop ck op v1 v2 (RTE msg) ->
        do_flagged_checks_on_binop (ck :: cks) op v1 v2 (RTE msg)
    | Do_Checks_Binop: forall ck op v1 v2 v cks v',
        do_flagged_check_on_binop ck op v1 v2 (OK v) ->
        do_flagged_checks_on_binop cks op v1 v2 v' ->
        do_flagged_checks_on_binop (ck :: cks) op v1 v2 v'.

Inductive do_flagged_checks_on_unop: check_flags -> unary_operator -> value -> Ret value -> Prop :=
    | Do_Check_Unop_Nil: forall op v v',
        Math.unary_operation op v = Some v' ->
        do_flagged_checks_on_unop nil op v (OK v')
    | Do_Checks_Unop_RTE: forall ck op v msg cks,
        do_flagged_check_on_unop ck op v (RTE msg) ->
        do_flagged_checks_on_unop (ck :: cks) op v (RTE msg)
    | Do_Checks_Unop: forall ck op v v' cks v'',
        do_flagged_check_on_unop ck op v (OK v') ->
        do_flagged_checks_on_unop cks op v v'' ->
        do_flagged_checks_on_unop (ck :: cks) op v v''.
*)
Inductive evalBinOpRT: check_flag -> binary_operator -> value -> value -> Ret value -> Prop :=
    | OverflowCheckBinop: forall op v1 v2 v v',
        op = Plus \/ op = Minus \/ op = Multiply \/ op = Divide ->
        Math.binary_operation op v1 v2 = Some (Int v) ->
        overflowCheck v v' ->
        evalBinOpRT OverflowCheck op v1 v2 v'
    | DivCheckBinop: forall op v1 v2 v,
        op = Divide \/ op = Modulus ->
        divCheck op v1 v2 v ->
        evalBinOpRT DivCheck op (Int v1) (Int v2) v.

Inductive evalUnOpRT: check_flag -> unary_operator -> value -> Ret value -> Prop :=
    | OverflowCheckUnop: forall v v' v'',
        Math.unary_minus v = Some (Int v') ->
        overflowCheck v' v'' ->
        evalUnOpRT OverflowCheck Unary_Minus v v''.

(** ** Run-Time Check for Binary Operator + RT *)
Inductive evalBinOpRTS: check_flags -> binary_operator -> value -> value -> Ret value -> Prop :=
    | CheckBinOpNil: forall op v1 v2 v,
        Math.binary_operation op v1 v2 = Some v ->
        evalBinOpRTS nil op v1 v2 (OK v)
    | ChecksBinOpRTE: forall ck op v1 v2 msg cks,
        evalBinOpRT ck op v1 v2 (RTE msg) ->
        evalBinOpRTS (ck :: cks) op v1 v2 (RTE msg)
    | ChecksBinOp: forall ck op v1 v2 v cks v',
        evalBinOpRT ck op v1 v2 (OK v) ->
        evalBinOpRTS cks op v1 v2 v' ->
        evalBinOpRTS (ck :: cks) op v1 v2 v'.

(** ** Run-Time Check for Unary Operator + RT *)
Inductive evalUnOpRTS: check_flags -> unary_operator -> value -> Ret value -> Prop :=
    | Do_Check_Unop_Nil: forall op v v',
        Math.unary_operation op v = Some v' ->
        evalUnOpRTS nil op v (OK v')
    | Do_Checks_Unop_RTE: forall ck op v msg cks,
        evalUnOpRT ck op v (RTE msg) ->
        evalUnOpRTS (ck :: cks) op v (RTE msg)
    | Do_Checks_Unop: forall ck op v v' cks v'',
        evalUnOpRT ck op v (OK v') ->
        evalUnOpRTS cks op v v'' ->
        evalUnOpRTS (ck :: cks) op v v''.

Inductive overflowChecks: check_flags -> Z -> Ret value -> Prop :=
    | OverflowCheck_Nil: forall v, 
        overflowChecks nil v (OK (Int v))
    | OverflowCheck_List: forall v v',
        overflowCheck v v' ->
        overflowChecks (OverflowCheck :: nil) v v'.

Inductive rangeChecks: check_flags -> Z -> Z -> Z -> Ret value -> Prop :=
    | RangeCheck_Nil: forall v l u,
        rangeChecks nil v l u (OK (Int v))
    | RangeCheck_List: forall v l u v',
        rangeCheck v l u v' ->
        rangeChecks (RangeCheck :: nil) v l u v'.


(** * Relational Semantics *)

(** ** Evaluation of Literal + RT *)

Inductive evalLiteralRT: check_flags -> literal -> Ret value -> Prop :=
    | EvalLiteralRT_Bool: forall cks v,
        evalLiteralRT cks (Boolean_Literal v) (OK (Bool v))
    | EvalLiteralRT_Int: forall cks v v',
        overflowChecks cks v v' -> 
        evalLiteralRT cks (Integer_Literal v) v'.

(** ** Evaluation of Expression + RT *)
(**
    for binary expression and unary expression, if a run-time error 
    is detected in any of its child expressions, then Ret a run-time
    error; for binary expression (e1 op e2), if both e1 and e2 
    are evaluated to some OK value, then run-time checks are
    performed according to the checking rules specified for the 
    operator 'op', whenever the check fails, a run-time error is 
    detected and the program is terminated, otherwise, OK binary 
    operation result is Reted;

   - in name evaluation evalNameRT, the check flags for name are all nil, e.g.
     (IndexedComponentRT n x_n x e nil), because if there is a
     RangeCheck on the name expression, this range check should be enforced
     by the context where the name expression appears, that's why it's invisible 
     during the evaluation of name expression;

     take the assignment (y := x) as an example, if y is a variable of integer 
     subtype, and x is a variable of integer, then there should be a RangeCheck
     flag on the right side (x) of the assignment; during the evaluation of the 
     assignment, first evaluate the value of x, and then do the range check on the
     value of x against the target subtype range of y, but the RangeCheck should
     be invisible when evaluate the value of x even though the RangeCheck is set
     on the variable x, this range check should be enforced at the assignment level; 
     that's why in name evaluation evalNameRT, the check flags for name are all nil;
*)

Inductive evalExpRT: symTabRT -> state -> expRT -> Ret value -> Prop :=
    | EvalLiteralRT: forall l v st s n in_cks ex_cks,
        evalLiteralRT in_cks l v ->
        evalExpRT st s (LiteralRT n l in_cks ex_cks) v
    | EvalNameRT: forall st s nm v n,
        evalNameRT st s nm v ->
        evalExpRT st s (NameRT n nm) v
    | EvalBinOpRTE1_RTE: forall st s e1 msg n op e2 in_cks ex_cks,
        evalExpRT st s e1 (RTE msg) ->
        evalExpRT st s (BinOpRT n op e1 e2 in_cks ex_cks) (RTE msg)
    | EvalBinOpRTE2_RTE: forall st s e1 v1 e2 msg n op in_cks ex_cks,
        evalExpRT st s e1 (OK v1) ->
        evalExpRT st s e2 (RTE msg) ->
        evalExpRT st s (BinOpRT n op e1 e2 in_cks ex_cks) (RTE msg)
    | EvalBinOpRT: forall st s e1 v1 e2 v2 in_cks op v n ex_cks,
        evalExpRT st s e1 (OK v1) ->
        evalExpRT st s e2 (OK v2) ->
        evalBinOpRTS in_cks op v1 v2 v ->
        evalExpRT st s (BinOpRT n op e1 e2 in_cks ex_cks) v
    | EvalUnOpRT_RTE: forall st s e msg n op in_cks ex_cks,
        evalExpRT st s e (RTE msg) ->
        evalExpRT st s (UnOpRT n op e in_cks ex_cks) (RTE msg)
    | EvalUnOpRT: forall st s e v in_cks op v' n ex_cks,
        evalExpRT st s e (OK v) ->
        evalUnOpRTS in_cks op v v' ->
        evalExpRT st s (UnOpRT n op e in_cks ex_cks) v'

(** ** Evaluation of Name + RT *)
with evalNameRT: symTabRT -> state -> nameRT -> Ret value -> Prop :=
    | EvalIdentifierRT: forall x s v st n ex_cks, 
        fetchG x s = Some v ->
        evalNameRT st s (IdentifierRT n x ex_cks) (OK v)
    | EvalIndexedComponentRTX_RTE: forall st s x msg n e ex_cks, 
        evalNameRT st s x (RTE msg) ->
        evalNameRT st s (IndexedComponentRT n x e ex_cks) (RTE msg)
    | EvalIndexedComponentRTE_RTE: forall st s x a e msg n ex_cks,
        evalNameRT st s x (OK (ArrayV a)) ->
        evalExpRT st s e (RTE msg) ->
        evalNameRT st s (IndexedComponentRT n x e ex_cks) (RTE msg)
    | EvalIndexedComponentRT_Range_RTE: forall st s x a e i t l u n ex_cks,
        evalNameRT st s x (OK (ArrayV a)) ->
        evalExpRT st s e (OK (Int i)) ->
        fetch_exp_type_rt (name_astnum_rt x) st = Some (Array_Type t) ->
        extract_array_index_range_rt st t (RangeRT l u) ->
        rangeChecks (exp_exterior_checks e) i l u (RTE RangeError) ->
        evalNameRT st s (IndexedComponentRT n x e ex_cks) (RTE RangeError)
    | EvalIndexedComponentRT: forall st s x a e i t l u v n ex_cks,
        evalNameRT st s x (OK (ArrayV a)) ->
        evalExpRT st s e (OK (Int i)) ->
        fetch_exp_type_rt (name_astnum_rt x) st = Some (Array_Type t) ->
        extract_array_index_range_rt st t (RangeRT l u) ->
        rangeChecks (exp_exterior_checks e) i l u (OK (Int i)) ->
        array_select a i = Some v ->
        evalNameRT st s (IndexedComponentRT n x e ex_cks) (OK v)
    | EvalSelectedComponentRTX_RTE: forall st s x msg n f ex_cks,
        evalNameRT st s x (RTE msg) ->
        evalNameRT st s (SelectedComponentRT n x f ex_cks) (RTE msg)
    | EvalSelectedComponentRT: forall st s x r f v n ex_cks,
        evalNameRT st s x (OK (RecordV r)) ->
        record_select r f = Some v ->
        evalNameRT st s (SelectedComponentRT n x f ex_cks) (OK v).


(** Inductive semantic of declarations. [eval_decl_x st s f decl f'] 
    means that [f'] is the frame to be pushed on s after evaluating decl, 
    [f] is used as an accumulator for building the frame.
*)

(** ** Evaluation of Declaration + RT *)

Inductive evalDeclRT: symTabRT -> state -> frame -> declRT -> Ret frame -> Prop :=
    | EvalDeclRT_Null: forall st s f,
        evalDeclRT st s f NullDeclRT (OK f)
    | EvalDeclRT_Var_None: forall d st s f n,
        d.(initialization_expRT) = None ->
        evalDeclRT st s f (ObjDeclRT n d) (OK (push f d.(object_nameRT) Undefined))
    | EvalDeclRT_Var_RTE: forall d e st f s msg n,
        d.(initialization_expRT) = Some e ->
        evalExpRT st (f :: s) e (RTE msg) ->
        evalDeclRT st s f (ObjDeclRT n d) (RTE msg)
    | EvalDeclRT_Var_NoCheck: forall d e st f s v n,
        d.(initialization_expRT) = Some e ->
        evalExpRT st (f :: s) e (OK v) ->
        v <> Undefined ->
        exp_exterior_checks e = nil ->
        evalDeclRT st s f (ObjDeclRT n d) (OK (push f d.(object_nameRT) v))
    | EvalDeclRT_Var_Range_RTE: forall d e st f s v l u n,
        d.(initialization_expRT) = Some e ->
        evalExpRT st (f :: s) e (OK (Int v)) ->
        exp_exterior_checks e = RangeCheck :: nil ->
        extract_subtype_range_rt st (d.(object_nominal_subtype_rt)) (RangeRT l u) ->
        rangeCheck v l u (RTE RangeError) ->
        evalDeclRT st s f (ObjDeclRT n d) (RTE RangeError)
    | EvalDeclRT_Var: forall d e st f s v l u n,
        d.(initialization_expRT) = Some e ->
        evalExpRT st (f :: s) e (OK (Int v)) ->
        exp_exterior_checks e = RangeCheck :: nil ->
        extract_subtype_range_rt st (d.(object_nominal_subtype_rt)) (RangeRT l u) ->
        rangeCheck v l u (OK (Int v)) ->
        evalDeclRT st s f (ObjDeclRT n d) (OK (push f d.(object_nameRT) (Int v)))
    | EvalDeclRT_Type: forall st s f n t,
        evalDeclRT st s f (TypeDeclRT n t) (OK f)
    | EvalDeclRT_Proc: forall st s f n p,
        evalDeclRT st s f (ProcBodyDeclRT n p) (OK f)
    | EvalDeclRT_Seq_E: forall st s f d1 msg n d2,
        evalDeclRT st s f d1 (RTE msg) ->
        evalDeclRT st s f (SeqDeclRT n d1 d2) (RTE msg)
    | EvalDeclRT_Seq: forall st s f d1 f' d2 f'' n,
        evalDeclRT st s f d1 (OK f') ->
        evalDeclRT st s f' d2 f'' ->
        evalDeclRT st s f (SeqDeclRT n d1 d2) f''.


(** update name with new value in the state and Ret newly updated state 
 
    the run-time check flags on the name expression will not affect the store update,
    they are only used when the expression is used on the right hand side of assignment;
*)

Inductive storeUpdateRT: symTabRT -> state -> nameRT -> value -> Ret state -> Prop := 
    | SU_Identifier_X: forall s x v s1 st n cks,
        updateG s x v = Some s1 ->
        storeUpdateRT st s (IdentifierRT n x cks) v (OK s1)
    | SU_Indexed_Component_xRTE_X: forall st s x msg n e cks v,
        evalNameRT st s x (RTE msg) ->
        storeUpdateRT st s (IndexedComponentRT n x e cks) v (RTE msg)
    | SU_Indexed_Component_eRTE_X: forall st s x a e msg n cks v,
        evalNameRT st s x (OK (ArrayV a)) \/ evalNameRT st s x (OK Undefined) ->
        evalExpRT st s e (RTE msg) ->
        storeUpdateRT st s (IndexedComponentRT n x e cks) v (RTE msg)
    | SU_Indexed_Component_Range_RTE_X: forall st s x a e i t l u n cks v,
        evalNameRT st s x (OK (ArrayV a)) \/ evalNameRT st s x (OK Undefined) ->
        evalExpRT st s e (OK (Int i)) ->
        fetch_exp_type_rt (name_astnum_rt x) st = Some (Array_Type t) ->
        extract_array_index_range_rt st t (RangeRT l u) ->
        rangeChecks (exp_exterior_checks e) i l u (RTE RangeError) ->
        storeUpdateRT st s (IndexedComponentRT n x e cks) v (RTE RangeError)
    | SU_Indexed_Component_X: forall st s x arrObj a e i t l u v a1 s1 n cks,
        evalNameRT st s x (OK arrObj) ->
        arrObj = (ArrayV a) \/ arrObj = Undefined ->
        evalExpRT st s e (OK (Int i)) ->
        fetch_exp_type_rt (name_astnum_rt x) st = Some (Array_Type t) ->
        extract_array_index_range_rt st t (RangeRT l u) ->
        rangeChecks (exp_exterior_checks e) i l u (OK (Int i)) ->
        arrayUpdate arrObj i v = (Some (ArrayV a1)) -> 
        storeUpdateRT st s x (ArrayV a1) s1 ->
        storeUpdateRT st s (IndexedComponentRT n x e cks) v s1
    | SU_Selected_Component_xRTE_X: forall st s x msg n f cks v,
        evalNameRT st s x (RTE msg) ->
        storeUpdateRT st s (SelectedComponentRT n x f cks) v (RTE msg)
    | SU_Selected_Component_X: forall st s x recObj r f v r1 s1 n cks,
        evalNameRT st s x (OK recObj) ->
        recObj = (RecordV r) \/ recObj = Undefined ->
        recordUpdate recObj f v = Some (RecordV r1) ->
        storeUpdateRT st s x (RecordV r1) s1 ->
        storeUpdateRT st s (SelectedComponentRT n x f cks) v s1.


(** ** Evaluation of Statement + RT *)

(** State manipulation for procedure calls and Ret *)

(** *** Copy In + RT *)

Inductive copyInRT: symTabRT -> state -> frame -> list paramSpecRT -> list expRT -> Ret frame -> Prop :=
    | CopyIn_Nil_X : forall st s f, 
        copyInRT st s f nil nil (OK f)
    | CopyIn_Mode_In_eRTE_X: forall param st s e msg f lparam le,
        param.(parameter_mode_rt) = In ->
        evalExpRT st s e (RTE msg) ->
        copyInRT st s f (param :: lparam) (e :: le) (RTE msg)
    | CopyIn_Mode_In_NoRangeCheck_X: forall param st s e v f f' lparam le f'',
        param.(parameter_mode_rt) = In ->
        evalExpRT st s e (OK v) ->
        v <> Undefined ->
        exp_exterior_checks e = nil ->
        push f param.(parameter_nameRT) v = f' ->
        copyInRT st s f' lparam le f'' ->
        copyInRT st s f (param :: lparam) (e :: le) f''
    | CopyIn_Mode_In_Range_RTE_X: forall param st s e v l u f lparam le,
        param.(parameter_mode_rt) = In ->
        evalExpRT st s e (OK (Int v)) ->
        exp_exterior_checks e = RangeCheck :: nil ->
        extract_subtype_range_rt st (param.(parameter_subtype_mark_rt)) (RangeRT l u) ->
        rangeCheck v l u (RTE RangeError) ->
        copyInRT st s f (param :: lparam) (e :: le) (RTE RangeError)
    | CopyIn_Mode_In_Range_X: forall param st s e v l u f f' lparam le f'',
        param.(parameter_mode_rt) = In ->
        evalExpRT st s e (OK (Int v)) ->
        exp_exterior_checks e = RangeCheck :: nil ->
        extract_subtype_range_rt st (param.(parameter_subtype_mark_rt)) (RangeRT l u) ->
        rangeCheck v l u (OK (Int v)) ->
        push f param.(parameter_nameRT) (Int v) = f' ->
        copyInRT st s f' lparam le f'' ->
        copyInRT st s f (param :: lparam) (e :: le) f''
    | CopyIn_Mode_InOut_eRTE_X: forall param st s nm msg f lparam n le,
        param.(parameter_mode_rt) = In_Out ->
        evalNameRT st s nm (RTE msg) ->
        copyInRT st s f (param :: lparam) ((NameRT n nm) :: le) (RTE msg)
    | CopyIn_Mode_InOut_NoRange_X: forall param st s nm v f f' lparam le f'' n,
        param.(parameter_mode_rt) = In_Out ->
        evalNameRT st s nm (OK v) ->
        v <> Undefined ->
        ~(List.In RangeCheck (name_exterior_checks nm)) ->
        push f param.(parameter_nameRT) v = f' ->
        copyInRT st s f' lparam le f'' ->
        copyInRT st s f (param :: lparam) ((NameRT n nm) :: le) f''
    | CopyIn_Mode_InOut_Range_RTE_X: forall param st s nm v l u f lparam le n,
        param.(parameter_mode_rt) = In_Out ->
        evalNameRT st s nm (OK (Int v)) ->
        List.In RangeCheck (name_exterior_checks nm) -> (*n may have both RangeCheck and RangeCheck_On_CopyOut*)
        extract_subtype_range_rt st (param.(parameter_subtype_mark_rt)) (RangeRT l u) ->
        rangeCheck v l u (RTE RangeError) ->
        copyInRT st s f (param :: lparam) ((NameRT n nm) :: le) (RTE RangeError)
    | CopyIn_Mode_InOut_Range_X: forall param st s nm v l u f f' lparam le f'' n,
        param.(parameter_mode_rt) = In_Out ->
        evalNameRT st s nm (OK (Int v)) ->
        List.In RangeCheck (name_exterior_checks nm) ->
        extract_subtype_range_rt st (param.(parameter_subtype_mark_rt)) (RangeRT l u) ->
        rangeCheck v l u (OK (Int v)) ->
        push f param.(parameter_nameRT) (Int v) = f' ->
        copyInRT st s f' lparam le f'' ->
        copyInRT st s f (param :: lparam) ((NameRT n nm) :: le) f''
    | CopyIn_Mode_Out_X: forall param f f' st s lparam le f'' n nm,
        param.(parameter_mode_rt) = Out ->
        push f param.(parameter_nameRT) Undefined = f' ->
        copyInRT st s f' lparam le f'' ->
        copyInRT st s f (param :: lparam) ((NameRT n nm) :: le) f''.


(** *** Copy Out + RT *)

Inductive copyOutRT: symTabRT -> state -> frame -> list paramSpecRT -> list expRT -> Ret state -> Prop :=
    | CopyOut_Nil_X : forall st s f, 
        copyOutRT st s f nil nil (OK s)
    | CopyOut_Mode_Out_nRTE_X: forall param f v nm st s msg lparam lexp n,
        param.(parameter_mode_rt) = Out \/ param.(parameter_mode_rt) = In_Out ->
        fetch param.(parameter_nameRT) f = Some v ->
        v <> Undefined ->
        ~(List.In RangeCheckOnReturn (name_exterior_checks nm)) ->
        storeUpdateRT st s nm v (RTE msg) ->
        copyOutRT st s f (param :: lparam) ((NameRT n nm) :: lexp) (RTE msg)
    | CopyOut_Mode_Out_NoRange_X: forall param f v nm st s s' lparam lexp s'' n,
        param.(parameter_mode_rt) = Out \/ param.(parameter_mode_rt) = In_Out ->
        fetch param.(parameter_nameRT) f = Some v ->
        v <> Undefined ->
        ~(List.In RangeCheckOnReturn (name_exterior_checks nm)) ->
        storeUpdateRT st s nm v (OK s') ->
        copyOutRT st s' f lparam lexp s'' ->
        copyOutRT st s f (param :: lparam) ((NameRT n nm) :: lexp) s''
    | CopyOut_Mode_Out_Range_RTE_X: forall param f v nm n st t l u s lparam lexp,
        param.(parameter_mode_rt) = Out \/ param.(parameter_mode_rt) = In_Out ->
        fetch param.(parameter_nameRT) f = Some (Int v) ->
        List.In RangeCheckOnReturn (name_exterior_checks nm) ->
        fetch_exp_type_rt n st = Some t ->
        extract_subtype_range_rt st t (RangeRT l u) ->
        rangeCheck v l u (RTE RangeError) ->
        copyOutRT st s f (param :: lparam) ((NameRT n nm) :: lexp) (RTE RangeError)
    | CopyOut_Mode_Out_Range_nRTE_X: forall param f v nm n st t l u s msg lparam lexp,
        param.(parameter_mode_rt) = Out \/ param.(parameter_mode_rt) = In_Out ->
        fetch param.(parameter_nameRT) f = Some (Int v) ->
        List.In RangeCheckOnReturn (name_exterior_checks nm) ->
        fetch_exp_type_rt n st = Some t ->
        extract_subtype_range_rt st t (RangeRT l u) ->
        rangeCheck v l u (OK (Int v)) ->
        storeUpdateRT st s nm (Int v) (RTE msg) ->
        copyOutRT st s f (param :: lparam) ((NameRT n nm) :: lexp) (RTE msg)
    | CopyOut_Mode_Out_Range_X: forall param f v nm n st t l u s s' lparam lexp s'',
        param.(parameter_mode_rt) = Out \/ param.(parameter_mode_rt) = In_Out ->
        fetch param.(parameter_nameRT) f = Some (Int v) ->
        List.In RangeCheckOnReturn (name_exterior_checks nm) ->
        fetch_exp_type_rt n st = Some t ->
        extract_subtype_range_rt st t (RangeRT l u) ->
        rangeCheck v l u (OK (Int v)) ->
        storeUpdateRT st s nm (Int v) (OK s') ->
        copyOutRT st s' f lparam lexp s'' ->
        copyOutRT st s f (param :: lparam) ((NameRT n nm) :: lexp) s''
    | CopyOut_Mode_In_X: forall param st s f lparam lexp s' e,
        param.(parameter_mode_rt) = In ->
        copyOutRT st s f lparam lexp s' ->
        copyOutRT st s f (param :: lparam) (e :: lexp) s'.


(** Inductive semantic of statement and declaration

   in a statement evaluation, whenever a run time error is detected in
   the evaluation of its sub-statements or sub-component, the
   evaluation is terminated and Ret a run-time error; otherwise,
   evaluate the statement into a OK state.

   - in the evaluation for assignment statement (AssignRT n x e),

     first, check if there is a RangeCheck flag on the right side (e) of 
     the assignment, 
     case 1: ~(List.In RangeCheck (exp_check_flags e)) means
     no range check needed for the value of expression e, 
     case 2: (exp_check_flags e = cks1 ++ RangeCheck :: cks2) means
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
     statement even though the RangeCheck flag is set on the expression e, and
     that's also why we remove the RangeCheck flag from e's run-time check flag
     set before the evaluation of e;

   - in the store update storeUpdateRT for indexed component (e.g. a(i):=v) or selected
     component (e.g. r.f := v), 
     
     if the value of array a (or value of record r) is Undefined, then create a new 
     aggregate array value with its ith element having value v (or create a new record 
     value with its field f having value v), and assign this new aggregate value to array 
     variable a (or record variable r);
     
     if the value of array a (or value of record r) is already defined, then update the
     ith element of its array value (or update the filed f of its record value), and assign
     the updated aggregate value to array variable a (or record variable r);

   - in the store update storeUpdateRT for indexed component (e.g. a(i):=v), a
     range check may be required on the value of index expression i if RangeCheck
     is set for it, and the range check should be performed for the value of i before
     it's used to update the array value;
 *)

(** *** evalStmtRT *)
Inductive evalStmtRT: symTabRT -> state -> stmtRT -> Ret state -> Prop := 
    | EvalNullRT: forall st s,
        evalStmtRT st s NullRT (OK s)
    | EvalAssignRT_RTE: forall st s e msg n x,
        evalExpRT st s e (RTE msg) ->
        evalStmtRT st s (AssignRT n x e) (RTE msg)
    | EvalAssignRT: forall st s e v x s1 n,
        evalExpRT st s e (OK v) ->
        v <> Undefined ->
        exp_exterior_checks e = nil ->
        storeUpdateRT st s x v s1 ->
        evalStmtRT st s (AssignRT n x e) s1
    | EvalAssignRT_Range_RTE: forall st s e v x t l u n,
        evalExpRT st s e (OK (Int v)) ->
        exp_exterior_checks e = RangeCheck :: nil ->
        fetch_exp_type_rt (name_astnum_rt x) st = Some t ->
        extract_subtype_range_rt st t (RangeRT l u) ->
        rangeCheck v l u (RTE RangeError) ->
        evalStmtRT st s (AssignRT n x e) (RTE RangeError)
    | EvalAssignRT_Range: forall st s e v x t l u s1 n,
        evalExpRT st s e (OK (Int v)) ->
        exp_exterior_checks e = RangeCheck :: nil ->
        fetch_exp_type_rt (name_astnum_rt x) st = Some t ->
        extract_subtype_range_rt st t (RangeRT l u) ->
        rangeCheck v l u (OK (Int v)) ->
        storeUpdateRT st s x (Int v) s1 ->
        evalStmtRT st s (AssignRT n x e) s1
    | EvalIfRT_RTE: forall st s b msg n c1 c2,
        evalExpRT st s b (RTE msg) ->
        evalStmtRT st s (IfRT n b c1 c2) (RTE msg)
    | EvalIfRT_True: forall st s b c1 s1 n c2,
        evalExpRT st s b (OK (Bool true)) ->
        evalStmtRT st s c1 s1 ->
        evalStmtRT st s (IfRT n b c1 c2) s1
    | EvalIfRT_False: forall st s b c2 s1 n c1,
        evalExpRT st s b (OK (Bool false)) ->
        evalStmtRT st s c2 s1 ->
        evalStmtRT st s (IfRT n b c1 c2) s1
    | EvalWhileRT_RTE: forall st s b msg n c,
        evalExpRT st s b (RTE msg) ->
        evalStmtRT st s (WhileRT n b c) (RTE msg)
    | EvalWhileRT_True_RTE: forall st s b c msg n,
        evalExpRT st s b (OK (Bool true)) ->
        evalStmtRT st s c (RTE msg) ->
        evalStmtRT st s (WhileRT n b c) (RTE msg)
    | EvalWhileRT_True: forall st s b c s1 n s2,
        evalExpRT st s b (OK (Bool true)) ->
        evalStmtRT st s c (OK s1) ->
        evalStmtRT st s1 (WhileRT n b c) s2 ->
        evalStmtRT st s (WhileRT n b c) s2
    | EvalWhileRT_False: forall st s b n c,
        evalExpRT st s b (OK (Bool false)) ->
        evalStmtRT st s (WhileRT n b c) (OK s)
    | EvalCallRT_Args_RTE: forall p st n0 pb s args msg n pn,
        fetch_proc_rt p st = Some (n, pb) ->
        copyInRT st s (newFrame n) (procedure_parameter_profile_rt pb) args (RTE msg) ->
        evalStmtRT st s (CallRT n0 pn p args) (RTE msg)
    | EvalCallRT_Decl_RTE: forall p st n0 pb s args f intact_s s1 msg n pn,
        fetch_proc_rt p st = Some (n, pb) ->
        copyInRT st s (newFrame n) (procedure_parameter_profile_rt pb) args (OK f) ->
        cut_until s n intact_s s1 -> (* s = intact_s ++ s1 *)
        evalDeclRT st s1 f (procedure_declarative_part_rt pb) (RTE msg) ->
        evalStmtRT st s (CallRT n0 pn p args) (RTE msg)
    | EvalCallRT_Body_RTE: forall p st n0 pb s args f intact_s s1 f1 msg n pn,
        fetch_proc_rt p st = Some (n, pb) ->
        copyInRT st s (newFrame n) (procedure_parameter_profile_rt pb) args (OK f) ->
        cut_until s n intact_s s1 -> (* s = intact_s ++ s1 *)
        evalDeclRT st s1 f (procedure_declarative_part_rt pb) (OK f1) ->
        evalStmtRT st (f1 :: s1) (procedure_statements_rt pb) (RTE msg) ->
        evalStmtRT st s (CallRT n0 pn p args) (RTE msg)
    | EvalCallRT: forall p st n0 pb s args f intact_s s1 f1 s2 locals_section params_section s3 s4 n pn,
        fetch_proc_rt p st = Some (n, pb) ->
        copyInRT st s (newFrame n) (procedure_parameter_profile_rt pb) args (OK f) ->
        cut_until s n intact_s s1 -> (* s = intact_s ++ s1 *)
        evalDeclRT st s1 f (procedure_declarative_part_rt pb) (OK f1) ->          
        evalStmtRT st (f1 :: s1) (procedure_statements_rt pb) (OK s2) ->
        s2 = (n, locals_section ++ params_section) :: s3 -> (* extract parameters from local frame *)
        List.length (store_of f) = List.length params_section ->
        copyOutRT st (intact_s ++ s3) (n, params_section) (procedure_parameter_profile_rt pb) args s4 ->
        evalStmtRT st s (CallRT n0 pn p args) s4
    | EvalSeqRT_RTE: forall st s c1 msg n c2,
        evalStmtRT st s c1 (RTE msg) ->
        evalStmtRT st s (SeqRT n c1 c2) (RTE msg)
    | EvalSeqRT: forall st s c1 s1 c2 s2 n,
        evalStmtRT st s c1 (OK s1) ->
        evalStmtRT st s1 c2 s2 ->
        evalStmtRT st s (SeqRT n c1 c2) s2.


(** ** evalProgramRT *)
(** the main procedure (with empty parameters) is working as the entry point of the whole program 
    - p: is the program
    - p.(mainRT): the main procedure of the program
    - mainProc: the declaration of the main procedure
    - the arguments of the main procedure is nil
*)

Inductive evalProgramRT: symTabRT -> state -> programRT -> Ret state -> Prop := 
    | EvalProgramRT: forall st s p n pn,
        evalStmtRT st nil (CallRT n pn p.(mainRT) nil) s ->
        evalProgramRT st nil p s.


(** * Help Lemmas *)

Lemma eval_exp_ex_cks_added: forall st s e v cks, 
  evalExpRT st s e v ->
    evalExpRT st s (update_exterior_checks_exp e cks) v.
Proof.
  intros; destruct e; 
  inversion H; smack;
  match goal with
  | [H: evalLiteralRT _ _ _ |- _] => constructor; smack
  | _ => idtac
  end;
  [ |
    apply EvalBinOpRTE1_RTE; auto |
    apply EvalBinOpRTE2_RTE with (v1:=v1); auto |
    apply EvalBinOpRT with (v1:=v1) (v2:=v2); auto |
    apply EvalUnOpRT_RTE; auto |
    apply EvalUnOpRT with (v := v0); auto
  ];
  match goal with
  | [H: evalNameRT _ _ ?n _ |- _] => inversion H; smack; constructor
  end;
  [ apply EvalIdentifierRT; auto |
    apply EvalIndexedComponentRTX_RTE; auto |
    apply EvalIndexedComponentRTE_RTE with (a := a0); auto |
    apply EvalIndexedComponentRT_Range_RTE with (a:=a0) (i:=i) (t:=t) (l:=l) (u:=u); auto |
    apply EvalIndexedComponentRT with (a:=a0) (i:=i) (t:=t) (l:=l) (u:=u); auto |
    apply EvalSelectedComponentRTX_RTE; auto |
    apply EvalSelectedComponentRT with (r:=r); auto
  ].
Qed.

Lemma eval_name_ex_cks_added: forall st s n v cks, 
  evalNameRT st s n v ->
    evalNameRT st s (update_exterior_checks_name n cks) v.
Proof.
  intros; destruct n; 
  inversion H; smack;
  [ apply EvalIdentifierRT; auto |
    apply EvalIndexedComponentRTX_RTE; auto |
    apply EvalIndexedComponentRTE_RTE with (a:=a0); auto |
    apply EvalIndexedComponentRT_Range_RTE with (a:=a0) (i:=i) (t:=t) (l:=l) (u:=u); auto |
    apply EvalIndexedComponentRT with (a:=a0) (i:=i) (t:=t) (l:=l) (u:=u); auto |
    apply EvalSelectedComponentRTX_RTE; auto |
    apply EvalSelectedComponentRT with (r:=r); auto
  ].
Qed.

Scheme expression_ind := Induction for exp Sort Prop 
                         with name_ind := Induction for name Sort Prop.

Scheme expression_x_ind := Induction for expRT Sort Prop 
                         with name_x_ind := Induction for nameRT Sort Prop.

Lemma eval_exp_ex_cks_stripped: forall e st s cks v,
  evalExpRT st s (update_exterior_checks_exp e cks) v ->
    evalExpRT st s e v.
Proof.
  apply (expression_x_ind
    (fun e: expRT =>
       forall (st : symTabRT) (s : STACK.state) (cks : exterior_checks) (v : Ret value),
      evalExpRT st s (update_exterior_checks_exp e cks) v ->
      evalExpRT st s e v)
    (fun n: nameRT =>
       forall (st : symTabRT) (s : STACK.state) (cks : exterior_checks) (v : Ret value),
      evalNameRT st s (update_exterior_checks_name n cks) v ->
      evalNameRT st s n v)
    ); intros;
  match goal with
  | [H: evalExpRT _ _ _ _ |- _] => inversion H; subst
  | [H: evalNameRT _ _ _ _ |- _] => inversion H; subst
  end.
- constructor; auto.
- constructor; auto.
  specialize (H _ _ _ _ H6); auto.
- apply EvalBinOpRTE1_RTE.
  rewrite <- (exp_exterior_checks_refl e) in H11.
  specialize (H _ _ _ _ H11); auto.
- apply EvalBinOpRTE2_RTE with (v1 := v1);
  rewrite <- (exp_exterior_checks_refl e) in H11;
  rewrite <- (exp_exterior_checks_refl e0) in H12;
  specialize (H _ _ _ _ H11); auto;
  specialize (H0 _ _ _ _ H12); auto.
- apply EvalBinOpRT with (v1 := v1) (v2 := v2); auto.
- apply EvalUnOpRT_RTE; auto.
- apply EvalUnOpRT with (v := v0); auto.
- constructor; auto.
- apply EvalIndexedComponentRTX_RTE.
  rewrite <- (name_exterior_checks_refl n) in H9;
  specialize (H _ _ _ _ H9); auto.
- apply EvalIndexedComponentRTE_RTE with (a := a0); auto.
- apply EvalIndexedComponentRT_Range_RTE with (a := a0) (i := i) (t := t) (l := l) (u := u); auto.
- apply EvalIndexedComponentRT with (a := a0) (i := i) (t := t) (l := l) (u := u); auto.
- apply EvalSelectedComponentRTX_RTE; auto.
- apply EvalSelectedComponentRT with (r := r); auto.
Qed.

Ltac apply_eval_exp_ex_cks_stripped :=
  match goal with
  | [H: evalExpRT ?st ?s (update_exterior_checks_exp ?e ?cks) ?v |- _] =>
      specialize (eval_exp_ex_cks_stripped _ _ _ _ _ H); let HZ := fresh "HZ" in intro HZ
  end.

Lemma eval_name_ex_cks_stripped: forall n st s cks v,
  evalNameRT st s (update_exterior_checks_name n cks) v ->
      evalNameRT st s n v.
Proof.
  induction n; intros;
  inversion H; subst.
- constructor; auto.
- apply EvalIndexedComponentRTX_RTE; auto.
- apply EvalIndexedComponentRTE_RTE with (a := a0); auto.
- apply EvalIndexedComponentRT_Range_RTE with (a := a0) (i := i) (t := t) (l := l) (u := u); auto.
- apply EvalIndexedComponentRT with (a := a0) (i := i) (t := t) (l := l) (u := u); auto.
- apply EvalSelectedComponentRTX_RTE; auto.
- apply EvalSelectedComponentRT with (r := r); auto.  
Qed.

Ltac apply_eval_name_ex_cks_stripped :=
  match goal with
  | [H: evalNameRT ?st ?s (update_exterior_checks_name ?n ?cks) ?v |- _] =>
      specialize (eval_name_ex_cks_stripped _ _ _ _ _ H); let HZ := fresh "HZ" in intro HZ
  end.


(** when the name expression is used as an address to update the store, then its exterior run-time
    check flags will not affect the store update; the run-time check flags are only used when the 
    name expression is to be evaluated as a value on the right hand side of assignment;
*)

Lemma store_update_ex_cks_added: forall st s n cks v s',
  storeUpdateRT st s n v s' ->
    storeUpdateRT st s (update_exterior_checks_name n cks) v s'.
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
  | [|- storeUpdateRT _ _ (update_exterior_checks_name _ _) _ _] =>
      apply store_update_ex_cks_added; auto
  end.

Lemma store_update_ex_cks_stripped: forall st s n cks v s',
  storeUpdateRT st s (update_exterior_checks_name n cks) v s' ->
    storeUpdateRT st s n v s'.
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
  | [H: storeUpdateRT _ _ (update_exterior_checks_name _ _) _ _ |- _] =>
      specialize (store_update_ex_cks_stripped _ _ _ _ _ _ H);
      let HZ := fresh "HZ" in intro HZ
  end.

(***********************************************************)

Lemma binop_arithm_operand_format: forall cks op v1 v2 v,
  evalBinOpRTS cks op v1 v2 (OK (Int v)) ->
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
  | [H: evalBinOpRTS _ _ _ _ (OK (Int _)) |- _] =>
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
  evalUnOpRTS cks op v (OK (Int v')) ->
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
  | [H: evalUnOpRTS _ _ _ (OK (Int _)) |- _] =>
      specialize (unop_arithm_operand_format _ _ _ _ H);
      let HZ := fresh "HZ" in
      let HZ1 := fresh "HZ" in 
      let n := fresh "n" in 
      intros HZ; destruct HZ as [n HZ1]
  end.










