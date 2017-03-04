(** 
_AUTHOR_

<<
Zhi Zhang
Department of Computer and Information Sciences
Kansas State University
zhangzhi@ksu.edu
>>
*)

Require Export ast_rt.
Require Export ast_util.
Require Export symboltable.

(* ***************************************************************
   generate and insert run-time check flags into SPARK AST nodes 
   according to the run-time check rules;
   *************************************************************** *)

(** run-time checks to be verified for an expression depend on both the
    types of its operations and the context where it appears, e.g. if
    it's used as an index, then RangeCheck should be set for it;
    in the following formalization, check_flags are the check flags
    that are enforced by the context of the expression, for example,
    in toIndexedComponent, RangeCheck will be enforced
    on the expression e as it's used as an index of array;

    in the formalization for expression as defined in language_flagged.v 
    and language.v, the constructor NameRT (Name) is introduced to 
    incorporate type nameRT (name) into type expRT (expression),
    for example, variable x is represented as a name expression with 
    (NameRT ast_num (IdentifierRT x_ast_num x checkflags) nil), and
    we enforce that the run-time check flags are put in the constructor
    IdentifierRT instead of NameRT, that's why the check flags for
    NameRT is nil;
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

(** * toExpRT *)

Inductive toExpRT: symTab -> exp -> expRT -> Prop :=
    | ToLitBool: forall st n b,
        toExpRT st (Literal n (Boolean_Literal b)) 
                   (LiteralRT n (Boolean_Literal b) nil nil)
    | ToLitIntT: forall st v n,
        in_bound v int32_bound true -> (*simple optimization: if v is in the range of Integer, then no overflow check*)
        toExpRT st (Literal n (Integer_Literal v)) 
                   (LiteralRT n (Integer_Literal v) nil nil)
    | ToLitIntF: forall st v n,
        in_bound v int32_bound false ->
        toExpRT st (Literal n (Integer_Literal v)) 
                   (LiteralRT n (Integer_Literal v) (OverflowCheck :: nil) nil)
    | ToName: forall st n nRT nm,
        toNameRT st nm nRT ->
        toExpRT st (Name n nm) 
                   (NameRT n nRT)
    | ToBinOpO: forall st op e1 e1RT e2 e2RT n,
        op = Plus \/ op = Minus \/ op = Multiply ->
        toExpRT st e1 e1RT ->
        toExpRT st e2 e2RT ->
        toExpRT st (BinOp n op e1 e2)
                   (BinOpRT n op e1RT e2RT (OverflowCheck :: nil) nil)
    | ToBinOpDO: forall st op e1 e1RT e2 e2RT n,
        op = Divide ->
        toExpRT st e1 e1RT ->
        toExpRT st e2 e2RT ->
        toExpRT st (BinOp n op e1 e2)
                   (BinOpRT n op e1RT e2RT (DivCheck :: OverflowCheck :: nil) nil)
    | ToBinOpM: forall st op e1 e1RT e2 e2RT n,
        op = Modulus ->
        toExpRT st e1 e1RT ->
        toExpRT st e2 e2RT ->
        toExpRT st (BinOp n op e1 e2)
                   (BinOpRT n op e1RT e2RT (DivCheck :: nil) nil)
    | ToBinOpOthers: forall st op e1 e1RT e2 e2RT n,
        op <> Plus ->
        op <> Minus ->
        op <> Multiply ->
        op <> Divide ->
        op <> Modulus ->
        toExpRT st e1 e1RT ->
        toExpRT st e2 e2RT ->
        toExpRT st (BinOp n op e1 e2)
                   (BinOpRT n op e1RT e2RT nil nil)
    | ToUnOpO: forall st op e eRT n,
        op = Unary_Minus ->
        toExpRT st e eRT ->
        toExpRT st (UnOp n op e) 
                   (UnOpRT n op eRT (OverflowCheck :: nil) nil)
    | ToUnOpOthers: forall st op e eRT n,
        op <> Unary_Minus ->
        toExpRT st e eRT ->
        toExpRT st (UnOp n op e) 
                   (UnOpRT n op eRT nil nil)

(** * toNameRT *)

with toNameRT: symTab -> name -> nameRT -> Prop :=
    | toIdentifier: forall st n x,
        toNameRT st (Identifier n x) (* the value of x should be already checked before it's stored in memory, so no check is needed when it's read *)
                    (IdentifierRT n x nil) 
    | toIndexedComponent: forall st e eRT x xRT n,
        toExpRT st e eRT ->
        toNameRT st x xRT -> (* x itself can be an indexed/selected component *)
        toNameRT st (IndexedComponent n x e) 
                    (IndexedComponentRT n xRT (update_exterior_checks_exp eRT (RangeCheck :: nil)) nil) 
    | toSelectedComponent: forall st x xRT n f,
        toNameRT st x xRT ->
        toNameRT st (SelectedComponent n x f) 
                    (SelectedComponentRT n xRT f nil).

(** * toArgsRT *)

(**
   for a procedure call, during its copy in, RangeCheck should be performed 
   on input argument if its corresponding formal parameter is a value of range 
   constrainted type; 
   similarly, during its copy out, RangeCheck should be performed on output 
   parameter if its corresponding actual argument is a value of range constrainted 
   type; 
   To distinguish the range checks performed on copy in and copy out,
   RangeCheckOnReturn is used to denote the range check on copy out, and
   RangeCheck is used to denote the range check on copy in by default;

   toArgsRT formalizes how to insert run-time check flags for arguments
   according to its corresponding formal parameters;
*)

Inductive toArgsRT: symTab -> list paramSpec -> list exp -> list expRT -> Prop :=
    | ToArgsNull: forall st,
        toArgsRT st nil nil nil
    | ToArgsIn: forall st param arg argRT lparam larg largRT,
        param.(parameter_mode) = In ->
        is_range_constrainted_type (param.(parameter_subtype_mark)) = false ->
        toExpRT  st arg argRT ->
        toArgsRT st lparam larg largRT -> 
        toArgsRT st (param :: lparam) (arg :: larg) (argRT :: largRT)
    | ToArgsInRangeCheck: forall st param arg argRT lparam larg largRT,
        param.(parameter_mode) = In ->
        is_range_constrainted_type (param.(parameter_subtype_mark)) = true ->
        toExpRT  st arg argRT ->
        toArgsRT st lparam larg largRT -> 
        toArgsRT st (param :: lparam) (arg :: larg) ((update_exterior_checks_exp argRT (RangeCheck :: nil)) :: largRT)
    | ToArgsOut: forall st param n t nRT lparam larg largRT nm,
        param.(parameter_mode) = Out ->
        fetch_exp_type n st = Some t ->
        is_range_constrainted_type t = false ->
        toNameRT st nm nRT ->
        toArgsRT st lparam larg largRT -> 
        toArgsRT st (param :: lparam) ((Name n nm) :: larg) ((NameRT n nRT) :: largRT)
    | ToArgsOutRangeCheck: forall st param n t nRT lparam larg largRT nm,
        param.(parameter_mode) = Out ->
        fetch_exp_type n st = Some t ->
        is_range_constrainted_type t = true ->
        toNameRT st nm nRT ->
        toArgsRT st lparam larg largRT -> 
        toArgsRT st (param :: lparam) ((Name n nm) :: larg) 
                                      ((NameRT n (update_exterior_checks_name nRT (RangeCheckOnReturn :: nil))) :: largRT)
    | ToArgsInOut: forall st param n t nRT lparam larg largRT nm,
        param.(parameter_mode) = In_Out ->
        is_range_constrainted_type (param.(parameter_subtype_mark)) = false ->
        fetch_exp_type n st = Some t ->
        is_range_constrainted_type t = false ->
        toNameRT st nm nRT ->
        toArgsRT st lparam larg largRT -> 
        toArgsRT st (param :: lparam) ((Name n nm) :: larg) ((NameRT n nRT) :: largRT)
    | ToArgsInOutRangeCheckIn: forall st param n t nRT lparam larg largRT nm,
        param.(parameter_mode) = In_Out ->
        is_range_constrainted_type (param.(parameter_subtype_mark)) = true ->
        fetch_exp_type n st = Some t ->
        is_range_constrainted_type t = false ->
        toNameRT st nm nRT ->
        toArgsRT st lparam larg largRT -> 
        toArgsRT st (param :: lparam) ((Name n nm) :: larg) 
                                      ((NameRT n (update_exterior_checks_name nRT (RangeCheck :: nil))) :: largRT)
    | ToArgsInOutRangeCheckOut: forall st param n t nRT lparam larg largRT nm,
        param.(parameter_mode) = In_Out ->
        is_range_constrainted_type (param.(parameter_subtype_mark)) = false ->
        fetch_exp_type n st = Some t ->
        is_range_constrainted_type t = true ->
        toNameRT st nm nRT ->
        toArgsRT st lparam larg largRT -> 
        toArgsRT st (param :: lparam) ((Name n nm) :: larg) 
                                      ((NameRT n (update_exterior_checks_name nRT (RangeCheckOnReturn :: nil))) :: largRT)
    | ToArgsInOutRangeCheck: forall st param n t nRT lparam larg largRT nm,
        param.(parameter_mode) = In_Out ->
        is_range_constrainted_type (param.(parameter_subtype_mark)) = true ->
        fetch_exp_type n st = Some t ->
        is_range_constrainted_type t = true ->
        toNameRT st nm nRT ->
        toArgsRT st lparam larg largRT -> 
        toArgsRT st (param :: lparam) ((Name n nm) :: larg) 
                                      ((NameRT n (update_exterior_checks_name nRT (RangeCheck :: RangeCheckOnReturn :: nil))) :: largRT).


(** * toStmtRT *)

(**
    given a statement, insert run-time check flags according to the
    run-time checking rules enforced on the semantics of SPARK language 
    and return a run-time checks-flagged statement;
*)
Inductive toStmtRT: symTab -> stmt -> stmtRT -> Prop := 
    | ToNull: forall st,
        toStmtRT st Null NullRT
    | ToAssign: forall x st t xRT e eRT n,
        fetch_exp_type (name_astnum x) st = Some t ->
        is_range_constrainted_type t = false ->        
        toNameRT st x xRT ->
        toExpRT  st e eRT ->
        toStmtRT st (Assign   n x e) 
                    (AssignRT n xRT eRT)
    | ToAssignRangeCheck: forall x st t xRT e eRT n,
        fetch_exp_type (name_astnum x) st = Some t ->
        is_range_constrainted_type t = true ->
        toNameRT st x xRT ->
        toExpRT  st e eRT ->
        toStmtRT st (Assign   n x e)
                    (AssignRT n xRT (update_exterior_checks_exp eRT (RangeCheck :: nil)))
    | ToIf: forall e eRT st c1 c1RT c2 c2RT n,
        toExpRT  st e eRT ->
        toStmtRT st c1 c1RT ->
        toStmtRT st c2 c2RT ->
        toStmtRT st (If   n e c1 c2) 
                    (IfRT n eRT c1RT c2RT)
    | ToWhile: forall e eRT st c cRT n,
        toExpRT  st e eRT ->
        toStmtRT st c cRT ->
        toStmtRT st (While   n e c) 
                    (WhileRT n eRT cRT)
    | ToCall: forall p st n0 pb params args argsRT n pn,
        fetch_proc p st = Some (n0, pb) ->
        procedure_parameter_profile pb = params ->
        toArgsRT st params args argsRT ->
        toStmtRT st (Call   n pn p args) 
                    (CallRT n pn p argsRT)
    | ToSeq: forall st c1 c1RT c2 c2RT n,
        toStmtRT st c1 c1RT ->
        toStmtRT st c2 c2RT ->
        toStmtRT st (Seq n   c1 c2)
                    (SeqRT n c1RT c2RT).


Inductive toTypeDeclRT: typeDecl -> typeDeclRT -> Prop :=
    | toSubtypeDecl: forall n tn t l u,
        toTypeDeclRT (SubtypeDecl   n tn t (Range l u))
                     (SubtypeDeclRT n tn t (RangeRT l u))
    | toDerivedTypeDecl: forall n tn t l u,
        toTypeDeclRT (DerivedTypeDecl   n tn t (Range l u))
                     (DerivedTypeDeclRT n tn t (RangeRT l u))
    | toIntegerTypeDecl: forall n tn l u,
        toTypeDeclRT (IntegerTypeDecl   n tn (Range l u))
                     (IntegerTypeDeclRT n tn (RangeRT l u))
    | toArrayTypeDecl: forall n tn tm t,
        toTypeDeclRT (ArrayTypeDecl   n tn tm t) (* tn: array type name, tm: index type mark, t: component type *)
                     (ArrayTypeDeclRT n tn tm t)
    | toRecordTypeDecl: forall n tn fs,
        toTypeDeclRT (RecordTypeDecl   n tn fs)  (* tn: record type name, fs: list of field types *)
                     (RecordTypeDeclRT n tn fs).

(** insert run-time check flags on the initialization expression 
    for a newly declared object;
*)
Inductive toObjDeclRT: symTab -> objDecl -> objDeclRT -> Prop :=
    | ToObjDeclNoneInit: forall st n x t,
        toObjDeclRT st (mkobjDecl   n x t None) 
                       (mkobjDeclRT n x t None) 
    | ToObjDecl: forall st t e eRT n x,
        is_range_constrainted_type t = false ->
        toExpRT st e eRT ->
        toObjDeclRT st (mkobjDecl   n x t (Some e)) (* declare a variable x of type t with initialization e *)
                       (mkobjDeclRT n x t (Some eRT))
    | ToObjDeclRangeCheck: forall st t e eRT n x,
        is_range_constrainted_type t = true ->
        toExpRT st e eRT ->
        toObjDeclRT st (mkobjDecl   n x t (Some e)) 
                       (mkobjDeclRT n x t (Some (update_exterior_checks_exp eRT (RangeCheck :: nil)))).

Inductive toObjDeclsRT: symTab -> list objDecl -> list objDeclRT -> Prop :=
    | ToObjDeclsNull: forall st,
        toObjDeclsRT st nil nil 
    | ToObjDecls: forall st o oRT lo loRT,
        toObjDeclRT  st o oRT ->
        toObjDeclsRT st lo loRT ->
        toObjDeclsRT st (o :: lo) (oRT :: loRT).


Inductive toParamSpecRT: paramSpec -> paramSpecRT -> Prop :=
    | ToParamSpec: forall n x t m,
        toParamSpecRT (mkparamSpec   n x t m) (* a parameter x of type t of in/out mode m *)
                   (mkparamSpecRT n x t m).

Inductive toParamSpecsRT: list paramSpec -> list paramSpecRT -> Prop :=
    | ToParamSpecsNull:
        toParamSpecsRT nil nil
    | ToParamSpecs: forall param paramRT lparam lparamRT,
        toParamSpecRT  param  paramRT ->
        toParamSpecsRT lparam lparamRT ->
        toParamSpecsRT (param :: lparam) (paramRT :: lparamRT).

(** * toDeclRT *)

Inductive toDeclRT: symTab -> decl -> declRT -> Prop :=
    | ToNullDecl: forall st,
        toDeclRT st NullDecl NullDeclRT
    | ToTypeDecl: forall t tRT st n,
        toTypeDeclRT t tRT ->
        toDeclRT st (TypeDecl   n t) 
                    (TypeDeclRT n tRT)
    | ToObjectDecl: forall st o oRT n,
        toObjDeclRT st o oRT ->
        toDeclRT st (ObjDecl   n o)
                    (ObjDeclRT n oRT) 
    | ToProcDecl: forall st p pRT n,
        toProcBodyDeclRT st p pRT ->
        toDeclRT st (ProcBodyDecl   n p)
                    (ProcBodyDeclRT n pRT) 
    | ToSeqDecl: forall st d1 d1RT d2 d2RT n,
        toDeclRT st d1 d1RT ->
        toDeclRT st d2 d2RT ->
        toDeclRT st (SeqDecl   n d1 d2) 
                    (SeqDeclRT n d1RT d2RT)

(** * toProcBodyDeclRT *)

with toProcBodyDeclRT: symTab -> procBodyDecl -> procBodyDeclRT -> Prop :=
       | ToProcBodyDecl: forall params paramsRT st decls declsRT stmt stmtRT n p,
           toParamSpecsRT params paramsRT ->
           toDeclRT st decls declsRT ->
           toStmtRT st stmt stmtRT ->
           toProcBodyDeclRT st (mkprocBodyDecl   n p params decls stmt)
                               (mkprocBodyDeclRT n p paramsRT declsRT stmtRT).

(** * toProgramRT *)
Inductive toProgramRT: symTab -> program -> programRT -> Prop :=
    | ToProgramRT: forall st p declsRT,
        toDeclRT st p.(decls) declsRT ->
        toProgramRT st p (mkprogramRT declsRT p.(main)).
