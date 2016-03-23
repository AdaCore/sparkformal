(** 
_AUTHOR_

<<
Zhi Zhang
Department of Computer and Information Sciences
Kansas State University
zhangzhi@ksu.edu
>>
*)

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

with toProcBodyDeclRT: symTab -> procBodyDecl -> procBodyDeclRT -> Prop :=
       | ToProcBodyDecl: forall params paramsRT st decls declsRT stmt stmtRT n p,
           toParamSpecsRT params paramsRT ->
           toDeclRT st decls declsRT ->
           toStmtRT st stmt stmtRT ->
           toProcBodyDeclRT st (mkprocBodyDecl   n p params decls stmt)
                               (mkprocBodyDeclRT n p paramsRT declsRT stmtRT).


(* ***************************************************************
                          Funtion Version
   *************************************************************** *)

(** * Functions for Inserting Run-Time Checks *)

Function toExpRTImpl (st: symTab) (e: exp): expRT :=
  match e with
  | Literal n (Boolean_Literal b) => 
      LiteralRT n (Boolean_Literal b) nil nil
  | Literal n (Integer_Literal v) =>
      match (Zle_bool min_signed v) && (Zle_bool v max_signed) with
      | true  => LiteralRT n (Integer_Literal v) nil nil (* optimization *)
      | false => LiteralRT n (Integer_Literal v) (OverflowCheck :: nil) nil
      end
  | Name n nm => 
      let nRT := toNameRTImpl st nm in
        NameRT n nRT
  | BinOp n op e1 e2 =>
      let e1RT := toExpRTImpl st e1 in
      let e2RT := toExpRTImpl st e2 in
        match op with
        | Plus     => BinOpRT n op e1RT e2RT (OverflowCheck :: nil) nil
        | Minus    => BinOpRT n op e1RT e2RT (OverflowCheck :: nil) nil
        | Multiply => BinOpRT n op e1RT e2RT (OverflowCheck :: nil) nil
        | Divide   => BinOpRT n op e1RT e2RT (DivCheck :: OverflowCheck :: nil) nil
        | Modulus   => BinOpRT n op e1RT e2RT (DivCheck :: nil) nil
        | _        => BinOpRT n op e1RT e2RT nil nil
        end
  | UnOp n op e => 
      let eRT := toExpRTImpl st e in
        match op with
        | Unary_Minus => UnOpRT n op eRT (OverflowCheck :: nil) nil
        | _           => UnOpRT n op eRT nil nil
        end
  end

with toNameRTImpl (st: symTab) (n: name): nameRT :=
  match n with
  | Identifier n x =>
      IdentifierRT n x nil
  | IndexedComponent n x e =>
      let xRT := toNameRTImpl st x in
      let eRT := toExpRTImpl st e in
        IndexedComponentRT n xRT (update_exterior_checks_exp eRT (RangeCheck :: nil)) nil
  | SelectedComponent n x f =>
      let xRT := toNameRTImpl st x in
        SelectedComponentRT n xRT f nil
  end.

Function toArgsRTImpl (st: symTab) (params: list paramSpec) (args: list exp): option (list expRT) :=
  match params, args with
  | nil, nil => Some nil
  | param :: lparam, arg :: larg =>
      match (toArgsRTImpl st lparam larg) with
      | Some largRT => 
          match param.(parameter_mode) with
          | In =>
            let argRT := toExpRTImpl st arg in
            if is_range_constrainted_type (param.(parameter_subtype_mark)) then
              Some ((update_exterior_checks_exp argRT (RangeCheck :: nil)) :: largRT)
            else
              Some (argRT :: largRT)
          | Out =>
            match arg with
            | Name n nm =>
                match fetch_exp_type n st with
                | Some t =>
                    let nRT := toNameRTImpl st nm in
                    if is_range_constrainted_type t then
                      Some ((NameRT n (update_exterior_checks_name nRT (RangeCheckOnReturn :: nil))) :: largRT)
                    else
                      Some ((NameRT n nRT) :: largRT)
                | None => None
                end
            | _ => None
            end
          | In_Out =>
            match arg with
            | Name n nm =>
                match fetch_exp_type n st with
                | Some t =>
                    let nRT := toNameRTImpl st nm in
                    if is_range_constrainted_type (param.(parameter_subtype_mark)) then 
                      if is_range_constrainted_type t then
                        Some ((NameRT n (update_exterior_checks_name nRT (RangeCheck :: RangeCheckOnReturn :: nil))) :: largRT)
                      else
                        Some ((NameRT n (update_exterior_checks_name nRT (RangeCheck :: nil))) :: largRT)
                    else
                      if is_range_constrainted_type t then
                        Some ((NameRT n (update_exterior_checks_name nRT (RangeCheckOnReturn :: nil))) :: largRT)
                      else
                        Some ((NameRT n nRT) :: largRT)
                | _ => None
                end
            | _ => None
            end
          end
      | _ => None
      end
  | _, _ => None
  end.

Function toStmtRTImpl (st: symTab) (c: stmt): option stmtRT :=
  match c with
  | Null => Some NullRT
  | Assign n x e =>
      let xRT := toNameRTImpl st x in
      let eRT := toExpRTImpl  st e in
        match fetch_exp_type (name_astnum x) st with
        | Some t =>
          if is_range_constrainted_type t then
            Some (AssignRT n xRT (update_exterior_checks_exp eRT (RangeCheck :: nil)))
          else
            Some (AssignRT n xRT eRT)
        | None   => None
        end
  | If n e c1 c2 =>
      let eRT  := toExpRTImpl st e in
      let c1' := toStmtRTImpl st c1 in
      let c2' := toStmtRTImpl st c2 in
        match (c1', c2') with 
        | (Some c1RT, Some c2RT) => 
            Some (IfRT n eRT c1RT c2RT)
        | _ => None
        end
  | While n e c =>
      let eRT := toExpRTImpl st e in
      let c' := toStmtRTImpl st c in
        match c' with 
        | Some cRT => 
            Some (WhileRT n eRT cRT)
        | _ => None
        end
  | Call n pn p args =>
      match fetch_proc p st with
      | Some (n0, pb) => 
          match toArgsRTImpl st (procedure_parameter_profile pb) args with
          | Some argsRT => Some (CallRT n pn p argsRT)
          | None              => None
          end
      | None         => None
      end
  | Seq n c1 c2 =>
      let c1' := toStmtRTImpl st c1 in
      let c2' := toStmtRTImpl st c2 in
      match (c1', c2') with
      | (Some c1RT, Some c2RT) =>
          Some (SeqRT n c1RT c2RT)
      | _ => None
      end
  end.

Function toTypeDeclRTImpl (t: typeDecl): typeDeclRT :=
  match t with
  | SubtypeDecl n tn t (Range l u) =>
      SubtypeDeclRT n tn t (RangeRT l u)
  | DerivedTypeDecl n tn t (Range l u) =>
      DerivedTypeDeclRT n tn t (RangeRT l u)
  | IntegerTypeDecl n tn (Range l u) =>
      IntegerTypeDeclRT n tn (RangeRT l u)
  | ArrayTypeDecl n tn tm t => (* tn: array type name, tm: index type mark, t: component type *)
      ArrayTypeDeclRT n tn tm t
  | RecordTypeDecl n tn fs =>  (* tn: record type name, fs: list of field types *)
      RecordTypeDeclRT n tn fs
  end.

Function toObjDeclRTImpl (st: symTab) (o: objDecl): objDeclRT :=
  match o with
  | mkobjDecl n x t None =>
      mkobjDeclRT n x t None
  | mkobjDecl n x t (Some e) => 
      let eRT := toExpRTImpl st e in
        if is_range_constrainted_type t then
          mkobjDeclRT n x t (Some (update_exterior_checks_exp eRT (RangeCheck :: nil)))
        else
          mkobjDeclRT n x t (Some eRT)
  end.

Function toObjDeclsRTImpl (st: symTab) (lo: list objDecl): list objDeclRT :=
  match lo with
  | nil => nil
  | o :: lo' => 
      let oRT  := toObjDeclRTImpl st o in
      let loRT := toObjDeclsRTImpl st lo' in
        oRT :: loRT
  end.

Function toParamSpecRTImpl (param: paramSpec): paramSpecRT :=
  match param with
  | mkparamSpec n x t m =>
      mkparamSpecRT n x t m
  end.

Function toParamSpecsRTImpl (lparam: list paramSpec): list paramSpecRT :=
  match lparam with
  | nil => nil
  | param :: lparam' =>
      let paramRT := toParamSpecRTImpl param in
      let lparamRT := toParamSpecsRTImpl lparam' in
        paramRT :: lparamRT
  end.


Function toDeclRTImpl (st: symTab) (d: decl): option declRT :=
  match d with
  | NullDecl => Some NullDeclRT
  | TypeDecl n t =>
      let tRT := toTypeDeclRTImpl t in
        Some (TypeDeclRT n tRT)
  | ObjDecl n o =>
      let oRT := toObjDeclRTImpl st o in 
        Some (ObjDeclRT n oRT)
  | ProcBodyDecl n p =>
      match toProcBodyDeclRTImpl st p with
      | Some pRT => Some (ProcBodyDeclRT n pRT)
      | None           => None
      end
  | SeqDecl n d1 d2 =>
      let d1' := toDeclRTImpl st d1 in
      let d2' := toDeclRTImpl st d2 in
      match (d1', d2') with 
      | (Some d1RT, Some d2RT) => Some (SeqDeclRT n d1RT d2RT)
      | _ => None
      end
  end

with toProcBodyDeclRTImpl (st: symTab) (p: procBodyDecl): option procBodyDeclRT :=
  match p with
  | mkprocBodyDecl n p params decls stmt =>
      let paramsRT := toParamSpecsRTImpl params in
      let decls' := toDeclRTImpl st decls in
      let stmt' := toStmtRTImpl st stmt in
      match (decls', stmt') with 
      | (Some declsRT, Some stmtRT) => Some (mkprocBodyDeclRT n p paramsRT declsRT stmtRT)
      | _ => None
      end
  end.


(* ***************************************************************
                 Semantics Equivalence Proof
   *************************************************************** *)

(** * Semantics Equivalence Proof For Run-Time Checks Generation *)

Scheme expression_ind := Induction for exp Sort Prop 
                         with name_ind := Induction for name Sort Prop.

(** * Soundness of RT-GEN IMPL *)

Section Checks_Generator_Implementation_Soundness_Proof.

  (** ** Soundness of RT-GEN for expression *)
  Lemma toExpRTImpl_soundness: forall e e' st,
    toExpRTImpl st e = e' ->
      toExpRT st e e'.
  Proof.
    apply (expression_ind
      (fun e: exp => forall (e' : expRT) (st: symTab),
        toExpRTImpl st e = e' ->
        toExpRT   st e e')
      (fun n: name => forall (n': nameRT) (st: symTab),
        toNameRTImpl st n = n' ->
        toNameRT   st n n')
      ); smack;
    [ (*Literal*) 
      destruct l;
      [ remember ((min_signed <=? z)%Z && (z <=? max_signed)%Z) as b; destruct b;
        smack; constructor; smack |
        smack; constructor
      ] | 
      (*Name*) | 
      (*BinOp a b e e0*) destruct b |
      (*UnOp a u e*) destruct u |
      (*Identifier a i*) |
      (*IndexedComponent a n e*) |
      (*SelectedComponent a n i*)
    ];
    match goal with
    | [H: _ = ?b |- in_bound _ _ ?b] => rewrite <- H; constructor; smack
    | _ => constructor; smack
    end.
  Qed.

  Lemma toNameRTImpl_soundness: forall st n n',
    toNameRTImpl st n = n' ->
      toNameRT st n n'.
  Proof.
    intros st n;
    induction n; smack; constructor; smack;
    apply toExpRTImpl_soundness; auto.
  Qed.

  (** ** Soundness of RT-GEN for arguments *)
  Lemma toArgsRTImpl_soundness: forall st params args args',
    toArgsRTImpl st params args = Some args' ->
      toArgsRT st params args args'.
  Proof.
    induction params; smack.
  - destruct args; smack;
    constructor.
  - destruct args; smack.
    remember (toArgsRTImpl st params args) as b1;
    remember (parameter_mode a) as b2; 
    destruct b1, b2; smack.
    + (*In Mode*)
      remember (is_range_constrainted_type (parameter_subtype_mark a)) as x;
      destruct x; smack;
      [ apply ToArgsInRangeCheck |
        apply ToArgsIn
      ]; smack; 
      apply toExpRTImpl_soundness; auto.
    + (*Out Mode*)
      destruct e; smack;
      remember (fetch_exp_type a0 st) as b3;
      destruct b3; smack;
      remember (is_range_constrainted_type t) as b4; destruct b4; smack;
      [ apply ToArgsOutRangeCheck with (t := t) |
        apply ToArgsOut with (t := t)
      ]; smack;
      apply toNameRTImpl_soundness; auto.
    + (*In_Out Mode*)
      destruct e; smack;
      remember (is_range_constrainted_type (parameter_subtype_mark a)) as b3;
      remember (fetch_exp_type a0 st) as b4;
      destruct b3, b4; smack;
      remember (is_range_constrainted_type t) as b5;
      destruct b5; smack;
      [ apply ToArgsInOutRangeCheck with (t:=t) |
        apply ToArgsInOutRangeCheckIn with (t:=t) |
        apply ToArgsInOutRangeCheckOut with (t:=t) |
        apply ToArgsInOut with (t:=t)
      ]; auto;
      apply toNameRTImpl_soundness; auto.
  Qed.

  (** ** Soundness of RT-GEN for statement *)
  Lemma toStmtRTImpl_soundness: forall st c c',
    toStmtRTImpl st c = Some c' ->
      toStmtRT st c c'.
  Proof.
    induction c; smack.
  - (*Null*)
    constructor.
  - (*Assign*)
    remember (fetch_exp_type (name_astnum n) st ) as b1;
    destruct b1; smack;
    remember (is_range_constrainted_type t) as b2;
    destruct b2; smack;
    [ apply ToAssignRangeCheck with (t := t) |
      apply ToAssign with (t := t)
    ]; auto;
    solve 
    [ apply toNameRTImpl_soundness; auto |
      apply toExpRTImpl_soundness; auto
    ].
  - (*If*)
    remember (toStmtRTImpl st c1) as b1;
    remember (toStmtRTImpl st c2) as b2;
    destruct b1, b2; smack;
    constructor; smack;
    apply toExpRTImpl_soundness; auto.
  - (*While*)
    remember (toStmtRTImpl st c) as b1;
    destruct b1; smack;
    constructor; smack;
    apply toExpRTImpl_soundness; auto.
  - (*Call*)
    remember (fetch_proc p st) as b1;
    destruct b1; smack;
    destruct t;
    remember (toArgsRTImpl st (procedure_parameter_profile p0) l) as b2;
    destruct b2; smack;
    apply ToCall with (n0 := l0) (pb := p0) (params := (procedure_parameter_profile p0)); smack;
    apply toArgsRTImpl_soundness; auto.
  - (*Seq*)
    remember (toStmtRTImpl st c1) as b1;
    remember (toStmtRTImpl st c2) as b2;
    destruct b1, b2; smack;
    constructor; auto.
  Qed.

  Lemma toTypeDeclRTImpl_soundness: forall t t',
    toTypeDeclRTImpl t = t' ->
        toTypeDeclRT t t'.
  Proof.
    destruct t; smack;
    try (destruct r); constructor.
  Qed.

  Lemma toObjDeclRTImpl_soundness: forall st o o',
    toObjDeclRTImpl st o = o' ->
      toObjDeclRT st o o'.
  Proof.
    intros;
    functional induction toObjDeclRTImpl st o; smack;
    [ constructor |
      apply ToObjDeclRangeCheck |
      apply ToObjDecl 
    ]; auto; apply toExpRTImpl_soundness; auto.
  Qed.

  Lemma toObjDeclsRTImpl_soundness: forall st lo lo',
    toObjDeclsRTImpl st lo = lo' ->
      toObjDeclsRT st lo lo'.
  Proof.
    induction lo; smack;
    constructor; smack;
    apply toObjDeclRTImpl_soundness; auto.
  Qed.

  Lemma toParamSpecRTImpl_soundness: forall param param',
    toParamSpecRTImpl param = param' ->
      toParamSpecRT param param'.
  Proof.
    smack;
    destruct param;
    constructor.  
  Qed.

  Lemma toParamSpecsRTImpl_soundness: forall lparam lparam',
    toParamSpecsRTImpl lparam = lparam' ->
      toParamSpecsRT lparam lparam'.
  Proof.
    induction lparam; smack;
    constructor; smack;
    apply toParamSpecRTImpl_soundness; auto.
  Qed.


  Scheme declaration_ind := Induction for decl Sort Prop 
                            with procedure_body_ind := Induction for procBodyDecl Sort Prop.

  (** ** Soundness of RT-GEN for declaration *)

  Lemma toDeclRTImpl_soundness: forall d d' st,
    toDeclRTImpl st d = Some d' ->
      toDeclRT st d d'.
  Proof.
    apply (declaration_ind
      (fun d: decl => forall (d' : declRT) (st: symTab),
        toDeclRTImpl st d = Some d' ->
        toDeclRT st d d')
      (fun p: procBodyDecl => forall (p': procBodyDeclRT) (st: symTab),
        toProcBodyDeclRTImpl st p = Some p' ->
        toProcBodyDeclRT st p p')
      ); smack.
  - constructor.
  - constructor;
    apply toTypeDeclRTImpl_soundness; auto.
  - constructor;
    apply toObjDeclRTImpl_soundness; auto.
  - remember (toProcBodyDeclRTImpl st p) as x; 
    destruct x; smack;
    constructor; auto.
  - remember (toDeclRTImpl st d) as x;
    remember (toDeclRTImpl st d0) as y;
    destruct x, y; smack;
    constructor; smack.
  - remember (toDeclRTImpl st procedure_declarative_part) as x;
    remember (toStmtRTImpl st procedure_statements) as y;
    destruct x, y; smack;
    constructor;
    [ apply toParamSpecsRTImpl_soundness | |
      apply toStmtRTImpl_soundness
    ]; auto.
  Qed.

  (** ** Soundness of RT-GEN for procedure *)

  Lemma toProcBodyDeclRTImpl_soundness: forall st p p',
    toProcBodyDeclRTImpl st p = Some p' ->
      toProcBodyDeclRT st p p'.
  Proof.
    intros;
    destruct p; smack.
    remember (toDeclRTImpl st procedure_declarative_part) as x;
    remember (toStmtRTImpl st procedure_statements) as y;
    destruct x, y; smack;
    constructor;
    [ apply toParamSpecsRTImpl_soundness |
      apply toDeclRTImpl_soundness |
      apply toStmtRTImpl_soundness 
    ]; auto.
  Qed.

End Checks_Generator_Implementation_Soundness_Proof.


(** * Completeness of RT-GEN IMPL *)

Section Checks_Generator_Implementation_Completeness_Proof.

  (** ** Completeness of RT-GEN for expression *)

  Lemma toExpRTImpl_completeness: forall e e' st,
    toExpRT st e e' ->
      toExpRTImpl st e = e'.
  Proof.
    apply (expression_ind
      (fun e: exp => forall (e' : expRT) (st: symTab),
        toExpRT   st e e' ->
        toExpRTImpl st e = e')
      (fun n: name => forall (n': nameRT) (st: symTab),
        toNameRT   st n n' ->
        toNameRTImpl st n = n')
      ); smack;
    match goal with
    | [H: toExpRT  _ ?e ?e' |- _] => inversion H; clear H; smack
    | [H: toNameRT _ ?n ?n' |- _] => inversion H; clear H; smack
    end;
    repeat progress match goal with
    | [H1:forall (e' : expRT) (st : symTab),
          toExpRT _ ?e e' ->
          toExpRTImpl _ ?e = e',
       H2:toExpRT _ ?e ?e1RT |- _] => specialize (H1 _ _ H2); smack
    | [H1:forall (n' : nameRT) (st : symTab),
          toNameRT _ ?n n' ->
          toNameRTImpl _ ?n = n',
       H2:toNameRT _ ?n ?nRT |- _] => specialize (H1 _ _ H2); smack
    end;
    match goal with
    | [H: in_bound _ _ _ |- _] => inversion H; smack
    | _ => idtac
    end;
    [ destruct b | 
      destruct u 
    ]; smack.
  Qed.

  Lemma toNameRTImpl_completeness: forall st n n',
    toNameRT st n n' ->
      toNameRTImpl st n = n'.
  Proof.
    intros;
    induction H; smack;
    match goal with
    | [H: toExpRT ?st ?e ?e' |- _] => 
        specialize (toExpRTImpl_completeness _ _ _ H); smack
    end; auto.
  Qed.

  (** ** Completeness of RT-GEN for arguments *)

  Lemma toArgsRTImpl_completeness: forall st params args args',
    toArgsRT st params args args' ->
      toArgsRTImpl st params args = Some args'.
  Proof.
    induction params; smack;
    match goal with
    | [H: toArgsRT _ _ ?args ?args' |- _] => inversion H; clear H; smack
    end;
    match goal with
    | [H1: forall (args : list exp) (args' : list expRT),
           toArgsRT _ ?params _ _ ->
           toArgsRTImpl _ ?params _ = Some _,
       H2: toArgsRT _ ?params _ _ |- _] => specialize (H1 _ _ H2)
    end;
    match goal with
    | [H: toArgsRTImpl ?st ?params ?larg = Some _ |- _] => rewrite H; simpl
    end;
    match goal with
    | [H: toExpRT _ ?e ?e' |- _] => specialize (toExpRTImpl_completeness _ _ _ H); smack
    | [H: toNameRT _ ?n ?n' |- _] => specialize (toNameRTImpl_completeness _ _ _ H); smack
    | _ => idtac
    end; auto.
  Qed.

  (** ** Completeness of RT-GEN for statement *)

  Lemma toStmtRTImpl_completeness: forall st c c',
    toStmtRT st c c' ->
      toStmtRTImpl st c = Some c'.
  Proof.
    induction c; smack;
    match goal with
    | [H: toStmtRT _ ?c ?c' |- _] => inversion H; clear H; smack
    end;
    repeat progress match goal with
    | [H: toExpRT  _ ?e ?e' |- _] => specialize (toExpRTImpl_completeness  _ _ _ H); clear H
    | [H: toNameRT _ ?n ?n' |- _] => specialize (toNameRTImpl_completeness _ _ _ H); clear H
    | [H1: forall c' : stmtRT,
           toStmtRT _ ?c _ ->
           toStmtRTImpl _ ?c = Some _,
       H2: toStmtRT _ ?c _ |- _ ] => specialize (H1 _ H2)
    end; smack;
    match goal with
    | [H: toArgsRT _ _ _ _ |- _ ] => specialize (toArgsRTImpl_completeness _ _ _ _ H); smack
    end.
  Qed.

  Lemma toTypeDeclRTImpl_completeness: forall t t',
    toTypeDeclRT t t' ->
      toTypeDeclRTImpl t = t'.
  Proof.
    destruct t; intros;
    match goal with
    | [H: toTypeDeclRT _ _ |- _] => inversion H; smack
    end.
  Qed.

  Lemma toObjDeclRTImpl_completeness: forall st o o',
    toObjDeclRT st o o' ->
      toObjDeclRTImpl st o = o'.
  Proof.
    intros;
    functional induction toObjDeclRTImpl st o;
    match goal with
    | [H: toObjDeclRT _ _ _ |- _] => inversion H; smack
    end;
    match goal with
    | [H: toExpRT _ _ _ |- _] => 
        specialize (toExpRTImpl_completeness _ _ _ H); smack
    end. 
  Qed.

  Lemma toObjDeclsRTImpl_completeness: forall st lo lo',
    toObjDeclsRT st lo lo' ->
      toObjDeclsRTImpl st lo = lo'.
  Proof.
    induction lo; smack;
    match goal with
    | [H: toObjDeclsRT _ _ _ |- _] => inversion H; clear H; smack
    end;
    match goal with
    | [H: toObjDeclRT _ ?o ?o' |- _] => 
        specialize (toObjDeclRTImpl_completeness _ _ _ H); smack
    end;
    specialize (IHlo _ H5); smack.
  Qed.

  Lemma toParamSpecRTImpl_completeness: forall param param',
    toParamSpecRT param param' ->
      toParamSpecRTImpl param = param'.
  Proof.
    intros;
    inversion H; auto.
  Qed.

  Lemma toParamSpecsRTImpl_completeness: forall lparam lparam',
    toParamSpecsRT lparam lparam' ->
      toParamSpecsRTImpl lparam = lparam'.
  Proof.
    induction lparam; intros;
    inversion H; auto;
    specialize (IHlparam _ H4);
    match goal with
    | [H: toParamSpecRT _ _ |- _] => 
        specialize (toParamSpecRTImpl_completeness _ _ H); smack
    end.
  Qed.

  (** ** Completeness of RT-GEN for declaration *)

  Lemma toDeclRTImpl_completeness: forall d d' st,
    toDeclRT st d d' ->
      toDeclRTImpl st d = Some d'.
  Proof.
    apply (declaration_ind
      (fun d: decl => forall (d' : declRT) (st: symTab),
        toDeclRT st d d' ->
        toDeclRTImpl st d = Some d')
      (fun p: procBodyDecl => forall (p': procBodyDeclRT) (st: symTab),
        toProcBodyDeclRT st p p' ->
        toProcBodyDeclRTImpl st p = Some p')
      ); smack;
    match goal with
    | [H: toDeclRT _ _ _ |- _] => inversion H; clear H; smack
    | [H: toProcBodyDeclRT _ _ _ |- _] => inversion H; clear H; smack
    end;
    repeat progress match goal with
    | [H: toTypeDeclRT _ _ |- _] => 
        specialize (toTypeDeclRTImpl_completeness _ _ H); smack
    | [H: toObjDeclRT _ _ _ |- _] =>
        specialize (toObjDeclRTImpl_completeness _ _ _ H); smack
    | [H: toParamSpecsRT _ _ |- _] =>
        specialize (toParamSpecsRTImpl_completeness _ _ H); clear H; smack
    | [H: toStmtRT _ _ _ |- _] =>
        specialize (toStmtRTImpl_completeness _ _ _ H); clear H; smack
    | [H1: forall (p' : procBodyDeclRT) (st : symTab),
           toProcBodyDeclRT _ ?p _ ->
           toProcBodyDeclRTImpl _ ?p = Some _,
       H2: toProcBodyDeclRT _ ?p _ |- _] =>
        specialize (H1 _ _ H2); smack
    | [H1: forall (d' : declRT) (st : symTab),
           toDeclRT _ ?d _ ->
           toDeclRTImpl _ ?d = Some _,
       H2: toDeclRT _ ?d _ |- _] => 
        specialize (H1 _ _ H2); clear H2; smack
    end.
  Qed.

  (** ** Completeness of RT-GEN for procedure *)

  Lemma toProcBodyDeclRTImpl_completeness: forall st p p',
    toProcBodyDeclRT st p p' ->
      toProcBodyDeclRTImpl st p = Some p'.
  Proof.
    intros;
    destruct p;
    match goal with
    [H: toProcBodyDeclRT _ _ _ |- _] => inversion H; clear H; smack
    end;
    repeat progress match goal with
    | [H: toParamSpecsRT _ _ |- _] =>
        specialize (toParamSpecsRTImpl_completeness _ _ H); clear H; smack
    | [H: toStmtRT _ _ _ |- _] =>
        specialize (toStmtRTImpl_completeness _ _ _ H); clear H; smack
    | [H: toDeclRT _ _ _ |- _] => 
        specialize (toDeclRTImpl_completeness _ _ _ H); clear H; smack
    end.
  Qed.

End Checks_Generator_Implementation_Completeness_Proof.

(** * Consistency of RT-GEN Impl with RT-GEN Spec *)

(** ** toExpRTImplConsistent *)
Lemma toExpRTImplConsistent: forall e e' st,
  toExpRT st e e' <-> 
    toExpRTImpl st e = e'.
Proof.
  intros; split; intro;
  [ apply toExpRTImpl_completeness; auto |
    apply toExpRTImpl_soundness; auto 
  ].
Qed.  

(** ** toStmtRTImplConsistent *)
Lemma toStmtRTImplConsistent: forall st c c',
  toStmtRT st c c' <->
    toStmtRTImpl st c = Some c'.
Proof.
  intros; split; intro;
  [ apply toStmtRTImpl_completeness; auto |
    apply toStmtRTImpl_soundness; auto 
  ].
Qed.

Lemma toProcBodyDeclRTConsistent: forall st p p',
  toProcBodyDeclRT st p p' <->
    toProcBodyDeclRTImpl st p = Some p'.
Proof.
  intros; split; intro;
  [ apply toProcBodyDeclRTImpl_completeness; auto |
    apply toProcBodyDeclRTImpl_soundness; auto 
  ].
Qed.

(** * Lemmas *)

Require Import CpdtTactics.

Lemma exp_ast_num_eq: forall st e e',
  toExpRT st e e' ->
    expression_astnum e = expression_astnum_rt e'.
Proof.
  intros; inversion H; smack.
Qed.

Lemma name_ast_num_eq: forall st n n',
  toNameRT st n n' ->
    name_astnum n = name_astnum_rt n'.
Proof.
  intros; inversion H; smack.
Qed.

Lemma exp_exterior_checks_beq_nil: forall st e e',
  toExpRT st e e' ->
    exp_exterior_checks e' = nil.
Proof.
  intros; 
  inversion H; smack;
  inversion H; subst;
  destruct n; 
  match goal with
  | [H: toNameRT _ _ _ |- _] => inversion H; smack
  end.
Qed.

Lemma name_exterior_checks_beq_nil: forall st n n',
  toNameRT st n n' ->
    name_exterior_checks n' = nil.
Proof.
  intros; 
  inversion H; smack.
Qed.

Lemma procedure_components_rel: forall st p p',
  toProcBodyDeclRT st p p' ->
  toParamSpecsRT (procedure_parameter_profile p) (procedure_parameter_profile_rt p') /\
  toDeclRT st (procedure_declarative_part p) (procedure_declarative_part_rt p') /\
  toStmtRT st (procedure_statements p) (procedure_statements_rt p').
Proof.
  intros.
  inversion H; smack.
Qed.


(** * Compile To Flagged Symbol Table *)

Inductive toProcDeclRTMap: symTab ->
                         list (idnum * (level * procBodyDecl)) -> 
                         list (idnum * (level * procBodyDeclRT)) -> Prop :=
    | ToProcDeclMapNull: forall st,
        toProcDeclRTMap st nil nil
    | ToProcDeclMap: forall st pb pb' pl pl' p l,
        toProcBodyDeclRT st pb pb' ->
        toProcDeclRTMap st pl pl' ->
        toProcDeclRTMap st ((p, (l, pb)) :: pl) ((p, (l, pb')) :: pl').

Inductive toTypeDeclRTMap: list (idnum * typeDecl) -> list (idnum * typeDeclRT) -> Prop :=
    | ToTypeDeclMapNull:
        toTypeDeclRTMap nil nil
    | ToTypeDeclMap: forall t t' tl tl' x,
        toTypeDeclRT t t' ->
        toTypeDeclRTMap tl tl' ->
        toTypeDeclRTMap ((x, t) :: tl) ((x, t') :: tl').

Inductive toSymTabRT: symTab -> symTabRT -> Prop := 
  | ToSymTab: forall p p' t t' x e srcloc nametable,
      toProcDeclRTMap (mkSymTab x p t e srcloc nametable) p p' ->
      toTypeDeclRTMap t t' ->
      toSymTabRT (mkSymTab x p t e srcloc nametable) (mkSymTabRT x p' t' e srcloc nametable).


(** ** Lemmas *)

Lemma procedure_declaration_rel: forall st pm pm' p n pb,
  toProcDeclRTMap st pm pm' ->
    Symbol_Table_Module.SymTable_Procs.fetches p pm = Some (n, pb) ->
      exists pb',
        Symbol_Table_Module_RT.SymTable_Procs.fetches p pm' = Some (n, pb') /\ 
        toProcBodyDeclRT st pb pb'.
Proof.
  intros st pm pm' p n pb H; revert p n pb.
  induction H; intros.
- inversion H; inversion H0; auto.
- unfold Symbol_Table_Module.SymTable_Procs.fetches in H1.
  unfold Symbol_Table_Module_RT.SymTable_Procs.fetches.
  remember (beq_nat p0 p) as Beq.
  destruct Beq. 
  + smack.
  + specialize (IHtoProcDeclRTMap _ _ _ H1).
    auto.
Qed.

Lemma procedure_declaration_rel_backward: forall st pm pm' p n pb,
  toProcDeclRTMap st pm pm' ->
    Symbol_Table_Module_RT.SymTable_Procs.fetches p pm' = Some (n, pb) ->
      exists pb',
        Symbol_Table_Module.SymTable_Procs.fetches p pm = Some (n, pb') /\ 
        toProcBodyDeclRT st pb' pb.
Proof.
  intros st pm pm' p n pb H; revert p n pb.
  induction H; intros.
- inversion H; inversion H0; auto.
- unfold Symbol_Table_Module_RT.SymTable_Procs.fetches in H1.
  unfold Symbol_Table_Module.SymTable_Procs.fetches.
  remember (beq_nat p0 p) as Beq.
  destruct Beq. 
  + smack.
  + specialize (IHtoProcDeclRTMap _ _ _ H1);
    auto.
Qed.

Lemma symbol_table_procedure_rel: forall st st' p n pb,
  toSymTabRT st st' ->  
    fetch_proc p st = Some (n, pb) ->
      exists pb',
        fetch_proc_rt p st' = Some (n, pb') /\
        toProcBodyDeclRT st pb pb'.
Proof.
  intros.
  inversion H; subst; clear H.
  unfold fetch_proc_rt;
  unfold fetch_proc in H0;
  simpl in *.
  specialize (procedure_declaration_rel _ _ _ _ _ _ H1 H0);
  auto.
Qed.

Lemma symbol_table_procedure_rel_backward: forall st st' p n pb,
  toSymTabRT st st' ->  
    fetch_proc_rt p st' = Some (n, pb) ->
      exists pb',
        fetch_proc p st = Some (n, pb') /\
        toProcBodyDeclRT st pb' pb.
Proof.
  intros.
  inversion H; subst; clear H.
  unfold fetch_proc;
  unfold fetch_proc_rt in H0;
  simpl in *.
  specialize (procedure_declaration_rel_backward _ _ _ _ _ _ H1 H0);
  auto.
Qed.

Lemma symbol_table_var_rel: forall st st' x,
  toSymTabRT st st' ->
    fetch_var x st = fetch_var_rt x st'.
Proof.
  intros.
  inversion H; smack.
Qed.

Lemma type_declaration_rel: forall tm tm' t td,
  toTypeDeclRTMap tm tm' ->
    Symbol_Table_Module.SymTable_Types.fetches t tm = Some td ->
    exists td',
      Symbol_Table_Module_RT.SymTable_Types.fetches t tm' = Some td' /\
      toTypeDeclRT td td'.
Proof.
  intros tm tm' t td H; revert t td.
  induction H; smack.
  destruct (beq_nat t0 x).
- inversion H; smack.
- apply IHtoTypeDeclRTMap; auto.
Qed.

Lemma type_declaration_rel_backward: forall tm tm' t td,
  toTypeDeclRTMap tm tm' ->
    Symbol_Table_Module_RT.SymTable_Types.fetches t tm' = Some td ->
    exists td',
      Symbol_Table_Module.SymTable_Types.fetches t tm = Some td' /\
      toTypeDeclRT td' td.
Proof.
  intros tm tm' t td H; revert t td.
  induction H; smack.
  destruct (beq_nat t0 x).
- inversion H; smack.
- apply IHtoTypeDeclRTMap; auto.
Qed.

Lemma symbol_table_type_rel: forall st st' t td,
  toSymTabRT st st' ->
    fetch_type t st = Some td ->
      exists td',
        fetch_type_rt t st' = Some td' /\ toTypeDeclRT td td'.
Proof.
  intros.
  inversion H; smack.
  unfold fetch_type, Symbol_Table_Module.fetch_type in H0; 
  unfold fetch_type_rt, Symbol_Table_Module_RT.fetch_type; smack.
  apply type_declaration_rel with (tm := t0); auto.
Qed.

Lemma symbol_table_type_rel_backward: forall st st' t td,
  toSymTabRT st st' ->
    fetch_type_rt t st' = Some td ->
      exists td',
        fetch_type t st = Some td' /\ toTypeDeclRT td' td.
Proof.
  intros.
  inversion H; smack.
  unfold fetch_type, Symbol_Table_Module_RT.fetch_type in H0; 
  unfold fetch_type_rt, Symbol_Table_Module.fetch_type; smack.
  apply type_declaration_rel_backward with (tm' := t'); auto.
Qed.

Lemma symbol_table_exp_type_rel: forall st st' e t,
  toSymTabRT st st' ->
    fetch_exp_type e st = t ->
      fetch_exp_type_rt e st' = t.
Proof.
  intros.
  inversion H; smack.
Qed.

Lemma symbol_table_exp_type_eq: forall st st' e,
  toSymTabRT st st' ->
    fetch_exp_type e st = fetch_exp_type_rt e st'.
Proof.
  intros.
  inversion H; smack.  
Qed.

Lemma subtype_range_rel: forall st st' t l u,
  toSymTabRT st st' ->
    extract_subtype_range st t (Range l u) ->
      extract_subtype_range_rt st' t (RangeRT l u).
Proof.
  intros.
  inversion H0; clear H0; smack.
  specialize (symbol_table_type_rel _ _ _ _ H H6); clear H6; smack.
  apply Extract_Range_RT with (tn := tn) (td := x); smack.
  destruct td; inversion H7; subst;
  inversion H2; auto.
Qed.

Lemma subtype_range_rel_backward: forall st st' t l u,
  toSymTabRT st st' ->
    extract_subtype_range_rt st' t (RangeRT l u) ->
      extract_subtype_range st t (Range l u).
Proof.
  intros.
  inversion H0; clear H0; smack.
  specialize (symbol_table_type_rel_backward _ _ _ _ H H6); clear H6; smack.
  apply Extract_Range with (tn := tn) (td := x); smack.
  destruct td; inversion H7; subst;
  inversion H2; auto.
Qed.

Lemma index_range_rel: forall st st' t l u,
  toSymTabRT st st' ->
    extract_array_index_range st t (Range l u) ->
      extract_array_index_range_rt st' t (RangeRT l u).
Proof.
  intros.
  inversion H0; clear H0; smack.
  specialize (symbol_table_type_rel _ _ _ _ H H3); clear H3; smack.
  specialize (symbol_table_type_rel _ _ _ _ H H7); clear H7; smack.  
  apply Extract_Index_Range_RT with (a_ast_num := a_ast_num) (tn := tn) (tm := tm) 
                                   (typ := typ) (tn' := tn') (td := x0); smack.
  inversion H2; auto.
  destruct td; inversion H8; subst;
  inversion H5; auto.
Qed.

Lemma index_range_rel_backward: forall st st' t l u,
  toSymTabRT st st' ->
    extract_array_index_range_rt st' t (RangeRT l u) ->
      extract_array_index_range st t (Range l u).
Proof.
  intros.
  inversion H0; clear H0; smack.
  specialize (symbol_table_type_rel_backward _ _ _ _ H H3); clear H3; smack.
  specialize (symbol_table_type_rel_backward _ _ _ _ H H7); clear H7; smack.  
  apply Extract_Index_Range with (a_ast_num := a_ast_num) (tn := tn) (tm := tm) 
                                 (typ := typ) (tn' := tn') (td := x0); smack.
  inversion H2; auto.
  destruct td; inversion H8; subst;
  inversion H5; auto.
Qed.
