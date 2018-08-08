(** 
_AUTHOR_

<<
Zhi Zhang
Department of Computer and Information Sciences
Kansas State University
zhangzhi@ksu.edu
>>
*)

(* ***************************************************************
                          Funtion Version
   *************************************************************** *)

Require Export rt_gen.


(** * toExpRTImpl *)

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

(** * toNameRTImpl *)
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

(** * toArgsRTImpl *)
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

(** * toStmtRTImpl *)
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
      (*let eRT := toExpRTImpl st e in*)
        if is_range_constrainted_type t then
          mkobjDeclRT n x t (Some (update_exterior_checks_exp (toExpRTImpl st e) (RangeCheck :: nil)))
        else
          mkobjDeclRT n x t (Some (toExpRTImpl st e))
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

(** * toDeclRTImpl *)
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

(** * toProcBodyDeclRTImpl *)
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

(** * toProgramRTImpl *)
Function toProgramRTImpl (st: symTab) (p: program): option programRT :=
  match toDeclRTImpl st p.(decls) with
  | Some declsRT => Some (mkprogramRT declsRT p.(main))
  | None => None
  end.
