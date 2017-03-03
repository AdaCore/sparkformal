(** 
_AUTHOR_

<<
Zhi Zhang
Department of Computer and Information Sciences
Kansas State University
zhangzhi@ksu.edu
>>
*)

Require Export ast_basics.

(** This file can be auto-generated from language_template.v by running languagegen in terminal *)

(** * SPARK Subset Language *)

(** We use the Ada terminology to define the terms of this subset 
    language, which makes it easy for Ada(SPARK) users to read it;
    Besides, we also indicate the reference chapter (for example, ,3.5.3)
    in Ada 2012 RM, and formalize the language in the same (not exactly) 
    order as they are defined in Ada 2012 RM;
*)

(* Ada 2012 RM, Chapter 3. Declaration and Types *)

(** ** Expression *)
(* Chapter 4 *)

Inductive exp: Type := 
    | Literal: astnum -> literal -> exp (* 4.2 *)
    | Name: astnum -> name -> exp (* 4.1 *)
    | BinOp: astnum -> binary_operator -> exp -> exp -> exp (* 4.5.3 and 4.5.5 *)
    | UnOp: astnum -> unary_operator -> exp -> exp (* 4.5.4 *)  

(** in IndexedComponent, the first astnum is the ast number for the indexed component, 
    and the second astnum is the ast number for array represented by name;
    in E_SelectedComponent, the first astnum is the ast number for the record field,
    and second astnum is the ast number for record represented by name;
 *)
with name: Type := (* 4.1 *)
    | Identifier: astnum -> idnum -> name (* 4.1 *)
    | IndexedComponent: astnum -> name -> exp -> name (* 4.1.1 *)
    | SelectedComponent: astnum -> name -> idnum -> name (* 4.1.3 *).

(** Induction scheme for exp and name *)
(**
Scheme exp_ind := Induction for exp Sort Prop
                         with name_ind := Induction for name Sort Prop.
*)

(** ** Statement *)
(* Chapter 5 *)
(* Sequence is not a statement in Ada, it's a shortcut for now;
   check flags can be easily added if they are needed later;
*)
Inductive stmt: Type := 
    | Null: stmt (* 5.1 *)
    | Assign: astnum -> name -> exp -> stmt (* 5.2 *)
    | If: astnum -> exp -> stmt -> stmt -> stmt (* 5.3 *)
    | While: astnum -> exp -> stmt -> stmt (* 5.5 *)
    | Call: astnum -> astnum -> procnum -> list exp -> stmt (* 6.4 *) (* the second astnum for the called procedure *)
    | Seq: astnum -> stmt -> stmt -> stmt (* 5.1 *).

(** it's used for subtype declarations:
    - subtype declaration,      e.g. subtype MyInt is Integer range 0 .. 5;
    - derived type declaration, e.g. type MyInt is new Integer range 1 .. 100;
    - integer type declaration, e.g. type MyInt is range 1 .. 10;
*)
Inductive range: Type := Range (l: Z) (u: Z). (* 3.5 *)

(** ** Type Declaration *)
Inductive typeDecl: Type := (* 3.2.1 *)
    | SubtypeDecl:
        astnum -> typenum (*subtype name*) -> type -> range -> typeDecl (* 3.2.2 *)
    | DerivedTypeDecl:
        astnum -> typenum (*derived type name*) -> type -> range -> typeDecl (* 3.4 *)
    | IntegerTypeDecl:
        astnum -> typenum (*integer type name*) -> range -> typeDecl (* 3.5.4 *)
    | ArrayTypeDecl: (* Constrained_Array_Definition, non-nested one-dimentional array *)
        astnum -> typenum (*array type name*) -> type (*index subtype mark*) -> type (*component type*) -> typeDecl (* 3.6 *)
    | RecordTypeDecl:
        astnum -> typenum (*record type name*) -> list (idnum * type (*field type*)) -> typeDecl (* 3.8 *).

(* 3.3.1 *)
Record objDecl: Type := mkobjDecl{
    declaration_astnum: astnum;
    object_name: idnum;
    object_nominal_subtype: type;
    initialization_exp: option (exp)
}.

(* 6.1 (15/3) *)
Record paramSpec: Type := mkparamSpec{
    parameter_astnum: astnum;
    parameter_name: idnum;
    parameter_subtype_mark: type;
    parameter_mode: mode
(*  parameter_default_exp: option (exp) *)
}.

(** ** Declaration *)
(* Mutual records/inductives are not allowed in coq, so we build a record by hand. *)
Inductive decl: Type :=  (* 3.1 *)
    | NullDecl: decl
    | TypeDecl: astnum -> typeDecl -> decl (* 3.2.1 *)
    | ObjDecl: astnum -> objDecl -> decl (* 3.3.1 *)
    | ProcBodyDecl: astnum -> procBodyDecl -> decl (* 6.1 *)
    | SeqDecl: astnum -> decl -> decl -> decl (* it's introduced for easy proof *)

(** ** Procedure *)
with procBodyDecl: Type :=
  mkprocBodyDecl
    (procedure_astnum: astnum)
    (procedure_name: procnum)
    (procedure_parameter_profile: list paramSpec)
    (procedure_declarative_part: decl)
    (procedure_statements: stmt).

(** * Program *)
(** A program is composed of a sequence of (1) type declarations, (2) variable declarations 
(3) procedure declarations, where 'main' is the main procedure (with empty parameters) working 
as the entry point of the whole program  *)

Record program : Type := mkprogram{
    decls: decl;
    main: procnum
}.

(** * Auxiliary Functions *)

Section AuxiliaryFunctions.

  Definition procedure_statements pb :=
    match pb with 
      | mkprocBodyDecl _ _ _ _ x => x
    end.

  Definition procedure_declarative_part pb :=
    match pb with
      | mkprocBodyDecl _ _ _ x _ => x
    end.

  Definition procedure_parameter_profile pb :=
    match pb with
      | mkprocBodyDecl _ _ x _ _ => x
    end.

  Definition procedure_name pb :=
    match pb with
      | mkprocBodyDecl _ x _ _ _ => x
    end.

  Definition type_name td :=
    match td with
    | SubtypeDecl _ tn _ _        => tn
    | DerivedTypeDecl _ tn _ _   => tn
    | IntegerTypeDecl _ tn _     => tn
    | ArrayTypeDecl _ tn _ _     => tn
    | RecordTypeDecl _ tn _      => tn
    end.

  Definition subtype_range (t: typeDecl): option range :=
    match t with
    | SubtypeDecl ast_num tn t r      => Some r
    | DerivedTypeDecl ast_num tn t r => Some r
    | IntegerTypeDecl ast_num tn r   => Some r
    | _                                          => None
    end.

  Definition expression_astnum e :=
    match e with
    | Literal ast_num l => ast_num
    | Name ast_num n => ast_num
    | BinOp ast_num bop e1 e2 => ast_num
    | UnOp ast_num uop e => ast_num
    end.  

  Definition name_astnum n :=
    match n with
    | Identifier ast_num x => ast_num
    | IndexedComponent ast_num x e => ast_num
    | SelectedComponent ast_num x f => ast_num
    end.

End AuxiliaryFunctions.






