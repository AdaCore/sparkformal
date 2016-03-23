(** 
_AUTHOR_

<<
Zhi Zhang
Department of Computer and Information Sciences
Kansas State University
zhangzhi@ksu.edu
>>
*)

Require Export language.
Require Export checks.

(** This file can be auto-generated from language_template.v by running languagegen in terminal *)

(** * SPARK Subset Language *)

(** We use the Ada terminology to define the terms of this subset 
    language, which makes it easy for Ada(SPARK) users to read it;
    Besides, we also indicate the reference chapter (for example, ,3.5.3)
    in Ada 2012 RM, and formalize the language in the same (not exactly) 
    order as they are defined in Ada 2012 RM;
*)

(* Ada 2012 RM, Chapter 3. Declaration and Types *)

(** ** Expressions *)
(* Chapter 4 *)

Inductive expRT: Type := 
    | LiteralRT: astnum -> literal -> interior_checks -> exterior_checks -> expRT (* 4.2 *)
    | NameRT: astnum -> nameRT -> expRT (* 4.1 *)
    | BinOpRT: astnum -> binary_operator -> expRT -> expRT -> interior_checks -> exterior_checks -> expRT (* 4.5.3 and 4.5.5 *)
    | UnOpRT: astnum -> unary_operator -> expRT -> interior_checks -> exterior_checks -> expRT (* 4.5.4 *)  

(** in IndexedComponentRT, the first astnum is the ast number for the indexed component, 
    and the second astnum is the ast number for array represented by nameRT;
    in SelectedComponentRT, the first astnum is the ast number for the record field,
    and second astnum is the ast number for record represented by nameRT;
 *)
with nameRT: Type := (* 4.1 *)
    | IdentifierRT: astnum -> idnum -> exterior_checks -> nameRT (* 4.1 *)
    | IndexedComponentRT: astnum -> nameRT -> expRT -> exterior_checks -> nameRT (* 4.1.1 *)
    | SelectedComponentRT: astnum -> nameRT -> idnum -> exterior_checks -> nameRT (* 4.1.3 *).

(** Induction scheme for expRT and nameRT *)
(**
Scheme expRT_ind := Induction for expRT Sort Prop
                         with nameRT_ind := Induction for nameRT Sort Prop.
*)

(** ** Statements *)
(* Chapter 5 *)
(* Sequence is not a statement in Ada, it's a shortcut for now;
   check flags can be easily added if they are needed later;
*)
Inductive stmtRT: Type := 
    | NullRT: stmtRT (* 5.1 *)
    | AssignRT: astnum -> nameRT -> expRT -> stmtRT (* 5.2 *)
    | IfRT: astnum -> expRT -> stmtRT -> stmtRT -> stmtRT (* 5.3 *)
    | WhileRT: astnum -> expRT -> stmtRT -> stmtRT (* 5.5 *)
    | CallRT: astnum -> astnum -> procnum -> list expRT -> stmtRT (* 6.4 *) (* the second astnum for the called procedure *)
    | SeqRT: astnum -> stmtRT -> stmtRT -> stmtRT (* 5.1 *).

(** it's used for subtype declarations:
    - subtype declaration,      e.g. subtype MyInt is Integer range 0 .. 5;
    - derived type declaration, e.g. type MyInt is new Integer range 1 .. 100;
    - integer type declaration, e.g. type MyInt is range 1 .. 10;
*)
Inductive rangeRT: Type := RangeRT (l: Z) (u: Z). (* 3.5 *)

(** ** Type Declarations *)
Inductive typeDeclRT: Type := (* 3.2.1 *)
    | SubtypeDeclRT:
        astnum -> typenum (*subtype name*) -> type -> rangeRT -> typeDeclRT (* 3.2.2 *)
    | DerivedTypeDeclRT:
        astnum -> typenum (*derived type name*) -> type -> rangeRT -> typeDeclRT (* 3.4 *)
    | IntegerTypeDeclRT:
        astnum -> typenum (*integer type name*) -> rangeRT -> typeDeclRT (* 3.5.4 *)
    | ArrayTypeDeclRT: (* Constrained_Array_Definition, non-nested one-dimentional array *)
        astnum -> typenum (*array type name*) -> type (*index subtype mark*) -> type (*component type*) -> typeDeclRT (* 3.6 *)
    | RecordTypeDeclRT:
        astnum -> typenum (*record type name*) -> list (idnum * type (*field type*)) -> typeDeclRT (* 3.8 *).

(* 3.3.1 *)
Record objDeclRT: Type := mkobjDeclRT{
    declaration_astnum_rt: astnum;
    object_nameRT: idnum;
    object_nominal_subtype_rt: type;
    initialization_expRT: option (expRT)
}.

(* 6.1 (15/3) *)
Record paramSpecRT: Type := mkparamSpecRT{
    parameter_astnum_rt: astnum;
    parameter_nameRT: idnum;
    parameter_subtype_mark_rt: type;
    parameter_mode_rt: mode
(*  parameter_default_expRT: option (expRT) *)
}.

(** ** Declarations *)
(* Mutual records/inductives are not allowed in coq, so we build a record by hand. *)
Inductive declRT: Type :=  (* 3.1 *)
    | NullDeclRT: declRT
    | TypeDeclRT: astnum -> typeDeclRT -> declRT (* 3.2.1 *)
    | ObjDeclRT: astnum -> objDeclRT -> declRT (* 3.3.1 *)
    | ProcBodyDeclRT: astnum -> procBodyDeclRT -> declRT (* 6.1 *)
    | SeqDeclRT: astnum -> declRT -> declRT -> declRT (* it's introduced for easy proof *)

with procBodyDeclRT: Type :=
  mkprocBodyDeclRT
    (procedure_astnum_rt: astnum)
    (procedurNameRT: procnum)
    (procedure_parameter_profile_rt: list paramSpecRT)
    (procedure_declarative_part_rt: declRT)
    (procedure_statements_rt: stmtRT).


(** ** Auxiliary Functions *)

Section AuxiliaryFunctions_RT.

  Definition procedure_statements_rt pb :=
    match pb with 
      | mkprocBodyDeclRT _ _ _ _ x => x
    end.

  Definition procedure_declarative_part_rt pb :=
    match pb with
      | mkprocBodyDeclRT _ _ _ x _ => x
    end.

  Definition procedure_parameter_profile_rt pb :=
    match pb with
      | mkprocBodyDeclRT _ _ x _ _ => x
    end.

  Definition procedur_name_rt pb :=
    match pb with
      | mkprocBodyDeclRT _ x _ _ _ => x
    end.

  Definition type_name_rt td :=
    match td with
    | SubtypeDeclRT _ tn _ _        => tn
    | DerivedTypeDeclRT _ tn _ _   => tn
    | IntegerTypeDeclRT _ tn _     => tn
    | ArrayTypeDeclRT _ tn _ _     => tn
    | RecordTypeDeclRT _ tn _      => tn
    end.

  Definition subtype_range_rt (t: typeDeclRT): option rangeRT :=
    match t with
    | SubtypeDeclRT ast_num tn t r      => Some r
    | DerivedTypeDeclRT ast_num tn t r => Some r
    | IntegerTypeDeclRT ast_num tn r   => Some r
    | _                                          => None
    end.

  Definition expression_astnum_rt e :=
    match e with
    | LiteralRT ast_num l in_checks ex_checks => ast_num
    | NameRT ast_num n => ast_num
    | BinOpRT ast_num bop e1 e2 in_checks ex_checks => ast_num
    | UnOpRT ast_num uop e in_checks ex_checks => ast_num
    end.  

  Definition name_astnum_rt n :=
    match n with
    | IdentifierRT ast_num x ex_checks => ast_num
    | IndexedComponentRT ast_num x e ex_checks => ast_num
    | SelectedComponentRT ast_num x f ex_checks => ast_num
    end.

End AuxiliaryFunctions_RT.











