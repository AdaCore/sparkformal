Require Import String.
Require Import symboltable.
Open Scope string_scope.
Definition Coq_AST_Tree := 
(D_Procedure_Body 1 
  (mkprocedure_body 2
    (* = = = Procedure Name = = = *)
    ((*P1*) 2)
    (* = = = Formal Parameters = = = *)
    (
    (mkparameter_specification 3 ((*ARG*) 3) Integer In_Out) :: 
    (mkparameter_specification 4 ((*ARG2*) 4) Integer In) :: nil)
    (* = = = Object Declarations = = = *)
    ((D_Object_Declaration 6 (mkobject_declaration 7 ((*N*) 6) Boolean (Some ((E_Literal 5 (Boolean_Literal true) ))))))
    (* = = = Procedure Body = = = *)
      (S_Assignment 8 (E_Identifier 9 ((*ARG*) 3) ) (E_Binary_Operation 10 Plus (E_Name 11 (E_Identifier 12 ((*ARG*) 3) )) (E_Literal 13 (Integer_Literal 7) ) ))
  )
).
Definition Symbol_Table := 
(mkSymbolTable
  (*///////////////////////////////////*)
  (* = = = (1) variable type map = = = *)
  (*///////////////////////////////////*)
  ((((*ARG*) 3), (In_Out, Integer)) :: (((*ARG2*) 4), (In, Integer)) :: (((*N*) 6), (In_Out, Boolean)) :: nil)
  (*////////////////////////////////////////////*)
  (* = = = (2) subprogram declaration map = = = *)
  (*////////////////////////////////////////////*)
  ((((*P1*) 2), (0, (mkprocedure_body 2
  (* = = = Procedure Name = = = *)
  ((*P1*) 2)
  (* = = = Formal Parameters = = = *)
  (
  (mkparameter_specification 3 ((*ARG*) 3) Integer In_Out) :: 
  (mkparameter_specification 4 ((*ARG2*) 4) Integer In) :: nil)
  (* = = = Object Declarations = = = *)
  ((D_Object_Declaration 6 (mkobject_declaration 7 ((*N*) 6) Boolean (Some ((E_Literal 5 (Boolean_Literal true) ))))))
  (* = = = Procedure Body = = = *)
    (S_Assignment 8 (E_Identifier 9 ((*ARG*) 3) ) (E_Binary_Operation 10 Plus (E_Name 11 (E_Identifier 12 ((*ARG*) 3) )) (E_Literal 13 (Integer_Literal 7) ) ))
))) :: nil)
  (*//////////////////////////////////////*)
  (* = = = (3) type declaration map = = = *)
  (*//////////////////////////////////////*)
  (nil)
  (*/////////////////////////////////////*)
  (* = = = (4) expression type map = = = *)
  (*/////////////////////////////////////*)
  ((11, Integer) :: (5, Boolean) :: (13, Integer) :: (10, Integer) :: (9, Integer) :: (12, Integer) :: nil)
  (*/////////////////////////////////////////////////*)
  (* = = = (5) ast node to source location map = = = *)
  (*/////////////////////////////////////////////////*)
  ((11, (sloc (*Line*)6 (*Col*)14 (*EndLine*)6 (*EndCol*)16)) :: (5, (sloc (*Line*)4 (*Col*)22 (*EndLine*)4 (*EndCol*)25)) :: (13, (sloc (*Line*)6 (*Col*)20 (*EndLine*)6 (*EndCol*)20)) :: (10, (sloc (*Line*)6 (*Col*)14 (*EndLine*)6 (*EndCol*)20)) :: (9, (sloc (*Line*)6 (*Col*)7 (*EndLine*)6 (*EndCol*)9)) :: (12, (sloc (*Line*)6 (*Col*)14 (*EndLine*)6 (*EndCol*)16)) :: nil)
  (* = = = (6) name id to a pair of (name string, unique name string) map = = = *)
  (*/////////////////////////////////////////////////*)
  ((mkNameTable
  (*///////////////////////////////////*)
  (* = = = (1) variable names map = = = *)
  (*///////////////////////////////////*)
  ((4, ("ARG2", "ada://parameter/proc1-1:9/P1-3:14/ARG2-3:39")) :: (3, ("ARG", "ada://parameter/proc1-1:9/P1-3:14/ARG-3:18")) :: (6, ("N", "ada://variable/proc1-1:9/P1-3:14/N+4:7")) :: nil)
  (*////////////////////////////////////////////*)
  (* = = = (2) subprogram names map = = = *)
  (*////////////////////////////////////////////*)
  ((2, ("P1", "ada://procedure_body/proc1-1:9/P1-3:14")) :: nil)
  (*//////////////////////////////////////*)
  (* = = = (3) package names map = = = *)
  (*//////////////////////////////////////*)
  ((1, ("proc1", "ada://package_body/proc1-1:9")) :: nil)
  (*/////////////////////////////////////*)
  (* = = = (4) type names map = = = *)
  (*/////////////////////////////////////*)
  (nil)
))
).
Definition Coq_AST_Tree_X := 
(D_Procedure_Body_X 1 
  (mkprocedure_body_x 2
    (* = = = Procedure Name = = = *)
    ((*P1*) 2)
    (* = = = Formal Parameters = = = *)
    (
    (mkparameter_specification_x 3 ((*ARG*) 3) Integer In_Out) :: 
    (mkparameter_specification_x 4 ((*ARG2*) 4) Integer In) :: nil)
    (* = = = Object Declarations = = = *)
    ((D_Object_Declaration_X 6 (mkobject_declaration_x 7 ((*N*) 6) Boolean (Some ((E_Literal_X 5 (Boolean_Literal true) (nil) nil))))))
    (* = = = Procedure Body = = = *)
      (S_Assignment_X 8 (E_Identifier_X 9 ((*ARG*) 3) (nil)) (E_Binary_Operation_X 10 Plus (E_Name_X 11 (E_Identifier_X 12 ((*ARG*) 3) (nil))) (E_Literal_X 13 (Integer_Literal 7) (nil) nil) (nil) nil))
  )
).
Definition Symbol_Table_X := 
(mkSymbolTable_x
  (*///////////////////////////////////*)
  (* = = = (1) variable type map = = = *)
  (*///////////////////////////////////*)
  ((((*ARG*) 3), (In_Out, Integer)) :: (((*ARG2*) 4), (In, Integer)) :: (((*N*) 6), (In_Out, Boolean)) :: nil)
  (*////////////////////////////////////////////*)
  (* = = = (2) subprogram declaration map = = = *)
  (*////////////////////////////////////////////*)
  ((((*P1*) 2), (0, (mkprocedure_body_x 2
  (* = = = Procedure Name = = = *)
  ((*P1*) 2)
  (* = = = Formal Parameters = = = *)
  (
  (mkparameter_specification_x 3 ((*ARG*) 3) Integer In_Out) :: 
  (mkparameter_specification_x 4 ((*ARG2*) 4) Integer In) :: nil)
  (* = = = Object Declarations = = = *)
  ((D_Object_Declaration_X 6 (mkobject_declaration_x 7 ((*N*) 6) Boolean (Some ((E_Literal_X 5 (Boolean_Literal true) (nil) nil))))))
  (* = = = Procedure Body = = = *)
    (S_Assignment_X 8 (E_Identifier_X 9 ((*ARG*) 3) (nil)) (E_Binary_Operation_X 10 Plus (E_Name_X 11 (E_Identifier_X 12 ((*ARG*) 3) (nil))) (E_Literal_X 13 (Integer_Literal 7) (nil) nil) (nil) nil))
))) :: nil)
  (*//////////////////////////////////////*)
  (* = = = (3) type declaration map = = = *)
  (*//////////////////////////////////////*)
  (nil)
  (*/////////////////////////////////////*)
  (* = = = (4) expression type map = = = *)
  (*/////////////////////////////////////*)
  ((11, Integer) :: (5, Boolean) :: (13, Integer) :: (10, Integer) :: (9, Integer) :: (12, Integer) :: nil)
  (*/////////////////////////////////////////////////*)
  (* = = = (5) ast node to source location map = = = *)
  (*/////////////////////////////////////////////////*)
  ((11, (sloc (*Line*)6 (*Col*)14 (*EndLine*)6 (*EndCol*)16)) :: (5, (sloc (*Line*)4 (*Col*)22 (*EndLine*)4 (*EndCol*)25)) :: (13, (sloc (*Line*)6 (*Col*)20 (*EndLine*)6 (*EndCol*)20)) :: (10, (sloc (*Line*)6 (*Col*)14 (*EndLine*)6 (*EndCol*)20)) :: (9, (sloc (*Line*)6 (*Col*)7 (*EndLine*)6 (*EndCol*)9)) :: (12, (sloc (*Line*)6 (*Col*)14 (*EndLine*)6 (*EndCol*)16)) :: nil)
  (* = = = (6) name id to a pair of (name string, unique name string) map = = = *)
  (*/////////////////////////////////////////////////*)
  ((mkNameTable
  (*///////////////////////////////////*)
  (* = = = (1) variable names map = = = *)
  (*///////////////////////////////////*)
  ((4, ("ARG2", "ada://parameter/proc1-1:9/P1-3:14/ARG2-3:39")) :: (3, ("ARG", "ada://parameter/proc1-1:9/P1-3:14/ARG-3:18")) :: (6, ("N", "ada://variable/proc1-1:9/P1-3:14/N+4:7")) :: nil)
  (*////////////////////////////////////////////*)
  (* = = = (2) subprogram names map = = = *)
  (*////////////////////////////////////////////*)
  ((2, ("P1", "ada://procedure_body/proc1-1:9/P1-3:14")) :: nil)
  (*//////////////////////////////////////*)
  (* = = = (3) package names map = = = *)
  (*//////////////////////////////////////*)
  ((1, ("proc1", "ada://package_body/proc1-1:9")) :: nil)
  (*/////////////////////////////////////*)
  (* = = = (4) type names map = = = *)
  (*/////////////////////////////////////*)
  (nil)
))
).
