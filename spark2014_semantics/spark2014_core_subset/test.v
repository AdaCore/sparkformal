Require Import language.
Require Import language_flagged.
Definition Coq_AST_Tree := 
(D_Procedure_Body 1 
  (mkprocedure_body 2
    (* = = = Procedure Name = = = *)
    ((*Test*) 1)
    (* = = = Formal Parameters = = = *)
    (
    (mkparameter_specification 3 ((*N*) 1) Integer In) :: 
    (mkparameter_specification 4 ((*M*) 2) Integer Out) :: nil)
    (* = = = Object Declarations = = = *)
    ((D_Seq_Declaration 5
  (D_Type_Declaration 6 (Record_Type_Declaration 7 ((*RecordT*) 1) ((((*X*) 3), Integer) :: nil))) 
  (D_Seq_Declaration 9
  (D_Type_Declaration 10 (Subtype_Declaration 11 ((*I*) 2) Integer (Range 0 5))) 
  (D_Seq_Declaration 12
  (D_Type_Declaration 13 (Array_Type_Declaration 14 ((*ArrayT*) 3) ((*index subtype mark*) Integer) ((*component type*) (Subtype ((*I*) 2))))) 
  (D_Seq_Declaration 15
  (D_Procedure_Body 16 
    (mkprocedure_body 17
      (* = = = Procedure Name = = = *)
      ((*Increase*) 2)
      (* = = = Formal Parameters = = = *)
      (
      (mkparameter_specification 18 ((*X*) 4) Integer In) :: 
      (mkparameter_specification 19 ((*Y*) 5) Integer Out) :: nil)
      (* = = = Object Declarations = = = *)
      (D_Null_Declaration)
      (* = = = Procedure Body = = = *)
        (S_Assignment 20 (E_Identifier 21 ((*Y*) 5) ) (E_Binary_Operation 22 Plus (E_Name 23 (E_Identifier 24 ((*X*) 4) ) ) (E_Literal 25 (Integer_Literal 1) ) ))
    )
  ) 
  (D_Seq_Declaration 26
  (D_Object_Declaration 27 (mkobject_declaration 28 ((*R*) 6) (Record_Type ((*RecordT*) 1)) None)) 
  (D_Seq_Declaration 29
  (D_Object_Declaration 30 (mkobject_declaration 31 ((*A*) 7) (Array_Type ((*ArrayT*) 3)) None)) 
  (D_Seq_Declaration 32
  (D_Object_Declaration 34 (mkobject_declaration 35 ((*Result*) 8) Integer (Some ((E_Literal 33 (Integer_Literal 1) ))))) 
  (D_Seq_Declaration 36
  (D_Object_Declaration 39 (mkobject_declaration 40 ((*T*) 9) Integer (Some ((E_Name 37 (E_Identifier 38 ((*Result*) 8) ) ))))) 
  (D_Seq_Declaration 41
  (D_Object_Declaration 42 (mkobject_declaration 43 ((*T1*) 10) Integer None)) 
  (D_Object_Declaration 44 (mkobject_declaration 45 ((*T2*) 11) Integer None))))))))))))
    (* = = = Procedure Body = = = *)
      (S_Sequence 46
      (S_Assignment 47 (E_Selected_Component 48 49 ((*R*) 6) ((*X*) 3) ) (E_Literal 52 (Integer_Literal 1) )) 
      (S_Sequence 53
      (S_Assignment 54 (E_Indexed_Component 55 56 ((*A*) 7) (E_Literal 58 (Integer_Literal 0) ) ) (E_Literal 59 (Integer_Literal 1) )) 
      (S_Sequence 60
      (S_Assignment 61 (E_Identifier 62 ((*T1*) 10) ) (E_Binary_Operation 63 Plus (E_Name 64 (E_Selected_Component 65 66 ((*R*) 6) ((*X*) 3) ) ) (E_Name 69 (E_Identifier 70 ((*N*) 1) ) ) )) 
      (S_Sequence 71
      (S_Assignment 72 (E_Identifier 73 ((*T2*) 11) ) (E_Binary_Operation 74 Plus (E_Name 75 (E_Indexed_Component 76 77 ((*A*) 7) (E_Literal 79 (Integer_Literal 0) ) ) ) (E_Name 80 (E_Identifier 81 ((*T1*) 10) ) ) )) 
      (S_Sequence 82
      (S_Assignment 83 (E_Identifier 84 ((*T*) 9) ) (E_Name 85 (E_Identifier 86 ((*T2*) 11) ) )) 
      (S_Sequence 87
      (S_Procedure_Call 88 89 ((*Increase*) 2) 
        ((E_Name 90 (E_Identifier 91 ((*T2*) 11) ) ) :: (E_Name 92 (E_Identifier 93 ((*T*) 9) ) ) :: nil)
      ) 
      (S_Sequence 94
      (S_If 95 (E_Binary_Operation 96 Greater_Than (E_Name 97 (E_Identifier 98 ((*T*) 9) ) ) (E_Literal 99 (Integer_Literal 0) ) )
        (S_Assignment 100 (E_Identifier 101 ((*T*) 9) ) (E_Binary_Operation 102 Plus (E_Name 103 (E_Identifier 104 ((*T*) 9) ) ) (E_Literal 105 (Integer_Literal 1) ) ))
        S_Null
      ) 
      (S_Sequence 106
      (S_If 107 (E_Binary_Operation 108 Greater_Than (E_Name 109 (E_Identifier 110 ((*T*) 9) ) ) (E_Literal 111 (Integer_Literal 1) ) )
        (S_Assignment 112 (E_Identifier 113 ((*T*) 9) ) (E_Binary_Operation 114 Plus (E_Name 115 (E_Identifier 116 ((*T*) 9) ) ) (E_Literal 117 (Integer_Literal 2) ) ))
        (S_Assignment 118 (E_Identifier 119 ((*T*) 9) ) (E_Binary_Operation 120 Minus (E_Name 121 (E_Identifier 122 ((*T*) 9) ) ) (E_Literal 123 (Integer_Literal 1) ) ))
      ) 
      (S_Sequence 124
      (S_While_Loop 125 (E_Binary_Operation 126 Greater_Than (E_Name 127 (E_Identifier 128 ((*T*) 9) ) ) (E_Literal 129 (Integer_Literal 0) ) )
        (S_Sequence 130
        (S_Assignment 131 (E_Identifier 132 ((*Result*) 8) ) (E_Binary_Operation 133 Divide (E_Binary_Operation 134 Multiply (E_Name 135 (E_Identifier 136 ((*Result*) 8) ) ) (E_Name 137 (E_Identifier 138 ((*T*) 9) ) ) ) (E_Name 139 (E_Identifier 140 ((*N*) 1) ) ) )) 
        (S_Assignment 141 (E_Identifier 142 ((*T*) 9) ) (E_Binary_Operation 143 Minus (E_Name 144 (E_Identifier 145 ((*T*) 9) ) ) (E_Literal 146 (Integer_Literal 1) ) )))
      ) 
      (S_Assignment 147 (E_Identifier 148 ((*M*) 2) ) (E_Name 149 (E_Identifier 150 ((*Result*) 8) ) )))))))))))
  )
).

Definition Symbol_Table := 
(mkSymbolTable
  (*///////////////////////////////////*)
  (* = = = (1) variable type map = = = *)
  (*///////////////////////////////////*)
  (nil)
  (*////////////////////////////////////////////*)
  (* = = = (2) subprogram declaration map = = = *)
  (*////////////////////////////////////////////*)
  ((((*Increase*) 2), (1, (mkprocedure_body 17
  (* = = = Procedure Name = = = *)
  ((*Increase*) 2)
  (* = = = Formal Parameters = = = *)
  (
  (mkparameter_specification 18 ((*X*) 4) Integer In) :: 
  (mkparameter_specification 19 ((*Y*) 5) Integer Out) :: nil)
  (* = = = Object Declarations = = = *)
  (D_Null_Declaration)
  (* = = = Procedure Body = = = *)
    (S_Assignment 20 (E_Identifier 21 ((*Y*) 5) ) (E_Binary_Operation 22 Plus (E_Name 23 (E_Identifier 24 ((*X*) 4) ) ) (E_Literal 25 (Integer_Literal 1) ) ))
))) :: (((*Test*) 1), (0, (mkprocedure_body 2
  (* = = = Procedure Name = = = *)
  ((*Test*) 1)
  (* = = = Formal Parameters = = = *)
  (
  (mkparameter_specification 3 ((*N*) 1) Integer In) :: 
  (mkparameter_specification 4 ((*M*) 2) Integer Out) :: nil)
  (* = = = Object Declarations = = = *)
  ((D_Seq_Declaration 5
(D_Type_Declaration 6 (Record_Type_Declaration 7 ((*RecordT*) 1) ((((*X*) 3), Integer) :: nil))) 
(D_Seq_Declaration 9
(D_Type_Declaration 10 (Subtype_Declaration 11 ((*I*) 2) Integer (Range 0 5))) 
(D_Seq_Declaration 12
(D_Type_Declaration 13 (Array_Type_Declaration 14 ((*ArrayT*) 3) ((*index subtype mark*) Integer) ((*component type*) (Subtype ((*I*) 2))))) 
(D_Seq_Declaration 15
(D_Procedure_Body 16 
  (mkprocedure_body 17
    (* = = = Procedure Name = = = *)
    ((*Increase*) 2)
    (* = = = Formal Parameters = = = *)
    (
    (mkparameter_specification 18 ((*X*) 4) Integer In) :: 
    (mkparameter_specification 19 ((*Y*) 5) Integer Out) :: nil)
    (* = = = Object Declarations = = = *)
    (D_Null_Declaration)
    (* = = = Procedure Body = = = *)
      (S_Assignment 20 (E_Identifier 21 ((*Y*) 5) ) (E_Binary_Operation 22 Plus (E_Name 23 (E_Identifier 24 ((*X*) 4) ) ) (E_Literal 25 (Integer_Literal 1) ) ))
  )
) 
(D_Seq_Declaration 26
(D_Object_Declaration 27 (mkobject_declaration 28 ((*R*) 6) (Record_Type ((*RecordT*) 1)) None)) 
(D_Seq_Declaration 29
(D_Object_Declaration 30 (mkobject_declaration 31 ((*A*) 7) (Array_Type ((*ArrayT*) 3)) None)) 
(D_Seq_Declaration 32
(D_Object_Declaration 34 (mkobject_declaration 35 ((*Result*) 8) Integer (Some ((E_Literal 33 (Integer_Literal 1) ))))) 
(D_Seq_Declaration 36
(D_Object_Declaration 39 (mkobject_declaration 40 ((*T*) 9) Integer (Some ((E_Name 37 (E_Identifier 38 ((*Result*) 8) ) ))))) 
(D_Seq_Declaration 41
(D_Object_Declaration 42 (mkobject_declaration 43 ((*T1*) 10) Integer None)) 
(D_Object_Declaration 44 (mkobject_declaration 45 ((*T2*) 11) Integer None))))))))))))
  (* = = = Procedure Body = = = *)
    (S_Sequence 46
    (S_Assignment 47 (E_Selected_Component 48 49 ((*R*) 6) ((*X*) 3) ) (E_Literal 52 (Integer_Literal 1) )) 
    (S_Sequence 53
    (S_Assignment 54 (E_Indexed_Component 55 56 ((*A*) 7) (E_Literal 58 (Integer_Literal 0) ) ) (E_Literal 59 (Integer_Literal 1) )) 
    (S_Sequence 60
    (S_Assignment 61 (E_Identifier 62 ((*T1*) 10) ) (E_Binary_Operation 63 Plus (E_Name 64 (E_Selected_Component 65 66 ((*R*) 6) ((*X*) 3) ) ) (E_Name 69 (E_Identifier 70 ((*N*) 1) ) ) )) 
    (S_Sequence 71
    (S_Assignment 72 (E_Identifier 73 ((*T2*) 11) ) (E_Binary_Operation 74 Plus (E_Name 75 (E_Indexed_Component 76 77 ((*A*) 7) (E_Literal 79 (Integer_Literal 0) ) ) ) (E_Name 80 (E_Identifier 81 ((*T1*) 10) ) ) )) 
    (S_Sequence 82
    (S_Assignment 83 (E_Identifier 84 ((*T*) 9) ) (E_Name 85 (E_Identifier 86 ((*T2*) 11) ) )) 
    (S_Sequence 87
    (S_Procedure_Call 88 89 ((*Increase*) 2) 
      ((E_Name 90 (E_Identifier 91 ((*T2*) 11) ) ) :: (E_Name 92 (E_Identifier 93 ((*T*) 9) ) ) :: nil)
    ) 
    (S_Sequence 94
    (S_If 95 (E_Binary_Operation 96 Greater_Than (E_Name 97 (E_Identifier 98 ((*T*) 9) ) ) (E_Literal 99 (Integer_Literal 0) ) )
      (S_Assignment 100 (E_Identifier 101 ((*T*) 9) ) (E_Binary_Operation 102 Plus (E_Name 103 (E_Identifier 104 ((*T*) 9) ) ) (E_Literal 105 (Integer_Literal 1) ) ))
      S_Null
    ) 
    (S_Sequence 106
    (S_If 107 (E_Binary_Operation 108 Greater_Than (E_Name 109 (E_Identifier 110 ((*T*) 9) ) ) (E_Literal 111 (Integer_Literal 1) ) )
      (S_Assignment 112 (E_Identifier 113 ((*T*) 9) ) (E_Binary_Operation 114 Plus (E_Name 115 (E_Identifier 116 ((*T*) 9) ) ) (E_Literal 117 (Integer_Literal 2) ) ))
      (S_Assignment 118 (E_Identifier 119 ((*T*) 9) ) (E_Binary_Operation 120 Minus (E_Name 121 (E_Identifier 122 ((*T*) 9) ) ) (E_Literal 123 (Integer_Literal 1) ) ))
    ) 
    (S_Sequence 124
    (S_While_Loop 125 (E_Binary_Operation 126 Greater_Than (E_Name 127 (E_Identifier 128 ((*T*) 9) ) ) (E_Literal 129 (Integer_Literal 0) ) )
      (S_Sequence 130
      (S_Assignment 131 (E_Identifier 132 ((*Result*) 8) ) (E_Binary_Operation 133 Divide (E_Binary_Operation 134 Multiply (E_Name 135 (E_Identifier 136 ((*Result*) 8) ) ) (E_Name 137 (E_Identifier 138 ((*T*) 9) ) ) ) (E_Name 139 (E_Identifier 140 ((*N*) 1) ) ) )) 
      (S_Assignment 141 (E_Identifier 142 ((*T*) 9) ) (E_Binary_Operation 143 Minus (E_Name 144 (E_Identifier 145 ((*T*) 9) ) ) (E_Literal 146 (Integer_Literal 1) ) )))
    ) 
    (S_Assignment 147 (E_Identifier 148 ((*M*) 2) ) (E_Name 149 (E_Identifier 150 ((*Result*) 8) ) )))))))))))
))) :: nil)
  (*//////////////////////////////////////*)
  (* = = = (3) type declaration map = = = *)
  (*//////////////////////////////////////*)
  ((((*RecordT*) 1), (Record_Type_Declaration 7 ((*RecordT*) 1) ((((*X*) 3), Integer) :: nil))) :: (((*ArrayT*) 3), (Array_Type_Declaration 14 ((*ArrayT*) 3) ((*index subtype mark*) Integer) ((*component type*) (Subtype ((*I*) 2))))) :: (((*I*) 2), (Subtype_Declaration 11 ((*I*) 2) Integer (Range 0 5))) :: nil)
  (*/////////////////////////////////////*)
  (* = = = (4) expression type map = = = *)
  (*/////////////////////////////////////*)
  ((146, Integer) :: (137, Integer) :: (92, Integer) :: (101, Integer) :: (110, Integer) :: (128, Integer) :: (119, Integer) :: (23, Integer) :: (104, Integer) :: (122, Integer) :: (86, Integer) :: (140, Integer) :: (113, Integer) :: (68, Integer) :: (59, Integer) :: (50, (Record_Type ((*RecordT*) 1))) :: (149, Integer) :: (134, Integer) :: (62, Integer) :: (80, Integer) :: (116, Integer) :: (98, Integer) :: (74, Integer) :: (38, Integer) :: (65, Integer) :: (142, Integer) :: (133, Integer) :: (115, Integer) :: (127, Integer) :: (136, Integer) :: (109, Integer) :: (91, Integer) :: (145, Integer) :: (73, Integer) :: (64, Integer) :: (55, Integer) :: (139, Integer) :: (67, (Record_Type ((*RecordT*) 1))) :: (58, Integer) :: (85, Integer) :: (148, Integer) :: (121, Integer) :: (22, Integer) :: (76, Integer) :: (103, Integer) :: (97, Integer) :: (79, Integer) :: (70, Integer) :: (52, Integer) :: (25, Integer) :: (37, Integer) :: (129, Integer) :: (138, Integer) :: (120, Integer) :: (96, Boolean) :: (150, Integer) :: (132, Integer) :: (105, Integer) :: (123, Integer) :: (114, Integer) :: (69, Integer) :: (78, (Array_Type ((*ArrayT*) 3))) :: (63, Integer) :: (90, Integer) :: (99, Integer) :: (144, Integer) :: (126, Boolean) :: (81, Integer) :: (135, Integer) :: (108, Boolean) :: (117, Integer) :: (57, (Array_Type ((*ArrayT*) 3))) :: (21, Integer) :: (48, Integer) :: (84, Integer) :: (93, Integer) :: (102, Integer) :: (75, Integer) :: (111, Integer) :: (51, Integer) :: (24, Integer) :: (33, Integer) :: (143, Integer) :: nil)
  (*/////////////////////////////////////////////////*)
  (* = = = (5) ast node to source location map = = = *)
  (*/////////////////////////////////////////////////*)
  ((146, (sloc (*Line*)40 (*Col*)16 (*EndLine*)40 (*EndCol*)16)) :: (137, (sloc (*Line*)39 (*Col*)27 (*EndLine*)39 (*EndCol*)27)) :: (92, (sloc (*Line*)27 (*Col*)17 (*EndLine*)27 (*EndCol*)17)) :: (101, (sloc (*Line*)29 (*Col*)7 (*EndLine*)29 (*EndCol*)7)) :: (110, (sloc (*Line*)32 (*Col*)7 (*EndLine*)32 (*EndCol*)7)) :: (128, (sloc (*Line*)38 (*Col*)10 (*EndLine*)38 (*EndCol*)10)) :: (119, (sloc (*Line*)35 (*Col*)7 (*EndLine*)35 (*EndCol*)7)) :: (23, (sloc (*Line*)11 (*Col*)12 (*EndLine*)11 (*EndCol*)12)) :: (104, (sloc (*Line*)29 (*Col*)12 (*EndLine*)29 (*EndCol*)12)) :: (122, (sloc (*Line*)35 (*Col*)12 (*EndLine*)35 (*EndCol*)12)) :: (86, (sloc (*Line*)26 (*Col*)9 (*EndLine*)26 (*EndCol*)10)) :: (140, (sloc (*Line*)39 (*Col*)32 (*EndLine*)39 (*EndCol*)32)) :: (113, (sloc (*Line*)33 (*Col*)7 (*EndLine*)33 (*EndCol*)7)) :: (68, (sloc (*Line*)24 (*Col*)12 (*EndLine*)24 (*EndCol*)12)) :: (59, (sloc (*Line*)23 (*Col*)12 (*EndLine*)23 (*EndCol*)12)) :: (50, (sloc (*Line*)22 (*Col*)4 (*EndLine*)22 (*EndCol*)4)) :: (149, (sloc (*Line*)42 (*Col*)9 (*EndLine*)42 (*EndCol*)14)) :: (134, (sloc (*Line*)39 (*Col*)18 (*EndLine*)39 (*EndCol*)27)) :: (62, (sloc (*Line*)24 (*Col*)4 (*EndLine*)24 (*EndCol*)5)) :: (80, (sloc (*Line*)25 (*Col*)17 (*EndLine*)25 (*EndCol*)18)) :: (116, (sloc (*Line*)33 (*Col*)12 (*EndLine*)33 (*EndCol*)12)) :: (98, (sloc (*Line*)28 (*Col*)7 (*EndLine*)28 (*EndCol*)7)) :: (74, (sloc (*Line*)25 (*Col*)10 (*EndLine*)25 (*EndCol*)18)) :: (38, (sloc (*Line*)18 (*Col*)18 (*EndLine*)18 (*EndCol*)23)) :: (65, (sloc (*Line*)24 (*Col*)10 (*EndLine*)24 (*EndCol*)12)) :: (142, (sloc (*Line*)40 (*Col*)7 (*EndLine*)40 (*EndCol*)7)) :: (133, (sloc (*Line*)39 (*Col*)17 (*EndLine*)39 (*EndCol*)32)) :: (115, (sloc (*Line*)33 (*Col*)12 (*EndLine*)33 (*EndCol*)12)) :: (127, (sloc (*Line*)38 (*Col*)10 (*EndLine*)38 (*EndCol*)10)) :: (136, (sloc (*Line*)39 (*Col*)18 (*EndLine*)39 (*EndCol*)23)) :: (109, (sloc (*Line*)32 (*Col*)7 (*EndLine*)32 (*EndCol*)7)) :: (91, (sloc (*Line*)27 (*Col*)13 (*EndLine*)27 (*EndCol*)14)) :: (145, (sloc (*Line*)40 (*Col*)12 (*EndLine*)40 (*EndCol*)12)) :: (73, (sloc (*Line*)25 (*Col*)4 (*EndLine*)25 (*EndCol*)5)) :: (64, (sloc (*Line*)24 (*Col*)10 (*EndLine*)24 (*EndCol*)12)) :: (55, (sloc (*Line*)23 (*Col*)4 (*EndLine*)23 (*EndCol*)7)) :: (139, (sloc (*Line*)39 (*Col*)32 (*EndLine*)39 (*EndCol*)32)) :: (67, (sloc (*Line*)24 (*Col*)10 (*EndLine*)24 (*EndCol*)10)) :: (58, (sloc (*Line*)23 (*Col*)6 (*EndLine*)23 (*EndCol*)6)) :: (85, (sloc (*Line*)26 (*Col*)9 (*EndLine*)26 (*EndCol*)10)) :: (148, (sloc (*Line*)42 (*Col*)4 (*EndLine*)42 (*EndCol*)4)) :: (121, (sloc (*Line*)35 (*Col*)12 (*EndLine*)35 (*EndCol*)12)) :: (22, (sloc (*Line*)11 (*Col*)12 (*EndLine*)11 (*EndCol*)16)) :: (76, (sloc (*Line*)25 (*Col*)10 (*EndLine*)25 (*EndCol*)13)) :: (103, (sloc (*Line*)29 (*Col*)12 (*EndLine*)29 (*EndCol*)12)) :: (97, (sloc (*Line*)28 (*Col*)7 (*EndLine*)28 (*EndCol*)7)) :: (79, (sloc (*Line*)25 (*Col*)12 (*EndLine*)25 (*EndCol*)12)) :: (70, (sloc (*Line*)24 (*Col*)16 (*EndLine*)24 (*EndCol*)16)) :: (52, (sloc (*Line*)22 (*Col*)11 (*EndLine*)22 (*EndCol*)11)) :: (25, (sloc (*Line*)11 (*Col*)16 (*EndLine*)11 (*EndCol*)16)) :: (37, (sloc (*Line*)18 (*Col*)18 (*EndLine*)18 (*EndCol*)23)) :: (129, (sloc (*Line*)38 (*Col*)14 (*EndLine*)38 (*EndCol*)14)) :: (138, (sloc (*Line*)39 (*Col*)27 (*EndLine*)39 (*EndCol*)27)) :: (120, (sloc (*Line*)35 (*Col*)12 (*EndLine*)35 (*EndCol*)16)) :: (96, (sloc (*Line*)28 (*Col*)7 (*EndLine*)28 (*EndCol*)11)) :: (150, (sloc (*Line*)42 (*Col*)9 (*EndLine*)42 (*EndCol*)14)) :: (132, (sloc (*Line*)39 (*Col*)7 (*EndLine*)39 (*EndCol*)12)) :: (105, (sloc (*Line*)29 (*Col*)16 (*EndLine*)29 (*EndCol*)16)) :: (123, (sloc (*Line*)35 (*Col*)16 (*EndLine*)35 (*EndCol*)16)) :: (114, (sloc (*Line*)33 (*Col*)12 (*EndLine*)33 (*EndCol*)16)) :: (69, (sloc (*Line*)24 (*Col*)16 (*EndLine*)24 (*EndCol*)16)) :: (78, (sloc (*Line*)25 (*Col*)10 (*EndLine*)25 (*EndCol*)10)) :: (63, (sloc (*Line*)24 (*Col*)10 (*EndLine*)24 (*EndCol*)16)) :: (90, (sloc (*Line*)27 (*Col*)13 (*EndLine*)27 (*EndCol*)14)) :: (99, (sloc (*Line*)28 (*Col*)11 (*EndLine*)28 (*EndCol*)11)) :: (144, (sloc (*Line*)40 (*Col*)12 (*EndLine*)40 (*EndCol*)12)) :: (126, (sloc (*Line*)38 (*Col*)10 (*EndLine*)38 (*EndCol*)14)) :: (81, (sloc (*Line*)25 (*Col*)17 (*EndLine*)25 (*EndCol*)18)) :: (135, (sloc (*Line*)39 (*Col*)18 (*EndLine*)39 (*EndCol*)23)) :: (108, (sloc (*Line*)32 (*Col*)7 (*EndLine*)32 (*EndCol*)11)) :: (117, (sloc (*Line*)33 (*Col*)16 (*EndLine*)33 (*EndCol*)16)) :: (57, (sloc (*Line*)23 (*Col*)4 (*EndLine*)23 (*EndCol*)4)) :: (21, (sloc (*Line*)11 (*Col*)7 (*EndLine*)11 (*EndCol*)7)) :: (48, (sloc (*Line*)22 (*Col*)4 (*EndLine*)22 (*EndCol*)6)) :: (84, (sloc (*Line*)26 (*Col*)4 (*EndLine*)26 (*EndCol*)4)) :: (93, (sloc (*Line*)27 (*Col*)17 (*EndLine*)27 (*EndCol*)17)) :: (102, (sloc (*Line*)29 (*Col*)12 (*EndLine*)29 (*EndCol*)16)) :: (75, (sloc (*Line*)25 (*Col*)10 (*EndLine*)25 (*EndCol*)13)) :: (111, (sloc (*Line*)32 (*Col*)11 (*EndLine*)32 (*EndCol*)11)) :: (51, (sloc (*Line*)22 (*Col*)6 (*EndLine*)22 (*EndCol*)6)) :: (24, (sloc (*Line*)11 (*Col*)12 (*EndLine*)11 (*EndCol*)12)) :: (33, (sloc (*Line*)17 (*Col*)23 (*EndLine*)17 (*EndCol*)23)) :: (143, (sloc (*Line*)40 (*Col*)12 (*EndLine*)40 (*EndCol*)16)) :: nil)
  (* = = = (6) name id to a pair of (name string, unique name string) map = = = *)
  (*/////////////////////////////////////////////////*)
  ((mkNameTable
  (*///////////////////////////////////*)
  (* = = = (1) variable names map = = = *)
  (*///////////////////////////////////*)
  ((8, ("Result", "ada://variable/Test+1:11/Result+17:4")) :: (11, ("T2", "ada://variable/Test+1:11/T2+20:4")) :: (2, ("M", "ada://parameter/Test+1:11/M+1:30")) :: (5, ("Y", "ada://parameter/Test+1:11/Increase+9:14/Y+9:35")) :: (4, ("X", "ada://parameter/Test+1:11/Increase+9:14/X+9:23")) :: (7, ("A", "ada://variable/Test+1:11/A+15:4")) :: (10, ("T1", "ada://variable/Test+1:11/T1+19:4")) :: (1, ("N", "ada://parameter/Test+1:11/N+1:17")) :: (9, ("T", "ada://variable/Test+1:11/T+18:4")) :: (3, ("X", "ada://component/Test+1:11/RecordT+3:9/X+4:7")) :: (6, ("R", "ada://variable/Test+1:11/R+14:4")) :: nil)
  (*////////////////////////////////////////////*)
  (* = = = (2) subprogram names map = = = *)
  (*////////////////////////////////////////////*)
  ((2, ("Increase", "ada://procedure_body/Test+1:11/Increase+9:14")) :: (1, ("Test", "ada://procedure_body/Test+1:11")) :: nil)
  (*//////////////////////////////////////*)
  (* = = = (3) package names map = = = *)
  (*//////////////////////////////////////*)
  (nil)
  (*/////////////////////////////////////*)
  (* = = = (4) type names map = = = *)
  (*/////////////////////////////////////*)
  ((2, ("I", "ada://subtype/Test+1:11/I+6:12")) :: (1, ("RecordT", "ada://ordinary_type/Test+1:11/RecordT+3:9")) :: (3, ("ArrayT", "ada://ordinary_type/Test+1:11/ArrayT+7:9")) :: nil)
))
).

