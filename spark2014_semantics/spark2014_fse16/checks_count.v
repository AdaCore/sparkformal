(** 
_AUTHOR_

<<
Zhi Zhang
Department of Computer and Information Sciences
Kansas State University
zhangzhi@ksu.edu
>>
*)
Require Export checks_generator.

(** * Count the number of check flags *) 

Section Check_Count.

  Record cks_infor_t: Type := cks_infor {
    num_of_cks  : nat;
    division_cks: nat;
    overflow_cks: nat;
    range_cks   : nat
  }.
  
  Function conj_cks_infor (x1 x2 : cks_infor_t): cks_infor_t := 
    match x1, x2 with
    | cks_infor cksNum d o r, cks_infor cksNum1 d1 o1 r1 =>
        cks_infor (cksNum + cksNum1) (d + d1) (o + o1) (r + r1)
    end.
  
  Function compute_cks_infor (cks: check_flags) : cks_infor_t :=
    match cks with
    | nil => cks_infor 0 0 0 0
    | ck :: cks' => 
      let r := compute_cks_infor cks' in
      match ck with
      | DivCheck => 
          cks_infor (r.(num_of_cks) + 1) (r.(division_cks) + 1) r.(overflow_cks) r.(range_cks)
      | OverflowCheck =>
          cks_infor (r.(num_of_cks) + 1) r.(division_cks) (r.(overflow_cks) + 1) r.(range_cks)
      | RangeCheck    => 
          cks_infor (r.(num_of_cks) + 1) r.(division_cks) r.(overflow_cks) (r.(range_cks) + 1)
      | RangeCheckOnReturn => 
          cks_infor (r.(num_of_cks) + 1) r.(division_cks) r.(overflow_cks) (r.(range_cks) + 1)
      | _ => r
      end
    end.

  (** ** Count Check Flags For Expression *)

  Function count_exp_check_flags (e: expRT): cks_infor_t :=
    match e with
    | LiteralRT n l in_cks ex_cks =>
        compute_cks_infor (in_cks ++ ex_cks)
    | NameRT n nm =>
        count_name_check_flags nm
    | BinOpRT n op e1 e2 in_cks ex_cks =>
        conj_cks_infor (compute_cks_infor (in_cks ++ ex_cks))
                       (conj_cks_infor 
                          (count_exp_check_flags e1)
                          (count_exp_check_flags e2)
                       )
    | UnOpRT n op e in_cks ex_cks =>
        conj_cks_infor (compute_cks_infor (in_cks ++ ex_cks))
                       (count_exp_check_flags e)
     end

  (** ** Check Flags Comparison Function For Name *)

  with count_name_check_flags (n: nameRT): cks_infor_t :=
    match n with
    | IdentifierRT n x ex_cks =>
        compute_cks_infor ex_cks
    | IndexedComponentRT n x e ex_cks =>
        conj_cks_infor (compute_cks_infor ex_cks)
                       (conj_cks_infor 
                          (count_name_check_flags x)
                          (count_exp_check_flags e)
                       )
    | SelectedComponentRT n x f ex_cks =>
        conj_cks_infor (compute_cks_infor ex_cks)
                       (count_name_check_flags x)
    end.

  Function count_args_check_flags (le: list expRT): cks_infor_t :=
    match le with
    | nil => cks_infor 0 0 0 0
    | (e1 :: le1') =>
        conj_cks_infor (count_exp_check_flags e1) 
                       (count_args_check_flags le1')
    end.


  (** ** Count Check Flags For Statement *)

  Function count_stmt_check_flags (c: stmtRT): cks_infor_t :=
    match c with
    | NullRT => cks_infor 0 0 0 0
    | AssignRT n x e =>
        conj_cks_infor (count_name_check_flags x) 
                       (count_exp_check_flags e)
    | IfRT n e c1 c2 =>
        conj_cks_infor (count_exp_check_flags e) 
                       (conj_cks_infor 
                          (count_stmt_check_flags c1)
                          (count_stmt_check_flags c2)
                       )
    | WhileRT n e c =>
        conj_cks_infor (count_exp_check_flags e) 
                       (count_stmt_check_flags c)
    | CallRT n pn p args =>
        (count_args_check_flags args)
    | SeqRT n c1 c2 =>
        conj_cks_infor (count_stmt_check_flags c1) 
                       (count_stmt_check_flags c2)
    end.

  Function count_type_decl_check_flags (t: typeDeclRT): cks_infor_t :=
    match t with
    | SubtypeDeclRT n tn t (RangeRT l u) =>
        cks_infor 0 0 0 0
    | DerivedTypeDeclRT n tn t (RangeRT l u) =>
        cks_infor 0 0 0 0
    | IntegerTypeDeclRT n tn (RangeRT l u) =>  
        cks_infor 0 0 0 0
    | ArrayTypeDeclRT n tn tm t =>
        cks_infor 0 0 0 0
    | RecordTypeDeclRT n tn fs =>
        cks_infor 0 0 0 0
    end.

  Function count_object_decl_check_flags (o: objDeclRT): cks_infor_t :=
    match o with
    | mkobjDeclRT n x t None =>
        cks_infor 0 0 0 0
    | mkobjDeclRT n x t (Some e) =>
        count_exp_check_flags e
    end.

  Function count_object_decls_check_flags (lo: list objDeclRT): cks_infor_t :=
    match lo with
    | nil => cks_infor 0 0 0 0
    | o1 :: lo1' => 
        conj_cks_infor (count_object_decl_check_flags o1) 
                       (count_object_decls_check_flags lo1')
    end.

  Function count_param_spec_check_flags (param: paramSpecRT): cks_infor_t :=
    match param with
    | mkparamSpecRT n x m t =>
        cks_infor 0 0 0 0
    end.

  Function count_param_specs_check_flags (lparam: list paramSpecRT): cks_infor_t :=
    match lparam with
    | nil => cks_infor 0 0 0 0
    | param1 :: lparam1' => 
        conj_cks_infor (count_param_spec_check_flags param1) 
                       (count_param_specs_check_flags lparam1')
    end.

  (** ** Count Check Flags For Declaration *)

  Function count_declaration_check_flags (d: declRT): cks_infor_t :=
    match d with
    | NullDeclRT => cks_infor 0 0 0 0
    | TypeDeclRT n t => 
        count_type_decl_check_flags t
    | ObjDeclRT n o =>
        count_object_decl_check_flags o
    | ProcBodyDeclRT n p =>
        count_procedure_body_check_flags p
    | SeqDeclRT n d1 d2 =>
        conj_cks_infor (count_declaration_check_flags d1) (count_declaration_check_flags d2)
    end

  with count_procedure_body_check_flags (p: procBodyDeclRT): cks_infor_t :=
    match p with
    | mkprocBodyDeclRT n p params decls stmt =>
        conj_cks_infor (count_param_specs_check_flags params) 
                       (conj_cks_infor 
                          (count_declaration_check_flags decls)
                          (count_stmt_check_flags stmt)
                       )
    end.

  Definition count_option_declaration_check_flags (x: option declRT): cks_infor_t :=
    match x with
    | Some ast => count_declaration_check_flags ast
    | None => cks_infor 0 0 0 0
    end.

End Check_Count.









