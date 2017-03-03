(** 
_AUTHOR_

<<
Zhi Zhang
Department of Computer and Information Sciences
Kansas State University
zhangzhi@ksu.edu
>>
*)

Require Export symboltable_module.
Require Export ast_rt.

(** * Symbol Table *)

(** it's used to map back to the source location once an error is detected in ast tree *)
Record source_location := sloc{
  line   : nat; 
  col    : nat; 
  endline: nat; 
  endcol : nat
}.

(** symbol table for normal SPARK program *)
Module Symbol_Table_Elements <: SymTable_Element.
  Definition Procedure_Decl := procBodyDecl.
  Definition Type_Decl := typeDecl.
  Definition Source_Location := source_location.
End Symbol_Table_Elements.

(** symbol table for SPARK program with run-time check decorations *)
Module Symbol_Table_Elements_RT <: SymTable_Element.
  Definition Procedure_Decl := procBodyDeclRT.
  Definition Type_Decl := typeDeclRT.
  Definition Source_Location := source_location.
End Symbol_Table_Elements_RT.

Module Symbol_Table_Module := SymbolTableM (Symbol_Table_Elements).

Module Symbol_Table_Module_RT := SymbolTableM (Symbol_Table_Elements_RT).

(** ** SymTab *)
Definition symTab := Symbol_Table_Module.symboltable.
Definition mkSymTab := Symbol_Table_Module.mkSymbolTable.
Definition proc_decl := Symbol_Table_Module.proc_decl.
Definition type_decl := Symbol_Table_Module.type_decl.

(** ** SymTabRT *)
Definition symTabRT := Symbol_Table_Module_RT.symboltable.
Definition mkSymTabRT := Symbol_Table_Module_RT.mkSymbolTable.
Definition proc_decl_rt := Symbol_Table_Module_RT.proc_decl.
Definition type_decl_rt := Symbol_Table_Module_RT.type_decl.

Definition level := Symbol_Table_Module.level.

(** * Symbol Table Operation *)

(** ** Symbol Table Operation for AST *)
(** name table and symbol table operations for program (AST) *)

Definition reside_nametable_vars := Symbol_Table_Module.reside_nametable_vars.
Definition reside_nametable_procs := Symbol_Table_Module.reside_nametable_procs.
Definition reside_nametable_pkgs := Symbol_Table_Module.reside_nametable_pkgs.
Definition reside_nametable_types := Symbol_Table_Module.reside_nametable_types.
Definition fetch_var_name := Symbol_Table_Module.fetch_var_name.
Definition fetch_proc_name := Symbol_Table_Module.fetch_proc_name.
Definition fetch_pkg_name := Symbol_Table_Module.fetch_pkg_name.
Definition fetch_type_name := Symbol_Table_Module.fetch_type_name.

Definition reside_symtable_vars := Symbol_Table_Module.reside_symtable_vars.
Definition reside_symtable_procs := Symbol_Table_Module.reside_symtable_procs.
Definition reside_symtable_types := Symbol_Table_Module.reside_symtable_types.
Definition reside_symtable_exps := Symbol_Table_Module.reside_symtable_exps.
Definition reside_symtable_sloc := Symbol_Table_Module.reside_symtable_sloc.
Definition fetch_var := Symbol_Table_Module.fetch_var.
Definition fetch_proc := Symbol_Table_Module.fetch_proc.
Definition fetch_type := Symbol_Table_Module.fetch_type.
Definition fetch_exp_type := Symbol_Table_Module.fetch_exp_type.
Definition fetch_sloc := Symbol_Table_Module.fetch_sloc.
Definition update_vars := Symbol_Table_Module.update_vars.
Definition update_procs := Symbol_Table_Module.update_procs.
Definition update_types := Symbol_Table_Module.update_types.
Definition update_exps := Symbol_Table_Module.update_exps.
Definition update_sloc := Symbol_Table_Module.update_sloc.

(** ** Symbol Table Operation for AST_RT *)
(** name table and symbol table operations for program with run-time check decorations (AST_RT) *)

Definition reside_nametable_vars_rt := Symbol_Table_Module_RT.reside_nametable_vars.
Definition reside_nametable_procs_rt := Symbol_Table_Module_RT.reside_nametable_procs.
Definition reside_nametable_pkgs_rt := Symbol_Table_Module_RT.reside_nametable_pkgs.
Definition reside_nametable_types_rt := Symbol_Table_Module_RT.reside_nametable_types.
Definition fetch_var_name_rt := Symbol_Table_Module_RT.fetch_var_name.
Definition fetch_proc_name_rt := Symbol_Table_Module_RT.fetch_proc_name.
Definition fetch_pkg_name_rt := Symbol_Table_Module_RT.fetch_pkg_name.
Definition fetch_type_name_rt := Symbol_Table_Module_RT.fetch_type_name.

Definition reside_symtable_vars_rt := Symbol_Table_Module_RT.reside_symtable_vars.
Definition reside_symtable_procs_rt := Symbol_Table_Module_RT.reside_symtable_procs.
Definition reside_symtable_types_rt := Symbol_Table_Module_RT.reside_symtable_types.
Definition reside_symtable_exps_rt := Symbol_Table_Module_RT.reside_symtable_exps.
Definition reside_symtable_sloc_rt := Symbol_Table_Module_RT.reside_symtable_sloc.
Definition fetch_var_rt := Symbol_Table_Module_RT.fetch_var.
Definition fetch_proc_rt := Symbol_Table_Module_RT.fetch_proc.
Definition fetch_type_rt := Symbol_Table_Module_RT.fetch_type.
Definition fetch_exp_type_rt := Symbol_Table_Module_RT.fetch_exp_type.
Definition fetch_sloc_rt := Symbol_Table_Module_RT.fetch_sloc.
Definition update_vars_rt := Symbol_Table_Module_RT.update_vars.
Definition update_procs_rt := Symbol_Table_Module_RT.update_procs.
Definition update_types_rt := Symbol_Table_Module_RT.update_types.
Definition update_exps_rt := Symbol_Table_Module_RT.update_exps.
Definition update_sloc_rt := Symbol_Table_Module_RT.update_sloc.



Definition fetch_array_index_type (st: symTab) (array_ast_num: astnum): option type :=
  match fetch_exp_type array_ast_num st with
  | Some (Array_Type t) =>
      match fetch_type t st with
      | Some (ArrayTypeDecl ast_num tn indexSubtypeMark componentType) =>
          Some indexSubtypeMark
      | _ => None
      end
  | _ => None
  end.

Definition fetch_array_index_type_rt (st: symTabRT) (array_ast_num: astnum): option type :=
  match fetch_exp_type_rt array_ast_num st with
  | Some (Array_Type t) =>
      match fetch_type_rt t st with
      | Some (ArrayTypeDeclRT ast_num tn indexSubtypeMark componentType) =>
          Some indexSubtypeMark
      | _ => None 
      end
  | _ => None
  end.

Inductive extract_subtype_range: symTab -> type -> range -> Prop :=
  | Extract_Range: forall t tn st td l u,
      subtype_num t = Some tn ->
      fetch_type tn st = Some td ->
      subtype_range td = Some (Range l u) ->
      extract_subtype_range st t (Range l u).

(* tm is a subtype_mark *)
Inductive extract_array_index_range: symTab -> typenum -> range -> Prop :=
  | Extract_Index_Range: forall t st a_ast_num tn tm typ tn' td l u, 
      fetch_type t st = Some (ArrayTypeDecl a_ast_num tn tm typ) ->
      subtype_num tm = Some tn' ->
      fetch_type tn' st = Some td ->
      subtype_range td = Some (Range l u) ->
      extract_array_index_range st t (Range l u).


Inductive extract_subtype_range_rt: symTabRT -> type -> rangeRT -> Prop :=
  | Extract_Range_RT: forall t tn st td l u,
      subtype_num t = Some tn ->
      fetch_type_rt tn st = Some td ->
      subtype_range_rt td = Some (RangeRT l u) ->
      extract_subtype_range_rt st t (RangeRT l u).


(* tm is a subtype_mark *)
Inductive extract_array_index_range_rt: symTabRT -> typenum -> rangeRT -> Prop :=
  | Extract_Index_Range_RT: forall t st a_ast_num tn tm typ tn' td l u, 
      fetch_type_rt t st = Some (ArrayTypeDeclRT a_ast_num tn tm typ) ->
      subtype_num tm = Some tn' ->
      fetch_type_rt tn' st = Some td ->
      subtype_range_rt td = Some (RangeRT l u) ->
      extract_array_index_range_rt st t (RangeRT l u).

(** * Help Lemmas *)
Lemma extract_array_index_range_rt_unique: forall st a l u l' u',
  extract_array_index_range_rt st a (RangeRT l u) ->
    extract_array_index_range_rt st a (RangeRT l' u') ->
      l = l' /\ u = u'.
Proof.
  intros.
  inversion H; inversion H0; subst.
  repeat progress match goal with
  | [H1: ?x = _, 
     H2: ?x = _ |- _] => rewrite H1 in H2; clear H1; inversion H2; subst
  end; auto.
Qed.

Ltac apply_extract_array_index_range_rt_unique := 
  match goal with
  | [H1: extract_array_index_range_rt _ ?a (RangeRT ?l ?u),
     H2: extract_array_index_range_rt _ ?a (RangeRT ?l' ?u') |- _] => 
      specialize (extract_array_index_range_rt_unique _ _ _ _ _ _ H1 H2);
      let HZ := fresh "HZ" in intros HZ; inversion HZ
  end.

Lemma extract_subtype_range_unique: forall st t l u l' u',
  extract_subtype_range_rt st t (RangeRT l u) ->
    extract_subtype_range_rt st t (RangeRT l' u') ->
      l = l' /\ u = u'.
Proof.
  intros;
  inversion H; inversion H0; smack.
Qed.

Ltac apply_extract_subtype_range_unique :=
  match goal with
  | [H1: extract_subtype_range_rt _ ?t _, 
     H2: extract_subtype_range_rt _ ?t _ |- _] => 
      specialize (extract_subtype_range_unique _ _ _ _ _ _ H1 H2);
      let HZ := fresh "HZ" in intros HZ; destruct HZ; subst
  end.

