(** 
_AUTHOR_

<<
Zhi Zhang
Department of Computer and Information Sciences
Kansas State University
zhangzhi@ksu.edu
>>
*)

Require Export environment.
Require Export Coq.Strings.String.

(** * Symbol Table Element *)

Record nametable := mkNameTable{
  varNames:  list (idnum * (string * string));
  procNames: list (procnum * (string * string));
  pkgNames: list (pkgnum * (string * string));
  typeNames: list (typenum * (string * string))
}.


Module Type SymTable_Element.

  Parameter Procedure_Decl: Type.

  Parameter Type_Decl: Type.
  
  Parameter Source_Location: Type.

End SymTable_Element.

(** * Symbol Table Module *)

Module SymbolTableM (S: SymTable_Element).

  Definition level := nat.
  
  Definition proc_decl := S.Procedure_Decl.

  Definition type_decl := S.Type_Decl.

  Definition source_location := S.Source_Location.
  
  (** ** Symbol Table Structure *)
  (** components of the symbol table:
      - vars : map each variable to its declared type and in/out mode;
      - procs: map each procedure name to its procedure declaration and 
               the nested level of its procedure declaration;
      - types: map each type name to its type declaration;
      - exps : record the type for each expression ast node;
      - sloc : map each ast node back to the source location in SPARK source code;
      - names: map name id, represented as natural number, to a pair of (name string, unique name string),
               e.g. 1 -> ("x", "ada://variable/pacakge_name/procedure_name_where_X_is_decalred/X+12:24")
  *)
 
  Record symboltable := mkSymbolTable{
    vars:  list (idnum * (mode * type));
    procs: list (procnum * (level * proc_decl));
    types: list (typenum * type_decl);
    exps: list (astnum * type);
    sloc: list (astnum * source_location); (*used to map back to the source location once an error is detected in ast tree*)
    names: nametable
  }.

  (** name table entry *)
  Module Entry_Name <: ENTRY.
    Definition T := prod string string.
  End Entry_Name.

  (** symbol table entry *)
  Module Entry_Type <: ENTRY.
    Definition T := prod mode type.
  End Entry_Type.

  Module Entry_Procedure_Decl <: ENTRY.
    Definition T := prod level proc_decl.
  End Entry_Procedure_Decl.

  Module Entry_Type_Decl <: ENTRY.
    Definition T := type_decl.
  End Entry_Type_Decl.

  Module Entry_Exp_Type <: ENTRY.
    Definition T := type.
  End Entry_Exp_Type.

  Module Entry_Sloc <: ENTRY.
    Definition T := source_location.
  End Entry_Sloc.

  (** name table module *)
  Module Names  := STORE(Entry_Name).
  
  (** symbol table module *)
  Module SymTable_Vars  := STORE(Entry_Type).
  Module SymTable_Procs := STORE(Entry_Procedure_Decl).
  Module SymTable_Types := STORE(Entry_Type_Decl).
  Module SymTable_Exps := STORE(Entry_Exp_Type).
  Module SymTable_Sloc := STORE(Entry_Sloc).

  (** ** Name Table Operation *)
  Function reside_nametable_vars  (x: idnum)   (nt: nametable) := Names.resides x nt.(varNames).
  Function reside_nametable_procs (x: procnum) (nt: nametable) := Names.resides x nt.(procNames).
  Function reside_nametable_pkgs  (x: pkgnum)  (nt: nametable) := Names.resides x nt.(pkgNames).
  Function reside_nametable_types (x: typenum) (nt: nametable) := Names.resides x nt.(typeNames).

  Function fetch_var_name  (x: idnum)   (nt: nametable) := Names.fetches x nt.(varNames).
  Function fetch_proc_name (x: procnum) (nt: nametable) := Names.fetches x nt.(procNames).
  Function fetch_pkg_name  (x: pkgnum)  (nt: nametable) := Names.fetches x nt.(pkgNames).
  Function fetch_type_name (x: typenum) (nt: nametable) := Names.fetches x nt.(typeNames).


  (** ** Symbol Table Operation *)

  Function reside_symtable_vars (x: idnum)   (st: symboltable) := SymTable_Vars.resides x st.(vars).
  Function reside_symtable_procs (x: procnum) (st: symboltable) := SymTable_Procs.resides x st.(procs).
  Function reside_symtable_types (x: typenum) (st: symboltable) := SymTable_Types.resides x st.(types).
  Function reside_symtable_exps (x: astnum) (st: symboltable) := SymTable_Exps.resides x st.(exps).
  Function reside_symtable_sloc (x: astnum) (st: symboltable) := SymTable_Sloc.resides x st.(sloc).

  Function fetch_var  (x: idnum)   (st: symboltable) := SymTable_Vars.fetches x st.(vars).
  Function fetch_proc (x: procnum) (st: symboltable) := SymTable_Procs.fetches x st.(procs).
  Function fetch_type (x: typenum) (st: symboltable) := SymTable_Types.fetches x st.(types).
  Function fetch_exp_type (x: astnum) (st: symboltable) := SymTable_Exps.fetches x st.(exps).
  Function fetch_sloc (x: astnum) (st: symboltable) := SymTable_Sloc.fetches x st.(sloc).

  Function update_store {V} (s: list (idnum * V)) (i: idnum) (v: V): list (idnum * V) :=
    match s with 
    | (i1, v1) :: s1 =>
        if beq_nat i1 i then
          (i1, v) :: s1
        else
          (i1, v1) :: (update_store s1 i v)
    | nil => (i, v) :: nil
    end.

  Arguments update_store {V} _ _ _.

  Function update_vars (st: symboltable) (x: idnum) (mt: mode * type): symboltable :=
    mkSymbolTable (update_store st.(vars) x mt) st.(procs) st.(types) st.(exps) st.(sloc) st.(names).

  Function update_procs (st: symboltable) (pid: procnum) (p: level * proc_decl): symboltable :=
    mkSymbolTable st.(vars) (update_store st.(procs) pid p) st.(types) st.(exps) st.(sloc) st.(names).

  Function update_types (st: symboltable) (tid: typenum) (td: type_decl): symboltable :=
    mkSymbolTable st.(vars) st.(procs) (update_store st.(types) tid td) st.(exps) st.(sloc) st.(names).

  Function update_exps (st: symboltable) (ast_num: astnum) (t: type): symboltable :=
    mkSymbolTable st.(vars) st.(procs) st.(types) (update_store st.(exps) ast_num t) st.(sloc) st.(names).

  Function update_sloc (st: symboltable) (ast_num: astnum) (sl: source_location): symboltable :=
    mkSymbolTable st.(vars) st.(procs) st.(types) st.(exps) (update_store st.(sloc) ast_num sl) st.(names).

  Function update_names (st: symboltable) (names: nametable): symboltable :=
    mkSymbolTable st.(vars) st.(procs) st.(types) st.(exps) st.(sloc) names.

End SymbolTableM.











































