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

(** * Run-Time Error *)
Inductive errorType: Type :=
    | DivByZero
    | OverflowError
    | RangeError.

(** * Return Value / State *)
(** Statement and expression evaluation returns one of the following results:
    - normal result;
    - run-time errors, which are required to be detected at run time,
      for example, overflow check and division by zero check;
    - unterminated state caused by infinite loop (only for functional semantics);
    - abnormal state, which includes compile time errors
      (for example, type checks failure and undefined variables), 
      bounded errors and erroneous execution. 
      In the future, the abnormal state can be refined into these 
      more precise categories (1.1.5);
*)

(* return value for exp/statement evaluation defined in inductive type *)
Inductive Ret (A:Type): Type :=
    | OK: A -> Ret A
    | RTE: errorType -> Ret A.


Arguments OK [A] _.
Arguments RTE [A] _.

(** the range of 32-bit (singed/unsigned) integer type: 
    - modulus : 2^32 ;
    - half_modulus : 2^31 ;
    - max_unsigned : 2^32 -1 ;
    - max_signed : 2^31 - 1 ;
    - min_signed : -2^31 ;
*)
Definition wordsize: nat := 32.
Definition modulus : Z := two_power_nat wordsize.
Definition half_modulus : Z := Z.div modulus 2.
Definition max_unsigned : Z := Z.sub modulus 1.
Definition max_signed : Z := Z.sub half_modulus 1.
Definition min_signed : Z := Z.opp half_modulus.

(** * Value *) 

(** Type of basic values*)

(** Type of stored values in the store *)
Inductive value: Type :=
    | Undefined
    | Int (n : Z)
    | Bool (n : bool)
    | ArrayV (a : list (arrindex * value)) (* in SPARK, array index may start from negative number *)
    | RecordV (r : list (idnum * value)).

Definition Division_Error: Ret value := RTE DivByZero.
Definition Overflow_Error: Ret value := RTE OverflowError.
Definition Range_Error: Ret value := RTE RangeError.


(** * Bound of Value *)

(** value is represented by a range, for a variable, if its initial value is undefined 
    or it's a parameter or its value is dynamically determined, then we use the range 
    of its type as its value, e.g. x: Integer; it's value is: (Interval Integer'First Integer'Last),
    x: Integer := 1; it's value is: (Interval 1 1);
    for boolean value, it doesn't matter whether it's true or false, so we just use Bool to 
    represent boolean value;
*)

Inductive bound : Type :=
  | Interval (l : Z) (u: Z)
  | Boolval
  | Aggregate.

Definition int32_bound : bound := (Interval min_signed max_signed).

(** check whether a value falls in a bound *)
Inductive in_bound: Z -> bound -> bool -> Prop :=
  | IB_True: forall v l u,
      (Zle_bool l v) && (Zle_bool v u) = true ->
      in_bound v (Interval l u) true
  | IB_False: forall v l u,
      (Zle_bool l v) && (Zle_bool v u) = false ->
      in_bound v (Interval l u) false.

(** * Value Operation *)
Module Math.

(** ** Arithmetic Operation *)

Definition add (v1 v2: value): option value := 
    match v1, v2 with
    | Int v1', Int v2' => Some (Int (v1' + v2'))
    | _, _ => None
    end.

Definition sub (v1 v2: value): option value := 
    match v1, v2 with
    | Int v1', Int v2' => Some (Int (v1' - v2'))
    | _, _ => None
    end.

Definition mul (v1 v2: value): option value :=
    match v1, v2 with
    | Int v1', Int v2' => Some (Int (v1' * v2'))
    | _, _ => None
    end.


(** map Ada operators to corresponding Coq operators:
    - div -> Z.quot
    - rem -> Z.rem
    - mod -> Z.modulo

      (Note: Ada "mod" has the following formula in Why:    
       - if y > 0 then EuclideanDivision.mod x y else EuclideanDivision.mod x y + y)
*)

Definition div (v1 v2: value): option value := 
    match v1, v2 with
    | Int v1', Int v2' => Some (Int (Z.quot v1' v2'))
    | _, _ => None
    end.

Definition rem (v1 v2: value): option value := 
    match v1, v2 with
    | Int v1', Int v2' => Some (Int (Z.rem v1' v2'))
    | _, _ => None
    end.

(* the keyword "mod" cannot redefined here, so we use "mod'" *)
Definition mod' (v1 v2: value): option value := 
    match v1, v2 with
    | Int v1', Int v2' => Some (Int (Z.modulo v1' v2'))
    | _, _ => None
    end.

(** ** Logic Operation  *)
Definition and (v1 v2: value): option value :=
    match v1, v2 with
    | Bool v1', Bool v2' => Some (Bool (andb v1' v2'))
    | _, _ => None
    end.

Definition or (v1 v2: value): option value :=
    match v1, v2 with
    | Bool v1', Bool v2' => Some (Bool (orb v1' v2'))
    | _, _ => None
    end.

(** ** Relational Operation *)
Definition eq (v1 v2: value): option value :=
    match v1, v2 with
    | Int v1', Int v2' => Some (Bool (Zeq_bool v1' v2'))
    | _, _ => None
    end.

Definition ne (v1 v2: value): option value :=
    match v1, v2 with
    | Int v1', Int v2' => Some (Bool (Zneq_bool v1' v2'))
    | _, _ => None
    end.

Definition gt (v1 v2: value): option value :=
    match v1, v2 with
    | Int v1', Int v2' => Some (Bool (Zgt_bool v1' v2'))
    | _, _ => None
    end.

Definition ge (v1 v2: value): option value :=
    match v1, v2 with
    | Int v1', Int v2' => Some (Bool (Zge_bool v1' v2'))
    | _, _ => None
    end.

Definition lt (v1 v2: value): option value :=
    match v1, v2 with
    | Int v1', Int v2' => Some (Bool (Zlt_bool v1' v2'))
    | _, _ => None
    end.

Definition le (v1 v2: value): option value :=
    match v1, v2 with
    | Int v1', Int v2' => Some (Bool (Zle_bool v1' v2'))
    | _, _ => None
    end.

(** Unary Operations *)
Definition unary_not (v: value): option value :=
    match v with
    | Bool v' => Some (Bool (negb v'))
    | _ => None
    end.

Definition unary_plus (v: value): option value := 
    match v with
    | Int v' => Some v
    | _ => None
    end.

Definition unary_minus (v: value): option value := 
    match v with
    | Int v' => Some (Int (Z.opp v'))
    | _ => None
    end.


(** * Binary Operation *)
Definition binary_operation (op: binary_operator) (v1: value) (v2: value): option value :=
    match op with
    | Equal => eq v1 v2
    | Not_Equal => ne v1 v2
    | Greater_Than => gt v1 v2
    | Greater_Than_Or_Equal => ge v1 v2
    | Less_Than => lt v1 v2
    | Less_Than_Or_Equal => le v1 v2
    | And => and v1 v2
    | Or => or v1 v2
    | Plus => add v1 v2
    | Minus => sub v1 v2
    | Multiply => mul v1 v2
    | Divide => div v1 v2
    | Modulus => mod' v1 v2
    end.

(** * Unary Operation *)
Definition unary_operation (op: unary_operator) (v: value): option value := 
    match op with
    | Not => unary_not v
(*  | Unary_Plus => unary_plus v *)
    | Unary_Minus => unary_minus v
    end. 

End Math. 

 
