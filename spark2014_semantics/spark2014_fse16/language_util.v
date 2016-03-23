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

(** * Auxiliary Functions For Language *)
Section AuxiliaryFunctions_For_Language.

End AuxiliaryFunctions_For_Language.


(** * Auxiliary Functions For Language_Flagged *)

Section AuxiliaryFunctions_For_Language_Flagged.

  (** Check Flags Extraction Functions *)

  Function name_exterior_checks (n: nameRT): exterior_checks :=
    match n with
    | IdentifierRT ast_num x ex_cks => ex_cks
    | IndexedComponentRT ast_num x e ex_cks => ex_cks
    | SelectedComponentRT ast_num x f ex_cks => ex_cks
    end.

  Function exp_exterior_checks (e: expRT): exterior_checks :=
    match e with
    | LiteralRT ast_num l in_cks ex_cks => ex_cks
    | NameRT ast_num n => name_exterior_checks n
    | BinOpRT ast_num op e1 e2 in_cks ex_cks => ex_cks
    | UnOpRT ast_num op e in_cks ex_cks => ex_cks
    end.

  Definition update_exterior_checks_name n checks :=
    match n with
    | IdentifierRT ast_num x ex_checks => IdentifierRT ast_num x checks
    | IndexedComponentRT ast_num x e ex_checks => IndexedComponentRT ast_num x e checks
    | SelectedComponentRT ast_num x f ex_checks => SelectedComponentRT ast_num x f checks
    end.

  Definition update_exterior_checks_exp e checks :=
    match e with
    | LiteralRT ast_num l in_checks ex_checks => LiteralRT ast_num l in_checks checks
    | NameRT ast_num n => 
        let n' := update_exterior_checks_name n checks in 
          NameRT ast_num n'
    | BinOpRT ast_num bop e1 e2 in_checks ex_checks => BinOpRT ast_num bop e1 e2 in_checks checks
    | UnOpRT ast_num uop e in_checks ex_checks => UnOpRT ast_num uop e in_checks checks
    end.

  Lemma exp_updated_exterior_checks: forall e cks,
    exp_exterior_checks (update_exterior_checks_exp e cks) = cks.
  Proof.
    intros; destruct e; smack;
    destruct n; smack.
  Qed.

  Lemma name_updated_exterior_checks: forall n cks,
    name_exterior_checks (update_exterior_checks_name n cks) = cks.
  Proof.
    intros; destruct n; smack.
  Qed.

  Lemma exp_exterior_checks_refl: forall e,
    update_exterior_checks_exp e (exp_exterior_checks e) = e.
  Proof.
    destruct e; smack.
    destruct n; simpl; smack.
  Qed.

  Lemma name_exterior_checks_refl: forall n,
    update_exterior_checks_name n (name_exterior_checks n) = n.
  Proof.
    destruct n; smack.
  Qed.

  Lemma update_exterior_checks_exp_astnum_eq: forall e cks,
    expression_astnum_rt (update_exterior_checks_exp e cks) = expression_astnum_rt e.
  Proof.
    intros;
    destruct e; smack.
  Qed.

  Lemma update_exterior_checks_name_astnum_eq: forall n cks,
    name_astnum_rt (update_exterior_checks_name n cks) = name_astnum_rt n.
  Proof.
    intros;
    destruct n; smack.
  Qed.

End AuxiliaryFunctions_For_Language_Flagged.











