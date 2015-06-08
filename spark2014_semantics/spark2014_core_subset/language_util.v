Require Export language_flagged.

(** * Auxiliary Functions For Language *)
Section AuxiliaryFunctions_For_Language.

End AuxiliaryFunctions_For_Language.


(** * Auxiliary Functions For Language_Flagged *)

Section AuxiliaryFunctions_For_Language_Flagged.

  (** Check Flags Extraction Functions *)

  Function name_exterior_checks (n: name_x): exterior_checks :=
    match n with
    | E_Identifier_X ast_num x ex_cks => ex_cks
    | E_Indexed_Component_X ast_num x e ex_cks => ex_cks
    | E_Selected_Component_X ast_num x f ex_cks => ex_cks
    end.

  Function exp_exterior_checks (e: expression_x): exterior_checks :=
    match e with
    | E_Literal_X ast_num l in_cks ex_cks => ex_cks
    | E_Name_X ast_num n => name_exterior_checks n
    | E_Binary_Operation_X ast_num op e1 e2 in_cks ex_cks => ex_cks
    | E_Unary_Operation_X ast_num op e in_cks ex_cks => ex_cks
    end.

  Definition update_exterior_checks_name n checks :=
    match n with
    | E_Identifier_X ast_num x ex_checks => E_Identifier_X ast_num x checks
    | E_Indexed_Component_X ast_num x e ex_checks => E_Indexed_Component_X ast_num x e checks
    | E_Selected_Component_X ast_num x f ex_checks => E_Selected_Component_X ast_num x f checks
    end.

  Definition update_exterior_checks_exp e checks :=
    match e with
    | E_Literal_X ast_num l in_checks ex_checks => E_Literal_X ast_num l in_checks checks
    | E_Name_X ast_num n => 
        let n' := update_exterior_checks_name n checks in 
          E_Name_X ast_num n'
    | E_Binary_Operation_X ast_num bop e1 e2 in_checks ex_checks => E_Binary_Operation_X ast_num bop e1 e2 in_checks checks
    | E_Unary_Operation_X ast_num uop e in_checks ex_checks => E_Unary_Operation_X ast_num uop e in_checks checks
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
    expression_astnum_x (update_exterior_checks_exp e cks) = expression_astnum_x e.
  Proof.
    intros;
    destruct e; smack.
  Qed.

  Lemma update_exterior_checks_name_astnum_eq: forall n cks,
    name_astnum_x (update_exterior_checks_name n cks) = name_astnum_x n.
  Proof.
    intros;
    destruct n; smack.
  Qed.

End AuxiliaryFunctions_For_Language_Flagged.











