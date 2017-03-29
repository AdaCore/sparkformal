Require Import environment.
Require Import Morphisms Relations SetoidList.

(* Import STACK. *)

(* Functional Scheme update_ind := Induction for update Sort Prop. *)
(* Functional Scheme updates_ind := Induction for updates Sort Prop. *)
(* Functional Scheme fetch_ind := Induction for fetch Sort Prop. *)


Module STORE_PROP (V:ENTRY).
  Module ST := STORE(V).
  Include ST.
  Functional Scheme update_ind := Induction for ST.update Sort Prop.
(*   Functional Scheme updates_ind := Induction for ST.updates Sort Prop. *)
  Functional Scheme fetch_ind := Induction for fetch Sort Prop.

  (* The AST provided by gnat/sireum are supposed to have no two variables sharing
   the same name. This should imply that there are no duplication of name in stacks. *)
  (* intra-store *)
  Definition NoDup (s : state) := 
    forall nme lvl sto (sto' sto'':store),
      frameG nme s = Some (lvl,sto) ->
      cuts_to nme sto = (sto',sto'') ->
      resides nme (List.tl sto'') = false.

  (* extra-store *)
  Definition NoDup_G (s : state) := 
    forall nme lvl sto s' s'',
      frameG nme s = Some (lvl,sto) ->
      cut_until s lvl s' s'' ->
      resideG nme s'' = false.



(** levels in the global stack match exactly their nesting levels. *)
Inductive exact_levelG:  state -> Prop :=
  | exact_levelG_nil: exact_levelG nil
  | exact_levelG_cons: forall stk fr,
      exact_levelG stk -> exact_levelG ((List.length stk, fr)::stk).


  Ltac rename_hyp1 h th :=
    match th with
    | in_bound _ _ _ => fresh "h_inbound"
    | updates ?sto ?x _ = _ => fresh "heq_updates_" sto "_" x
    | updates ?sto ?x _ = _ => fresh "heq_updates_" sto
    | updates ?sto ?x _ = _ => fresh "heq_updates_" x
    | updates ?sto ?x _ = _ => fresh "heq_updates"
    | update ?frm ?x _ = _ => fresh "heq_update_" frm "_" x
    | update ?frm ?x _ = _ => fresh "heq_update_" frm
    | update ?frm ?x _ = _ => fresh "heq_update_" x
    | update ?frm ?x _ = _ => fresh "heq_update"
    | updateG ?stk ?x _ = _ => fresh "heq_updateG_" stk "_" x
    | updateG ?stk ?x _ = _ => fresh "heq_updateG_" stk
    | updateG ?stk ?x _ = _ => fresh "heq_updateG_" x
    | updateG ?stk ?x _ = _ => fresh "heq_updateG"
    | fetchG ?x ?stk = _ => fresh "heq_SfetchG_" x "_" stk
    | fetchG ?x ?stk = _ => fresh "heq_SfetchG_" stk
    | fetchG ?x ?stk = _ => fresh "heq_SfetchG_" x
    | fetchG ?x ?stk = _ => fresh "heq_SfetchG"
    | fetch ?x ?frm = _ => fresh "heq_fetch_" x "_" frm
    | fetch ?x ?frm = _ => fresh "heq_fetch_" frm
    | fetch ?x ?frm = _ => fresh "heq_fetch_" x
    | fetch ?x ?frm = _ => fresh "heq_fetch"
    | fetches ?x ?sto = _ => fresh "heq_fetches_" x "_" sto
    | fetches ?x ?sto = _ => fresh "heq_fetches_" sto
    | fetches ?x ?sto = _ => fresh "heq_fetches_" x
    | fetches ?x ?sto = _ => fresh "heq_fetches"
    | cut_until ?st ?s ?fr ?paramsprf ?args (RTE ?er) => fresh "h_cut_until_RE"
    | cut_until ?st ?s ?fr ?paramsprf ?args (OK ?fr') => fresh "h_cut_until_" fr "_" fr'
    | cut_until ?st ?s ?fr ?paramsprf ?args ?fr' => fresh "h_cut_until_" fr "_" fr'
    | cut_until ?st ?s ?fr ?paramsprf ?args _ => fresh "h_cut_until_" fr
    | cut_until ?st ?s ?fr ?paramsprf ?args _ => fresh "h_cut_until"
    | exact_levelG ?CE => fresh "h_exct_lvl_" CE
    | exact_levelG ?CE => fresh "h_exct_lvl"
    end.

(*   Ltac rename_hyp ::= rename_hyp1. *)

  Lemma updates_ok_none : forall sto x v, updates sto x v = None <-> fetches x sto = None.
  Proof.
    intros.
    split;intro.
    - functional induction (updates sto x v).
      + discriminate.
      + discriminate.
      + unfold id in *. (* scorie from libhyprenaming *)
        simpl.
        rewrite e0.
        apply IHo.
        assumption.
      + reflexivity.
    - functional induction (fetches x sto).
      + discriminate.
      + unfold id in *. (* scorie from libhyprenaming *)
        simpl.
        rewrite e0.
        rewrite IHo;auto.
      + reflexivity.
  Qed.


  (* the none version could be solved by functiona inversion but it is
     not applicable here due to a bug in Function with functors. *)
  Lemma update_ok_none : forall frm x v, update frm x v = None <-> fetch x frm = None.
  Proof.
    intros.
    split.
    - functional induction (ST.update frm x v);intro.
      + discriminate.
      + unfold fetch.
        eapply updates_ok_none;eauto.
    - unfold fetch, update.
      intro heq_fetches_x.
      rewrite <- updates_ok_none in heq_fetches_x.
      rewrite heq_fetches_x.
      reflexivity.
  Qed.



  (* the none version could be solved by functiona inversion but it is
   ot applicable here due to a bug in Function with functors. *)
  Lemma updateG_ok_none : forall stk x v, updateG stk x v = None <-> fetchG x stk = None.
  Proof.
    intros.
    split.
    - functional induction (updateG stk x v);intro.
      + discriminate.
      + discriminate.
      + unfold id in *.
        simpl.
        apply update_ok_none in e0.
        rewrite e0.
        auto.
      + reflexivity.
    - functional induction (fetchG x stk);intro.
      + discriminate.
      + simpl.
        rewrite IHo;auto.
        rewrite <- update_ok_none in e0;eauto.
        rewrite e0;auto.
      + reflexivity.
  Qed.

  Lemma fetches_ok: forall id sto v, fetches id sto = Some v -> resides id sto = true.
  Proof.
    intros id sto v.
    functional induction (fetches id sto);intros heq;try discriminate.
    - inversion heq.
      subst.
      cbn.
      rewrite e0.
      reflexivity.
    - cbn.
      rewrite e0.
      auto.
  Qed.

  Lemma fetches_resides: forall nme x,
      (exists res, fetches nme x = Some res) <->
      resides nme x = true.
  Proof.
    intros ? ?.
    functional induction (fetches nme x);cbn;intros;subst.
    - rewrite e0.
      split;eauto.
    - rewrite e0.
      assumption.
    - split;intros; try discriminate.
      decompose [ex] H.
      discriminate.
  Qed.


  Lemma fetches_ok_none_1: forall id sto, fetches id sto = None -> resides id sto = false.
  Proof.
    intros id sto.
    functional induction (fetches id sto);intros;try discriminate.
    - cbn.
      rewrite e0.
      auto.
    - cbn.
      reflexivity.
  Qed.

  Lemma fetches_ok_none_2: forall id sto, resides id sto = false -> fetches id sto = None.
  Proof.
    intros id sto.
    functional induction (fetches id sto);intros;try discriminate; try auto.
    - cbn in H.
      rewrite e0 in H.
      discriminate.
    - cbn in H.
      rewrite e0 in H.
      auto.
  Qed.

  Lemma fetches_ok_none: forall id sto, fetches id sto = None <-> resides id sto = false.
  Proof.
    intros id sto.
    split.
    - apply fetches_ok_none_1;auto.
    - apply fetches_ok_none_2;auto.
  Qed.

  Lemma fetch_ok: forall id sto v, fetch id sto = Some v -> reside id sto = true.
  Proof.
    unfold fetch, reside.
    intros.
    apply fetches_ok in H.
    assumption.
  Qed.

  Lemma fetch_ok_none: forall id sto, fetch id sto = None -> reside id sto = false.
  Proof.
    unfold fetch, reside.
    intros.
    apply fetches_ok_none in H.
    assumption.
  Qed.

  Lemma fetchG_ok_none: forall id sto, fetchG id sto = None -> resideG id sto = false.
  Proof.
    intros id sto.
    functional induction (fetchG id sto);intros;try discriminate.
    - simpl.
      destruct (reside id f) eqn:heq_reside.
      + apply fetch_ok_none in e0.
        rewrite e0 in heq_reside;discriminate.
      + auto.
    - reflexivity. 
  Qed.

  Lemma fetchG_ok: forall id sto v, fetchG id sto = Some v -> resideG id sto = true.
  Proof.
    intros id sto.
    functional induction (fetchG id sto);intros;try discriminate.
    - simpl.
      destruct (reside id f) eqn:heq_reside.
      + reflexivity.
      + apply fetch_ok in e0.
        rewrite e0 in heq_reside;discriminate.
    - simpl.
      destruct (reside id f) eqn:heq_reside.
      + reflexivity.
      + apply IHo in H.
        assumption.
  Qed.

  Lemma updates_ok_same: forall sto id v sto',
      updates sto id v = Some sto'
      -> fetches id sto' = Some v.
  Proof.
    intros until v.
    functional induction (updates sto id v);intros;simpl in *;intros.
    - inversion H;simpl.
      rewrite e0.
      reflexivity.
    - inversion H;simpl.
      inversion e1;simpl.
      rewrite e0.
      apply IHo.
      assumption.
    - discriminate.
    - discriminate.
  Qed.

  Lemma updates_ok_same_orig: forall sto id v sto',
      updates sto id v = Some sto'
      -> exists v', fetches id sto = Some v'.
  Proof.
    intros sto id v.
    functional induction (updates sto id v);intros;simpl in *;intros.
    - rewrite e0.
      eauto.
    - rewrite e0.
      eapply IHo;eauto.
    - discriminate.
    - discriminate.
  Qed.

  Lemma updates_ok_same_resides: forall sto id v sto',
      updates sto id v = Some sto'
      -> resides id sto' = true.
  Proof.
    intros.
    eapply fetches_ok.
    eapply updates_ok_same;eauto.
  Qed.

  Lemma updates_ok_same_resides_orig: forall sto id v sto',
      updates sto id v = Some sto'
      -> resides id sto = true.
  Proof.
    intros.
    pose proof updates_ok_same_orig _ _ _ _ H.
    destruct H0.
    eapply fetches_ok;eauto.
  Qed.

  Lemma update_ok_same: forall frm id v frm',
      update frm id v = Some frm'
      -> fetch id frm' = Some v.
  Proof.
    intros until v.
    unfold fetch, update.
    intros.
    destruct (updates (store_of frm) id v) eqn:heq_upd.
    - inversion H;simpl.
      eapply updates_ok_same;eauto.
    - discriminate.
  Qed.


  Lemma update_ok_same_orig: forall frm id v frm',
      update frm id v = Some frm'
      -> exists v', fetch id frm = Some v'.
  Proof.
    intros until v.
    unfold fetch, update.
    intros.
    destruct (updates (store_of frm) id v) eqn:heq_upd.
    - inversion H;simpl.
      pose proof updates_ok_same_orig _ _ _ _ heq_upd.
      assumption.
    - discriminate.
  Qed.

  Lemma update_ok_same_reside: forall sto id v sto',
      update sto id v = Some sto'
      -> reside id sto' = true.
  Proof.
    intros.
    eapply fetch_ok.
    eapply update_ok_same;eauto.
  Qed.

  Lemma update_ok_same_reside_orig: forall sto id v sto',
      update sto id v = Some sto'
      -> reside id sto = true.
  Proof.
    intros.
    pose proof update_ok_same_orig _ _ _ _ H.
    destruct H0.
    eapply fetch_ok;eauto.
  Qed.

  Lemma updateG_ok_same: forall stk id v stk',
      updateG stk id v = Some stk'
      -> fetchG id stk' = Some v.
  Proof.
    intros until v.
    functional induction (updateG stk id v);simpl;intros.
    - inversion H;simpl.
      apply update_ok_same in e0.
      rewrite e0.
      reflexivity.
    - inversion H;simpl.
      specialize (IHo _ e1).
      destruct (fetch x f) eqn:h.
      + apply update_ok_none in e0.
        rewrite e0 in h;discriminate.
      + assumption.
    - discriminate.
    - discriminate.
  Qed.

  Lemma updateG_ok_same_orig: forall stk id v stk',
      updateG stk id v = Some stk'
      -> exists v', fetchG id stk = Some v'.
  Proof.
    intros until v.
    functional induction (updateG stk id v);simpl;intros;try discriminate.
    - inversion H;simpl.
      destruct (update_ok_same_orig _ _ _ _ e0).
      rewrite H0.
      eauto.
    - inversion H;simpl.
      apply update_ok_none in e0.
      rewrite e0.
      eapply IHo.
      eauto.
  Qed.

  Lemma updateG_ok_same_resideG: forall stk id v stk',
      updateG stk id v = Some stk'
      -> resideG id stk' = true.
  Proof.
    intros.
    eapply fetchG_ok.
    eapply updateG_ok_same.
    eauto.
  Qed.



  Lemma updates_ok_others: forall sto id v sto',
      updates sto id v = Some sto' ->
      forall id', id<>id' -> fetches id' sto = fetches id' sto'.
  Proof.
    intros until v.
    functional induction (updates sto id v);intros;simpl in *;intros.
    - inversion H;simpl.
      rewrite -> Nat.eqb_eq in e0.
      subst.
      apply Nat.neq_sym in H0.
      rewrite <- Nat.eqb_neq in H0.
      rewrite H0 in *.
      reflexivity.
    - inversion H;simpl.
      destruct (Nat.eq_dec id' y).
      + subst.
        rewrite Nat.eqb_refl in *.
        reflexivity.
      + rewrite <- Nat.eqb_neq in n.
        rewrite n in *.
        eapply IHo;eauto.
    - discriminate.
    - discriminate.
  Qed.

  Lemma update_ok_others: forall frm id v frm',
      update frm id v = Some frm' ->
      forall id', id<>id' -> fetch id' frm = fetch id' frm'.
  Proof.
    intros until v.
    functional induction (ST.update frm id v);destruct frm;simpl in *;intros.
    - inversion H;simpl.
      eapply updates_ok_others in e;eauto.
    - discriminate.
  Qed.

  Lemma update_ok_others_reside: forall frm id v frm',
      update frm id v = Some frm' ->
      forall id', id<>id' -> reside id' frm = reside id' frm'.
  Proof.
    intros ? ? ? ? heq_update_frm_id ? hneq. 
    pose proof update_ok_others _ _ _ _ heq_update_frm_id _ hneq.
    destruct (fetch id' frm) eqn:heq_fetch.
    - apply fetch_ok in heq_fetch.
      rewrite heq_fetch.
      symmetry in H.
      apply fetch_ok in H.
      rewrite H.
      reflexivity.
    - apply fetch_ok_none in heq_fetch.
      rewrite heq_fetch.
      symmetry in H.
      apply fetch_ok_none in H.
      rewrite H.
      reflexivity.
  Qed.

  Lemma updateG_ok_others: forall stk id v stk',
      updateG stk id v = Some stk' ->
      forall id', id<>id' -> fetchG id' stk = fetchG id' stk'.
  Proof.
    intros until v.
    functional induction (updateG stk id v);simpl;intros.
    - inversion H;simpl.
       (destruct (fetch id' f) eqn:h).
      + erewrite update_ok_others in h;eauto.
        rewrite h.
        reflexivity.
      + erewrite update_ok_others in h;eauto.
        rewrite h.
        reflexivity.
    - inversion H;simpl.
       (destruct (fetch id' f) eqn:h).
      + reflexivity.
      + eapply IHo;eauto.
    - discriminate.
    - discriminate.
  Qed.


  Lemma updateG_ok_others_resideG: forall frm id v frm',
      updateG frm id v = Some frm' ->
      forall id', id<>id' -> resideG id' frm = resideG id' frm'.
  Proof.
    intros ? ? ? ? heq_updateG_frm_id ? hneq.
    pose proof updateG_ok_others _ _ _ _ heq_updateG_frm_id _ hneq.
    destruct (fetchG id' frm) eqn:heq_fetchG.
    - apply fetchG_ok in heq_fetchG.
      rewrite heq_fetchG.
      symmetry in H.
      apply fetchG_ok in H.
      rewrite H.
      reflexivity.
    - apply fetchG_ok_none in heq_fetchG.
      rewrite heq_fetchG.
      symmetry in H.
      apply fetchG_ok_none in H.
      rewrite H.
      reflexivity.
  Qed.


  Lemma updateG_ok_same_frameG: forall stk id v lvl sto stk',
      updateG stk id v = Some stk'
      -> frameG id stk = Some (lvl,sto)
      -> exists sto', frameG id stk' = Some (lvl,sto').
  Proof.
    intros until v.
    functional induction (updateG stk id v);simpl;intros;try discriminate.
    - inversion H;simpl.
      pose proof update_ok_same_reside _ _ _ _ e0.
      pose proof update_ok_same_reside_orig _ _ _ _ e0.
      rewrite H1.
      rewrite H3 in H0.
      inversion H0;subst.
      unfold update in e0.
      cbn in *.
      destruct (updates sto x v) eqn:heq.
      + eauto.
      + discriminate.
    - inversion H;simpl.
      rewrite update_ok_none in e0.
      apply fetch_ok_none in e0.
      rewrite e0.
      rewrite e0 in H0.
      eauto.
  Qed.

  Lemma updateG_ok_same_frameG_orig: forall stk id v lvl sto stk',
      updateG stk id v = Some stk'
      -> frameG id stk' = Some (lvl,sto)
      -> exists sto', frameG id stk = Some (lvl,sto').
  Proof.
    intros until v.
    functional induction (updateG stk id v);simpl;intros;try discriminate.
    - inversion H;simpl;subst.
      pose proof update_ok_same_reside _ _ _ _ e0.
      pose proof update_ok_same_reside_orig _ _ _ _ e0.
      simpl in H0.
      rewrite H1 in H0.
      rewrite H2.
      inversion H0.
      unfold update in e0.
      cbn in *.
      destruct (updates (store_of f) x v) eqn:heq.
      + destruct f;simpl in *.
        subst;inversion e0.
        eauto.
      + discriminate.
    - inversion H;simpl;subst.
      simpl in H0.
      rewrite update_ok_none in e0.
      apply fetch_ok_none in e0.
      rewrite e0.
      rewrite e0 in H0.
      eapply IHo; eauto.
  Qed.

  Lemma reside_false_fetch_none: forall (id : idnum) (fr : frame), reside id fr = false <-> fetch id fr = None.
  Proof.
    intros id fr. 
    unfold reside, fetch in *.
    symmetry.
    apply fetches_ok_none.
  Qed.

  Lemma resideG_false_fetchG_none: forall (id : idnum) (sto : state), resideG id sto = false -> fetchG id sto = None.
  Proof.
    intros id sto.
    functional induction (resideG id sto);try now intros; discriminate.
    - intros h_resideG. 
      cbn.
      apply reside_false_fetch_none in e0.
      rewrite e0.
      auto.
    - intros;cbn.
      reflexivity.
  Qed.

  Lemma fetchG_ok_none_iff: forall sto id, fetchG id sto = None <-> resideG id sto = false.
  Proof.
    intros id sto.
    split;intros.
    - apply fetchG_ok_none;assumption.
    - apply resideG_false_fetchG_none;assumption.
  Qed.

  Lemma frameG_resideG_1: forall l nme, (exists x, frameG nme l = Some x) -> resideG nme l = true.
  Proof.
    intros l nme. 
    functional induction frameG nme l.
    - intros [x heq ].
      inversion heq;subst. clear heq.
      cbn in *.
      rewrite e0;auto.
    - intros [x heq ].
      cbn in *.
      rewrite e0.
      apply IHo.
      eauto.
    - intros  [x heq ].
      discriminate.
  Qed.


  Lemma frameG_resideG_2: forall l nme, resideG nme l = true -> exists x, frameG nme l = Some x.
  Proof.
    intros l nme. 
    functional induction resideG nme l.
    - intros _.
      cbn.
      rewrite e0;eauto.
    - intros h_eq.
      cbn in *.
      rewrite e0.
      eapply IHb.
      eauto.
    - intros abs. 
      discriminate.
  Qed.

  Lemma frameG_resideG: forall l nme, resideG nme l = true <-> exists x, frameG nme l = Some x.
  Proof.
    intros l nme. 
    split;intro h.
    - apply frameG_resideG_2;auto.
    - apply frameG_resideG_1;auto.
  Qed.

  
  Lemma cuts_to_decomp: forall nme sto sto' sto'',
      cuts_to nme sto = (sto', sto'')
      -> sto = sto'++sto''.
  Proof.
    intros nme sto. 
    functional induction cuts_to nme sto ;simpl.

    - intros sto' sto'' heq.
      inversion heq.
      reflexivity.
    - intros sto' sto'' heq.
      inversion heq; clear heq.
      simpl. subst.
      erewrite IHp;eauto.
    - intros sto' sto'' heq. 
      inversion heq;auto.
  Qed.

  Lemma cuts_to_snd: forall nme sto sto' sto'',
      cuts_to nme sto = (sto', sto'')
      -> sto'' = nil \/ exists x sto''', sto'' = (nme,x)::sto'''.
  Proof.
    intros nme sto. 
    functional induction cuts_to nme sto;simpl.
    - intros sto' sto'' H.
      inversion H.
      right.
      exists v, s'.
      rewrite Nat.eqb_eq in e0.
      subst;auto.
    - intros sto' sto'' H.
      inversion H; clear H.
      subst.
      eapply IHp;eauto.
    - intros sto' sto'' heq.
      inversion heq;auto.
  Qed.

  Lemma cuts_to_fst: forall nme sto sto' sto'',
      cuts_to nme sto = (sto', sto'')
      -> resides nme sto' = false.
  Proof.
    intros nme sto. 
    functional induction cuts_to nme sto;simpl.
    - intros sto' sto'' heq.
      inversion heq.
      reflexivity.
    - intros sto' sto'' heq.
      inversion heq; clear heq.
      simpl.
      rewrite e0.
      eapply IHp;eauto.
    - intros sto' sto'' heq.
      inversion heq;subst;auto.
  Qed.

  Lemma cuts_to_snd_reside: forall nme sto sto' sto'',
      resides nme sto = true
      -> cuts_to nme sto = (sto', sto'')
      -> exists x sto''', sto'' = (nme,x)::sto'''.
  Proof.
    intros nme sto sto' sto'' heq heq0.
    pose proof @cuts_to_snd _ _ _ _ heq0 as h_or.
    destruct h_or.
    - subst.
      pose proof cuts_to_fst _ _ _ _ heq0 as heq_bool_false.
      pose proof cuts_to_decomp _ _ _ _ heq0.
      subst.
      rewrite app_nil_r in *.
      rewrite heq_bool_false in heq. 
      discriminate.
    - inversion heq;auto.
  Qed.

  Lemma frameG_resides: forall nme s lvl sto, frameG nme s = Some (lvl, sto) ->  resides nme sto = true.
  Proof.
    intros nme s.
    functional induction frameG nme s.
    - intros lvl sto H. 
      inversion H.
      subst.
      assumption.
    - intros lvl sto H. 
      eapply IHo;eauto.
    - intros lvl sto H. 
      inversion H.
  Qed.

  Lemma exact_levelG_sublist: forall x CE,
      exact_levelG (x::CE)
      -> exact_levelG CE.
  Proof.
    intros x CE H.
    inversion H;cbn in *;auto.
  Qed.

Lemma cut_until_exact_levelG:
  forall s pb_lvl s' s'' ,
    exact_levelG s ->
    (pb_lvl <= Datatypes.length s)%nat ->
    cut_until s pb_lvl s'  s'' ->
    pb_lvl = Datatypes.length s''.
Proof.
  intros s pb_lvl s' s'' h_exactlvlG.
  revert pb_lvl s' s''.
  induction h_exactlvlG;simpl;intros ? ? ? h_lt h_cut.
  - inversion h_cut;subst;simpl in *.
    omega.
  - inversion h_lt;subst.
    + clear h_lt.        
      inversion h_cut;subst.
      * reflexivity.
      * simpl in *.
        exfalso;omega.
    + simpl in *.
      inversion h_cut;subst;simpl in *.
      * exfalso;omega.
      * eapply IHh_exactlvlG;eauto.
Qed.

Lemma cut_until_exact_levelG_2:
  forall s pb_lvl s' s'' ,
    exact_levelG s ->
    (pb_lvl > Datatypes.length s)%nat ->
    cut_until s pb_lvl s'  s'' ->
    Datatypes.length s = Datatypes.length s''.
Proof.
  intros s pb_lvl s' s'' h_exactlvlG.
  destruct h_exactlvlG;simpl.
  - intros H h_cut. inversion h_cut.
    reflexivity.
  - intros H h_cut. inversion h_cut;simpl in *;subst.
    + reflexivity.
    + exfalso;omega.
Qed.

Lemma exact_lvl_level_of_top:
  forall l',
    exact_levelG  l' ->
    forall nme lvl_nme fr_nme,
      frameG nme l' = Some (lvl_nme, fr_nme) -> 
      exists top,
        level_of_top l' = Some top /\
        (lvl_nme <= top)%nat.
Proof.
  intros l' h_exct_lvl_l'.
  induction h_exct_lvl_l';intros;subst.
  - discriminate.
  - cbn in H.
    destruct (resides nme fr) eqn:heq.
    + inversion H.
      cbn.
      eauto with arith.
    + cbn.
      exists (Datatypes.length stk);split;auto.
      edestruct IHh_exct_lvl_l';eauto.
      destruct H0 as [h h'].
      destruct stk;cbn in h;try discriminate.
      destruct f.
      inversion h.
      cbn.
      inversion h_exct_lvl_l';subst.
      auto with arith.
Qed.

Lemma nodup_G_cons :
  forall a l nme ,
    exact_levelG (a::l) ->
    NoDup_G (a::l) -> resideG nme l = true -> reside nme a = false.
Proof.
  intros a l nme h__exact h_nodupG h_reside. 
  destruct (reside nme a) eqn:?;auto.
  specialize (h_nodupG nme (level_of a) (store_of a) (a::nil) l).
  cbn in h_nodupG.
  rewrite h_reside,Heqb in h_nodupG.
  assert (Some a = Some (level_of a, store_of a)).
  { destruct a;auto. }
  specialize (h_nodupG H).
  clear H.
  assert (cut_until (a :: l) (level_of a) (a::nil) l).
  { constructor 3.
    - omega.
    - destruct l.
      + constructor 1.
      + constructor 2.
        inversion h__exact.
        inversion H0.
        subst.
        cbn.
        omega.  }
  specialize (h_nodupG H).
  discriminate.
Qed.


Lemma nodup_G_cons_2 :
  forall a l nme ,
    exact_levelG (a::l) ->
    NoDup_G (a::l) -> reside nme a = true -> resideG nme l = false.
Proof.
  intros a l nme h__exact h_nodupG h_reside. 
  destruct (resideG nme l) eqn:?;try discriminate;auto.

  specialize (h_nodupG nme (level_of a) (store_of a) (a::nil) l).
  cbn in h_nodupG.
  rewrite h_reside,Heqb in h_nodupG.
  assert (Some a = Some (level_of a, store_of a)).
  { destruct a;auto. }
  specialize (h_nodupG H).
  clear H.
  assert (cut_until (a :: l) (level_of a) (a::nil) l).
  { constructor 3.
    - omega.
    - destruct l.
      + constructor 1.
      + constructor 2.
        inversion h__exact.
        inversion H0.
        subst.
        cbn.
        omega.  }
  specialize (h_nodupG H).
  discriminate.
Qed.

Lemma stack_CE_NoDup_cons: forall l',
    exact_levelG l' ->
    NoDup_G l' ->
    NoDup l' ->
    forall l a,
      l'= a::l ->
      NoDup l.
Proof.
  intros l' H H0 H1 l a H2. 
  red.
  intros.
  red in H1.
  apply (H1 nme lvl sto sto' sto'').
  - subst.
    simpl.
    red in H0.
    assert (reside nme a = false).
    { eapply nodup_G_cons;eauto.
      eapply  frameG_resideG;eauto. }
    rewrite H2.
    assumption.
  - assumption.
Qed.



Lemma stack_CE_NoDup_G_cons: forall l',
    exact_levelG l' ->
    forall l a,
      l'= a::l ->
      NoDup_G (a::l) -> NoDup_G l.
Proof.
  intros ? h_exct_lvl_l'.
  induction h_exct_lvl_l';subst; intros; unfold NoDup_G in *;intros.
  - inversion H.
  - inversion H;subst.
    remember (Datatypes.length l, fr) as a0.
    assert (exact_levelG (a0 :: l)).
    { subst a0.
      constructor;auto. }
    assert (reside nme a0 = false).
    { eapply nodup_G_cons;eauto.
      eapply  frameG_resideG;eauto. }

    assert (frameG nme (a0 :: l) = Some (lvl, sto)).
    { cbn.
      rewrite H4.
      auto. }

    eapply H0 with (s':= a0 :: s');eauto.
    constructor 3.
    + pose proof exact_lvl_level_of_top (a0::l) as h.
      specialize h with (1:=H3) (2:=H5).
      destruct h as [top [h1 h2]].
      enough (lvl <= level_of a0)%nat by omega.

      assert (top = level_of a0).
      { cbn in h1.
        destruct a0;cbn.
        inversion h1; reflexivity. }
      subst top;auto with arith.
    + assumption.
Qed.


Lemma stack_CE_NoDup_G_sublist: forall CE1 CE2,
    exact_levelG (CE1 ++ CE2) ->
    NoDup_G (CE1++CE2) ->
    NoDup_G CE2.
Proof.
  induction CE1.
  - intros CE2 H h_nodupG. simpl List.app in h_nodupG.
    assumption.
  - intros CE2 H h_nodupG. apply IHCE1.
    { eapply exact_levelG_sublist;eauto. }
    cbn in h_nodupG.
    eapply stack_CE_NoDup_G_cons;eauto;cbn;auto.
Qed.

Lemma stack_CE_NoDup_sublist: forall CE1 CE2,
    exact_levelG (CE1 ++ CE2) ->
    NoDup_G (CE1++CE2) ->
    NoDup (CE1++CE2) ->
    NoDup CE2.
Proof.
  induction CE1.
  - intros CE2 H H0 h_nodup.
    simpl List.app in h_nodup.
    assumption.
  - intros CE2 H H0 h_nodup.
    apply IHCE1.
    + eapply exact_levelG_sublist;eauto.
    + eapply stack_CE_NoDup_G_cons;eauto;reflexivity.
    + cbn in h_nodup.
      eapply stack_CE_NoDup_cons;eauto;cbn;auto.
Qed.

Lemma cut_until_exct_lvl:
  forall CE lvl x,
    exact_levelG ((lvl,x)::CE) ->
    cut_until CE lvl nil CE.
Proof.
  intros CE lvl x h_exct_lvl.
  destruct CE;cbn in *.
  - constructor 1.
  - constructor 2.
    inversion h_exct_lvl;subst.
    inversion H0.
    cbn.
    omega.
Qed.




End STORE_PROP.
