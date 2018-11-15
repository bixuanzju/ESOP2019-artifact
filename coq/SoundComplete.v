
Require Import Infrastructure.
Require Import Assumed.
Require Import Algorithm.
Require Import List.
Require Import Omega.

Import ListNotations.

Lemma qvars_notin_union : forall Q s1 s2,
    qvars_notin s1 Q ->
    qvars_notin s2 Q ->
    qvars_notin (s1 \u s2) Q.
Proof with eauto.
  introv W.
  gen s2.
  induction W; introv S; inverts S; simpls...
Qed.


Lemma qvars_notin_union1 : forall Q s1 s2,
    qvars_notin (s1 \u s2) Q ->
    qvars_notin s1 Q.
Proof with eauto.
  intros Q.

  induction Q; introv W; simpls...

  destruct a; inverts W; simpls...
Qed.


Lemma qvars_notin_union2 : forall Q s1 s2,
    qvars_notin (s1 \u s2) Q ->
    qvars_notin s2 Q.
Proof with eauto.
  intros Q.

  induction Q; introv W; simpls...

  destruct a; inverts W; simpls...
Qed.


Lemma qvars_arr_append : forall Q A s,
    lc_sty A ->
    qvars_notin s Q ->
    qvars_notin s (Q ++ [qs_arr A]).
Proof with eauto.
  intros Q.

  induction Q; introv LC W; simpls...
  destruct a; inverts W...
Qed.


Lemma qvars_rcd_append : forall Q l s,
    qvars_notin s Q ->
    qvars_notin s (Q ++ [qs_rcd l]).
Proof with eauto.
  intros Q.

  induction Q; introv W; simpls...
  destruct a; inverts W...
Qed.


Lemma qvars_all_append : forall Q s X A,
    X `notin` s ->
    qvars_notin s Q ->
    qvars_notin s (Q ++ [qs_all X A]).
Proof with eauto.
  intros Q.
  induction Q; introv Not W; simpls...
  destruct a; inverts W...
Qed.

Lemma qvars_cons_rev : forall s a Q,
    qvars_notin s (a :: Q) ->
    qvars_notin s Q.
Proof with eauto.
  inversion 1; simpls...
Qed.

Ltac destruct_hypo :=
  match goal with
  | H: _ /\ _ |- _ => destruct H
  end.

Lemma qvars_append_rev : forall s Q1 Q2,
    qvars_notin s (Q1 ++ Q2) ->
    qvars_notin s Q1 /\ qvars_notin s Q2.
Proof with eauto.
  inductions Q1; introv H...
  rewrite cons_app_assoc in H.
  lets H2 : qvars_cons_rev H.
  forwards : IHQ1 H2. destruct_hypo.
  inversion H; splits...
Qed.

Hint Resolve qvars_arr_append qvars_all_append qvars_rcd_append qvars_cons_rev.

Lemma wf_fs_arr_append : forall Q A,
    wf_fs Q ->
    lc_sty A ->
    wf_fs (Q ++ [qs_arr A]).
Proof with eauto.
  introv WF.
  gen A.
  induction WF; introv LC; simpls...
Qed.


Lemma wf_fs_rcd_append : forall Q l,
    wf_fs Q ->
    wf_fs (Q ++ [qs_rcd l]).
Proof with eauto.
  introv WF.
  induction WF; simpls...
Qed.


Lemma wf_fs_all_append : forall Q X A,
    wf_fs Q ->
    lc_sty A ->
    X `notin` fv_sty_in_sty A ->
    X `notin` seqs_vars Q ->
    wf_fs (Q ++ [qs_all X A]).
Proof with eauto.
  introv WF.
  induction WF; introv LC NotV NotQ; simpls...
Qed.

Lemma wf_fs_rcd_append_rev : forall Q l,
    wf_fs (Q ++ [qs_rcd l]) ->
    wf_fs Q.
Proof with eauto.
  induction Q; introv H; simpls...
  inversions H; constructor...
  apply qvars_append_rev in H4.
  destruct_hypo...
  apply qvars_append_rev in H4.
  destruct_hypo...
Qed.

Lemma wf_fs_arr_append_rev : forall Q A,
  wf_fs (Q ++ [qs_arr A]) ->
  wf_fs Q /\ lc_sty A.
Proof with eauto.
  induction Q; introv H; simpls...
  - inversions H...
  - inversions H.
    + apply IHQ in H3. destruct_hypo.
      splits... constructor...
      apply qvars_append_rev in H4.
      destruct_hypo...
    + apply IHQ in H1. destruct_hypo.
      splits...
    + apply IHQ in H5. destruct_hypo.
      splits... constructor...
      apply qvars_append_rev in H4.
      destruct_hypo...
Qed.

Lemma wf_fs_all_append_rev : forall Q X A,
  wf_fs (Q ++ [qs_all X A]) ->
  wf_fs Q /\ lc_sty A /\ X `notin` seqs_vars Q.
Proof with eauto.
  induction Q; introv H; simpls...
  - inverts H...
  - inverts H.
    + apply IHQ in H3.
      repeat destruct_hypo.
      apply qvars_append_rev in H4.
      destruct_hypo.
      splits...
      inverts H4...

    + apply IHQ in H1.
      repeat destruct_hypo.
      splits...

    + apply IHQ in H5.
      repeat destruct_hypo.
      apply qvars_append_rev in H4.
      destruct_hypo.
      splits...
      inverts H5...
Qed.

Hint Resolve wf_fs_all_append wf_fs_rcd_append wf_fs_arr_append qvars_notin_union1 qvars_notin_union2 qvars_notin_union.



Lemma csub_regular : forall A B c,
    csub A B c -> lc_sty A /\ lc_sty B.
Proof with eauto.
  induction 1; repeat destruct_hypo;
    splits; introv...

  pick_fresh X.
  forwards ~ : H0 X.
  destruct_hypo.
  apply lc_sty_all_exists with X...

  pick_fresh X.
  forwards ~ : H0 X.
  destruct_hypo.
  apply lc_sty_all_exists with X...

  constructor... introv.
  inversions H. inversions H0.
  unfold open_sty_wrt_sty.
  simpls...
Qed.


Lemma asub_regular : forall Q A B c,
    asub A Q B c -> lc_sty A /\ lc_sty B /\ wf_fs Q.
Proof with eauto.
  induction 1; repeat destruct_hypo;
    try solve splits; introv...

  - splits...
    eapply wf_fs_rcd_append_rev...
  - apply wf_fs_arr_append_rev in H2.
    destruct_hypo...
  - pick_fresh X.
    forwards ~ : H0 X.
    repeat destruct_hypo.
    apply wf_fs_all_append_rev in H3.
    repeat destruct_hypo.
    splits...
    apply lc_sty_all_exists with X...
  - splits...
    eapply lc_sty_all_exists...
  - splits...
    eapply lc_sty_all_exists...
  - splits...
    eapply lc_sty_all_exists...
Qed.


Hint Extern 1 (lc_sty ?T) =>
  match goal with
  | H: csub _ ?T _ |- _ => apply (proj2 (csub_regular _ _ _ H))
  | H: csub ?T _ _ |- _ => apply (proj1 (csub_regular _ _ _ H))
  | H: asub ?T _ _ _ |- _ => apply (proj1 (asub_regular _ _ _ _ H))
  | H: asub _ _ ?T _ |- _ => apply (proj1 (proj2 (asub_regular _ _ _ _ H)))
  end.


Hint Extern 1 (wf_fs ?T) =>
  match goal with
  | H: asub _ ?T _ _ |- _ => apply (proj2 (proj2 (asub_regular _ _ _ _ H)))
  end.


Lemma applyfs_arr : forall Q B1 B2,
    applyfs (Q ++ [qs_arr B1]) B2 = applyfs Q (sty_arrow B1 B2).
Proof.
  intros.
  unfolds.
  rewrite fold_right_app.
  reflexivity.
Qed.

Lemma applyfs_rcd : forall Q l A,
    applyfs (Q ++ [qs_rcd l]) A = applyfs Q (sty_rcd l A).
Proof.
  intros.
  unfolds.
  rewrite fold_right_app.
  reflexivity.
Qed.


Lemma applyfs_all : forall Q X B A,
    applyfs (Q ++ [qs_all X B]) A = applyfs Q (sty_all B (close_sty_wrt_sty X A)).
Proof.
  intros.
  unfolds.
  rewrite fold_right_app.
  reflexivity.
Qed.



Lemma csub_subst : forall Z A B P c,
  csub A B c ->
  lc_sty A ->
  lc_sty B ->
  lc_sty P ->
  csub (subst_sty_in_sty P Z A) (subst_sty_in_sty P Z B) c.
Proof with eauto using subst_sty_in_sty_lc_sty, lc_body_sty_wrt_sty, lc_body_sty_all_2.
  introv Sub.
  gen Z P.
  induction Sub; introv LC1 LC2 LC3; simpls...

  - Case "CS_forall".

    pick fresh X and apply CS_forall...

    rewrite subst_sty_in_sty_open_sty_wrt_sty_var...
    rewrite subst_sty_in_sty_open_sty_wrt_sty_var...
    eapply H0...

  - Case "CS_distPoly".
    inverts LC1.
    pick fresh X.
    constructor...
    eapply lc_sty_all_exists...
    rewrite subst_sty_in_sty_open_sty_wrt_sty_var...
    eapply lc_sty_all_exists...
    rewrite subst_sty_in_sty_open_sty_wrt_sty_var...
Qed.



Lemma csub_rename : forall X Y A B c,
    X `notin` fv_sty_in_sty A ->
    X `notin` fv_sty_in_sty B ->
    Y `notin` fv_sty_in_sty A ->
    Y `notin` fv_sty_in_sty B ->
    csub (open_sty_wrt_sty A (sty_var_f X)) (open_sty_wrt_sty B (sty_var_f X)) c ->
    csub (open_sty_wrt_sty A (sty_var_f Y)) (open_sty_wrt_sty B (sty_var_f Y)) c.
Proof with eauto.
  introv ? ? ? ? Sub.
  destruct (X == Y); substs...
  replace (open_sty_wrt_sty A (sty_var_f Y)) with (subst_sty_in_sty (sty_var_f Y) X (open_sty_wrt_sty A (sty_var_f X)))...
  replace (open_sty_wrt_sty B (sty_var_f Y)) with (subst_sty_in_sty (sty_var_f Y) X (open_sty_wrt_sty B (sty_var_f X)))...
  eapply csub_subst...
  rewrite <- subst_sty_in_sty_intro...
  rewrite <- subst_sty_in_sty_intro...
Qed.

Lemma applyfs_notin : forall Q Y A,
    Y `notin` seqs_vars Q ->
    Y `notin` fv_sty_in_sty A ->
    Y `notin` (fv_sty_in_sty (applyfs Q A)).
Proof with eauto.
  intros Q.
  induction Q; introv Not1 Not2; simpls...

  destruct a; simpls...
  assert (Y `notin` (fv_sty_in_sty (close_sty_wrt_sty X (applyfs Q A)))).
  rewrite fv_sty_in_sty_close_sty_wrt_sty...
  solve_notin.
Qed.


Lemma applyfs_notin_close : forall Q Y X A,
    Y `notin` seqs_vars Q ->
    Y `notin` fv_sty_in_sty A \u (singleton X) ->
    Y `notin` fv_sty_in_sty (close_sty_wrt_sty X (applyfs Q A)).
Proof with eauto.
  intros.
  rewrite fv_sty_in_sty_close_sty_wrt_sty...
  forwards : applyfs_notin H...
Qed.


Lemma applyfs_lc : forall Q A,
    wf_fs Q ->
    lc_sty A ->
    lc_sty (applyfs Q A).
Proof with eauto.
  introv WF.
  gen A.
  induction WF; introv LC; simpls...

  pick fresh Y.
  eapply lc_sty_all_exists...
  rewrite open_sty_wrt_sty_close_sty_wrt_sty...

Qed.


Hint Resolve applyfs_lc.



(* ********************************************************************** *)
(** * Soundness *)

Lemma arrowTop : forall Q,
    wf_fs Q ->
    csub sty_top (applyfs Q sty_top) (calTop Q).
Proof with eauto.

  introv WF.
  induction WF; simpls...

  - Case "forall".
    eapply CS_trans...
    pick fresh Y and apply CS_forall...
    apply csub_rename with (X := X)...
    rewrite fv_sty_in_sty_close_sty_wrt_sty...
    eapply applyfs_notin_close...
    rewrite open_sty_wrt_sty_close_sty_wrt_sty...
Qed.


Lemma arrowAnd : forall Q A B,
    wf_fs Q ->
    lc_sty A ->
    lc_sty B ->
    csub (sty_and (applyfs Q A) (applyfs Q B)) (applyfs Q (sty_and A B)) (calAnd Q).
Proof with eauto.
  introv WF.
  induction WF; introv LC1 LC2; simpls...

  - Case "arrow".
    eapply CS_trans...

  - Case "rcd".
    eapply CS_trans...

  - Case "forall".
    specializes IHWF...

    apply CS_trans with (A2 := sty_all A0 (sty_and (close_sty_wrt_sty X (applyfs Q A)) (close_sty_wrt_sty X (applyfs Q B)))).
    pick fresh Y and apply CS_forall...
    apply csub_rename with (X := X); simpls...
    eapply notin_union; rewrite fv_sty_in_sty_close_sty_wrt_sty...
    rewrite fv_sty_in_sty_close_sty_wrt_sty...
    eapply notin_union; eapply applyfs_notin_close...
    eapply applyfs_notin_close...
    lets Hack: open_sty_wrt_sty_close_sty_wrt_sty.
    unfolds open_sty_wrt_sty; simpl...
    repeat rewrite Hack...
    econstructor...
    eapply lc_sty_all_exists...
    rewrite open_sty_wrt_sty_close_sty_wrt_sty...
    eapply lc_sty_all_exists...
    rewrite open_sty_wrt_sty_close_sty_wrt_sty...

Qed.


Theorem ASub2sub : forall Q A B c,
    asub A Q B c ->
    csub A (applyfs Q B) c.
Proof with eauto.
  introv H.
  induction H; simpls...

  - Case "A_top".
    eapply CS_trans...
    eapply arrowTop...

  - Case "A_and".
    eapply CS_trans...
    eapply arrowAnd...

  - Case "A_rcd".
    rewrite applyfs_rcd in IHasub...

  - Case "A_arr".
    rewrite applyfs_arr in IHasub...

  - Case "forall".
    pick fresh X.
    specializes H0...
    rewrite applyfs_all in H0.
    rewrite close_sty_wrt_sty_open_sty_wrt_sty in H0...


  - Case "A_allNat".
    pick fresh Y and apply CS_forall...
    eapply csub_rename...
    rewrite fv_sty_in_sty_close_sty_wrt_sty...
    eapply applyfs_notin_close...
    rewrite open_sty_wrt_sty_close_sty_wrt_sty...

  - Case "A_allNat".
    pick fresh Y and apply CS_forall...
    eapply csub_rename...
    rewrite fv_sty_in_sty_close_sty_wrt_sty...
    eapply applyfs_notin_close...
    rewrite open_sty_wrt_sty_close_sty_wrt_sty...

  - Case "A_allVar".
    pick fresh Z and apply CS_forall...
    eapply csub_rename...
    rewrite fv_sty_in_sty_close_sty_wrt_sty...
    eapply applyfs_notin_close...
    rewrite open_sty_wrt_sty_close_sty_wrt_sty...
Qed.



(* ********************************************************************** *)
(** * Reflexivity *)

(** [Rel A] denotes a set of reflexive supertypes of [A] *)
Inductive Rel : sty -> sty -> Prop :=
| R_nat : Rel sty_nat sty_nat
| R_var : forall X, Rel (sty_var_f X) (sty_var_f X)
| R_top : Rel sty_top sty_top
| R_bot : forall A,
    lc_sty A ->
    Rel sty_bot A
| R_rcd : forall l A B,
    Rel A B ->
    Rel (sty_rcd l A) (sty_rcd l B)
| R_and1 : forall A B C,
    Rel A C ->
    lc_sty B ->
    Rel (sty_and A B) C
| R_and2 : forall A B C,
    Rel B C ->
    lc_sty A ->
    Rel (sty_and A B) C
| R_and3 : forall A B,
    lc_sty A ->
    lc_sty B ->
    Rel (sty_and A B) (sty_and A B)
| R_arrow : forall A B B',
    Rel B B' ->
    lc_sty A ->
    Rel (sty_arrow A B) (sty_arrow A B')
| R_all : forall L A B B',
    lc_sty A ->
    (forall X, X \notin L ->
          Rel (open_sty_wrt_sty B (sty_var_f X))
              (open_sty_wrt_sty B' (sty_var_f X))) ->
    Rel (sty_all A B) (sty_all A B').


Hint Constructors Rel.

Notation "A ∈Super B" := (Rel B A)  (at level 1).



Lemma Rel_regular : forall A B,
    A ∈Super B -> lc_sty A /\ lc_sty B.
Proof with eauto.
  introv W.
  induction W; splits; try (inverts IHW); simpls...

  pick fresh X.
  forwards (? & ?) : H1...
  eapply lc_sty_all_exists...


  pick fresh X.
  forwards (? & ?) : H1...
  eapply lc_sty_all_exists...
Qed.


Hint Extern 1 (lc_sty ?T) =>
  match goal with
  | H: ?A ∈Super _ |- _ => apply (proj1 (Rel_regular _ _ H))
  | H: _ ∈Super ?A |- _ => apply (proj2 (Rel_regular _ _ H))
  end.


Lemma setRefl : forall A,
    lc_sty A -> A ∈Super A.
Proof with eauto.
  introv H.
  induction H...

  (* WTF *)
  Unshelve.
  exact (fv_sty_in_sty A).
Qed.



Lemma setAnd : forall A B C,
    lc_sty C ->
    lc_sty A ->
    lc_sty B ->
    (sty_and A B) ∈Super C ->
    A ∈Super C /\ B ∈Super C.
Proof with eauto using setRefl.
  introv LCC.
  gen A B.
  induction LCC; introv LCA LCB R; try solve [inverts R]...

  - Case "C is and".
    inverts R.

    forwards (? & ?): IHLCC1 LCA LCB...

    forwards (? & ?): IHLCC2 LCA LCB...

    splits...

Qed.



Inductive BotLike : sty -> Prop :=
| bl_bot : BotLike sty_bot
| bl_and1 : forall A B,
    BotLike A ->
    BotLike (sty_and A B)
| bl_and2 : forall A B,
    BotLike B ->
    BotLike (sty_and A B).

Hint Constructors BotLike.


Lemma Rel_BotLike: forall A,
    lc_sty A ->
    sty_bot ∈Super A ->
    BotLike A.
Proof with eauto.
  introv LC.
  induction LC; introv R; try solve [inverts R; eauto].
Qed.


Lemma BotLike_Rel : forall A B,
    BotLike A ->
    lc_sty A ->
    lc_sty B ->
    B ∈Super A.
Proof with eauto.
  introv Bot.
  gen B.

  induction Bot; introv LC1 LC2; simpls...

  inverts LC1...
  inverts LC1...
Qed.


Lemma setTrans : forall A B C,
    lc_sty B ->
    lc_sty A ->
    lc_sty C ->
    A ∈Super B ->
    B ∈Super C ->
    A ∈Super C.
Proof with eauto.
  introv LCB.
  gen A C.
  induction LCB; introv LCA LCC AsubB BsubC.

  inverts AsubB...
  inverts AsubB...
  eapply Rel_BotLike in BsubC...
  eapply BotLike_Rel...
  inverts AsubB...

  - Case "B is arrow".
    inverts AsubB.
    gen A B B'.
    induction LCC; intros; try inverts BsubC.

    + SCase "C is bot".
      inverts LCA...

    + SCase "C is arrow".
      inverts LCA...

    + SCase "C is and1".
      eapply R_and1...

    + SCase "C is and2".
      eapply R_and2...


  - Case "B is and".
    lets (? & ?) : setAnd BsubC...
    inverts AsubB...

  - Case "B is forall".
    inverts AsubB.
    gen A B B'.
    induction LCC; intros; try inverts BsubC.

    + SCase "C is bot".
      inverts LCA...

    + SCase "C is and1".
      eapply R_and1...

    + SCase "C is and2".
      eapply R_and2...

    + SCase "C is forall".
      clear IHLCC H0.
      inverts LCA.
      pick fresh X and apply R_all...

  - Case "B is record".
    gen A A0.
    induction C; intros; try inverts BsubC.

    + SCase "C is bot".
      inverts LCA...

    + SCase "C is and1".
      inverts AsubB.
      inverts LCA.
      constructor...

    + SCase "C is and2".
      inverts AsubB...

    + SCase "C is record".
      inverts AsubB...

Qed.



Notation "A ⊆R B" := (forall C, Rel A C -> Rel B C )  (at level 1).

Lemma setSubset : forall A B,
    A ∈Super B ->
    A ⊆R B.
Proof with eauto using setRefl.
  introv InR.
  induction InR...

  - Case "R_rcd".
    introv Sub.
    inverts Sub...

  - Case "R_arrow".
    introv Sub.
    inverts Sub...

  - Case "R_all".
    introv Sub.
    inverts Sub.
    pick fresh X and apply R_all...
Qed.



Lemma Rel_subst : forall Z A B P,
  Rel A B ->
  lc_sty A ->
  lc_sty B ->
  lc_sty P ->
  Rel (subst_sty_in_sty P Z A) (subst_sty_in_sty P Z B).
Proof with eauto using subst_sty_in_sty_lc_sty, lc_body_sty_wrt_sty, lc_body_sty_all_2, setRefl.
  introv W.
  gen Z P.
  induction W; introv LC1 LC2 LC3; simpls...

  - Case "Rel_var".
    destruct (X == Z)...

  - Case "Rel_all".

    pick fresh X and apply R_all...

    rewrite subst_sty_in_sty_open_sty_wrt_sty_var...
    rewrite subst_sty_in_sty_open_sty_wrt_sty_var...
    eapply H1...
Qed.



Lemma Rel_rename : forall X Y A B,
    X `notin` fv_sty_in_sty A ->
    X `notin` fv_sty_in_sty B ->
    Y `notin` fv_sty_in_sty A ->
    Y `notin` fv_sty_in_sty B ->
    Rel (open_sty_wrt_sty A (sty_var_f X)) (open_sty_wrt_sty B (sty_var_f X)) ->
    Rel (open_sty_wrt_sty A (sty_var_f Y)) (open_sty_wrt_sty B (sty_var_f Y)).
Proof with eauto.
  introv ? ? ? ? Sub.
  destruct (X == Y); substs...
  replace (open_sty_wrt_sty A (sty_var_f Y)) with (subst_sty_in_sty (sty_var_f Y) X (open_sty_wrt_sty A (sty_var_f X)))...
  replace (open_sty_wrt_sty B (sty_var_f Y)) with (subst_sty_in_sty (sty_var_f Y) X (open_sty_wrt_sty B (sty_var_f X)))...
  eapply Rel_subst...
  rewrite <- subst_sty_in_sty_intro...
  rewrite <- subst_sty_in_sty_intro...
Qed.



Lemma setList : forall Q A B,
    wf_fs Q ->
    lc_sty A ->
    lc_sty B ->
    (applyfs Q A) ∈Super (applyfs Q (sty_and A B)) /\
    (applyfs Q B) ∈Super (applyfs Q (sty_and A B)).
Proof with eauto using setRefl.

  introv WF.

  induction WF; introv LCA LCB; splits; simpls...

  specializes IHWF LCA LCB...
  specializes IHWF LCA LCB...
  specializes IHWF LCA LCB...
  specializes IHWF LCA LCB...
  specializes IHWF LCA LCB...

  pick fresh Y and apply R_all...
  eapply Rel_rename with (X := X).
  rewrite fv_sty_in_sty_close_sty_wrt_sty...
  rewrite fv_sty_in_sty_close_sty_wrt_sty...
  eapply applyfs_notin_close...
  eapply applyfs_notin_close...
  rewrite open_sty_wrt_sty_close_sty_wrt_sty...
  rewrite open_sty_wrt_sty_close_sty_wrt_sty...
  inverts IHWF...

  pick fresh Y and apply R_all...
  eapply Rel_rename with (X := X).
  rewrite fv_sty_in_sty_close_sty_wrt_sty...
  rewrite fv_sty_in_sty_close_sty_wrt_sty...
  eapply applyfs_notin_close...
  eapply applyfs_notin_close...
  rewrite open_sty_wrt_sty_close_sty_wrt_sty...
  rewrite open_sty_wrt_sty_close_sty_wrt_sty...
  apply IHWF...

Qed.



Lemma applyfs_arrow_append : forall Q B1 B2,
    applyfs (Q ++ [qs_arr B1]) B2 = applyfs Q (sty_arrow B1 B2).
Proof.
  intros.
  unfolds.
  rewrite fold_right_app.
  reflexivity.
Qed.


Lemma applyfs_rcd_append : forall Q l A,
    applyfs (Q ++ [qs_rcd l]) A = applyfs Q (sty_rcd l A).
Proof.
  intros.
  unfolds.
  rewrite fold_right_app.
  reflexivity.
Qed.


Lemma applyfs_all_append : forall Q X A B,
    applyfs (Q ++ [qs_all X B]) A = applyfs Q (sty_all B (close_sty_wrt_sty X A)).
Proof.
  intros.
  unfolds.
  rewrite fold_right_app.
  reflexivity.
Qed.


Lemma sizefs_cons : forall s Q,
    sizefs (s :: Q) = size_elem s + sizefs Q.
Proof.
  intros.
  simpls~.
Qed.

Lemma sizefs_append : forall s Q,
    sizefs (Q ++ [s]) = sizefs Q + size_elem s.
Proof with eauto.
  intros.
  induction Q.
  unfolds; simpls...

  simpls...
  repeat rewrite sizefs_cons...
  rewrite IHQ; omega.
Qed.


Lemma sizefs_nil : sizefs [] = 0.
Proof.
  unfolds.
  simpls~.
Qed.


Hint Rewrite sizefs_cons sizefs_append sizefs_nil : asub_rewrite.



Lemma fs_not_occur_subset : forall Q s1 s2,
    qvars_notin s2 Q ->
    s1 [<=] s2 ->
    qvars_notin s1 Q.
Proof with eauto.
  introv W.
  induction W; introv S; simpls...
  constructor...
Qed.


Lemma fs_not_occur_open : forall Q B Y,
    qvars_notin ((fv_sty_in_sty (sty_var_f Y)) \u fv_sty_in_sty B) Q ->
    qvars_notin (fv_sty_in_sty (open_sty_wrt_sty B (sty_var_f Y))) Q.
Proof with eauto.
  intros.
  eapply fs_not_occur_subset...
  apply fv_sty_in_sty_open_sty_wrt_sty_upper.
Qed.


Hint Resolve fs_not_occur_open.

Lemma set2Sub_aux : forall k Q A B,
    size_sty A + size_sty B + sizefs Q <= k ->
    lc_sty A ->
    lc_sty B ->
    wf_fs Q ->
    qvars_notin (fv_sty_in_sty A) Q ->
    (applyfs Q B) ∈Super A ->
    exists c, asub A Q B c.
Proof with eauto; autorewrite with asub_rewrite in *; simpls; try omega.
  intros k.
  induction k; introv HSize LCA LCB WF FS W.

  - Case "k = 0".
    inverts HSize.

    destruct LCB...

  - Case "k = S k".
    destruct LCB...

    + SCase "B is nat".
      destruct LCA...

      * SSCase "A = nat".
        inverts WF; try solve [inverts W]...
      * SSCase "A = top".
        inverts WF; try solve [inverts W]...
      * SSCase "A = var".
        inverts WF; try solve [inverts W]...

      * SSCase "A = arrow".
        inverts WF; try solve [inverts W]...

        inverts W as RelB.
        inverts FS.
        forwards RelA0: setRefl A0...
        change A0 with (applyfs [] A0) in RelA0.
        eapply IHk in RelA0...
        eapply IHk in RelB...
        destruct RelA0 as (c1 & ?).
        destruct RelB as (c2 & ?)...

      * SSCase "A = and".

        inverts WF.

        inverts W as W.
        eapply IHk in W...
        destruct W as (c & ?)...
        eapply IHk in W...
        destruct W as (c & ?)...


        inverts FS.
        inverts W as W.
        eapply IHk in W...
        destruct W as (c & ?)...
        eapply IHk in W...
        destruct W as (c & ?)...

        inverts FS.
        inverts W as W.
        eapply IHk in W...
        destruct W as (c & ?)...
        eapply IHk in W...
        destruct W as (c & ?)...

        inverts FS.
        inverts W as W.
        eapply IHk in W...
        destruct W as (c & ?)...
        eapply IHk in W...
        destruct W as (c & ?)...

      * SSCase "A = all".

        inverts WF; try solve [inverts W]...

        inverts FS...

        inverts W as ? RelB.
        forwards RelA0: setRefl A0...
        change A0 with (applyfs [] A0) in RelA0.
        eapply IHk in RelA0...
        pick fresh Y.
        specializes RelB...

        apply Rel_rename with (Y := X) in RelB...
        rewrite open_sty_wrt_sty_close_sty_wrt_sty in RelB...

        eapply IHk in RelB...
        destruct RelA0 as (c' & ?).
        destruct RelB as (c & ?).
        econstructor...

        rewrite size_sty_open_sty_wrt_sty_var...
        eapply applyfs_notin_close...
        rewrite fv_sty_in_sty_close_sty_wrt_sty...

      * SSCase "A = record".
        inverts WF; try solve [inverts W]...

        inverts FS...
        inverts W as W.
        eapply IHk in W...
        destruct W as (c & ?)...

    + SCase "B is bot".
      destruct LCA...

      * SSCase "A = nat".
        inverts WF; try solve [inverts W]...
      * SSCase "A = top".
        inverts WF; try solve [inverts W]...
      * SSCase "A = var".
        inverts WF; try solve [inverts W]...
      * SSCase "A = arrow".
        inverts WF; try solve [inverts W]...

        inverts W as RelB.
        inverts FS.
        forwards RelA0: setRefl A0...
        change A0 with (applyfs [] A0) in RelA0.
        eapply IHk in RelA0...
        eapply IHk in RelB...
        destruct RelA0 as (c1 & ?).
        destruct RelB as (c2 & ?)...

      * SSCase "A = and".

        inverts WF.

        inverts W as W.
        eapply IHk in W...
        destruct W as (c & ?)...
        eapply IHk in W...
        destruct W as (c & ?)...


        inverts FS.
        inverts W as W.
        eapply IHk in W...
        destruct W as (c & ?)...
        eapply IHk in W...
        destruct W as (c & ?)...

        inverts FS.
        inverts W as W.
        eapply IHk in W...
        destruct W as (c & ?)...
        eapply IHk in W...
        destruct W as (c & ?)...

        inverts FS.
        inverts W as W.
        eapply IHk in W...
        destruct W as (c & ?)...
        eapply IHk in W...
        destruct W as (c & ?)...

      * SSCase "A = all".

        inverts WF; try solve [inverts W]...

        inverts FS...

        inverts W as ? RelB.
        forwards RelA0: setRefl A0...
        change A0 with (applyfs [] A0) in RelA0.
        eapply IHk in RelA0...
        pick fresh Y.
        specializes RelB...

        apply Rel_rename with (Y := X) in RelB...
        rewrite open_sty_wrt_sty_close_sty_wrt_sty in RelB...

        eapply IHk in RelB...
        destruct RelA0 as (c' & ?).
        destruct RelB as (c & ?).
        econstructor...

        rewrite size_sty_open_sty_wrt_sty_var...
        eapply applyfs_notin_close...
        rewrite fv_sty_in_sty_close_sty_wrt_sty...

      * SSCase "A = record".
        inverts WF; try solve [inverts W]...

        inverts FS...
        inverts W as W.
        eapply IHk in W...
        destruct W as (c & ?)...

    + SCase "B is var".

      destruct LCA...

      * SSCase "A = nat".
        inverts WF; try solve [inverts W]...
      * SSCase "A = top".
        inverts WF; try solve [inverts W]...
      * SSCase "A = var".
        inverts WF; try solve [inverts W]...
        inverts W...
      * SSCase "A = arrow".
        inverts WF; try solve [inverts W]...

        inverts W as RelB.
        inverts FS.
        forwards RelA0: setRefl A0...
        change A0 with (applyfs [] A0) in RelA0.
        eapply IHk in RelA0...
        eapply IHk in RelB...
        destruct RelA0 as (c1 & ?).
        destruct RelB as (c2 & ?)...

      * SSCase "A = and".

        inverts WF.

        inverts W as W.
        eapply IHk in W...
        destruct W as (c & ?)...
        eapply IHk in W...
        destruct W as (c & ?)...


        inverts FS.
        inverts W as W.
        eapply IHk in W...
        destruct W as (c & ?)...
        eapply IHk in W...
        destruct W as (c & ?)...

        inverts FS.
        inverts W as W.
        eapply IHk in W...
        destruct W as (c & ?)...
        eapply IHk in W...
        destruct W as (c & ?)...

        inverts FS.
        inverts W as W.
        eapply IHk in W...
        destruct W as (c & ?)...
        eapply IHk in W...
        destruct W as (c & ?)...

      * SSCase "A = all".

        inverts WF; try solve [inverts W]...

        inverts FS...

        inverts W as ? RelB.
        forwards RelA0: setRefl A0...
        change A0 with (applyfs [] A0) in RelA0.
        eapply IHk in RelA0...
        pick fresh Y.
        specializes RelB ...

        apply Rel_rename with (Y := X0) in RelB...
        rewrite open_sty_wrt_sty_close_sty_wrt_sty in RelB...

        eapply IHk in RelB...
        destruct RelA0 as (c' & ?).
        destruct RelB as (c & ?).
        econstructor...

        rewrite size_sty_open_sty_wrt_sty_var...
        eapply applyfs_notin_close...
        rewrite fv_sty_in_sty_close_sty_wrt_sty...

      * SSCase "A = record".
        inverts WF; try solve [inverts W]...

        inverts FS...

        inverts W as W.
        eapply IHk in W...
        destruct W as (c & ?)...

    + SCase "B = arrow".
      rewrite <- applyfs_arrow_append in W.
      eapply IHk in W...
      destruct W as (c & ?)...

    + SCase "B = and".

      lets (FS1 & FS2) : setList Q A0 B...
      lets FSA0: setTrans FS1 W...
      lets FSB: setTrans FS2 W...
      eapply IHk in FSA0...
      destruct FSA0 as (c1 & ?).
      eapply IHk in FSB...
      destruct FSB as (c2 & ?)...

    + SCase "B = forall".
      pick fresh X.

      forwards Eq : close_sty_wrt_sty_open_sty_wrt_sty  B X...
      rewrite <- Eq in W. clear Eq.

      rewrite <- applyfs_all_append in W.
      eapply IHk in W; auto.
      destruct W as (c & ?).
      exists c...

      pick fresh Y and apply A_forall...
      eapply asub_rename...

      rewrite size_sty_open_sty_wrt_sty_var...

    + SCase "B = record".
      rewrite <- applyfs_rcd_append in W...
      eapply IHk in W...
      destruct W as (c & ?).
      exists c...

Qed.


Lemma set2Sub : forall Q A B,
    wf_fs Q ->
    lc_sty B ->
    qvars_notin (fv_sty_in_sty A) Q ->
    (applyfs Q B) ∈Super A ->
    exists c, asub A Q B c.
Proof.
  intros.
  apply set2Sub_aux with (size_sty A + size_sty B + sizefs Q); auto.
Qed.


Lemma asub_refl : forall A,
    lc_sty A ->
    exists c, asub A nil A c.
Proof with eauto.
  intros.
  apply set2Sub; simpls...
  apply setRefl...
Qed.


(* ********************************************************************** *)
(** * Transitivity *)

(** [asub_list Q1 A2] is pair-wise subtyping relations between [Q1] and [Q2] *)
Inductive asub_list : seqs -> seqs -> Prop :=
| phi_empty : asub_list [] []
| phi_arr : forall A B c Q1 Q2,
    asub_list Q1 Q2 ->
    asub A [] B c ->
    asub_list (qs_arr A :: Q1) (qs_arr B :: Q2)
| phi_rcd : forall l Q1 Q2,
    asub_list Q1 Q2 ->
    asub_list (qs_rcd l :: Q1) (qs_rcd l :: Q2)
| phi_all : forall X A B c Q1 Q2,
    asub_list Q1 Q2 ->
    asub A [] B c ->
    asub_list (qs_all X A :: Q1) (qs_all X B :: Q2).

Hint Constructors asub_list.


Lemma asub_list_arr_append : forall Q1 Q2 A B c,
    asub_list Q1 Q2 ->
    asub A [] B c ->
    asub_list (Q1 ++ [qs_arr A]) (Q2 ++ [qs_arr B]).
Proof with eauto.
  introv W.
  gen A B c.
  induction W; intros; simpls...
Qed.

Lemma asub_list_rcd_append : forall Q1 Q2 l,
    asub_list Q1 Q2 ->
    asub_list (Q1 ++ [qs_rcd l]) (Q2 ++ [qs_rcd l]).
Proof with eauto.
  introv W.
  induction W; intros; simpls...
Qed.


Lemma asub_list_all_append : forall Q1 Q2 X A B c,
    asub_list Q1 Q2 ->
    asub A [] B c ->
    asub_list (Q1 ++ [qs_all X A]) (Q2 ++ [qs_all X B]).
Proof with eauto.
  introv W.
  induction W; intros; simpls...
Qed.

(* Hint Resolve asub_list_all_append asub_list_arr_append asub_list_rcd_append. *)


Lemma seqs_vars_union : forall Q1 Q2,
    seqs_vars (Q1 ++ Q2) [=] seqs_vars Q1 \u seqs_vars Q2.
Proof with eauto.
  intros Q1.

  induction Q1; intros; simpls...

  fsetdec.

  rewrite IHQ1...

  fsetdec.
Qed.


Lemma qvars_notin_split: forall Q1 Q2 s,
    qvars_notin s (Q1 ++ Q2) ->
    qvars_notin s Q1 /\ qvars_notin s Q2.
Proof with eauto.
  intros Q1.
  induction Q1; introv Not; simpls...

  destruct a; inverts Not; simpls...

  forwards (? & ?): IHQ1...
  forwards (? & ?): IHQ1...
  forwards (? & ?): IHQ1...
Qed.




Lemma wf_fs_split : forall Q1 Q2,
    wf_fs (Q1 ++ Q2) ->
    wf_fs Q1 /\ wf_fs Q2.
Proof with eauto.
  intros Q1.
  induction Q1; introv WF; simpls...

  destruct a; inverts WF.

  forwards (? & ?): IHQ1...
  forwards (? & ?): qvars_notin_split...

  forwards (? & ?): IHQ1...
  forwards (? & ?): qvars_notin_split...


  forwards (? & ?): IHQ1...

Qed.


Lemma asub_trans_wrt_Q_aux : forall k A B C Q1 Q2 Q3 c1 c2,
    size_sty A + sizefs Q1 + size_sty B + sizefs Q2 + size_sty C + sizefs Q3 <= k ->
    lc_sty A ->
    lc_sty B ->
    lc_sty C ->
    asub A Q1 B c1 ->
    asub_list Q3 Q1 ->
    asub B Q2 C c2 ->
    wf_fs (Q3 ++ Q2) ->
    qvars_notin (fv_sty_in_sty A) Q2 ->
    exists c, asub A (Q3 ++ Q2) C c.
Proof with autorewrite with asub_rewrite in *; simpls; try omega; eauto.
  intros k.
  induction k; introv Size LCA LCB LCC AsubB Phi BsubC WF QVar.

  - Case "k = 0".
    inverts Size...
    destruct LCC...

  - Case "k = S k".
    destruct LCC.

    + SCase "C = nat".
      destruct LCB...

      * SSCase "B = nat".
        inverts BsubC...
        destruct LCA...

        ** SSSCase "A = nat".
           inverts AsubB.
           inverts Phi...

        ** SSSCase "A = top".
           inverts AsubB.

        ** SSSCase "A = var".
           inverts AsubB.

        ** SSSCase "A = arrow".
           inverts AsubB as ? HH1 HH2.
           inverts Phi as Phi HH.
           inverts WF.
           assert (HH' : asub sty_nat [] sty_nat co_id)...
           forwards (cc1 & ?): IHk HH2 Phi HH'...
           forwards (cc2 & ?): IHk HH phi_empty HH1...

        ** SSSCase "A = and".
           inverts AsubB as ? HH.

           assert (HH' : asub sty_nat [] sty_nat co_id)...
           forwards (cc & H) : >> IHk HH Phi HH'...

           assert (HH' : asub sty_nat [] sty_nat co_id)...
           forwards (cc & H) : >> IHk HH Phi HH'...

        ** SSSCase "A = all".
           simpl_env in *.
           inverts AsubB as ? ? ? ? ? HH1 HH2.
           inverts Phi as Phi HH.
           inverts WF.

           assert (HH' : asub sty_nat [] sty_nat co_id)...

           forwards (cc1 & ?): IHk HH2 Phi HH'...
           rewrite size_sty_open_sty_wrt_sty_var...
           simpl_env...

           forwards (cc2 & ?): IHk HH phi_empty HH1...

           exists (co_forall cc1).
           simpl_env in *...


        ** SSSCase "A = rcd".
           inverts AsubB as HH.
           inverts Phi as Phi.
           inverts WF.

           assert (HH' : asub sty_nat [] sty_nat co_id)...
           forwards (cc & ?) : >> IHk HH Phi HH'...

      * SSCase "B = top".
        inverts BsubC...

      * SSCase "B = bot".

        inverts BsubC...
        destruct LCA...

        ** SSSCase "A = nat".
           inverts AsubB.

        ** SSSCase "A = top".
           inverts AsubB.

        ** SSSCase "A = var".
           inverts AsubB.

        ** SSSCase "A = arrow".

           inverts AsubB as ? HH1 HH2.
           inverts Phi as Phi HH.
           inverts WF...
           assert (HH' : asub sty_bot Q2 sty_nat co_bot)...
           forwards (cc1 & ?): IHk HH2 Phi HH'...
           forwards (cc2 & ?): IHk HH phi_empty HH1...


        ** SSSCase "A = and".

           inverts AsubB as ? HH.

           assert (HH' : asub sty_bot Q2 sty_nat co_bot)...
           forwards (cc & ?) : IHk HH Phi HH'...

           assert (HH' : asub sty_bot Q2 sty_nat co_bot)...
           forwards (cc & ?) : >> IHk HH Phi HH'...

        ** SSSCase "A = all".
           inverts AsubB as ? ? ? ? ? HH1 HH2.
           inverts Phi as Phi HH.
           inverts WF as ? ? QVar2.
           forwards W : qvars_notin_union1 QVar2.
           forwards (? & ?) : qvars_append_rev W...

           assert (HH' : asub sty_bot Q2 sty_nat co_bot)...

           forwards (cc1 & ?): IHk HH2 Phi HH'...
           rewrite size_sty_open_sty_wrt_sty_var...

           forwards (cc2 & ?): IHk HH phi_empty HH1...

        ** SSSCase "A = rcd".
           inverts AsubB as HH.
           inverts Phi as Phi.
           inverts WF.

           assert (HH' : asub sty_bot Q2 sty_nat co_bot)...
           forwards (cc & ?) : >> IHk HH Phi HH'...


      * SSCase "B = var".
        inverts BsubC.

      * SSCase "B = arrow".

        inverts BsubC as ? HH1 HH2.
        inverts AsubB as HH...

        assert (Phi' : asub_list (Q3 ++ [qs_arr A3]) (Q1 ++ [qs_arr A0])).
          eapply asub_list_arr_append...

        forwards (cc & ?) : IHk HH Phi' HH2; simpl_env in *...
        unfold one...


      * SSCase "B = and".

        inverts  AsubB as HH1 HH2...
        inverts BsubC as ? HH...

        forwards (cc & ?) : IHk HH1 Phi HH...
        forwards (cc & ?) : IHk HH2 Phi HH...


      * SSCase "B = all".

        inverts BsubC as ? ? ? ? ? HH1 HH2...
        inverts QVar.

        forwards (? & ? & ?) : asub_regular AsubB...
        inverts AsubB as AsubB...
        pick_fresh Y.
        specializes AsubB...

        apply asub_rename with (Y := X) in AsubB...

        assert (Phi' : asub_list (Q3 ++ [qs_all X A3]) (Q1 ++ [qs_all X A0])).
          eapply asub_list_all_append...

        forwards (cc & ?) : IHk AsubB Phi' HH2...
        rewrite size_sty_open_sty_wrt_sty_var...
        unfold one...
        simpl_env...

        exists cc.
        simpl_env in *...



      * SSCase "B = rcd".

        inverts BsubC as HH1.
        inverts AsubB as HH2...

        assert (Phi' : asub_list (Q3 ++ [qs_rcd l]) (Q1 ++ [qs_rcd l])).
          eapply asub_list_rcd_append...

        forwards (cc & ?) : IHk HH2 Phi' HH1; simpl_env in *...
        unfold one...


    + SCase "C = top".
      exists (co_trans (calTop (Q3 ++ Q2)) co_top)...

    + SCase "C = bot".

      destruct LCB...

      * SSCase "B = nat".
        inverts BsubC...

      * SSCase "B = top".
        inverts BsubC...

      * SSCase "B = bot".
        inverts BsubC...

        destruct LCA...

        ** SSSCase "A = nat".
           inverts AsubB.

        ** SSSCase "A = top".
           inverts AsubB.

        ** SSSCase "A = var".
           inverts AsubB.

        ** SSSCase "A = arrow".
           inverts AsubB as ? HH1 HH2.
           inverts Phi as Phi HH.
           inverts WF.
           assert (HH' : asub sty_bot Q2 sty_bot co_bot)...
           forwards (cc1 & ?): IHk HH2 Phi HH'...
           forwards (cc2 & ?): IHk HH phi_empty HH1...

        ** SSSCase "A = and".

           inverts AsubB as ? HH.

           assert (HH' : asub sty_bot Q2 sty_bot co_bot)...
           forwards (cc & ?) : IHk HH Phi HH'...

           assert (HH' : asub sty_bot Q2 sty_bot co_bot)...
           forwards (cc & ?) : >> IHk HH Phi HH'...

        ** SSSCase "A = all".
           inverts AsubB as ? ? ? ? ? HH1 HH2.
           inverts Phi as Phi HH.
           inverts WF as ? ? QVar2.
           forwards W : qvars_notin_union1 QVar2.
           forwards (? & ?) : qvars_append_rev W...

           assert (HH' : asub sty_bot Q2 sty_bot co_bot)...

           forwards (cc1 & ?): IHk HH2 Phi HH'...
           rewrite size_sty_open_sty_wrt_sty_var...

           forwards (cc2 & ?): IHk HH phi_empty HH1...

        ** SSSCase "A = rcd".
           inverts AsubB as HH.
           inverts Phi as Phi.
           inverts WF.

           assert (HH' : asub sty_bot Q2 sty_bot co_bot)...
           forwards (cc & ?) : >> IHk HH Phi HH'...

      * SSCase "B = var".
        inverts BsubC...

      * SSCase "B = arrow".

        inverts BsubC as ? HH1 HH2.
        inverts AsubB as HH...

        assert (Phi' : asub_list (Q3 ++ [qs_arr A3]) (Q1 ++ [qs_arr A0])).
          eapply asub_list_arr_append...

        forwards (cc & ?) : IHk HH Phi' HH2; simpl_env in *...
        unfold one...


      * SSCase "B = and".

        inverts  AsubB as HH1 HH2...
        inverts BsubC as ? HH...

        forwards (cc & ?) : IHk HH1 Phi HH...
        forwards (cc & ?) : IHk HH2 Phi HH...


      * SSCase "B = all".

        inverts BsubC as ? ? ? ? ? HH1 HH2...
        inverts QVar.

        forwards (? & ? & ?) : asub_regular AsubB...
        inverts AsubB as AsubB...
        pick_fresh Y.
        specializes AsubB...

        apply asub_rename with (Y := X) in AsubB...

        assert (Phi' : asub_list (Q3 ++ [qs_all X A3]) (Q1 ++ [qs_all X A0])).
          eapply asub_list_all_append...

        forwards (cc & ?) : IHk AsubB Phi' HH2...
        rewrite size_sty_open_sty_wrt_sty_var...
        unfold one...
        simpl_env...

        exists cc.
        simpl_env in *...


      * SSCase "B = rcd".

        inverts BsubC as HH1.
        inverts AsubB as HH2...

        assert (Phi' : asub_list (Q3 ++ [qs_rcd l]) (Q1 ++ [qs_rcd l])).
          eapply asub_list_rcd_append...

        forwards (cc & ?) : IHk HH2 Phi' HH1; simpl_env in *...
        unfold one...


    + SCase "C = var".
      destruct LCB...

      * SSCase "B = nat".
        inverts BsubC.

      * SSCase "B = top".
        inverts BsubC...

      * SSCase "B = bot".

        inverts BsubC...
        destruct LCA...

        ** SSSCase "A = nat".
           inverts AsubB.

        ** SSSCase "A = top".
           inverts AsubB.

        ** SSSCase "A = var".
           inverts AsubB.

        ** SSSCase "A = arrow".

           inverts AsubB as ? HH1 HH2.
           inverts Phi as Phi HH.
           inverts WF...
           assert (HH' : asub sty_bot Q2 (sty_var_f X) co_bot)...
           forwards (cc1 & ?): IHk HH2 Phi HH'...
           forwards (cc2 & ?): IHk HH phi_empty HH1...


        ** SSSCase "A = and".

           inverts AsubB as ? HH.

           assert (HH' : asub sty_bot Q2 (sty_var_f X) co_bot)...
           forwards (cc & ?) : IHk HH Phi HH'...

           assert (HH' : asub sty_bot Q2 (sty_var_f X) co_bot)...
           forwards (cc & ?) : >> IHk HH Phi HH'...

        ** SSSCase "A = all".
           inverts AsubB as ? ? ? ? ? HH1 HH2.
           inverts Phi as Phi HH.
           inverts WF as ? ? QVar2.
           forwards W : qvars_notin_union1 QVar2.
           forwards (? & ?) : qvars_append_rev W...

           assert (HH' : asub sty_bot Q2 (sty_var_f X) co_bot)...

           forwards (cc1 & ?): IHk HH2 Phi HH'...
           rewrite size_sty_open_sty_wrt_sty_var...

           forwards (cc2 & ?): IHk HH phi_empty HH1...

        ** SSSCase "A = rcd".
           inverts AsubB as HH.
           inverts Phi as Phi.
           inverts WF.

           assert (HH' : asub sty_bot Q2 (sty_var_f X) co_bot)...
           forwards (cc & ?) : >> IHk HH Phi HH'...

      * SSCase "B = var".
        inverts BsubC.
        destruct LCA...

        ** SSSCase "A = nat".
           inverts AsubB.

        ** SSSCase "A = top".
           inverts AsubB.

        ** SSSCase "A = var".
           inverts AsubB.
           inverts Phi...

        ** SSSCase "A = arrow".
           inverts AsubB as ? HH1 HH2.
           inverts Phi as Phi HH.
           inverts WF.
           assert (HH' : asub (sty_var_f X) [] (sty_var_f X) co_id)...
           forwards (cc1 & ?): IHk HH2 Phi HH'...
           forwards (cc2 & ?): IHk HH phi_empty HH1...

        ** SSSCase "A = and".
           inverts AsubB as ? HH.

           assert (HH' : asub (sty_var_f X) [] (sty_var_f X) co_id)...
           forwards (cc & H) : >> IHk HH Phi HH'...

           assert (HH' : asub (sty_var_f X) [] (sty_var_f X) co_id)...
           forwards (cc & H) : >> IHk HH Phi HH'...

        ** SSSCase "A = all".
           simpl_env in *.
           inverts AsubB as ? ? ? ? ? HH1 HH2.
           inverts Phi as Phi HH.
           inverts WF.

           assert (HH' : asub (sty_var_f X) [] (sty_var_f X) co_id)...

           forwards (cc1 & ?): IHk HH2 Phi HH'...
           rewrite size_sty_open_sty_wrt_sty_var...
           simpl_env...

           forwards (cc2 & ?): IHk HH phi_empty HH1...

           exists (co_forall cc1).
           simpl_env in *...


        ** SSSCase "A = rcd".
           inverts AsubB as HH.
           inverts Phi as Phi.
           inverts WF.

           assert (HH' : asub (sty_var_f X) [] (sty_var_f X) co_id)...
           forwards (cc & ?) : >> IHk HH Phi HH'...


      * SSCase "B = arrow".

        inverts BsubC as ? HH1 HH2.
        inverts AsubB as HH...

        assert (Phi' : asub_list (Q3 ++ [qs_arr A3]) (Q1 ++ [qs_arr A0])).
          eapply asub_list_arr_append...

        forwards (cc & ?) : IHk HH Phi' HH2; simpl_env in *...
        unfold one...


      * SSCase "B = and".

        inverts  AsubB as HH1 HH2...
        inverts BsubC as ? HH...

        forwards (cc & ?) : IHk HH1 Phi HH...
        forwards (cc & ?) : IHk HH2 Phi HH...


      * SSCase "B = all".

        inverts BsubC as ? ? ? ? ? HH1 HH2.
        inverts QVar.
        forwards (? & ? & ?) : asub_regular AsubB...
        inverts AsubB as HH...

        pick_fresh Y.
        specializes HH...

        apply asub_rename with (Y := X0) in HH...

        assert (Phi' : asub_list (Q3 ++ [qs_all X0 A3]) (Q1 ++ [qs_all X0 A0])).
          eapply asub_list_all_append...

        forwards (cc & ?) : IHk HH Phi' HH2...
        rewrite size_sty_open_sty_wrt_sty_var...
        unfold one...
        simpl_env...

        exists cc...
        simpl_env in *...

      * SSCase "B = rcd".

        inverts BsubC as HH1.
        inverts AsubB as HH2...

        assert (Phi' : asub_list (Q3 ++ [qs_rcd l]) (Q1 ++ [qs_rcd l])).
          eapply asub_list_rcd_append...

        forwards (cc & ?) : IHk HH2 Phi' HH1; simpl_env in *...
        unfold one...


    + SCase "C = arrow".

      inverts BsubC as HH HH2.

      * SSCase "bot".
        assert (HH' : asub sty_bot (Q2 ++ [qs_arr A0]) B0 co_bot)...
        forwards (cc & ?) : IHk AsubB Phi HH'...
        rewrite_env ((Q3 ++ Q2) ++ [qs_arr A0]).
        eapply wf_fs_arr_append...
        exists cc.
        constructor; simpl_env...

      * SSCase "arrow".
        forwards (cc & ?) : IHk AsubB Phi HH...
        rewrite app_assoc.
        eapply wf_fs_arr_append...

        exists cc.
        constructor; simpl_env...

    + SCase "C = and".
      inverts BsubC as HH1 HH2.

      * SSCase "bot".
        assert (HH1' : asub sty_bot Q2 A0 co_bot)...
        assert (HH2' : asub sty_bot Q2 B0 co_bot)...
        forwards (cc1 & ?) : IHk AsubB Phi HH1'...
        forwards (cc2 & ?) : IHk AsubB Phi HH2'...


      * SSCase "and".
        forwards (cc1 & ?) : IHk AsubB Phi HH1...
        forwards (cc2 & ?) : IHk AsubB Phi HH2...


    + SCase "C = all".

      inverts BsubC as HH.

      * SSCase "bot".
        pick fresh Y.
        assert (HH' : asub sty_bot (Q2 ++ [qs_all Y A0]) (open_sty_wrt_sty B0 (sty_var_f Y)) co_bot)...
        forwards (cc & ?) : IHk AsubB Phi HH'; auto.
        rewrite size_sty_open_sty_wrt_sty_var...
        rewrite app_assoc.
        eapply wf_fs_all_append...
        rewrite seqs_vars_union...

        exists cc.
        pick fresh X and apply A_forall...
        unfold one.
        rewrite app_assoc in *.
        eapply asub_rename...

      * SSCase "forall".

        pick fresh Y.
        specializes HH...

        forwards (cc & ?) : IHk AsubB Phi HH; auto.
        rewrite size_sty_open_sty_wrt_sty_var...
        rewrite app_assoc.
        eapply wf_fs_all_append...
        rewrite seqs_vars_union...


        exists cc.
        pick fresh X and apply A_forall...
        unfold one.
        rewrite app_assoc in *.
        eapply asub_rename...


    + SCase "C = rcd".
      inverts BsubC as HH.

      * SSCase "bot".
        assert (HH' : asub sty_bot (Q2 ++ [qs_rcd l]) A0 co_bot)...
        forwards (cc & ?) : IHk AsubB Phi HH'...
        rewrite app_assoc.
        eapply wf_fs_rcd_append...
        exists cc.
        constructor; simpl_env...


      * SSCase "rcd".
        forwards (cc & ?) : IHk AsubB Phi HH...

        rewrite app_assoc.
        eapply wf_fs_rcd_append...

        exists cc.
        constructor; simpl_env...
Qed.



Lemma asub_trans_wrt_Q : forall A B C Q1 Q2 Q3 c1 c2,
    asub A Q1  B c1 ->
    asub_list Q3 Q1 ->
    asub B Q2 C c2 ->
    wf_fs (Q3 ++ Q2) ->
    qvars_notin (fv_sty_in_sty A) Q2 ->
    exists c, asub A (Q3 ++ Q2) C c.
Proof.
  intros.
  eapply asub_trans_wrt_Q_aux
    with (k := size_sty A + sizefs Q1 + size_sty B + sizefs Q2 + size_sty C + sizefs Q3); eauto.
Qed.


Lemma asub_trans : forall A B C c1 c2,
    asub A [] B c1 -> asub B [] C c2 -> exists c, asub A [] C c.
Proof with eauto.
  introv H1 H2.
  forwards : asub_trans_wrt_Q H1 H2...
Qed.




(* ********************************************************************** *)
(** * Completeness *)

Lemma asub_arr : forall Q A1 A2 B1 B2 c1 c2,
    asub B1 Q B2 c2 ->
    wf_fs Q ->
    qvars_notin (fv_sty_in_sty A2) Q ->
    asub A2 [] A1 c1 ->
    exists c, asub  (sty_arrow A1 B1) ([qs_arr A2] ++ Q) B2 c.
Proof with eauto.
  introv W.
  gen A1 A2 c1.
  induction W; introv WF QVar Sub; simpls...

  - Case "bot".
    clear H0.
    gen Q.

    induction H; intros; simpls...

    forwards (? & ?): IHlc_sty2 (Q ++ [qs_arr A])...

    forwards (? & ?): IHlc_sty1...
    forwards (? & ?): IHlc_sty2...

    pick fresh X.
    forwards (c & ?): H1 X (Q ++ [qs_all X A]).
    eapply wf_fs_all_append...
    eapply qvars_all_append...
    exists c...
    pick fresh Y and apply A_forall...
    eapply asub_rename...

    forwards (c & ?): IHlc_sty (Q ++ [qs_rcd l])...

  - Case "and".

    forwards (cc1 & HH1): IHW1 WF QVar...
    forwards (cc2 & HH2): IHW2 WF QVar...

  - Case "rcd".
    forwards (? & ? & WF') : asub_regular W.
    forwards (cc1 & HH1): IHW WF'...

  - Case "arrow".
    forwards (? & ? & WF') : asub_regular W.
    forwards (? & ?) : wf_fs_arr_append_rev WF'.
    forwards (cc1 & HH1): IHW WF'...

  - Case "all".
    pick fresh X.
    forwards W : H...
    forwards (? & ? & WF') : asub_regular W.
    forwards (? & ? & ?) : wf_fs_all_append_rev WF'.
    forwards IHW : H0 X WF' Sub; auto.
    destruct IHW as (cc & IHW)...
    exists cc.
    pick fresh Y and apply A_forall.
    eapply asub_rename...
Qed.


Lemma asub_all : forall B2 Q X A1 A2 B1 c1 c2,
    asub (open_sty_wrt_sty B1 (sty_var_f X)) Q B2 c2 ->
    asub A2 [] A1 c1 ->
    qvars_notin (union (fv_sty_in_sty A2) (fv_sty_in_sty (sty_var_f X))) Q ->
    X `notin` fv_sty_in_sty B1 ->
    X `notin` fv_sty_in_sty A1 ->
    X `notin` fv_sty_in_sty A2 ->
    exists c, asub  (sty_all A1 B1) ([qs_all X A2] ++ Q) B2 c.
Proof with eauto.

  intros B2.
  introv sub.
  lets [_ [HY _]] : asub_regular sub.
  generalize dependent Q. generalize dependent c2.

  inductions HY; introv Sub1 Sub2 QVar Not1 Not2 Not3; simpls...

  - Case "B2 = nat".
    exists (co_forall c2)...
    pick fresh Y and apply A_allNat...

  - Case "B2 = top".
    exists (co_trans (calTop (qs_all X A2 :: Q)) co_top)...
    constructor...
    eapply lc_sty_all_exists...

  - Case "B2 = bot".
    exists (co_forall c2)...
    pick fresh Y and apply A_allBot...

  - Case "B2 = var_f".
    exists (co_forall c2)...
    pick fresh Y and apply A_allVar...

  - Case "B2 = arrow".
    inverts Sub1 as Sub1 ? Eq.

    rewrite <- Eq in IHHY2.
    forwards (? & ?): IHHY2 co_bot (Q ++ [qs_arr A])...

    lets (? & ? & WF) : asub_regular Sub1.
    lets (? & ?) : wf_fs_arr_append_rev WF.
    forwards W : IHHY2 Sub1...
    destruct W as (c & W)...

  - Case "B2 = and".
    inverts Sub1 as Sub1 ? Eq.

    rewrite <- Eq in *.
    forwards (? & ?): IHHY1 co_bot...
    forwards (? & ?): IHHY2 co_bot...

    forwards W1 : IHHY1 Sub2...
    forwards W2 : IHHY2 Sub2...
    destruct W1 as (cc1 & W1)...
    destruct W2 as (cc2 & W2)...

  - Case "B2 = forall".
    inverts Sub1 as Sub1 ? Eq.

    rewrite <- Eq in *.
    pick fresh Y.
    forwards (c & ?): H0 co_bot (Q ++ [qs_all Y A]); auto.
    exists c...
    pick fresh Z and apply A_forall...
    eapply asub_rename...

    pick fresh Y.
    specializes Sub1...
    specialize (H0 Y c2 (Q ++ [qs_all Y A])).
    forwards ~ (co & ?) : H0 Sub1.
    exists co.
    pick fresh Z and apply A_forall...
    apply asub_rename with (X:=Y)...
    constructor...
    lets [_ [_ ?]] : asub_regular Sub1...
    lets [? _] : wf_fs_all_append_rev H2...

  - Case "B2 = rcd".
    inverts Sub1 as Sub1 ? Eq.

    rewrite <- Eq in *.
    forwards (? & ?): IHHY co_bot (Q ++ [qs_rcd l])...

    forwards W : IHHY Sub2...
    destruct W as (c & W)...
Qed.


Lemma asub_rcd : forall Q A B c1 l,
    asub A Q B c1 ->
    wf_fs Q ->
    exists c2, asub  (sty_rcd l A) ([qs_rcd l] ++ Q) B c2.
Proof with eauto.
  introv W.
  induction W; intros WF; simpls...

  - Case "bot".
    clear H0.
    gen Q.

    induction H; intros; simpls...

    forwards (? & ?): IHlc_sty2 (Q ++ [qs_arr A])...

    forwards (? & ?): IHlc_sty1...
    forwards (? & ?): IHlc_sty2...

    pick fresh X.
    forwards (c & ?): H1 X (Q ++ [qs_all X A]).
    eapply wf_fs_all_append...
    exists c...
    pick fresh Y and apply A_forall...
    eapply asub_rename...

    forwards (c & ?): IHlc_sty (Q ++ [qs_rcd l0])...

  - Case "and".
    forwards (cc1 & ?) : IHW1 WF...
    forwards (cc2 & ?) : IHW2 WF...

  - Case "rcd".
    forwards (? & ? & ?) : asub_regular W.
    forwards (cc & ?) : IHW...

  - Case "arrow".
    forwards (? & ? & ?) : asub_regular W.
    forwards (cc & ?) : IHW...

  - Case "all".
    pick fresh X.
    forwards W : H...
    forwards (? & ? & ?) : asub_regular W.
    forwards IHW : H0...
    destruct IHW as (cc & IHW)...
    exists cc.
    pick fresh Y and apply A_forall...
    eapply asub_rename...
Qed.



Theorem sub2asub : forall A B c,
    csub A B c -> exists c', asub A nil B c'.
Proof with eauto.
  introv W.

  induction W...


  - Case "refl".
    eapply asub_refl...

  - Case "trans".
    destruct IHW1 as (c1' & IHW1).
    destruct IHW2 as (c2' & IHW2).
    eapply asub_trans...

  - Case "topArr".
    pick fresh X.
    exists (co_trans  (calTop  [qs_all X sty_top]) co_top)...
    pick fresh Y and apply A_forall...
    simpls; econstructor...

  - Case "arr".
    destruct IHW1 as (c1' & IHW1).
    destruct IHW2 as (c2' & IHW2).
    forwards (cc & ?): asub_arr IHW2 IHW1...

  - Case "and".
    destruct IHW1 as (c1' & IHW1).
    destruct IHW2 as (c2' & IHW2).
    exists (co_trans (calAnd []) (co_pair c1' c2'))...

  - Case "andl".
    eapply set2Sub...
    eapply R_and1...
    eapply setRefl...


  - Case "andr".
    eapply set2Sub...
    eapply R_and2...
    eapply setRefl...


  - Case "forall".
    pick fresh X.

    destruct IHW as (c1 & IHW1).
    forwards (c2 & IHW2): H0...

    forwards (cc & ?): asub_all IHW2 IHW1...
    exists cc.
    pick fresh Y and apply A_forall...
    simpls.
    rewrite_env ([] ++ [qs_all Y A2]).
    eapply asub_rename...


  - Case "rcd".
    destruct IHW as (c' & IHW).

    forwards (? & ?) : asub_rcd IHW...


  - Case "distArr".
    set (T := sty_and (sty_arrow A1 A2) (sty_arrow A1 A3)).
    assert ((sty_arrow A1 A2) ∈Super (sty_arrow A1 A2)).
      eapply setRefl...
    assert ((sty_arrow A1 A3) ∈Super (sty_arrow A1 A3)).
      eapply setRefl...
    assert (W1 : (sty_arrow A1 A2) ∈Super T).
      eapply R_and1...
    assert (W2 : (sty_arrow A1 A3) ∈Super T).
      eapply R_and2...

    change (sty_arrow A1 A2) with (applyfs [(qs_arr A1)] A2) in W1.
    change (sty_arrow A1 A3) with (applyfs [(qs_arr A1)] A3) in W2.
    eapply set2Sub in W1...
    eapply set2Sub in W2...
    destruct W1 as (c1 & W1).
    destruct W2 as (c2 & W2).
    lets : A_and W1 W2...

  - Case "distRcd".

    set (T := sty_and (sty_rcd l A) (sty_rcd l B)).
    assert ((sty_rcd l A) ∈Super (sty_rcd l A)).
      apply setRefl...
    assert ((sty_rcd l B) ∈Super (sty_rcd l B)).
      apply setRefl...
    assert (W1 : (sty_rcd l A) ∈Super T).
      eapply R_and1...
    assert (W2 : (sty_rcd l B) ∈Super T).
      eapply R_and2...

    change (sty_rcd l A) with (applyfs ([qs_rcd l]) A) in W1.
    change (sty_rcd l B) with (applyfs ([qs_rcd l]) B) in W2.
    apply set2Sub in W1...
    apply set2Sub in W2...
    destruct W1 as (c1 & W1).
    destruct W2 as (c2 & W2).
    lets : A_and W1 W2...

  - Case "distAll".
    pick fresh X.
    inverts H.
    inverts H0.

    set (T := sty_and (sty_all A B1) (sty_all A B2)).
    assert ((sty_all A B1) ∈Super (sty_all A B1)).
      apply setRefl...
    assert ((sty_all A B2) ∈Super (sty_all A B2)).
      apply setRefl...
    assert (W1 : (sty_all A B1) ∈Super T).
      eapply R_and1...
    assert (W2 : (sty_all A B2) ∈Super T).
      eapply R_and2...


    assert (Eq1 : B1 = close_sty_wrt_sty X (open_sty_wrt_sty B1 (sty_var_f X))).
      rewrite close_sty_wrt_sty_open_sty_wrt_sty...
    assert (Eq2 : B2 = close_sty_wrt_sty X (open_sty_wrt_sty B2 (sty_var_f X))).
      rewrite close_sty_wrt_sty_open_sty_wrt_sty...
    rewrite Eq1 in W1.
    rewrite Eq2 in W2.
    clear Eq1 Eq2.

    change (sty_all A (close_sty_wrt_sty X (open_sty_wrt_sty B1 (sty_var_f X))))  with (applyfs ([qs_all X A]) (open_sty_wrt_sty B1 (sty_var_f X))) in W1.
    change (sty_all A (close_sty_wrt_sty X (open_sty_wrt_sty B2 (sty_var_f X))))  with (applyfs ([qs_all X A]) (open_sty_wrt_sty B2 (sty_var_f X))) in W2.
    apply set2Sub in W1; auto.
    apply set2Sub in W2; auto.
    destruct W1 as (c1 & W1).
    destruct W2 as (c2 & W2).
    lets W : A_and W1 W2...


    assert (Eq : (sty_and (open_sty_wrt_sty B1 (sty_var_f X)) (open_sty_wrt_sty B2 (sty_var_f X))) = ((open_sty_wrt_sty (sty_and B1 B2) (sty_var_f X))))...
    rewrite Eq in W.


    exists (co_trans (calAnd [qs_all X A]) (co_pair c1 c2))...
    pick fresh Y and apply A_forall...
    eapply asub_rename...
Qed.
