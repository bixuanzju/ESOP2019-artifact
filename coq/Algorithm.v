
Require Import Infrastructure.
Require Import List.
Import ListNotations.



Definition size_elem (s : qs) : nat :=
  match s with
  | qs_arr A => size_sty A
  | qs_all _ A => size_sty A
  | qs_rcd _ => 0
end.


Definition sizefs (Q : seqs) :=
  fold_right (fun l acc => l + acc) 0 (map size_elem Q).


(* ********************************************************************** *)
(** * Q => A *)

Definition applyfs (Q : seqs) (A : sty) :=
  fold_right (fun el acc =>
                match el with
                | qs_arr A => sty_arrow A acc
                | qs_rcd l => sty_rcd l acc
                | qs_all X A => sty_all A (close_sty_wrt_sty X acc)
                end) A Q.

(**


Well-formedness of Q

Q grows at the tail, which requires that variales appearing later should be
fresh with respect to previous items.

The following is not correct.

Inductive wf_fs : seqs -> Prop :=
| fs_empty : wf_fs []
| fs_arr : forall Q A, lc_sty A -> wf_fs Q -> wf_fs ((qs_arr A) :: Q )
| fs_rcd : forall Q l, wf_fs Q -> wf_fs ((qs_rcd l) :: Q)
| fs_all : forall Q X A,
    lc_sty A ->
    X `notin` fv_sty_in_sty A ->
    not_occur X Q ->
    wf_fs Q -> wf_fs ((qs_all X A) :: Q).

 *)



(** [qvars_notin s Q] means all type binders of [Q] do not occur in [s]    *)
Inductive qvars_notin (s : vars) : seqs -> Prop :=
| qvars_empty : qvars_notin s []
| qvars_arr : forall Q A, qvars_notin s Q -> qvars_notin s ((qs_arr A) :: Q)
| qvars_rcd : forall Q l, qvars_notin s Q -> qvars_notin s ((qs_rcd l) :: Q)
| qvars_all : forall Q X A,
    qvars_notin s Q ->
    X `notin` s ->
    qvars_notin s ((qs_all X A) :: Q).



(** [wf_fs Q]: well-formedness of [Q], ensuring that type bidners appearing later are fresh with respect to previous items *)
Inductive wf_fs : seqs -> Prop :=
| fs_empty : wf_fs []
| fs_arr : forall Q A,
    lc_sty A ->
    wf_fs Q ->
    qvars_notin (fv_sty_in_sty A) Q ->
    wf_fs ((qs_arr A) :: Q )
| fs_rcd : forall Q l, wf_fs Q -> wf_fs ((qs_rcd l) :: Q)
| fs_all : forall Q X A,
    lc_sty A ->
    X `notin` fv_sty_in_sty A ->
    qvars_notin (fv_sty_in_sty (sty_var_f X) \u fv_sty_in_sty A) Q ->
    wf_fs Q -> wf_fs ((qs_all X A) :: Q).


Hint Constructors qvars_notin wf_fs.




(* ********************************************************************** *)
(** * Two meta-functions of coercions  *)

Fixpoint calTop (Q : seqs) : co :=
  match Q with
  | nil => co_top
  | cons l fs' =>
    match l with
    | qs_arr _ => co_trans (co_arr co_top (calTop fs')) co_topArr
    | qs_rcd l => co_trans (calTop fs') co_id
    | qs_all _ _ => co_trans (co_forall (calTop fs')) co_topAll
    end
  end.

Fixpoint calAnd (Q : seqs) : co :=
  match Q with
  | nil => co_id
  | cons l fs' =>
    match l with
    | qs_arr _ => co_trans (co_arr co_id (calAnd fs')) co_distArr
    | qs_rcd l => co_trans (calAnd fs') (co_id)
    | qs_all _ _ => co_trans (co_forall (calAnd fs')) co_distPoly
    end
  end.


(* ********************************************************************** *)
(** * Algorithmic subtyping  *)

Inductive asub : sty -> seqs -> sty -> co -> Prop :=
 | A_nat :
     asub sty_nat  nil  sty_nat co_id
 | A_var : forall (X:typvar),
     asub (sty_var_f X)  nil  (sty_var_f X) co_id
 | A_top : forall (A:sty) (Q:seqs),
     lc_sty A ->
     wf_fs Q ->
     asub A Q sty_top (co_trans  (calTop  Q )  co_top)
 | A_bot : forall (A:sty) (Q:seqs),
     lc_sty A ->
     wf_fs Q ->
     asub sty_bot Q A co_bot
 | A_and : forall (A:sty) (Q:seqs) (B1 B2:sty) (c1 c2:co),
     asub A Q B1 c1 ->
     asub A Q B2 c2 ->
     asub A Q (sty_and B1 B2) (co_trans  (calAnd  Q )  (co_pair c1 c2))
 | A_rcdNat : forall (l:i) (A:sty) (Q:seqs) (c:co),
     asub A Q sty_nat c ->
     asub (sty_rcd l A)   (cons  (qs_rcd l)   Q )   sty_nat c
 | A_rcdBot : forall (l:i) (A:sty) (Q:seqs) (c:co),
     asub A Q sty_bot c ->
     asub (sty_rcd l A)   (cons  (qs_rcd l)   Q )   sty_bot c
 | A_rcdVar : forall (l:i) (A:sty) (Q:seqs) (X:typvar) (c:co),
     asub A Q (sty_var_f X) c ->
     asub (sty_rcd l A)   (cons  (qs_rcd l)   Q )   (sty_var_f X) c
 | A_rcd : forall (A:sty) (Q:seqs) (l:i) (B:sty) (c:co),
     asub A ( Q  ++ [(qs_rcd l)])   B c ->
     asub A Q (sty_rcd l B) c
 | A_arr : forall (A:sty) (Q:seqs) (B1 B2:sty) (c:co),
     asub A (Q ++ [(qs_arr B1)])   B2 c ->
     asub A Q (sty_arrow B1 B2) c
 | A_forall : forall (L:vars) (A:sty) (Q:seqs) (B1 B2:sty) (c:co),
     (forall X, X \notin  L  ->
           asub A (Q  ++ [(qs_all X B1)]) (open_sty_wrt_sty B2 (sty_var_f X)) c)  ->
     asub A Q (sty_all B1 B2) c
 | A_andNat1 : forall (A1 A2:sty) (Q:seqs) (c:co),
     lc_sty A2 ->
     asub A1 Q sty_nat c ->
     asub (sty_and A1 A2) Q sty_nat (co_trans c co_proj1)
 | A_andNat2 : forall (A1 A2:sty) (Q:seqs) (c:co),
     lc_sty A1 ->
     asub A2 Q sty_nat c ->
     asub (sty_and A1 A2) Q sty_nat (co_trans c co_proj2)
 | A_andBot1 : forall (A1 A2:sty) (Q:seqs) (c:co),
     lc_sty A2 ->
     asub A1 Q sty_bot c ->
     asub (sty_and A1 A2) Q sty_bot (co_trans c co_proj1)
 | A_andBot2 : forall (A1 A2:sty) (Q:seqs) (c:co),
     lc_sty A1 ->
     asub A2 Q sty_bot c ->
     asub (sty_and A1 A2) Q sty_bot (co_trans c co_proj2)
 | A_andVar1 : forall (A1 A2:sty) (Q:seqs) (X:typvar) (c:co),
     lc_sty A2 ->
     asub A1 Q (sty_var_f X) c ->
     asub (sty_and A1 A2) Q (sty_var_f X) (co_trans c co_proj1)
 | A_andVar2 : forall (A1 A2:sty) (Q:seqs) (X:typvar) (c:co),
     lc_sty A1 ->
     asub A2 Q (sty_var_f X) c ->
     asub (sty_and A1 A2) Q (sty_var_f X) (co_trans c co_proj2)
 | A_arrNat : forall (A1 A2 A:sty) (Q:seqs) (c1 c2:co),
     qvars_notin (fv_sty_in_sty A) Q ->
     asub A  nil  A1 c1 ->
     asub A2 Q sty_nat c2 ->
     asub (sty_arrow A1 A2)   (cons (qs_arr A) Q)   sty_nat (co_arr c1 c2)
 | A_arrBot : forall (A1 A2 A:sty) (Q:seqs) (c1 c2:co),
     qvars_notin (fv_sty_in_sty A) Q ->
     asub A  nil  A1 c1 ->
     asub A2 Q sty_bot c2 ->
     asub (sty_arrow A1 A2)   (cons (qs_arr A) Q)   sty_bot (co_arr c1 c2)
 | A_arrVar : forall (A1 A2 A:sty) (Q:seqs) (X:typvar) (c1 c2:co),
     qvars_notin (fv_sty_in_sty A) Q ->
     asub A  nil  A1 c1 ->
     asub A2 Q (sty_var_f X) c2 ->
     asub (sty_arrow A1 A2)   (cons (qs_arr A) Q)   (sty_var_f X) (co_arr c1 c2)
 | A_allNat : forall (L:vars) (A1 A2 A:sty) (Q:seqs) (c c':co) (X : typvar),
     X `notin` fv_sty_in_sty A ->
     X `notin` fv_sty_in_sty A1 ->
     X `notin` fv_sty_in_sty A2 ->
     qvars_notin (fv_sty_in_sty A \u fv_sty_in_sty (sty_var_f X)) Q ->
     asub A nil A1 c' ->
     asub  (open_sty_wrt_sty A2 (sty_var_f X) ) Q sty_nat c   ->
     asub (sty_all A1 A2)   (cons (qs_all X A) Q)   sty_nat (co_forall c)
 | A_allBot : forall (L:vars) (A1 A2 A:sty) (Q:seqs) (c c':co) (X : typvar),
     X `notin` fv_sty_in_sty A ->
     X `notin` fv_sty_in_sty A1 ->
     X `notin` fv_sty_in_sty A2 ->
     qvars_notin (fv_sty_in_sty A \u fv_sty_in_sty (sty_var_f X)) Q ->
     asub A nil A1 c' ->
     asub  (open_sty_wrt_sty A2 (sty_var_f X) ) Q sty_bot c   ->
     asub (sty_all A1 A2)   (cons (qs_all X A) Q)   sty_bot (co_forall c)
 | A_allVar : forall (L:vars) (A1 A2 A:sty) (Q:seqs) (Y:typvar) (c c':co) (X : typvar),
     X `notin` fv_sty_in_sty A ->
     X `notin` fv_sty_in_sty A1 ->
     X `notin` fv_sty_in_sty A2 ->
     qvars_notin (fv_sty_in_sty A \u fv_sty_in_sty (sty_var_f X)) Q ->
     asub A nil A1 c' ->
     asub  (open_sty_wrt_sty A2 (sty_var_f X) )  Q (sty_var_f Y) c   ->
     asub (sty_all A1 A2)   (cons (qs_all X A) Q)   (sty_var_f Y) (co_forall c).

Hint Constructors asub.
