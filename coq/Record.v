
Require Import Metalib.Metatheory.
Require Import Infrastructure.
Require Import Disjoint.
Require Import Record_inf.

(* defns WFTC_WFCL *)
Inductive wftc : TContext -> Prop :=    (* defn wftc *)
 | wftc_Empty :
     wftc  nil
 | wftc_Tvar : forall (Ttx:TContext) (a:typvar) (R:rlist),
     wftc Ttx ->
     wfcl Ttx R ->
      ( a  `notin` dom ( Ttx ))  ->
     wftc  (( a ~ R )++ Ttx )
with wfcl : TContext -> rlist -> Prop :=    (* defn wfcl *)
 | wfcl_Nil : forall (Ttx:TContext),
     wftc Ttx ->
     wfcl Ttx R_Empty
 | wfcl_Cons : forall (Ttx:TContext) (r:rtyp) (R:rlist),
     wfr Ttx r ->
     wfcl Ttx R ->
     wfcl Ttx (R_Cons r R)
with wfrt : TContext -> rt -> Prop :=    (* defn wfrt *)
 | wfrt_Prim : forall (Ttx:TContext),
     wfrt Ttx rt_Base
 | wfrt_Arrow : forall (Ttx:TContext) (rt1 rt2:rt),
     wfrt Ttx rt1 ->
     wfrt Ttx rt2 ->
     wfrt Ttx (rt_Fun rt1 rt2)
 | wfrt_All : forall (L:vars) (Ttx:TContext) (R:rlist) (rt5:rt),
     wfcl Ttx R ->
      ( forall a , a \notin  L  -> wfrt  (( a ~ R )++ Ttx )   ( open_rt_wrt_rtyp rt5 (r_TyVar_f a) )  )  ->
     wfrt Ttx (rt_ConQuan R rt5)
 | wfrt_Rec : forall (Ttx:TContext) (r:rtyp),
     wfr Ttx r ->
     wfrt Ttx (rt_Record r)
with wfr : TContext -> rtyp -> Prop :=    (* defn wfr *)
 | wfr_Var : forall (Ttx:TContext) (a:typvar) (R:rlist),
      binds  a   R   Ttx  ->
     wfr Ttx (r_TyVar_f a)
 | wfr_Base : forall (Ttx:TContext) (l:i) (rt5:rt),
     wfrt Ttx rt5 ->
     wfr Ttx (r_SingleField l rt5)
 | wfr_Empty : forall (Ttx:TContext),
     wfr Ttx r_Empty
 | wfr_Merge : forall (Ttx:TContext) (r1 r2:rtyp),
     wfr Ttx r1 ->
     wfr Ttx r2 ->
     cmp Ttx r1 r2 ->
     wfr Ttx (r_Merge r1 r2)
with cmp : TContext -> rtyp -> rtyp -> Prop :=    (* defn cmp *)
 | cmp_Eq : forall (Ttx:TContext) (r' s' r s:rtyp),
     cmp Ttx r s ->
     teq Ttx (rt_Record r) (rt_Record r') ->
     teq Ttx (rt_Record s) (rt_Record s') ->
     cmp Ttx r' s'
 | cmp_Symm : forall (Ttx:TContext) (s r:rtyp),
     cmp Ttx r s ->
     cmp Ttx s r
 | cmp_Base : forall Ttx r l t t',
     cmp Ttx r (r_SingleField l t) ->
     wfrt Ttx t' ->
     cmp Ttx r (r_SingleField l t')
 | cmp_Tvar : forall (Ttx:TContext) (a:typvar) (r:rtyp) (R:rlist),
     wfcl Ttx R ->
     wfr Ttx r ->
      binds  a   R   Ttx  ->
      rtyp_in_rlist  r   R  ->
     cmp Ttx (r_TyVar_f a) r
 | cmp_MergeE1 : forall (Ttx:TContext) (r s1 s2:rtyp),
     cmp Ttx r  (r_Merge s1 s2)  ->
     cmp Ttx r s1
 | cmp_MergeE2 : forall (Ttx:TContext) (r s2 s1:rtyp),
     cmp Ttx r  (r_Merge s1 s2)  ->
     cmp Ttx r s2
 | cmp_MergeI : forall (Ttx:TContext) (r s1 s2:rtyp),
     cmp Ttx s1 s2 ->
     cmp Ttx r s1 ->
     cmp Ttx r s2 ->
     cmp Ttx r  (r_Merge s1 s2)
 | cmp_BaseBase : forall (Ttx:TContext) (l:i) (rt5:rt) (l':i) (rt':rt),
      l  <>  l'  ->
     wfrt Ttx rt5 ->
     wfrt Ttx rt' ->
     cmp Ttx (r_SingleField l rt5) (r_SingleField l' rt')
 | cmp_Empty : forall (Ttx:TContext) (r:rtyp),
     wfr Ttx r ->
     cmp Ttx r r_Empty
with ceq : TContext -> rlist -> rlist -> Prop :=    (* defn ceq *)
 | ceq_Refl : forall (Ttx:TContext) (R:rlist),
     wfcl Ttx R ->
     ceq Ttx R R
 | ceq_Symm : forall (Ttx:TContext) (R' R:rlist),
     ceq Ttx R R' ->
     ceq Ttx R' R
 | ceq_Trans : forall (Ttx:TContext) (R R'' R':rlist),
     ceq Ttx R R' ->
     ceq Ttx R' R'' ->
     ceq Ttx R R''
 | ceq_Inner : forall (Ttx:TContext) (r:rtyp) (R:rlist) (r':rtyp) (R':rlist),
     ceq Ttx R R' ->
     teq Ttx (rt_Record r) (rt_Record r') ->
     ceq Ttx (R_Cons r R) (R_Cons r' R')
 | ceq_Swap : forall (Ttx:TContext) (r r':rtyp) (R:rlist),
     wfr Ttx r ->
     wfr Ttx r' ->
     wfcl Ttx R ->
     ceq Ttx (R_Cons r  (R_Cons r' R) ) (R_Cons r'  (R_Cons r R) )
 | ceq_Empty : forall (Ttx:TContext) (R:rlist),
     wfcl Ttx R ->
     ceq Ttx (R_Cons r_Empty R) R
 | ceq_Merge : forall (Ttx:TContext) (r1 r2:rtyp) (R:rlist),
     wfr Ttx (r_Merge r1 r2) ->
     wfcl Ttx R ->
     ceq Ttx (R_Cons  (r_Merge r1 r2)  R) (R_Cons r1  (R_Cons r2 R) )
 | ceq_Dupl : forall (Ttx:TContext) (r:rtyp) (R:rlist),
     wfr Ttx r ->
     wfcl Ttx R ->
     ceq Ttx (R_Cons r  (R_Cons r R) ) (R_Cons r R)
 | ceq_Base : forall (Ttx:TContext) (l:i) (t:rt) (R:rlist) (t':rt),
     (* teq Ttx rt5 rt' -> *)
     wfrt Ttx t ->
     wfrt Ttx t' ->
     wfcl Ttx R ->
     ceq Ttx (R_Cons (r_SingleField l t) R) (R_Cons (r_SingleField l t') R)
with teq : TContext -> rt -> rt -> Prop :=    (* defn teq *)
 | teq_Refl : forall (Ttx:TContext) (rt5:rt),
     wfrt Ttx rt5 ->
     teq Ttx rt5 rt5
 | teq_Symm : forall (Ttx:TContext) (rt' rt5:rt),
     teq Ttx rt5 rt' ->
     teq Ttx rt' rt5
 | teq_Trans : forall (Ttx:TContext) (rt5 rt'' rt':rt),
     teq Ttx rt5 rt' ->
     teq Ttx rt' rt'' ->
     teq Ttx rt5 rt''
 | teq_CongArrow : forall (Ttx:TContext) (rt1 rt2 rt1' rt2':rt),
     teq Ttx rt1 rt1' ->
     teq Ttx rt2 rt2' ->
     teq Ttx (rt_Fun rt1 rt2) (rt_Fun rt1' rt2')
 | teq_CongAll : forall (L:vars) (Ttx:TContext) (R:rlist) (rt5:rt) (R':rlist) (rt':rt),
     ceq Ttx R R' ->
      ( forall a , a \notin  L  -> teq  (( a ~ R )++ Ttx )   ( open_rt_wrt_rtyp rt5 (r_TyVar_f a) )   ( open_rt_wrt_rtyp rt' (r_TyVar_f a) )  )  ->
     teq Ttx (rt_ConQuan R rt5) (rt_ConQuan R' rt')
 | teq_CongBase : forall (Ttx:TContext) (l:i) (rt5 rt':rt),
     teq Ttx rt5 rt' ->
     teq Ttx (rt_Record (r_SingleField l rt5)) (rt_Record (r_SingleField l rt'))
 | teq_CongMerge : forall (Ttx:TContext) (r1 r2 r1' r2':rtyp),
     teq Ttx (rt_Record r1) (rt_Record r1') ->
     teq Ttx (rt_Record r2) (rt_Record r2') ->
     cmp Ttx r1 r2 ->
     cmp Ttx r1' r2' ->
     teq Ttx (rt_Record (r_Merge r1 r2)) (rt_Record (r_Merge r1' r2'))
 | teq_MergeUnit : forall (Ttx:TContext) (r:rtyp),
     wfr Ttx r ->
     teq Ttx (rt_Record (r_Merge r r_Empty)) (rt_Record r)
 | teq_MergeAssoc : forall (Ttx:TContext) (r1 r2 r3:rtyp),
     cmp Ttx r1 r2 ->
     cmp Ttx r1 r3 ->
     cmp Ttx r2 r3 ->
     teq Ttx (rt_Record (r_Merge r1  (r_Merge r2 r3) )) (rt_Record (r_Merge  (r_Merge r1 r2)  r3))
 | teq_MergeComm : forall (Ttx:TContext) (r1 r2:rtyp),
     cmp Ttx r1 r2 ->
     teq Ttx (rt_Record (r_Merge r1 r2)) (rt_Record (r_Merge r2 r1)).

(* defns COMLIST *)
Inductive cmpList : TContext -> rtyp -> rlist -> Prop :=    (* defn cmpList *)
 | cmpList_Nil : forall (Ttx:TContext) (r:rtyp),
     wfr Ttx r ->
     cmpList Ttx r R_Empty
 | cmpList_Cons : forall (Ttx:TContext) (r r':rtyp) (R:rlist),
     cmp Ttx r r' ->
     cmpList Ttx r R ->
     cmpList Ttx r (R_Cons r' R).

(* defns WFC *)
Inductive wfc : TContext -> GContext -> Prop :=    (* defn wfc *)
 | wfc_Empty : forall (Ttx:TContext),
     wftc Ttx ->
     wfc Ttx  nil
 | wfc_Var : forall (Ttx:TContext) (Gtx:GContext) (x:expvar) (rt5:rt),
     wfc Ttx Gtx ->
     wfrt Ttx rt5 ->
      ( x  `notin` dom ( Ttx ))  ->
      ( x  `notin` dom ( Gtx ))  ->
     wfc Ttx  (( x ~ rt5 )++ Gtx ) .

(* defns WTT *)
Inductive wtt : TContext -> GContext -> rexp -> rt -> sexp -> Prop :=    (* defn wtt *)
 | wtt_Eq : forall (Ttx:TContext) (Gtx:GContext) (re:rexp) (rt':rt) (ee:sexp) (rt5:rt),
     wtt Ttx Gtx re rt5 ee ->
     teq Ttx rt5 rt' ->
     wtt Ttx Gtx re rt' (sexp_anno ee  (trans_rt  rt' ) )
 | wtt_Var : forall (Ttx:TContext) (Gtx:GContext) (x:expvar) (rt5:rt),
     wftc Ttx ->
     wfc Ttx Gtx ->
      binds  x   rt5   Gtx  ->
     wtt Ttx Gtx (re_Var_f x) rt5 (sexp_var_f x)
 | wtt_ArrowI : forall (L:vars) (Ttx:TContext) (Gtx:GContext) (rt5:rt) (re:rexp) (rt':rt) (ee:sexp),
     wfrt Ttx rt5 ->
      ( forall x , x \notin  L  -> wtt Ttx  (( x ~ rt5 )++ Gtx )   ( open_rexp_wrt_rexp re (re_Var_f x) )  rt'  ( open_sexp_wrt_sexp ee (sexp_var_f x) )  )  ->
     wtt Ttx Gtx (re_Abs rt5 re) (rt_Fun rt5 rt') (sexp_anno  ( (sexp_abs ee) )  (sty_arrow  (trans_rt  rt5 )   (trans_rt  rt' ) ))
 | wtt_ArrowE : forall (Ttx:TContext) (Gtx:GContext) (re1 re2:rexp) (rt':rt) (ee1 ee2:sexp) (rt5:rt),
     wtt Ttx Gtx re1 (rt_Fun rt5 rt') ee1 ->
     wtt Ttx Gtx re2 rt5 ee2 ->
     wtt Ttx Gtx (re_App re1 re2) rt' (sexp_app ee1 ee2)
 | wtt_Base : forall (Ttx:TContext) (Gtx:GContext) (l:i) (re:rexp) (rt5:rt) (ee:sexp),
     wtt Ttx Gtx re rt5 ee ->
     wtt Ttx Gtx (re_SingleField l re) (rt_Record (r_SingleField l rt5)) (sexp_rcd l ee)
 | wtt_Empty : forall (Ttx:TContext) (Gtx:GContext),
     wftc Ttx ->
     wfc Ttx Gtx ->
     wtt Ttx Gtx re_Empty (rt_Record r_Empty) sexp_top
 | wtt_Merge : forall (Ttx:TContext) (Gtx:GContext) (re1 re2:rexp) (r1 r2:rtyp) (ee1 ee2:sexp),
     wtt Ttx Gtx re1 (rt_Record r1) ee1 ->
     wtt Ttx Gtx re2 (rt_Record r2) ee2 ->
     cmp Ttx r1 r2 ->
     wtt Ttx Gtx (re_Merge re1 re2) (rt_Record (r_Merge r1 r2)) (sexp_merge ee1 ee2)
 | wtt_Restr : forall (Ttx:TContext) (Gtx:GContext) (re:rexp) (l:i) (r:rtyp) (ee:sexp) (rt5:rt),
     wtt Ttx Gtx re (rt_Record (r_Merge (r_SingleField l rt5) r)) ee ->
     wtt Ttx Gtx (re_Res re l) (rt_Record r) (sexp_anno ee  (trans_rt  (rt_Record r) ) )
 | wtt_Select : forall (Ttx:TContext) (Gtx:GContext) (re:rexp) (l:i) (rt5:rt) (ee:sexp) (r:rtyp),
     wtt Ttx Gtx re (rt_Record (r_Merge (r_SingleField l rt5) r)) ee ->
     wtt Ttx Gtx (re_Selection re l) rt5 (sexp_proj  ( (sexp_anno ee (sty_rcd l  (trans_rt  rt5 ) )) )  l)
 | wtt_AllI : forall (L:vars) (Ttx:TContext) (Gtx:GContext) (R:rlist) (re:rexp) (rt5:rt) (ee:sexp),
     wfcl Ttx R ->
      ( forall a , a \notin  L  -> wtt  (( a ~ R )++ Ttx )  Gtx  ( open_rexp_wrt_rtyp re (r_TyVar_f a) )   ( open_rt_wrt_rtyp rt5 (r_TyVar_f a) )   ( open_sexp_wrt_sty ee (sty_var_f a) )  )  ->
     wtt Ttx Gtx (re_ConTyAbs R re) (rt_ConQuan R rt5) (sexp_tabs  (trans_rlist  R )  ee)
 | wtt_AllE : forall (Ttx:TContext) (Gtx:GContext) (re:rexp) (r:rtyp) (rt5:rt) (ee:sexp) (R:rlist),
     wtt Ttx Gtx re (rt_ConQuan R rt5) ee ->
     cmpList Ttx r R ->
     wtt Ttx Gtx (re_ConTyApp re r)  (open_rt_wrt_rtyp  rt5   r )  (sexp_tapp ee  (trans_rt  (rt_Record r) ) ).


(* ********************************************************************** *)
(** * Auxiliary definitions *)
(* ********************************************************************** *)


Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : vars => x) in
  let B := gather_atoms_with (fun x : var => {{ x }}) in
  let C3 := gather_atoms_with (fun x : stctx => dom x) in
  let C4 := gather_atoms_with (fun x : sctx => dom x) in
  let D4 := gather_atoms_with (fun x => fv_sty_in_sty x) in
  let D5 := gather_atoms_with (fun x => fv_sty_in_sexp x) in
  let D6 := gather_atoms_with (fun x => fv_sexp_in_sexp x) in
  let E1 := gather_atoms_with (fun x : TContext => dom x) in
  let E2 := gather_atoms_with (fun x : GContext => dom x) in
  let E3 := gather_atoms_with (fun x  => fv_rexp_in_rexp x) in
  let E4 := gather_atoms_with (fun x  => fv_rtyp_in_rexp x) in
  let E5 := gather_atoms_with (fun x  => fv_rtyp_in_rtyp x) in
  let E6 := gather_atoms_with (fun x  => fv_rtyp_in_rt x) in
  let E7 := gather_atoms_with (fun x  => fv_rtyp_in_rlist x) in
  constr:(A \u B \u C3 \u C4 \u D4 \u D5 \u D6 \u E1 \u E2 \u E3 \u E4 \u E5 \u E6 \u E7).


Definition trans_Ttx T := map trans_rlist  T.

Definition trans_Gtx G := map trans_rt G.



Lemma trans_open_rtyp_wrt_rtyp_rec2 : forall A B m,
    trans_rtyp2 ( open_rtyp_wrt_rtyp_rec m B A ) = open_sty_wrt_sty_rec m (trans_rtyp2 B ) (trans_rtyp2 A ).
Proof with eauto.
    intros A.
    induction A; intros B m; simpls...

    destruct (lt_eq_lt_dec n m)...
    destruct s...

    rewrite IHA1...
    rewrite IHA2...
Qed.

Lemma trans_open_rlist_wrt_rtyp_rec : forall R A n,
    trans_rlist (open_rlist_wrt_rtyp_rec n A R) =  open_sty_wrt_sty_rec n (trans_rtyp2 A) (trans_rlist R).
Proof with eauto.
  intros R.
  induction R; intros A n; simpls...

  rewrite trans_open_rtyp_wrt_rtyp_rec2...
  rewrite IHR...
Qed.


Lemma trans_open_rt_wrt_rtyp_rec : forall A B n,
    trans_rt ( open_rt_wrt_rtyp_rec n B A ) = open_sty_wrt_sty_rec n (trans_rtyp B ) (trans_rt A )

with

trans_open_rtyp_wrt_rtyp_rec : forall A B m,
    trans_rtyp ( open_rtyp_wrt_rtyp_rec m B A ) = open_sty_wrt_sty_rec m (trans_rtyp B ) (trans_rtyp A ).


Proof with eauto.
  - Case "rt".
    intros A.
    induction A; intros B n; simpls...

    rewrite IHA1...
    rewrite IHA2...

    rewrite trans_open_rlist_wrt_rtyp_rec...
    rewrite IHA...
    f_equal.
    admit.

  - Case "rtyp".

    intros A.
    induction A; intros B m; simpls...


    destruct (lt_eq_lt_dec n m)...
    destruct s...

    rewrite trans_open_rt_wrt_rtyp_rec...
    rewrite trans_open_rtyp_wrt_rtyp_rec...
    rewrite trans_open_rtyp_wrt_rtyp_rec...
Qed.


Lemma trans_open_rt_wrt_rtyp : forall t1 t2,
    trans_rt (open_rt_wrt_rtyp t1 t2) = open_sty_wrt_sty (trans_rt t1) (trans_rtyp t2).
Proof.
  intros.
  unfold open_rt_wrt_rtyp.
  unfold open_sty_wrt_sty.
  rewrite trans_open_rt_wrt_rtyp_rec.
  reflexivity.
Qed.


Lemma wfr_lc : forall T r,
    wfr T r ->
    lc_rtyp r

with

wfrt_lc : forall T t,
    wfrt T t ->
    lc_rt t

with

wfcl_lc : forall T R,
    wfcl T R ->
    lc_rlist R.
Proof with eauto.
  - Case "wft".
    introv WFR.
    induction WFR.

    constructor.
    constructor...
    constructor.
    constructor...

  - Case "wfrt".
    introv WFT.
    induction WFT.
    constructor.
    constructor...
    pick fresh a.
    specializes H1; auto.
    eapply lc_rt_ConQuan_exists...
    constructor...

  - Case "wfcl".
    introv WFCL.
    induction WFCL.
    constructor.
    constructor...
Qed.



Lemma wftc_uniq : forall T,
    wftc T ->
    uniq T.
Proof with eauto.
  intros T.
  alist induction T; intros; simpls...
  inverts H...
Qed.



Lemma trans_lc_rty2 : forall r,
    lc_rtyp r ->
    lc_sty (trans_rtyp2 r).
Proof with eauto.
  introv LC.
  induction LC; simpls...
Qed.

Lemma trans_lc_typ : forall t,
    lc_rt t ->
    lc_sty (trans_rt t)

with

trans_lc_rlist : forall R,
    lc_rlist R ->
    lc_sty (trans_rlist R)

with

trans_lc_rty : forall r,
    lc_rtyp r ->
    lc_sty (trans_rtyp r).

Proof with eauto using trans_lc_rty2.
  - Case "typ".
    introv LC.
    induction LC; simpls...

    pick fresh X.
    apply lc_sty_all_exists with X...
    replace (sty_var_f X) with (trans_rtyp (r_TyVar_f X))...
    rewrite <- trans_open_rt_wrt_rtyp...

  - Case "rtyp".
    introv LC.
    induction LC; simpls...

  - Case "rlist".
    introv LC.
    induction LC; simpls...
Qed.


Hint Resolve wfr_lc lc_sty_ty wfrt_lc wftc_uniq.


Definition csub Δ A B := exists c, sub Δ A B c.


Lemma CS_refl : forall Δ A,
    swft Δ A ->
    csub Δ A A.
Proof with eauto.
  intros.
  unfolds...
Qed.

Lemma CS_trans : forall Δ A B C,
    csub Δ A B ->
    csub Δ B C ->
    csub Δ A C.
Proof with eauto.
  introv Sub1 Sub2.
  destruct Sub1 as (c1 & Sub1).
  destruct Sub2 as (c2 & Sub2).
  unfolds...
Qed.

Lemma CS_top : forall Δ A,
    swft Δ A ->
    csub Δ A sty_top.
Proof with eauto.
  intros.
  unfolds...
Qed.


Lemma CS_bot : forall Δ A,
    swft Δ A ->
    csub Δ sty_bot A.
Proof with eauto.
  intros.
  unfolds...
Qed.

Lemma CS_arr : forall Δ A1 A2 B1 B2,
    csub Δ B1 A1 ->
    csub Δ A2 B2 ->
    csub Δ (sty_arrow A1 A2) (sty_arrow B1 B2).
Proof with eauto.
  introv Sub1 Sub2.
  destruct Sub1 as (c1 & Sub1).
  destruct Sub2 as (c2 & Sub2).
  unfolds...
Qed.


Lemma CS_rcd : forall Δ A B l,
    csub Δ A B ->
    csub Δ (sty_rcd l A) (sty_rcd l B).
Proof with eauto.
  introv Sub.
  destruct Sub as (c & ?).
  unfolds...
Qed.


Lemma CS_and : forall Δ A1 A2 A3,
    csub Δ A1 A2 ->
    csub Δ A1 A3 ->
    csub Δ A1 (sty_and A2 A3).
Proof with eauto.
  introv Sub1 Sub2.
  destruct Sub1 as (c1 & Sub1).
  destruct Sub2 as (c2 & Sub2).
  unfolds...
Qed.

Lemma CS_andl : forall Δ A1 A2,
    swft Δ A1 ->
    swft Δ A2 ->
    csub Δ (sty_and A1 A2) A1.
Proof with eauto.
  intros.
  unfolds...
Qed.



Lemma CS_andr : forall Δ A1 A2,
    swft Δ A1 ->
    swft Δ A2 ->
    csub Δ (sty_and A1 A2) A2.
Proof with eauto.
  intros.
  unfolds...
Qed.


Lemma CS_swft1 : forall Δ A B,
    csub Δ A B ->
    swft Δ A.
Proof with eauto.
  introv CS.
  destruct CS as (c & ?).
  eapply sub_regular in H.
  destruct H...
Qed.


Lemma CS_swft2 : forall Δ A B,
    csub Δ A B ->
    swft Δ B.
Proof with eauto.
  introv CS.
  destruct CS as (c & ?).
  eapply sub_regular in H.
  destruct H...
Qed.


Hint Resolve CS_refl CS_trans CS_top CS_arr CS_and CS_andl CS_andr CS_rcd CS_swft1 CS_swft2 CS_bot.


(* Note: stripped version without translation and monotype restriction   *)
Inductive has_type : stctx -> sctx -> sexp -> dirflag -> sty -> Prop :=
 | T2_top : forall (DD:stctx) (GG:sctx),
     swfe DD GG ->
     swfte DD ->
     has_type DD GG sexp_top Inf sty_top
 | T2_nat : forall (DD:stctx) (GG:sctx) (i5:i),
     swfe DD GG ->
     swfte DD ->
     has_type DD GG (sexp_lit i5) Inf sty_nat
 | T2_var : forall (DD:stctx) (GG:sctx) (x:expvar) (A:sty),
     swfte DD ->
     swfe DD GG ->
      binds ( x ) ( A ) ( GG )  ->
     has_type DD GG (sexp_var_f x) Inf A
 | T2_app : forall (DD:stctx) (GG:sctx) (ee1 ee2:sexp) (A2 A1:sty),
     has_type DD GG ee1 Inf (sty_arrow A1 A2) ->
     has_type DD GG ee2 Chk A1 ->
     has_type DD GG (sexp_app ee1 ee2) Inf A2
 | T2_merge : forall (DD:stctx) (GG:sctx) (ee1 ee2:sexp) (A1 A2:sty),
     has_type DD GG ee1 Inf A1 ->
     has_type DD GG ee2 Inf A2 ->
     disjoint DD A1 A2 ->
     has_type DD GG (sexp_merge ee1 ee2) Inf (sty_and A1 A2)
 | T2_anno : forall (DD:stctx) (GG:sctx) (ee:sexp) (A:sty),
     has_type DD GG ee Chk A ->
     has_type DD GG (sexp_anno ee A) Inf A
 | T2_tabs : forall (L:vars) (DD:stctx) (GG:sctx) (A:sty) (ee:sexp) (B:sty),
     swft DD A ->
      ( forall X , X \notin  L  -> has_type  (( X ~ A )++ DD )  GG  ( open_sexp_wrt_sty ee (sty_var_f X) )  Inf  ( open_sty_wrt_sty B (sty_var_f X) )  )  ->
     has_type DD GG (sexp_tabs A ee) Inf (sty_all A B)
 | T2_tapp : forall (DD:stctx) (GG:sctx) (ee:sexp) (t C B:sty),
     has_type DD GG ee Inf (sty_all B C) ->
     swft DD t ->
     disjoint DD t B ->
     has_type DD GG (sexp_tapp ee t) Inf  (open_sty_wrt_sty  C   t )
 | T2_rcd : forall (DD:stctx) (GG:sctx) (l:i) (ee:sexp) (A:sty),
     has_type DD GG ee Inf A ->
     has_type DD GG (sexp_rcd l ee) Inf (sty_rcd l A)
 | T2_proj : forall (DD:stctx) (GG:sctx) (ee:sexp) (l:i) (A:sty),
     has_type DD GG ee Inf (sty_rcd l A) ->
     has_type DD GG (sexp_proj ee l) Inf A
 | T2_abs : forall (L:vars) (DD:stctx) (GG:sctx) (ee:sexp) (A B:sty),
     swft DD A ->
      ( forall x , x \notin  L  -> has_type DD  (( x ~ A )++ GG )   ( open_sexp_wrt_sexp ee (sexp_var_f x) )  Chk B )  ->
     has_type DD GG (sexp_abs ee) Chk (sty_arrow A B)
 | T2_sub : forall (DD:stctx) (GG:sctx) (ee:sexp) (A B:sty),
     has_type DD GG ee Inf B ->
     swft DD A ->
     csub DD B A ->
     has_type DD GG ee Chk A.

Hint Constructors has_type.


Lemma notin_rtyp_rtyp2 : forall r X,
    X `notin` fv_rtyp_in_rtyp r ->
    X `notin` fv_sty_in_sty (trans_rtyp2 r).
Proof with eauto.
    intros r.
    induction r; introv Notin; simpls...
Qed.

Lemma notin_rtyp_sty : forall A X,
    X `notin` fv_rtyp_in_rt A ->
    X `notin` fv_sty_in_sty (trans_rt A )

with

notin_rtyp_rlist : forall R X,
    X `notin` fv_rtyp_in_rlist R ->
    X `notin` fv_sty_in_sty (trans_rlist R)

with

notin_rtyp_rtyp : forall r X,
    X `notin` fv_rtyp_in_rtyp r ->
    X `notin` fv_sty_in_sty (trans_rtyp r).

Proof with eauto using notin_rtyp_rtyp2.

  - Case "typ".

    intros A.
    induction A; introv Notin; simpls...

  - Case "rlist".

    intros R.
    induction R; introv Notin; simpls...

  - Case "rtyp".

    intros r.
    induction r; introv Notin; simpls...

Qed.



(* ********************************************************************** *)
(** * Type safety lemmas *)
(* ********************************************************************** *)

Section type_safe_trans.

  (* ********************************************************************** *)
  (* These are internal properties of Harper's system *)
  Variable cmp_regular : forall T r r',
    cmp T r r' ->
    wfr T r /\ wfr T r'.

  Variable wtt_regular : forall T G e1 t E,
    wtt T G e1 t E ->
    wfrt T t /\ wftc T.
  (* ********************************************************************** *)


  Lemma cmp_list_regular : forall T r R,
      cmpList T r R ->
      wftc T ->
      wfr T r /\ wfcl T R.
    Proof with eauto.
      introv CMP.
      induction CMP; introv WFTC; splits; simpls...
      forwards (? & ?) : cmp_regular H...
      forwards (? & ?) : cmp_regular H...
      forwards (? & ?) : IHCMP WFTC...
    Qed.



  Lemma wfr_to_swft2 : forall T r,
        wfr T r ->
        swft (trans_Ttx T) (trans_rtyp2 r).
  Proof with eauto.
    introv WFR.

    induction WFR; simpls...

    econstructor.
    eapply binds_map_2...
  Qed.


  Lemma wfcl_to_swft : forall T R,
      wfcl T R ->
      swft (trans_Ttx T) (trans_rlist R)
  with

  wfr_to_swft : forall T r,
      wfr T r ->
      swft (trans_Ttx T) (trans_rtyp r)

  with

  wft_to_swft :forall T t,
      wfrt T t ->
      swft (trans_Ttx T) (trans_rt t).


  Proof with eauto using wfr_to_swft2.
    - Case "wfcl_to_swft".

      introv WFCL.

      induction WFCL.

      + SCase "empty".
        clear wfr_to_swft wft_to_swft wfcl_to_swft.
        simpls...

      + SCase "rl_rtyp".
        forwards : wfr_to_swft H.
        clear wfr_to_swft wft_to_swft wfcl_to_swft.
        simpls...

    - Case "wfr_to_swft".

      introv WFR.

      induction WFR.

      + SCase "var".
        clear wfr_to_swft wft_to_swft wfcl_to_swft.
        simpls.
        econstructor.
        eapply binds_map_2...


      + SCase "record".
        forwards : wft_to_swft H.
        clear wfr_to_swft wft_to_swft wfcl_to_swft.
        simpls...

      + SCase "empty".
        clear wfr_to_swft wft_to_swft wfcl_to_swft.
        simpls...

      + SCase "restrict".
        clear wfr_to_swft wft_to_swft wfcl_to_swft.
        simpls...


    - Case "wft_to_swft".

      introv WFT.

      induction WFT.

      + SCase "base".
        clear wfr_to_swft wft_to_swft wfcl_to_swft.
        simpls...

      + SCase "arrow".
        clear wfr_to_swft wft_to_swft wfcl_to_swft.
        simpls...

      + SCase "forall".
        forwards : wfcl_to_swft H.
        clear wfr_to_swft wft_to_swft wfcl_to_swft.
        simpls.
        pick fresh X and apply swft_all; auto.
        replace (sty_var_f X) with (trans_rtyp (r_TyVar_f X)); auto.
        rewrite <- trans_open_rt_wrt_rtyp...

      + SCase "record".
        forwards : wfr_to_swft H.
        clear wfr_to_swft wft_to_swft wfcl_to_swft.
        simpls...
  Qed.


  Lemma wftc_to_swfte : forall T,
      wftc T ->
      swfte (trans_Ttx T).
  Proof with eauto.
    introv WFTC.

    induction WFTC; simpls...

    forwards : wfcl_to_swft H.

    econstructor...
    unfold trans_Ttx...
  Qed.


  Lemma wfc_to_swfe : forall T G,
      wfc T G ->
      swfe (trans_Ttx T) (trans_Gtx G).
  Proof with eauto using wft_to_swft.
    introv H.
    induction H; simpls...
    constructor...
    unfold trans_Gtx...
    unfold trans_Ttx...
  Qed.



  Lemma teq_csub2 : forall T r r',
      teq T (rt_Record r) (rt_Record r') ->
      uniq T ->
      csub (trans_Ttx T) (trans_rtyp2 r) (trans_rtyp2 r') /\
      csub (trans_Ttx T) (trans_rtyp2 r') (trans_rtyp2 r).
  Proof.
  Admitted.


  Lemma ceq_csub: forall T R R',
      ceq T R R' ->
      uniq T ->
      csub (trans_Ttx T) (trans_rlist R) (trans_rlist R') /\
      csub (trans_Ttx T) (trans_rlist R') (trans_rlist R).
  Proof with eauto using wft_to_swft, wfr_to_swft, wfcl_to_swft, notin_rtyp_sty, wfr_to_swft2.
      introv Eq.
      induction Eq; introv Uniq.

      + SCase "refl".
        splits...

      + SCase "sym".
        destruct (IHEq Uniq).
        splits...

      + SCase "trans".

        destruct (IHEq1 Uniq) as (Sub1 & Sub2).
        destruct (IHEq2 Uniq) as (Sub3 & Sub4).

        splits...


      + SCase "inner".

        lets (? & ?) : teq_csub2 H; try assumption.

        destruct (IHEq Uniq) as (Sub1 & Sub2).
        simpls.
        splits; eapply CS_and...

      + SCase "swap".

        simpls.
        splits.

        eapply CS_and.
        apply CS_trans with (B := (sty_and (trans_rtyp2 r') (trans_rlist R)))...
        eapply CS_andr...
        eapply CS_and.
        eapply CS_andl...
        apply CS_trans with (B := (sty_and (trans_rtyp2 r') (trans_rlist R)))...
        eapply CS_andr...

        eapply CS_and.
        apply CS_trans with (B := (sty_and (trans_rtyp2 r) (trans_rlist R)))...
        eapply CS_andr...
        eapply CS_and.
        eapply CS_andl...
        apply CS_trans with (B := (sty_and (trans_rtyp2 r) (trans_rlist R)))...
        eapply CS_andr...

      + SCase "empty".
        simpls.
        splits...

        eapply CS_and...

      + SCase "merge".

        simpls.
        inverts H.
        splits.

        eapply CS_and.
        apply CS_trans with (B := (sty_and (trans_rtyp2 r1) (trans_rtyp2 r2)))...
        eapply CS_andl...
        eapply CS_and.
        apply CS_trans with (B := (sty_and (trans_rtyp2 r1) (trans_rtyp2 r2)))...
        eapply CS_andl...
        eapply CS_andr...

        eapply CS_and.
        eapply CS_and.
        eapply CS_andl...
        apply CS_trans with (B := (sty_and (trans_rtyp2 r2) (trans_rlist R)))...
        eapply CS_andr...
        apply CS_trans with (B := (sty_and (trans_rtyp2 r2) (trans_rlist R)))...
        eapply CS_andr...

      + SCase "dupl".

        simpls; splits.


        eapply CS_and.
        eapply CS_andl...
        apply CS_trans with (B := (sty_and (trans_rtyp2 r) (trans_rlist R)))...
        eapply CS_andr...

        eapply CS_and.
        eapply CS_andl...
        apply CS_trans with (B := (sty_and (trans_rtyp2 r) (trans_rlist R)))...


      + SCase "base".

        simpls; splits...
  Qed.


  Lemma teq_csub : forall T t t',
      teq T t t' ->
      uniq T ->
      csub (trans_Ttx T) (trans_rt t) (trans_rt t') /\
      csub (trans_Ttx T) (trans_rt t') (trans_rt t).

  Proof with eauto using wft_to_swft, wfr_to_swft, wfcl_to_swft, notin_rtyp_sty, ceq_csub.

      introv Eq.
      induction Eq; introv Uniq.

      + SCase "refl".
        splits...

      + SCase "sym".
        destruct IHEq...

      + SCase "trans".

        destruct (IHEq1 Uniq) as (Sub1 & Sub2).
        destruct (IHEq2 Uniq) as (Sub3 & Sub4).

        splits...

      + SCase "arrow".

        simpls.

        destruct (IHEq1 Uniq) as (Sub1 & Sub2).
        destruct (IHEq2 Uniq) as (Sub3 & Sub4).

        splits...

      + SCase "typ_all".
        simpls.
        splits.

        pick fresh a.
        forwards ((c1 & Sub1) & (c2 & Sub2)) : H1 a; auto.
        forwards ((c3 & ?) & (c4 & ?)) : ceq_csub H; auto.
        rewrite trans_open_rt_wrt_rtyp in *.
        rewrite trans_open_rt_wrt_rtyp in *.
        unfolds.
        exists (co_forall c1).
        pick fresh b and apply S_forall; eauto.
        apply sub_renaming with (X := a)...
        unfold trans_Ttx; eauto.
        unfold trans_Ttx; eauto.
        rewrite_env (nil ++ [(a, trans_rlist R')] ++ trans_Ttx Ttx).
        apply sub_narrow with (Q := trans_rlist R); auto.
        simpls...
        unfold trans_Ttx; eauto.


        pick fresh a.
        forwards ((c1 & Sub1) & (c2 & Sub2)) : H1 a; auto.
        forwards ((c3 & ?) & (c4 & ?)) : ceq_csub H; auto.
        rewrite trans_open_rt_wrt_rtyp in *.
        rewrite trans_open_rt_wrt_rtyp in *.
        unfolds.
        exists (co_forall c2).
        pick fresh b and apply S_forall; eauto.
        apply sub_renaming with (X := a)...
        unfold trans_Ttx; eauto.
        unfold trans_Ttx; eauto.


      + SCase "base".
        forwards (? & ?) : IHEq...

        simpls; splits...

      + SCase "merge".
        destruct (IHEq1 Uniq).
        destruct (IHEq2 Uniq).

        simpls; splits; eapply CS_and...


      + SCase "merge_unit".

        simpls; splits...

        eapply CS_and...

      + SCase "merge_assoc".
        forwards (? & ?): cmp_regular H.
        forwards (? & ?): cmp_regular H0.
        simpls; splits.

        eapply CS_and.
        eapply CS_and.
        eapply CS_andl...
        apply CS_trans with (B := (sty_and (trans_rtyp r2) (trans_rtyp r3)))...
        eapply CS_andr...
        apply CS_trans with (B := (sty_and (trans_rtyp r2) (trans_rtyp r3)))...
        eapply CS_andr...

        eapply CS_and.
        apply CS_trans with (B := (sty_and (trans_rtyp r1) (trans_rtyp r2)))...
        eapply CS_andl...
        eapply CS_and.
        apply CS_trans with (B := (sty_and (trans_rtyp r1) (trans_rtyp r2)))...
        eapply CS_andl...
        eapply CS_andr...

      + SCase "merge_comm".
        forwards (? & ?): cmp_regular H.

        simpls; splits; eapply CS_and...
  Qed.


  Lemma trans_rtyp_sub : forall T r,
      wfr T r ->
      csub (trans_Ttx T) (trans_rtyp2 r) (trans_rtyp r).
  Admitted.


  Lemma rtyp_in_rlist_sub1: forall T r R,
      rtyp_in_rlist r R ->
      wfcl T R ->
      wfr T r ->
      csub (trans_Ttx T) (trans_rlist R) (trans_rtyp r).
  Proof with eauto.
    introv Rlst.
    induction Rlst; introv WFCL WFT; simpls...

    inverts WFCL.
    forwards : trans_rtyp_sub WFT.
    eapply CS_trans...
    eapply CS_andl...
    eapply wfcl_to_swft...

    inverts WFCL.
    forwards : trans_rtyp_sub H2.
    eapply CS_trans...
  Qed.


  Lemma rtyp_in_rlist_sub2: forall T r R,
      rtyp_in_rlist r R ->
      wfcl T R ->
      wfr T r ->
      csub (trans_Ttx T) (trans_rlist R) (trans_rtyp2 r).
  Proof with eauto using wfcl_to_swft, wfr_to_swft, wfr_to_swft, wfr_to_swft2.
    introv Rlst.
    induction Rlst; introv WFCL WFT; simpls...

    inverts WFCL.

    eapply CS_andl...

    inverts WFCL.
    specializes IHRlst...
  Qed.

  Lemma cmp_disjoint : forall T r r',
      cmp T r r' ->
      wftc T ->
      disjoint (trans_Ttx T) (trans_rtyp r) (trans_rtyp2 r') /\
      disjoint (trans_Ttx T) (trans_rtyp2 r) (trans_rtyp r').
  Proof with eauto using wft_to_swft, wfr_to_swft, wftc_to_swfte, wfr_to_swft2.
    introv CMP.

    induction CMP; introv Uniq; simpls...

    - Case "eq".
      assert (uniq (trans_Ttx Ttx)).
      unfold trans_Ttx...
      forwards (? & ?) : IHCMP Uniq.
      splits.

      lets ((? & ?) & ?) : teq_csub H...
      lets ((? & ?) & ?) : teq_csub2 H0...
      simpls.
      eapply disjoint_sub...
      eapply disjoint_symmetric...
      eapply disjoint_sub...
      eapply disjoint_symmetric...

      lets ((? & ?) & ?) : teq_csub2 H...
      lets ((? & ?) & ?) : teq_csub H0...
      simpls.
      eapply disjoint_sub...
      eapply disjoint_symmetric...
      eapply disjoint_sub...
      eapply disjoint_symmetric...


    - Case "symm".

      assert (uniq (trans_Ttx Ttx)).
      unfold trans_Ttx...
      forwards (? & ?) : IHCMP Uniq.
      splits.
      eapply disjoint_symmetric...
      eapply disjoint_symmetric...


    - Case "base".

      assert (uniq (trans_Ttx Ttx)).
      unfold trans_Ttx...
      forwards (? & ?) : IHCMP Uniq.

      splits...
      (* TODO: ningnin *)
      admit.


    - Case "tvar".

      splits.

      forwards (c & ?) : rtyp_in_rlist_sub2 H0...
      eapply D_tvarL...
      unfold trans_Ttx...

      forwards (c & ?) : rtyp_in_rlist_sub1 H0...
      eapply D_tvarL...
      unfold trans_Ttx...


    - Case "mergeE1".

      forwards (Dis1 & Dis2) : IHCMP Uniq.
      forwards (? & ?): cmp_regular CMP...
      splits.

      eapply disjoint_and in Dis1...
      inverts Dis1...

      eapply disjoint_and in Dis2...
      inverts Dis2...

    - Case "mergeE2".

      forwards (Dis1 & Dis2) : IHCMP Uniq.
      forwards (? & ?): cmp_regular CMP...
      splits.

      eapply disjoint_and in Dis1...
      inverts Dis1...

      eapply disjoint_and in Dis2...
      inverts Dis2...


    - Case "mergeI".

      forwards (? & ?) : IHCMP1 Uniq.
      forwards (? & ?) : IHCMP2 Uniq.
      forwards (? & ?) : IHCMP3 Uniq.

      splits...

    - Case "BaseBase".

      splits...

    - Case "Empty".
      splits...

  Qed.


  Lemma cmp_list_disjoint : forall T r R,
      cmpList T r R ->
      wftc T ->
      disjoint (trans_Ttx T) (trans_rtyp r) (trans_rlist R).
  Proof with eauto using wfr_to_swft.
    introv CMP.
    induction CMP; introv Uniq; simpls...

    forwards (? & ?): cmp_disjoint...

  Qed.


  Lemma cmp_disjoint2 : forall T r r',
      cmp T r r' ->
      wftc T ->
      disjoint (trans_Ttx T) (trans_rtyp r) (trans_rtyp r').
  Proof.
    (* TODO: ningning *)
  Admitted.

  Theorem type_safe : forall T G e t E,
      wtt T G e t E ->
      has_type (trans_Ttx T) (trans_Gtx G) E Inf (trans_rt t).
  Proof with eauto using wft_to_swft, wfc_to_swfe, wftc_to_swfte, wfcl_to_swft, wfr_to_swft, cmp_list_disjoint, cmp_disjoint2.

    introv WTT.

    induction WTT; simpls...


    - Case "wtt_eq".
      lets (? & ?) : teq_csub...
      forwards (? & ?) : wtt_regular WTT...

    - Case "wtt_var".
      econstructor...
      eapply binds_map_2...

    - Case "wtt_abs".
      econstructor...

      pick fresh x and apply T2_abs...
      forwards WTT : H0 x...
      forwards (? & ?) : wtt_regular WTT...
      forwards : H1 x...

    - Case "wtt_app".
      forwards (WFTC & ?) : wtt_regular WTT1...
      inverts WFTC...

      econstructor...


    - Case "wtt_merge".
      forwards (W & ?) : wtt_regular WTT1.
      inverts W.
      forwards (W & ?) : wtt_regular WTT2.
      inverts W.
      econstructor...

    - Case "wtt_restr".
      forwards (W & ?) : wtt_regular WTT.
      inverts W as W.
      inverts W as W.
      inverts W as W.

      econstructor.
      eapply T2_sub...

    - Case "wtt_select".
      forwards (W & ?) : wtt_regular WTT.
      inverts W as W.
      inverts W as W.
      inverts W as W.
      econstructor...
      econstructor...
      eapply T2_sub...

    - Case "wtt_tabs".
      pick fresh a and apply T2_tabs...
      forwards : H1 a...
      replace (sty_var_f a) with (trans_rtyp (r_TyVar_f a))...
      rewrite <- trans_open_rt_wrt_rtyp...

    - Case "wtt_tapp".
      forwards (? & ?) : wtt_regular WTT.
      forwards (? & ?) : cmp_list_regular H...
      rewrite trans_open_rt_wrt_rtyp.
  Qed.

End type_safe_trans.
