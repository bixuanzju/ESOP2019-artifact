Require Import Metalib.Metatheory.
Definition typvar := var.
Definition expvar := var.
Definition i := nat.



(* ********************************************************************** *)
(** * Fi+ types *)

Inductive sty : Set := 
 | sty_nat : sty
 | sty_top : sty
 | sty_bot : sty
 | sty_var_b (_:nat)
 | sty_var_f (X:typvar)
 | sty_arrow (A:sty) (B:sty)
 | sty_and (A:sty) (B:sty)
 | sty_all (A:sty) (B:sty)
 | sty_rcd (l:i) (A:sty).


(* ********************************************************************** *)
(** * Fco types *)

Inductive ty : Set := 
 | ty_nat : ty
 | ty_unit : ty
 | ty_var_b (_:nat)
 | ty_var_f (X:typvar)
 | ty_arrow (T1:ty) (T2:ty)
 | ty_prod (T1:ty) (T2:ty)
 | ty_all (T:ty).


(* ********************************************************************** *)
(** * Coercions *)

Inductive co : Set :=
 | co_id : co
 | co_trans (c1:co) (c2:co)
 | co_top : co
 | co_bot : co
 | co_arr (c1:co) (c2:co)
 | co_pair (c1:co) (c2:co)
 | co_proj1 : co
 | co_proj2 : co
 | co_forall (c:co)
 | co_distArr : co
 | co_topArr : co
 | co_topAll : co
 | co_distPoly : co.


(* ********************************************************************** *)
(** * Fi+ expressions *)

Inductive sexp : Set := 
 | sexp_var_b (_:nat)
 | sexp_var_f (x:expvar)
 | sexp_top : sexp
 | sexp_lit (i5:i)
 | sexp_abs (ee:sexp)
 | sexp_app (ee1:sexp) (ee2:sexp)
 | sexp_merge (ee1:sexp) (ee2:sexp)
 | sexp_tabs (A:sty) (ee:sexp)
 | sexp_tapp (ee:sexp) (A:sty)
 | sexp_anno (ee:sexp) (A:sty)
 | sexp_rcd (l:i) (ee:sexp)
 | sexp_proj (ee:sexp) (l:i).


(* ********************************************************************** *)
(** * Fco expressions *)

Inductive exp : Set := 
 | exp_var_b (_:nat)
 | exp_var_f (x:expvar)
 | exp_unit : exp
 | exp_lit (i5:i)
 | exp_abs (e:exp)
 | exp_app (e1:exp) (e2:exp)
 | exp_pair (e1:exp) (e2:exp)
 | exp_capp (c:co) (e:exp)
 | exp_tabs (e:exp)
 | exp_tapp (e:exp) (T:ty).


(* ********************************************************************** *)
(** * Fi+ expressions contexts *)

Inductive CC : Set :=
 | C_Empty : CC
 | C_Lam (x:expvar) (CC5:CC)
 | C_tabs (X:typvar) (A:sty) (CC5:CC)
 | C_tapp (CC5:CC) (A:sty)
 | C_AppL (CC5:CC) (ee:sexp)
 | C_AppRd (ee:sexp) (CC5:CC)
 | C_MergeL (CC5:CC) (ee:sexp)
 | C_MergeR (ee:sexp) (CC5:CC)
 | C_Anno (CC5:CC) (A:sty)
 | C_Rcd (l:i) (CC5:CC)
 | C_Proj (CC5:CC) (l:i).


(* ********************************************************************** *)
(** * Fi+ term contexts *)

Definition sctx : Set := list ( atom * sty ).


(* ********************************************************************** *)
(** * Fi+ type contexts *)

Definition stctx : Set := list ( atom * sty ).

Inductive dirflag : Set :=  (*r checking direction *)
 | Inf : dirflag
 | Chk : dirflag.


(* ********************************************************************** *)
(** * Fco expressions contexts *)

Inductive cc : Set :=  (*r target context *)
 | cc_empty : cc
 | cc_lam (x:expvar) (cc5:cc)
 | cc_tabs (X:typvar) (cc5:cc)
 | cc_tapp (cc5:cc) (T:ty)
 | cc_appL (cc5:cc) (e:exp)
 | cc_appR (e:exp) (cc5:cc)
 | cc_pairL (cc5:cc) (e:exp)
 | cc_pairR (e:exp) (cc5:cc)
 | cc_co (c:co) (cc5:cc).


(* ********************************************************************** *)
(** * Fco type contexts *)

Definition tctx : Set := list (atom * unit).


(* ********************************************************************** *)
(** * Fco term contexts *)

Definition ctx : Set := list ( atom * ty ).


(* ********************************************************************** *)
(** * Algorithmic queue *)

Inductive qs : Set := 
 | qs_arr (A:sty)
 | qs_all (X:typvar) (A:sty)
 | qs_rcd (l:i).

Definition p : Set := list atom.

Definition g : Set := list atom.

Definition seqs : Set := list qs.


(* ********************************************************************** *)
(** * Auxiliary definitions for locally-nameless encoding *)

Fixpoint open_ty_wrt_ty_rec (k:nat) (T_5:ty) (T__6:ty) {struct T__6}: ty :=
  match T__6 with
  | ty_nat => ty_nat 
  | ty_unit => ty_unit 
  | (ty_var_b nat) => 
      match lt_eq_lt_dec nat k with
        | inleft (left _) => ty_var_b nat
        | inleft (right _) => T_5
        | inright _ => ty_var_b (nat - 1)
      end
  | (ty_var_f X) => ty_var_f X
  | (ty_arrow T1 T2) => ty_arrow (open_ty_wrt_ty_rec k T_5 T1) (open_ty_wrt_ty_rec k T_5 T2)
  | (ty_prod T1 T2) => ty_prod (open_ty_wrt_ty_rec k T_5 T1) (open_ty_wrt_ty_rec k T_5 T2)
  | (ty_all T) => ty_all (open_ty_wrt_ty_rec (S k) T_5 T)
end.

Fixpoint open_sty_wrt_sty_rec (k:nat) (A5:sty) (A_6:sty) {struct A_6}: sty :=
  match A_6 with
  | sty_nat => sty_nat 
  | sty_top => sty_top 
  | sty_bot => sty_bot 
  | (sty_var_b nat) => 
      match lt_eq_lt_dec nat k with
        | inleft (left _) => sty_var_b nat
        | inleft (right _) => A5
        | inright _ => sty_var_b (nat - 1)
      end
  | (sty_var_f X) => sty_var_f X
  | (sty_arrow A B) => sty_arrow (open_sty_wrt_sty_rec k A5 A) (open_sty_wrt_sty_rec k A5 B)
  | (sty_and A B) => sty_and (open_sty_wrt_sty_rec k A5 A) (open_sty_wrt_sty_rec k A5 B)
  | (sty_all A B) => sty_all (open_sty_wrt_sty_rec k A5 A) (open_sty_wrt_sty_rec (S k) A5 B)
  | (sty_rcd l A) => sty_rcd l (open_sty_wrt_sty_rec k A5 A)
end.

Fixpoint open_exp_wrt_ty_rec (k:nat) (T_5:ty) (e_5:exp) {struct e_5}: exp :=
  match e_5 with
  | (exp_var_b nat) => exp_var_b nat
  | (exp_var_f x) => exp_var_f x
  | exp_unit => exp_unit 
  | (exp_lit i5) => exp_lit i5
  | (exp_abs e) => exp_abs (open_exp_wrt_ty_rec k T_5 e)
  | (exp_app e1 e2) => exp_app (open_exp_wrt_ty_rec k T_5 e1) (open_exp_wrt_ty_rec k T_5 e2)
  | (exp_pair e1 e2) => exp_pair (open_exp_wrt_ty_rec k T_5 e1) (open_exp_wrt_ty_rec k T_5 e2)
  | (exp_capp c e) => exp_capp c (open_exp_wrt_ty_rec k T_5 e)
  | (exp_tabs e) => exp_tabs (open_exp_wrt_ty_rec (S k) T_5 e)
  | (exp_tapp e T) => exp_tapp (open_exp_wrt_ty_rec k T_5 e) (open_ty_wrt_ty_rec k T_5 T)
end.

Fixpoint open_sexp_wrt_sty_rec (k:nat) (A5:sty) (ee_5:sexp) {struct ee_5}: sexp :=
  match ee_5 with
  | (sexp_var_b nat) => sexp_var_b nat
  | (sexp_var_f x) => sexp_var_f x
  | sexp_top => sexp_top 
  | (sexp_lit i5) => sexp_lit i5
  | (sexp_abs ee) => sexp_abs (open_sexp_wrt_sty_rec k A5 ee)
  | (sexp_app ee1 ee2) => sexp_app (open_sexp_wrt_sty_rec k A5 ee1) (open_sexp_wrt_sty_rec k A5 ee2)
  | (sexp_merge ee1 ee2) => sexp_merge (open_sexp_wrt_sty_rec k A5 ee1) (open_sexp_wrt_sty_rec k A5 ee2)
  | (sexp_tabs A ee) => sexp_tabs (open_sty_wrt_sty_rec k A5 A) (open_sexp_wrt_sty_rec (S k) A5 ee)
  | (sexp_tapp ee A) => sexp_tapp (open_sexp_wrt_sty_rec k A5 ee) (open_sty_wrt_sty_rec k A5 A)
  | (sexp_anno ee A) => sexp_anno (open_sexp_wrt_sty_rec k A5 ee) (open_sty_wrt_sty_rec k A5 A)
  | (sexp_rcd l ee) => sexp_rcd l (open_sexp_wrt_sty_rec k A5 ee)
  | (sexp_proj ee l) => sexp_proj (open_sexp_wrt_sty_rec k A5 ee) l
end.

Fixpoint open_sexp_wrt_sexp_rec (k:nat) (ee_5:sexp) (ee__6:sexp) {struct ee__6}: sexp :=
  match ee__6 with
  | (sexp_var_b nat) => 
      match lt_eq_lt_dec nat k with
        | inleft (left _) => sexp_var_b nat
        | inleft (right _) => ee_5
        | inright _ => sexp_var_b (nat - 1)
      end
  | (sexp_var_f x) => sexp_var_f x
  | sexp_top => sexp_top 
  | (sexp_lit i5) => sexp_lit i5
  | (sexp_abs ee) => sexp_abs (open_sexp_wrt_sexp_rec (S k) ee_5 ee)
  | (sexp_app ee1 ee2) => sexp_app (open_sexp_wrt_sexp_rec k ee_5 ee1) (open_sexp_wrt_sexp_rec k ee_5 ee2)
  | (sexp_merge ee1 ee2) => sexp_merge (open_sexp_wrt_sexp_rec k ee_5 ee1) (open_sexp_wrt_sexp_rec k ee_5 ee2)
  | (sexp_tabs A ee) => sexp_tabs A (open_sexp_wrt_sexp_rec k ee_5 ee)
  | (sexp_tapp ee A) => sexp_tapp (open_sexp_wrt_sexp_rec k ee_5 ee) A
  | (sexp_anno ee A) => sexp_anno (open_sexp_wrt_sexp_rec k ee_5 ee) A
  | (sexp_rcd l ee) => sexp_rcd l (open_sexp_wrt_sexp_rec k ee_5 ee)
  | (sexp_proj ee l) => sexp_proj (open_sexp_wrt_sexp_rec k ee_5 ee) l
end.

Fixpoint open_exp_wrt_exp_rec (k:nat) (e_5:exp) (e__6:exp) {struct e__6}: exp :=
  match e__6 with
  | (exp_var_b nat) => 
      match lt_eq_lt_dec nat k with
        | inleft (left _) => exp_var_b nat
        | inleft (right _) => e_5
        | inright _ => exp_var_b (nat - 1)
      end
  | (exp_var_f x) => exp_var_f x
  | exp_unit => exp_unit 
  | (exp_lit i5) => exp_lit i5
  | (exp_abs e) => exp_abs (open_exp_wrt_exp_rec (S k) e_5 e)
  | (exp_app e1 e2) => exp_app (open_exp_wrt_exp_rec k e_5 e1) (open_exp_wrt_exp_rec k e_5 e2)
  | (exp_pair e1 e2) => exp_pair (open_exp_wrt_exp_rec k e_5 e1) (open_exp_wrt_exp_rec k e_5 e2)
  | (exp_capp c e) => exp_capp c (open_exp_wrt_exp_rec k e_5 e)
  | (exp_tabs e) => exp_tabs (open_exp_wrt_exp_rec k e_5 e)
  | (exp_tapp e T) => exp_tapp (open_exp_wrt_exp_rec k e_5 e) T
end.

Fixpoint open_cc_wrt_ty_rec (k:nat) (T5:ty) (cc_6:cc) {struct cc_6}: cc :=
  match cc_6 with
  | cc_empty => cc_empty 
  | (cc_lam x cc5) => cc_lam x (open_cc_wrt_ty_rec k T5 cc5)
  | (cc_tabs X cc5) => cc_tabs X (open_cc_wrt_ty_rec k T5 cc5)
  | (cc_tapp cc5 T) => cc_tapp (open_cc_wrt_ty_rec k T5 cc5) (open_ty_wrt_ty_rec k T5 T)
  | (cc_appL cc5 e) => cc_appL (open_cc_wrt_ty_rec k T5 cc5) (open_exp_wrt_ty_rec k T5 e)
  | (cc_appR e cc5) => cc_appR (open_exp_wrt_ty_rec k T5 e) (open_cc_wrt_ty_rec k T5 cc5)
  | (cc_pairL cc5 e) => cc_pairL (open_cc_wrt_ty_rec k T5 cc5) (open_exp_wrt_ty_rec k T5 e)
  | (cc_pairR e cc5) => cc_pairR (open_exp_wrt_ty_rec k T5 e) (open_cc_wrt_ty_rec k T5 cc5)
  | (cc_co c cc5) => cc_co c (open_cc_wrt_ty_rec k T5 cc5)
end.

Fixpoint open_CC_wrt_sty_rec (k:nat) (A5:sty) (CC_6:CC) {struct CC_6}: CC :=
  match CC_6 with
  | C_Empty => C_Empty 
  | (C_Lam x CC5) => C_Lam x (open_CC_wrt_sty_rec k A5 CC5)
  | (C_tabs X A CC5) => C_tabs X (open_sty_wrt_sty_rec k A5 A) (open_CC_wrt_sty_rec k A5 CC5)
  | (C_tapp CC5 A) => C_tapp (open_CC_wrt_sty_rec k A5 CC5) (open_sty_wrt_sty_rec k A5 A)
  | (C_AppL CC5 ee) => C_AppL (open_CC_wrt_sty_rec k A5 CC5) (open_sexp_wrt_sty_rec k A5 ee)
  | (C_AppRd ee CC5) => C_AppRd (open_sexp_wrt_sty_rec k A5 ee) (open_CC_wrt_sty_rec k A5 CC5)
  | (C_MergeL CC5 ee) => C_MergeL (open_CC_wrt_sty_rec k A5 CC5) (open_sexp_wrt_sty_rec k A5 ee)
  | (C_MergeR ee CC5) => C_MergeR (open_sexp_wrt_sty_rec k A5 ee) (open_CC_wrt_sty_rec k A5 CC5)
  | (C_Anno CC5 A) => C_Anno (open_CC_wrt_sty_rec k A5 CC5) (open_sty_wrt_sty_rec k A5 A)
  | (C_Rcd l CC5) => C_Rcd l (open_CC_wrt_sty_rec k A5 CC5)
  | (C_Proj CC5 l) => C_Proj (open_CC_wrt_sty_rec k A5 CC5) l
end.

Fixpoint open_CC_wrt_sexp_rec (k:nat) (ee5:sexp) (CC_6:CC) {struct CC_6}: CC :=
  match CC_6 with
  | C_Empty => C_Empty 
  | (C_Lam x CC5) => C_Lam x (open_CC_wrt_sexp_rec k ee5 CC5)
  | (C_tabs X A CC5) => C_tabs X A (open_CC_wrt_sexp_rec k ee5 CC5)
  | (C_tapp CC5 A) => C_tapp (open_CC_wrt_sexp_rec k ee5 CC5) A
  | (C_AppL CC5 ee) => C_AppL (open_CC_wrt_sexp_rec k ee5 CC5) (open_sexp_wrt_sexp_rec k ee5 ee)
  | (C_AppRd ee CC5) => C_AppRd (open_sexp_wrt_sexp_rec k ee5 ee) (open_CC_wrt_sexp_rec k ee5 CC5)
  | (C_MergeL CC5 ee) => C_MergeL (open_CC_wrt_sexp_rec k ee5 CC5) (open_sexp_wrt_sexp_rec k ee5 ee)
  | (C_MergeR ee CC5) => C_MergeR (open_sexp_wrt_sexp_rec k ee5 ee) (open_CC_wrt_sexp_rec k ee5 CC5)
  | (C_Anno CC5 A) => C_Anno (open_CC_wrt_sexp_rec k ee5 CC5) A
  | (C_Rcd l CC5) => C_Rcd l (open_CC_wrt_sexp_rec k ee5 CC5)
  | (C_Proj CC5 l) => C_Proj (open_CC_wrt_sexp_rec k ee5 CC5) l
end.

Fixpoint open_cc_wrt_exp_rec (k:nat) (e5:exp) (cc_6:cc) {struct cc_6}: cc :=
  match cc_6 with
  | cc_empty => cc_empty 
  | (cc_lam x cc5) => cc_lam x (open_cc_wrt_exp_rec k e5 cc5)
  | (cc_tabs X cc5) => cc_tabs X (open_cc_wrt_exp_rec k e5 cc5)
  | (cc_tapp cc5 T) => cc_tapp (open_cc_wrt_exp_rec k e5 cc5) T
  | (cc_appL cc5 e) => cc_appL (open_cc_wrt_exp_rec k e5 cc5) (open_exp_wrt_exp_rec k e5 e)
  | (cc_appR e cc5) => cc_appR (open_exp_wrt_exp_rec k e5 e) (open_cc_wrt_exp_rec k e5 cc5)
  | (cc_pairL cc5 e) => cc_pairL (open_cc_wrt_exp_rec k e5 cc5) (open_exp_wrt_exp_rec k e5 e)
  | (cc_pairR e cc5) => cc_pairR (open_exp_wrt_exp_rec k e5 e) (open_cc_wrt_exp_rec k e5 cc5)
  | (cc_co c cc5) => cc_co c (open_cc_wrt_exp_rec k e5 cc5)
end.

Definition open_qs_wrt_sty_rec (k:nat) (A5:sty) (qs5:qs) : qs :=
  match qs5 with
  | (qs_arr A) => qs_arr (open_sty_wrt_sty_rec k A5 A)
  | (qs_all X A) => qs_all X (open_sty_wrt_sty_rec k A5 A)
  | (qs_rcd l) => qs_rcd l
end.

Definition open_cc_wrt_ty T5 cc_6 := open_cc_wrt_ty_rec 0 cc_6 T5.

Definition open_exp_wrt_exp e_5 e__6 := open_exp_wrt_exp_rec 0 e__6 e_5.

Definition open_CC_wrt_sty A5 CC_6 := open_CC_wrt_sty_rec 0 CC_6 A5.

Definition open_CC_wrt_sexp ee5 CC_6 := open_CC_wrt_sexp_rec 0 CC_6 ee5.

Definition open_sexp_wrt_sty A5 ee_5 := open_sexp_wrt_sty_rec 0 ee_5 A5.

Definition open_cc_wrt_exp e5 cc_6 := open_cc_wrt_exp_rec 0 cc_6 e5.

Definition open_sty_wrt_sty A5 A_6 := open_sty_wrt_sty_rec 0 A_6 A5.

Definition open_qs_wrt_sty A5 qs5 := open_qs_wrt_sty_rec 0 qs5 A5.

Definition open_exp_wrt_ty T_5 e_5 := open_exp_wrt_ty_rec 0 e_5 T_5.

Definition open_ty_wrt_ty T_5 T__6 := open_ty_wrt_ty_rec 0 T__6 T_5.

Definition open_sexp_wrt_sexp ee_5 ee__6 := open_sexp_wrt_sexp_rec 0 ee__6 ee_5.

(** terms are locally-closed pre-terms *)
(** definitions *)

(* defns LC_sty *)
Inductive lc_sty : sty -> Prop :=    (* defn lc_sty *)
 | lc_sty_nat : 
     (lc_sty sty_nat)
 | lc_sty_top : 
     (lc_sty sty_top)
 | lc_sty_bot : 
     (lc_sty sty_bot)
 | lc_sty_var_f : forall (X:typvar),
     (lc_sty (sty_var_f X))
 | lc_sty_arrow : forall (A B:sty),
     (lc_sty A) ->
     (lc_sty B) ->
     (lc_sty (sty_arrow A B))
 | lc_sty_and : forall (A B:sty),
     (lc_sty A) ->
     (lc_sty B) ->
     (lc_sty (sty_and A B))
 | lc_sty_all : forall (A B:sty),
     (lc_sty A) ->
      ( forall X , lc_sty  ( open_sty_wrt_sty B (sty_var_f X) )  )  ->
     (lc_sty (sty_all A B))
 | lc_sty_rcd : forall (l:i) (A:sty),
     (lc_sty A) ->
     (lc_sty (sty_rcd l A)).

(* defns LC_ty *)
Inductive lc_ty : ty -> Prop :=    (* defn lc_ty *)
 | lc_ty_nat : 
     (lc_ty ty_nat)
 | lc_ty_unit : 
     (lc_ty ty_unit)
 | lc_ty_var_f : forall (X:typvar),
     (lc_ty (ty_var_f X))
 | lc_ty_arrow : forall (T1 T2:ty),
     (lc_ty T1) ->
     (lc_ty T2) ->
     (lc_ty (ty_arrow T1 T2))
 | lc_ty_prod : forall (T1 T2:ty),
     (lc_ty T1) ->
     (lc_ty T2) ->
     (lc_ty (ty_prod T1 T2))
 | lc_ty_all : forall (T:ty),
      ( forall X , lc_ty  ( open_ty_wrt_ty T (ty_var_f X) )  )  ->
     (lc_ty (ty_all T)).

(* defns LC_sexp *)
Inductive lc_sexp : sexp -> Prop :=    (* defn lc_sexp *)
 | lc_sexp_var_f : forall (x:expvar),
     (lc_sexp (sexp_var_f x))
 | lc_sexp_top : 
     (lc_sexp sexp_top)
 | lc_sexp_lit : forall (i5:i),
     (lc_sexp (sexp_lit i5))
 | lc_sexp_abs : forall (ee:sexp),
      ( forall x , lc_sexp  ( open_sexp_wrt_sexp ee (sexp_var_f x) )  )  ->
     (lc_sexp (sexp_abs ee))
 | lc_sexp_app : forall (ee1 ee2:sexp),
     (lc_sexp ee1) ->
     (lc_sexp ee2) ->
     (lc_sexp (sexp_app ee1 ee2))
 | lc_sexp_merge : forall (ee1 ee2:sexp),
     (lc_sexp ee1) ->
     (lc_sexp ee2) ->
     (lc_sexp (sexp_merge ee1 ee2))
 | lc_sexp_tabs : forall (A:sty) (ee:sexp),
     (lc_sty A) ->
      ( forall X , lc_sexp  ( open_sexp_wrt_sty ee (sty_var_f X) )  )  ->
     (lc_sexp (sexp_tabs A ee))
 | lc_sexp_tapp : forall (ee:sexp) (A:sty),
     (lc_sexp ee) ->
     (lc_sty A) ->
     (lc_sexp (sexp_tapp ee A))
 | lc_sexp_anno : forall (ee:sexp) (A:sty),
     (lc_sexp ee) ->
     (lc_sty A) ->
     (lc_sexp (sexp_anno ee A))
 | lc_sexp_rcd : forall (l:i) (ee:sexp),
     (lc_sexp ee) ->
     (lc_sexp (sexp_rcd l ee))
 | lc_sexp_proj : forall (ee:sexp) (l:i),
     (lc_sexp ee) ->
     (lc_sexp (sexp_proj ee l)).

(* defns LC_exp *)
Inductive lc_exp : exp -> Prop :=    (* defn lc_exp *)
 | lc_exp_var_f : forall (x:expvar),
     (lc_exp (exp_var_f x))
 | lc_exp_unit : 
     (lc_exp exp_unit)
 | lc_exp_lit : forall (i5:i),
     (lc_exp (exp_lit i5))
 | lc_exp_abs : forall (e:exp),
      ( forall x , lc_exp  ( open_exp_wrt_exp e (exp_var_f x) )  )  ->
     (lc_exp (exp_abs e))
 | lc_exp_app : forall (e1 e2:exp),
     (lc_exp e1) ->
     (lc_exp e2) ->
     (lc_exp (exp_app e1 e2))
 | lc_exp_pair : forall (e1 e2:exp),
     (lc_exp e1) ->
     (lc_exp e2) ->
     (lc_exp (exp_pair e1 e2))
 | lc_exp_capp : forall (c:co) (e:exp),
     (lc_exp e) ->
     (lc_exp (exp_capp c e))
 | lc_exp_tabs : forall (e:exp),
      ( forall X , lc_exp  ( open_exp_wrt_ty e (ty_var_f X) )  )  ->
     (lc_exp (exp_tabs e))
 | lc_exp_tapp : forall (e:exp) (T:ty),
     (lc_exp e) ->
     (lc_ty T) ->
     (lc_exp (exp_tapp e T)).

(* defns LC_CC *)
Inductive lc_CC : CC -> Prop :=    (* defn lc_CC *)
 | lc_C_Empty : 
     (lc_CC C_Empty)
 | lc_C_Lam : forall (x:expvar) (CC5:CC),
     (lc_CC CC5) ->
     (lc_CC (C_Lam x CC5))
 | lc_C_tabs : forall (X:typvar) (A:sty) (CC5:CC),
     (lc_sty A) ->
     (lc_CC CC5) ->
     (lc_CC (C_tabs X A CC5))
 | lc_C_tapp : forall (CC5:CC) (A:sty),
     (lc_CC CC5) ->
     (lc_sty A) ->
     (lc_CC (C_tapp CC5 A))
 | lc_C_AppL : forall (CC5:CC) (ee:sexp),
     (lc_CC CC5) ->
     (lc_sexp ee) ->
     (lc_CC (C_AppL CC5 ee))
 | lc_C_AppRd : forall (ee:sexp) (CC5:CC),
     (lc_sexp ee) ->
     (lc_CC CC5) ->
     (lc_CC (C_AppRd ee CC5))
 | lc_C_MergeL : forall (CC5:CC) (ee:sexp),
     (lc_CC CC5) ->
     (lc_sexp ee) ->
     (lc_CC (C_MergeL CC5 ee))
 | lc_C_MergeR : forall (ee:sexp) (CC5:CC),
     (lc_sexp ee) ->
     (lc_CC CC5) ->
     (lc_CC (C_MergeR ee CC5))
 | lc_C_Anno : forall (CC5:CC) (A:sty),
     (lc_CC CC5) ->
     (lc_sty A) ->
     (lc_CC (C_Anno CC5 A))
 | lc_C_Rcd : forall (l:i) (CC5:CC),
     (lc_CC CC5) ->
     (lc_CC (C_Rcd l CC5))
 | lc_C_Proj : forall (CC5:CC) (l:i),
     (lc_CC CC5) ->
     (lc_CC (C_Proj CC5 l)).

(* defns LC_cc *)
Inductive lc_cc : cc -> Prop :=    (* defn lc_cc *)
 | lc_cc_empty : 
     (lc_cc cc_empty)
 | lc_cc_lam : forall (x:expvar) (cc5:cc),
     (lc_cc cc5) ->
     (lc_cc (cc_lam x cc5))
 | lc_cc_tabs : forall (X:typvar) (cc5:cc),
     (lc_cc cc5) ->
     (lc_cc (cc_tabs X cc5))
 | lc_cc_tapp : forall (cc5:cc) (T:ty),
     (lc_cc cc5) ->
     (lc_ty T) ->
     (lc_cc (cc_tapp cc5 T))
 | lc_cc_appL : forall (cc5:cc) (e:exp),
     (lc_cc cc5) ->
     (lc_exp e) ->
     (lc_cc (cc_appL cc5 e))
 | lc_cc_appR : forall (e:exp) (cc5:cc),
     (lc_exp e) ->
     (lc_cc cc5) ->
     (lc_cc (cc_appR e cc5))
 | lc_cc_pairL : forall (cc5:cc) (e:exp),
     (lc_cc cc5) ->
     (lc_exp e) ->
     (lc_cc (cc_pairL cc5 e))
 | lc_cc_pairR : forall (e:exp) (cc5:cc),
     (lc_exp e) ->
     (lc_cc cc5) ->
     (lc_cc (cc_pairR e cc5))
 | lc_cc_co : forall (c:co) (cc5:cc),
     (lc_cc cc5) ->
     (lc_cc (cc_co c cc5)).

(* defns LC_qs *)
Inductive lc_qs : qs -> Prop :=    (* defn lc_qs *)
 | lc_qs_arr : forall (A:sty),
     (lc_sty A) ->
     (lc_qs (qs_arr A))
 | lc_qs_all : forall (X:typvar) (A:sty),
     (lc_sty A) ->
     (lc_qs (qs_all X A))
 | lc_qs_rcd : forall (l:i),
     (lc_qs (qs_rcd l)).
(** free variables *)
Fixpoint fv_ty_in_ty (T_5:ty) : vars :=
  match T_5 with
  | ty_nat => {}
  | ty_unit => {}
  | (ty_var_b nat) => {}
  | (ty_var_f X) => {{X}}
  | (ty_arrow T1 T2) => (fv_ty_in_ty T1) \u (fv_ty_in_ty T2)
  | (ty_prod T1 T2) => (fv_ty_in_ty T1) \u (fv_ty_in_ty T2)
  | (ty_all T) => (fv_ty_in_ty T)
end.

Fixpoint fv_sty_in_sty (A5:sty) : vars :=
  match A5 with
  | sty_nat => {}
  | sty_top => {}
  | sty_bot => {}
  | (sty_var_b nat) => {}
  | (sty_var_f X) => {{X}}
  | (sty_arrow A B) => (fv_sty_in_sty A) \u (fv_sty_in_sty B)
  | (sty_and A B) => (fv_sty_in_sty A) \u (fv_sty_in_sty B)
  | (sty_all A B) => (fv_sty_in_sty A) \u (fv_sty_in_sty B)
  | (sty_rcd l A) => (fv_sty_in_sty A)
end.

Fixpoint fv_ty_in_exp (e_5:exp) : vars :=
  match e_5 with
  | (exp_var_b nat) => {}
  | (exp_var_f x) => {}
  | exp_unit => {}
  | (exp_lit i5) => {}
  | (exp_abs e) => (fv_ty_in_exp e)
  | (exp_app e1 e2) => (fv_ty_in_exp e1) \u (fv_ty_in_exp e2)
  | (exp_pair e1 e2) => (fv_ty_in_exp e1) \u (fv_ty_in_exp e2)
  | (exp_capp c e) => (fv_ty_in_exp e)
  | (exp_tabs e) => (fv_ty_in_exp e)
  | (exp_tapp e T) => (fv_ty_in_exp e) \u (fv_ty_in_ty T)
end.

Fixpoint fv_sty_in_sexp (ee_5:sexp) : vars :=
  match ee_5 with
  | (sexp_var_b nat) => {}
  | (sexp_var_f x) => {}
  | sexp_top => {}
  | (sexp_lit i5) => {}
  | (sexp_abs ee) => (fv_sty_in_sexp ee)
  | (sexp_app ee1 ee2) => (fv_sty_in_sexp ee1) \u (fv_sty_in_sexp ee2)
  | (sexp_merge ee1 ee2) => (fv_sty_in_sexp ee1) \u (fv_sty_in_sexp ee2)
  | (sexp_tabs A ee) => (fv_sty_in_sty A) \u (fv_sty_in_sexp ee)
  | (sexp_tapp ee A) => (fv_sty_in_sexp ee) \u (fv_sty_in_sty A)
  | (sexp_anno ee A) => (fv_sty_in_sexp ee) \u (fv_sty_in_sty A)
  | (sexp_rcd l ee) => (fv_sty_in_sexp ee)
  | (sexp_proj ee l) => (fv_sty_in_sexp ee)
end.

Fixpoint fv_sexp_in_sexp (ee_5:sexp) : vars :=
  match ee_5 with
  | (sexp_var_b nat) => {}
  | (sexp_var_f x) => {{x}}
  | sexp_top => {}
  | (sexp_lit i5) => {}
  | (sexp_abs ee) => (fv_sexp_in_sexp ee)
  | (sexp_app ee1 ee2) => (fv_sexp_in_sexp ee1) \u (fv_sexp_in_sexp ee2)
  | (sexp_merge ee1 ee2) => (fv_sexp_in_sexp ee1) \u (fv_sexp_in_sexp ee2)
  | (sexp_tabs A ee) => (fv_sexp_in_sexp ee)
  | (sexp_tapp ee A) => (fv_sexp_in_sexp ee)
  | (sexp_anno ee A) => (fv_sexp_in_sexp ee)
  | (sexp_rcd l ee) => (fv_sexp_in_sexp ee)
  | (sexp_proj ee l) => (fv_sexp_in_sexp ee)
end.

Fixpoint fv_exp_in_exp (e_5:exp) : vars :=
  match e_5 with
  | (exp_var_b nat) => {}
  | (exp_var_f x) => {{x}}
  | exp_unit => {}
  | (exp_lit i5) => {}
  | (exp_abs e) => (fv_exp_in_exp e)
  | (exp_app e1 e2) => (fv_exp_in_exp e1) \u (fv_exp_in_exp e2)
  | (exp_pair e1 e2) => (fv_exp_in_exp e1) \u (fv_exp_in_exp e2)
  | (exp_capp c e) => (fv_exp_in_exp e)
  | (exp_tabs e) => (fv_exp_in_exp e)
  | (exp_tapp e T) => (fv_exp_in_exp e)
end.

Fixpoint fv_ty_in_cc (cc_6:cc) : vars :=
  match cc_6 with
  | cc_empty => {}
  | (cc_lam x cc5) => (fv_ty_in_cc cc5)
  | (cc_tabs X cc5) => (fv_ty_in_cc cc5)
  | (cc_tapp cc5 T) => (fv_ty_in_cc cc5) \u (fv_ty_in_ty T)
  | (cc_appL cc5 e) => (fv_ty_in_cc cc5) \u (fv_ty_in_exp e)
  | (cc_appR e cc5) => (fv_ty_in_exp e) \u (fv_ty_in_cc cc5)
  | (cc_pairL cc5 e) => (fv_ty_in_cc cc5) \u (fv_ty_in_exp e)
  | (cc_pairR e cc5) => (fv_ty_in_exp e) \u (fv_ty_in_cc cc5)
  | (cc_co c cc5) => (fv_ty_in_cc cc5)
end.

Fixpoint fv_sty_in_CC (CC_6:CC) : vars :=
  match CC_6 with
  | C_Empty => {}
  | (C_Lam x CC5) => (fv_sty_in_CC CC5)
  | (C_tabs X A CC5) => (fv_sty_in_sty A) \u (fv_sty_in_CC CC5)
  | (C_tapp CC5 A) => (fv_sty_in_CC CC5) \u (fv_sty_in_sty A)
  | (C_AppL CC5 ee) => (fv_sty_in_CC CC5) \u (fv_sty_in_sexp ee)
  | (C_AppRd ee CC5) => (fv_sty_in_sexp ee) \u (fv_sty_in_CC CC5)
  | (C_MergeL CC5 ee) => (fv_sty_in_CC CC5) \u (fv_sty_in_sexp ee)
  | (C_MergeR ee CC5) => (fv_sty_in_sexp ee) \u (fv_sty_in_CC CC5)
  | (C_Anno CC5 A) => (fv_sty_in_CC CC5) \u (fv_sty_in_sty A)
  | (C_Rcd l CC5) => (fv_sty_in_CC CC5)
  | (C_Proj CC5 l) => (fv_sty_in_CC CC5)
end.

Fixpoint fv_sexp_in_CC (CC_6:CC) : vars :=
  match CC_6 with
  | C_Empty => {}
  | (C_Lam x CC5) => (fv_sexp_in_CC CC5)
  | (C_tabs X A CC5) => (fv_sexp_in_CC CC5)
  | (C_tapp CC5 A) => (fv_sexp_in_CC CC5)
  | (C_AppL CC5 ee) => (fv_sexp_in_CC CC5) \u (fv_sexp_in_sexp ee)
  | (C_AppRd ee CC5) => (fv_sexp_in_sexp ee) \u (fv_sexp_in_CC CC5)
  | (C_MergeL CC5 ee) => (fv_sexp_in_CC CC5) \u (fv_sexp_in_sexp ee)
  | (C_MergeR ee CC5) => (fv_sexp_in_sexp ee) \u (fv_sexp_in_CC CC5)
  | (C_Anno CC5 A) => (fv_sexp_in_CC CC5)
  | (C_Rcd l CC5) => (fv_sexp_in_CC CC5)
  | (C_Proj CC5 l) => (fv_sexp_in_CC CC5)
end.

Definition fv_sty_in_qs (qs5:qs) : vars :=
  match qs5 with
  | (qs_arr A) => (fv_sty_in_sty A)
  | (qs_all X A) => (fv_sty_in_sty A)
  | (qs_rcd l) => {}
end.

Fixpoint fv_exp_in_cc (cc_6:cc) : vars :=
  match cc_6 with
  | cc_empty => {}
  | (cc_lam x cc5) => (fv_exp_in_cc cc5)
  | (cc_tabs X cc5) => (fv_exp_in_cc cc5)
  | (cc_tapp cc5 T) => (fv_exp_in_cc cc5)
  | (cc_appL cc5 e) => (fv_exp_in_cc cc5) \u (fv_exp_in_exp e)
  | (cc_appR e cc5) => (fv_exp_in_exp e) \u (fv_exp_in_cc cc5)
  | (cc_pairL cc5 e) => (fv_exp_in_cc cc5) \u (fv_exp_in_exp e)
  | (cc_pairR e cc5) => (fv_exp_in_exp e) \u (fv_exp_in_cc cc5)
  | (cc_co c cc5) => (fv_exp_in_cc cc5)
end.

(** substitutions *)
Fixpoint subst_ty_in_ty (T_5:ty) (X5:typvar) (T__6:ty) {struct T__6} : ty :=
  match T__6 with
  | ty_nat => ty_nat 
  | ty_unit => ty_unit 
  | (ty_var_b nat) => ty_var_b nat
  | (ty_var_f X) => (if eq_var X X5 then T_5 else (ty_var_f X))
  | (ty_arrow T1 T2) => ty_arrow (subst_ty_in_ty T_5 X5 T1) (subst_ty_in_ty T_5 X5 T2)
  | (ty_prod T1 T2) => ty_prod (subst_ty_in_ty T_5 X5 T1) (subst_ty_in_ty T_5 X5 T2)
  | (ty_all T) => ty_all (subst_ty_in_ty T_5 X5 T)
end.

Fixpoint subst_sty_in_sty (A5:sty) (X5:typvar) (A_6:sty) {struct A_6} : sty :=
  match A_6 with
  | sty_nat => sty_nat 
  | sty_top => sty_top 
  | sty_bot => sty_bot 
  | (sty_var_b nat) => sty_var_b nat
  | (sty_var_f X) => (if eq_var X X5 then A5 else (sty_var_f X))
  | (sty_arrow A B) => sty_arrow (subst_sty_in_sty A5 X5 A) (subst_sty_in_sty A5 X5 B)
  | (sty_and A B) => sty_and (subst_sty_in_sty A5 X5 A) (subst_sty_in_sty A5 X5 B)
  | (sty_all A B) => sty_all (subst_sty_in_sty A5 X5 A) (subst_sty_in_sty A5 X5 B)
  | (sty_rcd l A) => sty_rcd l (subst_sty_in_sty A5 X5 A)
end.

Fixpoint subst_ty_in_exp (T_5:ty) (X5:typvar) (e_5:exp) {struct e_5} : exp :=
  match e_5 with
  | (exp_var_b nat) => exp_var_b nat
  | (exp_var_f x) => exp_var_f x
  | exp_unit => exp_unit 
  | (exp_lit i5) => exp_lit i5
  | (exp_abs e) => exp_abs (subst_ty_in_exp T_5 X5 e)
  | (exp_app e1 e2) => exp_app (subst_ty_in_exp T_5 X5 e1) (subst_ty_in_exp T_5 X5 e2)
  | (exp_pair e1 e2) => exp_pair (subst_ty_in_exp T_5 X5 e1) (subst_ty_in_exp T_5 X5 e2)
  | (exp_capp c e) => exp_capp c (subst_ty_in_exp T_5 X5 e)
  | (exp_tabs e) => exp_tabs (subst_ty_in_exp T_5 X5 e)
  | (exp_tapp e T) => exp_tapp (subst_ty_in_exp T_5 X5 e) (subst_ty_in_ty T_5 X5 T)
end.

Fixpoint subst_sty_in_sexp (A5:sty) (X5:typvar) (ee_5:sexp) {struct ee_5} : sexp :=
  match ee_5 with
  | (sexp_var_b nat) => sexp_var_b nat
  | (sexp_var_f x) => sexp_var_f x
  | sexp_top => sexp_top 
  | (sexp_lit i5) => sexp_lit i5
  | (sexp_abs ee) => sexp_abs (subst_sty_in_sexp A5 X5 ee)
  | (sexp_app ee1 ee2) => sexp_app (subst_sty_in_sexp A5 X5 ee1) (subst_sty_in_sexp A5 X5 ee2)
  | (sexp_merge ee1 ee2) => sexp_merge (subst_sty_in_sexp A5 X5 ee1) (subst_sty_in_sexp A5 X5 ee2)
  | (sexp_tabs A ee) => sexp_tabs (subst_sty_in_sty A5 X5 A) (subst_sty_in_sexp A5 X5 ee)
  | (sexp_tapp ee A) => sexp_tapp (subst_sty_in_sexp A5 X5 ee) (subst_sty_in_sty A5 X5 A)
  | (sexp_anno ee A) => sexp_anno (subst_sty_in_sexp A5 X5 ee) (subst_sty_in_sty A5 X5 A)
  | (sexp_rcd l ee) => sexp_rcd l (subst_sty_in_sexp A5 X5 ee)
  | (sexp_proj ee l) => sexp_proj (subst_sty_in_sexp A5 X5 ee) l
end.

Fixpoint subst_sexp_in_sexp (ee_5:sexp) (x5:expvar) (ee__6:sexp) {struct ee__6} : sexp :=
  match ee__6 with
  | (sexp_var_b nat) => sexp_var_b nat
  | (sexp_var_f x) => (if eq_var x x5 then ee_5 else (sexp_var_f x))
  | sexp_top => sexp_top 
  | (sexp_lit i5) => sexp_lit i5
  | (sexp_abs ee) => sexp_abs (subst_sexp_in_sexp ee_5 x5 ee)
  | (sexp_app ee1 ee2) => sexp_app (subst_sexp_in_sexp ee_5 x5 ee1) (subst_sexp_in_sexp ee_5 x5 ee2)
  | (sexp_merge ee1 ee2) => sexp_merge (subst_sexp_in_sexp ee_5 x5 ee1) (subst_sexp_in_sexp ee_5 x5 ee2)
  | (sexp_tabs A ee) => sexp_tabs A (subst_sexp_in_sexp ee_5 x5 ee)
  | (sexp_tapp ee A) => sexp_tapp (subst_sexp_in_sexp ee_5 x5 ee) A
  | (sexp_anno ee A) => sexp_anno (subst_sexp_in_sexp ee_5 x5 ee) A
  | (sexp_rcd l ee) => sexp_rcd l (subst_sexp_in_sexp ee_5 x5 ee)
  | (sexp_proj ee l) => sexp_proj (subst_sexp_in_sexp ee_5 x5 ee) l
end.

Fixpoint subst_exp_in_exp (e_5:exp) (x5:expvar) (e__6:exp) {struct e__6} : exp :=
  match e__6 with
  | (exp_var_b nat) => exp_var_b nat
  | (exp_var_f x) => (if eq_var x x5 then e_5 else (exp_var_f x))
  | exp_unit => exp_unit 
  | (exp_lit i5) => exp_lit i5
  | (exp_abs e) => exp_abs (subst_exp_in_exp e_5 x5 e)
  | (exp_app e1 e2) => exp_app (subst_exp_in_exp e_5 x5 e1) (subst_exp_in_exp e_5 x5 e2)
  | (exp_pair e1 e2) => exp_pair (subst_exp_in_exp e_5 x5 e1) (subst_exp_in_exp e_5 x5 e2)
  | (exp_capp c e) => exp_capp c (subst_exp_in_exp e_5 x5 e)
  | (exp_tabs e) => exp_tabs (subst_exp_in_exp e_5 x5 e)
  | (exp_tapp e T) => exp_tapp (subst_exp_in_exp e_5 x5 e) T
end.

Fixpoint subst_ty_in_cc (T5:ty) (X5:typvar) (cc_6:cc) {struct cc_6} : cc :=
  match cc_6 with
  | cc_empty => cc_empty 
  | (cc_lam x cc5) => cc_lam x (subst_ty_in_cc T5 X5 cc5)
  | (cc_tabs X cc5) => cc_tabs X (subst_ty_in_cc T5 X5 cc5)
  | (cc_tapp cc5 T) => cc_tapp (subst_ty_in_cc T5 X5 cc5) (subst_ty_in_ty T5 X5 T)
  | (cc_appL cc5 e) => cc_appL (subst_ty_in_cc T5 X5 cc5) (subst_ty_in_exp T5 X5 e)
  | (cc_appR e cc5) => cc_appR (subst_ty_in_exp T5 X5 e) (subst_ty_in_cc T5 X5 cc5)
  | (cc_pairL cc5 e) => cc_pairL (subst_ty_in_cc T5 X5 cc5) (subst_ty_in_exp T5 X5 e)
  | (cc_pairR e cc5) => cc_pairR (subst_ty_in_exp T5 X5 e) (subst_ty_in_cc T5 X5 cc5)
  | (cc_co c cc5) => cc_co c (subst_ty_in_cc T5 X5 cc5)
end.

Fixpoint subst_sty_in_CC (A5:sty) (X5:typvar) (CC_6:CC) {struct CC_6} : CC :=
  match CC_6 with
  | C_Empty => C_Empty 
  | (C_Lam x CC5) => C_Lam x (subst_sty_in_CC A5 X5 CC5)
  | (C_tabs X A CC5) => C_tabs X (subst_sty_in_sty A5 X5 A) (subst_sty_in_CC A5 X5 CC5)
  | (C_tapp CC5 A) => C_tapp (subst_sty_in_CC A5 X5 CC5) (subst_sty_in_sty A5 X5 A)
  | (C_AppL CC5 ee) => C_AppL (subst_sty_in_CC A5 X5 CC5) (subst_sty_in_sexp A5 X5 ee)
  | (C_AppRd ee CC5) => C_AppRd (subst_sty_in_sexp A5 X5 ee) (subst_sty_in_CC A5 X5 CC5)
  | (C_MergeL CC5 ee) => C_MergeL (subst_sty_in_CC A5 X5 CC5) (subst_sty_in_sexp A5 X5 ee)
  | (C_MergeR ee CC5) => C_MergeR (subst_sty_in_sexp A5 X5 ee) (subst_sty_in_CC A5 X5 CC5)
  | (C_Anno CC5 A) => C_Anno (subst_sty_in_CC A5 X5 CC5) (subst_sty_in_sty A5 X5 A)
  | (C_Rcd l CC5) => C_Rcd l (subst_sty_in_CC A5 X5 CC5)
  | (C_Proj CC5 l) => C_Proj (subst_sty_in_CC A5 X5 CC5) l
end.

Fixpoint subst_sexp_in_CC (ee5:sexp) (x5:expvar) (CC_6:CC) {struct CC_6} : CC :=
  match CC_6 with
  | C_Empty => C_Empty 
  | (C_Lam x CC5) => C_Lam x (subst_sexp_in_CC ee5 x5 CC5)
  | (C_tabs X A CC5) => C_tabs X A (subst_sexp_in_CC ee5 x5 CC5)
  | (C_tapp CC5 A) => C_tapp (subst_sexp_in_CC ee5 x5 CC5) A
  | (C_AppL CC5 ee) => C_AppL (subst_sexp_in_CC ee5 x5 CC5) (subst_sexp_in_sexp ee5 x5 ee)
  | (C_AppRd ee CC5) => C_AppRd (subst_sexp_in_sexp ee5 x5 ee) (subst_sexp_in_CC ee5 x5 CC5)
  | (C_MergeL CC5 ee) => C_MergeL (subst_sexp_in_CC ee5 x5 CC5) (subst_sexp_in_sexp ee5 x5 ee)
  | (C_MergeR ee CC5) => C_MergeR (subst_sexp_in_sexp ee5 x5 ee) (subst_sexp_in_CC ee5 x5 CC5)
  | (C_Anno CC5 A) => C_Anno (subst_sexp_in_CC ee5 x5 CC5) A
  | (C_Rcd l CC5) => C_Rcd l (subst_sexp_in_CC ee5 x5 CC5)
  | (C_Proj CC5 l) => C_Proj (subst_sexp_in_CC ee5 x5 CC5) l
end.

Definition subst_sty_in_qs (A5:sty) (X5:typvar) (qs5:qs) : qs :=
  match qs5 with
  | (qs_arr A) => qs_arr (subst_sty_in_sty A5 X5 A)
  | (qs_all X A) => qs_all X (subst_sty_in_sty A5 X5 A)
  | (qs_rcd l) => qs_rcd l
end.

Fixpoint subst_exp_in_cc (e5:exp) (x5:expvar) (cc_6:cc) {struct cc_6} : cc :=
  match cc_6 with
  | cc_empty => cc_empty 
  | (cc_lam x cc5) => cc_lam x (subst_exp_in_cc e5 x5 cc5)
  | (cc_tabs X cc5) => cc_tabs X (subst_exp_in_cc e5 x5 cc5)
  | (cc_tapp cc5 T) => cc_tapp (subst_exp_in_cc e5 x5 cc5) T
  | (cc_appL cc5 e) => cc_appL (subst_exp_in_cc e5 x5 cc5) (subst_exp_in_exp e5 x5 e)
  | (cc_appR e cc5) => cc_appR (subst_exp_in_exp e5 x5 e) (subst_exp_in_cc e5 x5 cc5)
  | (cc_pairL cc5 e) => cc_pairL (subst_exp_in_cc e5 x5 cc5) (subst_exp_in_exp e5 x5 e)
  | (cc_pairR e cc5) => cc_pairR (subst_exp_in_exp e5 x5 e) (subst_exp_in_cc e5 x5 cc5)
  | (cc_co c cc5) => cc_co c (subst_exp_in_cc e5 x5 cc5)
end.



(** infrastructure *)
Hint Constructors lc_sty lc_ty lc_sexp lc_exp lc_CC lc_cc lc_qs.
