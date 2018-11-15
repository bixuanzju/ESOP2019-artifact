
Require Import Syntax_ott.
Require Import TypeSystems.
Require Import Algorithm.
Require Import Metalib.Metatheory.

(* ********************************************************************** *)
(** * Well-known properties of System F *)

Definition halts t  :=
  exists t',  value t' /\ t ->* t'.

Axiom normalization : forall t T,
    typ nil nil t T ->
    halts t.

Axiom ty_absurd : forall e,
    typ nil nil e (ty_all (ty_var_b 0)) -> False.


(* ********************************************************************** *)
(** * Hairy Renaming due to locally-nameless encoding *)

Axiom asub_rename : forall X Y Q A B C c,
    asub A (Q ++ [qs_all X C]) (open_sty_wrt_sty B (sty_var_f X)) c ->
    X `notin` fv_sty_in_sty B \u fv_sty_in_sty A ->
    Y `notin` fv_sty_in_sty B \u fv_sty_in_sty A  ->
    wf_fs Q ->
    asub A (Q ++ [qs_all Y C]) (open_sty_wrt_sty B (sty_var_f Y)) c.
