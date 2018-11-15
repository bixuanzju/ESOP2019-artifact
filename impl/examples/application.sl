--> "-(2.0 + 3.0) = -5.0"

-- BEGIN_ALGEBRA_DEF
type ExpAlg[E] = { lit : Int -> E, add : E -> E -> E };
type IEval = { eval : Int };
trait evalAlg => {
  lit (x : Int) = { eval = x };
  add (x : IEval) (y : IEval) = { eval = x.eval + y.eval }
};
-- END_ALGEBRA_DEF

-- BEGIN_EXP_TYPE
type Exp = { accept : forall E . ExpAlg[E] -> E };
-- END_EXP_TYPE

-- BEGIN_VALUE_E1
e1 : Exp = { accept E f = f.add (f.lit 2) (f.lit 3) };
-- END_VALUE_E1


-- BEGIN_PRINT_DEF
type IPrint = { print : String };
trait printAlg => {
  lit (x : Int) = { print = x.toString };
  add (x : IPrint) (y : IPrint) = {
    print = "(" ++ x.print ++ " + " ++ y.print ++ ")"
  }
};
-- END_PRINT_DEF


-- BEGIN_SUB_DEF
type ExpExtAlg[E] = ExpAlg[E] & { neg : E -> E };
trait negEvalAlg inherits evalAlg => {
  neg (x : IEval) = { eval = 0 - x.eval }
};
trait negPrintAlg inherits printAlg => {
  neg (x : IPrint) = { print= "-" ++ x.print }
};
-- END_SUB_DEF


-- BEGIN_EXPEXT_TYPE
type ExtExp = { accept: forall E. ExpExtAlg[E] -> E };
-- END_EXPEXT_TYPE


-- BEGIN_VALUE_E2
e2 : ExtExp = { accept E f = f.neg (e1.accept E f) };
-- END_VALUE_E2


-- BEGIN_COMBINE
combine A [B * A] (f : Trait[ExpExtAlg[A]]) (g : Trait[ExpExtAlg[B]]) =
  trait inherits f & g => {};
-- END_COMBINE

-- BEGIN_NEW_ALG
combinedAlg = combine IEval IPrint negEvalAlg negPrintAlg;
-- END_NEW_ALG




-- BEGIN_CLOSE
trait expExtAlg  inherits negEvalAlg & printAlg => {
  neg (x : IPrint) = { print= "-" ++ x.print }
} : ExpExtAlg[IEval & IPrint];
-- END_CLOSE

-- BEGIN_USE
o = e2.accept (IEval & IPrint) (new[ExpExtAlg[IEval & IPrint]] combinedAlg);
main = o.print ++ " = " ++ o.eval.toString -- "-(2.0 + 3.0) = -5.0"
-- END_USE
