--> "(-2.0 + 3.0) = 1.0"

-- BEGIN_ALGEBRA_DEF
type ExpAlg[E] = { lit : Double -> E, add : E -> E -> E };
type IEval = { eval : Double };
trait evalAlg => {
  lit (x : Double)            = { eval = x };
  add (x : IEval) (y : IEval) = { eval = x.eval + y.eval } };
-- END_ALGEBRA_DEF


-- BEGIN_PRINT_DEF
type IPrint = { print : String };
trait printAlg => {
  lit (x : Double)              = { print = x.toString };
  add (x : IPrint) (y : IPrint) = {
    print = "(" ++ x.print ++ " + " ++ y.print ++ ")" } };
-- END_PRINT_DEF


-- BEGIN_SUB_DEF
type ExpExtAlg[E] = ExpAlg[E] & { neg : E -> E };
trait negEvalAlg  inherits evalAlg => {
  neg (x : IEval) = { eval = 0 - x.eval } };
-- END_SUB_DEF

-- BEGIN_CLOSE
trait expExtAlg  inherits negEvalAlg & printAlg => {
  neg (x : IPrint) = { print= "-" ++ x.print }
} : ExpExtAlg[IEval & IPrint];
-- END_CLOSE

type Exp = { accept : forall E . ExpAlg[E] -> E };
type ExtExp = { accept: forall E. ExpExtAlg[E] -> E };

e1 : Exp = { accept E f = f.add (f.lit 2) (f.lit 3) };
e2 : ExtExp = { accept E f = f.neg (e1.accept E f) };
e3 : ExtExp = { accept E f = f.add (e2.accept E f) (f.lit 3) };


-- BEGIN_USE
fac = new[ExpExtAlg[IEval & IPrint]] expExtAlg;
e = fac.add (fac.neg (fac.lit 2)) (fac.lit 3);
main = e.print ++ " = " ++ e.eval.toString -- "(-2.0 + 3.0) = 1.0"
-- END_USE
