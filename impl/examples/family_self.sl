--> "2.0 + 3.0 and 5 + 4 = 9.0"

type ExpAlg[E] = {
  lit : Double -> E,
  add : E -> E -> E
};

type Exp = { accept : forall E . ExpAlg[E] -> E };

type IEval = { eval : Double };
type IPrint = { print : String };


trait evalAlg  => {
  lit (x : Double)   = { eval = x };
  add (x : IEval) (y : IEval) = { eval = x.eval + y.eval }
} : ExpAlg[IEval];


e1 : Exp = { accept = /\E . \f -> f.add (f.lit 2) (f.lit 3) };


-- Family self reference
trait printAlg3 [fself : ExpAlg[IEval & IPrint]] =>  {
  lit (x : Double)  = { print = x.toString };
  add (e1 : IPrint) (e2 : IPrint) = {print =
    let plus54 = fself.add (fself.lit 5) (fself.lit 4)
    in e1.print ++ " + " ++ e2.print ++ " and " ++ "5 + 4 = " ++ plus54.eval.toString
  }
} : ExpAlg[IPrint];

trait evalAlg2  => {
  lit (x : Double) = { eval = x + 1 };
  add (x : IEval) (y : IEval) = { eval = x.eval + y.eval }
} : ExpAlg[IEval];

o = new[ExpAlg[IEval & IPrint]] evalAlg & printAlg3;

main = (e1.accept (IEval & IPrint) o).print
