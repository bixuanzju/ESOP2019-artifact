--> true


{-

An example where we show two mutually dependent traits

-}


type EvenOdd = {
  isEven : Double -> Bool,
  isOdd  : Double -> Bool };
trait even [self : EvenOdd] => {
  isEven(n : Double)  = if n == 0 then true else self.isOdd(n - 1) };
trait odd [self : EvenOdd] => {
  isOdd(n : Double)   = if n == 0 then false else self.isEven(n - 1) };
main = (new[EvenOdd] even & odd).isEven(42) -- Output: true
