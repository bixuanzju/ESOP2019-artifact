--> 4.0

type A = {m : Double, n : Double};

trait genA [self : A] => {
  m = 1;
  n = self.m + 1
};

trait genB [self : A] => {
  m = 2;
  n = self.m + 2
};


trait gen1 [self : A] inherits genA \ {m : Double} & genB \ {n : Double} => {
  override m = super.m + 1
} ;


trait gen2 [self : A] inherits genA \ {m : Double} & genB \ {n : Double} => {
  override m = (genA ^ self).m + 1
} ;


o1 = new[A] gen1;

o2 = new[A] gen2;

main = o1.n -- 4
