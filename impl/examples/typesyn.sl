--> 3.0

type AType = forall A . A -> A;

aid : AType = /\ A . (\x -> x) : A -> A;

main = aid Double 3
