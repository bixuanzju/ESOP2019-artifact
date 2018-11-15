--> 3.0

type IdType [B] = B -> B;

id : IdType [Double] = \x -> x;

main = id 3
