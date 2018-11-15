--> 24.0

fact (n : Double) : Double = if n == 0 then 1 else n * fact (n - 1)

main = fact 4
