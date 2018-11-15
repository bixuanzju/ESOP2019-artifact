--> "I am a duck, I can fly, I can swim"


type Swimming = { swim : String };
trait swimming  => {
  swim = "I can swim"
};


type Flying = { fly : String };
trait flying  => {
  fly = "I can fly"
};

type Bird = { name : String };
trait duck  inherits swimming & flying => {
  name = "I am a duck"
};

superDuck = new[Swimming & Flying & Bird] duck;
main = superDuck.name ++ ", " ++ superDuck.fly ++ ", " ++ superDuck.swim
