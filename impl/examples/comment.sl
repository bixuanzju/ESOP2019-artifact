--> "Have fun!4.0"

type Comment = { content : String };
comment (content : String) = trait [self : Comment] => {
  content = content
};


type Up = { upvotes : Double };
up (upvotes : Double) = trait  [self : Up] => {
  upvotes = upvotes
};

test = new[Comment & Up] comment("Have fun!") & up(4);
main = test.content ++ (test.upvotes).toString
