module Greek

import Syntax

data Cat = N | D | V | P
data Lex : Ty -> Type where
  εἰς        : Lex (D ~> P)
  τοσοῦτον   : Lex (N ~> D)
  ἥκομεν     : Lex (P ~> V)
  ἐλευθερίας : Lex (C N)

sentence : Expr (C V)
sentence = εἰς .> τοσοῦτον <. ἥκομεν |> ἐλευθερίας

testeval : (| sentence |) = L' ἥκομεν (L' εἰς (L' τοσοῦτον (L' ἐλευθερίας)))
testeval = refl
