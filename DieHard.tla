------------------------------- MODULE DieHard -------------------------------
EXTENDS Integers

VARIABLES small, big 

TypesOk == 
  /\ small \in 0..3 
  /\ big \in 0..5

BigIsNotFour == 
  /\ big /= 4

Init ==
  /\ small = 0
  /\ big = 0

FillSmall ==
  /\ small' = 3
  /\ big' = big

FillBig ==
  /\ small' = small
  /\ big' = 5

EmptySmall ==
  /\ small' = 0
  /\ big' = big

EmptyBig ==
  /\ small' = small
  /\ big' = 0

SmallToBig ==
    IF small + big <= 5
    THEN
      /\ small' = 0
      /\ big' = small + big
    ELSE
      /\ small' = small + big - 5
      /\ big' = 5

BigToSmall ==
  IF small + big >= 3
  THEN
      /\ small' = 3
      /\ big' = small + big - 3
  ELSE
      /\ small' = small + big
      /\ big' = 0

Next ==
    \/ FillSmall
    \/ FillBig
    \/ EmptySmall
    \/ EmptyBig
    \/ SmallToBig
    \/ BigToSmall

Spec == Init /\ [][Next]_<<small, big>>

=============================================================================