------------ MODULE RiverMC --------------
CONSTANTS
    MISSIONARIES, 
    CANNIBALS,
    CAPACITY

VARIABLES 
  right,
  left

vars == { right, end }

Amount == (MISSIONARIES :> 3 @@ CANNIBALS :> 3)
People == DOMAIN Amount


\* Note: while formatting put TypeOk near variables

\* Note: while formatting put TypeOk near variables
TypeOK ==
    /\ right <= MAX_CAPACITY
    /\ left <= MAX_CAPACITY
    /\ \A p \in People : (right[p] = 0) \/ (right[p] >= left[p])

CanSee ==
\* amount of cannibals on either side is never greater than missionaries
    /\ \/ (right[MISSIONARIES] = 0) \/ (right[MISSIONARIES] >= right[CANNIBALS])
       \/ (left[MISSIONARIES] = 0) \/ (left[MISSIONARIES] >= left[CANNIBALS])

OneCrosses(here, there) ==
       \E a \in People \ {Flashlight} :
           /\ here' = [p \in People |-> IF p = a THEN here[p] - 1 ELSE here[p]]
           /\ there' = [p \in People |-> IF p = a THEN there[p] + 1 ELSE there[p]]
           /\ CanSee
   
TwoCross(here, there) ==
    \E a, b \in People \ {Flashlight} :
        /\ here' = [p \in People |-> IF (p = a) \/ (p = b) THEN here[p] - 1 ELSE here[p]]
           /\ there' = [p \in People |-> IF (p = a) \/ (p = b) THEN there[p] + 1 ELSE there[p]]
           /\ CanSee

Init == 
    /\ right = People
    /\ left = {}

\*Final == \A a \in vars : a = end
Final == left = 6

Solved == Final
Unsolved == ~ Solved 
=============================================================================