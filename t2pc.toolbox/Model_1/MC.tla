---- MODULE MC ----
EXTENDS t2pc, TLC

\* CONSTANT definitions @modelParameterConstants:0RMMAYFAIL
const_15125333179022501000 == 
FALSE
----

\* CONSTANT definitions @modelParameterConstants:1TMMAYFAIL
const_15125333179022502000 == 
TRUE
----

\* CONSTANT definitions @modelParameterConstants:2BTMENABLE
const_15125333179022503000 == 
FALSE
----

\* CONSTANT definitions @modelParameterConstants:3RM
const_15125333179022504000 == 
{1,2,3}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_15125333179022505000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_15125333179022506000 ==
Consistent
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_15125333179022507000 ==
Termination
----
=============================================================================
\* Modification History
\* Created Tue Dec 05 23:08:37 EST 2017 by Nitin
