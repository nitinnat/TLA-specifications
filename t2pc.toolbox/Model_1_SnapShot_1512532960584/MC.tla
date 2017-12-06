---- MODULE MC ----
EXTENDS t2pc, TLC

\* CONSTANT definitions @modelParameterConstants:0RMMAYFAIL
const_15125329555052459000 == 
TRUE
----

\* CONSTANT definitions @modelParameterConstants:1TMMAYFAIL
const_15125329555052460000 == 
FALSE
----

\* CONSTANT definitions @modelParameterConstants:2BTMENABLE
const_15125329555052461000 == 
TRUE
----

\* CONSTANT definitions @modelParameterConstants:3RM
const_15125329555052462000 == 
{1,2,3}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_15125329555052463000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_15125329555052464000 ==
Consistent
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_15125329555052465000 ==
Termination
----
=============================================================================
\* Modification History
\* Created Tue Dec 05 23:02:35 EST 2017 by Nitin
