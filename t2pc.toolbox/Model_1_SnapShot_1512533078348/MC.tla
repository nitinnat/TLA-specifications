---- MODULE MC ----
EXTENDS t2pc, TLC

\* CONSTANT definitions @modelParameterConstants:0RMMAYFAIL
const_15125330732692487000 == 
TRUE
----

\* CONSTANT definitions @modelParameterConstants:1TMMAYFAIL
const_15125330732692488000 == 
TRUE
----

\* CONSTANT definitions @modelParameterConstants:2BTMENABLE
const_15125330732692489000 == 
TRUE
----

\* CONSTANT definitions @modelParameterConstants:3RM
const_15125330732692490000 == 
{1,2,3}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_15125330732692491000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_15125330732692492000 ==
Consistent
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_15125330732692493000 ==
Termination
----
=============================================================================
\* Modification History
\* Created Tue Dec 05 23:04:33 EST 2017 by Nitin
