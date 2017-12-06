----------------------------- MODULE t2pc -----------------------------

EXTENDS Integers, Sequences, FiniteSets, TLC
CONSTANT RM,       \* The set of participating resource managers
         RMMAYFAIL,
         TMMAYFAIL,
         BTMENABLE  \*TRUE when backup is needed, FALSE otherwise. Used to check problem 1.1
(*
--algorithm TransactionCommit {
  variable rmState = [rm \in RM |-> "working"], \*initially all RMs are working
           tmState = "init"; \* TM is in "init" state initially
           btmState = "init"; \* BTM is also ready to take over if TM fails.
   
  define {
    \* The TM or BTM can only commit when rmState is prepared, committed or failed.
    canCommit ==  \A rm \in RM : rmState[rm] \in {"prepared", "committed","failed"} 
                
    \* The TM or BTM can only abort when no other RM is committed.
    canAbort ==  \A rm \in RM : rmState[rm] # "committed"  \* TM can abort when no RM is in committed state
                   
    
   }
  macro Prepare(p) 
  { 
        
        await rmState[p] \in {"working","prepared"};
        rmState[p] := "prepared";
       
  }
   
  macro Decide(p) 
  {
  
 if (tmState # "hidden") \*If TM state is not hidden then execute this
       {
            either 
                { 
                    when  tmState = "commit" ;
                    if (rmState[p] = "prepared") rmState[p] := "committed"
             
                }
            or     
                { 
                    when tmState = "abort";
                    if (rmState[p] \in {"prepared", "working"}) rmState[p] := "aborted"
                }  
            or     
                { 
                
                    when rmState[p] = "working";
                    rmState[p] := "aborted"
                }
        } 
 else                       \*If TM state is hidden then check for BTM state.
       {
          if (BTMENABLE)
          {  
            either 
                { 
                    when  btmState = "commit" ;
                    
                    if (rmState[p] = "prepared") rmState[p] := "committed"
             
                }
            or     
                { \*When BTM state is "abort", then RM state goes to "aborted"
                    when btmState = "abort";
                    if (rmState[p] \in {"prepared", "working"}) rmState[p] := "aborted"
                }  
            or     
                { \*RM can spontaneously abort when it's in the working state.
                    when rmState[p] = "working";
                    rmState[p] := "aborted"
                }
            }
        }
                 
         
         
         
  }
   macro Fail(p) 
    {
        if (RMMAYFAIL) 
        {
             rmState[p] := "failed"
        }
    }
  
  
  fair process (RManager \in RM) 
  {
      start: while (rmState[self] \in {"working", "prepared"}) { 
      either Prepare(self) or Decide(self) or Fail(self)}
   }

 fair process (TManager = 0) 
  {
  
  
  
  
  
  
        TS: either 
            {
                await canCommit;
                TC: if (tmState # "hidden" /\  canCommit ) {tmState := "commit"};
                    
                F1: if (TMMAYFAIL) 
                        {
                            \* Change the tmState to hidden only if it's not already hidden (does not really matter)
                            if (tmState # "hidden") {
                            
                            \*Transfer the TM's state to BTM before going to hidden.
                            if (BTMENABLE) btmState := tmState;
                            tmState := "hidden";
                            
                            }
                           
                        }
            }
                    
            or 
            {
                await canAbort;
                TA: if (tmState # "hidden" /\ canAbort) {tmState := "abort"};
                    
            
                F2: if (TMMAYFAIL) 
                        {
                            if (tmState # "hidden") 
                            {
                                \*Transfer BTM state to TM
                                if (BTMENABLE) btmState := tmState;
                                tmState := "hidden"; \*TM fails
                                
                                
                            }
                    
                
                        }
            }
 
    }
    
    
    
  fair process(BTManager = 10)
  
  {
    BTS: either 
                {
                    await canCommit;
                    
                    \*BTM can commit only when BTM is enabled by the user, tmState is hidden and canCommit is true
                    BTC:  if (tmState = "hidden" /\ BTMENABLE /\ canCommit ) 
                    {
                        print <<"committing when rmstate is", rmState>>;
                        btmState := "commit";
                    }
                }
                    
                or 
                {
                    await canAbort;
                    BTA: if (tmState = "hidden" /\ BTMENABLE /\ canAbort) 
                     {
                     
                     btmState := "abort";
                     
                     }
                }
  
  }
}
*)
\* BEGIN TRANSLATION
VARIABLES rmState, tmState, btmState, pc

(* define statement *)
canCommit ==  \A rm \in RM : rmState[rm] \in {"prepared", "committed","failed"}


canAbort ==  \A rm \in RM : rmState[rm] # "committed"


vars == << rmState, tmState, btmState, pc >>

ProcSet == (RM) \cup {0} \cup {10}

Init == (* Global variables *)
        /\ rmState = [rm \in RM |-> "working"]
        /\ tmState = "init"
        /\ btmState = "init"
        /\ pc = [self \in ProcSet |-> CASE self \in RM -> "start"
                                        [] self = 0 -> "TS"
                                        [] self = 10 -> "BTS"]

start(self) == /\ pc[self] = "start"
               /\ IF rmState[self] \in {"working", "prepared"}
                     THEN /\ \/ /\ rmState[self] \in {"working","prepared"}
                                /\ rmState' = [rmState EXCEPT ![self] = "prepared"]
                             \/ /\ IF tmState # "hidden"
                                      THEN /\ \/ /\ tmState = "commit"
                                                 /\ IF rmState[self] = "prepared"
                                                       THEN /\ rmState' = [rmState EXCEPT ![self] = "committed"]
                                                       ELSE /\ TRUE
                                                            /\ UNCHANGED rmState
                                              \/ /\ tmState = "abort"
                                                 /\ IF rmState[self] \in {"prepared", "working"}
                                                       THEN /\ rmState' = [rmState EXCEPT ![self] = "aborted"]
                                                       ELSE /\ TRUE
                                                            /\ UNCHANGED rmState
                                              \/ /\ rmState[self] = "working"
                                                 /\ rmState' = [rmState EXCEPT ![self] = "aborted"]
                                      ELSE /\ IF BTMENABLE
                                                 THEN /\ \/ /\ btmState = "commit"
                                                            /\ IF rmState[self] = "prepared"
                                                                  THEN /\ rmState' = [rmState EXCEPT ![self] = "committed"]
                                                                  ELSE /\ TRUE
                                                                       /\ UNCHANGED rmState
                                                         \/ /\ btmState = "abort"
                                                            /\ IF rmState[self] \in {"prepared", "working"}
                                                                  THEN /\ rmState' = [rmState EXCEPT ![self] = "aborted"]
                                                                  ELSE /\ TRUE
                                                                       /\ UNCHANGED rmState
                                                         \/ /\ rmState[self] = "working"
                                                            /\ rmState' = [rmState EXCEPT ![self] = "aborted"]
                                                 ELSE /\ TRUE
                                                      /\ UNCHANGED rmState
                             \/ /\ IF RMMAYFAIL
                                      THEN /\ rmState' = [rmState EXCEPT ![self] = "failed"]
                                      ELSE /\ TRUE
                                           /\ UNCHANGED rmState
                          /\ pc' = [pc EXCEPT ![self] = "start"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                          /\ UNCHANGED rmState
               /\ UNCHANGED << tmState, btmState >>

RManager(self) == start(self)

TS == /\ pc[0] = "TS"
      /\ \/ /\ canCommit
            /\ pc' = [pc EXCEPT ![0] = "TC"]
         \/ /\ canAbort
            /\ pc' = [pc EXCEPT ![0] = "TA"]
      /\ UNCHANGED << rmState, tmState, btmState >>

TC == /\ pc[0] = "TC"
      /\ IF tmState # "hidden" /\  canCommit
            THEN /\ tmState' = "commit"
            ELSE /\ TRUE
                 /\ UNCHANGED tmState
      /\ pc' = [pc EXCEPT ![0] = "F1"]
      /\ UNCHANGED << rmState, btmState >>

F1 == /\ pc[0] = "F1"
      /\ IF TMMAYFAIL
            THEN /\ IF tmState # "hidden"
                       THEN /\ IF BTMENABLE
                                  THEN /\ btmState' = tmState
                                  ELSE /\ TRUE
                                       /\ UNCHANGED btmState
                            /\ tmState' = "hidden"
                       ELSE /\ TRUE
                            /\ UNCHANGED << tmState, btmState >>
            ELSE /\ TRUE
                 /\ UNCHANGED << tmState, btmState >>
      /\ pc' = [pc EXCEPT ![0] = "Done"]
      /\ UNCHANGED rmState

TA == /\ pc[0] = "TA"
      /\ IF tmState # "hidden" /\ canAbort
            THEN /\ tmState' = "abort"
            ELSE /\ TRUE
                 /\ UNCHANGED tmState
      /\ pc' = [pc EXCEPT ![0] = "F2"]
      /\ UNCHANGED << rmState, btmState >>

F2 == /\ pc[0] = "F2"
      /\ IF TMMAYFAIL
            THEN /\ IF tmState # "hidden"
                       THEN /\ IF BTMENABLE
                                  THEN /\ btmState' = tmState
                                  ELSE /\ TRUE
                                       /\ UNCHANGED btmState
                            /\ tmState' = "hidden"
                       ELSE /\ TRUE
                            /\ UNCHANGED << tmState, btmState >>
            ELSE /\ TRUE
                 /\ UNCHANGED << tmState, btmState >>
      /\ pc' = [pc EXCEPT ![0] = "Done"]
      /\ UNCHANGED rmState

TManager == TS \/ TC \/ F1 \/ TA \/ F2

BTS == /\ pc[10] = "BTS"
       /\ \/ /\ canCommit
             /\ pc' = [pc EXCEPT ![10] = "BTC"]
          \/ /\ canAbort
             /\ pc' = [pc EXCEPT ![10] = "BTA"]
       /\ UNCHANGED << rmState, tmState, btmState >>

BTC == /\ pc[10] = "BTC"
       /\ IF tmState = "hidden" /\ BTMENABLE /\ canCommit
             THEN /\ PrintT(<<"committing when rmstate is", rmState>>)
                  /\ btmState' = "commit"
             ELSE /\ TRUE
                  /\ UNCHANGED btmState
       /\ pc' = [pc EXCEPT ![10] = "Done"]
       /\ UNCHANGED << rmState, tmState >>

BTA == /\ pc[10] = "BTA"
       /\ IF tmState = "hidden" /\ BTMENABLE /\ canAbort
             THEN /\ btmState' = "abort"
             ELSE /\ TRUE
                  /\ UNCHANGED btmState
       /\ pc' = [pc EXCEPT ![10] = "Done"]
       /\ UNCHANGED << rmState, tmState >>

BTManager == BTS \/ BTC \/ BTA

Next == TManager \/ BTManager
           \/ (\E self \in RM: RManager(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in RM : WF_vars(RManager(self))
        /\ WF_vars(TManager)
        /\ WF_vars(BTManager)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION


 \*Consistency property for RMs. Two RMs cannot be in aborted and committed state simultaneously.
ConsistentRM ==  
  (*************************************************************************)
  (* A state predicate asserting that two RMs have not arrived at          *)
  (* conflicting decisions.                                                *)
  (*************************************************************************)
  \A rm1, rm2 \in RM : ~ /\ rmState[rm1] = "aborted"
                         /\ rmState[rm2] = "committed"
                         
   
   \*When the TM is active, then this needs to be satisfied for consistency                      
  ConsistentTM == ((~ tmState = "hidden") /\ (\A rm \in RM : ~ /\ rmState[rm] = "committed" /\ tmState = "abort"))
                    \/ (tmState = "hidden" /\ (~BTMENABLE) )
                      
   \*When TM is not active, i.e. in hidden state, then this property needs to be satisfied.                  
 ConsistentBTM ==  (BTMENABLE /\ tmState = "hidden") /\ (\A rm \in RM : ~ /\ rmState[rm] = "committed" /\ btmState = "abort")  

\*This will be the overall consistent property taking into account the RMs, TM and BTM.
  Consistent == ConsistentRM /\ (ConsistentTM \/ ConsistentBTM)
  

====================================================================
1.1 When RMMAYFAIL and TMMAYFAIL are both false, then the program runs with no errors.
When RMMAYFAIL is true and TMMAYFAIL is false, the program still runs with no errors.
This is correct because even though some RMs fail, the TM will look if other RMs have all committed or aborted.

1.2 When RMMAYFAIL is false and TMMAYFAIL is true, the temporal property is violated, i.e. Termination is not satisfied.
On examining the stack trace, we see that when a state of <prepared, aborted, aborted> is reached and the TM fails (becomes
hidden), the state does not change for a few more iterations. This is because there is no transaction manager to handle the 
RM requests. Since there is no way this state will change, it violates the termination property.

1.3 When both TM and RM are allowed to fail, and the BTM is enabled, then the program reaches
termination and also does not violate consistency.




