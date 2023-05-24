------------------------ MODULE euclid ----------------------------
EXTENDS Naturals, TLC
CONSTANT Num1 \* First Number
CONSTANT N \* Max second Number


(*
--algorithm Euclid {
  variables value1 = Num1; 
            value2 \in 1 .. N; 
            value2_init = value2;
  {
    while (value1 # 0) {
      if (value1 < value2) {
          value1 := value2 || value2 := value1;
      };
      value1 := value1 - value2;
    };
    print <<Num1, value2_init, "have gcd", value2>>
  }
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "4d620d94" /\ chksum(tla) = "5c4689b1")
VARIABLES value1, value2, value2_init, pc

vars == << value1, value2, value2_init, pc >>

Init == (* Global variables *)
        /\ value1 = Num1
        /\ value2 \in 1 .. N
        /\ value2_init = value2
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF value1 # 0
               THEN /\ IF value1 < value2
                          THEN /\ /\ value1' = value2
                                  /\ value2' = value1
                          ELSE /\ TRUE
                               /\ UNCHANGED << value1, value2 >>
                    /\ pc' = "Lbl_2"
               ELSE /\ PrintT(<<Num1, value2_init, "have gcd", value2>>)
                    /\ pc' = "Done"
                    /\ UNCHANGED << value1, value2 >>
         /\ UNCHANGED value2_init

Lbl_2 == /\ pc = "Lbl_2"
         /\ value1' = value1 - value2
         /\ pc' = "Lbl_1"
         /\ UNCHANGED << value2, value2_init >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1 \/ Lbl_2
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
======
