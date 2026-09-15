// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._



@pure def orComm(p: B, q: B): Unit = {
    Deduce(
        (p | q) |- (q | p)
        Proof(
            //PROOF GOES HERE
            1 ( p | q )     by Premise,
            2 SubProof(  
            //case where p is true
            //show that q | p is true
                3 Assume ( p ),
                4 ( q | p ) by OrI2(3)
            ),
            5 SubProof(
                6 Assume ( q ),
                7 ( q | p ) by OrI1(6)
            ),
            //claim by common conclusion
            //OrE line numbers:
                //OrE (OriginalOr, )
            8 ( q | p ) by OrE(1, 2, 5)

            //use OrE subproofs
            //case where q is true
                //show that q | p is true
        )
    )
}