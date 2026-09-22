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
<<<<<<< HEAD
            2 SubProof(  
            //case where p is true
            //show that q | p is true
=======

            //use OrE subproofs

            //case where p is true
            //show that q | p is true
            2 SubProof(
>>>>>>> 108a64175c761c1625003f7d155f89809e475965
                3 Assume ( p ),
                4 ( q | p ) by OrI2(3)
            ),
            5 SubProof(
                6 Assume ( q ),
                7 ( q | p ) by OrI1(6)
            ),
<<<<<<< HEAD
            //claim by common conclusion
            //OrE line numbers:
                //OrE (OriginalOr, )
            8 ( q | p ) by OrE(1, 2, 5)

            //use OrE subproofs
=======
            //claim my common conclusion
            //OrE line numbers:
                //OrE(originalOr, )
            8 ( q | p ) by OrE(1, 2, 5)
            
>>>>>>> 108a64175c761c1625003f7d155f89809e475965
            //case where q is true
                //show that q | p is true
        )
    )
}