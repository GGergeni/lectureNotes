// #Sireum #Logika
//@Logika: --manual

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

//want to return x * y, through repeated addition
//recursively compute x + x + ... + x (y times)
def mult(x: Z, y: Z): Z = {
  //what goes here?
  //what should we require?
  //what should we ensure?

  Contract(
    Requires( y >=  0),
    Ensures( Res[Z] == x*y )
  )

  var answer: Z = 0

  if (y == 0) {
    answer = 0

    Deduce(
      1 (y == 0) by Premise, //if condition is true
      2 (answer == 0) by Premise, //from assignment
      3 ( y >= 0) by Premise, // from precondition (not needed here)
      4 ( answer == x*y ) by Algebra*(1,2) //proves postcondition 
    )

    //what do we need to do here?
    //need: answer == x*y
  } else {

    //need to prove precondtion (requires) before recursive call
    Deduce(

      1 ( y >= 0) by Premise,
      2 (!( y == 0 )) by Premise,
      3 ( y-1 >= 0) by Algebra*(1,2) // proves precondition 
      //need to prove:
    )

    //will tel me x*(y-1)
    //will be x + x + ... + x (a total of y-1 times)
    var temp: Z = mult(x, y-1)
    answer = x + temp

    Deduce(
      1 (answer == x + temp) by Premise, //from assignment
      2 ( !( y == 0 ) ) by Premise, //if condition is false
      3 ( temp == x*(y-1)) by Premise, //from postcondition after 

      4 ( temp == x*y - x) by Algebra*(3),
      5 (answer == x + temp) by Algebra*(1,4),
      6 (answer == x*y) by Algebra*(5) //proves postcondition for

    )

    //what do we need to show here?
  }


    Deduce(
      1 (answer == x-y) by Premise
    )

  //what do we need to do here?
  //need to prove the postcondition about what i am returning
  //need: answer == x*y

  return answer
}

////////////// Test code //////////////

val a: Z = 5
val b: Z = 4

//prove the precondition for the call
Deduce(
  1 ( b == 4) by Premise,
  2 ( b >= 0) by Algebra*(1)

  //need: b >= 0
)


var ans: Z = mult(a, b)

//prove the assert
Deduce(
  1 ( a == 5) by Premise,
  2 ( b == 4) by Premise,
  3 ( ans == a*b ) by Premise, //from postcondition
  4 ( ans == 20) by Algebra*(1,2,3) // proves assert

  //need: ans == 20
)

//what do we want to assert that ans is?
assert(ans == 20)