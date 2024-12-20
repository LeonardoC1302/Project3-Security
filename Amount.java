/*
 * This assignment is based on Erik Poll's assignment (Radboud University, Nijmegen).
 */

/* OpenJML exercise

   Objects of this class represent euro amounts. For example, an Amount 
   object with
     euros == 1
     cents == 55
   represents 1.55 euro. 

   Specify the class with JML and check it OpenJML.  

   NB there may be errors in the code that you have to fix to stop 
   OpenJML from complaining, as these complaints of OpenJML 
   point to real bugs in the code. But keep changes to the code to
   a minimum of what is strictly needed. 
   Mark any changes you have made in the code with a comment,
   eg to indicate that you replaced <= by <.

   You should add enough annotations to stop OpenJML complaining,
   but you should ALSO specify invariants discussed below:

   1) We do not want to represent 1.55 euro as an object with
         euro  == 0
         cents == 155
      (Note that the "equals" method will not be correct if we allow 
       this.)
      Specify an invariant that rules this out.

   2) We do not want to represent 1.55 euro as an object with
         euros =  2
         cents =  -45
      Specify one (or more) invariant(s) that rule this out. But note that
      we DO want to allow negative amounts, otherwise the method negate 
      can't be allowed.
      It may be useful to use the JML notation ==> (for implication) in 
      your invariants.

   While developing your specs, it may be useful to use the keywords
      assert
   to add additional assertions in source code, to find out what 
   OpenJML can - or cannot - prove at a given program point.

*/

//@ nullable_by_default                      // Do not remove this annotation
public class Amount{


    //@ spec_public
    private int cents;
    //@ spec_public
    private int euros;


    /*@ requires euros >= 0 ==> cents >= 0;
      @ requires euros <= 0 ==> cents <= 0;
      @ requires (cents >= 0 && cents <100) || (cents < 0 && cents > -100);
      @ ensures this.euros == euros;
      @ ensures this.cents == cents;
      @ ensures this != null;
      @pure
    @*/
    public Amount(int euros, int cents){
        this.euros = euros;
        //@ assert this.euros == euros;
        this.cents = cents;
        //@ assert this.cents == cents;
    }
    

    //@ requires this.euros != Integer.MIN_VALUE;
    //@ requires this.cents != Integer.MIN_VALUE;
    //@ requires euros >= 0 ==> cents >= 0;
    //@ requires euros <= 0 ==> cents <= 0;
    //@ requires (cents >= 0 && cents <100) || (cents < 0 && cents > -100);

    //@ ensures \result != null;
    //@ ensures \result.euros == -euros;
    //@ ensures \result.cents == -cents;
    //@ ensures (\result.euros >= 0 ==> \result.cents >= 0) && (\result.euros <= 0 ==> \result.cents <= 0);
    //@ ensures (\result.cents >= 0 && \result.cents < 100) || (\result.cents < 0 && \result.cents > -100);
    //@ pure
    public Amount negate(){
        return new Amount(-euros,-cents); // se cambia el orden de los parametros
    }
  
    //@ requires a != null;
    //@ requires a.euros != Integer.MIN_VALUE;
    //@ requires a.cents != Integer.MIN_VALUE;
    //@ requires a.euros >= 0 ==> a.cents >= 0;
    //@ requires a.euros <= 0 ==> a.cents <= 0;
    //@ requires (a.cents >= 0 && a.cents <100) || (a.cents < 0 && a.cents > -100);

    //@ requires -a.euros != Integer.MIN_VALUE;
    //@ requires -a.cents != Integer.MIN_VALUE;
    //@ requires -a.euros >= 0 ==> -a.cents >= 0;
    //@ requires -a.euros <= 0 ==> -a.cents <= 0;
    //@ requires (-a.cents >= 0 && -a.cents <100) || (-a.cents < 0 && -a.cents > -100);

    //@ requires (-a.euros + euros >= 0) ==> (-a.cents + cents >= 0);
    //@ requires (-a.euros + euros <= 0) ==> (-a.cents + cents <= 0);
    //@ requires ((-a.cents + cents >= 0) && (-a.cents + cents < 100)) || ((-a.cents + cents < 0) && (-a.cents + cents > -100));
    //@ requires -a.euros + euros < Integer.MAX_VALUE;
    //@ requires -a.cents + cents >= Integer.MIN_VALUE;
    //@ requires a.negate() != null;
    //@ requires a.negate().euros + euros > Integer.MIN_VALUE;
    public Amount subtract(Amount a){
        return this.add(a.negate());
    }


    //@ requires a != null;
    //@ requires a.euros + euros < Integer.MAX_VALUE;
    //@ requires a.cents + cents <= Integer.MAX_VALUE;
    //@ requires a.euros + euros > Integer.MIN_VALUE;
    //@ requires a.euros + euros >= Integer.MIN_VALUE;
    //@ requires a.cents + cents >= Integer.MIN_VALUE;

    //@ requires (a.euros + euros <= 0) ==> (a.cents + cents <= 0);
    //@ requires ((a.cents + cents >= 0) && (a.cents + cents < 100)) || ((a.cents + cents < 0) && (a.cents + cents > -100));
    //@ requires (a.euros + euros >= 0) ==> (a.cents + cents >= 0);
    public Amount add(Amount a){
        int new_euros = euros + a.euros;
        int new_cents = cents + a.cents; 
        if (new_cents <= -100) {  // se debe incluir para cuando no hay centavos
            new_cents = new_cents + 100;
            new_euros = new_euros - 1;
        } 
        if (new_cents >= 100) {  // Se debe incluir para cuando no hay centavos
            new_cents = new_cents - 100;
            new_euros = new_euros + 1; // Se debe sumar y no restar
        } 
        if (new_cents < 0 && new_euros > 0) { 
            new_cents = new_cents + 100; 
            new_euros = new_euros - 1;
        } 
        if (new_cents > 0 && new_euros < 0) { // no se debe permitir 0
            new_cents = new_cents - 100; 
            new_euros = new_euros + 1;
        }
        
        return new Amount(new_euros,new_cents);
    }


    public boolean equal(Amount a) {
        if (a==null) return false;
        else return (euros == a.euros && cents == a.cents);
    }

}
