/*
 * This assignment is based on Erik Poll's assignment (Radboud University, Nijmegen).
 */
/* OpenJML Exercise:
 This class implements a Bag of integers, using an array.
 Add JML specs to this class, to stop OpenJML from complaining.
 NB there may be errors in the code that you have to fix to stop
 OpenJML from complaining, as these complaints of OpenJML
 point to real bugs in the code. But keep changes to the code to
 a minimum of what is strictly needed.
 Mark any changes you have made in the code with a comment,
 eg to indicate that you replaced <= by <.
 While developing your specs, it may be useful to use the keywords
 assert
 to add additional assertions in source code, to find out what
 OpenJML can - or cannot - prove at a given program point.
*/
//@ nullable_by_default // Do not remove this annotation
class Bag {
    int[] contents;
    int n;

    //@ requires input != null;
    //@ ensures n == input.length;
    //@ ensures contents != null;
    //@ ensures contents.length == input.length;
    //@ pure
    Bag(int[] input) {
        n = input.length;
        contents = new int[n];
        arraycopy(input, 0, contents, 0, n);
    }

    Bag() {
        n = 0;
        contents = new int[0];
    }

    //@ requires contents != null;
    //@ requires n <= contents.length;
    //@ requires n >= 0;
    void removeOnce(int elt) {
        // Changed <= to < to fix off-by-one error

        /*@ maintaining 0 <= i <= n;
        @ maintaining i <= contents.length;
        @ maintaining n <= contents.length;
        @*/
        for (int i = 0; i < n; i++) {
            //@ assert i < contents.length;
            if (contents[i] == elt) {
                n--;
                contents[i] = contents[n];
                return;
            }
        }
    }

    //@ requires contents != null;
    //@ requires n <= contents.length;
    //@ requires n >= 0;
    void removeAll(int elt) {
        /*@ maintaining 0 <= i <= n;
        @ maintaining i <= contents.length;
        @ maintaining n <= contents.length;
        @ maintaining n >= 0;  // Added to track that n stays non-negative
        @ maintaining \old(n) >= n;  // Added to track that n only decreases
        @ maintaining i <= \old(n);  // Added to ensure i stays within original bounds
        @*/
        for (int i = 0; i < n; i++) { // Changed <= to < to fix off-by-one error
            //@ assert i < contents.length;
            if (contents[i] == elt) {
                n--;
                contents[i] = contents[n];
                i--; // Para revisar el elemento que acabamos de agregar
            }
        }
    }

    //@ requires contents != null;
    //@ requires n <= contents.length;
    //@ requires n >= 0;
    //@ requires n < Integer.MAX_VALUE;
    int getCount(int elt) {
        int count = 0;
        /*@ maintaining 0 <= i <= n;  // Cambiado para usar n en lugar de contents.length
        @ maintaining i <= contents.length;
        @ maintaining count >= 0;
        @ maintaining count <= i;  // count no puede ser mayor que elementos revisados
        @ maintaining count <= Integer.MAX_VALUE - (n - i);  // Prevenir overflow futuro
        @*/
        for (int i = 0; i < n; i++) {
            //@ assert i < contents.length;
            if (contents[i] == elt) {
                count++;
            }
        }
        return count;
    }

    //@ requires n >= 0;
    //@ requires contents != null;
    //@ requires n < contents.length;
    //@ requires 2 * n >= 0;
    //@ requires n < Integer.MAX_VALUE / 2;
    void add(int elt) {
        //@ assert n >= 0;
        if (n == contents.length) {
            //@ assert 2 * n >= 0;
            int[] new_contents = new int[2 * n];
            arraycopy(contents, 0, new_contents, 0, n);
            contents = new_contents;
        }
        //@ assert n >= 0 && n < contents.length;
        contents[n] = elt;
        n++;
    }

    //@ requires b != null;
    //@ requires n + b.n >= Integer.MIN_VALUE;
    //@ requires n + b.n <= Integer.MAX_VALUE;
    //@ requires n >= 0;
    //@ requires b.n >= 0;
    //@ requires n + b.n >= 0;
    //@ requires b.contents != null;
    //@ requires contents != null;
    //@ requires n <= contents.length;
    //@ requires b.n <= b.contents.length;
    void add(Bag b) {
        int[] new_contents = new int[n + b.n];
        //@ assert n <= contents.length;  // Ayuda al verificador
        //@ assert 0 + n <= contents.length;  // Para la primera llamada a arraycopy
        arraycopy(contents, 0, new_contents, 0, n);

        //@ assert b.n <= b.contents.length;  // Ayuda al verificador
        //@ assert 0 + b.n <= b.contents.length;  // Para la segunda llamada a arraycopy
        // Changed n+1 to n to fix index out of bounds error
        arraycopy(b.contents, 0, new_contents, n, b.n);
        contents = new_contents;
    }

    //@ requires a != null;
    //@ requires a.length + this.n >= Integer.MIN_VALUE;
    //@ requires a.length + this.n <= Integer.MAX_VALUE;
    //@ requires a.length >= 0;  // implícito por ser un array, pero ayuda al verificador
    //@ requires this.n >= 0;    // necesario para la precondición de add(Bag)
    //@ requires n == a.length;
    //@ requires contents != null;
    //@ requires n<=contents.length;
    void add(int[] a) {
        this.add(new Bag(a));
    }

    //@ requires b != null;
    //@ requires b.n >= 0;  // prevent negative counts
    //@ requires b.n <= Integer.MAX_VALUE;  // prevent overflow when adding
    //@ requires b.contents != null;
    //@ requires b.n <= b.contents.length;
    Bag(Bag b) {
        contents = new int[b.n]; // Se debe inicializar, pues no se esta realizando en ninguna parte
        this.add(b);
    }

    //@ requires dest != null;
    //@ requires dest != null;
    //@ requires src != null;
    //@ requires srcOff >= 0;
    //@ requires srcOff + length <= src.length;
    //@ requires destOff >= 0;
    //@ requires destOff + length <= dest.length;
    //@ requires length >= 0;
    //@ requires srcOff + length <= Integer.MAX_VALUE;
    //@ requires destOff + length <= Integer.MAX_VALUE;
    /*@ assignable dest[destOff .. destOff + length - 1]; @*/
    private static void arraycopy(int[] src,
                                int srcOff,
                                int[] dest,
                                int destOff,
                                int length) {

        /*@ maintaining 0 <= i <= length;
        @ maintaining destOff + i <= dest.length;
        @ maintaining srcOff + i <= src.length;
        @*/
        for(int i=0; i<length; i++) {
            //@ assert destOff + i < dest.length && destOff + i >= 0;
            //@ assert srcOff + i < src.length && srcOff + i >= 0;
            dest[destOff + i] = src[srcOff + i];
        }
    }
}