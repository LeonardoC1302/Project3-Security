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
/*
    //@ requires input != null;
    Bag(int[] input) {
        n = input.length;
        contents = new int[n];
        arraycopy(input, 0, contents, 0, n);
    }
*/
    Bag() {
        n = 0;
        contents = new int[0];
    }
/*
    void removeOnce(int elt) {
        // Changed <= to < to fix off-by-one error
        for (int i = 0; i < n; i++) {
            if (contents[i] == elt) {
                n--;
                contents[i] = contents[n];
                return;
            }
        }
    }

    void removeAll(int elt) {
        // Changed <= to < to fix off-by-one error
        for (int i = 0; i < n; i++) {
            if (contents[i] == elt) {
                n--;
                contents[i] = contents[n];
            }
        }
    }

    int getCount(int elt) {
        // Changed <= to < to fix off-by-one error
        int count = 0;
        for (int i = 0; i < n; i++)
            if (contents[i] == elt) count++;
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
    void add(Bag b) {
        int[] new_contents = new int[n + b.n];
        arraycopy(contents, 0, new_contents, 0, n);
        // Changed n+1 to n to fix index out of bounds error
        arraycopy(b.contents, 0, new_contents, n, b.n);
        contents = new_contents;
    }

    void add(int[] a) {
        this.add(new Bag(a));
    }

    //@ requires b != null;
    Bag(Bag b) {
        this.add(b.contents); // Changed because add recieves the contents array
    }
*/
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
        int i = 0;
        /*@ maintaining 0 <= i <= length;
        @ maintaining destOff + i <= dest.length;
        @ maintaining srcOff + i <= src.length;
        @*/
        while (i < length) {
            //@ assert destOff + i < dest.length && destOff + i >= 0;
            //@ assert srcOff + i < src.length && srcOff + i >= 0;
            dest[destOff + i] = src[srcOff + i];
            i++;
        }
    }
}