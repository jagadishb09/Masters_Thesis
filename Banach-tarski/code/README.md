Proof of Banach-Tarski theorem:

Main reference:  Weston, T.. “THE BANACH-TARSKI PARADOX.” (2003).

groups.lisp: Used, characters #\a, #\b, #\c and #\d to represent words.
             Reduced words are those lists for which #\a, #\b and #\c,
             #\d characters are not next to each other.  word-fix is a
             function that fixes any word and makes it a reduced word.
             compose is the binary operation between two lists which
             is equal to (word-fix (append x y)) where x and y are two
             lists.  Proved group properties for the set of reduced
             words with compose as the binary operation.

free-group.lisp: Proved that if the characters #\a, #\b, #\c, #\d
		 represent the rotations mentioned in the reference
		 and matrix multiplication as the operation between
		 the matrices, then the set of resulting
		 matrices form a free group of rank 2.

rotations.lisp: Proved every matrix in the free group is a rotation in R3.

supportive-theorems.lisp: Theorems about symbol name of array2p which
                          were initially developed by Eric Smith of Kestrel Institute for 1-d arrays.
			  I've extended them to 2-d arrays.

hausdorff-paradox.lisp : In proogress (proof of Hausdorff paradox)