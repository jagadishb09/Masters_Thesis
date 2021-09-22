# A Formal Proof of the Banach-Tarski theorem:

## Main reference:  Weston, T.. “THE BANACH-TARSKI PARADOX.” (2003).

## Goal: Prove the Banach-Tarski theorem in ACL2(r)

We can divide the proof into three steps:

#### Step1: Prove the Hausdorff paradox

#### Step2: Prove the Banach-Tarski Theorem for the surface of the sphere

#### Step3: Prove the Banach-Tarski theorem for a solid ball cenetered at the origin

##### Progress:

Step1:
Hausdorff Paradox statement: There is a countable set D that is a subset of S^2 such that S^2-D can be divided into 5 pieces which can then be rotated to form 2 copies of S^2-D.

Proved the equivalences between different partitions of S^2-D. Check hausdorff-paradox.lisp for the proof.

To Do: Prove set D is countable.