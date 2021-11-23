; Banach-Tarski theorem
;
; Proof of Banach-Tarski theorem for the surface of the spehere centered at the
; origin with radius equal to 1.
;
;
; Copyright (C) 2021 University of Wyoming
;
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.
;
; Main Authors: Jagadish Bapanapally (jagadishb285@gmail.com)
;
; Contributing Authors:
;   Ruben Gamboa (ruben@uwyo.edu)

(in-package "ACL2")

; cert_param: (uses-acl2r)

(include-book "hausdorff-paradox-2")
(include-book "nonstd/nsa/trig" :dir :system)

;; Title: A Formal Proof of the Banach-Tarski Theorem in ACL2(r)

;; Abstract: The Banach-Tarski theorem states that a solid ball can be partitioned into a finite number of pieces which can be rotated to form two identical copies of the ball. The proof of the Banach-Tarski theorem involves generating a free group of rotations and then decomposing the ball using these rotations and rearranging them to get two copies of the ball. The key ingredients to the proof are the Hausdorff paradox and the vitali's theorem that uses the Axiom of choice. We have proved the Hausdorff paradox and the vitali's theorem in ACL2(r) and now we are working to prove the Banach-Tarski theorem for a solid ball centered at the origin with radius equal to 1.

(defthmd witness-not-in-x-coord-sequence-1
  (and (realp (exists-in-interval-but-not-in-x-coord-sequence-witness -1 1))
       (realp (acl2-sqrt (- 1 (* (exists-in-interval-but-not-in-x-coord-sequence-witness -1 1)
                                  (exists-in-interval-but-not-in-x-coord-sequence-witness -1 1))))))
       ;; (<= -1 (exists-in-interval-but-not-in-x-coord-sequence-witness -1 1))
       ;; (<= (exists-in-interval-but-not-in-x-coord-sequence-witness -1 1) 1))
  :hints (("goal"
           :use ((:instance witness-not-in-x-coord-sequence)
                 (:instance exists-point-on-s2-not-d-2))
           )))

(defun rotation-about-witness (angle point)
  `((:header :dimensions (3 3)
             :maximum-length 10)
    ((0 . 0) . ,(+ (acl2-cosine angle)
                   (* (point-in-r3-x1 point) (point-in-r3-x1 point) (- 1 (acl2-cosine angle)))) )
    ((0 . 1) . ,(- (* (point-in-r3-x1 point) (point-in-r3-y1 point) (- 1 (acl2-cosine angle)))
                   (* (point-in-r3-z1 point) (acl2-sine angle))) )
    ((0 . 2) . ,(+ (* (point-in-r3-x1 point) (point-in-r3-z1 point) (- 1 (acl2-cosine angle)))
                   (* (point-in-r3-y1 point) (acl2-sine angle))) )
    ((1 . 0) . ,(+ (* (point-in-r3-y1 point) (point-in-r3-x1 point) (- 1 (acl2-cosine angle)))
                   (* (point-in-r3-z1 point) (acl2-sine angle))) )
    ((1 . 1) . ,(+ (acl2-cosine angle)
                   (* (point-in-r3-y1 point) (point-in-r3-y1 point) (- 1 (acl2-cosine angle)))) )
    ((1 . 2) . ,(- (* (point-in-r3-y1 point) (point-in-r3-z1 point) (- 1 (acl2-cosine angle)))
                   (* (point-in-r3-x1 point) (acl2-sine angle))) )
    ((2 . 0) . ,(- (* (point-in-r3-z1 point) (point-in-r3-x1 point) (- 1 (acl2-cosine angle)))
                   (* (point-in-r3-y1 point) (acl2-sine angle))) )
    ((2 . 1) . ,(+ (* (point-in-r3-z1 point) (point-in-r3-y1 point) (- 1 (acl2-cosine angle)))
                   (* (point-in-r3-x1 point) (acl2-sine angle))) )
    ((2 . 2) . ,(+ (acl2-cosine angle)
                   (* (point-in-r3-z1 point) (point-in-r3-z1 point) (- 1 (acl2-cosine angle)))) )
    )
  )

(encapsulate
  ()
  (local (include-book "workshops/1999/embedded/Exercises/Exercise1-2/Exercise1.2" :dir :system))
  (defthmd test-200
    (implies (and (realp r)
                  (>= r 0)
                  (realp x)
                  (> x 0))
             (natp (/ (- r (mod r x)) x)))
    :hints (("Goal"
             :in-theory (enable mod)
             )))
  )

(encapsulate
  ()
  (local (include-book "workshops/1999/embedded/Exercises/Exercise1-2/Exercise1.2" :dir :system))
  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd test-201
    (implies (and (realp r)
                  (>= r 0)
                  (realp x)
                  (> x 0))
             (and (>= (mod r x) 0)
                  (realp (mod r x))
                  (< (mod r x) x)))
    :hints (("Goal"
             :in-theory (enable mod floor1)
             )))
  )

(defun-sk exists-natp-x (theta1 k)
  (exists x
          (and (natp x)
               (>= x 0)
               (< x (* 2 (acl2-pi)))
               (equal (acl2-sine (+ (* 2 (acl2-pi) k) x))
                      (acl2-sine theta1)))))

(defun-sk exists-int-k (theta1)
  (exists k
          (and (natp k)
               (>= (- theta1 (* 2 (acl2-pi) k)) 0)
               (< (- theta1 (* 2 (acl2-pi) k)) (* 2 (acl2-pi))))))


(defthmd test-1000
  (implies (realp theta1)
           (exists-int-k theta1))
  :hints

(defun-sk exists-int-k (theta1 theta2)
  (exists k
          (and (integerp k)
               (equal (+ (* 2 (acl2-pi) k) theta1)
                      theta2))))

(defthmd test-1000
  (implies (and (point-in-r3 p1)
                (realp theta1)
                (>= theta1 0)
                (realp theta2)
                (>= theta2 0)
                (m-= (rotation-about-witness theta1 p1)
                     (rotation-about-witness theta2 p1)))
           (exists-int-k theta1 theta2)))

-----

(defthmd r3-matrixp-rotation-witness
  (r3-matrixp (rotation-about-witness (acl2-pi) (point-on-s2-not-d)))
  :hints (("Goal"
           :use ((:instance witness-not-in-x-coord-sequence))
           :in-theory (e/d (aref2 header dimensions array2p) (acl2-sqrt))
           )))

(defun-sk choose-angle (n dp1 dp2)
  (exists theta
          (and (realp theta)
               (<= 0 theta)
               (< theta (acl2-pi))
               (m-= (m-* (rotation-about-witness (* theta n) (point-on-s2-not-d)) dp1)
                    dp2))))

(defun generate-angles-1 (n dp1 poles-list)
  (if (atom poles-list)
      nil
    (if (choose-angle n dp1 (car poles-list))
        (append (list (choose-angle-witness n dp1 (car poles-list)))
                (generate-angles-1 n dp1 (cdr poles-list)))
      (append (list nil)
              (generate-angles-1 n dp1 (cdr poles-list))))))

(defun generate-angles (n poles-list1 poles-list2)
  (if (atom poles-list1)
      nil
    (append (generate-angles-1 n (car poles-list1) poles-list2)
            (generate-angles n (cdr poles-list1) poles-list2))))
