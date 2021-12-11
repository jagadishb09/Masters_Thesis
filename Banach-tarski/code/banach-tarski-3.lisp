
(include-book "banach-tarski-1")

(encapsulate
  ()

  (local (include-book "arithmetic/top" :dir :system))

  (defthmd sine-p2=0-lemma-4-2
    (implies (and (realp p)
                  (realp q)
                  (realp r)
                  (equal (* p q) r)
                  (not (equal q 0)))
             (equal (/ r q) p)))

  (defthmd sine-p2=0-lemma-4-1
    (IMPLIES (AND (NOT (EQUAL X 0))
                  (REALP X)
                  (REALP Z)
                  (REALP P1)
                  (REALP P3)
                  (EQUAL (* P1 Z) (* P3 X)))
             (equal (/ (* p1 z) x) p3))
    :hints (("Goal"
             :use ((:instance sine-p2=0-lemma-4-2 (r (* p1 z)) (p p3) (q x)))
             )))

  (defthmd sine-p2=0-lemma-4-3-1
    (implies (equal x y)
             (equal (* x z) (* y z))))

  (defthmd sine-p2=0-lemma-4-3
    (IMPLIES (AND (NOT (EQUAL X 0))
                  (EQUAL (* P1 (/ X) Z) P3)
                  (REALP X)
                  (REALP Z)
                  (REALP P1)
                  (REALP P3)
                  (EQUAL (+ (EXPT X 2) (EXPT Z 2)) 1)
                  (EQUAL (+ (EXPT P1 2) (EXPT P3 2)) 1)
                  (EQUAL (* P1 Z) (* P3 X)))
             (equal (+ (* p1 p1 x x) (* p1 p1 z z)) (* x x)))
    :hints (("Subgoal 1"
             :use ((:instance sine-p2=0-lemma-4-3-1
                              (x (+ (EXPT P1 2)
                        (* (EXPT P1 2) (EXPT Z 2) (EXPT X -2))))
                              (y 1)
                              (z (expt x 2))))
             )
            ))

  (defthmd sine-p2=0-lemma-4-4
    (EQUAL (+ (* (EXPT P1 2) (EXPT X 2))
              (* (EXPT P1 2) (EXPT Z 2)))
           (* p1 p1 (+ (* x x) (* z z)))))

  (defthm sine-p2=0-lemma-4-5
    (implies (and (realp x)
                  (realp p1)
                  (equal (expt p1 2) (expt x 2)))
             (or (equal p1 x)
                 (equal p1 (- x))))
    :hints (("Goal"
             :use ((:instance sqrt-*-x-x (x x))
                   (:instance sqrt-*-x-x (x p1)))
             :in-theory (disable sqrt-*-x-x y-=-sqrt sqrt-=-y)
             ))
    :rule-classes nil)
  )

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd sine-p2=0-lemma
    (implies (and (realp x)
                  (realp z)
                  (equal (+ (* x x) (* z z)) 1)
                  (realp s)
                  (realp p2)
                  (equal (* z s p2) 0)
                  (equal (* x s p2) 0))
             (equal (* s p2) 0)))

  (defthm sine-p2=0-lemma-1
    (implies (and (realp x)
                  (realp z)
                  (equal (+ (* x x) (* z z)) 1)
                  (realp s)
                  (realp p2)
                  (equal (* z s p2) 0)
                  (equal (* x s p2) 0))
             (or (equal s 0)
                 (equal p2 0)))
    :rule-classes nil
    )

  (defthm sine-p2=0-lemma-2
    (implies (and (realp x)
                  (realp z)
                  (realp s)
                  (realp p1)
                  (realp p3)
                  (equal (- (* z s p1)
                            (* x s p3))
                         0))
             (or (equal s 0)
                 (equal (* z p1) (* x p3))))
    :rule-classes nil
    )

  (defthm sine-p2=0-lemma-3
    (implies (and (realp x)
                  (realp y)
                  (realp z)
                  (realp p1)
                  (realp p2)
                  (realp p3)
                  (equal y 0)
                  (equal p2 0)
                  (equal (+ (* x x) (* y y) (* z z)) 1)
                  (equal (+ (* p1 p1) (* p2 p2) (* p3 p3)) 1)
                  (equal (* z p1) (* x p3))
                  (equal x 0))
             (and (or (equal p3 z)
                      (equal p3 (- z)))
                  (equal p1 0)))
    :rule-classes nil)

  (defthm sine-p2=0-lemma-4
    (implies (and (realp x)
                  (realp y)
                  (realp z)
                  (realp p1)
                  (realp p2)
                  (realp p3)
                  (equal p2 0)
                  (equal y 0)
                  (equal (+ (* x x) (* y y) (* z z)) 1)
                  (equal (+ (* p1 p1) (* p2 p2) (* p3 p3)) 1)
                  (equal (* z p1) (* x p3)))
             (or (and (equal p1 x)
                      (equal p3 z))
                 (and (equal p1 (- x))
                      (equal p3 (- z)))))
    :hints (("Goal"
             :use ((:instance sine-p2=0-lemma-3 (x x) (y y) (z z) (p1 p1) (p2 p2) (p3 p3))
                   (:instance sine-p2=0-lemma-4-1 (x x) (z z) (p1 p1) (p3 p3))
                   (:instance sine-p2=0-lemma-4-3 (x x) (z z) (p1 p1) (p3 p3))
                   (:instance sine-p2=0-lemma-4-4 (p1 p1) (x x) (z z))
                   (:instance sine-p2=0-lemma-4-5)
                   )
             ))
    :rule-classes nil)
  )

----

(defthmd r-theta*p=p=>sine=0
  (implies (and (point-in-r3 p)
                (point-in-r3 u)
                (realp angle)
                (equal (+ (* (point-in-r3-x1 p) (point-in-r3-x1 p))
                          (* (point-in-r3-y1 p) (point-in-r3-y1 p))
                          (* (point-in-r3-z1 p) (point-in-r3-z1 p)))
                       1)
                (equal (+ (* (point-in-r3-x1 u) (point-in-r3-x1 u))
                          (* (point-in-r3-y1 u) (point-in-r3-y1 u))
                          (* (point-in-r3-z1 u) (point-in-r3-z1 u)))
                       1)
                (equal (point-in-r3-y1 u) 0)
                (m-= (m-* (rotation-about-witness angle u) p) p))
           (equal (acl2-sine angle) 0))
  :hints (("Goal"


           )))









--------------

(defthmd sine-is-0-in-0<pi=>x=0-1
  (implies (and (realp x)
                (< 0 x)
                (< x (acl2-pi)))
           (> (acl2-sine x) 0))
  :hints (("Goal"
           :use ((:instance sine-positive-in-0-pi/2 (x x))
                 (:instance sine-positive-in-pi/2-pi (x x)))
           )))


(defthmd sine-is-0-in-0<pi=>x=0
  (implies (and (realp x)
                (<= 0 x)
                (< x (acl2-pi))
                (equal (acl2-sine x) 0))
           (equal (* x x) 0))
  :hints (("Goal"
           :use ((:instance sine-is-0-in-0<pi=>x=0-1 (x x)))
           ))
  )

----


; Added by Matt K. for v2-7.
(add-match-free-override :once t)
(set-match-free-default :once)

(local
 (defun sine-interval (y)
   (declare (ignore y))
   (interval (- (/ (acl2-pi) 2)) (/ (acl2-pi) 2))))

(local
 (defun cosine-interval (y)
   (declare (ignore y))
   (interval 0 (acl2-pi))))

(local
 (defthm trivial-subinterval
   (implies (and (realp x)
                 (realp y)
                 (< x y))
            (subinterval-p (interval x y) (interval x y)))
   :hints (("Goal"
	    :in-theory (enable interval-definition-theory)))))

(local
 (defthm *-x-0
   (equal (* x 0) 0)))

(local
 (defthm-std standard-pi
   (standardp (acl2-pi))))

(local
 (defthm-std standard-exp
   (implies (standardp x)
            (standardp (acl2-exp x)))))


(local
 (defthm-std standard-cosine
   (implies (standardp x)
            (standardp (acl2-cosine x)))))


(encapsulate
  ()
  (local
   (defthm lemma-1
     (implies (and (realp c)
                   (realp s)
                   (equal (+ (* s s) (* c c)) 1))
              (<= c 1))))
  (local
   (defthm lemma-2
     (implies (and (realp c)
                   (realp s)
                   (equal (+ (* s s) (* c c)) 1))
              (<= -1 c))
     :hints (("Goal"
              :use ((:instance lemma-1 (c (- c))))
              :in-theory (disable lemma-1)))))
  (defthm cosine-bound
    (implies (realp x)
             (and (<= -1 (acl2-cosine x))
                  (<= (acl2-cosine x) 1)))
    :hints (("Goal"
             :use ((:instance lemma-1
                              (s (acl2-sine x))
                              (c (acl2-cosine x)))
                   (:instance lemma-2
                              (s (acl2-sine x))
                              (c (acl2-cosine x))))
             :in-theory (disable lemma-1 lemma-2))))
  )

(local
 (defthm standard-part-<=-acl2-pi
   (implies (and (realp x)
                 (<= x (acl2-pi)))
            (<= (standard-part x) (acl2-pi)))
   :hints (("Goal"
            :use ((:instance standard-part-<=
                             (x x)
                             (y (acl2-pi))))
            :in-theory (disable standard-part-<=)))))

(encapsulate
  ()
  (local
   (defthm lemma-1-1-1
     (implies (and (realp x)
                   (realp y)
                   (<= 0 x)
                   (< x y)
                   (<= y (acl2-pi)))
              (and (<= 0 (- y x))
                   (<= (- y x) (acl2-pi))))))
  (local
   (defthm lemma-1-1-2
     (equal (acl2-sine (* 1/2 (acl2-pi))) 1)))
  (local
   (defthm lemma-1-1-3
     (implies (and (realp x)
                   (<= 0 x)
                   (<= x (acl2-pi)))
              (<= 0 (acl2-sine x)))
     :hints (("goal"
              :use ((:instance sine-positive-in-0-pi/2)
                    (:instance sine-positive-in-pi/2-pi))
              :in-theory (disable sine-positive-in-0-pi/2
                                  sine-positive-in-pi/2-pi
                                  sine-2x
                                  sine-3x)))))

  (defthm test-case
    (implies (and (realp x)
                  (< 0 x)
                  (< x (acl2-pi)))
             (> (acl2-sine x) 0)))
;(or (equal (* x x) 0)
;   (equal (acl2-pi) x))))
  )

---

(include-book "hausdorff-paradox-2")
(include-book "nonstd/nsa/trig" :dir :system)

;; Title: A Formal Proof of the Banach-Tarski Theorem in ACL2(r)

;; Abstract: The Banach-Tarski theorem states that a solid ball can be partitioned into a finite number of pieces which can be rotated to form two identical copies of the ball. The proof of the Banach-Tarski theorem involves generating a free group of rotations and then decomposing the ball using these rotations and rearranging them to get two copies of the ball. The key ingredients to the proof are the Hausdorff paradox and the proof that the reals are uncountable. Denumerability of reals has already been proved in ACL2(r) and now we have proved the Hausdorff and currently, we are working to prove the Banach-Tarski theorem for a solid ball centered at the origin with radius equal to 1. In this paper we present a formal proof of the Hausdorff Paradox in ACL2(r).

(defthmd test-202
  (implies (and (not (equal th1 th2))
                (>= th1 0)
                (< th1 (* 2 (acl2-pi)))
                (>= th2 0)
                (< th2 (* 2 (acl2-pi))))
           (not (equal (acl2-sine th1) (acl2-sine th2))))
  :hints (("Goal"
           :use ((:instance acl2-sine (x th1))
                 (:instance acl2-sine (x th2)))
           :in-theory (enable (acl2-sine))
           )))

---

(encapsulate
  ()
  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd d-p=>d-p-p-1
    (implies (and (s2-def-p p1)
                  (point-in-r3 p2)
                  (equal (aref2 :fake-name p2 0 0) (- (aref2 :fake-name p1 0 0)))
                  (equal (aref2 :fake-name p2 1 0) (- (aref2 :fake-name p1 1 0)))
                  (equal (aref2 :fake-name p2 2 0) (- (aref2 :fake-name p1 2 0))))
             (s2-def-p p2))
    :hints (("Goal"
             :in-theory (disable aref2)
             )))
  )

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd d-p=>d-p-p-2-1
    (implies (r3-matrixp m)
             (and (equal (aref2 :fake-name (second (f-poles m)) 0 0)
                         (- (aref2 :fake-name (first (f-poles m)) 0 0)))
                  (equal (aref2 :fake-name (second (f-poles m)) 1 0)
                         (- (aref2 :fake-name (first (f-poles m)) 1 0)))
                  (equal (aref2 :fake-name (second (f-poles m)) 2 0)
                         (- (aref2 :fake-name (first (f-poles m)) 2 0)))))
    :hints (("Goal"
             :use ((:instance f-poles-prop-2 (m m)))
             :in-theory (disable aref2 f-poles acl2-sqrt square)
             )))

  (defthmd d-p=>d-p-p-2-2
    (implies (and (point-in-r3 p1)
                  (point-in-r3 p2)
                  (equal (aref2 :fake-name p2 0 0) (aref2 :fake-name p1 0 0))
                  (equal (aref2 :fake-name p2 1 0) (aref2 :fake-name p1 1 0))
                  (equal (aref2 :fake-name p2 2 0) (aref2 :fake-name p1 2 0)))
             (m-= p1 p2))
    :hints (("Goal"
             :in-theory (enable m-=)
             )))
  )

(defthmd test-202
  (implies (and (not (equal th1 th2))
                (>= th1 0)
                (< th1 (* 2 (acl2-pi)))
                (>= th2 0)
                (< th2 (* 2 (acl2-pi))))
           (not (equal (acl2-sine th1) (acl2-sine th2))))
  :hints (("Goal"
           :use ((:instance acl2-sine (x th1))
                 (:instance acl2-sine (x th2)))
           :in-theory (enable (acl2-sine))
           )))

----

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd d-p=>d-p-p-2
    (implies (and (d-p p1)
                  (point-in-r3 p2)
                  (equal (aref2 :fake-name p2 0 0) (- (aref2 :fake-name p1 0 0)))
                  (equal (aref2 :fake-name p2 1 0) (- (aref2 :fake-name p1 1 0)))
                  (equal (aref2 :fake-name p2 2 0) (- (aref2 :fake-name p1 2 0)))
                  (m-= (first (poles (word-exists-witness p1))) p1))
             (m-= p2 (second (poles (word-exists-witness p1)))))
    :hints (("Goal"
             :use ((:instance s2-def-p (point p1))
                   (:instance point-in-r3 (x p1))
                   (:instance d-p=>d-p-p-2-2 (p1 p2) (p2 (second (poles (word-exists-witness p1)))))
                   (:instance d-p (point p1))
                   (:instance poles (w (word-exists-witness p1)))
                   (:instance word-exists (point p1))
                   (:instance d-p=>d-p-p-2-1 (m (rotation (word-exists-witness p1) (acl2-sqrt 2))))
                   (:instance r3-rotationp (m (rotation (word-exists-witness p1) (acl2-sqrt 2))))
                   (:instance f-poles-prop-3 (m (rotation (word-exists-witness p1) (acl2-sqrt 2))))
                   (:instance rotation-is-r3-rotationp (w (word-exists-witness p1)) (x (acl2-sqrt 2))))
             :in-theory (e/d (m-=) (aref2 reducedwordp rotation acl2-sqrt square aref2 m-trans r3-m-inverse r3-m-determinant r3-matrixp f-poles word-exists d-p d-p-implies))
             ))
    )

  (defthmd d-p=>d-p-p-3
    (implies (and (d-p p1)
                  (point-in-r3 p2)
                  (equal (aref2 :fake-name p2 0 0) (- (aref2 :fake-name p1 0 0)))
                  (equal (aref2 :fake-name p2 1 0) (- (aref2 :fake-name p1 1 0)))
                  (equal (aref2 :fake-name p2 2 0) (- (aref2 :fake-name p1 2 0)))
                  (m-= (second (poles (word-exists-witness p1))) p1))
             (m-= p2 (first (poles (word-exists-witness p1)))))
    :hints (("Goal"
             :use ((:instance s2-def-p (point p1))
                   (:instance point-in-r3 (x p1))
                   (:instance d-p=>d-p-p-2-2 (p1 p2) (p2 (first (poles (word-exists-witness p1)))))
                   (:instance d-p (point p1))
                   (:instance poles (w (word-exists-witness p1)))
                   (:instance word-exists (point p1))
                   (:instance d-p=>d-p-p-2-1 (m (rotation (word-exists-witness p1) (acl2-sqrt 2))))
                   (:instance r3-rotationp (m (rotation (word-exists-witness p1) (acl2-sqrt 2))))
                   (:instance f-poles-prop-3 (m (rotation (word-exists-witness p1) (acl2-sqrt 2))))
                   (:instance rotation-is-r3-rotationp (w (word-exists-witness p1)) (x (acl2-sqrt 2))))
             :in-theory (e/d (m-=) (aref2 reducedwordp rotation acl2-sqrt square aref2 m-trans r3-m-inverse r3-m-determinant r3-matrixp f-poles word-exists d-p d-p-implies))
             ))
    )
  )

(defthmd d-p=>d-p-p-4
  (implies (and (m-= p2 pole)
                (m-= (m-* rot pole) pole))
           (m-= (m-* rot p2) p2)))

(defthmd d-p=>d-p-p
  (implies (and (d-p p1)
                (point-in-r3 p2)
                (equal (aref2 :fake-name p2 0 0) (- (aref2 :fake-name p1 0 0)))
                (equal (aref2 :fake-name p2 1 0) (- (aref2 :fake-name p1 1 0)))
                (equal (aref2 :fake-name p2 2 0) (- (aref2 :fake-name p1 2 0))))
           (d-p p2))
  :hints (("Goal"
           :use ((:instance two-poles-for-all-rotations (p p1)))
           :cases ((m-= (first (poles (word-exists-witness p1))) p1)
                   (m-= (second (poles (word-exists-witness p1))) p1))
           :in-theory (disable reducedwordp d-p word-exists square s2-def-p wordp array2p word-exists-suff)
           )
          ("Subgoal 2"
           :use ((:instance d-p=>d-p-p-2 (p1 p1) (p2 p2))
                 (:instance d-p (point p1))
                 (:instance d-p (point p2))
                 (:instance word-exists-suff (point p2) (w (word-exists-witness p1)))
                 (:instance word-exists (point p1))
                 (:instance d-p=>d-p-p-1 (p1 p1) (p2 p2))
                 (:instance f-returns-poles-1-second (w  (word-exists-witness p1)))
                 (:instance d-p=>d-p-p-4 (p2 p2) (pole (second (poles (word-exists-witness p1))))
                            (rot (rotation (word-exists-witness p1) (acl2-sqrt 2))))
                 )
           :in-theory nil
           )
          ("Subgoal 1"
           :use ((:instance d-p=>d-p-p-3 (p1 p1) (p2 p2))
                 (:instance d-p (point p1))
                 (:instance d-p (point p2))
                 (:instance word-exists-suff (point p2) (w (word-exists-witness p1)))
                 (:instance word-exists (point p1))
                 (:instance d-p=>d-p-p-1 (p1 p1) (p2 p2))
                 (:instance f-returns-poles-1-first (w  (word-exists-witness p1)))
                 (:instance d-p=>d-p-p-4 (p2 p2) (pole (first (poles (word-exists-witness p1))))
                            (rot (rotation (word-exists-witness p1) (acl2-sqrt 2))))
                 )
           :in-theory nil
           )

          )
  )

----

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

---

(defun-sk exists-int-k (theta1 theta2)
  (exists k
          (and (integerp k)
               (equal (+ theta2 (* 2 k (acl2-pi)))
                      theta1))))


(defthmd test-202
  (implies (and (point-in-r3 p)
                (not (m-= (point-on-s2-not-d) p))
                (realp theta1)
                (realp theta2)
                (m-= (m-* (rotation-about-witness theta1 (point-on-s2-not-d)) p)
                     (m-* (rotation-about-witness theta2 (point-on-s2-not-d)) p)))
           (exists-int-k theta1 theta2)))

(defthmd test-202
  (implies (and (not (equal th1 th2))
                (>= th1 0)
                (< th1 (* 2 (acl2-pi)))
                (>= th2 0)
                (< th2 (* 2 (acl2-pi))))
           (not (equal (acl2-sine th1) (acl2-sine th2))))
  :hints (("Goal"
           :use ((:instance acl2-sine (x th1))
                 (:instance acl2-sine (x th2)))
           :in-theory (enable (acl2-sine))
           )))

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
