
(include-book "banach-tarski-1")

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd k-range-1
    (implies (and (posp n)
                  (realp den)
                  (> den 0)
                  (realp x)
                  (< x den))
             (> (- n (/ x den)) 0)))
  )

  (defthmd k-range
    (implies (and (posp n)
                  (realp x)
                  (realp angle)
                  (>= angle 0)
                  (< angle (* 2 (acl2-pi)))
                  (>= x 0)
                  (integerp k)
                  (< x (* 2 (acl2-pi)))
                  (equal (* n angle)
                         (+ (* 2 (acl2-pi) k) x)))
             (and (>= k 0)
                  (< k (- n (/ x (* 2 (acl2-pi))))))))
  )









































---------------------------
(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd realnum-equiv
    (implies (and (realp r)
                  (realp x)
                  (> x 0))
             (equal (+ (* x (/ (- r (mod r x)) x)) (mod r x))
                    r))))

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd r-theta*p=p=>theta=2kpi
    (implies (and (point-in-r3 p)
                  (point-in-r3 u)
                  (realp angle)
                  (or (not (equal (point-in-r3-x1 p)
                                  (point-in-r3-x1 u)))
                      (not (equal (point-in-r3-x1 p)
                                  (point-in-r3-x1 u)))
                      (not (equal (point-in-r3-x1 p)
                                  (point-in-r3-x1 u))))
                  (or (not (equal (point-in-r3-x1 p)
                                  (- (point-in-r3-x1 u))))
                      (not (equal (point-in-r3-x1 p)
                                  (- (point-in-r3-x1 u))))
                      (not (equal (point-in-r3-x1 p)
                                  (- (point-in-r3-x1 u)))))
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
             (equal (* 2 (acl2-pi) (/ (- angle (mod angle (* 2 (acl2-pi)))) (* 2 (acl2-pi))))
                    angle))
    :hints (("Goal"
             :use ((:instance realnum-equiv (r angle) (x (* 2 (acl2-pi))))
                   (:instance integerp-r-mod-r-x/x (r angle) (x (* 2 (acl2-pi))))
                   (:instance range-mod-r-x (r angle) (x (* 2 (acl2-pi))))
                   (:instance rotation-angle=2pik
                              (k (/ (- angle (mod angle (* 2 (acl2-pi)))) (* 2 (acl2-pi))))
                              (u u)
                              (x (mod angle (* 2 (acl2-pi)))))
                   (:instance r-theta*p=p=>sine=0 (p p) (u u) (angle (mod angle (* 2 (acl2-pi)))))
                   (:instance r-theta*p=p=>cosine=1 (p p) (u u) (angle (mod angle (* 2 (acl2-pi)))))
                   (:instance sin=0-cos=1 (x (mod angle (* 2 (acl2-pi))))))
             :in-theory (e/d () (rotation-about-witness point-in-r3 point-in-r3-x1 point-in-r3-y1 point-in-r3-z1 aref2 m-= mod))
             )))
  )

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd r-theta1*p=r-theta2*p=>r-theta1-theta2*p=p
    (implies (and (realp angle1)
                  (realp angle2)
                  (point-in-r3 u)
                  (point-in-r3 p)
                  (equal (+ (* (point-in-r3-x1 u) (point-in-r3-x1 u))
                            (* (point-in-r3-y1 u) (point-in-r3-y1 u))
                            (* (point-in-r3-z1 u) (point-in-r3-z1 u)))
                         1)
                  (m-= (m-* (rotation-about-witness angle1 u) p)
                       (m-* (rotation-about-witness angle2 u) p)))
             (m-= (m-* (rotation-about-witness (- angle1 angle2) u) p)
                  p))
    :hints (("Goal"
             :use ((:instance r-t1*r-t2=r-t1+t2 (angle1 (- angle2)) (angle2 angle1) (u u))
                   (:instance r-t1*r-t2=r-t1+t2 (angle1 (- angle2)) (angle2 angle2) (u u))
                   (:instance r-theta*p=p=>r--theta*p=p-1
                              (m1 (m-* (rotation-about-witness angle1 u) p))
                              (m2 (m-* (rotation-about-witness angle2 u) p))
                              (m3 (m-* (rotation-about-witness (- angle2) u) p)))
                   (:instance r-theta*p=p=>r--theta*p=p-2
                              (m1 (rotation-about-witness (- angle2) u))
                              (m2 (rotation-about-witness angle1 u))
                              (m3 p)
                              (m4 (rotation-about-witness (- angle2) u))
                              (m5 (m-* (rotation-about-witness angle2 u) p)))
                   (:instance rotation-a-witn-of0 (p p) (u u)))
             :in-theory (e/d () (aref2 m-= m-* rotation-about-witness point-in-r3 point-in-r3-x1 point-in-r3-y1 point-in-r3-z1))
             ))
    )
  )

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
           )))

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd diff-d-p-p=>d-p-p1
    (implies (and (d-p p)
                  (point-in-r3 p1)
                  (m-= p p1))
             (d-p p1))
    :hints (("goal"
             :use ((:instance d-p (point p1))
                   (:instance word-exists-suff (w (word-exists-witness p)) (point p1))
                   (:instance d-p-p=>d-p-p1-lemma (m1 (rotation (word-exists-witness p) (acl2-sqrt 2)))
                              (m2 p) (m3 p1))
                   (:instance s2-def-p-p=>p1 (p p) (p1 p1)))

             :in-theory (e/d () (m-* acl2-sqrt reducedwordp rotation r3-rotationp acl2-sqrt word-exists-suff d-p))
             )))
  )

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd d-p-not-equal-to-u-n-u
    (implies (and (d-p p)
                  (point-in-r3 u)
                  (not (d-p u))
                  (point-in-r3 m-u)
                  (equal (aref2 :fake-name m-u 0 0)
                         (- (aref2 :fake-name u 0 0)))
                  (equal (aref2 :fake-name m-u 1 0)
                         (- (aref2 :fake-name u 1 0)))
                  (equal (aref2 :fake-name m-u 2 0)
                         (- (aref2 :fake-name u 2 0)))
                  )
             (and (not (m-= p u))
                  (not (m-= p m-u))))
    :hints (("Goal"
             :use ((:instance diff-d-p-p=>d-p-p1 (p p) (p1 u))
                   (:instance diff-d-p-p=>d-p-p1 (p p) (p1 m-u))
                   (:instance d-p=>d-p-p (p1 m-u) (p2 u)))
             :in-theory (e/d () (m-* acl2-sqrt reducedwordp rotation r3-rotationp acl2-sqrt word-exists-suff d-p))
             )))
  )
























































------------------------

(defthmd cos2pik+x
  (implies (integerp k)
           (equal (acl2-cosine (+ (* 2 (acl2-pi) k) x))
                  (acl2-cosine x)))
  :hints (("Goal"
           :use ((:instance cos-2npi (n k)))
           :in-theory (disable SINE-2X)
           )))

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd sin2pik+x
    (implies (integerp k)
             (equal (acl2-sine (+ (* 2 (acl2-pi) k) x))
                    (acl2-sine x)))
    :hints (("Goal"
             :use ((:instance sin-2npi (n k))
                   (:instance cos-2npi (n k)))
             :in-theory (disable sin-2npi COSINE-2X sine-2x)
             )))
  )


(defthmd rotation-a-witn-of0
  (implies (and (point-in-r3 p)
                (point-in-r3 u))
           (m-= (m-* (rotation-about-witness 0 u) p)
                p))
  :hints (("Goal"
           :use ((:instance m-*point-id=point (p1 p))
                 (:instance r-theta-0=id (u u)))
           :in-theory (e/d () (ASSOCIATIVITY-OF-M-* m-* aref2 rotation-about-witness point-in-r3-x1 point-in-r3-y1 point-in-r3-z1 id-rotation point-in-r3 (:EXECUTABLE-COUNTERPART ID-ROTATION)))
           )))

(defthmd rotation-angle=2pik
  (implies (and (integerp k)
                (point-in-r3 u))
           (equal (rotation-about-witness (+ (* 2 (acl2-pi) k) x) u)
                  (rotation-about-witness x u)))
  :hints (("Goal"
           :use ((:instance cos2pik+x (k k) (x x))
                 (:instance sin2pik+x (k k) (x x))
                 )
           )))

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd integerp-r-mod-r-x/x
    (implies (and (realp r)
                  (not (equal x 0))
                  (realp x))
             (integerp (/ (- r (mod r x)) x))))
  )

(encapsulate
  ()
  (local (include-book "workshops/1999/embedded/Exercises/Exercise1-2/Exercise1.2" :dir :system))
  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd range-mod-r-x
    (implies (and (realp r)
                  (realp x)
                  (> x 0))
             (and (>= (mod r x) 0)
                  (realp (mod r x))
                  (< (mod r x) x)))
    :hints (("Goal"
             :in-theory (enable mod floor1)
             )))
  )


----

  (defthmd test-2002
    (implies (and (realp r)
;(>= r 0)
                  (realp x)
;(not (equal x 0)))
                  (< x 0))
             (and (>= (mod r x) 0)
                  (realp (mod r x))))
                  ;(< (mod r x) (- x))))
    :hints (("Goal"
             :in-theory (enable mod floor1)
             )))
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

  (local (include-book "arithmetic-5/top" :dir :system))
  ;(local (include-book "workshops/1999/embedded/Exercises/Exercise1-2/Exercise1.2" :dir :system))

  (defthmd integerp-r-mod-r-x/x
    (implies (and (realp r)
                  (not (equal x 0))
                  (realp x))
             (integerp (/ (- r (mod r x)) x))))

  (local (include-book "workshops/1999/embedded/Exercises/Exercise1-2/Exercise1.2" :dir :system))

  (defthmd range-mod-r-x
    (implies (and (realp r)
                  (realp x)
                  (> x 0))
             (and (>= (mod r x) 0)
                  (< (mod r x) x)))
    :hints (("Goal"
             :in-theory (enable mod floor1)
             )))
  )











































-------------------------------------------------

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

(defthmd r-theta*p=p=>sine=0
  (implies (and (point-in-r3 p)
                (point-in-r3 u)
                (realp angle)
                (or (not (equal (point-in-r3-x1 p)
                                (point-in-r3-x1 u)))
                    (not (equal (point-in-r3-x1 p)
                                (point-in-r3-x1 u)))
                    (not (equal (point-in-r3-x1 p)
                                (point-in-r3-x1 u))))
                (or (not (equal (point-in-r3-x1 p)
                                (- (point-in-r3-x1 u))))
                    (not (equal (point-in-r3-x1 p)
                                (- (point-in-r3-x1 u))))
                    (not (equal (point-in-r3-x1 p)
                                (- (point-in-r3-x1 u)))))
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
           :use ((:instance r-theta*p=p=>r--theta*p=p (p p) (u u) (angle angle))
                 (:instance r-theta*p=p-lemma1 (p p) (u u) (angle angle))
                 (:instance r-theta*p=p-lemma2 (p p) (u u) (angle angle))
                 (:instance sine-p2=0-lemma
                            (x (point-in-r3-x1 u))
                            (z (point-in-r3-z1 u))
                            (s (acl2-sine angle))
                            (p2 (point-in-r3-y1 p)))
                 (:instance sine-p2=0-lemma-1
                            (x (point-in-r3-x1 u))
                            (z (point-in-r3-z1 u))
                            (s (acl2-sine angle))
                            (p2 (point-in-r3-y1 p)))
                 (:instance sine-p2=0-lemma-2
                            (x (point-in-r3-x1 u))
                            (z (point-in-r3-z1 u))
                            (s (acl2-sine angle))
                            (p1 (point-in-r3-x1 p))
                            (p3 (point-in-r3-z1 p)))
                 (:instance sine-p2=0-lemma-4
                            (x (point-in-r3-x1 u))
                            (y (point-in-r3-y1 u))
                            (z (point-in-r3-z1 u))
                            (p1 (point-in-r3-x1 p))
                            (p2 (point-in-r3-y1 p))
                            (p3 (point-in-r3-z1 p)))
                 )
           :in-theory (disable aref2 m-= m-* r3-rotationp rotation-about-witness r3-matrixp)
           )))

(encapsulate
  ()

  (local (include-book "arithmetic/top" :dir :system))

  (defthmd r-theta*p=p=>cosine=1-lemma1
    (implies (and (point-in-r3 p)
                  (point-in-r3 u)
                  (realp angle)
                  (equal (point-in-r3-y1 u) 0)
                  (m-= (m-* (rotation-about-witness angle u) p) p)
                  (equal (acl2-sine angle) 0))
             (or (equal (acl2-cosine angle) 1)
                 (equal (point-in-r3-y1 p) 0)))
    :hints (("Goal"
             :use ((:instance m-=p1p2-implies
                              (p1 (m-* (rotation-about-witness angle u) p))
                              (p2 p))
                   (:instance r-theta*p=p-lemma2-1 (u u) (p p) (angle angle))
                   (:instance r-theta*p=p-lemma1-1 (m (rotation-about-witness angle u)) (p p))
                   (:instance r3-rotationp-r-theta-10 (angle angle) (p u))
                   (:instance r-theta*p=p-lemma1-2 (angle angle) (u u))
                   (:instance r-theta*p=p-lemma1-3 (u u) (p p) (angle angle))
                   )
             :in-theory (e/d () (m-= alist2p array2p m-* rotation-about-witness aref2-m-* aref2))
             )))

  (defthmd r-theta*p=p=>cosine=1-lemma2-1
    (implies (equal (- 1 (* x x)) (* z z))
             (equal (- (* 2 p1) (* 2 p1 x x))
                    (* 2 p1 z z))))

  (defthmd r-theta*p=p=>cosine=1-lemma2-2
    (implies (and (realp p1)
                  (realp p3)
                  (realp x)
                  (realp z)
                  (equal (+ (* x x) (* z z)) 1)
                  (equal (- (* 2 p1) (* 2 p1 x x))
                         (* 2 x p3 z)))
             (equal (* p1 z z) (* x p3 z)))
    :hints (("Goal"
             :use ((:instance r-theta*p=p=>cosine=1-lemma2-1 (p1 p1) (x x)))
             )))
  )

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd r-theta*p=p=>cosine=1-lemma2
    (implies (and (point-in-r3 p)
                  (point-in-r3 u)
                  (realp angle)
                  (equal (+ (* (point-in-r3-x1 u) (point-in-r3-x1 u))
                            (* (point-in-r3-y1 u) (point-in-r3-y1 u))
                            (* (point-in-r3-z1 u) (point-in-r3-z1 u)))
                         1)
                  (equal (point-in-r3-y1 u) 0)
                  (equal (point-in-r3-y1 p) 0)
                  (equal (acl2-cosine angle) -1)
                  (m-= (m-* (rotation-about-witness angle u) p) p)
                  (equal (acl2-sine angle) 0))
             (equal (* (point-in-r3-x1 p) (point-in-r3-z1 u) (point-in-r3-z1 u))
                    (* (point-in-r3-z1 p) (point-in-r3-x1 u) (point-in-r3-z1 u))))
    :hints (("Goal"
             :use ((:instance m-=p1p2-implies
                              (p1 (m-* (rotation-about-witness angle u) p))
                              (p2 p))
                   (:instance r-theta*p=p-lemma1-4 (u u) (p p) (angle angle))
                   (:instance r-theta*p=p-lemma1-1 (m (rotation-about-witness angle u)) (p p))
                   (:instance r3-rotationp-r-theta-10 (angle angle) (p u))
                   (:instance r-theta*p=p-lemma1-2 (angle angle) (u u))
                   (:instance r-theta*p=p-lemma1-3 (u u) (p p) (angle angle))
                   (:instance r-theta*p=p=>cosine=1-lemma2-2
                              (p1 (point-in-r3-x1 p))
                              (p3 (point-in-r3-z1 p))
                              (x (point-in-r3-x1 u))
                              (z (point-in-r3-z1 u)))
                   )
             :in-theory (e/d () (m-= alist2p array2p m-* rotation-about-witness aref2-m-* aref2))
             )))
  )

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd r-theta*p=p=>cosine=1-lemma3
    (implies (and (point-in-r3 p)
                  (point-in-r3 u)
                  (realp angle)
                  (equal (+ (* (point-in-r3-x1 u) (point-in-r3-x1 u))
                            (* (point-in-r3-y1 u) (point-in-r3-y1 u))
                            (* (point-in-r3-z1 u) (point-in-r3-z1 u)))
                         1)
                  (equal (point-in-r3-y1 u) 0)
                  (equal (point-in-r3-y1 p) 0)
                  (equal (acl2-cosine angle) -1)
                  (m-= (m-* (rotation-about-witness angle u) p) p)
                  (equal (acl2-sine angle) 0))
             (equal (* (point-in-r3-z1 p) (point-in-r3-x1 u) (point-in-r3-x1 u))
                    (* (point-in-r3-x1 p) (point-in-r3-z1 u) (point-in-r3-x1 u))))
    :hints (("Goal"
             :use ((:instance m-=p1p2-implies
                              (p1 (m-* (rotation-about-witness angle u) p))
                              (p2 p))
                   (:instance r-theta*p=p-lemma1-5 (u u) (p p) (angle angle))
                   (:instance r-theta*p=p-lemma1-1 (m (rotation-about-witness angle u)) (p p))
                   (:instance r3-rotationp-r-theta-10 (angle angle) (p u))
                   (:instance r-theta*p=p-lemma1-2 (angle angle) (u u))
                   (:instance r-theta*p=p-lemma1-3 (u u) (p p) (angle angle))
                   (:instance r-theta*p=p=>cosine=1-lemma2-2
                              (p3 (point-in-r3-x1 p))
                              (p1 (point-in-r3-z1 p))
                              (z (point-in-r3-x1 u))
                              (x (point-in-r3-z1 u)))
                   )
             :in-theory (e/d () (m-= alist2p array2p m-* rotation-about-witness aref2-m-* aref2))
             )))
  )

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd r-theta*p=p=>cosine=1-lemma4
    (implies (and (point-in-r3 p)
                  (point-in-r3 u)
                  (realp angle)
                  (equal (+ (* (point-in-r3-x1 u) (point-in-r3-x1 u))
                            (* (point-in-r3-y1 u) (point-in-r3-y1 u))
                            (* (point-in-r3-z1 u) (point-in-r3-z1 u)))
                         1)
                  (equal (+ (* (point-in-r3-x1 p) (point-in-r3-x1 p))
                            (* (point-in-r3-y1 p) (point-in-r3-y1 p))
                            (* (point-in-r3-z1 p) (point-in-r3-z1 p)))
                         1)
                  (or (not (equal (point-in-r3-x1 p)
                                  (point-in-r3-x1 u)))
                      (not (equal (point-in-r3-x1 p)
                                  (point-in-r3-x1 u)))
                      (not (equal (point-in-r3-x1 p)
                                  (point-in-r3-x1 u))))
                  (or (not (equal (point-in-r3-x1 p)
                                  (- (point-in-r3-x1 u))))
                      (not (equal (point-in-r3-x1 p)
                                  (- (point-in-r3-x1 u))))
                      (not (equal (point-in-r3-x1 p)
                                  (- (point-in-r3-x1 u)))))
                  (equal (* (point-in-r3-x1 p) (point-in-r3-z1 u) (point-in-r3-z1 u))
                         (* (point-in-r3-z1 p) (point-in-r3-x1 u) (point-in-r3-z1 u)))
                  (equal (* (point-in-r3-z1 p) (point-in-r3-x1 u) (point-in-r3-x1 u))
                         (* (point-in-r3-x1 p) (point-in-r3-z1 u) (point-in-r3-x1 u)))
                  (equal (point-in-r3-y1 u) 0)
                  (equal (point-in-r3-y1 p) 0))
             (and (not (equal (point-in-r3-z1 u) 0))
                  (not (equal (point-in-r3-x1 u) 0))))
    :hints (("Goal"
             :use ((:instance sine-p2=0-lemma-4-5
                              (x (point-in-r3-x1 u))
                              (p1 (point-in-r3-x1 p)))
                   (:instance sine-p2=0-lemma-4-5
                              (x (point-in-r3-z1 u))
                              (p1 (point-in-r3-z1 p)))
                   )
             )))
  )

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd r-theta*p=p=>cosine=1-lemma5
    (implies (and (point-in-r3 p)
                  (point-in-r3 u)
                  (realp angle)
                  (equal (+ (* (point-in-r3-x1 u) (point-in-r3-x1 u))
                            (* (point-in-r3-y1 u) (point-in-r3-y1 u))
                            (* (point-in-r3-z1 u) (point-in-r3-z1 u)))
                         1)
                  (equal (+ (* (point-in-r3-x1 p) (point-in-r3-x1 p))
                            (* (point-in-r3-y1 p) (point-in-r3-y1 p))
                            (* (point-in-r3-z1 p) (point-in-r3-z1 p)))
                         1)
                  (or (not (equal (point-in-r3-x1 p)
                                  (point-in-r3-x1 u)))
                      (not (equal (point-in-r3-x1 p)
                                  (point-in-r3-x1 u)))
                      (not (equal (point-in-r3-x1 p)
                                  (point-in-r3-x1 u))))
                  (or (not (equal (point-in-r3-x1 p)
                                  (- (point-in-r3-x1 u))))
                      (not (equal (point-in-r3-x1 p)
                                  (- (point-in-r3-x1 u))))
                      (not (equal (point-in-r3-x1 p)
                                  (- (point-in-r3-x1 u)))))
                  (equal (* (point-in-r3-x1 p) (point-in-r3-z1 u) (point-in-r3-z1 u))
                         (* (point-in-r3-z1 p) (point-in-r3-x1 u) (point-in-r3-z1 u)))
                  (equal (* (point-in-r3-z1 p) (point-in-r3-x1 u) (point-in-r3-x1 u))
                         (* (point-in-r3-x1 p) (point-in-r3-z1 u) (point-in-r3-x1 u)))
                  (equal (point-in-r3-y1 u) 0)
                  (equal (point-in-r3-y1 p) 0))
             (equal (* (point-in-r3-z1 u) (point-in-r3-x1 p))
                    (* (point-in-r3-x1 u) (point-in-r3-z1 p))))
    :hints (("Goal"
             :use (:instance r-theta*p=p=>cosine=1-lemma4 (p p) (u u))
             ))))

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))
  (defthmd r-theta*p=p=>cosine=1-1
    (implies (and (realp angle)
                  (equal (acl2-sine angle) 0))
             (or (equal (acl2-cosine angle) 1)
                 (equal (acl2-cosine angle) -1)))
    :hints (("Goal"
             :use ((:instance sin**2+cos**2 (x angle))
                   (:instance sine-p2=0-lemma-4-5 (p1 (acl2-cosine angle)) (x 1)))
             :in-theory (disable sin**2+cos**2)
             )))
  )


(defthmd r-theta*p=p=>cosine=1
  (implies (and (point-in-r3 p)
                (point-in-r3 u)
                (realp angle)
                (or (not (equal (point-in-r3-x1 p)
                                (point-in-r3-x1 u)))
                    (not (equal (point-in-r3-x1 p)
                                (point-in-r3-x1 u)))
                    (not (equal (point-in-r3-x1 p)
                                (point-in-r3-x1 u))))
                (or (not (equal (point-in-r3-x1 p)
                                (- (point-in-r3-x1 u))))
                    (not (equal (point-in-r3-x1 p)
                                (- (point-in-r3-x1 u))))
                    (not (equal (point-in-r3-x1 p)
                                (- (point-in-r3-x1 u)))))
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
           (equal (acl2-cosine angle) 1))
  :hints (("Goal"
           :use ((:instance r-theta*p=p=>sine=0 (p p) (u u))
                 (:instance r-theta*p=p=>cosine=1-lemma1 (p p) (u u))
                 (:instance r-theta*p=p=>cosine=1-lemma2 (p p) (u u))
                 (:instance r-theta*p=p=>cosine=1-lemma3 (p p) (u u))
                 (:instance r-theta*p=p=>cosine=1-lemma5 (p p) (u u))
                 (:instance r-theta*p=p=>cosine=1-1 (angle angle))
                 (:instance sine-p2=0-lemma-4
                            (x (point-in-r3-x1 u))
                            (y (point-in-r3-y1 u))
                            (z (point-in-r3-z1 u))
                            (p1 (point-in-r3-x1 p))
                            (p2 (point-in-r3-y1 p))
                            (p3 (point-in-r3-z1 p)))
                 )
           :in-theory (disable aref2 m-= m-* r3-rotationp rotation-about-witness r3-matrixp)
           )))

;;;;sin t = 0, cos t =1 => t=0 if t in [0,2*pi)


(defthmd sine-is-0-in-0<2pi=>x=0orpi-1
  (implies (and (realp x)
                (< 0 x)
                (< x (acl2-pi)))
           (> (acl2-sine x) 0))
  :hints (("Goal"
           :use ((:instance sine-positive-in-0-pi/2 (x x))
                 (:instance sine-positive-in-pi/2-pi (x x)))
           )))

;;is this true?

(defthmd sine-is-0-in-0<2pi=>x=0orpi-2
  (implies (and (realp x)
                (<= 0 x)
                (< x (acl2-pi))
                (equal (acl2-sine x) 0))
           (equal (* x x) 0))
  :hints (("Goal"
           :use ((:instance sine-is-0-in-0<2pi=>x=0orpi-1 (x x)))
           )))

(defthmd sine-is-0-in-0<2pi=>x=0orpi-3
  (implies (and (realp x)
                (< (acl2-pi) x)
                (< x (* 2 (acl2-pi))))
           (< (acl2-sine x) 0))
  :hints (("Goal"
           :use ((:instance sine-negative-in-pi-3pi/2 (x x))
                 (:instance sine-negative-in-3pi/2-2pi (x x)))
           )))

;;is this true?

(defthmd sine-is-0-in-0<2pi=>x=0orpi-4
  (implies (and (realp x)
                (<= (acl2-pi) x)
                (equal (acl2-sine x) 0)
                (< x (* 2 (acl2-pi))))
           (equal (* x x) (* (acl2-pi) (acl2-pi))))
  :hints (("Goal"
           :use ((:instance sine-is-0-in-0<2pi=>x=0orpi-3 (x x)))
           ))
  )

(defthmd sine-is-0-in-0<2pi=>x=0orpi-5
  (implies (and (realp x)
                (<= 0 x)
                (equal (acl2-sine x) 0)
                (< x (* 2 (acl2-pi))))
           (or (equal (* x x) 0)
               (equal (* x x) (* (acl2-pi) (acl2-pi)))))
  :hints (("Goal"
           :use ((:instance sine-is-0-in-0<2pi=>x=0orpi-2)
                 (:instance sine-is-0-in-0<2pi=>x=0orpi-4))
           )))

(encapsulate
  ()

  (local (include-book "nonstd/nsa/inverse-trig" :dir :system))

  (defthmd cosine-is-1-in-0<2pi=>x=0-1
    (implies (and (realp x)
                  (<= 0 x)
                  (equal (acl2-cosine x) 1)
                  (<= x (acl2-pi)))
             (equal (* x x) 0))
    :hints (("Goal"
             :cases ((equal x 0)
                     (not (equal x 0)))
             :use ((:instance cosine-positive-in-0-pi/2 (x x))
                   (:instance cosine-pi/2)
                   (:instance cosine-pi)
                   (:instance cosine-negative-in-pi/2-pi (x x)))
             )
            ("Subgoal 1"
             :use ((:instance cosine-is-1-1-on-domain (x1 0) (x2 x)))
             :in-theory (enable inside-interval-p)
             ))
    )

  (defthmd cosine-is-1-in-0<2pi=>x=0-5
    (implies (and (realp x)
                  (>= (acl2-pi) x)
                  (>= x 0)
                  (equal (acl2-cosine x) -1))
             (equal (* x x) (* (acl2-pi) (acl2-pi))))
    :hints (("Goal"
             :cases ((equal x (acl2-pi))
                     (not (equal x (acl2-pi))))
             )
            ("subgoal 1"
             :use ((:instance cosine-is-1-1-on-domain (x1 (acl2-pi)) (x2 x))
                   (:instance cosine-pi))
             :in-theory (e/d (inside-interval-p) (cosine-pi))
             )

            ))
  )

(encapsulate
  ()
  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd cosine-is-1-in-0<2pi=>x=0-2
    (implies (and (realp r)
                  (> r x)
                  (realp x)
                  (>= r 0)
                  (< r (* 2 x)))
             (equal (mod r x) (- r x))))

  (defthmd cosine-is-1-in-0<2pi=>x=0-3
    (implies (and (realp r)
                  (> r x)
                  (realp x)
                  (>= r 0)
                  (< r (* 2 x)))
             (and (equal (+ x (mod r x)) r)
                  (> (mod r x) 0)
                  (< (mod r x) x))))

  (defthmd cosine-is-1-in-0<2pi=>x=0-4
    (implies (and (realp x)
                  (< (acl2-pi) x)
                  (< x (* 2 (acl2-pi))))
             (equal (acl2-cosine x)
                    (- (acl2-cosine (mod x (acl2-pi))))))
    :hints (("Goal"
             :use ((:instance cosine-is-1-in-0<2pi=>x=0-3
                              (r x) (x (acl2-pi)))
                   (:instance cos-pi+x (x (mod x (acl2-pi)))))
             ))
    )

  (defthmd cosine-is-1-in-0<2pi=>x=0-6
    (implies (and (realp x)
                  (>= x 0)
                  (< x (* 2 (acl2-pi)))
                  (equal (acl2-cosine x) 1))
             (equal (* x x) 0))
    :hints (("Goal"
             :use ((:instance cosine-is-1-in-0<2pi=>x=0-1 (x x))
                   (:instance cosine-is-1-in-0<2pi=>x=0-4 (x x))
                   (:instance cosine-is-1-in-0<2pi=>x=0-3 (r x) (x (acl2-pi)))
                   (:instance cosine-is-1-in-0<2pi=>x=0-5 (x (mod x (acl2-pi))))
                   )
             )))
  )

(defthmd sin=0-cos=1
  (implies (and (realp x)
                (>= x 0)
                (< x (* 2 (acl2-pi)))
                (equal (acl2-sine x) 0)
                (equal (acl2-cosine x) 1))
           (equal (* x x) 0))
  :hints (("Goal"
           :use ((:instance sine-is-0-in-0<2pi=>x=0orpi-5 (x x))
                 (:instance cosine-is-1-in-0<2pi=>x=0-6 (x x)))
           )))

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd cos-2npi-n>=0-1
    (implies (and (integerp n)
                  (EQUAL (ACL2-COSINE (+ (* 2 (ACL2-PI))
                                         (* 2 (ACL2-PI) (+ N -1))))
                         1))
             (EQUAL (ACL2-COSINE (* 2 (ACL2-PI) N)) 1))
    :hints (("Goal"
             :in-theory (disable COSINE-OF-SUMS COS-2PI+X COSINE-2X)
             ))))

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (local
   (defun induction-hint (n)
     (if (and (integerp n)
              (< 0 n))
         (1+ (induction-hint (+ n -1)))
       1)))

  (local
   (defthm *-x-0
     (equal (* x 0) 0)))

  (local
   (defthm cos-2npi-n>=0
     (implies (and (integerp n)
                   (<= 0 n))
              (equal (acl2-cosine (* 2 (acl2-pi) n))
                     1))
     :hints (("Goal"
              :induct (induction-hint n))
             ("Subgoal *1/1"
              :use ((:instance cos-2pi+x (x (* 2 (ACL2-PI) (+ N -1))))
                    (:instance cos-2npi-n>=0-1 (n n)))
              :in-theory nil
              ))))

  (defthm cos-2npi
    (implies (integerp n)
             (equal (acl2-cosine (* 2 (acl2-pi) n))
                    1))
    :hints (("Goal"
             :cases ((< n 0)
                     (= n 0)
                     (> n 0)))
            ("Subgoal 3"
             :use ((:instance cos-uminus
                              (x (* 2 (acl2-pi) n)))
                   (:instance cos-2npi-n>=0 (n (- n))))
             :in-theory (disable cos-uminus cos-2npi-n>=0 COSINE-2X))))

  )












-------------
;;is this true?

(defthmd sine-is-0-in-0<2pi=>x=0orpi-2
  (implies (and (realp x)
                (<= 0 x)
                (< x (acl2-pi))
                (equal (acl2-sine x) 0))
           (equal (* x x) 0))
  :hints (("Goal"
           :cases ((equal x 0)
                   (not (equal x 0)))
           :use ((:instance sine-is-0-in-0<2pi=>x=0orpi-1 (x x)))
           )))

(defthmd sine-is-0-in-0<2pi=>x=0orpi-3
  (implies (and (realp x)
                (< (acl2-pi) x)
                (< x (* 2 (acl2-pi))))
           (< (acl2-sine x) 0))
  :hints (("Goal"
           :use ((:instance sine-negative-in-pi-3pi/2 (x x))
                 (:instance sine-negative-in-3pi/2-2pi (x x)))
           )))

;;is this true?

(defthmd sine-is-0-in-0<2pi=>x=0orpi-4
  (implies (and (realp x)
                (<= (acl2-pi) x)
                (equal (acl2-sine x) 0)
                (< x (* 2 (acl2-pi))))
           (equal (* x x) (* (acl2-pi) (acl2-pi))))
  :hints (("Goal"
           :use ((:instance sine-is-0-in-0<2pi=>x=0orpi-3 (x x)))
                 ;(:instance sine-negative-in-3pi/2-2pi (x x)))
           ))
  ;:rule-classes nil
  )

(defthmd sine-is-0-in-0<2pi=>x=0orpi-5
  (implies (and (realp x)
                (<= 0 x)
                (equal (acl2-sine x) 0)
                (< x (* 2 (acl2-pi))))
           (or (equal (* x x) 0)
               (equal (* x x) (* (acl2-pi) (acl2-pi)))))
  :hints (("Goal"
           :use ((:instance sine-is-0-in-0<2pi=>x=0orpi-2)
                 (:instance sine-is-0-in-0<2pi=>x=0orpi-4))
           )))

-----

(encapsulate
  ()

  (local (include-book "arithmetic/top" :dir :system))

  (defthmd cosine-is-1-in-0<2pi=>x=0-1
    (implies (and (realp x)
                  (equal (acl2-cosine x) 1)
                  (<= 0 x)
                  (< x (* 2 (acl2-pi))))
             (equal (* x x) 0))
    :hints (("Goal"
             ;; :cases ((and (> x 0) (< x (* 1/2 (acl2-pi))))
             ;;         (and (> x (* 1/2 (acl2-pi))) (< x (acl2-pi)))
             ;;         (and (> x (* 3/2 (acl2-pi))) (< x (* 2 (acl2-pi))))
             ;;         (and (> x (acl2-pi)) (< x (* 3/2 (acl2-pi))))
             ;;         (equal x 0)
             ;;         (equal x (* 1/2 (acl2-pi)))
             ;;         (equal x (* 3/2 (acl2-pi))))
             :use ((:instance cosine-positive-in-0-pi/2 (x x))
                   (:instance cosine-positive-in-3pi/2-2pi (x x))
                   (:instance cosine-negative-in-pi/2-pi (x x))
                   (:instance cosine-0)
                   (:instance cosine-pi/2)
                   (:instance cosine-3pi/2)
                   (:instance cosine-negative-in-pi/2-pi (x x)))
             :in-theory (disable cosine-positive-in-0-pi/2 cosine-positive-in-3pi/2-2pi cosine-negative-in-pi/2-pi cosine-0 cosine-pi/2 cosine-3pi/2 cosine-negative-in-pi/2-pi)
             )
            ("Subgoal 2"
             :cases ((equal x (* 1/2 (acl2-pi)))
                     (equal x 0))
             :use ((:instance cosine-positive-in-0-pi/2 (x x))
                   (:instance cosine-0)
                   (:instance cosine-pi/2))
             )
            ))
  )

;;is this true?

(defthmd sine-is-0-in-0<pi=>x=0orpi-2
  (implies (and (realp x)
                (<= 0 x)
                (< x (acl2-pi))
                (equal (acl2-sine x) 0))
           (equal (* x x) 0))
  :hints (("Goal"
           :use ((:instance sine-is-0-in-0<pi=>x=0orpi-1 (x x)))
           )))

(defthmd sine-is-0-in-0<pi=>x=0orpi-3
  (implies (and (realp x)
                (< (acl2-pi) x)
                (< x (* 2 (acl2-pi))))
           (< (acl2-sine x) 0))
  :hints (("Goal"
           :use ((:instance sine-negative-in-pi-3pi/2 (x x))
                 (:instance sine-negative-in-3pi/2-2pi (x x)))
           )))

;;is this true?

(defthmd sine-is-0-in-0<pi=>x=0orpi-4
  (implies (and (realp x)
                (<= (acl2-pi) x)
                (equal (acl2-sine x) 0)
                (< x (* 2 (acl2-pi))))
           (equal (* x x) (* (acl2-pi) (acl2-pi))))
  :hints (("Goal"
           :use ((:instance sine-is-0-in-0<pi=>x=0orpi-3 (x x)))
                 ;(:instance sine-negative-in-3pi/2-2pi (x x)))
           ))
  ;:rule-classes nil
  )

(defthmd sine-is-0-in-0<pi=>x=0orpi-5
  (implies (and (realp x)
                (<= 0 x)
                (equal (acl2-sine x) 0)
                (< x (* 2 (acl2-pi))))
           (or (equal (* x x) 0)
               (equal (* x x) (* (acl2-pi) (acl2-pi)))))
  :hints (("Goal"
           :use ((:instance sine-is-0-in-0<pi=>x=0orpi-2)
                 (:instance sine-is-0-in-0<pi=>x=0orpi-4))
           )))


----






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
