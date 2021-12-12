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

(include-book "nonstd/nsa/trig" :dir :system)
(include-book "hausdorff-paradox-2")

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

(defthmd rotation-about-witness-values
  (and (equal (aref2 :fake-name (rotation-about-witness angle point) 0 0)
              (+ (acl2-cosine angle)
                 (* (point-in-r3-x1 point) (point-in-r3-x1 point) (- 1 (acl2-cosine angle)))))
       (equal (aref2 :fake-name (rotation-about-witness angle point) 0 1)
              (- (* (point-in-r3-x1 point) (point-in-r3-y1 point) (- 1 (acl2-cosine angle)))
                 (* (point-in-r3-z1 point) (acl2-sine angle))))
       (equal (aref2 :fake-name (rotation-about-witness angle point) 0 2)
              (+ (* (point-in-r3-x1 point) (point-in-r3-z1 point) (- 1 (acl2-cosine angle)))
                 (* (point-in-r3-y1 point) (acl2-sine angle))))
       (equal (aref2 :fake-name (rotation-about-witness angle point) 1 0)
              (+ (* (point-in-r3-y1 point) (point-in-r3-x1 point) (- 1 (acl2-cosine angle)))
                 (* (point-in-r3-z1 point) (acl2-sine angle))))
       (equal (aref2 :fake-name (rotation-about-witness angle point) 1 1)
              (+ (acl2-cosine angle)
                 (* (point-in-r3-y1 point) (point-in-r3-y1 point) (- 1 (acl2-cosine angle)))))
       (equal (aref2 :fake-name (rotation-about-witness angle point) 1 2)
              (- (* (point-in-r3-y1 point) (point-in-r3-z1 point) (- 1 (acl2-cosine angle)))
                 (* (point-in-r3-x1 point) (acl2-sine angle))))
       (equal (aref2 :fake-name (rotation-about-witness angle point) 2 0)
              (- (* (point-in-r3-z1 point) (point-in-r3-x1 point) (- 1 (acl2-cosine angle)))
                 (* (point-in-r3-y1 point) (acl2-sine angle))))
       (equal (aref2 :fake-name (rotation-about-witness angle point) 2 1)
              (+ (* (point-in-r3-z1 point) (point-in-r3-y1 point) (- 1 (acl2-cosine angle)))
                 (* (point-in-r3-x1 point) (acl2-sine angle))))
       (equal (aref2 :fake-name (rotation-about-witness angle point) 2 2)
              (+ (acl2-cosine angle)
                 (* (point-in-r3-z1 point) (point-in-r3-z1 point) (- 1 (acl2-cosine angle)))))
       )
  :hints (("Goal"
           :in-theory (enable aref2)
           ))
  )

(encapsulate
  ()

  (local (include-book "arithmetic/top" :dir :system))

  (defthmd r3-rotationp-r-theta-11-1-lemma1
    (iff (equal (+ (* s s) (* c c)) 1)
         (equal (* s s) (- 1 (* c c)))))

  (defthmd r3-rotationp-r-theta-11-1-lemma2
    (equal (- a (* a c)) (* a (- 1 c))))

  (defthmd r3-rotationp-r-theta-11-1-lemma3
    (equal (+ (* c a) (* b a))
           (+ (* a (+ b c)))))

  (defthmd r-t1*r-t2=r-t1+t2-m-*-00-lemma1
    (equal (+ (* d a) (* d b) (* d c))
           (* d (+ a b c))))

  (defthmd r-t1*r-t2=r-t1+t2-m-*-00-lemma2
    (iff (equal (+ (* x x) (* y y) (* z z)) 1)
         (equal (+ (* y y) (* z z)) (- 1 (* x x)))))

  (defthmd r3-rotationp-r-theta-11-1-lemma4
    (implies (point-in-r3 p)
             (and (realp (point-in-r3-x1 p))
                  (realp (point-in-r3-y1 p))
                  (realp (point-in-r3-z1 p)))))
  )

(defthmd witness-not-in-x-coord-sequence-1
  (and (realp (exists-in-interval-but-not-in-x-coord-sequence-witness -1 1))
       (realp (acl2-sqrt (- 1 (* (exists-in-interval-but-not-in-x-coord-sequence-witness -1 1)
                                 (exists-in-interval-but-not-in-x-coord-sequence-witness -1 1)))))
       (<= -1 (exists-in-interval-but-not-in-x-coord-sequence-witness -1 1))
       (<= (exists-in-interval-but-not-in-x-coord-sequence-witness -1 1) 1))
  :hints (("goal"
           :use ((:instance witness-not-in-x-coord-sequence)
                 (:instance exists-point-on-s2-not-d-2))
           )))

(defthmd r3-rotationp-r-theta-8
  (implies (realp angle)
           (and (realp (acl2-sine angle))
                (realp (acl2-cosine angle)))))

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd r3-rotationp-r-theta-10
    (implies (and (realp angle)
                  (point-in-r3 p))
             (r3-matrixp (rotation-about-witness angle p)))
    :hints (("Goal"
             :use ((:instance r3-rotationp-r-theta-8)
                   (:instance rotation-about-witness-values (angle angle) (point p)))
             :in-theory (e/d (header dimensions default array2p) (aref2))
             )))
  )

(encapsulate
  ()

  (local (include-book "arithmetic/top" :dir :system))

  (defthmd r-t1*r-t2=r-t1+t2-m-*-00
    (implies (and (realp c1)
                  (realp c2)
                  (realp x)
                  (realp y)
                  (realp z)
                  (realp s1)
                  (realp s2)
                  (equal m1-00 (+ c1 (* x x (- 1 c1))))
                  (equal m2-00 (+ c2 (* x x (- 1 c2))))
                  (equal m1-01 (- (* x y (- 1 c1)) (* z s1)))
                  (equal m2-10 (+ (* y x (- 1 c2)) (* z s2)))
                  (equal m1-02 (+ (* x z (- 1 c1)) (* y s1)))
                  (equal m2-20 (- (* z x (- 1 c2)) (* y s2)))
                  (equal m3-00 (+ cosc1c2 (* x x (- 1 cosc1c2))))
                  (equal cosc1c2 (- (* c1 c2) (* s1 s2)))
                  (equal sins1s2 (+ (* s1 c2) (* c1 s2)))
                  (equal (+ (* x x) (* y y) (* z z)) 1)
                  (equal (+ (* s1 s1) (* c1 c1)) 1)
                  (equal (+ (* s2 s2) (* c2 c2)) 1))
             (equal (+ (* m1-00 m2-00)
                       (* m1-01 m2-10)
                       (* m1-02 m2-20)
                       )
                    m3-00))
    :hints (("Goal"
             :use ((:instance r-t1*r-t2=r-t1+t2-m-*-00-lemma1
                              (d (- (* c1 x x)))
                              (a (* x x))
                              (b (* y y))
                              (c (* z z)))
                   (:instance r-t1*r-t2=r-t1+t2-m-*-00-lemma1
                              (d (- (* c2 x x)))
                              (a (* x x))
                              (b (* y y))
                              (c (* z z)))
                   (:instance r-t1*r-t2=r-t1+t2-m-*-00-lemma1
                              (d (* x x))
                              (a (* x x))
                              (b (* y y))
                              (c (* z z)))
                   (:instance r-t1*r-t2=r-t1+t2-m-*-00-lemma1
                              (d (* c1 c2 x x))
                              (a (* x x))
                              (b (* y y))
                              (c (* z z)))
                   (:instance r3-rotationp-r-theta-11-1-lemma3
                              (a (- (* s1 s2)))
                              (c (* y y))
                              (b (* z z)))
                   (:instance r-t1*r-t2=r-t1+t2-m-*-00-lemma2 (x x) (y y) (z z))
                   )
             )))

  (defthmd r-t1*r-t2=r-t1+t2-m-*-01
    (implies (and (realp c1)
                  (realp c2)
                  (realp x)
                  (realp y)
                  (realp z)
                  (realp s1)
                  (realp s2)
                  (equal m1-00 (+ c1 (* x x (- 1 c1))))
                  (equal m1-01 (- (* x y (- 1 c1)) (* z s1)))
                  (equal m1-02 (+ (* x z (- 1 c1)) (* y s1)))
                  (equal m2-01 (- (* x y (- 1 c2)) (* z s2)))
                  (equal m2-11 (+ c2 (* y y (- 1 c2))))
                  (equal m2-21 (+ (* z y (- 1 c2)) (* x s2)))
                  (equal m3-01 (- (* x y (- 1 cosc1c2)) (* z sins1s2)))
                  (equal cosc1c2 (- (* c1 c2) (* s1 s2)))
                  (equal sins1s2 (+ (* s1 c2) (* c1 s2)))
                  (equal (+ (* x x) (* y y) (* z z)) 1)
                  (equal (+ (* s1 s1) (* c1 c1)) 1)
                  (equal (+ (* s2 s2) (* c2 c2)) 1))
             (equal (+ (* m1-00 m2-01)
                       (* m1-01 m2-11)
                       (* m1-02 m2-21)
                       )
                    m3-01))
    :hints (("Goal"
             :use ((:instance r-t1*r-t2=r-t1+t2-m-*-00-lemma1
                              (d (- (* c1 x y)))
                              (a (* x x))
                              (b (* y y))
                              (c (* z z)))
                   (:instance r-t1*r-t2=r-t1+t2-m-*-00-lemma1
                              (d (- (* c2 x y)))
                              (a (* x x))
                              (b (* y y))
                              (c (* z z)))
                   (:instance r-t1*r-t2=r-t1+t2-m-*-00-lemma1
                              (d (* x y))
                              (a (* x x))
                              (b (* y y))
                              (c (* z z)))
                   (:instance r-t1*r-t2=r-t1+t2-m-*-00-lemma1
                              (d (* c1 c2 x y))
                              (a (* x x))
                              (b (* y y))
                              (c (* z z)))
                   )
             )))

  (defthmd r-t1*r-t2=r-t1+t2-m-*-02
    (implies (and (realp c1)
                  (realp c2)
                  (realp x)
                  (realp y)
                  (realp z)
                  (realp s1)
                  (realp s2)
                  (equal m1-00 (+ c1 (* x x (- 1 c1))))
                  (equal m1-01 (- (* x y (- 1 c1)) (* z s1)))
                  (equal m1-02 (+ (* x z (- 1 c1)) (* y s1)))
                  (equal m2-02 (+ (* x z (- 1 c2)) (* y s2)))
                  (equal m2-12 (- (* y z (- 1 c2)) (* x s2)))
                  (equal m2-22 (+ c2 (* z z (- 1 c2))))
                  (equal m3-02 (+ (* x z (- 1 cosc1c2)) (* y sins1s2)))
                  (equal cosc1c2 (- (* c1 c2) (* s1 s2)))
                  (equal sins1s2 (+ (* s1 c2) (* c1 s2)))
                  (equal (+ (* x x) (* y y) (* z z)) 1)
                  (equal (+ (* s1 s1) (* c1 c1)) 1)
                  (equal (+ (* s2 s2) (* c2 c2)) 1))
             (equal (+ (* m1-00 m2-02)
                       (* m1-01 m2-12)
                       (* m1-02 m2-22)
                       )
                    m3-02))
    :hints (("Goal"
             :use ((:instance r-t1*r-t2=r-t1+t2-m-*-00-lemma1
                              (d (- (* c1 x z)))
                              (a (* x x))
                              (b (* y y))
                              (c (* z z)))
                   (:instance r-t1*r-t2=r-t1+t2-m-*-00-lemma1
                              (d (- (* c2 x z)))
                              (a (* x x))
                              (b (* y y))
                              (c (* z z)))
                   (:instance r-t1*r-t2=r-t1+t2-m-*-00-lemma1
                              (d (* x z))
                              (a (* x x))
                              (b (* y y))
                              (c (* z z)))
                   (:instance r-t1*r-t2=r-t1+t2-m-*-00-lemma1
                              (d (* c1 c2 x z))
                              (a (* x x))
                              (b (* y y))
                              (c (* z z)))
                   )
             )))

  (defthmd r-t1*r-t2=r-t1+t2-m-*-10
    (implies (and (realp c1)
                  (realp c2)
                  (realp x)
                  (realp y)
                  (realp z)
                  (realp s1)
                  (realp s2)
                  (equal m1-10 (+ (* y x (- 1 c1)) (* z s1)))
                  (equal m1-11 (+ c1 (* y y (- 1 c1))))
                  (equal m1-12 (- (* y z (- 1 c1)) (* x s1)))
                  (equal m2-00 (+ c2 (* x x (- 1 c2))))
                  (equal m2-10 (+ (* y x (- 1 c2)) (* z s2)))
                  (equal m2-20 (- (* z x (- 1 c2)) (* y s2)))
                  (equal m3-10 (+ (* y x (- 1 cosc1c2)) (* z sins1s2)))
                  (equal cosc1c2 (- (* c1 c2) (* s1 s2)))
                  (equal sins1s2 (+ (* s1 c2) (* c1 s2)))
                  (equal (+ (* x x) (* y y) (* z z)) 1)
                  (equal (+ (* s1 s1) (* c1 c1)) 1)
                  (equal (+ (* s2 s2) (* c2 c2)) 1))
             (equal (+ (* m1-10 m2-00)
                       (* m1-11 m2-10)
                       (* m1-12 m2-20)
                       )
                    m3-10))
    :hints (("Goal"
             :use ((:instance r-t1*r-t2=r-t1+t2-m-*-00-lemma1
                              (d (- (* c1 x y)))
                              (a (* x x))
                              (b (* y y))
                              (c (* z z)))
                   (:instance r-t1*r-t2=r-t1+t2-m-*-00-lemma1
                              (d (- (* c2 x y)))
                              (a (* x x))
                              (b (* y y))
                              (c (* z z)))
                   (:instance r-t1*r-t2=r-t1+t2-m-*-00-lemma1
                              (d (* x y))
                              (a (* x x))
                              (b (* y y))
                              (c (* z z)))
                   (:instance r-t1*r-t2=r-t1+t2-m-*-00-lemma1
                              (d (* c1 c2 x y))
                              (a (* x x))
                              (b (* y y))
                              (c (* z z)))
                   )
             )))

  (defthmd r-t1*r-t2=r-t1+t2-m-*-11
    (implies (and (realp c1)
                  (realp c2)
                  (realp x)
                  (realp y)
                  (realp z)
                  (realp s1)
                  (realp s2)
                  (equal m1-10 (+ (* y x (- 1 c1)) (* z s1)))
                  (equal m1-11 (+ c1 (* y y (- 1 c1))))
                  (equal m1-12 (- (* y z (- 1 c1)) (* x s1)))
                  (equal m2-01 (- (* x y (- 1 c2)) (* z s2)))
                  (equal m2-11 (+ c2 (* y y (- 1 c2))))
                  (equal m2-21 (+ (* z y (- 1 c2)) (* x s2)))
                  (equal m3-11 (+ cosc1c2 (* y y (- 1 cosc1c2))))
                  (equal cosc1c2 (- (* c1 c2) (* s1 s2)))
                  (equal sins1s2 (+ (* s1 c2) (* c1 s2)))
                  (equal (+ (* x x) (* y y) (* z z)) 1)
                  (equal (+ (* s1 s1) (* c1 c1)) 1)
                  (equal (+ (* s2 s2) (* c2 c2)) 1))
             (equal (+ (* m1-10 m2-01)
                       (* m1-11 m2-11)
                       (* m1-12 m2-21)
                       )
                    m3-11))
    :hints (("Goal"
             :use ((:instance r-t1*r-t2=r-t1+t2-m-*-00-lemma1
                              (d (- (* c1 y y)))
                              (a (* x x))
                              (b (* y y))
                              (c (* z z)))
                   (:instance r-t1*r-t2=r-t1+t2-m-*-00-lemma1
                              (d (- (* c2 y y)))
                              (a (* x x))
                              (b (* y y))
                              (c (* z z)))
                   (:instance r-t1*r-t2=r-t1+t2-m-*-00-lemma1
                              (d (* y y))
                              (a (* x x))
                              (b (* y y))
                              (c (* z z)))
                   (:instance r-t1*r-t2=r-t1+t2-m-*-00-lemma1
                              (d (* c1 c2 y y))
                              (a (* x x))
                              (b (* y y))
                              (c (* z z)))
                   )
             )))

  (defthmd r-t1*r-t2=r-t1+t2-m-*-12
    (implies (and (realp c1)
                  (realp c2)
                  (realp x)
                  (realp y)
                  (realp z)
                  (realp s1)
                  (realp s2)
                  (equal m1-10 (+ (* y x (- 1 c1)) (* z s1)))
                  (equal m1-11 (+ c1 (* y y (- 1 c1))))
                  (equal m1-12 (- (* y z (- 1 c1)) (* x s1)))
                  (equal m2-02 (+ (* x z (- 1 c2)) (* y s2)))
                  (equal m2-12 (- (* y z (- 1 c2)) (* x s2)))
                  (equal m2-22 (+ c2 (* z z (- 1 c2))))
                  (equal m3-12 (- (* y z (- 1 cosc1c2)) (* x sins1s2)))
                  (equal cosc1c2 (- (* c1 c2) (* s1 s2)))
                  (equal sins1s2 (+ (* s1 c2) (* c1 s2)))
                  (equal (+ (* x x) (* y y) (* z z)) 1)
                  (equal (+ (* s1 s1) (* c1 c1)) 1)
                  (equal (+ (* s2 s2) (* c2 c2)) 1))
             (equal (+ (* m1-10 m2-02)
                       (* m1-11 m2-12)
                       (* m1-12 m2-22)
                       )
                    m3-12))
    :hints (("Goal"
             :use ((:instance r-t1*r-t2=r-t1+t2-m-*-00-lemma1
                              (d (- (* c1 y z)))
                              (a (* x x))
                              (b (* y y))
                              (c (* z z)))
                   (:instance r-t1*r-t2=r-t1+t2-m-*-00-lemma1
                              (d (- (* c2 y z)))
                              (a (* x x))
                              (b (* y y))
                              (c (* z z)))
                   (:instance r-t1*r-t2=r-t1+t2-m-*-00-lemma1
                              (d (* y z))
                              (a (* x x))
                              (b (* y y))
                              (c (* z z)))
                   (:instance r-t1*r-t2=r-t1+t2-m-*-00-lemma1
                              (d (* c1 c2 y z))
                              (a (* x x))
                              (b (* y y))
                              (c (* z z)))
                   )
             )))

  (defthmd r-t1*r-t2=r-t1+t2-m-*-20
    (implies (and (realp c1)
                  (realp c2)
                  (realp x)
                  (realp y)
                  (realp z)
                  (realp s1)
                  (realp s2)
                  (equal m1-20 (- (* z x (- 1 c1)) (* y s1)))
                  (equal m1-21 (+ (* z y (- 1 c1)) (* x s1)))
                  (equal m1-22 (+ c1 (* z z (- 1 c1))))
                  (equal m2-00 (+ c2 (* x x (- 1 c2))))
                  (equal m2-10 (+ (* y x (- 1 c2)) (* z s2)))
                  (equal m2-20 (- (* z x (- 1 c2)) (* y s2)))
                  (equal m3-20 (- (* z x (- 1 cosc1c2)) (* y sins1s2)))
                  (equal cosc1c2 (- (* c1 c2) (* s1 s2)))
                  (equal sins1s2 (+ (* s1 c2) (* c1 s2)))
                  (equal (+ (* x x) (* y y) (* z z)) 1)
                  (equal (+ (* s1 s1) (* c1 c1)) 1)
                  (equal (+ (* s2 s2) (* c2 c2)) 1))
             (equal (+ (* m1-20 m2-00)
                       (* m1-21 m2-10)
                       (* m1-22 m2-20)
                       )
                    m3-20))
    :hints (("Goal"
             :use ((:instance r-t1*r-t2=r-t1+t2-m-*-00-lemma1
                              (d (- (* c1 x z)))
                              (a (* x x))
                              (b (* y y))
                              (c (* z z)))
                   (:instance r-t1*r-t2=r-t1+t2-m-*-00-lemma1
                              (d (- (* c2 x z)))
                              (a (* x x))
                              (b (* y y))
                              (c (* z z)))
                   (:instance r-t1*r-t2=r-t1+t2-m-*-00-lemma1
                              (d (* x z))
                              (a (* x x))
                              (b (* y y))
                              (c (* z z)))
                   (:instance r-t1*r-t2=r-t1+t2-m-*-00-lemma1
                              (d (* c1 c2 x z))
                              (a (* x x))
                              (b (* y y))
                              (c (* z z)))
                   )
             )))

  (defthmd r-t1*r-t2=r-t1+t2-m-*-21
    (implies (and (realp c1)
                  (realp c2)
                  (realp x)
                  (realp y)
                  (realp z)
                  (realp s1)
                  (realp s2)
                  (equal m1-20 (- (* z x (- 1 c1)) (* y s1)))
                  (equal m1-21 (+ (* z y (- 1 c1)) (* x s1)))
                  (equal m1-22 (+ c1 (* z z (- 1 c1))))
                  (equal m2-01 (- (* x y (- 1 c2)) (* z s2)))
                  (equal m2-11 (+ c2 (* y y (- 1 c2))))
                  (equal m2-21 (+ (* z y (- 1 c2)) (* x s2)))
                  (equal m3-21 (+ (* z y (- 1 cosc1c2)) (* x sins1s2)))
                  (equal cosc1c2 (- (* c1 c2) (* s1 s2)))
                  (equal sins1s2 (+ (* s1 c2) (* c1 s2)))
                  (equal (+ (* x x) (* y y) (* z z)) 1)
                  (equal (+ (* s1 s1) (* c1 c1)) 1)
                  (equal (+ (* s2 s2) (* c2 c2)) 1))
             (equal (+ (* m1-20 m2-01)
                       (* m1-21 m2-11)
                       (* m1-22 m2-21)
                       )
                    m3-21))
    :hints (("Goal"
             :use ((:instance r-t1*r-t2=r-t1+t2-m-*-00-lemma1
                              (d (- (* c1 y z)))
                              (a (* x x))
                              (b (* y y))
                              (c (* z z)))
                   (:instance r-t1*r-t2=r-t1+t2-m-*-00-lemma1
                              (d (- (* c2 y z)))
                              (a (* x x))
                              (b (* y y))
                              (c (* z z)))
                   (:instance r-t1*r-t2=r-t1+t2-m-*-00-lemma1
                              (d (* y z))
                              (a (* x x))
                              (b (* y y))
                              (c (* z z)))
                   (:instance r-t1*r-t2=r-t1+t2-m-*-00-lemma1
                              (d (* c1 c2 y z))
                              (a (* x x))
                              (b (* y y))
                              (c (* z z)))
                   )
             )))

  (defthmd r-t1*r-t2=r-t1+t2-m-*-22
    (implies (and (realp c1)
                  (realp c2)
                  (realp x)
                  (realp y)
                  (realp z)
                  (realp s1)
                  (realp s2)
                  (equal m1-20 (- (* z x (- 1 c1)) (* y s1)))
                  (equal m1-21 (+ (* z y (- 1 c1)) (* x s1)))
                  (equal m1-22 (+ c1 (* z z (- 1 c1))))
                  (equal m2-02 (+ (* x z (- 1 c2)) (* y s2)))
                  (equal m2-12 (- (* y z (- 1 c2)) (* x s2)))
                  (equal m2-22 (+ c2 (* z z (- 1 c2))))
                  (equal m3-22 (+ cosc1c2 (* z z (- 1 cosc1c2))))
                  (equal cosc1c2 (- (* c1 c2) (* s1 s2)))
                  (equal sins1s2 (+ (* s1 c2) (* c1 s2)))
                  (equal (+ (* x x) (* y y) (* z z)) 1)
                  (equal (+ (* s1 s1) (* c1 c1)) 1)
                  (equal (+ (* s2 s2) (* c2 c2)) 1))
             (equal (+ (* m1-20 m2-02)
                       (* m1-21 m2-12)
                       (* m1-22 m2-22)
                       )
                    m3-22))
    :hints (("Goal"
             :use ((:instance r-t1*r-t2=r-t1+t2-m-*-00-lemma1
                              (d (- (* c1 z z)))
                              (a (* x x))
                              (b (* y y))
                              (c (* z z)))
                   (:instance r-t1*r-t2=r-t1+t2-m-*-00-lemma1
                              (d (- (* c2 z z)))
                              (a (* x x))
                              (b (* y y))
                              (c (* z z)))
                   (:instance r-t1*r-t2=r-t1+t2-m-*-00-lemma1
                              (d (* z z))
                              (a (* x x))
                              (b (* y y))
                              (c (* z z)))
                   (:instance r-t1*r-t2=r-t1+t2-m-*-00-lemma1
                              (d (* c1 c2 z z))
                              (a (* x x))
                              (b (* y y))
                              (c (* z z)))
                   )
             )))
  )

(defthmd m-=-equiv-lemma
  (implies (and (r3-matrixp m1)
                (r3-matrixp m2)
                (equal (aref2 :fake-name m1 0 0) (aref2 :fake-name m2 0 0))
                (equal (aref2 :fake-name m1 0 1) (aref2 :fake-name m2 0 1))
                (equal (aref2 :fake-name m1 0 2) (aref2 :fake-name m2 0 2))
                (equal (aref2 :fake-name m1 1 0) (aref2 :fake-name m2 1 0))
                (equal (aref2 :fake-name m1 1 1) (aref2 :fake-name m2 1 1))
                (equal (aref2 :fake-name m1 1 2) (aref2 :fake-name m2 1 2))
                (equal (aref2 :fake-name m1 2 0) (aref2 :fake-name m2 2 0))
                (equal (aref2 :fake-name m1 2 1) (aref2 :fake-name m2 2 1))
                (equal (aref2 :fake-name m1 2 2) (aref2 :fake-name m2 2 2))
                )
           (m-= m1 m2))
  :hints (("Goal"
           :in-theory (enable m-=)
           )))

(defthmd r-t1*r-t2=r-t1+t2
  (implies (and (realp angle1)
                (realp angle2)
                (point-in-r3 u)
                (equal (+ (* (point-in-r3-x1 u) (point-in-r3-x1 u))
                          (* (point-in-r3-y1 u) (point-in-r3-y1 u))
                          (* (point-in-r3-z1 u) (point-in-r3-z1 u)))
                       1))
           (m-= (m-* (rotation-about-witness angle1 u)
                     (rotation-about-witness angle2 u))
                (rotation-about-witness (+ angle1 angle2) u)))
  :hints (("Goal"
           :use ((:instance r3-rotationp-r-theta-10 (angle angle1) (p u))
                 (:instance r3-rotationp-r-theta-10 (angle angle2) (p u))
                 (:instance r3-rotationp-r-theta-10 (angle (+ angle1 angle2)) (p u))
                 (:instance r3-matrixp (m (rotation-about-witness angle1 u)))
                 (:instance r3-matrixp (m (rotation-about-witness angle2 u)))
                 (:instance r3-matrixp (m (rotation-about-witness (+ angle1 angle2) u)))
                 (:instance sine-of-sums (x angle1) (y angle2))
                 (:instance cosine-of-sums (x angle1) (y angle2))
                 (:instance sin**2+cos**2 (x angle1))
                 (:instance sin**2+cos**2 (x angle2))
                 (:instance r3-rotationp-r-theta-11-1-lemma4 (p u))
                 (:instance r3-rotationp-r-theta-8 (angle angle1))
                 (:instance r3-rotationp-r-theta-8 (angle angle2))
                 (:instance rotation-about-witness-values (point u) (angle angle1))
                 (:instance rotation-about-witness-values (point u) (angle angle2))
                 (:instance rotation-about-witness-values (point u) (angle (+ angle1 angle2)))
                 (:instance aref2-m-*
                            (m1 (rotation-about-witness angle1 u))
                            (m2 (rotation-about-witness angle2 u))
                            (name :fake-name)
                            (i 0)
                            (j 0))
                 (:instance aref2-m-*
                            (m1 (rotation-about-witness angle1 u))
                            (m2 (rotation-about-witness angle2 u))
                            (name :fake-name)
                            (i 0)
                            (j 1))
                 (:instance aref2-m-*
                            (m1 (rotation-about-witness angle1 u))
                            (m2 (rotation-about-witness angle2 u))
                            (name :fake-name)
                            (i 0)
                            (j 2))
                 (:instance aref2-m-*
                            (m1 (rotation-about-witness angle1 u))
                            (m2 (rotation-about-witness angle2 u))
                            (name :fake-name)
                            (i 1)
                            (j 0))
                 (:instance aref2-m-*
                            (m1 (rotation-about-witness angle1 u))
                            (m2 (rotation-about-witness angle2 u))
                            (name :fake-name)
                            (i 1)
                            (j 1))
                 (:instance aref2-m-*
                            (m1 (rotation-about-witness angle1 u))
                            (m2 (rotation-about-witness angle2 u))
                            (name :fake-name)
                            (i 1)
                            (j 2))
                 (:instance aref2-m-*
                            (m1 (rotation-about-witness angle1 u))
                            (m2 (rotation-about-witness angle2 u))
                            (name :fake-name)
                            (i 2)
                            (j 0))
                 (:instance aref2-m-*
                            (m1 (rotation-about-witness angle1 u))
                            (m2 (rotation-about-witness angle2 u))
                            (name :fake-name)
                            (i 2)
                            (j 1))
                 (:instance aref2-m-*
                            (m1 (rotation-about-witness angle1 u))
                            (m2 (rotation-about-witness angle2 u))
                            (name :fake-name)
                            (i 2)
                            (j 2))
                 (:instance r-t1*r-t2=r-t1+t2-m-*-00
                            (c1 (acl2-cosine angle1))
                            (c2 (acl2-cosine angle2))
                            (x (point-in-r3-x1 u))
                            (y (point-in-r3-y1 u))
                            (z (point-in-r3-z1 u))
                            (s1 (acl2-sine angle1))
                            (s2 (acl2-sine angle2))
                            (m1-00 (aref2 :fake-name (rotation-about-witness angle1 u) 0 0))
                            (m1-01 (aref2 :fake-name (rotation-about-witness angle1 u) 0 1))
                            (m1-02 (aref2 :fake-name (rotation-about-witness angle1 u) 0 2))
                            (m2-00 (aref2 :fake-name (rotation-about-witness angle2 u) 0 0))
                            (m2-10 (aref2 :fake-name (rotation-about-witness angle2 u) 1 0))
                            (m2-20 (aref2 :fake-name (rotation-about-witness angle2 u) 2 0))
                            (m3-00 (aref2 :fake-name (rotation-about-witness (+ angle1 angle2) u) 0 0))
                            (cosc1c2 (acl2-cosine (+ angle1 angle2)))
                            (sins1s2 (acl2-sine (+ angle1 angle2))))
                 (:instance r-t1*r-t2=r-t1+t2-m-*-01
                            (c1 (acl2-cosine angle1))
                            (c2 (acl2-cosine angle2))
                            (x (point-in-r3-x1 u))
                            (y (point-in-r3-y1 u))
                            (z (point-in-r3-z1 u))
                            (m1-00 (aref2 :fake-name (rotation-about-witness angle1 u) 0 0))
                            (m1-01 (aref2 :fake-name (rotation-about-witness angle1 u) 0 1))
                            (m1-02 (aref2 :fake-name (rotation-about-witness angle1 u) 0 2))
                            (m2-01 (aref2 :fake-name (rotation-about-witness angle2 u) 0 1))
                            (m2-11 (aref2 :fake-name (rotation-about-witness angle2 u) 1 1))
                            (m2-21 (aref2 :fake-name (rotation-about-witness angle2 u) 2 1))
                            (m3-01 (aref2 :fake-name (rotation-about-witness (+ angle1 angle2) u) 0 1))
                            (s1 (acl2-sine angle1))
                            (s2 (acl2-sine angle2))
                            (cosc1c2 (acl2-cosine (+ angle1 angle2)))
                            (sins1s2 (acl2-sine (+ angle1 angle2))))
                 (:instance r-t1*r-t2=r-t1+t2-m-*-02
                            (c1 (acl2-cosine angle1))
                            (c2 (acl2-cosine angle2))
                            (x (point-in-r3-x1 u))
                            (y (point-in-r3-y1 u))
                            (z (point-in-r3-z1 u))
                            (m1-00 (aref2 :fake-name (rotation-about-witness angle1 u) 0 0))
                            (m1-01 (aref2 :fake-name (rotation-about-witness angle1 u) 0 1))
                            (m1-02 (aref2 :fake-name (rotation-about-witness angle1 u) 0 2))
                            (m2-02 (aref2 :fake-name (rotation-about-witness angle2 u) 0 2))
                            (m2-12 (aref2 :fake-name (rotation-about-witness angle2 u) 1 2))
                            (m2-22 (aref2 :fake-name (rotation-about-witness angle2 u) 2 2))
                            (m3-02 (aref2 :fake-name (rotation-about-witness (+ angle1 angle2) u) 0 2))
                            (s1 (acl2-sine angle1))
                            (s2 (acl2-sine angle2))
                            (cosc1c2 (acl2-cosine (+ angle1 angle2)))
                            (sins1s2 (acl2-sine (+ angle1 angle2))))
                 (:instance r-t1*r-t2=r-t1+t2-m-*-10
                            (c1 (acl2-cosine angle1))
                            (c2 (acl2-cosine angle2))
                            (x (point-in-r3-x1 u))
                            (y (point-in-r3-y1 u))
                            (z (point-in-r3-z1 u))
                            (m1-10 (aref2 :fake-name (rotation-about-witness angle1 u) 1 0))
                            (m1-11 (aref2 :fake-name (rotation-about-witness angle1 u) 1 1))
                            (m1-12 (aref2 :fake-name (rotation-about-witness angle1 u) 1 2))
                            (m2-00 (aref2 :fake-name (rotation-about-witness angle2 u) 0 0))
                            (m2-10 (aref2 :fake-name (rotation-about-witness angle2 u) 1 0))
                            (m2-20 (aref2 :fake-name (rotation-about-witness angle2 u) 2 0))
                            (m3-10 (aref2 :fake-name (rotation-about-witness (+ angle1 angle2) u) 1 0))
                            (s1 (acl2-sine angle1))
                            (s2 (acl2-sine angle2))
                            (cosc1c2 (acl2-cosine (+ angle1 angle2)))
                            (sins1s2 (acl2-sine (+ angle1 angle2))))
                 (:instance r-t1*r-t2=r-t1+t2-m-*-11
                            (c1 (acl2-cosine angle1))
                            (c2 (acl2-cosine angle2))
                            (x (point-in-r3-x1 u))
                            (y (point-in-r3-y1 u))
                            (z (point-in-r3-z1 u))
                            (m1-10 (aref2 :fake-name (rotation-about-witness angle1 u) 1 0))
                            (m1-11 (aref2 :fake-name (rotation-about-witness angle1 u) 1 1))
                            (m1-12 (aref2 :fake-name (rotation-about-witness angle1 u) 1 2))
                            (m2-01 (aref2 :fake-name (rotation-about-witness angle2 u) 0 1))
                            (m2-11 (aref2 :fake-name (rotation-about-witness angle2 u) 1 1))
                            (m2-21 (aref2 :fake-name (rotation-about-witness angle2 u) 2 1))
                            (m3-11 (aref2 :fake-name (rotation-about-witness (+ angle1 angle2) u) 1 1))
                            (s1 (acl2-sine angle1))
                            (s2 (acl2-sine angle2))
                            (cosc1c2 (acl2-cosine (+ angle1 angle2)))
                            (sins1s2 (acl2-sine (+ angle1 angle2))))
                 (:instance r-t1*r-t2=r-t1+t2-m-*-12
                            (c1 (acl2-cosine angle1))
                            (c2 (acl2-cosine angle2))
                            (x (point-in-r3-x1 u))
                            (y (point-in-r3-y1 u))
                            (z (point-in-r3-z1 u))
                            (m1-10 (aref2 :fake-name (rotation-about-witness angle1 u) 1 0))
                            (m1-11 (aref2 :fake-name (rotation-about-witness angle1 u) 1 1))
                            (m1-12 (aref2 :fake-name (rotation-about-witness angle1 u) 1 2))
                            (m2-02 (aref2 :fake-name (rotation-about-witness angle2 u) 0 2))
                            (m2-12 (aref2 :fake-name (rotation-about-witness angle2 u) 1 2))
                            (m2-22 (aref2 :fake-name (rotation-about-witness angle2 u) 2 2))
                            (m3-12 (aref2 :fake-name (rotation-about-witness (+ angle1 angle2) u) 1 2))
                            (s1 (acl2-sine angle1))
                            (s2 (acl2-sine angle2))
                            (cosc1c2 (acl2-cosine (+ angle1 angle2)))
                            (sins1s2 (acl2-sine (+ angle1 angle2))))
                 (:instance r-t1*r-t2=r-t1+t2-m-*-20
                            (c1 (acl2-cosine angle1))
                            (c2 (acl2-cosine angle2))
                            (x (point-in-r3-x1 u))
                            (y (point-in-r3-y1 u))
                            (z (point-in-r3-z1 u))
                            (m1-20 (aref2 :fake-name (rotation-about-witness angle1 u) 2 0))
                            (m1-21 (aref2 :fake-name (rotation-about-witness angle1 u) 2 1))
                            (m1-22 (aref2 :fake-name (rotation-about-witness angle1 u) 2 2))
                            (m2-00 (aref2 :fake-name (rotation-about-witness angle2 u) 0 0))
                            (m2-10 (aref2 :fake-name (rotation-about-witness angle2 u) 1 0))
                            (m2-20 (aref2 :fake-name (rotation-about-witness angle2 u) 2 0))
                            (m3-20 (aref2 :fake-name (rotation-about-witness (+ angle1 angle2) u) 2 0))
                            (s1 (acl2-sine angle1))
                            (s2 (acl2-sine angle2))
                            (cosc1c2 (acl2-cosine (+ angle1 angle2)))
                            (sins1s2 (acl2-sine (+ angle1 angle2))))
                 (:instance r-t1*r-t2=r-t1+t2-m-*-21
                            (c1 (acl2-cosine angle1))
                            (c2 (acl2-cosine angle2))
                            (x (point-in-r3-x1 u))
                            (y (point-in-r3-y1 u))
                            (z (point-in-r3-z1 u))
                            (m1-20 (aref2 :fake-name (rotation-about-witness angle1 u) 2 0))
                            (m1-21 (aref2 :fake-name (rotation-about-witness angle1 u) 2 1))
                            (m1-22 (aref2 :fake-name (rotation-about-witness angle1 u) 2 2))
                            (m2-01 (aref2 :fake-name (rotation-about-witness angle2 u) 0 1))
                            (m2-11 (aref2 :fake-name (rotation-about-witness angle2 u) 1 1))
                            (m2-21 (aref2 :fake-name (rotation-about-witness angle2 u) 2 1))
                            (m3-21 (aref2 :fake-name (rotation-about-witness (+ angle1 angle2) u) 2 1))
                            (s1 (acl2-sine angle1))
                            (s2 (acl2-sine angle2))
                            (cosc1c2 (acl2-cosine (+ angle1 angle2)))
                            (sins1s2 (acl2-sine (+ angle1 angle2))))
                 (:instance r-t1*r-t2=r-t1+t2-m-*-22
                            (c1 (acl2-cosine angle1))
                            (c2 (acl2-cosine angle2))
                            (x (point-in-r3-x1 u))
                            (y (point-in-r3-y1 u))
                            (z (point-in-r3-z1 u))
                            (m1-20 (aref2 :fake-name (rotation-about-witness angle1 u) 2 0))
                            (m1-21 (aref2 :fake-name (rotation-about-witness angle1 u) 2 1))
                            (m1-22 (aref2 :fake-name (rotation-about-witness angle1 u) 2 2))
                            (m2-02 (aref2 :fake-name (rotation-about-witness angle2 u) 0 2))
                            (m2-12 (aref2 :fake-name (rotation-about-witness angle2 u) 1 2))
                            (m2-22 (aref2 :fake-name (rotation-about-witness angle2 u) 2 2))
                            (m3-22 (aref2 :fake-name (rotation-about-witness (+ angle1 angle2) u) 2 2))
                            (s1 (acl2-sine angle1))
                            (s2 (acl2-sine angle2))
                            (cosc1c2 (acl2-cosine (+ angle1 angle2)))
                            (sins1s2 (acl2-sine (+ angle1 angle2))))
                 (:instance m-=-equiv-lemma
                            (m1 (m-* (rotation-about-witness angle1 u)
                                     (rotation-about-witness angle2 u)))
                            (m2 (rotation-about-witness (+ angle1 angle2) u)))
                 (:instance r3-matrixp-m1*m2-is-r3-matrixp
                            (m1 (ROTATION-ABOUT-WITNESS ANGLE1 U))
                            (m2 (ROTATION-ABOUT-WITNESS ANGLE2 U)))
                 )
           :in-theory (e/d () (m-= aref2 m-* point-in-r3 r3-matrixp point-in-r3-x1 point-in-r3-y1 point-in-r3-z1 m-trans rotation-about-witness r3-m-determinant point-on-s2-not-d acl2-sqrt sin**2+cos**2 acl2-sqrt r3-m-inverse aref2 aref2-m-trans r3-m-inverse-= sine-of-sums cosine-of-sums aref2-m-* r3-matrixp-m1*m2-is-r3-matrixp))

           )
          ))

(defthmd r3-rotationp-r-theta-2-1
  (equal
   (*
    (ACL2-SQRT
     (+
      1
      (- (* (EXISTS-IN-INTERVAL-BUT-NOT-IN-X-COORD-SEQUENCE-WITNESS -1 1)
            (EXISTS-IN-INTERVAL-BUT-NOT-IN-X-COORD-SEQUENCE-WITNESS -1 1)))))
    (ACL2-SQRT
     (+
      1
      (-
       (* (EXISTS-IN-INTERVAL-BUT-NOT-IN-X-COORD-SEQUENCE-WITNESS -1 1)
          (EXISTS-IN-INTERVAL-BUT-NOT-IN-X-COORD-SEQUENCE-WITNESS -1 1))))))
   (+
    1
    (- (* (EXISTS-IN-INTERVAL-BUT-NOT-IN-X-COORD-SEQUENCE-WITNESS -1 1)
          (EXISTS-IN-INTERVAL-BUT-NOT-IN-X-COORD-SEQUENCE-WITNESS -1 1)))))
  :hints (("Goal"
           :use ((:instance exists-point-on-s2-not-d-1-4
                            (p (EXISTS-IN-INTERVAL-BUT-NOT-IN-X-COORD-SEQUENCE-WITNESS -1 1)))
                 (:instance witness-not-in-x-coord-sequence-1)
                 (:instance sqrt-sqrt
                            (x (+
                                1
                                (- (* (EXISTS-IN-INTERVAL-BUT-NOT-IN-X-COORD-SEQUENCE-WITNESS -1 1)
                                      (EXISTS-IN-INTERVAL-BUT-NOT-IN-X-COORD-SEQUENCE-WITNESS -1 1)))))))
           :in-theory nil
           )))

(defthmd r3-rotationp-r-theta-2
  (implies (equal (point-on-s2-not-d) point)
           (equal (+ (* (point-in-r3-x1 point) (point-in-r3-x1 point))
                     (* (point-in-r3-z1 point) (point-in-r3-z1 point)))
                  1))
  :hints (("Goal"
           :use ((:instance r3-rotationp-r-theta-2-1))
           :in-theory (enable aref2)
           )))

(defthmd r3-rotationp-r-theta-3
  (implies (equal (point-on-s2-not-d) point)
           (equal (* (point-in-r3-x1 point) (point-in-r3-x1 point))
                  (- 1 (* (point-in-r3-z1 point) (point-in-r3-z1 point)))))
  :hints (("Goal"
           :use (:instance r3-rotationp-r-theta-2)
           )))

(defthmd r3-rotationp-r-theta-4
  (implies (equal (point-on-s2-not-d) point)
           (equal (* (point-in-r3-z1 point) (point-in-r3-z1 point))
                  (- 1 (* (point-in-r3-x1 point) (point-in-r3-x1 point)))))
  :hints (("Goal"
           :use (:instance r3-rotationp-r-theta-2)
           )))

(defthmd r3-rotationp-r-theta-5
  (implies (equal (point-on-s2-not-d) point)
           (and (realp (point-in-r3-x1 point))
                (realp (point-in-r3-z1 point))
                (equal (point-in-r3-y1 point) 0)))
  :hints (("Goal"
           :use ((:instance exists-point-on-s2-not-d-2))
           :in-theory (enable aref2)
           )))

(defthmd r3-rotationp-r-theta-6
  (equal (* (acl2-sine x) (acl2-sine x))
         (- 1 (* (acl2-cosine x) (acl2-cosine x))))
  :hints (("Goal"
           :use (:instance sin**2+cos**2 (x x))
           :in-theory (disable sin**2+cos**2)
           )))

(defthmd r3-rotationp-r-theta-7
  (equal (* (acl2-cosine x) (acl2-cosine x))
         (- 1 (* (acl2-sine x) (acl2-sine x))))
  :hints (("Goal"
           :use (:instance sin**2+cos**2 (x x))
           :in-theory (disable sin**2+cos**2)
           )))

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd r3-rotationp-r-theta-9-1-1
    (implies (and (realp x)
                  (realp z)
                  (EQUAL (+ (EXPT X 2) (EXPT Z 2)) 1))
             (equal (* (+ (* x x) (* z z))
                       (+ (* x x) (* z z)))
                    1))))

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd r3-rotationp-r-theta-9-1-2
    (EQUAL (+ (EXPT X 4)
              (EXPT Z 4)
              (* 2 (EXPT X 2) (EXPT Z 2)))
           (* (+ (* x x) (* z z))
              (+ (* x x) (* z z)))
           )))

(defthmd r3-rotationp-r-theta-9-1-3
  (IMPLIES (AND (REALP X)
                (REALP Z)
                (EQUAL (+ (EXPT X 2) (EXPT Z 2)) 1)
                (NOT (EQUAL Z 0))
                (NOT (EQUAL X 0)))
           (EQUAL (+ (EXPT X 4)
                     (EXPT Z 4)
                     (* 2 (EXPT X 2) (EXPT Z 2)))
                  1))
  :hints (("Goal"
           :use ((:instance r3-rotationp-r-theta-9-1-1)
                 (:instance r3-rotationp-r-theta-9-1-2))
           :in-theory nil
           )))

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd r3-rotationp-r-theta-9-1-4
    (equal (+ 1 (* (EXPT X 2) (EXPT C 3))
              (* (EXPT Z 2) (EXPT C 3))
              (* C (EXPT S 2) (EXPT X 4))
              (* C (EXPT S 2) (EXPT Z 4))
              (* 2 C (EXPT S 2)
                 (EXPT X 2)
                 (EXPT Z 2)))
           (+ 1
              (* (expt c 3) (+ (EXPT X 2) (EXPT Z 2)))
              (* c (expt s 2) (+ (EXPT X 4) (EXPT Z 4) (* 2 (EXPT X 2) (EXPT Z 2)))))))

  (defthmd r3-rotationp-r-theta-9-1-5
    (EQUAL (+ (EXPT C 3)
              (* (EXPT C 2) (EXPT X 2))
              (* (EXPT C 2) (EXPT Z 2))
              (* (EXPT S 2) (EXPT X 4))
              (* (EXPT S 2) (EXPT Z 4))
              (* C (EXPT S 2) (EXPT X 2))
              (* C (EXPT S 2) (EXPT Z 2))
              (* 2 (EXPT S 2) (EXPT X 2) (EXPT Z 2)))
           (+ (EXPT C 3)
              (* (expt c 2) (+ (EXPT X 2) (EXPT Z 2)))
              (* c (expt s 2) (+ (EXPT X 2) (EXPT Z 2)))
              (* (expt s 2) (+ (EXPT X 4) (EXPT Z 4) (* 2 (EXPT X 2) (EXPT Z 2)))))))
  )

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd r3-rotationp-r-theta-9-1
    (implies (and (realp x)
                  (realp z)
                  (realp c)
                  (realp s)
                  (equal (+ (* x x) (* z z)) 1)
                  (equal (+ (* s s) (* c c)) 1))
             (EQUAL (+ (* x
                          x
                          z
                          z
                          c)
                       (- (* x
                             x
                             z
                             z
                             c))
                       (* x
                          x
                          c
                          c)
                       (* z
                          z
                          c
                          c)
                       (* x
                          x
                          x
                          x
                          s
                          s)
                       (* x
                          x
                          z
                          z
                          c
                          c)
                       (* x
                          x
                          z
                          z
                          c
                          c)
                       (- (* x
                             x
                             z
                             z
                             c
                             c))
                       (- (* x
                             x
                             z
                             z
                             c
                             c))
                       (* x
                          x
                          z
                          z
                          s
                          s)
                       (* x
                          x
                          z
                          z
                          s
                          s)
                       (* z
                          z
                          z
                          z
                          s
                          s)
                       (* c
                          c
                          c)
                       (- (* x
                             x
                             c
                             c
                             c))
                       (* x
                          x
                          c
                          s
                          s)
                       (- (* z
                             z
                             c
                             c
                             c))
                       (* z
                          z
                          c
                          s
                          s)
                       (- (* x
                             x
                             x
                             x
                             c
                             s
                             s))
                       (* x
                          x
                          z
                          z
                          c
                          c
                          c)
                       (- (* x
                             x
                             z
                             z
                             c
                             c
                             c))
                       (- (* x
                             x
                             z
                             z
                             c
                             s
                             s))
                       (- (* x
                             x
                             z
                             z
                             c
                             s
                             s))
                       (- (* z
                             z
                             z
                             z
                             c
                             s
                             s)))
                    1))
    :hints (("Goal"
             :use ((:instance r3-rotationp-r-theta-9-1-1)
                   (:instance r3-rotationp-r-theta-9-1-3))
             )
            ("Subgoal 1"
             :use ((:instance r3-rotationp-r-theta-9-1-4)
                   (:instance r3-rotationp-r-theta-9-1-5))
             )
            ))
  )

(defthmd r3-rotationp-r-theta-9
  (implies (realp angle)
           (EQUAL (+ (* (POINT-IN-R3-X1 (POINT-ON-S2-NOT-D))
                        (POINT-IN-R3-X1 (POINT-ON-S2-NOT-D))
                        (POINT-IN-R3-Z1 (POINT-ON-S2-NOT-D))
                        (POINT-IN-R3-Z1 (POINT-ON-S2-NOT-D))
                        (ACL2-COSINE ANGLE))
                     (- (* (POINT-IN-R3-X1 (POINT-ON-S2-NOT-D))
                           (POINT-IN-R3-X1 (POINT-ON-S2-NOT-D))
                           (POINT-IN-R3-Z1 (POINT-ON-S2-NOT-D))
                           (POINT-IN-R3-Z1 (POINT-ON-S2-NOT-D))
                           (ACL2-COSINE ANGLE)))
                     (* (POINT-IN-R3-X1 (POINT-ON-S2-NOT-D))
                        (POINT-IN-R3-X1 (POINT-ON-S2-NOT-D))
                        (ACL2-COSINE ANGLE)
                        (ACL2-COSINE ANGLE))
                     (* (POINT-IN-R3-Z1 (POINT-ON-S2-NOT-D))
                        (POINT-IN-R3-Z1 (POINT-ON-S2-NOT-D))
                        (ACL2-COSINE ANGLE)
                        (ACL2-COSINE ANGLE))
                     (* (POINT-IN-R3-X1 (POINT-ON-S2-NOT-D))
                        (POINT-IN-R3-X1 (POINT-ON-S2-NOT-D))
                        (POINT-IN-R3-X1 (POINT-ON-S2-NOT-D))
                        (POINT-IN-R3-X1 (POINT-ON-S2-NOT-D))
                        (ACL2-SINE ANGLE)
                        (ACL2-SINE ANGLE))
                     (* (POINT-IN-R3-X1 (POINT-ON-S2-NOT-D))
                        (POINT-IN-R3-X1 (POINT-ON-S2-NOT-D))
                        (POINT-IN-R3-Z1 (POINT-ON-S2-NOT-D))
                        (POINT-IN-R3-Z1 (POINT-ON-S2-NOT-D))
                        (ACL2-COSINE ANGLE)
                        (ACL2-COSINE ANGLE))
                     (* (POINT-IN-R3-X1 (POINT-ON-S2-NOT-D))
                        (POINT-IN-R3-X1 (POINT-ON-S2-NOT-D))
                        (POINT-IN-R3-Z1 (POINT-ON-S2-NOT-D))
                        (POINT-IN-R3-Z1 (POINT-ON-S2-NOT-D))
                        (ACL2-COSINE ANGLE)
                        (ACL2-COSINE ANGLE))
                     (- (* (POINT-IN-R3-X1 (POINT-ON-S2-NOT-D))
                           (POINT-IN-R3-X1 (POINT-ON-S2-NOT-D))
                           (POINT-IN-R3-Z1 (POINT-ON-S2-NOT-D))
                           (POINT-IN-R3-Z1 (POINT-ON-S2-NOT-D))
                           (ACL2-COSINE ANGLE)
                           (ACL2-COSINE ANGLE)))
                     (- (* (POINT-IN-R3-X1 (POINT-ON-S2-NOT-D))
                           (POINT-IN-R3-X1 (POINT-ON-S2-NOT-D))
                           (POINT-IN-R3-Z1 (POINT-ON-S2-NOT-D))
                           (POINT-IN-R3-Z1 (POINT-ON-S2-NOT-D))
                           (ACL2-COSINE ANGLE)
                           (ACL2-COSINE ANGLE)))
                     (* (POINT-IN-R3-X1 (POINT-ON-S2-NOT-D))
                        (POINT-IN-R3-X1 (POINT-ON-S2-NOT-D))
                        (POINT-IN-R3-Z1 (POINT-ON-S2-NOT-D))
                        (POINT-IN-R3-Z1 (POINT-ON-S2-NOT-D))
                        (ACL2-SINE ANGLE)
                        (ACL2-SINE ANGLE))
                     (* (POINT-IN-R3-X1 (POINT-ON-S2-NOT-D))
                        (POINT-IN-R3-X1 (POINT-ON-S2-NOT-D))
                        (POINT-IN-R3-Z1 (POINT-ON-S2-NOT-D))
                        (POINT-IN-R3-Z1 (POINT-ON-S2-NOT-D))
                        (ACL2-SINE ANGLE)
                        (ACL2-SINE ANGLE))
                     (* (POINT-IN-R3-Z1 (POINT-ON-S2-NOT-D))
                        (POINT-IN-R3-Z1 (POINT-ON-S2-NOT-D))
                        (POINT-IN-R3-Z1 (POINT-ON-S2-NOT-D))
                        (POINT-IN-R3-Z1 (POINT-ON-S2-NOT-D))
                        (ACL2-SINE ANGLE)
                        (ACL2-SINE ANGLE))
                     (* (ACL2-COSINE ANGLE)
                        (ACL2-COSINE ANGLE)
                        (ACL2-COSINE ANGLE))
                     (- (* (POINT-IN-R3-X1 (POINT-ON-S2-NOT-D))
                           (POINT-IN-R3-X1 (POINT-ON-S2-NOT-D))
                           (ACL2-COSINE ANGLE)
                           (ACL2-COSINE ANGLE)
                           (ACL2-COSINE ANGLE)))
                     (* (POINT-IN-R3-X1 (POINT-ON-S2-NOT-D))
                        (POINT-IN-R3-X1 (POINT-ON-S2-NOT-D))
                        (ACL2-COSINE ANGLE)
                        (ACL2-SINE ANGLE)
                        (ACL2-SINE ANGLE))
                     (- (* (POINT-IN-R3-Z1 (POINT-ON-S2-NOT-D))
                           (POINT-IN-R3-Z1 (POINT-ON-S2-NOT-D))
                           (ACL2-COSINE ANGLE)
                           (ACL2-COSINE ANGLE)
                           (ACL2-COSINE ANGLE)))
                     (* (POINT-IN-R3-Z1 (POINT-ON-S2-NOT-D))
                        (POINT-IN-R3-Z1 (POINT-ON-S2-NOT-D))
                        (ACL2-COSINE ANGLE)
                        (ACL2-SINE ANGLE)
                        (ACL2-SINE ANGLE))
                     (- (* (POINT-IN-R3-X1 (POINT-ON-S2-NOT-D))
                           (POINT-IN-R3-X1 (POINT-ON-S2-NOT-D))
                           (POINT-IN-R3-X1 (POINT-ON-S2-NOT-D))
                           (POINT-IN-R3-X1 (POINT-ON-S2-NOT-D))
                           (ACL2-COSINE ANGLE)
                           (ACL2-SINE ANGLE)
                           (ACL2-SINE ANGLE)))
                     (* (POINT-IN-R3-X1 (POINT-ON-S2-NOT-D))
                        (POINT-IN-R3-X1 (POINT-ON-S2-NOT-D))
                        (POINT-IN-R3-Z1 (POINT-ON-S2-NOT-D))
                        (POINT-IN-R3-Z1 (POINT-ON-S2-NOT-D))
                        (ACL2-COSINE ANGLE)
                        (ACL2-COSINE ANGLE)
                        (ACL2-COSINE ANGLE))
                     (- (* (POINT-IN-R3-X1 (POINT-ON-S2-NOT-D))
                           (POINT-IN-R3-X1 (POINT-ON-S2-NOT-D))
                           (POINT-IN-R3-Z1 (POINT-ON-S2-NOT-D))
                           (POINT-IN-R3-Z1 (POINT-ON-S2-NOT-D))
                           (ACL2-COSINE ANGLE)
                           (ACL2-COSINE ANGLE)
                           (ACL2-COSINE ANGLE)))
                     (- (* (POINT-IN-R3-X1 (POINT-ON-S2-NOT-D))
                           (POINT-IN-R3-X1 (POINT-ON-S2-NOT-D))
                           (POINT-IN-R3-Z1 (POINT-ON-S2-NOT-D))
                           (POINT-IN-R3-Z1 (POINT-ON-S2-NOT-D))
                           (ACL2-COSINE ANGLE)
                           (ACL2-SINE ANGLE)
                           (ACL2-SINE ANGLE)))
                     (- (* (POINT-IN-R3-X1 (POINT-ON-S2-NOT-D))
                           (POINT-IN-R3-X1 (POINT-ON-S2-NOT-D))
                           (POINT-IN-R3-Z1 (POINT-ON-S2-NOT-D))
                           (POINT-IN-R3-Z1 (POINT-ON-S2-NOT-D))
                           (ACL2-COSINE ANGLE)
                           (ACL2-SINE ANGLE)
                           (ACL2-SINE ANGLE)))
                     (- (* (POINT-IN-R3-Z1 (POINT-ON-S2-NOT-D))
                           (POINT-IN-R3-Z1 (POINT-ON-S2-NOT-D))
                           (POINT-IN-R3-Z1 (POINT-ON-S2-NOT-D))
                           (POINT-IN-R3-Z1 (POINT-ON-S2-NOT-D))
                           (ACL2-COSINE ANGLE)
                           (ACL2-SINE ANGLE)
                           (ACL2-SINE ANGLE))))
                  1))
  :hints (("Goal"
           :use ((:instance r3-rotationp-r-theta-9-1
                            (x (POINT-IN-R3-X1 (POINT-ON-S2-NOT-D)))
                            (z (POINT-IN-R3-Z1 (POINT-ON-S2-NOT-D)))
                            (s (acl2-sine angle))
                            (c (acl2-cosine angle)))
                 (:instance r3-rotationp-r-theta-8)
                 (:instance sin**2+cos**2 (x angle))
                 (:instance r3-rotationp-r-theta-2 (point (point-on-s2-not-d)))
                 (:instance r3-rotationp-r-theta-5 (point (POINT-ON-S2-NOT-D))))
           )))

(encapsulate
  ()

  (local (in-theory nil))

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd r3-rotationp-r-theta-1
    (implies (realp angle)
             (equal (r3-m-determinant (rotation-about-witness angle (point-on-s2-not-d)))
                    1))
    :hints (("Goal"
             :use ((:instance rotation-about-witness-values (angle angle) (point (point-on-s2-not-d)))
                   (:instance r3-rotationp-r-theta-2 (point (point-on-s2-not-d)))
                   (:instance r3-rotationp-r-theta-3 (point (point-on-s2-not-d)))
                   (:instance r3-rotationp-r-theta-4 (point (point-on-s2-not-d)))
                   (:instance r3-rotationp-r-theta-5 (point (point-on-s2-not-d)))
                   (:instance r3-rotationp-r-theta-9)
                   (:instance sin**2+cos**2 (x angle))
                   (:instance r3-rotationp-r-theta-8)
                   (:instance r3-rotationp-r-theta-6 (x angle)))
             :in-theory (e/d (r3-m-determinant header default dimensions rotation-about-witness) (point-on-s2-not-d acl2-sqrt point-in-r3-x1 point-in-r3-y1 point-in-r3-z1 sin**2+cos**2 aref2))
             )))
  )

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd r3-matrixp-r3-m-inverse
    (implies (r3-matrixp m)
             (r3-matrixp (r3-m-inverse m)))
    :hints (("Goal"
             :use ((:instance r3-m-inverse-= (m m)))
             :in-theory (e/d (array2p) (aref2 r3-m-inverse-=))
             )))

  (defthmd r3-matrixp-m-trans
    (implies (r3-matrixp m)
             (r3-matrixp (m-trans m))))

  (defthmd m-trans-values
    (implies (r3-matrixp m)
             (and (equal (aref2 :fake-name (m-trans m) 0 0)
                         (aref2 :fake-name m 0 0))
                  (equal (aref2 :fake-name (m-trans m) 0 1)
                         (aref2 :fake-name m 1 0))
                  (equal (aref2 :fake-name (m-trans m) 0 2)
                         (aref2 :fake-name m 2 0))
                  (equal (aref2 :fake-name (m-trans m) 1 0)
                         (aref2 :fake-name m 0 1))
                  (equal (aref2 :fake-name (m-trans m) 1 1)
                         (aref2 :fake-name m 1 1))
                  (equal (aref2 :fake-name (m-trans m) 1 2)
                         (aref2 :fake-name m 2 1))
                  (equal (aref2 :fake-name (m-trans m) 2 0)
                         (aref2 :fake-name m 0 2))
                  (equal (aref2 :fake-name (m-trans m) 2 1)
                         (aref2 :fake-name m 1 2))
                  (equal (aref2 :fake-name (m-trans m) 2 2)
                         (aref2 :fake-name m 2 2)))))
  )

(encapsulate
  ()

  (local (include-book "arithmetic/top" :dir :system))

  (defthmd r3-rotationp-r-theta-11-1-1-lemma1
    (implies (and (realp x)
                  (realp z)
                  (realp s)
                  (realp c)
                  (equal (+ (* s s) (* c c)) 1)
                  (equal (+ (* x x) (* z z)) 1))
             (equal (- (* c
                          (+ c (* z z (- 1 c))))
                       (* (* x s)
                          (- (* x s))))
                    (+ c (* x x (- 1 c)))))
    :hints (("Goal"
             :use ((:instance r3-rotationp-r-theta-11-1-lemma2
                              (a (* c c)) (c (* z z)))
                   (:instance r3-rotationp-r-theta-11-1-lemma3 (c (* c c)) (a (* x x)) (b (* s s)))
                   (:instance r3-rotationp-r-theta-11-1-lemma1 (s x) (c z)))
             ))))

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd r3-rotationp-r-theta-11-1-1-lemma2
    (implies (and (realp angle)
                  (point-in-r3 p)
                  (equal (r3-m-determinant (rotation-about-witness angle p)) 1)
                  (equal (point-in-r3-y1 p) 0)
                  (equal (aref2 :fake-name (rotation-about-witness angle p) 1 1)
                         (+ (acl2-cosine angle)
                            (* (point-in-r3-y1 p) (point-in-r3-y1 p) (- 1 (acl2-cosine angle)))))
                  (equal (aref2 :fake-name (rotation-about-witness angle p) 1 2)
                         (- (* (point-in-r3-y1 p) (point-in-r3-z1 p) (- 1 (acl2-cosine angle)))
                            (* (point-in-r3-x1 p) (acl2-sine angle))))
                  (equal (aref2 :fake-name (rotation-about-witness angle p) 2 1)
                         (+ (* (point-in-r3-z1 p) (point-in-r3-y1 p) (- 1 (acl2-cosine angle)))
                            (* (point-in-r3-x1 p) (acl2-sine angle))))
                  (equal (aref2 :fake-name (rotation-about-witness angle p) 2 2)
                         (+ (acl2-cosine angle)
                            (* (point-in-r3-z1 p) (point-in-r3-z1 p) (- 1 (acl2-cosine angle))))))
             (EQUAL (AREF2 :FAKE-NAME
                           (R3-M-INVERSE (ROTATION-ABOUT-WITNESS ANGLE P))
                           0 0)
                    (- (* (acl2-cosine angle)
                          (+ (acl2-cosine angle) (* (point-in-r3-z1 p) (point-in-r3-z1 p) (- 1 (acl2-cosine angle)))))
                       (* (* (point-in-r3-x1 p) (acl2-sine angle))
                          (- (* (point-in-r3-x1 p) (acl2-sine angle)))))))
    :hints (("Goal"
             :use ((:instance r3-matrixp-r3-m-inverse (m (rotation-about-witness angle p)))
                   (:instance r3-m-inverse-= (m (rotation-about-witness angle p)))
                   (:instance r3-rotationp-r-theta-10 (angle angle) (p p))
                   (:instance r3-rotationp-r-theta-11-1-lemma4 (p p))
                   )
             :in-theory (e/d () (point-in-r3 r3-matrixp point-in-r3-x1 point-in-r3-y1 point-in-r3-z1 m-trans rotation-about-witness r3-m-determinant point-on-s2-not-d acl2-sqrt sin**2+cos**2 acl2-sqrt r3-m-inverse aref2 aref2-m-trans r3-m-inverse-=)
                             )))
    ))

(encapsulate
  ()

  (local (include-book "arithmetic/top" :dir :system))

  (defthmd r3-rotationp-r-theta-11-1-1
    (implies (and (realp angle)
                  (point-in-r3 p)
                  (equal (r3-m-determinant (rotation-about-witness angle p)) 1)
                  (equal (point-in-r3-y1 p) 0)
                  (equal (+ (* (point-in-r3-x1 p) (point-in-r3-x1 p))
                            (* (point-in-r3-z1 p) (point-in-r3-z1 p)))
                         1))
             (EQUAL (AREF2 :FAKE-NAME
                           (R3-M-INVERSE (ROTATION-ABOUT-WITNESS ANGLE P))
                           0 0)
                    (AREF2 :FAKE-NAME
                           (ROTATION-ABOUT-WITNESS ANGLE P)
                           0 0)))
    :hints (("Goal"
             :use ((:instance r3-rotationp-r-theta-11-1-1-lemma1
                              (x (point-in-r3-x1 p))
                              (z (point-in-r3-z1 p))
                              (s (acl2-sine angle))
                              (c (acl2-cosine angle)))
                   (:instance r3-matrixp-r3-m-inverse (m (rotation-about-witness angle p)))
                   (:instance sin**2+cos**2 (x angle))
                   (:instance r3-matrixp-m-trans (m (rotation-about-witness angle p)))
                   (:instance r3-m-inverse-= (m (rotation-about-witness angle p)))
                   (:instance m-trans-values (m (rotation-about-witness angle p)))
                   (:instance r3-rotationp-r-theta-11-1-lemma4 (p p))
                   (:instance r3-rotationp-r-theta-8 (angle angle))
                   (:instance rotation-about-witness-values (angle angle) (point p))
                   (:instance r3-rotationp-r-theta-10 (angle angle) (p p))
                   (:instance r3-rotationp-r-theta-11-1-1-lemma2 (angle angle) (p p))
                   )
             :in-theory nil
             )))
  )

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd r3-rotationp-r-theta-11-1-2-lemma1
    (implies (and (realp x)
                  (realp z)
                  (realp s)
                  (realp c)
                  (equal (+ (* s s) (* c c)) 1)
                  (equal (+ (* x x) (* z z)) 1))
             (equal (- (* (* (* x z) (- 1 c))
                          (* x s))
                       (* (+ c (* z z (- 1 c)))
                          (- (* z s))))
                    (* z s)))))

(encapsulate
  ()

  (local (include-book "arithmetic/top" :dir :system))

  (defthmd r3-rotationp-r-theta-11-1-2-lemma2
    (implies (and (realp angle)
                  (point-in-r3 p)
                  (equal (r3-m-determinant (rotation-about-witness angle p)) 1)
                  (equal (point-in-r3-y1 p) 0)
                  (equal (aref2 :fake-name (rotation-about-witness angle p) 0 1)
                         (- (* (point-in-r3-x1 p) (point-in-r3-y1 p) (- 1 (acl2-cosine angle)))
                            (* (point-in-r3-z1 p) (acl2-sine angle))))
                  (equal (aref2 :fake-name (rotation-about-witness angle p) 0 2)
                         (+ (* (point-in-r3-x1 p) (point-in-r3-z1 p) (- 1 (acl2-cosine angle)))
                            (* (point-in-r3-y1 p) (acl2-sine angle))))
                  (equal (aref2 :fake-name (rotation-about-witness angle p) 2 1)
                         (+ (* (point-in-r3-z1 p) (point-in-r3-y1 p) (- 1 (acl2-cosine angle)))
                            (* (point-in-r3-x1 p) (acl2-sine angle))))
                  (equal (aref2 :fake-name (rotation-about-witness angle p) 2 2)
                         (+ (acl2-cosine angle)
                            (* (point-in-r3-z1 p) (point-in-r3-z1 p) (- 1 (acl2-cosine angle))))))
             (EQUAL (AREF2 :FAKE-NAME
                           (R3-M-INVERSE (ROTATION-ABOUT-WITNESS ANGLE P))
                           0 1)
                    (- (* (* (* (point-in-r3-x1 p) (point-in-r3-z1 p)) (- 1 (acl2-cosine angle)))
                          (* (point-in-r3-x1 p) (acl2-sine angle)))
                       (* (+ (acl2-cosine angle) (* (point-in-r3-z1 p) (point-in-r3-z1 p) (- 1 (acl2-cosine angle))))
                          (- (* (point-in-r3-z1 p) (acl2-sine angle)))))))
    :hints (("Goal"
             :use ((:instance r3-matrixp-r3-m-inverse (m (rotation-about-witness angle p)))
                   (:instance r3-m-inverse-= (m (rotation-about-witness angle p)))
                   (:instance r3-rotationp-r-theta-10 (angle angle) (p p))
                   (:instance r3-rotationp-r-theta-11-1-lemma4 (p p))
                   )
             :in-theory (e/d () (point-in-r3 r3-matrixp point-in-r3-x1 point-in-r3-y1 point-in-r3-z1 m-trans rotation-about-witness r3-m-determinant point-on-s2-not-d acl2-sqrt sin**2+cos**2 acl2-sqrt r3-m-inverse aref2 aref2-m-trans r3-m-inverse-=)
                             )))
    ))

(encapsulate
  ()

  (local (include-book "arithmetic/top" :dir :system))

  (defthmd r3-rotationp-r-theta-11-1-2
    (implies (and (realp angle)
                  (point-in-r3 p)
                  (equal (r3-m-determinant (rotation-about-witness angle p)) 1)
                  (equal (point-in-r3-y1 p) 0)
                  (equal (+ (* (point-in-r3-x1 p) (point-in-r3-x1 p))
                            (* (point-in-r3-z1 p) (point-in-r3-z1 p)))
                         1))
             (EQUAL (AREF2 :FAKE-NAME
                           (R3-M-INVERSE (ROTATION-ABOUT-WITNESS ANGLE P))
                           0 1)
                    (AREF2 :FAKE-NAME
                           (ROTATION-ABOUT-WITNESS ANGLE P)
                           1 0)))
    :hints (("Goal"
             :use ((:instance r3-rotationp-r-theta-11-1-2-lemma1
                              (x (point-in-r3-x1 p))
                              (z (point-in-r3-z1 p))
                              (s (acl2-sine angle))
                              (c (acl2-cosine angle)))
                   (:instance r3-matrixp-r3-m-inverse (m (rotation-about-witness angle p)))
                   (:instance sin**2+cos**2 (x angle))
                   (:instance r3-matrixp-m-trans (m (rotation-about-witness angle p)))
                   (:instance r3-m-inverse-= (m (rotation-about-witness angle p)))
                   (:instance m-trans-values (m (rotation-about-witness angle p)))
                   (:instance r3-rotationp-r-theta-11-1-lemma4 (p p))
                   (:instance r3-rotationp-r-theta-8 (angle angle))
                   (:instance rotation-about-witness-values (angle angle) (point p))
                   (:instance r3-rotationp-r-theta-10 (angle angle) (p p))
                   (:instance r3-rotationp-r-theta-11-1-2-lemma2 (angle angle) (p p))
                   )
             :in-theory nil
             )))
  )

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd r3-rotationp-r-theta-11-1-3-lemma1
    (implies (and (realp x)
                  (realp z)
                  (realp s)
                  (realp c)
                  (equal (+ (* s s) (* c c)) 1)
                  (equal (+ (* x x) (* z z)) 1))
             (equal (- (* (- (* z s))
                          (- (* x s)))
                       (* c (* x z (- 1 c))))
                    (* z x (- 1 c))))))

(encapsulate
  ()

  (local (include-book "arithmetic/top" :dir :system))

  (defthmd r3-rotationp-r-theta-11-1-3-lemma2
    (implies (and (realp angle)
                  (point-in-r3 p)
                  (equal (r3-m-determinant (rotation-about-witness angle p)) 1)
                  (equal (point-in-r3-y1 p) 0)
                  (equal (aref2 :fake-name (rotation-about-witness angle p) 0 1)
                         (- (* (point-in-r3-x1 p) (point-in-r3-y1 p) (- 1 (acl2-cosine angle)))
                            (* (point-in-r3-z1 p) (acl2-sine angle))))
                  (equal (aref2 :fake-name (rotation-about-witness angle p) 0 2)
                         (+ (* (point-in-r3-x1 p) (point-in-r3-z1 p) (- 1 (acl2-cosine angle)))
                            (* (point-in-r3-y1 p) (acl2-sine angle))))
                  (equal (aref2 :fake-name (rotation-about-witness angle p) 1 1)
                         (+ (acl2-cosine angle)
                            (* (point-in-r3-y1 p) (point-in-r3-y1 p) (- 1 (acl2-cosine angle)))))
                  (equal (aref2 :fake-name (rotation-about-witness angle p) 1 2)
                         (- (* (point-in-r3-y1 p) (point-in-r3-z1 p) (- 1 (acl2-cosine angle)))
                            (* (point-in-r3-x1 p) (acl2-sine angle)))))

             (EQUAL (AREF2 :FAKE-NAME
                           (R3-M-INVERSE (ROTATION-ABOUT-WITNESS ANGLE P))
                           0 2)
                    (- (* (- (* (point-in-r3-z1 p) (acl2-sine angle)))
                          (- (* (point-in-r3-x1 p) (acl2-sine angle))))
                       (* (acl2-cosine angle) (* (point-in-r3-x1 p) (point-in-r3-z1 p) (- 1 (acl2-cosine angle)))))))
    :hints (("Goal"
             :use ((:instance r3-matrixp-r3-m-inverse (m (rotation-about-witness angle p)))
                   (:instance r3-m-inverse-= (m (rotation-about-witness angle p)))
                   (:instance r3-rotationp-r-theta-10 (angle angle) (p p))
                   (:instance r3-rotationp-r-theta-11-1-lemma4 (p p))
                   )
             :in-theory (e/d () (point-in-r3 r3-matrixp point-in-r3-x1 point-in-r3-y1 point-in-r3-z1 m-trans rotation-about-witness r3-m-determinant point-on-s2-not-d acl2-sqrt sin**2+cos**2 acl2-sqrt r3-m-inverse aref2 aref2-m-trans r3-m-inverse-=)
                             )))
    ))

(encapsulate
  ()

  (local (include-book "arithmetic/top" :dir :system))

  (defthmd r3-rotationp-r-theta-11-1-3
    (implies (and (realp angle)
                  (point-in-r3 p)
                  (equal (r3-m-determinant (rotation-about-witness angle p)) 1)
                  (equal (point-in-r3-y1 p) 0)
                  (equal (+ (* (point-in-r3-x1 p) (point-in-r3-x1 p))
                            (* (point-in-r3-z1 p) (point-in-r3-z1 p)))
                         1))
             (EQUAL (AREF2 :FAKE-NAME
                           (R3-M-INVERSE (ROTATION-ABOUT-WITNESS ANGLE P))
                           0 2)
                    (AREF2 :FAKE-NAME
                           (ROTATION-ABOUT-WITNESS ANGLE P)
                           2 0)))
    :hints (("Goal"
             :use ((:instance r3-rotationp-r-theta-11-1-3-lemma1
                              (x (point-in-r3-x1 p))
                              (z (point-in-r3-z1 p))
                              (s (acl2-sine angle))
                              (c (acl2-cosine angle)))
                   (:instance r3-matrixp-r3-m-inverse (m (rotation-about-witness angle p)))
                   (:instance sin**2+cos**2 (x angle))
                   (:instance r3-matrixp-m-trans (m (rotation-about-witness angle p)))
                   (:instance r3-m-inverse-= (m (rotation-about-witness angle p)))
                   (:instance m-trans-values (m (rotation-about-witness angle p)))
                   (:instance r3-rotationp-r-theta-11-1-lemma4 (p p))
                   (:instance r3-rotationp-r-theta-8 (angle angle))
                   (:instance rotation-about-witness-values (angle angle) (point p))
                   (:instance r3-rotationp-r-theta-10 (angle angle) (p p))
                   (:instance r3-rotationp-r-theta-11-1-3-lemma2 (angle angle) (p p))
                   )
             :in-theory nil
             )))
  )

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd r3-rotationp-r-theta-11-1-4-lemma1
    (implies (and (realp x)
                  (realp z)
                  (realp s)
                  (realp c)
                  (equal (+ (* s s) (* c c)) 1)
                  (equal (+ (* x x) (* z z)) 1))
             (equal (- (* (- (* x s))
                          (* z x (- 1 c)))
                       (* (+ c (* z z (- 1 c)))
                          (* z s)))
                    (- (* z s))))))

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd r3-rotationp-r-theta-11-1-4-lemma2
    (implies (and (realp angle)
                  (point-in-r3 p)
                  (equal (r3-m-determinant (rotation-about-witness angle p)) 1)
                  (equal (point-in-r3-y1 p) 0)
                  (equal (aref2 :fake-name (rotation-about-witness angle p) 1 0)
                         (+ (* (point-in-r3-y1 p) (point-in-r3-x1 p) (- 1 (acl2-cosine angle)))
                            (* (point-in-r3-z1 p) (acl2-sine angle))))
                  (equal (aref2 :fake-name (rotation-about-witness angle p) 1 2)
                         (- (* (point-in-r3-y1 p) (point-in-r3-z1 p) (- 1 (acl2-cosine angle)))
                            (* (point-in-r3-x1 p) (acl2-sine angle))))
                  (equal (aref2 :fake-name (rotation-about-witness angle p) 2 0)
                         (- (* (point-in-r3-z1 p) (point-in-r3-x1 p) (- 1 (acl2-cosine angle)))
                            (* (point-in-r3-y1 p) (acl2-sine angle))))
                  (equal (aref2 :fake-name (rotation-about-witness angle p) 2 2)
                         (+ (acl2-cosine angle)
                            (* (point-in-r3-z1 p) (point-in-r3-z1 p) (- 1 (acl2-cosine angle))))))

             (EQUAL (AREF2 :FAKE-NAME
                           (R3-M-INVERSE (ROTATION-ABOUT-WITNESS ANGLE P))
                           1 0)
                    (- (* (- (* (point-in-r3-x1 p) (acl2-sine angle)))
                          (* (point-in-r3-z1 p) (point-in-r3-x1 p) (- 1 (acl2-cosine angle))))
                       (* (+ (acl2-cosine angle) (* (point-in-r3-z1 p) (point-in-r3-z1 p) (- 1 (acl2-cosine angle))))
                          (* (point-in-r3-z1 p) (acl2-sine angle))))))
    :hints (("Goal"
             :use ((:instance r3-matrixp-r3-m-inverse (m (rotation-about-witness angle p)))
                   (:instance r3-m-inverse-= (m (rotation-about-witness angle p)))
                   (:instance r3-rotationp-r-theta-10 (angle angle) (p p))
                   (:instance r3-rotationp-r-theta-11-1-lemma4 (p p))
                   )
             :in-theory (e/d () (point-in-r3 r3-matrixp point-in-r3-x1 point-in-r3-y1 point-in-r3-z1 m-trans rotation-about-witness r3-m-determinant point-on-s2-not-d acl2-sqrt sin**2+cos**2 acl2-sqrt r3-m-inverse aref2 aref2-m-trans r3-m-inverse-=)
                             )))
    ))

(encapsulate
  ()

  (local (include-book "arithmetic/top" :dir :system))

  (defthmd r3-rotationp-r-theta-11-1-4
    (implies (and (realp angle)
                  (point-in-r3 p)
                  (equal (r3-m-determinant (rotation-about-witness angle p)) 1)
                  (equal (point-in-r3-y1 p) 0)
                  (equal (+ (* (point-in-r3-x1 p) (point-in-r3-x1 p))
                            (* (point-in-r3-z1 p) (point-in-r3-z1 p)))
                         1))
             (EQUAL (AREF2 :FAKE-NAME
                           (R3-M-INVERSE (ROTATION-ABOUT-WITNESS ANGLE P))
                           1 0)
                    (AREF2 :FAKE-NAME
                           (ROTATION-ABOUT-WITNESS ANGLE P)
                           0 1)))
    :hints (("Goal"
             :use ((:instance r3-rotationp-r-theta-11-1-4-lemma1
                              (x (point-in-r3-x1 p))
                              (z (point-in-r3-z1 p))
                              (s (acl2-sine angle))
                              (c (acl2-cosine angle)))
                   (:instance r3-matrixp-r3-m-inverse (m (rotation-about-witness angle p)))
                   (:instance sin**2+cos**2 (x angle))
                   (:instance r3-matrixp-m-trans (m (rotation-about-witness angle p)))
                   (:instance r3-m-inverse-= (m (rotation-about-witness angle p)))
                   (:instance m-trans-values (m (rotation-about-witness angle p)))
                   (:instance r3-rotationp-r-theta-11-1-lemma4 (p p))
                   (:instance r3-rotationp-r-theta-8 (angle angle))
                   (:instance rotation-about-witness-values (angle angle) (point p))
                   (:instance r3-rotationp-r-theta-10 (angle angle) (p p))
                   (:instance r3-rotationp-r-theta-11-1-4-lemma2 (angle angle) (p p))
                   )
             :in-theory nil
             )))
  )

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd r3-rotationp-r-theta-11-1-5-lemma1
    (implies (and (realp x)
                  (realp z)
                  (realp s)
                  (realp c)
                  (equal (+ (* s s) (* c c)) 1)
                  (equal (+ (* x x) (* z z)) 1))
             (equal (- (* (+ c (* x x (- 1 c)))
                          (+ c (* z z (- 1 c))))
                       (* (* z x (- 1 c))
                          (* x z (- 1 c))))
                    c))))

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd r3-rotationp-r-theta-11-1-5-lemma2
    (implies (and (realp angle)
                  (point-in-r3 p)
                  (equal (r3-m-determinant (rotation-about-witness angle p)) 1)
                  (equal (point-in-r3-y1 p) 0)
                  (equal (aref2 :fake-name (rotation-about-witness angle p) 0 0)
                         (+ (acl2-cosine angle)
                            (* (point-in-r3-x1 p) (point-in-r3-x1 p) (- 1 (acl2-cosine angle)))))
                  (equal (aref2 :fake-name (rotation-about-witness angle p) 2 2)
                         (+ (acl2-cosine angle)
                            (* (point-in-r3-z1 p) (point-in-r3-z1 p) (- 1 (acl2-cosine angle)))))
                  (equal (aref2 :fake-name (rotation-about-witness angle p) 0 2)
                         (+ (* (point-in-r3-x1 p) (point-in-r3-z1 p) (- 1 (acl2-cosine angle)))
                            (* (point-in-r3-y1 p) (acl2-sine angle))))
                  (equal (aref2 :fake-name (rotation-about-witness angle p) 2 0)
                         (- (* (point-in-r3-z1 p) (point-in-r3-x1 p) (- 1 (acl2-cosine angle)))
                            (* (point-in-r3-y1 p) (acl2-sine angle)))))
             (EQUAL (AREF2 :FAKE-NAME
                           (R3-M-INVERSE (ROTATION-ABOUT-WITNESS ANGLE P))
                           1 1)
                    (- (* (+ (acl2-cosine angle) (* (point-in-r3-x1 p) (point-in-r3-x1 p) (- 1 (acl2-cosine angle))))
                          (+ (acl2-cosine angle) (* (point-in-r3-z1 p) (point-in-r3-z1 p) (- 1 (acl2-cosine angle)))))
                       (* (* (point-in-r3-z1 p) (point-in-r3-x1 p) (- 1 (acl2-cosine angle)))
                          (* (point-in-r3-x1 p) (point-in-r3-z1 p) (- 1 (acl2-cosine angle)))))))
    :hints (("Goal"
             :use ((:instance r3-matrixp-r3-m-inverse (m (rotation-about-witness angle p)))
                   (:instance r3-m-inverse-= (m (rotation-about-witness angle p)))
                   (:instance r3-rotationp-r-theta-10 (angle angle) (p p))
                   (:instance r3-rotationp-r-theta-11-1-lemma4 (p p))
                   )
             :in-theory (e/d () (point-in-r3 r3-matrixp point-in-r3-x1 point-in-r3-y1 point-in-r3-z1 m-trans rotation-about-witness r3-m-determinant point-on-s2-not-d acl2-sqrt sin**2+cos**2 acl2-sqrt r3-m-inverse aref2 aref2-m-trans r3-m-inverse-=)
                             )))
    ))

(encapsulate
  ()

  (local (include-book "arithmetic/top" :dir :system))

  (defthmd r3-rotationp-r-theta-11-1-5
    (implies (and (realp angle)
                  (point-in-r3 p)
                  (equal (r3-m-determinant (rotation-about-witness angle p)) 1)
                  (equal (point-in-r3-y1 p) 0)
                  (equal (+ (* (point-in-r3-x1 p) (point-in-r3-x1 p))
                            (* (point-in-r3-z1 p) (point-in-r3-z1 p)))
                         1))
             (EQUAL (AREF2 :FAKE-NAME
                           (R3-M-INVERSE (ROTATION-ABOUT-WITNESS ANGLE P))
                           1 1)
                    (AREF2 :FAKE-NAME
                           (ROTATION-ABOUT-WITNESS ANGLE P)
                           1 1)))
    :hints (("Goal"
             :use ((:instance r3-rotationp-r-theta-11-1-5-lemma1
                              (x (point-in-r3-x1 p))
                              (z (point-in-r3-z1 p))
                              (s (acl2-sine angle))
                              (c (acl2-cosine angle)))
                   (:instance r3-matrixp-r3-m-inverse (m (rotation-about-witness angle p)))
                   (:instance sin**2+cos**2 (x angle))
                   (:instance r3-matrixp-m-trans (m (rotation-about-witness angle p)))
                   (:instance r3-m-inverse-= (m (rotation-about-witness angle p)))
                   (:instance m-trans-values (m (rotation-about-witness angle p)))
                   (:instance r3-rotationp-r-theta-11-1-lemma4 (p p))
                   (:instance r3-rotationp-r-theta-8 (angle angle))
                   (:instance rotation-about-witness-values (angle angle) (point p))
                   (:instance r3-rotationp-r-theta-10 (angle angle) (p p))
                   (:instance r3-rotationp-r-theta-11-1-5-lemma2 (angle angle) (p p))
                   )
             :in-theory nil
             )))
  )

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd r3-rotationp-r-theta-11-1-6-lemma1
    (implies (and (realp x)
                  (realp z)
                  (realp s)
                  (realp c)
                  (equal (+ (* s s) (* c c)) 1)
                  (equal (+ (* x x) (* z z)) 1))
             (equal (- (* (* x z (- 1 c)) (* z s))
                       (* (- (* x s)) (+ c (* x x (- 1 c)))))
                    (* x s)))))

(encapsulate
  ()

  (local (include-book "arithmetic/top" :dir :system))

  (defthmd r3-rotationp-r-theta-11-1-6-lemma2
    (implies (and (realp angle)
                  (point-in-r3 p)
                  (equal (r3-m-determinant (rotation-about-witness angle p)) 1)
                  (equal (point-in-r3-y1 p) 0)
                  (equal (aref2 :fake-name (rotation-about-witness angle p) 0 0)
                         (+ (acl2-cosine angle)
                            (* (point-in-r3-x1 p) (point-in-r3-x1 p) (- 1 (acl2-cosine angle)))))
                  (equal (aref2 :fake-name (rotation-about-witness angle p) 0 2)
                         (+ (* (point-in-r3-x1 p) (point-in-r3-z1 p) (- 1 (acl2-cosine angle)))
                            (* (point-in-r3-y1 p) (acl2-sine angle))))
                  (equal (aref2 :fake-name (rotation-about-witness angle p) 1 0)
                         (+ (* (point-in-r3-y1 p) (point-in-r3-x1 p) (- 1 (acl2-cosine angle)))
                            (* (point-in-r3-z1 p) (acl2-sine angle))))
                  (equal (aref2 :fake-name (rotation-about-witness angle p) 1 2)
                         (- (* (point-in-r3-y1 p) (point-in-r3-z1 p) (- 1 (acl2-cosine angle)))
                            (* (point-in-r3-x1 p) (acl2-sine angle)))))

             (EQUAL (AREF2 :FAKE-NAME
                           (R3-M-INVERSE (ROTATION-ABOUT-WITNESS ANGLE P))
                           1 2)
                    (- (* (* (point-in-r3-x1 p) (point-in-r3-z1 p) (- 1 (acl2-cosine angle)))
                          (* (point-in-r3-z1 p) (acl2-sine angle)))
                       (* (- (* (point-in-r3-x1 p) (acl2-sine angle)))
                          (+ (acl2-cosine angle) (* (point-in-r3-x1 p)
                                                    (point-in-r3-x1 p)
                                                    (- 1 (acl2-cosine angle))))))
                    ))
    :hints (("Goal"
             :use ((:instance r3-matrixp-r3-m-inverse (m (rotation-about-witness angle p)))
                   (:instance r3-m-inverse-= (m (rotation-about-witness angle p)))
                   (:instance r3-rotationp-r-theta-10 (angle angle) (p p))
                   (:instance r3-rotationp-r-theta-11-1-lemma4 (p p))
                   )
             :in-theory (e/d () (point-in-r3-x1 point-in-r3-y1 point-in-r3-z1 m-trans rotation-about-witness r3-m-determinant point-on-s2-not-d acl2-sqrt sin**2+cos**2 acl2-sqrt r3-m-inverse aref2 aref2-m-trans r3-m-inverse-=))
             )
            ))
  )

(encapsulate
  ()

  (local (include-book "arithmetic/top" :dir :system))

  (defthmd r3-rotationp-r-theta-11-1-6
    (implies (and (realp angle)
                  (point-in-r3 p)
                  (equal (r3-m-determinant (rotation-about-witness angle p)) 1)
                  (equal (point-in-r3-y1 p) 0)
                  (equal (+ (* (point-in-r3-x1 p) (point-in-r3-x1 p))
                            (* (point-in-r3-z1 p) (point-in-r3-z1 p)))
                         1))
             (EQUAL (AREF2 :FAKE-NAME
                           (R3-M-INVERSE (ROTATION-ABOUT-WITNESS ANGLE P))
                           1 2)
                    (AREF2 :FAKE-NAME
                           (ROTATION-ABOUT-WITNESS ANGLE P)
                           2 1)))
    :hints (("Goal"
             :use ((:instance r3-rotationp-r-theta-11-1-6-lemma1
                              (x (point-in-r3-x1 p))
                              (z (point-in-r3-z1 p))
                              (s (acl2-sine angle))
                              (c (acl2-cosine angle)))
                   (:instance r3-matrixp-r3-m-inverse (m (rotation-about-witness angle p)))
                   (:instance sin**2+cos**2 (x angle))
                   (:instance r3-matrixp-m-trans (m (rotation-about-witness angle p)))
                   (:instance r3-m-inverse-= (m (rotation-about-witness angle p)))
                   (:instance m-trans-values (m (rotation-about-witness angle p)))
                   (:instance r3-rotationp-r-theta-11-1-lemma4 (p p))
                   (:instance r3-rotationp-r-theta-8 (angle angle))
                   (:instance rotation-about-witness-values (angle angle) (point p))
                   (:instance r3-rotationp-r-theta-10 (angle angle) (p p))
                   (:instance r3-rotationp-r-theta-11-1-6-lemma2 (angle angle) (p p))
                   )
             :in-theory nil
             )))
  )

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd r3-rotationp-r-theta-11-1-7-lemma1
    (implies (and (realp x)
                  (realp z)
                  (realp s)
                  (realp c)
                  (equal (+ (* s s) (* c c)) 1)
                  (equal (+ (* x x) (* z z)) 1))
             (equal (- (* (* z s) (* x s))
                       (* (* z x) (- 1 c) c))
                    (* x z (- 1 c))))))

(encapsulate
  ()

  (local (include-book "arithmetic/top" :dir :system))

  (defthmd r3-rotationp-r-theta-11-1-7-lemma2
    (implies (and (realp angle)
                  (point-in-r3 p)
                  (equal (r3-m-determinant (rotation-about-witness angle p)) 1)
                  (equal (point-in-r3-y1 p) 0)
                  (equal (aref2 :fake-name (rotation-about-witness angle p) 1 0)
                         (+ (* (point-in-r3-y1 p) (point-in-r3-x1 p) (- 1 (acl2-cosine angle)))
                            (* (point-in-r3-z1 p) (acl2-sine angle))))
                  (equal (aref2 :fake-name (rotation-about-witness angle p) 1 1)
                         (+ (acl2-cosine angle)
                            (* (point-in-r3-y1 p) (point-in-r3-y1 p) (- 1 (acl2-cosine angle)))))
                  (equal (aref2 :fake-name (rotation-about-witness angle p) 2 0)
                         (- (* (point-in-r3-z1 p) (point-in-r3-x1 p) (- 1 (acl2-cosine angle)))
                            (* (point-in-r3-y1 p) (acl2-sine angle))))
                  (equal (aref2 :fake-name (rotation-about-witness angle p) 2 1)
                         (+ (* (point-in-r3-z1 p) (point-in-r3-y1 p) (- 1 (acl2-cosine angle)))
                            (* (point-in-r3-x1 p) (acl2-sine angle)))))
             (EQUAL (AREF2 :FAKE-NAME
                           (R3-M-INVERSE (ROTATION-ABOUT-WITNESS ANGLE P))
                           2 0)
                    (- (* (* (point-in-r3-z1 p) (acl2-sine angle))
                          (* (point-in-r3-x1 p) (acl2-sine angle)))
                       (* (* (point-in-r3-z1 p) (point-in-r3-x1 p)) (- 1 (acl2-cosine angle))
                          (acl2-cosine angle)))
                    ))
    :hints (("Goal"
             :use ((:instance r3-matrixp-r3-m-inverse (m (rotation-about-witness angle p)))
                   (:instance r3-m-inverse-= (m (rotation-about-witness angle p)))
                   (:instance r3-rotationp-r-theta-10 (angle angle) (p p))
                   (:instance r3-rotationp-r-theta-11-1-lemma4 (p p))
                   )
             :in-theory (e/d () (point-in-r3-x1 point-in-r3-y1 point-in-r3-z1 m-trans rotation-about-witness r3-m-determinant point-on-s2-not-d acl2-sqrt sin**2+cos**2 acl2-sqrt r3-m-inverse aref2 aref2-m-trans r3-m-inverse-=))
             )
            ))
  )

(encapsulate
  ()

  (local (include-book "arithmetic/top" :dir :system))

  (defthmd r3-rotationp-r-theta-11-1-7
    (implies (and (realp angle)
                  (point-in-r3 p)
                  (equal (r3-m-determinant (rotation-about-witness angle p)) 1)
                  (equal (point-in-r3-y1 p) 0)
                  (equal (+ (* (point-in-r3-x1 p) (point-in-r3-x1 p))
                            (* (point-in-r3-z1 p) (point-in-r3-z1 p)))
                         1))
             (EQUAL (AREF2 :FAKE-NAME
                           (R3-M-INVERSE (ROTATION-ABOUT-WITNESS ANGLE P))
                           2 0)
                    (AREF2 :FAKE-NAME
                           (ROTATION-ABOUT-WITNESS ANGLE P)
                           0 2)))
    :hints (("Goal"
             :use ((:instance r3-rotationp-r-theta-11-1-7-lemma1
                              (x (point-in-r3-x1 p))
                              (z (point-in-r3-z1 p))
                              (s (acl2-sine angle))
                              (c (acl2-cosine angle)))
                   (:instance r3-matrixp-r3-m-inverse (m (rotation-about-witness angle p)))
                   (:instance sin**2+cos**2 (x angle))
                   (:instance r3-matrixp-m-trans (m (rotation-about-witness angle p)))
                   (:instance r3-m-inverse-= (m (rotation-about-witness angle p)))
                   (:instance m-trans-values (m (rotation-about-witness angle p)))
                   (:instance r3-rotationp-r-theta-11-1-lemma4 (p p))
                   (:instance r3-rotationp-r-theta-8 (angle angle))
                   (:instance rotation-about-witness-values (angle angle) (point p))
                   (:instance r3-rotationp-r-theta-10 (angle angle) (p p))
                   (:instance r3-rotationp-r-theta-11-1-7-lemma2 (angle angle) (p p))
                   )
             :in-theory nil
             )))
  )

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd r3-rotationp-r-theta-11-1-8-lemma1
    (implies (and (realp x)
                  (realp z)
                  (realp s)
                  (realp c)
                  (equal (+ (* s s) (* c c)) 1)
                  (equal (+ (* x x) (* z z)) 1))
             (equal (- (* (- (* z s)) (* z x) (- 1 c))
                       (* (* x s) (+ c (* x x (- 1 c)))))
                    (- (* x s)))))

  (defthmd r3-rotationp-r-theta-11-1-8-lemma3
    (implies (and (realp x)
                  (realp z)
                  (realp s)
                  (realp c))
             (equal (- (* (- (* z s)) (* z x) (- 1 c))
                       (* (* x s) (+ c (* x x (- 1 c)))))
                    (+ (- (* z z s x))
                       (* z z s x c)
                       (- (* x s c))
                       (- (* x x x s))
                       (* x x x s c)))))
  )

(encapsulate
  ()

  (local (include-book "arithmetic/top" :dir :system))

  (defthmd r3-rotationp-r-theta-11-1-8-lemma2
    (implies (and (realp angle)
                  (point-in-r3 p)
                  (equal (r3-m-determinant (rotation-about-witness angle p)) 1)
                  (equal (point-in-r3-y1 p) 0)
                  (equal (aref2 :fake-name (rotation-about-witness angle p) 0 0)
                         (+ (acl2-cosine angle)
                            (* (point-in-r3-x1 p) (point-in-r3-x1 p) (- 1 (acl2-cosine angle)))))
                  (equal (aref2 :fake-name (rotation-about-witness angle p) 2 1)
                         (+ (* (point-in-r3-z1 p) (point-in-r3-y1 p) (- 1 (acl2-cosine angle)))
                            (* (point-in-r3-x1 p) (acl2-sine angle))))
                  (equal (aref2 :fake-name (rotation-about-witness angle p) 2 0)
                         (- (* (point-in-r3-z1 p) (point-in-r3-x1 p) (- 1 (acl2-cosine angle)))
                            (* (point-in-r3-y1 p) (acl2-sine angle))))
                  (equal (aref2 :fake-name (rotation-about-witness angle p) 0 1)
                         (- (* (point-in-r3-x1 p) (point-in-r3-y1 p) (- 1 (acl2-cosine angle)))
                            (* (point-in-r3-z1 p) (acl2-sine angle)))))
             (EQUAL (AREF2 :FAKE-NAME
                           (R3-M-INVERSE (ROTATION-ABOUT-WITNESS ANGLE P))
                           2 1)
                    (+ (- (* (point-in-r3-z1 p) (point-in-r3-z1 p) (acl2-sine angle) (point-in-r3-x1 p)))
                       (* (point-in-r3-z1 p) (point-in-r3-z1 p) (acl2-sine angle) (point-in-r3-x1 p)
                          (acl2-cosine angle))
                       (- (* (point-in-r3-x1 p) (acl2-sine angle) (acl2-cosine angle)))
                       (- (* (point-in-r3-x1 p) (point-in-r3-x1 p) (point-in-r3-x1 p) (acl2-sine angle)))
                       (* (point-in-r3-x1 p) (point-in-r3-x1 p) (point-in-r3-x1 p) (acl2-sine angle)
                          (acl2-cosine angle)))
                    ))
    :hints (("Goal"
             :use ((:instance r3-matrixp-r3-m-inverse (m (rotation-about-witness angle p)))
                   (:instance r3-m-inverse-= (m (rotation-about-witness angle p)))
                   (:instance r3-rotationp-r-theta-10 (angle angle) (p p))
                   (:instance r3-rotationp-r-theta-11-1-lemma4 (p p))
                   )
             :in-theory (e/d () (point-in-r3-x1 point-in-r3-y1 point-in-r3-z1 m-trans rotation-about-witness r3-m-determinant point-on-s2-not-d acl2-sqrt sin**2+cos**2 acl2-sqrt r3-m-inverse aref2 aref2-m-trans r3-m-inverse-=))
             )
            ))
  )

(encapsulate
  ()

  (local (include-book "arithmetic/top" :dir :system))

  (defthmd r3-rotationp-r-theta-11-1-8
    (implies (and (realp angle)
                  (point-in-r3 p)
                  (equal (r3-m-determinant (rotation-about-witness angle p)) 1)
                  (equal (point-in-r3-y1 p) 0)
                  (equal (+ (* (point-in-r3-x1 p) (point-in-r3-x1 p))
                            (* (point-in-r3-z1 p) (point-in-r3-z1 p)))
                         1))
             (EQUAL (AREF2 :FAKE-NAME
                           (R3-M-INVERSE (ROTATION-ABOUT-WITNESS ANGLE P))
                           2 1)
                    (AREF2 :FAKE-NAME
                           (ROTATION-ABOUT-WITNESS ANGLE P)
                           1 2)))
    :hints (("Goal"
             :use ((:instance r3-rotationp-r-theta-11-1-8-lemma1
                              (x (point-in-r3-x1 p))
                              (z (point-in-r3-z1 p))
                              (s (acl2-sine angle))
                              (c (acl2-cosine angle)))
                   (:instance r3-rotationp-r-theta-11-1-8-lemma3
                              (x (point-in-r3-x1 p))
                              (z (point-in-r3-z1 p))
                              (s (acl2-sine angle))
                              (c (acl2-cosine angle)))
                   (:instance r3-matrixp-r3-m-inverse (m (rotation-about-witness angle p)))
                   (:instance sin**2+cos**2 (x angle))
                   (:instance r3-matrixp-m-trans (m (rotation-about-witness angle p)))
                   (:instance r3-m-inverse-= (m (rotation-about-witness angle p)))
                   (:instance m-trans-values (m (rotation-about-witness angle p)))
                   (:instance r3-rotationp-r-theta-11-1-lemma4 (p p))
                   (:instance r3-rotationp-r-theta-8 (angle angle))
                   (:instance rotation-about-witness-values (angle angle) (point p))
                   (:instance r3-rotationp-r-theta-10 (angle angle) (p p))
                   (:instance r3-rotationp-r-theta-11-1-8-lemma2 (angle angle) (p p))
                   )
             :in-theory nil
             )))
  )

(encapsulate
  ()

  (local (include-book "arithmetic/top" :dir :system))

  (defthmd r3-rotationp-r-theta-11-1-9-lemma1
    (implies (and (realp x)
                  (realp z)
                  (realp s)
                  (realp c)
                  (equal (* s s) (- 1 (* c c)))
                  (equal (* x x) (- 1 (* z z))))
             (equal (- (* (+ c (* x x (- 1 c))) c)
                       (* (* z s) (- (* z s))))
                    (+ (* c x x) (* z z))))
    :hints (("Goal"
             :use ((:instance r3-rotationp-r-theta-11-1-lemma2 (a (* c c)) (c (* x x)))
                   (:instance r3-rotationp-r-theta-11-1-lemma3 (a (* z z)) (b (* c c)) (c (* s s)))
                   (:instance r3-rotationp-r-theta-11-1-lemma1 (s s) (c c))
                   (:instance r3-rotationp-r-theta-11-1-lemma1 (s z) (c x))
                   ))
            ("Subgoal 1"
             :use((:instance r3-rotationp-r-theta-11-1-lemma2 (a (* c c)) (c (* x x)))
                  (:instance r3-rotationp-r-theta-11-1-lemma3 (a (* z z)) (b (* c c)) (c (* s s)))
                  (:instance r3-rotationp-r-theta-11-1-lemma1 (s s) (c c))
                  (:instance r3-rotationp-r-theta-11-1-lemma1 (s z) (c x)))
             )))

  (defthmd r3-rotationp-r-theta-11-1-9-lemma2
    (implies (and (realp x)
                  (realp z)
                  (realp s)
                  (realp c)
                  (equal (+ (* s s) (* c c)) 1)
                  (equal (+ (* x x) (* z z)) 1))
             (equal (- (* (+ c (* x x (- 1 c))) c)
                       (* (* z s) (- (* z s))))
                    (+ c (* z z) (- (* z z c)))))
    :hints (("Goal"
             :use ((:instance r3-rotationp-r-theta-11-1-9-lemma1)
                   (:instance r3-rotationp-r-theta-11-1-lemma1 (s x) (c z)))
             )))
  )

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd r3-rotationp-r-theta-11-1-9-lemma3
    (implies (and (realp angle)
                  (point-in-r3 p)
                  (equal (r3-m-determinant (rotation-about-witness angle p)) 1)
                  (equal (point-in-r3-y1 p) 0)
                  (equal (+ (* (point-in-r3-x1 p) (point-in-r3-x1 p))
                            (* (point-in-r3-z1 p) (point-in-r3-z1 p)))
                         1))
             (EQUAL (AREF2 :FAKE-NAME
                           (R3-M-INVERSE (ROTATION-ABOUT-WITNESS ANGLE P))
                           2 2)
                    (- (* (+ (acl2-cosine angle) (* (point-in-r3-x1 p) (point-in-r3-x1 p) (- 1 (acl2-cosine angle)))) (acl2-cosine angle))
                       (* (* (point-in-r3-z1 p) (acl2-sine angle)) (- (* (point-in-r3-z1 p) (acl2-sine angle)))))))
    :hints (("Goal"
             :use ((:instance r3-matrixp-r3-m-inverse (m (rotation-about-witness angle p)))
                   (:instance r3-m-inverse-= (m (rotation-about-witness angle p)))
                   (:instance rotation-about-witness-values (angle angle) (point p))
                   (:instance r3-rotationp-r-theta-10 (angle angle) (p p))
                   (:instance r3-rotationp-r-theta-11-1-lemma4 (p p))
                   )
             :in-theory (e/d () (point-in-r3-x1 point-in-r3-y1 point-in-r3-z1 m-trans rotation-about-witness r3-m-determinant point-on-s2-not-d acl2-sqrt sin**2+cos**2 acl2-sqrt r3-m-inverse aref2 aref2-m-trans r3-m-inverse-=))
             )))

  (defthmd r3-rotationp-r-theta-11-1-9
    (implies (and (realp angle)
                  (point-in-r3 p)
                  (equal (r3-m-determinant (rotation-about-witness angle p)) 1)
                  (equal (point-in-r3-y1 p) 0)
                  (equal (+ (* (point-in-r3-x1 p) (point-in-r3-x1 p))
                            (* (point-in-r3-z1 p) (point-in-r3-z1 p)))
                         1))
             (EQUAL (AREF2 :FAKE-NAME
                           (R3-M-INVERSE (ROTATION-ABOUT-WITNESS ANGLE P))
                           2 2)
                    (AREF2 :FAKE-NAME
                           (ROTATION-ABOUT-WITNESS ANGLE P)
                           2 2)))
    :hints (("Goal"
             :use ((:instance r3-rotationp-r-theta-11-1-9-lemma2
                              (x (point-in-r3-x1 p))
                              (z (point-in-r3-z1 p))
                              (s (acl2-sine angle))
                              (c (acl2-cosine angle)))
                   (:instance sin**2+cos**2 (x angle))
                   (:instance r3-matrixp-r3-m-inverse (m (rotation-about-witness angle p)))
                   (:instance r3-matrixp-m-trans (m (rotation-about-witness angle p)))
                   (:instance r3-m-inverse-= (m (rotation-about-witness angle p)))
                   (:instance m-trans-values (m (rotation-about-witness angle p)))
                   (:instance r3-rotationp-r-theta-11-1-lemma4 (p p))
                   (:instance r3-rotationp-r-theta-8 (angle angle))
                   (:instance rotation-about-witness-values (angle angle) (point p))
                   (:instance r3-rotationp-r-theta-10 (angle angle) (p p))
                   (:instance r3-rotationp-r-theta-11-1-9-lemma3 (angle angle) (p p))
                   )
             :in-theory (e/d () (point-in-r3-x1 point-in-r3-y1 point-in-r3-z1 m-trans rotation-about-witness r3-m-determinant point-on-s2-not-d acl2-sqrt sin**2+cos**2 acl2-sqrt r3-m-inverse aref2 aref2-m-trans r3-m-inverse-=))
             )))
  )

(defthmd r3-rotationp-r-theta-11-1
  (implies (and (realp angle)
                (equal (r3-m-determinant (rotation-about-witness angle p)) 1)
                (point-in-r3 p)
                (equal (point-in-r3-y1 p) 0)
                (equal (+ (* (point-in-r3-x1 p) (point-in-r3-x1 p))
                          (* (point-in-r3-z1 p) (point-in-r3-z1 p)))
                       1))
           (and (EQUAL (AREF2 :FAKE-NAME
                              (R3-M-INVERSE (ROTATION-ABOUT-WITNESS ANGLE P))
                              2 2)
                       (AREF2 :FAKE-NAME
                              (ROTATION-ABOUT-WITNESS ANGLE P)
                              2 2))
                (EQUAL (AREF2 :FAKE-NAME
                              (R3-M-INVERSE (ROTATION-ABOUT-WITNESS ANGLE P))
                              2 1)
                       (AREF2 :FAKE-NAME
                              (ROTATION-ABOUT-WITNESS ANGLE P)
                              1 2))
                (EQUAL (AREF2 :FAKE-NAME
                              (R3-M-INVERSE (ROTATION-ABOUT-WITNESS ANGLE P))
                              2 0)
                       (AREF2 :FAKE-NAME
                              (ROTATION-ABOUT-WITNESS ANGLE P)
                              0 2))
                (EQUAL (AREF2 :FAKE-NAME
                              (R3-M-INVERSE (ROTATION-ABOUT-WITNESS ANGLE P))
                              1 2)
                       (AREF2 :FAKE-NAME
                              (ROTATION-ABOUT-WITNESS ANGLE P)
                              2 1))
                (EQUAL (AREF2 :FAKE-NAME
                              (R3-M-INVERSE (ROTATION-ABOUT-WITNESS ANGLE P))
                              1 1)
                       (AREF2 :FAKE-NAME
                              (ROTATION-ABOUT-WITNESS ANGLE P)
                              1 1))
                (EQUAL (AREF2 :FAKE-NAME
                              (R3-M-INVERSE (ROTATION-ABOUT-WITNESS ANGLE P))
                              1 0)
                       (AREF2 :FAKE-NAME
                              (ROTATION-ABOUT-WITNESS ANGLE P)
                              0 1))
                (EQUAL (AREF2 :FAKE-NAME
                              (R3-M-INVERSE (ROTATION-ABOUT-WITNESS ANGLE P))
                              0 2)
                       (AREF2 :FAKE-NAME
                              (ROTATION-ABOUT-WITNESS ANGLE P)
                              2 0))
                (EQUAL (AREF2 :FAKE-NAME
                              (R3-M-INVERSE (ROTATION-ABOUT-WITNESS ANGLE P))
                              0 1)
                       (AREF2 :FAKE-NAME
                              (ROTATION-ABOUT-WITNESS ANGLE P)
                              1 0))
                (EQUAL (AREF2 :FAKE-NAME
                              (R3-M-INVERSE (ROTATION-ABOUT-WITNESS ANGLE P))
                              0 0)
                       (AREF2 :FAKE-NAME
                              (ROTATION-ABOUT-WITNESS ANGLE P)
                              0 0))
                ))
  :hints (("Goal"
           :use ((:instance r3-rotationp-r-theta-11-1-9)
                 (:instance r3-rotationp-r-theta-11-1-8)
                 (:instance r3-rotationp-r-theta-11-1-7)
                 (:instance r3-rotationp-r-theta-11-1-6)
                 (:instance r3-rotationp-r-theta-11-1-5)
                 (:instance r3-rotationp-r-theta-11-1-4)
                 (:instance r3-rotationp-r-theta-11-1-3)
                 (:instance r3-rotationp-r-theta-11-1-2)
                 (:instance r3-rotationp-r-theta-11-1-1)
                 )
           )))

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd r3-rotationp-r-theta-11
    (implies (and (realp angle)
                  (equal (r3-m-determinant (rotation-about-witness angle p)) 1)
                  (point-in-r3 p)
                  (equal (point-in-r3-y1 p) 0)
                  (equal (+ (* (point-in-r3-x1 p) (point-in-r3-x1 p))
                            (* (point-in-r3-z1 p) (point-in-r3-z1 p)))
                         1))
             (m-= (r3-m-inverse (rotation-about-witness angle p))
                  (m-trans (rotation-about-witness angle p))))
    :hints (("Goal"
             :use ((:instance sin**2+cos**2 (x angle))
                   (:instance r3-rotationp-r-theta-8)
                   (:instance rotation-about-witness-values (angle angle) (point p))
                   (:instance r3-rotationp-r-theta-10 (angle angle) (p p))
                   (:instance r3-matrixp-r3-m-inverse (m (rotation-about-witness angle p)))
                   (:instance r3-matrixp-m-trans (m (rotation-about-witness angle p)))
                   (:instance r3-m-inverse-= (m (rotation-about-witness angle p)))
                   (:instance m-trans-values (m (rotation-about-witness angle p)))
                   (:instance r3-rotationp-r-theta-11-1)
                   )
             :in-theory (e/d (m-= header dimensions alist2p) (point-in-r3-x1 point-in-r3-y1 point-in-r3-z1 m-trans rotation-about-witness r3-m-determinant point-on-s2-not-d acl2-sqrt sin**2+cos**2 acl2-sqrt r3-m-inverse aref2 aref2-m-trans r3-m-inverse-=))
             )))
  )

(defthmd r3-rotationp-r-theta
  (implies (realp angle)
           (r3-rotationp (rotation-about-witness angle (point-on-s2-not-d))))
  :hints (("Goal"
           :use ((:instance r3-rotationp-r-theta-11 (angle angle) (p (point-on-s2-not-d)))
                 (:instance r3-rotationp-r-theta-10 (angle angle) (p (point-on-s2-not-d)))
                 (:instance r3-rotationp-r-theta-2 (point (point-on-s2-not-d)))
                 (:instance r3-rotationp-r-theta-5 (point (point-on-s2-not-d)))
                 (:instance exists-point-on-s2-not-d-2)
                 (:instance s2-def-p (point (point-on-s2-not-d)))
                 (:instance r3-rotationp (m (rotation-about-witness angle (point-on-s2-not-d))))
                 (:instance r3-rotationp-r-theta-1 (angle angle)))
           :in-theory nil
           )))

(defthmd r-theta-0=id
  (implies (point-in-r3 u)
           (m-= (rotation-about-witness 0 u)
                (id-rotation)))
  :hints (("Goal"
           :in-theory (enable m-= aref2 dimensions header)
           )))

(defthmd r-theta*p=p=>r--theta*p=p-1
  (implies (m-= m1 m2)
           (m-= (m-* m3 m1) (m-* m3 m2))))

(defthmd r-theta*p=p=>r--theta*p=p-2
  (implies (m-= (m-* m1 m2 m3) (m-* m4 m5))
           (m-= (m-* (m-* m1 m2) m3) (m-* m4 m5))))

(defthmd r-theta*p=p=>r--theta*p=p
  (implies (and (point-in-r3 p)
                (point-in-r3 u)
                (equal (+ (* (point-in-r3-x1 u) (point-in-r3-x1 u))
                          (* (point-in-r3-y1 u) (point-in-r3-y1 u))
                          (* (point-in-r3-z1 u) (point-in-r3-z1 u)))
                       1)
                (realp angle)
                (m-= (m-* (rotation-about-witness angle u) p) p))
           (m-= (m-* (rotation-about-witness (- angle) u) p) p))
  :hints (("Goal"
           :use ((:instance r-theta*p=p=>r--theta*p=p-1
                            (m1 (m-* (rotation-about-witness angle u) p))
                            (m2 p)
                            (m3 (rotation-about-witness (- angle) u)))
                 (:instance r-t1*r-t2=r-t1+t2
                            (angle1 (- angle))
                            (angle2 angle)
                            (u u))
                 (:instance r-theta-0=id (u u))
                 (:instance m-*point-id=point (p1 p))
                 (:instance r-theta*p=p=>r--theta*p=p-2
                            (m1 (ROTATION-ABOUT-WITNESS (- ANGLE) U))
                            (m2 (ROTATION-ABOUT-WITNESS ANGLE U))
                            (m3 p)
                            (m4 (ROTATION-ABOUT-WITNESS (- ANGLE) U))
                            (m5 p))
                 )
           :in-theory (e/d () (ASSOCIATIVITY-OF-M-* m-* aref2 rotation-about-witness point-in-r3-x1 point-in-r3-y1 point-in-r3-z1 id-rotation point-in-r3 (:EXECUTABLE-COUNTERPART ID-ROTATION)))
           )))

(defthmd m-=p1p2-implies
  (implies (and (point-in-r3 p1)
                (point-in-r3 p2)
                (m-= p1 p2))
           (and (equal (aref2 :fake-name p1 0 0)
                       (aref2 :fake-name p2 0 0))
                (equal (aref2 :fake-name p1 1 0)
                       (aref2 :fake-name p2 1 0))
                (equal (aref2 :fake-name p1 2 0)
                       (aref2 :fake-name p2 2 0))))
  :hints (("Goal"
           :in-theory (enable m-=)
           )))

(defthmd r-theta*p=p-lemma1-1
  (implies (and (r3-matrixp m)
                (point-in-r3 p))
           (point-in-r3 (m-* m p))))

(defthmd r-theta*p=p-lemma1-2
  (implies (and (point-in-r3 u)
                (realp angle))
           (and (ALIST2P :FAKE-NAME (ROTATION-ABOUT-WITNESS ANGLE U))
                (ALIST2P :FAKE-NAME (ROTATION-ABOUT-WITNESS (- ANGLE) U))))
  :hints (("Goal"
           :in-theory (enable alist2p)
           )))

(defthmd r-theta*p=p-lemma1-3
  (implies (and (point-in-r3 u)
                (point-in-r3 p)
                (realp angle))
           (EQUAL (CADR (DIMENSIONS :FAKE-NAME (ROTATION-ABOUT-WITNESS ANGLE U)))
                  (CAR (DIMENSIONS :FAKE-NAME P))))
  :hints (("Goal"
           :in-theory (e/d (header dimensions) ())
           )))

(defthmd r-theta*p=p-lemma1-4
  (implies (and (point-in-r3 u)
                (point-in-r3 p)
                (realp angle))
           (equal (aref2 :fake-name (m-* (rotation-about-witness angle u) p) 0 0)
                  (+ (* (+ (acl2-cosine angle)
                           (* (point-in-r3-x1 u) (point-in-r3-x1 u) (- 1 (acl2-cosine angle))))
                        (point-in-r3-x1 p))
                     (* (- (* (point-in-r3-x1 u) (point-in-r3-y1 u) (- 1 (acl2-cosine angle)))
                           (* (point-in-r3-z1 u) (acl2-sine angle)))
                        (point-in-r3-y1 p))
                     (* (+ (* (point-in-r3-x1 u) (point-in-r3-z1 u) (- 1 (acl2-cosine angle)))
                           (* (point-in-r3-y1 u) (acl2-sine angle)))
                        (point-in-r3-z1 p)))))
  :hints (("Goal"
           :use ((:instance aref2-m-*
                            (m1 (rotation-about-witness angle u))
                            (m2 p)
                            (name :fake-name)
                            (i 0)
                            (j 0))
                 (:instance rotation-about-witness-values (angle angle) (point u))
                 (:instance r-theta*p=p-lemma1-2 (angle angle) (u u))
                 )
           :in-theory (e/d (header dimensions) ())
           )))

(defthmd r-theta*p=p-lemma1-5
  (implies (and (point-in-r3 u)
                (point-in-r3 p)
                (realp angle))
           (equal (aref2 :fake-name (m-* (rotation-about-witness angle u) p) 2 0)
                  (+ (* (- (* (point-in-r3-z1 u) (point-in-r3-x1 u) (- 1 (acl2-cosine angle)))
                           (* (point-in-r3-y1 u) (acl2-sine angle)))
                        (point-in-r3-x1 p))
                     (* (+ (* (point-in-r3-z1 u) (point-in-r3-y1 u) (- 1 (acl2-cosine angle)))
                           (* (point-in-r3-x1 u) (acl2-sine angle)))
                        (point-in-r3-y1 p))
                     (* (+ (acl2-cosine angle)
                           (* (point-in-r3-z1 u) (point-in-r3-z1 u) (- 1 (acl2-cosine angle))))
                        (point-in-r3-z1 p)))))
  :hints (("Goal"
           :use ((:instance aref2-m-*
                            (m1 (rotation-about-witness angle u))
                            (m2 p)
                            (name :fake-name)
                            (i 2)
                            (j 0))
                 (:instance rotation-about-witness-values (angle angle) (point u))
                 (:instance r-theta*p=p-lemma1-2 (angle angle) (u u))
                 )
           :in-theory (e/d (header dimensions) ())
           )))

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd r-theta*p=p-lemma1
    (implies (and (point-in-r3 p)
                  (point-in-r3 u)
                  (equal (point-in-r3-y1 u) 0)
                  (realp angle)
                  (m-= (m-* (rotation-about-witness angle u) p)
                       (m-* (rotation-about-witness (- angle) u) p)))
             (and (equal (* (point-in-r3-z1 u) (acl2-sine angle) (point-in-r3-y1 p)) 0)
                  (equal (* (point-in-r3-x1 u) (acl2-sine angle) (point-in-r3-y1 p)) 0)))
    :hints (("Goal"
             :use ((:instance m-=p1p2-implies
                              (p1 (m-* (rotation-about-witness angle u) p))
                              (p2 (m-* (rotation-about-witness (- angle) u) p)))
                   (:instance r-theta*p=p-lemma1-4 (u u) (p p) (angle angle))
                   (:instance r-theta*p=p-lemma1-4 (u u) (p p) (angle (- angle)))
                   (:instance r-theta*p=p-lemma1-5 (u u) (p p) (angle angle))
                   (:instance r-theta*p=p-lemma1-5 (u u) (p p) (angle (- angle)))
                   (:instance r-theta*p=p-lemma1-1 (m (rotation-about-witness angle u)) (p p))
                   (:instance r-theta*p=p-lemma1-1 (m (rotation-about-witness (- angle) u)) (p p))
                   (:instance r3-rotationp-r-theta-10 (angle angle) (p u))
                   (:instance r3-rotationp-r-theta-10 (angle (- angle)) (p u))
                   (:instance r-theta*p=p-lemma1-2 (angle angle) (u u))
                   (:instance r-theta*p=p-lemma1-3 (u u) (p p) (angle angle))
                   )
             :in-theory (e/d () (m-= alist2p array2p m-* rotation-about-witness aref2-m-* aref2))
             )))
  )

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd r-theta*p=p-lemma2-1
    (implies (and (point-in-r3 u)
                  (point-in-r3 p)
                  (realp angle))
             (equal (aref2 :fake-name (m-* (rotation-about-witness angle u) p) 1 0)
                    (+ (* (+ (* (point-in-r3-y1 u) (point-in-r3-x1 u) (- 1 (acl2-cosine angle)))
                             (* (point-in-r3-z1 u) (acl2-sine angle)))
                          (point-in-r3-x1 p))
                       (* (+ (acl2-cosine angle)
                             (* (point-in-r3-y1 u) (point-in-r3-y1 u) (- 1 (acl2-cosine angle))))
                          (point-in-r3-y1 p))
                       (* (- (* (point-in-r3-y1 u) (point-in-r3-z1 u) (- 1 (acl2-cosine angle)))
                             (* (point-in-r3-x1 u) (acl2-sine angle)))
                          (point-in-r3-z1 p)))))
    :hints (("Goal"
             :use ((:instance aref2-m-*
                              (m1 (rotation-about-witness angle u))
                              (m2 p)
                              (name :fake-name)
                              (i 1)
                              (j 0))
                   (:instance rotation-about-witness-values (angle angle) (point u))
                   (:instance r-theta*p=p-lemma1-2 (angle angle) (u u))
                   )
             :in-theory (e/d (header dimensions) ())
             )))

  (defthmd r-theta*p=p-lemma2
    (implies (and (point-in-r3 p)
                  (point-in-r3 u)
                  (equal (point-in-r3-y1 p) 0)
                  (equal (point-in-r3-y1 u) 0)
                  (realp angle)
                  (m-= (m-* (rotation-about-witness angle u) p) p))
             (equal (- (* (point-in-r3-z1 u) (acl2-sine angle) (point-in-r3-x1 p))
                       (* (point-in-r3-x1 u) (acl2-sine angle) (point-in-r3-z1 p)))
                    0))
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
  )

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
