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

;; (encapsulate
;;   ()

;;   (local (include-book "arithmetic/top" :dir :system))

;;   (defthmd r3-rotationp-r-theta-11-1-1-lemma1
;;     (implies (and (realp x)
;;                   (realp z)
;;                   (realp s)
;;                   (realp c)
;;                   (equal (+ (* s s) (* c c)) 1)
;;                   (equal (+ (* x x) (* z z)) 1))
;;              (equal (- (* c
;;                           (+ c (* z z (- 1 c))))
;;                        (* (* x s)
;;                           (- (* x s))))
;;                     (+ (* x x) (* c z z))))
;;     :hints (("Goal"
;;             :use ((:instance r3-rotationp-r-theta-11-1-lemma2
;;                              (a (* c c)) (c (* z z)))
;;                   (:instance r3-rotationp-r-theta-11-1-lemma3 (c (* c c)) (a (* x x)) (b (* s s)))
;;                   (:instance r3-rotationp-r-theta-11-1-lemma1 (s x) (c z)))
;;             ))))

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

;; (encapsulate
;;   ()

;;   (local (include-book "arithmetic/top" :dir :system))

;;   (defthmd r3-rotationp-r-theta-11-1-8
;;     (implies (and (realp angle)
;;                   (point-in-r3 p)
;;                   (equal (r3-m-determinant (rotation-about-witness angle p)) 1)
;;                   (equal (point-in-r3-y1 p) 0)
;;                   (equal (+ (* (point-in-r3-x1 p) (point-in-r3-x1 p))
;;                             (* (point-in-r3-z1 p) (point-in-r3-z1 p)))
;;                          1))
;;              (EQUAL (AREF2 :FAKE-NAME
;;                            (R3-M-INVERSE (ROTATION-ABOUT-WITNESS ANGLE P))
;;                            2 0)
;;                     (AREF2 :FAKE-NAME
;;                            (ROTATION-ABOUT-WITNESS ANGLE P)
;;                            0 2)))
;;     :hints (("Goal"
;;              :use ((:instance r3-rotationp-r-theta-11-1-8-lemma1
;;                               (x (point-in-r3-x1 p))
;;                               (z (point-in-r3-z1 p))
;;                               (s (acl2-sine angle))
;;                               (c (acl2-cosine angle)))
;;                    (:instance r3-rotationp-r-theta-11-1-8-lemma3
;;                              (x (point-in-r3-x1 p))
;;                              (z (point-in-r3-z1 p))
;;                              (s (acl2-sine angle))
;;                              (c (acl2-cosine angle)))
;;                    (:instance r3-matrixp-r3-m-inverse (m (rotation-about-witness angle p)))
;;                    (:instance sin**2+cos**2 (x angle))
;;                    (:instance r3-matrixp-m-trans (m (rotation-about-witness angle p)))
;;                    (:instance r3-m-inverse-= (m (rotation-about-witness angle p)))
;;                    (:instance m-trans-values (m (rotation-about-witness angle p)))
;;                    (:instance r3-rotationp-r-theta-11-1-lemma4 (p p))
;;                    (:instance r3-rotationp-r-theta-8 (angle angle))
;;                    (:instance rotation-about-witness-values (angle angle) (point p))
;;                    (:instance r3-rotationp-r-theta-10 (angle angle) (p p))
;;                    (:instance r3-rotationp-r-theta-11-1-8-lemma2 (angle angle) (p p))
;;                    )
;;              :in-theory nil
;;              )))
;;   )

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

;; (encapsulate
;;   ()

;;   (local (include-book "arithmetic/top" :dir :system))

;;   (defthmd r3-rotationp-r-theta-11-1-8
;;     (implies (and (realp angle)
;;                   (point-in-r3 p)
;;                   (equal (r3-m-determinant (rotation-about-witness angle p)) 1)
;;                   (equal (point-in-r3-y1 p) 0)
;;                   (equal (+ (* (point-in-r3-x1 p) (point-in-r3-x1 p))
;;                             (* (point-in-r3-z1 p) (point-in-r3-z1 p)))
;;                          1))
;;              (EQUAL (AREF2 :FAKE-NAME
;;                            (R3-M-INVERSE (ROTATION-ABOUT-WITNESS ANGLE P))
;;                            2 0)
;;                     (AREF2 :FAKE-NAME
;;                            (ROTATION-ABOUT-WITNESS ANGLE P)
;;                            0 2)))
;;     :hints (("Goal"
;;              :use ((:instance r3-rotationp-r-theta-11-1-8-lemma1
;;                               (x (point-in-r3-x1 p))
;;                               (z (point-in-r3-z1 p))
;;                               (s (acl2-sine angle))
;;                               (c (acl2-cosine angle)))
;;                    (:instance r3-rotationp-r-theta-11-1-8-lemma3
;;                              (x (point-in-r3-x1 p))
;;                              (z (point-in-r3-z1 p))
;;                              (s (acl2-sine angle))
;;                              (c (acl2-cosine angle)))
;;                    (:instance r3-matrixp-r3-m-inverse (m (rotation-about-witness angle p)))
;;                    (:instance sin**2+cos**2 (x angle))
;;                    (:instance r3-matrixp-m-trans (m (rotation-about-witness angle p)))
;;                    (:instance r3-m-inverse-= (m (rotation-about-witness angle p)))
;;                    (:instance m-trans-values (m (rotation-about-witness angle p)))
;;                    (:instance r3-rotationp-r-theta-11-1-lemma4 (p p))
;;                    (:instance r3-rotationp-r-theta-8 (angle angle))
;;                    (:instance rotation-about-witness-values (angle angle) (point p))
;;                    (:instance r3-rotationp-r-theta-10 (angle angle) (p p))
;;                    (:instance r3-rotationp-r-theta-11-1-8-lemma2 (angle angle) (p p))
;;                    )
;;              :in-theory nil
;;              )))
;;   )

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


-----------------










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
