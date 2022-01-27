; Banach-Tarski theorem
;
; Proof of the Banach-Tarski theorem.
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

(include-book "banach-tarski-b-0")

(defthmd r3-matrixp-r3d
  (implies (and (realp angle)
                (point-in-r3 u))
           (r3-matrixp (rotation-3d angle u)))
  :hints (("Goal"
           :in-theory (enable aref2 header dimensions array2p)
           )))

(defun vect-tr (x y z p)
  `((:header :dimensions (3 1)
	     :maximum-length 15)
    ((0 . 0) . ,(+ (aref2 :fake-name p 0 0) x) )
    ((1 . 0) . ,(+ (aref2 :fake-name p 1 0) y) )
    ((2 . 0) . ,(+ (aref2 :fake-name p 2 0) z) )
    ))

(defthmd vect-tr-values
  (and (equal (aref2 :fake-name (vect-tr x y z p) 0 0)
              (+ (aref2 :fake-name p 0 0) x))
       (equal (aref2 :fake-name (vect-tr x y z p) 1 0)
              (+ (aref2 :fake-name p 1 0) y))
       (equal (aref2 :fake-name (vect-tr x y z p) 2 0)
              (+ (aref2 :fake-name p 2 0) z)))
  :hints (("Goal"
           :in-theory (enable aref2)
           )))

(defthmd r3p-vectr-tr-p
  (implies (and (point-in-r3 p)
                (realp x)
                (realp y)
                (realp z))
           (point-in-r3 (vect-tr x y z p)))
  :hints (("goal"
           :in-theory (enable array2p header dimensions aref2)
           )))

(defun return-point-in-r3 (x y z)
  `((:header :dimensions (3 1)
	     :maximum-length 15)
    ((0 . 0) . ,x )
    ((1 . 0) . ,y )
    ((2 . 0) . ,z )
    ))

(defthmd return-point-in-r3=>r3p
  (implies (and (realp x)
                (realp y)
                (realp z))
           (point-in-r3 (return-point-in-r3 x y z)))
  :hints (("goal"
           :in-theory (enable array2p header dimensions aref2)
           )))

(defun rotation-about-arbitrary-line (angle m n p)
  (vect-tr (point-in-r3-x1 m) (point-in-r3-y1 m) (point-in-r3-z1 m)
           (m-* (rotation-3d angle
                             (return-point-in-r3 (- (point-in-r3-x1 n) (point-in-r3-x1 m))
                                                 (- (point-in-r3-y1 n) (point-in-r3-y1 m))
                                                 (- (point-in-r3-z1 n) (point-in-r3-z1 m))))
                (vect-tr (- (point-in-r3-x1 m)) (- (point-in-r3-y1 m)) (- (point-in-r3-z1 m)) p))))

(defthmd rotation-about-arbitrary-line=>
  (implies (and (point-in-r3 m)
                (point-in-r3 n)
                (point-in-r3 p)
                (not (m-= m n))
                (realp angle)
                (equal (+ (* (- (point-in-r3-x1 n) (point-in-r3-x1 m))
                             (- (point-in-r3-x1 n) (point-in-r3-x1 m)))
                          (* (- (point-in-r3-y1 n) (point-in-r3-y1 m))
                             (- (point-in-r3-y1 n) (point-in-r3-y1 m)))
                          (* (- (point-in-r3-z1 n) (point-in-r3-z1 m))
                             (- (point-in-r3-z1 n) (point-in-r3-z1 m))))
                       1))
           (equal (rotation-about-arbitrary-line angle m n p)
                  (vect-tr (point-in-r3-x1 m) (point-in-r3-y1 m) (point-in-r3-z1 m)
                           (m-* (rotation-3d angle
                                             (return-point-in-r3 (- (point-in-r3-x1 n) (point-in-r3-x1 m))
                                                                 (- (point-in-r3-y1 n) (point-in-r3-y1 m))
                                                                 (- (point-in-r3-z1 n) (point-in-r3-z1 m))))
                                (vect-tr (- (point-in-r3-x1 m)) (- (point-in-r3-y1 m)) (- (point-in-r3-z1 m)) p)))))
  :hints (("goal"
           :in-theory (disable rotation-3d vect-tr point-in-r3-x1 point-in-r3-y1 point-in-r3-z1 m-* return-point-in-r3)
           )))

(defthmd vectr-tr-lemma1
  (implies (and (m-= p1 p2)
                (point-in-r3 p1)
                (point-in-r3 p2))
           (equal (vect-tr x y z p1)
                  (vect-tr x y z p2)))
  :hints (("goal"
           :in-theory (enable m-=)
           )))

(defthmd rotation-about-arbitrary-line=>1
  (implies (and (m-= p1 p2)
                (point-in-r3 p1)
                (point-in-r3 p2))
           (equal (rotation-about-arbitrary-line angle m n p1)
                  (rotation-about-arbitrary-line angle m n p2)))
  :hints (("goal"
           :use ((:instance vectr-tr-lemma1 (p1 p1) (p2 p2)
                            (x (- (point-in-r3-x1 m)))
                            (y (- (point-in-r3-y1 m)))
                            (z (- (point-in-r3-z1 m)))))
           :in-theory (disable point-in-r3-x1 point-in-r3-y1 point-in-r3-z1 return-point-in-r3
                               rotation-3d vect-tr m-*)
           )))

(defthmd rotation-about-arbitrary-line=>r3p
  (implies (and (point-in-r3 m)
                (point-in-r3 n)
                (point-in-r3 p)
                (realp angle))
           (point-in-r3 (rotation-about-arbitrary-line angle m n p)))
  :hints (("Goal"
           :use ((:instance r3p-vectr-tr-p
                            (p (m-* (rotation-3d angle
                                             (return-point-in-r3 (- (point-in-r3-x1 n) (point-in-r3-x1 m))
                                                                 (- (point-in-r3-y1 n) (point-in-r3-y1 m))
                                                                 (- (point-in-r3-z1 n) (point-in-r3-z1 m))))
                                    (vect-tr (- (point-in-r3-x1 m)) (- (point-in-r3-y1 m)) (- (point-in-r3-z1 m))
                                             p)))
                            (x (point-in-r3-x1 m))
                            (y (point-in-r3-y1 m))
                            (z (point-in-r3-z1 m)))
                 (:instance set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-1-1
                            (rot (rotation-3d angle
                                              (return-point-in-r3 (- (point-in-r3-x1 n) (point-in-r3-x1 m))
                                                                  (- (point-in-r3-y1 n) (point-in-r3-y1 m))
                                                                  (- (point-in-r3-z1 n) (point-in-r3-z1 m)))))
                            (p1 (vect-tr (- (point-in-r3-x1 m)) (- (point-in-r3-y1 m)) (- (point-in-r3-z1 m))
                                         p)))
                 (:instance r3-matrixp-r3d
                            (angle angle)
                            (u (return-point-in-r3 (- (point-in-r3-x1 n) (point-in-r3-x1 m))
                                                                 (- (point-in-r3-y1 n) (point-in-r3-y1 m))
                                                                 (- (point-in-r3-z1 n) (point-in-r3-z1 m)))))
                 (:instance r3p-vectr-tr-p
                            (p p)
                            (x (- (point-in-r3-x1 m)))
                            (y (- (point-in-r3-y1 m)))
                            (z (- (point-in-r3-z1 m))))
                 (:instance r3-rotationp-r-theta-11-1-lemma4
                            (p p))
                 (:instance r3-rotationp-r-theta-11-1-lemma4
                            (p m))
                 (:instance r3-rotationp-r-theta-11-1-lemma4
                            (p n))
                 (:instance return-point-in-r3=>r3p
                            (x (+ (POINT-IN-R3-X1 N)
                                  (- (POINT-IN-R3-X1 M))))
                            (y (+ (POINT-IN-R3-y1 N)
                                  (- (POINT-IN-R3-y1 M))))
                            (z (+ (POINT-IN-R3-z1 N)
                                  (- (POINT-IN-R3-z1 M)))))
                 (:instance rotation-about-arbitrary-line
                            (p p)
                            (m m)
                            (n n)
                            (angle angle))
                 )
           :in-theory nil
           )))

(defun m-p ()
  `((:header :dimensions (3 1)
	     :maximum-length 15)
    ((0 . 0) . 1/10)
    ((1 . 0) . 1/4)
    ((2 . 0) . 0)
    ))


(defun n-p ()
  `((:header :dimensions (3 1)
	     :maximum-length 15)
    ((0 . 0) . 11/10)
    ((1 . 0) . 1/4)
    ((2 . 0) . 0)
    ))

(defthmd return-point-in-r3-n-m=
  (equal (return-point-in-r3 (- (point-in-r3-x1 (n-p)) (point-in-r3-x1 (m-p)))
                             (- (point-in-r3-y1 (n-p)) (point-in-r3-y1 (m-p)))
                             (- (point-in-r3-z1 (n-p)) (point-in-r3-z1 (m-p))))
         `((:header :dimensions (3 1)
                    :maximum-length 15)
           ((0 . 0) . 1)
           ((1 . 0) . 0)
           ((2 . 0) . 0)
           ))
  :hints (("Goal"
           :in-theory (enable aref2 )
           )))

(defthmd rotation-3d-angle-n-m=
  (implies (and (realp angle)
                (equal (return-point-in-r3 (- (point-in-r3-x1 (n-p)) (point-in-r3-x1 (m-p)))
                                           (- (point-in-r3-y1 (n-p)) (point-in-r3-y1 (m-p)))
                                           (- (point-in-r3-z1 (n-p)) (point-in-r3-z1 (m-p))))
                       ret-point))
           (equal (rotation-3d angle ret-point)
                  `((:header :dimensions (3 3)
                             :maximum-length 10)
                    ((0 . 0) . 1)
                    ((0 . 1) . 0)
                    ((0 . 2) . 0)
                    ((1 . 0) . 0)
                    ((1 . 1) . ,(acl2-cosine angle) )
                    ((1 . 2) . ,(- (acl2-sine angle)) )
                    ((2 . 0) . 0)
                    ((2 . 1) . ,(acl2-sine angle) )
                    ((2 . 2) . ,(acl2-cosine angle) )
                    )
                  )
           )
  )

(defthmd rotation-3d-angle-n-m=1
  (implies (and (realp angle)
                (equal (return-point-in-r3 (- (point-in-r3-x1 (n-p)) (point-in-r3-x1 (m-p)))
                                           (- (point-in-r3-y1 (n-p)) (point-in-r3-y1 (m-p)))
                                           (- (point-in-r3-z1 (n-p)) (point-in-r3-z1 (m-p))))
                       ret-point))
           (and (equal (aref2 :fake-name (rotation-3d angle ret-point) 0 0) 1)
                (equal (aref2 :fake-name (rotation-3d angle ret-point) 0 1) 0)
                (equal (aref2 :fake-name (rotation-3d angle ret-point) 0 2) 0)
                (equal (aref2 :fake-name (rotation-3d angle ret-point) 1 0) 0)
                (equal (aref2 :fake-name (rotation-3d angle ret-point) 1 1) (acl2-cosine angle))
                (equal (aref2 :fake-name (rotation-3d angle ret-point) 1 2) (- (acl2-sine angle)))
                (equal (aref2 :fake-name (rotation-3d angle ret-point) 2 0) 0)
                (equal (aref2 :fake-name (rotation-3d angle ret-point) 2 1) (acl2-sine angle))
                (equal (aref2 :fake-name (rotation-3d angle ret-point) 2 2) (acl2-cosine angle))))
  :hints (("Goal"
           :use ((:instance rotation-3d-angle-n-m= (angle angle) (ret-point ret-point))
                 )
           :in-theory (e/d (aref2) (rotation-3d))
           )))

(defthmd m-*rot-3d-vect-tr-values-1
  (and (EQUAL (AREF2 :FAKE-NAME
                     (LIST '(:HEADER :DIMENSIONS (3 1)
                                     :MAXIMUM-LENGTH 4
                                     :DEFAULT 0
                                     :NAME MATRIX-PRODUCT)
                           (CONS '(2 . 0)
                                 (+ (* -1/4 (ACL2-SINE ANGLE))
                                    (* 0 (AREF2 :FAKE-NAME P 0 0))
                                    (* (ACL2-SINE ANGLE)
                                       (AREF2 :FAKE-NAME P 1 0))
                                    (* (ACL2-COSINE ANGLE)
                                       (AREF2 :FAKE-NAME P 2 0))))
                           (CONS '(1 . 0)
                                 (+ (* -1/4 (ACL2-COSINE ANGLE))
                                    (* 0 (AREF2 :FAKE-NAME P 0 0))
                                    (* (ACL2-COSINE ANGLE)
                                       (AREF2 :FAKE-NAME P 1 0))
                                    (* (AREF2 :FAKE-NAME P 2 0)
                                       (- (ACL2-SINE ANGLE)))))
                           (CONS '(0 . 0)
                                 (+ -1/10 (AREF2 :FAKE-NAME P 0 0)
                                    (* 0 (AREF2 :FAKE-NAME P 1 0))
                                    (* 0 (AREF2 :FAKE-NAME P 2 0)))))
                     0 0)
              (+ -1/10 (AREF2 :FAKE-NAME P 0 0)))
       (EQUAL (AREF2 :FAKE-NAME
                     (LIST '(:HEADER :DIMENSIONS (3 1)
                                     :MAXIMUM-LENGTH 4
                                     :DEFAULT 0
                                     :NAME MATRIX-PRODUCT)
                           (CONS '(2 . 0)
                                 (+ (* -1/4 (ACL2-SINE ANGLE))
                                    (* 0 (AREF2 :FAKE-NAME P 0 0))
                                    (* (ACL2-SINE ANGLE)
                                       (AREF2 :FAKE-NAME P 1 0))
                                    (* (ACL2-COSINE ANGLE)
                                       (AREF2 :FAKE-NAME P 2 0))))
                           (CONS '(1 . 0)
                                 (+ (* -1/4 (ACL2-COSINE ANGLE))
                                    (* 0 (AREF2 :FAKE-NAME P 0 0))
                                    (* (ACL2-COSINE ANGLE)
                                       (AREF2 :FAKE-NAME P 1 0))
                                    (* (AREF2 :FAKE-NAME P 2 0)
                                       (- (ACL2-SINE ANGLE)))))
                           (CONS '(0 . 0)
                                 (+ -1/10 (AREF2 :FAKE-NAME P 0 0)
                                    (* 0 (AREF2 :FAKE-NAME P 1 0))
                                    (* 0 (AREF2 :FAKE-NAME P 2 0)))))
                     2 0)
              (+ (* -1/4 (ACL2-SINE ANGLE))
                 (* (ACL2-SINE ANGLE)
                    (AREF2 :FAKE-NAME P 1 0))
                 (* (ACL2-COSINE ANGLE)
                    (AREF2 :FAKE-NAME P 2 0))))
       (EQUAL (AREF2 :FAKE-NAME
                     (LIST '(:HEADER :DIMENSIONS (3 1)
                                     :MAXIMUM-LENGTH 4
                                     :DEFAULT 0
                                     :NAME MATRIX-PRODUCT)
                           (CONS '(2 . 0)
                                 (+ (* -1/4 (ACL2-SINE ANGLE))
                                    (* 0 (AREF2 :FAKE-NAME P 0 0))
                                    (* (ACL2-SINE ANGLE)
                                       (AREF2 :FAKE-NAME P 1 0))
                                    (* (ACL2-COSINE ANGLE)
                                       (AREF2 :FAKE-NAME P 2 0))))
                           (CONS '(1 . 0)
                                 (+ (* -1/4 (ACL2-COSINE ANGLE))
                                    (* 0 (AREF2 :FAKE-NAME P 0 0))
                                    (* (ACL2-COSINE ANGLE)
                                       (AREF2 :FAKE-NAME P 1 0))
                                    (* (AREF2 :FAKE-NAME P 2 0)
                                       (- (ACL2-SINE ANGLE)))))
                           (CONS '(0 . 0)
                                 (+ -1/10 (AREF2 :FAKE-NAME P 0 0)
                                    (* 0 (AREF2 :FAKE-NAME P 1 0))
                                    (* 0 (AREF2 :FAKE-NAME P 2 0)))))
                     1 0)
              (+ (* -1/4 (ACL2-COSINE ANGLE))
                 (* (ACL2-COSINE ANGLE)
                    (AREF2 :FAKE-NAME P 1 0))
                 (* (AREF2 :FAKE-NAME P 2 0)
                    (- (ACL2-SINE ANGLE)))))
       )

  :hints (("Goal"
           :in-theory (enable aref2)
           )))

(defthmd m-*rot-3d-vect-tr-values
  (implies (and (realp angle)
                (point-in-r3 p)
                (equal (return-point-in-r3 (- (point-in-r3-x1 (n-p)) (point-in-r3-x1 (m-p)))
                                           (- (point-in-r3-y1 (n-p)) (point-in-r3-y1 (m-p)))
                                           (- (point-in-r3-z1 (n-p)) (point-in-r3-z1 (m-p))))
                       ret-point)
                (equal (vect-tr (- (point-in-r3-x1 (m-p))) (- (point-in-r3-y1 (m-p))) (- (point-in-r3-z1 (m-p))) p)
                       vectr-tr-to-z))
           (and (equal (aref2 :fake-name (m-* (rotation-3d angle ret-point) vectr-tr-to-z) 0 0)
                       (- (point-in-r3-x1 p) 1/10))
                (equal (aref2 :fake-name (m-* (rotation-3d angle ret-point) vectr-tr-to-z) 1 0)
                       (+ (* (acl2-cosine angle) (- (point-in-r3-y1 p) 1/4))
                          (* (- (acl2-sine angle)) (point-in-r3-z1 p))))
                (equal (aref2 :fake-name (m-* (rotation-3d angle ret-point) vectr-tr-to-z) 2 0)
                       (+ (* (acl2-sine angle) (- (point-in-r3-y1 p) 1/4))
                          (* (acl2-cosine angle) (point-in-r3-z1 p))))))
  :hints (("Goal"
           :use ((:instance rotation-3d-angle-n-m=)
                 (:instance r3p-vectr-tr-p
                            (p p)
                            (x (- (point-in-r3-x1 (m-p))))
                            (y (- (point-in-r3-y1 (m-p))))
                            (z (- (point-in-r3-z1 (m-p)))))
                 (:instance r3-matrixp-r3d
                            (angle angle)
                            (u ret-point))
                 (:instance array2p-alist2p
                            (name :fake-name)
                            (l vectr-tr-to-z))
                 (:instance vect-tr-values
                            (p p)
                            (x (- (point-in-r3-x1 (m-p))))
                            (y (- (point-in-r3-y1 (m-p))))
                            (z (- (point-in-r3-z1 (m-p)))))
                 (:instance rotation-3d-angle-n-m=1)
                 (:instance m-*rot-3d-vect-tr-values-1)
                 )
           :in-theory (e/d (m-*) (rotation-3d))
           )))

(defthmd vectr-tr-m-*rot-3d-vect-tr=
  (implies (and (realp angle)
                (point-in-r3 p))
           (equal (rotation-about-arbitrary-line angle (m-p) (n-p) p)
                  `((:header :dimensions (3 1)
                             :maximum-length 15)
                    ((0 . 0) . ,(point-in-r3-x1 p) )
                    ((1 . 0) . ,(+ (* (acl2-cosine angle) (- (point-in-r3-y1 p) 1/4))
                                   (* (- (acl2-sine angle)) (point-in-r3-z1 p))
                                   1/4) )
                    ((2 . 0) . ,(+ (* (acl2-sine angle) (- (point-in-r3-y1 p) 1/4))
                                   (* (acl2-cosine angle) (point-in-r3-z1 p))) )
                    )
                  ))
  :hints (("Goal"
           :use ((:instance m-*rot-3d-vect-tr-values
                            (angle angle)
                            (p p)
                            (ret-point (return-point-in-r3 (- (point-in-r3-x1 (n-p)) (point-in-r3-x1 (m-p)))
                                                           (- (point-in-r3-y1 (n-p)) (point-in-r3-y1 (m-p)))
                                                           (- (point-in-r3-z1 (n-p)) (point-in-r3-z1 (m-p)))))
                            (vectr-tr-to-z (vect-tr (- (point-in-r3-x1 (m-p)))
                                                    (- (point-in-r3-y1 (m-p)))
                                                    (- (point-in-r3-z1 (m-p))) p)))
                 (:instance vect-tr
                            (x 1/10)
                            (y 1/4)
                            (z 0)
                            (p (m-* (rotation-3d angle (return-point-in-r3 (- (point-in-r3-x1 (n-p)) (point-in-r3-x1 (m-p)))
                                                                           (- (point-in-r3-y1 (n-p)) (point-in-r3-y1 (m-p)))
                                                                           (- (point-in-r3-z1 (n-p)) (point-in-r3-z1 (m-p)))))
                                    (vect-tr (- (point-in-r3-x1 (m-p)))
                                             (- (point-in-r3-y1 (m-p)))
                                             (- (point-in-r3-z1 (m-p))) p))))
                 )
           :in-theory (disable m-* rotation-3d vect-tr)
           )))

(defthmd vectr-tr-m-*rot-3d-vect-tr-values
  (implies (and (realp angle)
                (point-in-r3 p))
           (and (equal (aref2 :fake-name (rotation-about-arbitrary-line angle (m-p) (n-p) p) 0 0)
                       (point-in-r3-x1 p))
                (equal (aref2 :fake-name (rotation-about-arbitrary-line angle (m-p) (n-p) p) 1 0)
                       (+ (* (acl2-cosine angle) (- (point-in-r3-y1 p) 1/4))
                          (* (- (acl2-sine angle)) (point-in-r3-z1 p))
                          1/4))
                (equal (aref2 :fake-name (rotation-about-arbitrary-line angle (m-p) (n-p) p) 2 0)
                       (+ (* (acl2-sine angle) (- (point-in-r3-y1 p) 1/4))
                          (* (acl2-cosine angle) (point-in-r3-z1 p))))))
  :hints (("Goal"
           :use ((:instance vectr-tr-m-*rot-3d-vect-tr= (angle angle) (p p))
                 )
           :in-theory (e/d (aref2) (rotation-about-arbitrary-line))
           )))

(defthmd rotation-about-arbitrary-line=p
  (implies (and (equal angle 0)
                (point-in-r3 p))
           (m-= (rotation-about-arbitrary-line angle (m-p) (n-p) p) p))
  :hints (("Goal"
           :use ((:instance vectr-tr-m-*rot-3d-vect-tr-values
                            (angle 0)
                            (p p))
                 (:instance rotation-about-arbitrary-line=>r3p
                            (m (m-p))
                            (n (n-p))
                            (p p)
                            (angle 0)))
           :in-theory (e/d (m-=) (rotation-about-arbitrary-line))
           )))

(defthmd m-=-equiv-lemma-pr3
  (implies (and (point-in-r3 p1)
                (point-in-r3 p2)
                (equal (aref2 :fake-name p1 0 0) (aref2 :fake-name p2 0 0))
                (equal (aref2 :fake-name p1 1 0) (aref2 :fake-name p2 1 0))
                (equal (aref2 :fake-name p1 2 0) (aref2 :fake-name p2 2 0))
                )
           (m-= p1 p2))
  :hints (("goal"
           :in-theory (enable m-=)
           )))

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd rot-angle1-of-angle2*p=>1
    (implies (and (realp x)
                  (realp y)
                  (realp z)
                  (realp angle1)
                  (realp angle2)
                  (equal y-of-ang2 (+ (* (ACL2-COSINE ANGLE2)
                                         (+ -1/4 y))
                                      (* (- (ACL2-SINE ANGLE2))
                                         z)
                                      1/4))
                  (equal z-of-ang2 (+ (* (ACL2-SINE ANGLE2)
                                         (+ -1/4 y))
                                      (* (ACL2-COSINE ANGLE2)
                                         z))))
             (equal (+ (* (ACL2-COSINE ANGLE1)
                          (+ -1/4
                             y-of-ang2))
                       (* (- (ACL2-SINE ANGLE1))
                          z-of-ang2)
                       1/4)
                    (+ (* (ACL2-COSINE (+ ANGLE1 ANGLE2))
                          (+ -1/4 y))
                       (* (- (ACL2-SINE (+ ANGLE1 ANGLE2)))
                          z)
                       1/4))))

  (defthmd rot-angle1-of-angle2*p=>2
    (implies (and (realp x)
                  (realp y)
                  (realp z)
                  (realp angle1)
                  (realp angle2)
                  (equal y-of-ang2 (+ (* (ACL2-COSINE ANGLE2)
                                         (+ -1/4 y))
                                      (* (- (ACL2-SINE ANGLE2))
                                         z)
                                      1/4))
                  (equal z-of-ang2 (+ (* (ACL2-SINE ANGLE2)
                                         (+ -1/4 y))
                                      (* (ACL2-COSINE ANGLE2)
                                         z))))
             (equal (+ (* (ACL2-SINE ANGLE1)
                          (+ -1/4
                             y-of-ang2))
                       (* (ACL2-coSINE ANGLE1)
                          z-of-ang2))
                    (+ (* (ACL2-SINE (+ ANGLE1 ANGLE2))
                          (+ -1/4 y))
                       (* (ACL2-coSINE (+ ANGLE1 ANGLE2))
                          z)))))
  )

(defthmd rot-angle1-of-angle2*p=>
  (implies (and (point-in-r3 p)
                (point-in-r3 (m-p))
                (point-in-r3 (n-p))
                (realp angle1)
                (realp angle2))
           (m-= (rotation-about-arbitrary-line
                 angle1 (m-p) (n-p)
                 (rotation-about-arbitrary-line angle2 (m-p) (n-p) p))
                (rotation-about-arbitrary-line (+ angle1 angle2) (m-p) (n-p) p)))
  :hints (("Goal"
           :use ((:instance vectr-tr-m-*rot-3d-vect-tr-values
                            (angle angle2)
                            (p p))
                 (:instance vectr-tr-m-*rot-3d-vect-tr-values
                            (angle angle1)
                            (p (rotation-about-arbitrary-line angle2 (m-p) (n-p) p)))
                 (:instance rotation-about-arbitrary-line=>r3p
                            (m (m-p))
                            (n (n-p))
                            (p p)
                            (angle angle2))
                 (:instance rotation-about-arbitrary-line=>r3p
                            (p (rotation-about-arbitrary-line angle2 (m-p) (n-p) p))
                            (angle angle1)
                            (m (m-p))
                            (n (n-p)))
                 (:instance vectr-tr-m-*rot-3d-vect-tr-values
                            (angle (+ angle1 angle2))
                            (p p))
                 (:instance rotation-about-arbitrary-line=>r3p
                            (p p)
                            (angle (+ angle1 angle2))
                            (m (m-p))
                            (n (n-p)))
                 (:instance r3-rotationp-r-theta-11-1-lemma4
                            (p p))
                 (:instance array2p-alist2p
                            (name :fake-name)
                            (l (rotation-about-arbitrary-line (+ angle1 angle2) (m-p) (n-p) p)))
                 (:instance array2p-alist2p
                            (name :fake-name)
                            (l (rotation-about-arbitrary-line
                                angle1 (m-p) (n-p)
                                (rotation-about-arbitrary-line angle2 (m-p) (n-p) p))))
                 (:instance point-in-r3
                            (x (rotation-about-arbitrary-line (+ angle1 angle2) (m-p) (n-p) p)))
                 (:instance point-in-r3
                            (x (rotation-about-arbitrary-line angle2 (m-p) (n-p) p)))
                 (:instance point-in-r3
                            (x (rotation-about-arbitrary-line
                                angle1 (m-p) (n-p)
                                (rotation-about-arbitrary-line angle2 (m-p) (n-p) p))))
                 (:instance point-in-r3-x1
                            (p (rotation-about-arbitrary-line angle2 (m-p) (n-p) p)))
                 (:instance point-in-r3-y1
                            (p (rotation-about-arbitrary-line angle2 (m-p) (n-p) p)))
                 (:instance point-in-r3-z1
                            (p (rotation-about-arbitrary-line angle2 (m-p) (n-p) p)))
                 (:instance m-=-equiv-lemma-pr3
                            (p1 (rotation-about-arbitrary-line
                                 angle1 (m-p) (n-p)
                                 (rotation-about-arbitrary-line angle2 (m-p) (n-p) p)))
                            (p2 (rotation-about-arbitrary-line (+ angle1 angle2) (m-p) (n-p) p)))
                 (:instance rot-angle1-of-angle2*p=>2
                            (x (point-in-r3-x1 p))
                            (y (point-in-r3-y1 p))
                            (z (point-in-r3-z1 p))
                            (angle1 angle1)
                            (angle2 angle2)
                            (y-of-ang2 (+ (* (ACL2-COSINE ANGLE2)
                                             (+ -1/4 (POINT-IN-R3-Y1 P)))
                                          (* (- (ACL2-SINE ANGLE2))
                                             (POINT-IN-R3-Z1 P))
                                          1/4))
                            (z-of-ang2 (+ (* (ACL2-SINE ANGLE2)
                                             (+ -1/4 (POINT-IN-R3-Y1 P)))
                                          (* (ACL2-COSINE ANGLE2)
                                             (POINT-IN-R3-Z1 P))))
                            )
                 (:instance rot-angle1-of-angle2*p=>1
                            (x (point-in-r3-x1 p))
                            (y (point-in-r3-y1 p))
                            (z (point-in-r3-z1 p))
                            (angle1 angle1)
                            (angle2 angle2)
                            (y-of-ang2 (+ (* (ACL2-COSINE ANGLE2)
                                             (+ -1/4 (POINT-IN-R3-Y1 P)))
                                          (* (- (ACL2-SINE ANGLE2))
                                             (POINT-IN-R3-Z1 P))
                                          1/4))
                            (z-of-ang2 (+ (* (ACL2-SINE ANGLE2)
                                             (+ -1/4 (POINT-IN-R3-Y1 P)))
                                          (* (ACL2-COSINE ANGLE2)
                                             (POINT-IN-R3-Z1 P))))
                            )
                 )
           :in-theory nil
           )))

(defun zero-p (p)
  (and (point-in-r3 p)
       (= (cal-radius p) 0)))

(defthmd zero-p-lemma1
  (implies (zero-p p1)
           (and (equal (aref2 :fake-name p1 0 0) 0)
                (equal (aref2 :fake-name p1 1 0) 0)
                (equal (aref2 :fake-name p1 2 0) 0))))

(defthmd zero-p-lemma2
  (implies (and (zero-p p1)
                (zero-p p2))
           (m-= p1 p2))
  :hints (("goal"
           :use ((:instance zero-p-lemma1 (p1 p1))
                 (:instance zero-p-lemma1 (p1 p2)))
           :in-theory (e/d (m-=) (cal-radius))
           )))

(defthmd zero-p-lemma3
  (implies (and (zero-p p1)
                (point-in-r3 p2)
                (m-= p1 p2))
           (zero-p p2))
  :hints (("goal"
           :use ((:instance zero-p-lemma1 (p1 p1)))
           :in-theory (e/d (m-=) ())
           )))

(defthmd rotation-about-arbitrary-line=>r3p-m-n
  (implies (and (point-in-r3 p)
                (realp angle))
           (point-in-r3 (rotation-about-arbitrary-line angle (m-p) (n-p) p)))
  :hints (("goal"
           :use ((:instance rotation-about-arbitrary-line=>r3p (m (m-p)) (n (n-p)) (p p) (angle angle))
                 )
           :in-theory (disable rotation-about-arbitrary-line)
           )))

(defthmd rotation-about-arbitrary-line=p-m-n
  (implies (and (point-in-r3 p)
                (equal angle 0))
           (m-= (rotation-about-arbitrary-line angle (m-p) (n-p) p) p))
  :hints (("goal"
           :use ((:instance rotation-about-arbitrary-line=p (p p) (angle angle)))
           :in-theory (disable rotation-about-arbitrary-line)
           )))

(defthmd rot-angle1-of-angle2*p=>m-n
  (implies (and (point-in-r3 p)
                (realp angle1)
                (realp angle2))
           (m-= (rotation-about-arbitrary-line angle1 (m-p) (n-p)
                                               (rotation-about-arbitrary-line angle2 (m-p) (n-p) p))
                (rotation-about-arbitrary-line (+ angle1 angle2) (m-p) (n-p) p)))
  :hints (("goal"
           :use ((:instance rot-angle1-of-angle2*p=> (p p) (angle1 angle1) (angle2 angle2)))
           :in-theory (disable rotation-about-arbitrary-line)
           )))

(defthmd rot-i*angle*p-not-=p-m-n-1
  (not (zero-p (m-p)))
  :hints (("goal"
           :use ((:instance sqrt->-0 (x 29/400)))
           )))

(defthmd rot-i*angle*p-not-=p-m-n-2
  (not (zero-p (n-p)))
  :hints (("goal"
           :use ((:instance sqrt->-0 (x 349/400)))
           )))

(encapsulate
  (
   ((angle-const) => *)
   )

  (local (defun angle-const ()
                1/2))

  (defthmd angle-const-is-real
    (realp (angle-const)))
  )

(skip-proofs
 (defthmd rot-i*angle*p-not-=p-m-n
   (implies (and (zero-p p)
                 (posp i)
                 (equal angle (angle-const)))
            (not (m-= (rotation-about-arbitrary-line (* i angle) (m-p) (n-p) p)
                      p)))
   :hints (("goal"
            :use ((:instance rot-i*angle*p-not-=p-m-n-1)
                  (:instance rot-i*angle*p-not-=p-m-n-2))
            :in-theory (disable rotation-about-arbitrary-line acl2-sqrt acl2-pi)
            )))
 )

(skip-proofs
 (defthmd rot-i*angle*p-in-b^3
   (implies (and (zero-p p)
                 (realp angle))
            (<= (cal-radius (rotation-about-arbitrary-line angle (m-p) (n-p) p)) 1))))

(defun-sk exists-z-p (i point)
  (exists p
          (and (zero-p p)
               (m-= (rotation-about-arbitrary-line (* i (angle-const)) (m-p) (n-p) p) point))))

(defthmd exists-z-p=>
  (implies (exists-z-p i point)
           (and (zero-p (exists-z-p-witness i point))
                (m-= (rotation-about-arbitrary-line (* i (angle-const)) (m-p) (n-p) (exists-z-p-witness i point))
                     point)))
  :hints (("goal"
           :in-theory (disable d-p point-on-s2-not-d rotation-3d rotation-about-arbitrary-line)
           )))

(defun-sk ffunc (point)
  (exists i
          (and (natp i)
               (exists-z-p i point))))

(defun set-f-p (point)
  (and (point-in-r3 point)
       (ffunc point)))

(defun-sk rot-sqrt-2*f-func-1 (point)
  (exists p
          (and (set-f-p p)
               (m-= (rotation-about-arbitrary-line (angle-const) (m-p) (n-p) p) point))))

(defthmd rot-sqrt-2*f-func-1=>
  (implies (rot-sqrt-2*f-func-1 point)
           (and (set-f-p (rot-sqrt-2*f-func-1-witness point))
                (m-= (rotation-about-arbitrary-line (angle-const) (m-p) (n-p) (rot-sqrt-2*f-func-1-witness point))
                     point)))
  :hints (("goal"
           :in-theory (disable d-p point-on-s2-not-d rotation-3d ffunc rotation-about-arbitrary-line)
           )))

(defun rot-sqrt-2*f-func (point)
  (and (point-in-r3 point)
       (rot-sqrt-2*f-func-1 point)))

(defun ffunc-not-z (point)
  (and (set-f-p point)
       (not (zero-p point))))

(defthmd rot-sqrt-2*f-func=>f-1
  (implies (and (realp x)
                (natp i))
           (realp (* i x))))

(defthmd rot-sqrt-2*f-func=>f-2
  (implies (natp i)
           (and (natp (+ i 1))
                (posp (+ i 1)))))

(defthmd rot-sqrt-2*f-func=>f-3
  (equal (* (+ (ffunc-witness (rot-sqrt-2*f-func-1-witness point))
               1)
            (angle-const))
         (+ (angle-const)
            (* (ffunc-witness (rot-sqrt-2*f-func-1-witness point))
               (angle-const)))))

(defthmd rot-sqrt-2*ffunc=>f-not-z
  (implies (rot-sqrt-2*f-func point)
           (and (set-f-p point)
                (m-=
                 (rotation-about-arbitrary-line
                  (* (+ (ffunc-witness (rot-sqrt-2*f-func-1-witness point))
                        1)
                     (angle-const))
                  (m-p)
                  (n-p)
                  (exists-z-p-witness (ffunc-witness (rot-sqrt-2*f-func-1-witness point))
                                      (rot-sqrt-2*f-func-1-witness point)))
                 point)
                (zero-p (exists-z-p-witness (ffunc-witness (rot-sqrt-2*f-func-1-witness point))
                                            (rot-sqrt-2*f-func-1-witness point)))
                (realp (* (+ (ffunc-witness (rot-sqrt-2*f-func-1-witness point))
                             1)
                          (angle-const)))
                (not (zero-p point))))
  :hints (("goal"
           :use ((:instance rot-sqrt-2*f-func (point point))
                 (:instance rot-sqrt-2*f-func-1=> (point point))
                 (:instance set-f-p (point (rot-sqrt-2*f-func-1-witness point)))
                 (:instance ffunc (point (rot-sqrt-2*f-func-1-witness point)))
                 (:instance exists-z-p=> (i (ffunc-witness (rot-sqrt-2*f-func-1-witness point)))
                            (point (rot-sqrt-2*f-func-1-witness point)))
                 (:instance set-f-p (point point))
                 (:instance ffunc-suff (i (+ (ffunc-witness (rot-sqrt-2*f-func-1-witness point)) 1)) (point point))
                 (:instance exists-z-p-suff (p (exists-z-p-witness
                                                (ffunc-witness (rot-sqrt-2*f-func-1-witness point))
                                                (rot-sqrt-2*f-func-1-witness point)))
                            (i (+ (ffunc-witness (rot-sqrt-2*f-func-1-witness point)) 1))
                            (point point))
                 (:instance rotation-about-arbitrary-line=>1
                            (p1 (rot-sqrt-2*f-func-1-witness point))
                            (m (m-p))
                            (n (n-p))
                            (angle (angle-const))
                            (p2 (rotation-about-arbitrary-line
                                 (* (ffunc-witness (rot-sqrt-2*f-func-1-witness point))
                                    (angle-const))
                                 (m-p)
                                 (n-p)
                                 (exists-z-p-witness (ffunc-witness (rot-sqrt-2*f-func-1-witness point))
                                                     (rot-sqrt-2*f-func-1-witness point)))))
                 (:instance rotation-about-arbitrary-line=>r3p-m-n
                            (p (exists-z-p-witness (ffunc-witness (rot-sqrt-2*f-func-1-witness point))
                                                   (rot-sqrt-2*f-func-1-witness point)))
                            (angle (* (ffunc-witness (rot-sqrt-2*f-func-1-witness point))
                                      (angle-const))))
                 (:instance zero-p (p (exists-z-p-witness (ffunc-witness (rot-sqrt-2*f-func-1-witness point))
                                                          (rot-sqrt-2*f-func-1-witness point))))
                 (:instance rot-sqrt-2*f-func=>f-1
                            (x (angle-const))
                            (i (ffunc-witness (rot-sqrt-2*f-func-1-witness point))))
                 (:instance angle-const-is-real)
                 (:instance rot-sqrt-2*f-func=>f-2
                            (i (ffunc-witness (rot-sqrt-2*f-func-1-witness point))))
                 (:instance rot-angle1-of-angle2*p=>m-n
                            (angle1 (angle-const))
                            (angle2 (* (ffunc-witness (rot-sqrt-2*f-func-1-witness point))
                                       (angle-const)))
                            (p (exists-z-p-witness (ffunc-witness (rot-sqrt-2*f-func-1-witness point))
                                                   (rot-sqrt-2*f-func-1-witness point))))
                 (:instance m-=-is-an-equivalence
                            (x point)
                            (y (rotation-about-arbitrary-line (angle-const)
                                                              (m-p)
                                                              (n-p)
                                                              (rot-sqrt-2*f-func-1-witness point)))
                            (z (rotation-about-arbitrary-line
                                (+ (angle-const)
                                   (* (ffunc-witness (rot-sqrt-2*f-func-1-witness point))
                                      (angle-const)))
                                (m-p)
                                (n-p)
                                (exists-z-p-witness (ffunc-witness (rot-sqrt-2*f-func-1-witness point))
                                                    (rot-sqrt-2*f-func-1-witness point)))))
                 (:instance rot-sqrt-2*f-func=>f-3)
                 (:instance rot-i*angle*p-not-=p-m-n
                            (i (+ (ffunc-witness (rot-sqrt-2*f-func-1-witness point))
                                  1))
                            (angle (angle-const))
                            (p (exists-z-p-witness (ffunc-witness (rot-sqrt-2*f-func-1-witness point))
                                                   (rot-sqrt-2*f-func-1-witness point))))
                 (:instance zero-p-lemma2
                            (p2 (exists-z-p-witness (ffunc-witness (rot-sqrt-2*f-func-1-witness point))
                                                    (rot-sqrt-2*f-func-1-witness point)))
                            (p1 (rotation-about-arbitrary-line
                                 (* (+ (ffunc-witness (rot-sqrt-2*f-func-1-witness point))
                                       1)
                                    (angle-const))
                                 (m-p)
                                 (n-p)
                                 (exists-z-p-witness (ffunc-witness (rot-sqrt-2*f-func-1-witness point))
                                                     (rot-sqrt-2*f-func-1-witness point)))))
                 (:instance zero-p-lemma3
                            (p1 point)
                            (p2 (rotation-about-arbitrary-line
                                 (* (+ (ffunc-witness (rot-sqrt-2*f-func-1-witness point))
                                       1)
                                    (angle-const))
                                 (m-p)
                                 (n-p)
                                 (exists-z-p-witness (ffunc-witness (rot-sqrt-2*f-func-1-witness point))
                                                     (rot-sqrt-2*f-func-1-witness point)))))
                 (:instance rotation-about-arbitrary-line=>r3p-m-n
                            (p (exists-z-p-witness (ffunc-witness (rot-sqrt-2*f-func-1-witness point))
                                                   (rot-sqrt-2*f-func-1-witness point)))
                            (angle (* (+ (ffunc-witness (rot-sqrt-2*f-func-1-witness point))
                                         1)
                                      (angle-const))))
                 )
           :in-theory nil
           )))

(defthm f-not-z=>rot-sqrt-2*ffunc-1-1
  (implies (and (natp i)
                (not (posp i)))
           (equal i 0))
  :rule-classes nil)

(defthmd f-not-z=>rot-sqrt-2*ffunc-1-2
  (implies (posp i)
           (natp (- i 1))))


(defthmd f-not-z=>rot-sqrt-2*ffunc-1
  (implies (ffunc-not-z point)
           (and (posp (ffunc-witness point))
                (natp (- (ffunc-witness point) 1))))
  :hints (("goal"
           :cases ((posp (ffunc-witness point)))
           :use ((:instance ffunc-not-z (point point))
                 (:instance f-not-z=>rot-sqrt-2*ffunc-1-1 (i (ffunc-witness point)))
                 (:instance set-f-p (point point))
                 (:instance ffunc (point point))
                 (:instance exists-z-p (i (ffunc-witness point))
                            (point point))
                 (:instance rotation-about-arbitrary-line=p-m-n
                            (angle (* (ffunc-witness point) (angle-const)))
                            (p (exists-z-p-witness (ffunc-witness point)
                                                   point)))
                 (:instance zero-p-lemma3
                            (p1 (exists-z-p-witness (ffunc-witness point)
                                                    point))
                            (p2 point))
                 (:instance zero-p (p (exists-z-p-witness (ffunc-witness point)
                                                          point)))
                 (:instance f-not-z=>rot-sqrt-2*ffunc-1-2
                            (i (ffunc-witness point)))
                 )
           :in-theory nil
           )))

(defthmd f-not-z=>rot-sqrt-2*ffunc-2
  (equal (+ (angle-const)
            (* (+ -1 (ffunc-witness point))
               (angle-const)))
         (* (ffunc-witness point) (angle-const))))


(defthmd f-not-z=>rot-sqrt-2*ffunc
  (implies (ffunc-not-z point)
           (rot-sqrt-2*f-func point))
  :hints (("goal"
           :use ((:instance ffunc-not-z (point point))
                 (:instance set-f-p (point point))
                 (:instance ffunc (point point))
                 (:instance exists-z-p (i (ffunc-witness point)) (point point))
                 (:instance rot-sqrt-2*f-func (point point))
                 (:instance rot-sqrt-2*f-func-1-suff
                            (p (rotation-about-arbitrary-line (* (- (ffunc-witness point) 1) (angle-const))
                                                              (m-p)
                                                              (n-p)
                                                              (exists-z-p-witness (ffunc-witness point)
                                                                                  point)))
                            (point point))
                 (:instance set-f-p (point  (rotation-about-arbitrary-line (* (+ -1 (ffunc-witness point))
                                                                              (angle-const))
                                                                           (m-p)
                                                                           (n-p)
                                                                           (exists-z-p-witness (ffunc-witness point)
                                                                                               point))))
                 (:instance f-not-z=>rot-sqrt-2*ffunc-1 (point point))
                 (:instance rot-sqrt-2*f-func=>f-1
                            (x (angle-const))
                            (i (+ -1 (ffunc-witness point))))
                 (:instance angle-const-is-real)
                 (:instance rotation-about-arbitrary-line=>r3p-m-n
                            (p (exists-z-p-witness (ffunc-witness point)
                                                   point))
                            (angle (* (+ -1 (ffunc-witness point))
                                      (angle-const))))
                 (:instance zero-p (p (exists-z-p-witness (ffunc-witness point)
                                                          point)))
                 (:instance ffunc-suff (point (rotation-about-arbitrary-line (* (+ -1 (ffunc-witness point))
                                                                                (angle-const))
                                                                             (m-p)
                                                                             (n-p)
                                                                             (exists-z-p-witness (ffunc-witness point)
                                                                                                 point)))
                            (i (+ -1 (ffunc-witness point))))
                 (:instance exists-z-p-suff
                            (p (exists-z-p-witness (ffunc-witness point)
                                                   point))
                            (point (rotation-about-arbitrary-line (* (+ -1 (ffunc-witness point))
                                                                     (angle-const))
                                                                  (m-p)
                                                                  (n-p)
                                                                  (exists-z-p-witness (ffunc-witness point)
                                                                                      point)))
                            (i (+ -1 (ffunc-witness point))))
                 (:instance rot-angle1-of-angle2*p=>m-n
                            (angle1 (angle-const))
                            (angle2 (* (+ -1 (ffunc-witness point))
                                       (angle-const)))
                            (p (exists-z-p-witness (ffunc-witness point)
                                                   point)))
                 (:instance f-not-z=>rot-sqrt-2*ffunc-2)
                 )
           :in-theory nil
           )))

(defthmd rot-sqrt-2*ffunc-iff-f-not-z
  (iff (rot-sqrt-2*f-func p)
       (ffunc-not-z p))
  :hints (("goal"
           :use ((:instance rot-sqrt-2*ffunc=>f-not-z (point p))
                 (:instance f-not-z=>rot-sqrt-2*ffunc (point p))
                 (:instance ffunc-not-z (point p))
                 )
           :in-theory nil
           )))

(defthmd cal-radius>=0
  (implies (point-in-r3 p)
           (>= (cal-radius p) 0))
  :hints (("goal"
           :in-theory (disable (:type-prescription cal-radius) (:executable-counterpart tau-system))
           )))

(defun b3 (p)
  (and (point-in-r3 p)
       (<= (cal-radius p) 1)))

(defthmd b3=>b3-0-or-0
  (iff (b3 p)
       (or (zero-p p)
           (b3-0 p)))
  :hints (("goal"
           :use ((:instance cal-radius>=0 (p p)))
           :in-theory (disable cal-radius)
           )))

(defun b3-f (p)
  (and (b3 p)
       (not (set-f-p p))))

(defthmd cal-radius-p1=p2
  (implies (and (point-in-r3 p1)
                (point-in-r3 p2)
                (m-= p1 p2))
           (equal (cal-radius p1)
                  (cal-radius p2)))
  :hints (("goal"
           :in-theory (enable m-=)
           )))

(defthmd f=>b3
  (implies (set-f-p p)
           (b3 p))
  :hints (("goal"
           :use ((:instance set-f-p (point p))
                 (:instance b3 (p p))
                 (:instance ffunc (point p))
                 (:instance exists-z-p=> (i (ffunc-witness p)) (point p))
                 (:instance cal-radius-p1=p2 (p1 (rotation-about-arbitrary-line (* (ffunc-witness p) (angle-const))
                                                                                (m-p)
                                                                                (n-p)
                                                                                (exists-z-p-witness (ffunc-witness p)
                                                                                                    p)))
                            (p2 p))
                 (:instance rotation-about-arbitrary-line=>r3p-m-n
                            (p (exists-z-p-witness (ffunc-witness p)
                                                   p))
                            (angle (* (ffunc-witness p) (angle-const))))
                 (:instance zero-p (p (exists-z-p-witness (ffunc-witness p)
                                                          p)))
                 (:instance rot-sqrt-2*f-func=>f-1
                            (x (angle-const))
                            (i (ffunc-witness p)))
                 (:instance angle-const-is-real)
                 (:instance rot-i*angle*p-in-b^3 (p (exists-z-p-witness (ffunc-witness p)
                                                                        p))
                            (angle (* (ffunc-witness p) (angle-const))))
                 )
           :in-theory nil
           )))

(defthmd b3=>
  (iff (b3 p)
       (or (b3-f p)
           (set-f-p p)))
  :hints (("goal"
           :use ((:instance f=>b3))
           :in-theory (disable set-f-p b3)
           )))

(defthmd z=>f-1
  (natp 0))

(defthmd z=>f
  (implies (zero-p p)
           (set-f-p p))
  :hints (("goal"
           :use ((:instance zero-p (p p))
                 (:instance set-f-p (point p))
                 (:instance ffunc-suff (i 0) (point p))
                 (:instance z=>f-1)
                 (:instance exists-z-p-suff (p p) (i 0) (point p))
                 (:instance rotation-about-arbitrary-line=p-m-n
                            (angle (* 0 (angle-const)))
                            (p p))
                 )
           :in-theory nil
           )))

(defun b3-0-n-b3-f (p)
  (and (b3-0 p)
       (b3-f p)))

(defthm b3-0-n-b3-f-iff-b3-f
  (iff (b3-f p)
       (b3-0-n-b3-f p))
  :hints (("goal"
           :use ((:instance b3-0-n-b3-f (p p))
                 (:instance b3-f (p p))
                 (:instance b3=>b3-0-or-0 (p p))
                 (:instance z=>f (p p))
                 )
           :in-theory nil
           )))

(defun b3-0-n-f (p)
  (and (b3-0 p)
       (set-f-p p)))

(defthmd b3-0=>not-z
  (implies (b3-0 p)
           (not (zero-p p)))
  :hints (("goal"
           :use ((:instance b3-0 (p p))
                 (:instance zero-p (p p))
                 )
           :in-theory nil
           )))

(defthmd f-not-z-iff-b3-0-n-f
  (iff (ffunc-not-z p)
       (b3-0-n-f p))
  :hints (("goal"
           :use ((:instance ffunc-not-z (point p))
                 (:instance b3-0-n-f (p p))
                 (:instance z=>f (p p))
                 (:instance b3=>)
                 (:instance b3=>b3-0-or-0)
                 (:instance b3-0=>not-z (p p))
                 )
           :in-theory nil
           )))

(defun-sk rota-1-rota-f-1 (point)
  (exists p
          (and (rot-sqrt-2*f-func p)
               (m-= (rotation-about-arbitrary-line (- (angle-const)) (m-p) (n-p) p)
                    point))))

(defun rota-1-rota-f (p)
  (and (point-in-r3 p)
       (rota-1-rota-f-1 p)))

(defthmd rota-1-rota-f-iff-set-f-p-1
  (implies (set-f-p p)
           (rota-1-rota-f p))
  :hints (("goal"
           :use ((:instance rota-1-rota-f (p p))
                 (:instance set-f-p (point p))
                 (:instance rota-1-rota-f-1-suff
                            (p (rotation-about-arbitrary-line (angle-const) (m-p) (n-p) p))
                            (point p))
                 (:instance rot-sqrt-2*f-func (point (rotation-about-arbitrary-line (angle-const)
                                                                                    (m-p)
                                                                                    (n-p)
                                                                                    p)))
                 (:instance rotation-about-arbitrary-line=>r3p-m-n
                            (angle (angle-const))
                            (p p))
                 (:instance angle-const-is-real)
                 (:instance rot-sqrt-2*f-func-1-suff
                            (p p)
                            (point (rotation-about-arbitrary-line (angle-const)
                                                                  (m-p)
                                                                  (n-p)
                                                                  p)))
                 (:instance rot-angle1-of-angle2*p=>m-n
                            (p p)
                            (angle1 (- (angle-const)))
                            (angle2 (angle-const)))
                 (:instance rotation-about-arbitrary-line=p-m-n
                            (angle (+ (- (angle-const)) (angle-const)))
                            (p p))
                 )
           :in-theory nil
           )))

(defthmd rota-1-rota-f-iff-set-f-p-2-1
  (implies (and (m-= p1 p2)
                (point-in-r3 p2)
                (set-f-p p1))
           (set-f-p p2))
  :hints (("goal"
           :use ((:instance set-f-p (point p1))
                 (:instance ffunc (point p1))
                 (:instance exists-z-p (point p1)
                            (i (ffunc-witness p1)))
                 (:instance set-f-p (point p2))
                 (:instance ffunc-suff
                            (i (ffunc-witness p1))
                            (point p2))
                 (:instance exists-z-p-suff (i (ffunc-witness p1))
                            (p (exists-z-p-witness (ffunc-witness p1)
                                                   p1))
                            (point p2))
                 )
           :in-theory nil
           )))

(defthmd rota-1-rota-f-iff-set-f-p-2
  (implies (rota-1-rota-f p)
           (set-f-p p))
  :hints (("goal"
           :use ((:instance rota-1-rota-f (p p))
                 (:instance rota-1-rota-f-1 (point p))
                 (:instance rot-sqrt-2*f-func (point (rota-1-rota-f-1-witness p)))
                 (:instance rot-sqrt-2*f-func-1 (point (rota-1-rota-f-1-witness p)))
                 (:instance rotation-about-arbitrary-line=>1
                            (p1 (rota-1-rota-f-1-witness p))
                            (p2 (rotation-about-arbitrary-line
                                 (angle-const)
                                 (m-p)
                                 (n-p)
                                 (rot-sqrt-2*f-func-1-witness (rota-1-rota-f-1-witness p))))
                            (angle (- (angle-const)))
                            (m (m-p))
                            (n (n-p)))
                 (:instance set-f-p (point (rot-sqrt-2*f-func-1-witness (rota-1-rota-f-1-witness p))))
                 (:instance rotation-about-arbitrary-line=>r3p-m-n
                            (p (rot-sqrt-2*f-func-1-witness (rota-1-rota-f-1-witness p)))
                            (angle (angle-const)))
                 (:instance angle-const-is-real)
                 (:instance rot-angle1-of-angle2*p=>m-n
                            (angle1 (- (angle-const)))
                            (angle2 (angle-const))
                            (p (rot-sqrt-2*f-func-1-witness (rota-1-rota-f-1-witness p))))
                 (:instance rotation-about-arbitrary-line=p-m-n
                            (angle (+ (- (angle-const)) (angle-const)))
                            (p (rot-sqrt-2*f-func-1-witness (rota-1-rota-f-1-witness p))))
                 (:instance set-f-p (point p))
                 (:instance rota-1-rota-f-iff-set-f-p-2-1
                            (p1 (rot-sqrt-2*f-func-1-witness (rota-1-rota-f-1-witness p)))
                            (p2 p))
                 )
           :in-theory nil
           )))

(defthmd rota-1-rota-f-iff-set-f-p
  (iff (set-f-p p)
       (rota-1-rota-f p))
  :hints (("goal"
           :use ((:instance rota-1-rota-f-iff-set-f-p-1)
                 (:instance rota-1-rota-f-iff-set-f-p-2))
           )))

(defun-sk rota-inv-b3-0-n-f-1 (point)
  (exists p
          (and (b3-0-n-f p)
               (m-= (rotation-about-arbitrary-line (- (angle-const)) (m-p) (n-p) p)
                    point))))

(defun rota-inv-b3-0-n-f (p)
  (and (point-in-r3 p)
       (rota-inv-b3-0-n-f-1 p)))


(defthmd f-iff-rota-inv-b3-0-n-f-1
  (implies (set-f-p p)
           (rota-inv-b3-0-n-f p))
  :hints (("goal"
           :use ((:instance rota-inv-b3-0-n-f (p p))
                 (:instance set-f-p (point p))
                 (:instance rota-1-rota-f-iff-set-f-p (p p))
                 (:instance rota-1-rota-f (p p))
                 (:instance rota-1-rota-f-1 (point p))
                 (:instance rota-inv-b3-0-n-f (p p))
                 (:instance rot-sqrt-2*ffunc-iff-f-not-z (p (rota-1-rota-f-1-witness p)))
                 (:instance f-not-z-iff-b3-0-n-f (p (rota-1-rota-f-1-witness p)))
                 (:instance rota-inv-b3-0-n-f-1-suff
                            (p (rota-1-rota-f-1-witness p))
                            (point p))
                 )
           :in-theory nil
           )))

(defthmd f-iff-rota-inv-b3-0-n-f-2
  (implies (rota-inv-b3-0-n-f p)
           (set-f-p p))
  :hints (("goal"
           :use ((:instance rota-inv-b3-0-n-f (p p))
                 (:instance set-f-p (point p))
                 (:instance rota-inv-b3-0-n-f-1 (point p))
                 (:instance f-not-z-iff-b3-0-n-f (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance rot-sqrt-2*ffunc-iff-f-not-z
                            (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance rot-sqrt-2*f-func
                            (point (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance rot-sqrt-2*f-func-1
                            (point (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance rotation-about-arbitrary-line=>1
                            (p1 (rota-inv-b3-0-n-f-1-witness p))
                            (p2 (rotation-about-arbitrary-line
                                 (angle-const)
                                 (m-p)
                                 (n-p)
                                 (rot-sqrt-2*f-func-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                            (angle (- (angle-const)))
                            (m (m-p))
                            (n (n-p)))
                 (:instance set-f-p (point (rot-sqrt-2*f-func-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                 (:instance rotation-about-arbitrary-line=>r3p-m-n
                            (p (rot-sqrt-2*f-func-1-witness (rota-inv-b3-0-n-f-1-witness p)))
                            (angle (angle-const)))
                 (:instance angle-const-is-real)
                 (:instance rot-angle1-of-angle2*p=>m-n
                            (p (rot-sqrt-2*f-func-1-witness (rota-inv-b3-0-n-f-1-witness p)))
                            (angle1 (- (angle-const)))
                            (angle2 (angle-const)))
                 (:instance rotation-about-arbitrary-line=p-m-n
                            (p (rot-sqrt-2*f-func-1-witness (rota-inv-b3-0-n-f-1-witness p)))
                            (angle (+ (- (angle-const)) (angle-const))))
                 (:instance rota-1-rota-f-iff-set-f-p-2-1
                            (p1 (rot-sqrt-2*f-func-1-witness (rota-inv-b3-0-n-f-1-witness p)))
                            (p2 p))
                 )
           :in-theory nil
           )))

(defthmd f-iff-rota-inv-b3-0-n-f
  (iff (set-f-p p)
       (rota-inv-b3-0-n-f p))
  :hints (("goal"
           :use ((:instance f-iff-rota-inv-b3-0-n-f-1)
                 (:instance f-iff-rota-inv-b3-0-n-f-2)
                 )
           )))

(defthmd b3-iff-b3-0-n-b3-f-or-rota-inv-b3-0-n-f
  (iff (b3 p)
       (or (b3-0-n-b3-f p)
           (rota-inv-b3-0-n-f p)))
  :hints (("goal"
           :use ((:instance b3=> (p p))
                 (:instance b3-0-n-b3-f-iff-b3-f (p p))
                 (:instance f-iff-rota-inv-b3-0-n-f (p p))
                 )
           :in-theory nil
           )))

(defun-sk rot*b3-f-1 (rot point)
  (exists p
          (and (b3-f p)
               (m-= (m-* rot p) point))))

(defun rot*b3-f (rot p)
  (and (point-in-r3 p)
       (rot*b3-f-1 rot p)))

(defun-sk rot*set-f-1 (rot point)
  (exists p
          (and (set-f-p p)
               (m-= (m-* rot p) point))))

(defun rot*set-f (rot p)
  (and (point-in-r3 p)
       (rot*set-f-1 rot p)))

(defthmd rot*b3-in-b3
  (implies (and (b3 p)
                (r3-rotationp rot))
           (b3 (m-* rot p)))
  :hints (("goal"
           :use ((:instance b3 (p p))
                 (:instance m-=m-*rot-p1=p2=>r-p1=r-p2
                            (p1 p)
                            (p2 (m-* rot p)))
                 (:instance set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-1-1
                            (p1 p)
                            (rot rot))
                 (:instance r3-rotationp (m rot))
                 (:instance b3 (p (m-* rot p)))
                 )
           :in-theory nil
           )))

(defthmd rotp-rot=>rot*b3-f-or-rot-sf=>b3-1
  (implies (and (m-= (m-* m1 m2) m3)
                (m-= (m-* m3 m4) m5))
           (m-= (m-* m1 m2 m4) m5)))


(defthmd rotp-rot=>b3=>rot*b3-f-or-rot-sf
  (implies (and (r3-rotationp rot)
                (b3 p))
           (or (rot*b3-f rot p)
               (rot*set-f rot p)))
  :hints (("goal"
           :use ((:instance b3 (p p))
                 (:instance rot*b3-f (rot rot) (p p))
                 (:instance rot*b3-f-1-suff (p (m-* (r3-m-inverse rot) p)) (rot rot) (point p))
                 (:instance rot*set-f (rot rot) (p p))
                 (:instance rot*set-f-1-suff (p (m-* (r3-m-inverse rot) p)) (rot rot) (point p))
                 (:instance rot*b3-in-b3
                            (rot (r3-m-inverse rot))
                            (p p))
                 (:instance rot-m=>rot-m-inv (m rot))
                 (:instance b3-f (p (m-* (r3-m-inverse rot) p)))
                 (:instance m-*-m-m-inverse (m rot))
                 (:instance r3-rotationp (m rot))
                 (:instance m-*point-id=point (p1 p))
                 (:instance rotp-rot=>rot*b3-f-or-rot-sf=>b3-1
                            (m1 rot)
                            (m2 (r3-m-inverse rot))
                            (m4 p)
                            (m3 (id-rotation))
                            (m5 p))
                 )
           :in-theory nil
           )))

(defthmd rotp-rot=>rot*b3-f-or-rot-sf=>b3
  (implies (and (r3-rotationp rot)
                (or (rot*b3-f rot p)
                    (rot*set-f rot p)))
           (b3 p))
  :hints (("goal"
           :use ((:instance b3 (p p))
                 (:instance rot*b3-f (rot rot) (p p))
                 (:instance rot*b3-f-1 (rot rot) (point p))
                 (:instance rot*set-f (rot rot) (p p))
                 (:instance rot*set-f-1 (rot rot) (point p))
                 (:instance rot*b3-in-b3
                            (p (rot*b3-f-1-witness rot p))
                            (rot rot))
                 (:instance b3-f (p (rot*b3-f-1-witness rot p)))
                 (:instance b3 (p (m-* rot (rot*b3-f-1-witness rot p))))
                 (:instance cal-radius-p1=p2
                            (p1 (m-* rot (rot*b3-f-1-witness rot p)))
                            (p2 p))
                 (:instance rot*b3-in-b3
                            (p (rot*set-f-1-witness rot p))
                            (rot rot))
                 (:instance f=>b3
                            (p (rot*set-f-1-witness rot p)))
                 (:instance b3 (p (m-* rot (rot*set-f-1-witness rot p))))
                 (:instance cal-radius-p1=p2
                            (p1 (m-* rot (rot*set-f-1-witness rot p)))
                            (p2 p))
                 )
           :in-theory nil
           )))

(defthmd rotp-rot=>rot*b3-f-or-rot-sf-iff-b3
  (implies (r3-rotationp rot)
           (iff (or (rot*b3-f rot p)
                    (rot*set-f rot p))
                (b3 p)))
  :hints (("goal"
           :use ((:instance rotp-rot=>b3=>rot*b3-f-or-rot-sf)
                 (:instance rotp-rot=>rot*b3-f-or-rot-sf=>b3))
           :in-theory nil
           )))

(defun rot-3 ()
  (a-inv-rotation (acl2-sqrt 2)))

(defun rot-4 ()
  (m-* (a-inv-rotation (acl2-sqrt 2))
       (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))) (point-on-s2-not-d))))

(defun rot-5 ()
  (m-* (rotation-3d
        (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d))
       (a-inv-rotation (acl2-sqrt 2))))

(defun rot-6 ()
  (m-* (rotation-3d
        (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d))
       (a-inv-rotation (acl2-sqrt 2))
       (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))) (point-on-s2-not-d))))

(defun rot-7 ()
  (id-rotation))

(defun rot-8 ()
  (id-rotation))

(defun-sk rot-3-inv*f (point)
  (exists p
          (and (set-f-p p)
               (m-= (m-* (r3-m-inverse (rot-3)) p) point))))

(defun b3-01 (p)
  (and (b3-0-set-a3 p)
       (b3-f p)
       (rot-3-inv*f p)))

(defun b3-11 (p)
  (and (b3-0-set-a3 p)
       (set-f-p p)
       (rot-3-inv*f p)))

(defun-sk rota-1-rot-3-b3-01-1 (point)
  (exists p
          (and (b3-01 p)
               (m-= (rotation-about-arbitrary-line (- (angle-const)) (m-p) (n-p)
                                                   (m-* (rot-3) p))
                    point))))

(defun rota-1-rot-3-b3-01 (p)
  (and (point-in-r3 p)
       (rota-1-rot-3-b3-01-1 p)))

(defun-sk rota-1-rot-3-b3-11-1 (point)
  (exists p
          (and (b3-11 p)
               (m-= (rotation-about-arbitrary-line (- (angle-const)) (m-p) (n-p)
                                                   (m-* (rot-3) p))
                    point))))

(defun rota-1-rot-3-b3-11 (p)
  (and (point-in-r3 p)
       (rota-1-rot-3-b3-11-1 p)))

(defun-sk rot-4-inv*f (point)
  (exists p
          (and (set-f-p p)
               (m-= (m-* (r3-m-inverse (rot-4)) p) point))))

(defun b4-01 (p)
  (and (b3-0-set-a4 p)
       (b3-f p)
       (rot-4-inv*f p)))

(defun b4-11 (p)
  (and (b3-0-set-a4 p)
       (set-f-p p)
       (rot-4-inv*f p)))

(defun-sk rota-1-rot-4-b4-01-1 (point)
  (exists p
          (and (b4-01 p)
               (m-= (rotation-about-arbitrary-line (- (angle-const)) (m-p) (n-p)
                                                   (m-* (rot-4) p))
                    point))))

(defun rota-1-rot-4-b4-01 (p)
  (and (point-in-r3 p)
       (rota-1-rot-4-b4-01-1 p)))

(defun-sk rota-1-rot-4-b4-11-1 (point)
  (exists p
          (and (b4-11 p)
               (m-= (rotation-about-arbitrary-line (- (angle-const)) (m-p) (n-p)
                                                   (m-* (rot-4) p))
                    point))))

(defun rota-1-rot-4-b4-11 (p)
  (and (point-in-r3 p)
       (rota-1-rot-4-b4-11-1 p)))

(defun-sk rot-5-inv*f (point)
  (exists p
          (and (set-f-p p)
               (m-= (m-* (r3-m-inverse (rot-5)) p) point))))

(defun b5-01 (p)
  (and (b3-0-set-a5 p)
       (b3-f p)
       (rot-5-inv*f p)))

(defun b5-11 (p)
  (and (b3-0-set-a5 p)
       (set-f-p p)
       (rot-5-inv*f p)))

(defun-sk rota-1-rot-5-b5-01-1 (point)
  (exists p
          (and (b5-01 p)
               (m-= (rotation-about-arbitrary-line (- (angle-const)) (m-p) (n-p)
                                                   (m-* (rot-5) p))
                    point))))

(defun rota-1-rot-5-b5-01 (p)
  (and (point-in-r3 p)
       (rota-1-rot-5-b5-01-1 p)))

(defun-sk rota-1-rot-5-b5-11-1 (point)
  (exists p
          (and (b5-11 p)
               (m-= (rotation-about-arbitrary-line (- (angle-const)) (m-p) (n-p)
                                                   (m-* (rot-5) p))
                    point))))

(defun rota-1-rot-5-b5-11 (p)
  (and (point-in-r3 p)
       (rota-1-rot-5-b5-11-1 p)))

(defun-sk rot-6-inv*f (point)
  (exists p
          (and (set-f-p p)
               (m-= (m-* (r3-m-inverse (rot-6)) p) point))))

(defun b6-01 (p)
  (and (b3-0-set-a6 p)
       (b3-f p)
       (rot-6-inv*f p)))

(defun b6-11 (p)
  (and (b3-0-set-a6 p)
       (set-f-p p)
       (rot-6-inv*f p)))

(defun-sk rota-1-rot-6-b6-01-1 (point)
  (exists p
          (and (b6-01 p)
               (m-= (rotation-about-arbitrary-line (- (angle-const)) (m-p) (n-p)
                                                   (m-* (rot-6) p))
                    point))))

(defun rota-1-rot-6-b6-01 (p)
  (and (point-in-r3 p)
       (rota-1-rot-6-b6-01-1 p)))

(defun-sk rota-1-rot-6-b6-11-1 (point)
  (exists p
          (and (b6-11 p)
               (m-= (rotation-about-arbitrary-line (- (angle-const)) (m-p) (n-p)
                                                   (m-* (rot-6) p))
                    point))))

(defun rota-1-rot-6-b6-11 (p)
  (and (point-in-r3 p)
       (rota-1-rot-6-b6-11-1 p)))

(defun-sk rot-7-inv*f (point)
  (exists p
          (and (set-f-p p)
               (m-= (m-* (r3-m-inverse (rot-7)) p) point))))

(defun b7-01 (p)
  (and (b3-0-set-a7 p)
       (b3-f p)
       (rot-7-inv*f p)))

(defun b7-11 (p)
  (and (b3-0-set-a7 p)
       (set-f-p p)
       (rot-7-inv*f p)))

(defun-sk rota-1-rot-7-b7-01-1 (point)
  (exists p
          (and (b7-01 p)
               (m-= (rotation-about-arbitrary-line (- (angle-const)) (m-p) (n-p)
                                                   (m-* (rot-7) p))
                    point))))

(defun rota-1-rot-7-b7-01 (p)
  (and (point-in-r3 p)
       (rota-1-rot-7-b7-01-1 p)))

(defun-sk rota-1-rot-7-b7-11-1 (point)
  (exists p
          (and (b7-11 p)
               (m-= (rotation-about-arbitrary-line (- (angle-const)) (m-p) (n-p)
                                                   (m-* (rot-7) p))
                    point))))

(defun rota-1-rot-7-b7-11 (p)
  (and (point-in-r3 p)
       (rota-1-rot-7-b7-11-1 p)))

(defun-sk rot-8-inv*f (point)
  (exists p
          (and (set-f-p p)
               (m-= (m-* (r3-m-inverse (rot-8)) p) point))))

(defun b8-01 (p)
  (and (b3-0-set-a8 p)
       (b3-f p)
       (rot-8-inv*f p)))

(defun b8-11 (p)
  (and (b3-0-set-a8 p)
       (set-f-p p)
       (rot-8-inv*f p)))

(defun-sk rota-1-rot-8-b8-01-1 (point)
  (exists p
          (and (b8-01 p)
               (m-= (rotation-about-arbitrary-line (- (angle-const)) (m-p) (n-p)
                                                   (m-* (rot-8) p))
                    point))))

(defun rota-1-rot-8-b8-01 (p)
  (and (point-in-r3 p)
       (rota-1-rot-8-b8-01-1 p)))

(defun-sk rota-1-rot-8-b8-11-1 (point)
  (exists p
          (and (b8-11 p)
               (m-= (rotation-about-arbitrary-line (- (angle-const)) (m-p) (n-p)
                                                   (m-* (rot-8) p))
                    point))))

(defun rota-1-rot-8-b8-11 (p)
  (and (point-in-r3 p)
       (rota-1-rot-8-b8-11-1 p)))

;; (defthmd a3-a8-rot-a-inv-b3-0-nf=>2
;;   (implies (and (m-= (m-* m1 m2 m3) m4)
;;                 (m-= (m-* m5 m1) m6)
;;                 (m-= (m-* m6 m2) m7)
;;                 (m-= (m-* m8 m7) m9)
;;                 (m-= (m-* m9 m3) m10)
;;                 (m-= (m-* m11 m10) m12))
;;            (m-= (m-* m11 m8 m5 m4) m12)))

(defthmd a3-a8-rot-a-inv-b3-0-nf=>1
  (implies (and (m-= (m-* m1 m2) m3)
                (m-= (m-* m4 m1) m5)
                (m-= (m-* m5 m2) m6))
           (m-= (m-* m4 m3) m6)))

(defthm a3-a8-rot-a-inv-b3-0-nf=>sub-3
  (equal (m-* (m-* m1 m2 m3) m4)
         (m-* m1 m2 m3 m4))
  :hints (("Goal"
           :use ((:instance associativity-of-m-*-3
                            (m1 m1)
                            (m2 m2)
                            (m3 m3))
                 (:instance associativity-of-m-*-2
                            (m1 m1)
                            (m2 m2)
                            (m3 m3))
                 (:instance associativity-of-m-*
                            (m1 m1)
                            (m2 (m-* m2 m3))
                            (m3 m4))
                 (:instance associativity-of-m-*-2
                            (m1 m2)
                            (m2 m3)
                            (m3 m4))
                 )
           ))
  :rule-classes nil
  )

(defthmd a3-a8-rot-a-inv-b3-0-nf=>
  (implies (rota-inv-b3-0-n-f p)
           (or (rota-1-rot-3-b3-11 p)
               (rota-1-rot-3-b3-01 p)
               (rota-1-rot-4-b4-11 p)
               (rota-1-rot-4-b4-01 p)
               (rota-1-rot-5-b5-11 p)
               (rota-1-rot-5-b5-01 p)
               (rota-1-rot-6-b6-11 p)
               (rota-1-rot-6-b6-01 p)
               (rota-1-rot-7-b7-11 p)
               (rota-1-rot-7-b7-01 p)
               (rota-1-rot-8-b8-11 p)
               (rota-1-rot-8-b8-01 p)))
  :hints (("Goal"
           :cases ((b3-0-a-inv-b3-0-set-a3 (ROTA-INV-B3-0-N-F-1-WITNESS P))
                   (b3-0-a-inv-r-b3-0-set-a4 (ROTA-INV-B3-0-N-F-1-WITNESS P))
                   (b3-0-r-1-a-inv-b3-0-set-a5 (ROTA-INV-B3-0-N-F-1-WITNESS P))
                   (b3-0-r-1-a-inv-r-b3-0-set-a6 (ROTA-INV-B3-0-N-F-1-WITNESS P))
                   (b3-0-set-a7 (ROTA-INV-B3-0-N-F-1-WITNESS P))
                   (b3-0-set-a8 (ROTA-INV-B3-0-N-F-1-WITNESS P)))
           :use ((:instance ROTA-INV-B3-0-N-F (p p))
                 (:instance ROTA-INV-B3-0-N-F-1 (point p))
                 (:instance b3-0-n-f (p (ROTA-INV-B3-0-N-F-1-WITNESS P)))
                 (:instance b3-0-iff-a3-to-a8 (p (ROTA-INV-B3-0-N-F-1-WITNESS P)))
                 )
           :in-theory nil
           )
          ("Subgoal 6"
           :use((:instance b3-0-a-inv-b3-0-set-a3 (p (ROTA-INV-B3-0-N-F-1-WITNESS P)))
                (:instance b3-0-a-inv-b3-0-set-a3-1 (p (ROTA-INV-B3-0-N-F-1-WITNESS P)))
                (:instance rota-1-rot-3-b3-01 (p p))
                (:instance rota-1-rot-3-b3-11 (p p))
                (:instance rota-1-rot-3-b3-01-1-suff
                           (point p)
                           (p (B3-0-A-INV-B3-0-SET-A3-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
                (:instance b3-01
                           (p (B3-0-A-INV-B3-0-SET-A3-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
                (:instance rota-1-rot-3-b3-11-1-suff
                           (point p)
                           (p (B3-0-A-INV-B3-0-SET-A3-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
                (:instance b3-11
                           (p (B3-0-A-INV-B3-0-SET-A3-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
                (:instance b3-f
                           (p (B3-0-A-INV-B3-0-SET-A3-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
                (:instance b3-0-iff-a1-to-a14
                           (p (B3-0-A-INV-B3-0-SET-A3-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
                (:instance b3-0
                           (p (B3-0-A-INV-B3-0-SET-A3-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
                (:instance b3 (p (B3-0-A-INV-B3-0-SET-A3-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
                (:instance rot-3-inv*f-suff
                           (point (B3-0-A-INV-B3-0-SET-A3-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P)))
                           (p (ROTA-INV-B3-0-N-F-1-WITNESS P)))
                (:instance rot-3)
                (:instance a3-a8-rot-a-inv-b3-0-nf=>1
                           (m1 (ROT-3))
                           (m2 (B3-0-A-INV-B3-0-SET-A3-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P)))
                           (m3 (ROTA-INV-B3-0-N-F-1-WITNESS P))
                           (m4 (R3-M-INVERSE (ROT-3)))
                           (m5 (id-rotation))
                           (m6 (B3-0-A-INV-B3-0-SET-A3-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
                (:instance m-*-m-inverse-m
                           (m (rot-3)))
                (:instance m-*point-id=point
                           (p1 (B3-0-A-INV-B3-0-SET-A3-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
                (:instance base-rotations
                           (x (acl2-sqrt 2)))
                (:instance r3-rotationp (m (A-INV-ROTATION (ACL2-SQRT 2))))
                (:instance rotation-about-arbitrary-line=>1
                           (p1 (M-* (ROT-3)
                                    (B3-0-A-INV-B3-0-SET-A3-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
                           (p2 (ROTA-INV-B3-0-N-F-1-WITNESS P))
                           (angle (- (angle-const)))
                           (m (m-p))
                           (n (n-p)))
                (:instance set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-1-1
                           (p1 (B3-0-A-INV-B3-0-SET-A3-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P)))
                           (rot (rot-3)))
                )
           :in-theory nil
           )
          ("Subgoal 5"
           :use((:instance B3-0-A-INV-R-B3-0-SET-A4 (p (ROTA-INV-B3-0-N-F-1-WITNESS P)))
                (:instance B3-0-A-INV-R-B3-0-SET-A4-1 (p (ROTA-INV-B3-0-N-F-1-WITNESS P)))
                (:instance rota-1-rot-4-b4-01 (p p))
                (:instance rota-1-rot-4-b4-11 (p p))
                (:instance rota-1-rot-4-b4-01-1-suff
                           (point p)
                           (p (B3-0-A-INV-R-B3-0-SET-A4-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
                (:instance b4-01
                           (p (B3-0-A-INV-R-B3-0-SET-A4-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
                (:instance rota-1-rot-4-b4-11-1-suff
                           (point p)
                           (p (B3-0-A-INV-R-B3-0-SET-A4-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
                (:instance b4-11
                           (p (B3-0-A-INV-R-B3-0-SET-A4-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
                (:instance b3-f
                           (p (B3-0-A-INV-R-B3-0-SET-A4-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
                (:instance b3-0-iff-a1-to-a14
                           (p (B3-0-A-INV-R-B3-0-SET-A4-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
                (:instance b3-0
                           (p (B3-0-A-INV-R-B3-0-SET-A4-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
                (:instance b3 (p (B3-0-A-INV-R-B3-0-SET-A4-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
                (:instance rot-4-inv*f-suff
                           (point (B3-0-A-INV-R-B3-0-SET-A4-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P)))
                           (p (ROTA-INV-B3-0-N-F-1-WITNESS P)))
                (:instance rot-4)
                (:instance a3-a8-rot-a-inv-b3-0-nf=>1
                           (m1 (ROT-4))
                           (m2 (B3-0-A-INV-R-B3-0-SET-A4-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P)))
                           (m3 (ROTA-INV-B3-0-N-F-1-WITNESS P))
                           (m4 (R3-M-INVERSE (ROT-4)))
                           (m5 (id-rotation))
                           (m6 (B3-0-A-INV-R-B3-0-SET-A4-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
                (:instance associativity-of-m-*
                           (m1 (A-INV-ROTATION (ACL2-SQRT 2)))
                           (m2 (ROTATION-3D
                                (EXISTS-IN-INTERVAL-BUT-NOT-IN-ANGLE-SEQUENCE-WITNESS 0 (* 2 (ACL2-PI)))
                                (POINT-ON-S2-NOT-D)))
                           (m3 (B3-0-A-INV-R-B3-0-SET-A4-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
                (:instance m-*-m-inverse-m
                           (m (rot-4)))
                (:instance rot*rot-is-rot
                           (m1 (a-inv-rotation (acl2-sqrt 2)))
                           (m2 (ROTATION-3D
                                (EXISTS-IN-INTERVAL-BUT-NOT-IN-ANGLE-SEQUENCE-WITNESS 0 (* 2 (ACL2-PI)))
                                (POINT-ON-S2-NOT-D))))
                (:instance m-*point-id=point
                           (p1 (B3-0-A-INV-R-B3-0-SET-A4-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
                (:instance base-rotations
                           (x (acl2-sqrt 2)))
                (:instance r3-rotationp (m (rot-4)))
                (:instance r3-rotationp-r-theta
                           (angle (EXISTS-IN-INTERVAL-BUT-NOT-IN-ANGLE-SEQUENCE-WITNESS 0 (* 2 (ACL2-PI)))))
                (:instance witness-not-in-angle-sequence)
                (:instance rotation-about-arbitrary-line=>1
                           (p1 (M-* (ROT-4)
                                    (B3-0-A-INV-R-B3-0-SET-A4-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
                           (p2 (ROTA-INV-B3-0-N-F-1-WITNESS P))
                           (angle (- (angle-const)))
                           (m (m-p))
                           (n (n-p)))
                (:instance set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-1-1
                           (p1 (B3-0-A-INV-R-B3-0-SET-A4-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P)))
                           (rot (rot-4)))
                )
           :in-theory nil
           )
          ("Subgoal 4"
           :use((:instance b3-0-r-1-a-inv-b3-0-set-a5 (p (ROTA-INV-B3-0-N-F-1-WITNESS P)))
                (:instance b3-0-r-1-a-inv-b3-0-set-a5-1 (p (ROTA-INV-B3-0-N-F-1-WITNESS P)))
                (:instance rota-1-rot-5-b5-01 (p p))
                (:instance rota-1-rot-5-b5-11 (p p))
                (:instance rota-1-rot-5-b5-01-1-suff
                           (point p)
                           (p (b3-0-r-1-a-inv-b3-0-set-a5-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
                (:instance b5-01
                           (p (b3-0-r-1-a-inv-b3-0-set-a5-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
                (:instance rota-1-rot-5-b5-11-1-suff
                           (point p)
                           (p (b3-0-r-1-a-inv-b3-0-set-a5-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
                (:instance b5-11
                           (p (b3-0-r-1-a-inv-b3-0-set-a5-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
                (:instance b3-f
                           (p (b3-0-r-1-a-inv-b3-0-set-a5-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
                (:instance b3-0-iff-a1-to-a14
                           (p (b3-0-r-1-a-inv-b3-0-set-a5-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
                (:instance b3-0
                           (p (b3-0-r-1-a-inv-b3-0-set-a5-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
                (:instance b3 (p (b3-0-r-1-a-inv-b3-0-set-a5-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
                (:instance rot-5-inv*f-suff
                           (point (b3-0-r-1-a-inv-b3-0-set-a5-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P)))
                           (p (ROTA-INV-B3-0-N-F-1-WITNESS P)))
                (:instance rot-5)
                (:instance a3-a8-rot-a-inv-b3-0-nf=>1
                           (m1 (ROT-5))
                           (m2 (b3-0-r-1-a-inv-b3-0-set-a5-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P)))
                           (m3 (ROTA-INV-B3-0-N-F-1-WITNESS P))
                           (m4 (R3-M-INVERSE (ROT-5)))
                           (m5 (id-rotation))
                           (m6 (b3-0-r-1-a-inv-b3-0-set-a5-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
                (:instance associativity-of-m-*
                           (m2 (A-INV-ROTATION (ACL2-SQRT 2)))
                           (m1 (ROTATION-3D
                                (- (EXISTS-IN-INTERVAL-BUT-NOT-IN-ANGLE-SEQUENCE-WITNESS 0 (* 2 (ACL2-PI))))
                                (POINT-ON-S2-NOT-D)))
                           (m3 (b3-0-r-1-a-inv-b3-0-set-a5-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
                (:instance m-*-m-inverse-m
                           (m (rot-5)))
                (:instance rot*rot-is-rot
                           (m2 (a-inv-rotation (acl2-sqrt 2)))
                           (m1 (ROTATION-3D
                                (- (EXISTS-IN-INTERVAL-BUT-NOT-IN-ANGLE-SEQUENCE-WITNESS 0 (* 2 (ACL2-PI))))
                                (POINT-ON-S2-NOT-D))))
                (:instance m-*point-id=point
                           (p1 (b3-0-r-1-a-inv-b3-0-set-a5-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
                (:instance base-rotations
                           (x (acl2-sqrt 2)))
                (:instance r3-rotationp (m (rot-5)))
                (:instance r3-rotationp-r-theta
                           (angle (- (EXISTS-IN-INTERVAL-BUT-NOT-IN-ANGLE-SEQUENCE-WITNESS 0 (* 2 (ACL2-PI))))))
                (:instance witness-not-in-angle-sequence)
                (:instance rotation-about-arbitrary-line=>1
                           (p1 (M-* (ROT-5)
                                    (b3-0-r-1-a-inv-b3-0-set-a5-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
                           (p2 (ROTA-INV-B3-0-N-F-1-WITNESS P))
                           (angle (- (angle-const)))
                           (m (m-p))
                           (n (n-p)))
                (:instance set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-1-1
                           (p1 (b3-0-r-1-a-inv-b3-0-set-a5-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P)))
                           (rot (rot-5)))
                )
           :in-theory nil
           )
          ("Subgoal 3"
           :use((:instance B3-0-R-1-A-INV-R-B3-0-SET-A6 (p (ROTA-INV-B3-0-N-F-1-WITNESS P)))
                (:instance B3-0-R-1-A-INV-R-B3-0-SET-A6-1 (p (ROTA-INV-B3-0-N-F-1-WITNESS P)))
                (:instance rota-1-rot-6-b6-01 (p p))
                (:instance rota-1-rot-6-b6-11 (p p))
                (:instance rota-1-rot-6-b6-01-1-suff
                           (point p)
                           (p (B3-0-R-1-A-INV-R-B3-0-SET-A6-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
                (:instance b6-01
                           (p (B3-0-R-1-A-INV-R-B3-0-SET-A6-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
                (:instance rota-1-rot-6-b6-11-1-suff
                           (point p)
                           (p (B3-0-R-1-A-INV-R-B3-0-SET-A6-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
                (:instance b6-11
                           (p (B3-0-R-1-A-INV-R-B3-0-SET-A6-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
                (:instance b3-f
                           (p (B3-0-R-1-A-INV-R-B3-0-SET-A6-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
                (:instance b3-0-iff-a1-to-a14
                           (p (B3-0-R-1-A-INV-R-B3-0-SET-A6-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
                (:instance b3-0
                           (p (B3-0-R-1-A-INV-R-B3-0-SET-A6-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
                (:instance b3 (p (B3-0-R-1-A-INV-R-B3-0-SET-A6-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
                (:instance rot-6-inv*f-suff
                           (point (B3-0-R-1-A-INV-R-B3-0-SET-A6-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P)))
                           (p (ROTA-INV-B3-0-N-F-1-WITNESS P)))
                (:instance rot-6)
                (:instance a3-a8-rot-a-inv-b3-0-nf=>1
                           (m1 (ROT-6))
                           (m2 (B3-0-R-1-A-INV-R-B3-0-SET-A6-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P)))
                           (m3 (ROTA-INV-B3-0-N-F-1-WITNESS P))
                           (m4 (R3-M-INVERSE (ROT-6)))
                           (m5 (id-rotation))
                           (m6 (B3-0-R-1-A-INV-R-B3-0-SET-A6-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
                (:instance associativity-of-m-*
                           (m2 (A-INV-ROTATION (ACL2-SQRT 2)))
                           (m1 (ROTATION-3D
                                (- (EXISTS-IN-INTERVAL-BUT-NOT-IN-ANGLE-SEQUENCE-WITNESS 0 (* 2 (ACL2-PI))))
                                (POINT-ON-S2-NOT-D)))
                           (m3 (b3-0-r-1-a-inv-b3-0-set-a5-1-WITNESS
                                (ROTA-INV-B3-0-N-F-1-WITNESS P))))
                (:instance a3-a8-rot-a-inv-b3-0-nf=>sub-3
                           (m1 (ROTATION-3D (- (EXISTS-IN-INTERVAL-BUT-NOT-IN-ANGLE-SEQUENCE-WITNESS
                                                0 (* 2 (ACL2-PI))))
                                            (POINT-ON-S2-NOT-D)))
                           (m2 (A-INV-ROTATION (ACL2-SQRT 2)))
                           (m3 (ROTATION-3D (EXISTS-IN-INTERVAL-BUT-NOT-IN-ANGLE-SEQUENCE-WITNESS
                                             0 (* 2 (ACL2-PI)))
                                            (POINT-ON-S2-NOT-D)))
                           (m4 (B3-0-R-1-A-INV-R-B3-0-SET-A6-1-WITNESS
                                (ROTA-INV-B3-0-N-F-1-WITNESS P))))
                (:instance m-*-m-inverse-m
                           (m (rot-6)))
                (:instance b3-0-r-1-a-inv-r-b3-0-a6-iff-b3-0-r-1-a-1-r-a6-1
                           (m2 (a-inv-rotation (acl2-sqrt 2)))
                           (m1 (ROTATION-3D
                                (- (EXISTS-IN-INTERVAL-BUT-NOT-IN-ANGLE-SEQUENCE-WITNESS 0 (* 2 (ACL2-PI))))
                                (POINT-ON-S2-NOT-D)))
                           (m3 (ROTATION-3D
                                (EXISTS-IN-INTERVAL-BUT-NOT-IN-ANGLE-SEQUENCE-WITNESS 0 (* 2 (ACL2-PI)))
                                (POINT-ON-S2-NOT-D))))
                (:instance m-*point-id=point
                           (p1 (B3-0-R-1-A-INV-R-B3-0-SET-A6-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
                (:instance base-rotations
                           (x (acl2-sqrt 2)))
                (:instance r3-rotationp (m (rot-6)))
                (:instance r3-rotationp-r-theta
                           (angle (- (EXISTS-IN-INTERVAL-BUT-NOT-IN-ANGLE-SEQUENCE-WITNESS 0 (* 2 (ACL2-PI))))))
                (:instance r3-rotationp-r-theta
                           (angle (EXISTS-IN-INTERVAL-BUT-NOT-IN-ANGLE-SEQUENCE-WITNESS 0 (* 2 (ACL2-PI)))))
                (:instance witness-not-in-angle-sequence)
                (:instance rotation-about-arbitrary-line=>1
                           (p1 (M-* (ROT-6)
                                    (B3-0-R-1-A-INV-R-B3-0-SET-A6-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
                           (p2 (ROTA-INV-B3-0-N-F-1-WITNESS P))
                           (angle (- (angle-const)))
                           (m (m-p))
                           (n (n-p)))
                (:instance set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-1-1
                           (p1 (B3-0-R-1-A-INV-R-B3-0-SET-A6-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P)))
                           (rot (rot-6)))
                )
           :in-theory nil
           )
          ("Subgoal 2"
           :use((:instance b3-0-set-a7 (p (ROTA-INV-B3-0-N-F-1-WITNESS P)))
                (:instance rota-1-rot-7-b7-01 (p p))
                (:instance rota-1-rot-7-b7-11 (p p))
                (:instance rota-1-rot-7-b7-01-1-suff
                           (point p)
                           (p (ROTA-INV-B3-0-N-F-1-WITNESS P)))
                (:instance b7-01
                           (p (ROTA-INV-B3-0-N-F-1-WITNESS P)))
                (:instance rota-1-rot-7-b7-11-1-suff
                           (point p)
                           (p (ROTA-INV-B3-0-N-F-1-WITNESS P)))
                (:instance b7-11
                           (p (ROTA-INV-B3-0-N-F-1-WITNESS P)))
                (:instance b3-f
                           (p (ROTA-INV-B3-0-N-F-1-WITNESS P)))
                (:instance b3-0-iff-a1-to-a14
                           (p (ROTA-INV-B3-0-N-F-1-WITNESS P)))
                (:instance b3-0
                           (p (ROTA-INV-B3-0-N-F-1-WITNESS P)))
                (:instance b3 (p (ROTA-INV-B3-0-N-F-1-WITNESS P)))
                (:instance rot-7-inv*f-suff
                           (point (ROTA-INV-B3-0-N-F-1-WITNESS P))
                           (p (ROTA-INV-B3-0-N-F-1-WITNESS P)))
                (:instance rot-7)
                (:instance a3-a8-rot-a-inv-b3-0-nf=>1
                           (m1 (ROT-7))
                           (m2 (ROTA-INV-B3-0-N-F-1-WITNESS P))
                           (m3 (ROTA-INV-B3-0-N-F-1-WITNESS P))
                           (m4 (R3-M-INVERSE (ROT-7)))
                           (m5 (id-rotation))
                           (m6 (ROTA-INV-B3-0-N-F-1-WITNESS P)))
                (:instance m-*-m-inverse-m
                           (m (rot-7)))
                (:instance m-*point-id=point
                           (p1 (ROTA-INV-B3-0-N-F-1-WITNESS P)))
                (:instance base-rotations
                           (x (acl2-sqrt 2)))
                (:instance r3-rotationp (m (id-rotation)))
                (:instance rotation-about-arbitrary-line=>1
                           (p1 (M-* (ROT-7)
                                    (ROTA-INV-B3-0-N-F-1-WITNESS P)))
                           (p2 (ROTA-INV-B3-0-N-F-1-WITNESS P))
                           (angle (- (angle-const)))
                           (m (m-p))
                           (n (n-p)))
                (:instance set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-1-1
                           (p1 (ROTA-INV-B3-0-N-F-1-WITNESS P))
                           (rot (rot-7)))
                )
           :in-theory nil
           )
          ("Subgoal 1"
           :use((:instance b3-0-set-a8 (p (ROTA-INV-B3-0-N-F-1-WITNESS P)))
                (:instance rota-1-rot-8-b8-01 (p p))
                (:instance rota-1-rot-8-b8-11 (p p))
                (:instance rota-1-rot-8-b8-01-1-suff
                           (point p)
                           (p (ROTA-INV-B3-0-N-F-1-WITNESS P)))
                (:instance b8-01
                           (p (ROTA-INV-B3-0-N-F-1-WITNESS P)))
                (:instance rota-1-rot-8-b8-11-1-suff
                           (point p)
                           (p (ROTA-INV-B3-0-N-F-1-WITNESS P)))
                (:instance b8-11
                           (p (ROTA-INV-B3-0-N-F-1-WITNESS P)))
                (:instance b3-f
                           (p (ROTA-INV-B3-0-N-F-1-WITNESS P)))
                (:instance b3-0-iff-a1-to-a14
                           (p (ROTA-INV-B3-0-N-F-1-WITNESS P)))
                (:instance b3-0
                           (p (ROTA-INV-B3-0-N-F-1-WITNESS P)))
                (:instance b3 (p (ROTA-INV-B3-0-N-F-1-WITNESS P)))
                (:instance rot-8-inv*f-suff
                           (point (ROTA-INV-B3-0-N-F-1-WITNESS P))
                           (p (ROTA-INV-B3-0-N-F-1-WITNESS P)))
                (:instance rot-8)
                (:instance a3-a8-rot-a-inv-b3-0-nf=>1
                           (m1 (ROT-8))
                           (m2 (ROTA-INV-B3-0-N-F-1-WITNESS P))
                           (m3 (ROTA-INV-B3-0-N-F-1-WITNESS P))
                           (m4 (R3-M-INVERSE (ROT-8)))
                           (m5 (id-rotation))
                           (m6 (ROTA-INV-B3-0-N-F-1-WITNESS P)))
                (:instance m-*-m-inverse-m
                           (m (rot-8)))
                (:instance m-*point-id=point
                           (p1 (ROTA-INV-B3-0-N-F-1-WITNESS P)))
                (:instance base-rotations
                           (x (acl2-sqrt 2)))
                (:instance r3-rotationp (m (id-rotation)))
                (:instance rotation-about-arbitrary-line=>1
                           (p1 (M-* (ROT-8)
                                    (ROTA-INV-B3-0-N-F-1-WITNESS P)))
                           (p2 (ROTA-INV-B3-0-N-F-1-WITNESS P))
                           (angle (- (angle-const)))
                           (m (m-p))
                           (n (n-p)))
                (:instance set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-1-1
                           (p1 (ROTA-INV-B3-0-N-F-1-WITNESS P))
                           (rot (rot-8)))
                )
           :in-theory nil
           )
          ))

(defthmd rot*b3-0-set=>b3-0
  (implies (and (or (b3-0-set-a1 p)
                    (b3-0-set-a2 p)
                    (b3-0-set-a3 p)
                    (b3-0-set-a4 p)
                    (b3-0-set-a5 p)
                    (b3-0-set-a6 p)
                    (b3-0-set-a7 p)
                    (b3-0-set-a8 p)
                    (b3-0-set-a9 p)
                    (b3-0-set-a10 p)
                    (b3-0-set-a11 p)
                    (b3-0-set-a12 p)
                    (b3-0-set-a13 p)
                    (b3-0-set-a14 p))
                (r3-rotationp rot))
           (b3-0 (m-* rot p)))
  :hints (("Goal"
           :use ((:instance b3-0-iff-a1-to-a14
                            (p p))
                 (:instance m-=m-*rot-p1=p2=>r-p1=r-p2
                            (p1 p)
                            (rot rot)
                            (p2 (m-* rot p)))
                 (:instance b3-0-set-a1 (p p))
                 (:instance b3-0-set-a2 (p p))
                 (:instance b3-0-set-a3 (p p))
                 (:instance b3-0-set-a4 (p p))
                 (:instance b3-0-set-a5 (p p))
                 (:instance b3-0-set-a6 (p p))
                 (:instance b3-0-set-a7 (p p))
                 (:instance b3-0-set-a8 (p p))
                 (:instance b3-0-set-a9 (p p))
                 (:instance b3-0-set-a10 (p p))
                 (:instance b3-0-set-a11 (p p))
                 (:instance b3-0-set-a12 (p p))
                 (:instance b3-0-set-a13 (p p))
                 (:instance b3-0-set-a14 (p p))
                 (:instance b3-0 (p (m-* rot p)))
                 (:instance set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-1-1 (p1 p)
                            (rot rot))
                 (:instance r3-rotationp (m rot))
                 )
           :in-theory nil
           )))

(defthmd rota-1-rot-3-b3-01-or-11=>2
  (implies (and (r3-rotationp rot)
                (set-f-p p1)
                (point-in-r3 p2)
                (m-= (m-* (r3-m-inverse rot) p1) p2))
           (set-f-p (m-* rot p2)))
  :hints (("Goal"
           :use ((:instance a3-a8-rot-a-inv-b3-0-nf=>1
                            (m1 (r3-m-inverse rot))
                            (m2 p1)
                            (m3 p2)
                            (m4 rot)
                            (m5 (id-rotation))
                            (m6 p1))
                 (:instance m-*-m-m-inverse (m rot))
                 (:instance r3-rotationp (m rot))
                 (:instance rota-1-rota-f-iff-set-f-p-2-1
                            (p1 p1)
                            (p2 (M-* ROT P2)))
                 (:instance set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-1-1
                            (p1 p2)
                            (rot rot))
                 (:instance m-*point-id=point (p1 p1))
                 (:instance set-f-p (point p1))
                 )
           :in-theory nil
           )))

(defthmd rota-1-rot-3-8-b-3-8-01-or-11=>
  (implies (or (rota-1-rot-3-b3-11 p)
               (rota-1-rot-3-b3-01 p)
               (rota-1-rot-4-b4-11 p)
               (rota-1-rot-4-b4-01 p)
               (rota-1-rot-5-b5-11 p)
               (rota-1-rot-5-b5-01 p)
               (rota-1-rot-6-b6-11 p)
               (rota-1-rot-6-b6-01 p)
               (rota-1-rot-7-b7-11 p)
               (rota-1-rot-7-b7-01 p)
               (rota-1-rot-8-b8-11 p)
               (rota-1-rot-8-b8-01 p))
           (rota-inv-b3-0-n-f p))
  :hints (("Goal"
           :cases ((or (rota-1-rot-3-b3-11 p)
                       (rota-1-rot-3-b3-01 p))
                   (or (rota-1-rot-4-b4-11 p)
                       (rota-1-rot-4-b4-01 p))
                   (or (rota-1-rot-5-b5-11 p)
                       (rota-1-rot-5-b5-01 p))
                   (or (rota-1-rot-6-b6-11 p)
                       (rota-1-rot-6-b6-01 p))
                   (or (rota-1-rot-7-b7-11 p)
                       (rota-1-rot-7-b7-01 p))
                   (or (rota-1-rot-8-b8-11 p)
                       (rota-1-rot-8-b8-01 p)))
           :in-theory nil)
          ("Subgoal 6"
           :use ((:instance rota-1-rot-3-b3-11 (p p))
                 (:instance rota-1-rot-3-b3-11-1 (point p))
                 (:instance rota-inv-b3-0-n-f (p p))
                 (:instance ROTA-INV-B3-0-N-F-1-SUFF
                            (point p)
                            (p (M-* (ROT-3)
                                    (ROTA-1-ROT-3-B3-11-1-WITNESS P))))
                 (:instance b3-11 (p (ROTA-1-ROT-3-B3-11-1-WITNESS P)))
                 (:instance rot*b3-0-set=>b3-0
                            (rot (rot-3))
                            (p (ROTA-1-ROT-3-B3-11-1-WITNESS P)))
                 (:instance b3-0-set-a3 (p (ROTA-1-ROT-3-B3-11-1-WITNESS P)))
                 (:instance b3-0-n-f (p (M-* (ROT-3)
                                             (ROTA-1-ROT-3-B3-11-1-WITNESS P))))
                 (:instance rot-3-inv*f (point (ROTA-1-ROT-3-B3-11-1-WITNESS P)))
                 (:instance rota-1-rot-3-b3-01-or-11=>2
                            (rot (rot-3))
                            (p1 (ROT-3-INV*F-WITNESS (ROTA-1-ROT-3-B3-11-1-WITNESS P)))
                            (p2 (ROTA-1-ROT-3-B3-11-1-WITNESS P)))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance rot-3)
                 (:instance rota-1-rot-3-b3-01 (p p))
                 (:instance rota-1-rot-3-b3-01-1 (point p))
                 (:instance ROTA-INV-B3-0-N-F-1-SUFF
                            (point p)
                            (p (M-* (ROT-3)
                                    (ROTA-1-ROT-3-B3-01-1-WITNESS P))))
                 (:instance b3-01 (p (ROTA-1-ROT-3-B3-01-1-WITNESS P)))
                 (:instance rot*b3-0-set=>b3-0
                            (rot (rot-3))
                            (p (ROTA-1-ROT-3-B3-01-1-WITNESS P)))
                 (:instance b3-0-set-a3 (p (ROTA-1-ROT-3-B3-01-1-WITNESS P)))
                 (:instance b3-0-n-f (p (M-* (ROT-3)
                                             (ROTA-1-ROT-3-B3-01-1-WITNESS P))))
                 (:instance rot-3-inv*f (point (ROTA-1-ROT-3-B3-01-1-WITNESS P)))
                 (:instance rota-1-rot-3-b3-01-or-11=>2
                            (rot (rot-3))
                            (p1 (ROT-3-INV*F-WITNESS (ROTA-1-ROT-3-B3-01-1-WITNESS P)))
                            (p2 (ROTA-1-ROT-3-B3-01-1-WITNESS P))))
           :in-theory nil
           )
          ("Subgoal 5"
           :use ((:instance rota-1-rot-4-b4-11 (p p))
                 (:instance rota-1-rot-4-b4-11-1 (point p))
                 (:instance rota-inv-b3-0-n-f (p p))
                 (:instance ROTA-INV-B3-0-N-F-1-SUFF
                            (point p)
                            (p (M-* (ROT-4)
                                    (ROTA-1-ROT-4-B4-11-1-WITNESS P))))
                 (:instance b4-11 (p (ROTA-1-ROT-4-B4-11-1-WITNESS P)))
                 (:instance rot*b3-0-set=>b3-0
                            (rot (rot-4))
                            (p (ROTA-1-ROT-4-B4-11-1-WITNESS P)))
                 (:instance b3-0-set-a4 (p (ROTA-1-ROT-4-B4-11-1-WITNESS P)))
                 (:instance b3-0-n-f (p (M-* (ROT-4)
                                             (ROTA-1-ROT-4-B4-11-1-WITNESS P))))
                 (:instance rot-4-inv*f (point (ROTA-1-ROT-4-B4-11-1-WITNESS P)))
                 (:instance rota-1-rot-3-b3-01-or-11=>2
                            (rot (rot-4))
                            (p1 (ROT-4-INV*F-WITNESS (ROTA-1-ROT-4-B4-11-1-WITNESS P)))
                            (p2 (ROTA-1-ROT-4-B4-11-1-WITNESS P)))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance rot-4)
                 (:instance rot*rot-is-rot
                            (m1 (a-inv-rotation (acl2-sqrt 2)))
                            (m2 (ROTATION-3D
                                 (EXISTS-IN-INTERVAL-BUT-NOT-IN-ANGLE-SEQUENCE-WITNESS 0 (* 2 (ACL2-PI)))
                                 (POINT-ON-S2-NOT-D))))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance r3-rotationp-r-theta
                            (angle (EXISTS-IN-INTERVAL-BUT-NOT-IN-ANGLE-SEQUENCE-WITNESS 0 (* 2 (ACL2-PI)))))
                 (:instance witness-not-in-angle-sequence)
                 (:instance rota-1-rot-4-b4-01 (p p))
                 (:instance rota-1-rot-4-b4-01-1 (point p))
                 (:instance ROTA-INV-B3-0-N-F-1-SUFF
                            (point p)
                            (p (M-* (ROT-4)
                                    (ROTA-1-ROT-4-B4-01-1-WITNESS P))))
                 (:instance b4-01 (p (ROTA-1-ROT-4-B4-01-1-WITNESS P)))
                 (:instance rot*b3-0-set=>b3-0
                            (rot (rot-4))
                            (p (ROTA-1-ROT-4-B4-01-1-WITNESS P)))
                 (:instance b3-0-set-a4 (p (ROTA-1-ROT-4-B4-01-1-WITNESS P)))
                 (:instance b3-0-n-f (p (M-* (ROT-4)
                                             (ROTA-1-ROT-4-B4-01-1-WITNESS P))))
                 (:instance rot-4-inv*f (point (ROTA-1-ROT-4-B4-01-1-WITNESS P)))
                 (:instance rota-1-rot-3-b3-01-or-11=>2
                            (rot (rot-4))
                            (p1 (ROT-4-INV*F-WITNESS (ROTA-1-ROT-4-B4-01-1-WITNESS P)))
                            (p2 (ROTA-1-ROT-4-B4-01-1-WITNESS P)))
                 )
           :in-theory nil
           )
          ("Subgoal 4"
           :use ((:instance rota-1-rot-5-b5-11 (p p))
                 (:instance rota-1-rot-5-b5-11-1 (point p))
                 (:instance rota-inv-b3-0-n-f (p p))
                 (:instance ROTA-INV-B3-0-N-F-1-SUFF
                            (point p)
                            (p (M-* (ROT-5)
                                    (ROTA-1-ROT-5-B5-11-1-WITNESS P))))
                 (:instance b5-11 (p (ROTA-1-ROT-5-B5-11-1-WITNESS P)))
                 (:instance rot*b3-0-set=>b3-0
                            (rot (rot-5))
                            (p (ROTA-1-ROT-5-B5-11-1-WITNESS P)))
                 (:instance b3-0-set-a5 (p (ROTA-1-ROT-5-B5-11-1-WITNESS P)))
                 (:instance b3-0-n-f (p (M-* (ROT-5)
                                             (ROTA-1-ROT-5-B5-11-1-WITNESS P))))
                 (:instance rot-5-inv*f (point (ROTA-1-ROT-5-B5-11-1-WITNESS P)))
                 (:instance rota-1-rot-3-b3-01-or-11=>2
                            (rot (rot-5))
                            (p1 (ROT-5-INV*F-WITNESS (ROTA-1-ROT-5-B5-11-1-WITNESS P)))
                            (p2 (ROTA-1-ROT-5-B5-11-1-WITNESS P)))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance rot-5)
                 (:instance rot*rot-is-rot
                            (m2 (a-inv-rotation (acl2-sqrt 2)))
                            (m1 (ROTATION-3D
                                 (- (EXISTS-IN-INTERVAL-BUT-NOT-IN-ANGLE-SEQUENCE-WITNESS 0 (* 2 (ACL2-PI))))
                                 (POINT-ON-S2-NOT-D))))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance r3-rotationp-r-theta
                            (angle (- (EXISTS-IN-INTERVAL-BUT-NOT-IN-ANGLE-SEQUENCE-WITNESS 0 (* 2 (ACL2-PI))))))
                 (:instance witness-not-in-angle-sequence)
                 (:instance rota-1-rot-5-b5-01 (p p))
                 (:instance rota-1-rot-5-b5-01-1 (point p))
                 (:instance ROTA-INV-B3-0-N-F-1-SUFF
                            (point p)
                            (p (M-* (ROT-5)
                                    (ROTA-1-ROT-5-B5-01-1-WITNESS P))))
                 (:instance b5-01 (p (ROTA-1-ROT-5-B5-01-1-WITNESS P)))
                 (:instance rot*b3-0-set=>b3-0
                            (rot (rot-5))
                            (p (ROTA-1-ROT-5-B5-01-1-WITNESS P)))
                 (:instance b3-0-set-a5 (p (ROTA-1-ROT-5-B5-01-1-WITNESS P)))
                 (:instance b3-0-n-f (p (M-* (ROT-5)
                                             (ROTA-1-ROT-5-B5-01-1-WITNESS P))))
                 (:instance rot-5-inv*f (point (ROTA-1-ROT-5-B5-01-1-WITNESS P)))
                 (:instance rota-1-rot-3-b3-01-or-11=>2
                            (rot (rot-5))
                            (p1 (ROT-5-INV*F-WITNESS (ROTA-1-ROT-5-B5-01-1-WITNESS P)))
                            (p2 (ROTA-1-ROT-5-B5-01-1-WITNESS P)))
                 )
           :in-theory nil
           )
          ("Subgoal 3"
           :use ((:instance rota-1-rot-6-b6-11 (p p))
                 (:instance rota-1-rot-6-b6-11-1 (point p))
                 (:instance rota-inv-b3-0-n-f (p p))
                 (:instance ROTA-INV-B3-0-N-F-1-SUFF
                            (point p)
                            (p (M-* (ROT-6)
                                    (ROTA-1-ROT-6-B6-11-1-WITNESS P))))
                 (:instance b6-11 (p (ROTA-1-ROT-6-B6-11-1-WITNESS P)))
                 (:instance rot*b3-0-set=>b3-0
                            (rot (rot-6))
                            (p (ROTA-1-ROT-6-B6-11-1-WITNESS P)))
                 (:instance b3-0-set-a6 (p (ROTA-1-ROT-6-B6-11-1-WITNESS P)))
                 (:instance b3-0-n-f (p (M-* (ROT-6)
                                             (ROTA-1-ROT-6-B6-11-1-WITNESS P))))
                 (:instance rot-6-inv*f (point (ROTA-1-ROT-6-B6-11-1-WITNESS P)))
                 (:instance rota-1-rot-3-b3-01-or-11=>2
                            (rot (rot-6))
                            (p1 (ROT-6-INV*F-WITNESS (ROTA-1-ROT-6-B6-11-1-WITNESS P)))
                            (p2 (ROTA-1-ROT-6-B6-11-1-WITNESS P)))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance rot-6)
                 (:instance b3-0-r-1-a-inv-r-b3-0-a6-iff-b3-0-r-1-a-1-r-a6-1
                            (m2 (a-inv-rotation (acl2-sqrt 2)))
                            (m1 (ROTATION-3D
                                 (- (EXISTS-IN-INTERVAL-BUT-NOT-IN-ANGLE-SEQUENCE-WITNESS 0 (* 2 (ACL2-PI))))
                                 (POINT-ON-S2-NOT-D)))
                            (m3 (ROTATION-3D
                                 (EXISTS-IN-INTERVAL-BUT-NOT-IN-ANGLE-SEQUENCE-WITNESS 0 (* 2 (ACL2-PI)))
                                 (POINT-ON-S2-NOT-D))))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance r3-rotationp-r-theta
                            (angle (- (EXISTS-IN-INTERVAL-BUT-NOT-IN-ANGLE-SEQUENCE-WITNESS 0 (* 2 (ACL2-PI))))))
                 (:instance r3-rotationp-r-theta
                            (angle (EXISTS-IN-INTERVAL-BUT-NOT-IN-ANGLE-SEQUENCE-WITNESS 0 (* 2 (ACL2-PI)))))
                 (:instance witness-not-in-angle-sequence)
                 (:instance rota-1-rot-6-b6-01 (p p))
                 (:instance rota-1-rot-6-b6-01-1 (point p))
                 (:instance ROTA-INV-B3-0-N-F-1-SUFF
                            (point p)
                            (p (M-* (ROT-6)
                                    (ROTA-1-ROT-6-B6-01-1-WITNESS P))))
                 (:instance b6-01 (p (ROTA-1-ROT-6-B6-01-1-WITNESS P)))
                 (:instance rot*b3-0-set=>b3-0
                            (rot (rot-6))
                            (p (ROTA-1-ROT-6-B6-01-1-WITNESS P)))
                 (:instance b3-0-set-a6 (p (ROTA-1-ROT-6-B6-01-1-WITNESS P)))
                 (:instance b3-0-n-f (p (M-* (ROT-6)
                                             (ROTA-1-ROT-6-B6-01-1-WITNESS P))))
                 (:instance rot-6-inv*f (point (ROTA-1-ROT-6-B6-01-1-WITNESS P)))
                 (:instance rota-1-rot-3-b3-01-or-11=>2
                            (rot (rot-6))
                            (p1 (ROT-6-INV*F-WITNESS (ROTA-1-ROT-6-B6-01-1-WITNESS P)))
                            (p2 (ROTA-1-ROT-6-B6-01-1-WITNESS P)))
                 )
           :in-theory nil
           )
          ("Subgoal 2"
           :use ((:instance rota-1-rot-7-b7-11 (p p))
                 (:instance rota-1-rot-7-b7-11-1 (point p))
                 (:instance rota-inv-b3-0-n-f (p p))
                 (:instance ROTA-INV-B3-0-N-F-1-SUFF
                            (point p)
                            (p (M-* (ROT-7)
                                    (ROTA-1-ROT-7-B7-11-1-WITNESS P))))
                 (:instance b7-11 (p (ROTA-1-ROT-7-B7-11-1-WITNESS P)))
                 (:instance rot*b3-0-set=>b3-0
                            (rot (rot-7))
                            (p (ROTA-1-ROT-7-B7-11-1-WITNESS P)))
                 (:instance b3-0-set-a7 (p (ROTA-1-ROT-7-B7-11-1-WITNESS P)))
                 (:instance b3-0-n-f (p (M-* (ROT-7)
                                             (ROTA-1-ROT-7-B7-11-1-WITNESS P))))
                 (:instance rot-7-inv*f (point (ROTA-1-ROT-7-B7-11-1-WITNESS P)))
                 (:instance rota-1-rot-3-b3-01-or-11=>2
                            (rot (rot-7))
                            (p1 (ROT-7-INV*F-WITNESS (ROTA-1-ROT-7-B7-11-1-WITNESS P)))
                            (p2 (ROTA-1-ROT-7-B7-11-1-WITNESS P)))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance rot-7)
                 (:instance rota-1-rot-7-b7-01 (p p))
                 (:instance rota-1-rot-7-b7-01-1 (point p))
                 (:instance ROTA-INV-B3-0-N-F-1-SUFF
                            (point p)
                            (p (M-* (ROT-7)
                                    (ROTA-1-ROT-7-B7-01-1-WITNESS P))))
                 (:instance b7-01 (p (ROTA-1-ROT-7-B7-01-1-WITNESS P)))
                 (:instance rot*b3-0-set=>b3-0
                            (rot (rot-7))
                            (p (ROTA-1-ROT-7-B7-01-1-WITNESS P)))
                 (:instance b3-0-set-a7 (p (ROTA-1-ROT-7-B7-01-1-WITNESS P)))
                 (:instance b3-0-n-f (p (M-* (ROT-7)
                                             (ROTA-1-ROT-7-B7-01-1-WITNESS P))))
                 (:instance rot-7-inv*f (point (ROTA-1-ROT-7-B7-01-1-WITNESS P)))
                 (:instance rota-1-rot-3-b3-01-or-11=>2
                            (rot (rot-7))
                            (p1 (ROT-7-INV*F-WITNESS (ROTA-1-ROT-7-B7-01-1-WITNESS P)))
                            (p2 (ROTA-1-ROT-7-B7-01-1-WITNESS P)))
                 )
           :in-theory nil
           )
          ("Subgoal 1"
           :use ((:instance rota-1-rot-8-b8-11 (p p))
                 (:instance rota-1-rot-8-b8-11-1 (point p))
                 (:instance rota-inv-b3-0-n-f (p p))
                 (:instance ROTA-INV-B3-0-N-F-1-SUFF
                            (point p)
                            (p (M-* (ROT-8)
                                    (ROTA-1-ROT-8-B8-11-1-WITNESS P))))
                 (:instance b8-11 (p (ROTA-1-ROT-8-B8-11-1-WITNESS P)))
                 (:instance rot*b3-0-set=>b3-0
                            (rot (rot-8))
                            (p (ROTA-1-ROT-8-B8-11-1-WITNESS P)))
                 (:instance b3-0-set-a8 (p (ROTA-1-ROT-8-B8-11-1-WITNESS P)))
                 (:instance b3-0-n-f (p (M-* (ROT-8)
                                             (ROTA-1-ROT-8-B8-11-1-WITNESS P))))
                 (:instance rot-8-inv*f (point (ROTA-1-ROT-8-B8-11-1-WITNESS P)))
                 (:instance rota-1-rot-3-b3-01-or-11=>2
                            (rot (rot-8))
                            (p1 (ROT-8-INV*F-WITNESS (ROTA-1-ROT-8-B8-11-1-WITNESS P)))
                            (p2 (ROTA-1-ROT-8-B8-11-1-WITNESS P)))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance rot-8)
                 (:instance rota-1-rot-8-b8-01 (p p))
                 (:instance rota-1-rot-8-b8-01-1 (point p))
                 (:instance ROTA-INV-B3-0-N-F-1-SUFF
                            (point p)
                            (p (M-* (ROT-8)
                                    (ROTA-1-ROT-8-B8-01-1-WITNESS P))))
                 (:instance b8-01 (p (ROTA-1-ROT-8-B8-01-1-WITNESS P)))
                 (:instance rot*b3-0-set=>b3-0
                            (rot (rot-8))
                            (p (ROTA-1-ROT-8-B8-01-1-WITNESS P)))
                 (:instance b3-0-set-a8 (p (ROTA-1-ROT-8-B8-01-1-WITNESS P)))
                 (:instance b3-0-n-f (p (M-* (ROT-8)
                                             (ROTA-1-ROT-8-B8-01-1-WITNESS P))))
                 (:instance rot-8-inv*f (point (ROTA-1-ROT-8-B8-01-1-WITNESS P)))
                 (:instance rota-1-rot-3-b3-01-or-11=>2
                            (rot (rot-8))
                            (p1 (ROT-8-INV*F-WITNESS (ROTA-1-ROT-8-B8-01-1-WITNESS P)))
                            (p2 (ROTA-1-ROT-8-B8-01-1-WITNESS P)))
                 )
           :in-theory nil
           )
          ))

(defun-sk rot-3-inv*b3-f (point)
  (exists p
          (and (b3-f p)
               (m-= (m-* (r3-m-inverse (rot-3)) p) point))))

(defun b3-00 (p)
  (and (b3-0-set-a3 p)
       (b3-f p)
       (rot-3-inv*b3-f p)))

(defun b3-10 (p)
  (and (b3-0-set-a3 p)
       (set-f-p p)
       (rot-3-inv*b3-f p)))

(defun-sk rot-3-b3-00-1 (point)
  (exists p
          (and (b3-00 p)
               (m-= (m-* (rot-3) p) point))))

(defun rot-3-b3-00 (p)
  (and (point-in-r3 p)
       (rot-3-b3-00-1 p)))

(defun-sk rot-3-b3-10-1 (point)
  (exists p
          (and (b3-10 p)
               (m-= (m-* (rot-3) p) point))))

(defun rot-3-b3-10 (p)
  (and (point-in-r3 p)
       (rot-3-b3-10-1 p)))

(defun-sk rot-4-inv*b3-f (point)
  (exists p
          (and (b3-f p)
               (m-= (m-* (r3-m-inverse (rot-4)) p) point))))

(defun b4-00 (p)
  (and (b3-0-set-a4 p)
       (b3-f p)
       (rot-4-inv*b3-f p)))

(defun b4-10 (p)
  (and (b3-0-set-a4 p)
       (set-f-p p)
       (rot-4-inv*b3-f p)))

(defun-sk rot-4-b4-00-1 (point)
  (exists p
          (and (b4-00 p)
               (m-= (m-* (rot-4) p) point))))

(defun rot-4-b4-00 (p)
  (and (point-in-r3 p)
       (rot-4-b4-00-1 p)))

(defun-sk rot-4-b4-10-1 (point)
  (exists p
          (and (b4-10 p)
               (m-= (m-* (rot-4) p) point))))

(defun rot-4-b4-10 (p)
  (and (point-in-r3 p)
       (rot-4-b4-10-1 p)))

(defun-sk rot-5-inv*b3-f (point)
  (exists p
          (and (b3-f p)
               (m-= (m-* (r3-m-inverse (rot-5)) p) point))))

(defun b5-00 (p)
  (and (b3-0-set-a5 p)
       (b3-f p)
       (rot-5-inv*b3-f p)))

(defun b5-10 (p)
  (and (b3-0-set-a5 p)
       (set-f-p p)
       (rot-5-inv*b3-f p)))

(defun-sk rot-5-b5-00-1 (point)
  (exists p
          (and (b5-00 p)
               (m-= (m-* (rot-5) p) point))))

(defun rot-5-b5-00 (p)
  (and (point-in-r3 p)
       (rot-5-b5-00-1 p)))

(defun-sk rot-5-b5-10-1 (point)
  (exists p
          (and (b5-10 p)
               (m-= (m-* (rot-5) p) point))))

(defun rot-5-b5-10 (p)
  (and (point-in-r3 p)
       (rot-5-b5-10-1 p)))

(defun-sk rot-6-inv*b3-f (point)
  (exists p
          (and (b3-f p)
               (m-= (m-* (r3-m-inverse (rot-6)) p) point))))

(defun b6-00 (p)
  (and (b3-0-set-a6 p)
       (b3-f p)
       (rot-6-inv*b3-f p)))

(defun b6-10 (p)
  (and (b3-0-set-a6 p)
       (set-f-p p)
       (rot-6-inv*b3-f p)))

(defun-sk rot-6-b6-00-1 (point)
  (exists p
          (and (b6-00 p)
               (m-= (m-* (rot-6) p) point))))

(defun rot-6-b6-00 (p)
  (and (point-in-r3 p)
       (rot-6-b6-00-1 p)))

(defun-sk rot-6-b6-10-1 (point)
  (exists p
          (and (b6-10 p)
               (m-= (m-* (rot-6) p) point))))

(defun rot-6-b6-10 (p)
  (and (point-in-r3 p)
       (rot-6-b6-10-1 p)))

(defun-sk rot-7-inv*b3-f (point)
  (exists p
          (and (b3-f p)
               (m-= (m-* (r3-m-inverse (rot-7)) p) point))))

(defun b7-00 (p)
  (and (b3-0-set-a7 p)
       (b3-f p)
       (rot-7-inv*b3-f p)))

(defun b7-10 (p)
  (and (b3-0-set-a7 p)
       (set-f-p p)
       (rot-7-inv*b3-f p)))

(defun-sk rot-7-b7-00-1 (point)
  (exists p
          (and (b7-00 p)
               (m-= (m-* (rot-7) p) point))))

(defun rot-7-b7-00 (p)
  (and (point-in-r3 p)
       (rot-7-b7-00-1 p)))

(defun-sk rot-7-b7-10-1 (point)
  (exists p
          (and (b7-10 p)
               (m-= (m-* (rot-7) p) point))))

(defun rot-7-b7-10 (p)
  (and (point-in-r3 p)
       (rot-7-b7-10-1 p)))

(defun-sk rot-8-inv*b3-f (point)
  (exists p
          (and (b3-f p)
               (m-= (m-* (r3-m-inverse (rot-8)) p) point))))

(defun b8-00 (p)
  (and (b3-0-set-a8 p)
       (b3-f p)
       (rot-8-inv*b3-f p)))

(defun b8-10 (p)
  (and (b3-0-set-a8 p)
       (set-f-p p)
       (rot-8-inv*b3-f p)))

(defun-sk rot-8-b8-00-1 (point)
  (exists p
          (and (b8-00 p)
               (m-= (m-* (rot-8) p) point))))

(defun rot-8-b8-00 (p)
  (and (point-in-r3 p)
       (rot-8-b8-00-1 p)))

(defun-sk rot-8-b8-10-1 (point)
  (exists p
          (and (b8-10 p)
               (m-= (m-* (rot-8) p) point))))

(defun rot-8-b8-10 (p)
  (and (point-in-r3 p)
       (rot-8-b8-10-1 p)))

(defthmd a3-a8-b3-0-n-b3-f=>
  (implies (b3-0-n-b3-f p)
           (or (rot-3-b3-00 p)
               (rot-3-b3-10 p)
               (rot-4-b4-00 p)
               (rot-4-b4-10 p)
               (rot-5-b5-00 p)
               (rot-5-b5-10 p)
               (rot-6-b6-00 p)
               (rot-6-b6-10 p)
               (rot-7-b7-00 p)
               (rot-7-b7-10 p)
               (rot-8-b8-00 p)
               (rot-8-b8-10 p)))
  :hints (("Goal"
           :cases ((b3-0-a-inv-b3-0-set-a3 p)
                   (b3-0-a-inv-r-b3-0-set-a4 p)
                   (B3-0-R-1-A-INV-B3-0-SET-A5 P)
                   (B3-0-R-1-A-INV-R-B3-0-SET-A6 P)
                   (B3-0-SET-A7 P)
                   (B3-0-SET-A8 P))
           :use ((:instance B3-0-N-b3-F (p p))
                 (:instance b3-0-iff-a3-to-a8 (p p))
                 )
           :in-theory nil
           )
          ("Subgoal 6"
           :use ((:instance b3-0-a-inv-b3-0-set-a3 (p p))
                 (:instance b3-0-a-inv-b3-0-set-a3-1 (p p))
                 (:instance rot-3-b3-10 (p p))
                 (:instance rot-3-b3-10-1-suff (point p) (p (B3-0-A-INV-B3-0-SET-A3-1-WITNESS P)))
                 (:instance b3-10 (p (B3-0-A-INV-B3-0-SET-A3-1-WITNESS P)))
                 (:instance b3-f (p (B3-0-A-INV-B3-0-SET-A3-1-WITNESS P)))
                 (:instance rot-3-b3-00 (p p))
                 (:instance rot-3-b3-00-1-suff (point p) (p (B3-0-A-INV-B3-0-SET-A3-1-WITNESS P)))
                 (:instance b3-00 (p (B3-0-A-INV-B3-0-SET-A3-1-WITNESS P)))
                 (:instance rot-3)
                 (:instance ROT-3-INV*B3-F-SUFF (p p) (point (B3-0-A-INV-B3-0-SET-A3-1-WITNESS P)))
                 (:instance a3-a8-rot-a-inv-b3-0-nf=>1
                            (m1 (ROT-3))
                            (m2 (B3-0-A-INV-B3-0-SET-A3-1-WITNESS P))
                            (m3 p)
                            (m4 (r3-m-inverse (rot-3)))
                            (m5 (id-rotation))
                            (m6 (B3-0-A-INV-B3-0-SET-A3-1-WITNESS P)))
                 (:instance m-*point-id=point (p1 (B3-0-A-INV-B3-0-SET-A3-1-WITNESS P)))
                 (:instance b3-0-set-a3 (p (B3-0-A-INV-B3-0-SET-A3-1-WITNESS P)))
                 (:instance m-*-m-inverse-m
                            (m (rot-3)))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance r3-rotationp (m (a-inv-rotation (acl2-sqrt 2))))
                 (:instance b3 (p (B3-0-A-INV-B3-0-SET-A3-1-WITNESS P)))
                 )
           :in-theory nil
           )
          ("Subgoal 5"
           :use ((:instance B3-0-A-INV-R-B3-0-SET-A4 (p p))
                 (:instance B3-0-A-INV-R-B3-0-SET-A4-1 (p p))
                 (:instance rot-4-b4-10 (p p))
                 (:instance rot-4-b4-10-1-suff (point p) (p (B3-0-A-INV-R-B3-0-SET-A4-1-WITNESS P)))
                 (:instance b4-10 (p (B3-0-A-INV-R-B3-0-SET-A4-1-WITNESS P)))
                 (:instance b3-f (p (B3-0-A-INV-R-B3-0-SET-A4-1-WITNESS P)))
                 (:instance rot-4-b4-00 (p p))
                 (:instance rot-4-b4-00-1-suff (point p) (p (B3-0-A-INV-R-B3-0-SET-A4-1-WITNESS P)))
                 (:instance b4-00 (p (B3-0-A-INV-R-B3-0-SET-A4-1-WITNESS P)))
                 (:instance rot-4)
                 (:instance ROT-4-INV*B3-F-SUFF (p p) (point (B3-0-A-INV-R-B3-0-SET-A4-1-WITNESS P)))
                 (:instance a3-a8-rot-a-inv-b3-0-nf=>1
                            (m1 (ROT-4))
                            (m2 (B3-0-A-INV-R-B3-0-SET-A4-1-WITNESS P))
                            (m3 p)
                            (m4 (r3-m-inverse (rot-4)))
                            (m5 (id-rotation))
                            (m6 (B3-0-A-INV-R-B3-0-SET-A4-1-WITNESS P)))
                 (:instance associativity-of-m-*
                            (m1 (A-INV-ROTATION (ACL2-SQRT 2)))
                            (m2 (ROTATION-3D
                                 (EXISTS-IN-INTERVAL-BUT-NOT-IN-ANGLE-SEQUENCE-WITNESS 0 (* 2 (ACL2-PI)))
                                 (POINT-ON-S2-NOT-D)))
                            (m3 (B3-0-A-INV-R-B3-0-SET-A4-1-WITNESS P)))
                 (:instance m-*point-id=point (p1 (B3-0-A-INV-R-B3-0-SET-A4-1-WITNESS P)))
                 (:instance b3-0-set-a4 (p (B3-0-A-INV-R-B3-0-SET-A4-1-WITNESS P)))
                 (:instance m-*-m-inverse-m
                            (m (rot-4)))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance r3-rotationp-r-theta
                            (angle (EXISTS-IN-INTERVAL-BUT-NOT-IN-ANGLE-SEQUENCE-WITNESS 0 (* 2 (ACL2-PI)))))
                 (:instance rot*rot-is-rot
                            (m1 (a-inv-rotation (acl2-sqrt 2)))
                            (m2 (ROTATION-3D
                                 (EXISTS-IN-INTERVAL-BUT-NOT-IN-ANGLE-SEQUENCE-WITNESS 0 (* 2 (ACL2-PI)))
                                 (POINT-ON-S2-NOT-D))))
                 (:instance witness-not-in-angle-sequence)
                 (:instance r3-rotationp (m (rot-4)))
                 (:instance b3 (p (B3-0-A-INV-R-B3-0-SET-A4-1-WITNESS P)))
                 )
           :in-theory nil
           )
          ("Subgoal 4"
           :use ((:instance B3-0-R-1-A-INV-B3-0-SET-A5 (p p))
                 (:instance B3-0-R-1-A-INV-B3-0-SET-A5-1 (p p))
                 (:instance rot-5-b5-10 (p p))
                 (:instance rot-5-b5-10-1-suff (point p) (p (B3-0-R-1-A-INV-B3-0-SET-A5-1-WITNESS P)))
                 (:instance b5-10 (p (B3-0-R-1-A-INV-B3-0-SET-A5-1-WITNESS P)))
                 (:instance b3-f (p (B3-0-R-1-A-INV-B3-0-SET-A5-1-WITNESS P)))
                 (:instance rot-5-b5-00 (p p))
                 (:instance rot-5-b5-00-1-suff (point p) (p (B3-0-R-1-A-INV-B3-0-SET-A5-1-WITNESS P)))
                 (:instance b5-00 (p (B3-0-R-1-A-INV-B3-0-SET-A5-1-WITNESS P)))
                 (:instance rot-5)
                 (:instance ROT-5-INV*B3-F-SUFF (p p) (point (B3-0-R-1-A-INV-B3-0-SET-A5-1-WITNESS P)))
                 (:instance a3-a8-rot-a-inv-b3-0-nf=>1
                            (m1 (ROT-5))
                            (m2 (B3-0-R-1-A-INV-B3-0-SET-A5-1-WITNESS P))
                            (m3 p)
                            (m4 (r3-m-inverse (rot-5)))
                            (m5 (id-rotation))
                            (m6 (B3-0-R-1-A-INV-B3-0-SET-A5-1-WITNESS P)))
                 (:instance associativity-of-m-*
                            (m2 (A-INV-ROTATION (ACL2-SQRT 2)))
                            (m1 (ROTATION-3D
                                 (- (EXISTS-IN-INTERVAL-BUT-NOT-IN-ANGLE-SEQUENCE-WITNESS 0 (* 2 (ACL2-PI))))
                                 (POINT-ON-S2-NOT-D)))
                            (m3 (B3-0-R-1-A-INV-B3-0-SET-A5-1-WITNESS P)))
                 (:instance m-*point-id=point (p1 (B3-0-R-1-A-INV-B3-0-SET-A5-1-WITNESS P)))
                 (:instance b3-0-set-a5 (p (B3-0-R-1-A-INV-B3-0-SET-A5-1-WITNESS P)))
                 (:instance m-*-m-inverse-m
                            (m (rot-5)))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance r3-rotationp-r-theta
                            (angle (- (EXISTS-IN-INTERVAL-BUT-NOT-IN-ANGLE-SEQUENCE-WITNESS 0 (* 2 (ACL2-PI))))))
                 (:instance rot*rot-is-rot
                            (m2 (a-inv-rotation (acl2-sqrt 2)))
                            (m1 (ROTATION-3D
                                 (- (EXISTS-IN-INTERVAL-BUT-NOT-IN-ANGLE-SEQUENCE-WITNESS 0 (* 2 (ACL2-PI))))
                                 (POINT-ON-S2-NOT-D))))
                 (:instance witness-not-in-angle-sequence)
                 (:instance r3-rotationp (m (rot-5)))
                 (:instance b3 (p (B3-0-R-1-A-INV-B3-0-SET-A5-1-WITNESS P)))
                 )
           :in-theory nil
           )
          ("Subgoal 3"
           :use ((:instance B3-0-R-1-A-INV-R-B3-0-SET-A6 (p p))
                 (:instance B3-0-R-1-A-INV-R-B3-0-SET-A6-1 (p p))
                 (:instance rot-6-b6-10 (p p))
                 (:instance rot-6-b6-10-1-suff (point p) (p (B3-0-R-1-A-INV-R-B3-0-SET-A6-1-WITNESS P)))
                 (:instance b6-10 (p (B3-0-R-1-A-INV-R-B3-0-SET-A6-1-WITNESS P)))
                 (:instance b3-f (p (B3-0-R-1-A-INV-R-B3-0-SET-A6-1-WITNESS P)))
                 (:instance rot-6-b6-00 (p p))
                 (:instance rot-6-b6-00-1-suff (point p) (p (B3-0-R-1-A-INV-R-B3-0-SET-A6-1-WITNESS P)))
                 (:instance b6-00 (p (B3-0-R-1-A-INV-R-B3-0-SET-A6-1-WITNESS P)))
                 (:instance rot-6)
                 (:instance ROT-6-INV*B3-F-SUFF (p p) (point (B3-0-R-1-A-INV-R-B3-0-SET-A6-1-WITNESS P)))
                 (:instance a3-a8-rot-a-inv-b3-0-nf=>1
                            (m1 (ROT-6))
                            (m2 (B3-0-R-1-A-INV-R-B3-0-SET-A6-1-WITNESS P))
                            (m3 p)
                            (m4 (r3-m-inverse (rot-6)))
                            (m5 (id-rotation))
                            (m6 (B3-0-R-1-A-INV-R-B3-0-SET-A6-1-WITNESS P)))
                 (:instance a3-a8-rot-a-inv-b3-0-nf=>sub-3
                            (m1 (ROTATION-3D
                                 (- (EXISTS-IN-INTERVAL-BUT-NOT-IN-ANGLE-SEQUENCE-WITNESS 0 (* 2 (ACL2-PI))))
                                            (POINT-ON-S2-NOT-D)))
                            (m2 (A-INV-ROTATION (ACL2-SQRT 2)))
                            (m3 (ROTATION-3D
                                 (EXISTS-IN-INTERVAL-BUT-NOT-IN-ANGLE-SEQUENCE-WITNESS 0 (* 2 (ACL2-PI)))
                                 (POINT-ON-S2-NOT-D)))
                            (m4 (B3-0-R-1-A-INV-R-B3-0-SET-A6-1-WITNESS P)))
                 (:instance m-*point-id=point (p1 (B3-0-R-1-A-INV-R-B3-0-SET-A6-1-WITNESS P)))
                 (:instance b3-0-set-a6 (p (B3-0-R-1-A-INV-R-B3-0-SET-A6-1-WITNESS P)))
                 (:instance m-*-m-inverse-m
                            (m (rot-6)))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance r3-rotationp-r-theta
                            (angle (- (EXISTS-IN-INTERVAL-BUT-NOT-IN-ANGLE-SEQUENCE-WITNESS 0 (* 2 (ACL2-PI))))))
                 (:instance r3-rotationp-r-theta
                            (angle (EXISTS-IN-INTERVAL-BUT-NOT-IN-ANGLE-SEQUENCE-WITNESS 0 (* 2 (ACL2-PI)))))
                 (:instance b3-0-r-1-a-inv-r-b3-0-a6-iff-b3-0-r-1-a-1-r-a6-1
                            (m2 (a-inv-rotation (acl2-sqrt 2)))
                            (m1 (ROTATION-3D
                                 (- (EXISTS-IN-INTERVAL-BUT-NOT-IN-ANGLE-SEQUENCE-WITNESS 0 (* 2 (ACL2-PI))))
                                 (POINT-ON-S2-NOT-D)))
                            (m3 (ROTATION-3D
                                 (EXISTS-IN-INTERVAL-BUT-NOT-IN-ANGLE-SEQUENCE-WITNESS 0 (* 2 (ACL2-PI)))
                                 (POINT-ON-S2-NOT-D))))
                 (:instance witness-not-in-angle-sequence)
                 (:instance r3-rotationp (m (rot-6)))
                 (:instance b3 (p (B3-0-R-1-A-INV-R-B3-0-SET-A6-1-WITNESS P)))
                 )
           :in-theory nil
           )
          ("Subgoal 2"
           :use ((:instance rot-7-b7-10 (p p))
                 (:instance rot-7-b7-10-1-suff (point p) (p p))
                 (:instance b7-10 (p p))
                 (:instance b3-f (p p))
                 (:instance b3-0-set-a7 (p p))
                 (:instance rot-7-b7-00 (p p))
                 (:instance rot-7-b7-00-1-suff (point p) (p p))
                 (:instance b7-00 (p p))
                 (:instance rot-7)
                 (:instance ROT-7-INV*B3-F-SUFF (p p) (point p))
                 (:instance a3-a8-rot-a-inv-b3-0-nf=>1
                            (m1 (ROT-7))
                            (m2 p)
                            (m3 p)
                            (m4 (r3-m-inverse (rot-7)))
                            (m5 (id-rotation))
                            (m6 p))
                 (:instance m-*point-id=point (p1 p))
                 (:instance m-*-m-inverse-m
                            (m (rot-7)))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance r3-rotationp (m (id-rotation)))
                 )
           :in-theory nil
           )
          ("Subgoal 1"
           :use ((:instance rot-8-b8-10 (p p))
                 (:instance rot-8-b8-10-1-suff (point p) (p p))
                 (:instance b8-10 (p p))
                 (:instance b3-f (p p))
                 (:instance b3-0-set-a8 (p p))
                 (:instance rot-8-b8-00 (p p))
                 (:instance rot-8-b8-00-1-suff (point p) (p p))
                 (:instance b8-00 (p p))
                 (:instance rot-8)
                 (:instance ROT-8-INV*B3-F-SUFF (p p) (point p))
                 (:instance a3-a8-rot-a-inv-b3-0-nf=>1
                            (m1 (ROT-8))
                            (m2 p)
                            (m3 p)
                            (m4 (r3-m-inverse (rot-8)))
                            (m5 (id-rotation))
                            (m6 p))
                 (:instance m-*point-id=point (p1 p))
                 (:instance m-*-m-inverse-m
                            (m (rot-8)))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance r3-rotationp (m (id-rotation)))
                 )
           :in-theory nil
           )
          ))

(defthmd rot-3-8-b-3-8-01-or-11=>1-1
  (implies (and (m-= (m-* m1 m2) m3)
                (m-= (m-* m4 m5) m2))
           (m-= (m-* (m-* m1 m4) m5) m3)))

(defthmd rot-3-8-b-3-8-01-or-11=>1-2
  (implies (and (m-= (m-* m1 m2) m3)
                (m-= (m-* m1 m2 m4) m5)
                (m-= (m-* m3 m4) m6))
           (m-= m6 m5)))

(defthmd rot-3-8-b-3-8-01-or-11=>1
  (implies (and (r3-rotationp rot)
                (set-f-p p)
                (point-in-r3 wit-wit)
                (m-= (m-* rot wit) p)
                (m-= (m-* (r3-m-inverse rot) wit-wit) wit))
           (set-f-p wit-wit))
  :hints (("Goal"
           :use ((:instance associativity-of-m-*-1
                            (m1 rot)
                            (m2 (r3-m-inverse rot))
                            (m3 wit-wit))
                 (:instance m-*-m-m-inverse
                            (m rot))
                 (:instance r3-rotationp (m rot))
                 (:instance m-*point-id=point
                            (p1 wit-wit))
                 (:instance rota-1-rota-f-iff-set-f-p-2-1
                            (p2 wit-wit)
                            (p1 p))
                 (:instance set-f-p (point wit-wit))
                 (:instance rot-3-8-b-3-8-01-or-11=>1-1
                            (m1 rot)
                            (m2 wit)
                            (m3 p)
                            (m4 (r3-m-inverse rot))
                            (m5 wit-wit))
                 (:instance rot-3-8-b-3-8-01-or-11=>1-2
                            (m1 rot)
                            (m2 (r3-m-inverse rot))
                            (m3 (id-rotation))
                            (m4 wit-wit)
                            (m5 p)
                            (m6 wit-wit))
                 )
           :in-theory nil

           )))

(defthmd rot-3-8-b-3-8-01-or-11=>
  (implies (or (rot-3-b3-00 p)
               (rot-3-b3-10 p)
               (rot-4-b4-00 p)
               (rot-4-b4-10 p)
               (rot-5-b5-00 p)
               (rot-5-b5-10 p)
               (rot-6-b6-00 p)
               (rot-6-b6-10 p)
               (rot-7-b7-00 p)
               (rot-7-b7-10 p)
               (rot-8-b8-00 p)
               (rot-8-b8-10 p))
           (b3-0-n-b3-f p))
  :hints (("Goal"
           :cases ((rot-3-b3-00 p)
                   (rot-3-b3-10 p)
                   (rot-4-b4-00 p)
                   (rot-4-b4-10 p)
                   (rot-5-b5-00 p)
                   (rot-5-b5-10 p)
                   (rot-6-b6-00 p)
                   (rot-6-b6-10 p)
                   (rot-7-b7-00 p)
                   (rot-7-b7-10 p)
                   (rot-8-b8-00 p)
                   (rot-8-b8-10 p)
                   )
           :in-theory nil
           )
          ("Subgoal 12"
           :use ((:instance rot-3-b3-00 (p p))
                 (:instance rot-3-b3-00-1 (point p))
                 (:instance b3-00 (p (ROT-3-B3-00-1-WITNESS P)))
                 (:instance rot-3-inv*b3-f (point (ROT-3-B3-00-1-WITNESS P)))
                 (:instance b3-0-n-b3-f (p p))
                 (:instance rot*b3-0-set=>b3-0
                            (p (ROT-3-B3-00-1-WITNESS P))
                            (rot (rot-3)))
                 (:instance rot-3)
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance b3-0 (p (M-* (ROT-3) (ROT-3-B3-00-1-WITNESS P))))
                 (:instance b3-0 (p p))
                 (:instance cal-radius-p1=p2
                            (p1 (M-* (ROT-3) (ROT-3-B3-00-1-WITNESS P)))
                            (p2 p))
                 (:instance b3-f (p p))
                 (:instance b3 (p p))
                 (:instance rot-3-8-b-3-8-01-or-11=>1
                            (rot (rot-3))
                            (wit (ROT-3-B3-00-1-WITNESS P))
                            (p p)
                            (wit-wit (ROT-3-INV*B3-F-WITNESS (ROT-3-B3-00-1-WITNESS P))))
                 (:instance b3 (p (ROT-3-INV*B3-F-WITNESS (ROT-3-B3-00-1-WITNESS P))))
                 (:instance b3-f (p (ROT-3-INV*B3-F-WITNESS (ROT-3-B3-00-1-WITNESS P))))
                 )
           :in-theory nil
           )
          ("Subgoal 11"
           :use ((:instance rot-3-b3-10 (p p))
                 (:instance rot-3-b3-10-1 (point p))
                 (:instance b3-10 (p (ROT-3-B3-10-1-WITNESS P)))
                 (:instance rot-3-inv*b3-f (point (ROT-3-B3-10-1-WITNESS P)))
                 (:instance b3-0-n-b3-f (p p))
                 (:instance rot*b3-0-set=>b3-0
                            (p (ROT-3-B3-10-1-WITNESS P))
                            (rot (rot-3)))
                 (:instance rot-3)
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance b3-0 (p (M-* (ROT-3) (ROT-3-B3-10-1-WITNESS P))))
                 (:instance b3-0 (p p))
                 (:instance cal-radius-p1=p2
                            (p1 (M-* (ROT-3) (ROT-3-B3-10-1-WITNESS P)))
                            (p2 p))
                 (:instance b3-f (p p))
                 (:instance b3 (p p))
                 (:instance rot-3-8-b-3-8-01-or-11=>1
                            (rot (rot-3))
                            (wit (ROT-3-B3-10-1-WITNESS P))
                            (p p)
                            (wit-wit (ROT-3-INV*B3-F-WITNESS (ROT-3-B3-10-1-WITNESS P))))
                 (:instance b3 (p (ROT-3-INV*B3-F-WITNESS (ROT-3-B3-10-1-WITNESS P))))
                 (:instance b3-f (p (ROT-3-INV*B3-F-WITNESS (ROT-3-B3-10-1-WITNESS P))))
                 )
           :in-theory nil
           )
          ("Subgoal 10"
           :use ((:instance rot-4-b4-00 (p p))
                 (:instance rot-4-b4-00-1 (point p))
                 (:instance b4-00 (p (ROT-4-B4-00-1-WITNESS P)))
                 (:instance rot-4-inv*b3-f (point (ROT-4-B4-00-1-WITNESS P)))
                 (:instance b3-0-n-b3-f (p p))
                 (:instance rot*b3-0-set=>b3-0
                            (p (ROT-4-B4-00-1-WITNESS P))
                            (rot (rot-4)))
                 (:instance rot-4)
                 (:instance rot*rot-is-rot
                            (m1 (a-inv-rotation (acl2-sqrt 2)))
                            (m2 (ROTATION-3D
                                 (EXISTS-IN-INTERVAL-BUT-NOT-IN-ANGLE-SEQUENCE-WITNESS 0 (* 2 (ACL2-PI)))
                                 (POINT-ON-S2-NOT-D))))
                 (:instance r3-rotationp-r-theta
                            (angle (EXISTS-IN-INTERVAL-BUT-NOT-IN-ANGLE-SEQUENCE-WITNESS 0 (* 2 (ACL2-PI)))))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance witness-not-in-angle-sequence)
                 (:instance b3-0 (p (M-* (ROT-4) (ROT-4-B4-00-1-WITNESS P))))
                 (:instance b3-0 (p p))
                 (:instance cal-radius-p1=p2
                            (p1 (M-* (ROT-4) (ROT-4-B4-00-1-WITNESS P)))
                            (p2 p))
                 (:instance b3-f (p p))
                 (:instance b3 (p p))
                 (:instance rot-3-8-b-3-8-01-or-11=>1
                            (rot (rot-4))
                            (wit (ROT-4-B4-00-1-WITNESS P))
                            (p p)
                            (wit-wit (ROT-4-INV*B3-F-WITNESS (ROT-4-B4-00-1-WITNESS P))))
                 (:instance b3 (p (ROT-4-INV*B3-F-WITNESS (ROT-4-B4-00-1-WITNESS P))))
                 (:instance b3-f (p (ROT-4-INV*B3-F-WITNESS (ROT-4-B4-00-1-WITNESS P))))
                 )
           :in-theory nil
           )
          ("Subgoal 9"
           :use ((:instance rot-4-b4-10 (p p))
                 (:instance rot-4-b4-10-1 (point p))
                 (:instance b4-10 (p (ROT-4-B4-10-1-WITNESS P)))
                 (:instance rot-4-inv*b3-f (point (ROT-4-B4-10-1-WITNESS P)))
                 (:instance b3-0-n-b3-f (p p))
                 (:instance rot*b3-0-set=>b3-0
                            (p (ROT-4-B4-10-1-WITNESS P))
                            (rot (rot-4)))
                 (:instance rot-4)
                 (:instance rot*rot-is-rot
                            (m1 (a-inv-rotation (acl2-sqrt 2)))
                            (m2 (ROTATION-3D
                                 (EXISTS-IN-INTERVAL-BUT-NOT-IN-ANGLE-SEQUENCE-WITNESS 0 (* 2 (ACL2-PI)))
                                 (POINT-ON-S2-NOT-D))))
                 (:instance r3-rotationp-r-theta
                            (angle (EXISTS-IN-INTERVAL-BUT-NOT-IN-ANGLE-SEQUENCE-WITNESS 0 (* 2 (ACL2-PI)))))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance witness-not-in-angle-sequence)
                 (:instance b3-0 (p (M-* (ROT-4) (ROT-4-B4-10-1-WITNESS P))))
                 (:instance b3-0 (p p))
                 (:instance cal-radius-p1=p2
                            (p1 (M-* (ROT-4) (ROT-4-B4-10-1-WITNESS P)))
                            (p2 p))
                 (:instance b3-f (p p))
                 (:instance b3 (p p))
                 (:instance rot-3-8-b-3-8-01-or-11=>1
                            (rot (rot-4))
                            (wit (ROT-4-B4-10-1-WITNESS P))
                            (p p)
                            (wit-wit (ROT-4-INV*B3-F-WITNESS (ROT-4-B4-10-1-WITNESS P))))
                 (:instance b3 (p (ROT-4-INV*B3-F-WITNESS (ROT-4-B4-10-1-WITNESS P))))
                 (:instance b3-f (p (ROT-4-INV*B3-F-WITNESS (ROT-4-B4-10-1-WITNESS P))))
                 )
           :in-theory nil
           )
          ("Subgoal 8"
           :use ((:instance rot-5-b5-00 (p p))
                 (:instance rot-5-b5-00-1 (point p))
                 (:instance b5-00 (p (ROT-5-B5-00-1-WITNESS P)))
                 (:instance rot-5-inv*b3-f (point (ROT-5-B5-00-1-WITNESS P)))
                 (:instance b3-0-n-b3-f (p p))
                 (:instance rot*b3-0-set=>b3-0
                            (p (ROT-5-B5-00-1-WITNESS P))
                            (rot (rot-5)))
                 (:instance rot-5)
                 (:instance rot*rot-is-rot
                            (m2 (a-inv-rotation (acl2-sqrt 2)))
                            (m1 (ROTATION-3D
                                 (- (EXISTS-IN-INTERVAL-BUT-NOT-IN-ANGLE-SEQUENCE-WITNESS 0 (* 2 (ACL2-PI))))
                                 (POINT-ON-S2-NOT-D))))
                 (:instance r3-rotationp-r-theta
                            (angle (- (EXISTS-IN-INTERVAL-BUT-NOT-IN-ANGLE-SEQUENCE-WITNESS 0 (* 2 (ACL2-PI))))))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance witness-not-in-angle-sequence)
                 (:instance b3-0 (p (M-* (ROT-5) (ROT-5-B5-00-1-WITNESS P))))
                 (:instance b3-0 (p p))
                 (:instance cal-radius-p1=p2
                            (p1 (M-* (ROT-5) (ROT-5-B5-00-1-WITNESS P)))
                            (p2 p))
                 (:instance b3-f (p p))
                 (:instance b3 (p p))
                 (:instance rot-3-8-b-3-8-01-or-11=>1
                            (rot (rot-5))
                            (wit (ROT-5-B5-00-1-WITNESS P))
                            (p p)
                            (wit-wit (ROT-5-INV*B3-F-WITNESS (ROT-5-B5-00-1-WITNESS P))))
                 (:instance b3 (p (ROT-5-INV*B3-F-WITNESS (ROT-5-B5-00-1-WITNESS P))))
                 (:instance b3-f (p (ROT-5-INV*B3-F-WITNESS (ROT-5-B5-00-1-WITNESS P))))
                 )
           :in-theory nil
           )
          ("Subgoal 7"
           :use ((:instance rot-5-b5-10 (p p))
                 (:instance rot-5-b5-10-1 (point p))
                 (:instance b5-10 (p (ROT-5-B5-10-1-WITNESS P)))
                 (:instance rot-5-inv*b3-f (point (ROT-5-B5-10-1-WITNESS P)))
                 (:instance b3-0-n-b3-f (p p))
                 (:instance rot*b3-0-set=>b3-0
                            (p (ROT-5-B5-10-1-WITNESS P))
                            (rot (rot-5)))
                 (:instance rot-5)
                 (:instance rot*rot-is-rot
                            (m2 (a-inv-rotation (acl2-sqrt 2)))
                            (m1 (ROTATION-3D
                                 (- (EXISTS-IN-INTERVAL-BUT-NOT-IN-ANGLE-SEQUENCE-WITNESS 0 (* 2 (ACL2-PI))))
                                 (POINT-ON-S2-NOT-D))))
                 (:instance r3-rotationp-r-theta
                            (angle (- (EXISTS-IN-INTERVAL-BUT-NOT-IN-ANGLE-SEQUENCE-WITNESS 0 (* 2 (ACL2-PI))))))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance witness-not-in-angle-sequence)
                 (:instance b3-0 (p (M-* (ROT-5) (ROT-5-B5-10-1-WITNESS P))))
                 (:instance b3-0 (p p))
                 (:instance cal-radius-p1=p2
                            (p1 (M-* (ROT-5) (ROT-5-B5-10-1-WITNESS P)))
                            (p2 p))
                 (:instance b3-f (p p))
                 (:instance b3 (p p))
                 (:instance rot-3-8-b-3-8-01-or-11=>1
                            (rot (rot-5))
                            (wit (ROT-5-B5-10-1-WITNESS P))
                            (p p)
                            (wit-wit (ROT-5-INV*B3-F-WITNESS (ROT-5-B5-10-1-WITNESS P))))
                 (:instance b3 (p (ROT-5-INV*B3-F-WITNESS (ROT-5-B5-10-1-WITNESS P))))
                 (:instance b3-f (p (ROT-5-INV*B3-F-WITNESS (ROT-5-B5-10-1-WITNESS P))))
                 )
           :in-theory nil
           )
          ("Subgoal 6"
           :use ((:instance rot-6-b6-00 (p p))
                 (:instance rot-6-b6-00-1 (point p))
                 (:instance b6-00 (p (ROT-6-B6-00-1-WITNESS P)))
                 (:instance rot-6-inv*b3-f (point (ROT-6-B6-00-1-WITNESS P)))
                 (:instance b3-0-n-b3-f (p p))
                 (:instance rot*b3-0-set=>b3-0
                            (p (ROT-6-B6-00-1-WITNESS P))
                            (rot (rot-6)))
                 (:instance rot-6)
                 (:instance b3-0-r-1-a-inv-r-b3-0-a6-iff-b3-0-r-1-a-1-r-a6-1
                            (m2 (a-inv-rotation (acl2-sqrt 2)))
                            (m1 (ROTATION-3D
                                 (- (EXISTS-IN-INTERVAL-BUT-NOT-IN-ANGLE-SEQUENCE-WITNESS 0 (* 2 (ACL2-PI))))
                                 (POINT-ON-S2-NOT-D)))
                            (m3 (ROTATION-3D
                                 (EXISTS-IN-INTERVAL-BUT-NOT-IN-ANGLE-SEQUENCE-WITNESS 0 (* 2 (ACL2-PI)))
                                 (POINT-ON-S2-NOT-D))))
                 (:instance r3-rotationp-r-theta
                            (angle (- (EXISTS-IN-INTERVAL-BUT-NOT-IN-ANGLE-SEQUENCE-WITNESS 0 (* 2 (ACL2-PI))))))
                 (:instance r3-rotationp-r-theta
                            (angle (EXISTS-IN-INTERVAL-BUT-NOT-IN-ANGLE-SEQUENCE-WITNESS 0 (* 2 (ACL2-PI)))))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance witness-not-in-angle-sequence)
                 (:instance b3-0 (p (M-* (ROT-6) (ROT-6-B6-00-1-WITNESS P))))
                 (:instance b3-0 (p p))
                 (:instance cal-radius-p1=p2
                            (p1 (M-* (ROT-6) (ROT-6-B6-00-1-WITNESS P)))
                            (p2 p))
                 (:instance b3-f (p p))
                 (:instance b3 (p p))
                 (:instance rot-3-8-b-3-8-01-or-11=>1
                            (rot (rot-6))
                            (wit (ROT-6-B6-00-1-WITNESS P))
                            (p p)
                            (wit-wit (ROT-6-INV*B3-F-WITNESS (ROT-6-B6-00-1-WITNESS P))))
                 (:instance b3 (p (ROT-6-INV*B3-F-WITNESS (ROT-6-B6-00-1-WITNESS P))))
                 (:instance b3-f (p (ROT-6-INV*B3-F-WITNESS (ROT-6-B6-00-1-WITNESS P))))
                 )
           :in-theory nil
           )
          ("Subgoal 5"
           :use ((:instance rot-6-b6-10 (p p))
                 (:instance rot-6-b6-10-1 (point p))
                 (:instance b6-10 (p (ROT-6-B6-10-1-WITNESS P)))
                 (:instance rot-6-inv*b3-f (point (ROT-6-B6-10-1-WITNESS P)))
                 (:instance b3-0-n-b3-f (p p))
                 (:instance rot*b3-0-set=>b3-0
                            (p (ROT-6-B6-10-1-WITNESS P))
                            (rot (rot-6)))
                 (:instance rot-6)
                 (:instance b3-0-r-1-a-inv-r-b3-0-a6-iff-b3-0-r-1-a-1-r-a6-1
                            (m2 (a-inv-rotation (acl2-sqrt 2)))
                            (m1 (ROTATION-3D
                                 (- (EXISTS-IN-INTERVAL-BUT-NOT-IN-ANGLE-SEQUENCE-WITNESS 0 (* 2 (ACL2-PI))))
                                 (POINT-ON-S2-NOT-D)))
                            (m3 (ROTATION-3D
                                 (EXISTS-IN-INTERVAL-BUT-NOT-IN-ANGLE-SEQUENCE-WITNESS 0 (* 2 (ACL2-PI)))
                                 (POINT-ON-S2-NOT-D))))
                 (:instance r3-rotationp-r-theta
                            (angle (- (EXISTS-IN-INTERVAL-BUT-NOT-IN-ANGLE-SEQUENCE-WITNESS 0 (* 2 (ACL2-PI))))))
                 (:instance r3-rotationp-r-theta
                            (angle (EXISTS-IN-INTERVAL-BUT-NOT-IN-ANGLE-SEQUENCE-WITNESS 0 (* 2 (ACL2-PI)))))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance witness-not-in-angle-sequence)
                 (:instance b3-0 (p (M-* (ROT-6) (ROT-6-B6-10-1-WITNESS P))))
                 (:instance b3-0 (p p))
                 (:instance cal-radius-p1=p2
                            (p1 (M-* (ROT-6) (ROT-6-B6-10-1-WITNESS P)))
                            (p2 p))
                 (:instance b3-f (p p))
                 (:instance b3 (p p))
                 (:instance rot-3-8-b-3-8-01-or-11=>1
                            (rot (rot-6))
                            (wit (ROT-6-B6-10-1-WITNESS P))
                            (p p)
                            (wit-wit (ROT-6-INV*B3-F-WITNESS (ROT-6-B6-10-1-WITNESS P))))
                 (:instance b3 (p (ROT-6-INV*B3-F-WITNESS (ROT-6-B6-10-1-WITNESS P))))
                 (:instance b3-f (p (ROT-6-INV*B3-F-WITNESS (ROT-6-B6-10-1-WITNESS P))))
                 )
           :in-theory nil
           )
          ("Subgoal 4"
           :use ((:instance rot-7-b7-00 (p p))
                 (:instance rot-7-b7-00-1 (point p))
                 (:instance b7-00 (p (ROT-7-B7-00-1-WITNESS P)))
                 (:instance rot-7-inv*b3-f (point (ROT-7-B7-00-1-WITNESS P)))
                 (:instance b3-0-n-b3-f (p p))
                 (:instance rot*b3-0-set=>b3-0
                            (p (ROT-7-B7-00-1-WITNESS P))
                            (rot (rot-7)))
                 (:instance rot-7)
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance b3-0 (p (M-* (ROT-7) (ROT-7-B7-00-1-WITNESS P))))
                 (:instance b3-0 (p p))
                 (:instance cal-radius-p1=p2
                            (p1 (M-* (ROT-7) (ROT-7-B7-00-1-WITNESS P)))
                            (p2 p))
                 (:instance b3-f (p p))
                 (:instance b3 (p p))
                 (:instance rot-3-8-b-3-8-01-or-11=>1
                            (rot (rot-7))
                            (wit (ROT-7-B7-00-1-WITNESS P))
                            (p p)
                            (wit-wit (ROT-7-INV*B3-F-WITNESS (ROT-7-B7-00-1-WITNESS P))))
                 (:instance b3 (p (ROT-7-INV*B3-F-WITNESS (ROT-7-B7-00-1-WITNESS P))))
                 (:instance b3-f (p (ROT-7-INV*B3-F-WITNESS (ROT-7-B7-00-1-WITNESS P))))
                 )
           :in-theory nil
           )
          ("Subgoal 3"
           :use ((:instance rot-7-b7-10 (p p))
                 (:instance rot-7-b7-10-1 (point p))
                 (:instance b7-10 (p (ROT-7-B7-10-1-WITNESS P)))
                 (:instance rot-7-inv*b3-f (point (ROT-7-B7-10-1-WITNESS P)))
                 (:instance b3-0-n-b3-f (p p))
                 (:instance rot*b3-0-set=>b3-0
                            (p (ROT-7-B7-10-1-WITNESS P))
                            (rot (rot-7)))
                 (:instance rot-7)
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance b3-0 (p (M-* (ROT-7) (ROT-7-B7-10-1-WITNESS P))))
                 (:instance b3-0 (p p))
                 (:instance cal-radius-p1=p2
                            (p1 (M-* (ROT-7) (ROT-7-B7-10-1-WITNESS P)))
                            (p2 p))
                 (:instance b3-f (p p))
                 (:instance b3 (p p))
                 (:instance rot-3-8-b-3-8-01-or-11=>1
                            (rot (rot-7))
                            (wit (ROT-7-B7-10-1-WITNESS P))
                            (p p)
                            (wit-wit (ROT-7-INV*B3-F-WITNESS (ROT-7-B7-10-1-WITNESS P))))
                 (:instance b3 (p (ROT-7-INV*B3-F-WITNESS (ROT-7-B7-10-1-WITNESS P))))
                 (:instance b3-f (p (ROT-7-INV*B3-F-WITNESS (ROT-7-B7-10-1-WITNESS P))))
                 )
           :in-theory nil
           )
          ("Subgoal 2"
           :use ((:instance rot-8-b8-00 (p p))
                 (:instance rot-8-b8-00-1 (point p))
                 (:instance b8-00 (p (ROT-8-B8-00-1-WITNESS P)))
                 (:instance rot-8-inv*b3-f (point (ROT-8-B8-00-1-WITNESS P)))
                 (:instance b3-0-n-b3-f (p p))
                 (:instance rot*b3-0-set=>b3-0
                            (p (ROT-8-B8-00-1-WITNESS P))
                            (rot (rot-8)))
                 (:instance rot-8)
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance b3-0 (p (M-* (ROT-8) (ROT-8-B8-00-1-WITNESS P))))
                 (:instance b3-0 (p p))
                 (:instance cal-radius-p1=p2
                            (p1 (M-* (ROT-8) (ROT-8-B8-00-1-WITNESS P)))
                            (p2 p))
                 (:instance b3-f (p p))
                 (:instance b3 (p p))
                 (:instance rot-3-8-b-3-8-01-or-11=>1
                            (rot (rot-8))
                            (wit (ROT-8-B8-00-1-WITNESS P))
                            (p p)
                            (wit-wit (ROT-8-INV*B3-F-WITNESS (ROT-8-B8-00-1-WITNESS P))))
                 (:instance b3 (p (ROT-8-INV*B3-F-WITNESS (ROT-8-B8-00-1-WITNESS P))))
                 (:instance b3-f (p (ROT-8-INV*B3-F-WITNESS (ROT-8-B8-00-1-WITNESS P))))
                 )
           :in-theory nil
           )
          ("Subgoal 1"
           :use ((:instance rot-8-b8-10 (p p))
                 (:instance rot-8-b8-10-1 (point p))
                 (:instance b8-10 (p (ROT-8-B8-10-1-WITNESS P)))
                 (:instance rot-8-inv*b3-f (point (ROT-8-B8-10-1-WITNESS P)))
                 (:instance b3-0-n-b3-f (p p))
                 (:instance rot*b3-0-set=>b3-0
                            (p (ROT-8-B8-10-1-WITNESS P))
                            (rot (rot-8)))
                 (:instance rot-8)
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance b3-0 (p (M-* (ROT-8) (ROT-8-B8-10-1-WITNESS P))))
                 (:instance b3-0 (p p))
                 (:instance cal-radius-p1=p2
                            (p1 (M-* (ROT-8) (ROT-8-B8-10-1-WITNESS P)))
                            (p2 p))
                 (:instance b3-f (p p))
                 (:instance b3 (p p))
                 (:instance rot-3-8-b-3-8-01-or-11=>1
                            (rot (rot-8))
                            (wit (ROT-8-B8-10-1-WITNESS P))
                            (p p)
                            (wit-wit (ROT-8-INV*B3-F-WITNESS (ROT-8-B8-10-1-WITNESS P))))
                 (:instance b3 (p (ROT-8-INV*B3-F-WITNESS (ROT-8-B8-10-1-WITNESS P))))
                 (:instance b3-f (p (ROT-8-INV*B3-F-WITNESS (ROT-8-B8-10-1-WITNESS P))))
                 )
           :in-theory nil
           )
          ))











































;; -----------------------
;; (defun rot-9 ()
;;   (b-inv-rotation (acl2-sqrt 2)))

;; (defun rot-10 ()
;;   (m-* (b-inv-rotation (acl2-sqrt 2))
;;        (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))) (point-on-s2-not-d))))

;; (defun rot-11 ()
;;   (m-* (rotation-3d
;;         (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d))
;;        (b-inv-rotation (acl2-sqrt 2))))

;; (defun rot-12 ()
;;   (m-* (rotation-3d
;;         (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d))
;;        (b-inv-rotation (acl2-sqrt 2))
;;        (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))) (point-on-s2-not-d))))

;; (defun rot-13 ()
;;   (id-rotation))

;; (defun rot-14 ()
;;   (id-rotation))
