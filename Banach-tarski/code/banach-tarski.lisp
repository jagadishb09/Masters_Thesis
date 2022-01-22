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

(defun vect-tr (x y z p)
  `((:header :dimensions (3 1)
	     :maximum-length 15)
    ((0 . 0) . ,(+ (aref2 :fake-name p 0 0) x) )
    ((1 . 0) . ,(+ (aref2 :fake-name p 1 0) y) )
    ((2 . 0) . ,(+ (aref2 :fake-name p 2 0) z) )
    ))

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

(skip-proofs
 (defthmd rotation-about-arbitrary-line=>r3p
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
            (point-in-r3 (rotation-about-arbitrary-line angle m n p)))))

(skip-proofs
 (defthmd rotation-about-arbitrary-line=p
   (implies (and (point-in-r3 m)
                 (point-in-r3 n)
                 (point-in-r3 p)
                 (not (m-= m n))
                 (equal angle 0)
                 (equal (+ (* (- (point-in-r3-x1 n) (point-in-r3-x1 m))
                              (- (point-in-r3-x1 n) (point-in-r3-x1 m)))
                           (* (- (point-in-r3-y1 n) (point-in-r3-y1 m))
                              (- (point-in-r3-y1 n) (point-in-r3-y1 m)))
                           (* (- (point-in-r3-z1 n) (point-in-r3-z1 m))
                              (- (point-in-r3-z1 n) (point-in-r3-z1 m))))
                        1))
            (m-= (rotation-about-arbitrary-line angle m n p) p))))

(skip-proofs
 (defthmd rot-angle1-of-angle2*p=>
   (implies (and (point-in-r3 m)
                 (point-in-r3 n)
                 (point-in-r3 p)
                 (not (m-= m n))
                 (realp angle1)
                 (realp angle2)
                 (equal (+ (* (- (point-in-r3-x1 n) (point-in-r3-x1 m))
                              (- (point-in-r3-x1 n) (point-in-r3-x1 m)))
                           (* (- (point-in-r3-y1 n) (point-in-r3-y1 m))
                              (- (point-in-r3-y1 n) (point-in-r3-y1 m)))
                           (* (- (point-in-r3-z1 n) (point-in-r3-z1 m))
                              (- (point-in-r3-z1 n) (point-in-r3-z1 m))))
                        1))
            (m-= (rotation-about-arbitrary-line angle1 m n (rotation-about-arbitrary-line angle2 m n p))
                 (rotation-about-arbitrary-line (+ angle1 angle2) m n p)))))

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

(skip-proofs
 (defthmd rot-i*angle*p-not-=p
   (implies (and (point-in-r3 m)
                 (point-in-r3 n)
                 (zero-p p)
                 (not (zero-p m))
                 (not (zero-p n))
                 (not (m-= m n))
                 (posp i)
                 (equal angle (/ (* (acl2-sqrt 2) (acl2-pi)) 180))
                 (equal (+ (* (- (point-in-r3-x1 n) (point-in-r3-x1 m))
                              (- (point-in-r3-x1 n) (point-in-r3-x1 m)))
                           (* (- (point-in-r3-y1 n) (point-in-r3-y1 m))
                              (- (point-in-r3-y1 n) (point-in-r3-y1 m)))
                           (* (- (point-in-r3-z1 n) (point-in-r3-z1 m))
                              (- (point-in-r3-z1 n) (point-in-r3-z1 m))))
                        1))
            (not (m-= (rotation-about-arbitrary-line (* i angle) m n p)
                      p)))))

(skip-proofs
 (defthmd rot-i*angle*p-not-=rot-j
   (implies (and (point-in-r3 m)
                 (point-in-r3 n)
                 (zero-p p)
                 (not (zero-p m))
                 (not (zero-p n))
                 (not (m-= m n))
                 (posp i)
                 (posp j)
                 (< i j)
                 (equal angle (/ (* (acl2-sqrt 2) (acl2-pi)) 180))
                 (equal (+ (* (- (point-in-r3-x1 n) (point-in-r3-x1 m))
                              (- (point-in-r3-x1 n) (point-in-r3-x1 m)))
                           (* (- (point-in-r3-y1 n) (point-in-r3-y1 m))
                              (- (point-in-r3-y1 n) (point-in-r3-y1 m)))
                           (* (- (point-in-r3-z1 n) (point-in-r3-z1 m))
                              (- (point-in-r3-z1 n) (point-in-r3-z1 m))))
                        1))
            (not (m-= (rotation-about-arbitrary-line (* i angle) m n p)
                      (rotation-about-arbitrary-line (* j angle) m n p))))))

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
    ((0 . 0) . -9/10)
    ((1 . 0) . 1/4)
    ((2 . 0) . 0)
    ))

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
           :use ((:instance rotation-about-arbitrary-line=p (m (m-p)) (n (n-p)) (p p) (angle angle)))
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
           :use ((:instance rot-angle1-of-angle2*p=> (m (m-p)) (n (n-p)) (p p) (angle1 angle1) (angle2 angle2)))
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

(defthmd rot-i*angle*p-not-=p-m-n
  (implies (and (zero-p p)
                (posp i)
                (equal angle (/ (* (acl2-sqrt 2) (acl2-pi)) 180)))
           (not (m-= (rotation-about-arbitrary-line (* i angle) (m-p) (n-p) p)
                     p)))
  :hints (("goal"
           :use ((:instance rot-i*angle*p-not-=p (m (m-p)) (n (n-p)) (p p) (i i)
                            (angle (/ (* (acl2-sqrt 2) (acl2-pi)) 180)))
                 (:instance rot-i*angle*p-not-=p-m-n-1)
                 (:instance rot-i*angle*p-not-=p-m-n-2))
           :in-theory (disable rotation-about-arbitrary-line acl2-sqrt acl2-pi)
           )))

(defthmd rot-i*angle*p-not-=rot-j-m-n
  (implies (and (zero-p p)
                (posp i)
                (posp j)
                (< i j)
                (equal angle (/ (* (acl2-sqrt 2) (acl2-pi)) 180)))
           (not (m-= (rotation-about-arbitrary-line (* i angle) (m-p) (n-p) p)
                     (rotation-about-arbitrary-line (* j angle) (m-p) (n-p) p))))
  :hints (("goal"
           :use ((:instance rot-i*angle*p-not-=rot-j (m (m-p)) (n (n-p)) (p p) (i i) (j j)
                            (angle (/ (* (acl2-sqrt 2) (acl2-pi)) 180)))
                 (:instance rot-i*angle*p-not-=p-m-n-1)
                 (:instance rot-i*angle*p-not-=p-m-n-2))
           :in-theory (disable rotation-about-arbitrary-line acl2-sqrt acl2-pi)
           )))

(defun angle-const()
  (/ (* (acl2-sqrt 2) (acl2-pi)) 180))

(defthmd angle-const-is-real
  (realp (angle-const)))

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
           :in-theory (disable d-p point-on-s2-not-d rotation-3d rotation-about-arbitrary-line angle-const)
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
           :in-theory (disable d-p point-on-s2-not-d rotation-3d ffunc rotation-about-arbitrary-line angle-const)
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
                 (:instance angle-const)
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
