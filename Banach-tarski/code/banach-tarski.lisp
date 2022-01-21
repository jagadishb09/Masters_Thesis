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
  :hints (("Goal"
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
  :hints (("Goal"
           :in-theory (enable array2p header dimensions aref2)
           )))

;; (verify-guards point-in-r3)
;; (verify-guards point-in-r3-x1)
;; (verify-guards point-in-r3-y1)
;; (verify-guards point-in-r3-z1)
;; (verify-guards return-point-in-r3)
;; (verify-guards acl2-exp)
;; (verify-guards acl2-sine)
;; (verify-guards return-point-in-r3)

(defun rotation-about-arbitrary-line (angle m n p)
  ;; (declare (xargs :guard (and (point-in-r3 m)
  ;;                             (point-in-r3 n)
  ;;                             (not (m-= m n))
  ;;                             (point-in-r3 p)
  ;;                             (realp angle)
  ;;                             (equal (+ (* (- (point-in-r3-x1 n) (point-in-r3-x1 m))
  ;;                                          (- (point-in-r3-x1 n) (point-in-r3-x1 m)))
  ;;                                       (* (- (point-in-r3-y1 n) (point-in-r3-y1 m))
  ;;                                          (- (point-in-r3-y1 n) (point-in-r3-y1 m)))
  ;;                                       (* (- (point-in-r3-z1 n) (point-in-r3-z1 m))
  ;;                                          (- (point-in-r3-z1 n) (point-in-r3-z1 m))))
  ;;                                    1))))
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
  :hints (("Goal"
           :in-theory (disable rotation-3d vect-tr point-in-r3-x1 point-in-r3-y1 point-in-r3-z1 m-* return-point-in-r3)
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

(skip-proofs
 (defthmd rot-i*angle*p-in-
   (implies (and (point-in-r3 m)
                 (point-in-r3 n)
                 (zero-p p)
                 (<= (cal-radius m) 1/2)
                 (not (zero-p m))
                 (not (zero-p n))
                 (not (m-= m n))
                 (realp angle)
                 (equal (+ (* (- (point-in-r3-x1 n) (point-in-r3-x1 m))
                              (- (point-in-r3-x1 n) (point-in-r3-x1 m)))
                           (* (- (point-in-r3-y1 n) (point-in-r3-y1 m))
                              (- (point-in-r3-y1 n) (point-in-r3-y1 m)))
                           (* (- (point-in-r3-z1 n) (point-in-r3-z1 m))
                              (- (point-in-r3-z1 n) (point-in-r3-z1 m))))
                        1))
            (<= (cal-radius (rotation-about-arbitrary-line angle m n p)) 1))))

(defun m-p ()
  `((:header :dimensions (3 1)
	     :maximum-length 15)
    ((0 . 0) . 1/10)
    ((1 . 0) . 0)
    ((2 . 0) . 0)
    ))


(defun n-p ()
  `((:header :dimensions (3 1)
	     :maximum-length 15)
    ((0 . 0) . -9/10)
    ((1 . 0) . 0)
    ((2 . 0) . 0)
    ))

(defun rotation-about-sqrt-2 (i p)
  (rotation-about-arbitrary-line (* i (/ (* (acl2-sqrt 2) (acl2-pi)) 180)) (m-p) (n-p) p))

(defun-sk exists-z-p (i point)
  (exists p
          (and (zero-p p)
               (m-= (rotation-about-sqrt-2 i p) point))))

;; (defthmd exists-z-p=>
;;   (implies (exists-d-p n point)
;;            (and (d-p (exists-d-p-witness n point))
;;                 (m-= (m-* (rotation-3d
;;                            (* n (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))
;;                            (point-on-s2-not-d))
;;                           (exists-d-p-witness n point))
;;                      point)))
;;   :hints (("goal"
;;            :in-theory (disable d-p point-on-s2-not-d rotation-3d)
;;            )))

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
               (m-= (rotation-about-sqrt-2 1 p) point))))

;; (defthmd seq-witness*e-func=>
;;   (implies (seq-witness*e-func point)
;;            (and (set-e-p (seq-witness*e-func-witness point))
;;                 (m-= (m-* (rotation-3d
;;                            (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))
;;                            (point-on-s2-not-d))
;;                           (seq-witness*e-func-witness point))
;;                      point)))
;;   :hints (("goal"
;;            :in-theory (disable d-p point-on-s2-not-d rotation-3d efunc)
;;            )))

(defun rot-sqrt-2*f-func (point)
  (and (point-in-r3 point)
       (rot-sqrt-2*f-func-1 point)))

(defun ffunc-not-d (point)
  (and (set-f-p point)
       (not (zero-p point))))
