
(in-package "ACL2")

; cert_param: (uses-acl2r)

(local (include-book "arithmetic/realp" :dir :system))
(local (include-book "arithmetic/inequalities" :dir :system))
(include-book "nonstd/nsa/inverse-square" :dir :system)
(include-book "nonstd/nsa/inverse-trig" :dir :system)
(include-book "nonstd/integrals/u-substitution" :dir :system)

;; (acl2-sqrt 15)/4 to (acl2-sqrt 12) / 4
;; 1/4 to 3/4

(defun int-f-domain() (interval (acl2-sqrt (/ 12 16)) (acl2-sqrt (/ 15 16))))

(defun sub-domain() (interval (/ 1 4) (/ 1 2)))

(defun integral-function (x)
  (if (inside-interval-p x (int-f-domain))
      (/ x (+ (- 1 (* x x)) (acl2-sqrt (- 1 (* x x)))))
    0))

(defun sub-func (x)
  (if (inside-interval-p x (sub-domain))
      (acl2-sqrt (- 1 (* x x)))
    0))

(defun sub-func-prime (x)
  (if (inside-interval-p x (sub-domain))
      (/ (- x) (acl2-sqrt (- 1 (* x x))))
    0))

(defthm-std int-f-domain-std
  (standardp (int-f-domain)))

(defthm-std sub-domain-std
  (standardp (sub-domain)))

(defthm-std int-func-std
  (implies (standardp x)
           (standardp (integral-function x))))

(defthm-std sub-func-std
  (implies (standardp x)
           (standardp (sub-func x))))

(defthm-std sub-func-prime-std
  (implies (standardp x)
           (standardp (sub-func-prime x))))

(defthmd intervalp-int-f-domain
  (interval-p (int-f-domain)))

(defthmd int-f-domain-real
  (implies (inside-interval-p x (int-f-domain))
	   (realp x)))

(defthmd int-f-domain-non-trivial
  (or (null (interval-left-endpoint (int-f-domain)))
      (null (interval-right-endpoint (int-f-domain)))
      (< (interval-left-endpoint (int-f-domain))
	 (interval-right-endpoint (int-f-domain)))))

(defthmd intervalp-sub-domain
  (interval-p (sub-domain)))

(defthmd sub-domain-real
  (implies (inside-interval-p x (sub-domain))
	   (realp x)))

(defthmd sub-domain-non-trivial
  (or (null (interval-left-endpoint (sub-domain)))
      (null (interval-right-endpoint (sub-domain)))
      (< (interval-left-endpoint (sub-domain))
	 (interval-right-endpoint (sub-domain)))))

(defthmd ineq-lemma1
  (implies (and (realp x1)
                (realp x2)
                (>= x1 0)
                (>= x2 0)
                (> x1 x2))
           (> (* x1 x1) (* x1 x2))))

; matt k. addition to speed up proofs:
(in-theory (disable sqrt-epsilon-delta))

(defthmd ineq-lemma2
  (implies (and (realp x1)
                (realp x2)
                (>= x1 0)
                (>= x2 0)
                (< x2 x1))
           (>= (* x1 x2) (* x2 x2))))

(defthmd ineq-lemma3
  (implies (and (realp a)
                (realp b)
                (realp c)
                (> a b)
                (>= b c))
           (> a c)))

(defthmd ineq-lemma4
  (implies (and (realp x1)
                (realp x2)
                (>= x1 0)
                (>= x2 0)
                (> x1 x2))
           (> (* x1 x1) (* x2 x2)))
  :hints (("goal"
           :use ((:instance ineq-lemma1 (x1 x1) (x2 x2))
                 (:instance ineq-lemma2 (x1 x1) (x2 x2))
                 (:instance ineq-lemma3 (a (* x1 x1)) (b (* x1 x2)) (c (* x2 x2))))
           :in-theory nil
           )))

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd sub-func-range-1
    (implies (and (realp x)
                  (realp y)
                  (<= x y)
                  (>= x 0)
                  (>= y 0))
             (<= (* x x) (* y y)))
    :hints (("Goal"
             :use ((:instance ineq-lemma4 (x1 y) (x2 x)))
             )))
  )

(defthmd sub-func-range-2
  (implies (and (realp x)
                (<= x (/ 1 2))
                (>= x (/ 1 4)))
           (and (<= (* x x) (/ 1 4))
                (>= (* x x) (/ 1 16))))
  :hints (("Goal"
           :use ((:instance sub-func-range-1 (x x) (y (/ 1 2)))
                 (:instance sub-func-range-1 (x (/ 1 4)) (y x)))
           )))

(defthmd sub-func-range-3
  (implies (and (realp x)
                (<= x (/ 1 2))
                (>= x (/ 1 4)))
           (and (<= (- 1 (* x x)) (/ 15 16))
                (>= (- 1 (* x x)) (/ 12 16))))
  :hints (("Goal"
           :use ((:instance sub-func-range-2))
           )))

(encapsulate
  ()

  (local (include-book "arithmetic/top" :dir :system))

  (defthmd sub-func-range-4
    (implies (realp x)
             (realp (acl2-sqrt x))))

  (defthmd sub-func-range
    (implies (and (realp x)
                  (<= x (/ 1 2))
                  (>= x (/ 1 4)))
             (and (<= (acl2-sqrt (/ 12 16)) (acl2-sqrt (- 1 (* x x))))
                  (<= (acl2-sqrt (- 1 (* x x))) (acl2-sqrt (/ 15 16)))))
    :hints (("Goal"
             :use ((:instance sqrt-<-y (x (- 1 (* x x))) (y (acl2-sqrt (/ 15 16))))
                   (:instance y-<-sqrt (x (- 1 (* x x))) (y (acl2-sqrt (/ 12 16))))
                   (:instance y*y=x->y=sqrt-x (x (- 1 (* x x))) (y (acl2-sqrt (/ 15 16))))
                   (:instance y*y=x->y=sqrt-x (x (- 1 (* x x))) (y (acl2-sqrt (/ 12 16))))
                   (:instance sqrt-=-y (x (/ 3 4)) (y (acl2-sqrt (/ 3 4))))
                   (:instance sqrt-=-y (x (/ 15 16)) (y (acl2-sqrt (/ 15 16))))
                   (:instance sub-func-range-3 (x x))
                   (:instance sqrt->-0 (x (/ 15 16)))
                   (:instance sub-func-range-4 (x (/ 15 16)))
                   (:instance sqrt->-0 (x (/ 12 16)))
                   (:instance sub-func-range-4 (x (/ 12 16)))
                   )
             :in-theory nil
             )))
  )

(defthmd subfunc-range-in-domain-of-int-f
  (implies (inside-interval-p x (sub-domain))
	   (inside-interval-p (sub-func x) (int-f-domain)))
  :hints (("goal"
	   :use ((:instance sub-func-range)
		 (:instance intervalp-int-f-domain)
		 (:instance int-f-domain-real))
	   :in-theory (e/d (interval-definition-theory) (acl2-sqrt))
	   )))

(defthmd int-f-real
  (realp (integral-function x)))

(defthmd sub-func-real
  (realp (sub-func x)))

(defthm sub-func-prime-real
  (realp (sub-func-prime x)))

;; (defthm sub-func-prime-continuous
;;   (implies (and (standardp x)
;; 		(inside-interval-p x (sub-domain))
;; 		(i-close x x1)
;; 		(inside-interval-p x1 (sub-domain)))
;; 	   (i-close (sub-func-prime x)
;; 		    (sub-func-prime x1)))

;; (defthm sub-func-prime-is-derivative
;;   (implies (and (standardp x)
;; 		(inside-interval-p x (sub-domain))
;; 		(inside-interval-p x1 (sub-domain))
;; 		(i-close x x1) (not (= x x1)))
;; 	   (i-close (/ (- (sub-func x) (sub-func x1)) (- x x1))
;; 		    (sub-func-prime x)))

;; (defthm sub-func-differentiable
;;   (implies (and (standardp x)
;; 		(inside-interval-p x (sub-domain))
;; 		(inside-interval-p y1 (sub-domain))
;; 		(inside-interval-p y2 (sub-domain))
;; 		(i-close x y1) (not (= x y1))
;; 		(i-close x y2) (not (= x y2)))
;; 	   (and (i-limited (/ (- (sub-func x) (sub-func y1)) (- x y1)))
;; 		(i-close (/ (- (sub-func x) (sub-func y1)) (- x y1))
;; 			 (/ (- (sub-func x) (sub-func y2)) (- x y2)))))

;; (defthm circle-continuous
;;   (implies (and (standardp x)
;; 		(inside-interval-p x (circle-x-domain))
;; 		(i-close x x1)
;; 		(inside-interval-p x1 (circle-x-domain)))
;; 	   (i-close (circle x)
;; 		    (circle x1)))
