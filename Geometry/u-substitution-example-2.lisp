
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

(defthmd sub-func-prime-real
  (realp (sub-func-prime x)))

(defthmd i-small-*-lemma
  (implies (and (i-small x)
                (i-small y))
           (i-small (* x y))))

(defthmd i-small-x-*-limited-y
  (implies (and (i-limited z)
                (i-small (- x x1)))
           (i-small (* z (- x x1))))
  :hints (("Goal"
           :use (:instance limited*small->small (y (- x x1)) (x z))
           )))

(defthmd i-close-x-y=>
   (implies (i-close x y)
	    (i-small (- x y)))
   :hints (("goal"
	    :in-theory (enable i-close)
	    )))

(defthmd i-close-x-y=>x*x-c-to-x*y
  (implies (and (i-limited x)
                (i-close x y))
           (i-close (* x x) (* x y))))

(defthmd i-close-x-y=>x*x-c-to-y*y
  (implies (and (i-limited x)
                (i-close x y))
           (i-close (* x x) (* y y))))

(defthmd i-close-x-y=>1-x-c-to-1-y
  (implies (i-close x y)
           (i-close (- 1 x) (- 1 y)))
  :hints (("Goal"
           :in-theory (enable i-close)
           )))

(defthmd root-close-lemma
  (implies (and (realp y1)
		(realp y2)
		(not (= (standard-part y1) (standard-part y2))))
	   (not (i-close y1 y2)))
  :hints (("goal"
	   :in-theory (enable i-close i-small)
	   )))

(defthmd root-close-lemma-1
  (implies (and (realp y1)
		(realp y2)
		(not (i-close y1 y2)))
	   (not (= (standard-part y1) (standard-part y2))))
  :hints (("goal"
	   :in-theory (enable i-close i-small)
	   )))

(defthmd root-close-lemma-2
  (implies (and (realp y1)
                (realp y2)
                (i-limited y1)
                (i-limited y2)
                (>= y1 0)
                (>= y2 0)
                (not (i-close y1 y2)))
           (not (= (* (standard-part y1) (standard-part y1)) (* (standard-part y2) (standard-part y2))))
           )
  :hints (("goal"
           :use ((:instance root-close-lemma-1 (y1 y1) (y2 y2))
                 (:instance ineq-lemma4 (x1 (standard-part y1)) (x2 (standard-part y2)))
                 (:instance ineq-lemma4 (x1 (standard-part y2)) (x2 (standard-part y1))))
           :in-theory nil
           )))

(defthmd square-is-standard
  (implies (and (i-limited y1)
                (realp y1))
           (equal (* (standard-part y1) (standard-part y1))
                  (standard-part (square y1))
                  )))

(defthmd root-close-lemma-3
  (implies (and (realp y1)
                (realp y2)
                (i-limited y1)
                (i-limited y2)
                (>= y1 0)
                (>= y2 0)
                (not (i-close y1 y2)))
           (not (= (standard-part (square y1)) (standard-part (square y2)))))

  :hints (("goal"
           :use ((:instance root-close-lemma-2 (y1 y1) (y2 y2))
                 (:instance square-is-standard (y1 y1))
                 (:instance square-is-standard (y1 y2)))
           :in-theory nil
           )))

(defthmd sqr-real-lemma
  (implies (realp x)
           (realp (square x))))

(defthmd root-close-lemma-6
  (implies (and (realp y1)
                (realp y2)
                (i-limited y1)
                (i-limited y2)
                (>= y1 0)
                (>= y2 0)
                (not (i-close y1 y2)))
           (not (i-close (square y1) (square y2))))
  :hints (("goal"
           :use ((:instance root-close-lemma-3 (y1 y1) (y2 y2))
                 (:instance root-close-lemma (y1 (square y1)) (y2 (square y2)))
                 (:instance sqr-real-lemma (x y1))
                 (:instance sqr-real-lemma (x y2)))
           )))

(defthmd sqrt-real-lemma
  (implies (realp x)
           (realp (acl2-sqrt x))))

(defthmd sqrt>=0-lemma
  (implies (and (i-limited x)
                (realp x))
           (>= (acl2-sqrt x) 0)))

(defthmd i-close-x1-x2=>root-close
  (implies (and (standardp x1)
                (realp x1)
                (realp x2)
                (>= x1 0)
                (>= x2 0)
                (i-close x1 x2))
           (i-close (acl2-sqrt x1) (acl2-sqrt x2)))
  :hints (("goal"
           :use ((:definition square)
                 (:instance standards-are-limited-forward (x x1))
                 (:instance i-close-limited-2 (y x1) (x x2))
                 (:instance sqrt-real-lemma (x x1))
                 (:instance sqrt-real-lemma (x x2))
                 (:instance limited-sqrt (x x1))
                 (:instance limited-sqrt (x x2))
                 (:instance sqrt>=0-lemma (x x1))
                 (:instance sqrt>=0-lemma (x x2))
                 (:instance root-close-lemma-6 (y1 (acl2-sqrt x1) ) (y2 (acl2-sqrt x2))))
           )))

(defthmd i-close-x-x1=>i-limited-x1
  (implies (and (standardp x)
                (acl2-numberp x)
                (i-close x x1))
           (i-limited x1))
  :hints (("Goal"
           :use ((:instance i-close-limited (y x1) (x x)))
           )))

(defthmd inside-interval=>i-limited
  (implies (inside-interval-p x (sub-domain))
           (i-limited x))
  :hints (("Goal"
           :use ((:instance limited-squeeze (a (/ 1 4)) (b (/ 1 2)) (x x)))
           :in-theory (enable interval-definition-theory)
           )))

(defthmd i-limited-1-x*x
  (implies (i-limited x)
           (i-limited (- 1 (* x x)))))

(defthmd standardp-x*x
  (implies (standardp x)
           (standardp (* x x))))

(defthmd standard-1-*x*x
  (implies (standardp x)
           (standardp (- 1 (* x x)))))

(defthmd x-in-sub-domain=>x>=0
  (implies (and (realp x)
                (>= x (acl2-sqrt (/ 12 16))))
           (>= x 0)))

(defthmd sqrt-1-*x*x-close-to-1-*x1*x1
  (implies (and (standardp x)
		(inside-interval-p x (sub-domain))
                (inside-interval-p x1 (sub-domain))
                (i-close x x1))
           (i-close (acl2-sqrt (- 1 (* x x))) (acl2-sqrt (- 1 (* x1 x1)))))
  :hints (("Goal"
           :use ((:instance i-close-x1-x2=>root-close (x1 (- 1 (* x x))) (x2 (- 1 (* x1 x1))))
                 (:instance sub-func-range-3 (x x))
                 (:instance sub-func-range-3 (x x1))
                 (:instance i-close-x-y=>x*x-c-to-y*y (x x) (y x1))
                 (:instance i-close-x-y=>1-x-c-to-1-y (x (* x x)) (y (* x1 x1)))
                 (:instance i-close (x x) (y x1))
                 )
           :in-theory (enable interval-definition-theory)
           )))

(defthmd small-if-<-small-lemma
  (implies (and (i-small x)
                (realp x)
                (realp y)
                (<= 0 y)
                (<= y x))
           (i-small y))
  :hints (("Goal"
           :use ((:instance standard-part-squeeze
                            (x 0)
                            (y y)
                            (z x)))
           :in-theory (disable ;small-<-non-small-lemma
                       small-<-non-small))))

(defthmd sqrt-1-*x*x-not-i-small-1
  (implies (and (standardp x)
                (realp x)
                (> x 0))
           (not (i-small x)))
  :hints (("Goal"
           :in-theory (enable i-small)
           )))

(defthm-std sqrt-1-*x*x-not-i-small-2
  (implies (standardp x)
           (standardp (acl2-sqrt x))))

(defthmd sqrt-1-*x*x-not-i-small
  (implies (and (inside-interval-p x (sub-domain))
                (standardp x))
           (not (i-small (acl2-sqrt (- 1 (* x x))))))
  :hints (("Goal"
           :use ((:instance standard-part-sqrt (x (- 1 (* x x))))
                 (:instance sub-func-range-3 (x x))
                 (:instance small-if-<-small-lemma (x (- 1 (* x x))) (y (/ 12 16)))
                 (:instance sqrt-1-*x*x-not-i-small-1 (x (acl2-sqrt (- 1 (* x x)))))
                 (:instance sqrt-1-*x*x-not-i-small-2 (x (- 1 (* x x))))
                 (:instance standard-1-*x*x (x x))
                 )
           :in-theory (enable interval-definition-theory)
           )))

(defthmd sqrt-1-*x*x-not-i-small-x1
  (implies (and (inside-interval-p x (sub-domain))
                (inside-interval-p x1 (sub-domain))
                (i-close x x1)
                (standardp x))
           (not (i-small (acl2-sqrt (- 1 (* x1 x1))))))
  :hints (("Goal"
           :use ((:instance i-close-small-2
                            (y (acl2-sqrt (- 1 (* x1 x1))))
                            (x (acl2-sqrt (- 1 (* x1 x1)))))
                 (:instance sqrt-1-*x*x-not-i-small)
                 (:instance sqrt-1-*x*x-close-to-1-*x1*x1)
                 )
           )))

(encapsulate
  ()

  (local (include-book "arithmetic/top" :dir :system))

  (defthmd i-close-/-lemma
    (implies (and (i-close x x1)
                  (not (i-small x))
                  (i-limited x)
                  (i-limited x1)
                  (not (i-small x1))
                  (not (equal x 0))
                  (not (equal x1 0)))
             (i-close (/ x) (/ x1)))
    :hints (("Goal"
             :use ((:instance limited*small->small (y (- x1 x)) (x (/ (* x x1))))
                   (:instance i-small-uminus (x (- x x1)))
                   )
             :in-theory (enable i-close)
             )))
  )

(defthmd i-close-1/sqrt-x-1/sqrt-x1
  (implies (and (inside-interval-p x (sub-domain))
                (inside-interval-p x1 (sub-domain))
                (i-close x x1)
                (standardp x))
           (i-close (/ (acl2-sqrt (- 1 (* x x)))) (/ (acl2-sqrt (- 1 (* x1 x1))))))
  :hints (("Goal"
           :use ((:instance i-close-/-lemma (x (acl2-sqrt (- 1 (* x x)))) (x1 (acl2-sqrt (- 1 (* x1 x1)))))
                 (:instance sqrt-1-*x*x-close-to-1-*x1*x1 (x x) (X1 x1))
                 (:instance sqrt-1-*x*x-not-i-small (x x))
                 (:instance sqrt-1-*x*x-not-i-small-x1 (x x) (x1 x1))
                 (:instance limited-sqrt (x (- 1 (* x x))))
                 (:instance sub-func-range-3)
                 )
           :in-theory (enable interval-definition-theory)
           )))

(defthmd i-close-x-x1=>xy-to-x1y
  (implies (and (i-close x x1)
                (i-limited y))
           (i-close (* x y) (* x1 y))))

(defthmd sub-func-prime-continuous-1
  (implies (and (standardp x)
		(inside-interval-p x (sub-domain))
		(i-close x x1)
		(inside-interval-p x1 (sub-domain)))
           (i-close (/ (- x) (acl2-sqrt (- 1 (* x x))))
                    (/ (- x) (acl2-sqrt (- 1 (* x1 x1))))))
  :hints (("Goal"
           :use ((:instance i-close-x-x1=>xy-to-x1y
                            (y x)
                            (x1 (/ (acl2-sqrt (- 1 (* x1 x1)))))
                            (x (/ (acl2-sqrt (- 1 (* x x))))))
                 (:instance i-limited-udivide (x (acl2-sqrt (- 1 (* x x)))))
                 (:instance limited-sqrt (x (- 1 (* x x))))
                 (:instance sub-func-range-3)
                 (:instance sqrt-1-*x*x-not-i-small)
                 (:instance i-close-1/sqrt-x-1/sqrt-x1)
                 )
           :in-theory (enable interval-definition-theory)
           )))

(defthmd sub-func-prime-continuous-2
  (implies (and (standardp x)
		(inside-interval-p x (sub-domain))
		(i-close x x1)
		(inside-interval-p x1 (sub-domain)))
           (i-close (/ (- x) (acl2-sqrt (- 1 (* x1 x1))))
                    (/ (- x1) (acl2-sqrt (- 1 (* x1 x1))))))
  :hints (("Goal"
           :use ((:instance i-close-x-x1=>xy-to-x1y
                            (x (- x))
                            (x1 (- x1))
                            (y (/ (acl2-sqrt (- 1 (* x1 x1))))))
                 (:instance i-limited-udivide (x (acl2-sqrt (- 1 (* x x)))))
                 (:instance limited-sqrt (x (- 1 (* x x))))
                 (:instance sub-func-range-3)
                 (:instance i-close-limited
                            (x (/ (acl2-sqrt (- 1 (* x x)))))
                            (y (/ (acl2-sqrt (- 1 (* x1 x1))))))
                 (:instance i-close-1/sqrt-x-1/sqrt-x1)
                 (:instance sqrt-1-*x*x-not-i-small)
                 )
           :in-theory (enable interval-definition-theory)
           )))

(defthmd sub-func-prime-continuous
  (implies (and (standardp x)
		(inside-interval-p x (sub-domain))
		(i-close x x1)
		(inside-interval-p x1 (sub-domain)))
	   (i-close (sub-func-prime x)
		    (sub-func-prime x1)))
  :hints (("Goal"
           :use ((:instance sub-func-prime-continuous-1)
                 (:instance sub-func-prime-continuous-2)
                 )
           )))
----
(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd not-i-small-x+y
    (implies (and (not (i-small x))
                  (realp x)
                  (realp y)
                  (> x 0)
                  (> y 0)
                  (not (i-small y)))
             (not (i-small (+ x y))))
    :hints (("Goal"
             :use ((:instance standard-part-<-2 (x 0) (y y))
                   (:instance standard-part-<-2 (x 0) (y x))
                   )
             :in-theory (enable i-small)
             )))
  )

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd test-case-100
    (implies (and (realp x)
                  (> a 0)
                  (> b 0)
                  (realp a)
                  (realp b)
                  (<= a x)
                  (realp y)
                  (<= b y))
             (<= (* a b) (* x y))))
  )
























(defthmd sqrt-1-*x*x-close-to-1-*x1*x1-f
  (implies (and (standardp x)
		(inside-interval-p x (int-f-domain))
                (inside-interval-p x1 (int-f-domain))
                (i-close x x1))
           (i-close (acl2-sqrt (- 1 (* x x))) (acl2-sqrt (- 1 (* x1 x1)))))
  :hints (("Goal"
           :use ((:instance i-close-x1-x2=>root-close (x1 (- 1 (* x x))) (x2 (- 1 (* x1 x1))))
                 (:instance sub-func-range-3 (x x))
                 (:instance sub-func-range-3 (x x1))
                 (:instance i-close-x-y=>x*x-c-to-y*y (x x) (y x1))
                 (:instance i-close-x-y=>1-x-c-to-1-y (x (* x x)) (y (* x1 x1)))
                 (:instance i-close (x x) (y x1))
                 )
           :in-theory (enable interval-definition-theory)
           )))

(defthmd small-if-<-small-lemma
  (implies (and (i-small x)
                (realp x)
                (realp y)
                (<= 0 y)
                (<= y x))
           (i-small y))
  :hints (("Goal"
           :use ((:instance standard-part-squeeze
                            (x 0)
                            (y y)
                            (z x)))
           :in-theory (disable ;small-<-non-small-lemma
                       small-<-non-small))))

(defthmd sqrt-1-*x*x-not-i-small-1
  (implies (and (standardp x)
                (realp x)
                (> x 0))
           (not (i-small x)))
  :hints (("Goal"
           :in-theory (enable i-small)
           )))

(defthm-std sqrt-1-*x*x-not-i-small-2
  (implies (standardp x)
           (standardp (acl2-sqrt x))))

(defthmd sqrt-1-*x*x-not-i-small
  (implies (and (inside-interval-p x (sub-domain))
                (standardp x))
           (not (i-small (acl2-sqrt (- 1 (* x x))))))
  :hints (("Goal"
           :use ((:instance standard-part-sqrt (x (- 1 (* x x))))
                 (:instance sub-func-range-3 (x x))
                 (:instance small-if-<-small-lemma (x (- 1 (* x x))) (y (/ 12 16)))
                 (:instance sqrt-1-*x*x-not-i-small-1 (x (acl2-sqrt (- 1 (* x x)))))
                 (:instance sqrt-1-*x*x-not-i-small-2 (x (- 1 (* x x))))
                 (:instance standard-1-*x*x (x x))
                 )
           :in-theory (enable interval-definition-theory)
           )))

(defthmd sqrt-1-*x*x-not-i-small-x1
  (implies (and (inside-interval-p x (sub-domain))
                (inside-interval-p x1 (sub-domain))
                (i-close x x1)
                (standardp x))
           (not (i-small (acl2-sqrt (- 1 (* x1 x1))))))
  :hints (("Goal"
           :use ((:instance i-close-small-2
                            (y (acl2-sqrt (- 1 (* x1 x1))))
                            (x (acl2-sqrt (- 1 (* x1 x1)))))
                 (:instance sqrt-1-*x*x-not-i-small)
                 (:instance sqrt-1-*x*x-close-to-1-*x1*x1)
                 )
           )))

(encapsulate
  ()

  (local (include-book "arithmetic/top" :dir :system))

  (defthmd i-close-/-lemma
    (implies (and (i-close x x1)
                  (not (i-small x))
                  (i-limited x)
                  (i-limited x1)
                  (not (i-small x1))
                  (not (equal x 0))
                  (not (equal x1 0)))
             (i-close (/ x) (/ x1)))
    :hints (("Goal"
             :use ((:instance limited*small->small (y (- x1 x)) (x (/ (* x x1))))
                   (:instance i-small-uminus (x (- x x1)))
                   )
             :in-theory (enable i-close)
             )))
  )

(defthmd i-close-1/sqrt-x-1/sqrt-x1
  (implies (and (inside-interval-p x (sub-domain))
                (inside-interval-p x1 (sub-domain))
                (i-close x x1)
                (standardp x))
           (i-close (/ (acl2-sqrt (- 1 (* x x)))) (/ (acl2-sqrt (- 1 (* x1 x1))))))
  :hints (("Goal"
           :use ((:instance i-close-/-lemma (x (acl2-sqrt (- 1 (* x x)))) (x1 (acl2-sqrt (- 1 (* x1 x1)))))
                 (:instance sqrt-1-*x*x-close-to-1-*x1*x1 (x x) (X1 x1))
                 (:instance sqrt-1-*x*x-not-i-small (x x))
                 (:instance sqrt-1-*x*x-not-i-small-x1 (x x) (x1 x1))
                 (:instance limited-sqrt (x (- 1 (* x x))))
                 (:instance sub-func-range-3)
                 )
           :in-theory (enable interval-definition-theory)
           )))

(defthmd i-close-x-x1=>xy-to-x1y
  (implies (and (i-close x x1)
                (i-limited y))
           (i-close (* x y) (* x1 y))))

(defthmd sub-func-prime-continuous-1
  (implies (and (standardp x)
		(inside-interval-p x (sub-domain))
		(i-close x x1)
		(inside-interval-p x1 (sub-domain)))
           (i-close (/ (- x) (acl2-sqrt (- 1 (* x x))))
                    (/ (- x) (acl2-sqrt (- 1 (* x1 x1))))))
  :hints (("Goal"
           :use ((:instance i-close-x-x1=>xy-to-x1y
                            (y x)
                            (x1 (/ (acl2-sqrt (- 1 (* x1 x1)))))
                            (x (/ (acl2-sqrt (- 1 (* x x))))))
                 (:instance i-limited-udivide (x (acl2-sqrt (- 1 (* x x)))))
                 (:instance limited-sqrt (x (- 1 (* x x))))
                 (:instance sub-func-range-3)
                 (:instance sqrt-1-*x*x-not-i-small)
                 (:instance i-close-1/sqrt-x-1/sqrt-x1)
                 )
           :in-theory (enable interval-definition-theory)
           )))

(defthmd sub-func-prime-continuous-2
  (implies (and (standardp x)
		(inside-interval-p x (sub-domain))
		(i-close x x1)
		(inside-interval-p x1 (sub-domain)))
           (i-close (/ (- x) (acl2-sqrt (- 1 (* x1 x1))))
                    (/ (- x1) (acl2-sqrt (- 1 (* x1 x1))))))
  :hints (("Goal"
           :use ((:instance i-close-x-x1=>xy-to-x1y
                            (x (- x))
                            (x1 (- x1))
                            (y (/ (acl2-sqrt (- 1 (* x1 x1))))))
                 (:instance i-limited-udivide (x (acl2-sqrt (- 1 (* x x)))))
                 (:instance limited-sqrt (x (- 1 (* x x))))
                 (:instance sub-func-range-3)
                 (:instance i-close-limited
                            (x (/ (acl2-sqrt (- 1 (* x x)))))
                            (y (/ (acl2-sqrt (- 1 (* x1 x1))))))
                 (:instance i-close-1/sqrt-x-1/sqrt-x1)
                 (:instance sqrt-1-*x*x-not-i-small)
                 )
           :in-theory (enable interval-definition-theory)
           )))

(defthmd sub-func-prime-continuous
  (implies (and (standardp x)
		(inside-interval-p x (sub-domain))
		(i-close x x1)
		(inside-interval-p x1 (sub-domain)))
	   (i-close (sub-func-prime x)
		    (sub-func-prime x1)))
  :hints (("Goal"
           :use ((:instance sub-func-prime-continuous-1)
                 (:instance sub-func-prime-continuous-2)
                 )
           )))





























;; (defthm circle-continuous
;;   (implies (and (standardp x)
;; 		(inside-interval-p x (circle-x-domain))
;; 		(i-close x x1)
;; 		(inside-interval-p x1 (circle-x-domain)))
;; 	   (i-close (circle x)
;; 		    (circle x1)))


-------



;; (defthmd i-small-x-y
;;   (implies (and (acl2-numberp x)
;;                 (acl2-numberp y)
;;                 (i-small (- x y)))
;;            (i-close x y))
;;   :hints (("goal"
;;            :in-theory (enable i-small i-close)
;;            )))


(encapsulate
  ()

  (local (include-book "arithmetic/top" :dir :system))

  (defthmd i-close-/-lemma
    (implies (and (i-close x x1)
                  (not (i-small x))
                  (i-limited x)
                  (i-limited x1)
                  (not (i-small x1))
                  (not (equal x 0))
                  (not (equal x1 0)))
             (i-close (/ x) (/ x1)))
    :hints (("Goal"
             :use ((:instance limited*small->small (y (- x1 x)) (x (/ (* x x1))))
                   (:instance i-small-uminus (x (- x x1)))
                   )
             :in-theory (enable i-close)
             )))
  )

(defthmd int-f-domain-real-1
  (implies (and (realp x)
                (not (i-small y1))
                (not (i-small y2))
                (realp y1)
                (realp y2)
                (<= x y2)
                (<= y1 x))
	   (not (i-small x)))
  :hints (("Goal"
           ;:in-theory (enable interval-definition-theory)
           )))


(defthmd i-small-sqrt-lemma
  (i-limited 16))

(defthmd sub-func-prime-continuous
  (implies (and (standardp x)
		(inside-interval-p x (sub-domain))
		(i-close x x1)
		(inside-interval-p x1 (sub-domain)))
	   (i-close (sub-func-prime x)
		    (sub-func-prime x1)))

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
