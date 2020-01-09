(in-package "ACL2")

(include-book "/Users/jagadishbapanapally/Documents/acl2-8.2/acl2-sources/books/nonstd/nsa/inverse-square")
(include-book "/Users/jagadishbapanapally/Documents/acl2-8.2/acl2-sources/books/nonstd/nsa/trig")
(include-book "/Users/jagadishbapanapally/Documents/acl2-8.2/acl2-sources/books/nonstd/integrals/ftc-2")

(encapsulate 
 ((rad() t))
 (local (defun rad() 1))
 (defthm rad-def
   (and (realp (rad))
	(standardp (rad))
	(>= (rad) 0)))
 )

(defun f1 (x)
  (if (realp x)
      (- (* (square (rad)) x) (* x (square x) 1/3))
    0)
  )

(defun f1-prime (x)
  (- (square (rad)) (square x))
  )

(defun f1-domain () (interval nil nil))

(defthm intervalp-f1-domain
  (interval-p (f1-domain)))

(defthm f1-domain-real
  (implies (inside-interval-p x (f1-domain))
	   (realp x)))

(defthm f1-domain-non-trivial
  (or (null (interval-left-endpoint (f1-domain)))
      (null (interval-right-endpoint (f1-domain)))
      (< (interval-left-endpoint (f1-domain))
	 (interval-right-endpoint (f1-domain))))
  :rule-classes nil)


(defthm f1-real
  (realp (f1 x)))

(defthm f1-prime-real
  (realp (f1-prime x)))

(encapsulate
 ()
 (local (include-book "/Users/jagadishbapanapally/Documents/acl2-8.2/acl2-sources/books/arithmetic/top-with-meta"))

 (local
  (defthm lemma-1
    (implies (and (standardp x)
		  (inside-interval-p x (f1-domain))
		  (inside-interval-p y (f1-domain))
		  (i-close x y) (not (= x y)))
	     (= (/ (- (f1 x) (f1 y)) (- x y)) (/ (- (* (square (rad)) (- x y)) (* 1/3 (- x y) (+ (square x) (* x y) (square y)))) (- x y)))
	     )
    )
  )

 (local
  (defthm lemma-2
    (implies (and (acl2-numberp x)
		  (acl2-numberp y)
		  (acl2-numberp z)
		  (not (= z 0)))
	     (= (/ (- (* x z) (* 1/3 z y)) z) (- x (* 1/3 y))))		  
    )
  )

 (local
  (defthm lemma-3
    (implies (realp x)
	     (realp (* x x)))
    )
  )

 (local
  (defthm lemma-4
    (implies (and (realp x)
		  (realp y)
		  (not (= x y)))
	     (not (= (- x y) 0)))
    )
  )

 (local
  (defthm lemma-5
    (implies (and (standardp x)
		  (inside-interval-p x (f1-domain))
		  (inside-interval-p y (f1-domain))
		  (i-close x y) (not (= x y)))
	     (= (/ (- (f1 x) (f1 y)) (- x y)) (- (square (rad)) (* 1/3 (+ (square x) (* x y) (square y)))))
	     )
    :hints (("Goal"
	     :use ((:instance lemma-1)
		   (:instance lemma-2
			      (x (square (rad)))
			      (z (- x y))
			      (y (+ (square x) (* x y) (square y)))
			      )
		   (:instance f1-domain-real (x x))
		   (:instance f1-domain-real (x y))
		   (:instance rad-def)
		   (:instance square (x (rad)))
		   (:instance lemma-3 (x (rad)))
		   (:instance lemma-4 (x x) (y y))
		   (:instance realfix (x (* (rad) (rad))))
		   )
	     :in-theory nil
	     ))
    )
  )

 (local
  (defthm lemma-6
    (implies (and (standardp x)
		  (inside-interval-p x (f1-domain))
		  (inside-interval-p y (f1-domain))
		  (i-close x y) (not (= x y)))
	     (i-small (* 1/3 x (- x y)))
	     )
    :hints (("Goal"
	     :use ((:instance i-close)
		   (:instance standards-are-limited-forward (x x))
		   (:instance f1-domain-real (x x))
		   (:instance f1-domain-real (x y))
		   (:instance limited*small->small (x x) (y (- x y)))
		   (:instance limited*small->small (x 1/3) (y (* x (- x y))))
		   )
	     ))
    )
  )

 (local
  (defthm lemma-7
    (implies (and (standardp x)
		  (inside-interval-p x (f1-domain))
		  (inside-interval-p y (f1-domain))
		  (i-close x y) (not (= x y)))
	     (i-small (* 1/3 (+ x y) (- x y)))
	     )
    :hints (("Goal"
	     :use ((:instance i-close)
		   (:instance standards-are-limited-forward (x x))
		   (:instance f1-domain-real (x x))
		   (:instance f1-domain-real (x y))
		   (:instance i-limited-plus)
		   (:instance i-close-limited)
		   (:instance limited*small->small (x x) (y (- x y)))
		   (:instance limited*small->small (x (+ x y)) (y (- x y)))
		   (:instance limited*small->small (x 1/3) (y (* (+ x y) (- x y))))
		   )
	     ))
    )
  )
 
 (defthm f1-prime-is-derivative
   (implies (and (standardp x)
		 (inside-interval-p x (f1-domain))
		 (inside-interval-p y (f1-domain))
		 (i-close x y) (not (= x y)))
	    (i-close (/ (- (f1 x) (f1 y)) (- x y))
		     (f1-prime x)))
   :hints (("Goal"
	    :use ((:instance lemma-5)
		  (:instance lemma-6)
		  (:instance lemma-7)
		  (:instance i-small-plus (x (* 1/3 x (- x y))) (y (* 1/3 (+ x y) (- x y))))
		  (:instance i-small (x (- (+ (* (RAD) (RAD))
					      (- (* 1/3 X X))
					      (- (* 1/3 X Y))
					      (- (* 1/3 Y Y)))
					   (+ (* (RAD) (RAD)) (- (* X X))))))
		  (:instance f1-domain-real)
		  (:instance f1-domain-real (x y))
		  (:instance rad-def)
		  )
	    :in-theory (enable nsa-theory)
	    
	    ))
   )
 )

(defthm f1-prime-continuous
  (implies (and (standardp x)
		(realp x)
		(realp y)
		(i-close x y))
	   (i-close (f1-prime x) (f1-prime y)))
  :hints (("Goal"
	   :use (:instance square-is-continuous (x1 x) (x2 y))
	   :in-theory (enable nsa-theory)
	   ))
  )

(defun map-f1-prime (p)
  (if (consp p)
      (cons (f1-prime (car p))
	    (map-f1-prime (cdr p)))
    nil))

(defun riemann-f1-prime (p)
  (dotprod (deltas p)
           (map-f1-prime (cdr p)))
  )

(encapsulate
 ()
 
 (local 
  (defthm limited-riemann-f1-small-partition
    (implies (and (realp a) (standardp a)
		  (realp b) (standardp b)
		  (inside-interval-p a (f1-domain))
		  (inside-interval-p b (f1-domain))
		  (< a b))
	     (i-limited (riemann-f1-prime (make-small-partition a b))))
    
    :hints (("Goal"
	     :use (
		   (:functional-instance limited-riemann-rcfn-small-partition
					 (rcfn-domain f1-domain)
					 (riemann-rcfn riemann-f1-prime)
					 (map-rcfn map-f1-prime)
					 (rcfn f1-prime)
					 )
		   )
	     )
	    ("Subgoal 2"
	     :use ((:instance f1-prime-continuous)
		   (:instance rad-def)
		   )
	     )
	    )
    ))
 
 (local (in-theory (disable riemann-f1-prime)))
 
 (defun-std strict-int-f1-prime (a b)
   (if (and (realp a)
	    (realp b)
	    (inside-interval-p a (f1-domain))
	    (inside-interval-p b (f1-domain))
	    (< a b))
       (standard-part (riemann-f1-prime (make-small-partition a b)))
     0))
 )

(defun int-f1-prime (a b)
  (if (<= a b)
      (strict-int-f1-prime a b)
    (- (strict-int-f1-prime b a))))


(defthm apply-ftc-2-vol
  (implies (and (inside-interval-p a (f1-domain))
		(inside-interval-p b (f1-domain)))
	   (equal (int-f1-prime a b)
		  (- (f1 b)
		     (f1 a))))
  :hints (("Goal"
	   :use (
		 (:functional-instance ftc-2
				       (rcdfn-domain f1-domain)
				       (rcdfn f1)
				       (rcdfn-prime f1-prime)
				       (map-rcdfn-prime map-f1-prime)
				       (int-rcdfn-prime int-f1-prime)
				       (riemann-rcdfn-prime riemann-f1-prime)
				       (strict-int-rcdfn-prime strict-int-f1-prime)
				       ))
	   )
	  ("Subgoal 7"
	   :use (:instance f1-prime-continuous (x x) (y x1))
	   )
	  ("Subgoal 6"
	   :use (:instance f1-prime-is-derivative (x x) (y x1))
	   )
	  ))

(defun volume-of-a-sphere ()
  (* 2 (acl2-pi) (int-f1-prime 0 (rad)))
  )

(encapsulate
 ()
 (local (include-book "/Users/jagadishbapanapally/Documents/acl2-8.2/acl2-sources/books/arithmetic/top-with-meta"))
 (defthm volume-of-a-sphere-equals
   (= (volume-of-a-sphere) (* 4 (acl2-pi) (rad) (rad) (rad) 1/3))
   :hints (("Goal"
	    :use ((:instance apply-ftc-2-vol (a 0) (b (rad)))
		  (:instance rad-def)
		  )
	    :in-theory (enable nsa-theory interval-definition-theory)
	    ))
   )
 )
