(in-package "ACL2")

(include-book "/Users/jagadishbapanapally/Documents/acl2-8.2/acl2-sources/books/nonstd/nsa/trig")
(include-book "/Users/jagadishbapanapally/Documents/acl2-8.2/acl2-sources/books/nonstd/integrals/ftc-2")
(include-book "/Users/jagadishbapanapally/Documents/acl2-8.2/acl2-sources/books/nonstd/nsa/inverse-square")
(include-book "/Users/jagadishbapanapally/Documents/acl2-8.2/acl2-sources/books/nonstd/workshops/2011/reid-gamboa-differentiator/support/sin-cos-minimal")

(encapsulate 
 ((rad() t))
 (local (defun rad() 1))
 (defthm rad-def
   (and (realp (rad))
	(standardp (rad))
	(>= (rad) 0)))
 )

(defun s-domain () (interval 0 (acl2-pi)))

					;(defun v-domain () (interval 0 (* 2 (acl2-pi))))

(defun sphere-x (x)
  (* (rad) (acl2-cosine x))
  )

(defun sphere-y (x)
  (* (rad) (acl2-sine x))
  )

(defun sx-derivative (x)
  (* (- 1) (rad) (acl2-sine x)) 
  )

(defun sy-derivative (x)
  (* (rad) (acl2-cosine x)) 
  )

(encapsulate
 ()

 (defthm acl2-number-der-x
   (and (acl2-numberp (* (rad) (/ (- (acl2-cosine x) (acl2-cosine y)) (- x y))))
	(acl2-numberp (* (rad) (- (acl2-sine x))))
	)
   )

 (defthm sx-der-lemma
   (implies (and (standardp x)
		 (realp x)
		 (realp y)
		 (i-close x y)
		 (not (= x y))
		 )
	    (i-close (/ (- (sphere-x x) (sphere-x y)) (- x y)) (sx-derivative x))
	    )
   :hints (("Goal"
	    :use ((:instance rad-def)
		  (:instance i-close (x (* (rad) (/ (- (acl2-cosine x) (acl2-cosine y)) (- x y))))
			     (y (* (rad) (- (acl2-sine x)))))
		  (:instance limited*small->small (x (rad))  (y (- (/ (- (acl2-cosine x) (acl2-cosine y)) (- x y))
								   (- (acl2-sine x)))))
		  (:instance acl2-number-der-x)
		  (:instance i-close (x  (/ (- (acl2-cosine x) (acl2-cosine y)) (- x y)))
			     (y (- (acl2-sine x))))     
		  (:instance standards-are-limited-forward (x (rad)))
		  (:instance acl2-cosine-derivative (x x) (y y)))
	    )))

 (defthm acl2-number-der-y
   (and (acl2-numberp (* (rad) (/ (- (acl2-sine x) (acl2-sine y)) (- x y))))
	(acl2-numberp (* (rad) (acl2-cosine x))))
   )

 (defthm sy-der-lemma
   (implies (and (standardp x)
		 (realp x)
		 (realp y)
		 (i-close x y)
		 (not (= x y))
		 )
	    (i-close (/ (- (sphere-y x) (sphere-y y)) (- x y)) (sy-derivative x))
	    )
   :hints (("Goal"
	    :use ((:instance rad-def)
		  (:instance i-close (x (* (rad) (/ (- (acl2-sine x) (acl2-sine y)) (- x y))))
			     (y (* (rad) (acl2-cosine x))))
		  (:instance limited*small->small (x (rad))  (y (- (/ (- (acl2-sine x) (acl2-sine y)) (- x y))
								   (acl2-cosine x))))
		  (:instance acl2-number-der-y)
		  (:instance i-close (x  (/ (- (acl2-sine x) (acl2-sine y)) (- x y)))
			     (y (acl2-cosine x)))     
		  (:instance standards-are-limited-forward (x (rad)))
		  (:instance acl2-sine-derivative (x x) (y y)))
	    )))

 (local
  (defthm lemma-1
    (implies (and (realp x)
		  (realp y)
		  (realp z))
	     (= (+ (* x y) (* x z)) (* x (+ y z)))
	     )
    )
  )
 
 (local
  (defthm rad*norm
    (implies (realp x)
	     (= (+ (* (rad) (rad) (square (acl2-sine x))) (* (rad) (rad) (square (acl2-cosine x)))) (* (rad) (rad))))
    :hints (("Goal"
	     :use ((:instance sin**2+cos**2)
		   (:instance rad-def)
		   (:instance lemma-1 (x (* (rad) (rad))) (y (square (acl2-sine x))) (z (square (acl2-cosine x))))
		   )
	     ))
    )
  )

 (defthm norm-of-der
   (implies (realp x)
	    (= (acl2-sqrt (+ (square (sx-derivative x)) (square (sy-derivative x)))) (rad)))
   :hints (("Goal"
	    :use ((:instance sin**2+cos**2)
		  (:instance rad-def)
		  (:instance rad*norm)
		  (:instance y*y=x->y=sqrt-x (x (* rad rad)) (y (rad)))
		  )
	    ))
   )
 )


(defun f1-prime (x)
  (if (inside-interval-p x (s-domain))
      (* (rad) (acl2-sine x) (acl2-sqrt (+ (square (sx-derivative x)) (square (sy-derivative x)))))
    0)
  )

(defun f1 (x)
  (if (inside-interval-p x (s-domain))
      (- (* (rad) (rad) (acl2-cosine x)))
    0)
  )

(defthm intervalp-s-domain
  (interval-p (s-domain)))

(defthm s-domain-real
  (implies (inside-interval-p x (s-domain))
	   (realp x)))

(defthm f1-prime-real
  (realp (f1-prime x))
  )

(defthm f1-real
  (realp (f1 x))
  )

(defthm s-domain-non-trivial
  (or (null (interval-left-endpoint (s-domain)))
      (null (interval-right-endpoint (s-domain)))
      (< (interval-left-endpoint (s-domain))
	 (interval-right-endpoint (s-domain))))
  :rule-classes nil)

(encapsulate
 ()
 (local (include-book "/Users/jagadishbapanapally/Documents/acl2-8.2/acl2-sources/books/arithmetic/top-with-meta" :dir :system))

 (defthm f1-prime-is-derivative
   (implies (and (standardp x)
		 (inside-interval-p x (s-domain))
		 (inside-interval-p y (s-domain))
		 (i-close x y)
		 (not (= x y))
		 )
	    (i-close (/ (- (f1 x) (f1 y)) (- x y)) (f1-prime x))
	    )
   :hints (("Goal"
	    :use (
					;(:instance acl2-cosine-derivative (x x) (y y))
		  (:instance norm-of-der)
		  (:instance sx-der-lemma)
		  (:instance rad-def)
		  (:instance standards-are-limited-forward (x (- (rad))))
					;(:instance sy-der-lemma)
		  (:instance limited*small->small (x (- (rad))) (y (- (/ (- (sphere-x x) (sphere-x y)) (- x y)) (sx-derivative x))))
		  (:instance i-close (x (/ (- (f1 x) (f1 y)) (- x y))) (y (f1-prime x)))
		  (:instance i-small-uminus (x (+ (* (RAD) (RAD) (ACL2-SINE X))
						  (* (RAD)
						     (RAD)
						     (ACL2-COSINE X)
						     (/ (+ X (- Y))))
						  (- (* (RAD)
							(RAD)
							(ACL2-COSINE Y)
							(/ (+ X (- Y))))))))
		  (:instance s-domain-real)
		  (:instance s-domain-real (x y))
		  )
	    :in-theory (enable i-close)
	    ))
   )
 
 (defthm f1-prime-continuous
   (implies (and (standardp x)
		 (inside-interval-p x (s-domain))
		 (i-close x y)
		 (inside-interval-p y (s-domain)))
	    (i-close (f1-prime x)
		     (f1-prime y)))
   :hints (("Goal"
	    :use ((:instance sine-continuous (x x) (y y))
		  (:instance standards-are-limited-forward (x (rad)))
		  (:instance norm-of-der)
		  (:instance norm-of-der (x y))
		  (:instance s-domain-real)
		  (:instance s-domain-real (x y))
		  (:instance i-limited-times (x (rad)) (y (rad)))
		  (:instance i-close (x (acl2-sine x)) (y (acl2-sine y)))
		  (:instance limited*small->small (x (* (rad) (rad))) (y (- (acl2-sine x) (acl2-sine y))))
		  )
	    :in-theory (enable i-close)
	    ))
   )
 )

(defun map-f1-prime (p)
  (if (consp p)
      (cons (f1-prime (car p))
	    (map-f1-prime (cdr p)))
    nil))

(defun riemann-f1-prime (p)
  (dotprod (deltas p)
	   (map-f1-prime (cdr p))))


(encapsulate
 nil

 (local (include-book "/Users/jagadishbapanapally/Documents/acl2-8.2/acl2-sources/books/arithmetic/top-with-meta" :dir :system))

 (local
  (defthm limited-riemann-f1-prime-small-partition
    (implies (and (realp a) (standardp a)
		  (realp b) (standardp b)
		  (inside-interval-p a (s-domain))
		  (inside-interval-p b (s-domain))
		  (< a b))
	     (i-limited (riemann-f1-prime (make-small-partition a b))))
    :hints (("Goal"
	     :use (:functional-instance limited-riemann-rcfn-small-partition
					(rcfn-domain s-domain)
					(rcfn f1-prime)
					(map-rcfn map-f1-prime)
					(riemann-rcfn riemann-f1-prime)))
	    ("Subgoal 2"
	     :use ((:instance s-domain-non-trivial)))
	    
	    ("Subgoal 4"
	     :use ((:instance norm-of-der)
		   (:instance norm-of-der (x y))
		   (:instance f1-prime-continuous)))
	    
	    ("Subgoal 3"
	     :use ((:instance norm-of-der)
		   (:instance norm-of-der (x y))
		   (:instance rad-def)
		   (:instance f1-prime-continuous)))
					;(:instance f1-prime-continuous)
	    )))

 (local (in-theory (disable riemann-f1-prime)))



 (defun-std strict-int-f1-prime (a b)
   (if (and (realp a)
	    (realp b)
	    (inside-interval-p a (s-domain))
	    (inside-interval-p b (s-domain))
	    (< a b))
       (standard-part (riemann-f1-prime (make-small-partition a b)))
     0))
 )

(defun int-f1-prime (a b)
  (if (<= a b)
      (strict-int-f1-prime a b)
    (- (strict-int-f1-prime b a))))

(defthm apply-ftc-2-s-area
  (implies (and (inside-interval-p a (s-domain))
		(inside-interval-p b (s-domain)))
	   (equal (int-f1-prime a b)
		  (- (f1 b)
		     (f1 a))))
  :hints (("Goal"
	   :use (
		 (:functional-instance ftc-2
				       (rcdfn-domain s-domain)
				       (rcdfn f1)
				       (rcdfn-prime f1-prime)
				       (map-rcdfn-prime map-f1-prime)
				       (int-rcdfn-prime int-f1-prime)
				       (riemann-rcdfn-prime riemann-f1-prime)
				       (strict-int-rcdfn-prime strict-int-f1-prime)
				       ))
	   )
					;("Subgoal 7"
					;:use (:instance f1-prime-continuous (x x) (y x1))
					;)
	  ("Subgoal 7"
	   :use ((:instance norm-of-der)
		 (:instance f1-prime-is-derivative (x x) (y x1)))
	   )
	  ("Subgoal 8"
	   :use ((:instance norm-of-der)
		 (:instance f1-prime-continuous (x x) (y x1))))
	  ))

(defun surface-area-of-a-sphere ()
  (* 2 (acl2-pi) (int-f1-prime 0 (acl2-pi)))
  )

(encapsulate
 ()
 (local (include-book "/Users/jagadishbapanapally/Documents/acl2-8.2/acl2-sources/books/arithmetic/top-with-meta"))
 (defthm surface-area-of-a-sphere-equals
   (= (surface-area-of-a-sphere) (* 4 (acl2-pi) (rad) (rad)))
   :hints (("Goal"
	    :use ((:instance apply-ftc-2-s-area (a 0) (b (acl2-pi)))
		  (:instance rad-def)
		  (:instance pi-between-2-4)
		  )
	    :in-theory (enable nsa-theory interval-definition-theory)
	    ))
   )
 )
