;;;;test


(encapsulate
 ()
 (defthmd i-small-plus-lemma
   (implies (i-close x y)
	    (i-small (- x y))))
 
 (defthmd i-close-plus-lemma
   (implies (i-small (- x y))
	    (i-close (- x y) 0)))
 
 (defthmd i-close-plus-lemma-1
   (implies (and (acl2-numberp x)
		 (acl2-numberp y)
		 (i-close (- x y) 0))
	    (i-close x y)
	    ))
 
 (defthmd i-close-plus-lemma-2
   (implies (and (acl2-numberp x)
		 (acl2-numberp y)
		 (i-small (- x y))
		 )
	    (i-close x y))
   
   :hints (("Goal"
	    :use (
		  (:instance i-close-plus-lemma(x x) )
		  (:instance i-close-plus-lemma-1(x x))
		  )
	    )))

 (defthmd i-small-limited-lemma
   (implies (and (acl2-numberp x) (i-small x))
	    (i-limited x))
   )

 (defthmd close-stdpart-lemma1
   (implies (and (i-close x y)
		 (i-limited x))
	    (equal (standard-part x) (standard-part y)))
   )

 (defthmd close-stdpart-lemma2-1
   (implies (and  (standardp x)
		  (acl2-numberp x)
		  )
	    (equal (standard-part x) x)
	    )
   )

 (defthmd close-stdpart-lemma2
   (implies (and (i-close x y)
		 (standardp x)
		 (acl2-numberp x)
		 (acl2-numberp y))
	    (equal (standard-part y) x))
   :hints (("Goal"
	    :use ((:instance close-stdpart-lemma1 (x x) (y y))
		  (:instance close-stdpart-lemma2-1 (x x))
		  )))
   )

 (defthmd i-close-lemma1
   (implies (and (i-close x y)
		 (equal x z))
	    (i-close y z)
	    )
   
   )

 (defthmd realp-i-l
   (realp (i-large-integer))
   )

 (defthmd x+eps-real
   (implies (and (realp x)
		 (realp eps)
		 (i-small eps))
	    (realp (+ eps x))
	    )
   
   )

 )

(local (include-book "/Users/jagadishbapanapally/Documents/acl2-8.2/acl2-sources/books/arithmetic/top-with-meta" :dir :system))
(local (include-book "/Users/jagadishbapanapally/Documents/acl2-8.2/acl2-sources/books/nonstd/nsa/nsa" :dir :system))

(defthmd i-close-lemma2
  (implies (and (acl2-numberp a)
		(acl2-numberp b)
		(acl2-numberp x)
		(acl2-numberp y)
		(i-close a b)
		(i-close x y)
		(i-limited a)
		(i-limited y)
		)
	   (i-small (+ (* a (- x y)) (* y (- a b))))
	   )
  :hints (("Goal"
	   :use ((:instance i-small-plus-lemma
			    (x x)
			    (y y))
		 (:instance i-small-plus-lemma
			    (x a)
			    (y b))
		 (:instance small*limited->small
			    (x (- x y))
			    (y a))
		 (:instance small*limited->small
			    (x (- a b))
			    (y y))
		 (:instance i-small-plus
			    (x (* a (- x y)))
			    (y (* y (- a b))))
		 )
					; :in-theory nil
	   ))
  )

(defthmd i-close-lemma3
  (implies (and (acl2-numberp a)
		(acl2-numberp b)
		(acl2-numberp x)
		(acl2-numberp y)
		(i-close a b)
		(i-close x y)
		(i-limited a)
		(i-limited y)
		)
	   (i-close  (* a x) (* b y))
	   )
  :hints (("Goal" 
	   :use ((:instance i-close-lemma2)
		 (:instance i-close-plus-lemma-2
			    (x (* a x))
			    (y (* b y)))
		 )
	   ))
  )

(local (include-book "/Users/jagadishbapanapally/Documents/acl2-8.2/acl2-sources/books/nonstd/integrals/ftc-2" :dir :system))
(local (include-book "/Users/jagadishbapanapally/Documents/acl2-8.2/acl2-sources/books/nonstd/nsa/chain-rule" :dir :system))
(local (include-book "/Users/jagadishbapanapally/Documents/acl2-8.2/acl2-sources/books/nonstd/integrals/continuous-function" :dir :system))
(local (include-book "/Users/jagadishbapanapally/Documents/acl2-8.2/acl2-sources/books/nonstd/integrals/ftc-1" :dir :system))
(local (include-book "/Users/jagadishbapanapally/Documents/acl2-8.2/acl2-sources/books/nonstd/nsa/continuity-product" :dir :system))

(encapsulate
 (
  ((fi *) => *)
  ((F-o-fi-domain) => *)
  ((F-prime *) => *)
  ((fi-prime *) => *)
  (fi-range () t)
  (consta () t)
  )

 (local (defun fi (x) (declare (ignore x)) 0))
 (local (defun F-o-fi-domain () (interval 0 1)))
 (local (defun F-prime (x) (declare (ignore x)) 0))
 (local (defun fi-prime (x) (declare (ignore x)) 0))
 (local (defun fi-range () (interval 0 1)))
 (local (defun consta() 1))
 
 (defthmd consta-def
   (and (inside-interval-p (consta) (fi-range))
	(standardp (consta))
	)
   )

 (defthm F-prime-real
   (realp (F-prime x))
   :rule-classes (:rewrite :type-prescription))

 (defthm F-prime-continuous
   (implies (and (standardp x)
		 (inside-interval-p x (fi-range))
		 (i-close x x1)
		 (inside-interval-p x1 (fi-range)))
	    (i-close (F-prime x)
		     (F-prime x1))))

 (defthm fi-real
   (realp (fi x))
   :rule-classes (:rewrite :type-prescription))

 (defthm fi-prime-real
   (realp (fi-prime x))
   :rule-classes (:rewrite :type-prescription))

 (local (defthm i-close-0-lemma
	  (IMPLIES (AND (STANDARDP X)
			(INSIDE-INTERVAL-P x '(0 . 1))
			(INSIDE-INTERVAL-P x1 '(0 . 1))
			(I-CLOSE x x1)
			(NOT (EQUAL X X1)))
		   (equal (* 0 (/ (+ x (- x1)))) 0))
	  ))
 
 (defthm fi-prime-is-derivative
   (implies (and (standardp x)
		 (inside-interval-p x (f-o-fi-domain))
		 (inside-interval-p x1 (f-o-fi-domain))
		 (i-close x x1) (not (= x x1)))
	    (i-close (/ (- (fi x) (fi x1)) (- x x1))
		     (fi-prime x)))
   :hints (("Goal"
	    :use (
		  (:instance i-close-0-lemma (x x) (x1 x1))
		  )
	    ))
   )

 (defthm fi-prime-continuous
   (implies (and (standardp x)
		 (inside-interval-p x (f-o-fi-domain))
		 (i-close x x1)
		 (inside-interval-p x1 (f-o-fi-domain)))
	    (i-close (fi-prime x)
		     (fi-prime x1))))

 (defthm intervalp-fi-range
   (interval-p (fi-range))
   :rule-classes (:type-prescription :rewrite))

 (defthm fi-range-real
   (implies (inside-interval-p x (fi-range))
	    (realp x)))

 (defthm fi-range-non-trivial
   (or (null (interval-left-endpoint (fi-range)))
       (null (interval-right-endpoint (fi-range)))
       (< (interval-left-endpoint (fi-range))
	  (interval-right-endpoint (fi-range))))
   :rule-classes nil)

 (defthm fi-differentiable
   (implies (and (standardp x)
		 (inside-interval-p x (f-o-fi-domain))
		 (inside-interval-p y1 (f-o-fi-domain))
		 (inside-interval-p y2 (f-o-fi-domain))
		 (i-close x y1) (not (= x y1))
		 (i-close x y2) (not (= x y2)))
	    (and (i-limited (/ (- (fi x) (fi y1)) (- x y1)))
		 (i-close (/ (- (fi x) (fi y1)) (- x y1))
			  (/ (- (fi x) (fi y2)) (- x y2))))))

 (defthm intervalp-F-o-fi-domain
   (interval-p (F-o-fi-domain))
   :rule-classes (:type-prescription :rewrite))

 (defthm F-o-fi-domain-real
   (implies (inside-interval-p x (F-o-fi-domain))
	    (realp x))
   :rule-classes (:forward-chaining))

 (defthm F-o-fi-domain-non-trivial
   (or (null (interval-left-endpoint (F-o-fi-domain)))
       (null (interval-right-endpoint (F-o-fi-domain)))
       (< (interval-left-endpoint (F-o-fi-domain))
	  (interval-right-endpoint (F-o-fi-domain))))
   :rule-classes nil)

 (defthm fi-range-in-domain-of-f-o-fi
   (implies (inside-interval-p x (f-o-fi-domain))
	    (inside-interval-p (fi x) (fi-range))))
 
 )


(local
 (defthm-std standard-f-prime
   (implies (standardp x)
	    (standardp (f-prime x)))))

(local
 (defthm-std standard-fi-prime
   (implies (standardp x)
	    (standardp (fi-prime x)))))



(encapsulate
 (
  ((F-o-fi *) => *)
  ((differential-cr-f * *) => *)
  ((differential-cr-fi * *) => *)
  ((F *) => *)
  ((map-f-prime-1 *) => *)
  ((riemann-f-prime-1 *) => *)
  ((strict-int-f-prime-1 * *) => *)
  ((int-f-prime-1 * *) => *)
  )

 (local
  (defun map-f-prime-1 (p)
    (if (consp p)
	(cons (f-prime (car p))
	      (map-f-prime-1 (cdr p)))
      nil))
  )

 (local
  (defun riemann-f-prime-1 (p)
    (dotprod (deltas p)
	     (map-f-prime-1 (cdr p))))
  )

 (local
  (defthm limited-riemann-f-prime-small-partition
    (implies (and (realp a) (standardp a)
		  (realp b) (standardp b)
		  (inside-interval-p a (fi-range))
		  (inside-interval-p b (fi-range))
		  (< a b))
	     (i-limited (riemann-f-prime-1 (make-small-partition a b))))
    :hints (("Goal"
	     :use (
		   (:functional-instance limited-riemann-rcfn-small-partition
					 (rcfn-domain fi-range)
					 (riemann-rcfn riemann-f-prime-1)
					 (map-rcfn map-f-prime-1)
					 (rcfn f-prime)
					 )
		   )
	     :in-theory (enable interval-definition-theory)
	     )
	    ("Subgoal 1"
	     :use ((:instance fi-range-non-trivial))
	     )
	    )
    )
  )

 (local (in-theory (disable riemann-f-prime-1)))
 (local (defun-std strict-int-f-prime-1 (a b)
	  (if (and (realp a)
		   (realp b)
		   (inside-interval-p a (fi-range))
		   (inside-interval-p b (fi-range))
		   (< a b))
	      (standard-part (riemann-f-prime-1 (make-small-partition a b)))
	    0)))

 (local
  (defun int-f-prime-1 (a b)
    (if (<= a b)
	(strict-int-f-prime-1 a b)
      (- (strict-int-f-prime-1 b a))))
  )


 (local
  (defthm ftc-1-fprime
    (implies (and (inside-interval-p a (fi-range))
		  (inside-interval-p b (fi-range))
		  (inside-interval-p c (fi-range))
		  (standardp b)
		  (i-close b c)
		  (not (equal b c)))
	     (i-close (/ (- (int-f-prime-1 a b) (int-f-prime-1 a c))
			 (- b c))
		      (f-prime b)))
    :hints (("Goal"
	     :use ((:functional-instance ftc-1
					 (int-rcfn int-f-prime-1)
					 (strict-int-rcfn strict-int-f-prime-1)
					 (map-rcfn map-f-prime-1)
					 (riemann-rcfn riemann-f-prime-1)
					 (rcfn f-prime)
					 (rcfn-domain fi-range)
					 )
		   )
	     ))
    )
  )

 (local
  (defthm realp-strict-int-f-prime
    (implies (and (realp a)
		  (realp b))
	     (realp (strict-int-f-prime-1 a b)))
    :hints (("Goal"
	     :by (:functional-instance realp-strict-int-rcfn
				       (strict-int-rcfn strict-int-f-prime-1)
				       (rcfn-domain fi-range)
				       (rcfn f-prime)
				       (riemann-rcfn riemann-f-prime-1)
				       (map-rcfn map-f-prime-1))))))

 (local
  (defthm-std realp-strict-int-f-prime-stronger
    (realp (strict-int-f-prime-1 a b))
    :hints (("Goal"
	     :cases ((not (realp a))
		     (not (realp b))))
	    ("Subgoal 3"
	     :use ((:instance realp-strict-int-f-prime)))
	    )))

 (local
  (defthm realp-int-f-prime
    (realp (int-f-prime-1 a b))
    )
  )

 (local
  (defun f(x)
    (int-f-prime-1 (consta) x)
    )
  )

 (local
  (encapsulate
   nil

   (local
    (defthm int-f-prime-1-lemma-1
      (implies 
       (standardp x)				
       (standardp (int-f-prime-1 (consta) x))
       )
      :hints (("Goal"
	       :use (
		     (:instance fi-range-real (x x))
		     (:instance consta-def)
		     )
	       ))
      )
    )

   (local
    (in-theory '(int-f-prime-1-lemma-1)))
   (defun-std  f (x)
     (int-f-prime-1 (consta) x)
     )
   )
  )
 
 (defthm F-real
   (realp (F x))
   :hints (("Goal"
	    :use (
		  (:definition f)
		  (:instance realp-int-f-prime
			     (a (consta))
			     (b x))
		  )
	    :in-theory (disable int-f-prime-1)
	    ))
   )

 (defthm F-prime-is-derivative
   (implies (and (standardp x)
		 (inside-interval-p x (fi-range))
		 (inside-interval-p x1 (fi-range))
		 (i-close x x1) (not (= x x1)))
	    (i-close (/ (- (F x) (F x1)) (- x x1))
		     (F-prime x)))
   :hints (("Goal"
	    :use ((:instance ftc-1-fprime
			     (b x)
			     (a (consta))
			     (c x1)
			     )
		  (:instance consta-def)
		  )
	    ))
   )
 
 (defthm f-differentiable
   (implies (and (standardp x)
		 (inside-interval-p x (fi-range))
		 (inside-interval-p y1 (fi-range))
		 (inside-interval-p y2 (fi-range))
		 (i-close x y1) (not (= x y1))
		 (i-close x y2) (not (= x y2)))
	    (and (i-limited (/ (- (f x) (f y1)) (- x y1)))
		 (i-close (/ (- (f x) (f y1)) (- x y1))
			  (/ (- (f x) (f y2)) (- x y2)))))
   :hints (("Goal"
	    :use ((:instance F-prime-is-derivative
			     (x x)
			     (x1 y1)
			     )
		  (:instance F-prime-is-derivative
			     (x x)
			     (x1 y2)
			     )
		  (:instance standard-f-prime)
		  (:instance standards-are-limited-forward
			     (x (f-prime x))
			     )
		  )
	    ))
   )

 (local
  (defun F-o-fi (x)
    (F (fi x))))

 (local
  (defun differential-cr-f (x eps)
    (/ (- (f (+ x eps)) (f x)) eps)))
 (local
  (defun differential-cr-fi (x eps)
    (/ (- (fi (+ x eps)) (fi x)) eps)))

 (defthm F-o-fi-equal
   (implies (inside-interval-p x (F-o-fi-domain))
	    (equal (F-o-fi x) (F (fi x))))
   )

 (defthm F-o-fi-real
   (realp (F-o-fi x))
   :rule-classes (:rewrite :type-prescription))

 (defthm differential-cr-f-definition
   (implies (and (inside-interval-p x (fi-range))
		 (inside-interval-p (+ x eps) (fi-range)))
	    (equal (differential-cr-f x eps)
		   (/ (- (f (+ x eps)) (f x)) eps))))

 (defthm differential-cr-fi-definition
   (implies (and (inside-interval-p x (f-o-fi-domain))
		 (inside-interval-p (+ x eps) (f-o-fi-domain)))
	    (equal (differential-cr-fi x eps)
		   (/ (- (fi (+ x eps)) (fi x)) eps))))
 )

(local
 (defthm-std standard-fi-range
   (standardp (fi-range))))

(local
 (defthm-std standard-fi-range-left-endpoint
   (standardp (interval-left-endpoint (fi-range)))))

(local
 (defthm-std standard-fi-range-right-endpoint
   (standardp (interval-right-endpoint (fi-range)))))

(local
 (defthm standard-part-eps
   (implies (i-small eps)
	    (equal (standard-part eps) 0))
   :hints (("Goal"
	    :in-theory (enable i-small)))
   ))

(local
 (defthmd x-in-interval-implies-x+-eps-in-interval-1
   (implies (and (realp x)
		 (standardp x)
		 (realp x1)
		 (standardp x1)
		 (< x1 x)
		 (realp eps)
		 (i-small eps))
	    (< x1
	       (+ x eps)))
   :hints (("Goal"
	    :use ((:instance standard-part-<-2
			     (x x1)
			     (y (+ x eps))))))))

(local
 (defthmd x-in-interval-implies-x+-eps-in-interval-2
   (implies (and (realp x)
		 (standardp x)
		 (realp x2)
		 (standardp x2)
		 (< x x2)
		 (realp eps)
		 (i-small eps))
	    (< (+ x eps)
	       x2))
   :hints (("Goal"
	    :use ((:instance standard-part-<-2
			     (x (+ x eps))
			     (y x2)))))))

(local
 (defthm x-in-trivial-interval
   (implies (and (realp x)
		 (interval-p interval)
		 (not (realp (interval-left-endpoint interval)))
		 (not (realp (interval-right-endpoint interval))))
	    (inside-interval-p x interval))
   :hints (("Goal"
	    :in-theory (enable interval-definition-theory)))
   ))

(local
 (defthm x-in-left-trivial-interval
   (implies (and (realp x)
		 (interval-p interval)
		 (not (realp (interval-left-endpoint interval)))
		 (inside-interval-p y interval)
		 (< x y))
	    (inside-interval-p x interval))
   :hints (("Goal"
	    :in-theory (enable interval-definition-theory)))
   ))

(local
 (defthm x-in-right-trivial-interval
   (implies (and (realp x)
		 (interval-p interval)
		 (not (realp (interval-right-endpoint interval)))
		 (inside-interval-p y interval)
		 (> x y))
	    (inside-interval-p x interval))
   :hints (("Goal"
	    :in-theory (enable interval-definition-theory)))
   ))

(local
 (defthm nil-not-in-interval
   (implies (and (not x)
		 (interval-p interval))
	    (not (inside-interval-p x interval)))
   :hints (("Goal"
	    :in-theory (enable interval-definition-theory)))
   ))

(local
 (defthm x-in-interval-implies-x+-eps-in-interval
   (implies (and (inside-interval-p x (fi-range))
		 (standardp x)
		 (realp eps)
		 (i-small eps)
		 (< 0 eps))
	    (or (inside-interval-p (+ x eps) (fi-range))
		(inside-interval-p (- x eps) (fi-range))))
   :hints (("Goal"
	    :use (
		  (:instance fi-range-real)
		  (:instance intervalp-fi-range)
		  (:instance fi-range-non-trivial)
		  (:instance x-in-interval-implies-x+-eps-in-interval-1
			     (x x)
			     (eps eps)
			     (x1 (interval-left-endpoint (fi-range))))
		  (:instance x-in-interval-implies-x+-eps-in-interval-1
			     (x x)
			     (eps (- eps))
			     (x1 (interval-left-endpoint (fi-range))))
		  (:instance x-in-interval-implies-x+-eps-in-interval-2
			     (x x)
			     (eps eps)
			     (x2 (interval-right-endpoint (fi-range))))
		  (:instance x-in-interval-implies-x+-eps-in-interval-2
			     (x x)
			     (eps (- eps))
			     (x2 (interval-right-endpoint (fi-range))))
		  )
	    )
	   ("Subgoal 9"
	    :in-theory (enable interval-definition-theory))
	   ("Subgoal 7"
	    :in-theory (enable interval-definition-theory))
	   ("Subgoal 6"
	    :in-theory (enable interval-definition-theory))
	   ("Subgoal 3"
	    :in-theory (enable interval-definition-theory))
	   ("Subgoal 1"
	    :in-theory (enable interval-definition-theory))
	   )
   ))

(local
 (defthm F-prime-definition
   (implies (and (inside-interval-p x (fi-range))
		 (standardp x))
	    (equal (F-prime x)
		   (if (inside-interval-p (+ x (/ (i-large-integer))) (fi-range))
		       (standard-part (differential-cr-f x (/ (i-large-integer))))
		     (if (inside-interval-p (- x (/ (i-large-integer))) (fi-range))
			 (standard-part (differential-cr-f x (- (/ (i-large-integer)))))
		       'error))))

   :hints (("Goal"
	    :use (
		  (:instance standard-f-prime)
		  (:instance x-in-interval-implies-x+-eps-in-interval
			     (x x)
			     (eps (/ (i-large-integer))))
		  (:instance F-prime-is-derivative (x x)
			     (x1 (+ x (/ (I-LARGE-INTEGER))))
			     )
		  (:instance F-prime-is-derivative (x x)
			     (x1 (- x (/ (I-LARGE-INTEGER))))
			     )
		  (:instance i-close-plus-lemma-2
			     (x x)
			     (y (+ (- (/ (I-LARGE-INTEGER))) X))
			     )
		  (:instance i-close-plus-lemma-2
			     (y x)
			     (x  (+ (/ (I-LARGE-INTEGER)) x))
			     )
		  (:instance close-stdpart-lemma2
			     (x (f-prime x))
			     (y (differential-cr-f x (/ (i-large-integer))))
			     )
		  (:instance close-stdpart-lemma2
			     (x (f-prime x))
			     (y (differential-cr-f x (- (/ (i-large-integer)))))
			     )
		  )
	    ))
   )
 )

(local
 (defthm-std standard-f-o-fi-domain
   (standardp (f-o-fi-domain))))

(local
 (defthm-std standard-f-o-fi-domain-left-endpoint
   (standardp (interval-left-endpoint (f-o-fi-domain)))))

(local
 (defthm-std standard-f-o-fi-domain-right-endpoint
   (standardp (interval-right-endpoint (f-o-fi-domain)))))

(local
 (defthm x-in-interval-implies-x+-eps-in-interval-f-o-fi-domain
   (implies (and (inside-interval-p x (f-o-fi-domain))
		 (standardp x)
		 (realp eps)
		 (i-small eps)
		 (< 0 eps))
	    (or (inside-interval-p (+ x eps) (f-o-fi-domain))
		(inside-interval-p (- x eps) (f-o-fi-domain))))
   :hints (("Goal"
	    :use (
		  (:instance f-o-fi-domain-real)
		  (:instance intervalp-f-o-fi-domain)
		  (:instance f-o-fi-domain-non-trivial)
		  (:instance x-in-interval-implies-x+-eps-in-interval-1
			     (x x)
			     (eps eps)
			     (x1 (interval-left-endpoint (f-o-fi-domain))))
		  (:instance x-in-interval-implies-x+-eps-in-interval-1
			     (x x)
			     (eps (- eps))
			     (x1 (interval-left-endpoint (f-o-fi-domain))))
		  (:instance x-in-interval-implies-x+-eps-in-interval-2
			     (x x)
			     (eps eps)
			     (x2 (interval-right-endpoint (f-o-fi-domain))))
		  (:instance x-in-interval-implies-x+-eps-in-interval-2
			     (x x)
			     (eps (- eps))
			     (x2 (interval-right-endpoint (f-o-fi-domain))))
		  )
	    )
	   ("Subgoal 9"
	    :in-theory (enable interval-definition-theory))
	   ("Subgoal 7"
	    :in-theory (enable interval-definition-theory))
	   ("Subgoal 6"
	    :in-theory (enable interval-definition-theory))
	   ("Subgoal 3"
	    :in-theory (enable interval-definition-theory))
	   ("Subgoal 1"
	    :in-theory (enable interval-definition-theory))
	   )
   ))

(local
 (defthm fi-prime-definition
   (implies (and (inside-interval-p x (f-o-fi-domain))
		 (standardp x))
	    (equal (fi-prime x)
		   (if (inside-interval-p (+ x (/ (i-large-integer))) (f-o-fi-domain))
		       (standard-part (differential-cr-fi x (/ (i-large-integer))))
		     (if (inside-interval-p (- x (/ (i-large-integer))) (f-o-fi-domain))
			 (standard-part (differential-cr-fi x (- (/ (i-large-integer)))))
		       'error))))

   :hints (("Goal"
	    :use (
		  (:instance standard-fi-prime)
		  (:instance x-in-interval-implies-x+-eps-in-interval-f-o-fi-domain
			     (x x)
			     (eps (/ (i-large-integer))))
		  (:instance fi-prime-is-derivative (x x)
			     (x1 (+ x (/ (I-LARGE-INTEGER))))
			     )
		  (:instance fi-prime-is-derivative (x x)
			     (x1 (- x (/ (I-LARGE-INTEGER))))
			     )
		  (:instance i-close-plus-lemma-2
			     (x x)
			     (y (+ (- (/ (I-LARGE-INTEGER))) X))
			     )
		  (:instance i-close-plus-lemma-2
			     (y x)
			     (x  (+ (/ (I-LARGE-INTEGER)) x))
			     )
		  (:instance close-stdpart-lemma2
			     (x (fi-prime x))
			     (y (differential-cr-fi x (/ (i-large-integer))))
			     )
		  (:instance close-stdpart-lemma2
			     (x (fi-prime x))
			     (y (differential-cr-fi x (- (/ (i-large-integer)))))
			     )
		  )
	    ))
   )
 )

(local 
 (defthm realp-differential-cr-f
   (implies (and (inside-interval-p x (fi-range))
		 (inside-interval-p (+ x eps) (fi-range))
		 (realp eps))
	    (realp (differential-cr-f x eps)))
   :hints (("Goal"
	    :use (:functional-instance realp-differential-rdfn
				       (differential-rdfn differential-cr-f)
				       (rdfn f)
				       (rdfn-domain fi-range)))
	   ("Subgoal 3"
	    :use (:instance f-differentiable)
	    )

	   ("Subgoal 2"
	    :use (:instance fi-range-non-trivial)
	    )

	   ("Subgoal 7"
	    :use (:instance fi-differentiable
			    (x x)
			    (y1 y1)
			    (y2 y2))
	    )
	   )
   )
 )

(local 
 (defthm differential-cr-f-limited
   (implies (and (standardp x)
		 (inside-interval-p x (fi-range))
		 (inside-interval-p (+ x eps) (fi-range))
		 (i-small eps))
	    (i-limited (differential-cr-f x eps)))
   :hints (("Goal"
	    :use ((:functional-instance differential-cr-fn1-limited
					(differential-cr-fn1 differential-cr-f)
					(cr-fn1 f)
					(cr-fn2-range fi-range)
					(cr-fn2 fi)
					(cr-fn2-domain f-o-fi-domain))
		  
		  ))
	   ("Subgoal 2"
	    :use (:instance  F-real)
	    )
	   ("Subgoal 3"
	    :use (:instance f-o-fi-domain-non-trivial)
	    )
	   ("Subgoal 4"
	    :use (:instance fi-range-non-trivial)
	    )
	   ("Subgoal 6"
	    :use (:instance f-differentiable
			    (x x)
			    (y1 y1)
			    (y2 y2))
	    )
	   ("Subgoal 7"
	    :use (:instance fi-differentiable
			    (x x)
			    (y1 y1)
			    (y2 y2))
	    )
	   ))
 )

(local (in-theory (disable differential-cr-f-definition)))
(local (in-theory (disable F-prime-definition)))

(local 
 (defthm realp-differential-cr-fi
   (implies (and (inside-interval-p x (f-o-fi-domain))
		 (inside-interval-p (+ x eps) (f-o-fi-domain))
		 (realp eps))
	    (realp (differential-cr-fi x eps)))
   :hints (("Goal"
	    :by (:functional-instance realp-differential-rdfn
				      (differential-rdfn differential-cr-fi)
				      (rdfn fi)
				      (rdfn-domain f-o-fi-domain)))


	   ("Subgoal 3"
	    :use (:instance fi-differentiable)
	    )

	   ("Subgoal 2"
	    :use (:instance f-o-fi-domain-non-trivial)
	    )

	   ("Subgoal 7"
	    :use (:instance fi-differentiable
			    (x x)
			    (y1 y1)
			    (y2 y2))
	    )
	   ))
 )

(local 
 (defthm differential-cr-fi-limited
   (implies (and (standardp x)
		 (inside-interval-p x (f-o-fi-domain))
		 (inside-interval-p (+ x eps) (f-o-fi-domain))
		 (i-small eps))
	    (i-limited (differential-cr-fi x eps)))
   :hints (("Goal"
	    :by (:functional-instance differential-rdfn-limited
				      (differential-rdfn differential-cr-fi)
				      (rdfn fi)
				      (rdfn-domain f-o-fi-domain)))))
 )

(local (in-theory (disable differential-cr-fi-definition)))
(local (in-theory (disable fi-prime-definition)))

(encapsulate
 (((differential-cr-f-o-fi * *) => *))
 (local
  (defun differential-cr-f-o-fi (x eps)
    (if (equal (fi (+ x eps)) (fi x))
	0
      (* (differential-cr-f (fi x) (- (fi (+ x eps)) (fi x)))
	 (differential-cr-fi x eps))))
  )

 (defthm differential-cr-f-o-fi-definition
   (implies (and (inside-interval-p x (f-o-fi-domain))
		 (inside-interval-p (+ x eps) (f-o-fi-domain)))
	    (equal (differential-cr-f-o-fi x eps)
		   (if (equal (fi (+ x eps)) (fi x))
		       0
		     (* (differential-cr-f (fi x) (- (fi (+ x eps)) (fi x)))
			(differential-cr-fi x eps))))))
 )


(encapsulate
 (((derivative-cr-f-o-fi *) => *))

 (local 
  (defun derivative-cr-f-o-fi (x)
    (* (F-prime (fi x))
       (fi-prime x)))
  )

 (defthm derivative-cr-f-o-fi-definition
   (implies (inside-interval-p x (f-o-fi-domain))
	    (equal (derivative-cr-f-o-fi x)
		   (* (F-prime (fi x))
		      (fi-prime x)))))
 )

(local 
 (defthm differential-cr-f-o-fi-close
   (implies (and (inside-interval-p x (f-o-fi-domain))
		 (standardp x)
		 (realp eps) (i-small eps) (not (= eps 0))
		 (inside-interval-p (+ x eps) (f-o-fi-domain))
		 (syntaxp (not (equal eps (/ (i-large-integer))))))
	    (equal (standard-part (differential-cr-f-o-fi x eps))
		   (derivative-cr-f-o-fi x)))
   :hints (("Goal"
	    :use (:functional-instance differential-cr-fn1-o-fn2-close
				       (derivative-cr-fn1-o-fn2 derivative-cr-f-o-fi)
				       (differential-cr-fn1-o-fn2 differential-cr-f-o-fi)
				       (cr-fn1-o-fn2 f-o-fi)
				       (cr-fn2-domain f-o-fi-domain)
				       (cr-fn2-range fi-range)
				       (cr-fn1 f)
				       (cr-fn2 fi)
				       (derivative-cr-fn2 fi-prime)
				       (derivative-cr-fn1 F-prime)
				       (differential-cr-fn1 differential-cr-f)
				       (differential-cr-fn2 differential-cr-fi)))

	   ("Subgoal 4"
	    :use (:instance fi-prime-definition)
	    )
	   ("Subgoal 3"
	    :use (:instance differential-cr-fi-definition)
	    )

	   ("Subgoal 2"
	    :use (:instance F-prime-definition)
	    )
	   ))
 )

(local 
 (defthm differential-cr-f-o-fi-close-1
   (implies (and (standardp x)
		 (inside-interval-p x (F-o-fi-domain))
		 (inside-interval-p x1 (F-o-fi-domain))
		 (i-close x x1) (not (= x x1)))
	    (equal (standard-part (differential-cr-f-o-fi x (- x1 x)))
		   (derivative-cr-f-o-fi x))
	    )
   :hints(("Goal"
	   :use ((:instance differential-cr-f-o-fi-close
			    (x x)
			    (eps (- x1 x))
			    )
		 (:instance i-small-plus-lemma
			    (x x1)
			    (y x))
		 )
	   ))
   )
 )

(local 
 (defthm expand-differential-cr-f-o-fi
   (implies (and (inside-interval-p x (f-o-fi-domain))
		 (inside-interval-p (+ x eps) (f-o-fi-domain)))
	    (equal (differential-cr-f-o-fi x eps)
		   (/ (- (f-o-fi (+ x eps)) (f-o-fi x)) eps)))
   :hints (("Goal"
	    :use (:functional-instance expand-differential-cr-fn1-o-fn2
				       (derivative-cr-fn1-o-fn2 derivative-cr-f-o-fi)
				       (differential-cr-fn1-o-fn2 differential-cr-f-o-fi)
				       (cr-fn1-o-fn2 f-o-fi)
				       (cr-fn2-domain f-o-fi-domain)
				       (cr-fn2-range fi-range)
				       (cr-fn1 f)
				       (cr-fn2 fi)
				       (derivative-cr-fn2 fi-prime)
				       (derivative-cr-fn1 F-prime)
				       (differential-cr-fn1 differential-cr-f)
				       (differential-cr-fn2 differential-cr-fi)))
	   )
   )
 )

(encapsulate
 nil
 (local
  (defthm lemma-1
    (implies (and 
	      (acl2-numberp a)
	      (acl2-numberp b)
	      (acl2-numberp c)
	      (acl2-numberp d))
	     (equal (/ (- a b) (- c d))
		    (/ (- b a) (- d c))
		    )
	     )
    ))

 (local
  (defthm lemma
    (implies (and 
	      (INSIDE-INTERVAL-P X (F-O-FI-DOMAIN))
	      (INSIDE-INTERVAL-P X1 (F-O-FI-DOMAIN)))
	     (equal (+ X1 X (- X1)) X)
	     )
    ))

 (defthmd expand-differential-cr-f-o-fi-1
   (implies (and (inside-interval-p x (f-o-fi-domain))
		 (inside-interval-p x1 (f-o-fi-domain)))
	    (equal (differential-cr-f-o-fi x1 (- x x1))
		   (/ (- (f-o-fi x) (f-o-fi x1)) (- x x1))))
   :hints (("Goal"
	    :use ((:instance expand-differential-cr-f-o-fi
			     (x x1)
			     (eps (- x x1))
			     )
		  (:instance F-o-fi-domain-real)
		  (:instance lemma)
		  )
	    :in-theory '(expand-differential-cr-f-o-fi)
	    ))
   )

 (defthmd expand-differential-cr-f-o-fi-2
   (implies (and (inside-interval-p x (f-o-fi-domain))
		 (inside-interval-p x1 (f-o-fi-domain)))
	    (equal (differential-cr-f-o-fi x (- x1 x))
		   (/ (- (f-o-fi x) (f-o-fi x1)) (- x x1))))
   :hints (("Goal"
	    :use ((:instance expand-differential-cr-f-o-fi-1
			     (x x1)
			     (x1 x)
			     )
		  (:instance F-o-fi-domain-real(x x))
		  (:instance F-o-fi-domain-real(x x1))
		  (:instance lemma-1
			     (a (f-o-fi x))
			     (b (f-o-fi x1))
			     (c x)
			     (d x1)
			     )
		  (:instance F-o-fi-real(x x))
		  (:instance F-o-fi-real(x x1))
		  )
	    :in-theory '(expand-differential-cr-f-o-fi-1)
	    )
	   ))
 )

(local
 (defthm differential-cr-f-o-fi-limited
   (implies (and (standardp x)
		 (inside-interval-p x (f-o-fi-domain))
		 (inside-interval-p (+ x eps) (f-o-fi-domain))
		 (i-small eps))
	    (i-limited (differential-cr-f-o-fi x eps)))

   :hints (("Goal"
	    :use (:functional-instance differential-cr-fn1-o-fn2-limited
				       (derivative-cr-fn1-o-fn2 derivative-cr-f-o-fi)
				       (differential-cr-fn1-o-fn2 differential-cr-f-o-fi)
				       (cr-fn1-o-fn2 f-o-fi)
				       (cr-fn2-domain f-o-fi-domain)
				       (cr-fn2-range fi-range)
				       (cr-fn1 f)
				       (cr-fn2 fi)
				       (derivative-cr-fn2 fi-prime)
				       (derivative-cr-fn1 F-prime)
				       (differential-cr-fn1 differential-cr-f)
				       (differential-cr-fn2 differential-cr-fi)))
	   )
   )
 )

(encapsulate
 nil
 (local
  (defthm lemma
    (implies (and 
	      (INSIDE-INTERVAL-P X (F-O-FI-DOMAIN))
	      (INSIDE-INTERVAL-P X1 (F-O-FI-DOMAIN)))
	     (equal (+ X X1 (- X)) X1)
	     )
    ))

 (defthmd derivative-cr-f-o-fi-limited-1
   (implies (and (standardp x)
		 (inside-interval-p x (F-o-fi-domain))
		 (inside-interval-p x1 (F-o-fi-domain))
		 (i-close x x1) (not (= x x1)))
	    (i-limited (differential-cr-f-o-fi x (- x1 x))))
   :hints (("Goal"
	    :use ((:instance differential-cr-f-o-fi-limited
			     (x x)
			     (eps (- x1 x))
			     )
		  (:instance lemma)
		  (:instance i-close-symmetric
			     (x x)
			     (y x1))
		  (:instance i-small-plus-lemma
			     (x x1)
			     (y x))
		  )
	    :in-theory '(differential-cr-f-o-fi-limited)
	    ))
   )
 )

(local
 (defthm derivative-cr-f-o-fi-is-derivative
   (implies (and (standardp x)
		 (inside-interval-p x (F-o-fi-domain))
		 (inside-interval-p x1 (F-o-fi-domain))
		 (i-close x x1) (not (= x x1)))
	    (i-close (/ (- (f-o-fi x) (f-o-fi x1)) (- x x1))
		     (derivative-cr-f-o-fi x))
	    )
   
   :hints (("Goal"
	    :use(
		 (:instance expand-differential-cr-f-o-fi-2
			    (x x)
			    (x1 x1))
		 (:instance  derivative-cr-f-o-fi-limited-1
			     (x x)
			     (x1 x1))
		 (:instance standard-part-close
			    (x (differential-cr-f-o-fi x (- x1 x)))
			    )
		 (:instance differential-cr-f-o-fi-close-1
			    (x x)
			    (x1 x1))
		 (:instance i-close-lemma1
			    (x (standard-part (differential-cr-f-o-fi x (- x1 x))))
			    (y (differential-cr-f-o-fi x (- x1 x)))
			    (z (derivative-cr-f-o-fi x))
			    )
		 )
	    ))
   )
 )

(local 
(defthm real-derivative-cr-f-o-fi
  (implies (inside-interval-p x (f-o-fi-domain))
	   (realp (derivative-cr-f-o-fi x)))
  :hints (("Goal"
	   :use (:functional-instance real-derivative-cr-fn1-o-fn2
				      (derivative-cr-fn1-o-fn2 derivative-cr-f-o-fi)
				      (differential-cr-fn1-o-fn2 differential-cr-f-o-fi)
				      (cr-fn1-o-fn2 f-o-fi)
				      (cr-fn2-domain f-o-fi-domain)
				      (cr-fn2-range fi-range)
				      (cr-fn1 f)
				      (cr-fn2 fi)
				      (derivative-cr-fn2 fi-prime)
				      (derivative-cr-fn1 F-prime)
				      (differential-cr-fn1 differential-cr-f)
				      (differential-cr-fn2 differential-cr-fi)))
	  )
  )
)


(defun F-o-fi-prime (x)
  (if (inside-interval-p x (f-o-fi-domain))
      (derivative-cr-f-o-fi x)
    0)
  )

(defthm F-o-fi-prime-real
  (realp (F-o-fi-prime x))
  :hints (("Goal"
	   :use (:instance real-derivative-cr-f-o-fi)
	   ))
  )

(defthm F-o-fi-prime-is-derivative
  (implies (and (standardp x)
		(inside-interval-p x (F-o-fi-domain))
		(inside-interval-p x1 (F-o-fi-domain))
		(i-close x x1) (not (= x x1)))
	   (i-close (/ (- (F-o-fi x) (F-o-fi x1)) (- x x1))
		    (F-o-fi-prime x)))
  :hints (("Goal"
	   :use (
		 (:instance  derivative-cr-f-o-fi-is-derivative)
		 )
	   :in-theory '(F-o-fi-prime derivative-cr-f-o-fi-is-derivative)
	   ))
  )

(encapsulate
 ()

 (local
  (defthm-std fi-standard-1
    (implies (standardp x)
	     (standardp (fi x))
	     )
    )
  )

 (local
  (defthm fi-standard
    (implies (standard-numberp x)
	     (standard-numberp (fi x))
	     )
    :hints (("Goal"
	     :use (:instance fi-standard-1)
	     ))
    )
  )

 (local
  (defthm-std fi-prime-standard-1
    (implies (standardp x)
	     (standardp (fi-prime x))
	     )
    )
  )

 (local
  (defthm fi-prime-standard
    (implies (standard-numberp x)
	     (standard-numberp (fi-prime x))
	     )
    :hints (("Goal"
	     :use (:instance fi-prime-standard-1)
	     ))
    )
  )

 (local
  (defthm-std f-prime-f-standard-1
    (implies (standardp x)
	     (standardp (f-prime (fi x)))
	     )
    )
  )

 (local
  (defthm f-prime-f-standard
    (implies (standard-numberp x)
	     (standard-numberp (f-prime (fi x)))
	     )
    :hints (("Goal"
	     :use (:instance f-prime-f-standard-1)
	     ))
    )
  )

 (local
  (defthm f-continuous
    (implies (and (standardp x)
		  (inside-interval-p x (fi-range))
		  (i-close x y)
		  (inside-interval-p y (fi-range))
		  )
	     (i-close (f x) (f y))
	     )
    :hints (("Goal"
	     :use ((:functional-instance rdfn-continuous
					 (rdfn f)
					 (rdfn-domain fi-range))
		   )
	     ))
    )
  )


 (local
  (defthm fi-prime-real-1
    (implies (realp x)
	     (realp (fi-prime x)))
    )
  )

 (local
  (defthm f-prime-fi-real-1
    (implies (realp x)
	     (realp (f-prime (fi x))))
    )
  )

 (local
  (defthm fi-continuous
    (implies (and (standardp x)
		  (inside-interval-p x (f-o-fi-domain))
		  (i-close x y)
		  (inside-interval-p y (f-o-fi-domain))
		  )
	     (i-close (fi x) (fi y))
	     )
    :hints (("Goal"
	     :use ((:functional-instance rdfn-continuous
					 (rdfn fi)
					 (rdfn-domain f-o-fi-domain))
		   )
	     ))
    )
  )

 (local
  (defthm f-prime-fi-continuous
    (implies (and (standardp x)
		  (inside-interval-p x (F-o-fi-domain))
		  (i-close x x1)
		  (inside-interval-p x1 (F-o-fi-domain))
					;(not (= x x1))
		  )
	     (i-close (f-prime (fi x))
		      (f-prime (fi x1))))
    :hints (("Goal"
	     :use ((:instance F-prime-continuous)
		   (:instance fi-range-in-domain-of-f-o-fi (x x))
		   (:instance fi-range-in-domain-of-f-o-fi (x x1))
		   )
	     ))
    ))

 (local
  (defun f-prime-fi (x)
    (f-prime (fi x))
    )
  )

 (defthm F-o-fi-prime-continuous
   (implies (and (standardp x)
		 (inside-interval-p x (F-o-fi-domain))
		 (i-close x x1)
		 (inside-interval-p x1 (F-o-fi-domain))
		 )
	    (i-close (F-o-fi-prime x)
		     (F-o-fi-prime x1)))
   :hints (("Goal"
	    :in-theory (enable standards-are-limited)
	    )
	   )
   )
 )

(in-theory (disable F-o-fi-prime))

(defun map-F-o-fi-prime (p)
  (if (consp p)
      (cons (F-o-fi-prime (car p))
	    (map-F-o-fi-prime (cdr p)))
    nil))

(defun riemann-F-o-fi-prime (p)
  (dotprod (deltas p)
	   (map-F-o-fi-prime (cdr p))))

(defthm realp-riemann-F-o-fi-prime
  (implies (partitionp p)
	   (realp (riemann-F-o-fi-prime p)))
  :hints (("Goal"
	   :use (:instance  F-o-fi-prime-real)
	   ))
  )

(encapsulate
 nil

 (local
  (defthm limited-riemann-F-o-fi-prime-small-partition
    (implies (and (realp a) (standardp a)
		  (realp b) (standardp b)
		  (inside-interval-p a (F-o-fi-domain))
		  (inside-interval-p b (F-o-fi-domain))
		  (< a b))
	     (i-limited (riemann-F-o-fi-prime (make-small-partition a b))))
    :hints (("Goal"
	     :by (:functional-instance limited-riemann-rcfn-small-partition
				       (rcfn-domain F-o-fi-domain)
				       (rcfn F-o-fi-prime)
				       (map-rcfn map-F-o-fi-prime)
				       (riemann-rcfn riemann-F-o-fi-prime)))
	    ("Subgoal 2"
	     :use ((:instance F-o-fi-domain-non-trivial))))))

 (local (in-theory (disable riemann-F-o-fi-prime)))

 (defun-std strict-int-F-o-fi-prime (a b)
   (if (and (realp a)
	    (realp b)
	    (inside-interval-p a (F-o-fi-domain))
	    (inside-interval-p b (F-o-fi-domain))
	    (< a b))
       (standard-part (riemann-F-o-fi-prime (make-small-partition a b)))
     0))
 )

(defun int-F-o-fi-prime (a b)
  (if (<= a b)
      (strict-int-F-o-fi-prime a b)
    (- (strict-int-F-o-fi-prime b a))))

(encapsulate
 nil
 (local  (in-theory (disable F-o-fi-equal)))

 (defthmd ftc-2-usub
   (implies (and (inside-interval-p a (f-o-fi-domain))
		 (inside-interval-p b (f-o-fi-domain)))
	    (equal (int-f-o-fi-prime a b)
		   (- (f-o-fi b)
		      (f-o-fi a))))
   :hints (("Goal"
	    :use ((:functional-instance ftc-2
					(rcdfn-domain F-o-fi-domain)
					(int-rcdfn-prime int-F-o-fi-prime)
					(riemann-rcdfn-prime riemann-F-o-fi-prime)
					(map-rcdfn-prime map-F-o-fi-prime)
					(rcdfn F-o-fi)
					(rcdfn-prime F-o-fi-prime)
					(strict-int-rcdfn-prime strict-int-F-o-fi-prime))))

	   ("Subgoal 7"
	    :use ((:instance F-o-fi-prime-is-derivative)))
	   ("Subgoal 8"
	    :use ((:instance F-o-fi-real)))
	   ("Subgoal 6"
	    :use ((:instance  F-o-fi-domain-non-trivial)))
	   )
   ))

(defthmd ftc2-usub-equal
  (implies (and (inside-interval-p a (f-o-fi-domain))
		(inside-interval-p b (f-o-fi-domain)))
	   (equal (int-f-o-fi-prime a b)
		  (- (f (fi b))
		     (f (fi a)))))
  :hints (("Goal"
	   :use ((:instance ftc-2-usub)
		 (:instance F-o-fi-equal(x a))
		 (:instance F-o-fi-equal(x b))
		 )
	   
	   ))
  )

(defun map-F-prime (p)
  (if (consp p)
      (cons (F-prime (car p))
	    (map-F-prime (cdr p)))
    nil))

(defun riemann-F-prime (p)
  (dotprod (deltas p)
	   (map-F-prime (cdr p))))

(defthm realp-riemann-F-prime
  (implies (partitionp p)
	   (realp (riemann-F-prime p))))

(encapsulate
 nil

 (local
  (defthm limited-riemann-F-prime-small-partition
    (implies (and (realp a) (standardp a)
		  (realp b) (standardp b)
		  (inside-interval-p a (fi-range))
		  (inside-interval-p b (fi-range))
		  (< a b))
	     (i-limited (riemann-F-prime (make-small-partition a b))))
    :hints (("Goal"
	     :by (:functional-instance limited-riemann-rcfn-small-partition
				       (rcfn-domain fi-range)
				       (rcfn F-prime)
				       (map-rcfn map-F-prime)
				       (riemann-rcfn riemann-F-prime))
	     :in-theory (disable F-prime-definition)
	     )
	    ("Subgoal 2"
	     :use ((:instance fi-range-non-trivial)))
	    )))

 (local (in-theory (disable riemann-F-prime)))

 (defun-std strict-int-F-prime (a b)
   (if (and (realp a)
	    (realp b)
	    (inside-interval-p a (fi-range))
	    (inside-interval-p b (fi-range))
	    (< a b))
       (standard-part (riemann-F-prime (make-small-partition a b)))
     0))
 )

(defun int-F-prime (a b)
  (if (<= a b)
      (strict-int-F-prime a b)
    (- (strict-int-F-prime b a))))

(defthmd ftc-2-usub-1
  (implies (and (inside-interval-p a (fi-range))
		(inside-interval-p b (fi-range)))
	   (equal (int-f-prime a b)
		  (- (f b)
		     (f a))))
  :hints (("Goal"
	   :use (:functional-instance ftc-2
				      (rcdfn-domain fi-range)
				      (int-rcdfn-prime int-F-prime)
				      (riemann-rcdfn-prime riemann-F-prime)
				      (map-rcdfn-prime map-F-prime)
				      (rcdfn F)
				      (rcdfn-prime F-prime)
				      (strict-int-rcdfn-prime strict-int-F-prime))
	   
	   :in-theory (disable F-prime-definition)
	   )
	  ("Subgoal 7"
	   :use ((:instance F-prime-is-derivative)))
	  ("Subgoal 8"
	   :use ((:instance F-real)))
	  ("Subgoal 6"
	   :use ((:instance  fi-range-non-trivial)))
	  )
  )

(defthmd ftc2-usub-1-equal
  (implies (and (inside-interval-p a (f-o-fi-domain))
		(inside-interval-p b (f-o-fi-domain)))
	   (equal (int-f-prime (fi a) (fi b))
		  (- (f (fi b))
		     (f (fi a)))))
  :hints (("Goal"
	   :use (
		 (:instance ftc-2-usub-1 (a (fi a))
			    (b (fi b))
			    )
		 )
	   )
	  )
					;:rule-classes (:rewrite)
  )

(defthm ftc2-usub-usub1-equal
  (implies (and (inside-interval-p a (f-o-fi-domain))
		(inside-interval-p b (f-o-fi-domain)))
	   (equal (int-f-prime (fi a) (fi b))
		  (int-f-o-fi-prime a b)))
  :hints (("Goal"
	   :use (
		 (:instance ftc2-usub-1-equal)
		 (:instance ftc2-usub-equal)
		 )
	   ))
  )