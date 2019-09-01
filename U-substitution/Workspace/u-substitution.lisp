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
					; :hints (("Goal"
					;	    :use ((:instance close-x-y->same-standard-part (x x) (y y)))))
					;  )
   )

 ;; (defthmd i-limited-lemma
 ;;   (implies (and (acl2-numberp x)
 ;; 		 (acl2-numberp y)
 ;; 					;(acl2-numberp z)
 ;; 		 (not (= x 0))
 ;; 		 (i-limited x)
 ;; 		 (i-limited (* x y)))
 ;; 	    (i-limited y)
	    
 ;; 	    )
 ;;   )
 
 ;; (defthmd stdpart-equal-lemma
 ;;   (implies (and (equal (standard-part a) (standard-part b))
 ;; 		 (equal (standard-part x) (standard-part y)))
 ;; 	    (equal (* (standard-part a) (standard-part x))
 ;; 		   (* (standard-part b) (standard-part y)))
 ;; 	    )

 ;;   )


 ;; (defthmd stdpart-i-close
 ;;   (implies (and (acl2-numberp a)
 ;; 		 (acl2-numberp b)
 ;; 		 (equal (standard-part a) (standard-part b)))
 ;; 	    (i-close a b)
	    
 ;; 	    )

 ;;   )

 (defthmd i-close-lemma1
   (implies (and (i-close x y)
		 (equal x z))
	    (i-close y z)
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

 ;; (defthmd stdpart-lemma
 ;;   (implies (and (acl2-numberp a)
 ;; 		 (acl2-numberp b))
 ;; 	    (equal (standard-part (* a b))
 ;; 		   (* (standard-part a) (standard-part b))))

 ;;   )

 ;; (defthmd i-close-lemma2
 ;;   (implies (and (acl2-numberp x)
 ;; 		 (acl2-numberp y)
 ;; 		 (acl2-numberp a)
 ;; 		 (acl2-numberp b)
 ;; 		 (i-close x y)
 ;; 		 (i-close a b))
 ;; 	    (i-close (* x a) (* y b))
 ;; 	    )
 ;;   :hints (("Goal"
 ;; 	    :use ((:instance stdpart-equal-lemma)
 ;; 		  (:instance 
 ;; 	    ))
 ;;   )
 
 )


(local (include-book "/Users/jagadishbapanapally/Documents/acl2-8.2/acl2-sources/books/nonstd/integrals/ftc-2" :dir :system))

(local (include-book "/Users/jagadishbapanapally/Documents/acl2-8.2/acl2-sources/books/nonstd/nsa/chain-rule" :dir :system))

(encapsulate
 ( ((F *) => *)
   ((fi *) => *)
   ((F-o-fi *) => *)
   ((differential-cr-f * *) => *)
   ((differential-cr-fi * *) => *)
  ; ((F-o-fi-prime *) => *)
   ((F-o-fi-domain) => *)
   ((F-prime *) => *)
   ((fi-prime *) => *)
   (fi-range () t))



 (local (defun F (x) (declare (ignore x)) 0))
 (local (defun fi (x) (declare (ignore x)) 0))
 (local
  (defun F-o-fi (x)
    (F (fi x))))
 ;(local (defun F-o-fi-prime (x) (declare (ignore x)) 0))
 (local (defun F-o-fi-domain () (interval 0 1)))

 (local (defun F-prime (x) (declare (ignore x)) 0))
 (local (defun fi-prime (x) (declare (ignore x)) 0))
 (local (defun fi-range () (interval 0 1)))
 (local
  (defun differential-cr-f (x eps)
    (/ (- (f (+ x eps)) (f x)) eps)))
 (local
  (defun differential-cr-fi (x eps)
    (/ (- (fi (+ x eps)) (fi x)) eps)))
					;(local (defun F-domain () (interval 0 1)))

 (defthm F-o-fi-equal
   (implies (inside-interval-p x (F-o-fi-domain))
	    (equal (F-o-fi x) (F (fi x))))
	    )
 
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

 (defthm F-o-fi-real
   (realp (F-o-fi x))
   :rule-classes (:rewrite :type-prescription))

 (local
  (defthm lemma
    (implies (acl2-numberp x)
	     (equal (* 0 x) 0))
    )
  )



					;---------------------F-prime---------------------


 (defthm F-real
   (realp (F x))
   :rule-classes (:rewrite :type-prescription))

 (defthm F-prime-real
   (realp (F-prime x))
   :rule-classes (:rewrite :type-prescription))


 (local (defthm i-close-0-lemma
	  (IMPLIES (AND (STANDARDP X)
			(INSIDE-INTERVAL-P x '(0 . 1))
			(INSIDE-INTERVAL-P x1 '(0 . 1))
			(I-CLOSE x x1)
			(NOT (EQUAL X X1)))
		   (equal (* 0 (/ (+ x (- x1)))) 0))
	  ))
 
 (defthm F-prime-is-derivative
   (implies (and (standardp x)
		 (inside-interval-p x (fi-range))
		 (inside-interval-p x1 (fi-range))
		 (i-close x x1) (not (= x x1)))
	    (i-close (/ (- (F x) (F x1)) (- x x1))
		     (F-prime x)))
   :hints (("Goal"
	    :use (
		  (:instance i-close-0-lemma (x x) (x1 x1))
		  )
					;:in-theory (disable  (:REWRITE I-CLOSE-REFLEXIVE))
	    ))
   )

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
					;:in-theory (disable  (:REWRITE I-CLOSE-REFLEXIVE))
	    ))
   )

 (defthm fi-prime-continuous
   (implies (and (standardp x)
		 (inside-interval-p x (f-o-fi-domain))
		 (i-close x x1)
		 (inside-interval-p x1 (f-o-fi-domain)))
	    (i-close (fi-prime x)
		     (fi-prime x1))))


					;---------------------------chain rule--------------------------


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

 (defthm fi-range-in-domain-of-f-o-fi
   (implies (inside-interval-p x (f-o-fi-domain))
	    (inside-interval-p (fi x) (fi-range))))

 (defthm f-differentiable
   (implies (and (standardp x)
		 (inside-interval-p x (fi-range))
		 (inside-interval-p y1 (fi-range))
		 (inside-interval-p y2 (fi-range))
		 (i-close x y1) (not (= x y1))
		 (i-close x y2) (not (= x y2)))
	    (and (i-limited (/ (- (f x) (f y1)) (- x y1)))
		 (i-close (/ (- (f x) (f y1)) (- x y1))
			  (/ (- (f x) (f y2)) (- x y2))))))

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

;;;;;;;;;;;;;;;;;


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
	     :use ((:instance fi-range-non-trivial)
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
	     :in-theory (disable fi-range)
	     )
	    ("Subgoal 7"
	     :in-theory (enable interval-definition-theory))
	    ("Subgoal 5"
	     :in-theory (enable interval-definition-theory))
	    ("Subgoal 4"
	     :in-theory (enable interval-definition-theory))
	    ("Subgoal 3"
	     :in-theory (enable interval-definition-theory))
	    ("Subgoal 1"
	     :in-theory (enable interval-definition-theory))
	    )
    ;:rule-classes nil
    ))
;;;;;;;;;


 


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
	    :use (:instance x-in-interval-implies-x+-eps-in-interval
			    (x x)
			    (eps (/ (i-large-integer)))
			    )
	    ))
   )


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
	    :use (:functional-instance F-prime-definition
				       (fi-range f-o-fi-domain)
				       (differential-cr-f differential-cr-fi)
				       (f fi)
				       (f-prime fi-prime)
				       )
	    :in-theory (enable interval-definition-theory)
	    ))
   )
 
 )


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

(in-theory (disable differential-cr-f-definition))

(in-theory (disable F-prime-definition))

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

(in-theory (disable differential-cr-fi-definition))

(in-theory (disable fi-prime-definition))



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


 (defthm expand-differential-cr-f-o-fi-1
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

 (defthm expand-differential-cr-f-o-fi-2
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


 (defthm derivative-cr-f-o-fi-limited-1
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


(defun F-o-fi-prime (x)
  (if (inside-interval-p x (f-o-fi-domain))
      (derivative-cr-f-o-fi x)
    0)
  )


;(skip-proofs
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



					;(skip-proofs

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

 ;; (local
 ;;  (defthm fi-prime-limited
 ;;    (implies (and (standardp x)
 ;; 		  (inside-interval-p x (F-o-fi-domain))
 ;; 		  (i-close x x1)
 ;; 		  (inside-interval-p x1 (F-o-fi-domain))
 ;; 		  (not (= x x1)))
 ;; 	     (and (i-limited (fi-prime x1))
 ;; 		  (i-limited (fi-prime x)))
	     
 ;; 	     )
 ;;    :hints (("Goal"
 ;; 	     :use ((:instance fi-prime-continuous)
 ;; 		   (:instance fi-differentiable
 ;; 			      (x x)
 ;; 			      (y1 x1)
 ;; 			      (y2 x1))
 ;; 		   (:instance fi-prime-is-derivative)
 ;; 		   (:instance i-close-limited
 ;; 			      (x (/ (- (fi x) (fi x1)) (- x x1)))
 ;; 			      (y (fi-prime x)))
 ;; 		   (:instance i-close-limited
 ;; 			      (x (fi-prime x))
 ;; 			      (y (fi-prime x1)))
		   
 ;; 		   )
 ;; 	     ))
 ;;    )
 ;;  )


 ;; (defthmd f-prime-limited-lemma-1
 ;;   (implies (and (standardp x)
 ;; 		 (inside-interval-p x (fi-range))
 ;; 		 (i-close x x1)
 ;; 		 (inside-interval-p x1 (fi-range))
 ;; 		 (not (= x x1)))
 ;; 	    (and (i-limited (f-prime x))
 ;; 		 (i-limited (f-prime x1)))
 ;; 	    )
 ;;   :hints (("Goal"
 ;; 	    :use ((:instance f-prime-continuous)
 ;; 		  (:instance f-differentiable
 ;; 			     (x x)
 ;; 			     (y1 x1)
 ;; 			     (y2 x1))
 ;; 		  (:instance f-prime-is-derivative)
 ;; 		  (:instance i-close-limited
 ;; 			     (x (/ (- (f x) (f x1)) (- x x1)))
 ;; 			     (y (f-prime x)))
 ;; 		  (:instance i-close-limited
 ;; 			     (x (f-prime x))
 ;; 			     (y (f-prime x1)))
		  
 ;; 		  )
 ;; 	    ))
 ;;   )

 ;; (local
 ;;  (defthm f-prime-limited-lemma-2
 ;;    (IMPLIES (AND (not (EQUAL (FI X) (FI X1)))
 ;; 		  (STANDARDP X)
 ;; 		  (INSIDE-INTERVAL-P X (F-O-FI-DOMAIN))
 ;; 		  (I-CLOSE X X1)
 ;; 		  (INSIDE-INTERVAL-P X1 (F-O-FI-DOMAIN))
 ;; 		  (NOT (EQUAL X X1)))
 ;; 	     (i-limited (F-PRIME (FI X))))
 ;;    :hints (("Goal"
 ;; 	     :use ((:instance f-prime-continuous)
 ;; 		   (:instance f-differentiable
 ;; 			      (x x)
 ;; 			      (y1 x1)
 ;; 			      (y2 x1))
 ;; 		   (:instance f-prime-is-derivative)
 ;; 		   (:instance i-close-limited
 ;; 			      (x (/ (- (f x) (f x1)) (- x x1)))
 ;; 			      (y (f-prime x)))
 ;; 		   (:instance i-close-limited
 ;; 			      (x (f-prime x))
 ;; 			      (y (f-prime x1)))
 
 ;; 		   )
 ;; 	     ))
 ;;    )
 ;;  )

 ;; (defthmd f-prime-limited
 ;;   (implies (and (standardp x)
 ;; 		 (inside-interval-p x (f-o-fi-domain))
 ;; 		 (inside-interval-p x1 (f-o-fi-domain))
 ;; 		 (i-close x x1)
 ;; 		 (not (= x x1))
 ;; 		 (not (= (FI X1) (FI X)))
 ;; 		 )
 ;; 	    (and (i-limited (f-prime (fi x)))
 ;; 		 (i-limited (f-prime (fi x1))))
 ;; 	    )
 ;;   :hints (("Goal"
 ;; 	    :use ((:instance f-prime-limited-lemma-1
 ;; 			     (x (fi x))
 ;; 			     (x1 (fi x1)))
 ;; 		  (:instance fi-continuous
 ;; 			     (x x)
 ;; 			     (y x1))
 ;; 		  (:instance fi-range-in-domain-of-f-o-fi (x x))
 ;; 		  (:instance fi-range-in-domain-of-f-o-fi (x x1))
 ;; 		  )
	    
	    
 ;; 	    ))
 ;;   )


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


 ;; (defthm F-o-fi-prime-continuous-lemma1
 ;;   (implies (and (standardp x)
 ;; 		 (inside-interval-p x (F-o-fi-domain))
 ;; 		 (i-close x x1)
 ;; 		 (inside-interval-p x1 (F-o-fi-domain))
 ;; 		 (= x x1)
 ;; 		 )
 ;; 	    (i-close (F-o-fi-prime x)
 ;; 		     (F-o-fi-prime x1)))
 ;;   )


 ;; (defthm derivative-cr-fn1-o-fn2-must-be-zero
 ;;    (implies (and (standardp x)
 ;; 		   (inside-interval-p x (cr-fn2-domain))
 ;; 		   (realp eps)
 ;; 		   (not (equal eps 0))
 ;; 		   (i-small eps)
 ;; 		   (inside-interval-p (+ x eps) (cr-fn2-domain))
 ;; 		   (equal (cr-fn2 (+ x eps)) (cr-fn2 x)))
 ;; 	     (equal (derivative-cr-fn1-o-fn2 x) 0))
 ;;  :hints (("Goal"
 ;; 	   :in-theory '(derivative-cr-fn2-must-be-zero
 ;; 			derivative-cr-fn1-o-fn2-definition)
 ;; 	   )))


 (local
  (defun f-prime-fi (x)
    (f-prime (fi x))
    )
  )

 (local (include-book "/Users/jagadishbapanapally/Documents/acl2-8.2/acl2-sources/books/nonstd/nsa/continuity-product" :dir :system))
 (local (include-book "/Users/jagadishbapanapally/Documents/acl2-8.2/acl2-sources/books/arithmetic/top-with-meta" :dir :system))

 ;; (defthm F-o-fi-prime-continuous-lemma
 ;;   (implies (and (standardp x)
 ;; 		 (inside-interval-p x (F-o-fi-domain))
 ;; 		 (realp x)
 ;; 		 (realp y)
 ;; 		 (i-close x y)
 ;; 		 (inside-interval-p y (F-o-fi-domain))
 ;; 		 )
 ;; 	    (i-close (F-o-fi-prime x)
 ;; 		     (F-o-fi-prime y)))
 ;;   :hints (("Goal"
 ;; 	    :use ((:instance 
				       
 ;; 				       )
 ;; 	    ))

 ;;   )


 (defthm F-o-fi-prime-continuous
   (implies (and (standardp x)
 		 (inside-interval-p x (F-o-fi-domain))
 		 (i-close x x1)
 		 (inside-interval-p x1 (F-o-fi-domain))
 		 )
 	    (i-close (F-o-fi-prime x)
 		     (F-o-fi-prime x1)))
   :hints (("Goal"
 	    ;; :use (
	    ;; 	  (:instance f-prime-fi-continuous)
	    ;;  	  (:instance fi-prime-continuous)
	    ;; 	  (:instance F-o-fi-prime-is-derivative)

	    ;; ;; 	  (:instance close-times-2
	    ;; ;; 		     (x1 fi-prime(x))
	    ;; ;; 		     (x2 fi-prime(x1))
	    ;; ;; 		     (y1 f-prime (fi x))
	    ;; ;; 		     (y2 f-prime (fi x1))
	    ;; ;; 		     )

	    ;;  	  )
	    :in-theory (enable standards-are-limited)
 	    )
	   ;; ("Subgoal 8"
	   ;;  :use ((:instance F-o-fi-prime-is-derivative)
	   ;; 	  )
	   ;;  )
	   )

   )
 

 ;; (defthm F-o-fi-prime-continuous-lemma2
 ;;   (implies (and (standardp x)
 ;; 		 (inside-interval-p x (F-o-fi-domain))
 ;; 		 (i-close x x1)
 ;; 		 (inside-interval-p x1 (F-o-fi-domain))
 ;; 		 (not (= x x1))
 ;; 		 )
 ;; 	    (i-close (F-o-fi-prime x)
 ;; 		     (F-o-fi-prime x1)))

 ;;   :hints (("Goal"
 ;; 	    :use (
 ;; 		  (:instance F-continuous
 ;; 			     (x (fi x))
 ;; 			     (y (fi x1)))
 ;; 		  (:instance fi-continuous
 ;; 			     (x x)
 ;; 			     (y x1))
 ;; 		  (:instance fi-prime-continuous)
 ;; 		  (:instance f-prime-fi-continuous)
 ;; 			    ; (x (fi x))
 ;; 			     ;(x1 (fi x1)))
 ;; 		 ; (:instance f-prime-continuous
 ;; 		;	     (x x)
 ;; 		;	     (x1 x1))
 ;; 		  (:instance fi-standard)
 ;; 		  (:instance fi-prime-limited)
 ;; 		  (:instance f-prime-limited
 ;; 		  	     (x (fi x))
 ;; 		  	     (x1 (fi x1)))
 ;; 		  (:instance i-close-lemma3
 ;; 		  	     (a (f-prime x))
 ;; 		  	     (b (f-prime x1))
 ;; 		  	     (x (f-prime (fi x)))
 ;; 		  	     (y (f-prime (fi x1)))
 ;; 		  	     )
 ;; 		  )
	  
 ;; 	    )
	   
 ;; 	   )


 ;;   )
 )
					;)

(in-theory (disable F-o-fi-prime))


 ;(defthm F-o-fi-prime-continuous
  ; (implies (and (standardp x)
;		 (inside-interval-p x (F-o-fi-domain))
;		 (i-close x x1)
;		 (inside-interval-p x1 (F-o-fi-domain)))
;	    (i-close (F-o-fi-prime x)
;		     (F-o-fi-prime x1))))





;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;








;;;;;;;integral;;;;






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

					;----------F-----


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
	   ; ("Subgoal 3"
	    ;:use ((:instance F-prime-continuous)))
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
	   :use ((:functional-instance ftc-2
				       (rcdfn-domain fi-range)
				       (int-rcdfn-prime int-F-prime)
				       (riemann-rcdfn-prime riemann-F-prime)
				       (map-rcdfn-prime map-F-prime)
				       (rcdfn F)
				       (rcdfn-prime F-prime)
				       (strict-int-rcdfn-prime strict-int-F-prime)))
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
		 ;(:instance fi-inside-interval (a a))
		 ;(:instance fi-inside-interval (a b))
		 (:instance ftc-2-usub-1 (a (fi a))
			    (b (fi b))
			    )
		 )
	   
	   )
	  
	  )
  :rule-classes (:rewrite))


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
