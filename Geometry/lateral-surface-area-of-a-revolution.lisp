;; This buffer is for text that is not saved, and for Lisp evaluation.
;; To create a file, visit it with C-x C-f and enter text in its buffer.

(in-package "ACL2")

(include-book "length-of-a-rectifiable-curve")
(include-book "nonstd/nsa/trig" :dir :system)

(encapsulate
 ()

 (local
  (defthm lemma-1
    (implies (and (acl2-numberp x)
		  (acl2-numberp y)
		  (i-small y)
		  (not (= y 0))
		  (i-limited (/ x y)))
	     (i-small x))
    :hints (("Goal"
	     :use ((:instance limited*large->large (y (/ y))))
	     :in-theory (disable limited*large->large)))))

 (defthm c-continuous
   (implies (and (standardp x)
		 (inside-interval-p x (c-domain))
		 (i-close x y)
		 (inside-interval-p y (c-domain)))
	    (and (i-close (c x) (c y))
		 (i-close (realpart (c x)) (realpart (c y)))
		 (i-close (imagpart (c x)) (imagpart (c y)))))
   :hints (("Goal"
	    :use ((:instance c-differentiable (y1 y) (y2 y))
		  (:instance lemma-1
			     (x (+ (c x) (- (c y))))
			     (y (+ x (- y))))
		  (:instance c-acl2numberp)
		  (:instance c-acl2numberp (x y))
		  (:instance c-domain-real)
		  (:instance c-domain-real (x y))
		  (:instance re-im-close (x (c x)) (y (c y))))
	    :in-theory (enable-disable (i-close)
				       (c-differentiable
					lemma-1)))))
 )

(local
 (defthm acl2-numberp-std
   (implies (acl2-numberp x)
	    (acl2-numberp (standard-part x)))
   )
 )

(local
 (defthm product-continuous
   (implies (and (acl2-numberp x)
		 (standardp x)
		 (acl2-numberp y)
		 (acl2-numberp a)
		 (standardp a)
		 (acl2-numberp b)
		 (i-close x y)
		 (i-close a b))
	    (i-close (* x a) (* y b)))
   :hints (("Goal"
	    :use ((:instance i-small-plus-lemma)
		  (:instance i-small-plus-lemma (x a) (y b))
		  (:instance small*limited->small (x (- x y)) (y a))
		  (:instance i-close-limited)
		  (:instance i-close-limited (x a) (y b))
		  (:instance limited*small->small (x y) (y (- a b)))
		  (:instance i-close-transitive (x (* x a)) (y (* y a)) (z (* y b)))
		  (:instance i-close-plus-lemma-2 (x (* x a)) (y (* y a)))
		  (:instance i-close-plus-lemma-2 (x (* y a)) (y (* y b)))
		  )
	    :in-theory (enable standards-are-limited)
	    ))
   )
 )

(defthm-std std-c
  (implies (standardp x)
	   (standardp (c x)))
  )

(local
 (defthm acl2-sqrt-lemma
   (implies (and (standardp x)
		 (acl2-numberp x))
	    (standardp (acl2-sqrt x))
	    )
   :hints (("Goal"
	    :use (
		  (:DEFINITION FIX)
		  (:FORWARD-CHAINING STANDARDS-ARE-LIMITED-FORWARD)
		  (:REWRITE LIMITED-ITER-SQRT-STRONG)
		  (:REWRITE STANDARDP-STANDARD-PART)
		  (:TYPE-PRESCRIPTION ITER-SQRT-TYPE-PRESCRIPTION))
	    :in-theory (enable acl2-sqrt)
	    ))
   )
 )

(defthm std-der-sum-sqrt
  (implies (and (standardp x)
		(acl2-numberp x))
	   (standardp (der-sum-sqrt x)))
  :hints (("Goal"
	   :use ((:instance der-sqr-sum-standard)
		 (:instance acl2-sqrt-lemma)
		 )
	   ))
  )

(defthm surface-continuous
  (implies (and (standardp x)
		(inside-interval-p x (c-domain))
		(i-close x y)
		(inside-interval-p y (c-domain)))
	   (i-close (* (imagpart (c x)) (der-sum-sqrt x)) (* (imagpart (c y)) (der-sum-sqrt y))))
  :hints (("Goal"
	   :cases ((complexp (c x)) (realp (c x)))
	   :use ((:instance c-continuous)
		 (:instance der-sum-sqrt-cont)
		 (:instance acl2-numberp-std (x (c x)))
		 (:instance acl2-numberp-std (x (c y)))
		 (:instance acl2-numberp-std (x (der-sum-sqrt y)))
		 (:instance acl2-numberp-std (x (der-sum-sqrt x)))
		 (:instance std-c)
		 (:instance std-der-sum-sqrt)
		 (:instance standards-are-limited-forward (x (c x)))
		 (:instance complex-limited-2 (x (c x)))
		 (:instance standardp-complex (x (realpart (c x))) (y (imagpart (c x))))
		 (:instance product-continuous (x (imagpart (c x))) (y (imagpart (c y))) (a (der-sum-sqrt x)) (b (der-sum-sqrt y)))
		 )
	   :in-theory (enable standards-are-limited)
	   ))
  )

(defun imc (x)
  (imagpart (c x))
  )

(defun imc*der-sum-sqrt (x)
  (* 2 (acl2-pi) (imc x) (der-sum-sqrt x))
  )

(local
 (defthm acl2-pi-limited
   (i-limited (acl2-pi))
   :hints (("Goal"
	    :use ((:instance pi-between-2-4)
		  (:instance limited-squeeze (a 2) (b 4) (x (acl2-pi)))
		  )
	    :in-theory (enable nsa-theory interval-definition-theory standards-are-limited)
	    ))
   )
 )


(defthm imc*der-sum-sqrt-continuous
  (implies (and (standardp x)
		(inside-interval-p x (c-domain))
		(i-close x y)
		(inside-interval-p y (c-domain)))
	   (i-close (imc*der-sum-sqrt x) (imc*der-sum-sqrt y))
	   )
      :hints (("Goal"
	       :use ((:instance surface-continuous)
		     (:instance i-small-plus-lemma
				(x  (* (imagpart (c x)) (der-sum-sqrt x)))
				(y (* (imagpart (c y)) (der-sum-sqrt y))))
		     (:instance limited*small->small
				(x (* 2 (acl2-pi)))
				(y (- (* (imagpart (c x)) (der-sum-sqrt x)) (* (imagpart (c y)) (der-sum-sqrt y)))))
		     (:instance pi-between-2-4)
		     (:instance i-limited-times (x 2) (y (acl2-pi)))
		     (:instance acl2-pi-limited)
		     (:instance i-close-plus-lemma-2
				(x (* 2 (acl2-pi) (imc x) (der-sum-sqrt x)))
				(y (* 2 (acl2-pi) (imc y) (der-sum-sqrt y))))
		     )
	       :in-theory (enable nsa-theory)
	       ))
  )

(defun map-imc*der-sum-sqrt (p)
  (if (consp p)
      (cons (imc*der-sum-sqrt (car p))
	    (map-imc*der-sum-sqrt (cdr p)))
    nil))

(defun riemann-imc*der-sum-sqrt (p)
  (dotprod (deltas p)
           (map-imc*der-sum-sqrt (cdr p))))

(encapsulate
 ()

 ;(local (in-theory (disable riemann-imc*der-sum-sqrt)))

 (local
  (defthm limited-riemann-imc*der-sum-sqrt-small-partition
    (implies (and (realp a) (standardp a)
		  (realp b) (standardp b)
		  (inside-interval-p a (c-domain))
		  (inside-interval-p b (c-domain))
		  (< a b))
	     (i-limited (riemann-imc*der-sum-sqrt (make-small-partition a b))))

    :hints (("Goal"
	     :use (
		   (:functional-instance limited-riemann-rcfn-small-partition
					 (rcfn-domain c-domain)
					 (riemann-rcfn riemann-imc*der-sum-sqrt)
					 (map-rcfn map-imc*der-sum-sqrt)
					 (rcfn imc*der-sum-sqrt)
					 )
		   )
	     )
	    ("Subgoal 1"
	     :use (:instance intervalp-der-sqrt-domain)
	     )
	    ("Subgoal 2"
	     :use ((:instance c-domain-non-trivial))
	     )
	    ("Subgoal 3"
	     :use ((:instance imc*der-sum-sqrt-continuous (x x) (y y)))
	     ))
    ))

 (local (in-theory (disable riemann-imc*der-sum-sqrt)))

 (defun-std strict-int-imc*der-sum-sqrt (a b)
   (if (and (realp a)
	    (realp b)
	    (inside-interval-p a (c-domain))
	    (inside-interval-p b (c-domain))
	    (< a b))
       (standard-part (riemann-imc*der-sum-sqrt (make-small-partition a b)))
     0))
 )

(defthm strict-int-imc*der-sum-sqrt-is-integral-of-der-sum-sqrt
  (implies (and (standardp a)
                (standardp b)
                (<= a b)
                (inside-interval-p a (c-domain))
                (inside-interval-p b (c-domain))
                (partitionp p)
                (equal (car p) a)
                (equal (car (last p)) b)
                (i-small (mesh p)))
           (i-close (riemann-imc*der-sum-sqrt p)
                    (strict-int-imc*der-sum-sqrt a b)))

  :hints (("Goal"
           :use (
                 (:functional-instance strict-int-rcfn-is-integral-of-rcfn
				       (rcfn-domain c-domain)
				       (riemann-rcfn riemann-imc*der-sum-sqrt)
				       (strict-int-rcfn strict-int-imc*der-sum-sqrt)
				       (map-rcfn map-imc*der-sum-sqrt)
				       (rcfn imc*der-sum-sqrt)
				       )
                 )
           ))
  )
