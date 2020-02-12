(in-package "ACL2")

(include-book "/Users/jagadishbapanapally/Documents/GitHub/Research/A-Mechanized-proof-of-the-curve-length-of-a-rectifiable-curve/Workspace/circumference-of-a-circle")
(include-book "/Users/jagadishbapanapally/Documents/GitHub/Research/spheres/lateral-surface-area-of-a-revolution")

(defun imcircle*norm-der (x)
  (* 2 (acl2-pi) (imf x)  (circle-der-sum-sqrt x))
  )

(defthm imcircle*norm-der-continuous
  (implies (and (standardp x)
		(inside-interval-p x (circle-der-sum-sqrt-domain))
		(inside-interval-p y (circle-der-sum-sqrt-domain))
		(i-close x y))
	   (i-close (imcircle*norm-der x) (imcircle*norm-der y))
	   )
  :hints (("Goal"
	   :use (:functional-instance imc*der-sum-sqrt-continuous
				      (imc*der-sum-sqrt imcircle*norm-der)
				      (imc imf)
				      (c circle)
				      (c-derivative circle-der)
				      (rc-derivative rcircle-derivative)
				      (ic-derivative icircle-derivative)
				      (rc-der-sqr rcircle-der-sqr)
				      (der-sum-sqrt-domain circle-der-sum-sqrt-domain)
				      (ic-der-sqr icircle-der-sqr)
				      (der-sqr-sum circle-der-sqr-sum)
				      (der-sum-sqrt circle-der-sum-sqrt)
				      )
	   )
	  ("Subgoal 2"
	   :use (:instance circle-differentiable)
	   )
	  ("Subgoal 3"
	   :use (:instance circle-der-lemma)
	   )
	  ("Subgoal 4"
	   :use (:instance  circle-der-continuous)
	   )
	  ("Subgoal 6"
	   :use (:instance circle-equal)
	   )
	  )
  )


(defun map-imcircle*der-sum-sqrt (p)
  (if (consp p)
      (cons (imcircle*norm-der (car p))
	    (map-imcircle*der-sum-sqrt (cdr p)))
    nil))

(defun riemann-imcircle*der-sum-sqrt (p)
  (dotprod (deltas p)
           (map-imcircle*der-sum-sqrt (cdr p))))

(encapsulate
 ()
 
 (local 
  (defthm limited-riemann-imcircle*der-sum-sqrt-small-partition
    (implies (and (realp a) (standardp a)
		  (realp b) (standardp b)
		  (inside-interval-p a (circle-der-sum-sqrt-domain))
		  (inside-interval-p b (circle-der-sum-sqrt-domain))
		  (< a b))
	     (i-limited (riemann-imcircle*der-sum-sqrt (make-small-partition a b))))
    
    :hints (("Goal"
	     :use (
		   (:functional-instance limited-riemann-rcfn-small-partition
					 (rcfn-domain circle-der-sum-sqrt-domain)
					 (riemann-rcfn riemann-imcircle*der-sum-sqrt)
					 (map-rcfn map-imcircle*der-sum-sqrt)
					 (rcfn imcircle*norm-der)
					 )
		   )
	     )
	    ("Subgoal 1"
	     :use (:instance intervalp-circle-der-sqrt-domain)
	     )
	    ("Subgoal 2"
	     :use ((:instance imcircle*norm-der-continuous))
	     )
	    ("Subgoal 3"
	     :use ((:instance imcircle*norm-der-continuous (x x) (y y)))
	     ))
    ))

 (local (in-theory (disable riemann-imcircle*der-sum-sqrt)))
 
 (defun-std strict-int-imcircle*der-sum-sqrt (a b)
   (if (and (realp a)
	    (realp b)
	    (inside-interval-p a (circle-der-sum-sqrt-domain))
	    (inside-interval-p b (circle-der-sum-sqrt-domain))
	    (< a b))
       (standard-part (riemann-imcircle*der-sum-sqrt (make-small-partition a b)))
     0))
 )

(defthm strict-int-imcircle*der-sum-sqrt-is-integral-of-der-sum-sqrt
  (implies (and (standardp a)
                (standardp b)
                (<= a b)
                (inside-interval-p a (circle-der-sum-sqrt-domain))
                (inside-interval-p b (circle-der-sum-sqrt-domain))
                (partitionp p)
                (equal (car p) a)
                (equal (car (last p)) b)
                (i-small (mesh p)))
           (i-close (riemann-imcircle*der-sum-sqrt p)
                    (strict-int-imcircle*der-sum-sqrt a b)))
  
  :hints (("Goal"
           :use (
                 (:functional-instance strict-int-imc*der-sum-sqrt-is-integral-of-der-sum-sqrt
				       (riemann-imc*der-sum-sqrt riemann-imcircle*der-sum-sqrt)
				       (strict-int-imc*der-sum-sqrt strict-int-imcircle*der-sum-sqrt)
				       (map-imc*der-sum-sqrt map-imcircle*der-sum-sqrt)
				       (imc*der-sum-sqrt imcircle*norm-der)
				       (imc imf)
				       (c circle)
				       (c-derivative circle-der)
				       (rc-derivative rcircle-derivative)
				       (ic-derivative icircle-derivative)
				       (rc-der-sqr rcircle-der-sqr)
				       (der-sum-sqrt-domain circle-der-sum-sqrt-domain)
				       (ic-der-sqr icircle-der-sqr)
				       (der-sqr-sum circle-der-sqr-sum)
				       (der-sum-sqrt circle-der-sum-sqrt)
				       )
                 )
           ))
  )

(defun f1-prime (x)
  (if (inside-interval-p x (circle-der-sum-sqrt-domain))
      (imcircle*norm-der x)
    0)
  )

(defthm f1-prime-=
  (implies (inside-interval-p x (circle-der-sum-sqrt-domain))
	   (and (= (f1-prime x) (* 2 (acl2-pi) (rad) (rad) (acl2-sine x)))
		(= (f1-prime x) (imcircle*norm-der x))))
  
  :hints (("Goal"
	   :use ((:instance circle-der-sum-sqrt-eq)
		 (:instance circle-der-sum-sqrt-domain-real)
		 (:instance f1-prime)
		 (:instance imcircle*norm-der)
		 (:instance imf)
		 (:instance circle-equal)
		 (:instance imagpart-complex (x (* (rad) (acl2-cosine x))) (y (* (rad) (acl2-sine x))))
		 )
	   :in-theory (enable complex-definition)
	   )
	  )
  )

(in-theory (disable f1-prime))

(defun f1 (x)
  (if (inside-interval-p x (circle-der-sum-sqrt-domain))
      (- (* 2 (acl2-pi) (rad) (rad) (acl2-cosine x)))
    0)
  )

(defthm f1-prime-real
  (realp (f1-prime x))
  )

(defthm f1-real
  (realp (f1 x))
  )

(defthm f1-prime-continuous
  (implies (and (standardp x)
		(inside-interval-p x (circle-der-sum-sqrt-domain))
		(i-close x y)
		(inside-interval-p y (circle-der-sum-sqrt-domain)))
	   (i-close (f1-prime x)
		    (f1-prime y)))
  :hints (("Goal"
	   :use ((:instance imcircle*norm-der-continuous)
		 (:instance f1-prime-=)
		 )
	   :in-theory (enable i-close complex-definition)
	   ))
  )

(defun sphere-x (x)
  (* (rad) (acl2-cosine x)))

(defun sphere-y (x)
  (* (rad) (acl2-sine x)))

(defun sx-derivative (x)
  (* (- 1) (rad) (acl2-sine x)))

(defun sy-derivative (x)
  (* (rad) (acl2-cosine x)))

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
	    :use ((:instance rad-det)
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
	    :use ((:instance rad-det)
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
		   (:instance rad-det)
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
		  (:instance rad-det)
		  (:instance rad*norm)
		  (:instance y*y=x->y=sqrt-x (x (* rad rad)) (y (rad)))
		  )
	    ))
   )
 )

(local
 (defthm acl2-pi-limited
   (i-limited (acl2-pi))
   :hints (("Goal"
	    :use ((:instance pi-between-2-4)
		  (:instance limited-squeeze (a 2) (b 4) (x (acl2-pi)))
		  )
	    :in-theory (enable standards-are-limited)
	    ))
   )
 )

(local
 (defthm f1-prime-deri-lemma
   (implies (inside-interval-p x (circle-der-sum-sqrt-domain))
	    (=  (* (imf x)  (circle-der-sum-sqrt x)) (* (rad) (rad) (acl2-sine x))))
   :hints (("Goal"
	    :use ((:instance f1-prime-=)
		  (:instance acl2-pi-limited)
		  (:instance i-limited-times (x 2) (y (acl2-pi)))
		  )
	    :in-theory (disable circle-der-sum-sqrt imf)
	    ))
   )
 )

(defthmd f1-prime-is-derivative-lemma
  (implies (and (standardp x)
		(inside-interval-p x (circle-der-sum-sqrt-domain))
		(inside-interval-p y (circle-der-sum-sqrt-domain))
		(i-close x y)
		(not (= x y))
		)
	   (i-close (- (/ (- (* (rad) (rad) (acl2-cosine x)) (* (rad) (rad) (acl2-cosine y))) (- x y)))
		    (* (imf x) (circle-der-sum-sqrt x)))
	   )
  :hints (("Goal"
	   :use (
		 (:instance norm-of-der)
		 (:instance sx-der-lemma)
		 (:instance rad-det)
		 (:instance standards-are-limited-forward (x (- (rad))))
		 (:instance limited*small->small (x (- (rad))) (y (- (/ (- (sphere-x x) (sphere-x y)) (- x y)) (sx-derivative x))))
		 (:instance i-small-uminus (x (+ (* (RAD) (RAD) (ACL2-SINE X))
						 (* (RAD)
						    (RAD)
						    (ACL2-COSINE X)
						    (/ (+ X (- Y))))
						 (- (* (RAD)
						       (RAD)
						       (ACL2-COSINE Y)
						       (/ (+ X (- Y))))))))
		 (:instance circle-der-sum-sqrt-domain-real)
		 (:instance circle-der-sum-sqrt-domain-real (x y))
		 (:instance circle-der-sum-sqrt-eq)
		 (:instance f1-prime-deri-lemma)
		 )
	   :in-theory (enable complex-definition nsa-theory)
	   ))
  )

(defthmd f1-prime-is-derivative
  (implies (and (standardp x)
		(inside-interval-p x (circle-der-sum-sqrt-domain))
		(inside-interval-p y (circle-der-sum-sqrt-domain))
		(i-close x y)
		(not (= x y))
		)
	   (i-close (/ (- (f1 x) (f1 y)) (- x y)) (f1-prime x)))
  :hints (("Goal"
	   :use ((:instance i-small-plus-lemma
			    (x (- (/ (- (* (rad) (rad) (acl2-cosine x)) (* (rad) (rad) (acl2-cosine y))) (- x y))))
			    (y (* (imf x) (circle-der-sum-sqrt x))))
		 (:instance limited*small->small
			    (x (* 2 (acl2-pi)))
			    (y (- (- (/ (- (* (rad) (rad) (acl2-cosine x)) (* (rad) (rad) (acl2-cosine y))) (- x y)))
				  (* (imf x) (circle-der-sum-sqrt x)))) 
			     )
		 (:instance acl2-pi-limited)
		 (:instance i-limited-times (x 2) (y (acl2-pi)))
		 (:instance i-close (x (/ (- (f1 x) (f1 y)) (- x y))) (y (f1-prime x)))
		 (:instance f1-prime-is-derivative-lemma)
		 (:instance f1-prime-=)
		 )
	   :in-theory (enable-disable (complex-definition nsa-theory) (imf circle-der-sum-sqrt))
	   ))
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

 (local
  (defthm limited-riemann-f1-prime-small-partition
    (implies (and (realp a) (standardp a)
		  (realp b) (standardp b)
		  (inside-interval-p a (circle-der-sum-sqrt-domain))
		  (inside-interval-p b (circle-der-sum-sqrt-domain))
		  (< a b))
	     (i-limited (riemann-f1-prime (make-small-partition a b))))
    :hints (("Goal"
	     :use (:functional-instance limited-riemann-rcfn-small-partition
					(rcfn-domain circle-der-sum-sqrt-domain)
					(rcfn f1-prime)
					(map-rcfn map-f1-prime)
					(riemann-rcfn riemann-f1-prime)))
	    ("Subgoal 2"
	     :use ((:instance circle-der-sum-sqrt-domain-non-trivial)
		   (:instance f1-prime-continuous)))
	    
	    ("Subgoal 4"
	     :use ((:instance norm-of-der)
		   (:instance norm-of-der (x y))
		   (:instance f1-prime-continuous)))
	    
	    ("Subgoal 3"
	     :use ((:instance norm-of-der)
		   (:instance norm-of-der (x y))
		   (:instance rad-det)
		   (:instance f1-prime-continuous)))
	    )))

 (local (in-theory (disable riemann-f1-prime)))

 (defun-std strict-int-f1-prime (a b)
   (if (and (realp a)
	    (realp b)
	    (inside-interval-p a (circle-der-sum-sqrt-domain))
	    (inside-interval-p b (circle-der-sum-sqrt-domain))
	    (< a b))
       (standard-part (riemann-f1-prime (make-small-partition a b)))
     0))
 )

(defun int-f1-prime (a b)
  (if (<= a b)
      (strict-int-f1-prime a b)
    (- (strict-int-f1-prime b a))))

(defthm apply-ftc-2-s-area
  (implies (and (inside-interval-p a (circle-der-sum-sqrt-domain))
		(inside-interval-p b (circle-der-sum-sqrt-domain)))
	   (equal (int-f1-prime a b)
		  (- (f1 b)
		     (f1 a))))
  :hints (("Goal"
	   :use (
		 (:functional-instance ftc-2
				       (rcdfn-domain circle-der-sum-sqrt-domain)
				       (rcdfn f1)
				       (rcdfn-prime f1-prime)
				       (map-rcdfn-prime map-f1-prime)
				       (int-rcdfn-prime int-f1-prime)
				       (riemann-rcdfn-prime riemann-f1-prime)
				       (strict-int-rcdfn-prime strict-int-f1-prime)
				       ))
	   )
	  ("Subgoal 6"
	   :use ((:instance norm-of-der)
		 (:instance f1-prime-is-derivative (x x) (y x1)))
	   )
	  ("Subgoal 7"
	   :use ((:instance norm-of-der)
		 (:instance f1-prime-continuous (x x) (y x1))))
	  ))

(defun surface-area-of-a-sphere ()
  (int-f1-prime 0 (acl2-pi))
  )

(defthm surface-area-of-a-sphere-equals
  (= (surface-area-of-a-sphere) (* 4 (acl2-pi) (rad) (rad)))
  :hints (("Goal"
	   :use ((:instance apply-ftc-2-s-area (a 0) (b (acl2-pi)))
		 (:instance rad-det)
		 (:instance pi-between-2-4)
		 )
	   :in-theory (enable nsa-theory interval-definition-theory)
	   ))
  )
