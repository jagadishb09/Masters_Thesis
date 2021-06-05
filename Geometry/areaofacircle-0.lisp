; Area of a Circle
; Application of Intgration by Substitution
; reference : https://en.wikipedia.org/wiki/Area_of_a_circle
;
; Copyright (C) 2021 University of Wyoming
;
;
; Main Author: Jagadish Bapanapally (jagadishb285@gmail.com)
; Contributing Authors:
;   Ruben Gamboa (ruben@uwyo.edu)

(in-package "ACL2")

; cert_param: (uses-acl2r)

(local (include-book "arithmetic/realp" :dir :system))
(local (include-book "arithmetic/inequalities" :dir :system))
(include-book "nonstd/nsa/inverse-square" :dir :system)
(include-book "nonstd/nsa/inverse-trig" :dir :system)
(include-book "nonstd/integrals/u-substitution" :dir :system)

(encapsulate
 ((rad() t)
  (consta1 () t)
  )
 (local (defun rad() 1))
 (local (defun fi-dom-variable() 5))
 (local (defun consta1() 1))

 (defthm rad-def
   (and (realp (rad))
	(> (rad) 0)
	(standardp (rad))
	)
   )

 (defthmd consta1-def
   (and (inside-interval-p (consta1) (interval 0 (rad)))
	(standardp (consta1))
	)
   :hints (("Goal"
	    :in-theory (enable interval-definition-theory)
	    ))
   )
 )

(defun circle-x-domain() (interval 0 (rad)))

(defun fi-domain() (interval 0 (* 1/2 (acl2-pi))))

(defun circle (x)
  (acl2-sqrt (- (* (rad) (rad)) (* x x)))
  )

(defun sub-func (x)
  (if (inside-interval-p x (fi-domain))
      (* (rad) (acl2-sine x))
    0)
  )

(defun sub-func-prime (x)
  (if (inside-interval-p x (fi-domain))
      (* (rad) (acl2-cosine x))
    0)
  )


(defthm-std c-domain-standard
  (standardp (circle-x-domain))
  )

(defthm-std fi-domain-standard
  (standardp (fi-domain))
  )

(defthm-std circle-standard
  (implies (standardp x)
	   (standardp (circle x))))

(defthm-std sub-func-standard
  (implies (standardp x)
	   (standardp (sub-func x))))

(defthm-std sub-func-prime-standard
  (implies (standardp x)
	   (standardp (sub-func-prime x))))


(local
 (defthm c-domain-interval-lemma
   (implies (and (realp x)
		 (> x 0)
		 )
	    (< (- x) 0)
	    )
   )
 )

(defthm intervalp-c-domain
  (interval-p (circle-x-domain))
  :hints(("Goal"
	  :use (:instance c-domain-interval-lemma
			  (x (rad)))
	  :in-theory (enable interval-definition-theory)
	  ))
  )

(defthm c-domain-real
  (implies (inside-interval-p x (circle-x-domain))
	   (realp x)))

(defthm c-domain-non-trivial
  (or (null (interval-left-endpoint (circle-x-domain)))
      (null (interval-right-endpoint (circle-x-domain)))
      (< (interval-left-endpoint (circle-x-domain))
	 (interval-right-endpoint (circle-x-domain))))
  )

(defthm intervalp-fi-domain
  (interval-p (fi-domain))
  :hints(("Goal"
	  :use (:instance pi-between-2-4)
	  )))

(defthm fi-domain-real
  (implies (inside-interval-p x (fi-domain))
	   (realp x))
  )

(defthm fi-domain-non-trivial
  (or (null (interval-left-endpoint (fi-domain)))
      (null (interval-right-endpoint (fi-domain)))
      (< (interval-left-endpoint (fi-domain))
	 (interval-right-endpoint (fi-domain))))
  )

(local
 (defthm sine-bound
   (implies (realp x)
	    (and (<= -1 (acl2-sine x))
		 (<= (acl2-sine x) 1)))
   :hints (("Goal"
	    :use ((:instance cosine-bound
			     (x (+ (* 1/2 (acl2-pi)) (- x))))
		  (:instance cos-pi/2-x (x x)))
	    :in-theory (disable cosine-bound cos-pi/2-x)))))

(local
 (defthm lemma-1
   (implies (and (realp y)
		 (realp x)
		 (realp z)
		 (>= x (rad))
		 (>= y z)
		 )
	    (>= (* x y) (* x z))
	    )
   )
 )

(local
 (defthm sub-func-range
   (implies (realp x)
	    (and (<= 0 (sub-func x))
		 (<= (sub-func x) (rad))))
   :hints (("Goal"
	    :use ((:instance sine-bound)
		  (:instance  rad-def)
		  (:instance sine-positive-in-0-pi/2)
		  (:instance lemma-1
			     (x (rad))
			     (z (acl2-sine x))
			     (y 1))
		  (:instance sine-0)
		  )
	    )
	   ("Subgoal 9"
	    :in-theory (enable interval-definition-theory)
	    )
	   ("Subgoal 3"
	    :in-theory (enable interval-definition-theory)
	    )
	   )
   ))

(defthm circle-domain-in-domain-of-fi
  (implies (inside-interval-p x (fi-domain))
	   (inside-interval-p (sub-func x) (circle-x-domain)))
  :hints (("Goal"
	   :use (
		 (:instance sub-func-range)
		 (:instance intervalp-c-domain)
		 (:instance c-domain-real)
		 )
	   :in-theory (enable interval-definition-theory)
	   ))
  )

(defthm circle-real
  (realp (circle x))
  )

(defthm sub-func-real
  (realp (sub-func x))
  )

(defthm sub-func-prime-real
  (realp (sub-func-prime x))
  )



(local
 (defthm lemma-7
   (implies (acl2-numberp x)
	    (equal (+ (standard-part x) (non-standard-part x)) x)
	    )
   :hints (("Goal"
	    :in-theory (enable non-standard-part)
	    ))
   )
 )

(local
 (defthm lemma-8
   (implies (and
	     (i-limited x)
	     (i-limited y)
	     (realp x)
	     (realp y)
	     (= (standard-part x) (standard-part y)))
	    (i-small (- x y)))
   :hints (("Goal"
	    :use ((:instance lemma-7 (x x))
		  (:instance lemma-7 (x y))
		  (:instance i-small-non-standard-part (x x))
		  (:instance i-small-non-standard-part (x y))
		  (:instance i-small-plus
			     (x (non-standard-part x))
			     (y (- (non-standard-part y))))
		  (:instance i-small-uminus (x (non-standard-part y)))
		  (:instance fix (x (non-standard-part y)))
		  (:instance i-small (x 0))
		  )
	    ))
   )
 )

(defthmd root-close-lemma
  (implies (and (realp y1)
		(realp y2)
		(not (= (standard-part y1) (standard-part y2)))
		)
	   (not (i-close y1 y2))
	   )
  :hints (("Goal"
	   :in-theory (enable i-close i-small)
	   ))
  )

(defthmd root-close-lemma-1
  (implies (and (realp y1)
		(realp y2)
		(not (i-close y1 y2))
		)
	   (not (= (standard-part y1) (standard-part y2)))
	   )
  :hints (("Goal"
	   :in-theory (enable i-close i-small)
	   ))
  )

(local
 (defthm ineq-lemma1
   (implies (and (realp x1)
		 (realp x2)
		 (>= x1 0)
		 (>= x2 0)
		 (> x1 x2)
		 )
	    (> (* x1 x1) (* x1 x2)))
   ))

(local
 (encapsulate
  ()

  (local (in-theory nil))
  (local (include-book "arithmetic-5/top" :dir :system))
  (local (include-book "arithmetic/inequalities" :dir :system))

  (local
   (defthm ineq-lemma2-1
     (implies (and (realp a)
		   (realp b)
		   (realp c)
		   (>= a 0)
		   (>= b 0)
		   (< (* a c) (* b c))
		   (> c 0))
	      (< a b))
     :hints (("Goal"
	      :use (:instance <-*-right-cancel (x a) (y b) (z c))))))
  
  (defthm ineq-lemma2
    (implies (and (realp x1)
		  (realp x2)
		  (>= x1 0)
		  (>= x2 0)
		  (< x2 x1)
		  )
	     (>= (* x1 x2) (* x2 x2)))
    :hints (("Goal"
	     :use (:instance ineq-lemma2-1 (a x1) (b x2) (c x2))
	     ))
    )))

(local
 (defthm ineq-lemma3
   (implies (and (realp a)
		 (realp b)
		 (realp c)
		 (> a b)
		 (>= b c))
	    (> a c))
   ))


(local
 (defthm ineq-lemma4
   (implies (and (realp x1)
		 (realp x2)
		 (>= x1 0)
		 (>= x2 0)
		 (> x1 x2))
	    (> (* x1 x1) (* x2 x2)))

   :hints (("Goal"

	    :use (
		  (:instance ineq-lemma1 (x1 x1) (x2 x2))
		  (:instance ineq-lemma2 (x1 x1) (x2 x2))
		  (:instance ineq-lemma3 (a (* x1 x1)) (b (* x1 x2)) (c (* x2 x2)))
		  )
	    :in-theory nil
	    ))
   ))

(local
 (defthm root-close-lemma-2
   (implies (and (realp y1)
		 (realp y2)
		 (i-limited y1)
		 (i-limited y2)
		 (>= y1 0)
		 (>= y2 0)
		 (not (i-close y1 y2)))
	    (not (= (* (standard-part y1) (standard-part y1)) (* (standard-part y2) (standard-part y2))))
	    )
   :hints (("Goal"
	    :use (
		  (:instance root-close-lemma-1 (y1 y1) (y2 y2))
		  (:instance ineq-lemma4 (x1 (standard-part y1)) (x2 (standard-part y2)))
		  (:instance ineq-lemma4 (x1 (standard-part y2)) (x2 (standard-part y1)))
		  )
	    :in-theory nil
	    ))
   ))

(local
 (defthm square-is-standard
   (implies (and (i-limited y1)
		 (realp y1))
	    (equal (* (standard-part y1) (standard-part y1))
		   (standard-part (square y1))
		   ))

   ))

(local
 (defthm root-close-lemma-3
   (implies (and (realp y1)
		 (realp y2)
		 (i-limited y1)
		 (i-limited y2)
		 (>= y1 0)
		 (>= y2 0)
		 (not (i-close y1 y2))
		 )
	    (not (= (standard-part (square y1)) (standard-part (square y2)))))

   :hints (("Goal"
	    :use (
		  (:instance root-close-lemma-2 (y1 y1) (y2 y2))
		  (:instance square-is-standard (y1 y1))
		  (:instance square-is-standard (y1 y2))
		  )
	    :in-theory nil
	    ))
   ))


(local
 (defthm sqr-real-lemma
   (implies (realp x)
	    (realp (square x)))
   ))


(local
 (defthm root-close-lemma-6
   (implies (and (realp y1)
		 (realp y2)
		 (i-limited y1)
		 (i-limited y2)
		 (>= y1 0)
		 (>= y2 0)
		 (not (i-close y1 y2))
		 )
	    (not (i-close (square y1) (square y2))))

   :hints (("Goal"
	    :use (
		  (:instance root-close-lemma-3 (y1 y1) (y2 y2))
		  (:instance root-close-lemma (y1 (square y1)) (y2 (square y2)))
		  (:instance sqr-real-lemma (x y1))
		  (:instance sqr-real-lemma (x y2))
		  )
	    :in-theory nil
	    ))
   ))

(local
 (defthm sqrt-real-lemma
   (implies (realp x)
	    (realp (acl2-sqrt x)))
   ))

(local
 (defthm sqrt>=0-lemma
   (implies (and (i-limited x)
		 (realp x))
	    (>= (acl2-sqrt x) 0))
   ))

(local
 (defthm root-close-f
   (implies
    (and (standardp x1)
	 (realp x1)
	 (realp x2)
	 (>= x1 0)
	 (>= x2 0)
	 (i-close x1 x2)
	 )
    (i-close (acl2-sqrt x1) (acl2-sqrt x2))
    )
   :hints (("Goal"
	    :use (
		  (:definition square)
		  (:instance STANDARDS-ARE-LIMITED-FORWARD (x x1))
		  (:instance i-close-limited-2 (y x1) (x x2))
		  (:instance sqrt-real-lemma (x x1))
		  (:instance sqrt-real-lemma (x x2))
		  (:instance limited-sqrt (x x1))
		  (:instance limited-sqrt (x x2))
		  (:instance sqrt>=0-lemma (x x1))
		  (:instance sqrt>=0-lemma (x x2))
		  (:instance root-close-lemma-6 (y1 (acl2-sqrt x1) ) (y2 (acl2-sqrt x2)))
		  )
	    ))


   ))

(local
 (defthm lemma-3
   (implies (and (i-limited x)
		 (i-close y1 y2))
	    (i-close (* x y1) (* x y2)))
   :hints (("Goal"
	    :in-theory (enable i-close))
	   ("Goal''"
	    :use ((:instance limited*small->small
			     (y (+ y1 (- y2)))))
	    :in-theory (disable limited*small->small)))))

(defthm sub-func-prime-continuous
  (implies (and (standardp x)
		(inside-interval-p x (fi-domain))
		(i-close x x1)
		(inside-interval-p x1 (fi-domain)))
	   (i-close (sub-func-prime x)
		    (sub-func-prime x1)))

  :hints (("Goal"
	   :use (
		 (:instance rad-def)
		 (:instance standards-are-limited-forward
			    (x (rad))
			    )
		 (:instance sine-continuous
			    (x x)
			    (y x1))
		 (:instance lemma-3
			    (x (rad))
			    (y1 (acl2-sine x))
			    (y2 (acl2-sine x1))
			    )
		 )
	   ))
  )

(local
 (defthm lemma-4
   (implies (i-close x y)
	    (i-small (- x y))
	    )
   :hints (("Goal"
	    :in-theory (enable i-small i-close)
	    ))
   )
 )

(local
 (defthm lemma-5
   (implies (and (acl2-numberp x)
		 (acl2-numberp y)
		 (i-small (- x y))
		 )
	    (i-close x y)
	    )
   :hints (("Goal"
	    :in-theory (enable i-small i-close)
	    ))
   )
 )

(encapsulate
 ()
 (local (include-book "nonstd/workshops/2011/reid-gamboa-differentiator/support/exp-minimal" :dir :system))

 (local
  (defthm-std acl2-exp-standard
    (implies (standardp x)
	     (standardp (acl2-exp x))))
  )

 (defthmd cosine-standard
   (implies (standardp x)
	    (standardp (acl2-cosine x)))
   :hints (("Goal"
	    :use (:instance acl2-exp-standard)
	    :in-theory (enable acl2-cosine))))

 (local
  (defderivative sin-eqn-deriv
    (/ (- (acl2-exp (* #c(0 1) x))
	  (acl2-exp (* #c(0 -1) x)))
       #c(0 2))))


 (defthm acl2-sine-derivative
   (implies (and (acl2-numberp x)
		 (acl2-numberp y)
		 (standardp x)
		 (i-close x y)
		 (not (equal x y)))
	    (i-close (/ (- (acl2-sine x) (acl2-sine y))
			(- x y))
		     (acl2-cosine x)))
   :hints (("Goal" :use (:instance sin-eqn-deriv)
	    :in-theory (enable acl2-sine acl2-cosine))))

 (local
  (defderivative cos-eqn-deriv
    (/ (+ (ACL2-EXP (* #C(0 1) X))
	  (ACL2-EXP (* #C(0 -1) X)))
       2)))

 (defthm acl2-cosine-derivative
   (implies (and (acl2-numberp x)
		 (acl2-numberp y)
		 (standardp x)
		 (i-close x y)
		 (not (equal x y)))
	    (i-close (/ (- (acl2-cosine x) (acl2-cosine y))
			(- x y))
		     (- (acl2-sine x))))
   :hints (("Goal" :use (:instance cos-eqn-deriv)
	    :in-theory (enable acl2-sine acl2-cosine))))
 )

(defthm sub-func-prime-is-derivative
  (implies (and (standardp x)
		(inside-interval-p x (fi-domain))
		(inside-interval-p x1 (fi-domain))
		(i-close x x1) (not (= x x1)))
	   (i-close (/ (- (sub-func x) (sub-func x1)) (- x x1))
		    (sub-func-prime x)))
  :hints (("Goal"
	   :use (
		 (:instance rad-def)
		 (:instance standards-are-limited-forward
			    (x (rad)))
		 (:instance acl2-sine-derivative
			    (x x)
			    (y x1))
		 (:instance lemma-4
			    (x (/ (- (acl2-sine x) (acl2-sine x1)) (- x x1)))
			    (y (acl2-cosine x)))
		 (:instance limited*small->small
			    (x (rad))
			    (y (- (/ (- (acl2-sine x) (acl2-sine x1)) (- x x1)) (acl2-cosine x))))
		 (:instance lemma-5
			    (x (* (rad) (/ (- (acl2-sine x) (acl2-sine x1)) (- x x1))))
			    (y (* (rad) (acl2-cosine x))))
		 )
	   ))
  )

(defthm sub-func-differentiable
  (implies (and (standardp x)
		(inside-interval-p x (fi-domain))
		(inside-interval-p y1 (fi-domain))
		(inside-interval-p y2 (fi-domain))
		(i-close x y1) (not (= x y1))
		(i-close x y2) (not (= x y2)))
	   (and (i-limited (/ (- (sub-func x) (sub-func y1)) (- x y1)))
		(i-close (/ (- (sub-func x) (sub-func y1)) (- x y1))
			 (/ (- (sub-func x) (sub-func y2)) (- x y2)))))
  :hints (("Goal"
	   :use(
		(:definition sub-func-prime)
		(:instance fi-domain-real)
		(:instance rad-def)
		(:instance standards-are-limited-forward
			   (x (rad)))
		(:instance cosine-standard)
		(:instance realp-cosine)
		(:instance standards-are-limited-forward
			   (x (acl2-cosine x))
			   )
		(:instance i-limited-times
			   (x (rad))
			   (y (acl2-cosine x))
			   )
		(:instance sub-func-prime-is-derivative
			   (x x)
			   (x1 y1))
		(:instance i-close-limited
			   (x (* (rad) (acl2-cosine x)))
			   (y (/ (- (sub-func x) (sub-func y1)) (- x y1)))
			   )
		(:instance sub-func-prime-is-derivative
			   (x x)
			   (x1 y2))
		(:instance i-close-symmetric
			   (x (/ (- (sub-func x) (sub-func y1)) (- x y1)))
			   (y (sub-func-prime x))
		 	   )
		(:instance i-close-symmetric
			   (x (/ (- (sub-func x) (sub-func y2)) (- x y2)))
			   (y (sub-func-prime x))
		 	   )
		(:instance i-close-transitive
			   (x (/ (- (sub-func x) (sub-func y1)) (- x y1)))
			   (y (sub-func-prime x))
			   (z (/ (- (sub-func x) (sub-func y2)) (- x y2)))
			   )
		)
	   :in-theory nil
	   ))
  )

(local
 (defthm square-lemma-1
   (IMPLIES (AND (realp x1)
		 (realp x2)
		 (<= 0 x1)
		 (< x1 x2))
	    (< (* X1 X1) (* X2 X2)))
   :hints (("Goal"
	    :cases ((< 0 x1))))))

(local
 (defthm ineq-lemma-5
   (IMPLIES (AND (realp x1)
		 (realp x2)
		 (> 0 x1)
		 (> 0 x2)
		 (> x1 x2))
	    (> (* X1 X2) (* X1 X1)))
   )
 )

(local
 (defthm ineq-lemma-6
   (IMPLIES (AND (realp x1)
		 (realp x2)
		 (> 0 x1)
		 (> 0 x2)
		 (> x1 x2))
	    (> (* X2 X2) (* X1 X2)))
   )
 )

(local
 (defthm square-lemma-2
   (IMPLIES (AND (realp x1)
		 (realp x2)
		 (> 0 x1)
		 (> x1 x2))
	    (> (* X2 X2) (* X1 X1)))
   :hints (("Goal"
	    :use ((:instance ineq-lemma-5
			     (x1 x1)
			     (x2 x2))
		  (:instance ineq-lemma-6
			     (x1 x1)
			     (x2 x2))
		  (:instance ineq-lemma3 (a (* x2 x2)) (b (* x1 x2)) (c (* x1 x1)))
		  )
	    ))
   ))

(local
 (defthm square-lemma-3
   (implies (and (realp x)
		 (> x (- (rad)))
		 (< x (rad))
		 )
	    (< (* x x) (* (rad) (rad))))
   :hints (("Goal"
	    :use ((:instance square-lemma-1
			     (x2 (rad))
			     (x1 x))
		  (:instance square-lemma-2
			     (x2 (-(rad)))
			     (x1 x))
		  )
	    ))
   )
 )

(local
 (defthm square-lemma-4
   (implies (and (realp x)
		 (or (= (- x)  (rad))
		     (= x  (rad)))
		 )
	    (= (* x x) (* (rad) (rad))))
   )
 )

(local
 (defthm square-lemma-6
   (implies (and (realp x)
		 (and  (>= x (- (rad)))
		       (<= x (rad))))
	    (equal (or (and  (> x (- (rad)))
			     (< x (rad)))
		       (= x (rad))
		       (= x (-(rad))))

		   (and  (>= x (- (rad)))
			 (<= x (rad)))))
   :hints (("Goal"
	    :use ((:instance rad-def)
		  )))
   )
 )

(local
 (defthm square-lemma-7
   (implies (realp x)
	    (= (* x x) (* (- x) (- x)))
	    )
   )
 )

(local
 (defthm square-lemma-8
   (implies (and (realp x)
		 (>= x (- (rad)))
		 (<= x (rad)))
	    (<= (* x x) (* (rad) (rad)))
	    )
   :hints (("Goal"
	    :use ((:instance rad-def)
		  (:instance square-lemma-6)
		  (:instance square-lemma-3)
		  (:instance square-lemma-4)
		  (:instance square-lemma-7 (x (rad)))
		  )
	    :in-theory nil
	    ))
   )
 )

(local
 (defthm c-domain-lemma
   (equal (interval-right-endpoint (circle-x-domain)) (rad))
   :hints (("Goal"
	    :in-theory
	    (enable (interval-right-endpoint))
	    ))
   )
 )

(local
 (defthm c-domain-lemma-1
   (equal (interval-left-endpoint (circle-x-domain)) 0)
   :hints (("Goal"
	    :in-theory
	    (enable (interval-left-endpoint))
	    ))
   )
 )

(local
 (defthm circle-continuous-lemma-1
   (implies (inside-interval-p x (circle-x-domain))
	    (and (>= x 0)
		 (<= x (rad)))
	    )
   :hints (("Goal"
	    :use (
		  (:definition circle-x-domain)
		  (:instance c-domain-lemma)
		  (:instance c-domain-lemma-1)
		  (:instance INSIDE-INTERVAL-P
			     (x x)
			     (interval (circle-x-domain))
			     )
		  (:instance c-domain-real)
		  (:instance rad-def)
		  )
	    :in-theory nil
	    ))
   )
 )

(local
 (defthm circle-continuous-lemma-2
   (implies (inside-interval-p x (circle-x-domain))
	    (<=  (* x x) (* (rad) (rad)))
	    )
   :hints (("Goal"
	    :use (
		  (:instance square-lemma-8)
		  (:instance circle-continuous-lemma-1)
		  (:instance (:instance c-domain-real)
			     )
		  )
	    :in-theory nil
	    ))
   )
 )

(local
 (defthm circle-continuous-lemma-3
   (implies (and (standard-numberp x)
		 (standard-numberp x1)
		 )
	    (standard-numberp (- (* x x) (* x1 x1))))
   )
 )

(local
 (defthm lemma-6
   (implies (realp x)
	    (equal (fix (- x)) (- x)))
   )
 )

(local
 (defthm circle-continuous-lemma-4
   (implies (and (realp x)
		 (realp y)
		 (i-close x y)
		 (realp z)
		 (standardp z)
		 (i-limited x))
	    (and (equal (- (standard-part z) (standard-part x)) (standard-part (- z x)))
		 (equal (- (standard-part z) (standard-part y)) (standard-part (- z y)))
		 (equal (standard-part (- z x)) (standard-part (- z y)))
		 )
	    )
   :hints (("Goal"
	    :use (
		  (:instance lemma-6 (x x))
		  (:instance lemma-6 (x y))
		  (:instance FIx(x z))
		  (:instance STANDARD-PART-OF-PLUS (x z) (y (- x)))
		  (:instance STANDARD-PART-OF-STANDARDP (x z))
		  (:instance STANDARD-PART-OF-UMINUS(x x))
		  (:instance STANDARD-PART-OF-PLUS (x z) (y (- y)))
		  (:instance STANDARD-PART-OF-STANDARDP(x z))
		  (:instance STANDARD-PART-OF-UMINUS(x y))
		  (:instance STANDARD-PART-OF-STANDARDP (x z))
		  (:instance standard-part-of-uminus (x x))
		  (:instance standard-part-of-uminus (x y))
		  (:instance FIx(x x))
		  (:instance FIx(x y))
		  (:instance close-x-y->same-standard-part
			     (x x)
			     (y y)
			     )
		  (:instance standard-part-of-uminus
			     (x x))
		  (:instance standard-part-of-uminus
			     (x y))
		  )
	    :in-theory nil
	    )
	   ("Subgoal 2"
	    :use ((:instance STANDARD-PART-OF-STANDARDP (x z))
		  (:instance standard-part-of-uminus (x x))
		  (:instance standard-part-of-uminus (x y))
		  (:instance FIx(x x))
		  )
	    )

	   ("Subgoal 4"
	    :use (
		  (:instance close-x-y->same-standard-part
			     (x x)
			     (y y)
			     ))
	    )
	   )
   ))

(local
 (defthm i-close-plus-lemma-2
   (implies (and (acl2-numberp x)
		 (acl2-numberp y)
		 (i-small (- x y))
		 )
	    (i-close x y))

   :hints (("Goal"
   	    :use (
   		  (:instance i-close (x x) (y y))
   		  )
	    :in-theory nil
   	    ))
   )
 )

(local
 (defthm circle-continuous-lemma-5
   (implies (and (realp x)
		 (realp y)
		 (i-close x y)
		 (realp z)
		 (i-limited z)
		 (i-limited x)
		 (i-limited y)
		 (standardp z))
	    (i-close (- z x) (- z y))
	    )
   :hints (("Goal"
	    :use ((:instance circle-continuous-lemma-4)
		  (:instance lemma-8
			     (x (- z x))
			     (y (- z y))
			     )
		  (:instance i-limited-plus
			     (x z)
			     (y (- x)))
		  (:instance i-limited-plus
			     (x z)
			     (y (- y)))
		  (:instance i-large-uminus (x x))
		  (:instance i-large-uminus (x y))
		  (:instance i-close-plus-lemma-2
			     (x (- z x))
			     (y (- z y))
			     )
		  )
	    :in-theory nil
	    ))
   )
 )


(local
 (defthm circle-continuous-lemma-6
   (implies (and (standardp x)
		 (inside-interval-p x (circle-x-domain))
		 (i-close x x1)
		 (inside-interval-p x1 (circle-x-domain)))
	    (i-close (- (* (rad) (rad)) (* x x)) (- (* (rad) (rad)) (* x1 x1)))
	    )
   :hints (("Goal"
	    :use (
		  (:instance c-domain-real (x x))
		  (:instance c-domain-real (x x1))
		  (:instance square-is-continuous
			     (x1 x)
			     (x2 x1))
		  (:instance rad-def)
		  (:instance STANDARDS-ARE-LIMITED-FORWARD (x x))
		  (:instance STANDARDS-ARE-LIMITED-FORWARD (x (rad)))
		  (:instance circle-continuous-lemma-5
			     (x (* x x))
			     (y (* x1 x1))
			     (z (* (rad) (rad)))
			     )
		  (:instance i-limited-times (x (rad))
			     (y (rad)))
		  (:instance i-limited-times (x x)
			     (y x))
		  (:instance i-limited-times (x x1)
			     (y x1))
		  (:instance i-close-limited
			     (x x)
			     (y x1)
			     )
		  (:instance standardp-times
			     (x (rad))
			     (y (rad)))
		  )
	    :in-theory nil
	    ))
   )
 )


(local
 (defthm lemma-9
   (implies (and
	     (acl2-numberp x)
	     (acl2-numberp y)
	     (standardp x)
	     (standardp y))
	    (standardp (+ x y))
	    )
   )
 )

(local
 (defthm lemma-10
   (implies (and
	     (acl2-numberp x)
	     (standardp x))
	    (standardp (- x))
	    )
   )
 )

(local
 (defthm lemma-11
   (implies (realp x)
	    (equal (realfix x) x)
	    )
   )
 )

(defthm circle-continuous
  (implies (and (standardp x)
		(inside-interval-p x (circle-x-domain))
		(i-close x x1)
		(inside-interval-p x1 (circle-x-domain)))
	   (i-close (circle x)
		    (circle x1)))
  :hints (("Goal"
	   :use (
		 (:instance square (x (rad)))
		 (:instance square (x x))
		 (:instance square (x x1))
		 (:instance circle (x x))
		 (:instance circle (x x1))
		 (:instance circle-continuous-lemma-2 (x x))
		 (:instance circle-continuous-lemma-2 (x x1))
		 (:instance root-close-f (x1 (- (* (rad) (rad)) (* x x)))
			    (x2 (- (* (rad) (rad)) (* x1 x1))))
		 (:instance rad-def)
		 (:instance c-domain-real (x x))
		 (:instance c-domain-real (x x1))
		 (:instance circle-continuous-lemma-6)
		 (:instance standardp-times
			    (x (rad))
			    (y (rad)))
		 (:instance standardp-times
			    (x x)
			    (y x))
		 (:instance standard-part-of-plus
			    (x (* (rad) (rad)))
			    (y (- (* x x)))
			    )
		 (:instance lemma-6 (x (* x x)))
		 (:instance standard-part-of-plus
			    (x (* (rad) (rad)))
			    (y (- (* x1 x1)))
			    )
		 (:instance lemma-6 (x (* x1 x1)))
		 (:instance fix (x (* (rad) (rad))))
		 (:instance standardp-standard-part
			    (x (* (rad) (rad))))
		 (:instance standardp-standard-part
			    (x (* x x)))
		 (:instance standardp-standard-part
			    (x (+ (* (RAD) (RAD)) (- (* X X)))))
		 (:instance STANDARDS-ARE-LIMITED-FORWARD (x x))
		 (:instance STANDARDS-ARE-LIMITED-FORWARD (x (rad)))
		 (:instance i-limited-times
			    (x (rad))
			    (y (rad)))
		 (:instance i-limited-times
			    (x x)
			    (y x))
		 (:instance i-limited-plus
			    (x (* (rad) (rad)))
			    (y (- (* x x))))
		 (:instance i-large-uminus
			    (x (* x x)))
		 (:instance lemma-9
			    (x (* (rad) (rad)))
			    (y (- (* x x)))
			    )
		 (:instance lemma-10
			    (x (* x x))
			    )
		 (:instance realp-*
			    (x x)
			    (y x)
			    )
		 (:instance realp-*
			    (x (rad))
			    (y (rad))
			    )
		 (:instance realp-*
			    (x x1)
			    (y x1)
			    )
		 (:instance lemma-11 (x (* x x)))
		 (:instance lemma-11 (x (* x1 x1)))
		 (:instance lemma-11 (x (* (rad) (rad))))
		 )
	   :in-theory nil
	   ))
  )

(encapsulate
 (((circle-sub-derivative *) => *))

 (local
  (defun circle-sub-derivative (x)
    (* (circle (sub-func x)) (sub-func-prime x))
    ))

 (defthm derivative-circle-sub-definition
   (implies (inside-interval-p x (fi-domain))
	    (equal (circle-sub-derivative x)
		   (* (circle (sub-func x))
		      (sub-func-prime x))))
   :hints (("Goal"
	    :use (:functional-instance derivative-cr-f-o-fi-definition
				       (f-o-fi-domain fi-domain)
				       (f-prime circle)
				       (fi sub-func)
				       (fi-prime sub-func-prime)
				       (fi-range circle-x-domain)
				       (DERIVATIVE-CR-F-O-FI circle-sub-derivative)
				       (consta consta1)
				       )
	    )
	   ("Subgoal 10"
	    :use (:instance circle-domain-in-domain-of-fi)
	    )
	   ("Subgoal 9"
	    :use (:instance intervalp-fi-domain)
	    )
	   ("Subgoal 8"
	    :use (:instance sub-func-differentiable)
	    )
	   ("Subgoal 7"
	    :use (:instance intervalp-c-domain)
	    )
	   ("Subgoal 6"
	    :use (:instance sub-func-prime-continuous)
	    )
	   ("Subgoal 5"
	    :use (:instance sub-func-prime-is-derivative)
	    )
	   ("Subgoal 4"
	    :use (:instance circle-continuous)
	    )
	   ("Subgoal 3"
	    :use (:instance consta1-def)
	    )
	   ("Subgoal 2"
	    :use (:instance consta1-def)
	    )
	   ("Subgoal 1"
	    :use (:instance circle-sub-derivative(x x))
	    )
	   )
   )
 )

(defun circle-sub-prime (x)
  (if (inside-interval-p x (fi-domain))
      (circle-sub-derivative x)
    0)
  )

(defun map-circle-sub-prime (p)
  (if (consp p)
      (cons (circle-sub-prime (car p))
	    (map-circle-sub-prime (cdr p)))
    nil))

(defun riemann-circle-sub-prime (p)
  (dotprod (deltas p)
	   (map-circle-sub-prime (cdr p))))

(encapsulate
 nil

 (local
  (defthm limited-riemann-circle-sub-prime-small-partition
    (implies (and (realp a) (standardp a)
		  (realp b) (standardp b)
		  (inside-interval-p a (fi-domain))
		  (inside-interval-p b (fi-domain))
		  (< a b))
	     (standardp (standard-part (riemann-circle-sub-prime (make-small-partition a b)))))
    :hints (("Goal"
 	     :use (:functional-instance limited-riemann-F-o-fi-prime-small-partition
					(f-o-fi-domain fi-domain)
					(F-o-fi-prime circle-sub-prime)
					(map-f-o-fi-prime map-circle-sub-prime)
					(riemann-f-o-fi-prime riemann-circle-sub-prime)
					(DERIVATIVE-CR-F-O-FI circle-sub-derivative)
					(fi-range circle-x-domain)
					(consta  consta1)
					(f-prime circle)
					(fi sub-func)
					(fi-prime sub-func-prime)
					))
	    ("Goal"
	     :use (
		   (:instance riemann-circle-sub-prime)
		   (:instance map-circle-sub-prime)
		   (:instance circle-sub-prime)
		   (:instance derivative-circle-sub-definition)
		   (:instance fi-domain)
		   (:instance circle-domain-in-domain-of-fi)
		   (:instance intervalp-fi-domain)
		   (:instance sub-func-differentiable)
		   (:instance intervalp-c-domain)
		   (:instance sub-func-prime-continuous)
		   (:instance sub-func-prime-is-derivative)
		   (:instance circle-continuous)
		   (:instance consta1-def)
		   )
	     )

 	    ("Subgoal 13"
 	     :use (:instance riemann-circle-sub-prime)
 	     :in-theory (enable dotprod)
 	     )
 	    ("Subgoal 12"
 	     :use (:instance map-circle-sub-prime)
 	     )
 	    ("Subgoal 11"
 	     :use (:instance circle-sub-prime)
 	     )
 	    ("Subgoal 10"
 	     :use ((:instance derivative-circle-sub-definition)
 	    	   (:instance fi-domain)
 	    	   )
 	     )
 	    ("Subgoal 9"
 	     :use (:instance circle-domain-in-domain-of-fi)
 	     )
 	    ("Subgoal 8"
 	     :use (:instance intervalp-fi-domain)
 	     )
 	    ("Subgoal 7"
 	     :use (:instance sub-func-differentiable)
 	     )
 	    ("Subgoal 6"
 	     :use (:instance intervalp-c-domain)
 	     )
 	    ("Subgoal 5"
 	     :use (:instance sub-func-prime-continuous)
 	     )
 	    ("Subgoal 4"
 	     :use (:instance sub-func-prime-is-derivative)
 	     )
 	    ("Subgoal 3"
 	     :use (:instance circle-continuous)
 	     )
 	    ("Subgoal 2"
 	     :use (:instance consta1-def)
 	     )
 	    ("Subgoal 1"
 	     :use (:instance consta1-def)
 	     )
 	    )))

 (local (in-theory nil))
 (local (in-theory (enable limited-riemann-circle-sub-prime-small-partition nsa-theory)))

 (defun-std strict-int-circle-sub-prime (a b)
   (if (and (realp a)
	    (realp b)
	    (inside-interval-p a (fi-domain))
	    (inside-interval-p b (fi-domain))
	    (< a b))
       (standard-part (riemann-circle-sub-prime (make-small-partition a b)))
     0))

 (defthm strict-int-circle-sub-prime-lemma
   (IMPLIES
    (AND (STANDARDP A) (STANDARDP B))
    (EQUAL
     (STRICT-INT-CIRCLE-SUB-PRIME A B)
     (IF (AND (REALP A)
 	      (REALP B)
	      (inside-interval-p a (fi-domain))
	      (inside-interval-p b (fi-domain))
 	      (< A B))
 	 (STANDARD-PART (RIEMANN-CIRCLE-SUB-PRIME (MAKE-SMALL-PARTITION A B)))
 	 0)))
   )
 )

(defun int-circle-sub-prime (a b)
  (if (<= a b)
      (strict-int-circle-sub-prime a b)
    (- (strict-int-circle-sub-prime b a))))

(defun map-circle (p)
  (if (consp p)
      (cons (circle (car p))
	    (map-circle (cdr p)))
    nil))

(defun riemann-circle (p)
  (dotprod (deltas p)
	   (map-circle (cdr p))))


(encapsulate
 nil

 (local
  (defthmd limited-riemann-circle-small-partition
    (implies (and (realp a) (standardp a)
		  (realp b) (standardp b)
		  (inside-interval-p a (circle-x-domain))
		  (inside-interval-p b (circle-x-domain))
		  (< a b))
	     (standardp (standard-part (riemann-circle (make-small-partition a b)))))
    :hints (("Goal"
	     :use (:functional-instance limited-riemann-F-prime-small-partition
					(fi-range circle-x-domain)
					(F-prime circle)
					(map-F-prime map-circle)
					(riemann-F-prime riemann-circle)
					(f-o-fi-domain fi-domain)
					(fi sub-func)
					(fi-prime sub-func-prime)
					(consta consta1))
	     )
	    ("Subgoal 2"
 	     :use (:instance riemann-circle)
 	     )
	    ("Subgoal 1"
 	     :use (:instance  map-circle)
 	     )

	    )
    )
  )

 (local (in-theory nil))
 (local (in-theory (enable limited-riemann-circle-small-partition nsa-theory)))

 (defun-std strict-int-circle (a b)
   (if (and (realp a)
	    (realp b)
	    (inside-interval-p a (circle-x-domain))
	    (inside-interval-p b (circle-x-domain))
	    (< a b))
       (standard-part (riemann-circle (make-small-partition a b)))
     0))

 (defthm strict-int-circle-lemma
   (IMPLIES
    (AND (STANDARDP A) (STANDARDP B))
    (EQUAL (STRICT-INT-CIRCLE A B)
	   (IF (AND (REALP A)
		    (REALP B)
		    (INSIDE-INTERVAL-P A (circle-x-domain))
		    (INSIDE-INTERVAL-P B (circle-x-domain))
		    (< A B))
	       (STANDARD-PART (RIEMANN-CIRCLE (MAKE-SMALL-PARTITION A B)))
	       0)))
   )
 )

(defun int-circle (a b)
  (if (<= a b)
      (strict-int-circle a b)
    (- (strict-int-circle b a))))

(defthm usubstitution-circle
  (implies (and (inside-interval-p a (fi-domain))
		(inside-interval-p b (fi-domain)))
	   (equal (int-circle (sub-func a) (sub-func b))
		  (int-circle-sub-prime a b)))
  :hints (("Goal"
	   :use (:functional-instance usubstitution-f-o-fi
				      (int-f-prime int-circle)
				      (int-f-o-fi-prime int-circle-sub-prime)
				      (f-o-fi-domain fi-domain)
				      (fi sub-func)
				      (fi-prime sub-func-prime)
				      (f-prime circle)
				      (consta consta1)
				      (fi-range circle-x-domain)
				      (STRICT-INT-F-O-FI-PRIME strict-int-circle-sub-prime)
				      (strict-int-f-prime strict-int-circle)
				      (RIEMANN-F-O-FI-PRIME riemann-circle-sub-prime)
				      (MAP-F-O-FI-PRIME map-circle-sub-prime)
				      (map-F-prime map-circle)
				      (riemann-F-prime riemann-circle)
				      (F-o-fi-prime circle-sub-prime)
				      (DERIVATIVE-CR-F-O-FI circle-sub-derivative)
				      )
					;:in-theory nil
	   )
	  ("Subgoal 4"
	   :use (:instance int-circle-sub-prime (a a) (b b))
	   )
	  ("Subgoal 3"
	   :use (:instance strict-int-circle-sub-prime-lemma)
	   )
	  ("Subgoal 2"
	   :use (:instance int-circle (a a) (b b))
	   )
	  ("Subgoal 1"
	   :use (:instance strict-int-circle-lemma)
	   )
	  )
  )

(encapsulate
 nil
 (local (in-theory nil))
 (local (include-book "arithmetic-5/top" :dir :system))
 (local
  (defthm lemma-12
    (implies (acl2-numberp x)
	     (equal (- (* x x) (* (* x y) (* x y))) (* x x (+ 1 (-(* y y)))))
	     )
    ))

 (local
  (defthm lemma-13
    (implies (and (acl2-numberp x)
		  (acl2-numberp y)
		  )
	     (equal (* x x y y) (* (* x y) (* x y)))
	     )
    ))

 (local
  (defthm lemma-14
    (implies (and (realp x)
		  (>= x 0))
	     (= (abs x) x))
    :hints (("Goal"
	     :use (:instance abs (x x))
	     :in-theory nil
	     ))

    ))

 (defthm circle-sub-prime-equals
   (implies (and (inside-interval-p x (fi-domain))
		 (>= (acl2-cosine x) 0))
	    (equal (circle-sub-prime x) (*  (* (rad) (acl2-cosine x)) (* (rad) (acl2-cosine x)))))
   :hints (("Goal"
	    :use ((:instance circle-sub-prime)
		  (:instance derivative-circle-sub-definition)
		  (:instance SUB-FUNC-PRIME (x x))
		  (:instance sub-func (x x))
		  (:instance fi-domain-real)
		  (:instance rad-def)
		  (:instance sub-func-real)
		  (:instance sub-func-prime-real)
		  (:instance sqrt-*-x-x(x (* (rad) (acl2-cosine x))))
		  (:instance cos**2->1-sin**2)
		  (:instance circle (x (sub-func x)))
		  (:instance lemma-12
			     (x (rad))
			     (y (acl2-sine x)))
		  (:instance lemma-13
			     (x (rad))
			     (y (acl2-cosine x))
			     )
		  (:instance lemma-14
			     (x (* (rad) (acl2-cosine x)))
			     )
		  )
	    :in-theory nil

	    ))
   )
 )
 
 (defun f-sine (x)
  (if (realp x)
      (acl2-sine x)
    0)
  )

(defun f2-x (x)
  (if (realp x)
      (* 2 x)
    0)
  )

(defun f2-range() (interval 0 (acl2-pi)))

(local
 (defthm-std standard-f2-range
   (standardp (f2-range))))

(local
 (defthm-std standard-f2-range-left-endpoint
   (standardp (interval-left-endpoint (f2-range)))))

(local
 (defthm-std standard-f2-range-right-endpoint
   (standardp (interval-right-endpoint (f2-range)))))

(defthmd intervalp-f2-range
  (interval-p (f2-range))
  )

(defthmd f2-range-real
  (implies (inside-interval-p x (f2-range))
	   (realp x)))

(defthmd f2-range-non-trivial
  (or (null (interval-left-endpoint (f2-range)))
      (null (interval-right-endpoint (f2-range)))
      (< (interval-left-endpoint (f2-range))
	 (interval-right-endpoint (f2-range)))))

(defthmd f-sine-real
  (realp (f-sine x)))

(defthmd f2-x--real
  (realp (f2-x x)))
 
(defthmd f2-range-in-domain-of-f-sine
  (implies (inside-interval-p x (fi-domain))
	   (inside-interval-p (f2-x x) (f2-range)))
  :hints (("Goal"
	   :use ((:instance acl2-pi-type-prescription)
		 (:instance pi-between-2-4)
		 (:instance fi-domain-real))
	   :in-theory (enable inside-interval-p)
	   )))

(defthm-std f-sine-std
  (implies (standardp x)
	   (standardp (f-sine x)))
  )

(local (defthm-std acl2-cosine-std
	 (implies (standardp x)
		  (standardp (acl2-cosine x)))
	 ))

(defthmd f-sine-differentiable
  (implies (and (standardp x)
		(inside-interval-p x (f2-range))
		(inside-interval-p y1 (f2-range))
		(inside-interval-p y2 (f2-range))
		(i-close x y1) (not (= x y1))
		(i-close x y2) (not (= x y2))
		)
	   (and (i-limited (/ (- (f-sine x) (f-sine y1)) (- x y1)))
		(i-close (/ (- (f-sine x) (f-sine y1)) (- x y1))
			 (/ (- (f-sine x) (f-sine y2)) (- x y2)))
		))
  :hints (("Goal"
	   :use ((:instance f2-range-real)
		 (:instance f2-range-real(x y1))
		 (:instance f2-range-real(x y2))
		 (:instance acl2-sine-derivative(x x)
			    (y y1))
		 (:instance standards-are-limited-forward (x (acl2-cosine x)))
		 (:instance i-close-limited-2
			    (y (acl2-cosine x))
			    (x (/ (- (f-sine x) (f-sine y1)) (- x y1))))
		 (:instance acl2-sine)
		 (:instance acl2-cosine)
		 (:instance f-sine-std)
		 (:instance f-sine)
		 (:instance f-sine (x y1))
		 (:instance f-sine (x y2))
		 (:instance acl2-cosine-std)
		 (:instance acl2-sine-derivative(x x)
			    (y y2))
		 (:instance i-close-transitive
			    (x (/ (- (f-sine x) (f-sine y1)) (- x y1)))
			    (y (acl2-cosine x))
			    (z (/ (- (f-sine x) (f-sine y2)) (- x y2)))
			    )
		 (:instance i-close-symmetric
			    (x (/ (- (f-sine x) (f-sine y2)) (- x y2)))
			    (y (acl2-cosine x))
			    )
		 )
	   :in-theory nil
	   ))
  )
  
  
(local
 (defthm lemma-23
   (implies (and (acl2-numberp x)
		 (acl2-numberp y)
		 (not (= x y)))
	    (not (= (- x y) 0))
	    )
   )
 )

(encapsulate
 nil

 (local (in-theory nil))
 (local (include-book "arithmetic-5/top" :dir :system))
 (local (include-book "nonstd/nsa/nsa" :dir :system))

 (local (defthm f2-x-def
	  (implies (realp x)
		   (equal (f2-x x) (* 2 x)))
	  :hints (("Goal"
		   :use (:instance f2-x (x x))
		   ))
	  ))
 (local
  (defthm lemma-21
    (equal (- (* 2 x)  (* 2 y)) (* 2 (- x y)))
    )
  )

 (local
  (defthm f2-x-diff-lemma
    (implies (and (realp x)
		  (realp y1)
		  (not (= (- x y1) 0)))
	     (equal (/ (- (f2-x x) (f2-x y1)) (- x y1)) (/ (* 2 (- x y1)) (- x y1))))
    :hints (("Goal"
	     :use (
		   (:instance F2-X-def(x x))
		   (:instance f2-x (x y1))
		   (:instance lemma-21
			      (x x)
			      (y y1)
			      )
		   )
	     :in-theory nil
	     ))

    ))

 (local
  (defthm lemma-22
    (implies (and (acl2-numberp x)
		  (not (= x 0)))
	     (equal (/ (* 2 x) x) 2)
	     )
    )
  )

 (local
  (defthm f2-x-differentiable-lemma
    (implies (and (standardp x)
		  (inside-interval-p x (fi-domain))
		  (inside-interval-p y1 (fi-domain))
		  (i-close x y1) (not (= x y1))
		  (not (= (- x y1) 0))
		  )
	     (equal (/ (- (f2-x x) (f2-x y1)) (- x y1)) 2)
	     )
    :hints (("Goal"
	     :use (
		   (:instance f2-x-diff-lemma)
		   (:instance fi-domain-real (x y1))
		   (:instance fi-domain-real (x x))
		   (:instance lemma-22 (x (- x y1)))
		   )
	     :in-theory nil
	     )
	    )
    )
  )

 (defthmd f2-x-differentiable
   (implies (and (standardp x)
		 (inside-interval-p x (fi-domain))
		 (inside-interval-p y1 (fi-domain))
		 (inside-interval-p y2 (fi-domain))
		 (i-close x y1) (not (= x y1))
		 (i-close x y2) (not (= x y2)))
	    (and  (i-limited (/ (- (f2-x x) (f2-x y1)) (- x y1)))
		  (i-close (/ (- (f2-x x) (f2-x y1)) (- x y1))
			   (/ (- (f2-x x) (f2-x y2)) (- x y2)))))
   :hints (("Goal"
	    :use (
		  (:instance f2-x-differentiable-lemma
			     (x x)
			     (y1 y1))
		  (:instance f2-x-differentiable-lemma
			     (x x)
			     (y1 y2))
		  (:instance lemma-23
			     (x x)
			     (y y1))
		  (:instance lemma-23
			     (x x)
			     (y y2))
		  (:instance fi-domain-real (x y1))
		  (:instance fi-domain-real (x x))
		  (:instance fi-domain-real (x y2))
		  (:instance standard-numberp-integers-to-100000000
			     (x 2))
		  (:instance standards-are-limited-forward (x 2))
		  (:instance i-close-reflexive (x 2))
		  )
	    ))
   )

 )

(encapsulate

 ( ((differential-f-sine * *) => *) )

 (local (in-theory nil))
 (local
  (defun differential-f-sine (x eps)
    (/ (- (f-sine (+ x eps)) (f-sine x)) eps)))

 (defthm differential-f-sine-definition
   (implies (and (inside-interval-p x (f2-range))
                 (inside-interval-p (+ x eps) (f2-range)))
            (equal (differential-f-sine x eps)
                   (/ (- (f-sine (+ x eps)) (f-sine x)) eps))))

 )

(defthmd realp-differential-f-sine
  (implies (and (inside-interval-p x (f2-range))
		(inside-interval-p (+ x eps) (f2-range))
		(realp eps))
	   (realp (differential-f-sine x eps)))
  :hints (("Goal"
	   :use (:functional-instance realp-differential-cr-fn1
				      (differential-cr-fn1 differential-f-sine)
				      (cr-fn1 f-sine)
				      (cr-fn2-range f2-range)
				      (cr-fn2-domain fi-domain)
				      (cr-fn2 f2-x))
	   )
	  ("Subgoal 5"
	   :use (:instance f2-range-in-domain-of-f-sine)
	   )
	  ("Subgoal 6"
	   :use (:instance f-sine-differentiable)
	   )
	  ("Subgoal 7"
	   :use (:instance f2-x-differentiable)
	   )
	  )

  )

(defthm differential-f-sine-limited
  (implies (and (standardp x)
		(inside-interval-p x (f2-range))
		(inside-interval-p (+ x eps) (f2-range))
		(i-small eps))
	   (i-limited (differential-f-sine x eps)))
  :hints (("Goal"
	   :use (:functional-instance differential-cr-fn1-limited
				      (differential-cr-fn1 differential-f-sine)
				      (cr-fn1 f-sine)
				      (cr-fn2-range f2-range)
				      (cr-fn2-domain fi-domain)
				      (cr-fn2 f2-x)))))

(in-theory (disable differential-f-sine-definition))

(encapsulate

 ( ((derivative-f-sine *) => *) )

 (local
  (defun-std derivative-f-sine (x)
    (if (inside-interval-p x (f2-range))
        (if (inside-interval-p (+ x (/ (i-large-integer))) (f2-range))
            (standard-part (differential-f-sine x (/ (i-large-integer))))
	  (if (inside-interval-p (- x (/ (i-large-integer))) (f2-range))
	      (standard-part (differential-f-sine x (- (/ (i-large-integer)))))
            'error))
      'error)))

 (defthm derivative-f-sine-definition
   (implies (and (inside-interval-p x (f2-range))
                 (standardp x))
            (equal (derivative-f-sine x)
                   (if (inside-interval-p (+ x (/ (i-large-integer))) (f2-range))
                       (standard-part (differential-f-sine x (/ (i-large-integer))))
                     (if (inside-interval-p (- x (/ (i-large-integer))) (f2-range))
                         (standard-part (differential-f-sine x (- (/ (i-large-integer)))))
                       'error))))

   :hints (("Goal"
	    :use (:functional-instance derivative-cr-fn1-definition
				       (differential-cr-fn1 differential-f-sine)
				       (cr-fn1 f-sine)
				       (cr-fn2-range f2-range)
				       (cr-fn2-domain fi-domain)
				       (derivative-cr-fn1 derivative-f-sine)
				       (cr-fn2 f2-x)))))


 )

(encapsulate

 ( ((differential-cr-f2 * *) => *) )

 (local
  (defun differential-cr-f2 (x eps)
    (/ (- (f2-x (+ x eps)) (f2-x x)) eps)))

 (defthm differential-cr-f2-definition
   (implies (and (inside-interval-p x (fi-domain))
                 (inside-interval-p (+ x eps) (fi-domain)))
            (equal (differential-cr-f2 x eps)
                   (/ (- (f2-x (+ x eps)) (f2-x x)) eps)))))


(defthmd realp-differential-cr-f2
  (implies (and (inside-interval-p x (fi-domain))
		(inside-interval-p (+ x eps) (fi-domain))
		(realp eps))
	   (realp (differential-cr-f2 x eps)))
  :hints (("Goal"
	   :use (:functional-instance realp-differential-cr-fn2
				      (differential-cr-fn2 differential-cr-f2)
				      (cr-fn1 f-sine)
				      (cr-fn2-range f2-range)
				      (cr-fn2-domain fi-domain)
				      (derivative-cr-fn1 derivative-f-sine)
				      (cr-fn2 f2-x))
	   )
	  ))

(defthm differential-cr-f2-limited
  (implies (and (standardp x)
		(inside-interval-p x (fi-domain))
		(inside-interval-p (+ x eps) (fi-domain))
		(i-small eps))
	   (i-limited (differential-cr-f2 x eps)))
  :hints (("Goal"
	   :use (:functional-instance differential-cr-fn2-limited
				      (differential-cr-fn2 differential-cr-f2)
				      (cr-fn1 f-sine)
				      (cr-fn2-range f2-range)
				      (cr-fn2-domain fi-domain)
				      (derivative-cr-fn1 derivative-f-sine)
				      (cr-fn2 f2-x))
	   )
	  ))

(in-theory (disable differential-cr-f2-definition))

(encapsulate
 ( ((derivative-cr-f2 *) => *) )

 (local (in-theory nil))
 
 (local
  (encapsulate
   ()

   (local (in-theory nil))
   (local (include-book "arithmetic-5/top" :dir :system))
   (local (include-book "nonstd/nsa/nsa" :dir :system))

   (local
    (defthm derivative-cr-f2-lemma-1
      (i-small (/ (i-large-integer)))
      :hints (("Goal"
	       :use (:instance i-large-integer-is-large)
	       :in-theory (enable i-large)
	       ))))
   
   (defthm derivative-cr-f2-lemma1
     (IMPLIES
      (AND (STANDARDP X)
	   (INSIDE-INTERVAL-P X (INTERVAL 0 (* 1/2 (ACL2-PI))))
	   (INSIDE-INTERVAL-P (+ (/ (I-LARGE-INTEGER)) X)
			      (INTERVAL 0 (* 1/2 (ACL2-PI)))))
      (STANDARDP (STANDARD-PART (DIFFERENTIAL-CR-F2 X (/ (I-LARGE-INTEGER))))))
     :hints (("Goal"
	      :use ((:instance differential-cr-f2-limited (x x) (eps (/ (i-large-integer))))
		    (:instance standardp-standard-part (x (DIFFERENTIAL-CR-F2 X (/ (I-LARGE-INTEGER))))))
	      :in-theory (e/d (fi-domain interval) (DIFFERENTIAL-CR-F2-LIMITED))
	      )))
   (defthm derivative-cr-f2-lemma2
     (IMPLIES
      (AND (STANDARDP X)
	   (INSIDE-INTERVAL-P X (INTERVAL 0 (* 1/2 (ACL2-PI))))
	   (INSIDE-INTERVAL-P (+ (- (/ (I-LARGE-INTEGER))) X)
			      (INTERVAL 0 (* 1/2 (ACL2-PI)))))
      (STANDARDP (STANDARD-PART (DIFFERENTIAL-CR-F2 X (- (/ (I-LARGE-INTEGER)))))))
     :hints (("Goal"
	      :use ((:instance differential-cr-f2-limited (x x) (eps (- (/ (i-large-integer)))))
		    (:instance i-small-uminus (x (/ (i-large-integer))))
		    (:instance standardp-standard-part (x (DIFFERENTIAL-CR-F2 X  (- (/ (I-LARGE-INTEGER)))))))
	      :in-theory (e/d (fi-domain interval fix) (DIFFERENTIAL-CR-F2-LIMITED))
	      )))
   
   (defthm derivative-cr-f2-lemma3
     (IMPLIES
      (STANDARDP X)
      (STANDARDP
       (IF
	(INSIDE-INTERVAL-P X (FI-DOMAIN))
	(COND ((INSIDE-INTERVAL-P (+ X (/ (I-LARGE-INTEGER)))
				  (FI-DOMAIN))
	       (STANDARD-PART (DIFFERENTIAL-CR-F2 X (/ (I-LARGE-INTEGER)))))
	      ((INSIDE-INTERVAL-P (+ X (- (/ (I-LARGE-INTEGER))))
				  (FI-DOMAIN))
	       (STANDARD-PART (DIFFERENTIAL-CR-F2 X (- (/ (I-LARGE-INTEGER))))))
	      (T 'ERROR))
	'ERROR)))
     :hints (("Subgoal 4"
	      :use ((:instance derivative-cr-f2-lemma1 (x x)))
	      :in-theory (enable fi-domain))
	     ("Subgoal 3"
	      :use (:instance derivative-cr-f2-lemma2)
	      :in-theory (enable fi-domain))
	     ("Subgoal 2"
	      :use ((:instance derivative-cr-f2-lemma1 (x x)))
	      :in-theory (enable fi-domain))
	     ("Subgoal 1"
	      :use (:instance derivative-cr-f2-lemma2)
	      :in-theory (enable fi-domain))))))

 (local
  (defun-std derivative-cr-f2 (x)
    (if (inside-interval-p x (fi-domain))
        (if (inside-interval-p (+ x (/ (i-large-integer))) (fi-domain))
            (standard-part (differential-cr-f2 x (/ (i-large-integer))))
	  (if (inside-interval-p (- x (/ (i-large-integer))) (fi-domain))
	      (standard-part (differential-cr-f2 x (- (/ (i-large-integer)))))
            'error))
      'error)))

 (defthm derivative-cr-f2-definition
   (implies (and (inside-interval-p x (fi-domain))
                 (standardp x))
            (equal (derivative-cr-f2 x)
                   (if (inside-interval-p (+ x (/ (i-large-integer))) (fi-domain))
                       (standard-part (differential-cr-f2 x (/ (i-large-integer))))
                     (if (inside-interval-p (- x (/ (i-large-integer))) (fi-domain))
                         (standard-part (differential-cr-f2 x (- (/ (i-large-integer)))))
                       'error)))))
 )

(encapsulate
 ( ((f-sine-o-f2 *) => *) )

 (local
  (defun f-sine-o-f2 (x)
    (f-sine (f2-x x))))

 (defthm f-sine-o-f2-definition
   (implies (inside-interval-p x (fi-domain))
            (equal (f-sine-o-f2 x)
                   (f-sine (f2-x x)))))
 )

(encapsulate
 ( ((differential-f-sine-o-f2 * *) => *) )

 (local
  (defun differential-f-sine-o-f2 (x eps)
    (if (equal (f2-x (+ x eps)) (f2-x x))
        0
      (* (differential-f-sine (f2-x x) (- (f2-x (+ x eps)) (f2-x x)))
	 (differential-cr-f2 x eps)))))

 (defthm differential-f-sine-o-f2-definition
   (implies (and (inside-interval-p x (fi-domain))
                 (inside-interval-p (+ x eps) (fi-domain)))
            (equal (differential-f-sine-o-f2 x eps)
                   (if (equal (f2-x (+ x eps)) (f2-x x))
                       0
                     (* (differential-f-sine (f2-x x) (- (f2-x (+ x eps)) (f2-x x)))
                        (differential-cr-f2 x eps))))))
 )

(encapsulate
 ( ((derivative-f-sine-o-f2 *) => *) )

 (local
  (defun derivative-f-sine-o-f2 (x)
    (* (derivative-f-sine (f2-x x))
       (derivative-cr-f2 x))))

 (defthm derivative-f-sine-o-f2-definition
   (implies (inside-interval-p x (fi-domain))
            (equal (derivative-f-sine-o-f2 x)
                   (* (derivative-f-sine (f2-x x))
                      (derivative-cr-f2 x)))))
 )


(defthmd differential-f-sine-o-f2-close
  (implies (and (inside-interval-p x (fi-domain))
		(standardp x)
		(realp eps) (i-small eps) (not (= eps 0))
		(inside-interval-p (+ x eps) (fi-domain))
		(syntaxp (not (equal eps (/ (i-large-integer))))))
	   (equal (standard-part (differential-f-sine-o-f2 x eps))
		  (derivative-f-sine-o-f2 x)))
  :hints (("Goal"
	   :use (:functional-instance differential-cr-fn1-o-fn2-close
				      (derivative-cr-fn1-o-fn2 derivative-f-sine-o-f2)
				      (differential-cr-fn1-o-fn2 differential-f-sine-o-f2)
				      (cr-fn1-o-fn2 f-sine-o-f2)
				      (cr-fn2-domain fi-domain)
				      (derivative-cr-fn2 derivative-cr-f2)
				      (differential-cr-fn2 differential-cr-f2)
				      (derivative-cr-fn1 derivative-f-sine)
				      (differential-cr-fn1 differential-f-sine)
				      (cr-fn1 f-sine)
				      (cr-fn2 f2-x)
				      (cr-fn2-range f2-range)
				      )
	   )))

(skip-proofs
 (defthmd differential-f-sine-std-equals
   (implies (and
	     (standardp x)
	     (inside-interval-p x (f2-range))
	     (inside-interval-p (+ x eps) (f2-range))
	     (i-small eps)
	     (not (= eps 0)))
	    (equal (standard-part (differential-f-sine x eps)) (acl2-cosine x))
	    )
   :hints(("Goal"
	   :use ((:instance acl2-sine-derivative
			    (x x)
			    (y (+ x eps)))

		 (:instance f2-range-real)
		 (:instance f2-range-real(x (+ x eps)))
		 (:instance i-close (x x)
			    (y (+ x eps))
			    )
		 (:instance differential-f-sine-definition)
		 )
	   :in-theory (enable nsa-theory)
	   ))
   ))

(defthmd differential-cr-f2-equals
  (implies (and (standardp x)
		(i-small eps)
		(not (= eps 0))
		(inside-interval-p x (fi-domain))
		(inside-interval-p (+ x eps) (fi-domain)))
	   (equal (differential-cr-f2 x eps) 2)
	   )
  :hints (("Goal"
	   :use (:instance differential-cr-f2-definition)
	   ))
  )

(local
 (defthm lemma-101
   (implies (and (realp eps)
		 (i-small eps))
	    (< eps 1))
   :hints (("Goal"
	    :use ((:instance i-small (x eps))
		  (:instance standard-part-<-2
			     (x eps)
			     (y 1)))
	    ))
   )
 )

(local
 (defthm lemma-102
   (implies (and (realp x)
		 (realp eps)
		 (< x eps)
		 (< 0 eps)
		 (<= 0 x))
	    (< (abs x) (abs eps)))
   )
 )

(local
 (defthm lemma-103
   (implies (and (realp x)
		 (realp eps)
		 (< (- x eps) 0))
	    (< x eps))
   )
 )

(local
 (defthm lemma-104
   (implies (and (standardp x)
		 (realp x)
		 (realp eps)
		 (i-small eps)
		 (< 0 eps)
		 (<= 0 x)
		 (< (- x eps) 0))
	    (i-small (+ eps x)))
   :hints (("Goal"
	    :use ((:instance lemma-103)
		  (:instance lemma-102)
		  (:instance small-if-<-small
			     (x eps)
			     (y x))
		  (:instance i-small-plus
			     (x eps)
			     (y x))
		  )))
   )
 )

(local
 (defthm lemma-105
   (implies (and (standardp x)
		 (realp x)
		 (realp eps)
		 (i-small eps)
		 (< 0 eps)
		 (<= 0 x)
		 (< (- x eps) 0))
	    (< (+ eps x) 1))
   :hints (("Goal"
	    :use ((:instance lemma-104)
		  (:instance lemma-101 (eps (+ eps x)))
		  (:instance pi-between-2-4)
		  (:instance acl2-pi-type-prescription)
		  )))
   )
 )

(local
 (defthm lemma-106
   (implies (and (<= x y)
		 (< z x)
		 (< p z))
	    (< p y))
   )
 )


(local
 (defthm lemma-107
   (implies (and (standardp x)
		 (realp x)
		 (realp eps)
		 (i-small eps)
		 (< 0 eps)
		 (<= 0 x)
		 (< (- x eps) 0))
	    (< (+ eps x) (acl2-pi)))
   :hints (("Goal"
	    :use ((:instance lemma-105)
		  (:instance pi-between-2-4)
		  (:instance lemma-106
			     (x 2)
			     (y (acl2-pi))
			     (z 1)
			     (p (+ eps x)))
		  (:instance acl2-pi-type-prescription)
		  )))
   )
 )

(local
 (defthm lemma-108
   (equal (car (f2-range)) 0)
   :hints (("Goal"
	    :in-theory (enable interval-definition-theory)
	    ))
   )
 )

(local
 (defthm lemma-109
   (equal (cdr (f2-range)) (acl2-pi))
   :hints (("Goal"
	    :in-theory (enable interval-definition-theory)
	    ))
   )
 )

(encapsulate
 nil
 (local (in-theory nil))
 (local (include-book "areaofacircle-0"))
 (defthmd x-in-interval-implies-x+-eps-in-interval-f2-range
   (implies (and (inside-interval-p x (f2-range))
		 (standardp x)
		 (realp eps)
		 (i-small eps)
		 (< 0 eps))
	    (or (inside-interval-p (+ x eps) (f2-range))
		(inside-interval-p (- x eps) (f2-range))))
   :hints (("Goal"
	    :use ((:instance lemma-101)
		  (:instance pi-between-2-4)
		  (:instance lemma-107)
		  (:instance f2-range)
		  (:instance lemma-108)
		  (:instance lemma-109)
		  )
	    :in-theory (enable interval-definition-theory)
	    )))
 )

(defthmd derivative-f-sine-equals
  (implies (and (inside-interval-p x (f2-range))
		(standardp x)
		)
	   (equal (derivative-f-sine x) (acl2-cosine x))
	   )
  :hints (("Goal"
	   :use (
		 (:instance derivative-f-sine-definition)
		 (:instance x-in-interval-implies-x+-eps-in-interval-f2-range
			    (x x)
			    (eps (/ (i-large-integer))))
		 (:instance differential-f-sine-std-equals
			    (x x)
			    (eps (/ (i-large-integer))))
		 (:instance differential-f-sine-std-equals
			    (x x)
			    (eps (- (/ (i-large-integer)))))
		 )
	   ))
  )

(local
 (defthm lemma-110
   (implies (<= x y)
	    (<= (* 1/2 x) (* 1/2 y)))
   )
 )

(local
 (defthm lemma-111
   (implies (and (<= x y)
		 (< z x))
	    (< z y))
   )
 )

(local
 (defthm lemma-112
   (implies (and (standardp x)
		 (realp x)
		 (realp eps)
		 (i-small eps)
		 (< 0 eps)
		 (<= 0 x)
		 (< (- x eps) 0))
	    (< (+ eps x) (* 1/2 (ACL2-PI))))
   :hints (("Goal"
	    :use ((:instance lemma-105)
		  (:instance pi-between-2-4)
		  (:instance lemma-110
			     (x 2)
			     (y (acl2-pi)))
		  (:instance lemma-111
			     (x 1)
			     (y (* 1/2 (ACL2-PI)))
			     (z (+ eps x)))
		  (:instance acl2-pi-type-prescription)
		  )))
   )
 )

(local
 (defthm lemma-113
   (equal (car (fi-domain)) 0)
   :hints (("Goal"
	    :in-theory (enable interval-definition-theory)
	    ))
   )
 )

(local
 (defthm lemma-114
   (equal (cdr (fi-domain)) (* 1/2 (acl2-pi)))
   :hints (("Goal"
	    :in-theory (enable interval-definition-theory)
	    ))
   )
 )

(encapsulate
 nil
 (local (in-theory nil))
 (local (include-book "areaofacircle-0"))
 (defthmd x-in-interval-implies-x+-eps-in-interval-fi-dom
   (implies (and (inside-interval-p x (fi-domain))
		 (standardp x)
		 (realp eps)
		 (i-small eps)
		 (< 0 eps))
	    (or (inside-interval-p (+ x eps) (fi-domain))
		(inside-interval-p (- x eps) (fi-domain))))
   :hints (("Goal"
	    :use ((:instance lemma-112)
		  (:instance lemma-113)
		  (:instance lemma-114))
	    :in-theory (enable interval-definition-theory)
	    ))
   )
 )

(defthmd derivative-cr-f2-equals
  (implies (and (inside-interval-p x (fi-domain))
		(standardp x)
		)
	   (equal (derivative-cr-f2 x) 2)
	   )
  :hints (("Goal"
	   :use (
		 (:instance derivative-cr-f2-definition)
		 (:instance x-in-interval-implies-x+-eps-in-interval-fi-dom
			    (x x)
			    (eps (/ (i-large-integer))))
		 (:instance differential-cr-f2-equals
			    (x x)
			    (eps (/ (i-large-integer))))
		 (:instance differential-cr-f2-equals
			    (x x)
			    (eps (- (/ (i-large-integer)))))
		 )
	   ))
  )

(skip-proofs
 (defthmd differential-f-sine-o-f2-close-1
   (implies (and (inside-interval-p x (fi-domain))
		 (standardp x)
		 (realp eps) (i-small eps) (not (= eps 0))
		 (inside-interval-p (+ x eps) (fi-domain)))
	    (equal (standard-part (differential-f-sine-o-f2 x eps))
		   (* 2 (acl2-cosine (* 2 x)))))
   :hints (("Goal"
	    :use (
		  (:instance differential-f-sine-o-f2-close)
		  (:instance derivative-cr-f2-equals)
		  (:instance derivative-f-sine-equals(x (f2-x x)))
		  (:instance derivative-f-sine-o-f2-definition)
		  (:instance f2-range-in-domain-of-f-sine)
		  )
	    ))
   ))

(skip-proofs
 (local
  (defthm lemma-24
    (implies (and (acl2-numberp x)
		  (acl2-numberp y)
		  (= (standard-part x) y))
	     (i-close x y)
	     )
    :hints (("Goal"
	     :in-theory (enable nsa-theory)
	     ))
    )
  ))

(defthmd differential-f-sine-o-f2-derivative
  (implies (and (inside-interval-p x (fi-domain))
		(standardp x)
		(realp eps) (i-small eps) (not (= eps 0))
		(inside-interval-p (+ x eps) (fi-domain)))
	   (i-close  (/ (- (acl2-sine (* 2 (+ x eps))) (acl2-sine (* 2 x))) eps) (* 2 (acl2-cosine (* 2 x)))))
  :hints (
	  ("Goal"
	   :use ((:instance differential-f-sine-o-f2-close-1)
		 )

	   :in-theory (disable differential-f-sine-o-f2-definition fi-domain f-sine-o-f2-definition COSINE-2X)
	   )
	  ("Goal'"
	   :use (:functional-instance realp-differential-cr-fn1-o-fn2
				      (derivative-cr-fn1-o-fn2 derivative-f-sine-o-f2)
				      (differential-cr-fn1-o-fn2 differential-f-sine-o-f2)
				      (cr-fn1-o-fn2 f-sine-o-f2)
				      (cr-fn2-domain fi-domain)
				      (derivative-cr-fn2 derivative-cr-f2)
				      (differential-cr-fn2 differential-cr-f2)
				      (derivative-cr-fn1 derivative-f-sine)
				      (differential-cr-fn1 differential-f-sine)
				      (cr-fn1 f-sine)
				      (cr-fn2 f2-x)
				      (cr-fn2-range f2-range))
	   :in-theory (disable differential-f-sine-o-f2-definition fi-domain f-sine-o-f2-definition COSINE-2X)
	   )
	  ("Goal''"
	   :use (
		 (:instance lemma-24
		 	    (x (differential-f-sine-o-f2 x eps))
		 	    (y (* 2 (acl2-cosine (* 2 x)))))
		 )
	   :in-theory (disable differential-f-sine-o-f2-definition fi-domain f-sine-o-f2-definition COSINE-2X)
	   )
	  ("Goal'''"
	   :use (:functional-instance expand-differential-cr-fn1-o-fn2
				      (derivative-cr-fn1-o-fn2 derivative-f-sine-o-f2)
				      (differential-cr-fn1-o-fn2 differential-f-sine-o-f2)
				      (cr-fn1-o-fn2 f-sine-o-f2)
				      (cr-fn2-domain fi-domain)
				      (derivative-cr-fn2 derivative-cr-f2)
				      (differential-cr-fn2 differential-cr-f2)
				      (derivative-cr-fn1 derivative-f-sine)
				      (differential-cr-fn1 differential-f-sine)
				      (cr-fn1 f-sine)
				      (cr-fn2 f2-x)
				      (cr-fn2-range f2-range))
	   :in-theory nil
	   )
	  ("Subgoal 1"
	   :use (:instance f-sine-o-f2-definition)
	   )
	  ("Goal'4'"
	   :use ((:instance f-sine-o-f2-definition(x x) )
		 (:instance f-sine-o-f2-definition(x (+ x eps)))
		 (:instance f-sine (x (f2-x (+ x eps))))
		 (:instance f2-x (x (+ x eps)))
		 (:instance f-sine (x (f2-x x)))
		 (:instance f2-x (x x))
		 (:instance f2-range-in-domain-of-f-sine (x x))
		 (:instance f2-range-in-domain-of-f-sine (x (+ x eps)))
		 (:instance f2-range-real)
		 (:instance fi-domain-real)
		 )
	   )
	  ("Subgoal 2"
	   :use ((:instance f-sine-o-f2-definition(x x) )
		 (:instance f-sine-o-f2-definition(x (+ x eps)))
		 (:instance f-sine (x (f2-x (+ x eps))))
		 (:instance f2-x (x (+ x eps)))
		 (:instance f-sine (x (f2-x x)))
		 (:instance f2-x (x x))
		 (:instance f2-range-in-domain-of-f-sine (x x))
		 (:instance f2-range-in-domain-of-f-sine (x (+ x eps)))
		 (:instance f2-range-real)
		 (:instance fi-domain-real)
		 ))

	  )
  )

(encapsulate
 nil
 (local (include-book "arithmetic/equalities" :dir :system))

 (local
  (defthm lemma-1-1
    (implies (and (acl2-numberp a)
		  (acl2-numberp b))
	     (equal (* -1 (- a b))
		    (- b a)
		    ))

    )
  )

 (local
  (defthm lemma-1-2
    (implies (and (acl2-numberp a)
		  (acl2-numberp b)
		  (acl2-numberp c)
		  (acl2-numberp d))
	     (equal (/ (* -1 (- a b)) (* -1 (- c d)))
		    (/ (- b a) (- d c)))
	     )
    :hints (("Goal"
	     :use ((:instance lemma-1-1)
		   (:instance lemma-1-1 (a c) (b d)))
	     :in-theory nil
	     ))
    )
  )

 (local
  (defthm lemma-1-3
    (implies (and (acl2-numberp a)
		  (acl2-numberp b)
		  (acl2-numberp c)
		  (acl2-numberp d))
	     (equal (* (/ a b) (/ c d))
		    (/ (* a c) (* b d))))
    )
  )

 (local
  (defthm lemma-118
    (implies (and
	      (acl2-numberp a)
	      (acl2-numberp b)
	      (acl2-numberp c)
	      (acl2-numberp d))
	     (equal (/ (- a b) (- c d))
		    (/ (- b a) (- d c))
		    )
	     )
    :hints (("Goal"
	     :use ((:instance lemma-1-3
			      (a -1) (b -1) (c (- a b)) (d (- c d)))
		   (:instance lemma-1-2))

	     ))
    )
  )

 (skip-proofs
  (defthmd differential-f-sine-o-f2-derivative-1
    (implies (and (inside-interval-p x (fi-domain))
		  (standardp x)
		  (i-close x x1)
		  (not (= x x1))
		  (inside-interval-p x1 (fi-domain)))
	     (i-close  (/ (- (acl2-sine (* 2 x)) (acl2-sine (* 2 x1))) (- x x1)) (* 2 (acl2-cosine (* 2 x)))))
    :hints (("Goal"
	     :use (:instance differential-f-sine-o-f2-derivative
			     (x x)
			     (eps (- x1 x))
			     )
	     )
	    ("Subgoal 2"
	     :in-theory (enable nsa-theory)
	     )
	    ("Subgoal 1"
	     :use (:instance lemma-118
			     (a (acl2-sine (* 2 x1))) (b (acl2-sine (* 2 x)))
			     (c x1) (d x))
	     )
	    )
    ))
 )



(local
 (defthm lemma-25
   (implies (and (acl2-numberp x)
		 (acl2-numberp y)
		 (not (= y 0))
		 (= x y))
	    (i-close (/ (* 2 x) y) 2)
	    )

   )
 )

(local
 (defthm lemma-26
   (implies (and (acl2-numberp x)
		 (acl2-numberp y))
	    (= (* 2 (- x y)) (- (* 2 x) (* 2 y) ))
	    )
   )
 )

(local
 (defthm lemma-27
   (implies (and (acl2-numberp x)
		 (acl2-numberp y)
		 (not (= x y)))
	    (not (= (- x y) 0))
	    )

   )
 )

(defthmd differential-f2-x
  (implies (and (inside-interval-p x (fi-domain))
		(standardp x)
		(i-close x x1)
		(not (= x x1))
		(inside-interval-p x1 (fi-domain)))
	   (i-close (/ (- (* 2 x) (* 2 x1)) (- x x1)) 2))
  :hints (("Goal"
	   :use ((:instance i-close-reflexive (x 2))
		 (:instance fi-domain-real (x x))
		 (:instance fi-domain-real (x x1))
		 (:instance lemma-25 (x (- x x1))
			    (y (- x x1))
			    )
		 (:instance lemma-26 (x x)
			    (y x1)
			    )
		 (:instance lemma-27 (x x)
			    (y x1)
			    )
		 )
	   :in-theory nil
	   ))
  )

(skip-proofs
 (local
  (defthm lemma-119
    (implies (inside-interval-p x (fi-domain))
	     (>= (acl2-cosine x) 0))
    :hints (("Goal"
	     :use ((:instance acl2-pi-type-prescription)
		   (:instance cosine-positive-in-0-pi/2)
		   (:instance cosine-pi/2)
		   (:instance acl2-cos-0-=-1))
	     :in-theory (enable inside-interval-p)
	     )))))

(local
 (defthm lemma-120
   (implies (inside-interval-p x (fi-domain))
	    (equal (circle-sub-prime x) (*  (* (rad) (acl2-cosine x)) (* (rad) (acl2-cosine x)))))
   :hints (("Goal"
	    :use ((:instance circle-sub-prime-equals)
		  (:instance cosine-positive-in-0-pi/2)
		  (:instance cosine-pi/2)
		  (:instance acl2-cos-0-=-1)
		  (:instance lemma-119))
	    :in-theory (enable interval-definition-theory)
	    ))))

(defun rcdfn-f (x)
  (if (realp x)
      (* (rad) (rad) (/ 4) (* (+ (acl2-sine (* 2 x)) (* 2 x))))
    0)
  )

(defthmd rcdfn-f-real
  (realp (rcdfn-f x))
  )

(defthm-std rcdfn-f-std
  (implies (standardp x)
	   (standardp (rcdfn-f x)))
  )

(skip-proofs
 (local
  (defthm lemma-28
    (implies (and (acl2-numberp x)
		  (acl2-numberp y)
		  (i-small (- x y)))
	     (i-close x y))
    :hints (("Goal"
	     :in-theory (enable nsa-theory)
	     ))
    )
  ))

(local
 (defthm lemma-29
   (implies (and (acl2-numberp x)
		 (acl2-numberp y)
		 (acl2-numberp z)
		 (i-limited z)
		 (i-close x y))
	    (i-close (* x z) (* y z)))
   :hints (("Goal"
	    :use (
		  (:instance i-close (x x) (y y))
		  (:instance small*limited->small (x (- x y)) (y z))
		  (:instance lemma-28 (x (* x z)) (y (* y z)))
		  )
	    ))
   )
 )

(local
 (defthm lemma-30
   (implies (and (acl2-numberp a)
		 (acl2-numberp b)
		 (acl2-numberp c)
		 (acl2-numberp d))
	    (equal (+ (- a b) (- c d))
		   (- (+ a c) (+ b d)))
	    )
   )
 )

(local
 (defthm lemma-31
   (implies (and (acl2-numberp a)
		 (acl2-numberp b)
		 (acl2-numberp c))
	    (equal (+ (/ a c) (/ b c))
		   (/ (+ a b) c))
	    )
   )
 )

(skip-proofs
 (defthmd circle-sub-prime-is-derivative
   (implies (and (standardp x)
		 (inside-interval-p x (fi-domain))
		 (inside-interval-p x1 (fi-domain))
		 (i-close x x1) (not (= x x1)))
	    (i-close (/ (- (rcdfn-f x) (rcdfn-f x1)) (- x x1))
		     (circle-sub-prime x)))
   :hints (("Goal"
	    :use ((:instance differential-f-sine-o-f2-derivative-1)
		  (:instance lemma-120)
		  (:instance differential-f2-x)
		  (:instance i-close
			     (x  (/ (- (acl2-sine (* 2 x)) (acl2-sine (* 2 x1))) (- x x1)))
			     (y (* 2 (acl2-cosine (* 2 x))))
			     )
		  (:instance i-close
			     (x (/ (- (* 2 x) (* 2 x1)) (- x x1)))
			     (y 2)
			     )
		  (:instance i-small-plus
			     (x (- (/ (- (acl2-sine (* 2 x)) (acl2-sine (* 2 x1))) (- x x1)) (* 2 (acl2-cosine (* 2 x)))))
			     (y (- (/ (- (* 2 x) (* 2 x1)) (- x x1)) 2))
			     )
		  (:instance lemma-30
			     (a (/ (- (acl2-sine (* 2 x)) (acl2-sine (* 2 x1))) (- x x1)))
			     (b (* 2 (acl2-cosine (* 2 x))))
			     (c (/ (- (* 2 x) (* 2 x1)) (- x x1)))
			     (d 2)
			     )
		  (:instance lemma-28
			     (x (+ (/ (- (acl2-sine (* 2 x)) (acl2-sine (* 2 x1))) (- x x1)) (/ (- (* 2 x) (* 2 x1)) (- x x1))))
			     (y (+ (* 2 (acl2-cosine (* 2 x))) 2))
			     )
		  (:instance lemma-31
			     (a (- (acl2-sine (* 2 x)) (acl2-sine (* 2 x1))))
			     (b (/ (- (* 2 x) (* 2 x1))))
			     (c (- x x1))
			     )
		  (:instance standards-are-limited-forward (x (rad)))
		  (:instance rad-def)
		  (:instance i-limited-times (x (rad)) (y (rad)))
		  (:instance i-limited-times (x (* (rad) (rad))) (y (/ 4)))
		  (:instance lemma-29
			     (x (+ (/ (- (acl2-sine (* 2 x)) (acl2-sine (* 2 x1))) (- x x1)) (/ (- (* 2 x) (* 2 x1)) (- x x1))))
			     (y (+ (* 2 (acl2-cosine (* 2 x))) 2))
			     (z (* (rad) (rad) (/ 4)))
			     )
		  (:instance cosine-2x)
		  (:instance cos**2->1-sin**2)
		  (:instance rcdfn-f (x x))
		  (:instance rcdfn-f (x x1))
		  )
	    ))
   ))

(skip-proofs
 (defthmd circle-sub-prime-continuous
   (implies (and (standardp x)
		 (inside-interval-p x (fi-domain))
		 (i-close x x1)
		 (inside-interval-p x1 (fi-domain)))
	    (i-close (circle-sub-prime x)
		     (circle-sub-prime x1)))
   :hints (("Goal"
	    :use ((:instance cosine-continuous
			     (x x)
			     (y y))
		  (:instance lemma-120)
		  (:instance rad-def)
		  (:instance standards-are-limited-forward(x (rad)))
		  (:instance lemma-29
			     (x (acl2-cosine x))
			     (y (acl2-cosine x1))
			     (z (rad)))
		  (:instance square-is-continuous
			     (x1 (* (rad) (acl2-cosine x)))
			     (x2 (* (rad) (acl2-cosine x1))))
		  )
	    ))
   ))

(skip-proofs
 (defthmd circle-area-ftc-2
   (implies (and (inside-interval-p a (fi-domain))
		 (inside-interval-p b (fi-domain)))
	    (equal (int-circle-sub-prime a b)
		   (- (rcdfn-f b)
		      (rcdfn-f a))))
   :hints (("Goal"
	    :use (:functional-instance ftc-2
				       (rcdfn rcdfn-f)
				       (rcdfn-prime circle-sub-prime)
				       (map-rcdfn-prime map-circle-sub-prime)
				       (riemann-rcdfn-prime riemann-circle-sub-prime)
				       (rcdfn-domain fi-domain)
				       (int-rcdfn-prime int-circle-sub-prime)
				       (strict-int-rcdfn-prime strict-int-circle-sub-prime)
				       )
	    )
	   ("Goal"
	    :use (
		  (:instance circle-sub-prime-continuous)
		  (:instance circle-sub-prime-is-derivative)
		  (:instance intervalp-fi-domain)
		  (:instance fi-domain-non-trivial)
		  (:instance fi-domain-standard)
		  (:instance fi-domain)
		  )
	    )
	   ("Subgoal 9"
	    :use (:instance circle-sub-prime-continuous)
	    )
	   ("Subgoal 8"
	    :use (:instance circle-sub-prime-is-derivative)
	    )
	   )
   ))

(defthmd lemma-0-inside
  (inside-interval-p 0 (fi-domain))
  :hints (("Goal"
	   :use ((:instance fi-domain))
	   :in-theory (enable inside-interval-p)
	   ))
  )

(defthmd lemma-1/2-pi-inside
  (inside-interval-p (* 1/2 (acl2-pi)) (fi-domain))
  :hints (("Goal"
	   :use ((:instance fi-domain)
		 (:instance pi-between-2-4)
		 (:instance acl2-pi-type-prescription)
		 )
	   :in-theory (enable inside-interval-p)
	   ))
  )

(skip-proofs
 (defthm circle-area
   (equal (* 4 (int-circle-sub-prime 0 (* 1/2 (acl2-pi)))) (* (rad) (rad) (acl2-pi)))
   :hints (("Goal"
	    :use ((:instance circle-area-ftc-2 (a 0)
			     (b (* 1/2 (acl2-pi))))
		  (:instance lemma-0-inside)
		  (:instance lemma-1/2-pi-inside)
		  (:instance acl2-pi-type-prescription)
		  (:instance rcdfn-f (x 0))
		  (:instance rcdfn-f (x (* 1/2 (acl2-pi))))
		  )
	    ))
   ))
