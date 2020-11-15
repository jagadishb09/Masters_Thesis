
(include-book "free-group")
(local (include-book "arithmetic-5/top" :dir :system))


(encapsulate
 ()
 (local (include-book "workshops/1999/embedded/Exercises/Exercise1-2/Exercise1.2" :dir :system))
 (defthmd mod--frgrp
   (implies
    (and (force (integerp x))
	 (force (integerp y))
	 (force (integerp z))
	 (force (not (equal z 0))))
    (equal (mod (- x y) z)
	   (mod (- (mod x z) (mod y z)) z)))
   :hints (("Goal" :use (hack-24 hack-25))))

  (defthmd mod--frgrp-1
   (implies
    (and (force (integerp x))
	 (force (integerp y))
	 (force (integerp z))
	 (force (not (equal z 0))))
    (equal 
     (mod (- (mod x z) (mod y z)) z)
     (mod (- x y) z)))
   :hints (("Goal" :use (mod--frgrp))))

 (defthmd intp-x-y
   (implies (and (integerp x)
		 (integerp y))
	    (integerp (mod y x)))
   )

 (defthmd mod-+-frgrp
   (implies
    (and (integerp x)
	 (integerp y)
	 (integerp z)
	 (not (equal z 0)))
    (equal (mod (+ x y) z)
	   (mod (+ (mod x z) (mod y z)) z)))
   :hints (("Goal"
	    :in-theory nil
	    :use (:instance mod-+-exp))
	   )
   )
 
 )


(defun n-mod3 (w x)
  (cons (mod (car (n-f w x)) 3) (cons (mod (car (cdr (n-f w x))) 3) (cons (mod (car (cdr (cdr (n-f w x) )))  3) nil)))
  )



(defthmd n-mod3-=
  (and  (equal (mod (car (n-f w x)) 3)
	       (car (n-mod3 w x)))
	(equal (mod (cadr (n-f w x)) 3)
	       (cadr (n-mod3 w x)))
	(equal (mod (caddr (n-f w x)) 3)
	       (caddr (n-mod3 w x))))
  :hints (("Goal"
	   :in-theory (disable mod n-f)
	   ))
  )

;;;;N(a^n)

(encapsulate
 ()

 (local
  (defthmd n-mod3-a-r-lemma1-1
    (implies (and (integerp a)
		  (integerp c))
	     (equal (mod (+ a (* 3 c))  3)
		    (mod a 3)
		    )
	     )
    )
  )

 (local
  (defthmd n-mod3-a-r-lemma1-3
    (equal (- b (* 4 c))
	   (- (- b c) (* 3 c)))
    )
  )

 (local
  (defthmd n-mod3-a-r-lemma1-4
    (equal (+  (* 2 b) c)
	   (+ (- c b) (* 3 b)))
    )
  )

 (local
  (defthmd n-mod3-a-r-lemma1-5
    (implies (and (integerp b)
		  (integerp c))
	     (and (equal (- b (* 4 c))
			 (- (- b c) (* 3 c)))
		  (equal (mod (- b (* 4 c)) 3)
			 (mod (- b  c) 3))
		  (equal (mod (+ (* 2 b) c) 3)
			 (mod (- c b) 3))))
    :hints (("Goal"
	     :use ((:instance n-mod3-a-r-lemma1-3 (b b) (c c))
		   (:instance n-mod3-a-r-lemma1-1 (a (- b c)) (c (- c)))
		   (:instance n-mod3-a-r-lemma1-4 (b b) (c c))
		   (:instance n-mod3-a-r-lemma1-1 (a (- c b)) (c b))
		   )
	     ))
    )
  )

 (local
  (defthmd n-mod3-a-r-lemma1-6
    (implies (and (weak-wordp w)
		  (equal x (acl2-sqrt 2)))
	     (and (integerp (car (n-f w x)))
		  (integerp (cadr (n-f w x)))
		  (integerp (caddr (n-f w x)))
		  (equal (car (n-f (CONS (WA) W) x)) (* 3 (CAR (n-f W x))))
		  (equal (cadr (n-f (CONS (WA) W) x))
			 (+ (CADR (n-f W x))
			    (- (* 4 (CADDR (n-f W x))))))
		  (equal (caddr (n-f (CONS (WA) W) x))
			 (+ (* 2 (CADR (n-f W x)))
			    (CADDR (n-f W x)))))
	     
	     )
    :hints (("Goal"
	     :use ((:instance rotation-values (w w) (x x))
		   (:instance n-f-a-r (w w) (x x))
		   (:instance n-f (w w) (x x))
		   (:instance n-f (w (cons (wa) w)) (x x)))
	     :in-theory (disable int-point acl2-sqrt rotation reducedwordp mod)
	     ))
    )
  )

 (defthmd integerp-n-mod3
   (implies (and (weak-wordp w)
		 (equal x (acl2-sqrt 2)))
	    (and (integerp (car (n-mod3 w x)))
		 (integerp (cadr (n-mod3 w x)))
		 (integerp (caddr (n-mod3 w x)))
		 )
	    )
   :hints (("Goal"
	    :use ((:instance n-mod3-=)
		  (:instance n-mod3-a-r-lemma1-6 (w w) (x x))
		  (:instance intp-x-y (x 3) (y (car (n-f w x))))
		  (:instance intp-x-y (x 3) (y (car (cdr (n-f w x)))))
		  (:instance intp-x-y (x 3) (y (car (cdr (cdr (n-f w x))))))
		  )
	    :in-theory nil
	    ))

   )

 (local
  (defthmd n-mod3-a-r-lemma1
    (implies (and (weak-wordp w)
		  (equal x (acl2-sqrt 2)))
	     (equal (n-mod3 (cons (wa) w) x)
		    (cons 0 (cons (mod (- (car (cdr (n-f w x)))  (car (cdr (cdr (n-f w x))))) 3)
				  (cons (mod (- (car (cdr (cdr (n-f w x)))) (car (cdr (n-f w x)))) 3) nil)))

		    )
	     )
    :hints (("Goal"
	     :use (
		   (:instance n-mod3 (w (cons (wa) w)) (x x))
		   (:instance n-mod3-a-r-lemma1-1 (a 0) (c (car (n-f w x))))
		   (:instance n-mod3-a-r-lemma1-5 (b (cadr (n-f w x))) (c (caddr (n-f w x))))
		   (:instance n-mod3-a-r-lemma1-6 (w w) (x x))
		   )
	     :in-theory (disable int-point rotation reducedwordp acl2-sqrt n-f mod)
	     :do-not-induct t
	     )	   
	    )
    )
  )



 (local
  (defthmd n-mod3-a-r-1
    (implies (and (integerp x)
		  (integerp y)
		  (not (equal y 0)))
	     (integerp (mod x y)))
    )
  )
 
 (defthmd n-mod3-a-r
   (implies (and (weak-wordp w)
		 (equal x (acl2-sqrt 2)))
	    (equal (n-mod3 (cons (wa) w) x)
		   (cons 0 (cons (mod (- (car (cdr (n-mod3 w x)))  (car (cdr (cdr (n-mod3 w x))))) 3)
				 (cons (mod (- (car (cdr (cdr (n-mod3 w x)))) (car (cdr (n-mod3 w x)))) 3) nil)))

		   )
	    )
   :hints (("Goal"
	    :use (
		  (:instance n-mod3-a-r-lemma1 (w w) (x x))
		  (:instance n-mod3-a-r-lemma1-6 (w w) (x x))
		  (:instance n-mod3-a-r-1 (x (cadr (n-f w x))) (y 3))
		  (:instance n-mod3-a-r-1 (x (caddr (n-f w x))) (y 3))
		  (:instance mod--frgrp
			     (x (cadr (n-f w x)))
			     (y (caddr (n-f w x)))
			     (z 3))

		  (:instance mod--frgrp
			     (y (cadr (n-f w x)))
			     (x (caddr (n-f w x)))
			     (z 3))
		  (:instance n-mod3-=)
		  
		  )
	    :in-theory nil
	    :do-not-induct t
	    ))
   
   )
 )

(defun a-word (n)
  (cond ((zp n) nil)
	(t (cons #\a (a-word (- n 1)))))
  )


(defthmd weak-wordp-a-word
  (implies (integerp n)
	   (weak-wordp (a-word n))
	   )
  )

(defthmd weak-word-aword-w
  (implies (and (integerp n)
		(weak-wordp w))
	   (weak-wordp (append (a-word n) w)))
  :hints (("Goal"
	   :use ((:instance closure-weak-word (x (a-word n)) (y w))
		 (:instance weak-wordp-a-word (n n)))
	   ))
  )

(defthmd n-mod3-a-n-r-1
  (implies (and (weak-wordp w)
		(integerp n)
		(> n 0))
	   (and (equal 
		 (cons (wa) (append (a-word (- n 1)) w))
		 (append (a-word n) w))
		(equal
		 (append (a-word n) w)
		 (cons (wa) (append (a-word (- n 1)) w)))
		)

	   )
  )


(encapsulate
 ()

 (local
  (defthmd mod3-a-n-r-2-1
    (implies (and (integerp b)
		  (integerp c))
	     (equal (- (* 2 b) (* 2 c))
		    (+ (* 3 (- b c))
		       (- c b)))
	     )
    )
  )

 (local
  (defthmd n-mod3-a-n-r-2-2
    (implies (and (integerp a)
		  (integerp c))
	     (equal (mod (+ (* 3 c) a)  3)
		    (mod a 3)
		    )
	     )
    )
  )

 (local
  (defthmd n-mod3-a-n-r-2
    (implies (and (integerp b)
		  (integerp c))
	     (equal (mod (- (* 2 b) (* 2 c)) 3)
		    (mod (- c b) 3))
	     )
    :hints (("Goal"
	     :use (
		   (:instance mod3-a-n-r-2-1 (b b) (c c))
		   (:instance mod-+-frgrp (x (* 3 (- b c))) (y (- c b)) (z 3))
		   (:instance mod--frgrp (x c) (y b) (z 3))
		   (:instance n-mod3-a-n-r-2-2 (c (- b c)) (a (- c b)))
		   )
	     :in-theory nil
	     ))
    )
  )

 (defthmd n-mod3-1/2.2-1
   (implies (and (integerp n)
		 (> n 0)
		 (> n 1))
	    (and (integerp (- n 1))
		 (< 0 (- n 1))))
   )

 (defthmd n-mod3-a-n-r1/2.2.1-1-1
   (implies (equal x (list a b c))
	    (and (equal (car x) a)
		 (equal (cadr x) b)
		 (equal (caddr x) c)))
   )

 (defthmd n-mod3-a-n-r1/2.2.1-1-2
   (implies (and (integerp x)
		 (integerp y))
	    (integerp (- x y)))
   )

 (defthmd n-mod3-a-n-r1/2.2.1-1-3
   (equal (+ (+ x
		(- y))
	     (- (+ y
		   (- x))))
	  (+ (* 2 x)
	     (- (* 2 y))))
   )

 (defthmd n-mod3-a-n-r1/2.2.1-1
   (IMPLIES (AND (IMPLIES (AND (WEAK-WORDP W)
			       (EQUAL X (ACL2-SQRT 2))
			       (INTEGERP (+ -1 N))
			       (< 0 (+ -1 N)))
			  (EQUAL (N-MOD3 (APPEND (A-WORD (+ -1 N)) W) X)
				 (LIST 0
				       (MOD (+ (CADR (N-MOD3 W X))
					       (- (CADDR (N-MOD3 W X))))
					    3)
				       (MOD (+ (CADDR (N-MOD3 W X))
					       (- (CADR (N-MOD3 W X))))
					    3))))
		 (< 1 N))
		 ;(NOT (ZP N)))
	    (IMPLIES (AND (WEAK-WORDP W)
			  (EQUAL X (ACL2-SQRT 2))
			  (INTEGERP N)
			  (< 0 N))
		     (EQUAL (N-MOD3 (APPEND (A-WORD N) W) X)
				(LIST 0
				      (MOD (+ (CADDR (N-MOD3 W X))
					      (- (CADR (N-MOD3 W X))))
					   3)
				      (MOD (+ (CADR (N-MOD3 W X))
					      (- (CADDR (N-MOD3 W X))))
					   3)))))
   :hints (("Goal"
	    :use ((:instance n-mod3-a-n-r1/2.2.1-1-2 (x (CADR (N-MOD3 W X))) (y (CADDR (N-MOD3 W X))))
		  (:instance n-mod3-a-n-r1/2.2.1-1-2 (y (CADR (N-MOD3 W X))) (x (CADDR (N-MOD3 W X))))
		  (:instance n-mod3-a-n-r1/2.2.1-1-3 (x (CADR (N-MOD3 W X))) (y (CADDR (N-MOD3 W X))))
		  (:instance n-mod3-a-n-r1/2.2.1-1-3 (y (CADR (N-MOD3 W X))) (x (CADDR (N-MOD3 W X))))
		  (:instance n-mod3-a-n-r-1 (w w) (n n))
		  (:instance weak-word-aword-w (n (- n 1)) (w w))
		  (:instance n-mod3-a-r (w (append (a-word (- n 1)) w)) (x x))
		  (:instance integerp-n-mod3 (w w) (x x))
		  (:instance mod--frgrp-1
			     (x (+ (CADR (N-MOD3 W X))
				   (- (CADDR (N-MOD3 W X)))))
			     (y (+ (CADDR (N-MOD3 W X))
				   (- (CADR (N-MOD3 W X)))))
			     (z 3)
			     )
		  (:instance mod--frgrp-1
			     (y (+ (CADR (N-MOD3 W X))
				   (- (CADDR (N-MOD3 W X)))))
			     (x (+ (CADDR (N-MOD3 W X))
				   (- (CADR (N-MOD3 W X)))))
			     (z 3)
			     )
		  (:instance n-mod3-a-n-r-2 (b (CADR (N-MOD3 W X))) (c (CADDR (N-MOD3 W X))))
		  (:instance n-mod3-a-n-r-2 (c (CADR (N-MOD3 W X))) (b (CADDR (N-MOD3 W X))))
		  (:instance n-mod3-1/2.2-1 (n n))
		  (:instance integerp-n-mod3 (w (append (a-word (- n 1)) w)) (x x))
		  (:instance n-mod3-a-n-r1/2.2.1-1-1 (x (N-MOD3 (APPEND (A-WORD (+ -1 N)) W)
								(ACL2-SQRT 2)))
			     (a 0)
			     (b (MOD (+ (CADR (N-MOD3 W (ACL2-SQRT 2)))
					(- (CADDR (N-MOD3 W (ACL2-SQRT 2)))))
				     3))
			     (c (MOD (+ (CADDR (N-MOD3 W (ACL2-SQRT 2)))
					(- (CADR (N-MOD3 W (ACL2-SQRT 2)))))
				     3)))
				
		  )
	    :in-theory nil
	    :do-not-induct t
	    ))
   )

 (defthmd n-mod3-a-n-r1/2.2.1-lemma1
   (IMPLIES (AND (WEAK-WORDP W)
		 (EQUAL (N-MOD3 (APPEND (A-WORD (+ -1 N)) W) X)
			(LIST 0
			      (MOD (+ (CADR (N-MOD3 W X))
				      (- (CADDR (N-MOD3 W X))))
				   3)
			      (MOD (+ (CADDR (N-MOD3 W X))
				      (- (CADR (N-MOD3 W X))))
				   3)))
		 (EQUAL X (ACL2-SQRT 2))
		 (INTEGERP N)
		 (integerp (- n 1))
		 (< 0 (- N 1))
		 (> n 1)
		 (< 0 N))
	    (EQUAL (N-MOD3 (APPEND (A-WORD N) W) X)
		   (LIST 0
			 (MOD (+ (CADDR (N-MOD3 W X))
				 (- (CADR (N-MOD3 W X))))
			      3)
			 (MOD (+ (CADR (N-MOD3 W X))
				 (- (CADDR (N-MOD3 W X))))
			      3))))

   :hints (("Goal"
	    :use (:instance n-mod3-a-n-r1/2.2.1-1)
	    :in-theory nil
	    ))
   )
   

 (defthmd n-mod3-a-n-r1/2.2.1-2
   (IMPLIES (AND (IMPLIES (AND (WEAK-WORDP W)
			       (EQUAL X (ACL2-SQRT 2))
			       (INTEGERP (+ -1 N))
			       (< 0 (+ -1 N)))
			  (EQUAL (N-MOD3 (APPEND (A-WORD (+ -1 N)) W) X)
				 (LIST 0
				        (MOD (+ (CADDR (N-MOD3 W X))
					       (- (CADR (N-MOD3 W X))))
					    3)
				       (MOD (+ (CADR (N-MOD3 W X))
					       (- (CADDR (N-MOD3 W X))))
					    3))))
		 (< 1 N))
		 ;(NOT (ZP N)))
	    (IMPLIES (AND (WEAK-WORDP W)
			  (EQUAL X (ACL2-SQRT 2))
			  (INTEGERP N)
			  (< 0 N))
		     (EQUAL (N-MOD3 (APPEND (A-WORD N) W) X)
			    (LIST 0
				  (MOD (+ (CADR (N-MOD3 W X))
					  (- (CADDR (N-MOD3 W X))))
				       3)
				  (MOD (+ (CADDR (N-MOD3 W X))
					      (- (CADR (N-MOD3 W X))))
					   3)))))
   :hints (("Goal"
	    :use ((:instance n-mod3-a-n-r1/2.2.1-1-2 (x (CADR (N-MOD3 W X))) (y (CADDR (N-MOD3 W X))))
		  (:instance n-mod3-a-n-r1/2.2.1-1-2 (y (CADR (N-MOD3 W X))) (x (CADDR (N-MOD3 W X))))
		  (:instance n-mod3-a-n-r1/2.2.1-1-3 (x (CADR (N-MOD3 W X))) (y (CADDR (N-MOD3 W X))))
		  (:instance n-mod3-a-n-r1/2.2.1-1-3 (y (CADR (N-MOD3 W X))) (x (CADDR (N-MOD3 W X))))
		  (:instance n-mod3-a-n-r-1 (w w) (n n))
		  (:instance weak-word-aword-w (n (- n 1)) (w w))
		  (:instance n-mod3-a-r (w (append (a-word (- n 1)) w)) (x x))
		  (:instance integerp-n-mod3 (w w) (x x))
		  (:instance mod--frgrp-1
			     (x (+ (CADR (N-MOD3 W X))
				   (- (CADDR (N-MOD3 W X)))))
			     (y (+ (CADDR (N-MOD3 W X))
				   (- (CADR (N-MOD3 W X)))))
			     (z 3)
			     )
		  (:instance mod--frgrp-1
			     (y (+ (CADR (N-MOD3 W X))
				   (- (CADDR (N-MOD3 W X)))))
			     (x (+ (CADDR (N-MOD3 W X))
				   (- (CADR (N-MOD3 W X)))))
			     (z 3)
			     )
		  (:instance n-mod3-a-n-r-2 (b (CADR (N-MOD3 W X))) (c (CADDR (N-MOD3 W X))))
		  (:instance n-mod3-a-n-r-2 (c (CADR (N-MOD3 W X))) (b (CADDR (N-MOD3 W X))))
		  (:instance n-mod3-1/2.2-1 (n n))
		  (:instance integerp-n-mod3 (w (append (a-word (- n 1)) w)) (x x))
		  (:instance n-mod3-a-n-r1/2.2.1-1-1 (x (N-MOD3 (APPEND (A-WORD (+ -1 N)) W)
								(ACL2-SQRT 2)))
			     (a 0)
			     (c (MOD (+ (CADR (N-MOD3 W (ACL2-SQRT 2)))
					(- (CADDR (N-MOD3 W (ACL2-SQRT 2)))))
				     3))
			     (b (MOD (+ (CADDR (N-MOD3 W (ACL2-SQRT 2)))
					(- (CADR (N-MOD3 W (ACL2-SQRT 2)))))
				     3)))
				
		  )
	    :in-theory nil
	    :do-not-induct t
	    ))
   )

 (defthmd n-mod3-a-n-r1/2.2.1-lemma2
   (IMPLIES (AND (WEAK-WORDP W)
		 (EQUAL (N-MOD3 (APPEND (A-WORD (+ -1 N)) W) X)
			(LIST 0
			      (MOD (+ (CADDR (N-MOD3 W X))
				      (- (CADR (N-MOD3 W X))))
				   3)
			      (MOD (+ (CADR (N-MOD3 W X))
				      (- (CADDR (N-MOD3 W X))))
				   3)))
		 (EQUAL X (ACL2-SQRT 2))
		 (INTEGERP N)
		 (integerp (- n 1))
		 (< 0 (- N 1))
		 (> n 1)
		 (< 0 N))
	    (EQUAL (N-MOD3 (APPEND (A-WORD N) W) X)
		   (LIST 0
			 (MOD (+ (CADR (N-MOD3 W X))
				 (- (CADDR (N-MOD3 W X))))
			      3)
			 (MOD (+ (CADDR (N-MOD3 W X))
				 (- (CADR (N-MOD3 W X))))
			      3))))

   :hints (("Goal"
	    :use (:instance n-mod3-a-n-r1/2.2.1-2)
	    :in-theory nil
	    ))
   )
 
 )


(defthmd n-mod3-a-n-r
  (implies (and (weak-wordp w)
		(equal x (acl2-sqrt 2))
		(integerp n)
		(> n 0))
	   (or (equal (n-mod3 (append (a-word n) w) x)
		      (cons 0 (cons (mod (- (car (cdr (n-mod3 w x)))  (car (cdr (cdr (n-mod3 w x))))) 3)
				    (cons (mod (- (car (cdr (cdr (n-mod3 w x)))) (car (cdr (n-mod3 w x)))) 3) nil))))
	       (equal (n-mod3 (append (a-word n) w) x)
		      (cons 0 (cons (mod (- (car (cdr (cdr (n-mod3 w x)))) (car (cdr (n-mod3 w x)))) 3)
				    (cons (mod (- (car (cdr (n-mod3 w x))) (car (cdr (cdr (n-mod3 w x))))) 3) nil))))))
  
  :hints (("Goal"
	   :in-theory (disable mod n-mod3 weak-wordp)
	   )

	  ("Subgoal *1/2"
	   :cases ((>  n 1)
		   (<= n 1))
	   )
	  ("Subgoal *1/2.2"
	   :use ((:instance n-mod3-a-n-r1/2.2.1-lemma2)
		 (:instance n-mod3-a-n-r1/2.2.1-lemma1)
		 (:instance n-mod3-1/2.2-1 (n n)))
	   :in-theory nil
	   )
	  
	  ("Subgoal *1/2.1"
	   :use (:instance n-mod3-a-r (w w) (x x))
	   )
	  )
  )


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;N(a-inv^n)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(encapsulate
 ()

 (local
  (defthmd n-mod3-a-r-lemma1-1
    (implies (and (integerp a)
		  (integerp c))
	     (equal (mod (+ a (* 3 c))  3)
		    (mod a 3)
		    )
	     )
    )
  )

 (local
  (defthmd n-mod3-a-r-lemma1-3
    (equal (+ b (* 4 c))
	   (+ (+ b c) (* 3 c)))
    )
  )

 (local
  (defthmd n-mod3-a-r-lemma1-4
    (equal (- c  (* 2 b))
	   (- (+ c b) (* 3 b)))
    )
  )

 (local
  (defthmd n-mod3-a-r-lemma1-5
    (implies (and (integerp b)
		  (integerp c))
	     (and (equal (+ b (* 4 c))
			 (+ (+ b c) (* 3 c)))
		  (equal (mod (+ b (* 4 c)) 3)
			 (mod (+ b  c) 3))
		  (equal (mod (- c (* 2 b)) 3)
			 (mod (+ c b) 3))))
    :hints (("Goal"
	     :use ((:instance n-mod3-a-r-lemma1-3 (b b) (c c))
		   (:instance n-mod3-a-r-lemma1-1 (a (+ b c)) (c c))
		   (:instance n-mod3-a-r-lemma1-4 (b b) (c c))
		   (:instance n-mod3-a-r-lemma1-1 (a (+ c b)) (c (- b)))
		   )
	     ))
    )
  )

 (local
  (defthmd n-mod3-a-r-lemma1-6
    (implies (and (weak-wordp w)
		  (equal x (acl2-sqrt 2)))
	     (and (integerp (car (n-f w x)))
		  (integerp (cadr (n-f w x)))
		  (integerp (caddr (n-f w x)))
		  (equal (car (n-f (CONS (WA-inv) W) x)) (* 3 (CAR (n-f W x))))
		  (equal (cadr (n-f (CONS (WA-inv) W) x))
			 (+ (CADR (n-f W x))
			    (+ (* 4 (CADDR (n-f W x))))))
		  (equal (caddr (n-f (CONS (WA-inv) W) x))
			 (- (CADDR (n-f W x)) (* 2 (CADR (n-f W x))))))
	     
	     )
    :hints (("Goal"
	     :use ((:instance rotation-values (w w) (x x))
		   (:instance n-f-a-inv-r (w w) (x x))
		   (:instance n-f (w w) (x x))
		   (:instance n-f (w (cons (wa-inv) w)) (x x)))
	     :in-theory (disable int-point acl2-sqrt rotation reducedwordp mod)
	     ))
    )
  )

 (local
  (defthmd n-mod3-a-r-lemma1
    (implies (and (weak-wordp w)
		  (equal x (acl2-sqrt 2)))
	     (equal (n-mod3 (cons (wa-inv) w) x)
		    (cons 0 (cons (mod (+ (car (cdr (n-f w x)))  (car (cdr (cdr (n-f w x))))) 3)
				  (cons (mod (+ (car (cdr (cdr (n-f w x)))) (car (cdr (n-f w x)))) 3) nil)))

		    )
	     )
    :hints (("Goal"
	     :use (
		   (:instance n-mod3 (w (cons (wa-inv) w)) (x x))
		   (:instance n-mod3-a-r-lemma1-1 (a 0) (c (car (n-f w x))))
		   (:instance n-mod3-a-r-lemma1-5 (b (cadr (n-f w x))) (c (caddr (n-f w x))))
		   (:instance n-mod3-a-r-lemma1-6 (w w) (x x))
		   )
	     :in-theory (disable int-point rotation reducedwordp acl2-sqrt n-f mod)
	     :do-not-induct t
	     )	   
	    )
    )
  )



 (local
  (defthmd n-mod3-a-r-1
    (implies (and (integerp x)
		  (integerp y)
		  (not (equal y 0)))
	     (integerp (mod x y)))
    )
  )
 
 (defthmd n-mod3-a-inv-r
   (implies (and (weak-wordp w)
		 (equal x (acl2-sqrt 2)))
	    (equal (n-mod3 (cons (wa-inv) w) x)
		   (cons 0 (cons (mod (+ (car (cdr (n-mod3 w x)))  (car (cdr (cdr (n-mod3 w x))))) 3)
				 (cons (mod (+ (car (cdr (cdr (n-mod3 w x)))) (car (cdr (n-mod3 w x)))) 3) nil)))

		   )
	    )
   :hints (("Goal"
	    :use (
		  (:instance n-mod3-a-r-lemma1 (w w) (x x))
		  (:instance n-mod3-a-r-lemma1-6 (w w) (x x))
		  (:instance n-mod3-a-r-1 (x (cadr (n-f w x))) (y 3))
		  (:instance n-mod3-a-r-1 (x (caddr (n-f w x))) (y 3))
		  (:instance mod-+-frgrp
			     (x (cadr (n-f w x)))
			     (y (caddr (n-f w x)))
			     (z 3))

		  (:instance mod-+-frgrp
			     (y (cadr (n-f w x)))
			     (x (caddr (n-f w x)))
			     (z 3))
		  (:instance n-mod3-=)
		  
		  )
	    :in-theory nil
	    :do-not-induct t
	    ))
   
   )
 )

(defun a-inv-word (n)
  (cond ((zp n) nil)
	(t (cons #\b (a-inv-word (- n 1)))))
  )


(defthmd weak-wordp-a-inv-word
  (implies (integerp n)
	   (weak-wordp (a-inv-word n))
	   )
  )

(defthmd weak-word-a-inv-word-w
  (implies (and (integerp n)
		(weak-wordp w))
	   (weak-wordp (append (a-inv-word n) w)))
  :hints (("Goal"
	   :use ((:instance closure-weak-word (x (a-inv-word n)) (y w))
		 (:instance weak-wordp-a-inv-word (n n)))
	   ))
  )

(defthmd n-mod3-a-inv-n-r-1
  (implies (and (weak-wordp w)
		(integerp n)
		(> n 0))
	   (and (equal 
		 (cons (wa-inv) (append (a-inv-word (- n 1)) w))
		 (append (a-inv-word n) w))
		(equal
		 (append (a-inv-word n) w)
		 (cons (wa-inv) (append (a-inv-word (- n 1)) w)))
		)

	   )
  )

(encapsulate
 ()


 (local
  (defthmd n-mod3-a-inv-n-r-2
    (implies (and (integerp b)
		  (integerp c))
	     (equal (+ (* 2 b) (* 2 c))
		    (+ (* 3 (+ b c))
		       (+ (- c) (- b))))
	     )
    )
  )

 (local
  (defthmd n-mod3-a-inv-n-r-3
    (implies (and (integerp a)
		  (integerp c))
	     (equal (mod (+ (* 3 c) a)  3)
		    (mod a 3)
		    )
	     )
    )
  )

 (local
  (defthmd n-mod3-a-inv-n-r-4
    (implies (and (integerp b)
		  (integerp c))
	     (equal (mod (+ (* 2 b) (* 2 c)) 3)
		    (mod (+ (- c) (- b)) 3))
	     )
    :hints (("Goal"
	     :use (
		   (:instance n-mod3-a-inv-n-r-2 (b b) (c c))
		   (:instance mod-+-frgrp (x (* 3 (+ b c))) (y (+ (- c) (- b))) (z 3))
		   ;(:instance mod--frgrp (x c) (y b) (z 3))
		   (:instance n-mod3-a-inv-n-r-3 (c (+ b c)) (a (+ (- c) (- b))))
		   )
	     :in-theory nil
	     ))
    )
  )

 (defthmd n-mod3-a-inv-n-r-5
   (equal (+ (+ x
		y)
	     (+ y
		   x))
	  (+ (* 2 x) (* 2 y))))


 (defthmd n-mod3-a-inv-n-r-6
   (implies (equal x (list a b c))
	    (and (equal (car x) a)
		 (equal (cadr x) b)
		 (equal (caddr x) c)))
   )

 
 
 (defthmd n-mod3-a-inv-n-r-lemma1
   (IMPLIES (AND (WEAK-WORDP W)
		 (EQUAL (N-MOD3 (APPEND (A-inv-WORD (+ -1 N)) W) X)
			(LIST 0
			      (MOD (+ (CADR (N-MOD3 W X))
				      (CADDR (N-MOD3 W X)))
				   3)
			      (MOD (+ (CADDR (N-MOD3 W X))
				      (CADR (N-MOD3 W X)))
				   3)))
		 (EQUAL X (ACL2-SQRT 2))
		 (INTEGERP N)
		 (integerp (- n 1))
		 (< 0 (- N 1))
		 (> n 1)
		 (< 0 N))
	    (EQUAL (N-MOD3 (APPEND (A-inv-WORD N) W) X)
		   (LIST 0
			 (MOD (+ (- (CADDR (N-MOD3 W X)))
				 (- (CADR (N-MOD3 W X))))
			      3)
			 (MOD (+ (- (CADR (N-MOD3 W X)))
				 (- (CADDR (N-MOD3 W X))))
			      3))))

   :hints (("Goal"
	    :use ((:instance n-mod3-a-inv-n-r-1 (w w) (n n))
		  (:instance weak-word-a-inv-word-w (n (- n 1)) (w w))
		  ;(:instance n-mod3-a-inv-r (w (append (a-inv-word (- n 1)) w)) (x x))
		  (:instance integerp-n-mod3 (w w) (x x))
		  (:instance n-mod3-a-inv-r (w (APPEND (A-inv-WORD (+ -1 N)) W)) (x x))
		  (:instance n-mod3-a-inv-n-r-6
			     (x (N-MOD3 (APPEND (A-inv-WORD (+ -1 N)) W) X))
			     (a 0)
			     (b (MOD (+ (CADR (N-MOD3 W X))
					(CADDR (N-MOD3 W X)))
				     3))
			     (c (MOD (+ (CADDR (N-MOD3 W X))
					(CADR (N-MOD3 W X)))
				     3)))
		  (:instance n-mod3-a-inv-n-r-5 (x (CADR (N-MOD3 W X))) (y (CADDR (N-MOD3 W X))))
		  (:instance n-mod3-a-inv-n-r-4 (b (CADR (N-MOD3 W X))) (c (CADDR (N-MOD3 W X))))
		  (:instance mod-+-frgrp
			     (x (MOD (+ (CADR (N-MOD3 W (ACL2-SQRT 2)))
					(CADDR (N-MOD3 W (ACL2-SQRT 2))))
				     3))
			     (y (MOD (+ (CADDR (N-MOD3 W (ACL2-SQRT 2)))
					(CADR (N-MOD3 W (ACL2-SQRT 2))))
				     3))
			     (z 3))
		  (:instance integerp-n-mod3 (w (append (a-inv-word (- n 1)) w)) (x x))
		  (:instance  weak-word-a-inv-word-w (n (- n 1)))
		  )
	    :in-theory (disable mod n-mod3 append weak-wordp a-inv-word acl2-sqrt)
	    ))
   )


 ;; (defthmd n-mod3-a-inv-n-r-lemma2-1
 ;;   (implies (and (integerp x)
 ;; 		 (integerp y))
 ;; 	    (integerp (mod x y)))
 ;;   )

 (defthmd n-mod3-a-inv-n-r-lemma2-1
   (implies (integerp x)
	    (equal (- (- x)) x)))

 (defthmd n-mod3-a-inv-n-r-lemma2-2
   (implies (integerp x)
	    (equal (+ x y) (+ y x))))
 

 
 (defthmd n-mod3-a-inv-n-r-lemma2
   (IMPLIES (AND (WEAK-WORDP W)
		 (EQUAL (N-MOD3 (APPEND (A-inv-WORD (+ -1 N)) W) X)
			(LIST 0
			      (MOD (+ (- (CADR (N-MOD3 W X)))
				      (- (CADDR (N-MOD3 W X))))
				   3)
			      (MOD (+ (- (CADDR (N-MOD3 W X)))
				      (- (CADR (N-MOD3 W X))))
				   3)))
		 (EQUAL X (ACL2-SQRT 2))
		 (INTEGERP N)
		 (integerp (- n 1))
		 (< 0 (- N 1))
		 (> n 1)
		 (< 0 N))
	    (EQUAL (N-MOD3 (APPEND (A-inv-WORD N) W) X)
		   (LIST 0
			 (MOD (+ (CADDR (N-MOD3 W X))
				 (CADR (N-MOD3 W X)))
			      3)
			 (MOD (+ (CADR (N-MOD3 W X))
				 (CADDR (N-MOD3 W X)))
			      3))))

   :hints (("Goal"
	    :use ((:instance n-mod3-a-inv-n-r-1 (w w) (n n))
		  (:instance weak-word-a-inv-word-w (n (- n 1)) (w w))
		  (:instance n-mod3-a-inv-r (w (append (a-inv-word (- n 1)) w)) (x x))
		  (:instance integerp-n-mod3 (w w) (x x))
		  (:instance n-mod3-a-inv-r (w (APPEND (A-inv-WORD (+ -1 N)) W)) (x x))
		  (:instance n-mod3-a-inv-n-r-6
			     (x (N-MOD3 (APPEND (A-inv-WORD (+ -1 N)) W) X))
			     (a 0)
			     (b (MOD (+ (- (CADR (N-MOD3 W X)))
					(- (CADDR (N-MOD3 W X))))
				     3))
			     (c (MOD (+ (- (CADDR (N-MOD3 W X)))
					(- (CADR (N-MOD3 W X))))
				     3)))
		  (:instance n-mod3-a-inv-n-r-5 (x (- (CADR (N-MOD3 W X)))) (y (- (CADDR (N-MOD3 W X)))))
		  (:instance n-mod3-a-inv-n-r-5 (y (- (CADR (N-MOD3 W X)))) (x (- (CADDR (N-MOD3 W X)))))
		  (:instance n-mod3-a-inv-n-r-4 (b (- (CADR (N-MOD3 W X)))) (c (- (CADDR (N-MOD3 W X)))))
		  (:instance n-mod3-a-inv-n-r-4 (c (- (CADR (N-MOD3 W X)))) (b (- (CADDR (N-MOD3 W X)))))
		  (:instance mod-+-frgrp
			     (x (+ (- (CADR (N-MOD3 W (ACL2-SQRT 2))))
				   (- (CADDR (N-MOD3 W (ACL2-SQRT 2))))))
			     (y (+ (- (CADDR (N-MOD3 W (ACL2-SQRT 2))))
				   (- (CADR (N-MOD3 W (ACL2-SQRT 2))))))
			     (z 3))
		  (:instance mod-+-frgrp
			     (y (+ (- (CADR (N-MOD3 W (ACL2-SQRT 2))))
				   (- (CADDR (N-MOD3 W (ACL2-SQRT 2))))))
			     (x (+ (- (CADDR (N-MOD3 W (ACL2-SQRT 2))))
				   (- (CADR (N-MOD3 W (ACL2-SQRT 2))))))
			     (z 3))
		  (:instance integerp-n-mod3 (w (append (a-inv-word (- n 1)) w)) (x x))
		  (:instance  weak-word-a-inv-word-w (n (- n 1)))
		  (:instance n-mod3-a-inv-n-r-lemma2-1 (x (CADDR (N-MOD3 W (ACL2-SQRT 2)))))
		  (:instance n-mod3-a-inv-n-r-lemma2-1 (x (CADR (N-MOD3 W (ACL2-SQRT 2)))))
		  (:instance n-mod3-a-inv-n-r-lemma2-2
			     (x (CADDR (N-MOD3 W (ACL2-SQRT 2))))
			     (y (CADR (N-MOD3 W (ACL2-SQRT 2)))))
		  )
	    :in-theory nil
	    ;(disable mod n-mod3 append weak-wordp a-inv-word acl2-sqrt)
	    ))
   )


 (defthmd n-mod3-a-inv-n-r=*1/2.2
   (implies (and (integerp n)
		 (> n 0)
		 (> n 1))
	    (and (integerp (- n 1))
		 (< 0 (- n 1))))
   )

 (defthmd n-mod3-a-inv-n-r
   (implies (and (weak-wordp w)
		 (equal x (acl2-sqrt 2))
		 (integerp n)
		 (> n 0))
	    (or (equal (n-mod3 (append (a-inv-word n) w) x)
		       (cons 0 (cons (mod (+ (- (car (cdr (n-mod3 w x))))  (- (car (cdr (cdr (n-mod3 w x)))))) 3)
				     (cons (mod (+ (- (car (cdr (cdr (n-mod3 w x))))) (- (car (cdr (n-mod3 w x))))) 3) nil))))
		(equal (n-mod3 (append (a-inv-word n) w) x)
		       (cons 0 (cons (mod (+ (car (cdr (cdr (n-mod3 w x)))) (car (cdr (n-mod3 w x)))) 3)
				     (cons (mod (+ (car (cdr (n-mod3 w x))) (car (cdr (cdr (n-mod3 w x))))) 3) nil))))))
   
   :hints (("Goal"
	    :in-theory (disable mod n-mod3 weak-wordp)
	    )

	   ("Subgoal *1/2"
	    :cases ((>  n 1)
		    (<= n 1))
	    )
	   ("Subgoal *1/2.2"
	    :use ((:instance n-mod3-a-inv-n-r-lemma1)
		  (:instance n-mod3-a-inv-n-r-lemma2)
		  (:instance n-mod3-a-inv-n-r=*1/2.2 (n n)))
	    ;:in-theory nil
	    )
	   
	   ("Subgoal *1/2.1"
	    :use (:instance n-mod3-a-inv-r (w w) (x x))
	    )
	   )
   )
)
