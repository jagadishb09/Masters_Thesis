
(include-book "free-group")
(local (include-book "arithmetic-5/top" :dir :system))

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

 (local (include-book "workshops/1999/embedded/Exercises/Exercise1-2/Exercise1.2" :dir :system))

 (local
  (defthmd n-mod3-a-r-1
    (implies (and (integerp x)
		  (integerp y)
		  (not (equal y 0)))
	     (integerp (mod x y)))
    )
  )

 (local
  (defthmd n-mod3-a-r-2
    (and (equal (mod (cadr (n-f w x)) 3)
		(cadr (n-mod3 w x)))
	 (equal (mod (caddr (n-f w x)) 3)
		(caddr (n-mod3 w x))))
    :hints (("Goal"
	     :use ((:instance n-mod3 (w w) (x x)))
	     ))
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
		  (:instance mod--
			     (x (cadr (n-f w x)))
			     (y (caddr (n-f w x)))
			     (z 3))

		  (:instance mod--
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


(defthmd n-mod3-a-n-r
  (implies (and (weak-wordp w)
		(equal x (acl2-sqrt 2))
		(integerp n)
		(> n 0)
		(evenp n))
	   (equal (n-mod3 (append (a-word n) w) x)
		  
  )


(encapsulate
 ()
 (local
  (defthmd reduced-a-word-1
    (implies (and (reducedwordp w)
		  (not (equal (car w) #\b)))
	     (reducedwordp (cons #\a w)))
    :hints (("Goal"
	     :use (:instance character-listp-word (x w))
	     ))
    )
  )

 (local
  (defthmd reduced-a-word-2
    (implies (and (integerp n)
		  (> n 1))
	     (AND (INTEGERP (+ -1 N))
                            (<= 1 (+ -1 N))))

    )
  )

 (local
  (defthmd reduced-a-word-3
    (implies (and (integerp n)
		  (>= n 1))
	     (not (equal (car (a-word n)) #\b)))
    )
  )
	     
 
 (defthmd reduced-a-word
   (implies (and (integerp n)
		 (>= n 1))
	    (reducedwordp (a-word n)))
   :hints (("Subgoal *1/2"
	    :cases ((= n 1)
		    (> n 1))
	    :use(
		 (:instance reduced-a-word-2 (n n))
		 (:instance a-word (n n))
		 (:instance reduced-a-word-1 (w (a-word (- n 1))))
		 (:instance reduced-a-word-3 (n (- n 1)))
		 )
	    ))
   )
)

 
 (if (>= n 0)
     (equal (len (a-word n)) n)
   0))
