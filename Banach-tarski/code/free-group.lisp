
(include-book "workshops/2003/cowles-gamboa-van-baalen_matrix/support/matalg" :dir :system)
(include-book "nonstd/nsa/sqrt" :dir :system)
(include-book "groups")



(defun id-rotation ()
  '((:header :dimensions (3 3)
	     :maximum-length 10)
    ((0 . 0) . 1)
    ((0 . 1) . 0)
    ((0 . 2) . 0)
    ((1 . 0) . 0)
    ((1 . 1) . 1)
    ((1 . 2) . 0)
    ((2 . 0) . 0)
    ((2 . 1) . 0)
    ((2 . 2) . 1) 
    )
  )

(defun a-rotation (x)
  `((:header :dimensions (3 3)
	     :maximum-length 10)
    ((0 . 0) . 1)
    ((0 . 1) . 0)
    ((0 . 2) . 0)
    ((1 . 0) . 0)
    ((1 . 1) . 1/3)
    ((1 . 2) . ,(* -2/3 x) )
    ((2 . 0) . 0)
    ((2 . 1) . ,(* 2/3 x) )
    ((2 . 2) . 1/3)
    )
  )

(defun a-inv-rotation (x)
  `((:header :dimensions (3 3)
	     :maximum-length 10)
    ((0 . 0) . 1)
    ((0 . 1) . 0)
    ((0 . 2) . 0)
    ((1 . 0) . 0)
    ((1 . 1) . 1/3)
    ((1 . 2) . ,(* 2/3 x) )
    ((2 . 0) . 0)
    ((2 . 1) . ,(* -2/3 x) )
    ((2 . 2) . 1/3) 
    )
  )

(defun b-rotation (x)
  `((:header :dimensions (3 3)
	     :maximum-length 10)
    ((0 . 0) . 1/3)
    ((0 . 1) . ,(* -2/3 x) )
    ((0 . 2) . 0)
    ((1 . 0) . ,(* 2/3 x) )
    ((1 . 1) . 1/3)
    ((1 . 2) . 0)
    ((2 . 0) . 0)
    ((2 . 1) . 0)
    ((2 . 2) . 1)    
    )
  )

(defun b-inv-rotation (x)
  `((:header :dimensions (3 3)
	     :maximum-length 10)
    ((0 . 0) . 1/3)
    ((0 . 1) . ,(* 2/3 x) )
    ((0 . 2) . 0)
    ((1 . 0) . ,(* -2/3 x) )
    ((1 . 1) . 1/3)
    ((1 . 2) . 0)
    ((2 . 0) . 0)
    ((2 . 1) . 0)
    ((2 . 2) . 1)
    )
  )

(defun point-p ()
  '((:header :dimensions (3 1)
	     :maximum-length 15)
    ((0 . 0) . 0)
    ((1 . 0) . 1)
    ((2 . 0) . 0)
    
    )
  )



(local (include-book "arithmetic-5/top" :dir :system))

(local
 (defthm compress21-lemma
   (equal (compress21 name l n i j default)
	  (if (zp (- i n)) nil
	    (append (compress211 name l n 0 j default)
		    (compress21 name l (+ n 1) i j default))))
   :hints (("Goal"
	    :in-theory (enable compress21 compress211)
	    ))		 
   )
 )

(local
 (defthm m-=-row-1-lemma
   (equal (m-=-row-1 m1 m2 m n)
	  (if (zp m)
	      (m-=-row m1 m2 0 n)
	    (and (m-=-row m1 m2 m n)
		 (m-=-row-1 m1 m2 (- m 1) n))))
   )
 )

(local
 (defthm m-=-row-lemma
   (equal (m-=-row m1 m2 m n)
	  (if (zp n)
	      (equal (fix (aref2 '$arg1 M1 m 0))
		     (fix (aref2 '$arg2 M2 m 0)))
	    (and (equal (fix (aref2 '$arg1 M1 m n))
			(fix (aref2 '$arg2 M2 m n)))
		 (m-=-row M1 M2 m (- n 1)))))
   )
 )


(defthmd funs-lemmas-1
  (and (m-= (m-* (id-rotation) (a-rotation x)) (a-rotation x))
       (m-= (m-* (id-rotation) (a-inv-rotation x)) (a-inv-rotation x))
       (m-= (m-* (id-rotation) (b-rotation x)) (b-rotation x))
       (m-= (m-* (id-rotation) (b-inv-rotation x)) (b-inv-rotation x))
       (m-= (m-* (a-rotation x) (id-rotation)) (a-rotation x))
       (m-= (m-* (a-inv-rotation x) (id-rotation)) (a-inv-rotation x))
       (m-= (m-* (b-rotation x) (id-rotation)) (b-rotation x))
       (m-= (m-* (b-inv-rotation x) (id-rotation)) (b-inv-rotation x))
       )
  :hints (("Goal"
	   :in-theory (enable 
		       alist2p array2p aset2 aref2 compress2 header
		       dimensions maximum-length default
		       matrixp compress21
		       m-=
		       m-0
		       m-1
		       m-trans
		       m-unary--
		       s-*
		       m-binary-+
		       m-binary-*
		       m-/
		       m-singularp
		       M-BINARY-*-ROW-1
		       m-=-row-1
		       m-=-row)
	   )
	  )
  )

(defthmd array2p-funs
  (implies (symbolp y)
	   (and (array2p y (id-rotation))
		(array2p y (a-rotation x))
		(array2p y (a-inv-rotation x))
		(array2p y (b-rotation x))
		(array2p y (b-inv-rotation x))
		(array2p y (point-p))
		(equal (first (dimensions y (id-rotation))) 3)
		(equal (second (dimensions y (id-rotation))) 3)
		(equal (first (dimensions y (a-rotation x))) 3)
		(equal (second (dimensions y (a-rotation x))) 3)
		(equal (first (dimensions y (a-inv-rotation x))) 3)
		(equal (second (dimensions y (a-inv-rotation x))) 3)
		(equal (first (dimensions y (b-rotation x))) 3)
		(equal (second (dimensions y (b-rotation x))) 3)
		(equal (first (dimensions y (b-inv-rotation x))) 3)
		(equal (second (dimensions y (b-inv-rotation x))) 3)
		(equal (first (dimensions y (point-p))) 3)
		(equal (second (dimensions y (point-p))) 1)
		)
	   )
  :hints (("Goal"
	   :in-theory (enable array2p dimensions header maximum-length)
	   ))
  )

(defthmd
  dimensions-array2p-m-*
  (implies (and (array2p name M1)
		(array2p name M2)
		(equal (first (dimensions name M1)) 3)
		(equal (second (dimensions name M1)) 3)
		(equal (first (dimensions name M2)) 3)
		(equal (second (dimensions name M2)) 3))
	   (equal (dimensions name (m-* M1 M2))
		  (list (first (dimensions name M1))
			(second (dimensions name M2)))))
  )

(defthmd
  dimensions-array2p-m-*-1
  (implies (and (array2p name M1)
		(array2p name M2)
		(equal (first (dimensions name M1)) 3)
		(equal (second (dimensions name M1)) 3)
		(equal (first (dimensions name M2)) 3)
		(equal (second (dimensions name M2)) 1))
	   (equal (dimensions name (m-* M1 M2))
		  (list (first (dimensions name M1))
			(second (dimensions name M2)))))
  )


(defun rotation (w x)
  (cond ((atom w) (id-rotation))
	((equal (car w) (wa)) (m-* (a-rotation x) (rotation (cdr w) x)))
	((equal (car w) (wa-inv)) (m-* (a-inv-rotation x) (rotation (cdr w) x)))
	((equal (car w) (wb)) (m-* (b-rotation x) (rotation (cdr w) x)))
	((equal (car w) (wb-inv)) (m-* (b-inv-rotation x) (rotation (cdr w) x)))
	)
  )

(defthmd rotation-=
  (implies (and (reducedwordp w)
		(not (atom w)))	   
	   (cond 
	    ((equal (car w) (wa)) (equal (rotation w x) (m-* (a-rotation x) (rotation (cdr w) x))))
	    ((equal (car w) (wa-inv)) (equal (rotation w x) (m-* (a-inv-rotation x) (rotation (cdr w) x))))
	    ((equal (car w) (wb)) (equal (rotation w x) (m-* (b-rotation x) (rotation (cdr w) x))))
	    ((equal (car w) (wb-inv)) (equal (rotation w x) (m-* (b-inv-rotation x) (rotation (cdr w) x))))
	    )
	   ))

(defthmd rotation-props-ind-case-0
  (IMPLIES
   (AND (NOT (ATOM W))
	(IMPLIES (AND (REDUCEDWORDP (CDR W))
		      (SYMBOLP NAME))
		 (AND (ARRAY2P NAME (ROTATION (CDR W) X))
		      (EQUAL (CAR (DIMENSIONS NAME (ROTATION (CDR W) X)))
			     3)
		      (EQUAL (CADR (DIMENSIONS NAME (ROTATION (CDR W) X)))
			     3))))
   (IMPLIES (AND (REDUCEDWORDP W)
		 (SYMBOLP NAME))
	    (ARRAY2P NAME (ROTATION W X))
	    ))
  :hints (("Goal"
	   :use (
		 (:instance rotation-= (w w) (x x))
		 (:instance reduced-cdr (x w))
		 )
	   :in-theory nil
	   )
	  ("Subgoal 4"
	   :use ((:instance array2p-m-*
			    (name name)
			    (m2 (rotation (cdr w) x))
			    (m1 (a-rotation x)))
		 (:instance array2p-funs (y name) (x x))
		 )
	   )
	  ("Subgoal 3"
	   :use ((:instance array2p-m-*
			    (name name)
			    (m2 (rotation (cdr w) x))
			    (m1 (a-inv-rotation x)))
		 (:instance array2p-funs (y name) (x x))
		 )
	   )
	  ("Subgoal 2"
	   :use ((:instance array2p-m-*
			    (name name)
			    (m2 (rotation (cdr w) x))
			    (m1 (b-rotation x)))
		 (:instance array2p-funs (y name) (x x))
		 )
	   )
	  ("Subgoal 1"
	   :use ((:instance array2p-m-*
			    (name name)
			    (m2 (rotation (cdr w) x))
			    (m1 (b-inv-rotation x)))
		 (:instance array2p-funs (y name) (x x))
		 )
	   )
	  
	  )
  )


(defthmd rotation-props-ind-case-1
  (IMPLIES
   (AND (NOT (ATOM W))
	(IMPLIES (AND (REDUCEDWORDP (CDR W))
		      (SYMBOLP NAME))
		 (AND (ARRAY2P NAME (ROTATION (CDR W) X))
		      (EQUAL (CAR (DIMENSIONS NAME (ROTATION (CDR W) X)))
			     3)
		      (EQUAL (CADR (DIMENSIONS NAME (ROTATION (CDR W) X)))
			     3))))
   (IMPLIES (AND (REDUCEDWORDP W)
		 (SYMBOLP NAME))
	    (and 
	     (EQUAL (CAR (DIMENSIONS NAME (ROTATION W X)))
		    3)
	     (EQUAL (CADR (DIMENSIONS NAME (ROTATION W X)))
		    3)
	     )))
  :hints (("Goal"
	   :use (
		 (:instance rotation-= (w w) (x x))
		 (:instance reduced-cdr (x w))
		 )
	   :in-theory nil
	   )
	  ("Subgoal 8"
	   :use ((:instance dimensions-array2p-m-*
			    (m1 (a-rotation x))
			    (m2 (rotation (cdr w) x)))
		 (:instance array2p-funs (y name) (x x)))
	   )
	  ("Subgoal 7"
	   :use ((:instance dimensions-array2p-m-*
			    (m1 (a-rotation x))
			    (m2 (rotation (cdr w) x)))
		 (:instance array2p-funs (y name) (x x)))
	   )
	  ("Subgoal 6"
	   :use ((:instance dimensions-array2p-m-*
			    (m1 (a-inv-rotation x))
			    (m2 (rotation (cdr w) x)))
		 (:instance array2p-funs (y name) (x x)))
	   )
	  ("Subgoal 5"
	   :use ((:instance dimensions-array2p-m-*
			    (m1 (a-inv-rotation x))
			    (m2 (rotation (cdr w) x)))
		 (:instance array2p-funs (y name) (x x)))
	   )
	  ("Subgoal 4"
	   :use ((:instance dimensions-array2p-m-*
			    (m1 (b-rotation x))
			    (m2 (rotation (cdr w) x)))
		 (:instance array2p-funs (y name) (x x)))
	   )
	  ("Subgoal 3"
	   :use ((:instance dimensions-array2p-m-*
			    (m1 (b-rotation x))
			    (m2 (rotation (cdr w) x)))
		 (:instance array2p-funs (y name) (x x)))
	   )
	  ("Subgoal 2"
	   :use ((:instance dimensions-array2p-m-*
			    (m1 (b-inv-rotation x))
			    (m2 (rotation (cdr w) x)))
		 (:instance array2p-funs (y name) (x x)))
	   )
	  ("Subgoal 1"
	   :use ((:instance dimensions-array2p-m-*
			    (m1 (b-inv-rotation x))
			    (m2 (rotation (cdr w) x)))
		 (:instance array2p-funs (y name) (x x)))
	   )

	  )
  )

(defthmd rotation-props
  (implies (and (reducedwordp w)
		(symbolp name))
	   (and (array2p name (rotation w x))
		(equal (first (dimensions name (rotation w x))) 3)
		(equal (second (dimensions name (rotation w x))) 3))
	   )
  :hints (("Subgoal *1/5"
	   :use ((:instance rotation-props-ind-case-0)
		 (:instance rotation-props-ind-case-1))
	   )
	  ("Subgoal *1/4"
	   :use ((:instance rotation-props-ind-case-0)
		 (:instance rotation-props-ind-case-1))
	   )
	  ("Subgoal *1/3"
	   :use ((:instance rotation-props-ind-case-0)
		 (:instance rotation-props-ind-case-1))
	   )
	  ("Subgoal *1/2"
	   :use ((:instance rotation-props-ind-case-0)
		 (:instance rotation-props-ind-case-1))
	   )
	  ("Subgoal *1/1"
	   :in-theory (enable dimensions header maximum-length)
	   )
	  )
  )


(defthmd m-*-rotation-point-dim
  (implies (and (reducedwordp w)
		(symbolp name))
	   (and (array2p name (m-* (rotation w x) (point-p)))
		(equal (first (dimensions name (m-* (rotation w x) (point-p)))) 3)
		(equal (second (dimensions name (m-* (rotation w x) (point-p)))) 1))
	   )
  :hints (("Goal"
	   :use ((:instance rotation-props (w w) (x x) (name name))
		 (:instance dimensions-array2p-m-*-1
			    (m1 (rotation w x))
			    (m2 (point-p))
			    (name name))
		 (:instance array2p-funs
			    (y name))
		 )
	   :in-theory (disable rotation)
	   ))
  )

(defun int-point (a i j n x)
  (cond ((and (equal i 0) (equal j 0)) (* (/ (aref2 '$arg1 a i j) x) (expt 3 n)))
	((and (equal i 2) (equal j 0)) (* (/ (aref2 '$arg1 a i j) x) (expt 3 n)))
	((and (equal i 1) (equal j 0)) (* (aref2 '$arg1 a i j) (expt 3 n)))
	(t nil))
  )


(defthmd rotation-values-ind-case-lemma1-1
  (implies (and (symbolp name)
		(acl2-numberp (aref2 name m1 0 0))
		(acl2-numberp (aref2 name m1 1 0))
		(acl2-numberp (aref2 name m1 2 0)))
	   (and (acl2-numberp (aref2 '$arg1 m1 0 0))
		(acl2-numberp (aref2 '$arg1 m1 1 0))
		(acl2-numberp (aref2 '$arg1 m1 2 0))
		(acl2-numberp (aref2 '$arg2 m1 0 0))
		(acl2-numberp (aref2 '$arg2 m1 1 0))
		(acl2-numberp (aref2 '$arg2 m1 2 0)))
	   
	   )
  :hints (("Goal"
	   :in-theory (enable aref2 default header)
	   ))

  )

(defthmd rotation-values-ind-case-lemma1
  (implies (and (symbolp name)
		(acl2-numberp (aref2 name m1 0 0))
		(acl2-numberp (aref2 name m1 1 0))
		(acl2-numberp (aref2 name m1 2 0))
		(acl2-numberp x)
		(array2p name m1)
		(equal (first (dimensions name m1)) 3)
		(equal (second (dimensions name m1)) 1))
	   (and (equal (aref2 name (m-* (a-rotation x) m1) 0 0) (aref2 name m1 0 0))
		(equal (aref2 name (m-* (a-rotation x) m1) 1 0) (/ (- (aref2 name m1 1 0) (* 2 x (aref2 name m1 2 0))) 3))
		(equal (aref2 name (m-* (a-rotation x) m1) 2 0) (/ (+ (* 2 x (aref2 name m1 1 0)) (aref2 name m1 2 0)) 3))
		(equal (aref2 name (m-* (a-inv-rotation x) m1) 0 0) (aref2 name m1 0 0))
		(equal (aref2 name (m-* (a-inv-rotation x) m1) 1 0) (/ (+ (aref2 name m1 1 0) (* 2 x (aref2 name m1 2 0))) 3))
		(equal (aref2 name (m-* (a-inv-rotation x) m1) 2 0) (/ (- (aref2 name m1 2 0) (* 2 x (aref2 name m1 1 0))) 3))
		(equal (aref2 name (m-* (b-rotation x) m1) 0 0) (/ (- (aref2 name m1 0 0) (* 2 x (aref2 name m1 1 0))) 3))
		(equal (aref2 name (m-* (b-rotation x) m1) 1 0) (/ (+ (aref2 name m1 1 0) (* 2 x (aref2 name m1 0 0))) 3))
		(equal (aref2 name (m-* (b-rotation x) m1) 2 0) (aref2 name m1 2 0))
		(equal (aref2 name (m-* (b-inv-rotation x) m1) 0 0) (/ (+ (aref2 name m1 0 0) (* 2 x (aref2 name m1 1 0))) 3))
		(equal (aref2 name (m-* (b-inv-rotation x) m1) 1 0) (/ (- (aref2 name m1 1 0) (* 2 x (aref2 name m1 0 0))) 3))
		(equal (aref2 name (m-* (b-inv-rotation x) m1) 2 0) (aref2 name m1 2 0)))
	   )
  :hints (("Goal"
	   :use (
		 (:instance array2p-funs (y name))
		 (:instance array2p-alist2p (name name) (l m1))
		 (:instance array2p-alist2p (name name) (l (a-rotation x)))
		 (:instance array2p-alist2p (name name) (l (a-inv-rotation x)))
		 (:instance array2p-alist2p (name name) (l (b-rotation x)))
		 (:instance array2p-alist2p (name name) (l (b-inv-rotation x)))
		 (:instance rotation-values-ind-case-lemma1-1)
		 )
	   :in-theory (enable aref2 default header)
	   ))
  )


(encapsulate
 ()

 (local
  (defthmd acl2-nump-rot-ind
    (IMPLIES (AND (NOT (ATOM W))
		  (IMPLIES (AND (ACL2-NUMBERP X)
				(symbolp name)
				(REDUCEDWORDP (CDR W)))
			   (and (ACL2-NUMBERP (aref2 name (M-* (ROTATION (CDR W) X) (POINT-P)) 0 0))
				(ACL2-NUMBERP (aref2 name (M-* (ROTATION (CDR W) X) (POINT-P)) 1 0))
				(ACL2-NUMBERP (aref2 name (M-* (ROTATION (CDR W) X) (POINT-P)) 2 0)))))
	     (IMPLIES (AND (ACL2-NUMBERP X) (REDUCEDWORDP W) (symbolp name))
		      (and (ACL2-NUMBERP (aref2 name (M-* (ROTATION w X) (POINT-P)) 0 0))
			   (ACL2-NUMBERP (aref2 name (M-* (ROTATION w X) (POINT-P)) 1 0))
			   (ACL2-NUMBERP (aref2 name (M-* (ROTATION w X) (POINT-P)) 2 0)))))
    :hints (("Goal"
	     :use (
		   (:instance m-*-rotation-point-dim (w (cdr w)) (name name))
		   (:instance rotation-= (w w))
		   (:instance associativity-of-m-*
			      (m1 (a-rotation x))
			      (m2 (rotation (cdr w) x))
			      (m3 (point-p)))
		   (:instance associativity-of-m-*
			      (m1 (a-inv-rotation x))
			      (m2 (rotation (cdr w) x))
			      (m3 (point-p)))
		   (:instance associativity-of-m-*
			      (m1 (b-rotation x))
			      (m2 (rotation (cdr w) x))
			      (m3 (point-p)))
		   (:instance associativity-of-m-*
			      (m1 (b-inv-rotation x))
			      (m2 (rotation (cdr w) x))
			      (m3 (point-p)))

		   (:instance rotation-values-ind-case-lemma1
			      (m1 (M-* (ROTATION (CDR W) X) (POINT-P)))
			      (name name)
			      (x x)
			      )
		   
		   )
	     :do-not-induct t
	     
	     ))
    
    )
  )
 

 (defthmd acl2-nump-rot
   (implies (and (acl2-numberp x)
		 (symbolp name)
		 (reducedwordp w))
	    (and (ACL2-NUMBERP (aref2 name (M-* (ROTATION w X) (POINT-P)) 0 0))
		 (ACL2-NUMBERP (aref2 name (M-* (ROTATION w X) (POINT-P)) 1 0))
		 (ACL2-NUMBERP (aref2 name (M-* (ROTATION w X) (POINT-P)) 2 0))))
   
   :hints (("Subgoal *1/5"
	    :use (:instance acl2-nump-rot-ind)
	    )
	   ("Subgoal *1/4"
	    :use (:instance acl2-nump-rot-ind)
	    )
	   ("Subgoal *1/3"
	    :use (:instance acl2-nump-rot-ind)
	    )
	   ("Subgoal *1/2"
	    :use (:instance acl2-nump-rot-ind)
	    )
	   ("Subgoal *1/1"
	    :in-theory (enable reducedwordp rotation aref2)
	    )
	   
	   )
   )
 )


(encapsulate
 ()

 (local
  (defthmd lemma-0-1
    (implies (integerp n)
	     (equal (* (expt 3 (- n 1)) 3) (expt 3 n)))
    )
  )

 (local
  (defthmd lemma-0-2
    (implies (integerp x)
	     (integerp (* x 3)))
    )
  )

 (local
  (defthmd lemma-0
    (implies (and (acl2-numberp a)
		  (equal x (acl2-sqrt 2))
		  (integerp n)
		  (>= n 0)
		  (integerp (* (/ a x) (expt 3 (- n 1)))))
	     (integerp (* (/ a x) (expt 3 n)))
	     )

    :hints (("Goal"
	     :use ((:instance lemma-0-1)
		   (:instance lemma-0-2 (x (* (/ a x) (expt 3 (- n 1)))))
		   )
	     ))
    )
  )

 (local
  (defthmd lemma-1-1
    (implies (integerp n)
	     (and (equal (expt 3 n) (* (expt 3 (- n 1)) 3))
		  (equal (/ (expt 3 n) 3) (expt 3 (- n 1))))
	     )
    )
  )

 (local
  (defthmd lemma-1-2
    (implies (integerp x)
	     (and (integerp (* x 4))
		  (integerp (* 4 x))
		  (integerp (* x -4))
		  (integerp (- x))))
    )
  )

 (local
  (defthmd lemma-1-3
    (implies (and (integerp x)
		  (integerp y))
	     (and (integerp (+ x y))
		  (integerp (- x y))))
    )
  )

 (local
  (defthmd sqrt-2-lemmas
    (equal (acl2-sqrt 2) (/ 2 (acl2-sqrt 2)))
    :hints (("Goal"
	     :use (:instance sqrt-* (x 2) (y 2))
	     ))
    )
  )

 (local
  (defthmd lemma-1-4
    (implies (and (integerp n)
		  (acl2-numberp b)
		  (acl2-numberp c)
		  )
	     (equal (* (/ (- b (* 2 x c)) 3) (expt 3 n))
		    (- (* b (expt 3 (- n 1))) (* 2 x c (expt 3 (- n 1)))))
	     )
    :hints (("Goal"
	     :use (:instance lemma-1-1)
	     ))
    )
  )

 (local
  (defthmd lemma-1-5
    (implies (and (integerp n)
		  (acl2-numberp c)
		  (equal x (acl2-sqrt 2))
		  )
	     (equal (* 2 x c (expt 3 (- n 1)))
		    (* 4 (/ c x) (expt 3 (- n 1))))
	     )
    :hints (("Goal"
	     :use
	     (
	      (:instance sqrt-* (x 2) (y 2))
	      (:instance sqrt-4)
	      (:instance sqrt-2-lemmas)
	      )
	     :in-theory (disable acl2-sqrt)
	     ))
    )
  )
 

 (local
  (defthmd lemma-1
    (implies (and (acl2-numberp b)
		  (acl2-numberp c)
		  (equal x (acl2-sqrt 2))
		  (integerp n)
		  (>= n 0)
		  (integerp (* b (expt 3 (- n 1))))
		  (integerp (* (/ c x) (expt 3 (- n 1)))))
	     (integerp (* (/ (- b (* 2 x c)) 3) (expt 3 n)))
	     )

    :hints (("Goal"
	     :use (
		   (:instance lemma-1-2 (x (* (/ c x) (expt 3 (- n 1)))))
		   (:instance lemma-1-3
			      (x (* b (expt 3 (- n 1))))
			      (y (* 4 (/ c x) (expt 3 (- n 1)))))
		   (:instance lemma-1-4)
		   (:instance lemma-1-5)
		   )
	     :in-theory nil
	     ))
    )
  )

 (local
  (defthmd lemma-2-1
    (implies (and (acl2-numberp b)
		  (acl2-numberp c)
		  (equal x (acl2-sqrt 2))
		  (integerp n)
		  (>= n 0))
	     (equal (* (/ (/ (+ (* 2 x b) c) 3) x) (expt 3 n))
		    (+ (* 2 b (expt 3 (- n 1))) (* (/ c x) (expt 3 (- n 1))))
		    )
	     )
    :hints (("Goal"
	     :in-theory (disable acl2-sqrt)
	     ))
    )
  )
 
 (local
  (defthmd lemma-2
    (implies (and (acl2-numberp b)
		  (acl2-numberp c)
		  (equal x (acl2-sqrt 2))
		  (integerp n)
		  (>= n 0)
		  (integerp (* b (expt 3 (- n 1))))
		  (integerp (* (/ c x) (expt 3 (- n 1)))))
	     (integerp (* (/ (/ (+ (* 2 x b) c) 3) x) (expt 3 n)))
	     )
    :hints (("Goal"
	     :use ((:instance lemma-2-1))
	     :in-theory (disable acl2-sqrt)
	     ))
    )
  )


 (local
  (defthmd lemma-3-1
    (implies (and (integerp n)
		  (acl2-numberp b)
		  (acl2-numberp c)
		  )
	     (equal (* (/ (+ b (* 2 x c)) 3) (expt 3 n))
		    (+ (* b (expt 3 (- n 1))) (* 2 x c (expt 3 (- n 1)))))
	     )
    :hints (("Goal"
	     :use (:instance lemma-1-1)
	     ))
    )
  )
 
 
 (local
  (defthmd lemma-3
    (implies (and (acl2-numberp b)
		  (acl2-numberp c)
		  (equal x (acl2-sqrt 2))
		  (integerp n)
		  (>= n 0)
		  (integerp (* b (expt 3 (- n 1))))
		  (integerp (* (/ c x) (expt 3 (- n 1)))))
	     (integerp (* (/ (+ b (* 2 x c)) 3) (expt 3 n)))
	     )
    :hints (("Goal"
	     :use (
		   (:instance lemma-1-2 (x (* (/ c x) (expt 3 (- n 1)))))
		   (:instance lemma-1-3
			      (x (* b (expt 3 (- n 1))))
			      (y (* 4 (/ c x) (expt 3 (- n 1)))))
		   (:instance lemma-3-1)
		   (:instance lemma-1-5)
		   )
	     :in-theory nil
	     ))
    )
  )

 (local
  (defthmd lemma-4-1
    (implies (and (acl2-numberp b)
		  (acl2-numberp c)
		  (equal x (acl2-sqrt 2))
		  (integerp n)
		  (>= n 0))
	     (equal (* (/ (/ (- c (* 2 x b)) 3) x) (expt 3 n))
		    (- (* (/ c x) (expt 3 (- n 1))) (* 2 b (expt 3 (- n 1))))
		    )
	     )
    :hints (("Goal"
	     :in-theory (disable acl2-sqrt)
	     ))
    )
  )

 (local
  (defthmd lemma-4
    (implies (and (acl2-numberp b)
		  (acl2-numberp c)
		  (equal x (acl2-sqrt 2))
		  (integerp n)
		  (>= n 0)
		  (integerp (* b (expt 3 (- n 1))))
		  (integerp (* (/ c x) (expt 3 (- n 1)))))
	     (integerp (* (/ (/ (- c (* 2 x b)) 3) x) (expt 3 n)))
	     )
    :hints (("Goal"
	     :use (
		   (:instance lemma-4-1)
		   )
	     ))
    )
  )

 (local
  (defthmd lemma-5-1
    (implies (and (acl2-numberp a)
		  (acl2-numberp b)
		  (equal x (acl2-sqrt 2))
		  (integerp n)
		  (>= n 0))
	     (equal (* (/ (/ (- a (* 2 x b)) 3) x) (expt 3 n))
		    (- (* (/ a x) (expt 3 (- n 1))) (* 2 b (expt 3 (- n 1))))
		    )
	     )
    :hints (("Goal"
	     :in-theory (disable acl2-sqrt)
	     ))
    )
  )

 (local
  (defthmd lemma-5
    (implies (and (acl2-numberp a)
		  (acl2-numberp b)
		  (equal x (acl2-sqrt 2))
		  (integerp n)
		  (>= n 0)
		  (integerp (* (/ a x) (expt 3 (- n 1))))
		  (integerp (* b (expt 3 (- n 1)))))
	     (integerp (* (/ (/ (- a (* 2 x b)) 3) x) (expt 3 n)))
	     )
    :hints (("Goal"
	     :use (
		   (:instance lemma-5-1)
		   )
	     ))
    )
  )

 (local
  (defthmd lemma-6-1
    (implies (and (integerp n)
		  (acl2-numberp b)
		  (acl2-numberp a)
		  )
	     (equal (* (/ (+ b (* 2 x a)) 3) (expt 3 n))
		    (+ (* b (expt 3 (- n 1))) (* 2 x a (expt 3 (- n 1)))))
	     )
    :hints (("Goal"
	     :use (:instance lemma-1-1)
	     ))
    )
  )

 (local
  (defthmd lemma-6
    (implies (and (acl2-numberp a)
		  (acl2-numberp b)
		  (equal x (acl2-sqrt 2))
		  (integerp n)
		  (>= n 0)
		  (integerp (* (/ a x) (expt 3 (- n 1))))
		  (integerp (* b (expt 3 (- n 1)))))
	     (integerp (* (/ (+ b (* 2 x a)) 3) (expt 3 n)))
	     )
    :hints (("Goal"
	     :use (
		   (:instance lemma-1-2 (x (* (/ a x) (expt 3 (- n 1)))))
		   (:instance lemma-1-3
			      (x (* b (expt 3 (- n 1))))
			      (y (* 4 (/ a x) (expt 3 (- n 1)))))
		   (:instance lemma-6-1)
		   (:instance lemma-1-5 (c a))
		   )
	     :in-theory nil
	     ))
    )
  )

 (local
  (defthmd lemma-7
    (implies (and (acl2-numberp c)
		  (equal x (acl2-sqrt 2))
		  (integerp n)
		  (>= n 0)
		  (integerp (* (/ c x) (expt 3 (- n 1)))))
	     (integerp (* (/ c x) (expt 3 n)))
	     )
    :hints (("Goal"
	     :use ((:instance lemma-1-1)
		   (:instance lemma-0-2 (x (* (/ c x) (expt 3 (- n 1)))))
		   )
	     :in-theory (disable acl2-sqrt)
	     ))
    )
  )

 (local
  (defthmd lemma-8-1
    (implies (and (acl2-numberp b)
		  (acl2-numberp a)
		  (equal x (acl2-sqrt 2))
		  (integerp n)
		  (>= n 0))
	     (equal (* (/ (/ (+ a (* 2 x b)) 3) x) (expt 3 n))
		    (+ (* (/ a x) (expt 3 (- n 1))) (* 2 b (expt 3 (- n 1))))
		    )
	     )
    :hints (("Goal"
	     :in-theory (disable acl2-sqrt)
	     ))
    )
  )

 (local
  (defthmd lemma-8
    (implies (and (acl2-numberp a)
		  (acl2-numberp b)
		  (equal x (acl2-sqrt 2))
		  (integerp n)
		  (>= n 0)
		  (integerp (* (/ a x) (expt 3 (- n 1))))
		  (integerp (* b (expt 3 (- n 1)))))
	     (integerp (* (/ (/ (+ a (* 2 x b)) 3) x) (expt 3 n)))
	     )
    :hints (("Goal"
	     :use (
		   (:instance lemma-8-1)
		   )
	     :in-theory (disable acl2-sqrt)
	     ))
    )
  )

 (local
  (defthmd lemma-9
    (implies (and (acl2-numberp a)
		  (acl2-numberp b)
		  (equal x (acl2-sqrt 2))
		  (integerp n)
		  (>= n 0)
		  (integerp (* (/ a x) (expt 3 (- n 1))))
		  (integerp (* b (expt 3 (- n 1)))))
	     (integerp (* (/ (- b (* 2 x a)) 3) (expt 3 n)))
	     )
    :hints (("Goal"
	     :use (:instance lemma-1 (b b) (c a))
	     ))
    )
  )
 

 (defthmd lemma-int
   (implies (and (acl2-numberp a)
		 (acl2-numberp b)
		 (acl2-numberp c)
		 (equal x (acl2-sqrt 2))
		 (integerp n)
		 (>= n 0)
		 (integerp (* (/ a x) (expt 3 (- n 1))))
		 (integerp (* b (expt 3 (- n 1))))
		 (integerp (* (/ c x) (expt 3 (- n 1))))
		 )
	    (and (integerp (* (/ a x) (expt 3 n)))
		 (integerp (* (/ (- b (* 2 x c)) 3) (expt 3 n)))
		 (integerp (* (/ (/ (+ (* 2 x b) c) 3) x) (expt 3 n)))
		 (integerp (* (/ (+ b (* 2 x c)) 3) (expt 3 n)))
		 (integerp (* (/ (/ (- c (* 2 x b)) 3) x) (expt 3 n)))
		 (integerp (* (/ (/ (- a (* 2 x b)) 3) x) (expt 3 n)))
		 (integerp (* (/ (+ b (* 2 x a)) 3) (expt 3 n)))
		 (integerp (* (/ c x) (expt 3 n)))
		 (integerp (* (/ (/ (+ a (* 2 x b)) 3) x) (expt 3 n)))
		 (integerp (* (/ (- b (* 2 x a)) 3) (expt 3 n)))
		 ))
   :hints (("Goal"
	    :use ((:instance lemma-0)
		  (:instance lemma-1)
		  (:instance lemma-2)
		  (:instance lemma-3)
		  (:instance lemma-4)
		  (:instance lemma-5)
		  (:instance lemma-6)
		  (:instance lemma-7)
		  (:instance lemma-8)
		  (:instance lemma-9)
		  )
	    :in-theory nil
	    ))
   )
 )


(defthmd sqrt-2-lemmas
  (and (acl2-numberp (acl2-sqrt 2))
       (i-limited (acl2-sqrt 2))
       (realp (acl2-sqrt 2))
       (equal (* (acl2-sqrt 2) (acl2-sqrt 2)) 2)
       (equal (/ 2 (acl2-sqrt 2)) (acl2-sqrt 2))
       (> (acl2-sqrt 2) 1)
       (not (equal (acl2-sqrt 2) 0)))
  :hints (("Goal"
	   :use ((:instance sqrt-* (x 2) (y 2))

		 )
	   :in-theory (disable acl2-sqrt)
	   ))
  )

(defthmd word-len-lemma
  (implies (reducedwordp w)
	   (and (integerp (len w))
		(>= (len w) 0)
		(if (consp w)
		    (and (equal (- (len w) 1) (len (cdr w)))
			 (equal (len (cdr w)) (- (len w) 1)))
		  0)
		)
	   )
  )

(encapsulate
 ()

 (local
  (defthm rotation-values-ind-case
    (IMPLIES
     (AND (CONSP W)
	  (IMPLIES (AND (REDUCEDWORDP (CDR W))
			(EQUAL X (ACL2-SQRT 2)))
		   (AND (INTEGERP (INT-POINT (M-* (ROTATION (CDR W) X) (POINT-P))
					     0 0 (LEN (CDR W))
					     X))
			(INTEGERP (INT-POINT (M-* (ROTATION (CDR W) X) (POINT-P))
					     1 0 (LEN (CDR W))
					     X))
			(INTEGERP (INT-POINT (M-* (ROTATION (CDR W) X) (POINT-P))
					     2 0 (LEN (CDR W))
					     X)))))
     (IMPLIES (AND (REDUCEDWORDP W)
		   (EQUAL X (ACL2-SQRT 2)))
	      (AND (INTEGERP (INT-POINT (M-* (ROTATION W X) (POINT-P))
					0 0 (LEN W)
					X))
		   (INTEGERP (INT-POINT (M-* (ROTATION W X) (POINT-P))
					1 0 (LEN W)
					X))
		   (INTEGERP (INT-POINT (M-* (ROTATION W X) (POINT-P))
					2 0 (LEN W)
					X)))))
    :hints (("Goal"
	     :cases ((EQUAL (CAR W) (WA))
		     (EQUAL (CAR W) (WA-inv))
		     (EQUAL (CAR W) (WB))
		     (EQUAL (CAR W) (WB-inv))
		     )
	     :use (
		   (:instance word-len-lemma (w w))
		   (:instance sqrt-2-lemmas)
		   (:instance reduced-cdr (x w))
		   (:instance rotation-= (w w) (x x))
		   (:instance associativity-of-m-*
			      (m1 (a-inv-rotation x))
			      (m2 (rotation (cdr w) x))
			      (m3 (point-p)))
		   (:instance associativity-of-m-*
			      (m1 (b-rotation x))
			      (m2 (rotation (cdr w) x))
			      (m3 (point-p)))
		   (:instance associativity-of-m-*
			      (m1 (b-inv-rotation x))
			      (m2 (rotation (cdr w) x))
			      (m3 (point-p)))
		   (:instance associativity-of-m-*
			      (m1 (a-rotation x))
			      (m2 (rotation (cdr w) x))
			      (m3 (point-p)))
		   (:instance word-len-lemma (w w))
		   (:instance reduced-cdr (x w))
		   (:instance acl2-nump-rot (x x) (name '$arg1) (w (cdr w)))
		   (:instance m-*-rotation-point-dim (w (cdr w)) (name '$arg1))
		   (:instance rotation-values-ind-case-lemma1
			      (name '$arg1)
			      (x x)
			      (m1 (M-* (ROTATION (CDR W) X) (POINT-P)))
			      )
		   (:instance lemma-int
			      (x x)
			      (n (len w))
			      (a (aref2 '$arg1 (M-* (ROTATION (CDR W) X) (POINT-P)) 0 0))
			      (b (aref2 '$arg1 (M-* (ROTATION (CDR W) X) (POINT-P)) 1 0))
			      (c (aref2 '$arg1 (M-* (ROTATION (CDR W) X) (POINT-P)) 2 0)))
		   (:instance int-point
			      (a (M-* (ROTATION w (ACL2-SQRT 2))
				      (POINT-P)))
			      (i 0)
			      (j 0)
			      (n (len w))
			      (x x))
		   (:instance int-point
			      (a (M-* (ROTATION w (ACL2-SQRT 2))
				      (POINT-P)))
			      (i 1)
			      (j 0)
			      (n (len w))
			      (x x))
		   (:instance int-point
			      (a (M-* (ROTATION w (ACL2-SQRT 2))
				      (POINT-P)))
			      (i 2)
			      (j 0)
			      (n (len w))
			      (x x))
		   (:instance int-point
			      (a (M-* (ROTATION (cdr w) (ACL2-SQRT 2))
				      (POINT-P)))
			      (i 0)
			      (j 0)
			      (n (len (cdr w)))
			      (x x))
		   (:instance int-point
			      (a (M-* (ROTATION (cdr w) (ACL2-SQRT 2))
				      (POINT-P)))
			      (i 1)
			      (j 0)
			      (n (len (cdr w)))
			      (x x))
		   (:instance int-point
			      (a (M-* (ROTATION (cdr w) (ACL2-SQRT 2))
				      (POINT-P)))
			      (i 2)
			      (j 0)
			      (n (len (cdr w)))
			      (x x))
		   )
	     :in-theory nil
	     :do-not-induct t
	     )
	    )
    )
  )

 (defthmd rotation-values
   (implies (and (reducedwordp w)
		 (equal x (acl2-sqrt 2)))
	    (and (integerp (int-point (m-* (rotation w x) (point-p)) 0 0 (len w) x))
		 (integerp (int-point (m-* (rotation w x) (point-p)) 1 0 (len w) x))
		 (integerp (int-point (m-* (rotation w x) (point-p)) 2 0 (len w) x))
		 )
	    )
   :hints (("Subgoal *1/1"
	    :use ((:instance rotation-values-ind-case))
	    :in-theory (disable acl2-sqrt)
	    ))
   )
 )

(defun n-f(w x)
  (cons (int-point (m-* (rotation w x) (point-p)) 0 0 (len w) (acl2-sqrt 2))
	(cons (int-point (m-* (rotation w x) (point-p)) 1 0 (len w) (acl2-sqrt 2))
	      (cons (int-point (m-* (rotation w x) (point-p)) 2 0 (len w) (acl2-sqrt 2)) nil)))
  )

(encapsulate
 ()

 (local
  (defthmd len-lemma
    (implies (reducedwordp w)
	     (and (equal (len (cons (wa) w)) (+ (len w) 1))
		  (integerp (len w)))
	     )
    )
  )

 (local
  (defthmd n-f-a-r-lemma
    (implies (reducedwordp w)
	     (equal (rotation (cons (wa) w) x)
		    (m-* (a-rotation x) (rotation w x))))
    )
  )

 (local
  (defthmd expt-lemma
    (implies (integerp n)
	     (equal (expt 3 (+ n 1)) (* (expt 3 n) 3)))
    )
  )

 (local
  (defthmd sub4-lemma0
    (implies
     (EQUAL (+ (* 1/3
		  (AREF2 '$ARG1
			 (M-* (ROTATION W (ACL2-SQRT 2))
			      '((:HEADER :DIMENSIONS (3 1)
					 :MAXIMUM-LENGTH 15)
				((0 . 0) . 0)
				((1 . 0) . 1)
				((2 . 0) . 0)))
			 2 0))
	       (* 2/3 (ACL2-SQRT 2)
		  (AREF2 '$ARG1
			 (M-* (ROTATION W (ACL2-SQRT 2))
			      '((:HEADER :DIMENSIONS (3 1)
					 :MAXIMUM-LENGTH 15)
				((0 . 0) . 0)
				((1 . 0) . 1)
				((2 . 0) . 0)))
			 1 0)))
	    (AREF2 '$ARG1
		   (M-* (A-ROTATION (ACL2-SQRT 2))
			(ROTATION W (ACL2-SQRT 2))
			'((:HEADER :DIMENSIONS (3 1)
				   :MAXIMUM-LENGTH 15)
			  ((0 . 0) . 0)
			  ((1 . 0) . 1)
			  ((2 . 0) . 0)))
		   2 0))
     (EQUAL 
      (AREF2 '$ARG1
	     (M-* (A-ROTATION (ACL2-SQRT 2))
		  (ROTATION W (ACL2-SQRT 2))
		  '((:HEADER :DIMENSIONS (3 1)
			     :MAXIMUM-LENGTH 15)
		    ((0 . 0) . 0)
		    ((1 . 0) . 1)
		    ((2 . 0) . 0)))
	     2 0)
      (+ 
       (* 2/3 (ACL2-SQRT 2)
	  (AREF2 '$ARG1
		 (M-* (ROTATION W (ACL2-SQRT 2))
		      '((:HEADER :DIMENSIONS (3 1)
				 :MAXIMUM-LENGTH 15)
			((0 . 0) . 0)
			((1 . 0) . 1)
			((2 . 0) . 0)))
		 1 0))
       (* 1/3
	  (AREF2 '$ARG1
		 (M-* (ROTATION W (ACL2-SQRT 2))
		      '((:HEADER :DIMENSIONS (3 1)
				 :MAXIMUM-LENGTH 15)
			((0 . 0) . 0)
			((1 . 0) . 1)
			((2 . 0) . 0)))
		 2 0)))
      )
     
     )
    )
  )

 (local
  (defthmd sub4-lemma1
    (equal
     (AREF2 '$ARG1
	    (M-* (ROTATION (CONS #\a W) (ACL2-SQRT 2))
		 '((:HEADER :DIMENSIONS (3 1)
			    :MAXIMUM-LENGTH 15)
		   ((0 . 0) . 0)
		   ((1 . 0) . 1)
		   ((2 . 0) . 0)))
	    2 0)
     (AREF2 '$ARG1
	    (M-* (A-ROTATION (ACL2-SQRT 2))
		 (ROTATION W (ACL2-SQRT 2))
		 '((:HEADER :DIMENSIONS (3 1)
			    :MAXIMUM-LENGTH 15)
		   ((0 . 0) . 0)
		   ((1 . 0) . 1)
		   ((2 . 0) . 0)))
	    2 0)
     )
    )
  )

 (local
  (defthmd sub4-lemma2
    (implies
     (EQUAL (+ (* 1/3
		  (AREF2 '$ARG1
			 (M-* (ROTATION W (ACL2-SQRT 2))
			      '((:HEADER :DIMENSIONS (3 1)
					 :MAXIMUM-LENGTH 15)
				((0 . 0) . 0)
				((1 . 0) . 1)
				((2 . 0) . 0)))
			 2 0))
	       (* 2/3 (ACL2-SQRT 2)
		  (AREF2 '$ARG1
			 (M-* (ROTATION W (ACL2-SQRT 2))
			      '((:HEADER :DIMENSIONS (3 1)
					 :MAXIMUM-LENGTH 15)
				((0 . 0) . 0)
				((1 . 0) . 1)
				((2 . 0) . 0)))
			 1 0)))
	    (AREF2 '$ARG1
		   (M-* (A-ROTATION (ACL2-SQRT 2))
			(ROTATION W (ACL2-SQRT 2))
			'((:HEADER :DIMENSIONS (3 1)
				   :MAXIMUM-LENGTH 15)
			  ((0 . 0) . 0)
			  ((1 . 0) . 1)
			  ((2 . 0) . 0)))
		   2 0))
     
     (EQUAL (* 3 (/ (ACL2-SQRT 2))
	       (AREF2 '$ARG1
		      (M-* (ROTATION (CONS #\a W) (ACL2-SQRT 2))
			   '((:HEADER :DIMENSIONS (3 1)
				      :MAXIMUM-LENGTH 15)
			     ((0 . 0) . 0)
			     ((1 . 0) . 1)
			     ((2 . 0) . 0)))
		      2 0))
	    (+ (* 2
		  (AREF2 '$ARG1
			 (M-* (ROTATION W (ACL2-SQRT 2))
			      '((:HEADER :DIMENSIONS (3 1)
					 :MAXIMUM-LENGTH 15)
				((0 . 0) . 0)
				((1 . 0) . 1)
				((2 . 0) . 0)))
			 1 0))
	       (* (/ (ACL2-SQRT 2))
		  (AREF2 '$ARG1
			 (M-* (ROTATION W (ACL2-SQRT 2))
			      '((:HEADER :DIMENSIONS (3 1)
					 :MAXIMUM-LENGTH 15)
				((0 . 0) . 0)
				((1 . 0) . 1)
				((2 . 0) . 0)))
			 2 0))))
     )

    :hints (("Goal"
	     :use (
		   (:instance sub4-lemma0)
		   (:instance sub4-lemma1)
		   )
	     :in-theory (disable m-* aref2 acl2-sqrt)
	     ))
    
    )
  )

 (local
  (defthmd sub2-lemma
    (implies (and (acl2-numberp x)
		  (equal (+ (* 1/3 x) (* -2/3 (acl2-sqrt 2) y)) z))
	     (equal (+ (* 3 z) (* 4 (/ (acl2-sqrt 2)) y)) x))
    :hints (("Goal"
	     :use (:instance sqrt-2-lemmas)
	     :in-theory (disable acl2-sqrt)
	     ))
    )
  )

  (defthmd n-f-a-r
    (implies (and (reducedwordp w)
		  (equal x (acl2-sqrt 2)))
	     (equal (n-f (cons (wa) w) x) (cons (* 3 (car (n-f w x))) (cons (- (car (cdr (n-f w x))) (* 4 (car (cdr (cdr (n-f w x)))))) (cons (+ (* 2 (car (cdr (n-f w x)))) (car (cdr (cdr (n-f w x))))) nil)))))
    :hints (("Goal"
	     :use ((:instance m-*-rotation-point-dim (w w) (x x) (name '$arg1))
		   (:instance rotation-values-ind-case-lemma1 (name '$arg1) (m1 (m-* (rotation w x) (point-p))))
		   (:instance acl2-nump-rot (w w) (name '$arg1) (x x))
		   (:instance sqrt-2-lemmas)
		   (:instance len-lemma (w w))
		   (:instance n-f-a-r-lemma (w w) (x (acl2-sqrt 2)))
		   (:instance n-f (w w) (x x))
		   (:instance n-f (w (cons (wa) w)) (x x))
		   (:instance associativity-of-m-*
			      (m1 (a-rotation x))
			      (m2 (rotation w x))
			      (m3 (point-p)))
		   (:instance expt-lemma (n (len w)))
		   )
	     :in-theory (disable aref2 rotation a-rotation b-rotation m-* a-inv-rotation b-inv-rotation point-p acl2-sqrt rotation reducedwordp)
	     :do-not-induct t
	     )

	    ("Subgoal 4"
	     :use (
		   (:instance sub4-lemma0)
		   (:instance sub4-lemma1)
		   (:instance sub4-lemma2)
		   )
	     )

	    ("Subgoal 2"
	     :use (
		   (:instance sub2-lemma
			      (x (AREF2 '$ARG1
					(M-* (ROTATION W (ACL2-SQRT 2))
					     '((:HEADER :DIMENSIONS (3 1)
							:MAXIMUM-LENGTH 15)
					       ((0 . 0) . 0)
					       ((1 . 0) . 1)
					       ((2 . 0) . 0)))
					1 0))
			      (y (AREF2 '$ARG1
					(M-* (ROTATION W (ACL2-SQRT 2))
					     '((:HEADER :DIMENSIONS (3 1)
							:MAXIMUM-LENGTH 15)
					       ((0 . 0) . 0)
					       ((1 . 0) . 1)
					       ((2 . 0) . 0)))
					2 0))
			      (z (AREF2 '$ARG1
					(M-* (A-ROTATION (ACL2-SQRT 2))
					     (ROTATION W (ACL2-SQRT 2))
					     '((:HEADER :DIMENSIONS (3 1)
							:MAXIMUM-LENGTH 15)
					       ((0 . 0) . 0)
					       ((1 . 0) . 1)
					       ((2 . 0) . 0)))
					1 0))
			      
			      )

		    )
	     )
	    
	    )
    )
  )

(defun n-mod3 (w x)
  (cons (mod (car (n-f w x)) 3) (cons (mod (car (cdr (n-f w x))) 3) (cons (mod (car (cdr (cdr (n-f w x) )))  3) nil)))
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
  (defthmd n-mod3-a-r-lemma1-2
    (equal (mod 0 3)
	   0)
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
    (implies (and (reducedwordp w)
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
		   (:instance n-f (w (cons (wa) w)) (x x)))
	     :in-theory (disable int-point acl2-sqrt rotation reducedwordp)
	     ))
    )
  )

 (local
  (defthmd n-mod3-a-r-lemma1
    (implies (and (reducedwordp w)
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
	     :in-theory (disable int-point rotation reducedwordp acl2-sqrt n-f)
	     :do-not-induct t
	     )	   
	    )
    )
  )
 )

 (defthmd n-mod3-a-r
   (implies (and (reducedwordp w)
		 (equal x (acl2-sqrt 2)))
	    (equal (n-mod3 (cons (wa) w) x)
		   (cons 0 (cons (mod (- (car (cdr (n-mod3 w x)))  (car (cdr (cdr (n-mod3 w x))))) 3)
				 (cons (mod (- (car (cdr (cdr (n-mod3 w x)))) (car (cdr (n-mod3 w x)))) 3) nil)))

		   )
	    )
   :hints (("Goal"
	    :use (
		  (:instance n-f-a-r (w w) (x x))
		  (:instance N (w (cons (wa) w)) (x x))
		  (:instance N (w w) (x x))
		  (:instance n-f (w w) (x x))
		  (:instance n-f (w w))
					;(:instance N (w (cons (wa) w)) (x x))
		  (:instance rotation-values (w w) (x x))
		  (:instance N-a-r-lemma0 (a 0) (c (car (n-f w x))))
		  (:instance N-a-r-lemma0
			     (a (- (car (cdr (n-f w x)))  (car (cdr (cdr (n-f w x))))))
			     (c (* (- (car (cdr (cdr (n-f w x))))))))
		  (:instance N-a-r-lemma0
			     (a (- (car (cdr (cdr (n-f w x)))) (car (cdr (n-f w x)))))
			     (c (car (cdr (n-f w x))))
			     )
		  (:instance mod--
			     (x (cadr (n-f w x)))
			     (y (caddr (n-f w x)))
			     (z 3))

		  (:instance mod--
			     (y (cadr (n-f w x)))
			     (x (caddr (n-f w x)))
			     (z 3))
		  
		  )
	    ))
   
   )
 )
 
 
 ;; (defthmd N-a-r
 ;;   (implies (and (reducedwordp w)
 ;; 		 (equal x (acl2-sqrt 2)))
 ;; 	    (equal (N (cons (wa) w) x)
 ;; 		   (cons 0 (cons (mod (- (car (cdr (N w x)))  (car (cdr (cdr (N w x))))) 3)
 ;; 				 (cons (mod (- (car (cdr (cdr (N w x)))) (car (cdr (N w x)))) 3) nil)))

 ;; 		   )
 ;; 	    )
 ;;   :hints (("Goal"
 ;; 	    :use (
 ;; 		  (:instance n-f-a-r (w w) (x x))
 ;; 		  (:instance N (w (cons (wa) w)) (x x))
 ;; 		  (:instance N (w w) (x x))
 ;; 		  (:instance n-f (w w) (x x))
 ;; 		  (:instance n-f (w w))
 ;; 					;(:instance N (w (cons (wa) w)) (x x))
 ;; 		  (:instance rotation-values (w w) (x x))
 ;; 		  (:instance N-a-r-lemma0 (a 0) (c (car (n-f w x))))
 ;; 		  (:instance N-a-r-lemma0
 ;; 			     (a (- (car (cdr (n-f w x)))  (car (cdr (cdr (n-f w x))))))
 ;; 			     (c (* (- (car (cdr (cdr (n-f w x))))))))
 ;; 		  (:instance N-a-r-lemma0
 ;; 			     (a (- (car (cdr (cdr (n-f w x)))) (car (cdr (n-f w x)))))
 ;; 			     (c (car (cdr (n-f w x))))
 ;; 			     )
 ;; 		  (:instance mod--
 ;; 			     (x (cadr (n-f w x)))
 ;; 			     (y (caddr (n-f w x)))
 ;; 			     (z 3))

 ;; 		  (:instance mod--
 ;; 			     (y (cadr (n-f w x)))
 ;; 			     (x (caddr (n-f w x)))
 ;; 			     (z 3))
		  
 ;; 		  )
 ;; 	    ))
   
 ;;   )
 ;; )
