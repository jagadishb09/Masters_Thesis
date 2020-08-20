(include-book "std/typed-lists/character-listp" :dir :system)
(include-book "std/lists/top" :dir :system)

(defun wa()
  #\a
  )

(defun wa-inv()
  #\b
  )

(defun wb()
  #\c
  )

(defun wb-inv()
  #\d
  )


(defthmd abcd-chars
  (and (characterp (wa))
       (characterp (wa-inv))
       (characterp (wb))
       (characterp (wb-inv)))
  )

(defun weak-wordp (w)
  (cond ((atom w) (equal w nil))
	(t (and (or (equal (car w) (wa))
		    (equal (car w) (wa-inv))
		    (equal (car w) (wb))
		    (equal (car w) (wb-inv)))
		(weak-wordp (cdr w))))))


(defun wordp(w letter)
  (cond ((atom w) (equal w nil))
	((equal letter (wa)) (let ((firstw (car w)) (restw (cdr w)))
			       (and (or (equal firstw (wa))
					(equal firstw (wb))
					(equal firstw (wb-inv)))
				    (wordp restw firstw))))
	((equal letter (wa-inv)) (let ((firstw (car w)) (restw (cdr w)))
				   (and (or (equal firstw (wa-inv))
					    (equal firstw (wb))
					    (equal firstw (wb-inv)))
					(wordp restw firstw))))

	((equal letter (wb)) (let ((firstw (car w)) (restw (cdr w)))
			       (and (or (equal firstw (wa))
					(equal firstw (wa-inv))
					(equal firstw (wb)))
				    (wordp restw firstw))))
	((equal letter (wb-inv)) (let ((firstw (car w)) (restw (cdr w)))
				   (and (or (equal firstw (wa))
					    (equal firstw (wa-inv))
					    (equal firstw (wb-inv)))
					(wordp restw firstw))))))


(defun a-wordp(w)
  (and (equal (car w) (wa))
       (wordp (cdr w) (wa))))

(defun b-wordp(w)
  (and (equal (car w) (wb))
       (wordp (cdr w) (wb))))

(defun a-inv-wordp(w)
  (and (equal (car w) (wa-inv))
       (wordp (cdr w) (wa-inv))))

(defun b-inv-wordp(w)
  (and (equal (car w) (wb-inv))
       (wordp (cdr w) (wb-inv))))

(defthmd a-wordp-equivalent
  (implies (a-wordp a)
	   (and (not (a-inv-wordp a))
		(not (b-wordp a))
		(not (b-inv-wordp a))
		(not (equal a '()))))
  )

(defthmd b-wordp-equivalent
  (implies (b-wordp b)
	   (and (not (a-inv-wordp b))
		(not (a-wordp b))
		(not (b-inv-wordp b))
		(not (equal b '()))))
  )

(defthmd a-inv-wordp-equivalent
  (implies (a-inv-wordp a-inv)
	   (and (not (a-wordp a-inv))
		(not (b-wordp a-inv))
		(not (b-inv-wordp a-inv))
		(not (equal a-inv '()))))
  )

(defthmd b-inv-wordp-equivalent
  (implies (b-inv-wordp b-inv)
	   (and (not (b-wordp b-inv))
		(not (a-wordp b-inv))
		(not (a-inv-wordp b-inv))
		(not (equal b-inv '()))))
  )

(defun word-fix (w)
  (if (atom w)
      nil
    (let ((fixword (word-fix (cdr w))))
      (let ((w (cons (car w) fixword)))
	(cond ((equal fixword nil)
	       (list (car w)))
	      ((equal (car (cdr w)) (wa))
	       (if (equal (car w) (wa-inv))
		   (cdr (cdr w))
		 w))
	      ((equal (car (cdr w)) (wa-inv))
	       (if (equal (car w) (wa))
		   (cdr (cdr w))
		 w))
	      ((equal (car (cdr w)) (wb))
	       (if (equal (car w) (wb-inv))
		   (cdr (cdr w))
		 w))
	      ((equal (car (cdr w)) (wb-inv))
	       (if (equal (car w) (wb))
		   (cdr (cdr w))
		 w)))))))




(defun compose (x y)
  (word-fix (append x y))
  )

(defun reducedwordp (x)
  (or (a-wordp x)
      (a-inv-wordp x)
      (b-wordp x)
      (b-inv-wordp x)
      (equal x '()))
  )

(defthmd weak-wordp-equivalent
  (implies (weak-wordp x)
	   (reducedwordp (word-fix x))))

(encapsulate
 ()

 (local
  (defthm lemma
    (implies (or (a-wordp x)
		 (a-inv-wordp x)
		 (b-wordp x)
		 (b-inv-wordp x)
		 (equal x '()))
	     (weak-wordp x))))

 (defthmd a-wordp=>weak-wordp
   (IMPLIES (a-wordp x)
	    (weak-wordp x)))

 (defthmd b-wordp=>weak-wordp
   (IMPLIES (b-wordp x)
	    (weak-wordp x)))

 (defthmd b-inv-wordp=>weak-wordp
   (IMPLIES (b-inv-wordp x)
	    (weak-wordp x)))

 (defthmd a-inv-wordp=>weak-wordp
   (IMPLIES (a-inv-wordp x)
	    (weak-wordp x)))

 (defthmd reducedwordp=>weak-wordp
   (IMPLIES (reducedwordp x)
	    (weak-wordp x)))
 
 )

(encapsulate
 ()

 (local
  (defthm lemma
    (implies (or (a-wordp x)
		 (a-inv-wordp x)
		 (b-wordp x)
		 (b-inv-wordp x)
		 (equal x '()))
	     (equal (word-fix x) x))))


 (defthmd word-fix=a-wordp
   (IMPLIES (a-wordp x)
	    (equal (word-fix x) x))
   )

 (defthmd word-fix=a-inv-wordp
   (IMPLIES (a-inv-wordp x)
	    (equal (word-fix x) x))
   )

 (defthmd word-fix=b-wordp
   (IMPLIES (b-wordp x)
	    (equal (word-fix x) x))
   )

 (defthmd word-fix=b-inv-wordp
   (IMPLIES (b-inv-wordp x)
	    (equal (word-fix x) x))
   )

 (defthmd word-fix=reducedwordp
   (implies (reducedwordp x)
	    (equal (word-fix x) x))
   )

 (defthmd word-fix=reducedwordp-1
   (implies (and (weak-wordp x)
		 (equal (word-fix x) x))
	    (reducedwordp x))
   :hints (("Goal"
	    :use (:instance weak-wordp-equivalent (x x))
	    ))
   )
 )


(defthmd weak-word-cdr
  (implies (weak-wordp x)
	   (weak-wordp (cdr x)))
  )

(defthmd character-listp-word
  (implies (or (reducedwordp x)
	       (weak-wordp x))
	   (character-listp x))
  )

(defthmd reduced-cdr
  (implies (reducedwordp x)
	   (reducedwordp (cdr x)))
  )


;;;;;;;;;;;;closure property


(defthmd closure-weak-word
  (implies (and (weak-wordp x)
		(weak-wordp y))
	   (weak-wordp (append x y)))
  )


(defthmd closure-lemma
  (implies (and (reducedwordp x)
		(reducedwordp y))
	   (weak-wordp (append x y)))
  :hints (("Goal"
	   :use ((:instance a-wordp=>weak-wordp (x x))
		 (:instance b-wordp=>weak-wordp (x x))
		 (:instance a-inv-wordp=>weak-wordp (x x))
		 (:instance b-inv-wordp=>weak-wordp (x x))
		 (:instance a-wordp=>weak-wordp (x y))
		 (:instance b-wordp=>weak-wordp (x y))
		 (:instance a-inv-wordp=>weak-wordp (x y))
		 (:instance b-inv-wordp=>weak-wordp (x y))
		 (:instance closure-weak-word)
		 )
	   ))
  )

(defthmd closure-prop
  (implies (and (reducedwordp x)
		(reducedwordp y))
	   (reducedwordp (compose x y))
	   )
  :hints (("Goal"
	   :use ((:instance closure-lemma (x x) (y y))
		 (:instance weak-wordp-equivalent (x (append x y)))
		 )
	   ))
  )

;;;;;;;;associative property;;;;

(encapsulate
 ()

 (local
  (defthm weak-wordp-equivalent-assoc
    (implies (weak-wordp x)
	     (reducedwordp (word-fix x))))
  )

 (local
  (defthm reducedwordp=>weak-wordp-assoc
    (IMPLIES (reducedwordp x)
	     (weak-wordp x)))
  )
 

 (local
  (defthm word-fix=reducedwordp-assoc
    (implies (reducedwordp x)
	     (equal (word-fix x) x))
    )
  )

 (local
  (defthm word-fix=reducedwordp-1-assoc
    (implies (and (weak-wordp x)
		  (equal (word-fix x) x))
	     (reducedwordp x))
    :hints (("Goal"
	     :use (:instance weak-wordp-equivalent (x x))
	     ))
    )
  )
 
 (local
  (defthm weak-word-cdr-assoc
    (implies (weak-wordp x)
	     (weak-wordp (cdr x)))
    )
  )

 (local
  (defthm character-listp-word-assoc
    (implies (or (reducedwordp x)
		 (weak-wordp x))
	     (character-listp x))
    )
  )
 

 (local
  (defthm reduced-cdr-assoc
    (implies (reducedwordp x)
	     (reducedwordp (cdr x)))
    )
  )

 (local
  (defthm closure-weak-word-assoc
    (implies (and (weak-wordp x)
		  (weak-wordp y))
	     (weak-wordp (append x y)))
    )
  )

 (local
  (defthm closure-lemma-assoc
    (implies (and (reducedwordp x)
		  (reducedwordp y))
	     (weak-wordp (append x y)))
    :hints (("Goal"
	     :use ((:instance a-wordp=>weak-wordp (x x))
		   (:instance b-wordp=>weak-wordp (x x))
		   (:instance a-inv-wordp=>weak-wordp (x x))
		   (:instance b-inv-wordp=>weak-wordp (x x))
		   (:instance a-wordp=>weak-wordp (x y))
		   (:instance b-wordp=>weak-wordp (x y))
		   (:instance a-inv-wordp=>weak-wordp (x y))
		   (:instance b-inv-wordp=>weak-wordp (x y))
		   (:instance closure-weak-word)
		   )
	     ))
    )
  )


 (local
  (defthm closure-prop-assoc
    (implies (and (reducedwordp x)
		  (reducedwordp y))
	     (reducedwordp (compose x y))
	     )
    :hints (("Goal"
	     :use ((:instance closure-lemma (x x) (y y))
		   (:instance weak-wordp-equivalent (x (append x y)))
		   )
	     ))
    )
  )

 (local
  (defthm wordfix-wordfix
    (implies (weak-wordp x)
	     (equal (word-fix (word-fix x)) (word-fix x)))
    )
  )

 (local
  (defthm append-nil-assoc                   
    (implies (character-listp x)             
	     (equal (append x nil) x))
    :rule-classes ((:rewrite 
		    :backchain-limit-lst (3)
		    :match-free :all)))
  )

 (local
  (defthm append-lemma                   
    (implies (and (reducedwordp x)
		  (reducedwordp y)
		  (reducedwordp z))
	     (equal (append x (append y z)) (append x y z))
	     )
    :rule-classes nil
    )
  )

 (local
  (defthm weak-word-=
    (implies (weak-wordp x)
	     (or (equal x '())
		 (and (equal (car x) (wa)) (weak-wordp (cdr x)))
		 (and (equal (car x) (wa-inv)) (weak-wordp (cdr x)))
		 (and (equal (car x) (wb)) (weak-wordp (cdr x)))
		 (and (equal (car x) (wb-inv)) (weak-wordp (cdr x)))
		 ))
    )
  )
 

 (local
  (defthm weak-wordp-rev
    (implies (weak-wordp x)
	     (weak-wordp (rev x)))
    )
  )
 

 (local
  (defthm compose-assoc-lemma
    (implies (and (weak-wordp x)
		  (weak-wordp y))
	     (equal (word-fix (append x (word-fix y))) (word-fix (append x y)))
	     )
    :hints (("Goal"
	     :use ((:instance weak-wordp-equivalent-assoc (x x))
		   (:instance weak-wordp-equivalent-assoc (x y))
		   (:instance reducedwordp=>weak-wordp-assoc (x (word-fix x)))
		   (:instance reducedwordp=>weak-wordp-assoc (x (word-fix y)))
		   (:instance word-fix (w (append x (word-fix y))))
		   (:instance word-fix (w (word-fix (append x y))))
		   )
	     :in-theory (enable word-fix append)
	     ))
    )
  )

 (local
  (defthm compose-assoc-lemma1
    (implies (and (weak-wordp x)
		  (weak-wordp y)
		  (weak-wordp z))
	     (equal (word-fix (append x (word-fix (append y z)))) (word-fix (append x y z)))
	     )
    :hints (("Goal"
	     :use ((:instance compose-assoc-lemma (x (append y z)))
		   (:instance closure-weak-word-assoc (x y) (y z))
		   )
	     :in-theory (enable word-fix append)
	     ))
    )
  )

 (encapsulate
  ()

  (local
   (defthmd lemma1
     (implies (character-listp x)
	      (equal (append (rev (cdr (rev x))) (last x))
		     x))
     :hints (("Goal"
	      :in-theory (enable rev)
	      ))
     )
   )

  (local
   (defthmd lemma2
     (implies (and (listp x)
		   (listp y)
		   (listp z))
	      (equal (append x y z)
		     (append (append x y) z))
	      )
     )
   )
  

  (local
   (defthmd lemma3
     (implies (and (character-listp x)
		   x)
	      (and (equal (list (car (last x))) (last x))
		   (listp (rev (cdr (rev x))))
		   (listp (list (car (last x))))
		   (listp (last x))
		   (character-listp (list (car x)))))
     :hints (("Goal"
	      :in-theory (enable last car character-listp rev)
	      ))
     )
   )

  (local
   (defthmd lemma4
     (implies (and (weak-wordp x)
		   x)
	      (weak-wordp (last x)))
     )
   )
  
  (local
   (defthmd word-fix-rev-lemma1
     (implies (and (weak-wordp x)
		   (reducedwordp (append x (list y)))
		   (characterp z)
		   (weak-wordp (list z)))
	      (equal (word-fix (append x (list y) (list z)))
		     (append x (word-fix (append (list y) (list z))))))
     )
   )

  (local
   (defthmd word-fix-rev-lemma2
     (implies (and (reducedwordp x)
		   (characterp y)
		   (reducedwordp x)
		   (weak-wordp (list y)))
	      (equal (word-fix (append x (list y)))
		     (append (rev (cdr (rev x))) (word-fix (append (last x) (list y))))))
     :hints (("Goal"
	      :cases ((not x)
		      x)
	      :do-not-induct t
	      )

	     ("Subgoal 1"
	      :use (
		    (:instance character-listp-word-assoc (x x))
		    (:instance reducedwordp=>weak-wordp (x x))
		    (:instance weak-wordp-rev (x x))
		    (:instance weak-word-cdr (x (rev x)))
		    (:instance weak-wordp-rev (x (cdr (rev x))))
		    (:instance character-listp-word-assoc (x (rev (cdr (rev x)))))
		    (:instance lemma3 (x x))
		    (:instance word-fix-rev-lemma1
			       (x (rev (cdr (rev x))))
			       (y (car (last x)))
			       (z y))
		    (:instance lemma1 (x x))
		    (:instance lemma2
			       (x (rev (cdr (rev x))))
			       (y (last x))
			       (z (list y)))
		    )
	      :do-not-induct t
	      :in-theory nil
	      )	   
	     )   
     )
   )

  (local
   (defthmd lemma11
     (implies (weak-wordp x)
	      (if x (and (weak-wordp (list (car x)))
			 (weak-wordp (last x)))
		(weak-wordp (last x)))
	      )
     )
   )
  
  (local
   (skip-proofs
    (defthmd word-fix-rev-lemma3-1
      (implies (and (characterp x)
		    (weak-wordp (list x))
		    (reducedwordp y)
		    (characterp z)
		    (weak-wordp (list z)))
	       (equal (word-fix (append (list (car x)) y (list z)))
		      (word-fix (append (word-fix (append (list (car x)) y)) (list z)))))
      :hints (("Goal"
	       :in-theory (enable append)
	       ))
      )
    )
   )

  (local
   (defthmd lemma-13
     (implies (and (character-listp x)
		   x
		   (characterp y))
	      (equal (append x (list y))
		     (append (list (car x)) (cdr x) (list y))))
     :hints (("Goal"
	      :in-theory (enable append)
	      ))
     )
   )
  

  (local
   (skip-proofs
    (defthmd word-fix-rev-lemma3-induct
      (implies (and (not (atom x))
		    (implies (and (weak-wordp (cdr x))
				  (characterp y)
				  (weak-wordp (list y)))
			     (equal (word-fix (append (cdr x) (list y)))
				    (word-fix (append (word-fix (cdr x)) (list y))))))
	       (implies (and (weak-wordp x)
			     (characterp y)
			     (weak-wordp (list y)))
			(equal (word-fix (append x (list y)))
			       (word-fix (append (word-fix x) (list y)))))
	       )
      )
    )
   )
	       

  (local
   ;(skip-proofs
    (defthmd word-fix-rev-lemma3
      (implies (and (weak-wordp x)
		    (characterp y)
		    (weak-wordp (list y)))
	       (equal (word-fix (append x (list y)))
		      (word-fix (append (word-fix x) (list y)))))

      :hints (("Goal"
	       :cases ((not x)
		       x)

	       )
	      ("Subgoal *1/11"
	       :use ((:instance lemma-13 (x x))
		     (:instance character-listp-word-assoc (x x))
		     (:instance compose-assoc-lemma1
				(x (list (car x)))
				(y (cdr x))
				(z (list y)))
		     (:instance compose-assoc-lemma
				(x (list (car x)))
				(y (append (word-fix (cdr x)) (list y))))
		     (:instance weak-word-cdr (x x))
		     (:instance weak-wordp-equivalent-assoc (x (cdr x)))
		     (:instance word-fix-rev-lemma3-1
				(x (car x))
				(y (word-fix (cdr x)))
				(z y))
		     )
	       )
	      
	      ("Subgoal *1/9"
	       :use ((:instance word-fix-rev-lemma3-induct (x x))
		     )
	       )

	      ("Subgoal *1/8"
	       :use ((:instance word-fix-rev-lemma3-induct (x x))
		     )
	       )

	      ("Subgoal *1/7"
	       :use ((:instance word-fix-rev-lemma3-induct (x x))
		     )
	       )

	      ("Subgoal *1/6"
	       :use ((:instance word-fix-rev-lemma3-induct (x x))
		     )
	       )

	      ("Subgoal *1/5"
	       :use ((:instance word-fix-rev-lemma3-induct (x x))
		     )
	       )

	      ("Subgoal *1/4"
	       :use ((:instance word-fix-rev-lemma3-induct (x x))
		     )
	       )

	      ("Subgoal *1/3"
	       :use ((:instance word-fix-rev-lemma3-induct (x x))
		     )
	       )

	      ("Subgoal *1/2"
	       :use ((:instance word-fix-rev-lemma3-induct (x x))
		     )
	       )
	      
	      )
      )
   ; )
   )

  
  (local
   (defthmd word-fix-rev-lemma4
     (implies (weak-wordp x)
	      (equal (word-fix x)
		     (append (rev (cdr (rev (word-fix (rev (cdr (rev x)))))))
			     (word-fix (append (last (word-fix (rev (cdr (rev x)))))
					       (last x))))))
     :hints (("Goal"
	      :cases ((not x)
		      x)
	      :do-not-induct t
	      )
	     ("Subgoal 1"
	      :use ((:instance lemma1 (x x))
		    (:instance character-listp-word-assoc (x x))
		    (:instance weak-wordp-rev (x x))
		    (:instance weak-word-cdr (x (rev x)))
		    (:instance weak-wordp-rev (x (cdr (rev x))))
		    (:instance lemma3 (x x))
		    (:instance word-fix-rev-lemma3 (x (rev (cdr (rev x)))) (y (car (last x))))
		    (:instance weak-wordp-equivalent-assoc (x (rev (cdr (rev x)))))
		    (:instance word-fix-rev-lemma2
			       (x (word-fix (rev (cdr (rev x)))))
			       (y (car (last x))))
		    (:instance word-fix (w (APPEND (REV (CDR (REV X))) (LAST X))))
		    (:instance lemma4 (x x))
		    )
	      )
	     )
     )
   )

  (local
   (defthmd lemma5
     (implies (character-listp x)
	      (equal (rev (rev x)) x))
     )
   )

  (local
   (defthmd lemma6
     (implies (and (character-listp x)
		   x)
	      (equal (last (rev x)) (list (car x))))
     :hints (("Goal"
	      :in-theory (enable rev)
	      ))
     )
   )

  (local
   (defthmd lemma7
     (implies (and (character-listp x)
		   (character-listp y))
	      (equal (rev (append x y))
		     (append (rev y) (rev x))))
     
     )
   )

  (local
   (defthmd lemma8
     (implies (and (weak-wordp x)
		   (<= (len x) 1))
	      (or (equal x nil)
		  (equal x '(#\a))
		  (equal x '(#\b))
		  (equal x '(#\c))
		  (equal x '(#\d))))
     )
   )

  (local
   (defthmd lemma9
     (implies (and 
	       (weak-wordp x)
	       (weak-wordp y)
	       (<= (len x) 1)
	       (<= (len y) 1))
	      (equal (rev (word-fix (append x y)))
		     (word-fix (append y x))))
     :hints (("Goal"

	      :use ((:instance lemma8 (x x))
		    (:instance lemma8 (x y)))
	      
	      :cases (
		      (and (atom x) (atom y))
		      (and (equal x '(#\a)) (equal y '(#\a)))
		      (and (equal x '(#\a)) (equal y '(#\b)))
		      (and (equal x '(#\a)) (equal y '(#\c)))
		      (and (equal x '(#\a)) (equal y '(#\d)))
		      (and (equal x '(#\b)) (equal y '(#\a)))
		      (and (equal x '(#\b)) (equal y '(#\b)))
		      (and (equal x '(#\b)) (equal y '(#\c)))
		      (and (equal x '(#\b)) (equal y '(#\d)))
		      (and (equal x '(#\c)) (equal y '(#\a)))
		      (and (equal x '(#\c)) (equal y '(#\b)))
		      (and (equal x '(#\c)) (equal y '(#\c)))
		      (and (equal x '(#\c)) (equal y '(#\d)))
		      (and (equal x '(#\d)) (equal y '(#\a)))
		      (and (equal x '(#\d)) (equal y '(#\b)))
		      (and (equal x '(#\d)) (equal y '(#\c)))
		      (and (equal x '(#\d)) (equal y '(#\d)))
		      (and (atom x) (equal y '(#\a)))
		      (and (atom x) (equal y '(#\b)))
		      (and (atom x) (equal y '(#\c)))
		      (and (atom x) (equal y '(#\d)))
		      (and (equal x '(#\d)) (atom y))
		      (and (equal x '(#\d)) (atom y))
		      (and (equal x '(#\d)) (atom y))
		      (and (equal x '(#\d)) (atom y))		      
		      )
	      :in-theory (enable append rev)
	      )
	     )
     )
   )

  (local
   (defthmd lemma10
     (implies (and (characterp x)
		   (weak-wordp (list x))
		   (reducedwordp y)
		   (not (atom y)))
	      (equal (word-fix (append (list x) y))
		     (append (word-fix (append (list x) (list (car y)))) (cdr y)))
	      )
     :hints (("Goal"
	      :use ((:instance reduced-cdr-assoc (x y))
		    (:instance word-fix=reducedwordp-assoc (x (cdr x)))
		    )
	      ))
     )
   )

  (local
   (defthm lemma12
     (implies (and (weak-wordp x)
		   (word-fix (cdr x))
		   x)
	      (equal (word-fix x)
		     (append (word-fix (append (list (car x)) (list (car (word-fix (cdr x))))))
			     (cdr (word-fix (cdr x))))))
     :hints (("Goal"
	      :use ((:instance compose-assoc-lemma (x (list (car x))) (y (cdr x)))
		    (:instance lemma10 (x (car x)) (y (word-fix (cdr x))))
		    (:instance weak-word-cdr (x x))
		    (:instance lemma11 (x x))
		    (:instance weak-wordp-equivalent-assoc (x (word-fix (cdr x)))))
					;:in-theory nil
	      :do-not-induct t
	      ))
     )
   )

  (local
   (defthmd word-fix-lemma2
     (implies (and (weak-wordp x)
		   (not (atom x))
		   (EQUAL (WORD-FIX (REV (CDR X)))
			  (REV (WORD-FIX (CDR X))))
		   )
	      (equal (word-fix (rev x))
		     (append (rev (cdr (word-fix (cdr x))))
			     (word-fix (append (last (rev (word-fix (cdr x))))
					       (list (car x)))))))
     :hints (("Goal"
	      :cases ((not x)
		      x))
	     ("Subgoal 1"
	      :use ((:instance weak-wordp-rev (x x))
		    (:instance word-fix-rev-lemma4 (x (rev x)))
		    (:instance lemma5 (x x))
		    (:instance weak-word-cdr (x x))
		    (:instance weak-wordp-equivalent-assoc (x x))
		    (:instance weak-wordp-equivalent-assoc (x (cdr x)))
		    (:instance character-listp-word-assoc (x x))
		    (:instance character-listp-word-assoc (x (word-fix (cdr x))))
		    (:instance lemma5 (x (word-fix (cdr x))))
		    (:instance lemma6 (x x))
		    
		    
		    )
	      :in-theory nil
	      :do-not-induct t
	      ))
     )
   )

  (local
   (defthmd word-fix-lemma1
     (implies (and (weak-wordp x)
		   (not (atom x))
		   (EQUAL (WORD-FIX (REV (CDR X)))
			  (REV (WORD-FIX (CDR X))))
		   )
	      (equal (word-fix (rev x)) (rev (word-fix x))))
     :hints (("Goal"
	      :cases ((not x)
		      x)
	      :do-not-induct t
	      )
	     ("Subgoal 1"
	      :cases ((not (word-fix (cdr x)))
		      (word-fix (cdr x)))
	      :use (
		    (:instance lemma5 (x (word-fix (append (last (rev (word-fix (cdr x))))
							   (list (car x))))))
		    (:instance word-fix-lemma2 (x x))
		    (:instance lemma7 
			       (x (rev (word-fix (append (last (rev (word-fix (cdr x))))
							 (list (car x))))))
			       (y (cdr (fix (cdr x)))))
		    (:instance lemma9
			       (x (last (rev (word-fix (cdr x)))))
			       (y (list (car x))))
		    (:instance lemma12 (x x))
		    (:instance lemma11 (x x))
		    (:instance weak-word-cdr (x x))
		    (:instance weak-wordp-equivalent-assoc (x (cdr x)))
		    (:instance reducedwordp=>weak-wordp-assoc (x (cdr x)))
		    (:instance weak-wordp-rev (x (word-fix (cdr x))))
		    (:instance character-listp-word-assoc (x x))
		    (:instance lemma11 (x (rev (word-fix (cdr x)))))
		    (:instance closure-weak-word-assoc
			       (x (last (rev (word-fix (cdr x)))))
			       (y (list (car x))))
		    (:instance weak-wordp-equivalent-assoc
			       (x (append (last (rev (word-fix (cdr x))))
					  (list (car x)))))
		    (:instance character-listp-word-assoc
			       (x (word-fix (append (last (rev (word-fix (cdr x))))
						    (list (car x))))))
		    )
	      :in-theory (enable append)
	      
	      )
	     )								    
     )
   )
  
  
  (defthmd word-fix-rev-lemma
    (implies (weak-wordp x)
	     (equal (word-fix (rev x)) (rev (word-fix x))))

    :hints (
	    ("Subgoal *1/21"
	     :use (:instance word-fix-lemma1 (x x))
	     )
	    ("Subgoal *1/20"
	     :use (:instance word-fix-lemma1 (x x))
	     )
	    ("Subgoal *1/19"
	     :use (:instance word-fix-lemma1 (x x))
	     )
	    ("Subgoal *1/18"
	     :use (:instance word-fix-lemma1 (x x))
	     )
	    ("Subgoal *1/17"
	     :use (:instance word-fix-lemma1 (x x))
	     )
	    ("Subgoal *1/16"
	     :use (:instance word-fix-lemma1 (x x))
	     )
	    ("Subgoal *1/15"
	     :use (:instance word-fix-lemma1 (x x))
	     )
	    ("Subgoal *1/14"
	     :use (:instance word-fix-lemma1 (x x))
	     )
	    ("Subgoal *1/13"
	     :use (:instance word-fix-lemma1 (x x))
	     )
	    ("Subgoal *1/12"
	     :use (:instance word-fix-lemma1 (x x))
	     )
	    ("Subgoal *1/11"
	     :use (:instance word-fix-lemma1 (x x))
	     )

	    ("Subgoal *1/10"
	     :use (:instance word-fix-lemma1 (x x))
	     )

	    ("Subgoal *1/9"
	     :use (:instance word-fix-lemma1 (x x))
	     )

	    ("Subgoal *1/8"
	     :use (:instance word-fix-lemma1 (x x))
	     )

	    ("Subgoal *1/7"
	     :use (:instance word-fix-lemma1 (x x))
	     )

	    ("Subgoal *1/6"
	     :use (:instance word-fix-lemma1 (x x))
	     )

	    ("Subgoal *1/5"
	     :use (:instance word-fix-lemma1 (x x))
	     )

	    ("Subgoal *1/4"
	     :use (:instance word-fix-lemma1 (x x))
	     )

	    ("Subgoal *1/3"
	     :use (:instance word-fix-lemma1 (x x))
	     )

	    ("Subgoal *1/2"
	     :use (:instance word-fix-lemma1 (x x))
	     )
	    )
    
    )
  )

 (defthmd assoc-prop
   (implies (and (reducedwordp x)
		 (reducedwordp y)
		 (reducedwordp z))
	    (equal (compose (compose x y) z) (compose x (compose y z))))

   :hints (("Goal"
	    :use ((:instance rev-of-rev (x (word-fix (append (word-fix (append x y)) z))))
		  (:instance word-fix-rev-lemma (x (append (word-fix (append x y)) z)))
		  (:instance word-fix-rev-lemma (x (append x y)))
		  (:instance compose-assoc-lemma1 (x (rev z)) (y (rev y)) (z (rev x)))
		  (:instance word-fix-rev-lemma (x (append (rev z) (rev y) (rev x)))))
	    :do-not-induct t
	    ))
   
   )
 )

;;;;;;;;;;;;;inverse exists;;;;;;

(defthmd basecase
  (IMPLIES (ATOM X)
	   (IMPLIES (AND (WEAK-WORDP X)
			 (EQUAL (WORD-FIX X) X))
		    (EQUAL (WORD-FIX (REV X))
			   (REV X))))
  )

(encapsulate
 ()
 (local 
  (defthm weak-word-cdr
    (implies (weak-wordp x)
	     (weak-wordp (cdr x)))
    )  
  )

 (local 
  (defthm reducedword-cdr
    (implies (reducedwordp x)
	     (reducedwordp (cdr x)))
    )  
  )

 (local
  (defthm word-fix-cdr
    (implies (and (weak-wordp x)
		  (equal (word-fix x) x))
	     (equal (word-fix (cdr x)) (cdr x)))
    :hints (("Goal"
	     :use ((:instance word-fix=reducedwordp-1 (x x))
		   (:instance reducedword-cdr (x x))
		   (:instance word-fix=reducedwordp (x (cdr x))))
	     
	     ))
    )
  )

 (local 
  (defthm weak-wordp-rev
    (implies (weak-wordp x)
	     (weak-wordp (rev x)))
    )
  )

 (local
  (defthm word-fix-lemma1
    (implies (and 
	      (reducedwordp x)
	      (not (equal x '()))
	      (characterp y)
	      (weak-wordp (list y))
	      (cond ((equal (nth (- (len x) 1) x) (wa)) (not (equal y (wa-inv))))
		    ((equal (nth (- (len x) 1) x) (wb)) (not (equal y (wb-inv))))
		    ((equal (nth (- (len x) 1) x) (wb-inv)) (not (equal y (wb))))
		    ((equal (nth (- (len x) 1) x) (wa-inv)) (not (equal y (wa))))
		    )
	      )
	     (reducedwordp (append x (list y))))
    )
  )

 (local
  (defthm word-fix-lemma2
    (implies (and (weak-wordp x)
		  (equal (word-fix x) x)
		  (not (equal x '()))
		  (characterp y)
		  (weak-wordp (list y))
		  (cond ((equal (nth (- (len x) 1) x) (wa)) (not (equal y (wa-inv))))
			((equal (nth (- (len x) 1) x) (wb)) (not (equal y (wb-inv))))
			((equal (nth (- (len x) 1) x) (wb-inv)) (not (equal y (wb))))
			((equal (nth (- (len x) 1) x) (wa-inv)) (not (equal y (wa))))
			)
		  )
	     (equal (word-fix (append x (list y))) (append x (list y))))
    :hints (("Goal"
	     :use ((:instance word-fix-lemma1 (x x))
		   (:instance word-fix=reducedwordp-1 (x x))
		   (:instance word-fix=reducedwordp (x (append x (list y)))))
	     ))
    )
  )

 (local
  (defthm character-listp-word
    (implies (or (reducedwordp x)
		 (weak-wordp x))
	     (character-listp x))
    )
  )

 (local
  (defthm word-fix-lemma3
    (implies (and (weak-wordp x)
		  (not (atom x)))
	     (equal (append (rev (cdr x)) (list (car x))) (rev x)))
    :hints (("Goal"
	     :use (:instance character-listp-word (x x))
	     :in-theory (enable rev)
	     
	     ))
    )
  )

 (local
  (defthm word-fix-lemma5
    (implies (and (not (atom x))
		  (word-fix (cdr x)))
	     (and (cdr x)
		  (not (equal (rev (cdr x)) nil))
		  (not (atom (rev (cdr x))))))
    )
  )

 (local
  (defthm word-fix-lemma6
    (implies (and (not (atom x))
		  (weak-wordp x))
	     (and (characterp (car x))
		  (weak-wordp (list (car x)))))
    )
  )

 (local
  (defthm word-fix-lemma7
    (implies (and (not (atom x))
		  (not (atom (rev (cdr x))))
		  (reducedwordp x))
	     (cond ((equal (nth (- (len (rev (cdr x))) 1) (rev (cdr x))) (wa)) (not (equal (car x) (wa-inv))))
		   ((equal (nth (- (len (rev (cdr x))) 1) (rev (cdr x))) (wb)) (not (equal (car x) (wb-inv))))
		   ((equal (nth (- (len (rev (cdr x))) 1) (rev (cdr x))) (wb-inv)) (not (equal (car x) (wb))))
		   ((equal (nth (- (len (rev (cdr x))) 1) (rev (cdr x))) (wa-inv)) (not (equal (car x) (wa))))
		   )
	     )
    )
  )

 (defthmd word-fix-lemma
   (implies (and (not (atom x))
		 (word-fix (cdr x))
					;(cdr x)
		 (IMPLIES (AND (WEAK-WORDP (CDR X))
			       (EQUAL (WORD-FIX (CDR X)) (CDR X)))
			  (EQUAL (WORD-FIX (REV (CDR X)))
				 (REV (CDR X)))))
	    (IMPLIES (AND (WEAK-WORDP X)
			  (EQUAL (WORD-FIX X) X))
		     (EQUAL (WORD-FIX (REV X))
			    (REV X))))
   :hints (("Goal"
	    :use ((:instance weak-word-cdr (x x))
		  (:instance word-fix-cdr (x x))
		  (:instance weak-wordp-rev (x (cdr x)))
		  (:instance word-fix-lemma2 (x (rev (cdr x))) (y (car x)))
		  (:instance word-fix-lemma3 (x x))
		  (:instance word-fix-lemma5 (x x))
		  (:instance word-fix-lemma6 (x x))
		  (:instance word-fix=reducedwordp-1 (x x))
		  (:instance word-fix=reducedwordp-1 (x (cdr x)))
		  (:instance word-fix-lemma7 (x x)))
	    :in-theory nil
	    :do-not-induct t
	    ))
   )
 )

(defthmd word-fix-lemma-1
  (implies (and (weak-wordp x)
		(equal (word-fix x) x))
	   (equal (word-fix (rev x)) (rev x)))
  :hints (("Subgoal *1/10"
	   :use ((:instance word-fix-lemma))
	   )
	  ("Subgoal *1/9"
	   :use ((:instance word-fix-lemma))
	   )
	  ("Subgoal *1/8"
	   :use ((:instance word-fix-lemma))
	   )
	  ("Subgoal *1/7"
	   :use ((:instance word-fix-lemma))
	   )
	  ("Subgoal *1/6"
	   :use ((:instance word-fix-lemma))
	   )
	  ("Subgoal *1/5"
	   :use ((:instance word-fix-lemma))
	   )
	  ("Subgoal *1/4"
	   :use ((:instance word-fix-lemma))
	   )
	  ("Subgoal *1/3"
	   :use ((:instance word-fix-lemma))
	   )
	  ))


(defthmd weak-wordp-rev
  (implies (weak-wordp x)
	   (weak-wordp (rev x)))
  )



(defthmd rev-word-inv-reduced
  (implies (reducedwordp x)
	   (reducedwordp (rev x)))
  :hints (("Goal"
	   :use ((:instance reducedwordp=>weak-wordp)
		 (:instance word-fix=reducedwordp)
		 (:instance weak-wordp-rev)
		 (:instance word-fix-lemma-1)
		 (:instance word-fix=reducedwordp-1 (x x))
		 (:instance word-fix=reducedwordp-1 (x (rev x))))
	   :in-theory nil
	   
	   ))
  )

(defun word-flip (x)
  (cond ((atom x) nil)
	((equal (car x) (wa)) (cons (wa-inv) (word-flip (cdr x))))
        ((equal (car x) (wa-inv)) (cons (wa) (word-flip (cdr x))))
        ((equal (car x) (wb)) (cons (wb-inv) (word-flip (cdr x))))
        ((equal (car x) (wb-inv)) (cons (wb) (word-flip (cdr x)))))
  )

(defun word-inverse (x)
  (rev (word-flip x))
  )

(defthmd weak-wordp-flip
  (implies (or (a-wordp x)
	       (b-wordp x)
	       (a-inv-wordp x)
	       (b-inv-wordp x)
	       (equal x '()))
	   (weak-wordp (word-flip x)))
  )

(defthmd weak-wordp-flip-1
  (implies (weak-wordp x)
	   (weak-wordp (word-flip x)))
  )

(defthmd weak-wordp-inverse
  (implies (weak-wordp x)
	   (weak-wordp (word-inverse x)))
  :hints (("Goal"
	   :use (:instance weak-wordp-flip-1)
	   ))
  )

(defthmd reduced-wordp-flip-1
  (implies (or (a-wordp x)
	       (b-wordp x)
	       (a-inv-wordp x)
	       (b-inv-wordp x))
	   (reducedwordp (word-flip x)))
  :hints (("Goal"
	   :use (:instance weak-wordp-inverse)
	   ))
  )

(defthmd reduced-wordp-flip-2
  (implies (equal x '())
	   (reducedwordp (word-flip x)))
  )


(defthmd reduced-wordp-flip
  (implies (reducedwordp x)
	   (reducedwordp (word-flip x)))
  :hints (("Goal"
	   :use ((:instance reduced-wordp-flip-1)
		 (:instance reduced-wordp-flip-2))
					;:in-theory nil
	   ))
  )


(defthmd reducedwordp-word-inverse
  (implies (reducedwordp x)
	   (reducedwordp (word-inverse x)))
  :hints (("Goal"
	   :use (
		 (:instance reduced-wordp-flip (x x))
		 (:instance rev-word-inv-reduced (x (word-flip x)))
		 )
	   ))
  )

(defthmd reduced-inverse-induct-lemma1
  (implies (and (reducedwordp x)
		(not (atom x)))
	   (equal (append (rev (word-flip (cdr x))) (word-flip (list (car x)))) (rev (word-flip x)))
	   )
  )


(defthmd reduced-inverse-induct-lemma2
  (implies (and (character-listp x)
		(not (atom x))
		(character-listp y))
	   (equal (cdr (append x y)) (append (cdr x) y)))
  :hints (("Goal"
	   :in-theory (enable append)
	   ))
  )

(defthmd reduced-inverse-induct-lemma3
  (implies (and (reducedwordp x)
		(not (atom x)))
	   (not (atom (rev (word-flip x)))))
  )

(defthmd reduced-inverse-induct-lemma4
  (implies (and (reducedwordp x)
		(not (atom x)))
	   (reducedwordp (word-flip (list (car x)))))
  )

(defthmd reduced-inverse-induct-lemma5
  (implies (and (reducedwordp x)
		(not (atom x)))
	   (equal (compose (list (car x)) (word-flip (list (car x)))) '())))


(defthmd reduced-inverse-induct-lemma6
  (implies (and (reducedwordp x)
		(not (atom x)))
	   (equal 
	    (compose (cdr x) (compose (rev (word-flip (cdr x))) (word-flip (list (car x)))))
	    (WORD-FIX (CDR (APPEND X (REV (WORD-FLIP X)))))))
  :hints (("Goal"
	   :use ((:instance reduced-wordp-flip (x x))
		 (:instance word-fix=reducedwordp (x (rev (word-flip x))))
		 (:instance reduced-inverse-induct-lemma1 (x x))
		 (:instance rev-word-inv-reduced (x (word-flip x)))
		 )
	   :in-theory (enable compose)
	   ))
  )


(defthmd reduced-inverse-induct
  (IMPLIES (AND (NOT (ATOM X))
		(IMPLIES (REDUCEDWORDP (CDR X))
			 (EQUAL (COMPOSE (CDR X)
					 (REV (WORD-FLIP (CDR X))))
				NIL)))
	   (IMPLIES (REDUCEDWORDP X)
		    (EQUAL (COMPOSE X (REV (WORD-FLIP X)))
			   NIL)))

  :hints (("Goal"
	   :use ((:instance reduced-cdr (x x))
		 (:instance reduced-wordp-flip (x (cdr x)))
		 (:instance rev-word-inv-reduced (x (word-flip (cdr x))))
		 (:instance reduced-wordp-flip (x x))
		 (:instance rev-word-inv-reduced (x (word-flip x)))
		 (:instance assoc-prop (x (cdr x)) (y (rev (word-flip (cdr x)))) (z (word-flip (list (car x)))))
		 (:instance reduced-inverse-induct-lemma1 (x x))
		 (:instance reduced-inverse-induct-lemma2 (x x) (y (rev (word-flip x))))
		 (:instance character-listp-word (x x))
		 (:instance character-listp-word (x (rev (word-flip x))))
		 (:instance reduced-inverse-induct-lemma3 (x x))
		 (:instance reduced-inverse-induct-lemma4 (x x))
		 (:instance word-fix=reducedwordp (x (rev (word-flip x))))
		 (:instance COMPOSE (x NIL) (y (WORD-FLIP (LIST (CAR X)))))
		 (:instance COMPOSE (x (REV (WORD-FLIP (CDR X)))) (y (WORD-FLIP (LIST (CAR X)))))
		 (:instance reduced-inverse-induct-lemma5 (x x))
		 (:instance COMPOSE (x X) (y (REV (WORD-FLIP X))))
		 (:instance word-fix (w (append x (rev (word-flip x)))))
		 (:instance reduced-inverse-induct-lemma6 (x x))
		 )
	   :in-theory (enable compose)
	   :do-not-induct t
	   )
	  )
  )

(defthmd reduced-inverse-lemma
  (implies (reducedwordp x)
	   (equal (compose x (rev (word-flip x))) '()))
  :hints (
	  ("Subgoal *1/5"
	   :use ((:instance reduced-inverse-induct))
	   )
	  ("Subgoal *1/4"
	   :use ((:instance reduced-inverse-induct))
	   )
	  ("Subgoal *1/3"
	   :use ((:instance reduced-inverse-induct))
	   )
	  ("Subgoal *1/2"
	   :use ((:instance reduced-inverse-induct))
	   )
	  
	  )
  )

(defthmd reduced-inverse
  (implies (reducedwordp x)
	   (equal (compose x (word-inverse x)) '()))
  :hints (("Goal"
	   :use (:instance reduced-inverse-lemma)
	   ))
  )
