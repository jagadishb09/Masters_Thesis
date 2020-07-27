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




;;;;;;;;;;;;;inverse exists;;;;;;

(defthmd basecase
  (IMPLIES (ATOM X)
         (IMPLIES (AND (WEAK-WORDP X)
                       (EQUAL (WORD-FIX X) X))
                  (EQUAL (WORD-FIX (REVERSE X))
                         (REVERSE X))))
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
	     (weak-wordp (reverse x)))
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
	     (equal (append (reverse (cdr x)) (list (car x))) (reverse x)))
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
		  (not (equal (reverse (cdr x)) nil))
		  (not (atom (reverse (cdr x))))))
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
		  (not (atom (reverse (cdr x))))
		  (reducedwordp x))
	     (cond ((equal (nth (- (len (reverse (cdr x))) 1) (reverse (cdr x))) (wa)) (not (equal (car x) (wa-inv))))
		   ((equal (nth (- (len (reverse (cdr x))) 1) (reverse (cdr x))) (wb)) (not (equal (car x) (wb-inv))))
		   ((equal (nth (- (len (reverse (cdr x))) 1) (reverse (cdr x))) (wb-inv)) (not (equal (car x) (wb))))
		   ((equal (nth (- (len (reverse (cdr x))) 1) (reverse (cdr x))) (wa-inv)) (not (equal (car x) (wa))))
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
			  (EQUAL (WORD-FIX (REVERSE (CDR X)))
				 (REVERSE (CDR X)))))
	    (IMPLIES (AND (WEAK-WORDP X)
			  (EQUAL (WORD-FIX X) X))
		     (EQUAL (WORD-FIX (REVERSE X))
			    (REVERSE X))))
   :hints (("Goal"
	    :use ((:instance weak-word-cdr (x x))
		  (:instance word-fix-cdr (x x))
		  (:instance weak-wordp-rev (x (cdr x)))
		  (:instance word-fix-lemma2 (x (reverse (cdr x))) (y (car x)))
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
	   (equal (word-fix (reverse x)) (reverse x)))
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
	   (weak-wordp (reverse x)))
  )



(defthmd rev-word-inv-reduced
  (implies (reducedwordp x)
	   (reducedwordp (reverse x)))
  :hints (("Goal"
	   :use ((:instance reducedwordp=>weak-wordp)
		 (:instance word-fix=reducedwordp)
		 (:instance weak-wordp-rev)
		 (:instance word-fix-lemma-1)
		 (:instance word-fix=reducedwordp-1 (x x))
		 (:instance word-fix=reducedwordp-1 (x (reverse x))))
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
  (reverse (word-flip x))
  )

(defthmd weak-wordp-inverse
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























(defthmd last-x-=car-rev
  (implies (character-listp x)
	   (equal (car (last x)) (car (reverse x))))
  :hints (("Goal"
	   :in-theory (enable rev)
	   ))
  )

(defthmd character-listp-word
  (implies (or (reducedwordp x)
	       (weak-wordp x))
	   (character-listp x))
  )

(defthmd rev-word-inv-lemma1
  (implies (and (character-listp x)
		(integerp n)
		(>= n 0)
		(< n (len x)))
	   (equal (nth n x) (nth (- (len x) (+ n 1)) (reverse x))))
  :hints (("Goal"
	   ;:in-theory (enable len nth)
	   ;:do-not-induct t
	   ))
  )


(defthmd rev-word-inv-lemma2
  (implies (and (weak-wordp x)
		(integerp n)
		(< n (len x)))
	   (cond ((equal (nth n x) (wb-inv)) (equal (nth n (word-flip x)) (wb)))
		 ((equal (nth n x) (wa-inv)) (equal (nth n (word-flip x)) (wa)))
		 ((equal (nth n x) (wb)) (equal (nth n (word-flip x)) (wb-inv)))
		 ((equal (nth n x) (wa)) (equal (nth n (word-flip x)) (wa-inv)))
		 ((equal x '()) (equal x '()))))
  )

(defthmd rev-word-inv-lemma3
  (implies (weak-wordp x)
	   (and (equal (len x) (len (reverse x)))
		(equal (len x) (len (word-flip x)))
		(equal (len x) (len (reverse (word-flip x)))))))
  

(defthmd rev-word-inv-lemma4
    (implies (and (weak-wordp x)
		  (integerp n)
		  (>= n 0)
		  (< n (len x)))
	     (cond ((equal (nth n x) (wb-inv)) (equal (nth (- (len x) (+ n 1)) (reverse (word-flip x))) (wb)))
		   ((equal (nth n x) (wa-inv)) (equal (nth (- (len x) (+ n 1)) (reverse (word-flip x))) (wa)))
		   ((equal (nth n x) (wb)) (equal (nth (- (len x) (+ n 1)) (reverse (word-flip x))) (wb-inv)))
		   ((equal (nth n x) (wa)) (equal (nth (- (len x) (+ n 1)) (reverse (word-flip x))) (wa-inv)))
		   ((equal x '()) (equal x '()))))
    :hints (("Goal"
	     :use ((:instance rev-word-inv-lemma2 (x x))
		   (:instance rev-word-inv-lemma1 (x (word-flip x)))
		   (:instance rev-word-inv-lemma3 (x x))) 
	     :do-not-induct t
	     ))
    )

(defthmd rev-word-inv-lemma
  (implies (and (weak-wordp x)
		(integerp n)
		(>= n 0)
		(< n (len x)))
	   (cond ((equal (nth n x) (wb-inv)) (equal (nth (- (len x) (+ n 1)) (word-inverse x)) (wb)))
		 ((equal (nth n x) (wa-inv)) (equal (nth (- (len x) (+ n 1)) (word-inverse x)) (wa)))
		 ((equal (nth n x) (wb)) (equal (nth (- (len x) (+ n 1)) (word-inverse x)) (wb-inv)))
		 ((equal (nth n x) (wa)) (equal (nth (- (len x) (+ n 1)) (word-inverse x)) (wa-inv)))
		 ((equal x '()) (equal x '()))))
  :hints (("Goal"
	   :use ((:instance rev-word-inv-lemma4 (x x)))
	   ))
  )


(defthmd weak-wordp-rev
  (implies (weak-wordp x)
	   (weak-wordp (reverse x)))
  )


(defthmd weak-word-=
  (implies (weak-wordp x)
	   (or (equal x '())
	       (and (equal (car x) (wa)) (weak-wordp (cdr x)))
	       (and (equal (car x) (wa-inv)) (weak-wordp (cdr x)))
	       (and (equal (car x) (wb)) (weak-wordp (cdr x)))
	       (and (equal (car x) (wb-inv)) (weak-wordp (cdr x)))
	       ))
  )



;; (defthmd reducedwordp-rev-lemma
;;   (implies (and (reducedwordp x)
;; 		(equal x '()))
;; 	   (reducedwordp (reverse x)))
;;   )

;; (defthmd reducedwordp-rev-lemma1
;;     (implies (and (reducedwordp x)
;; 		  (not (equal x '())))
;; 	     (not (equal (reverse x) '()))))
  

;; (defthmd reducedwordp-rev
;;   (implies (and (reducedwordp x)
;; 		(integerp n)
;; 		(>= n 0)
;; 		(< n (len x)))
;; 		(reducedwordp (reverse x)))
;;   :hints (("Goal"
;; 	   :use ((:instance rev-word-inv-lemma1 (x x) (n n))
;; 		 (:instance character-listp-word (x x))
;; 		 (:instance reducedwordp=>weak-wordp (x x))
;; 		 (:instance reducedwordp-rev-lemma)
;; 		 )
;; 	   :do-not-induct t
;; 	   )
;; 	  ("Subgoal 94"
;; 	   :use (:instance reducedwordp-rev-lemma1 (x x))
;; 	   )
;; 	  )
;;   )

;; (defun-sk reducedwordp-def (x)
;;   (forall n
;; 	  (implies (and (weak-wordp x)
;; 			(integerp n)
			
;; 			;(>= n 0)
;; 			;(< n (len x))
;; 			;; (characterp y)
;; 			;; (equal y (nth n x))
;; 			(cond ((equal (nth n x) (wa)) (not (equal (nth (+ n 1) x) (wa-inv))))
;; 			      ((equal (nth n x) (wb)) (not (equal (nth (+ n 1) x) (wb-inv))))
;; 			      ((equal (nth n x) (wa-inv)) (not (equal (nth (+ n 1) x) (wa))))
;; 			      ((equal (nth n x) (wb-inv)) (not (equal (nth (+ n 1) x) (wb))))
;; 			      ((equal x '()) (equal x '()))
;; 			      )
;; 			)
;; 		   (reducedwordp x)))
;;   )

;; (defthm reducedwordp-lemma
;;   (implies (weak-wordp x)
;; 	   (reducedwordp-def x))
;;   :hints (("Goal"
;; 	   :use ((:instance weak-word-= (x x)))
;; 	   ;do-not-induct t
;; 	   ))
;;   )
























(defthmd compose-lemma
    (implies (or (and (equal x (list (wa)))
		      (a-inv-wordp y))
		 (and (equal x (list (wb)))
		      (b-inv-wordp y))
		 (and (equal x (list (wb-inv)))
		      (b-wordp y))
		 (and (equal x (list (wa-inv)))
		      (a-wordp y)))
	     (equal (compose x y) (cdr y)))
    :hints (("Goal"
	     :use ((:instance word-fix=reducedwordp (x (cdr y)))
		   (:instance reducedwordp (x y))
		   (:instance reduced-cdr (x y))
		   )
	     :do-not-induct t
	   ))
  )

(defthmd inverse-compose=identity-lemma
  (implies (and (reducedwordp x)
		(reducedwordp (word-inverse x))
		(equal x '()))
	   (equal (compose x (word-inverse x)) '()))
  )

(defthmd inverse-compose=identity-lemma-1
  (implies (and (reducedwordp x)
		(reducedwordp (word-inverse x))
		(equal (word-inverse x) '()))
	   (equal (compose x (word-inverse x)) '()))
  )


(skip-proofs
 (defthmd lemma-test
   (implies (and (not (atom x))
		 (characterp y)
		 (equal (car (last x)) y))
	    (equal (last x) (list y)))
   )
 )


(defthmd compose-red-lemma
  (implies (and (weak-wordp x)
		(not (atom x))
		(reducedwordp y)
		(equal (car (last x)) (wa))
		(equal (car y) (wa-inv)))
	   (equal (compose x y) (compose (reverse (cdr (reverse x))) (cdr y))))

  :hints (("Goal"
	   :use ((:instance compose-lemma (x (last x)) (y y)))
	   :expand (word-fix (append x y))
	   :in-theory (enable append)
	   :do-not-induct t
	   )
	  ("Subgoal 2"
	   :use ((:instance member-weak-word (x x) (y (car (last x))))
		 (:instance lemma-test (x x) (y (car (last x)))))
	   )
	  ("Subgoal 3"
	   :use (:instance member-weak-word (x x) (y (car (last x))))
	   )
	  )
  )



(defthm inverse-compose=identity
  (implies (and (reducedwordp x)
		(reducedwordp (word-inverse x)))
	   (equal (compose x (word-inverse x)) '()))
  :hints (("Goal"
	   :use ((:instance reducedwordp=>weak-wordp (x x))
		 (:instance reducedwordp=>weak-wordp (x (word-inverse x)))
		 (:instance word-fix=reducedwordp (x (word-inverse x)))
		 (:instance reduced-wordp-inverse (x x))
		 (:instance rev-word-inv-reduced (x (word-flip x)))
		 (:instance compose-lemma (x (last x)) (y (word-inverse x)))
		 (:instance rev-word-inv-lemma1 (x x))
		 (:instance inverse-compose=identity-lemma (x x))
		 (:instance inverse-compose=identity-lemma-1 (x x))
		 )
	   :in-theory (enable word-fix append)
	   ;:do-not-induct t
	   ))
  )




(defthmd test-lemma
  (implies (and (weak-wordp x)
		(member y x)
		(equal y (wa)))
	   (equal (car (member y x)) (wa)))

  )


(defthmd test-lemma-1
  (implies (and (weak-wordp x)
		(member y x)
		(equal y (wa))
		(equal (car (cdr (member y x))) (wa-inv)))
	   (not (reducedwordp x)))
  )


(defthmd test-lemma-2
  (implies (and (weak-wordp x)
		(not (equal x '()))
		(member y x)
		(or (and (equal y (wa))
			 (not (equal (car (cdr (member y x))) (wa-inv))))
		    (and (equal y (wa-inv))
			 (not (equal (car (cdr (member y x))) (wa))))
		    (and (equal y (wb))
			 (not (equal (car (cdr (member y x))) (wb-inv))))
		    (and (equal y (wb-inv))
			 (not (equal (car (cdr (member y x))) (wb))))
		    )
		)
	   (reducedwordp x))
  )

(defthmd test-lemma-2
  (implies (and (weak-wordp x)
		(not (reducedwordp x))
		(member y x))
	   (or (cond ((equal y (wa)) (equal (car (member y x)) (wa-inv)))
		     ((equal y (wa-inv)) (equal (car (member y x)) (wa)))
		     ((equal y (wb)) (equal (car (member y x)) (wb-inv)))
		     ((equal y (wb-inv)) (equal (car (member y x)) (wb))))))
	   
  )









(defthmd rev-rev=x
  (implies (character-listp x)
	   (equal (reverse (reverse x)) x))
  )






(defthmd weak-wordp-rev
  (implies (weak-wordp x)
	   (weak-wordp (reverse x)))
  )


(defthmd rev-word-inv-weak
  (implies (reducedwordp x)
	   (weak-wordp (reverse (word-inverse x))))
  :hints (("Goal"
	   :use ((:instance weak-wordp-inverse)
		 (:instance weak-wordp-rev (x (reverse x))))
	   ))
  )



(encapsulate
 ()

 (local
  (defthmd reduced-cdr
    (implies (reducedwordp x)
	     (reducedwordp (cdr x)))
    )
  )

 (local
  (defthmd weak-word-=
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
  (defthmd member-weak-word
    (implies (and (weak-wordp x)
		  (characterp y)
		  (not (equal x '()))
		  (member y x))
	     (or (equal y (wa))
		 (equal y (wb))
		 (equal y (wa-inv))
		 (equal y (wb-inv))))

    :hints (("Goal"
	     :use (:instance weak-word-= (x x))
	     :in-theory (disable reducedwordp)
	     )
	    )
    )
  )

 (defthmd rev-rev-lemma
   (implies (and (character-listp x)
		 (not (a-wordp (reverse x)))
		 (NOT (EQUAL (CAR (REV X)) #\b))
		 (NOT (EQUAL (CAR (REV X)) #\c))
		 (NOT (EQUAL (CAR (REV X)) #\d))
		 (not (equal (reverse x) '())))
	    (not (reducedwordp x)))

   :hints (("Subgoal 8"
	    :use ((:instance last-x-=car-rev (x x))
		  (:instance reducedwordp=>weak-wordp (x x))
		  (:instance member-weak-word (x x) (y (car (last x))))
		  (:instance reduced-cdr (x x))
		  )
	    )

	   ("Subgoal 7"
	    :use ((:instance last-x-=car-rev (x x))
		  (:instance reducedwordp=>weak-wordp (x x))
		  (:instance member-weak-word (x x) (y (car (last x))))
		  )
	    )

	   ("Subgoal 6"
	    :use ((:instance last-x-=car-rev (x x))
		  (:instance reducedwordp=>weak-wordp (x x))
		  (:instance member-weak-word (x x) (y (car (last x))))
		  )
	    )
	   ("Subgoal 5"
	    :use ((:instance last-x-=car-rev (x x))
		  (:instance reducedwordp=>weak-wordp (x x))
		  (:instance member-weak-word (x x) (y (car (last x))))
		  )
	    )
	   ("Subgoal 4"
	    :use ((:instance rev-rev=x (x x))
		  )
	    :expand (WORDP (CDR (REV X)) #\a)
	    )
	   
	   
	   )
   )
 )


(defthmd rev-word-inv-reduced
  (implies (reducedwordp x)
	   (reducedwordp (reverse x)))

  :hints (("Subgoal 32"
	   :use ((:instance character-listp-word (x x))
		 (:instance rev-rev=x (x x)))
	   ))
  
  )












(defthmd weak-cdr
  (implies (weak-wordp x)
	   (weak-wordp (cdr x)))
  )

(defthmd character-listp-word
  (implies (or (reducedwordp x)
	       (weak-wordp x))
	   (character-listp x))
  )


(defthmd last-x-=car-rev
  (implies (character-listp x)
	   (equal (car (last x)) (car (reverse x))))
  :hints (("Goal"
	   :in-theory (enable rev)
	   ))
  )



(defthmd char-listp-cdr
  (implies (character-listp x)
	   (character-listp (cdr x)))
  )

(defthmd lemma1
  (implies (consp x)
	   (member (car (last x)) x))
  )

(defthmd lemma2
  (implies (and (weak-wordp x)
		(not (equal x '())))
	   (consp x))
  )

(defthmd wordp-wa-implies
  (implies (wordp x (wa))
	   (or (equal x '())
	       (cond ((equal (car x) (wa)) (wordp (cdr x) (wa)))
		     ((equal (car x) (wb)) (wordp (cdr x) (wb)))
		     ((equal (car x) (wb-inv)) (wordp (cdr x) (wb-inv))))))
  )

(defthmd wordp-wa-inv-implies
  (implies (wordp x (wa-inv))
	   (or (equal x '())
	       (cond ((equal (car x) (wa-inv)) (wordp (cdr x) (wa-inv)))
		     ((equal (car x) (wb)) (wordp (cdr x) (wb)))
		     ((equal (car x) (wb-inv)) (wordp (cdr x) (wb-inv))))))
  )

(defthmd wordp-wb-implies
  (implies (wordp x (wb))
	   (or (equal x '())
	       (cond ((equal (car x) (wb)) (wordp (cdr x) (wb)))
		     ((equal (car x) (wa)) (wordp (cdr x) (wa)))
		     ((equal (car x) (wa-inv)) (wordp (cdr x) (wa-inv))))))
  )

(defthmd wordp-wb-inv-implies
  (implies (wordp x (wb-inv))
	   (or (equal x '())
	       (cond ((equal (car x) (wb-inv)) (wordp (cdr x) (wb-inv)))
		     ((equal (car x) (wa)) (wordp (cdr x) (wa)))
		     ((equal (car x) (wa-inv)) (wordp (cdr x) (wa-inv))))))
  )


(defthmd test-lemma
  (implies (and (weak-wordp x)
		(> (len x) 2)
		(member y x)
		(equal (car (member y x)) (wa))
		(equal (car (cdr (member y x))) (wa-inv)))
	   (not (reducedwordp (rev x))))
    :hints (("Goal"
	     :in-theory (enable rev))
	    ("Subgoal 4"
	     :use (:instance wordp-wa-implies (x (cdr (rev x))))
	     )
	    )
  )




(defthm rev-word-inv-reduced
  (implies (reducedwordp x)
	   (reducedwordp (reverse x)))
  :hints (("Subgoal 32"
	   :use ((:instance character-listp-word (x x))
		 (:instance lemma2)
		 (:instance lemma1)
		 (:instance last-x-=car-rev (x x))
		 (:instance member-weak-word (x x) (y (car (last x)))))
	   :in-theory (enable rev)
	   ))
  )
  :hints (("Goal"
	   :use ((:instance weak-wordp-rev)
		 (:instance weak-word-= (x (reverse x)))
		 (:instance weak-word-= (x x))
		 (:instance reduced-cdr)
		 (:instance weak-cdr(x x))
		 (:instance weak-cdr(x (reverse x)))
		 (:instance reducedwordp=>weak-wordp (x x))
		 (:instance character-listp-word (x x))
		 (:instance character-listp-word (x (reverse x)))
		 ;(:instance last-x-=car-rev (x x))
		 (:instance char-listp-cdr (x x)))
	   :in-theory (enable rev)
	   )
	  ("Subgoal 64"
	   :use ((:instance member-weak-word (x x) (y (car (last x)))))
	   )

	  ("Subgoal 63"
	   :use (;(:instance last-x-=car-rev (x x))
		 (:instance char-listp-cdr (x x)))
	   )
	  
	  )
  )



;; (defthmd rev-word-inv-lemma-1
;;   (implies (and (weak-wordp x)
;; 		(equal (car (last x)) (wa))
;; 		(equal y (word-flip x)))
;; 	   (equal (car (last y)) (wa-inv)))
;;   )

;; (defthmd rev-word-inv-lemma-2
;;   (implies (and (weak-wordp x)
;; 		(equal (car (last x)) (wa-inv))
;; 		(equal y (word-flip x)))
;; 	   (equal (car (last y)) (wa)))
;;   )


;; (defthmd rev-word-inv-lemma-3
;;   (implies (and (weak-wordp x)
;; 		(equal (car (last x)) (wb))
;; 		(equal y (word-flip x)))
;; 	   (equal (car (last y)) (wb-inv)))
;;   )

;; (defthmd rev-word-inv-lemma-4
;;   (implies (and (weak-wordp x)
;; 		(equal (car (last x)) (wb-inv))
;; 		(equal y (word-flip x)))
;; 	   (equal (car (last y)) (wb)))
;;   )

;; (defthmd weak-word-=
;;   (implies (weak-wordp x)
;; 	   (or (equal x '())
;; 	       (and (equal (car x) (wa)) (weak-wordp (cdr x)))
;; 	       (and (equal (car x) (wa-inv)) (weak-wordp (cdr x)))
;; 	       (and (equal (car x) (wb)) (weak-wordp (cdr x)))
;; 	       (and (equal (car x) (wb-inv)) (weak-wordp (cdr x)))
;; 	       ))
;;   )

;; (defthmd member-weak-word
;;   (implies (and (weak-wordp x)
;; 		(characterp y)
;; 		(not (equal x '()))
;; 		(member y x))
;; 	   (or (equal y (wa))
;; 	       (equal y (wb))
;; 	       (equal y (wa-inv))
;; 	       (equal y (wb-inv))))

;;   :hints (("Goal"
;; 	   :use (:instance weak-word-= (x x))
;; 	   :in-theory (disable reducedwordp)
;; 	   )
;; 	  )
;;   )

;; (defthmd rev-word-inv-lemma
;;   (implies (weak-wordp x)
;; 		;(not (equal x '()))
;; 	   ;(equal y (word-inverse x)))
;; 	   (cond ((equal (car (last x)) (wa)) (equal (car (last (word-flip x))) (wa-inv)))
;; 		 ((equal (car (last x)) (wb)) (equal (car (last (word-flip x))) (wb-inv)))
;; 		 ((equal (car (last x)) (wa-inv)) (equal (car (last (word-flip x))) (wa)))
;; 		 ((equal (car (last x)) (wb-inv)) (equal (car (last (word-flip x))) (wb)))
;; 		 ((equal x '()) (equal x '()))))
;;   :hints (("Goal"
;; 	   :use ((:instance character-listp-word (x x))
;; 		 (:instance member-weak-word (x x) (y (car (last x))))
;; 		 (:instance weak-word-= (x x))
;; 		 (:instance rev-word-inv-lemma-1 (x x) (y (word-flip x)))
;; 		 (:instance rev-word-inv-lemma-2 (x x) (y (word-flip x)))
;; 		 (:instance rev-word-inv-lemma-3 (x x) (y (word-flip x)))
;; 		 (:instance rev-word-inv-lemma-4 (x x) (y (word-flip x))))
;; 	   :do-not-induct t
		 
;; 	   ))
;;   )


;; (defthmd rev-word-inv-lemma1
;;   (implies (weak-wordp x)
;; 	   (cond ((equal (car (last x)) (wb-inv)) (equal (car (reverse (word-flip x))) (wb)))
;; 		 ((equal (car (last x)) (wa-inv)) (equal (car (reverse (word-flip x))) (wa)))
;; 		 ((equal (car (last x)) (wa)) (equal (car (reverse (word-flip x))) (wa-inv)))
;; 		 ((equal (car (last x)) (wb)) (equal (car (reverse (word-flip x))) (wb-inv)))
;; 		 ((equal x '()) (equal x '()))))
;;   :hints (("Goal"
;; 	   :use (
;; 		 (:instance weak-wordp-inverse-1 (x x))
;; 		 (:instance character-listp-word (x (word-flip x)))
;; 		 (:instance rev-word-inv-lemma (x x))
;; 		 (:instance last-x-=car-rev (x (word-flip x))))
;; 	   ;:in-theory nil
;; 	   ))
;;   )

;; (defthmd rev-word-inv-lemma2
;;   (implies (weak-wordp x)
;; 	   (cond ((equal (car (last x)) (wb-inv)) (equal (car (word-inverse x)) (wb)))
;; 		 ((equal (car (last x)) (wa-inv)) (equal (car (word-inverse x)) (wa)))
;; 		 ((equal (car (last x)) (wa)) (equal (car (word-inverse x)) (wa-inv)))
;; 		 ((equal (car (last x)) (wb)) (equal (car (word-inverse x)) (wb-inv)))
;; 		 ((equal x '()) (equal x '()))))
;;   :hints (("Goal"
;; 	   :use (
;; 		 (:instance weak-wordp-inverse-1 (x x))
;; 		 (:instance character-listp-word (x (word-flip x)))
;; 		 (:instance rev-word-inv-lemma (x x))
;; 		 (:instance last-x-=car-rev (x (word-flip x))))
;; 	   ;:in-theory nil
;; 	   ))
;;   )


;;  (defthmd reducedwordp=>weak-wordp
;;    (IMPLIES (reducedwordp x)
;; 	    (weak-wordp x)))

;;  (defthmd word-fix=reducedwordp
;;    (implies (reducedwordp x)
;; 	    (equal (word-fix x) x))
;;    )

;;  (defthmd word-fix=reducedwordp-1
;;    (implies (and (weak-wordp x)
;; 		 (equal (word-fix x) x))
;; 	    (reducedwordp x))
;;    :hints (("Goal"
;; 	    :use (:instance weak-wordp-equivalent (x x))
;; 	    ))
;;    )


;; (defthmd reduced-wordp-inverse
;;   (implies (reducedwordp x)
;; 	   (reducedwordp (word-inverse x)))
;;   :hints (("Goal"
;; 	   :use ((:instance reduced-wordp-inverse-1)
;; 		 (:instance reduced-wordp-inverse-2))
;; 	   ;:in-theory nil
;; 	   ))
;;   )

;; (defthmd rev-word-inv-reduced
;;   (implies (reducedwordp x)
;; 	   (reducedwordp (reverse x)))
;;   :hints (("Goal"
;; 	   :use ((:instance reducedwordp=>weak-wordp)
;; 		 (:instance word-fix=reducedwordp)
;; 		 (:instance weak-wordp-rev)
;; 		 (:instance word-fix-lemma-1)
;; 		 (:instance word-fix=reducedwordp-1 (x x))
;; 		 (:instance word-fix=reducedwordp-1 (x (reverse x))))
;; 	   :in-theory nil
		 
;; 	   ))
;;   )

;; (defthmd compose-lemma
;;     (implies (or (and (equal x (list (wa)))
;; 		      (a-inv-wordp y))
;; 		 (and (equal x (list (wb)))
;; 		      (b-inv-wordp y))
;; 		 (and (equal x (list (wb-inv)))
;; 		      (b-wordp y))
;; 		 (and (equal x (list (wa-inv)))
;; 		      (a-wordp y)))
;; 	     (equal (compose x y) (cdr y)))
;;     :hints (("Goal"
;; 	     :use ((:instance word-fix=reducedwordp (x (cdr y)))
;; 		   (:instance reducedwordp (x y))
;; 		   (:instance reduced-cdr (x y))
;; 		   )
;; 	     :do-not-induct t
;; 	   ))
;;     )

;; (defthmd rev-word-inv-lemma1
;;   (implies (weak-wordp x)
;; 	   (cond ((equal (car (last x)) (wb-inv)) (equal (car (reverse (word-flip x))) (wb)))
;; 		 ((equal (car (last x)) (wa-inv)) (equal (car (reverse (word-flip x))) (wa)))
;; 		 ((equal (car (last x)) (wa)) (equal (car (reverse (word-flip x))) (wa-inv)))
;; 		 ((equal (car (last x)) (wb)) (equal (car (reverse (word-flip x))) (wb-inv)))
;; 		 ((equal x '()) (equal x '()))))
;;   :hints (("Goal"
;; 	   :use (
;; 		 (:instance weak-wordp-inverse-1 (x x))
;; 		 (:instance character-listp-word (x (word-flip x)))
;; 		 (:instance rev-word-inv-lemma (x x))
;; 		 (:instance last-x-=car-rev (x (word-flip x))))
;; 	   ;:in-theory nil
;; 	   ))
;;   )


  ;; :hints (("Goal"
  ;; 	   :use ((:instance reduced-wordp-inverse)
  ;; 		 (:instance reduced-wordp-reverse (x (word-inverse x))))
  ;; 	   :in-theory (enable rev)
  ;; 	   )))





;; (defthmd rev-word-inv-reduced-base
;;   (implies (and (endp x)
;; 		(reducedwordp x))
;; 	   (reducedwordp (reverse x)))
;;   )


;; (skip-proofs
;;  (defthm rev-word-inv-reduced-induction
;;    (implies (and (reducedwordp x)
;; 		 (implies (and (not (endp x))
;; 			       (reducedwordp (cdr x)))
;; 			  (reducedwordp (reverse (cdr x)))))
;; 		 (reducedwordp (reverse x)))
;;    )
;;  )


;; (defthmd rev-word-inv-reduced
;;   (implies (reducedwordp x)
;; 	   (reducedwordp (reverse x)))
;;   :hints (("Goal"
;; 	   :use ((:instance rev-word-inv-reduced-base)
;; 		 (:instance rev-word-inv-reduced-induction))
;; 	   ;:induct (reducedwordp (reverse x))
	   
;; 	   ))
;;   )



;; (defthmd rev-word-inv-lemma-41
;;   (implies (and (weak-wordp x)
;; 		(equal (car (last x)) (wb-inv))
;; 		(equal y (word-inverse x)))
;; 	   (equal (car (reverse y)) (wb)))
;;   :hints (("Goal"
;; 	   :use (
;; 		 (:instance weak-wordp-inverse-1 (x x))
;; 		 (:instance character-listp-word (x (word-inverse x)))
;; 		 (:instance rev-word-inv-lemma-4 (x x) (y y))
;; 		 (:instance last-x-=car-rev (x y)))
;; 	   :in-theory nil
;; 	   ))
;;   )


;; (defthmd rev-word-inv-lemma-31
;;   (implies (and (weak-wordp x)
;; 		(equal (car (last x)) (wb))
;; 		(equal y (word-inverse x)))
;; 	   (equal (car (reverse y)) (wb-inv)))
;;   :hints (("Goal"
;; 	   :use (
;; 		 (:instance weak-wordp-inverse-1 (x x))
;; 		 (:instance character-listp-word (x (word-inverse x)))
;; 		 (:instance rev-word-inv-lemma-3 (x x) (y y))
;; 		 (:instance last-x-=car-rev (x y)))
;; 	   :in-theory nil
;; 	   ))
;;   )




;; (defthmd rev-word-inv-lemma-11
;;   (implies (and (weak-wordp x)
;; 		(equal (car (last x)) (wa))
;; 		(equal y (word-inverse x)))
;; 	   (equal (car (reverse y)) (wa-inv)))
;;   :hints (("Goal"
;; 	   :use (
;; 		 (:instance weak-wordp-inverse-1 (x x))
;; 		 (:instance character-listp-word (x (word-inverse x)))
;; 		 (:instance rev-word-inv-lemma-1 (x x) (y y))
;; 		 (:instance last-x-=car-rev (x y)))
;; 	   :in-theory nil
;; 	   ))
;;   )


;; (defthmd rev-word-inv-lemma-21
;;   (implies (and (weak-wordp x)
;; 		(equal (car (last x)) (wa-inv))
;; 		(equal y (word-inverse x)))
;; 	   (equal (car (reverse y)) (wa)))
;;   :hints (("Goal"
;; 	   :use (
;; 		 (:instance weak-wordp-inverse-1 (x x))
;; 		 (:instance character-listp-word (x (word-inverse x)))
;; 		 (:instance rev-word-inv-lemma-2 (x x) (y y))
;; 		 (:instance last-x-=car-rev (x y)))
;; 	   :in-theory nil
;; 	   ))
;;   )


;; (defthmd compose-lemma-1
;;   (implies (and (equal x (list (wa)))
;; 		(a-inv-wordp y))
;; 	   (equal (compose x y) (cdr y)))
;;   :hints (("Goal"
;; 	   :use ((:instance word-fix=reducedwordp (x (cdr y)))
;; 		 (:instance reducedwordp (x y))
;; 		 (:instance reduced-cdr (x y))
;; 		 )
;; 	   :do-not-induct t
;; 	   ))
;;   )

;; (defthmd compose-lemma-2
;;   (implies (and (equal x (list (wa-inv)))
;; 		(a-wordp y))
;; 	   (equal (compose x y) (cdr y)))
;;   :hints (("Goal"
;; 	   :use ((:instance word-fix=reducedwordp (x (cdr y)))
;; 		 (:instance reducedwordp (x y))
;; 		 (:instance reduced-cdr (x y))
;; 		 )
;; 	   :do-not-induct t
;; 	   ))
;;   )

;; (defthmd compose-lemma-3
;;   (implies (and (equal x (list (wb)))
;; 		(b-inv-wordp y))
;; 	   (equal (compose x y) (cdr y)))
;;   :hints (("Goal"
;; 	   :use ((:instance word-fix=reducedwordp (x (cdr y)))
;; 		 (:instance reducedwordp (x y))
;; 		 (:instance reduced-cdr (x y))
;; 		 )
;; 	   :do-not-induct t
;; 	   ))
;;   )

;; (defthmd compose-lemma-4
;;   (implies (and (equal x (list (wb-inv)))
;; 		(b-wordp y))
;; 	   (equal (compose x y) (cdr y)))
;;   :hints (("Goal"
;; 	   :use ((:instance word-fix=reducedwordp (x (cdr y)))
;; 		 (:instance reducedwordp (x y))
;; 		 (:instance reduced-cdr (x y))
;; 		 )
;; 	   :do-not-induct t
;; 	   ))
;;   )




























;; (defun word-inverse (w)
;;   (if (atom w)
;;       nil
;;     (let ((inv (word-inverse (cdr w))))
;;       (cond ((equal (car w) (wa)) (append inv (list (wa-inv))))
;; 	    ((equal (car w) (wa-inv)) (append inv (list (wa))))
;; 	    ((equal (car w) (wb)) (append inv (list (wb-inv))))
;; 	    ((equal (car w) (wb-inv)) (append inv (list (wb))))))))



(defthm weak-wordp-inverse
  (implies (or (a-wordp x)
	       (b-wordp x)
	       (a-inv-wordp x)
	       (b-inv-wordp x)
	       (equal x '()))
	   (weak-wordp (word-inverse x)))
  )










(defthmd member-reducedword
  (implies (and (reducedwordp x)
		(characterp y)
		(not (equal x '()))
		(member y x))
	   (or (equal y (wa))
	       (equal y (wb))
	       (equal y (wa-inv))
	       (equal y (wb-inv))))
  :hints (("Goal"
	   :use ((:instance reducedwordp=>weak-wordp (x x))
		 (:instance member-weak-word (x x) (y y)))
	   :in-theory (disable reducedwordp)
	   )
	  )
  )

(defthmd mem-x=rev
  (implies (and (character-listp x)
		(characterp y)
		(member y x))
	   (member y (reverse x)))
  :hints (("Goal"
	   :in-theory (enable rev)
	   ))
  )

(defthmd lemma1
  (implies (reducedwordp x)
	   (reducedwordp (cdr x)))
  )

(defthmd lemma2
  (implies (character-listp x)
	   (equal (car (last x)) (car (reverse x))))
  :hints (("goal"
	   :in-theory (enable rev)
	   ))
  )























(skip-proofs
 (defthm reduced-wordp-reverse
   (implies (and (or (a-wordp x)
		     (b-wordp x)
		     (a-inv-wordp x)
		     (b-inv-wordp x))
		 (not (equal x '())))
	    (weak-wordp (reverse x)))
   :hints (("Goal"
	    :use ((:instance lemma1)
		  (:instance reducedwordp=>weak-wordp (x x))
		  (:instance member-weak-word)
		  (:instance mem-x=rev)
		  (:instance weak-word-= (x x)))
	    :in-theory (enable rev)
	    ))
   )
 )





(skip-proofs

 )



(defun-sk reduced-identity-exists (x)
  (exists i
	  (implies (and (a-wordp x)
			(reducedwordp i))
		   (equal (compose x i) '())))
  )


(defthmd reduced-identity-exists-lemma
  (implies (REDUCED-IDENTITY-EXISTS-WITNESS X)
	   (reduced-identity-exists x))
  )













(defun a-inv-a-wordp (x)
  (and (equal (car x) (wa-inv))
       (a-wordp (cdr x)))
  )


(defun-sk exists-x-a-in-a-wordp (y)
  (exists x
	  (equal (compose (wa-inv) (a-wordp x)) y))
  )












































(defthm prop-2.1-1
  (implies 
   (a-inv-a-wordp x)
   (weak-wordp x))
  )


(defthm prop-2.1-2
 (implies (and (equal (append '(#\a) '(#\b)) nil)
	       (character-listp x)
	       (or (a-wordp x)
		   (b-wordp x)
		   (b-inv-wordp x)))
	  (a-inv-a-wordp x)
	  )
 )

(defthm cor-2.1
  
  )

























































(encapsulate
 ()

 (defthmd lemma1
   (implies (reducedwordp x)
	    (reducedwordp (cdr x)))
   )

 (defthmd lemma2
   (implies (reducedwordp x)
	    (equal (word-fix (cdr x)) (cdr x)))
   :hints (("Goal"
	    :use ((:instance lemma1 (x x))
		  (:instance word-fix=reducedwordp (x (cdr x))))
	    ))
   )

 (defthmd lemma3
   (implies (and (reducedwordp x)
		 (reducedwordp y)
		 (reducedwordp z))
	    (equal (compose (compose x y) z) (word-fix (append (append x y) z)))
	    )
   :hints (("Goal"
	    :use (
		  (:instance closure-prop (x y) (y z))
		  (:instance closure-prop (x x) (y (compose y z)))
		  (:instance closure-prop (x (compose x y)) (y z))
		  (:instance closure-prop (x x) (y y))
		  (:instance word-fix=a-wordp (x x))
		  (:instance word-fix=a-inv-wordp (x x))
		  (:instance word-fix=b-wordp (x x))
		  (:instance word-fix=b-inv-wordp (x x))
		  (:instance word-fix=a-wordp (x y))
		  (:instance word-fix=a-inv-wordp (x y))
		  (:instance word-fix=b-wordp (x y))
		  (:instance word-fix=b-inv-wordp (x y))
		  (:instance word-fix=a-wordp (x z))
		  (:instance word-fix=a-inv-wordp (x z))
		  (:instance word-fix=b-wordp (x z))
		  (:instance word-fix=b-inv-wordp (x z))
		  (:instance word-fix=a-wordp (x (compose y z)))
		  (:instance word-fix=a-inv-wordp (x (compose y z)))
		  (:instance word-fix=b-wordp (x (compose y z)))
		  (:instance word-fix=b-inv-wordp (x (compose y z)))
		  (:instance word-fix=a-wordp (x (compose x y)))
		  (:instance word-fix=a-inv-wordp (x (compose x y)))
		  (:instance word-fix=b-wordp (x (compose x y)))
		  (:instance word-fix=b-inv-wordp (x (compose x y)))
		  (:instance lemma2 (x x))
		  (:instance lemma1 (x x))
		  (:instance lemma2 (x y))
		  (:instance lemma1 (x y))
		  (:instance lemma2 (x z))
		  (:instance lemma1 (x z))
		  )
	    ))
   )


 (defthmd assoc-prop
   (implies (and (reducedwordp x)
		 (reducedwordp y)
		 (reducedwordp z))
	    (equal (compose (compose x y) z) (compose x (compose y z)))
	    )
   :hints (("Goal"
	    :use (
		  (:instance closure-prop (x y) (y z))
		  (:instance closure-prop (x x) (y (compose y z)))
		  (:instance closure-prop (x (compose x y)) (y z))
		  (:instance closure-prop (x x) (y y))
		  (:instance word-fix=a-wordp (x x))
		  (:instance word-fix=a-inv-wordp (x x))
		  (:instance word-fix=b-wordp (x x))
		  (:instance word-fix=b-inv-wordp (x x))
		  (:instance word-fix=a-wordp (x y))
		  (:instance word-fix=a-inv-wordp (x y))
		  (:instance word-fix=b-wordp (x y))
		  (:instance word-fix=b-inv-wordp (x y))
		  (:instance word-fix=a-wordp (x z))
		  (:instance word-fix=a-inv-wordp (x z))
		  (:instance word-fix=b-wordp (x z))
		  (:instance word-fix=b-inv-wordp (x z))
		  (:instance word-fix=a-wordp (x (compose y z)))
		  (:instance word-fix=a-inv-wordp (x (compose y z)))
		  (:instance word-fix=b-wordp (x (compose y z)))
		  (:instance word-fix=b-inv-wordp (x (compose y z)))
		  (:instance word-fix=a-wordp (x (compose x y)))
		  (:instance word-fix=a-inv-wordp (x (compose x y)))
		  (:instance word-fix=b-wordp (x (compose x y)))
		  (:instance word-fix=b-inv-wordp (x (compose x y)))
		  (:instance lemma2 (x x))
		  (:instance lemma1 (x x))
		  (:instance lemma2 (x y))
		  (:instance lemma1 (x y))
		  (:instance lemma2 (x z))
		  (:instance lemma1 (x z))
		  )
	    ))
   )

 )



(defthm lemma0
  (IMPLIES (AND (CONSP X)
              (NOT (EQUAL (CAR X) #\a))
              (NOT (EQUAL (CAR X) #\b))
              (NOT (EQUAL (CAR X) #\c))
              (NOT (EQUAL (CAR X) #\d))
              (WORD-FIX (CDR X))
              (NOT (EQUAL (CAR (WORD-FIX (CDR X))) #\a))
              (NOT (EQUAL (CAR (WORD-FIX (CDR X))) #\b))
              (NOT (EQUAL (CAR (WORD-FIX (CDR X))) #\c))
	      (not (EQUAL (CAR (WORD-FIX (CDR X))) #\d)))
	   (not (reducedwordp (word-fix x))))
  )


(defthm lemma1
  (implies (and (reducedwordp y)
		(equal (word-fix x) y))
	   (weak-wordp x))  
  )

(defthm lemma2
  (implies (reducedwordp (word-fix z))
	   (weak-wordp z))
  :hints (("Goal"
	   :use (:instance lemma1 (y (word-fix z)))
	   ))

  )



























(defthm lemma
  (implies (not (weak-wordp x))
	   (not (reducedwordp (word-fix x))))
  )


(defthm lemmaaa
  (implies (and (equal (word-fix x) y)
		(or (a-wordp y)
		    (a-inv-wordp y)
		    (b-wordp y)
		    (b-inv-wordp y)
		    (equal y '())))
	   (weak-wordp x))	   
  )




(defun compose-a-inv-a-wordp (w)
  (and (equal (car w) (wa-inv))
       (a-inv-wordp (cdr w)))
    )




(defthm prop-2.1-1
  (implies (and (a-wordp x)
		(equal y (compose '(#\b) x)))
	   (or (equal y '())
	       (a-wordp y)
	       (b-wordp y)
	       (b-inv-wordp y))))


(implies (and (reducedwordp z)
	      (a-wordp x)
	      (equal y (compose '(#\b) x)))
	 (or (composea-in
	     (a-inv-wordp z)))


(defthm prop-2.1-2
  (implies (and	(b-wordp x)
		(equal y (compose '(#\d) x)))
	   (or (equal y '())
	       (a-wordp y)
	       (b-wordp y)
	       (a-inv-wordp y))))
