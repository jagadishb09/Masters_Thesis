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

;;;;;;;;;;;;;;;;;;associative property



;; (defthmd word-fix-lemma
;;   (implies (and (weak-wordp x)
;; 		(not (equal x '())))
;; 	   (equal (word-fix x) (append (word-fix (list (car x) (car (word-fix (cdr x)))))
;; 				       (cdr (word-fix (cdr x))))))
;;   :hints (("Goal"
;; 	   :use ((:instance weak-wordp-equivalent (x (cdr x)))
;; 		 (:instance character-listp-word (x x))
;; 		 (:instance character-listp-word (x (cdr x)))
;; 		 (:instance word-fix (w x))
;; 		 (:instance weak-word-cdr (x x))
;; 		 (:instance weak-wordp-equivalent (x x))
;; 		 (:instance reducedwordp=>weak-wordp (x x))
;; 		 (:instance reducedwordp=>weak-wordp (x (cdr x)))
;; 		 (:instance weak-wordp-equivalent (x (cdr x)))
;; 	   	 (:instance reducedwordp=>weak-wordp (x (word-fix (cdr x)))))
;; 	   :in-theory (enable append)
;; 	   ;:do-not-induct t
;; 	   ))
;;   )




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
  (defthm append-nil-assoc                    ; as above, but with defaults and
    (implies (character-listp x)             ; a backchain limit
	     (equal (append x nil) x))
    :rule-classes ((:rewrite 
		    :backchain-limit-lst (3) ; or equivalently, 3
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


 ;; (local

 ;;  (defthm word-fix-lemma
 ;;    (implies (and (weak-wordp x)
 ;; 		  (not (equal x '())))
 ;; 	     (equal (word-fix x) (append (word-fix (list (car x) (car (word-fix (cdr x)))))
 ;; 					 (cdr (word-fix (cdr x))))))
 ;;    :hints (("Goal"
 ;; 	     :use ((:instance weak-wordp-equivalent-assoc (x (cdr x)))
 ;; 		   (:instance reducedwordp=>weak-wordp-assoc (x (word-fix (cdr x)))))
 ;; 	     :in-theory (enable append)
 ;; 	     :do-not-induct t
 ;; 	     ))
 ;;    )
 ;;  )
 ;; )

(local
 (defthm assoc-prop-lemma100
   (implies (and (weak-wordp x)
		 (equal y (wa))
		 (equal z (wb)))
	    (equal (word-fix (append (append x (list y)) (list z))) (append (word-fix (append x (list y))) (list z))))
   :hints (("Goal"
	    ;:do-not-induct t
	    ))
   )
 )
)


 ;; (local
 ;;  (defthm assoc-prop-lemma100
 ;;    (implies (and (weak-wordp x)
 ;; 		  (equal y (wa))
 ;; 		  (equal z (wa-inv)))
 ;; 	     (equal (word-fix (append (append x (list y)) (list z))) (word-fix x)))
 ;;    )
 ;;  )
 
 ;; (local
 ;;  (defthm assoc-prop-lemma101
 ;;    (implies (and (weak-wordp x)
 ;; 		  (equal (last x) (list (wa-inv)))
 ;; 		  (equal y (wa))
 ;; 		  (weak-wordp (list y)))
 ;; 	     (equal (word-fix (append (word-fix x) (list y))) (word-fix (rev (cdr (rev x))))))
 ;;    )
 ;;  )
 
 

 ;; (defthm assoc-prep-lemma1
 ;;   (implies (weak-wordp x)
 ;; 	    (equal (rev (word-fix x)) (word-fix (rev x))))
 ;;   )


 ;; (defthm assoc-prep-lemma
 ;;   (implies (and (reducedwordp x)
 ;; 		 (reducedwordp y)
 ;; 		 (reducedwordp z))
 ;; 	    (equal (compose x (compose y z)) (word-fix (append x y z)))
 ;; 	    )

 ;;   :hints (("Subgoal 64"
 ;; 	    :use ((:instance wordfix-wordfix (x (append y z)))
 ;; 		  (:instance closure-lemma-assoc (x y) (y z))
 ;; 		  (:instance append-lemma)
 ;; 		  (:instance word-fix (w (append x (append y z))))
 ;; 		  (:instance word-fix (w (append x (word-fix (append y z)))))
 ;; 		  (:instance word-fix (w (append x y z))))
 ;; 	    ))
 ;;   )
   


 ;; (defthmd assoc-prop
 ;;   (implies (and (reducedwordp x)
 ;; 		 (reducedwordp y)
 ;; 		 (reducedwordp z))
 ;; 	    (equal (compose (compose x y) z) (compose x (compose y z))))
 ;;   :hints (("Goal"
 ;; 	    :in-theory (enable append)
 ;; 	    )
 ;; 	   ;; ("Subgoal 101"
 ;; 	   ;;  :use ((:instance character-listp-word-assoc (x y))
 ;; 	   ;; 	  (:instance character-listp-word-assoc (x z))
 ;; 	   ;; 	  (:instance word-fix=reducedwordp-assoc (x y))
 ;; 	   ;; 	  (:instance word-fix=reducedwordp-assoc (x z))
 ;; 	   ;; 	  (:instance wordfix-wordfix (x y))
 ;; 	   ;; 	  (:instance wordfix-wordfix (x z))
 ;; 	   ;; 	  )
 ;; 	   ;;  :in-theory (enable append)
 ;; 	   ;;  )
 ;; 	   )
 ;;   )
 
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

 ;; (defthmd assoc-prop
 ;;   (implies (and (reducedwordp x)
 ;; 		 (reducedwordp y)
 ;; 		 (reducedwordp z))
 ;; 	    (equal (compose (compose x y) z) (compose x (compose y z))))
 ;;   :hints (("Goal"
 ;; 	    :in-theory (enable append)
 ;; 	    ))
 ;;   )



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

























;;;;;;;associative property

(defthmd subgoal-lemma
  (implies (character-listp x)
	   (equal (append nil x) x))
  )

(defthmd subgoal-lemma1
  (implies (character-listp x)
	   (equal (append x nil) x))
  )



  :hints (("Goal"
	   :use ((:instance character-listp-word (x x))
		 (:instance character-listp-word (x y))
		 (:instance character-listp-word (x z))
		 (:instance word-fix=reducedwordp (x x))
		 (:instance word-fix=reducedwordp (x y))
		 (:instance word-fix=reducedwordp (x z))
		 (:instance subgoal-lemma (x x))
		 (:instance subgoal-lemma (x y))
		 (:instance subgoal-lemma (x z))
		 (:instance subgoal-lemma1 (x x))
		 (:instance subgoal-lemma1 (x y))
		 (:instance subgoal-lemma1 (x z))
		 (:instance reducedwordp=>weak-wordp (x x))
		 (:instance reducedwordp=>weak-wordp (x y))
		 (:instance reducedwordp=>weak-wordp (x z))
		 (:instance closure-lemma (x x) (y y))
		 (:instance closure-lemma (x x) (y z))
		 (:instance closure-lemma (x y) (y z))
		 (:instance weak-wordp-equivalent (x (append x y)))
		 (:instance weak-wordp-equivalent (x (append x z)))
		 (:instance weak-wordp-equivalent (x (append y z)))
		 (:instance word-fix=reducedwordp (x (word-fix (append x y))))
		 (:instance word-fix=reducedwordp (x (word-fix (append x z))))
		 (:instance word-fix=reducedwordp (x (word-fix (append y z))))
		 )
	   :in-theory (enable append)
	   ))
  )




	  ("Subgoal 101"
	   :use ((:instance character-listp-word (x y))
		 (:instance subgoal-lemma (x y))
		 (:instance word-fix=reducedwordp (x y))
		 (:instance closure-lemma (x y) (y z))
		 (:instance weak-wordp-equivalent (x (append y z)))
		 (:instance character-listp-word (x (word-fix (append y z))))
		 (:instance subgoal-lemma (x (word-fix (append y z))))
		 (:instance word-fix=reducedwordp (x (word-fix (append y z)))))
	   )
	  ("Subgoal 100"
	   :use ((:instance character-listp-word (x x))
		 (:instance character-listp-word (x y))
		 (:instance character-listp-word (x z))
		 (:instance word-fix=reducedwordp (x x))
		 (:instance subgoal-lemma (x x))
		 (:instance subgoal-lemma (x z))
		 (:instance subgoal-lemma1 (x x))
		 (:instance subgoal-lemma1 (x z))
		 
		 )
	   )
	  ("Subgoal 99"
	   :use ((:instance character-listp-word (x x))
		 (:instance character-listp-word (x y))
		 (:instance character-listp-word (x z))
		 (:instance word-fix=reducedwordp (x x))
		 (:instance word-fix=reducedwordp (x z))
		 (:instance subgoal-lemma (x x))
		 (:instance subgoal-lemma (x z))
		 (:instance subgoal-lemma1 (x x))
		 (:instance subgoal-lemma1 (x z))
		 )
	   :in-theory nil
	   )

	  ("Subgoal 98"
	   :use ((:instance character-listp-word (x x))
		 (:instance character-listp-word (x y))
		 (:instance character-listp-word (x z))
		 (:instance word-fix=reducedwordp (x x))
		 (:instance word-fix=reducedwordp (x z))
		 (:instance subgoal-lemma (x x))
		 (:instance subgoal-lemma (x z))
		 (:instance subgoal-lemma1 (x x))
		 (:instance subgoal-lemma1 (x z))
		 )
	   )
	  
	  
	  )
  )


































































































(defthmd weak-word-cdr
  (implies (weak-wordp x)
	   (weak-wordp (cdr x)))
  )

(defthmd test-lemma
  (implies (weak-wordp x)
	   (equal (word-fix (rev x)) (rev (word-fix x))))

  :hints (("Subgoal *1/21"
	   :use ((:instance weak-word-cdr (x x))
		 (:instance weak-wordp-equivalent (x (cdr x))))
	   ))
  
  )





(defthmd weak-word-cdr
  (implies (weak-wordp x)
	   (weak-wordp (cdr x)))
  )

(defthmd word-fix-lemma-10
  (implies (and (weak-wordp x)
		(member y (word-fix x))
		(word-fix x))
	   (and (or (equal y (wa))
		    (equal y (wa-inv))
		    (equal y (wb))
		    (equal y (wb-inv))
		    (equal y '()))
		(consp (word-fix x))))

  )



;; (defthmd reducedword-cdr
;;   (implies (reducedwordp x)
;; 	   (reducedwordp (cdr x)))
;;   )  

;; (defthmd word-fix-cdr
;;   (implies (reducedwordp x)
;; 	   (equal (word-fix (cdr x)) (cdr x)))
;;   :hints (("Goal"
;; 	   :use ((:instance reducedword-cdr (x x))
;; 		 (:instance word-fix=reducedwordp (x (cdr x))))
;; 	   ))
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

(defthmd car-lemma
  (implies (consp x)
	   (member (car x) x)
	   ))


(defthmd base-lemma
  (implies (and (weak-wordp x)
		(not (or (equal (car (word-fix x)) (wa))
			 (equal (car (word-fix x)) (wa-inv))
			 (equal (car (word-fix x)) (wb))
			 (equal (car (word-fix x)) (wb-inv)))))
		
	   (and (equal (car (word-fix x)) '())
		

  :hints (("Goal"
	   :use ((:instance word-fix-lemma-10 (x x) (y (CAR (word-fix x))))
		 
		 )
	   :do-not-induct t
	   ))
  )


(IMPLIES (AND (CONSP X)
              (WORD-FIX (CDR X))
              (NOT (EQUAL (CAR (WORD-FIX (CDR X))) #\a))
              (NOT (EQUAL (CAR (WORD-FIX (CDR X))) #\b))
              (NOT (EQUAL (CAR (WORD-FIX (CDR X))) #\c))
              (NOT (EQUAL (CAR (WORD-FIX (CDR X))) #\d))
              (IMPLIES (AND (WEAK-WORDP (CDR X))
                            (CHARACTERP Y)
                            (OR (EQUAL Y #\a)
                                (EQUAL Y #\b)
                                (EQUAL Y #\c)
                                (EQUAL Y #\d))
                            (EQUAL (WORD-FIX (CDR X)) NIL))
                       (EQUAL (WORD-FIX (APPEND (CDR X) (LIST Y)))
                              (LIST Y)))
              (WEAK-WORDP X)
              (CHARACTERP Y)
              (OR (EQUAL Y #\a)
                  (EQUAL Y #\b)
                  (EQUAL Y #\c)
                  (EQUAL Y #\d))
              (NOT (WORD-FIX X)))
         (EQUAL (WORD-FIX (APPEND X (LIST Y)))
                (LIST Y)))


(defthmd reducedwordp-word-inverse-lemma
  (implies (and (weak-wordp x)
		;(not (equal x '()))
		(characterp y)
		(or (equal y (wa))
		    (equal y (wa-inv))
		    (equal y (wb))
		    (equal y (wb-inv)))
		(equal (word-fix x) '()))
	   (equal (word-fix (append x (list y))) (list y)))
  :hints (("Goal"
	   :use ((:instance weak-word-cdr (x x))
		 (:instance word-fix=reducedwordp-1 (x x))
		 (:instance word-fix=reducedwordp (x x))
		 (:instance reducedword-cdr (x x))
		 (:instance word-fix-cdr (x x))
		 (:instance weak-word-= (x x)))
		 
	   )
	  ("Subgoal 11"
	   :use ((:instance word-fix-lemma-10 (x (cdr x)) (y (CAR (WORD-FIX (CDR X)))))
		 (:instance car-lemma (x (word-fix (cdr x)))))
	   )
	  )
  )

























(defthmd rev-word-inv-lemma1
  (implies (weak-wordp x)
	   (equal (nth n x)
		  (if (< (nfix n) (len x))
		      (cond ((equal (nth n (word-flip x)) (wb)) (wb-inv))
			    ((equal (nth n (word-flip x)) (wa)) (wa-inv))
			    ((equal (nth n (word-flip x)) (wb-inv)) (wb))
			    ((equal (nth n (word-flip x)) (wa-inv)) (wa))
			    ((equal x '()) nil))
		    nil
		    )
		  )
	   )
  :hints (("Goal"
	   :in-theory (enable nth)
	   ))
  )


(defthmd rev-word-inv-lemma2
  (implies (weak-wordp x)
	   (equal (nth n (word-flip x))
		  (if (< (nfix n) (len x))
		      (cond ((equal (nth n x) (wb)) (wb-inv))
			    ((equal (nth n x) (wa)) (wa-inv))
			    ((equal (nth n x) (wb-inv)) (wb))
			    ((equal (nth n x) (wa-inv)) (wa))
			    ((equal x '()) nil))
		    nil
		    )
		  )
	   )
  :hints (("Goal"
	   :in-theory (enable nth)
	   ))
  )

(defthmd len-lemma
  (implies (weak-wordp x)
	   (and (equal (len x) (len (rev x)))
		(equal (len x) (len (word-flip x)))
		(equal (len x) (len (rev (word-flip x))))
		(equal (len x) (len (word-inverse x))))))

(encapsulate
 ()

 (local (include-book "arithmetic-5/top" :dir :system))

 (defthmd rev-word-inv-lemma3
   (implies (weak-wordp x)
	    (equal (nth n x)
		   (if (< (nfix n) (len x))
		       (cond ((equal (nth (- (len x) (+ 1 (nfix n))) (word-inverse x)) (wb)) (wb-inv))
			     ((equal (nth (- (len x) (+ 1 (nfix n))) (word-inverse x)) (wa)) (wa-inv))
			     ((equal (nth (- (len x) (+ 1 (nfix n))) (word-inverse x)) (wb-inv)) (wb))
			     ((equal (nth (- (len x) (+ 1 (nfix n))) (word-inverse x)) (wa-inv)) (wa))
			     ((equal x '()) nil))
		     nil
		     )
		   )
	    )
   :hints (("Goal"
	    :use ((:instance rev-word-inv-lemma1)
		  (:instance rev-word-inv-lemma2)
		  (:instance len-lemma))
	    :in-theory (enable nth rev)
	    :do-not-induct t
	    ))
   )
 )





(defthmd inverse-compose=identity-lemma-1
  (implies (and (reducedwordp x)
		(equal x '()))
	   (and (equal (compose x (word-inverse x)) '())
		(iff (equal x '()) (equal (word-inverse x) '()))))
  )

(defthmd reduced-cdr
  (implies (reducedwordp x)
	   (reducedwordp (cdr x)))
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

(defthmd nth-lemma
  (implies (and (character-listp x)
		(not x)
		(characterp (nth n x)))
	   (and (>= n 0)
		(< n (len x))))
  )


(defthmd inverse-compose=identity
  (implies (reducedwordp x)
	   (equal (word-fix (append x (word-inverse x))) '()))
  :hints (("Goal"
	   :use (
		 (:instance word-fix=reducedwordp (x (word-inverse x)))
		 (:instance word-fix=reducedwordp (x x))
	   	 (:instance reducedwordp-word-inverse (x x))
	   	 (:instance len-lemma (x x))
		 (:instance inverse-compose=identity-lemma-1)
		 (:instance closure-prop (x x) (y (word-inverse x)))
		 (:instance reducedwordp=>weak-wordp (x x))
		 (:instance reducedwordp=>weak-wordp (x (word-inverse x)))
		 (:instance reducedwordp=>weak-wordp (x (word-flip x)))
		 (:instance rev-word-inv-lemma3)
		 (:instance reduced-cdr (x x))
		 (:instance reduced-cdr (x (word-inverse x)))
		 (:instance reduced-cdr (x (word-flip x)))
		 (:instance weak-word-= (x x))
		 (:instance weak-word-= (x (word-inverse x)))
		 (:instance weak-word-= (x (word-flip x)))
		 (:instance nth-lemma)
		 (:instance character-listp-word (x x))
		 (:instance character-listp-word (x (word-inverse x)))
		 (:instance character-listp-word (x (word-flip x)))
		 (:instance reduced-wordp-flip (x x))
		 (:instance weak-wordp-flip-1 (x x))
	   	 )
	   :in-theory (enable append nth rev)
	   :do-not-induct t
	   ))
  )

;; (encapsulate
;;  ()

;;  (local (include-book "arithmetic-5/top" :dir :system))

;;  (defthmd rev-word-inv-lemma4
;;    (implies (and (weak-wordp x)
;; 		 (integerp n))
;; 	    (equal (nth n (word-inverse x))
;; 		   (if (< (nfix n) (len x))
;; 		       (cond ((equal (nth (- (len x) (+ 1 (nfix n))) x) (wb)) (wb-inv))
;; 			     ((equal (nth (- (len x) (+ 1 (nfix n))) x) (wa)) (wa-inv))
;; 			     ((equal (nth (- (len x) (+ 1 (nfix n))) x) (wb-inv)) (wb))
;; 			     ((equal (nth (- (len x) (+ 1 (nfix n))) x) (wa-inv)) (wa))
;; 			     ((equal (word-inverse x) '()) nil))
;; 		     nil
;; 		     )
;; 		   )
;; 	    )
;;    :hints (("Goal"
;; 	    :use ((:instance rev-word-inv-lemma1)
;; 		  (:instance rev-word-inv-lemma2)
;; 		  (:instance rev-word-inv-lemma3)
;; 		  (:instance weak-wordp-inverse)
;; 		  (:instance len-lemma)
;; 		  (:instance character-listp-word (x x))
;; 		  (:instance character-listp-word (x (word-inverse x))))
;; 	    :in-theory (enable nth rev word-inverse nfix)
;; 	    :do-not-induct t
;; 	    ))
;;    )
;;  )






































;; (defthmd len=reduced=word-inverse
;;   (implies (reducedwordp x)
;; 	   (equal (len x) (len (word-inverse x))))
;;   )









(defthmd last-x-=car-rev
  (implies (character-listp x)
	   (equal (car (last x)) (car (rev x))))
  :hints (("Goal"
	   :in-theory (enable rev)
	   ))
  )



(defthmd rev-word-inv-lemma1
  (implies (and (character-listp x)
		(integerp n)
		(>= n 0)
		(< n (len x)))
	   (equal (nth n x) (nth (- (len x) (+ n 1)) (rev x))))
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
	   (and (equal (len x) (len (rev x)))
		(equal (len x) (len (word-flip x)))
		(equal (len x) (len (rev (word-flip x))))
		(equal (len x) (len (word-inverse x))))))
  

(defthmd rev-word-inv-lemma4
    (implies (and (weak-wordp x)
		  (integerp n)
		  (>= n 0)
		  (< n (len x)))
	     (cond ((equal (nth n x) (wb-inv)) (equal (nth (- (len x) (+ n 1)) (rev (word-flip x))) (wb)))
		   ((equal (nth n x) (wa-inv)) (equal (nth (- (len x) (+ n 1)) (rev (word-flip x))) (wa)))
		   ((equal (nth n x) (wb)) (equal (nth (- (len x) (+ n 1)) (rev (word-flip x))) (wb-inv)))
		   ((equal (nth n x) (wa)) (equal (nth (- (len x) (+ n 1)) (rev (word-flip x))) (wa-inv)))
		   ((equal x '()) (equal x '()))))
    :hints (("Goal"
	     :use ((:instance rev-word-inv-lemma2 (x x))
		   (:instance rev-word-inv-lemma1 (x (word-flip x)))
		   (:instance rev-word-inv-lemma3 (x x))) 
	     :do-not-induct t
	     ))
    )

(defthmd rev-word-inv-lemma5
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


(defthmd rev-word-inv-lemma6
  (implies (and (weak-wordp x)
		(< (nfix n) (len x)))
	   (cond ((equal (nth n x) (wb-inv)) (equal (nth (- (len x) (+ n 1)) (word-inverse x)) (wb)))
		 ((equal (nth n x) (wa-inv)) (equal (nth (- (len x) (+ n 1)) (word-inverse x)) (wa)))
		 ((equal (nth n x) (wb)) (equal (nth (- (len x) (+ n 1)) (word-inverse x)) (wb-inv)))
		 ((equal (nth n x) (wa)) (equal (nth (- (len x) (+ n 1)) (word-inverse x)) (wa-inv)))
		 ((equal x '()) (equal x '()))))
)

(defthmd reduced-cdr
  (implies (reducedwordp x)
	   (reducedwordp (cdr x)))
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


(defthmd inverse-compose=identity-lemma-1
  (implies (and (reducedwordp x)
		(equal x '()))
	   (and (equal (compose x (word-inverse x)) '())
		(iff (equal x '()) (equal (word-inverse x) '()))))
  )

(defthmd inverse-compose=identity
  (implies (reducedwordp x)
	   (equal (word-fix (append x (word-inverse x))) '()))
  :hints (("Goal"
	   :use (
		 (:instance word-fix=reducedwordp (x (word-inverse x)))
		 (:instance word-fix=reducedwordp (x x))
	   	 (:instance reducedwordp-word-inverse (x x))
	   	 (:instance len=reduced=word-inverse (x x))
		 (:instance inverse-compose=identity-lemma-1)
		 (:instance closure-prop (x x) (y (word-inverse x)))
		 (:instance reducedwordp=>weak-wordp (x x))
		 (:instance reducedwordp=>weak-wordp (x (word-inverse x)))
		 (:instance rev-word-inv-lemma)
		 (:instance reduced-cdr (x x))
		 (:instance reduced-cdr (x (word-inverse x)))
		 (:instance weak-word-= (x x))
		 (:instance weak-word-= (x (word-inverse x)))
	   	 )
	   :in-theory (enable append nth rev)
	   :do-not-induct t
	   )
	  ;; ("Subgoal 16"
	  ;;  :use (
	  ;; 	 (:instance reducedwordp-word-inverse (x x))
	  ;; 	 (:instance len=reduced=word-inverse (x x))
	  ;; 	 )
	  ;;  :expand (WORD-FIX (APPEND X (REV (WORD-FLIP X))))
	  ;;  )
	  )
  )


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

























(defthmd weak-wordp-rev
  (implies (weak-wordp x)
	   (weak-wordp (rev x)))
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

(defthmd inverse-compose=identity-lemma-1
  (implies (and (reducedwordp x)
		(reducedwordp (word-inverse x))
		(equal (word-inverse x) '()))
	   (equal (compose x (word-inverse x)) '()))
  )





;; (defthmd reducedwordp-rev-lemma
;;   (implies (and (reducedwordp x)
;; 		(equal x '()))
;; 	   (reducedwordp (rev x)))
;;   )

;; (defthmd reducedwordp-rev-lemma1
;;     (implies (and (reducedwordp x)
;; 		  (not (equal x '())))
;; 	     (not (equal (rev x) '()))))
  

;; (defthmd reducedwordp-rev
;;   (implies (and (reducedwordp x)
;; 		(integerp n)
;; 		(>= n 0)
;; 		(< n (len x)))
;; 		(reducedwordp (rev x)))
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
	   (equal (compose x y) (compose (rev (cdr (rev x))) (cdr y))))

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
	   (equal (rev (rev x)) x))
  )






(defthmd weak-wordp-rev
  (implies (weak-wordp x)
	   (weak-wordp (rev x)))
  )


(defthmd rev-word-inv-weak
  (implies (reducedwordp x)
	   (weak-wordp (rev (word-inverse x))))
  :hints (("Goal"
	   :use ((:instance weak-wordp-inverse)
		 (:instance weak-wordp-rev (x (rev x))))
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
		 (not (a-wordp (rev x)))
		 (NOT (EQUAL (CAR (REV X)) #\b))
		 (NOT (EQUAL (CAR (REV X)) #\c))
		 (NOT (EQUAL (CAR (REV X)) #\d))
		 (not (equal (rev x) '())))
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
	   (reducedwordp (rev x)))

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
	   (equal (car (last x)) (car (rev x))))
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
	   (reducedwordp (rev x)))
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
		 (:instance weak-word-= (x (rev x)))
		 (:instance weak-word-= (x x))
		 (:instance reduced-cdr)
		 (:instance weak-cdr(x x))
		 (:instance weak-cdr(x (rev x)))
		 (:instance reducedwordp=>weak-wordp (x x))
		 (:instance character-listp-word (x x))
		 (:instance character-listp-word (x (rev x)))
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
;; 	   (cond ((equal (car (last x)) (wb-inv)) (equal (car (rev (word-flip x))) (wb)))
;; 		 ((equal (car (last x)) (wa-inv)) (equal (car (rev (word-flip x))) (wa)))
;; 		 ((equal (car (last x)) (wa)) (equal (car (rev (word-flip x))) (wa-inv)))
;; 		 ((equal (car (last x)) (wb)) (equal (car (rev (word-flip x))) (wb-inv)))
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
;; 	   (reducedwordp (rev x)))
;;   :hints (("Goal"
;; 	   :use ((:instance reducedwordp=>weak-wordp)
;; 		 (:instance word-fix=reducedwordp)
;; 		 (:instance weak-wordp-rev)
;; 		 (:instance word-fix-lemma-1)
;; 		 (:instance word-fix=reducedwordp-1 (x x))
;; 		 (:instance word-fix=reducedwordp-1 (x (rev x))))
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
;; 	   (cond ((equal (car (last x)) (wb-inv)) (equal (car (rev (word-flip x))) (wb)))
;; 		 ((equal (car (last x)) (wa-inv)) (equal (car (rev (word-flip x))) (wa)))
;; 		 ((equal (car (last x)) (wa)) (equal (car (rev (word-flip x))) (wa-inv)))
;; 		 ((equal (car (last x)) (wb)) (equal (car (rev (word-flip x))) (wb-inv)))
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
  ;; 		 (:instance reduced-wordp-rev (x (word-inverse x))))
  ;; 	   :in-theory (enable rev)
  ;; 	   )))





;; (defthmd rev-word-inv-reduced-base
;;   (implies (and (endp x)
;; 		(reducedwordp x))
;; 	   (reducedwordp (rev x)))
;;   )


;; (skip-proofs
;;  (defthm rev-word-inv-reduced-induction
;;    (implies (and (reducedwordp x)
;; 		 (implies (and (not (endp x))
;; 			       (reducedwordp (cdr x)))
;; 			  (reducedwordp (rev (cdr x)))))
;; 		 (reducedwordp (rev x)))
;;    )
;;  )


;; (defthmd rev-word-inv-reduced
;;   (implies (reducedwordp x)
;; 	   (reducedwordp (rev x)))
;;   :hints (("Goal"
;; 	   :use ((:instance rev-word-inv-reduced-base)
;; 		 (:instance rev-word-inv-reduced-induction))
;; 	   ;:induct (reducedwordp (rev x))
	   
;; 	   ))
;;   )



;; (defthmd rev-word-inv-lemma-41
;;   (implies (and (weak-wordp x)
;; 		(equal (car (last x)) (wb-inv))
;; 		(equal y (word-inverse x)))
;; 	   (equal (car (rev y)) (wb)))
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
;; 	   (equal (car (rev y)) (wb-inv)))
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
;; 	   (equal (car (rev y)) (wa-inv)))
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
;; 	   (equal (car (rev y)) (wa)))
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
	   (member y (rev x)))
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
	   (equal (car (last x)) (car (rev x))))
  :hints (("goal"
	   :in-theory (enable rev)
	   ))
  )























(skip-proofs
 (defthm reduced-wordp-rev
   (implies (and (or (a-wordp x)
		     (b-wordp x)
		     (a-inv-wordp x)
		     (b-inv-wordp x))
		 (not (equal x '())))
	    (weak-wordp (rev x)))
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
	    ))
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
