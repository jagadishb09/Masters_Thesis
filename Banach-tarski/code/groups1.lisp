(include-book "std/strings/top" :dir :system)
(include-book "std/typed-lists/character-listp" :dir :system)
(include-book "std/typed-lists/string-listp" :dir :system)
;(include-book "std/strings/make-character-list" :dir :system)
(include-book "std/lists/top" :dir :system)

;; ()+()=()
;; (a b c d)

;; =a
;; =(a)

;; (a)


"abcd"

"a"

a
ainv
b
binv




(encapsulate
 ((wa() t)
  (wb() t)
  (wc() t)
  (wd() t)
  (wi() t))
 (local (defun wa() ""))
 (local (defun wb() ""))
 (local (defun wc() ""))
 (local (defun wd() ""))
 (local (defun wi() ""))

 (defthm length-strings
   (and 
	(= (length (wa))
	   (length (wb)))
	(= (length (wc))
	   (length (wd)))
	(= (length (wb))
	   (length (wc)))
	(= (length (wd))
	   (length (wi)))
	))

 (defthm stringp-strs
   (AND (stringp (wa))
	(stringp (wb))
	(stringp (wc))
	(stringp (wd))
	(stringp (wi))))


 (defthm identity-rules
   (AND (equal (string-append (wa) (wb)) (wi))
	(equal (string-append (wb) (wa)) (wi))
	(equal (string-append (wc) (wd)) (wi))
	(equal (string-append (wd) (wc)) (wi))
	(equal (string-append (wa) (wi)) (wa))
	(equal (string-append (wb) (wi)) (wb))
	(equal (string-append (wc) (wi)) (wc))
	(equal (string-append (wd) (wi)) (wd))
	(equal (string-append (wi) (wa)) (wa))
	(equal (string-append (wi) (wb)) (wb))
	(equal (string-append (wi) (wc)) (wc))
	(equal (string-append (wi) (wd)) (wd))
	(equal (string-append (wi) (wi)) (wi))
	))
 )

(defun wordp (x)
  (declare (xargs :guard t))
  (and
   (stringp x)
   (> (length x) 0)
   (if (= (length x) 1)
       (or (equal x (wa))
	   (equal x (wb))
	   (equal x (wc))
	   (equal x (wd))
	   (equal x (wi)))
     
     (let ((firstx (subseq x 0 1)) (reststr (subseq x 1 (length x))))
       (and (or (equal firstx (wa))
		(equal firstx (wb))
		(equal firstx (wc))
		(equal firstx (wd))
		(equal firstx (wi)))
	    (wordp reststr)))))
  )

(defun checkwordp(str letter)
					;(declare (xargs :guard t))
  (and (stringp str)
       (stringp letter)
       (> (length str) 0)
       (= (length letter) 1)

       (if (= (length str) 1)
	   (cond ((equal letter (wa)) (or (equal str (wa))
					  (equal str (wc))
					  (equal str (wd))))
		 ((equal letter (wb)) (or (equal str (wb))
					  (equal str (wc))
					  (equal str (wd))))
		 ((equal letter (wc)) (or (equal str (wa))
					  (equal str (wb))
					  (equal str (wc))))
		 ((equal letter (wd)) (or (equal str (wa))
					  (equal str (wb))
					  (equal str (wd)))))
	 (let ((firstx (subseq str 0 1)) (reststr (subseq str 1 (length str))))
	   (cond ((equal letter (wa)) (or (and (equal firstx (wa))
					       (checkwordp reststr firstx))
					  (and (equal firstx (wc))
					       (checkwordp reststr firstx))
					  (and (equal firstx (wd))
					       (checkwordp reststr firstx))))
		 ((equal letter (wb)) (or (and (equal firstx (wb))
					       (checkwordp reststr firstx))
					  (and (equal firstx (wc))
					       (checkwordp reststr firstx))
					  (and (equal firstx (wd))
					       (checkwordp reststr firstx))))
		 ((equal letter (wc)) (or (and (equal firstx (wa))
					       (checkwordp reststr firstx))
					  (and (equal firstx (wb))
					       (checkwordp reststr firstx))
					  (and (equal firstx (wc))
					       (checkwordp reststr firstx))))
		 ((equal letter (wd)) (or (and (equal firstx (wa))
					       (checkwordp reststr firstx))
					  (and (equal firstx (wb))
					       (checkwordp reststr firstx))
					  (and (equal firstx (wd))
					       (checkwordp reststr firstx)))))))))


(defun awordp(x)
  ;(declare (xargs :guard t))
  (and (stringp x)
       (> (length x) 0)
       (if (= (length x) 1)
	   (equal x (wa))
	 (let ((firstx (subseq x 0 1)) (reststr (subseq x 1 (length x))))
	   (and (equal firstx (wa))
		(checkwordp reststr (wa)))))))


(defun bwordp(x)
  ;(declare (xargs :guard t))
  (and (stringp x)
       (> (length x) 0)
       (if (= (length x) 1)
	   (equal x (wb))
	 (let ((firstx (subseq x 0 1)) (reststr (subseq x 1 (length x))))
	   (and (equal firstx (wb))
		(checkwordp reststr (wb)))))))


(defun cwordp(x)
  ;(declare (xargs :guard t))
  (and (stringp x)
       (> (length x) 0)
       (if (= (length x) 1)
	   (equal x (wc))
	 (let ((firstx (subseq x 0 1)) (reststr (subseq x 1 (length x))))
	   (and (equal firstx (wc))
		(checkwordp reststr (wc)))))))


(defun dwordp(x)
  ;(declare (xargs :guard t))
  (and (stringp x)
       (> (length x) 0)
       (if (= (length x) 1)
	   (equal x (wd))
	 (let ((firstx (subseq x 0 1)) (reststr (subseq x 1 (length x))))
	   (and (equal firstx (wd))
		(checkwordp reststr (wd)))))))


(defthm awordp-equivalent
  (implies (and (stringp a)
		(awordp a)
		(NOT (equal (WA) (WB)))
		(NOT (equal (WA) (WC)))
		(NOT (equal (WA) (WD)))
		(NOT (equal (WB) (WC)))
		(NOT (equal (WB) (WD)))
		(NOT (equal (WC) (WD)))
		(NOT (equal (WA) (WI)))
		(NOT (equal (WB) (WI)))
		(NOT (equal (WC) (WI)))
		(NOT (equal (WD) (WI)))
		(= (length (wa)) 1))
	   (and (not (bwordp a))
		(not (cwordp a))
		(not (dwordp a))
		(not (equal a (wi)))))
		
    :hints (("Goal"
	   :use ((:instance length-strings)
		 (:instance identity-rules)
		 )
	   ))
    )

(defthm bwordp-equivalent
  (implies (and (stringp b)
		(bwordp b)
		(NOT (equal (WA) (WB)))
		(NOT (equal (WA) (WC)))
		(NOT (equal (WA) (WD)))
		(NOT (equal (WB) (WC)))
		(NOT (equal (WB) (WD)))
		(NOT (equal (WC) (WD)))
		(NOT (equal (WA) (WI)))
		(NOT (equal (WB) (WI)))
		(NOT (equal (WC) (WI)))
		(NOT (equal (WD) (WI)))
		(= (length (wa)) 1))
	   (and (not (awordp b))
		(not (cwordp b))
		(not (dwordp b))
		(not (equal b (wi)))))
		
    :hints (("Goal"
	   :use ((:instance length-strings)
		 (:instance identity-rules)
		 )
	   ))
    )

(defthm cwordp-equivalent
  (implies (and (stringp c)
		(cwordp c)
		(NOT (equal (WA) (WB)))
		(NOT (equal (WA) (WC)))
		(NOT (equal (WA) (WD)))
		(NOT (equal (WB) (WC)))
		(NOT (equal (WB) (WD)))
		(NOT (equal (WC) (WD)))
		(NOT (equal (WA) (WI)))
		(NOT (equal (WB) (WI)))
		(NOT (equal (WC) (WI)))
		(NOT (equal (WD) (WI)))
		(= (length (wa)) 1))
	   (and (not (awordp c))
		(not (bwordp c))
		(not (dwordp c))
		(not (equal c (wi)))))
		
    :hints (("Goal"
	   :use ((:instance length-strings)
		 (:instance identity-rules)
		 )
	   ))
    )

(defthm dwordp-equivalent
  (implies (and (stringp d)
		(dwordp d)
		(NOT (equal (WA) (WB)))
		(NOT (equal (WA) (WC)))
		(NOT (equal (WA) (WD)))
		(NOT (equal (WB) (WC)))
		(NOT (equal (WB) (WD)))
		(NOT (equal (WC) (WD)))
		(NOT (equal (WA) (WI)))
		(NOT (equal (WB) (WI)))
		(NOT (equal (WC) (WI)))
		(NOT (equal (WD) (WI)))
		(= (length (wa)) 1))
	   (and (not (awordp d))
		(not (bwordp d))
		(not (cwordp d))
		(not (equal d (wi)))))
		
    :hints (("Goal"
	   :use ((:instance length-strings)
		 (:instance identity-rules)
		 )
	   ))
    )


(defun appendp=x (x)
  (if (and (stringp x) (> (length x) 0))
      (if (= (length x) 1)
	  x
	(string-append (subseq x 0 1) (appendp=x (subseq x 1 (length x)))))
    nil
    )
  )

(defthm appendp=x=x-lemma-1
  (implies (stringp x)
	   (integerp (length x)))
  )

(defthm appendp=x=x-lemma-2
  (implies (and (stringp x)
		(> (length x) 0)
		(not (equal (length x) 1)))
	   (> (length x) 1))
	   
  )

(defthm append=x=x-lemma-3
  (implies (and (stringp x)
		(> (length x) 1))

	   (equal (explode x) (cons (car (explode x)) (cdr (explode x)))))
  ;; :hints (("Goal"
  ;; 	    :in-theory (enable union-equal)
  ;; 	    ))

  )


(defthm append=x=x-lemma-4
  (implies (and (stringp x)
		(> (length x) 1))
	   (equal (car (explode x)) (car (explode (subseq x 0 1)))))
  :hints (("Goal"
  	   :use (:instance append=x=x-lemma-3)
  	   :in-theory (enable subseq subseq-list)
  	   ))

  )


;; (defthm appendp=x=x-lemma-3
;;    (implies (and (stringp x)
;; 		 (> (length x) 1))
;; 	    (equal (MAKE-CHARACTER-LIST (TAKE (+ -1 (LEN (EXPLODE X)))
;;                                                    (NTHCDR 1 (EXPLODE X)))) (cdr (explode x))))
;;   )

;(skip-proofs
 (defthm appendp=x=x-lemma-4
   (implies (and (stringp x)
		 (> (length x) 1))
	    (equal (string-append (subseq x 0 1) (subseq x 1 (length x))) x))
   :hints (("Goal"
	    :use (:instance append=x=x-lemma-3)
   	   ; :in-theory (enable subseq make-character-list subseq-list nthcdr take)
   	    ))
   )
 ;)


(defthm appendp=x=x
  (implies  (and (stringp x)
		 (> (length x) 0))
	    (equal (appendp=x x) x)
	    )
  :hints (("Goal"
	   :use ((:instance appendp=x=x-lemma-2)
		 (:instance appendp=x=x-lemma-3)

		  )
	   )
	  ("Subgoal *1/2.1"
	   :use ((:instance appendp=x=x-lemma-2)
		 (:instance appendp=x=x-lemma-3)

		 )))
  )


(defun wordp-x (x)
  (or (awordp x)
      (bwordp x)
      (cwordp x)
      (dwordp x)
      (equal x (wi)))
  )

































;; (defthm length-lemma
;;   (implies (and (stringp x)
;; 		(> (length x) 0))
;; 	   (< (length (subseq x 1 (length x))) (length x)))
;;   )




(defthm appendp=x=x-lemma-4
  (implies (and (stringp x)
		(= (length x) 1))
	   (= (length (string-append x x)) 2))
  )

(defthm appendp=x=x-lemma-5
  (implies (and (stringp x)
		(= (length x) 1))
	   (= (length (subseq (string-append x x) 0 1)) 1))
  )

(skip-proofs
 (defthm appendp=x=x-lemma-6
   (implies (and (stringp x)
		 (= (length x) 1))
	    (equal (subseq (string-append x x) 0 1) x))
   :hints (("Goal"
	    :use (
		  (:instance appendp=x=x-lemma-4)
		  (:instance appendp=x=x-lemma-5)
		  )
	    :in-theory (enable subseq subseq-list)
	    ))
   )
 )

(skip-proofs
 (defthm appendp=x=x-lemma-7
   (implies (and (stringp x)
		 (= (length x) 1))
	    (equal (subseq (string-append x x) 1 2) x))
   :hints (("Goal"
	    :use (
		  (:instance appendp=x=x-lemma-4)
		  (:instance appendp=x=x-lemma-5)
		  )
	    :in-theory (enable subseq subseq-list)
	    ))
   )
 )

(skip-proofs
 (defthm appendp=x=x-lemma-8
   (implies (and (stringp x)
		 (= (length x) 1)
		 (stringp y))
	    (equal (subseq (string-append x y) 0 1) x))
   :hints (("Goal"
	    :use (
		  (:instance appendp=x=x-lemma-4)
		  (:instance appendp=x=x-lemma-5)
		  )
	    :in-theory (enable subseq subseq-list)
	    ))
   )
 )

(skip-proofs
 (defthm appendp=x=x-lemma-9
   (implies (and (stringp x)
		 (= (length x) 1)
		 (= (subseq x 0 1) z)
		 (stringp z)
		 (stringp y))
	    (equal (subseq (string-append x y) 0 1) z))
   :hints (("Goal"
	    :use (
		  (:instance appendp=x=x-lemma-4)
		  (:instance appendp=x=x-lemma-5)
		  )
	    :in-theory (enable subseq subseq-list)
	    ))
   )
 )

;; (defthm appendp=x=x-lemma-7
;;   (implies (and (stringp x)
;; 		(= (length x) 1))
;; 	   (equal (explode x) (list (car (explode x))))
;; 	   )
;;   )

(defthm appendp=x=x-lemma-10
  (implies (and (stringp x)
		(stringp y))
	   (equal (implode (append (explode x) (explode y))) (string-append x y)))
  
  )

(skip-proofs
 (defthm appendp=x=x-lemma-11
   (implies (and (stringp x)
		 (= (length x) 1))
	    (equal (subseq x 0 1) x))
   :hints (("Goal"
	    :in-theory (enable subseq)
	    ))
   
   )
 )


(defthm closure-prop
  (implies (and (wordp-x x)
		(wordp-x y)
		(stringp x)
		(stringp y)
		(> (length x) 0)
		(> (length y) 0)
		(NOT (equal (WA) (WB)))
		(NOT (equal (WA) (WC)))
		(NOT (equal (WA) (WD)))
		(NOT (equal (WB) (WC)))
		(NOT (equal (WB) (WD)))
		(NOT (equal (WC) (WD)))
		(NOT (equal (WA) (WI)))
		(NOT (equal (WB) (WI)))
		(NOT (equal (WC) (WI)))
		(NOT (equal (WD) (WI)))
		(= (length (wa)) 1))
	   (and (wordp-x (string-append x y))))

  :hints (("Goal"
	   :use (
		 (:instance appendp=x=x (x x))
		 (:instance appendp=x=x (x y))
		 (:instance length-strings)
		 (:instance identity-rules)
		 (:instance appendp=x=x-lemma-6 (x (wd)))
		 (:instance appendp=x=x-lemma-7 (x (wd)))
		 (:instance appendp=x=x-lemma-8 (x x) (y (wc)))
		 (:instance appendp=x=x-lemma-9 (x x) (y (wd)) (z (wc)))
		 (:instance appendp=x=x-lemma-10 (x x) (y (wd)))
		 (:instance appendp=x=x-lemma-11)
		 

		 )
	   :in-theory (disable explode implode string-append)
	   )
	   )
		
  )

(defthm wordp-equivalent
  (implies (and (stringp x)
		(wordp x)
		(NOT (equal (WA) (WB)))
		(NOT (equal (WA) (WC)))
		(NOT (equal (WA) (WD)))
		(NOT (equal (WB) (WC)))
		(NOT (equal (WB) (WD)))
		(NOT (equal (WC) (WD)))
		(NOT (equal (WA) (WI)))
		(NOT (equal (WB) (WI)))
		(NOT (equal (WC) (WI)))
		(NOT (equal (WD) (WI)))
		(= (length (wa)) 1))

	   (or (awordp x)
	       (bwordp x)
	       (cwordp x)
	       (dwordp x)
	       (equal x (wi))))
  :hints (("Goal"
	   :use ((:instance length-strings)
		 (:instance identity-rules)
		 (:instance awordp-equivalent (a x))
		 (:instance bwordp-equivalent (b x))
		 (:instance cwordp-equivalent (c x))
		 (:instance dwordp-equivalent (d x))
		 (:instance appendp=x=x (x x))

		 )
	   :in-theory (enable appendp=x)
	   )
	  ))

(defthm abcdwordp-equivalent
  (implies (and (stringp a)
		(awordp a)
		(stringp b)
		(bwordp b)
		(stringp c)
		(cwordp c)
		(stringp d)
		(dwordp d)
		(NOT (equal (WA) (WB)))
		(NOT (equal (WA) (WC)))
		(NOT (equal (WA) (WD)))
		(NOT (equal (WB) (WC)))
		(NOT (equal (WB) (WD)))
		(NOT (equal (WC) (WD)))
		(NOT (equal (WA) (WI)))
		(NOT (equal (WB) (WI)))
		(NOT (equal (WC) (WI)))
		(NOT (equal (WD) (WI)))
		(= (length (wa)) 1))
	   
	   (and (not (equal a b))
		(not (equal a c))
		(not (equal a d))
		(not (equal a (wi)))
		(not (equal b c))
		(not (equal b d))
		(not (equal b (wi)))
		(not (equal c d))
		(not (equal c (wi)))
		(not (equal d (wi)))

		     ))
	   
  :hints (("Goal"
	   :use ((:instance length-strings)
		 (:instance identity-rules)
		 )
	   ))
  )




;; (defthm append=x-lemma
;;   (implies (stringp x)
;; 	   (= (acl2-count x) (len x)))
;;   )

(defun appendp=x (x)
  (if (stringp x)
      (if (>= (length x) 1)
	  (if (= (length x) 1)
	      x
	    (string-append (string (car (explode x))) (appendp=x (implode (cdr (explode x))))))
	x)
    nil))

(defthm stringp-lemma-1
  (implies (and (stringp x)
		(stringp-check x))
	   (equal (string-append (string (car (explode x))) (implode (cdr (explode x)))) x))
  )

(defthm stringp-lemma
  (implies (stringp x)
	   (equal  (appendp=x x) x))
  )


(defthm prop-2.1-1
  (implies (and (stringp x)
		(awordp x)
		(stringp y)
		(equal y (string-append (wb) x))
		(stringp a)
		(awordp a)
		(stringp c)
		(cwordp c)
		(stringp d)
		(dwordp d)
		(stringp-check x)
		(stringp-check a)
		(stringp-check c)
		(stringp-check d)
		(NOT (equal (WA) (WB)))
		(NOT (equal (WA) (WC)))
		(NOT (equal (WA) (WD)))
		(NOT (equal (WB) (WC)))
		(NOT (equal (WB) (WD)))
		(NOT (equal (WC) (WD)))
		(NOT (equal (WA) (WI)))
		(NOT (equal (WB) (WI)))
		(NOT (equal (WC) (WI)))
		(NOT (equal (WD) (WI)))
		(= (length (wa)) 1))
	   (or (equal y (wi))
	       (equal y a)
	       (equal y c)
	       (equal y d)))
  :hints (("Goal"
	   :use ((:instance length-strings)
		 (:instance identity-rules)
		; (:instance abcdwordp-equivalent)
		 )
	   ;:in-theory (disable abcdwordp-equivalent wordp-equivalent)
	   ))
  )

(defthm corollary-2.2-1
  (implies (and (stringp x)
		(wordp x)
		(stringp y)
		(awordp y)
		(stringp z)
		(bwordp z)
		(NOT (equal (WA) (WB)))
		(NOT (equal (WA) (WC)))
		(NOT (equal (WA) (WD)))
		(NOT (equal (WB) (WC)))
		(NOT (equal (WB) (WD)))
		(NOT (equal (WC) (WD)))
		(NOT (equal (WA) (WI)))
		(NOT (equal (WB) (WI)))
		(NOT (equal (WC) (WI)))
		(NOT (equal (WD) (WI)))
		(= (length (wa)) 1))
	   
	   (or (equal x (string-append (wb) y))
	       (equal x z)))

  :hints (("Goal"
	   :use ((:instance length-strings)
		 (:instance identity-rules)
		 (:instance prop-2.1)
		 )
	   ))
  
  )


(defthm wordp-equivalent
  (implies (and (stringp x)
		(wordp x)
		(NOT (equal (WA) (WB)))
		(NOT (equal (WA) (WC)))
		(NOT (equal (WA) (WD)))
		(NOT (equal (WB) (WC)))
		(NOT (equal (WB) (WD)))
		(NOT (equal (WC) (WD)))
		(NOT (equal (WA) (WI)))
		(NOT (equal (WB) (WI)))
		(NOT (equal (WC) (WI)))
		(NOT (equal (WD) (WI)))
		(= (length (wa)) 1)
		(= (length x) 1))
	   
	   (or (awordp x)
	       (bwordp x)
	       (cwordp x)
	       (dwordp x)
	       (equal x (wi))
	       ))
  :hints (("Goal"
	   :use ((:instance length-strings)
		 (:instance identity-rules)

		  )
	   ))
  )

(defthm prop-2.1
  (implies (and (stringp x)
		(awordp x)
		(NOT (equal (WA) (WB)))
		(NOT (equal (WA) (WC)))
		(NOT (equal (WA) (WD)))
		(NOT (equal (WB) (WC)))
		(NOT (equal (WB) (WD)))
		(NOT (equal (WC) (WD)))
		(NOT (equal (WA) (WI)))
		(NOT (equal (WB) (WI)))
		(NOT (equal (WC) (WI)))
		(NOT (equal (WD) (WI)))
		(= (length (wa)) 1))
	   (or (equal (string-append (wb) x) (wi))
	       (awordp (string-append (wb) x))
	       (cwordp (string-append (wb) x))
	       (dwordp (string-append (wb) x))))
  :hints (("Goal"
	   :use ((:instance length-strings)
		 (:instance identity-rules)
		  )
	   ))
  )

(defthm corollary-2.2-1
  (implies (and (stringp x)
		(wordp x)
		(stringp y)
		(awordp y)
		(stringp z)
		(bwordp z)
		(NOT (equal (WA) (WB)))
		(NOT (equal (WA) (WC)))
		(NOT (equal (WA) (WD)))
		(NOT (equal (WB) (WC)))
		(NOT (equal (WB) (WD)))
		(NOT (equal (WC) (WD)))
		(NOT (equal (WA) (WI)))
		(NOT (equal (WB) (WI)))
		(NOT (equal (WC) (WI)))
		(NOT (equal (WD) (WI)))
		(= (length (wa)) 1))
	   
	   (or (equal x (string-append (wb) y))
	       (equal x z)))

  :hints (("Goal"
	   :use ((:instance length-strings)
		 (:instance identity-rules)
		 (:instance prop-2.1)
		 )
	   ))
  
  )
