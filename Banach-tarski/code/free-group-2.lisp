
(include-book "free-group-1")

(defthmd weak-cons-car-cdr
  (implies (and (character-listp x)
		(not (atom x)))
	   (equal (cons (car x) (cdr x)) x))
  )

(defthmd n-mod3-a-r-wa
  (implies (and (weak-wordp w)
		(equal (car w) (wa))
		(equal x (acl2-sqrt 2)))
	   (equal (n-mod3 w x)
		  (cons 0 (cons (mod (- (car (cdr (n-mod3 (cdr w) x)))  (car (cdr (cdr (n-mod3 (cdr w) x))))) 3)
				(cons (mod (- (car (cdr (cdr (n-mod3 (cdr w) x)))) (car (cdr (n-mod3 (cdr w) x)))) 3) nil)))

		  )
	   )
  :hints (("Goal"
	   :use (
		 (:instance n-mod3-a-r (w (cdr w)) (x x))
		 (:instance weak-word-cdr (x w))
		 (:instance weak-cons-car-cdr (x w))
		 (:instance character-listp-word (x w))
		 )
	   :in-theory (disable n-mod3 weak-wordp acl2-sqrt)
	   :do-not-induct t
	   ))
  
  )

(defthmd n-mod3-a-inv-r-wa-inv
  (implies (and (weak-wordp w)
		(equal (car w) (wa-inv))
		(equal x (acl2-sqrt 2)))
	   (equal (n-mod3 w x)
		  (cons 0 (cons (mod (+ (car (cdr (n-mod3 (cdr w) x)))  (car (cdr (cdr (n-mod3 (cdr w) x))))) 3)
				(cons (mod (+ (car (cdr (cdr (n-mod3 (cdr w) x)))) (car (cdr (n-mod3 (cdr w) x)))) 3) nil)))

		  )
	   )
  :hints (("Goal"
	   :use (
		 (:instance n-mod3-a-inv-r (w (cdr w)) (x x))
		 (:instance weak-word-cdr (x w))
		 (:instance weak-cons-car-cdr (x w))
		 (:instance character-listp-word (x w))
		 )
	   :in-theory (disable n-mod3 weak-wordp acl2-sqrt)
	   :do-not-induct t
	   ))
  )

(defthmd n-mod3-b-r-wb
  (implies (and (weak-wordp w)
		(equal (car w) (wb))
		(equal x (acl2-sqrt 2)))
	   (equal (n-mod3 w x)
		  (cons (mod (+ (car (n-mod3 (cdr w) x))  (car (cdr (n-mod3 (cdr w) x)))) 3)
			(cons (mod (+ (car (cdr (n-mod3 (cdr w) x))) (car (n-mod3 (cdr w) x))) 3) (cons 0 nil))))
	   )
  :hints (("Goal"
	   :use (
		 (:instance n-mod3-b-r (w (cdr w)) (x x))
		 (:instance weak-word-cdr (x w))
		 (:instance weak-cons-car-cdr (x w))
		 (:instance character-listp-word (x w))
		 )
	   :in-theory (disable n-mod3 weak-wordp acl2-sqrt)
	   :do-not-induct t
	   ))
  )

(defthmd n-mod3-b-inv-r-wb-inv
  (implies (and (weak-wordp w)
		(equal (car w) (wb-inv))
		(equal x (acl2-sqrt 2)))
	   (equal (n-mod3 w x)
		  (cons (mod (- (car (n-mod3 (cdr w) x))  (car (cdr (n-mod3 (cdr w) x)))) 3)
			(cons (mod (- (car (cdr (n-mod3 (cdr w) x))) (car (n-mod3 (cdr w) x))) 3) (cons 0 nil))))
	   )
  :hints (("Goal"
	   :use (
		 (:instance n-mod3-b-inv-r (w (cdr w)) (x x))
		 (:instance weak-word-cdr (x w))
		 (:instance weak-cons-car-cdr (x w))
		 (:instance character-listp-word (x w))
		 )
	   :in-theory (disable n-mod3 weak-wordp acl2-sqrt)
	   :do-not-induct t
	   ))
  )

(defthmd reducedword-cdr
  (implies (reducedwordp x)
	   (reducedwordp (cdr x)))
  )

(defthmd n-mod3-red-lemma-final
  (implies (and (reducedwordp w)
		(equal x (acl2-sqrt 2))
		(> (len w) 0))
	   (cond ((equal (car w) (wa))
		  (or (equal (n-mod3 w x) '(0 1 2))
		      (equal (n-mod3 w x) '(0 2 1)))
		  )
		 ((equal (car w) (wa-inv))
		  (or (equal (n-mod3 w x) '(0 1 1))
		      (equal (n-mod3 w x) '(0 2 2))))
		 ((equal (car w) (wb))
		  (or (equal (n-mod3 w x) '(1 1 0))
		      (equal (n-mod3 w x) '(2 2 0))))
		 ((equal (car w) (wb-inv))
		  (or (equal (n-mod3 w x) '(2 1 0))
		      (equal (n-mod3 w x) '(1 2 0))))
		 )
	   )

  :hints (("Subgoal *1/1"
	   :cases ((> (len (cdr w)) 0)
		   (= (len (cdr w)) 0))
	   )
	  ("Subgoal *1/1.1"
	   :cases ((equal (car w) (wa))
		   (equal (car w) (wa-inv))
		   (equal (car w) (wb))
		   (equal (car w) (wb-inv))
		   )
	   :use ((:instance sqrt-2-lemmas)
		 (:instance n-mod3-nil)
		 (:instance reducedwordp=>weak-wordp (x w))
		 (:instance n-mod3-a-r-wa (w w) (x x))
		 (:instance n-mod3-a-inv-r-wa-inv (w w) (x x))
		 (:instance n-mod3-b-r-wb (w w) (x x))
		 (:instance n-mod3-b-inv-r-wb-inv (w w) (x x))
		 )
	   :in-theory (disable acl2-sqrt m-* n-mod3)
	   )

	  ("Subgoal *1/1.2"
	   :cases ((equal (car w) (wa))
		   (equal (car w) (wa-inv))
		   (equal (car w) (wb))
		   (equal (car w) (wb-inv))
		   )
	   :use (:instance reducedword-cdr (x w))
	   :in-theory (disable n-mod3 acl2-sqrt)
	   )
	  ("Subgoal *1/1.2.1"
	   :cases ((equal (car (cdr w)) (wa))
		   (equal (car (cdr w)) (wa-inv))
		   (equal (car (cdr w)) (wb))
		   (equal (car (cdr w)) (wb-inv))
		   )
	   :use ((:instance reducedwordp=>weak-wordp (x w))
		 (:instance n-mod3-b-inv-r-wb-inv (w w) (x x)))
	   )
	  ("Subgoal *1/1.2.2"
	   :cases ((equal (car (cdr w)) (wa))
		   (equal (car (cdr w)) (wa-inv))
		   (equal (car (cdr w)) (wb))
		   (equal (car (cdr w)) (wb-inv))
		   )
	   :use ((:instance reducedwordp=>weak-wordp (x w))
		 (:instance n-mod3-b-r-wb (w w) (x x)))
	   )
	  ("Subgoal *1/1.2.3"
	   :cases ((equal (car (cdr w)) (wa))
		   (equal (car (cdr w)) (wa-inv))
		   (equal (car (cdr w)) (wb))
		   (equal (car (cdr w)) (wb-inv))
		   )
	   :use ((:instance reducedwordp=>weak-wordp (x w))
		 (:instance n-mod3-a-inv-r-wa-inv (w w) (x x)))
	   )
	  ("Subgoal *1/1.2.4"
	   :cases ((equal (car (cdr w)) (wa))
		   (equal (car (cdr w)) (wa-inv))
		   (equal (car (cdr w)) (wb))
		   (equal (car (cdr w)) (wb-inv))
		   )
	   :use ((:instance reducedwordp=>weak-wordp (x w))
		 (:instance n-mod3-a-r-wa (w w) (x x)))
	   )
	  )
  )




;; (defun aawordp (w n)
;;   (cond ((integerp n) (cond ((zp n) t)
;; 			    (t (and (equal (car w) #\a) (aawordp (cdr w) (- n 1))))))
;; 	((atom n) t)))

;; (defun a-inva-invwordp (w n)
;;   (cond ((integerp n) (cond ((zp n) t)
;; 			    (t (and (equal (car w) #\b) (a-inva-invwordp (cdr w) (- n 1))))))
;; 	((atom n) t)))

;; (defun bbwordp (w n)
;;   (cond ((integerp n) (cond ((zp n) t)
;; 			    (t (and (equal (car w) #\c) (bbwordp (cdr w) (- n 1))))))
;; 	((atom n) t)))

;; (defun b-invb-invwordp (w n)
;;   (cond ((integerp n) (cond ((zp n) t)
;; 			    (t (and (equal (car w) #\d) (b-invb-invwordp (cdr w) (- n 1))))))
;; 	((atom n) t)))

;; (defun r-eq (w)
;;   (if (atom w)
;;       nil
;;     (let ((powers (r-eq (cdr w))))
;;       (let ((cadw (car (cdr w)))
;; 	    (cap (car powers))
;; 	    (caw (car w)))
;; 	(cond ((atom (cdr w)) '(1))
;; 	      ((equal caw cadw) (update-nth 0 (+ cap 1) powers))
;; 	      (t (append '(1) powers)))))))

;; ;; (defun reducedword-eq (w)
;; ;;   (if (evenp (len (r-eq w)))
;; ;;       (r-eq w)
;; ;;     (append (r-eq w) '(0)))
;; ;;   )

;; (defthmd red-eq-lemma1-1
;;   (implies (and (reducedwordp w)
;; 		(> (len w) 0))
;; 	   (integer-listp (r-eq w)))
;;   )

;; ;; (defthmd red-eq-lemma1-2
;; ;;   (implies (and (integer-listp a)
;; ;; 		(integer-listp b))
;; ;; 	   (integer-listp (append a b)))
;; ;;   )

;; ;; (defthmd red-eq-lemma1
;; ;;   (implies (and (reducedwordp w)
;; ;; 		(> (len w) 0))
;; ;; 	   (integer-listp (reducedword-eq w)))

;; ;;   :hints (("Goal"
;; ;; 	   :cases ((evenp (len (r-eq w)))
;; ;; 		   (oddp (len (r-eq w))))
;; ;; 	   :use (:instance red-eq-lemma1-1 (w w))
;; ;; 	   :do-not-induct t
;; ;; 	   )
;; ;; 	  ("Subgoal 1"
;; ;; 	   :use (:instance red-eq-lemma1-2 (a (r-eq w)) (b '(0)))
;; ;; 	   :do-not-induct t
;; ;; 	   )
;; ;; 	  )
;; ;;   )

;; (defthmd red-eq-lemma2
;;   (implies (and (reducedwordp w)
;; 		(atom (r-eq w)))
;; 	   (atom w))
;;   )

;; ;; atom w => atom powers
;; ;; powers >0
;; ;; remove reducedword-eq
;; ;; n-mod3 for a-n b-n1 n1>=0
;; ;; n-mod3 aawordp n

;; (defthmd red-eq-lemma3-1
;;   (implies (and (integer-listp a)
;; 		(oddp (len a)))
;; 	   (evenp (len (append a '(0)))))
;;   )

;; ;; (defthmd red-eq-lemma3
;; ;;   (implies (reducedwordp w)
;; ;; 	   (evenp (len (reducedword-eq w))))
;; ;;   :hints (("Goal"
;; ;; 	   :cases ((evenp (len (r-eq w)))
;; ;; 		   (oddp (len (r-eq w))))
;; ;; 	   :use (:instance red-eq-lemma1-1 (w w))
;; ;; 	   :do-not-induct t
;; ;; 	   )
;; ;; 	  ("Subgoal 1"
;; ;; 	   :use ((:instance red-eq-lemma1-1 (w w))
;; ;; 		 (:instance red-eq-lemma3-1 (a (r-eq w))))
;; ;; 	   :do-not-induct t
;; ;; 	   )
;; ;; 	  )
;; ;;   )

;; ;; (defthmd red-eq-lemma4
;; ;;   (implies (and (reducedwordp w)
;; ;; 		(> (len w) 0)
;; ;; 		(> n 0)
;; ;; 		(< n (len (r-eq w))))
;; ;; 	   (> (nth n (r-eq w)) 0))
;; ;;   :hints (("Goal"
;; ;; 	   :in-theory (disable reducedwordp)
;; ;; 	   ))
;; ;;   )

;; (defun aa-invstartp (w powers)
;;   (cond ((atom powers) t)
;; 	(t (or (and (aawordp w (car powers)) (or (and (bbwordp (nthcdr (car powers) w) (cadr powers))
;; 						      (if (cddr powers)
;; 							  (aa-invstartp  (nthcdr (+ (caddr powers) (car powers)) w) (cddr powers))
;; 							t))
;; 						 (and (b-invb-invwordp (nthcdr (car powers) w) (cadr powers))
;; 						      (if (cddr powers)
;; 							  (aa-invstartp (nthcdr (+ (caddr powers) (car powers)) w) (cddr powers))
;; 							t))))
;; 	       (and (a-inva-invwordp w (car powers)) (or (and (bbwordp (nthcdr (car powers) w) (cadr powers))
;; 							      (if (cddr powers)
;; 								  (aa-invstartp (nthcdr (+ (caddr powers) (car powers)) w) (cddr powers))
;; 								t))
;; 							 (and (b-invb-invwordp (nthcdr (car powers) w) (cadr powers))
;; 							      (if (cddr powers)
;; 								  (aa-invstartp (nthcdr (+ (caddr powers) (car powers)) w) (cddr powers))
;; 								t))))
;; 	       ))
;; 	))

;; (defun bb-invstartp (w powers)
;;   (cond ((atom powers) t)
;; 	(t (or (and (bbwordp w (car powers)) (or (and (aawordp (nthcdr (car powers) w) (cadr powers))
;; 						      (if (cddr powers)
;; 							  (bb-invstartp (nthcdr (+ (caddr powers) (car powers)) w)
;; 										(cddr powers))
;; 							t))
;; 						 (and (a-inva-invwordp (nthcdr (car powers) w) (cadr powers))
;; 						      (if (cddr powers)
;; 							  (bb-invstartp (nthcdr (+ (caddr powers) (car powers)) w) (cddr powers))
;; 							t))))
;; 	       (and (b-invb-invwordp w (car powers)) (or (and (aawordp (nthcdr (car powers) w) (cadr powers))
;; 							      (if (cddr powers)
;; 								  (bb-invstartp (nthcdr (+ (caddr powers)
;; 											   (car powers)) w)
;; 										(cddr powers))
;; 								t))
;; 							 (and (a-inva-invwordp (nthcdr (car powers) w)
;; 									       (cadr powers))
;; 							      (if (cddr powers)
;; 								  (bb-invstartp (nthcdr (+ (caddr powers)
;; 											   (car powers)) w)
;; 										(cddr powers))
;; 								t))))
;; 	       ))
;; 	))


;; (defthmd aa-invstartp-lemma1
;;   (implies (and (reducedwordp w)
;; 		(aa-invstartp w (r-eq w))
;; 		(not (atom w)))
;; 	   (or (equal (car w) (wa))
;; 	       (equal (car w) (wa-inv))))
;;   :hints (("Goal"
;; 	   :cases ((equal (car w) (wa))
;; 		   (equal (car w) (wa-inv))
;; 		   (equal (car w) (wb))
;; 		   (equal (car w) (wb-inv))
;; 		   )
;; 	   ))
;;   )


;; (defthmd reducedwordp-eq-lemma1
;;   (implies (and (reducedwordp w)
;; 		(> (len w) 0))
;; 	   (or (bb-invstartp w (r-eq w))
;; 	       (aa-invstartp w (r-eq w)))
;; 	   )
;;   :hints ((
;;   )

;; (Let ((w '(#\c #\a #\c #\a)))
;;      (implies (and (reducedwordp w)
;; 		(> (len w) 0))
;; 	      (bb-invstartp w (r-eq w)))
;; 	   )

