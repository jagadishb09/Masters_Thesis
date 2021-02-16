
(in-package "ACL2")

(include-book "workshops/2003/cowles-gamboa-van-baalen_matrix/support/matalg" :dir :system)
(include-book "free-group")

(defun r3-matrixp (m)
  (and (array2p '$arg1 m)
       (equal (r m) (c m))
       (equal (r m) 3)
       (realp (aref2 '$arg1 m 0 0))
       (realp (aref2 '$arg1 m 0 1))
       (realp (aref2 '$arg1 m 0 2))
       (realp (aref2 '$arg1 m 1 0))
       (realp (aref2 '$arg1 m 1 1))
       (realp (aref2 '$arg1 m 1 2))
       (realp (aref2 '$arg1 m 2 0))
       (realp (aref2 '$arg1 m 2 1))
       (realp (aref2 '$arg1 m 2 2))
       )
  )

(defun r3-m-determinant (m)
  (declare (xargs :guard (and (array2p '$arg1 m)
			      (equal (r m) (c m))
			      (equal (r m) 3))
		  :verify-guards nil))
  (+ (* (aref2 '$arg1 m 0 0) (- (* (aref2 '$arg1 m 1 1) (aref2 '$arg1 m 2 2))
				(* (aref2 '$arg1 m 1 2) (aref2 '$arg1 m 2 1))))
     (* (- (aref2 '$arg1 m 0 1)) (- (* (aref2 '$arg1 m 1 0) (aref2 '$arg1 m 2 2))
				    (* (aref2 '$arg1 m 1 2) (aref2 '$arg1 m 2 0))))
     (* (aref2 '$arg1 m 0 2) (- (* (aref2 '$arg1 m 1 0) (aref2 '$arg1 m 2 1))
				(* (aref2 '$arg1 m 1 1) (aref2 '$arg1 m 2 0))))
     )
  )


(defun r3-m-inverse (m)
  `((:header :dimensions (3 3)
	     :maximum-length 10)
    ((0 . 0) . ,(/ (- (* (aref2 '$arg1 m 2 2) (aref2 '$arg1 m 3 3))
		      (* (aref2 '$arg1 m 3 2) (aref2 '$arg1 m 2 3)))
		   (determinant m)))
    ((0 . 1) . ,(/ (- (* (aref2 '$arg1 m 1 3) (aref2 '$arg1 m 3 2))
		      (* (aref2 '$arg1 m 3 3) (aref2 '$arg1 m 1 2)))
		   (determinant m)))
    ((0 . 2) . ,(/ (- (* (aref2 '$arg1 m 1 2) (aref2 '$arg1 m 2 3))
		      (* (aref2 '$arg1 m 2 2) (aref2 '$arg1 m 1 3)))
		   (determinant m)))
    ((1 . 0) . ,(/ (- (* (aref2 '$arg1 m 2 3) (aref2 '$arg1 m 3 1))
		      (* (aref2 '$arg1 m 3 3) (aref2 '$arg1 m 2 1)))
		   (determinant m)))
    ((1 . 1) . ,(/ (- (* (aref2 '$arg1 m 1 1) (aref2 '$arg1 m 3 3))
		      (* (aref2 '$arg1 m 3 1) (aref2 '$arg1 m 1 3)))
		   (determinant m)))
    ((1 . 2) . ,(/ (- (* (aref2 '$arg1 m 1 3) (aref2 '$arg1 m 2 1))
		      (* (aref2 '$arg1 m 2 3) (aref2 '$arg1 m 1 1)))
		   (determinant m)))
    ((2 . 0) . ,(/ (- (* (aref2 '$arg1 m 2 1) (aref2 '$arg1 m 3 2))
		      (* (aref2 '$arg1 m 3 1) (aref2 '$arg1 m 2 2)))
		   (determinant m)))
    ((2 . 1) . ,(/ (- (* (aref2 '$arg1 m 1 2) (aref2 '$arg1 m 3 1))
		      (* (aref2 '$arg1 m 3 2) (aref2 '$arg1 m 1 1)))
		   (determinant m)))
    ((2 . 2) . ,(/ (- (* (aref2 '$arg1 m 1 1) (aref2 '$arg1 m 2 2))
		      (* (aref2 '$arg1 m 2 1) (aref2 '$arg1 m 1 2)))
		   (determinant m)))
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

(defthmd m-*-m-m-inverse
  (implies (and (r3-matrixp m)
		(not (= (determinant m) 0)))
	   (m-= (m-* m (r3-m-inverse m)) (id-rotation)))
  :hints (("Goal"
	   :use ((:instance array2p-alist2p (name '$arg1) (L m))
		 (:instance aref2-m-* (m1 m) (m2 (r3-m-inverse m)) (name '$arg1))
		 )
	   :in-theory (e/d (alist2p m-= m-=-row-1 m-=-row) (aref2))
	   )
	  )
  )

(defthmd m-*-m-inverse-m
  (implies (and (r3-matrixp m)
		(not (= (determinant m) 0)))
	   (m-= (m-* (r3-m-inverse m) m) (id-rotation)))
  )
  



;; (encapsulate
;;  ()
 
;;  ;(local (include-book "arithmetic-5/top" :dir :system))

;;  (local
;;   (defthm compress21-lemma
;;     (equal (compress21 name l n i j default)
;;  	   (if (zp (- i n)) nil
;;  	     (append (compress211 name l n 0 j default)
;;  		     (compress21 name l (+ n 1) i j default))))
;;     :hints (("Goal"
;;  	     :in-theory (enable compress21 compress211)
;;  	     ))		 
;;     )
;;   )

;;  (defthm dimen-lemma
;;   (implies (and (equal (r m) (c m))
;; 		(equal (r m) 3))
;; 	   (and (equal (CAR (DIMENSIONS '$arg1 M)) 3)
;; 		(equal (CAdR (DIMENSIONS '$arg1 M)) 3)
;; 		(equal (CAR (DIMENSIONS '$arg2 M)) 3)
;; 		(equal (CAdR (DIMENSIONS '$arg2 M)) 3)))
;;   :hints (("Goal"
;; 	   :in-theory (enable dimensions header)
;; 	   ))
;;   )
;;  ;; (local
;;  ;;  (defthm m-=-row-1-lemma
;;  ;;    (equal (m-=-row-1 m1 m2 m n)
;;  ;; 	   (if (zp m)
;;  ;; 	       (m-=-row m1 m2 0 n)
;;  ;; 	     (and (m-=-row m1 m2 m n)
;;  ;; 		  (m-=-row-1 m1 m2 (- m 1) n))))
;;  ;;    )
;;  ;;  )

;;  ;; (local
;;  ;;  (defthm m-=-row-lemma
;;  ;;    (equal (m-=-row m1 m2 m n)
;;  ;; 	   (if (zp n)
;;  ;; 	       (equal (fix (aref2 '$arg1 M1 m 0))
;;  ;; 		      (fix (aref2 '$arg2 M2 m 0)))
;;  ;; 	     (and (equal (fix (aref2 '$arg1 M1 m n))
;;  ;; 			 (fix (aref2 '$arg2 M2 m n)))
;;  ;; 		  (m-=-row M1 M2 m (- n 1)))))
;;  ;;    )
;;  ;;  )

;;  (defthm det-a*b=
;;    (implies (and (array2p '$arg1 m1)
;; 		 (equal (r m1) (c m1))
;; 		 (equal (r m1) 3)
;; 		 (array2p '$arg1 m2)
;; 		 (equal (r m2) (c m2))
;; 		 (equal (r m2) 3)
;; 		 (realp (aref2 '$arg1 m 0 0))
;; 		 (realp (aref2 '$arg1 m1 0 1))
;; 		 (realp (aref2 '$arg1 m1 0 2))
;; 		 (realp (aref2 '$arg1 m1 1 0))
;; 		 (realp (aref2 '$arg1 m1 1 1))
;; 		 (realp (aref2 '$arg1 m1 1 2))
;; 		 (realp (aref2 '$arg1 m1 2 0))
;; 		 (realp (aref2 '$arg1 m1 2 1))
;; 		 (realp (aref2 '$arg1 m1 2 2))
;; 		 (realp (aref2 '$arg1 m2 0 0))
;; 		 (realp (aref2 '$arg1 m2 0 1))
;; 		 (realp (aref2 '$arg1 m2 0 2))
;; 		 (realp (aref2 '$arg1 m2 1 0))
;; 		 (realp (aref2 '$arg1 m2 1 1))
;; 		 (realp (aref2 '$arg1 m2 1 2))
;; 		 (realp (aref2 '$arg1 m2 2 0))
;; 		 (realp (aref2 '$arg1 m2 2 1))
;; 		 (realp (aref2 '$arg1 m2 2 2)))
;; 	    (= (* (r3-m-determinant m1) (r3-m-determinant m2))
;; 	       (r3-m-determinant (m-* m1 m2))))
;;    :hints (("Goal"
;; 	    :in-theory (e/d (m-* compress2 M-BINARY-*-ROW-1 m-binary-*-row array2p) (aref2))
;; 	    :do-not-induct t
;; 	    )
;; 	   ("Subgoal 2"
;; 	    ;:in-theory nil
;; 	    )
;; 	   )
;;    )
;;  )


;; ;; (defun r3-m-inverse (m)
;; ;;   (declare (xargs :guard (array2p '$arg1 m)
;; ;; 		  :verify-guards nil))

;; ;;   )

;; (defun r3-rotationp (m)
;;   (and (array2p '$arg1 m)
;;        (equal (r m) (c m))
;;        (equal (r m) 3)
;;        (= (r3-m-determinant m) 1)
;;        (m-= (m-trans m) (m-/ m))
;;        (realp (aref2 '$arg1 m 0 0))
;;        (realp (aref2 '$arg1 m 0 1))
;;        (realp (aref2 '$arg1 m 0 2))
;;        (realp (aref2 '$arg1 m 1 0))
;;        (realp (aref2 '$arg1 m 1 1))
;;        (realp (aref2 '$arg1 m 1 2))
;;        (realp (aref2 '$arg1 m 2 0))
;;        (realp (aref2 '$arg1 m 2 1))
;;        (realp (aref2 '$arg1 m 2 2))
;;        )
;;   )

;; (defthm dimen-lemma
;;   (implies (and (equal (r m) (c m))
;; 		(equal (r m) 3))
;; 	   (and (equal (CAR (DIMENSIONS '$C M)) 3)
;; 		(equal (CAdR (DIMENSIONS '$C M)) 3)))
;;   :hints (("Goal"
;; 	   :in-theory (enable dimensions header)
;; 	   ))
;;   )

;; (defthm det-ma-det=1p
;;   (implies (and (mat-det=1p m)
;; 		(equal (aref2 '$arg1 m 0 0) a)
;; 		(equal (aref2 '$arg1 m 0 1) b)
;; 		(equal (aref2 '$arg1 m 0 2) c)
;; 		(equal (aref2 '$arg1 m 1 0) d)
;; 		(equal (aref2 '$arg1 m 1 1) e)
;; 		(equal (aref2 '$arg1 m 1 2) f)
;; 		(equal (aref2 '$arg1 m 2 0) g)
;; 		(equal (aref2 '$arg1 m 2 1) h)
;; 		(equal (aref2 '$arg1 m 2 2) i)
;; 		)
;; 	   (equal (determinant m) (+ (* a (- (* e i) (* f h)))
;; 				     (* (- b) (- (* d i) (* f g)))
;; 				     (* c (- (* d h) (* e g))))))
;;   :hints (
;; 	  ("Goal"
;; 	   :in-theory (e/d (determinant-inverse-loop) (aref2 dimensions compress2 zero-column find-non-zero-col-1))
;; 	   )
;; 	  ("Subgoal 2"

;; 	   :use (:instance DETERMINANT-INVERSE-LOOP (a '((:HEADER :DIMENSIONS (3 3)
;;                                                        :MAXIMUM-LENGTH 10
;;                                                        :DEFAULT 0
;;                                                        :NAME IDENTITY-MATRIX)
;;                                               ((0 . 0) . 1)
;;                                               ((1 . 1) . 1)
;;                                               ((2 . 2) . 1)))
;;                                             (b '((:HEADER :DIMENSIONS (3 3)
;;                                                        :MAXIMUM-LENGTH 10
;;                                                        :DEFAULT 0
;;                                                        :NAME IDENTITY-MATRIX)
;;                                               ((0 . 0) . 1)
;;                                               ((1 . 1) . 1)
;;                                               ((2 . 2) . 1)))
;;                                             (c (COMPRESS2 '$C M))
;;                                             (d 1) (i 0) (j 2) (k 0) (n 2))
	   
;; 	   :in-theory (e/d (determinant-inverse-loop) (aref2 dimensions compress2 zero-column find-non-zero-col-1))
	   
;; 	   )
	  
;; 	  ("Subgoal 3"
;; 	   :use ((:instance array2p-alist2p (name '$arg1) (L m)))
;; 	   :in-theory (enable alist2p)
;; 	   )
;; 	  ("Subgoal 1"
;; 	   :use ((:instance array2p-alist2p (name '$arg1) (L m)))
;; 	   :in-theory (enable alist2p)
;; 	   )
;; 	  )
;;   )
;;   ;; :hints (("Goal"
;;   ;; 	   :cases (
;;   ;; 		   (or (equal a 0) (not (equal a 0)))
;;   ;; 		   (or (equal b 0) (not (equal b 0)))
;;   ;; 		   (or (equal c 0) (not (equal c 0)))
;;   ;; 		   (or (equal d 0) (not (equal d 0)))
;;   ;; 		   (or (equal e 0) (not (equal e 0)))
;;   ;; 		   (or (equal f 0) (not (equal f 0)))
;;   ;; 		   (or (equal g 0) (not (equal g 0)))
;;   ;; 		   (or (equal h 0) (not (equal h 0)))
;;   ;; 		   (or (equal i 0) (not (equal i 0)))
;;   ;; 		   )
;;   ;; 	   ))
;;   )


;; (defthmd id-rotp
;;   (rotationp (id-rotation))
;;   )



;; (encapsulate
;;  ()
;;  (local (include-book "arithmetic-5/top" :dir :system))

;;  (local
;;   (defthm compress21-lemma
;;     (equal (compress21 name l n i j default)
;; 	   (if (zp (- i n)) nil
;; 	     (append (compress211 name l n 0 j default)
;; 		     (compress21 name l (+ n 1) i j default))))
;;     :hints (("Goal"
;; 	     :in-theory (enable compress21 compress211)
;; 	     ))		 
;;     )
;;   )

;;  ;; (local
;;  ;;  (defthm m-=-row-1-lemma
;;  ;;    (equal (m-=-row-1 m1 m2 m n)
;;  ;; 	   (if (zp m)
;;  ;; 	       (m-=-row m1 m2 0 n)
;;  ;; 	     (and (m-=-row m1 m2 m n)
;;  ;; 		  (m-=-row-1 m1 m2 (- m 1) n))))
;;  ;;    )
;;  ;;  )

;;  ;; (local
;;  ;;  (defthm m-=-row-lemma
;;  ;;    (equal (m-=-row m1 m2 m n)
;;  ;; 	   (if (zp n)
;;  ;; 	       (equal (fix (aref2 '$arg1 M1 m 0))
;;  ;; 		      (fix (aref2 '$arg2 M2 m 0)))
;;  ;; 	     (and (equal (fix (aref2 '$arg1 M1 m n))
;;  ;; 			 (fix (aref2 '$arg2 M2 m n)))
;;  ;; 		  (m-=-row M1 M2 m (- n 1)))))
;;  ;;    )
;;  ;;  )

;;  (local
;;   (defthm dim-lemma
;;     (implies (and (array2p name m1)
;; 		  (symbolp name))
;; 	     (and (equal (r m1) (car (dimensions '$C m1)))
;; 		  (equal (c m1) (cadr (dimensions '$C m1))))
;; 	     )
;;     :hints (("Goal"
;; 	    :in-theory (enable dimensions header)
;; 	    )
;; 	    )
;;     )
;;   )
 

;;  (defthmd det-lemma
;;    (implies (and (mat-det=1 m1)
;; 		 (mat-det=1 m2)
;; 		)
;; 	   (equal (determinant (m-* m1 m2)) (* (determinant m1) (determinant m2))))
;;   :hints (("Goal"
;; 	   :use ((:instance array2p-alist2p (name '$C) (L m2))
;; 		 (:instance array2p-alist2p (name '$C) (L m1))
;; 		 (:instance array2p-alist2p (name '$C) (L (m-* m1 m2)))
;; 		 (:instance array2p-m-*-1 (m1 m1) (m2 m2) (name '$C))
;; 		 )
;; 	   )
;; 	  ("Subgoal 18"
;; 	   :in-theory (enable dimensions)
;; 	   )
;; 	  ("Subgoal 3"
;; 	   :in-theory (e/d (determinant-inverse-loop) (compress2))
;; 	   ))
;;   )
