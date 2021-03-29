
(in-package "ACL2")

(include-book "workshops/2003/cowles-gamboa-van-baalen_matrix/support/matalg" :dir :system)
;(local (include-book "arithmetic-5/top" :dir :system))
(include-book "free-group")

(defun r3-matrixp (m)
  (and (array2p :fake-name m)
       (equal (r m) (c m))
       (equal (r m) 3)
       (realp (aref2 :fake-name m 0 0))
       (realp (aref2 :fake-name m 0 1))
       (realp (aref2 :fake-name m 0 2))
       (realp (aref2 :fake-name m 1 0))
       (realp (aref2 :fake-name m 1 1))
       (realp (aref2 :fake-name m 1 2))
       (realp (aref2 :fake-name m 2 0))
       (realp (aref2 :fake-name m 2 1))
       (realp (aref2 :fake-name m 2 2))
       )
  )

(defun r3-m-determinant (m)
  (declare (xargs :guard (and (array2p :fake-name m)
			      (equal (r m) (c m))
			      (equal (r m) 3))
		  :verify-guards nil))
  (+ (* (aref2 :fake-name m 0 0) (- (* (aref2 :fake-name m 1 1) (aref2 :fake-name m 2 2))
                                    (* (aref2 :fake-name m 1 2) (aref2 :fake-name m 2 1))))
     (* (- (aref2 :fake-name m 0 1)) (- (* (aref2 :fake-name m 1 0) (aref2 :fake-name m 2 2))
                                        (* (aref2 :fake-name m 1 2) (aref2 :fake-name m 2 0))))
     (* (aref2 :fake-name m 0 2) (- (* (aref2 :fake-name m 1 0) (aref2 :fake-name m 2 1))
                                    (* (aref2 :fake-name m 1 1) (aref2 :fake-name m 2 0))))
     )
  )

(local
 (defthm realp-r3-m-determinant
   (implies (r3-matrixp m)
	    (realp (r3-m-determinant m)))
   )
 )

(defthm normalize-header-name
  (implies (syntaxp (not (equal name '':fake-name)))
           (equal (header name l)
                  (header :fake-name l)))
  :hints (("Goal" :in-theory (e/d (header) ()))))

;(local (in-theory (enable normalize-header-name)))

(defthm normalize-default-name
  (implies (syntaxp (not (equal name '':fake-name)))
           (equal (default name l)
                  (default :fake-name l)))
  :hints (("Goal" :in-theory (e/d (default) ()))))

;(local (in-theory (enable normalize-default-name)))

(defthm normalize-maximum-length-name
  (implies (syntaxp (not (equal name '':fake-name)))
           (equal (maximum-length name l)
                  (maximum-length :fake-name l)))
  :hints (("Goal" :in-theory (e/d (maximum-length) ()))))

;(local (in-theory (enable normalize-maximum-length-name)))

(defthm normalize-dimensions-name
  (implies (syntaxp (not (equal name '':fake-name)))
           (equal (dimensions name l)
                  (dimensions :fake-name l)))
  :hints (("Goal" :in-theory (e/d (dimensions) ()))))

;(local (in-theory (enable normalize-dimensions-name)))

(defthm normalize-compress11-name
  (implies (syntaxp (not (equal name '':fake-name)))
           (equal (compress11 name l i n default)
                  (compress11 :fake-name l i n default)))
  :hints (("Goal" :in-theory (e/d (compress11) ()))))

;(local (in-theory (enable normalize-compress11-name)))

(defthm normalize-compress1-name
  (implies (syntaxp (not (equal name '':fake-name)))
           (equal (compress1 name l)
                  (compress1 :fake-name l)))
  :hints (("Goal" :in-theory (e/d (compress1) ()))))

(defthm normalize-compress211-name
  (implies (syntaxp (not (equal name '':fake-name)))
           (equal (compress211 name l i x j default)
                  (compress211 :fake-name l i x j default)))
  :hints (("Goal" :in-theory (e/d (compress211) ()))))

(defthm normalize-compress21-name
  (implies (syntaxp (not (equal name '':fake-name)))
           (equal (compress21 name l n i j default)
                  (compress21 :fake-name l n i j default)))
  :hints (("Goal" :in-theory (e/d (compress21) ()))))

;(local (in-theory (enable normalize-compress11-name)))

(defthm normalize-compress2-name
  (implies (syntaxp (not (equal name '':fake-name)))
           (equal (compress2 name l)
                  (compress2 :fake-name l)))
  :hints (("Goal" :in-theory (e/d (compress2) ()))))

(defthm normalize-aref2-name
  (implies (syntaxp (not (equal name '':fake-name)))
           (equal (aref2 name l i j)
                  (aref2 :fake-name l i j)))
  :hints (("Goal" :in-theory (e/d (aref2) ()))))

(defthm normalize-array2p-name
  (implies (and (syntaxp (not (equal name '':fake-name)))
		(symbolp name))
           (equal (array2p name l)
                  (array2p :fake-name l)))
  :hints (("Goal" :in-theory (e/d (array2p) ()))))

(defthm normalize-alist2p-name
  (implies (and (syntaxp (not (equal name '':fake-name)))
		(symbolp name))
           (equal (alist2p name l)
                  (alist2p :fake-name l)))
  :hints (("Goal" :in-theory (e/d (alist2p) ()))))

(local
 (defthm
   aref2-m-*-1
   (implies (and (alist2p :fake-name M1)
		 (alist2p :fake-name M2)
		 (equal (second (dimensions :fake-name M1))
			(first  (dimensions :fake-name M2)))
		 (integerp i)
		 (integerp j)
		 (>= i 0)
		 (>= j 0)
		 (< i (first (dimensions :fake-name M1)))
		 (< j (second (dimensions :fake-name M2))))
	    (equal (aref2 :fake-name (m-* M1 M2) i j)
		   (dot M1
			M2
			i
			(+ -1 (second (dimensions :fake-name M1)))
			j)))
   :hints (("Goal"
	    :use (:instance aref2-m-* (m1 m1) (m2 m2) (i i) (j j))
	    :in-theory (enable aref2 header default))))
 )

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))
  (defthmd det-lemma
    (implies (and (r3-matrixp m1)
                  (r3-matrixp m2)
                  )
             (equal (r3-m-determinant (m-* m1 m2)) (* (r3-m-determinant m1) (r3-m-determinant m2))))
    :hints (("Goal"
             :in-theory (enable r3-matrixp r3-m-determinant realp acl2-numberp)
             ))
    )
  )

(defun r3-m-inverse (m)
  `((:header :dimensions (3 3)
	     :maximum-length 10)
    ((0 . 0) . ,(/ (- (* (aref2 '$arg1 m 1 1) (aref2 '$arg1 m 2 2))
		      (* (aref2 '$arg1 m 2 1) (aref2 '$arg1 m 1 2)))
		   (r3-m-determinant m)))
    ((0 . 1) . ,(/ (- (* (aref2 '$arg1 m 0 2) (aref2 '$arg1 m 2 1))
		      (* (aref2 '$arg1 m 2 2) (aref2 '$arg1 m 0 1)))
		   (r3-m-determinant m)))
    ((0 . 2) . ,(/ (- (* (aref2 '$arg1 m 0 1) (aref2 '$arg1 m 1 2))
		      (* (aref2 '$arg1 m 1 1) (aref2 '$arg1 m 0 2)))
		   (r3-m-determinant m)))
    ((1 . 0) . ,(/ (- (* (aref2 '$arg1 m 1 2) (aref2 '$arg1 m 2 0))
		      (* (aref2 '$arg1 m 2 2) (aref2 '$arg1 m 1 0)))
		   (r3-m-determinant m)))
    ((1 . 1) . ,(/ (- (* (aref2 '$arg1 m 0 0) (aref2 '$arg1 m 2 2))
		      (* (aref2 '$arg1 m 2 0) (aref2 '$arg1 m 0 2)))
		   (r3-m-determinant m)))
    ((1 . 2) . ,(/ (- (* (aref2 '$arg1 m 0 2) (aref2 '$arg1 m 1 0))
		      (* (aref2 '$arg1 m 1 2) (aref2 '$arg1 m 0 0)))
		   (r3-m-determinant m)))
    ((2 . 0) . ,(/ (- (* (aref2 '$arg1 m 1 0) (aref2 '$arg1 m 2 1))
		      (* (aref2 '$arg1 m 2 0) (aref2 '$arg1 m 1 1)))
		   (r3-m-determinant m)))
    ((2 . 1) . ,(/ (- (* (aref2 '$arg1 m 0 1) (aref2 '$arg1 m 2 0))
		      (* (aref2 '$arg1 m 2 1) (aref2 '$arg1 m 0 0)))
		   (r3-m-determinant m)))
    ((2 . 2) . ,(/ (- (* (aref2 '$arg1 m 0 0) (aref2 '$arg1 m 1 1))
		      (* (aref2 '$arg1 m 1 0) (aref2 '$arg1 m 0 1)))
		   (r3-m-determinant m)))
    )
  )

(local
 (defthm array2p-r3-m-inverse
   (implies (r3-matrixp m)
	    (array2p :fake-name (r3-m-inverse m)))
   :hints (("Goal"
	    :in-theory (enable array2p header dimensions)
	    :do-not-induct t
	    ))
   )   
 )

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthm r3-m-inverse-=
    (implies (r3-matrixp m)
             
             (and (equal (aref2 :fakename (r3-m-inverse m) 0 0)
                         (/ (- (* (aref2 :fakename m 1 1) (aref2 :fakename m 2 2))
                               (* (aref2 :fakename m 2 1) (aref2 :fakename m 1 2)))
                            (r3-m-determinant m)))
                  (equal (aref2 :fakename (r3-m-inverse m) 0 1)
                         (/ (- (* (aref2 :fakename m 0 2) (aref2 :fakename m 2 1))
                               (* (aref2 :fakename m 2 2) (aref2 :fakename m 0 1)))
                            (r3-m-determinant m)))
                  (equal (aref2 :fakename (r3-m-inverse m) 0 2)
                         (/ (- (* (aref2 :fakename m 0 1) (aref2 :fakename m 1 2))
                               (* (aref2 :fakename m 1 1) (aref2 :fakename m 0 2)))
                            (r3-m-determinant m)))
                  (equal (aref2 :fakename (r3-m-inverse m) 1 0)
                         (/ (- (* (aref2 :fakename m 1 2) (aref2 :fakename m 2 0))
                               (* (aref2 :fakename m 2 2) (aref2 :fakename m 1 0)))
                            (r3-m-determinant m)))
                  (equal (aref2 :fakename (r3-m-inverse m) 1 1)
                         (/ (- (* (aref2 :fakename m 0 0) (aref2 :fakename m 2 2))
                               (* (aref2 :fakename m 2 0) (aref2 :fakename m 0 2)))
                            (r3-m-determinant m)))
                  (equal (aref2 :fakename (r3-m-inverse m) 1 2)
                         (/ (- (* (aref2 :fakename m 0 2) (aref2 :fakename m 1 0))
                               (* (aref2 :fakename m 1 2) (aref2 :fakename m 0 0)))
                            (r3-m-determinant m)))
                  (equal (aref2 :fakename (r3-m-inverse m) 2 0)
                         (/ (- (* (aref2 :fakename m 1 0) (aref2 :fakename m 2 1))
                               (* (aref2 :fakename m 2 0) (aref2 :fakename m 1 1)))
                            (r3-m-determinant m)))
                  (equal (aref2 :fakename (r3-m-inverse m) 2 1)
                         (/ (- (* (aref2 :fakename m 0 1) (aref2 :fakename m 2 0))
                               (* (aref2 :fakename m 2 1) (aref2 :fakename m 0 0)))
                            (r3-m-determinant m)))
                  (equal (aref2 :fakename (r3-m-inverse m) 2 2)
                         (/ (- (* (aref2 :fakename m 0 0) (aref2 :fakename m 1 1))
                               (* (aref2 :fakename m 1 0) (aref2 :fakename m 0 1)))
                            (r3-m-determinant m)))
                  (equal (r (r3-m-inverse m)) (c (r3-m-inverse m)))
                  (equal (r (r3-m-inverse m)) 3)
                  )
             )
    :hints (("Goal"
             :in-theory (e/d (r3-m-inverse dimensions header) (r3-m-determinant aref2))
             :expand ((:free (i j) (AREF2 :FAKE-NAME
                                          (LIST '(:HEADER :DIMENSIONS (3 3)
                                                          :MAXIMUM-LENGTH 10)
                                                (CONS '(0 . 0)
                                                      (+ (* (/ (R3-M-DETERMINANT M))
                                                            (AREF2 :FAKE-NAME M 1 1)
                                                            (AREF2 :FAKE-NAME M 2 2))
                                                         (- (* (/ (R3-M-DETERMINANT M))
                                                               (AREF2 :FAKE-NAME M 1 2)
                                                               (AREF2 :FAKE-NAME M 2 1)))))
                                                (CONS '(0 . 1)
                                                      (+ (- (* (/ (R3-M-DETERMINANT M))
                                                               (AREF2 :FAKE-NAME M 0 1)
                                                               (AREF2 :FAKE-NAME M 2 2)))
                                                         (* (/ (R3-M-DETERMINANT M))
                                                            (AREF2 :FAKE-NAME M 0 2)
                                                            (AREF2 :FAKE-NAME M 2 1))))
                                                (CONS '(0 . 2)
                                                      (+ (* (/ (R3-M-DETERMINANT M))
                                                            (AREF2 :FAKE-NAME M 0 1)
                                                            (AREF2 :FAKE-NAME M 1 2))
                                                         (- (* (/ (R3-M-DETERMINANT M))
                                                               (AREF2 :FAKE-NAME M 0 2)
                                                               (AREF2 :FAKE-NAME M 1 1)))))
                                                (CONS '(1 . 0)
                                                      (+ (- (* (/ (R3-M-DETERMINANT M))
                                                               (AREF2 :FAKE-NAME M 1 0)
                                                               (AREF2 :FAKE-NAME M 2 2)))
                                                         (* (/ (R3-M-DETERMINANT M))
                                                            (AREF2 :FAKE-NAME M 2 0)
                                                            (AREF2 :FAKE-NAME M 1 2))))
                                                (CONS '(1 . 1)
                                                      (+ (* (/ (R3-M-DETERMINANT M))
                                                            (AREF2 :FAKE-NAME M 0 0)
                                                            (AREF2 :FAKE-NAME M 2 2))
                                                         (- (* (/ (R3-M-DETERMINANT M))
                                                               (AREF2 :FAKE-NAME M 0 2)
                                                               (AREF2 :FAKE-NAME M 2 0)))))
                                                (CONS '(1 . 2)
                                                      (+ (- (* (/ (R3-M-DETERMINANT M))
                                                               (AREF2 :FAKE-NAME M 0 0)
                                                               (AREF2 :FAKE-NAME M 1 2)))
                                                         (* (/ (R3-M-DETERMINANT M))
                                                            (AREF2 :FAKE-NAME M 1 0)
                                                            (AREF2 :FAKE-NAME M 0 2))))
                                                (CONS '(2 . 0)
                                                      (+ (* (/ (R3-M-DETERMINANT M))
                                                            (AREF2 :FAKE-NAME M 1 0)
                                                            (AREF2 :FAKE-NAME M 2 1))
                                                         (- (* (/ (R3-M-DETERMINANT M))
                                                               (AREF2 :FAKE-NAME M 1 1)
                                                               (AREF2 :FAKE-NAME M 2 0)))))
                                                (CONS '(2 . 1)
                                                      (+ (- (* (/ (R3-M-DETERMINANT M))
                                                               (AREF2 :FAKE-NAME M 0 0)
                                                               (AREF2 :FAKE-NAME M 2 1)))
                                                         (* (/ (R3-M-DETERMINANT M))
                                                            (AREF2 :FAKE-NAME M 0 1)
                                                            (AREF2 :FAKE-NAME M 2 0))))
                                                (CONS '(2 . 2)
                                                      (+ (* (/ (R3-M-DETERMINANT M))
                                                            (AREF2 :FAKE-NAME M 0 0)
                                                            (AREF2 :FAKE-NAME M 1 1))
                                                         (- (* (/ (R3-M-DETERMINANT M))
                                                               (AREF2 :FAKE-NAME M 0 1)
                                                               (AREF2 :FAKE-NAME M 1 0))))))
                                          i j)))
             ))
    )
  )

(local
 (defthm r3-m-inverse-realp
   (implies (r3-matrixp m)
	    (and (realp (aref2 :fake-name (r3-m-inverse m) 0 0))
		 (realp (aref2 :fake-name (r3-m-inverse m) 0 1))
		 (realp (aref2 :fake-name (r3-m-inverse m) 0 2))
		 (realp (aref2 :fake-name (r3-m-inverse m) 1 0))
		 (realp (aref2 :fake-name (r3-m-inverse m) 1 1))
		 (realp (aref2 :fake-name (r3-m-inverse m) 1 2))
		 (realp (aref2 :fake-name (r3-m-inverse m) 2 0))
		 (realp (aref2 :fake-name (r3-m-inverse m) 2 1))
		 (realp (aref2 :fake-name (r3-m-inverse m) 2 2)))
	    )
   :hints (("Goal"
	    :use ((:instance  r3-m-inverse-= (m m))
		  (:instance realp-r3-m-determinant (m m)))
	    :in-theory (e/d (r3-matrixp) (r3-m-determinant aref2))
	    ))
   )
 )

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

(encapsulate
  ()

  (local (include-book "arithmetic-3/top" :dir :system))

  (local
   (defthmd lemma-100-1
     (implies (and (realp a)
                   (not (= a 0)))
              (equal (/ a a) 1)))
   )

  (local
   (defthm lemma-1
     (implies (and 
               (REALP (AREF2 :FAKE-NAME M 0 0))
               (REALP (AREF2 :FAKE-NAME M 0 1))
               (REALP (AREF2 :FAKE-NAME M 0 2))
               (REALP (AREF2 :FAKE-NAME M 1 0))
               (REALP (AREF2 :FAKE-NAME M 1 1))
               (REALP (AREF2 :FAKE-NAME M 1 2))
               (REALP (AREF2 :FAKE-NAME M 2 0))
               (REALP (AREF2 :FAKE-NAME M 2 1))
               (REALP (AREF2 :FAKE-NAME M 2 2))
               (NOT (EQUAL (+ (* (AREF2 :FAKE-NAME M 0 0)
                                 (AREF2 :FAKE-NAME M 1 1)
                                 (AREF2 :FAKE-NAME M 2 2))
                              (* (AREF2 :FAKE-NAME M 0 1)
                                 (AREF2 :FAKE-NAME M 2 0)
                                 (AREF2 :FAKE-NAME M 1 2))
                              (* (AREF2 :FAKE-NAME M 1 0)
                                 (AREF2 :FAKE-NAME M 0 2)
                                 (AREF2 :FAKE-NAME M 2 1)))
                           (+ (* (AREF2 :FAKE-NAME M 0 0)
                                 (AREF2 :FAKE-NAME M 1 2)
                                 (AREF2 :FAKE-NAME M 2 1))
                              (* (AREF2 :FAKE-NAME M 0 1)
                                 (AREF2 :FAKE-NAME M 1 0)
                                 (AREF2 :FAKE-NAME M 2 2))
                              (* (AREF2 :FAKE-NAME M 0 2)
                                 (AREF2 :FAKE-NAME M 1 1)
                                 (AREF2 :FAKE-NAME M 2 0))))))
              (EQUAL (+ (* (AREF2 :FAKE-NAME M 0 0)
                           (AREF2 :FAKE-NAME M 1 1)
                           (AREF2 :FAKE-NAME M 2 2)
                           (/ (+ (* (AREF2 :FAKE-NAME M 0 0)
                                    (AREF2 :FAKE-NAME M 1 1)
                                    (AREF2 :FAKE-NAME M 2 2))
                                 (- (* (AREF2 :FAKE-NAME M 0 0)
                                       (AREF2 :FAKE-NAME M 1 2)
                                       (AREF2 :FAKE-NAME M 2 1)))
                                 (- (* (AREF2 :FAKE-NAME M 0 1)
                                       (AREF2 :FAKE-NAME M 1 0)
                                       (AREF2 :FAKE-NAME M 2 2)))
                                 (* (AREF2 :FAKE-NAME M 0 1)
                                    (AREF2 :FAKE-NAME M 2 0)
                                    (AREF2 :FAKE-NAME M 1 2))
                                 (- (* (AREF2 :FAKE-NAME M 0 2)
                                       (AREF2 :FAKE-NAME M 1 1)
                                       (AREF2 :FAKE-NAME M 2 0)))
                                 (* (AREF2 :FAKE-NAME M 1 0)
                                    (AREF2 :FAKE-NAME M 0 2)
                                    (AREF2 :FAKE-NAME M 2 1)))))
                        (* (AREF2 :FAKE-NAME M 0 1)
                           (AREF2 :FAKE-NAME M 2 0)
                           (AREF2 :FAKE-NAME M 1 2)
                           (/ (+ (* (AREF2 :FAKE-NAME M 0 0)
                                    (AREF2 :FAKE-NAME M 1 1)
                                    (AREF2 :FAKE-NAME M 2 2))
                                 (- (* (AREF2 :FAKE-NAME M 0 0)
                                       (AREF2 :FAKE-NAME M 1 2)
                                       (AREF2 :FAKE-NAME M 2 1)))
                                 (- (* (AREF2 :FAKE-NAME M 0 1)
                                       (AREF2 :FAKE-NAME M 1 0)
                                       (AREF2 :FAKE-NAME M 2 2)))
                                 (* (AREF2 :FAKE-NAME M 0 1)
                                    (AREF2 :FAKE-NAME M 2 0)
                                    (AREF2 :FAKE-NAME M 1 2))
                                 (- (* (AREF2 :FAKE-NAME M 0 2)
                                       (AREF2 :FAKE-NAME M 1 1)
                                       (AREF2 :FAKE-NAME M 2 0)))
                                 (* (AREF2 :FAKE-NAME M 1 0)
                                    (AREF2 :FAKE-NAME M 0 2)
                                    (AREF2 :FAKE-NAME M 2 1)))))
                        (* (AREF2 :FAKE-NAME M 1 0)
                           (AREF2 :FAKE-NAME M 0 2)
                           (AREF2 :FAKE-NAME M 2 1)
                           (/ (+ (* (AREF2 :FAKE-NAME M 0 0)
                                    (AREF2 :FAKE-NAME M 1 1)
                                    (AREF2 :FAKE-NAME M 2 2))
                                 (- (* (AREF2 :FAKE-NAME M 0 0)
                                       (AREF2 :FAKE-NAME M 1 2)
                                       (AREF2 :FAKE-NAME M 2 1)))
                                 (- (* (AREF2 :FAKE-NAME M 0 1)
                                       (AREF2 :FAKE-NAME M 1 0)
                                       (AREF2 :FAKE-NAME M 2 2)))
                                 (* (AREF2 :FAKE-NAME M 0 1)
                                    (AREF2 :FAKE-NAME M 2 0)
                                    (AREF2 :FAKE-NAME M 1 2))
                                 (- (* (AREF2 :FAKE-NAME M 0 2)
                                       (AREF2 :FAKE-NAME M 1 1)
                                       (AREF2 :FAKE-NAME M 2 0)))
                                 (* (AREF2 :FAKE-NAME M 1 0)
                                    (AREF2 :FAKE-NAME M 0 2)
                                    (AREF2 :FAKE-NAME M 2 1))))))
                     (+ 1
                        (* (AREF2 :FAKE-NAME M 0 0)
                           (AREF2 :FAKE-NAME M 1 2)
                           (AREF2 :FAKE-NAME M 2 1)
                           (/ (+ (* (AREF2 :FAKE-NAME M 0 0)
                                    (AREF2 :FAKE-NAME M 1 1)
                                    (AREF2 :FAKE-NAME M 2 2))
                                 (- (* (AREF2 :FAKE-NAME M 0 0)
                                       (AREF2 :FAKE-NAME M 1 2)
                                       (AREF2 :FAKE-NAME M 2 1)))
                                 (- (* (AREF2 :FAKE-NAME M 0 1)
                                       (AREF2 :FAKE-NAME M 1 0)
                                       (AREF2 :FAKE-NAME M 2 2)))
                                 (* (AREF2 :FAKE-NAME M 0 1)
                                    (AREF2 :FAKE-NAME M 2 0)
                                    (AREF2 :FAKE-NAME M 1 2))
                                 (- (* (AREF2 :FAKE-NAME M 0 2)
                                       (AREF2 :FAKE-NAME M 1 1)
                                       (AREF2 :FAKE-NAME M 2 0)))
                                 (* (AREF2 :FAKE-NAME M 1 0)
                                    (AREF2 :FAKE-NAME M 0 2)
                                    (AREF2 :FAKE-NAME M 2 1)))))
                        (* (AREF2 :FAKE-NAME M 0 1)
                           (AREF2 :FAKE-NAME M 1 0)
                           (AREF2 :FAKE-NAME M 2 2)
                           (/ (+ (* (AREF2 :FAKE-NAME M 0 0)
                                    (AREF2 :FAKE-NAME M 1 1)
                                    (AREF2 :FAKE-NAME M 2 2))
                                 (- (* (AREF2 :FAKE-NAME M 0 0)
                                       (AREF2 :FAKE-NAME M 1 2)
                                       (AREF2 :FAKE-NAME M 2 1)))
                                 (- (* (AREF2 :FAKE-NAME M 0 1)
                                       (AREF2 :FAKE-NAME M 1 0)
                                       (AREF2 :FAKE-NAME M 2 2)))
                                 (* (AREF2 :FAKE-NAME M 0 1)
                                    (AREF2 :FAKE-NAME M 2 0)
                                    (AREF2 :FAKE-NAME M 1 2))
                                 (- (* (AREF2 :FAKE-NAME M 0 2)
                                       (AREF2 :FAKE-NAME M 1 1)
                                       (AREF2 :FAKE-NAME M 2 0)))
                                 (* (AREF2 :FAKE-NAME M 1 0)
                                    (AREF2 :FAKE-NAME M 0 2)
                                    (AREF2 :FAKE-NAME M 2 1)))))
                        (* (AREF2 :FAKE-NAME M 0 2)
                           (AREF2 :FAKE-NAME M 1 1)
                           (AREF2 :FAKE-NAME M 2 0)
                           (/ (+ (* (AREF2 :FAKE-NAME M 0 0)
                                    (AREF2 :FAKE-NAME M 1 1)
                                    (AREF2 :FAKE-NAME M 2 2))
                                 (- (* (AREF2 :FAKE-NAME M 0 0)
                                       (AREF2 :FAKE-NAME M 1 2)
                                       (AREF2 :FAKE-NAME M 2 1)))
                                 (- (* (AREF2 :FAKE-NAME M 0 1)
                                       (AREF2 :FAKE-NAME M 1 0)
                                       (AREF2 :FAKE-NAME M 2 2)))
                                 (* (AREF2 :FAKE-NAME M 0 1)
                                    (AREF2 :FAKE-NAME M 2 0)
                                    (AREF2 :FAKE-NAME M 1 2))
                                 (- (* (AREF2 :FAKE-NAME M 0 2)
                                       (AREF2 :FAKE-NAME M 1 1)
                                       (AREF2 :FAKE-NAME M 2 0)))
                                 (* (AREF2 :FAKE-NAME M 1 0)
                                    (AREF2 :FAKE-NAME M 0 2)
                                    (AREF2 :FAKE-NAME M 2 1))))))))
     :hints (("Goal"
              :use (:instance lemma-100-1
                              (a (/ (+ (* (AREF2 :FAKE-NAME M 0 0)
                                          (AREF2 :FAKE-NAME M 1 1)
                                          (AREF2 :FAKE-NAME M 2 2))
                                       (- (* (AREF2 :FAKE-NAME M 0 0)
                                             (AREF2 :FAKE-NAME M 1 2)
                                             (AREF2 :FAKE-NAME M 2 1)))
                                       (- (* (AREF2 :FAKE-NAME M 0 1)
                                             (AREF2 :FAKE-NAME M 1 0)
                                             (AREF2 :FAKE-NAME M 2 2)))
                                       (* (AREF2 :FAKE-NAME M 0 1)
                                          (AREF2 :FAKE-NAME M 2 0)
                                          (AREF2 :FAKE-NAME M 1 2))
                                       (- (* (AREF2 :FAKE-NAME M 0 2)
                                             (AREF2 :FAKE-NAME M 1 1)
                                             (AREF2 :FAKE-NAME M 2 0)))
                                       (* (AREF2 :FAKE-NAME M 1 0)
                                          (AREF2 :FAKE-NAME M 0 2)
                                          (AREF2 :FAKE-NAME M 2 1))))))
              :in-theory (disable aref2)
              ))
     )
   )
  
  (defthm m-*-m-m-inverse
    (implies (and (r3-matrixp m)
                  (not (= (r3-m-determinant m) 0)))
             (m-= (m-* m (r3-m-inverse m)) (id-rotation)))
    :hints (("Goal"
             :use ((:instance array2p-alist2p (name :fake-name) (L m))
                   (:instance array2p-m-*-1
                              (m1 m)
                              (m2 (r3-m-inverse m))
                              (name :fake-name))
                   (:instance r3-m-inverse-= (m m))
                   (:instance dimensions-m-* (m1 m)
                              (m2 (r3-m-inverse m))
                              (name :fake-name))
                   (:instance array2p-alist2p (name :fake-name)
                              (L (r3-m-inverse m))))
             :in-theory (e/d (m-= dot) (aref2 r3-m-inverse))
             )
            ("Subgoal 9"
             :in-theory (e/d (r3-m-inverse) (r3-m-determinant))
             )
            ("Subgoal 8"
             :in-theory (e/d (r3-m-inverse) (r3-m-determinant))
             )
            ("Subgoal 7"
             :in-theory (e/d (r3-m-inverse) (r3-m-determinant))
             )
            ("Subgoal 6"
             :in-theory (e/d (r3-m-inverse) (r3-m-determinant))
             )
            ("Subgoal 5"
             :in-theory (e/d (r3-m-inverse) (r3-m-determinant))
             )                                                
            ("Subgoal 4"
             :in-theory (e/d (r3-m-inverse) (r3-m-determinant))
             )
            ("Subgoal 3"
             :in-theory (e/d (r3-m-inverse) (r3-m-determinant))
             )
            ("Subgoal 2"
             :in-theory (e/d (r3-m-inverse) (r3-m-determinant))
             )
            ("Subgoal 1"
             :in-theory (e/d (r3-m-inverse) (r3-m-determinant))
             )          
            )
    )

  (defthm m-*-m-inverse-m
    (implies (and (r3-matrixp m)
                  (not (= (r3-m-determinant m) 0)))
             (m-= (m-* (r3-m-inverse m) m) (id-rotation)))
    :hints (("Goal"
             :use ((:instance array2p-alist2p (name :fake-name) (L m))
                   (:instance array2p-m-*-1
                              (m2 m)
                              (m1 (r3-m-inverse m))
                              (name :fake-name))
                   (:instance r3-m-inverse-= (m m))
                   (:instance dimensions-m-* (m2 m)
                              (m1 (r3-m-inverse m))
                              (name :fake-name))
                   (:instance array2p-alist2p (name :fake-name)
                              (L (r3-m-inverse m))))
             :in-theory (e/d (m-= dot) (aref2 r3-m-inverse))
             )
            ("Subgoal 9"
             :in-theory (e/d (r3-m-inverse) (r3-m-determinant))
             )
            ("Subgoal 8"
             :in-theory (e/d (r3-m-inverse) (r3-m-determinant))
             )
            ("Subgoal 7"
             :in-theory (e/d (r3-m-inverse) (r3-m-determinant))
             )
            ("Subgoal 6"
             :in-theory (e/d (r3-m-inverse) (r3-m-determinant))
             )
            ("Subgoal 5"
             :in-theory (e/d (r3-m-inverse) (r3-m-determinant))
             )                                                
            ("Subgoal 4"
             :in-theory (e/d (r3-m-inverse) (r3-m-determinant))
             )
            ("Subgoal 3"
             :in-theory (e/d (r3-m-inverse) (r3-m-determinant))
             )
            ("Subgoal 2"
             :in-theory (e/d (r3-m-inverse) (r3-m-determinant))
             )
            ("Subgoal 1"
             :in-theory (e/d (r3-m-inverse) (r3-m-determinant))
             )          
            )
    )
  )

(skip-proofs
 (defthm m-inverse-m-*-m1-m2
   (implies (and (r3-matrixp m1)
                 (r3-matrixp m2))
            (m-= (r3-m-inverse (m-* m1 m2))
                 (m-* (r3-m-inverse m2) (r3-m-inverse m1))))
   :hints (("Goal"
            :in-theory (enable m-= m-* M-BINARY-*-ROW-1 compress2)
            ))
   )
 )

(defthm r3-matrixp-m1*m2-is-r3-matrixp
  (implies (and (r3-matrixp m1)
                (r3-matrixp m2))
           (r3-matrixp (m-* m1 m2)))
  )

(defun r3-rotationp (m)
  (and (r3-matrixp m)
       (= (r3-m-determinant m) 1)
       (m-= (r3-m-inverse m) (m-trans m)))
  )

(defthm rot*rot-is-rot
  (implies (and (r3-rotationp m1)
                (r3-rotationp m2))
           (r3-rotationp (m-* m1 m2)))
  :hints (("Goal"
           :use ((:instance r3-matrixp-m1*m2-is-r3-matrixp (m1 m1) (m2 m2))
                 (:instance det-lemma (m1 m1) (m2 m2))
                 (:instance m-inverse-m-*-m1-m2 (m1 m1) (m2 m2))
                 (:instance m-trans-m-*=m-*-m-trans (m1 m1) (m2 m2) (name :fake-name))
                 (:instance array2p-alist2p (L m1) (name :fake-name))
                 (:instance array2p-alist2p (L m2) (name :fake-name))
                 )
           :in-theory (e/d (r3-matrixp r3-rotationp)
                           (m-* aref2 m-= m-trans r3-m-inverse r3-m-determinant))
           ))
  )

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))
  
  (defthm base-rotations
    (implies (equal x (acl2-sqrt 2))
             (and (r3-rotationp (a-rotation x))
                  (r3-rotationp (a-inv-rotation x))
                  (r3-rotationp (b-rotation x))
                  (r3-rotationp (b-inv-rotation x))
                  (r3-rotationp (id-rotation))))
    :hints (("Goal"
             :use ((:instance array2p-funs (y :fake-name))
                   (:instance sqrt-2-lemmas))
             :in-theory (e/d (aref2 m-=) (acl2-sqrt))
             ))
    )
  )

(defthmd reducedwordp-charlistp
  (implies (and (character-listp w)
                w)
           (equal (append (list (car w)) (cdr w)) w)))

(defthmd rotation-is-r3-rotationp-basecase
  (implies (equal x (acl2-sqrt 2))
           (and (r3-rotationp (rotation '(#\a) x))
                (r3-rotationp (rotation '(#\b) x))
                (r3-rotationp (rotation '(#\c) x))
                (r3-rotationp (rotation '(#\d) x))))
  :hints (("Goal"
           :use ((:instance rot*rot-is-rot
                            (m1 (a-rotation x))
                            (m2 (id-rotation)))
                 (:instance rot*rot-is-rot
                            (m1 (b-rotation x))
                            (m2 (id-rotation)))
                 (:instance rot*rot-is-rot
                            (m1 (a-inv-rotation x))
                            (m2 (id-rotation)))
                 (:instance rot*rot-is-rot
                            (m1 (b-inv-rotation x))
                            (m2 (id-rotation)))
                 (:instance base-rotations (x x)))
           ))
  )

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd rotation-is-r3-rotationp
    (implies (and (reducedwordp w)
                  (equal x (acl2-sqrt 2)))
             (r3-rotationp (rotation w x)))
    :hints (("Goal"
             :in-theory (disable acl2-sqrt)
             )
            ("Subgoal *1/5"
             :use ((:instance character-listp-word (x w))
                   (:instance rotation-= (w w))
                   (:instance reducedwordp=>weak-wordp (x w))
                   (:instance funs-lemmas-1 (x x))
                   (:instance rotation-is-r3-rotationp-basecase (x x))
                   (:instance rot*rot-is-rot
                              (m1 (rotation (list (car w)) x))
                              (m2 (rotation (cdr w) x))))
             :in-theory (disable acl2-sqrt r3-rotationp aref2)
             )
            ("Subgoal *1/4"
             :use ((:instance character-listp-word (x w))
                   (:instance rotation-= (w w))
                   (:instance reducedwordp=>weak-wordp (x w))
                   (:instance funs-lemmas-1 (x x))
                   (:instance rotation-is-r3-rotationp-basecase (x x))
                   (:instance rot*rot-is-rot
                              (m1 (rotation (list (car w)) x))
                              (m2 (rotation (cdr w) x))))
             :in-theory (disable acl2-sqrt r3-rotationp aref2)
             )
            ("Subgoal *1/3"
             :use ((:instance character-listp-word (x w))
                   (:instance rotation-= (w w))
                   (:instance reducedwordp=>weak-wordp (x w))
                   (:instance funs-lemmas-1 (x x))
                   (:instance rotation-is-r3-rotationp-basecase (x x))
                   (:instance rot*rot-is-rot
                              (m1 (rotation (list (car w)) x))
                              (m2 (rotation (cdr w) x))))
             :in-theory (disable acl2-sqrt r3-rotationp aref2)
             )
            ("Subgoal *1/2"
             :use ((:instance character-listp-word (x w))
                   (:instance rotation-= (w w))
                   (:instance reducedwordp=>weak-wordp (x w))
                   (:instance funs-lemmas-1 (x x))
                   (:instance rotation-is-r3-rotationp-basecase (x x))
                   (:instance rot*rot-is-rot
                              (m1 (rotation (list (car w)) x))
                              (m2 (rotation (cdr w) x))))
             :in-theory (disable acl2-sqrt r3-rotationp aref2)
             )
            ("Subgoal *1/1"
             :use ((:instance character-listp-word (x w))
                   (:instance rotation-= (w w))
                   (:instance reducedwordp=>weak-wordp (x w))
                   (:instance funs-lemmas-1 (x x))
                   (:instance rotation-is-r3-rotationp-basecase (x x))
                   (:instance rot*rot-is-rot
                              (m1 (rotation (list (car w)) x))
                              (m2 (rotation (cdr w) x))))
             :in-theory (disable acl2-sqrt r3-rotationp aref2)
             )
            )
    )
  )

;; (skip-proofs
;;  (defthmd m-*-m-inverse-m
;;    (implies (and (r3-matrixp m)
;; 		 (not (= (determinant m) 0)))
;; 	    (m-= (m-* (r3-m-inverse m) m) (id-rotation)))
;;    )
;;  )



;; (defun r3-m-inverse-1 ()
;;   (compress2 :fake-name   `((:header :dimensions (3 3)
;; 				     :maximum-length 10))
;;   )
;; )


;; (local
;;  (defthm compress21-lemma
;;    (equal (compress21 name l n i j default)
;; 	  (if (zp (- i n)) nil
;; 	    (append (compress211 name l n 0 j default)
;; 		    (compress21 name l (+ n 1) i j default))))
;;    :hints (("Goal"
;; 	    :in-theory (enable compress21 compress211)
;; 	    ))		 
;;    )
;;  )

;; (local
;;  (defthm r3-m-inverse-=
;;    (implies (and (r3-matrixp m)
;; 		 (symbolp name)
;; 		 (not (equal (r3-m-determinant m) 0)))
;; 	    (equal (aref2 name (r3-m-inverse m) 0 0)
;; 		   (/ (- (* (aref2 name m 1 1) (aref2 name m 2 2))
;; 			 (* (aref2 name m 2 1) (aref2 name m 1 2)))
;; 		      (r3-m-determinant m)))

;; 	    )
;;    :hints (("Goal"
;; 	    :use (:instance  array2p-r3-m-inverse (name name) (m m))
;; 	    :in-theory (e/d (aref2 r3-m-inverse array2p) (r3-m-determinant))
;; 	    ))
;;    )
;;  )

;; (local
;;  (defthm r3-m-inverse-=
;;    (implies (and (r3-matrixp m)
;; 		 (symbolp name)
;; 		 (not (= (r3-m-determinant m) 0)))
;; 	    (and (equal (aref2 name (r3-m-inverse m) 0 0)
;; 			(/ (- (* (aref2 name m 1 1) (aref2 name m 2 2))
;; 			      (* (aref2 name m 2 1) (aref2 name m 1 2)))
;; 			   (r3-m-determinant m)))
;; 		 (equal (aref2 name (r3-m-inverse m) 0 1)
;; 			(/ (- (* (aref2 name m 0 2) (aref2 name m 2 1))
;; 			      (* (aref2 name m 2 2) (aref2 name m 0 1)))
;; 			   (r3-m-determinant m)))
;; 		 (equal (aref2 name (r3-m-inverse m) 0 2)
;; 			(/ (- (* (aref2 name m 0 1) (aref2 name m 1 2))
;; 			      (* (aref2 name m 1 1) (aref2 name m 0 2)))
;; 			   (r3-m-determinant m)))
;; 		 (equal (aref2 name (r3-m-inverse m) 1 0)
;; 			(/ (- (* (aref2 name m 1 2) (aref2 name m 2 0))
;; 			      (* (aref2 name m 2 2) (aref2 name m 1 0)))
;; 			   (r3-m-determinant m)))
;; 		 (equal (aref2 name (r3-m-inverse m) 1 1)
;; 			(/ (- (* (aref2 name m 0 0) (aref2 name m 2 2))
;; 			      (* (aref2 name m 2 0) (aref2 name m 0 2)))
;; 			   (r3-m-determinant m)))
;; 		 (equal (aref2 name (r3-m-inverse m) 1 2)
;; 			(/ (- (* (aref2 name m 0 2) (aref2 name m 1 0))
;; 			      (* (aref2 name m 1 2) (aref2 name m 0 0)))
;; 			   (r3-m-determinant m)))
;; 		 (equal (aref2 name (r3-m-inverse m) 2 0)
;; 			(/ (- (* (aref2 name m 1 0) (aref2 name m 2 1))
;; 			      (* (aref2 name m 2 0) (aref2 name m 1 1)))
;; 			   (r3-m-determinant m)))
;; 		 (equal (aref2 name (r3-m-inverse m) 2 1)
;; 			(/ (- (* (aref2 name m 0 1) (aref2 name m 2 0))
;; 			      (* (aref2 name m 2 1) (aref2 name m 0 0)))
;; 			   (r3-m-determinant m)))
;; 		 (equal (aref2 name (r3-m-inverse m) 2 2)
;; 			(/ (- (* (aref2 name m 0 0) (aref2 name m 1 1))
;; 			      (* (aref2 name m 1 0) (aref2 name m 0 1)))
;; 			   (r3-m-determinant m)))
;; 		 )
;; 	    )
;;    :hints (("Goal"
;; 	    :in-theory (e/d (aref2) (r3-m-determinant))
;; 	    ))
;;    )
;;  )

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

;; (local
;;  (defthm m-=-row-1-lemma
;;    (equal (m-=-row-1 m1 m2 m n)
;; 	  (if (zp m)
;; 	      (m-=-row m1 m2 0 n)
;; 	    (and (m-=-row m1 m2 m n)
;; 		 (m-=-row-1 m1 m2 (- m 1) n))))
;;    )
;;  )

;; (local
;;  (defthm m-=-row-lemma
;;    (equal (m-=-row m1 m2 m n)
;; 	  (if (zp n)
;; 	      (equal (fix (aref2 '$arg1 M1 m 0))
;; 		     (fix (aref2 '$arg2 M2 m 0)))
;; 	    (and (equal (fix (aref2 '$arg1 M1 m n))
;; 			(fix (aref2 '$arg2 M2 m n)))
;; 		 (m-=-row M1 M2 m (- n 1)))))
;;    )
;;  )

;; (defthmd m-*-m-inverse-m
;;   (implies (and (r3-matrixp m)
;; 		(not (= (r3-m-determinant m) 0)))
;; 	   (m-= (m-* (r3-m-inverse m) m) (id-rotation)))
;;   :hints (("Goal"
;; 	   :in-theory (e/d (m-=) (aref2))
;; 	   ))
;;   )


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


;;  (local
;;   (defthm
;;     alist2p-$arg1
;;     (implies (alist2p name  l)
;; 	     (alist2p '$arg1 l))
;;     :hints (("Goal"
;; 	     :use (:instance alist2p-$arg (name name) (l l))
;; 	     :in-theory (enable alist2p)
;; 	     ))
;;     )
;;     ;:rule-classes :forward-chaining)
;;   )



;(defmacro monirune (rune)
; `(monitor ',rune '(quote (:eval :ok-if (brr@ :wonp) :failure-reason+))))
;; `(monitor ',rune '(quote (:target+ :eval :ok-if (brr@ :wonp) :failure-reason+))))


;; (defthm
;;   (implies (syntaxp name)



;;  (local
;;   (defthm
;;     alist2p-$arg1
;;     (implies (alist2p name  l)
;; 	     (alist2p '$arg1 l))
;;     :hints (("Goal"
;; 	     :use (:instance alist2p-$arg (name name) (l l))
;; 	     :in-theory (enable alist2p)
;; 	     ))
;;     )
;;     ;:rule-classes :forward-chaining)
;;   )

;;  (local
;;   (defthm
;;     array2p-$arg1
;;     (implies (array2p name  l)
;; 	     (array2p '$arg1 l))
;;     :hints (("Goal"
;; 	     :use (:instance array2p-$arg (name name) (l l))
;; 	     :in-theory (enable array2p)
;; 	     ))
;;     )
;;   )


;;  (local
;;   (defthm
;;     aref2-m-*-1
;;     (implies (and (alist2p name M1)
;; 		  (alist2p name M2)
;; 		  (equal (second (dimensions name M1))
;; 			 (first  (dimensions name M2)))
;; 		  (integerp i)
;; 		  (integerp j)
;; 		  (>= i 0)
;; 		  (>= j 0)
;; 		  (< i (first (dimensions name M1)))
;; 		  (< j (second (dimensions name M2))))
;; 	     (equal (aref2 name (m-* M1 M2) i j)
;; 		    (dot M1
;; 			 M2
;; 			 i
;; 			 (+ -1 (second (dimensions name M1)))
;; 			 j)))
;;     :hints (("Goal"
;; 	     :use (:instance aref2-m-* (m1 m1) (m2 m2) (i i) (j j))
;; 	     :in-theory (enable aref2 header default))))
;;   )

;; (local (include-book "arithmetic-5/top" :dir :system))
;; (defthmd det-lemma
;;   (implies (and (r3-matrixp m1)
;; 		(r3-matrixp m2)
;; 		)
;; 	   (equal (r3-m-determinant (m-* m1 m2)) (* (r3-m-determinant m1) (r3-m-determinant m2))))
;;   :hints (("Goal"
;; 	   :in-theory (enable r3-matrixp r3-m-determinant realp acl2-numberp)
;; 	   ))
;;   )

;; (encapsulate
;;  ()

;;  (local (in-theory nil))
;;  (local (include-book "arithmetic-5/top" :dir :system))

;;  (skip-proofs
;;   (local
;;    (defthm acl2-num-m-*m1m2
;;         (implies (and (r3-matrixp m1)
;;  		      (r3-matrixp m2)
;;  		      (integerp i)
;;  		      (integerp j)
;;  		      (>= i 0)
;;  		      (<= i 2)
;;  		      (>= j 0)
;;  		      (<= j 2))
;;  		 (ACL2-NUMBERP (AREF2 '$ARG1 (M-* M1 M2) i j))
;;  		 )
;; 	)
;;    )
;;   )

;;  (local
;;   (defthm
;;     alist2p-$arg1
;;     (implies (alist2p name  l)
;; 	     (alist2p '$arg1 l))
;;     :hints (("Goal"
;; 	     :use (:instance alist2p-$arg (name name) (l l))
;; 	     :in-theory (enable alist2p)
;; 	     ))
;;     )
;;     ;:rule-classes :forward-chaining)
;;   )

;;  (local
;;   (defthm
;;     array2p-$arg1
;;     (implies (array2p name  l)
;; 	     (array2p '$arg1 l))
;;     :hints (("Goal"
;; 	     :use (:instance array2p-$arg (name name) (l l))
;; 	     :in-theory (enable array2p)
;; 	     ))
;;     )
;;   )

;;  (local
;;   (defthm
;;     alist2p-$C
;;     (implies (alist2p name  l)
;; 	     (alist2p '$C l))
;;     :hints (("Goal"
;; 	     :use (:instance alist2p-$arg (name name) (l l))
;; 	     :in-theory (enable alist2p)
;; 	     ))
;;     )
;;   )

;;  (local
;;   (defthm
;;     array2p-$C
;;     (implies (array2p name  l)
;; 	     (array2p '$C l))
;;     :hints (("Goal"
;; 	     :use (:instance array2p-$arg (name name) (l l))
;; 	     :in-theory (enable array2p)
;; 	     )))
;;   )

;;  (local
;;   (defthm
;;     aref2-m-*-1
;;     (implies (and (alist2p name M1)
;; 		  (alist2p name M2)
;; 		  (equal (second (dimensions name M1))
;; 			 (first  (dimensions name M2)))
;; 		  (integerp i)
;; 		  (integerp j)
;; 		  (>= i 0)
;; 		  (>= j 0)
;; 		  (< i (first (dimensions name M1)))
;; 		  (< j (second (dimensions name M2))))
;; 	     (equal (aref2 name (m-* M1 M2) i j)
;; 		    (dot M1
;; 			 M2
;; 			 i
;; 			 (+ -1 (second (dimensions name M1)))
;; 			 j)))
;;     :hints (("Goal"
;; 	     :use (:instance aref2-m-* (m1 m1) (m2 m2) (i i) (j j))
;; 	     :in-theory (enable aref2 header default))))
;;   )

;;  (defthmd det-lemma
;;    (implies (and (r3-matrixp m1)
;; 		 (r3-matrixp m2)
;; 		 )
;; 	    (equal (r3-m-determinant (m-* m1 m2)) (* (r3-m-determinant m1) (r3-m-determinant m2))))
;;    :hints (("Goal"
;; 	    :in-theory (enable r3-matrixp r3-m-determinant realp acl2-numberp)
;; 	    ))
;;    )
;;  )


;; (defun r3-m-inverse (m)
;;   `((:header :dimensions (3 3)
;; 	     :maximum-length 10)
;;     ((0 . 0) . ,(/ (- (* (aref2 '$arg1 m 2 2) (aref2 '$arg1 m 3 3))
;; 		      (* (aref2 '$arg1 m 3 2) (aref2 '$arg1 m 2 3)))
;; 		   (determinant m)))
;;     ((0 . 1) . ,(/ (- (* (aref2 '$arg1 m 1 3) (aref2 '$arg1 m 3 2))
;; 		      (* (aref2 '$arg1 m 3 3) (aref2 '$arg1 m 1 2)))
;; 		   (determinant m)))
;;     ((0 . 2) . ,(/ (- (* (aref2 '$arg1 m 1 2) (aref2 '$arg1 m 2 3))
;; 		      (* (aref2 '$arg1 m 2 2) (aref2 '$arg1 m 1 3)))
;; 		   (determinant m)))
;;     ((1 . 0) . ,(/ (- (* (aref2 '$arg1 m 2 3) (aref2 '$arg1 m 3 1))
;; 		      (* (aref2 '$arg1 m 3 3) (aref2 '$arg1 m 2 1)))
;; 		   (determinant m)))
;;     ((1 . 1) . ,(/ (- (* (aref2 '$arg1 m 1 1) (aref2 '$arg1 m 3 3))
;; 		      (* (aref2 '$arg1 m 3 1) (aref2 '$arg1 m 1 3)))
;; 		   (determinant m)))
;;     ((1 . 2) . ,(/ (- (* (aref2 '$arg1 m 1 3) (aref2 '$arg1 m 2 1))
;; 		      (* (aref2 '$arg1 m 2 3) (aref2 '$arg1 m 1 1)))
;; 		   (determinant m)))
;;     ((2 . 0) . ,(/ (- (* (aref2 '$arg1 m 2 1) (aref2 '$arg1 m 3 2))
;; 		      (* (aref2 '$arg1 m 3 1) (aref2 '$arg1 m 2 2)))
;; 		   (determinant m)))
;;     ((2 . 1) . ,(/ (- (* (aref2 '$arg1 m 1 2) (aref2 '$arg1 m 3 1))
;; 		      (* (aref2 '$arg1 m 3 2) (aref2 '$arg1 m 1 1)))
;; 		   (determinant m)))
;;     ((2 . 2) . ,(/ (- (* (aref2 '$arg1 m 1 1) (aref2 '$arg1 m 2 2))
;; 		      (* (aref2 '$arg1 m 2 1) (aref2 '$arg1 m 1 2)))
;; 		   (determinant m)))
;;     )
;;   )

;; (local
;;  (defthm m-=-row-1-lemma
;;    (equal (m-=-row-1 m1 m2 m n)
;; 	  (if (zp m)
;; 	      (m-=-row m1 m2 0 n)
;; 	    (and (m-=-row m1 m2 m n)
;; 		 (m-=-row-1 m1 m2 (- m 1) n))))
;;    )
;;  )

;; (local
;;  (defthm m-=-row-lemma
;;    (equal (m-=-row m1 m2 m n)
;; 	  (if (zp n)
;; 	      (equal (fix (aref2 '$arg1 M1 m 0))
;; 		     (fix (aref2 '$arg2 M2 m 0)))
;; 	    (and (equal (fix (aref2 '$arg1 M1 m n))
;; 			(fix (aref2 '$arg2 M2 m n)))
;; 		 (m-=-row M1 M2 m (- n 1)))))
;;    )
;;  )

;; (skip-proofs
;;  (defthmd m-*-m-m-inverse
;;    (implies (and (r3-matrixp m)
;; 		 (not (= (determinant m) 0)))
;; 	    (m-= (m-* m (r3-m-inverse m)) (id-rotation)))
;;    :hints (("Goal"
;; 	    :use ((:instance array2p-alist2p (name '$arg1) (L m))
;; 		  (:instance aref2-m-* (m1 m) (m2 (r3-m-inverse m)) (name '$arg1))
;; 		  )
;; 	    :in-theory (e/d (alist2p m-= m-=-row-1 m-=-row) (aref2))
;; 	    )
;; 	   )
;;    )
;;  )

;; (skip-proofs
;;  (defthmd m-*-m-inverse-m
;;    (implies (and (r3-matrixp m)
;; 		 (not (= (determinant m) 0)))
;; 	    (m-= (m-* (r3-m-inverse m) m) (id-rotation)))
;;    )
;;  )




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
