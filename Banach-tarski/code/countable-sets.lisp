;; (include-book "workshops/2006/cowles-gamboa-euclid/Euclid/prime-fac" :dir :system)


(encapsulate
  (
   ((f *) => * :formals (n) :guard (posp n))
   ((g *) => * :formals (n) :guard (posp n)))

   (local (defun f (n)
            (declare (xargs :guard (posp n))
                     (ignore n))
            (list 0)))

   (local (defun g (n)
            (declare (xargs :guard (posp n))
                     (ignore n))
            (list 0)))

  ;; (defthmd listp-f
  ;;   (true-listp (f n)))

  ;; (defthmd listp-g
  ;;   (true-listp (g n)))

  )

;; (defun f-1 ()
;;   (list #\a #\b #\c))

;; (defun f (n)
;;   (nth (- n 1) (f-1)))

;; (defun g-1 ()
;;   (list #\p #\q #\r))

;; (defun g (n)
;;   (nth (- n 1) (g-1)))

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defun mod-remainder-2 (pow num)
    (if (> num 0)
        (if (not (equal (mod num 2) 0))
            (list pow num)
          (mod-remainder-2 (+ pow 1) (/ num 2)))
      nil))

  (defthmd mod-remainder-2-lemma-1
    (implies (and (> num 0)
                  (integerp pow)
                  (integerp num))
             (equal (len (mod-remainder-2 pow num)) 2)))

  (defun mod-remainder-3 (pow num)
    (if (> num 0)
        (if (not (equal (mod num 3) 0))
            (list pow num)
          (mod-remainder-3 (+ pow 1) (/ num 3)))
      nil))

  (defthmd mod-remainder-3-lemma-1
    (implies (and (> num 0)
                  (integerp pow)
                  (integerp num))
             (equal (len (mod-remainder-3 pow num)) 2)))
  )

(defun f-*-g-seq-i (i)
  (let ((rm-2 (mod-remainder-2 0 i)))
    (let ((rm-3 (mod-remainder-3 0 (nth 1 rm-2))))
      (if (equal (nth 1 rm-3) 1)
          (list (list (f (+ (nth 0 rm-2) 1)) (g (+ (nth 0 rm-3) 1))))
        (list 0)))))

(encapsulate
  ()

  (local (include-book "arithmetic/top" :dir :system))

  (defun f-*-g-seq-2 (i)
    (if (zp i)
        nil
      (append (f-*-g-seq-2 (- i 1)) (f-*-g-seq-i i))))
  )

(defun f-*-g-seq (i)
  (if (posp i)
      (f-*-g-seq-2 i)
    nil))

(defun f-*-g-sequence (n)
  (if (posp n)
      (nth (- n 1) (f-*-g-seq n))
    0))

(defthmd f-*-g-seq-i-lemma1
  (implies (posp n)
           (equal (len (f-*-g-seq-i n))
                  1)))

(defthmd f-*-g-seq-i-lemma2
  (implies (posp n)
           (true-listp (f-*-g-seq-i n))))

(defthmd f-*-g-seq-2-lemma1
  (equal (f-*-g-seq-2 1)
         (f-*-g-seq-i 1)))

(defthmd f-*-g-seq-2-lemma2
  (implies (natp n)
           (true-listp (f-*-g-seq-2 n))))

(defthm f-*-g-seq-2-lemma2-sub1/3
  (implies (AND (NOT (ZP N))
                (<= (+ -1 N) 0)
                (INTEGERP N)
                (< 0 N))
           (and (equal n 1)
                (posp 1)))
  :rule-classes nil)

(defthmd f-*-g-seq-2-lemma2-sub1/4
  (implies (and (true-listp x)
                (true-listp y)
                (equal (len x) p)
                (equal (len y) 1))
           (equal (len (append x y))
                  (+ p 1))))

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd f-*-g-seq-2-lemma3
    (implies (posp n)
             (equal (len (f-*-g-seq-2 n))
                    n))
    :hints (("Subgoal *1/3"
             :use ((:instance f-*-g-seq-2-lemma2-sub1/3 (n n))
                   (:instance f-*-g-seq-2-lemma1)
                   (:instance f-*-g-seq-i-lemma1 (n 1)))
             :in-theory nil
             )
            ("Subgoal *1/4"
             :use ((:instance f-*-g-seq-i-lemma1 (n n))
                   (:instance f-*-g-seq-2-lemma2-sub1/4 (x (F-*-G-SEQ-2 (+ -1 N)))
                              (y (F-*-G-SEQ-I N))
                              (p (LEN (F-*-G-SEQ-2 (+ -1 N))))))
             :in-theory (disable f-*-g-seq-i)
             )
            ))
  )

(defthmd f-*-g-seq-2-lemma4-1
  (implies (and (true-listp f)
                (true-listp g)
                (equal (len f) n)
                (equal (len g) 1))
           (equal (list (nth n (append f g)))
                  g)))

(defthmd f-*-g-seq-2-lemma4
  (implies (posp n)
           (equal (list (nth (- n 1) (f-*-g-seq-2 n)))
                  (f-*-g-seq-i n)))
  :hints (("Goal"
           :use ((:instance f-*-g-seq-2-lemma4-1 (f (f-*-g-seq-2 (- n 1)))
                            (g (f-*-g-seq-i n))
                            (n (- n 1)))
                 (:instance f-*-g-seq-i-lemma1 (n n))
                 (:instance f-*-g-seq-2-lemma3 (n (- n 1))))
           :do-not-induct t
           )))

-----

(defun-sk exists-pospn-3^n (n-2 q)
  (exists n-3
          (and (posp n-3)
               (equal (* (expt 2 n-2) (expt 3 n-3))
                      q))))

(defun-sk exists-pospn-2^n (q)
  (exists n-2
          (and (posp n-2)
               (exists-pospn-3^n n-2 q))))


(defthm f-*-g-seq-i-lemma3-sub*1/2-1
  (implies (and (integerp x)
                (integerp y)
                (integerp x1)
                (integerp y1)
                (equal (* (expt 2 x) (expt 3 y)) p)
                (equal (* (expt 2 x1) (expt 3 y1)) q)
                (equal p q))
           (and (equal x x1)
                (equal y y1)))
  :rule-classes nil
  )

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd f-*-g-seq-i-lemma3-sub1
    (implies (and (posp n1)
                  (posp n2)
                  (equal (* (expt 2 n1) (expt 3 n2)) q))
             (equal (mod q 2) 0)))
  )

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthm f-*-g-seq-i-lemma3-sub*1/2-1
    (implies (and (integerp x)
                  (> x 0)
                  (integerp y))
             (not (equal (* (expt 2 x) y)
                         1)))))


  (defthm f-*-g-seq-i-lemma3-sub*1/2-1
    (implies (and (integerp x)
                  (integerp y)
                  (equal (* (expt 2 x) (expt 3 y))
                         1))
             (and (equal x 0)
                  (equal y 0)))
    :hints (("Goal"
             :cases ((and (not (equal x 0)) (not (equal y 0)))
                     (and (equal x 0) (not (equal y 0)))
                     (and (not (equal x 0)) (equal y 0)))

             ))
    :rule-classes nil
    )
  )

  (defthm f-*-g-seq-i-lemma3-sub*1/2-1
    (implies (and (integerp x)
                  (integerp y)
                  (integerp x1)
                  (integerp y2)
                  (equal (* (expt 2 x) (expt 3 y)) q)
                  (equal (* (expt 2 x1) (expt 3 y1)) q2)
                  (equal q q2))
             (and (equal x x1)
                  (equal y y1)))
    :rule-classes nil
    )
  )


(encapsulate
  ()

  (local (include-book "arithmetic/top" :dir :system))

  (defthmd f-*-g-seq-i-lemma3
    (implies (and (exists-pospn-2^n q)
                  (posp x))
             (equal (mod-remainder-2 x q)
                    (list (+ x (exists-pospn-2^n-witness q))
                          (exists-pospn-3^n-witness (exists-pospn-2^n-witness q) q))))
    :hints (("Subgoal *1/2"
             ;:use ((:instance f-*-g-seq-i-lemma3-sub*1/2-1 (x (- (exists-pospn-2^n-witness q) 1))
              ;                (y (exists-pospn-2^n-witness (* q 1/2))))
               ;    (:instance exists-pospn-2^n=> (q q))
                ;   (:instance exists-pospn-2^n=> (q (* q 1/2))))
             :in-theory nil
             )
            ("Subgoal *1/1"
             :use ((:instance f-*-g-seq-i-lemma3-sub1 (n1 (exists-pospn-2^n-witness q))
                              (n2 (exists-pospn-3^n-witness (exists-pospn-2^n-witness q) q))))
             )
            ))
  )







---------

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

   (defthmd test-case-lemma1-sub1/3
     (IMPLIES
      (AND (NOT (ZIP N1))
           (NOT (= (FIX 2) 0))
           (< 0 N1)
           (IMPLIES (AND (POSP (+ N1 -1))
                         (POSP N2)
                         (EQUAL (NTH (+ -1 N1 -1) (F (+ N1 -1)))
                                P)
                         (EQUAL (NTH (+ -1 N2) (G N2)) Q))
                    (EQUAL (NTH (+ -1 (* (EXPT 2 (+ N1 -1)) (EXPT 3 N2)))
                                (F-*-G-SEQ (* (EXPT 2 (+ N1 -1)) (EXPT 3 N2))))
                           (LIST P Q))))
      (IMPLIES (AND (POSP N1)
                    (POSP N2)
                    (EQUAL (NTH (+ -1 N1) (F N1)) P)
                    (EQUAL (NTH (+ -1 N2) (G N2)) Q))
               (EQUAL (NTH (+ -1 (* (EXPT 2 N1) (EXPT 3 N2)))
                           (F-*-G-SEQ (* (EXPT 2 N1) (EXPT 3 N2))))
                      (LIST P Q))))))

(defun-sk exists-pospn-3^n (n-2 q)
  (exists n-3
          (and (posp n-3)
               (equal (* (expt 2 n-2) (expt 3 n-3))
                      q))))

(defun-sk exists-pospn-2^n (q)
  (exists n-2
          (and (posp n-2)
               (exists-pospn-3^n n-2 q))))

(defthmd exists-pospn-2^n=>
  (implies (exists-pospn-2^n q)
           (and (posp (exists-pospn-2^n-witness q))
                (equal (expt 2 (exists-pospn-2^n-witness q))
                       q))))

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd f-*-g-seq-i-lemma3-sub1
    (implies (and (posp n)
                  (equal (expt 2 n) q))
             (equal (mod q 2) 0)))

  (defthm f-*-g-seq-i-lemma3-sub*1/2-1
    (implies (and (integerp x)
                  (integerp y)
                  (equal (expt 2 x)
                         (expt 2 y)))
             (equal x y))
    :rule-classes nil
    )
  )

(defthmd f-*-g-seq-i

(encapsulate
  ()

  (local (include-book "arithmetic/top" :dir :system))

  (defthmd f-*-g-seq-i-lemma3
    (implies (and (exists-pospn-2^n q)
                  (posp x))
             (equal (mod-remainder-2 x q)
                    (list (+ x (exists-pospn-2^n-witness q)) 1)))
    :hints (("Subgoal *1/2"
             :use ((:instance f-*-g-seq-i-lemma3-sub*1/2-1 (x (- (exists-pospn-2^n-witness q) 1))
                              (y (exists-pospn-2^n-witness (* q 1/2))))
                   (:instance exists-pospn-2^n=> (q q))
                   (:instance exists-pospn-2^n=> (q (* q 1/2))))
             ;:in-theory nil
             )
            ("Subgoal *1/1"
             :use ((:instance f-*-g-seq-i-lemma3-sub1 (n (exists-pospn-2^n-witness q))))
             )
            ))
  )

(defun f-*-g-seq-i (i)
  (let ((rm-2 (mod-remainder-2 0 i)))
    (let ((rm-3 (mod-remainder-3 0 (nth 1 rm-2))))
      (if (equal (nth 1 rm-3) 1)
          (list (list (f (+ (nth 0 rm-2) 1)) (g (+ (nth 0 rm-3) 1))))
        (list 0)))))

(encapsulate
  ()

  (local (include-book "arithmetic/top" :dir :system))

  (defthmd f-*-g-seq-lemma1
    (implies (and (posp n1)
                  (posp n2))
             (POSP (* (EXPT 2 N1) (EXPT 3 N2)))))

  (defthmd test-case-lemma1
    (implies (and (posp n1)
                  (posp n2)
                  (equal (nth (- n1 1) (f n1)) p)
                  (equal (nth (- n2 1) (g n2)) q))
             (equal (nth (- (* (expt 2 n1) (expt 3 n2)) 1)
                         (f-*-g-seq (* (expt 2 n1) (expt 3 n2))))
                    (list p q)))
    :hints (("Goal"
             :use ((:instance f-*-g-seq-2-lemma4 (n (* (expt 2 n1) (expt 3 n2))))
                   (:instance f-*-g-seq-lemma1))
             :in-theory nil
             :do-not-induct t
             )))
  )




(defun generate-angle-2 (point poles-list2 n1 n2 zero-th-list)
  (if (atom poles-list2)
      zero-th-list
    (let ((updated-list (update-nth (- (* (expt 2 n1) (expt 3 n2)) 1) (list point (car poles-list2))
                                    zero-th-list)))
      (generate-angle-2 point (cdr poles-list2) n1 (+ n2 1) updated-list))))

(defun return-zero-list (total-length)
  (if (zp (- total-length 1))
      nil
    (append (list 0) (return-zero-list (- total-length 1)))))


(defun generate-angle-1 (poles-list1 poles-list2 n1 n2 zero-th-list)
  (if (atom poles-list1)
      zero-th-list
    (let ((updated-list (generate-angle-2 (car poles-list1) poles-list2 n1 n2 zero-th-list)))
      (generate-angle-1 (cdr poles-list1) poles-list2 (+ n1 1) n2 updated-list))))

(defun f-*-g (list1 list2)
  (let ((zero-th-list (return-zero-list (* (expt 2 (len list1)) (expt 3 (len list2))))))
    (generate-angle-1 list1 list2 1 1 zero-th-list)))

(defthmd test-case
  (implies (and (posp n)
                (posp m)
                (equal (nth n (f)) p)
                (equal (nth m (g)) q))
           (equal (nth (- (* (expt 2 (+ n 1)) (expt 3 (+ m 1))) 1) (f-*-g (f) (g)))
                  (list p q))))
