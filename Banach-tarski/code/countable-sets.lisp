; Banach-Tarski theorem
;
; Proof of Banach-Tarski theorem for the surface of the spehere centered at the
; origin with radius equal to 1.
;
;
; Copyright (C) 2021 University of Wyoming
;
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.
;
; Main Authors: Jagadish Bapanapally (jagadishb285@gmail.com)
;
; Contributing Authors:
;   Ruben Gamboa (ruben@uwyo.edu)

(in-package "ACL2")

(local (include-book "projects/quadratic-reciprocity/euclid" :dir :system))

; cert_param: (uses-acl2r)

(encapsulate
  (((f *) => *)
   ((g *) => *))

   (local (defun f (n)
            (declare (ignore n))
            (list 0)))

   (local (defun g (n)
            (declare (ignore n))
            (list 0)))
   )

;; (defun f-1 ()
;;   (list #\a #\b #\c))

;; (defun g-1 ()
;;   (list #\p #\q #\r))

;; (defun f (n)
;;   (if (posp n)
;;       (nth (- n 1) (f-1))
;;     0))

;; (defun g (n)
;;   (if (posp n)
;;       (nth (- n 1) (g-1))
;;     0))

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
          (if (or (equal (nth 0 rm-2) 0)
                  (equal (nth 0 rm-3) 0))
              (list 0)
            (list (list (f (nth 0 rm-2)) (g (nth 0 rm-3)))))
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

(encapsulate
  ()
  (local (include-book "arithmetic-5/top" :dir :system))

  (local
   (defthmd integerp=>divides
     (implies (and (integerp x)
                   (integerp y)
                   (not (equal y 0))
                   (INTEGERP (/ x y)))
              (rtl::divides y x))
     :hints (("Goal"
              :in-theory (enable rtl::divides)
              ))))

  (local
   (defthmd integerp=>divides-1
     (implies (and (integerp x)
                   (integerp y)
                   (not (equal y 0))
                   (rtl::divides y x))
              (integerp (/ x y)))
     :hints (("Goal"
              :in-theory (enable rtl::divides)
              ))))

  (local
   (defthmd mod-2-x>0-sub1/3-1
     (implies (and (integerp x)
                   (< 0 x)
                   (INTEGERP (* 1/3 (EXPT 2 X))))
              (INTEGERP (* 1/3 (EXPT 2 (+ -1 x)))))
     :hints (("Goal"
              :use ((:instance integerp=>divides (x (EXPT 2 X)) (y 3))
                    (:instance rtl::euclid (p 3) (a 2) (b (EXPT 2 (+ -1 x)))))
              :in-theory (enable rtl::primep rtl::least-divisor rtl::divides)
              ))))

  (defthmd mod-2-x>0-sub1/3
    (IMPLIES (AND (NOT (ZIP X))
                  (NOT (= (FIX 2) 0))
                  (< 0 X)
                  (IMPLIES (POSP (+ X -1))
                           (< 0 (MOD (EXPT 2 (+ X -1)) 3))))
             (IMPLIES (POSP X)
                      (< 0 (MOD (EXPT 2 X) 3))))
    :hints (("Goal"
             :use (mod-2-x>0-sub1/3-1)
             )))

  (local
   (defthmd mod-3-y>0-sub1/3-1
     (implies (and (integerp y)
                   (< 0 y)
                   (INTEGERP (* 1/2 (EXPT 3 y))))
              (INTEGERP (* 1/2 (EXPT 3 (+ -1 y)))))
     :hints (("Goal"
              :use ((:instance integerp=>divides (x (EXPT 3 y)) (y 2))
                    (:instance rtl::euclid (p 2) (a 3) (b (EXPT 3 (+ -1 y)))))
              :in-theory (enable rtl::primep rtl::least-divisor rtl::divides)
              ))))

  (defthmd mod-3-y>0-sub1/3
    (IMPLIES (AND (NOT (ZIP Y))
                  (NOT (= (FIX 3) 0))
                  (< 0 Y)
                  (IMPLIES (POSP (+ Y -1))
                           (< 0 (MOD (EXPT 3 (+ Y -1)) 2))))
             (IMPLIES (POSP Y)
                      (< 0 (MOD (EXPT 3 Y) 2))))
    :hints (("Goal"
             :use (mod-3-y>0-sub1/3-1)
             )))

  )

(defthmd mod-2-x>0
  (implies (posp x)
           (> (mod (expt 2 x) 3) 0))
  :hints (("Subgoal *1/3"
           :use (:instance mod-2-x>0-sub1/3)
           )))

(defthmd mod-3-y>0
  (implies (posp y)
           (> (mod (expt 3 y) 2) 0))
  :hints (("Subgoal *1/3"
           :use (:instance mod-3-y>0-sub1/3)
           )))

(encapsulate
  ()
  (local (include-book "arithmetic/top-with-meta" :dir :system))

  (defthmd 2^x*3^y=1=>xy=0-1
    (implies (and (> n1 0)
                  (integerp n1))
             (> (EXPT 2 N1) 1)))

  (defthmd 2^x*3^y=1=>xy=0-2
    (implies (and (> n2 0)
                  (integerp n2))
             (> (EXPT 3 N2) 1)))

  (defthmd 2^x*3^y=1=>xy=0-3
    (implies (and (realp x)
                  (realp y)
                  (> x 1)
                  (> y 1))
             (> (* x y) 1)))

  (defthmd 2^x*3^y=1=>xy=0-4
    (implies (and (integerp n1)
                  (integerp n2)
                  (> n1 0)
                  (> n2 0))
             (> (* (expt 2 n1) (expt 3 n2)) 1))
    :hints (("Goal"
             :use ((:instance 2^x*3^y=1=>xy=0-1)
                   (:instance 2^x*3^y=1=>xy=0-2)
                   (:instance 2^x*3^y=1=>xy=0-3 (x (expt 2 n1)) (y (expt 3 n2))))
             )))

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd 2^x*3^y=1=>xy=0-5-1
    (implies (and (realp x)
                  (realp y)
                  (> y 0)
                  (realp z)
                  (< z x))
             (< (* y z) (* y x))))

  (defthmd 2^x*3^y=1=>xy=0-5
    (implies (and (< 1 x)
                  (realp x))
             (< (/ 1 x) 1)))

  (defthmd 2^x*3^y=1=>xy=0-6
    (implies (and (realp x)
                  (realp y)
                  (equal x y))
             (equal (mod x 3)
                    (mod y 3))))
  )

(encapsulate
  ()
  (local (include-book "arithmetic/top" :dir :system))

  (defthmd 2^x*3^y=1=>xy=0-7
    (implies (and (< 0 y)
                  (integerp y))
             (equal (mod (expt 3 y) 3) 0)))
  )

(encapsulate
  ()
  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd 2^x*3^y=1=>xy=0-8
    (implies (and (realp x)
                  (realp y)
                  (> x 0)
                  (equal (* x y) 1))
             (equal (/ 1 x) y))))

(encapsulate
  ()
  (local (include-book "arithmetic/top" :dir :system))

  (defthmd 2^x*3^y=1=>xy=0-9
    (implies (and (integerp x)
                  (< x 0)
                  (< 0 y)
                  (integerp y))
             (not (equal (* (expt 2 x) (expt 3 y)) 1)))
    :hints (("Goal"
             :do-not-induct t
             :use ((:instance 2^x*3^y=1=>xy=0-6 (x (expt 2 (- x))) (y (expt 3 y)))
                   (:instance mod-2-x>0 (x (- x)))
                   (:instance 2^x*3^y=1=>xy=0-8 (x (expt 2 x)) (y (expt 3 y)))
                   (:instance 2^x*3^y=1=>xy=0-7 (y y)))
             )))

  (defthmd 2^x*3^y=1=>xy=0-10
    (implies (and (integerp x)
                  (> x 0)
                  (> 0 y)
                  (integerp y))
             (not (equal (* (expt 2 x) (expt 3 y)) 1)))
    :hints (("Goal"
             :do-not-induct t
             :use ((:instance 2^x*3^y=1=>xy=0-6 (x (expt 3 (- y))) (y (expt 2 x)))
                   (:instance mod-2-x>0 (x x))
                   (:instance 2^x*3^y=1=>xy=0-8 (y (expt 2 x)) (x (expt 3 (- y))))
                   (:instance 2^x*3^y=1=>xy=0-7 (y (- y))))
             )))
  )

(encapsulate
  ()
  (local (include-book "arithmetic-5/top" :dir :system))

  (defthm 2^x*3^y=1=>xy=0
    (implies (and (integerp x)
                  (integerp y)
                  (equal (* (expt 2 x) (expt 3 y)) 1))
             (and (equal x 0)
                  (equal y 0)))
    :hints (("Goal"
            :cases ((and (> x 0) (> y 0))
                    (and (< x 0) (< y 0))
                    (and (< x 0) (> y 0))
                    (and (> x 0) (< y 0)))
             :do-not-induct t
             )
            ("Subgoal 3"
             :use ((:instance 2^x*3^y=1=>xy=0-4 (n1 (- x)) (n2 (- y)))
                   (:instance 2^x*3^y=1=>xy=0-5 (x (* (expt 2 (- x)) (expt 3 (- y))))))
             )
            ("Subgoal 2"
             :use ((:instance 2^x*3^y=1=>xy=0-9))
             :in-theory nil
             )
            ("Subgoal 1"
             :use ((:instance 2^x*3^y=1=>xy=0-10))
             :in-theory nil
             )
            )
    :rule-classes nil)
  )

(encapsulate
  ()
  (local (include-book "arithmetic-5/top" :dir :system))

  (defthm 2^x*3^y=2^x1*3^y1
    (implies (and (integerp x)
                  (integerp y)
                  (integerp x1)
                  (integerp y1)
                  (equal (* (expt 2 x) (expt 3 y))
                         (* (expt 2 x1) (expt 3 y1))))
             (and (equal x x1)
                  (equal y y1)))
    :hints (("Goal"
             :use ((:instance 2^x*3^y=1=>xy=0 (x (- x x1)) (y (- y y1))))
             ))
    :rule-classes nil)
  )

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
                (posp (exists-pospn-3^n-witness (exists-pospn-2^n-witness q) q))
                (equal (* (expt 2 (exists-pospn-2^n-witness q))
                          (expt 3 (exists-pospn-3^n-witness (exists-pospn-2^n-witness q) q)))
                       q))))

(defthmd mod-remainder-2=>
  (implies (and (integerp x)
                (realp q)
                (> q 0)
                (equal (mod q 2) 0))
           (equal (mod-remainder-2 x q)
                  (mod-remainder-2 (+ x 1) (/ q 2)))))

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd f-*-g-seq-i-lemma3-*1/1
    (implies (and (posp n1)
                  (posp n2)
                  (equal (* (expt 2 n1) (expt 3 n2)) q))
             (equal (mod q 2) 0)))
  )

(defthmd f-*-g-seq-i-lemma3-1/2.1
  (IMPLIES
   (AND
    (EXISTS-POSPN-2^N (* Q 1/2))
    (< 0 Q)
    (EQUAL (MOD Q 2) 0)
    (EQUAL
     (MOD-REMAINDER-2 (+ X 1) (* Q 1/2))
     (LIST (+ (+ X 1)
              (EXISTS-POSPN-2^N-WITNESS (* Q 1/2)))
           (EXPT 3
                 (EXISTS-POSPN-3^N-WITNESS (EXISTS-POSPN-2^N-WITNESS (* Q 1/2))
                                           (* Q 1/2)))))
    (EXISTS-POSPN-2^N Q)
    (INTEGERP X))
   (EQUAL (MOD-REMAINDER-2 X Q)
          (LIST (+ X (EXISTS-POSPN-2^N-WITNESS Q))
                (EXPT 3
                      (EXISTS-POSPN-3^N-WITNESS (EXISTS-POSPN-2^N-WITNESS Q)
                                                Q)))))
  :hints (("Goal"
           :use ((:instance mod-remainder-2=> (x x) (q q))
                 (:instance 2^x*3^y=1=>xy=0-4 (n1 (exists-pospn-2^n-witness q))
                            (n2 (exists-pospn-3^n-witness (exists-pospn-2^n-witness q) q)))
                 (:instance exists-pospn-2^n=> (q q))
                 (:instance exists-pospn-2^n=> (q (* q 1/2)))
                 (:instance 2^x*3^y=2^x1*3^y1
                            (x (+ (EXISTS-POSPN-2^N-WITNESS (* Q 1/2)) 1))
                            (y (EXISTS-POSPN-3^N-WITNESS (EXISTS-POSPN-2^N-WITNESS (* Q 1/2))
                                                         (* Q 1/2)))
                            (x1 (EXISTS-POSPN-2^N-WITNESS Q))
                            (y1 (EXISTS-POSPN-3^N-WITNESS (EXISTS-POSPN-2^N-WITNESS Q)
                                                          Q)))
                 )
           ))
  )

(encapsulate
  ()

  (local (include-book "arithmetic/top" :dir :system))

  (defthmd f-*-g-seq-i-lemma3-1/2.2-sub1-1
    (IMPLIES (AND (EQUAL (MOD (* 2 Y) 2) 0)
                  (EQUAL (MOD-REMAINDER-2 X (* 2 Y))
                         (MOD-REMAINDER-2 (+ X 1)
                                          (* (* 2 Y) 1/2)))
                  (INTEGERP X)
                  (NOT (EQUAL (MOD Y 2) 0))
                  (REALP Y)
                  (< 0 Y))
             (EQUAL (MOD-REMAINDER-2 X (* 2 Y))
                    (LIST (+ X 1) Y)))))

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd f-*-g-seq-i-lemma3-1/2.2-sub1-2
    (implies (integerp x)
             (equal (mod (* 2 x) 2) 0))
    :hints (("Goal"
             :in-theory (enable mod floor1)
             )))
  )

(encapsulate
  ()

  (local (include-book "arithmetic/top" :dir :system))

  (defthmd f-*-g-seq-i-lemma3-1/2.2-sub1-3
    (implies (and (integerp x)
                  (not (equal (mod y 2) 0))
                  (integerp y)
                  (> y 0))
             (equal (mod-remainder-2 x (* 2 y))
                    (list (+ x 1) y)))
    :hints (("Goal"
             :use ((:instance mod-remainder-2 (pow x)
                              (num (* 2 y))))
             :in-theory nil
             :do-not-induct t
             )
            ("Subgoal 2"
             :use (:instance f-*-g-seq-i-lemma3-1/2.2-sub1-1)
             )
            ("Subgoal 1"
             :use (:instance f-*-g-seq-i-lemma3-1/2.2-sub1-2 (x y))
             )
            ))
  )

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd f-*-g-seq-i-lemma3-1/2.2-sub1-4
    (implies (posp y)
             (and (integerp (expt 3 y))
                  (> (expt 3 y) 0)))
    )
  )

(encapsulate
  ()

  (local (include-book "arithmetic/top" :dir :system))

  (defthm f-*-g-seq-i-lemma3-1/2.2-sub1-5
    (implies (and (not (posp (- x 1)))
                  (posp x))
             (equal x 1))
    :rule-classes nil)
  )

(encapsulate
  ()

  (local (include-book "arithmetic/top" :dir :system))

  (defthmd f-*-g-seq-i-lemma3-1/2.2-sub1
    (IMPLIES (AND (NOT (POSP (+ -1 (EXISTS-POSPN-2^N-WITNESS Q))))
                  (NOT (EXISTS-POSPN-2^N (* Q 1/2)))
                  (< 0 Q)
                  (EQUAL (MOD Q 2) 0)
                  (EXISTS-POSPN-2^N Q)
                  (INTEGERP X))
             (EQUAL (MOD-REMAINDER-2 X Q)
                    (LIST (+ X (EXISTS-POSPN-2^N-WITNESS Q))
                          (expt 3 (EXISTS-POSPN-3^N-WITNESS (EXISTS-POSPN-2^N-WITNESS Q)
                                                    Q)))))
    :hints (("Goal"
             :use (
                   (:instance exists-pospn-2^n=> (q q))
                   (:instance mod-3-y>0
                              (y (EXISTS-POSPN-3^N-WITNESS 1 Q)))
                   (:instance f-*-g-seq-i-lemma3-1/2.2-sub1-3 (x x)
                              (y (expt 3 (EXISTS-POSPN-3^N-WITNESS 1 Q))))
                   (:instance f-*-g-seq-i-lemma3-1/2.2-sub1-4
                              (y (EXISTS-POSPN-3^N-WITNESS 1 Q)))
                   (:instance f-*-g-seq-i-lemma3-1/2.2-sub1-5 (x (EXISTS-POSPN-2^N-WITNESS Q))))
             :do-not-induct t
             ))
    )
  )

(defthmd f-*-g-seq-i-lemma3-1/2.2
  (IMPLIES
   (AND (NOT (EXISTS-POSPN-2^N (* Q 1/2)))
        (< 0 Q)
        (EQUAL (MOD Q 2) 0)
        (EXISTS-POSPN-2^N Q)
        (INTEGERP X))
   (EQUAL (MOD-REMAINDER-2 X Q)
          (LIST (+ X (EXISTS-POSPN-2^N-WITNESS Q))
                (EXPT 3
                      (EXISTS-POSPN-3^N-WITNESS (EXISTS-POSPN-2^N-WITNESS Q)
                                                Q)))))
  :hints (("Goal"
           :cases ((not (posp (- (EXISTS-POSPN-2^N-WITNESS Q) 1))))
           :do-not-induct t
           )
          ("Subgoal 2"
           :use ((:instance EXISTS-POSPN-2^N-suff (n-2 (- (EXISTS-POSPN-2^N-WITNESS q) 1))
                            (q (* q 1/2)))
                 (:instance exists-pospn-2^n=> (q q))
                 (:instance EXISTS-POSPN-3^N-suff
                            (n-3 (EXISTS-POSPN-3^N-WITNESS (EXISTS-POSPN-2^N-WITNESS Q)
                                                           Q))
                            (n-2 (- (EXISTS-POSPN-2^N-WITNESS q) 1))
                            (q (* q 1/2))))
           )
          ("Subgoal 1"
           :use (:instance f-*-g-seq-i-lemma3-1/2.2-sub1)
           )
          ))

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd f-*-g-seq-i-lemma3
    (implies (and (exists-pospn-2^n q)
                  (integerp x))
             (equal (mod-remainder-2 x q)
                    (list (+ x (exists-pospn-2^n-witness q))
                          (expt 3 (exists-pospn-3^n-witness (exists-pospn-2^n-witness q) q)))))
    :hints (("Subgoal *1/2"
             :cases ((EXISTS-POSPN-2^N (* Q 1/2)))
             :in-theory nil
             )
            ("Subgoal *1/2.2"
             :in-theory nil
             :use ((:instance f-*-g-seq-i-lemma3-1/2.2))
             )
            ("Subgoal *1/2.1"
             :in-theory nil
             :use ((:instance f-*-g-seq-i-lemma3-1/2.1))
             )
            ("Subgoal *1/1"
             :use ((:instance f-*-g-seq-i-lemma3-*1/1 (n1 (exists-pospn-2^n-witness q))
                              (n2 (exists-pospn-3^n-witness (exists-pospn-2^n-witness q) q))))
             )
            ))
  )

(encapsulate
  ()

  (local (include-book "arithmetic/top" :dir :system))

  (defthmd f-*-g-seq-i-lemma4
    (implies (and (integerp x)
                  (posp y))
             (equal (mod-remainder-3 x (expt 3 y))
                    (list (+ x y) 1)))))

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

(encapsulate
  ()

  (local (include-book "arithmetic/top" :dir :system))

  (defthmd f-*-g-seq-lemma1
   (implies (and (posp n1)
                 (posp n2))
            (POSP (* (EXPT 2 N1) (EXPT 3 N2)))))

  (defthmd f-*-g-seq-1
    (implies (posp n1)
             (integerp n1)))

  (defthmd f-*-g-seq-nth-value
    (implies (and (posp n1)
                  (posp n2)
                  (equal (f n1) p)
                  (equal (g n2) q))
             (equal (nth (- (* (expt 2 n1) (expt 3 n2)) 1)
                         (f-*-g-seq (* (expt 2 n1) (expt 3 n2))))
                    (list p q)))
    :hints (("Goal"
             :use ((:instance f-*-g-seq-2-lemma4 (n (* (expt 2 n1) (expt 3 n2))))
                   (:instance f-*-g-seq-lemma1)
                   (:instance f-*-g-seq-i-lemma3 (x 0)
                              (q (* (expt 2 n1) (expt 3 n2)))
                              )
                   (:instance exists-pospn-2^n-suff (n-2 n1)
                              (q (* (expt 2 n1) (expt 3 n2))))
                   (:instance exists-pospn-3^n-suff
                              (n-3 n2)
                              (n-2 n1)
                              (q (* (expt 2 n1) (expt 3 n2))))
                   (:instance 2^x*3^y=2^x1*3^y1
                              (x n1) (y n2)
                              (x1 (EXISTS-POSPN-2^N-WITNESS (* (EXPT 2 N1) (EXPT 3 N2))))
                              (y1 (EXISTS-POSPN-3^N-WITNESS
                                   (EXISTS-POSPN-2^N-WITNESS (* (EXPT 2 N1) (EXPT 3 N2)))
                                   (* (EXPT 2 N1) (EXPT 3 N2)))))
                   (:instance f-*-g-seq-i-lemma3 (q (* (expt 2 n1) (expt 3 n2)))
                              (x 0))
                   (:instance f-*-g-seq-i-lemma4 (x 0) (y n2))
                   (:instance f-*-g-seq-1 (n1 n1))
                   (:instance exists-pospn-2^n=>
                              (q (* (expt 2 n1) (expt 3 n2))))
                   (:instance f-*-g-seq-1 (n1 n2))
                   (:instance f-*-g-seq-1 (n1 (EXISTS-POSPN-3^N-WITNESS
                                               (EXISTS-POSPN-2^N-WITNESS (* (EXPT 2 N1) (EXPT 3 N2)))
                                               (* (EXPT 2 N1) (EXPT 3 N2)))))
                   (:instance f-*-g-seq-1 (n1 (EXISTS-POSPN-2^N-WITNESS (* (EXPT 2 N1) (EXPT 3 N2)))))
                   )
             :do-not-induct t
             )))
  )

(defthmd f-*-g-sequence-nth
  (implies (and (posp n1)
                (posp n2)
                (equal (f n1) p)
                (equal (g n2) q))
           (equal (f-*-g-sequence (* (expt 2 n1) (expt 3 n2)))
                  (list p q)))
  :hints (("Goal"
           :use ((:instance f-*-g-seq-nth-value (n1 n1) (n2 n2) (p (f n1)) (q (g n2)))
                 (:instance 2^x*3^y=1=>xy=0-4 (n1 n1) (n2 n2)))
           )))
