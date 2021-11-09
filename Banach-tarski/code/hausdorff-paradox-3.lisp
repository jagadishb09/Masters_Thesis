(in-package "ACL2")

(include-book "hausdorff-paradox-2")

(defthmd generate-words-main-lemma-7-3
  (implies (natp n)
           (< n (len (generate-words-main (+ n 1)))))
  :hints (("Goal"
           :use ((:instance generate-words-main-lemma7-1 (m (+ n 1))))
           )))

(defthmd poles-list-length
  (implies (true-listp lst)
           (equal (len (poles-list lst))
                  (* 2 (len lst)))))

(defthmd pole-sequence-point-in-r3-1
  (implies (natp n)
           (equal (* 2 1/2 N) n)))

(encapsulate
  ()
  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd pole-sequence-point-in-r3-2
    (implies (and (natp n)
                  (oddp n))
             (integerp (/ (- n 1) 2))))

  (defthmd pole-sequence-point-in-r3-3
    (implies (and (integerp n)
                  (integerp (* 1/2 n)))
             (equal (* 2 1/2 N) n)))

  )

(defthmd pole-sequence-point-in-r3
  (implies (and (natp n)
                lst
                (< n (len (poles-list lst)))
                (true-listp lst))
           (point-in-r3 (nth n (poles-list lst))))
  :hints (("Goal"
           :in-theory (disable acl2-sqrt aref2 reducedwordp weak-wordp f-poles-1 f-poles-2 rotation r3-matrixp r3-m-inverse r3-m-determinant)
           :cases ((evenp n)
                   (oddp n))
           :do-not-induct t
           )
          ("Subgoal 2"
           :use ((:instance poles-list-lemma1 (lst lst) (n (/ n 2)))
                 (:instance poles-list-length (lst lst))
                 (:instance pole-sequence-point-in-r3-1)
                 (:instance rotation-is-r3-rotationp (w (NTH (* 1/2 N) LST)) (x (acl2-sqrt 2)))
                 (:instance f-poles-prop-3 (m (ROTATION (NTH (* 1/2 N) LST)
                                                        (ACL2-SQRT 2))))
                 )

           )
          ("Subgoal 1"
           :use ((:instance poles-list-lemma2 (lst lst) (n (/ (- n 1) 2)))
                 (:instance poles-list-length (lst lst))
                 (:instance pole-sequence-point-in-r3-1)
                 (:instance rotation-is-r3-rotationp (w (NTH (/ (- n 1) 2) LST)) (x (acl2-sqrt 2)))
                 (:instance f-poles-prop-3 (m (ROTATION (NTH (/ (- n 1) 2) LST)
                                                        (ACL2-SQRT 2))))
                 (:instance pole-sequence-point-in-r3-2 (n n))
                 )

           )
          ))

(defun poles-x-coordinates (poles-list)
  (if (atom poles-list)
      nil
    (append (list (aref2 :fake-name (car poles-list) 0 0))
            (poles-x-coordinates (cdr poles-list)))))

(defun x-coord-sequence-1 (n)
  (nth n (poles-x-coordinates (poles-list (generate-words-main (+ n 1))))))

(defun-sk exists-in-x-coord-sequence-1 (x)
  (exists i
          (and (natp i)
               (equal (x-coord-sequence-1 i) x))))

(defthmd x-coord-list-lemma1
  (implies (and (true-listp poles-lst)
                (natp n))
           (equal (nth n (poles-x-coordinates poles-lst))
                  (aref2 :fake-name (nth n poles-lst) 0 0))))

(defthmd exists-in-x-coord-sequence-1-lemma1
  (implies (and (natp n)
                (< n x))
           (and (TRUE-LISTP
                 (POLES-LIST (GENERATE-WORDS-MAIN (+ n 1))))
                (GENERATE-WORDS-MAIN (+ n 1))
                (true-listp (GENERATE-WORDS-MAIN (+ n 1)))
                (< n (* 2 x)))))

(defthmd exists-in-x-coord-sequence-1-lemma2
  (implies (and (point-in-r3 p)
                (point-in-r3 p2)
                (m-= p2 p))
           (equal (aref2 :fake-name p 0 0)
                  (aref2 :fake-name p2 0 0)
                  ))
  :hints (("Goal"
           :in-theory (enable m-=)
           )))

(defthmd exists-in-x-coord-sequence-1-lemma
  (implies (d-p p)
           (exists-in-x-coord-sequence-1 (aref2 :fake-name p 0 0)))
  :hints (("Goal"
           :use ((:instance exists-pole-n-thm (p p))
                 (:instance exists-in-x-coord-sequence-1-suff (i (exists-pole-n-witness p))
                            (x (aref2 :fake-name p 0 0)))
                 (:instance x-coord-list-lemma1 (n (exists-pole-n-witness p))
                            (poles-lst (poles-list (generate-words-main (+ (exists-pole-n-witness p) 1))))
                            )
                 (:instance exists-pole-n (pole p))
                 (:instance exists-in-x-coord-sequence-1-lemma1 (n (exists-pole-n-witness p))
                            (x (LEN (GENERATE-WORDS-MAIN (+ (EXISTS-POLE-N-WITNESS P) 1)))))
                 (:instance X-COORD-SEQUENCE-1 (n (EXISTS-POLE-N-WITNESS P)))
                 (:instance POLE-SEQUENCE (n (EXISTS-POLE-N-WITNESS P)))
                 (:instance pole-sequence-point-in-r3 (n (EXISTS-POLE-N-WITNESS P))
                            (lst (GENERATE-WORDS-MAIN (+ (EXISTS-POLE-N-WITNESS P) 1))))
                 (:instance generate-words-main-lemma-7-3 (n (exists-pole-n-witness p)))
                 (:instance poles-list-length (lst (generate-words-main (+ (exists-pole-n-witness p) 1))))
                 (:instance d-p (point p))
                 (:instance s2-def-p (point p))
                 (:instance exists-in-x-coord-sequence-1-lemma2
                            (p2 (POLE-SEQUENCE (EXISTS-POLE-N-WITNESS P)))
                            (p p))
                 )
           :in-theory nil
           )))

(defun x-coord-sequence (n)
  (if (posp n)
      (nth (- n 1) (poles-x-coordinates (poles-list (generate-words-main n))))
    0))

(defun-sk exists-in-x-coord-sequence (x)
  (exists i
          (and (posp i)
               (equal (x-coord-sequence i) x))))

(defthmd exists-in-x-coord-sequence-lemma-lemma1
  (implies (natp n)
           (posp (+ n 1))))

(defthmd exists-in-x-coord-sequence-lemma
  (implies (d-p p)
           (exists-in-x-coord-sequence (aref2 :fake-name p 0 0)))
  :hints (("Goal"
           :use ((:instance exists-in-x-coord-sequence-1-lemma (p p))
                 (:instance exists-in-x-coord-sequence-1 (x (AREF2 :FAKE-NAME P 0 0)))
                 (:instance exists-in-x-coord-sequence-suff
                            (i (+ (exists-in-x-coord-sequence-1-witness (aref2 :fake-name p 0 0)) 1))
                            (x (aref2 :fake-name p 0 0)))
                 (:instance exists-in-x-coord-sequence-lemma-lemma1
                            (n (EXISTS-IN-X-COORD-SEQUENCE-1-WITNESS (AREF2 :FAKE-NAME P 0 0))))
                 (:instance X-COORD-SEQUENCE-1
                            (n (EXISTS-IN-X-COORD-SEQUENCE-1-WITNESS (AREF2 :FAKE-NAME P 0 0))))
                 )
           :in-theory (disable poles-x-coordinates reducedwordp d-p generate-words-main poles-list poles word-exists)
           )))

(defun-sk exists-in-interval-but-not-in-x-coord-sequence-1 (A B)
  (exists x
          (and (realp x)
               (< A x)
               (< x B)
               (not (exists-in-x-coord-sequence x)))))


-----

;; (defthmd poles-x-coordinates-lemma1
;;   (implies (and (natp n)
;;                 lst
;;                 (true-listp lst))
;;            (real-listp (poles-x-coordinates (poles-list lst))))
;;   :hints (("Goal"
;;            :in-theory (disable acl2-sqrt f-poles-1 f-poles-2)
;;            )))

(skip-proofs
 (defthmd x-coord-sequence-lemma1
   (realp (x-coord-sequence n)))
 )

(encapsulate
  ()

  (local (include-book "nonstd/transcendentals/reals-are-uncountable-1" :dir :system))

  (defthm existence-of-x-not-in-sequence
    (exists-in-interval-but-not-in-x-coord-sequence-1 -1 1)
    :hints (("Goal"
             :use ((:functional-instance reals-are-not-countable
                                         (seq x-coord-sequence)
                                         (a (lambda () -1))
                                         (b (lambda () 1))
                                         (exists-in-sequence exists-in-x-coord-sequence)
                                         (exists-in-sequence-witness exists-in-x-coord-sequence-witness)
                                         (exists-in-interval-but-not-in-sequence exists-in-interval-but-not-in-x-coord-sequence-1)
                                         (exists-in-interval-but-not-in-sequence-witness exists-in-interval-but-not-in-x-coord-sequence-1-witness)))
             )
            ("Subgoal 4"
             :use (
                   (:instance exists-in-interval-but-not-in-x-coord-sequence-1-suff (x x))
                   )
             )))
  )

(defun-sk exists-in-interval-but-not-in-x-coord-sequence (A B)
  (exists x
          (and (realp x)
               (<= A x)
               (<= x B)
               (not (exists-in-x-coord-sequence x)))))

(defthm existence-of-x-not-in-sequence-lemma
  (exists-in-interval-but-not-in-x-coord-sequence -1 1)
  :hints (("Goal"
           :use ((:instance existence-of-x-not-in-sequence)
                 (:instance exists-in-interval-but-not-in-x-coord-sequence-1 (A -1) (B 1))
                 (:instance exists-in-interval-but-not-in-x-coord-sequence-suff (x (exists-in-interval-but-not-in-x-coord-sequence-1-witness -1 1)) (A -1) (B 1)))
           :in-theory nil
           )))
