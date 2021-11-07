(in-package "ACL2")

(include-book "hausdorff-paradox-2")

;; (defthmd two-poles-for-all-rotations-1
;;   (implies (and (point-in-r3 p)
;;                 (point-in-r3 p1)
;;                 (point-in-r3 p2)
;;                 (or (m-= p1 p)
;;                     (m-= p2 p)))
;;            (or (equal p1 p)
;;                (equal p2 p)))
;;   :hints (("Goal"
;;            :in-theory (e/d (m-=) (poles word-exists reducedwordp weak-wordp acl2-sqrt aref2))
;;            )))

;; (defthmd generate-words-main-is-a-list-1
;;   (implies (natp n)
;;            (true-listp (generate-words-main n))))

(defun poles-list (word-list)
  (if (atom word-list)
      nil
    (append (poles (car word-list))
            (poles-list (cdr word-list)))))

(defthmd poles-list-lemma1
  (implies (and (true-listp lst)
                (natp n)
                (< n (len lst)))
           (equal (nth (* 2 n) (poles-list lst))
                  (first (poles (nth n lst)))))
  :hints (("Goal"
           :in-theory (disable f-poles-1 f-poles-2 aref2 reducedwordp rotation acl2-sqrt)
           )))

(defthmd poles-list-lemma2
  (implies (and (true-listp lst)
                (natp n)
                (< n (len lst)))
           (equal (nth (+ (* 2 n) 1) (poles-list lst))
                  (second (poles (nth n lst)))))
  :hints (("Goal"
           :in-theory (disable f-poles-1 f-poles-2 aref2 reducedwordp rotation acl2-sqrt)
           )))

(defun pole-sequence (n)
  (nth n (poles-list (generate-words-main (+ n 1)))))

(defun poles-x-coordinates (poles-list)
  (if (atom poles-list)
      nil
    (append (list (aref2 :fake-name (car poles-list) 0 0))
            (poles-x-coordinates (cdr poles-list)))))

(defthmd poles-x-coordinates-lemma1
  (implies (and (natp n)
                lst
                (true-listp lst))
           (real-listp (poles-x-coordinates (poles-list lst))))
  :hints (("Goal"
           :in-theory (disable acl2-sqrt f-poles-1 f-poles-2)
           )))

--

(defun x-coord-sequence (n)
  (if (posp n)
      (nth (- n 1) (poles-x-coordinates (poles-list (generate-words-main (+ n 1)))))
    0))

(skip-proofs
 (defthmd x-coord-sequence-lemma1
   (realp (x-coord-sequence n)))
 )

(defun-sk exists-in-x-coord-sequence (x)
  (exists i
          (and (posp i)
               (equal (x-coord-sequence i) x))))

(defun-sk exists-in-interval-but-not-in-x-coord-sequence (A B)
  (exists x
          (and (realp x)
               (< A x)
               (< x B)
               (not (exists-in-x-coord-sequence x)))))

(skip-proofs
 (defthmd x-coord-sequence-lemma2
   (IMPLIES (AND (REALP X)
              (< A X)
              (< X B)
              (NOT (EXISTS-IN-X-COORD-SEQUENCE X)))
         (EXISTS-IN-INTERVAL-BUT-NOT-IN-X-COORD-SEQUENCE A B))
 ))

(encapsulate
  ()

  (local (include-book "nonstd/transcendentals/reals-are-uncountable-1" :dir :system))

  (skip-proofs
   (defthm x-coord-sequence-lemma2
     (IMPLIES (AND (REALP X)
                   (< A X)
                   (< X B)
                   (NOT (EXISTS-IN-X-COORD-SEQUENCE X)))
              (EXISTS-IN-INTERVAL-BUT-NOT-IN-X-COORD-SEQUENCE A B))
     ))

  (defthm existence-of-x-not-in-sequence-lemma
    (exists-in-interval-but-not-in-x-coord-sequence -1 1)
    :hints (("Goal"
             :use ((:functional-instance reals-are-not-countable
                                         (seq x-coord-sequence)
                                         (a (lambda () -1))
                                         (b (lambda () 1))
                                         (exists-in-sequence exists-in-x-coord-sequence)
                                         (exists-in-sequence-witness exists-in-x-coord-sequence-witness)
                                         (exists-in-interval-but-not-in-sequence exists-in-interval-but-not-in-x-coord-sequence)
                                         (exists-in-interval-but-not-in-sequence-witness exists-in-interval-but-not-in-x-coord-sequence-witness)))
             )
            ("Goal"
             :use ((:instance x-coord-sequence-lemma2 (x x) (a a) (b b))
                   (:instance x-coord-sequence-lemma1)
                   )
             :in-theory (disable x-coord-sequence-lemma2 aref2)
             )

            ))
  )

(defun-sk exists-pole-n (pole)
  (exists n
          (and (natp n)
               (m-= (pole-sequence n) pole))))

(defthmd exists-pole-n-thm
  (implies (d-p p)
           (exists-pole-n p))
  :hints (("Goal"
           :use ((:instance exists-pole-n-suff (n (* 2 (exists-word-n-witness (word-exists-witness p)))))
                 (:instance exists-word-n-thm (w (word-exists-witness p)))
                 (:instance reducedwordp=>weak-wordp (x (word-exists-witness p))))
           :in-theory (disable aref2 m-= rotation reducedwordp r3-matrixp r3-rotationp weak-wordp acl2-sqrt poles generate-words-main)
           :do-not-induct t
           )))



---

(defun weak-words-reco (wp)
  (if (atom wp)
      t
    (and (weak-wordp (car wp))
         (weak-words-reco (cdr wp)))))

(defun weak-words-listp (wp)
  (and (consp wp)
       (weak-words-reco wp)))

(defthmd weak-words-listp-lemma1-sub1/2
  (IMPLIES (AND (CONSP (GENERATE-WORDS-MAIN M))
                (INTEGERP M)
                (< 0 M))
           (equal (NTH 0 (GENERATE-WORDS-MAIN M))
                  nil))
  )

(IMPLIES
 (AND
   (NOT (ENDP (GENERATE-WORDS-FUNC IN-LIST (+ N 1))))
   (NOT (ZP N))
   (IMPLIES (AND (NATP (+ -1 N))
                 (EQUAL IN-LIST '(NIL (#\a) (#\b) (#\c) (#\d))))
            (WEAK-WORDP (NTH (+ -1 N)
                             (GENERATE-WORDS-FUNC IN-LIST (+ (+ -1 N) 1))))))
 (IMPLIES (AND (NATP N)
               (EQUAL IN-LIST '(NIL (#\a) (#\b) (#\c) (#\d))))
          (WEAK-WORDP (NTH N
                           (GENERATE-WORDS-FUNC IN-LIST (+ N 1))))))

(defthmd weak-words-listp-lemma1-sub1/3.2-1/4
  (implies (and (natp n)
                (equal in-list '(NIL (#\a) (#\b) (#\c) (#\d))))
           (weak-wordp (nth n (generate-words-func in-list (+ n 1))))))
  :hints (("Subgoal *1/6"
           :in-theory nil
           )))

(defthmd weak-words-listp-lemma1-sub1/3.2
  (implies (and (posp m)
                (natp n)
                (equal in-list '(NIL (#\a) (#\b) (#\c) (#\d))))
           (weak-wordp (nth n (generate-words-func in-list m)))))


-----

(IMPLIES (AND (NOT (ENDP (GENERATE-WORDS-MAIN M)))
              (NOT (ZP N))
              (IMPLIES (AND (NATP (+ -1 N)) (POSP M))
                       (WEAK-WORDP (NTH (+ -1 N)
                                        (GENERATE-WORDS-MAIN M)))))
         (IMPLIES (AND (NATP N) (POSP M))
                  (WEAK-WORDP (NTH N (GENERATE-WORDS-MAIN M)))))


(defthmd weak-words-listp-lemma1
  (implies (and (natp n)
                (posp m))
           (weak-wordp (nth n (generate-words-main m))))
  :hints (("Subgoal *1/2"
           :use ((:instance weak-words-listp-lemma1-sub1/2))
           ;:in-theory (disable generate-words-main)
           ;:induct (generate-words-main m)
           )))

---

(defthmd weak-words-listp-lemma1

(skip-proofs
 (defthmd weak-words-listp-lemma1-sub1/5
   (IMPLIES
    (AND (NOT (ENDP (GENERATE-WORDS-FUNC '(NIL (#\a) (#\b) (#\c) (#\d))
                                         (+ -1 N))))
         (NOT (ZP N))
         (WEAK-WORDP (NTH (+ -1 N)
                          (GENERATE-WORDS-FUNC '(NIL (#\a) (#\b) (#\c) (#\d))
                                               (+ -1 -1 N))))
         (INTEGERP N)
         (< 0 N)
         (INTEGERP (+ -1 N))
         (< 0 (+ -1 N)))
    (WEAK-WORDP (NTH N
                     (GENERATE-WORDS-FUNC '(NIL (#\a) (#\b) (#\c) (#\d))
                                          (+ -1 N)))))
   ))

(defthmd weak-words-listp-lemma1
  (implies (and (posp n)
                (posp (- n 1))
                (equal in-list '(NIL (#\a) (#\b) (#\c) (#\d))))
           (weak-wordp (nth n (generate-words-func in-list (- n 1)))))
  :hints (("Subgoal *1/5"
           :use ((:instance weak-words-listp-lemma1-sub1/5))
           )))

(defthmd weak-words-listp-lemma1
  (implies (and (posp n)
                (equal in-list '(NIL (#\a) (#\b) (#\c) (#\d))))
           (WEAK-WORDS-RECO (GENERATE-WORDS-FUNC in-list n)))
  :hints (("Subgoal *1/4"
           :in-theory nil
           )))

  --


(defun poles-list (word-list)
  (if (atom word-list)
      nil
    (append (poles (car word-list))
            (poles-list (cdr word-list)))))

(defthmd weak-words-listp-lemma1
  (implies (and (weak-words-listp words-list)
                (> (len words-list) 1))
           (weak-words-listp (cdr words-list))))

(defthmd weak-words-listp-lemma2
  (implies (weak-words-listp words-list)
           (weak-wordp (car words-list))))


;; (skip-proofs
;;  (defthmd poles-of-w-in-list-sub1/3
;;    (IMPLIES
;;     (AND (NOT (ENDP WORDS-LIST))
;;          (NOT (ZP N))
;;          (IMPLIES (AND (NATP (+ -1 N))
;;                        (< (+ -1 N) (LEN (CDR WORDS-LIST)))
;;                        (WEAK-WORDS-LISTP (CDR WORDS-LIST)))
;;                   (EQUAL (NTH (* 2 (+ -1 N))
;;                               (POLES-LIST (CDR WORDS-LIST)))
;;                          (CAR (POLES (NTH (+ -1 N) (CDR WORDS-LIST)))))))
;;     (IMPLIES (AND (NATP N)
;;                   (< N (LEN WORDS-LIST))
;;                   (WEAK-WORDS-LISTP WORDS-LIST))
;;              (EQUAL (NTH (* 2 N) (POLES-LIST WORDS-LIST))
;;                     (CAR (POLES (NTH N WORDS-LIST))))))
;;    )
;;  )


---


(defthmd poles-of-w-in-list-sub1/3.2
  (IMPLIES (AND (WEAK-WORDS-LISTP (CDR WORDS-LIST))
                (WEAK-WORDP (CAR WORDS-LIST))
                (CONSP WORDS-LIST)
                (NOT (ZP N))
                (NOT (WEAK-WORDP (NTH (+ -1 N) (CDR WORDS-LIST))))
                (EQUAL (NTH (+ -2 (* 2 N))
                            (POLES-LIST (CDR WORDS-LIST)))
                       NIL)
                (<= 0 N)
                (< N (LEN WORDS-LIST))
                (WEAK-WORDS-LISTP WORDS-LIST))
           (NOT (NTH (* 2 N)
                     (LIST* (F-POLES-1 (ROTATION (CAR WORDS-LIST)
                                                 (ACL2-SQRT 2)))
                            (F-POLES-2 (ROTATION (CAR WORDS-LIST)
                                                 (ACL2-SQRT 2)))
                            (POLES-LIST (CDR WORDS-LIST))))))
  :hints (("Goal"
           :in-theory (disable f-poles-1 f-poles-2)
           :do-not-induct t
           )))
  )

----

(skip-proofs
 (defthmd poles-of-w-in-list-sub1/3.1
   (IMPLIES
    (AND (WEAK-WORDS-LISTP (CDR WORDS-LIST))
         (WEAK-WORDP (CAR WORDS-LIST))
         (CONSP WORDS-LIST)
         (NOT (ZP N))
         (WEAK-WORDP (NTH (+ -1 N) (CDR WORDS-LIST)))
         (EQUAL (NTH (+ -2 (* 2 N))
                     (POLES-LIST (CDR WORDS-LIST)))
                (CAR (LIST (F-POLES-1 (ROTATION (NTH (+ -1 N) (CDR WORDS-LIST))
                                                (ACL2-SQRT 2)))
                           (F-POLES-2 (ROTATION (NTH (+ -1 N) (CDR WORDS-LIST))
                                                (ACL2-SQRT 2))))))
         (<= 0 N)
         (< N (LEN WORDS-LIST))
         (WEAK-WORDS-LISTP WORDS-LIST))
    (EQUAL (NTH (* 2 N)
                (LIST* (F-POLES-1 (ROTATION (CAR WORDS-LIST)
                                            (ACL2-SQRT 2)))
                       (F-POLES-2 (ROTATION (CAR WORDS-LIST)
                                            (ACL2-SQRT 2)))
                       (POLES-LIST (CDR WORDS-LIST))))
           (F-POLES-1 (ROTATION (NTH (+ -1 N) (CDR WORDS-LIST))
                                (ACL2-SQRT 2)))))
   ))

(skip-proofs
 (defthmd poles-of-w-in-list-sub1/3.11
   (IMPLIES (AND (CONSP WORDS-LIST)
                 (NOT (ZP N))
                 (NOT (WEAK-WORDS-LISTP (CDR WORDS-LIST)))
                 (<= 0 N)
                 (< N (LEN WORDS-LIST))
                 (WEAK-WORDS-LISTP WORDS-LIST)
                 (NOT (WEAK-WORDP (CAR WORDS-LIST)))
                 (<= 0 (* 2 N))
                 (WEAK-WORDP (NTH (+ -1 N) (CDR WORDS-LIST))))
            (EQUAL (NTH (* 2 N)
                        (POLES-LIST (CDR WORDS-LIST)))
                   (F-POLES-1 (ROTATION (NTH (+ -1 N) (CDR WORDS-LIST))
                                        (ACL2-SQRT 2)))))
   ))

(defthmd poles-of-w-in-list
  (implies (and (natp n)
                (< n (len words-list))
                (weak-words-listp words-list))
           (equal (nth (* 2 n) (poles-list words-list))
                  (first (poles (nth n words-list)))))
  :hints (("Goal"
           :in-theory (disable rotation acl2-sqrt aref2 weak-wordp generate-words-main f-poles-1 f-poles-2 weak-words-listp)
           )
          ("Subgoal *1/3"
           :use ((:instance weak-words-listp-lemma1 (words-list words-list))
                 (:instance weak-words-listp-lemma2)
                 (:instance poles-of-w-in-list-sub1/3.2)
                 (:instance poles-of-w-in-list-sub1/3.1)
                 )
           )

          ))

          ("Subgoal *1/3"
           ;; :use ((:instance poles-of-w-in-list-sub1/3.11)
           ;;       (:instance poles-of-w-in-list-sub1/3.13)
           ;;       (:instance poles-of-w-in-list-sub1/3.15)
           ;;       )
           )
          ("Subgoal *1/3.11"
           :use (:instance poles-of-w-in-list-sub1/3.11)
           )
          ("Subgoal *1/3.13"
           :use (:instance poles-of-w-in-list-sub1/3.13)
           )
          ("Subgoal *1/3.15"
           :use (:instance poles-of-w-in-list-sub1/3.15)
           )
          ))
;; ("Subgoal *1/2"
          ;;  :in-theory nil
          ;;  )
          ;; ("Subgoal *1/1"
          ;;  :in-theory nil
          ;;  )

          ;; ))
