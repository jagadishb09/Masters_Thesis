
(in-package "ACL2")

(include-book "hausdorff-paradox-1")

;; (encapsulate
;;  ( ((s2-syn *) => * :formals (n) :guard (posp n))
;;    ((a) => *)
;;    ((b) => *)
;;    )
;;  (local (defun s2-syn ()
;;           ;(declare (xargs :guard (array2p :fake-name p))
;; ;        (ignore p))
;;             '((:header :dimensions (3 1)
;;                        :maximum-length 15)
;;               ((0 . 0) . 0)
;;               ((1 . 0) . 1)
;;               ((2 . 0) . 0)
;;               )
;;             ))

;;  (defun s2-x ()
;;    (aref2 :fakename (s2-syn) 0 0))

;;  (local (defun a () 0))
;;  (local (defun b () 1))

;;  (defthm seq-is-real
;;    (realp (seq n))
;;    :rule-classes (:rewrite :type-prescription))

;;  (defthm a-b-is-open-interval
;;    (and (realp (a))
;;         (realp (b))
;;         (< (a) (b))))
;;  )

(encapsulate
  ((poles (w) t))
  (local (defun poles (w) (declare (ignore w)) '(1 2)))

  (skip-proofs
   (defthmd two-poles-for-each-rotation
     (implies (weak-wordp w)
              (equal (len (poles w)) 2))))

  (skip-proofs
   (defthmd poles-lie-on-s2
     (implies (weak-wordp w)
              (and (s2-def-p (first (poles w)))
                   (s2-def-p (second (poles w)))))))

  (skip-proofs
   (defthmd f-returns-poles-1
     (implies (weak-wordp w)
              (and (m-= (m-* (rotation w (acl2-sqrt 2)) (first (poles w))) (first (poles w)))
                   (m-= (m-* (rotation w (acl2-sqrt 2)) (second (poles w))) (second (poles w)))))))

  (skip-proofs
   (defthmd two-poles-for-all-rotations
     (implies (and (weak-wordp w)
                   (point-in-r3 p)
                   (m-= (m-* (rotation w (acl2-sqrt 2)) p) p))
              (or (m-= (first (poles w)) p)
                  (m-= (second (poles w)) p))))))

(defthmd f-returns-poles
  (implies (and (reducedwordp w)
                w)
           (and (d-p (first (poles w)))
                (d-p (second (poles w)))))
  :hints (("goal"
           :use ((:instance f-returns-poles-1 (w w))
                 (:instance word-exists-suff (w w) (point (first (poles w))))
                 (:instance word-exists-suff (w w) (point (second (poles w))))
                 (:instance poles-lie-on-s2 (w w))
                 (:instance d-p (point (first (poles w))))
                 (:instance d-p (point (second (poles w))))
                 (:instance reducedwordp=>weak-wordp (x w)))
           :in-theory nil
           )))

(defun generate-word-len-1 (n)
  (cond ((equal n 1) '((#\a)))
        ((equal n 2) '((#\b)))
        ((equal n 3) '((#\c)))
        ((equal n 4) '((#\d)))))

(defun generate-words-len-1 (n)
  (if (zp n)
      '(())
    (append (generate-words-len-1 (- n 1)) (generate-word-len-1 (- n 1)))))

(defun generate-words (list-of-words index)
  (append list-of-words
          (list (append (nth index list-of-words) (list (wa))))
          (list (append (nth index list-of-words) (list (wa-inv))))
          (list (append (nth index list-of-words) (list (wb))))
          (list (append (nth index list-of-words) (list (wb-inv)))))
  )

(defun generate-words-func (list index)
  (if (zp (- index 1))
      (generate-words list 1)
    (generate-words (generate-words-func list (- index 1)) index)))

(defun generate-words-main (n)
  (if (> n 5)
      (generate-words-func (generate-words-len-1 5) (- n 5))
    (generate-words-len-1 n)))

(defun first-poles (list-r-words len)
  (if (zp len)
      nil
    (append (first-poles list-r-words (- len 1)) (list (nth 0 (poles (nth (- len 1) list-r-words)))))))

(defun second-poles (list-r-words len)
  (if (zp len)
      nil
    (append (second-poles list-r-words (- len 1)) (list (nth 1 (poles (nth (- len 1) list-r-words)))))))

(defun generate-poles (list-r-words)
  (append (first-poles list-r-words (len list-r-words)) (second-poles list-r-words (len list-r-words))))

(defun generate-x (poles-list len)
  (if (zp len)
      nil
    (append (generate-x poles-list (- len 1)) (list (aref2 :fake-name (nth (- len 1) poles-list) 0 0)))))

(defun generate-x-coordinates (poles-list)
  (generate-x poles-list (len poles-list)))

(defun enumerate-x-of-poles-upto-length (idx)
  (generate-x-coordinates (generate-poles (generate-words-main (/ idx 2)))))

(defun x-coordinate-sequence (idx)
  (if (posp idx)
      (if (evenp idx)
          (nth (1- idx) (enumerate-x-of-poles-upto-length idx))
        (nth (/ (- idx 1) 2) (enumerate-x-of-poles-upto-length (+ idx 1))))
    0))

(defun weak-words-reco (wp)
  (if (atom wp)
      T
    (and (weak-wordp (car wp))
         (weak-words-reco (cdr wp)))))

(defun weak-words-listp (wp)
  (and (consp wp)
       (weak-words-reco wp)))

(defun generate-words (list-of-words index)
  (append list-of-words
          (list (append (nth index list-of-words) (list (wa))))
          (list (append (nth index list-of-words) (list (wa-inv))))
          (list (append (nth index list-of-words) (list (wb))))
          (list (append (nth index list-of-words) (list (wb-inv)))))
  )

(defun generate-words-func (list index)
  (if (zp (- index 1))
      (generate-words list 1)
    (generate-words (generate-words-func list (- index 1)) index)))

(defthmd generate-words-func-equiv
  (implies (and (> h 1)
                (posp h))
           (equal (generate-words-func lst h)
                  (append (generate-words-func lst (- h 1))
                          (list (append (nth h (generate-words-func lst (- h 1))) (list (wa))))
                          (list (append (nth h (generate-words-func lst (- h 1))) (list (wa-inv))))
                          (list (append (nth h (generate-words-func lst (- h 1))) (list (wb))))
                          (list (append (nth h (generate-words-func lst (- h 1))) (list (wb-inv)))))))
  :hints (("goal"
           :do-not-induct t
           )))

(defthmd generate-words-func-lemma1
  (implies (and (true-listp lst)
                (posp (+ h 1))
                (posp h))
           (< (+ h 1) (len (generate-words-func lst h)))))

(defthmd generate-words-func-lemma2-1
  (iff (weak-words-reco (append lst1 lst2))
           (and (weak-words-reco lst1)
                (weak-words-reco lst2))))

(defthmd generate-words-func-lemma2-2
  (implies (and (natp index)
                (consp wp)
                (weak-words-reco wp))
           (weak-wordp (nth index wp))))

(defthmd generate-words-func-lemma2-sub1/2
  (IMPLIES
   (AND
    (EQUAL
     (GENERATE-WORDS-FUNC '(NIL (#\a) (#\b) (#\c) (#\d))
                          INDEX)
     (APPEND
      (GENERATE-WORDS-FUNC '(NIL (#\a) (#\b) (#\c) (#\d))
                           (+ -1 INDEX))
      (LIST (APPEND (NTH INDEX
                         (GENERATE-WORDS-FUNC '(NIL (#\a) (#\b) (#\c) (#\d))
                                              (+ -1 INDEX)))
                    (LIST (WA))))
      (LIST (APPEND (NTH INDEX
                         (GENERATE-WORDS-FUNC '(NIL (#\a) (#\b) (#\c) (#\d))
                                              (+ -1 INDEX)))
                    (LIST (WA-INV))))
      (LIST (APPEND (NTH INDEX
                         (GENERATE-WORDS-FUNC '(NIL (#\a) (#\b) (#\c) (#\d))
                                              (+ -1 INDEX)))
                    (LIST (WB))))
      (LIST (APPEND (NTH INDEX
                         (GENERATE-WORDS-FUNC '(NIL (#\a) (#\b) (#\c) (#\d))
                                              (+ -1 INDEX)))
                    (LIST (WB-INV))))))
    (NOT (ZP (+ -1 INDEX)))
    (WEAK-WORDS-RECO (GENERATE-WORDS-FUNC '(NIL (#\a) (#\b) (#\c) (#\d))
                                          (+ -1 INDEX)))
    (INTEGERP INDEX)
    (< 0 INDEX))
   (WEAK-WORDS-RECO (GENERATE-WORDS-FUNC '(NIL (#\a) (#\b) (#\c) (#\d))
                                         INDEX)))
  :hints (("Goal"
           :use ((:instance generate-words-func-lemma2-1
                            (lst1 (GENERATE-WORDS-FUNC '(NIL (#\a) (#\b) (#\c) (#\d))
                                                       (+ -1 INDEX)))
                            (lst2 (LIST (APPEND (NTH INDEX
                                                     (GENERATE-WORDS-FUNC '(NIL (#\a) (#\b) (#\c) (#\d))
                                                                          (+ -1 INDEX)))
                                                (LIST (WA)))
                                        (APPEND (NTH INDEX
                                                     (GENERATE-WORDS-FUNC '(NIL (#\a) (#\b) (#\c) (#\d))
                                                                          (+ -1 INDEX)))
                                                (LIST (WA-INV)))
                                        (APPEND (NTH INDEX
                                                     (GENERATE-WORDS-FUNC '(NIL (#\a) (#\b) (#\c) (#\d))
                                                                          (+ -1 INDEX)))
                                                (LIST (WB)))
                                        (APPEND (NTH INDEX
                                                     (GENERATE-WORDS-FUNC '(NIL (#\a) (#\b) (#\c) (#\d))
                                                                          (+ -1 INDEX)))
                                                (LIST (WB-INV))))))

                 )
           :do-not-induct t
           )
          ("Subgoal 4"
           :use ((:instance generate-words-func-lemma2-2
                            (index index)
                            (wp (GENERATE-WORDS-FUNC '(NIL (#\a) (#\b) (#\c) (#\d)) (+ -1 INDEX))))
                 (:instance closure-weak-word (x (NTH INDEX
                                                      (GENERATE-WORDS-FUNC '(NIL (#\a) (#\b) (#\c) (#\d))
                                                                           (+ -1 INDEX))))
                            (y '(#\d))))

           )
          ("Subgoal 3"
           :use ((:instance generate-words-func-lemma2-2
                            (index index)
                            (wp (GENERATE-WORDS-FUNC '(NIL (#\a) (#\b) (#\c) (#\d)) (+ -1 INDEX))))
                 (:instance closure-weak-word (x (NTH INDEX
                                                      (GENERATE-WORDS-FUNC '(NIL (#\a) (#\b) (#\c) (#\d))
                                                                           (+ -1 INDEX))))
                            (y '(#\a))))

           )
          ("Subgoal 2"
           :use ((:instance generate-words-func-lemma2-2
                            (index index)
                            (wp (GENERATE-WORDS-FUNC '(NIL (#\a) (#\b) (#\c) (#\d)) (+ -1 INDEX))))
                 (:instance closure-weak-word (x (NTH INDEX
                                                      (GENERATE-WORDS-FUNC '(NIL (#\a) (#\b) (#\c) (#\d))
                                                                           (+ -1 INDEX))))
                            (y '(#\c))))

           )
          ("Subgoal 1"
           :use ((:instance generate-words-func-lemma2-2
                            (index index)
                            (wp (GENERATE-WORDS-FUNC '(NIL (#\a) (#\b) (#\c) (#\d)) (+ -1 INDEX))))
                 (:instance closure-weak-word (x (NTH INDEX
                                                      (GENERATE-WORDS-FUNC '(NIL (#\a) (#\b) (#\c) (#\d))
                                                                           (+ -1 INDEX))))
                            (y '(#\b))))

           )
          ))

(defthmd generate-words-func-lemma2-sub1/3
  (IMPLIES
   (AND (<= INDEX 1)
        (NOT (ZP (+ -1 INDEX)))
        (WEAK-WORDS-RECO (GENERATE-WORDS-FUNC '(NIL (#\a) (#\b) (#\c) (#\d))
                                              (+ -1 INDEX)))
        (INTEGERP INDEX)
        (< 0 INDEX))
   (WEAK-WORDS-RECO (GENERATE-WORDS-FUNC '(NIL (#\a) (#\b) (#\c) (#\d))
                                         INDEX))))

(defthmd generate-words-func-lemma2-sub1/1
  (IMPLIES
   (AND (NOT (POSP INDEX))
        (NOT (ZP (+ -1 INDEX)))
        (WEAK-WORDS-RECO (GENERATE-WORDS-FUNC '(NIL (#\a) (#\b) (#\c) (#\d))
                                              (+ -1 INDEX)))
        (INTEGERP INDEX)
        (< 0 INDEX))
   (WEAK-WORDS-RECO (GENERATE-WORDS-FUNC '(NIL (#\a) (#\b) (#\c) (#\d))
                                         INDEX))))

(defthmd generate-words-func-lemma2
  (implies (posp index)
           (weak-words-listp (generate-words-func '(nil (#\a) (#\b) (#\c) (#\d)) index)))
  :hints (("Subgoal *1/4"
           :use ((:instance generate-words-func-equiv (h index) (lst '(NIL (#\a) (#\b) (#\c) (#\d))))
                 )
           :in-theory nil
           )
          ("Subgoal *1/4.2"
           :use (:instance generate-words-func-lemma2-sub1/2)
           :in-theory nil
           )
          ("Subgoal *1/4.3"
           :use (:instance generate-words-func-lemma2-sub1/3)
           :in-theory nil
           )
          ("Subgoal *1/4.1"
           :use (:instance generate-words-func-lemma2-sub1/1)
           :in-theory nil
           )
          ))

(defthmd generate-words-func-lemma3
  (implies (posp index)
           (weak-words-listp (generate-words-main index)))
  :hints (("Goal"
           :cases ((= index 1)
                   (= index 2)
                   (= index 3)
                   (= index 4)
                   (= index 5)
                   (> index 5))
           :use ((:instance generate-words-func-lemma2 (index (- index 5))))
           :do-not-induct t
           )))

(defthmd generate-words-func-lemma4
  (implies (and (posp index)
                (natp n))
           (weak-wordp (nth n (generate-words-main index))))
  :hints (("Goal"
           :use ((:instance generate-words-func-lemma3)
                 (:instance generate-words-func-lemma2-2 (index n)
                            (wp (generate-words-main index))))
           :in-theory (disable generate-words-main)
           )))

(defun-sk exists-weak-word (w)
  (exists n
          (and (posp n)
               (equal (nth n (generate-words-main n))
                      w))))

------

(skip-proofs
 (defthmd any-weak-word-exists-sub*1/2
   (IMPLIES (AND (NOT (ATOM W))
                 (OR (EQUAL (CAR W) (WA))
                     (EQUAL (CAR W) (WA-INV))
                     (EQUAL (CAR W) (WB))
                     (EQUAL (CAR W) (WB-INV)))
                 (IMPLIES (WEAK-WORDP (CDR W))
                          (EXISTS-WEAK-WORD (CDR W))))
            (IMPLIES (WEAK-WORDP W)
                     (EXISTS-WEAK-WORD W)))))

(defthmd any-weak-word-exists
  (implies (weak-wordp w)
           (exists-weak-word w))
  :hints (("Subgoal *1/2"
           :use ((:instance any-weak-word-exists-sub*1/2))
           )
          ("Subgoal *1/1"
           :use ((:instance EXISTS-WEAK-WORD-SUFF (n 0) (w w)))
           )
          ))

----


(defthmd generate-words-func-lemma1
  (implies (and (true-listp lst)
                (posp (+ h 1))
                (posp h))
           (< (+ h 1) (len (generate-words-func lst h)))))



(defun generate-words (list-of-words index)
  (append list-of-words
          (list (append (nth index list-of-words) (list (wa))))
          (list (append (nth index list-of-words) (list (wa-inv))))
          (list (append (nth index list-of-words) (list (wb))))
          (list (append (nth index list-of-words) (list (wb-inv)))))
  )

(defun generate-words-func (list index)
  (if (zp (- index 1))
      (generate-words list 1)
    (generate-words (generate-words-func list (- index 1)) index)))
--

(skip-proofs
 (defthmd generate-words-func-lemma2-sub-*1/2
   (IMPLIES
    (AND
     (NOT (ZP (+ -1 INDEX)))
     (IMPLIES
      (AND (POSP (+ -1 INDEX)) (NATP N))
      (WEAK-WORDP (NTH N
                       (GENERATE-WORDS-FUNC '(NIL (#\a) (#\b) (#\c) (#\d))
                                            (+ -1 INDEX))))))
    (IMPLIES
     (AND (POSP INDEX) (NATP N))
     (WEAK-WORDP (NTH N
                      (GENERATE-WORDS-FUNC '(NIL (#\a) (#\b) (#\c) (#\d))
                                           INDEX)))))))

(defthmd generate-words-func-lemma2
  (implies (and (posp index)
                (natp n))
           (weak-wordp (nth n (generate-words-func '(nil (#\a) (#\b) (#\c) (#\d)) index))))
  :hints (("Goal"
           :induct (generate-words-func '(nil (#\a) (#\b) (#\c) (#\d)) index)
           )
          ("Subgoal *1/2"
           :use (:instance generate-words-func-lemma2-sub-*1/2)
           )
          ))





----
(defthmd generate-words-func-lemma2
  (implies (and (posp h)
                (natp n)
                (true-listp lst)
                (natp k)
                (weak-wordp (nth k lst))
                (<= (len (nth k lst)) 1))
           (weak-wordp (nth n (generate-words-func lst h))))
  :hints (("Goal"
          :induct (generate-words-func lst h)
          )))

(skip-proofs
 (defthmd generate-words-func-lemma2-sub1/4
   (IMPLIES
    (AND (NOT (ZP (+ -1 H)))
         (WEAK-WORDP (NTH N
                          (GENERATE-WORDS-FUNC '(NIL (#\a) (#\b) (#\c) (#\d))
                                               (+ -1 H))))
         (INTEGERP H)
         (< 0 H)
         (INTEGERP N)
         (<= 0 N))
    (WEAK-WORDP (NTH N
                     (GENERATE-WORDS-FUNC '(NIL (#\a) (#\b) (#\c) (#\d))
                                          H))))))

(IMPLIES
    (AND (NOT (ENDP (GENERATE-WORDS-FUNC '(NIL (#\a) (#\b) (#\c) (#\d))
                                         H)))
         (NOT (ZP H))
         (WEAK-WORDP (NTH (+ -1 H)
                          (GENERATE-WORDS-FUNC '(NIL (#\a) (#\b) (#\c) (#\d))
                                               (+ -1 H))))
         (INTEGERP H)
         (< 0 H))
    (WEAK-WORDP (NTH H
                     (GENERATE-WORDS-FUNC '(NIL (#\a) (#\b) (#\c) (#\d))
                                          H))))

(defthmd generate-words-func-lemma2-1
  (implies (posp h)
           (weak-wordp (nth h (generate-words-func '(nil (#\a) (#\b) (#\c) (#\d)) h))))
  :hints (("Goal"
           :induct (generate-words-func '(nil (#\a) (#\b) (#\c) (#\d)) h)
           ;:in-theory nil
           )
          ("Subgoal *1/2"
           :in-theory nil
           )
          ))

(defthmd generate-words-func-lemma2
  (implies (and (posp h)
                (natp n))
           (weak-wordp (nth n (generate-words-func '(nil (#\a) (#\b) (#\c) (#\d)) h))))
  :hints (("goal"
           :induct (generate-words-func '(nil (#\a) (#\b) (#\c) (#\d)) h)
           )
          ("subgoal *1/4"
           ;:use ((:instance generate-words-func-lemma2-sub1/4))
           :in-theory nil
           )
          ("subgoal *1/3"
;:use ((:instance generate-words-func-lemma2-*1/2))
           :in-theory nil
           )
          ("subgoal *1/2"
;:use ((:instance generate-words-func-lemma2-*1/2))
           :in-theory nil
           )
          ("subgoal *1/1"
;:use ((:instance generate-words-func-lemma2-*1/2))
           ;:in-theory nil
           )
          ))

  -----

(defthmd generate-words-func-equiv
  (implies (and (> h 1)
                (posp h))
           (equal (generate-words-func lst h)
                  (append (generate-words-func lst (- h 1))
                          (list (append (nth h (generate-words-func lst (- h 1))) (list (wa))))
                          (list (append (nth h (generate-words-func lst (- h 1))) (list (wa-inv))))
                          (list (append (nth h (generate-words-func lst (- h 1))) (list (wb))))
                          (list (append (nth h (generate-words-func lst (- h 1))) (list (wb-inv)))))))
  :hints (("goal"
           :do-not-induct t
           )))

(defthmd generate-words-func-lemma2-*1/2-1-1
  (implies (and (<= (len lst) n)
                (< n
                    (len (append lst (list w1)
                                 (list w2)
                                 (list w3)
                                 (list w4)))))
           (implies (and (natp n)
                         (true-listp lst)
                         (weak-wordp (nth n lst))
                         (weak-wordp w1)
                         (weak-wordp w2)
                         (weak-wordp w3)
                         (weak-wordp w4))
                    (weak-wordp (nth n
                                     (append lst (list w1)
                                             (list w2)
                                             (list w3)
                                             (list w4))))))
  :hints (("goal"
           :do-not-induct t
           :cases ((equal n (len lst))
                   (equal n (+ (len lst) 1))
                   (equal n (+ (len lst) 2))
                   (equal n (+ (len lst) 3))
                   (equal n (+ (len lst) 4)))
           )))

(defthmd generate-words-func-lemma2-*1/2-1
  (implies (and (natp n)
                (true-listp lst)
                (weak-wordp (nth n lst))
                (weak-wordp w1)
                (weak-wordp w2)
                (weak-wordp w3)
                (weak-wordp w4))
           (weak-wordp (nth n (append lst (list w1) (list w2) (list w3) (list w4)))))
  :hints (("goal"
           :cases ((< n (len lst))
                   (>= n (len (append lst (list w1) (list w2) (list w3) (list w4)))))
           :use ((:instance generate-words-func-lemma2-*1/2-1-1))
           :do-not-induct t
           )))

(defthmd generate-words-func-lemma2-*1/2-2
  (implies (natp n)
           (weak-wordp (nth n '(nil (#\a) (#\b) (#\c) (#\d))))))

;; (skip-proofs
;;  (defthmd generate-words-func-lemma2-*1/2-3
;;    (implies (and (posp h)
;;                  (posp (- h 1))
;;                  (natp n)
;;                  (weak-wordp (nth n
;;                                   (generate-words-func '(nil (#\a) (#\b) (#\c) (#\d))
;;                                                        (+ -1 h)))))
;;             (weak-wordp (nth h (generate-words-func '(nil (#\a) (#\b) (#\c) (#\d))
;;                                                     (+ -1 h)))))
;;    :hints (("goal"
;;             :do-not-induct t
;;             ))))

(defthmd generate-words-func-lemma2-*1/2-3
  (implies (true-listp lst)
           (>= (len lst) 0)))

(defthmd generate-words-func-lemma2-*1/2-4
  (implies (and (posp h)
                (posp (- h 1))
                (true-listp lst)
                (natp n)
                (implies (and (posp (- h 1))
                              (natp n))
                         (weak-wordp (nth n lst))))
           (weak-wordp (nth h lst))))

(defthmd generate-words-func-lemma2-*1/2
  (implies
   (and
    (not (zp (+ -1 h)))
    (implies
     (and (posp (+ -1 h)) (natp n))
     (weak-wordp (nth n
                      (generate-words-func '(nil (#\a) (#\b) (#\c) (#\d))
                                           (+ -1 h))))))
   (implies
    (and (posp h) (natp n))
    (weak-wordp (nth n
                     (generate-words-func '(nil (#\a) (#\b) (#\c) (#\d))
                                          h)))))
  :hints (("goal"
           :cases ((posp (- h 1)))
           :use ((:instance generate-words-func-equiv (lst '(nil (#\a) (#\b) (#\c) (#\d)))
                            (h h))
                 (:instance generate-words-func-lemma2-*1/2-1 (lst '(nil (#\a) (#\b) (#\c) (#\d)))
                            (w1 (append (nth h (generate-words-func '(nil (#\a) (#\b) (#\c) (#\d)) (- h 1)))
                                        (list (wa))))
                            (w2 (append (nth h (generate-words-func '(nil (#\a) (#\b) (#\c) (#\d)) (- h 1)))
                                        (list (wa-inv))))
                            (w3 (append (nth h (generate-words-func '(nil (#\a) (#\b) (#\c) (#\d)) (- h 1)))
                                        (list (wb))))
                            (w4 (append (nth h (generate-words-func '(nil (#\a) (#\b) (#\c) (#\d)) (- h 1)))
                                        (list (wb-inv)))))
                 (:instance closure-weak-word
                            (x (append (nth h (generate-words-func '(nil (#\a) (#\b) (#\c) (#\d)) (- h 1)))))
                            (y (list (wa))))
                 (:instance closure-weak-word
                            (x (append (nth h (generate-words-func '(nil (#\a) (#\b) (#\c) (#\d)) (- h 1)))))
                            (y (list (wa-inv))))
                 (:instance closure-weak-word
                            (x (append (nth h (generate-words-func '(nil (#\a) (#\b) (#\c) (#\d)) (- h 1)))))
                            (y (list (wb))))
                 (:instance closure-weak-word
                            (x (append (nth h (generate-words-func '(nil (#\a) (#\b) (#\c) (#\d)) (- h 1)))))
                            (y (list (wb-inv))))
                 (:instance generate-words-func-lemma2-*1/2-2)
                 ;(:instance generate-words-func-lemma2-*1/2-3)
                 )
           :do-not-induct t
           )))


          ("subgoal 1"
           :cases ((equal n (len (generate-words-func '(nil (#\a) (#\b) (#\c) (#\d)) (+ -1 h))))
                   (equal n (+ (len (generate-words-func '(nil (#\a) (#\b) (#\c) (#\d)) (+ -1 h))) 1))
                   (equal n (+ (len (generate-words-func '(nil (#\a) (#\b) (#\c) (#\d)) (+ -1 h))) 2))
                   (equal n (+ (len (generate-words-func '(nil (#\a) (#\b) (#\c) (#\d)) (+ -1 h))) 3)))
           )
          ("Subgoal 1.4"
           :use ((:instance generate-words-func-lemma2-*1/2-sub1.4))
           )
          ))

(defthmd generate-words-func-lemma2
  (implies (and (posp h)
                (natp n))
           (weak-wordp (nth n (generate-words-func '(nil (#\a) (#\b) (#\c) (#\d)) h))))
  :hints (("goal"
           :induct (generate-words-func '(nil (#\a) (#\b) (#\c) (#\d)) h))
          ("subgoal *1/2"
           :use ((:instance generate-words-func-lemma2-*1/2))
           :in-theory nil
           )))

(defthmd generate-words-main-lemma1-1
  (implies (and (posp h)
                (<= h 5)
                (natp n))
           (weak-wordp (nth n (generate-words-main h)))))

(defthmd generate-words-main-lemma1
  (implies (and (posp h)
                (natp n))
           (weak-wordp (nth n (generate-words-main h))))
  :hints (("Goal"
           :cases ((> h 5))
           :use ((:instance generate-words-func-lemma2 (h (- h 5)))
                 (:instance generate-words-main-lemma1-1))
           :do-not-induct t
           )))

(defthmd test-2000
  (implies (and (posp h)
                (posp (- h 1))
                (natp n)
                (< h n)
                (true-listp lst)
                (weak-wordp (nth n lst)))
           (weak-wordp (nth h lst)))
  :hints (("Subgoal *1/4"
           :cases ((= h 0)
                   (= h 1)
                   (= h 2))
           )
          ("Subgoal *1/4.1"
           :cases ((= n 2))
           )
          ))

;; (defun-sk test-1000-func (w)
;;   (exists n
;;           (equal (nth (- n 1) (generate-words-main n))
;;                  w)))

;; (skip-proofs
;;  (defthmd test-1000-1
;;    (IMPLIES (AND (NOT (ATOM W))
;;                  (OR (EQUAL (CAR W) (WA))
;;                      (EQUAL (CAR W) (WA-INV))
;;                      (EQUAL (CAR W) (WB))
;;                      (EQUAL (CAR W) (WB-INV)))
;;                  (IMPLIES (WEAK-WORDP (CDR W))
;;                           (TEST-1000-FUNC (CDR W))))
;;             (IMPLIES (WEAK-WORDP W)
;;                      (TEST-1000-FUNC W)))))


;; (defthmd test-1000
;;   (implies (and (weak-wordp w)
;;                 (> (len w) 1))
;;            (test-1000-func w))
;;   :hints (("Subgoal *1/2"
;;            ;:use ((:instance test-1000-1))
;;            ;:in-theory nil
;;            )
;;           ("Subgoal *1/1"
;;            :in-theory nil
;;            ;:use (:instance TEST-1000-FUNC-SUFF (n 1))
;;            )
;;           ))

---

(skip-proofs
 (defthmd generate-words-func-lemma1-*1/2
   (IMPLIES
    (AND
     (NOT (ZP (+ -1 H)))
     (IMPLIES (AND (POSP (+ -1 H))
                   (NATP N)
                   (< N (+ -1 H)))
              (REDUCEDWORDP (NTH N
                                 (GENERATE-WORDS-FUNC '((#\a) (#\b) (#\c) (#\d))
                                                      (+ -1 H))))))
    (IMPLIES (AND (POSP H) (NATP N) (< N H))
             (REDUCEDWORDP (NTH N
                                (GENERATE-WORDS-FUNC '((#\a) (#\b) (#\c) (#\d))
                                                     H)))))))

(defthmd generate-words-func-lemma1-*1/2.3
  (IMPLIES (AND (NOT (ZP (+ -1 H)))
                (NOT (POSP (+ -1 H)))
                (POSP H)
                (NATP N)
                (< N H))
           (REDUCEDWORDP (NTH N
                              (GENERATE-WORDS-FUNC '((#\a) (#\b) (#\c) (#\d))
                                                   H)))))



---

;; Subgoal *1/2.2
;; (IMPLIES
;;      (AND (NOT (ZP (+ -1 H)))
;;           (REDUCEDWORDP (NTH N
;;                              (GENERATE-WORDS-FUNC '((#\a) (#\b) (#\c) (#\d))
;;                                                   (+ -1 H))))
;;           (POSP H)
;;           (NATP N)
;;           (< N H))
;;      (REDUCEDWORDP (NTH N
;;                         (GENERATE-WORDS-FUNC '((#\a) (#\b) (#\c) (#\d))
;;                                              H))))

(defthmd generate-words-func-lemma1-*1/2.1-1
  (implies (and (posp h)
                (natp n)
                (<= (+ -1 h) n)
                (< n h))
           (equal (- h 1) n)))

(defthmd generate-words-func-lemma1-*1/2.1
  (IMPLIES (AND (NOT (ZP (+ -1 H)))
                (<= (+ -1 H) N)
                (POSP H)
                (NATP N)
                (< N H))
           (REDUCEDWORDP (NTH N
                              (GENERATE-WORDS-FUNC '((#\a) (#\b) (#\c) (#\d))
                                                   H))))
  :hints (("Goal"
           :use ((:instance generate-words-func-lemma1-*1/2.1-1))
           :in-theory nil
           )))

(defthmd generate-words-func-lemma1
  (implies (and (posp h)
                (natp n)
                (< n h))
           (reducedwordp (nth n (GENERATE-WORDS-FUNC '((#\a) (#\b) (#\c) (#\d)) h))))
  :hints (
          ("Goal"
           :induct (GENERATE-WORDS-FUNC '((#\a) (#\b) (#\c) (#\d)) h)
           )
          ("Subgoal *1/2"
           ;:use ((:instance generate-words-func-lemma1-*1/2))
           :in-theory nil
           )
          ("Subgoal *1/1"
           ;:in-theory nil
           )

          ))

(defthmd generate-words-func-lemma1
  (implies (and (posp h)
                (natp n)
                (< n (len (GENERATE-WORDS-FUNC '((#\a) (#\b) (#\c) (#\d)) h))))
           (reducedwordp (nth n (GENERATE-WORDS-FUNC '((#\a) (#\b) (#\c) (#\d)) h))))
  :hints (
          ("Goal"
           :induct (GENERATE-WORDS-FUNC '((#\a) (#\b) (#\c) (#\d)) h)
           )
          ("Subgoal *1/2"
           ;:use ((:instance generate-words-func-lemma1-*1/2))
           :in-theory nil
           )
          ("Subgoal *1/1"
           :in-theory nil
           )

          ))


(defthmd generate-words-main-reduced-words-1
  (implies (and (natp n)
                (not (natp (+ -1 n))))
           (zp n)))

(defthmd generate-words-main-reduced-words-2
  (IMPLIES (AND (NOT (ENDP (GENERATE-WORDS-MAIN H)))
                (NOT (ZP N))
                (REDUCEDWORDP (NTH (+ -1 N) (GENERATE-WORDS-MAIN H)))
                (POSP H)
                (NATP N)
                (< N H))
           (REDUCEDWORDP (NTH N (GENERATE-WORDS-MAIN H))))
  :hints (("Subgoal *1/106"
           :in-theory nil
           )))

(defthmd generate-words-main-reduced-words-3-1
  (implies (and (zp n)
                (natp n))
           (equal (- n 1) -1)))

(skip-proofs
 (defthmd generate-words-main-reduced-words-3-2-1-1
   (IMPLIES (AND (NOT (ZP (+ -1 H)))
                 (EQUAL (CAR (GENERATE-WORDS-FUNC '((#\a) (#\b) (#\c) (#\d))
                                                  (+ -1 H)))
                        '(#\a))
                 (INTEGERP H)
                 (< 0 H))
            (EQUAL (CAR (GENERATE-WORDS-FUNC '((#\a) (#\b) (#\c) (#\d))
                                             H))
                   '(#\a)))))

(defthmd generate-words-main-reduced-words-3-2-1
  (implies (posp h)
           (equal (car (GENERATE-WORDS-FUNC '((#\a) (#\b) (#\c) (#\d)) h))
                  '(#\a)))
  :hints (("Subgoal *1/4"
           :use (:instance generate-words-main-reduced-words-3-2-1-1)
           )))



(defthmd generate-words-main-reduced-words-3-2
  (implies (and (equal n 0)
                (POSP H))
           (equal (NTH N (GENERATE-WORDS-MAIN H)) '(#\a)))
  :hints (("Goal"
           ;:do-not-induct t
           )))


(defthmd generate-words-main-reduced-words-3
  (IMPLIES (AND (NOT (ENDP (GENERATE-WORDS-MAIN H)))
                (ZP N)
                (POSP H)
                (NATP N)
                (< N H))
           (REDUCEDWORDP (NTH N (GENERATE-WORDS-MAIN H))))
  :hints (("Goal"
           :use ((:instance generate-words-main-reduced-words-3-1)
                 (:instance generate-words-main-reduced-words-3-2))
           )))

(defthmd generate-words-main-reduced-words
  (implies (and (posp h)
                (natp n)
                (< n h))
           (reducedwordp (nth n (generate-words-main h))))
  :hints (("Subgoal *1/3"
           :use ((:instance generate-words-main-reduced-words-1)
                 (:instance generate-words-main-reduced-words-2))
           )
          ("Subgoal *1/2"
           :use ((:instance generate-words-main-reduced-words-3))
           )))
---

  (append (generate-words-len-1 (- n 1))

(defun generate-words (n)
  (append (generate-word-len-1 '() n)

(defun enumerate-x-of-poles-upto-length (idx)
  (generate-x's (generate-poles (generate-words (/ idx 2)))))


(defun x-coordinate-sequence (idx)
  (if (posp idx)
      (if (evenp idx)
          (nth (1- idx) (enumerate-x-of-poles-upto-length idx))
        (nth (/ (- idx 1) 2) (enumerate-x-of-poles-upto-length (+ idx 1))))
    0))
