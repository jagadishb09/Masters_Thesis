
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
   (defthmd poles-returns-two-points
     (implies (weak-wordp w)
              (and (point-in-r3 (first (poles w)))
                   (point-in-r3 (second (poles w)))))))

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
  :hints (("Goal"
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
  (if (zp (- n 1))
      (append '() (generate-word-len-1 n))
    (append (generate-words-len-1 (- n 1)) (generate-word-len-1 n))))

(defun generate-words (list-of-words index)
  (cond ((equal (car (last (nth index list-of-words))) (wa))
         (append list-of-words
                 (list (append (nth index list-of-words) (list (wa))))
                 (list (append (nth index list-of-words) (list (wb))))
                 (list (append (nth index list-of-words) (list (wb-inv))))))
        ((equal (car (last (nth index list-of-words))) (wa-inv))
         (append list-of-words
                 (list (append (nth index list-of-words) (list (wa-inv))))
                 (list (append (nth index list-of-words) (list (wb))))
                 (list (append (nth index list-of-words) (list (wb-inv))))))
        ((equal (car (last (nth index list-of-words))) (wb))
         (append list-of-words
                 (list (append (nth index list-of-words) (list (wa))))
                 (list (append (nth index list-of-words) (list (wa-inv))))
                 (list (append (nth index list-of-words) (list (wb))))))
        ((equal (car (last (nth index list-of-words))) (wb-inv))
         (append list-of-words
                 (list (append (nth index list-of-words) (list (wa))))
                 (list (append (nth index list-of-words) (list (wa-inv))))
                 (list (append (nth index list-of-words) (list (wb-inv))))))
        )
  )

(defun generate-words-func (list index)
  (if (zp (- index 1))
      (generate-words list 0)
    (generate-words (generate-words-func list (- index 1)) (- index 1))))

(defun generate-words-main (n)
  (if (> n 4)
      (generate-words-func (generate-words-len-1 4) (- n 4))
    (generate-words-len-1 n)))

--

(defthmd generate-words-func-lemma1
  (implies (and (posp h)
                (natp n)
                (< n h))
           (reducedwordp (nth n (GENERATE-WORDS-FUNC '((#\a) (#\b) (#\c) (#\d)) h))))
  :hints (("Subgoal *1/2"
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
