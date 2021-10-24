
(in-package "acl2")

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
          (list (append (list (wa)) (nth index list-of-words)))
          (list (append (list (wa-inv)) (nth index list-of-words)))
          (list (append (list (wb)) (nth index list-of-words)))
          (list (append (list (wb-inv)) (nth index list-of-words)))))

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
      t
    (and (weak-wordp (car wp))
         (weak-words-reco (cdr wp)))))

(defun weak-words-listp (wp)
  (and (consp wp)
       (weak-words-reco wp)))

(defthmd generate-words-func-equiv
  (implies (and (> h 1)
                (posp h))
           (equal (generate-words-func lst h)
                  (append (generate-words-func lst (- h 1))
                          (list (append (list (wa)) (nth h (generate-words-func lst (- h 1)))))
                          (list (append (list (wa-inv)) (nth h (generate-words-func lst (- h 1)))))
                          (list (append (list (wb)) (nth h (generate-words-func lst (- h 1)))))
                          (list (append (list (wb-inv)) (nth h (generate-words-func lst (- h 1))))))))
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

(defthmd generate-words-func-lemma2-sub1/4
  (implies
   (and
    (not (zp (+ -1 index)))
    (weak-words-reco (generate-words-func '(nil (#\a) (#\b) (#\c) (#\d))
                                          (+ -1 index)))
    (integerp index)
    (< 0 index))
   (weak-words-reco (generate-words-func '(nil (#\a) (#\b) (#\c) (#\d))
                                         index)))
  :hints (("goal"
           :use ((:instance generate-words-func-lemma2-1
                            (lst1 (generate-words-func '(nil (#\a) (#\b) (#\c) (#\d))
                                                       (+ -1 index)))
                            (lst2 (list (append (list (wa))
                                                (nth index
                                                     (generate-words-func '(nil (#\a) (#\b) (#\c) (#\d))
                                                                          (+ -1 index))))
                                        (append (list (wa-inv))
                                                (nth index
                                                     (generate-words-func '(nil (#\a) (#\b) (#\c) (#\d))
                                                                          (+ -1 index))))
                                        (append (list (wb))
                                                (nth index
                                                     (generate-words-func '(nil (#\a) (#\b) (#\c) (#\d))
                                                                          (+ -1 index))))
                                        (append (list (wb-inv))
                                                (nth index
                                                     (generate-words-func '(nil (#\a) (#\b) (#\c) (#\d))
                                                                          (+ -1
                                                                             index)))))))
                 (:instance generate-words-func-equiv (h index)
                            (lst '(nil (#\a) (#\b) (#\c) (#\d))))
                 (:instance generate-words-func-lemma2-2
                            (index index)
                            (wp (generate-words-func '(nil (#\a) (#\b) (#\c) (#\d)) (+ -1 index))))

                 )
           :do-not-induct t
           )))

(defthmd generate-words-func-lemma2
  (implies (posp index)
           (weak-words-listp (generate-words-func '(nil (#\a) (#\b) (#\c) (#\d)) index)))
  :hints (("subgoal *1/4"
           :use ((:instance generate-words-func-lemma2-sub1/4))
           :do-not-induct t
          )))

(defthmd generate-words-func-lemma3
  (implies (posp index)
           (weak-words-listp (generate-words-main index)))
  :hints (("goal"
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
  :hints (("goal"
           :use ((:instance generate-words-func-lemma3)
                 (:instance generate-words-func-lemma2-2 (index n)
                            (wp (generate-words-main index))))
           :in-theory (disable generate-words-main)
           )))

-----

(defun-sk exists-weak-word (w)
  (exists n
          (and (natp n)
               (equal (nth n (generate-words-main (+ n 1)))
                      w))))

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

---

(defthmd test-2000
  (implies (and (natp n)
                (> n 5))
           (equal (generate-words-main (+ n 1))
                  (append (generate-words-main n)
                          (list (append (list (wa)) (nth (- n 4) (generate-words-main n))))
                          (list (append (list (wa-inv)) (nth (- n 4) (generate-words-main n))))
                          (list (append (list (wb)) (nth (- n 4) (generate-words-main n))))
                          (list (append (list (wb-inv)) (nth (- n 4) (generate-words-main n))))))))

(defthmd test-2001
  (implies (and (natp n)
                (< n (len lst1)))
           (equal (nth n (append lst1 lst2))
                  (nth n lst1))))
