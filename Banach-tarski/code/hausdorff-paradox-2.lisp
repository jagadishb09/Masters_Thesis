
(in-package "ACL2")

(include-book "hausdorff-paradox-1")

;; ---

;; (defun f-poles (r)

;;   )

;; (defun poles (w)
;;   (if (r3-rotationp (rotation w))
;;       (f-poles (rotation w))
;;     nil))

(defun m11-a (m)
  (declare (xargs :guard (r3-matrixp m)
                  :verify-guards nil))
  (aref2 :fake-name m 0 0))

(defun m12-b (m)
  (declare (xargs :guard (r3-matrixp m)
                  :verify-guards nil))
  (aref2 :fake-name m 0 1))

(defun m13-c (m)
  (declare (xargs :guard (r3-matrixp m)
                  :verify-guards nil))
  (aref2 :fake-name m 0 2))

(defun m21-d (m)
  (declare (xargs :guard (r3-matrixp m)
                  :verify-guards nil))
  (aref2 :fake-name m 1 0))

(defun m22-e (m)
  (declare (xargs :guard (r3-matrixp m)
                  :verify-guards nil))
  (aref2 :fake-name m 1 1))

(defun m23-f (m)
  (declare (xargs :guard (r3-matrixp m)
                  :verify-guards nil))
  (aref2 :fake-name m 1 2))

(defun m31-g (m)
  (declare (xargs :guard (r3-matrixp m)
                  :verify-guards nil))
  (aref2 :fake-name m 2 0))

(defun m32-h (m)
  (declare (xargs :guard (r3-matrixp m)
                  :verify-guards nil))
  (aref2 :fake-name m 2 1))

(defun m33-i (m)
  (declare (xargs :guard (r3-matrixp m)
                  :verify-guards nil))
  (aref2 :fake-name m 2 2))

(defun point-in-r3-x1 (p)
  (declare (xargs :guard (point-in-r3 p)
                  :verify-guards nil))
  (aref2 :fake-name p 0 0))

(defun point-in-r3-y1 (p)
  (declare (xargs :guard (point-in-r3 p)
                  :verify-guards nil))
  (aref2 :fake-name p 1 0))

(defun point-in-r3-z1 (p)
  (declare (xargs :guard (point-in-r3 p)
                  :verify-guards nil))
  (aref2 :fake-name p 2 0))

(defthmd r3-matrixp=>m=m-trans-1
  (implies (and (r3-matrixp m)
                (equal (m12-b m) (m21-d m))
                (equal (m13-c m) (m31-g m))
                (equal (m23-f m) (m32-h m)))
           (m-= (m-trans m) m))
  :hints (("goal"
           :in-theory (enable m-=)
           )))

(defthmd r3-matrixp=>m=m-trans-2
  (implies (and (r3-matrixp m)
                (m-= (r3-m-inverse m) (m-trans m))
                (equal (m12-b m) (m21-d m))
                (equal (m13-c m) (m31-g m))
                (equal (m23-f m) (m32-h m)))
           (m-= m (r3-m-inverse m)))
  :hints (("goal"
           :use ((:instance r3-matrixp=>m=m-trans-1))
           :in-theory (e/d () (r3-m-inverse))
           )))

(defthmd r3-m-inverse=word-inverse
  (implies (and (reducedwordp w)
                (equal x (acl2-sqrt 2)))
           (m-= (r3-m-inverse (rotation w x))
                (rotation (word-inverse w) x)))
  :hints (("goal"
           :use ((:instance m-*rot-rot-inv=id (p w) (x (acl2-sqrt 2)))
                 (:instance m1*m2=i (m1 (rotation w x)) (m2 (rotation (word-inverse w) x)))
                 (:instance rotation-is-r3-rotationp (w w) (x (acl2-sqrt 2)))
                 (:instance rotation-is-r3-rotationp (w (word-inverse w)) (x (acl2-sqrt 2)))
                 (:instance reducedwordp-word-inverse (x w))
                 )
           :in-theory (e/d () (r3-m-inverse rotation word-inverse reducedwordp))
           )))

(defthmd reduced-rotation-prop-1
  (implies (and (reducedwordp w)
                (equal x (acl2-sqrt 2))
                w)
           (or (not (equal (m12-b (rotation w x)) (m21-d (rotation w x))))
               (not (equal (m13-c (rotation w x)) (m31-g (rotation w x))))
               (not (equal (m23-f (rotation w x)) (m32-h (rotation w x))))))
  :hints (("goal"
           :use ((:instance rotation-is-r3-rotationp (w w) (x (acl2-sqrt 2)))
                 (:instance r3-matrixp=>m=m-trans-1 (m (rotation w x)))
                 (:instance r3-matrixp=>m=m-trans-2 (m (rotation w x)))
                 (:instance r3-m-inverse=word-inverse (w w) (x (acl2-sqrt 2)))
                 (:instance a!=b=>rot-a!=rot-b (a w) (b (word-inverse w)) (x (acl2-sqrt 2)))
                 (:instance reducedwordp-word-inverse (x w))
                 (:instance compose-aa-not-nil-1 (a w))
                 (:instance compose-aa-not-nil-2 (a w))
                 (:instance reducedwordp=>weak-wordp (x w))
                 )

           :in-theory (e/d () (r3-m-inverse rotation word-inverse reducedwordp acl2-sqrt))
           )))

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
                (posp h))
           (< h (- (len (generate-words-func lst h)) 1))))

(defthmd generate-words-func-lemma1-1
  (implies (and (true-listp lst)
                (posp h))
           (< h (len (generate-words-func lst h)))))

(defthmd generate-words-func-lemma2-2
  (implies (and (natp n)
                (< n (len lst1)))
           (equal (nth n (append lst1 lst2))
                  (nth n lst1))))

(defthmd generate-words-func-lemma2-1-3.1.2
  (implies (and (integerp m)
                (<= 0 m))
           (natp m)))

(defthmd generate-words-func-lemma2-1
  (implies (and (true-listp lst)
                (posp h)
                (natp m)
                (< m h))
           (equal (nth m (generate-words-func lst h))
                  (nth m (generate-words-func lst (- h 1)))))
  :hints (("subgoal 3"
           :cases ((posp (- h 1)))
           )
          ("subgoal 3.1"
           :use ((:instance generate-words-func-lemma2-2 (n m)
                            (lst1 (generate-words-func lst (+ -1 h)))
                            (lst2 (list (cons #\a
                                              (nth h (generate-words-func lst (+ -1 h))))
                                        (cons #\b
                                              (nth h (generate-words-func lst (+ -1 h))))
                                        (cons #\c
                                              (nth h (generate-words-func lst (+ -1 h))))
                                        (cons #\d
                                              (nth h
                                                   (generate-words-func lst (+
                                                                             -1
                                                                             h)))))))
                 (:instance generate-words-func-lemma2-1-3.1.2)
                 (:instance generate-words-func-lemma1-1 (h (- h 1))))
           :in-theory nil
           )))

(defthmd generate-words-func-lemma2-3
  (implies (and (true-listp lst)
                (posp n)
                (posp m)
                (< m n))
           (equal (nth m (generate-words-func lst n))
                  (nth m (generate-words-func lst (- n 1)))))
  :hints (("goal"
           :use ((:instance generate-words-func-lemma2-1 (lst lst) (h n) (m m)))
           )))

(defthmd generate-words-func-lemma2-4
  (implies (and (true-listp lst)
                (posp m))
           (equal (nth m (generate-words-func lst m))
                  (nth m (generate-words-func lst (+ m 1)))))
  :hints (("goal"
           :use ((:instance generate-words-func-lemma2-3 (lst lst) (n (+ m 1)) (m m)))
           )))

(defthmd generate-words-func-lemma2-5
  (implies (and (true-listp lst)
                (natp n)
                (< n (len (generate-words-func lst m)))
                (posp m))
           (equal (nth n (generate-words-func lst m))
                  (nth n (generate-words-func lst (+ m 1))))))

(defthmd generate-words-func-lemma2-6
  (implies (and (true-listp lst)
                (posp m))
           (< (len (generate-words-func lst m))
              (len (generate-words-func lst (+ m 1))))))

(defthmd generate-words-func-lemma2-7
  (implies (and (true-listp lst)
                (posp x)
                (posp m))
           (< (len (generate-words-func lst m))
              (len (generate-words-func lst (+ m x)))))
  :hints (("subgoal *1/1"
           :cases ((= m 1))
           )))

(defthmd generate-words-func-lemma2-8
  (implies (and (true-listp lst)
                (natp x)
                (posp m))
           (< m (len (generate-words-func lst (+ m x)))))
  :hints (("goal"
           :cases ((= x 0))
           :use ((:instance generate-words-func-lemma1-1 (h m) (lst lst))
                 (:instance generate-words-func-lemma2-7 (lst lst) (x x) (m m)))
           :in-theory (disable generate-words-func-lemma1-1 generate-words-func-lemma2-6 generate-words-func-lemma2-7 generate-words-func-equiv)
           )
          ))

(defthmd generate-words-func-lemma2-9
  (implies (and (true-listp lst)
                (> (len lst) 1)
                (posp x))
           (equal (nth 1 (generate-words-func lst x))
                  (cadr lst))))

(defthmd generate-words-func-lemma2-10-1/2.3
  (implies (and (not (zp (+ -1 x)))
                (<= (+ -1 x) m)
                (true-listp lst)
                (< 1 (len lst))
                (< m x)
                (< n (len (generate-words-func lst m)))
                (natp x)
                (posp m)
                (natp n))
           (equal (nth n (generate-words-func lst m))
                  (nth n (generate-words-func lst x))))
  :hints (("goal"
           :cases ((equal m (- x 1)))
           :use ((:instance generate-words-func-lemma2-5 (n n) (m (- x 1))))
           )))

(defthmd generate-words-func-lemma2-10-1
  (implies (and (integerp m)
                (integerp x))
           (equal (+ -1 m (- m) x)
                  (- x 1))))

(defthmd generate-words-func-lemma2-10-1/2.2
  (implies (and (not (zp (+ -1 x)))
                (equal (nth n (generate-words-func lst m))
                       (nth n (generate-words-func lst (+ -1 x))))
                (true-listp lst)
                (< 1 (len lst))
                (< m x)
                (< n (len (generate-words-func lst m)))
                (natp x)
                (posp m)
                (natp n))
           (equal (nth n (generate-words-func lst m))
                  (nth n (generate-words-func lst x))))
  :hints (("goal"
           :use ((:instance generate-words-func-lemma2-5 (m (- x 1)) (n n) (lst lst))
                 (:instance generate-words-func-lemma2-10-1)
                 (:instance generate-words-func-lemma2-7 (lst lst) (m m) (x (- (- x m) 1))))
           :do-not-induct t
           )))

(defthmd generate-words-func-lemma2-10-1/2.1-1
  (implies (and (natp x)
                (not (natp (+ -1 x)))
                (integerp m)
                (< m x))
           (not (posp m))))

(defthmd generate-words-func-lemma2-10-1/2.1-2
  (implies (posp m)
           (integerp m)))

(defthmd generate-words-func-lemma2-10
  (implies (and (true-listp lst)
                (< 1 (len lst))
                (> x m)
                (< n (len (generate-words-func lst m)))
                (natp x)
                (posp m)
                (natp n))
           (equal (nth n (generate-words-func lst m))
                  (nth n (generate-words-func lst x))))
  :hints (("goal"
           :induct (generate-words-func lst x)
           )
          ("subgoal *1/2"
           :in-theory nil
           :do-not-induct t
           )
          ("subgoal *1/2.3"
           :use ((:instance generate-words-func-lemma2-10-1/2.3))
           )
          ("subgoal *1/2.2"
           :use ((:instance generate-words-func-lemma2-10-1/2.2))
           )
          ("subgoal *1/2.1"
           :use ((:instance generate-words-func-lemma2-10-1/2.1-1)
                 (:instance generate-words-func-lemma2-10-1/2.1-2))
           )))

(defthmd generate-words-main-lemma1-1
  (implies (and (true-listp lst)
                (equal lst '(nil (#\a) (#\b) (#\c) (#\d)))
                (posp m))
           (equal (nth 5 (generate-words-func lst 1))
                  (nth 5 (generate-words-func lst m)))))

(defthmd generate-words-main-lemma1
  (implies (and (equal eit 5)
                (natp x)
                (> x 5))
           (equal (nth eit (generate-words-main x))
                       '(#\a #\a)))
  :hints (("goal"
           :use ((:instance generate-words-main-lemma1-1 (lst '(nil (#\a) (#\b) (#\c) (#\d)))
                            (m (- x 5))))
           :do-not-induct t
           )))
(defthmd generate-words-main-lemma2-1
  (implies (posp m)
           (equal (car (generate-words-func '(nil (#\a) (#\b) (#\c) (#\d)) m))
                  nil)))

(defthmd generate-words-main-lemma2
  (implies (and (posp x)
                (equal eit 0)
                (> x eit))
           (equal (nth eit (generate-words-main x))
                  nil))
  :hints (("goal"
           :cases ((= x 1)
                   (= x 2)
                   (= x 3)
                   (= x 4)
                   (= x 5)
                   (> x 5))
           )
          ("subgoal 1"
           :use ((:instance generate-words-main-lemma2-1 (m (- x 5))))
           )))

(defthmd generate-words-main-lemma3-1
  (implies (posp m)
           (equal (nth 1 (generate-words-func '(nil (#\a) (#\b) (#\c) (#\d)) m))
                  '(#\a))))

(defthmd generate-words-main-lemma3
  (implies (and (posp x)
                (equal eit 1)
                (> x eit))
           (equal (nth eit (generate-words-main x))
                  '(#\a)))
  :hints (("goal"
           :cases ((= x 2)
                   (= x 3)
                   (= x 4)
                   (= x 5)
                   (> x 5))
           )
          ("subgoal 1"
           :use ((:instance generate-words-main-lemma3-1 (m (- x 5))))
           )))

(defthmd generate-words-main-lemma4-1
  (implies (posp m)
           (equal (nth 2 (generate-words-func '(nil (#\a) (#\b) (#\c) (#\d)) m))
                  '(#\b))))

(defthmd generate-words-main-lemma4
  (implies (and (posp x)
                (equal eit 2)
                (> x eit))
           (equal (nth eit (generate-words-main x))
                  '(#\b)))
  :hints (("goal"
           :cases ((= x 3)
                   (= x 4)
                   (= x 5)
                   (> x 5))
           )
          ("subgoal 1"
           :use ((:instance generate-words-main-lemma4-1 (m (- x 5))))
           )))

(defthmd generate-words-main-lemma5-1
  (implies (posp m)
           (equal (nth 3 (generate-words-func '(nil (#\a) (#\b) (#\c) (#\d)) m))
                  '(#\c))))

(defthmd generate-words-main-lemma5
  (implies (and (posp x)
                (equal eit 3)
                (> x eit))
           (equal (nth eit (generate-words-main x))
                  '(#\c)))
  :hints (("goal"
           :cases ((= x 4)
                   (= x 5)
                   (> x 5))
           )
          ("subgoal 1"
           :use ((:instance generate-words-main-lemma5-1 (m (- x 5))))
           )))

(defthmd generate-words-main-lemma6-1
  (implies (posp m)
           (equal (nth 4 (generate-words-func '(nil (#\a) (#\b) (#\c) (#\d)) m))
                  '(#\d))))

(defthmd generate-words-main-lemma6
  (implies (and (posp x)
                (equal eit 4)
                (> x eit))
           (equal (nth eit (generate-words-main x))
                  '(#\d)))
  :hints (("goal"
           :cases ((= x 5)
                   (> x 5))
           )
          ("subgoal 1"
           :use ((:instance generate-words-main-lemma6-1 (m (- x 5))))
           )))

(defthmd generate-words-main-lemma7-2
  (implies (posp n)
           (< (+ n 5)
              (len (generate-words-func '(nil (#\a) (#\b) (#\c) (#\d)) n))))
  :hints (("goal"
           :induct (generate-words-func '(nil (#\a) (#\b) (#\c) (#\d)) n)
           )))

(defthmd generate-words-main-lemma7-1
  (implies (and (natp m)
                (> m 5))
           (< m (len (generate-words-main m))))
  :hints (("goal"
           :use ((:instance generate-words-func-lemma1-1 (lst '(nil (#\a) (#\b) (#\c) (#\d)))
                            (h (- n 5)))
                 (:instance generate-words-main-lemma7-2 (n (- m 5))))

           )))

(defthmd generate-words-main-lemma7
  (implies (and (natp x)
                (> m 5)
                (> x m)
                (natp m))
           (equal (nth m (generate-words-main m))
                  (nth m (generate-words-main x))))
  :hints (("goal"
           :use ((:instance generate-words-func-lemma2-10 (lst '(nil (#\a) (#\b) (#\c) (#\d)))
                            (m (- m 5))
                            (n m)
                            (x (- x 5)))
                 (:instance generate-words-main-lemma7-1))
           :do-not-induct t
           )))

(defthmd generate-words-main-lemma8
  (implies (and (> m 5)
                (natp m))
           (and (equal (nth m (generate-words-main (+ m 4)))
                       (nth m (generate-words-main m)))
                (equal (nth m (generate-words-main m))
                       (nth m (generate-words-main (+ (len (generate-words-main (+ m 4))) 1))))))
  :hints (("goal"
           :use ((:instance generate-words-main-lemma7 (x (+ m 5)) (m m))
                 (:instance generate-words-main-lemma7 (x (+ (len (generate-words-main (+ m 4))) 1)) (m m))
                 (:instance generate-words-main-lemma7-1 (m (+ m 4)))
                 )
           :do-not-induct t
           )))

(defthmd generate-words-main-lemma9
  (implies (and (posp m)
                (<= m 5)
                (natp n)
                (< n (len (generate-words-main m))))
           (< n m)))

(defthmd generate-words-main-lemma10-1
  (implies (and (natp n)
                (posp m)
                (< n (len (generate-words-main m)))
                (<= m 5))
           (< n m)))

(defthmd generate-words-main-lemma10-2
  (implies (and (integerp m)
                (< 0 m)
                (integerp x)
                (< 0 x)
                (< m x)
                (integerp n)
                (<= 0 n)
                (<= m 5)
                (< n (len (generate-words-len-1 m)))
                (<= x 5))
           (equal (nth n (generate-words-len-1 m))
                  (nth n (generate-words-len-1 x)))))

(defthmd generate-words-main-lemma10
  (implies (and (posp m)
                (posp x)
                (> x m)
                (natp n)
                (< n (len (generate-words-main m))))
           (equal (nth n (generate-words-main m))
                  (nth n (generate-words-main x))))
  :hints (("goal"
           :do-not-induct t
           )
          ("subgoal 1"
           :use ((:instance generate-words-main-lemma10-2))
           )
          ("subgoal 2"
           :cases ((= n 0)
                   (= n 1)
                   (= n 2)
                   (= n 3)
                   (= n 4))
           :use ((:instance generate-words-main-lemma10-1)
                 (:instance generate-words-main-lemma2 (x m) (eit n))
                 (:instance generate-words-main-lemma2 (x x) (eit n))
                 (:instance generate-words-main-lemma3 (x m) (eit n))
                 (:instance generate-words-main-lemma3 (x x) (eit n))
                 (:instance generate-words-main-lemma4 (x m) (eit n))
                 (:instance generate-words-main-lemma4 (x x) (eit n))
                 (:instance generate-words-main-lemma5 (x m) (eit n))
                 (:instance generate-words-main-lemma5 (x x) (eit n))
                 (:instance generate-words-main-lemma6 (x m) (eit n))
                 (:instance generate-words-main-lemma6 (x x) (eit n)))
           )
          ("subgoal 4"
           :use ((:instance generate-words-func-lemma2-10 (lst '(nil (#\a) (#\b) (#\c) (#\d)))
                            (m (- m 5))
                            (x (- x 5)))))))

(defun-sk exists-weak-word-1 (w n)
  (exists m
          (and (natp m)
               (< m n)
               (equal (nth m (generate-words-main n))
                      w))))

(defun-sk exists-weak-word (w)
  (exists n
          (and (posp n)
               (exists-weak-word-1 w n))))

(defthmd exists-weak-word-implies
  (implies (exists-weak-word w)
           (and (posp (exists-weak-word-witness w))
                (natp (exists-weak-word-1-witness w (exists-weak-word-witness w)))
                (< (exists-weak-word-1-witness w (exists-weak-word-witness w)) (exists-weak-word-witness w))
                (equal (nth (exists-weak-word-1-witness w (exists-weak-word-witness w))
                            (generate-words-main (exists-weak-word-witness w)))
                       w))))

(defthmd any-weak-word-exist-sub-1/2.4-7
  (implies (and (weak-wordp (cdr w))
                (not (atom w))
                (equal (car w) (wa))
                (exists-weak-word (cdr w))
                (weak-wordp w)
                (= (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 0))
           (exists-weak-word w))

  :hints (("goal"
           :use ((:instance exists-weak-word-implies (w (cdr w)))
                 (:instance generate-words-main-lemma2
                            (eit (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))))
                            (x (exists-weak-word-witness (cdr w))))
                 (:instance exists-weak-word-suff (n 2) (w '(#\a)))
                 (:instance exists-weak-word-1-suff (m 1) (w '(#\a)) (n 2)))
           :do-not-induct t
           )))

(defthmd any-weak-word-exist-sub-1/2.4-6
  (implies (and (weak-wordp (cdr w))
                (not (atom w))
                (equal (car w) (wa))
                (exists-weak-word (cdr w))
                (weak-wordp w)
                (= (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 1))
           (exists-weak-word w))

  :hints (("goal"
           :use ((:instance exists-weak-word-implies (w (cdr w)))
                 (:instance generate-words-main-lemma3
                            (eit (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))))
                            (x (exists-weak-word-witness (cdr w))))
                 (:instance exists-weak-word-suff (n 6) (w '(#\a #\a)))
                 (:instance exists-weak-word-1-suff (m 5) (w '(#\a #\a)) (n 6)))
           :do-not-induct t
           )))

(defthmd any-weak-word-exist-sub-1/2.4-5
  (implies (and (weak-wordp (cdr w))
                (not (atom w))
                (equal (car w) (wa))
                (exists-weak-word (cdr w))
                (weak-wordp w)
                (= (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 2))
           (exists-weak-word w))

  :hints (("goal"
           :use ((:instance exists-weak-word-implies (w (cdr w)))
                 (:instance generate-words-main-lemma4
                            (eit (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))))
                            (x (exists-weak-word-witness (cdr w))))
                 (:instance exists-weak-word-suff (n 10) (w '(#\a #\b)))
                 (:instance exists-weak-word-1-suff (m 9) (w '(#\a #\b)) (n 10)))
           :do-not-induct t
           )))

(defthmd any-weak-word-exist-sub-1/2.4-4
  (implies (and (weak-wordp (cdr w))
                (not (atom w))
                (equal (car w) (wa))
                (exists-weak-word (cdr w))
                (weak-wordp w)
                (= (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 3))
           (exists-weak-word w))

  :hints (("goal"
           :use ((:instance exists-weak-word-implies (w (cdr w)))
                 (:instance generate-words-main-lemma5
                            (eit (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))))
                            (x (exists-weak-word-witness (cdr w))))
                 (:instance exists-weak-word-suff (n 14) (w '(#\a #\c)))
                 (:instance exists-weak-word-1-suff (m 13) (w '(#\a #\c)) (n 14)))
           :do-not-induct t
           )))

(defthmd any-weak-word-exist-sub-1/2.4-3
  (implies (and (weak-wordp (cdr w))
                (not (atom w))
                (equal (car w) (wa))
                (exists-weak-word (cdr w))
                (weak-wordp w)
                (= (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 4))
           (exists-weak-word w))

  :hints (("goal"
           :use ((:instance exists-weak-word-implies (w (cdr w)))
                 (:instance generate-words-main-lemma6
                            (eit (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))))
                            (x (exists-weak-word-witness (cdr w))))
                 (:instance exists-weak-word-suff (n 18) (w '(#\a #\d)))
                 (:instance exists-weak-word-1-suff (m 17) (w '(#\a #\d)) (n 18)))
           :do-not-induct t
           )))

(defthmd any-weak-word-exist-sub-1/2.4-2
  (implies (and (weak-wordp (cdr w))
                (not (atom w))
                (equal (car w) (wa))
                (exists-weak-word (cdr w))
                (weak-wordp w)
                (= (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 5))
           (exists-weak-word w))

  :hints (("goal"
           :use ((:instance exists-weak-word-implies (w (cdr w)))
                 (:instance generate-words-main-lemma1
                            (eit (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))))
                            (x (exists-weak-word-witness (cdr w))))
                 (:instance exists-weak-word-suff (n 22) (w '(#\a #\a #\a)))
                 (:instance exists-weak-word-1-suff (m 21) (w '(#\a #\a #\a)) (n 22)))
           :do-not-induct t
           )))

(defthmd exists-weak-word-lemma1
  (implies (and (natp n)
                (> n 5))
           (equal (generate-words-main (+ n 1))
                  (append (generate-words-main n)
                          (list (append (list (wa)) (nth (- n 4) (generate-words-main n))))
                          (list (append (list (wa-inv)) (nth (- n 4) (generate-words-main n))))
                          (list (append (list (wb)) (nth (- n 4) (generate-words-main n))))
                          (list (append (list (wb-inv)) (nth (- n 4) (generate-words-main n))))))))

(defthmd any-weak-word-exist-sub-1/2.4-1-hints-1
  (implies (equal lst (append lst1 lst2))
           (equal (nth (len lst1) lst)
                  (car lst2))))

(defthmd any-weak-word-exist-sub-1/2.4-1-hints-2
  (implies (and (weak-wordp (cdr w))
                (not (atom w))
                (equal (car w) (wa))
                (exists-weak-word (cdr w))
                (weak-wordp w)
                (> (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 5)
                (equal
                 (nth
                  (len
                   (generate-words-main
                    (+ (exists-weak-word-1-witness (cdr w)
                                                   (exists-weak-word-witness (cdr w)))
                       4)))
                  (generate-words-main
                   (+ (exists-weak-word-1-witness (cdr w)
                                                  (exists-weak-word-witness (cdr w)))
                      5)))
                 w))
           (equal
            (nth
             (len
              (generate-words-main
               (+ (exists-weak-word-1-witness (cdr w)
                                              (exists-weak-word-witness (cdr w)))
                  4)))
             (generate-words-main
              (+ (exists-weak-word-1-witness (cdr w)
                                             (exists-weak-word-witness (cdr w)))
                 5)))
            (nth
             (len
              (generate-words-main
               (+ (exists-weak-word-1-witness (cdr w)
                                              (exists-weak-word-witness (cdr w)))
                  4)))
             (generate-words-main
              (+ (len
                  (generate-words-main
                   (+ (exists-weak-word-1-witness (cdr w)
                                                  (exists-weak-word-witness (cdr w)))
                      4))) 1)))))
  :hints (("goal"
           :use ((:instance generate-words-main-lemma10 (m (+ (exists-weak-word-1-witness (cdr w)
                                                                                          (exists-weak-word-witness
                                                                                           (cdr w))) 5))
                            (n (len (generate-words-main
                                     (+ (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w)))
                                        4))))
                            (x (+ (len (generate-words-main
                                        (+ (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w)))
                                           4))) 1)))
                 (:instance generate-words-main-lemma7-1
                            (m (+ (exists-weak-word-1-witness (cdr w)
                                                              (exists-weak-word-witness (cdr w)))
                                  4))))
           :do-not-induct t
           )))


(defthmd any-weak-word-exist-sub-1/2.4-1-hints
  (implies (and (weak-wordp (cdr w))
                (not (atom w))
                (equal (car w) (wa))
                (exists-weak-word (cdr w))
                (weak-wordp w)
                (> (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 5))
           (and (posp (exists-weak-word-witness (cdr w)))
                (natp (exists-weak-word-1-witness (cdr w)
                                                  (exists-weak-word-witness (cdr w))))
                (natp (+ (exists-weak-word-1-witness (cdr w)
                                                     (exists-weak-word-witness (cdr w)))
                         4))
                (natp (exists-weak-word-witness (cdr w)))
                (posp (+ (exists-weak-word-1-witness (cdr w)
                                          (exists-weak-word-witness (cdr w)))
                         5))
                (natp
                 (len
                  (generate-words-main
                   (+ (exists-weak-word-1-witness (cdr w)
                                                  (exists-weak-word-witness (cdr w)))
                      4))))
                (posp
                 (+
                  (len
                   (generate-words-main
                    (+ (exists-weak-word-1-witness (cdr w)
                                                   (exists-weak-word-witness (cdr w)))
                       4)))
                  1))
                (equal
                 (nth
                  (len
                   (generate-words-main
                    (+ (exists-weak-word-1-witness (cdr w)
                                                   (exists-weak-word-witness (cdr w)))
                       4)))
                  (generate-words-main
                   (+ (exists-weak-word-1-witness (cdr w)
                                                  (exists-weak-word-witness (cdr w)))
                      5)))
                 w)))
  :hints (("goal"
           :use ((:instance exists-weak-word-lemma1
                            (n (+ (exists-weak-word-1-witness (cdr w)
                                                              (exists-weak-word-witness (cdr w)))
                                  4)))
                 (:instance generate-words-main-lemma7 (x (exists-weak-word-witness (cdr w)))
                            (m (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w)))))
                 (:instance generate-words-main-lemma7
                            (x (+ (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 4))
                            (m (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w)))))
                 (:instance any-weak-word-exist-sub-1/2.4-1-hints-1
                            (lst (generate-words-main
                                  (+ (exists-weak-word-1-witness (cdr w)
                                                                 (exists-weak-word-witness (cdr w)))
                                     5)))
                            (lst1 (generate-words-main
                                   (+ (exists-weak-word-1-witness (cdr w)
                                                                  (exists-weak-word-witness (cdr w)))
                                      4)))
                            (lst2 (list (append (list (wa)) (nth
                                                             (exists-weak-word-1-witness (cdr w)
                                                                                         (exists-weak-word-witness
                                                                                          (cdr w)))
                                                             (generate-words-main (+ (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 4))))
                                        (append (list (wa-inv)) (nth
                                                             (exists-weak-word-1-witness (cdr w)
                                                                                         (exists-weak-word-witness
                                                                                          (cdr w)))
                                                             (generate-words-main (+ (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 4))))
                                        (append (list (wb)) (nth
                                                             (exists-weak-word-1-witness (cdr w)
                                                                                         (exists-weak-word-witness
                                                                                          (cdr w)))
                                                             (generate-words-main (+ (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 4))))
                                        (append (list (wb-inv)) (nth
                                                             (exists-weak-word-1-witness (cdr w)
                                                                                         (exists-weak-word-witness
                                                                                          (cdr w)))
                                                             (generate-words-main
  (+ (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w)))
     4))))))))
           :do-not-induct t
           )))

(defthmd any-weak-word-exist-sub-1/2.4-1
  (implies (and (weak-wordp (cdr w))
                (not (atom w))
                (equal (car w) (wa))
                (exists-weak-word (cdr w))
                (weak-wordp w)
                (> (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 5))
           (exists-weak-word w))
  :hints (("goal"
           :do-not-induct t
           :use ((:instance exists-weak-word-implies (w (cdr w)))
                 (:instance exists-weak-word-lemma1
                            (n (+ (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 4)))
                 (:instance generate-words-main-lemma7 (x (exists-weak-word-witness (cdr w)))
                            (m (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w)))))
                 (:instance generate-words-main-lemma7
                            (x (+ (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 4))
                            (m (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w)))))
                 (:instance exists-weak-word-suff
                            (n (+ (len (generate-words-main
                                        (+ (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w)))
                                           4))) 1))
                            (w w))
                 (:instance exists-weak-word-1-suff
                            (n (+ (len (generate-words-main
                                        (+ (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w)))
                                           4))) 1))
                            (w w)
                            (m (len (generate-words-main
                                     (+ (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w)))
                                        4)))))
                 (:instance any-weak-word-exist-sub-1/2.4-1-hints-2)
                 (:instance any-weak-word-exist-sub-1/2.4-1-hints))
           :in-theory nil
           )))

(defthmd any-weak-word-exist-sub-1/2.4
  (implies (and (weak-wordp (cdr w))
                (not (atom w))
                (equal (car w) (wa))
                (exists-weak-word (cdr w))
                (weak-wordp w))
           (exists-weak-word w))
  :hints (("goal"
           :cases ((= (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 0)
                   (= (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 1)
                   (= (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 2)
                   (= (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 3)
                   (= (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 4)
                   (= (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 5)
                   (> (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 5))
           :use ((:instance exists-weak-word-implies (w (cdr w))))
           :do-not-induct t
           )
          ("subgoal 7"
           :use ((:instance any-weak-word-exist-sub-1/2.4-7))
           :in-theory nil
           )
          ("subgoal 6"
           :use ((:instance any-weak-word-exist-sub-1/2.4-6))
           :in-theory nil
           )
          ("subgoal 5"
           :use ((:instance any-weak-word-exist-sub-1/2.4-5))
           :in-theory nil
           )
          ("subgoal 4"
           :use ((:instance any-weak-word-exist-sub-1/2.4-4))
           :in-theory nil
           )
          ("subgoal 3"
           :use ((:instance any-weak-word-exist-sub-1/2.4-3))
           :in-theory nil
           )
          ("subgoal 2"
           :use ((:instance any-weak-word-exist-sub-1/2.4-2))
           :in-theory nil
           )
          ("subgoal 1"
           :use ((:instance any-weak-word-exist-sub-1/2.4-1))
           )
          ))

(defthmd any-weak-word-exist-sub-1/2.3-7
  (implies (and (weak-wordp (cdr w))
                (not (atom w))
                (equal (car w) (wb))
                (exists-weak-word (cdr w))
                (weak-wordp w)
                (= (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 0))
           (exists-weak-word w))

  :hints (("goal"
           :use ((:instance exists-weak-word-implies (w (cdr w)))
                 (:instance generate-words-main-lemma2
                            (eit (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))))
                            (x (exists-weak-word-witness (cdr w))))
                 (:instance exists-weak-word-suff (n 4) (w '(#\c)))
                 (:instance exists-weak-word-1-suff (m 3) (w '(#\c)) (n 4)))
           :do-not-induct t
           )))

(defthmd any-weak-word-exist-sub-1/2.3-6
  (implies (and (weak-wordp (cdr w))
                (not (atom w))
                (equal (car w) (wb))
                (exists-weak-word (cdr w))
                (weak-wordp w)
                (= (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 1))
           (exists-weak-word w))

  :hints (("goal"
           :use ((:instance exists-weak-word-implies (w (cdr w)))
                 (:instance generate-words-main-lemma3
                            (eit (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))))
                            (x (exists-weak-word-witness (cdr w))))
                 (:instance exists-weak-word-suff (n 8) (w '(#\c #\a)))
                 (:instance exists-weak-word-1-suff (m 7) (w '(#\c #\a)) (n 8)))
           :do-not-induct t
           )))

(defthmd any-weak-word-exist-sub-1/2.3-5
  (implies (and (weak-wordp (cdr w))
                (not (atom w))
                (equal (car w) (wb))
                (exists-weak-word (cdr w))
                (weak-wordp w)
                (= (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 2))
           (exists-weak-word w))

  :hints (("goal"
           :use ((:instance exists-weak-word-implies (w (cdr w)))
                 (:instance generate-words-main-lemma4
                            (eit (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))))
                            (x (exists-weak-word-witness (cdr w))))
                 (:instance exists-weak-word-suff (n 12) (w '(#\c #\b)))
                 (:instance exists-weak-word-1-suff (m 11) (w '(#\c #\b)) (n 12)))
           :do-not-induct t
           )))

(defthmd any-weak-word-exist-sub-1/2.3-4
  (implies (and (weak-wordp (cdr w))
                (not (atom w))
                (equal (car w) (wb))
                (exists-weak-word (cdr w))
                (weak-wordp w)
                (= (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 3))
           (exists-weak-word w))

  :hints (("goal"
           :use ((:instance exists-weak-word-implies (w (cdr w)))
                 (:instance generate-words-main-lemma5
                            (eit (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))))
                            (x (exists-weak-word-witness (cdr w))))
                 (:instance exists-weak-word-suff (n 16) (w '(#\c #\c)))
                 (:instance exists-weak-word-1-suff (m 15) (w '(#\c #\c)) (n 16)))
           :do-not-induct t
           )))

(defthmd any-weak-word-exist-sub-1/2.3-3
  (implies (and (weak-wordp (cdr w))
                (not (atom w))
                (equal (car w) (wb))
                (exists-weak-word (cdr w))
                (weak-wordp w)
                (= (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 4))
           (exists-weak-word w))

  :hints (("goal"
           :use ((:instance exists-weak-word-implies (w (cdr w)))
                 (:instance generate-words-main-lemma6
                            (eit (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))))
                            (x (exists-weak-word-witness (cdr w))))
                 (:instance exists-weak-word-suff (n 20) (w '(#\c #\d)))
                 (:instance exists-weak-word-1-suff (m 19) (w '(#\c #\d)) (n 20)))
           :do-not-induct t
           )))

(defthmd any-weak-word-exist-sub-1/2.3-2
  (implies (and (weak-wordp (cdr w))
                (not (atom w))
                (equal (car w) (wb))
                (exists-weak-word (cdr w))
                (weak-wordp w)
                (= (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 5))
           (exists-weak-word w))

  :hints (("goal"
           :use ((:instance exists-weak-word-implies (w (cdr w)))
                 (:instance generate-words-main-lemma1
                            (eit (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))))
                            (x (exists-weak-word-witness (cdr w))))
                 (:instance exists-weak-word-suff (n 24) (w '(#\c #\a #\a)))
                 (:instance exists-weak-word-1-suff (m 23) (w '(#\c #\a #\a)) (n 24)))
           :do-not-induct t
           )))

(defthmd any-weak-word-exist-sub-1/2.3-1-hints-1
  (implies (equal lst (append lst1 lst2))
           (equal (nth (+ (len lst1) 2) lst)
                  (caddr lst2))))

(defthmd any-weak-word-exist-sub-1/2.3-1-hints-2
  (implies (and (weak-wordp (cdr w))
                (not (atom w))
                (equal (car w) (wb))
                (exists-weak-word (cdr w))
                (weak-wordp w)
                (> (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 5)
                (equal
                 (nth
                  (+
                  (len
                   (generate-words-main
                    (+ (exists-weak-word-1-witness (cdr w)
                                                   (exists-weak-word-witness (cdr w)))
                       4))) 2)
                  (generate-words-main
                   (+ (exists-weak-word-1-witness (cdr w)
                                                  (exists-weak-word-witness (cdr w)))
                      5)))
                 w))
           (equal
            (nth
             (+
              (len
               (generate-words-main
                (+ (exists-weak-word-1-witness (cdr w)
                                               (exists-weak-word-witness (cdr w)))
                   4))) 2)
             (generate-words-main
              (+ (exists-weak-word-1-witness (cdr w)
                                             (exists-weak-word-witness (cdr w)))
                 5)))
            (nth
             (+
              (len
               (generate-words-main
                (+ (exists-weak-word-1-witness (cdr w)
                                               (exists-weak-word-witness (cdr w)))
                   4))) 2)
             (generate-words-main
              (+ (len
                  (generate-words-main
                   (+ (exists-weak-word-1-witness (cdr w)
                                                  (exists-weak-word-witness (cdr w)))
                      4))) 3)))))
  :hints (("goal"
           :use ((:instance generate-words-main-lemma10 (m (+ (exists-weak-word-1-witness (cdr w)
                                                                                          (exists-weak-word-witness
                                                                                           (cdr w))) 5))
                            (n (+ (len (generate-words-main
                                        (+ (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w)))
                                           4))) 2))
                            (x (+ (len (generate-words-main
                                        (+ (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w)))
                                           4))) 3)))
                 (:instance generate-words-main-lemma7-1
                            (m (+ (exists-weak-word-1-witness (cdr w)
                                                              (exists-weak-word-witness (cdr w)))
                                  4))))
           :do-not-induct t
           )))

(defthmd any-weak-word-exist-sub-1/2.3-1-hints
  (implies (and (weak-wordp (cdr w))
                (not (atom w))
                (equal (car w) (wb))
                (exists-weak-word (cdr w))
                (weak-wordp w)
                (> (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 5))
           (and (posp (exists-weak-word-witness (cdr w)))
                (natp (exists-weak-word-1-witness (cdr w)
                                                  (exists-weak-word-witness (cdr w))))
                (natp (+ (exists-weak-word-1-witness (cdr w)
                                                     (exists-weak-word-witness (cdr w)))
                         4))
                (natp (exists-weak-word-witness (cdr w)))
                (posp (+ (exists-weak-word-1-witness (cdr w)
                                          (exists-weak-word-witness (cdr w)))
                         5))
                (natp
                 (+
                  (len
                   (generate-words-main
                    (+ (exists-weak-word-1-witness (cdr w)
                                                   (exists-weak-word-witness (cdr w)))
                       4))) 2))
                (posp
                 (+
                  (len
                   (generate-words-main
                    (+ (exists-weak-word-1-witness (cdr w)
                                                   (exists-weak-word-witness (cdr w)))
                       4)))
                  3))
                (equal
                 (nth
                  (+
                   (len
                    (generate-words-main
                     (+ (exists-weak-word-1-witness (cdr w)
                                                    (exists-weak-word-witness (cdr w)))
                        4)))
                   2)
                  (generate-words-main
                   (+ (exists-weak-word-1-witness (cdr w)
                                                  (exists-weak-word-witness (cdr w)))
                      5)))
                 w)))
  :hints (("goal"
           :use ((:instance exists-weak-word-lemma1
                            (n (+ (exists-weak-word-1-witness (cdr w)
                                                              (exists-weak-word-witness (cdr w)))
                                  4)))
                 (:instance generate-words-main-lemma7 (x (exists-weak-word-witness (cdr w)))
                            (m (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w)))))
                 (:instance generate-words-main-lemma7
                            (x (+ (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 4))
                            (m (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w)))))
                 (:instance any-weak-word-exist-sub-1/2.3-1-hints-1
                            (lst (generate-words-main
                                  (+ (exists-weak-word-1-witness (cdr w)
                                                                 (exists-weak-word-witness (cdr w)))
                                     5)))
                            (lst1 (generate-words-main
                                   (+ (exists-weak-word-1-witness (cdr w)
                                                                  (exists-weak-word-witness (cdr w)))
                                      4)))
                            (lst2 (list (append (list (wa)) (nth
                                                             (exists-weak-word-1-witness (cdr w)
                                                                                         (exists-weak-word-witness
                                                                                          (cdr w)))
                                                             (generate-words-main (+ (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 4))))
                                        (append (list (wa-inv)) (nth
                                                             (exists-weak-word-1-witness (cdr w)
                                                                                         (exists-weak-word-witness
                                                                                          (cdr w)))
                                                             (generate-words-main (+ (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 4))))
                                        (append (list (wb)) (nth
                                                             (exists-weak-word-1-witness (cdr w)
                                                                                         (exists-weak-word-witness
                                                                                          (cdr w)))
                                                             (generate-words-main (+ (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 4))))
                                        (append (list (wb-inv)) (nth
                                                             (exists-weak-word-1-witness (cdr w)
                                                                                         (exists-weak-word-witness
                                                                                          (cdr w)))
                                                             (generate-words-main
  (+ (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w)))
     4))))))))
           :do-not-induct t
           )))

(defthmd any-weak-word-exist-sub-1/2.3-1
  (implies (and (weak-wordp (cdr w))
                (not (atom w))
                (equal (car w) (wb))
                (exists-weak-word (cdr w))
                (weak-wordp w)
                (> (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 5))
           (exists-weak-word w))
  :hints (("goal"
           :do-not-induct t
           :use ((:instance exists-weak-word-implies (w (cdr w)))
                 (:instance exists-weak-word-lemma1
                            (n (+ (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 4)))
                 (:instance generate-words-main-lemma7 (x (exists-weak-word-witness (cdr w)))
                            (m (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w)))))
                 (:instance generate-words-main-lemma7
                            (x (+ (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 4))
                            (m (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w)))))
                 (:instance exists-weak-word-suff
                            (n (+ (len (generate-words-main
                                        (+ (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w)))
                                           4))) 3))
                            (w w))
                 (:instance exists-weak-word-1-suff
                            (n (+ (len (generate-words-main
                                        (+ (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w)))
                                           4))) 3))
                            (w w)
                            (m (+ (len (generate-words-main
                                        (+ (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w)))
                                           4))) 2)))
                 (:instance any-weak-word-exist-sub-1/2.3-1-hints-2)
                 (:instance any-weak-word-exist-sub-1/2.3-1-hints))
           :in-theory nil
           )))

(defthmd any-weak-word-exist-sub-1/2.3
  (implies (and (weak-wordp (cdr w))
                (not (atom w))
                (equal (car w) (wb))
                (exists-weak-word (cdr w))
                (weak-wordp w))
           (exists-weak-word w))
  :hints (("goal"
           :cases ((= (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 0)
                   (= (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 1)
                   (= (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 2)
                   (= (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 3)
                   (= (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 4)
                   (= (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 5)
                   (> (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 5))
           :use ((:instance exists-weak-word-implies (w (cdr w))))
           :do-not-induct t
           )
          ("subgoal 7"
           :use ((:instance any-weak-word-exist-sub-1/2.3-7))
           :in-theory nil
           )
          ("subgoal 6"
           :use ((:instance any-weak-word-exist-sub-1/2.3-6))
           :in-theory nil
           )
          ("subgoal 5"
           :use ((:instance any-weak-word-exist-sub-1/2.3-5))
           :in-theory nil
           )
          ("subgoal 4"
           :use ((:instance any-weak-word-exist-sub-1/2.3-4))
           :in-theory nil
           )
          ("subgoal 3"
           :use ((:instance any-weak-word-exist-sub-1/2.3-3))
           :in-theory nil
           )
          ("subgoal 2"
           :use ((:instance any-weak-word-exist-sub-1/2.3-2))
           :in-theory nil
           )
          ("subgoal 1"
           :use ((:instance any-weak-word-exist-sub-1/2.3-1))
           )
          ))

(defthmd any-weak-word-exist-sub-1/2.2-7
  (implies (and (weak-wordp (cdr w))
                (not (atom w))
                (equal (car w) (wa-inv))
                (exists-weak-word (cdr w))
                (weak-wordp w)
                (= (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 0))
           (exists-weak-word w))

  :hints (("goal"
           :use ((:instance exists-weak-word-implies (w (cdr w)))
                 (:instance generate-words-main-lemma2
                            (eit (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))))
                            (x (exists-weak-word-witness (cdr w))))
                 (:instance exists-weak-word-suff (n 3) (w '(#\b)))
                 (:instance exists-weak-word-1-suff (m 2) (w '(#\b)) (n 3)))
           :do-not-induct t
           )))

(defthmd any-weak-word-exist-sub-1/2.2-6
  (implies (and (weak-wordp (cdr w))
                (not (atom w))
                (equal (car w) (wa-inv))
                (exists-weak-word (cdr w))
                (weak-wordp w)
                (= (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 1))
           (exists-weak-word w))

  :hints (("goal"
           :use ((:instance exists-weak-word-implies (w (cdr w)))
                 (:instance generate-words-main-lemma3
                            (eit (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))))
                            (x (exists-weak-word-witness (cdr w))))
                 (:instance exists-weak-word-suff (n 7) (w '(#\b #\a)))
                 (:instance exists-weak-word-1-suff (m 6) (w '(#\b #\a)) (n 7)))
           :do-not-induct t
           )))

(defthmd any-weak-word-exist-sub-1/2.2-5
  (implies (and (weak-wordp (cdr w))
                (not (atom w))
                (equal (car w) (wa-inv))
                (exists-weak-word (cdr w))
                (weak-wordp w)
                (= (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 2))
           (exists-weak-word w))

  :hints (("goal"
           :use ((:instance exists-weak-word-implies (w (cdr w)))
                 (:instance generate-words-main-lemma4
                            (eit (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))))
                            (x (exists-weak-word-witness (cdr w))))
                 (:instance exists-weak-word-suff (n 11) (w '(#\b #\b)))
                 (:instance exists-weak-word-1-suff (m 10) (w '(#\b #\b)) (n 11)))
           :do-not-induct t
           )))

(defthmd any-weak-word-exist-sub-1/2.2-4
  (implies (and (weak-wordp (cdr w))
                (not (atom w))
                (equal (car w) (wa-inv))
                (exists-weak-word (cdr w))
                (weak-wordp w)
                (= (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 3))
           (exists-weak-word w))

  :hints (("goal"
           :use ((:instance exists-weak-word-implies (w (cdr w)))
                 (:instance generate-words-main-lemma5
                            (eit (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))))
                            (x (exists-weak-word-witness (cdr w))))
                 (:instance exists-weak-word-suff (n 15) (w '(#\b #\c)))
                 (:instance exists-weak-word-1-suff (m 14) (w '(#\b #\c)) (n 15)))
           :do-not-induct t
           )))

(defthmd any-weak-word-exist-sub-1/2.2-3
  (implies (and (weak-wordp (cdr w))
                (not (atom w))
                (equal (car w) (wa-inv))
                (exists-weak-word (cdr w))
                (weak-wordp w)
                (= (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 4))
           (exists-weak-word w))

  :hints (("goal"
           :use ((:instance exists-weak-word-implies (w (cdr w)))
                 (:instance generate-words-main-lemma6
                            (eit (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))))
                            (x (exists-weak-word-witness (cdr w))))
                 (:instance exists-weak-word-suff (n 20) (w '(#\b #\d)))
                 (:instance exists-weak-word-1-suff (m 18) (w '(#\b #\d)) (n 20)))
           :do-not-induct t
           )))

(defthmd any-weak-word-exist-sub-1/2.2-2
  (implies (and (weak-wordp (cdr w))
                (not (atom w))
                (equal (car w) (wa-inv))
                (exists-weak-word (cdr w))
                (weak-wordp w)
                (= (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 5))
           (exists-weak-word w))

  :hints (("goal"
           :use ((:instance exists-weak-word-implies (w (cdr w)))
                 (:instance generate-words-main-lemma1
                            (eit (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))))
                            (x (exists-weak-word-witness (cdr w))))
                 (:instance exists-weak-word-suff (n 24) (w '(#\b #\a #\a)))
                 (:instance exists-weak-word-1-suff (m 22) (w '(#\b #\a #\a)) (n 24)))
           :do-not-induct t
           )))

(defthmd any-weak-word-exist-sub-1/2.2-1-hints-1
  (implies (equal lst (append lst1 lst2))
           (equal (nth (+ (len lst1) 1) lst)
                  (cadr lst2))))

(defthmd any-weak-word-exist-sub-1/2.2-1-hints-2
  (implies (and (weak-wordp (cdr w))
                (not (atom w))
                (equal (car w) (wa-inv))
                (exists-weak-word (cdr w))
                (weak-wordp w)
                (> (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 5)
                (equal
                 (nth
                  (+
                  (len
                   (generate-words-main
                    (+ (exists-weak-word-1-witness (cdr w)
                                                   (exists-weak-word-witness (cdr w)))
                       4))) 1)
                  (generate-words-main
                   (+ (exists-weak-word-1-witness (cdr w)
                                                  (exists-weak-word-witness (cdr w)))
                      5)))
                 w))
           (equal
            (nth
             (+
              (len
               (generate-words-main
                (+ (exists-weak-word-1-witness (cdr w)
                                               (exists-weak-word-witness (cdr w)))
                   4))) 1)
             (generate-words-main
              (+ (exists-weak-word-1-witness (cdr w)
                                             (exists-weak-word-witness (cdr w)))
                 5)))
            (nth
             (+
              (len
               (generate-words-main
                (+ (exists-weak-word-1-witness (cdr w)
                                               (exists-weak-word-witness (cdr w)))
                   4))) 1)
             (generate-words-main
              (+ (len
                  (generate-words-main
                   (+ (exists-weak-word-1-witness (cdr w)
                                                  (exists-weak-word-witness (cdr w)))
                      4))) 2)))))
  :hints (("goal"
           :use ((:instance generate-words-main-lemma10 (m (+ (exists-weak-word-1-witness (cdr w)
                                                                                          (exists-weak-word-witness
                                                                                           (cdr w))) 5))
                            (n (+ (len (generate-words-main
                                        (+ (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w)))
                                           4))) 1))
                            (x (+ (len (generate-words-main
                                        (+ (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w)))
                                           4))) 2)))
                 (:instance generate-words-main-lemma7-1
                            (m (+ (exists-weak-word-1-witness (cdr w)
                                                              (exists-weak-word-witness (cdr w)))
                                  4))))
           :do-not-induct t
           )))

(defthmd any-weak-word-exist-sub-1/2.2-1-hints
  (implies (and (weak-wordp (cdr w))
                (not (atom w))
                (equal (car w) (wa-inv))
                (exists-weak-word (cdr w))
                (weak-wordp w)
                (> (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 5))
           (and (posp (exists-weak-word-witness (cdr w)))
                (natp (exists-weak-word-1-witness (cdr w)
                                                  (exists-weak-word-witness (cdr w))))
                (natp (+ (exists-weak-word-1-witness (cdr w)
                                                     (exists-weak-word-witness (cdr w)))
                         4))
                (natp (exists-weak-word-witness (cdr w)))
                (posp (+ (exists-weak-word-1-witness (cdr w)
                                          (exists-weak-word-witness (cdr w)))
                         5))
                (natp
                 (+
                  (len
                   (generate-words-main
                    (+ (exists-weak-word-1-witness (cdr w)
                                                   (exists-weak-word-witness (cdr w)))
                       4))) 1))
                (posp
                 (+
                  (len
                   (generate-words-main
                    (+ (exists-weak-word-1-witness (cdr w)
                                                   (exists-weak-word-witness (cdr w)))
                       4)))
                  2))
                (equal
                 (nth
                  (+
                   (len
                    (generate-words-main
                     (+ (exists-weak-word-1-witness (cdr w)
                                                    (exists-weak-word-witness (cdr w)))
                        4)))
                   1)
                  (generate-words-main
                   (+ (exists-weak-word-1-witness (cdr w)
                                                  (exists-weak-word-witness (cdr w)))
                      5)))
                 w)))
  :hints (("goal"
           :use ((:instance exists-weak-word-lemma1
                            (n (+ (exists-weak-word-1-witness (cdr w)
                                                              (exists-weak-word-witness (cdr w)))
                                  4)))
                 (:instance generate-words-main-lemma7 (x (exists-weak-word-witness (cdr w)))
                            (m (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w)))))
                 (:instance generate-words-main-lemma7
                            (x (+ (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 4))
                            (m (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w)))))
                 (:instance any-weak-word-exist-sub-1/2.2-1-hints-1
                            (lst (generate-words-main
                                  (+ (exists-weak-word-1-witness (cdr w)
                                                                 (exists-weak-word-witness (cdr w)))
                                     5)))
                            (lst1 (generate-words-main
                                   (+ (exists-weak-word-1-witness (cdr w)
                                                                  (exists-weak-word-witness (cdr w)))
                                      4)))
                            (lst2 (list (append (list (wa)) (nth
                                                             (exists-weak-word-1-witness (cdr w)
                                                                                         (exists-weak-word-witness
                                                                                          (cdr w)))
                                                             (generate-words-main (+ (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 4))))
                                        (append (list (wa-inv)) (nth
                                                             (exists-weak-word-1-witness (cdr w)
                                                                                         (exists-weak-word-witness
                                                                                          (cdr w)))
                                                             (generate-words-main (+ (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 4))))
                                        (append (list (wb)) (nth
                                                             (exists-weak-word-1-witness (cdr w)
                                                                                         (exists-weak-word-witness
                                                                                          (cdr w)))
                                                             (generate-words-main (+ (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 4))))
                                        (append (list (wb-inv)) (nth
                                                             (exists-weak-word-1-witness (cdr w)
                                                                                         (exists-weak-word-witness
                                                                                          (cdr w)))
                                                             (generate-words-main
  (+ (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w)))
     4))))))))
           :do-not-induct t
           )))

(defthmd any-weak-word-exist-sub-1/2.2-1
  (implies (and (weak-wordp (cdr w))
                (not (atom w))
                (equal (car w) (wa-inv))
                (exists-weak-word (cdr w))
                (weak-wordp w)
                (> (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 5))
           (exists-weak-word w))
  :hints (("goal"
           :do-not-induct t
           :use ((:instance exists-weak-word-implies (w (cdr w)))
                 (:instance exists-weak-word-lemma1
                            (n (+ (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 4)))
                 (:instance generate-words-main-lemma7 (x (exists-weak-word-witness (cdr w)))
                            (m (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w)))))
                 (:instance generate-words-main-lemma7
                            (x (+ (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 4))
                            (m (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w)))))
                 (:instance exists-weak-word-suff
                            (n (+ (len (generate-words-main
                                        (+ (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w)))
                                           4))) 2))
                            (w w))
                 (:instance exists-weak-word-1-suff
                            (n (+ (len (generate-words-main
                                        (+ (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w)))
                                           4))) 2))
                            (w w)
                            (m (+ (len (generate-words-main
                                        (+ (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w)))
                                           4))) 1)))
                 (:instance any-weak-word-exist-sub-1/2.2-1-hints-2)
                 (:instance any-weak-word-exist-sub-1/2.2-1-hints))
           :in-theory nil
           )))

(defthmd any-weak-word-exist-sub-1/2.2
  (implies (and (weak-wordp (cdr w))
                (not (atom w))
                (equal (car w) (wa-inv))
                (exists-weak-word (cdr w))
                (weak-wordp w))
           (exists-weak-word w))
  :hints (("goal"
           :cases ((= (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 0)
                   (= (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 1)
                   (= (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 2)
                   (= (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 3)
                   (= (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 4)
                   (= (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 5)
                   (> (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 5))
           :use ((:instance exists-weak-word-implies (w (cdr w))))
           :do-not-induct t
           )
          ("subgoal 7"
           :use ((:instance any-weak-word-exist-sub-1/2.2-7))
           :in-theory nil
           )
          ("subgoal 6"
           :use ((:instance any-weak-word-exist-sub-1/2.2-6))
           :in-theory nil
           )
          ("subgoal 5"
           :use ((:instance any-weak-word-exist-sub-1/2.2-5))
           :in-theory nil
           )
          ("subgoal 4"
           :use ((:instance any-weak-word-exist-sub-1/2.2-4))
           :in-theory nil
           )
          ("subgoal 3"
           :use ((:instance any-weak-word-exist-sub-1/2.2-3))
           :in-theory nil
           )
          ("subgoal 2"
           :use ((:instance any-weak-word-exist-sub-1/2.2-2))
           :in-theory nil
           )
          ("subgoal 1"
           :use ((:instance any-weak-word-exist-sub-1/2.2-1))
           )
          ))

(defthmd any-weak-word-exist-sub-1/2.1-7
  (implies (and (weak-wordp (cdr w))
                (not (atom w))
                (equal (car w) (wb-inv))
                (exists-weak-word (cdr w))
                (weak-wordp w)
                (= (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 0))
           (exists-weak-word w))

  :hints (("goal"
           :use ((:instance exists-weak-word-implies (w (cdr w)))
                 (:instance generate-words-main-lemma2
                            (eit (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))))
                            (x (exists-weak-word-witness (cdr w))))
                 (:instance exists-weak-word-suff (n 5) (w '(#\d)))
                 (:instance exists-weak-word-1-suff (m 4) (w '(#\d)) (n 5)))
           :do-not-induct t
           )))

(defthmd any-weak-word-exist-sub-1/2.1-6
  (implies (and (weak-wordp (cdr w))
                (not (atom w))
                (equal (car w) (wb-inv))
                (exists-weak-word (cdr w))
                (weak-wordp w)
                (= (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 1))
           (exists-weak-word w))

  :hints (("goal"
           :use ((:instance exists-weak-word-implies (w (cdr w)))
                 (:instance generate-words-main-lemma3
                            (eit (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))))
                            (x (exists-weak-word-witness (cdr w))))
                 (:instance exists-weak-word-suff (n 9) (w '(#\d #\a)))
                 (:instance exists-weak-word-1-suff (m 8) (w '(#\d #\a)) (n 9)))
           :do-not-induct t
           )))

(defthmd any-weak-word-exist-sub-1/2.1-5
  (implies (and (weak-wordp (cdr w))
                (not (atom w))
                (equal (car w) (wb-inv))
                (exists-weak-word (cdr w))
                (weak-wordp w)
                (= (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 2))
           (exists-weak-word w))

  :hints (("goal"
           :use ((:instance exists-weak-word-implies (w (cdr w)))
                 (:instance generate-words-main-lemma4
                            (eit (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))))
                            (x (exists-weak-word-witness (cdr w))))
                 (:instance exists-weak-word-suff (n 13) (w '(#\d #\b)))
                 (:instance exists-weak-word-1-suff (m 12) (w '(#\d #\b)) (n 13)))
           :do-not-induct t
           )))

(defthmd any-weak-word-exist-sub-1/2.1-4
  (implies (and (weak-wordp (cdr w))
                (not (atom w))
                (equal (car w) (wb-inv))
                (exists-weak-word (cdr w))
                (weak-wordp w)
                (= (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 3))
           (exists-weak-word w))

  :hints (("goal"
           :use ((:instance exists-weak-word-implies (w (cdr w)))
                 (:instance generate-words-main-lemma5
                            (eit (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))))
                            (x (exists-weak-word-witness (cdr w))))
                 (:instance exists-weak-word-suff (n 17) (w '(#\d #\c)))
                 (:instance exists-weak-word-1-suff (m 16) (w '(#\d #\c)) (n 17)))
           :do-not-induct t
           )))

(defthmd any-weak-word-exist-sub-1/2.1-3
  (implies (and (weak-wordp (cdr w))
                (not (atom w))
                (equal (car w) (wb-inv))
                (exists-weak-word (cdr w))
                (weak-wordp w)
                (= (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 4))
           (exists-weak-word w))

  :hints (("goal"
           :use ((:instance exists-weak-word-implies (w (cdr w)))
                 (:instance generate-words-main-lemma6
                            (eit (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))))
                            (x (exists-weak-word-witness (cdr w))))
                 (:instance exists-weak-word-suff (n 21) (w '(#\d #\d)))
                 (:instance exists-weak-word-1-suff (m 20) (w '(#\d #\d)) (n 21)))
           :do-not-induct t
           )))

(defthmd any-weak-word-exist-sub-1/2.1-2
  (implies (and (weak-wordp (cdr w))
                (not (atom w))
                (equal (car w) (wb-inv))
                (exists-weak-word (cdr w))
                (weak-wordp w)
                (= (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 5))
           (exists-weak-word w))

  :hints (("goal"
           :use ((:instance exists-weak-word-implies (w (cdr w)))
                 (:instance generate-words-main-lemma1
                            (eit (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))))
                            (x (exists-weak-word-witness (cdr w))))
                 (:instance exists-weak-word-suff (n 25) (w '(#\d #\a #\a)))
                 (:instance exists-weak-word-1-suff (m 24) (w '(#\d #\a #\a)) (n 25)))
           :do-not-induct t
           )))

(defthmd any-weak-word-exist-sub-1/2.1-1-hints-1
  (implies (equal lst (append lst1 lst2))
           (equal (nth (+ (len lst1) 3) lst)
                  (cadddr lst2))))

(defthmd any-weak-word-exist-sub-1/2.1-1-hints-2
  (implies (and (weak-wordp (cdr w))
                (not (atom w))
                (equal (car w) (wb-inv))
                (exists-weak-word (cdr w))
                (weak-wordp w)
                (> (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 5)
                (equal
                 (nth
                  (+
                  (len
                   (generate-words-main
                    (+ (exists-weak-word-1-witness (cdr w)
                                                   (exists-weak-word-witness (cdr w)))
                       4))) 3)
                  (generate-words-main
                   (+ (exists-weak-word-1-witness (cdr w)
                                                  (exists-weak-word-witness (cdr w)))
                      5)))
                 w))
           (equal
            (nth
             (+
              (len
               (generate-words-main
                (+ (exists-weak-word-1-witness (cdr w)
                                               (exists-weak-word-witness (cdr w)))
                   4))) 3)
             (generate-words-main
              (+ (exists-weak-word-1-witness (cdr w)
                                             (exists-weak-word-witness (cdr w)))
                 5)))
            (nth
             (+
              (len
               (generate-words-main
                (+ (exists-weak-word-1-witness (cdr w)
                                               (exists-weak-word-witness (cdr w)))
                   4))) 3)
             (generate-words-main
              (+ (len
                  (generate-words-main
                   (+ (exists-weak-word-1-witness (cdr w)
                                                  (exists-weak-word-witness (cdr w)))
                      4))) 4)))))
  :hints (("goal"
           :use ((:instance generate-words-main-lemma10 (m (+ (exists-weak-word-1-witness (cdr w)
                                                                                          (exists-weak-word-witness
                                                                                           (cdr w))) 5))
                            (n (+ (len (generate-words-main
                                        (+ (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w)))
                                           4))) 3))
                            (x (+ (len (generate-words-main
                                        (+ (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w)))
                                           4))) 4)))
                 (:instance generate-words-main-lemma7-1
                            (m (+ (exists-weak-word-1-witness (cdr w)
                                                              (exists-weak-word-witness (cdr w)))
                                  4))))
           :do-not-induct t
           )))

(defthmd any-weak-word-exist-sub-1/2.1-1-hints
  (implies (and (weak-wordp (cdr w))
                (not (atom w))
                (equal (car w) (wb-inv))
                (exists-weak-word (cdr w))
                (weak-wordp w)
                (> (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 5))
           (and (posp (exists-weak-word-witness (cdr w)))
                (natp (exists-weak-word-1-witness (cdr w)
                                                  (exists-weak-word-witness (cdr w))))
                (natp (+ (exists-weak-word-1-witness (cdr w)
                                                     (exists-weak-word-witness (cdr w)))
                         4))
                (natp (exists-weak-word-witness (cdr w)))
                (posp (+ (exists-weak-word-1-witness (cdr w)
                                          (exists-weak-word-witness (cdr w)))
                         5))
                (natp
                 (+
                  (len
                   (generate-words-main
                    (+ (exists-weak-word-1-witness (cdr w)
                                                   (exists-weak-word-witness (cdr w)))
                       4))) 3))
                (posp
                 (+
                  (len
                   (generate-words-main
                    (+ (exists-weak-word-1-witness (cdr w)
                                                   (exists-weak-word-witness (cdr w)))
                       4)))
                  4))
                (equal
                 (nth
                  (+
                   (len
                    (generate-words-main
                     (+ (exists-weak-word-1-witness (cdr w)
                                                    (exists-weak-word-witness (cdr w)))
                        4)))
                   3)
                  (generate-words-main
                   (+ (exists-weak-word-1-witness (cdr w)
                                                  (exists-weak-word-witness (cdr w)))
                      5)))
                 w)))
  :hints (("goal"
           :use ((:instance exists-weak-word-lemma1
                            (n (+ (exists-weak-word-1-witness (cdr w)
                                                              (exists-weak-word-witness (cdr w)))
                                  4)))
                 (:instance generate-words-main-lemma7 (x (exists-weak-word-witness (cdr w)))
                            (m (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w)))))
                 (:instance generate-words-main-lemma7
                            (x (+ (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 4))
                            (m (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w)))))
                 (:instance any-weak-word-exist-sub-1/2.1-1-hints-1
                            (lst (generate-words-main
                                  (+ (exists-weak-word-1-witness (cdr w)
                                                                 (exists-weak-word-witness (cdr w)))
                                     5)))
                            (lst1 (generate-words-main
                                   (+ (exists-weak-word-1-witness (cdr w)
                                                                  (exists-weak-word-witness (cdr w)))
                                      4)))
                            (lst2 (list (append (list (wa)) (nth
                                                             (exists-weak-word-1-witness (cdr w)
                                                                                         (exists-weak-word-witness
                                                                                          (cdr w)))
                                                             (generate-words-main (+ (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 4))))
                                        (append (list (wa-inv)) (nth
                                                             (exists-weak-word-1-witness (cdr w)
                                                                                         (exists-weak-word-witness
                                                                                          (cdr w)))
                                                             (generate-words-main (+ (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 4))))
                                        (append (list (wb)) (nth
                                                             (exists-weak-word-1-witness (cdr w)
                                                                                         (exists-weak-word-witness
                                                                                          (cdr w)))
                                                             (generate-words-main (+ (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 4))))
                                        (append (list (wb-inv)) (nth
                                                             (exists-weak-word-1-witness (cdr w)
                                                                                         (exists-weak-word-witness
                                                                                          (cdr w)))
                                                             (generate-words-main
  (+ (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w)))
     4))))))))
           :do-not-induct t
           )))

(defthmd any-weak-word-exist-sub-1/2.1-1
  (implies (and (weak-wordp (cdr w))
                (not (atom w))
                (equal (car w) (wb-inv))
                (exists-weak-word (cdr w))
                (weak-wordp w)
                (> (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 5))
           (exists-weak-word w))
  :hints (("goal"
           :do-not-induct t
           :use ((:instance exists-weak-word-implies (w (cdr w)))
                 (:instance exists-weak-word-lemma1
                            (n (+ (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 4)))
                 (:instance generate-words-main-lemma7 (x (exists-weak-word-witness (cdr w)))
                            (m (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w)))))
                 (:instance generate-words-main-lemma7
                            (x (+ (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 4))
                            (m (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w)))))
                 (:instance exists-weak-word-suff
                            (n (+ (len (generate-words-main
                                        (+ (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w)))
                                           4))) 4))
                            (w w))
                 (:instance exists-weak-word-1-suff
                            (n (+ (len (generate-words-main
                                        (+ (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w)))
                                           4))) 4))
                            (w w)
                            (m (+ (len (generate-words-main
                                        (+ (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w)))
                                           4))) 3)))
                 (:instance any-weak-word-exist-sub-1/2.1-1-hints-2)
                 (:instance any-weak-word-exist-sub-1/2.1-1-hints))
           :in-theory nil
           )))

(defthmd any-weak-word-exist-sub-1/2.1
  (implies (and (weak-wordp (cdr w))
                (not (atom w))
                (equal (car w) (wb-inv))
                (exists-weak-word (cdr w))
                (weak-wordp w))
           (exists-weak-word w))
  :hints (("goal"
           :cases ((= (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 0)
                   (= (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 1)
                   (= (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 2)
                   (= (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 3)
                   (= (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 4)
                   (= (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 5)
                   (> (exists-weak-word-1-witness (cdr w) (exists-weak-word-witness (cdr w))) 5))
           :use ((:instance exists-weak-word-implies (w (cdr w))))
           :do-not-induct t
           )
          ("subgoal 7"
           :use ((:instance any-weak-word-exist-sub-1/2.1-7))
           :in-theory nil
           )
          ("subgoal 6"
           :use ((:instance any-weak-word-exist-sub-1/2.1-6))
           :in-theory nil
           )
          ("subgoal 5"
           :use ((:instance any-weak-word-exist-sub-1/2.1-5))
           :in-theory nil
           )
          ("subgoal 4"
           :use ((:instance any-weak-word-exist-sub-1/2.1-4))
           :in-theory nil
           )
          ("subgoal 3"
           :use ((:instance any-weak-word-exist-sub-1/2.1-3))
           :in-theory nil
           )
          ("subgoal 2"
           :use ((:instance any-weak-word-exist-sub-1/2.1-2))
           :in-theory nil
           )
          ("subgoal 1"
           :use ((:instance any-weak-word-exist-sub-1/2.1-1))
           )
          ))

(defthmd any-weak-word-exists
  (implies (weak-wordp w)
           (exists-weak-word w))
  :hints (
          ("subgoal *1/2"
           :use ((:instance weak-word-cdr (x w)))
           :in-theory nil
           )
          ("subgoal *1/2.4"
           :use ((:instance any-weak-word-exist-sub-1/2.4))
           :in-theory nil
           )
          ("subgoal *1/2.3"
           :use ((:instance any-weak-word-exist-sub-1/2.3))
           :in-theory nil
           )
          ("subgoal *1/2.2"
           :use ((:instance any-weak-word-exist-sub-1/2.2))
           :in-theory nil
           )
          ("subgoal *1/2.1"
           :use ((:instance any-weak-word-exist-sub-1/2.1))
           :in-theory nil
           )

          ("subgoal *1/1"
           :use ((:instance exists-weak-word-suff (n 1) (w nil))
                 (:instance exists-weak-word-1-suff (m 0) (w nil) (n 1)))
           :do-not-induct t
           )
          ))
