
(include-book "banach-tarski-s2")

(defun cal-radius (p)
  (acl2-sqrt (+ (* (point-in-r3-x1 p) (point-in-r3-x1 p))
                (* (point-in-r3-y1 p) (point-in-r3-y1 p))
                (* (point-in-r3-z1 p) (point-in-r3-z1 p)))))

(defun point-p/r (p)
  `((:header :dimensions (3 1)
	     :maximum-length 15)
    ((0 . 0) . ,(/ (point-in-r3-x1 p) (cal-radius p)) )
    ((1 . 0) . ,(/ (point-in-r3-y1 p) (cal-radius p)) )
    ((2 . 0) . ,(/ (point-in-r3-z1 p) (cal-radius p)) )
    )
  )

(defthmd point-p/r=>1
  (and (equal (aref2 :fake-name (point-p/r p) 0 0) (/ (point-in-r3-x1 p) (cal-radius p)))
       (equal (aref2 :fake-name (point-p/r p) 1 0) (/ (point-in-r3-y1 p) (cal-radius p)))
       (equal (aref2 :fake-name (point-p/r p) 2 0) (/ (point-in-r3-z1 p) (cal-radius p))))
  :hints (("goal"
           :in-theory (e/d (aref2) (cal-radius))
           )))

(defthmd point-p/r=>2
  (and (equal (point-in-r3-x1 (point-p/r p)) (/ (point-in-r3-x1 p) (cal-radius p)))
       (equal (point-in-r3-y1 (point-p/r p)) (/ (point-in-r3-y1 p) (cal-radius p)))
       (equal (point-in-r3-z1 (point-p/r p)) (/ (point-in-r3-z1 p) (cal-radius p))))
  :hints (("goal"
           :in-theory (e/d (aref2) (cal-radius))
           )))

(defthmd pr3-point-p
  (implies (and (point-in-r3 p)
                (> (cal-radius p) 0)
                (realp (cal-radius p)))
           (point-in-r3 (point-p/r p)))
  :hints (("goal"
           :in-theory (e/d (array2p dimensions header aref2) (acl2-sqrt cal-radius))
           )))

(defun b3-0 (p)
  (and (point-in-r3 p)
       (> (cal-radius p) 0)
       (<= (cal-radius p) 1)))

(defun-sk b3-0-s2-1 (p)
  (exists p-s2
          (and (s2-def-p p-s2)
               (equal (point-in-r3-x1 p-s2) (/ (point-in-r3-x1 p) (cal-radius p)))
               (equal (point-in-r3-y1 p-s2) (/ (point-in-r3-y1 p) (cal-radius p)))
               (equal (point-in-r3-z1 p-s2) (/ (point-in-r3-z1 p) (cal-radius p))))))

(defun b3-0-s2 (p)
  (and (point-in-r3 p)
       (> (cal-radius p) 0)
       (<= (cal-radius p) 1)
       (b3-0-s2-1 p)))

(defthmd pr3=>r^2>=0
  (implies (point-in-r3 p)
           (>= (+ (* (point-in-r3-x1 p) (point-in-r3-x1 p))
                  (* (point-in-r3-y1 p) (point-in-r3-y1 p))
                  (* (point-in-r3-z1 p) (point-in-r3-z1 p)))
               0)))

(defthmd b3-0=>r^2>0
  (implies (b3-0 p)
           (and (realp (cal-radius p))
                (equal (* (cal-radius p) (cal-radius p))
                       (+ (* (point-in-r3-x1 p) (point-in-r3-x1 p))
                          (* (point-in-r3-y1 p) (point-in-r3-y1 p))
                          (* (point-in-r3-z1 p) (point-in-r3-z1 p))))
                (> (* (cal-radius p) (cal-radius p)) 0)))
  :hints (("goal"
           :use ((:instance y-=-sqrt
                            (x (+ (* (point-in-r3-x1 p) (point-in-r3-x1 p))
                                  (* (point-in-r3-y1 p) (point-in-r3-y1 p))
                                  (* (point-in-r3-z1 p) (point-in-r3-z1 p))))
                            (y (cal-radius p)))
                 (:instance pr3=>r^2>=0 (p p)))
           :in-theory (disable acl2-sqrt y-=-sqrt)
           )))

(encapsulate
  ()

  (local (include-book "arithmetic/top" :dir :system))

  (defthmd b3-0-iff-b3-0-equiv-1-1
    (implies (and (realp d)
                  (realp a)
                  (realp b)
                  (realp c)
                  (equal x (/ a d))
                  (equal y (/ b d))
                  (equal z (/ c d)))
             (equal (+ (* x x) (* y y) (* z z))
                    (/ (+ (* a a) (* b b) (* c c)) (* d d)))))

  (defthmd b3-0-iff-b3-0-equiv-1
    (implies (b3-0 p)
             (s2-def-p (point-p/r p)))
    :hints (("goal"
             :use ((:instance b3-0-s2-1-suff (p-s2 (point-p/r p)) (p p))
                   (:instance point-p/r=>1 (p p))
                   (:instance s2-def-p (point (point-p/r p)))
                   (:instance pr3-point-p (p p))
                   (:instance b3-0 (p p))
                   (:instance b3-0=>r^2>0 (p p))
                   (:instance b3-0-iff-b3-0-equiv-1-1
                              (d (cal-radius p))
                              (x (aref2 :fake-name (point-p/r p) 0 0))
                              (y (aref2 :fake-name (point-p/r p) 1 0))
                              (z (aref2 :fake-name (point-p/r p) 2 0))
                              (a (point-in-r3-x1 p))
                              (b (point-in-r3-y1 p))
                              (c (point-in-r3-z1 p)))

                   )
             :in-theory (e/d () (point-in-r3 point-in-r3-x1 point-in-r3-y1 point-in-r3-z1 point-p/r cal-radius s2-def-p b3-0-s2 b3-0-s2-1 (:rewrite b3-0-s2-1-suff) pr3-point-p))
             )))

  (defthmd b3-0-iff-b3-0-s2
    (iff (b3-0 p)
         (b3-0-s2 p))
    :hints (("goal"
             :use ((:instance b3-0-s2-1-suff (p-s2 (point-p/r p)) (p p))
                   (:instance point-p/r=>1 (p p))
                   (:instance point-p/r=>2 (p p))
                   (:instance s2-def-p (point (point-p/r p)))
                   (:instance pr3-point-p (p p))
                   (:instance b3-0 (p p))
                   (:instance b3-0=>r^2>0 (p p))
                   (:instance b3-0-iff-b3-0-equiv-1 (p p))
                   (:instance b3-0-s2 (p p))
                   )
             :in-theory (e/d () (point-in-r3 point-in-r3-x1 point-in-r3-y1 point-in-r3-z1 point-p/r cal-radius s2-def-p b3-0-s2 b3-0-s2-1 (:rewrite b3-0-s2-1-suff) pr3-point-p))
             )))
  )

(defun-sk b3-0-set-a1-1 (p)
  (exists p-s2
          (and (set-a1 p-s2)
               (equal (point-in-r3-x1 p-s2) (/ (point-in-r3-x1 p) (cal-radius p)))
               (equal (point-in-r3-y1 p-s2) (/ (point-in-r3-y1 p) (cal-radius p)))
               (equal (point-in-r3-z1 p-s2) (/ (point-in-r3-z1 p) (cal-radius p))))))

(defun b3-0-set-a1 (p)
  (and (point-in-r3 p)
       (> (cal-radius p) 0)
       (<= (cal-radius p) 1)
       (b3-0-set-a1-1 p)))

(defun-sk b3-0-set-a2-1 (p)
  (exists p-s2
          (and (set-a2 p-s2)
               (equal (point-in-r3-x1 p-s2) (/ (point-in-r3-x1 p) (cal-radius p)))
               (equal (point-in-r3-y1 p-s2) (/ (point-in-r3-y1 p) (cal-radius p)))
               (equal (point-in-r3-z1 p-s2) (/ (point-in-r3-z1 p) (cal-radius p))))))

(defun b3-0-set-a2 (p)
  (and (point-in-r3 p)
       (> (cal-radius p) 0)
       (<= (cal-radius p) 1)
       (b3-0-set-a2-1 p)))

(defun-sk b3-0-set-a3-1 (p)
  (exists p-s2
          (and (set-a3 p-s2)
               (equal (point-in-r3-x1 p-s2) (/ (point-in-r3-x1 p) (cal-radius p)))
               (equal (point-in-r3-y1 p-s2) (/ (point-in-r3-y1 p) (cal-radius p)))
               (equal (point-in-r3-z1 p-s2) (/ (point-in-r3-z1 p) (cal-radius p))))))

(defun b3-0-set-a3 (p)
  (and (point-in-r3 p)
       (> (cal-radius p) 0)
       (<= (cal-radius p) 1)
       (b3-0-set-a3-1 p)))

(defun-sk b3-0-set-a4-1 (p)
  (exists p-s2
          (and (set-a4 p-s2)
               (equal (point-in-r3-x1 p-s2) (/ (point-in-r3-x1 p) (cal-radius p)))
               (equal (point-in-r3-y1 p-s2) (/ (point-in-r3-y1 p) (cal-radius p)))
               (equal (point-in-r3-z1 p-s2) (/ (point-in-r3-z1 p) (cal-radius p))))))

(defun b3-0-set-a4 (p)
  (and (point-in-r3 p)
       (> (cal-radius p) 0)
       (<= (cal-radius p) 1)
       (b3-0-set-a4-1 p)))

(defun-sk b3-0-set-a5-1 (p)
  (exists p-s2
          (and (set-a5 p-s2)
               (equal (point-in-r3-x1 p-s2) (/ (point-in-r3-x1 p) (cal-radius p)))
               (equal (point-in-r3-y1 p-s2) (/ (point-in-r3-y1 p) (cal-radius p)))
               (equal (point-in-r3-z1 p-s2) (/ (point-in-r3-z1 p) (cal-radius p))))))

(defun b3-0-set-a5 (p)
  (and (point-in-r3 p)
       (> (cal-radius p) 0)
       (<= (cal-radius p) 1)
       (b3-0-set-a5-1 p)))

(defun-sk b3-0-set-a6-1 (p)
  (exists p-s2
          (and (set-a6 p-s2)
               (equal (point-in-r3-x1 p-s2) (/ (point-in-r3-x1 p) (cal-radius p)))
               (equal (point-in-r3-y1 p-s2) (/ (point-in-r3-y1 p) (cal-radius p)))
               (equal (point-in-r3-z1 p-s2) (/ (point-in-r3-z1 p) (cal-radius p))))))

(defun b3-0-set-a6 (p)
  (and (point-in-r3 p)
       (> (cal-radius p) 0)
       (<= (cal-radius p) 1)
       (b3-0-set-a6-1 p)))

(defun-sk b3-0-set-a7-1 (p)
  (exists p-s2
          (and (set-a7 p-s2)
               (equal (point-in-r3-x1 p-s2) (/ (point-in-r3-x1 p) (cal-radius p)))
               (equal (point-in-r3-y1 p-s2) (/ (point-in-r3-y1 p) (cal-radius p)))
               (equal (point-in-r3-z1 p-s2) (/ (point-in-r3-z1 p) (cal-radius p))))))

(defun b3-0-set-a7 (p)
  (and (point-in-r3 p)
       (> (cal-radius p) 0)
       (<= (cal-radius p) 1)
       (b3-0-set-a7-1 p)))

(defun-sk b3-0-set-a8-1 (p)
  (exists p-s2
          (and (set-a8 p-s2)
               (equal (point-in-r3-x1 p-s2) (/ (point-in-r3-x1 p) (cal-radius p)))
               (equal (point-in-r3-y1 p-s2) (/ (point-in-r3-y1 p) (cal-radius p)))
               (equal (point-in-r3-z1 p-s2) (/ (point-in-r3-z1 p) (cal-radius p))))))

(defun b3-0-set-a8 (p)
  (and (point-in-r3 p)
       (> (cal-radius p) 0)
       (<= (cal-radius p) 1)
       (b3-0-set-a8-1 p)))

(defun-sk b3-0-set-a9-1 (p)
  (exists p-s2
          (and (set-a9 p-s2)
               (equal (point-in-r3-x1 p-s2) (/ (point-in-r3-x1 p) (cal-radius p)))
               (equal (point-in-r3-y1 p-s2) (/ (point-in-r3-y1 p) (cal-radius p)))
               (equal (point-in-r3-z1 p-s2) (/ (point-in-r3-z1 p) (cal-radius p))))))

(defun b3-0-set-a9 (p)
  (and (point-in-r3 p)
       (> (cal-radius p) 0)
       (<= (cal-radius p) 1)
       (b3-0-set-a9-1 p)))

(defun-sk b3-0-set-a10-1 (p)
  (exists p-s2
          (and (set-a10 p-s2)
               (equal (point-in-r3-x1 p-s2) (/ (point-in-r3-x1 p) (cal-radius p)))
               (equal (point-in-r3-y1 p-s2) (/ (point-in-r3-y1 p) (cal-radius p)))
               (equal (point-in-r3-z1 p-s2) (/ (point-in-r3-z1 p) (cal-radius p))))))

(defun b3-0-set-a10 (p)
  (and (point-in-r3 p)
       (> (cal-radius p) 0)
       (<= (cal-radius p) 1)
       (b3-0-set-a10-1 p)))

(defun-sk b3-0-set-a11-1 (p)
  (exists p-s2
          (and (set-a11 p-s2)
               (equal (point-in-r3-x1 p-s2) (/ (point-in-r3-x1 p) (cal-radius p)))
               (equal (point-in-r3-y1 p-s2) (/ (point-in-r3-y1 p) (cal-radius p)))
               (equal (point-in-r3-z1 p-s2) (/ (point-in-r3-z1 p) (cal-radius p))))))

(defun b3-0-set-a11 (p)
  (and (point-in-r3 p)
       (> (cal-radius p) 0)
       (<= (cal-radius p) 1)
       (b3-0-set-a11-1 p)))

(defun-sk b3-0-set-a12-1 (p)
  (exists p-s2
          (and (set-a12 p-s2)
               (equal (point-in-r3-x1 p-s2) (/ (point-in-r3-x1 p) (cal-radius p)))
               (equal (point-in-r3-y1 p-s2) (/ (point-in-r3-y1 p) (cal-radius p)))
               (equal (point-in-r3-z1 p-s2) (/ (point-in-r3-z1 p) (cal-radius p))))))

(defun b3-0-set-a12 (p)
  (and (point-in-r3 p)
       (> (cal-radius p) 0)
       (<= (cal-radius p) 1)
       (b3-0-set-a12-1 p)))

(defun-sk b3-0-set-a13-1 (p)
  (exists p-s2
          (and (set-a13 p-s2)
               (equal (point-in-r3-x1 p-s2) (/ (point-in-r3-x1 p) (cal-radius p)))
               (equal (point-in-r3-y1 p-s2) (/ (point-in-r3-y1 p) (cal-radius p)))
               (equal (point-in-r3-z1 p-s2) (/ (point-in-r3-z1 p) (cal-radius p))))))

(defun b3-0-set-a13 (p)
  (and (point-in-r3 p)
       (> (cal-radius p) 0)
       (<= (cal-radius p) 1)
       (b3-0-set-a13-1 p)))

(defun-sk b3-0-set-a14-1 (p)
  (exists p-s2
          (and (set-a14 p-s2)
               (equal (point-in-r3-x1 p-s2) (/ (point-in-r3-x1 p) (cal-radius p)))
               (equal (point-in-r3-y1 p-s2) (/ (point-in-r3-y1 p) (cal-radius p)))
               (equal (point-in-r3-z1 p-s2) (/ (point-in-r3-z1 p) (cal-radius p))))))

(defun b3-0-set-a14 (p)
  (and (point-in-r3 p)
       (> (cal-radius p) 0)
       (<= (cal-radius p) 1)
       (b3-0-set-a14-1 p)))

(defthmd b3-0=>a1-to-a14
  (implies (b3-0-s2 p)
           (or (b3-0-set-a1 p)
               (b3-0-set-a2 p)
               (b3-0-set-a3 p)
               (b3-0-set-a4 p)
               (b3-0-set-a5 p)
               (b3-0-set-a6 p)
               (b3-0-set-a7 p)
               (b3-0-set-a8 p)
               (b3-0-set-a9 p)
               (b3-0-set-a10 p)
               (b3-0-set-a11 p)
               (b3-0-set-a12 p)
               (b3-0-set-a13 p)
               (b3-0-set-a14 p)))
  :hints (("Goal"
           :use ((:instance b3-0-s2 (p p))
                 (:instance b3-0-s2-1 (p p))
                 (:instance s2-equiv-1 (p (b3-0-s2-1-witness p)))
                 (:instance b3-0-set-a1 (p p))
                 (:instance b3-0-set-a1-1-suff (p p) (p-s2 (b3-0-s2-1-witness p)))
                 (:instance b3-0-set-a2 (p p))
                 (:instance b3-0-set-a2-1-suff (p p) (p-s2 (b3-0-s2-1-witness p)))
                 (:instance b3-0-set-a3 (p p))
                 (:instance b3-0-set-a3-1-suff (p p) (p-s2 (b3-0-s2-1-witness p)))
                 (:instance b3-0-set-a4 (p p))
                 (:instance b3-0-set-a4-1-suff (p p) (p-s2 (b3-0-s2-1-witness p)))
                 (:instance b3-0-set-a5 (p p))
                 (:instance b3-0-set-a5-1-suff (p p) (p-s2 (b3-0-s2-1-witness p)))
                 (:instance b3-0-set-a6 (p p))
                 (:instance b3-0-set-a6-1-suff (p p) (p-s2 (b3-0-s2-1-witness p)))
                 (:instance b3-0-set-a7 (p p))
                 (:instance b3-0-set-a7-1-suff (p p) (p-s2 (b3-0-s2-1-witness p)))
                 (:instance b3-0-set-a8 (p p))
                 (:instance b3-0-set-a8-1-suff (p p) (p-s2 (b3-0-s2-1-witness p)))
                 (:instance b3-0-set-a9 (p p))
                 (:instance b3-0-set-a9-1-suff (p p) (p-s2 (b3-0-s2-1-witness p)))
                 (:instance b3-0-set-a10 (p p))
                 (:instance b3-0-set-a10-1-suff (p p) (p-s2 (b3-0-s2-1-witness p)))
                 (:instance b3-0-set-a11 (p p))
                 (:instance b3-0-set-a11-1-suff (p p) (p-s2 (b3-0-s2-1-witness p)))
                 (:instance b3-0-set-a12 (p p))
                 (:instance b3-0-set-a12-1-suff (p p) (p-s2 (b3-0-s2-1-witness p)))
                 (:instance b3-0-set-a13 (p p))
                 (:instance b3-0-set-a13-1-suff (p p) (p-s2 (b3-0-s2-1-witness p)))
                 (:instance b3-0-set-a14 (p p))
                 (:instance b3-0-set-a14-1-suff (p p) (p-s2 (b3-0-s2-1-witness p)))
                 )
           :in-theory nil
           )))

(defthmd a1-to-a14=>b3-0
  (implies (or (b3-0-set-a1 p)
               (b3-0-set-a2 p)
               (b3-0-set-a3 p)
               (b3-0-set-a4 p)
               (b3-0-set-a5 p)
               (b3-0-set-a6 p)
               (b3-0-set-a7 p)
               (b3-0-set-a8 p)
               (b3-0-set-a9 p)
               (b3-0-set-a10 p)
               (b3-0-set-a11 p)
               (b3-0-set-a12 p)
               (b3-0-set-a13 p)
               (b3-0-set-a14 p))
           (b3-0 p))
  :hints (("Goal"
           :in-theory (disable b3-0-set-a1-1 b3-0-set-a2-1 b3-0-set-a3-1 b3-0-set-a4-1 b3-0-set-a5-1 b3-0-set-a6-1 b3-0-set-a7-1 b3-0-set-a8-1 b3-0-set-a9-1 b3-0-set-a10-1 b3-0-set-a11-1 b3-0-set-a12-1 b3-0-set-a13-1 b3-0-set-a14-1)
           )))

(defthmd b3-0-iff-a1-to-a14
  (iff (b3-0-s2 p)
       (or (b3-0-set-a1 p)
           (b3-0-set-a2 p)
           (b3-0-set-a3 p)
           (b3-0-set-a4 p)
           (b3-0-set-a5 p)
           (b3-0-set-a6 p)
           (b3-0-set-a7 p)
           (b3-0-set-a8 p)
           (b3-0-set-a9 p)
           (b3-0-set-a10 p)
           (b3-0-set-a11 p)
           (b3-0-set-a12 p)
           (b3-0-set-a13 p)
           (b3-0-set-a14 p)))
  :hints (("Goal"
           :use ((:instance b3-0-iff-b3-0-s2 (p p))
                 (:instance b3-0=>a1-to-a14 (p p))
                 (:instance a1-to-a14=>b3-0 (p p)))
           :in-theory nil
           )))

;; proof that, b3-0 sets are disjoint.
;; (skip-proofs
;;  (defthmd a1=>not-a2
;;    (implies (set-a1 p)
;;             (not (set-a2 p)))))

;; (defthmd n-p1=p2=>diff-n-p2
;;   (implies (and (m-= p1 p2)
;;                 (point-in-r3 p1)
;;                 (point-in-r3 p2)
;;                 (diff-n-s2-d-p p1))
;;            (diff-n-s2-d-p p2))
;;   :hints (("Goal"
;;            :use ((:instance diff-n-s2-d-p (p p1))
;;                  (:instance diff-n-s2-d-p (p p2))
;;                  (:instance diff-n-s2-d-p-q (p p1))
;;                  (:instance diff-n-s2-d-p-q-1 (cp1 (CHOICE-SET-S2-D-P (DIFF-N-S2-D-P-Q-WITNESS P1)))
;;                             (p p1))
;;                  (:instance diff-n-s2-d-p-q-1-suff (w nil) (cp1 (CHOICE-SET-S2-D-P (DIFF-N-S2-D-P-Q-WITNESS P1)))
;;                             (p p2))
;;                  (:instance diff-n-s2-d-p-q-suff (p1 (DIFF-N-S2-D-P-Q-WITNESS P1)) (p p2))
;;                  )
;;            :in-theory nil
;;            )))


;; (defthmd p1=p2=>set-a1-p2
;;   (implies (and (point-in-r3 p1)
;;                 (point-in-r3 p2)
;;                 (set-a1 p1)
;;                 (m-= p1 p2))
;;            (set-a1 p2))
;;   :hints (("Goal"
;;            :use ((:instance set-a1 (p p1))
;;                  (:instance m0 (p p1))
;;                  (:instance s2-not-e (point p1))
;;                  (:instance p1=p2-n-e-p1=>e-p2 (p2 p1) (p1 p2))
;;                  (:instance set-a1 (p p2))
;;                  (:instance m0 (p p2))
;;                  (:instance s2-d-p-equivalence-1 (p p1))
;;                  (:instance s2-d-p (point p1))
;;                  (:instance s2-d-p (point p2))
;;                  (:instance s2-def-p-p=>p1 (p p1) (p1 p2))
;;                  (:instance d-p-p=>d-p-p1 (p p2) (p1 p1))
;;                  (:instance s2-d-p-equivalence-1 (p p2))
;;                  (:instance n-p1=p2=>diff-n-p2 (p1 p1) (p2 p2))
;;                  (:instance s2-not-e (point p2))
;;                  )
;;            :in-theory nil
;;            )))

;; (defthmd disjoint-lemma-1
;;   (implies (and (point-in-r3 p1)
;;                 (point-in-r3 p2)
;;                 (EQUAL (POINT-IN-R3-X1 p2)
;;                        (POINT-IN-R3-X1 p1))
;;                 (EQUAL (POINT-IN-R3-Y1 p2)
;;                        (POINT-IN-R3-Y1 p1))
;;                 (EQUAL (POINT-IN-R3-Z1 p2)
;;                        (POINT-IN-R3-Z1 p1)))
;;            (m-= p1 p2))
;;   :hints (("Goal"
;;            :in-theory (enable m-=)
;;            )))

;; (defthmd disjoint-lemma
;;   (implies (b3-0-set-a1 p)
;;            (not (b3-0-set-a2 p)))
;;   :hints (("Goal"
;;            :use ((:instance b3-0-set-a1 (p p))
;;                  (:instance b3-0-set-a1-1 (p p))
;;                  (:instance b3-0-set-a2 (p p))
;;                  (:instance b3-0-set-a2-1 (p p))
;;                  (:instance set-a1 (p (B3-0-SET-A1-1-WITNESS P)))
;;                  (:instance m0 (p (B3-0-SET-A1-1-WITNESS P)))
;;                  (:instance s2-d-p-equivalence-1 (p (B3-0-SET-A1-1-WITNESS P)))
;;                  (:instance s2-d-p (point (B3-0-SET-A1-1-WITNESS P)))
;;                  (:instance s2-def-p (point (B3-0-SET-A1-1-WITNESS P)))
;;                  (:instance set-a2 (p (B3-0-SET-A2-1-WITNESS P)))
;;                  (:instance r-1*m1 (p (B3-0-SET-A2-1-WITNESS P)))
;;                  (:instance p1=p2=>set-a1-p2 (p1 (B3-0-SET-A1-1-WITNESS P))
;;                             (p2 (B3-0-SET-A2-1-WITNESS P)))
;;                  (:instance disjoint-lemma-1 (p1 (B3-0-SET-A1-1-WITNESS P))
;;                             (p2 (B3-0-SET-A2-1-WITNESS P)))
;;                  (:instance a1=>not-a2 (p (B3-0-SET-A2-1-WITNESS P)))
;;                  )
;;            :in-theory nil
;;            )))
