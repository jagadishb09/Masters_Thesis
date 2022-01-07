
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
           (and (>= (+ (* (point-in-r3-x1 p) (point-in-r3-x1 p))
                       (* (point-in-r3-y1 p) (point-in-r3-y1 p))
                       (* (point-in-r3-z1 p) (point-in-r3-z1 p)))
                    0)
                (realp (cal-radius p))
                (realp (/ (cal-radius p)))
                (>= (cal-radius p) 0))))

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
  :hints (("goal"
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
  :hints (("goal"
           :in-theory (disable b3-0-set-a1-1 b3-0-set-a2-1 b3-0-set-a3-1 b3-0-set-a4-1 b3-0-set-a5-1 b3-0-set-a6-1 b3-0-set-a7-1 b3-0-set-a8-1 b3-0-set-a9-1 b3-0-set-a10-1 b3-0-set-a11-1 b3-0-set-a12-1 b3-0-set-a13-1 b3-0-set-a14-1)
           )))

(defthmd b3-0-iff-a1-to-a14
  (iff (or (b3-0-s2 p)
           (b3-0 p))
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
  :hints (("goal"
           :use ((:instance b3-0-iff-b3-0-s2 (p p))
                 (:instance b3-0=>a1-to-a14 (p p))
                 (:instance a1-to-a14=>b3-0 (p p)))
           :in-theory nil
           )))

;; proof that, b3-0 sets are disjoint.
;;
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
;;   :hints (("goal"
;;            :use ((:instance diff-n-s2-d-p (p p1))
;;                  (:instance diff-n-s2-d-p (p p2))
;;                  (:instance diff-n-s2-d-p-q (p p1))
;;                  (:instance diff-n-s2-d-p-q-1 (cp1 (choice-set-s2-d-p (diff-n-s2-d-p-q-witness p1)))
;;                             (p p1))
;;                  (:instance diff-n-s2-d-p-q-1-suff (w nil) (cp1 (choice-set-s2-d-p (diff-n-s2-d-p-q-witness p1)))
;;                             (p p2))
;;                  (:instance diff-n-s2-d-p-q-suff (p1 (diff-n-s2-d-p-q-witness p1)) (p p2))
;;                  )
;;            :in-theory nil
;;            )))


;; (defthmd p1=p2=>set-a1-p2
;;   (implies (and (point-in-r3 p1)
;;                 (point-in-r3 p2)
;;                 (set-a1 p1)
;;                 (m-= p1 p2))
;;            (set-a1 p2))
;;   :hints (("goal"
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
;;                 (equal (point-in-r3-x1 p2)
;;                        (point-in-r3-x1 p1))
;;                 (equal (point-in-r3-y1 p2)
;;                        (point-in-r3-y1 p1))
;;                 (equal (point-in-r3-z1 p2)
;;                        (point-in-r3-z1 p1)))
;;            (m-= p1 p2))
;;   :hints (("goal"
;;            :in-theory (enable m-=)
;;            )))

;; (defthmd disjoint-lemma
;;   (implies (b3-0-set-a1 p)
;;            (not (b3-0-set-a2 p)))
;;   :hints (("goal"
;;            :use ((:instance b3-0-set-a1 (p p))
;;                  (:instance b3-0-set-a1-1 (p p))
;;                  (:instance b3-0-set-a2 (p p))
;;                  (:instance b3-0-set-a2-1 (p p))
;;                  (:instance set-a1 (p (b3-0-set-a1-1-witness p)))
;;                  (:instance m0 (p (b3-0-set-a1-1-witness p)))
;;                  (:instance s2-d-p-equivalence-1 (p (b3-0-set-a1-1-witness p)))
;;                  (:instance s2-d-p (point (b3-0-set-a1-1-witness p)))
;;                  (:instance s2-def-p (point (b3-0-set-a1-1-witness p)))
;;                  (:instance set-a2 (p (b3-0-set-a2-1-witness p)))
;;                  (:instance r-1*m1 (p (b3-0-set-a2-1-witness p)))
;;                  (:instance p1=p2=>set-a1-p2 (p1 (b3-0-set-a1-1-witness p))
;;                             (p2 (b3-0-set-a2-1-witness p)))
;;                  (:instance disjoint-lemma-1 (p1 (b3-0-set-a1-1-witness p))
;;                             (p2 (b3-0-set-a2-1-witness p)))
;;                  (:instance a1=>not-a2 (p (b3-0-set-a2-1-witness p)))
;;                  )
;;            :in-theory nil
;;            )))

;; (defun-sk set-a-inv-a3-1 (point)
;;   (exists p
;;           (and (set-a3 p)
;;                (m-= (m-* (a-inv-rotation (acl2-sqrt 2)) p)
;;                     point))))

;; (defun set-a-inv-a3 (p)
;;   (and (point-in-r3 p)
;;        (set-a-inv-a3-1 p)))

(defthmd m1=m2/a=>m1=s-*/a-m2
  (implies (and (point-in-r3 p1)
                (point-in-r3 p2)
                (equal (point-in-r3-x1 p1)
                       (* a (point-in-r3-x1 p2)))
                (equal (point-in-r3-y1 p1)
                       (* a (point-in-r3-y1 p2)))
                (equal (point-in-r3-z1 p1)
                       (* a (point-in-r3-z1 p2))))
           (m-= p1 (s-* a p2)))
  :hints (("goal"
           :use ((:instance aref2-s-* (m p2) (a a))
                 (:instance dimensions-s-* (m p2) (a a)))
           :in-theory (e/d (m-=) (s-*))
           )))

(defthmd m-=m1m2=>r-m1=r-m2-1
  (implies (and (point-in-r3 p1)
                (point-in-r3 p2)
                (m-= p1 p2))
           (and (equal (aref2 :fake-name p1 0 0) (aref2 :fake-name p2 0 0))
                (equal (aref2 :fake-name p1 1 0) (aref2 :fake-name p2 1 0))
                (equal (aref2 :fake-name p1 2 0) (aref2 :fake-name p2 2 0))))
  :hints (("goal"
           :in-theory (enable m-=)
           )))

(defthmd m-=m1m2=>r-m1=r-m2-2
  (implies (and (point-in-r3 p1)
                (point-in-r3 p2)
                (r3-rotationp rot)
                (m-= (m-* rot p1) p2))
           (equal (+ (* (aref2 :fake-name p1 0 0) (aref2 :fake-name p1 0 0))
                     (* (aref2 :fake-name p1 1 0) (aref2 :fake-name p1 1 0))
                     (* (aref2 :fake-name p1 2 0) (aref2 :fake-name p1 2 0)))
                  (+ (* (aref2 :fake-name p2 0 0) (aref2 :fake-name p2 0 0))
                     (* (aref2 :fake-name p2 1 0) (aref2 :fake-name p2 1 0))
                     (* (aref2 :fake-name p2 2 0) (aref2 :fake-name p2 2 0)))))
  :hints (("goal"
           :use ((:instance rotation*point-on-s2 (p1 p1) (p2 (m-* rot p1)))
                 (:instance set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-1-1
                            (rot rot)
                            (p1 p1))
                 (:instance r3-rotationp (m rot))
                 (:instance m-=m1m2=>r-m1=r-m2-1 (p1 (m-* rot p1)) (p2 p2))
                 )
           :in-theory nil
           )))

(defthmd m-=m-*rot-p1=p2=>r-p1=r-p2
  (implies (and (point-in-r3 p1)
                (point-in-r3 p2)
                (r3-rotationp rot)
                (m-= (m-* rot p1) p2))
           (equal (cal-radius p1)
                  (cal-radius p2)))
  :hints (("goal"
           :use ((:instance m-=m1m2=>r-m1=r-m2-2 (p1 p1) (p2 p2) (rot rot))
                 )
           :in-theory (disable m-= m-* point-in-r3 r3-rotationp)
           )))

(defthmd pr3-p=>pr3-a*p
  (implies (and (point-in-r3 p)
                (realp a))
           (point-in-r3 (s-* a p))))

(defthmd xyz-p1=xyz-p2
  (implies (and (r3-matrixp rot)
                (point-in-r3 p1)
                (point-in-r3 p2)
                (point-in-r3 p3)
                (realp a)
                (m-= (m-* rot p2) p1)
                (m-= p3 (s-* a p2)))
           (and (equal (point-in-r3-x1 (m-* rot p3)) (* a (point-in-r3-x1 p1)))
                (equal (point-in-r3-y1 (m-* rot p3)) (* a (point-in-r3-y1 p1)))
                (equal (point-in-r3-z1 (m-* rot p3)) (* a (point-in-r3-z1 p1)))))
  :hints (("goal"
           :use ((:instance m-=-implies-equal-m-*-2
                            (m2 p3)
                            (m1 rot)
                            (m2-equiv (s-* a p2)))
                 (:instance m-*-s-*-right (m1 rot) (a a) (m2 p2) (name :fake-name))
                 (:instance aref2-s-* (a a) (m (m-* rot p2)))
                 (:instance r3-matrixp (m rot))
                 (:instance point-in-r3 (x p2))
                 (:instance m-=m1m2=>r-m1=r-m2-1 (p1 (m-* rot p3)) (p2 (s-* a p1)))
                 (:instance set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-1-1
                            (p1 p3)
                            (rot rot))
                 (:instance pr3-p=>pr3-a*p (a a) (p p1))
                 )
           :in-theory (e/d () (m-= m-* aref2 header dimensions array2p alist2p r3-matrixp point-in-r3))
           )))

(defun-sk b3-0-a-inv-b3-0-set-a3-1 (p)
  (exists p-s2
          (and (b3-0-set-a3 p-s2)
               (m-= (m-* (a-inv-rotation (acl2-sqrt 2)) p-s2)
                    p))))

(defun b3-0-a-inv-b3-0-set-a3 (p)
  (and (point-in-r3 p)
       (b3-0-a-inv-b3-0-set-a3-1 p)))


(defun-sk b3-0-set-a-inv-a3-1 (p)
  (exists p-s2
          (and (set-a-inv-a3 p-s2)
               (equal (point-in-r3-x1 p-s2) (/ (point-in-r3-x1 p) (cal-radius p)))
               (equal (point-in-r3-y1 p-s2) (/ (point-in-r3-y1 p) (cal-radius p)))
               (equal (point-in-r3-z1 p-s2) (/ (point-in-r3-z1 p) (cal-radius p))))))

(defun b3-0-set-a-inv-a3 (p)
  (and (point-in-r3 p)
       (> (cal-radius p) 0)
       (<= (cal-radius p) 1)
       (b3-0-set-a-inv-a3-1 p)))

(defthmd b3-0-a-1-a3-iff-a-1-b3-0-a3-1
  (implies (and (equal (point-in-r3-x1
                        (b3-0-set-a3-1-witness (b3-0-a-inv-b3-0-set-a3-1-witness p)))
                       (* (point-in-r3-x1 (b3-0-a-inv-b3-0-set-a3-1-witness p))
                          (/ (cal-radius p))))
                (equal (point-in-r3-y1
                        (b3-0-set-a3-1-witness (b3-0-a-inv-b3-0-set-a3-1-witness p)))
                       (* (point-in-r3-y1 (b3-0-a-inv-b3-0-set-a3-1-witness p))
                          (/ (cal-radius p))))
                (equal (point-in-r3-z1
                        (b3-0-set-a3-1-witness (b3-0-a-inv-b3-0-set-a3-1-witness p)))
                       (* (point-in-r3-z1 (b3-0-a-inv-b3-0-set-a3-1-witness p))
                          (/ (cal-radius p)))))
           (and (equal (point-in-r3-x1
                        (b3-0-set-a3-1-witness (b3-0-a-inv-b3-0-set-a3-1-witness p)))
                       (* (/ (cal-radius p))
                          (point-in-r3-x1 (b3-0-a-inv-b3-0-set-a3-1-witness p))))
                (equal (point-in-r3-z1
                        (b3-0-set-a3-1-witness (b3-0-a-inv-b3-0-set-a3-1-witness p)))
                       (* (/ (cal-radius p))
                          (point-in-r3-z1 (b3-0-a-inv-b3-0-set-a3-1-witness p))))
                (equal (point-in-r3-y1
                        (b3-0-set-a3-1-witness (b3-0-a-inv-b3-0-set-a3-1-witness p)))
                       (* (/ (cal-radius p))
                          (point-in-r3-y1 (b3-0-a-inv-b3-0-set-a3-1-witness p)))))))

(defthmd b3-0-a-1-a3-iff-a-1-b3-0-a3-2
  (equal (* x y)
         (* y x)))


(defthmd b3-0-a-1-b3-0-a3=>b3-0-a-1-a3
  (implies (b3-0-a-inv-b3-0-set-a3 p)
           (b3-0-set-a-inv-a3 p))
  :hints (("goal"
           :use ((:instance b3-0-a-inv-b3-0-set-a3 (p p))
                 (:instance b3-0-a-inv-b3-0-set-a3-1 (p p))
                 (:instance b3-0-set-a3 (p (b3-0-a-inv-b3-0-set-a3-1-witness p)))
                 (:instance b3-0-set-a3-1 (p (b3-0-a-inv-b3-0-set-a3-1-witness p)))
                 (:instance b3-0-set-a-inv-a3 (p p))
                 (:instance m-=m-*rot-p1=p2=>r-p1=r-p2 (p1 (b3-0-a-inv-b3-0-set-a3-1-witness p))
                            (p2 p)
                            (rot (a-inv-rotation (acl2-sqrt 2))))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance b3-0-set-a-inv-a3-1-suff
                            (p-s2 (m-* (a-inv-rotation (acl2-sqrt 2))
                                       (b3-0-set-a3-1-witness (b3-0-a-inv-b3-0-set-a3-1-witness p))))
                            (p p))
                 (:instance set-a-inv-a3 (p (m-* (a-inv-rotation (acl2-sqrt 2))
                                                 (b3-0-set-a3-1-witness (b3-0-a-inv-b3-0-set-a3-1-witness p)))))
                 (:instance set-a3 (p (b3-0-set-a3-1-witness (b3-0-a-inv-b3-0-set-a3-1-witness p))))
                 (:instance wa-00 (p (b3-0-set-a3-1-witness (b3-0-a-inv-b3-0-set-a3-1-witness p))))
                 (:instance wa-0 (p (b3-0-set-a3-1-witness (b3-0-a-inv-b3-0-set-a3-1-witness p))))
                 (:instance s2-not-e (point (b3-0-set-a3-1-witness (b3-0-a-inv-b3-0-set-a3-1-witness p))))
                 (:instance s2-def-p (point (b3-0-set-a3-1-witness (b3-0-a-inv-b3-0-set-a3-1-witness p))))
                 (:instance set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-1-1
                            (p1 (b3-0-set-a3-1-witness (b3-0-a-inv-b3-0-set-a3-1-witness p)))
                            (rot (a-inv-rotation (acl2-sqrt 2))))
                 (:instance r3-rotationp (m (a-inv-rotation (acl2-sqrt 2))))
                 (:instance set-a-inv-a3-1-suff
                            (p (b3-0-set-a3-1-witness (b3-0-a-inv-b3-0-set-a3-1-witness p)))
                            (point (m-* (a-inv-rotation (acl2-sqrt 2))
                                        (b3-0-set-a3-1-witness (b3-0-a-inv-b3-0-set-a3-1-witness p)))))
                 (:instance xyz-p1=xyz-p2
                            (p1 p)
                            (p2 (b3-0-a-inv-b3-0-set-a3-1-witness p))
                            (p3 (b3-0-set-a3-1-witness (b3-0-a-inv-b3-0-set-a3-1-witness p)))
                            (rot (a-inv-rotation (acl2-sqrt 2)))
                            (a (/ (cal-radius p))))
                 (:instance pr3=>r^2>=0 (p p))
                 (:instance m1=m2/a=>m1=s-*/a-m2
                            (p1 (b3-0-set-a3-1-witness (b3-0-a-inv-b3-0-set-a3-1-witness p)))
                            (p2 (b3-0-a-inv-b3-0-set-a3-1-witness p))
                            (a (/ (cal-radius p))))
                 (:instance b3-0-a-1-a3-iff-a-1-b3-0-a3-1)
                 (:instance b3-0-a-1-a3-iff-a-1-b3-0-a3-2
                            (x (/ (cal-radius p)))
                            (y (point-in-r3-x1 p)))
                 (:instance b3-0-a-1-a3-iff-a-1-b3-0-a3-2
                            (x (/ (cal-radius p)))
                            (y (point-in-r3-y1 p)))
                 (:instance b3-0-a-1-a3-iff-a-1-b3-0-a3-2
                            (x (/ (cal-radius p)))
                            (y (point-in-r3-z1 p)))
                 )
           :in-theory nil
           )))

(defthmd b3-0-a-1-a3=>b3-0-a-1-b3-0-a3-1
  (implies (point-in-r3 p1)
           (m-= (m-* (a-rotation (acl2-sqrt 2)) (a-inv-rotation (acl2-sqrt 2)) p1)
                p1))
  :hints (("Goal"
           :use ((:instance funs-lemmas-2 (x (acl2-sqrt 2)))
                 (:instance m-*point-id=point (p1 p1))
                 (:instance ASSOCIATIVITY-OF-M-*
                            (m1 (a-rotation (acl2-sqrt 2)))
                            (m2 (a-inv-rotation (acl2-sqrt 2)))
                            (m3 p1))
                 )
           :in-theory (e/d () (a-rotation a-inv-rotation b-rotation b-inv-rotation acl2-sqrt m-= m-* (:EXECUTABLE-COUNTERPART ID-ROTATION) id-rotation ASSOCIATIVITY-OF-M-* M-*POINT-ID=POINT))
           )))

(defthmd b3-0-a-1-a3=>b3-0-a-1-b3-0-a3-2
  (implies (and (EQUAL
                 (POINT-IN-R3-X1 (SET-A-INV-A3-1-WITNESS (B3-0-SET-A-INV-A3-1-WITNESS P)))
                 (* (/ (CAL-RADIUS P))
                    (POINT-IN-R3-X1 (M-* (A-ROTATION (ACL2-SQRT 2)) P))))
                (EQUAL
                 (POINT-IN-R3-y1 (SET-A-INV-A3-1-WITNESS (B3-0-SET-A-INV-A3-1-WITNESS P)))
                 (* (/ (CAL-RADIUS P))
                    (POINT-IN-R3-y1 (M-* (A-ROTATION (ACL2-SQRT 2)) P))))
                (EQUAL
                 (POINT-IN-R3-z1 (SET-A-INV-A3-1-WITNESS (B3-0-SET-A-INV-A3-1-WITNESS P)))
                 (* (/ (CAL-RADIUS P))
                    (POINT-IN-R3-z1 (M-* (A-ROTATION (ACL2-SQRT 2)) P)))))
           (and (EQUAL
                 (POINT-IN-R3-X1 (SET-A-INV-A3-1-WITNESS (B3-0-SET-A-INV-A3-1-WITNESS P)))
                 (* (POINT-IN-R3-X1 (M-* (A-ROTATION (ACL2-SQRT 2)) P))
                    (/ (CAL-RADIUS P))))
                (EQUAL
                 (POINT-IN-R3-y1 (SET-A-INV-A3-1-WITNESS (B3-0-SET-A-INV-A3-1-WITNESS P)))
                 (* (POINT-IN-R3-y1 (M-* (A-ROTATION (ACL2-SQRT 2)) P))
                    (/ (CAL-RADIUS P))))
                (EQUAL
                 (POINT-IN-R3-z1 (SET-A-INV-A3-1-WITNESS (B3-0-SET-A-INV-A3-1-WITNESS P)))
                 (* (POINT-IN-R3-z1 (M-* (A-ROTATION (ACL2-SQRT 2)) P))
                    (/ (CAL-RADIUS P)))))))

(defthmd b3-0-a-1-a3=>b3-0-a-1-b3-0-a3-3
  (implies (point-in-r3 p1)
           (m-= (m-* (a-inv-rotation (acl2-sqrt 2)) (a-rotation (acl2-sqrt 2)) p1)
                p1))
  :hints (("Goal"
           :use ((:instance funs-lemmas-2 (x (acl2-sqrt 2)))
                 (:instance m-*point-id=point (p1 p1))
                 (:instance ASSOCIATIVITY-OF-M-*
                            (m1 (a-inv-rotation (acl2-sqrt 2)))
                            (m2 (a-rotation (acl2-sqrt 2)))
                            (m3 p1))
                 )
           :in-theory (e/d () (a-rotation a-inv-rotation b-rotation b-inv-rotation acl2-sqrt m-= m-* (:EXECUTABLE-COUNTERPART ID-ROTATION) id-rotation ASSOCIATIVITY-OF-M-* M-*POINT-ID=POINT))
           )))

(defthmd b3-0-a-1-a3=>b3-0-a-1-b3-0-a3
  (implies (b3-0-set-a-inv-a3 p)
           (b3-0-a-inv-b3-0-set-a3 p))
  :hints (("Goal"
           :use ((:instance b3-0-set-a-inv-a3 (p p))
                 (:instance b3-0-set-a-inv-a3-1 (p p))
                 (:instance set-a-inv-a3 (p (B3-0-SET-A-INV-A3-1-WITNESS P)))
                 (:instance set-a-inv-a3-1 (point (B3-0-SET-A-INV-A3-1-WITNESS P)))
                 (:instance b3-0-a-inv-b3-0-set-a3 (p p))
                 (:instance b3-0-a-inv-b3-0-set-a3-1-suff
                            (p p)
                            (p-s2 (m-* (a-rotation (acl2-sqrt 2)) p)))
                 (:instance b3-0-set-a3 (p (m-* (a-rotation (acl2-sqrt 2)) p)))
                 (:instance set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-1-1
                            (p1 p)
                            (rot (a-rotation (acl2-sqrt 2))))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance r3-rotationp (m (a-rotation (acl2-sqrt 2))))
                 (:instance m1=m2/a=>m1=s-*/a-m2
                            (p1 (B3-0-SET-A-INV-A3-1-WITNESS P))
                            (p2 p)
                            (a (/ (CAL-RADIUS P))))
                 (:instance b3-0-a-1-a3-iff-a-1-b3-0-a3-2
                            (x (/ (cal-radius p)))
                            (y (point-in-r3-x1 p)))
                 (:instance b3-0-a-1-a3-iff-a-1-b3-0-a3-2
                            (x (/ (cal-radius p)))
                            (y (point-in-r3-y1 p)))
                 (:instance b3-0-a-1-a3-iff-a-1-b3-0-a3-2
                            (x (/ (cal-radius p)))
                            (y (point-in-r3-z1 p)))
                 (:instance set-a3 (p (SET-A-INV-A3-1-WITNESS (B3-0-SET-A-INV-A3-1-WITNESS P))))
                 (:instance wa-00 (p (SET-A-INV-A3-1-WITNESS (B3-0-SET-A-INV-A3-1-WITNESS P))))
                 (:instance wa-0 (p (SET-A-INV-A3-1-WITNESS (B3-0-SET-A-INV-A3-1-WITNESS P))))
                 (:instance s2-not-e (point (SET-A-INV-A3-1-WITNESS (B3-0-SET-A-INV-A3-1-WITNESS P))))
                 (:instance s2-def-p (point (SET-A-INV-A3-1-WITNESS (B3-0-SET-A-INV-A3-1-WITNESS P))))
                 (:instance M-=-IMPLIES-EQUAL-M-*-2
                            (m1 (a-rotation (acl2-sqrt 2)))
                            (m2 (M-* (A-INV-ROTATION (ACL2-SQRT 2))
                                     (SET-A-INV-A3-1-WITNESS (B3-0-SET-A-INV-A3-1-WITNESS P))))
                            (m2-equiv (B3-0-SET-A-INV-A3-1-WITNESS P)))
                 (:instance b3-0-a-1-a3=>b3-0-a-1-b3-0-a3-1
                            (p1 (SET-A-INV-A3-1-WITNESS (B3-0-SET-A-INV-A3-1-WITNESS P))))
                 (:instance m-*-s-*-right
                            (m1 (A-ROTATION (ACL2-SQRT 2)))
                            (m2 p)
                            (name :fake-name)
                            (a (/ (CAL-RADIUS P))))
                 (:instance r3-matrixp (m (A-ROTATION (ACL2-SQRT 2))))
                 (:instance array2p-alist2p

                            (name :fake-name)
                            (l (A-ROTATION (ACL2-SQRT 2))))
                 (:instance point-in-r3 (x p))
                 (:instance normalize-dimensions-name (name '$ARG) (l p))
                 (:instance array2p-alist2p
                            (name :fake-name)
                            (l p))
                 (:instance M-=-IMPLIES-EQUAL-M-*-2
                            (m1 (a-rotation (acl2-sqrt 2)))
                            (m2 (B3-0-SET-A-INV-A3-1-WITNESS P))
                            (m2-equiv (S-* (/ (CAL-RADIUS P)) P)))
                 (:instance B3-0-SET-A3-1-suff
                            (p-s2 (SET-A-INV-A3-1-WITNESS (B3-0-SET-A-INV-A3-1-WITNESS P)))
                            (p (M-* (A-ROTATION (ACL2-SQRT 2)) P)))
                 (:instance m-=m1m2=>r-m1=r-m2-1
                            (p1 (SET-A-INV-A3-1-WITNESS (B3-0-SET-A-INV-A3-1-WITNESS P)))
                            (p2 (S-* (/ (CAL-RADIUS P))
                                     (M-* (A-ROTATION (ACL2-SQRT 2)) P))))
                 (:instance pr3-p=>pr3-a*p
                            (a (/ (cal-radius p)))
                            (p (M-* (A-ROTATION (ACL2-SQRT 2)) P)))
                 (:instance pr3=>r^2>=0 (p p))
                 (:instance aref2-s-*
                            (name :fake-name)
                            (A (/ (CAL-RADIUS P)))
                            (M (M-* (A-ROTATION (ACL2-SQRT 2)) P))
                            (i 0)
                            (j 0))
                 (:instance aref2-s-*
                            (name :fake-name)
                            (A (/ (CAL-RADIUS P)))
                            (M (M-* (A-ROTATION (ACL2-SQRT 2)) P))
                            (i 1)
                            (j 0))
                 (:instance aref2-s-*
                            (name :fake-name)
                            (A (/ (CAL-RADIUS P)))
                            (M (M-* (A-ROTATION (ACL2-SQRT 2)) P))
                            (i 2)
                            (j 0))
                 (:instance m-=m-*rot-p1=p2=>r-p1=r-p2
                            (p1 p)
                            (p2 (M-* (A-ROTATION (ACL2-SQRT 2)) P))
                            (rot (a-rotation (acl2-sqrt 2))))
                 (:instance point-in-r3-x1
                            (p (SET-A-INV-A3-1-WITNESS (B3-0-SET-A-INV-A3-1-WITNESS P))))
                 (:instance point-in-r3-x1
                            (p (M-* (A-ROTATION (ACL2-SQRT 2)) p)))
                 (:instance point-in-r3-y1
                            (p (SET-A-INV-A3-1-WITNESS (B3-0-SET-A-INV-A3-1-WITNESS P))))
                 (:instance point-in-r3-y1
                            (p (M-* (A-ROTATION (ACL2-SQRT 2)) p)))
                 (:instance point-in-r3-z1
                            (p (SET-A-INV-A3-1-WITNESS (B3-0-SET-A-INV-A3-1-WITNESS P))))
                 (:instance point-in-r3-z1
                            (p (M-* (A-ROTATION (ACL2-SQRT 2)) p)))
                 (:instance b3-0-a-1-a3=>b3-0-a-1-b3-0-a3-2)
                 (:instance b3-0-a-1-a3=>b3-0-a-1-b3-0-a3-3 (p1 p))
                 )
           :in-theory nil
           )))


;; (defthmd m1=m2/a=>m1=s-*/a-m2
;;   (implies (and (point-in-r3 p1)
;;                 (point-in-r3 p2)
;;                 (equal (point-in-r3-x1 p1)
;;                        (* a (point-in-r3-x1 p2)))
;;                 (equal (point-in-r3-y1 p1)
;;                        (* a (point-in-r3-y1 p2)))
;;                 (equal (point-in-r3-z1 p1)
;;                        (* a (point-in-r3-z1 p2))))
;;            (m-= p1 (s-* a p2)))
;;   :hints (("Goal"
;;            :use ((:instance aref2-s-* (M p2) (a a))
;;                  (:instance dimensions-s-* (M p2) (a a)))
;;            :in-theory (e/d (m-=) (s-*))
;;            )))

;; (defthmd m-=m1m2=>r-m1=r-m2-1
;;   (implies (and (point-in-r3 p1)
;;                 (point-in-r3 p2)
;;                 (m-= p1 p2))
;;            (and (equal (aref2 :fake-name p1 0 0) (aref2 :fake-name p2 0 0))
;;                 (equal (aref2 :fake-name p1 1 0) (aref2 :fake-name p2 1 0))
;;                 (equal (aref2 :fake-name p1 2 0) (aref2 :fake-name p2 2 0))))
;;   :hints (("Goal"
;;            :in-theory (enable m-=)
;;            )))

;; (defthmd m-=m1m2=>r-m1=r-m2-2
;;   (implies (and (point-in-r3 p1)
;;                 (point-in-r3 p2)
;;                 (r3-rotationp rot)
;;                 (m-= (m-* rot p1) p2))
;;            (equal (+ (* (aref2 :fake-name p1 0 0) (aref2 :fake-name p1 0 0))
;;                      (* (aref2 :fake-name p1 1 0) (aref2 :fake-name p1 1 0))
;;                      (* (aref2 :fake-name p1 2 0) (aref2 :fake-name p1 2 0)))
;;                   (+ (* (aref2 :fake-name p2 0 0) (aref2 :fake-name p2 0 0))
;;                      (* (aref2 :fake-name p2 1 0) (aref2 :fake-name p2 1 0))
;;                      (* (aref2 :fake-name p2 2 0) (aref2 :fake-name p2 2 0)))))
;;   :hints (("Goal"
;;            :use ((:instance rotation*point-on-s2 (p1 p1) (p2 (m-* rot p1)))
;;                  (:instance set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-1-1
;;                             (rot rot)
;;                             (p1 p1))
;;                  (:instance r3-rotationp (m rot))
;;                  (:instance m-=m1m2=>r-m1=r-m2-1 (p1 (m-* rot p1)) (p2 p2))
;;                  )
;;            :in-theory nil
;;            ))
;;   )

;; (defthmd m-=m-*rot-p1=p2=>r-p1=r-p2
;;   (implies (and (point-in-r3 p1)
;;                 (point-in-r3 p2)
;;                 (r3-rotationp rot)
;;                 (m-= (m-* rot p1) p2))
;;            (equal (cal-radius p1)
;;                   (cal-radius p2)))
;;   :hints (("Goal"
;;            :use ((:instance m-=m1m2=>r-m1=r-m2-2 (p1 p1) (p2 p2) (rot rot))
;;                  )
;;            :in-theory (disable m-= m-* point-in-r3 r3-rotationp)
;;            )))
