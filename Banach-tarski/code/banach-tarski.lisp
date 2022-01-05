
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

(defun-sk b3-0-s2 (p)
  (exists p-s2
          (and (s2-def-p p-s2)
               (equal (point-in-r3-x1 p-s2) (/ (point-in-r3-x1 p) (cal-radius p)))
               (equal (point-in-r3-y1 p-s2) (/ (point-in-r3-y1 p) (cal-radius p)))
               (equal (point-in-r3-z1 p-s2) (/ (point-in-r3-z1 p) (cal-radius p))))))

(defun b3-0-equiv (p)
  (and (point-in-r3 p)
       (> (cal-radius p) 0)
       (<= (cal-radius p) 1)
       (b3-0-s2 p)))

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
             :use ((:instance b3-0-s2-suff (p-s2 (point-p/r p)) (p p))
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
             :in-theory (e/d () (point-in-r3 point-in-r3-x1 point-in-r3-y1 point-in-r3-z1 point-p/r cal-radius s2-def-p b3-0-equiv b3-0-s2 (:rewrite b3-0-s2-suff) pr3-point-p))
             )))

  (defthmd b3-0-iff-b3-0-equiv
    (iff (b3-0 p)
         (b3-0-equiv p))
    :hints (("goal"
             :use ((:instance b3-0-s2-suff (p-s2 (point-p/r p)) (p p))
                   (:instance point-p/r=>1 (p p))
                   (:instance point-p/r=>2 (p p))
                   (:instance s2-def-p (point (point-p/r p)))
                   (:instance pr3-point-p (p p))
                   (:instance b3-0 (p p))
                   (:instance b3-0=>r^2>0 (p p))
                   (:instance b3-0-iff-b3-0-equiv-1 (p p))
                   (:instance b3-0-equiv (p p))
                   )
             :in-theory (e/d () (point-in-r3 point-in-r3-x1 point-in-r3-y1 point-in-r3-z1 point-p/r cal-radius s2-def-p b3-0-equiv b3-0-s2 (:rewrite b3-0-s2-suff) pr3-point-p))
             )))
  )
