
(include-book "banach-tarski-1")

(defun-sk set-a-inv-a3-1 (point)
  (exists p
          (and (set-a3 p)
               (m-= (m-* (a-inv-rotation (acl2-sqrt 2)) p)
                    point))))

(defun set-a-inv-a3 (p)
  (and (point-in-r3 p)
       (set-a-inv-a3-1 p)))

(defun-sk set-a-inv-r-a4-1 (point)
  (exists p
          (and (set-a4 p)
               (m-= (m-* (a-inv-rotation (acl2-sqrt 2))
                         (rotation-about-witness (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))) (point-on-s2-not-d))
                         p)
                    point))))

(defun set-a-inv-r-a4 (p)
  (and (point-in-r3 p)
       (set-a-inv-r-a4-1 p)))

(defun-sk set-r-1-a-inv-a5-1 (point)
  (exists p
          (and (set-a5 p)
               (m-= (m-*
                     (rotation-about-witness (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d))
                     (a-inv-rotation (acl2-sqrt 2))
                     p)
                    point))))

(defun set-r-1-a-inv-a5 (p)
  (and (point-in-r3 p)
       (set-r-1-a-inv-a5-1 p)))

(defun-sk set-r-1-a-inv-r-a6-1 (point)
  (exists p
          (and (set-a6 p)
               (m-= (m-*
                     (rotation-about-witness (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d))
                     (a-inv-rotation (acl2-sqrt 2))
                     (rotation-about-witness (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))) (point-on-s2-not-d))
                     p)
                    point))))

(defun set-r-1-a-inv-r-a6 (p)
  (and (point-in-r3 p)
       (set-r-1-a-inv-r-a6-1 p)))

---

(defthmd s2-equivalence-2-1
  (implies (s2-def-p p)
           (or (set-a-inv-a3 p)
               (set-a-inv-r-a4 p)
               (set-r-1-a-inv-a5 p)
               (set-r-1-a-inv-r-a6 p)
               (set-a7 p)
               (set-a8 p)))
  :hints (("Goal"
           :use ((:instance s2-iff-s2-e-or-e (point p))
                 (:instance s2-not-e=>s2-not-d-n-s2-not-e (point p))
                 (:instance set-e-p-iff-wit-inv*s2-d-p-n-set-e-p (point p))
                 (:instance s2-d-p-equivalence-2 (p p))
                 (:instance s2-not-d-n-s2-not-e (point p))
                 )
           :cases ((and (a-inv-diff-a-s2-d-p p) (s2-not-e p))
                   (and (diff-a-inv-s2-d-p p) (s2-not-e p))
                   (wit-inv*s2-d-p-n-set-e-p p)
                   )

           :in-theory nil
           )
          ("Subgoal 3"
           :use ((:instance a-inv-diff-a-s2-d-p (p p))
                 (:instance a-inv-diff-a-s2-d-p-1 (p p))
                 (:instance set-a-inv-a3 (p p))
                 (:instance set-a-inv-a3-1-suff (p (A-INV-DIFF-A-S2-D-P-1-WITNESS P)) (point p))
                 (:instance set-a3 (p (A-INV-DIFF-A-S2-D-P-1-WITNESS P)))
                 (:instance wa-00 (p (A-INV-DIFF-A-S2-D-P-1-WITNESS P)))
                 (:instance wa-0 (p (A-INV-DIFF-A-S2-D-P-1-WITNESS P)))
                 (:instance set-a-inv-r-a4 (p p))
                 (:instance set-a-inv-r-a4-1-suff (point p)
                            (p (A-INV-DIFF-A-S2-D-P-1-WITNESS P)))
                 (:instance set-a4 (p (A-INV-DIFF-A-S2-D-P-1-WITNESS P)))
                 (:instance set-a4-1-suff (point p) (p (A-INV-DIFF-A-S2-D-P-1-WITNESS P)))
                 (:instance wa-10 (p (A-INV-DIFF-A-S2-D-P-1-WITNESS P)))
                 ;(:instance wa-0 (p (A-INV-DIFF-A-S2-D-P-1-WITNESS P)))
                 )
           )
          ))

---

(defthmd s2-iff-s2-e-or-e
  (iff (s2-def-p point)
       (or (s2-not-e point)
           (set-e-p point))))

(defthmd iff-s2-s2-e-or-witinv*s2-d-n-e
  (iff (s2-def-p point)
       (or (s2-not-d-n-s2-not-e point)
           (wit-inv*s2-d-p-n-set-e-p point)))
  :hints (("goal"
           :use ((:instance s2-not-e=>s2-not-d-n-s2-not-e (point point))
                 (:instance set-e-p-iff-wit-inv*s2-d-p-n-set-e-p (point point))
                 (:instance s2-not-e (point point))
                 (:instance s2-iff-s2-e-or-e (point point))
                 )
           :in-theory nil
           )))

(defun m0 (p)
  (and (diff-n-s2-d-p p)
       (s2-not-e p)))

(defun m1 (p)
  (and (diff-n-s2-d-p p)
       (set-e-p p)))

(defun wa-0 (p)
  (and (diff-a-s2-d-p p)
       (s2-not-e p)))

(defun wa-1 (p)
  (and (diff-a-s2-d-p p)
       (set-e-p p)))

(defun wa-inv-0 (p)
  (and (diff-a-inv-s2-d-p p)
       (s2-not-e p)))

(defun wa-inv-1 (p)
  (and (diff-a-inv-s2-d-p p)
       (set-e-p p)))

(defun wb-0 (p)
  (and (diff-b-s2-d-p p)
       (s2-not-e p)))

(defun wb-1 (p)
  (and (diff-b-s2-d-p p)
       (set-e-p p)))

(defun wb-inv-0 (p)
  (and (diff-b-inv-s2-d-p p)
       (s2-not-e p)))

(defun wb-inv-1 (p)
  (and (diff-b-inv-s2-d-p p)
       (set-e-p p)))

(defun-sk r-1*m1-1 (point)
  (exists p
          (and (m1 p)
               (m-= (m-* (rotation-about-witness (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d)) p) point))))

(defun r-1*m1 (p)
  (and (point-in-r3 p)
       (r-1*m1-1 p)))

(defun-sk r-1*wa-1-1 (point)
  (exists p
          (and (wa-1 p)
               (m-= (m-* (rotation-about-witness (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d)) p) point))))

(defun r-1*wa-1 (p)
  (and (point-in-r3 p)
       (r-1*wa-1-1 p)))

(defun-sk r-1*wa-inv-1-1 (point)
  (exists p
          (and (wa-inv-1 p)
               (m-= (m-* (rotation-about-witness (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d)) p) point))))

(defun r-1*wa-inv-1 (p)
  (and (point-in-r3 p)
       (r-1*wa-inv-1-1 p)))

(defun-sk r-1*wb-1-1 (point)
  (exists p
          (and (wb-1 p)
               (m-= (m-* (rotation-about-witness (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d)) p) point))))

(defun r-1*wb-1 (p)
  (and (point-in-r3 p)
       (r-1*wb-1-1 p)))

(defun-sk r-1*wb-inv-1-1 (point)
  (exists p
          (and (wb-inv-1 p)
               (m-= (m-* (rotation-about-witness (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d)) p) point))))

(defun r-1*wb-inv-1 (p)
  (and (point-in-r3 p)
       (r-1*wb-inv-1-1 p)))

(defun r-1-diff-s2 (p)
  (or (r-1*m1 p)
      (r-1*wa-1 p)
      (r-1*wa-inv-1 p)
      (r-1*wb-1 p)
      (r-1*wb-inv-1 p)))

(defthmd s2=>r-1-diff-s2
  (implies (wit-inv*s2-d-p-n-set-e-p p)
           (r-1-diff-s2 p))
  :hints (("goal"
           :use ((:instance wit-inv*s2-d-p-n-set-e-p (point p))
                 (:instance wit-inv*s2-d-p-n-set-e-1 (point p))
                 (:instance s2-d-p-n-set-e (point (wit-inv*s2-d-p-n-set-e-1-witness p)))
                 (:instance s2-d-p-equivalence-1 (p (wit-inv*s2-d-p-n-set-e-1-witness p)))
                 (:instance set-e-p (point (wit-inv*s2-d-p-n-set-e-1-witness p)))
                 (:instance r-1*m1-1-suff (point p)
                            (p (wit-inv*s2-d-p-n-set-e-1-witness p)))
                 (:instance m1 (p (wit-inv*s2-d-p-n-set-e-1-witness p)))
                 (:instance r-1*m1 (p p))
                 (:instance r-1-diff-s2 (p p))
                 (:instance r-1*wa-1-1-suff (point p)
                            (p (wit-inv*s2-d-p-n-set-e-1-witness p)))
                 (:instance wa-1 (p (wit-inv*s2-d-p-n-set-e-1-witness p)))
                 (:instance r-1*wa-1 (p p))
                 (:instance r-1*wb-1-1-suff (point p)
                            (p (wit-inv*s2-d-p-n-set-e-1-witness p)))
                 (:instance wb-1 (p (wit-inv*s2-d-p-n-set-e-1-witness p)))
                 (:instance r-1*wb-1 (p p))
                 (:instance r-1*wb-inv-1-1-suff (point p)
                            (p (wit-inv*s2-d-p-n-set-e-1-witness p)))
                 (:instance wb-inv-1 (p (wit-inv*s2-d-p-n-set-e-1-witness p)))
                 (:instance r-1*wb-inv-1 (p p))
                 (:instance r-1*wa-inv-1-1-suff (point p)
                            (p (wit-inv*s2-d-p-n-set-e-1-witness p)))
                 (:instance wa-inv-1 (p (wit-inv*s2-d-p-n-set-e-1-witness p)))
                 (:instance r-1*wa-inv-1 (p p))
                 )
           :in-theory nil
           )))

(defthmd r-1-diff-s2=>s2
  (implies (r-1-diff-s2 p)
           (wit-inv*s2-d-p-n-set-e-p p))
  :hints (("goal"
           :use ((:instance r-1-diff-s2 (p p))
                 (:instance wit-inv*s2-d-p-n-set-e-p (point p))
                 )
           :cases ((r-1*m1 p)
                   (r-1*wb-inv-1 p)
                   (r-1*wa-inv-1 p)
                   (r-1*wa-1 p)
                   (r-1*wb-1 p))
           :in-theory nil
           )
          ("subgoal 5"
           :use ((:instance r-1*m1 (p p))
                 (:instance r-1*m1-1 (point p))
                 (:instance m1 (p (r-1*m1-1-witness p)))
                 (:instance s2-d-p-equivalence-1 (p (r-1*m1-1-witness p)))
                 (:instance wit-inv*s2-d-p-n-set-e-1-suff (point p)
                            (p (r-1*m1-1-witness p)))
                 (:instance s2-d-p-n-set-e (point (r-1*m1-1-witness p)))
                 )
           )
          ("subgoal 4"
           :use ((:instance r-1*wb-inv-1 (p p))
                 (:instance r-1*wb-inv-1-1 (point p))
                 (:instance wb-inv-1 (p (r-1*wb-inv-1-1-witness p)))
                 (:instance s2-d-p-equivalence-1 (p (r-1*wb-inv-1-1-witness p)))
                 (:instance wit-inv*s2-d-p-n-set-e-1-suff (point p)
                            (p (r-1*wb-inv-1-1-witness p)))
                 (:instance s2-d-p-n-set-e (point (r-1*wb-inv-1-1-witness p)))
                 )
           )
          ("subgoal 3"
           :use ((:instance r-1*wa-inv-1 (p p))
                 (:instance r-1*wa-inv-1-1 (point p))
                 (:instance wa-inv-1 (p (r-1*wa-inv-1-1-witness p)))
                 (:instance s2-d-p-equivalence-1 (p (r-1*wa-inv-1-1-witness p)))
                 (:instance wit-inv*s2-d-p-n-set-e-1-suff (point p)
                            (p (r-1*wa-inv-1-1-witness p)))
                 (:instance s2-d-p-n-set-e (point (r-1*wa-inv-1-1-witness p)))
                 )
           )
          ("subgoal 2"
           :use ((:instance r-1*wa-1 (p p))
                 (:instance r-1*wa-1-1 (point p))
                 (:instance wa-1 (p (r-1*wa-1-1-witness p)))
                 (:instance s2-d-p-equivalence-1 (p (r-1*wa-1-1-witness p)))
                 (:instance wit-inv*s2-d-p-n-set-e-1-suff (point p)
                            (p (r-1*wa-1-1-witness p)))
                 (:instance s2-d-p-n-set-e (point (r-1*wa-1-1-witness p)))
                 )
           )
          ("subgoal 1"
           :use ((:instance r-1*wb-1 (p p))
                 (:instance r-1*wb-1-1 (point p))
                 (:instance wb-1 (p (r-1*wb-1-1-witness p)))
                 (:instance s2-d-p-equivalence-1 (p (r-1*wb-1-1-witness p)))
                 (:instance wit-inv*s2-d-p-n-set-e-1-suff (point p)
                            (p (r-1*wb-1-1-witness p)))
                 (:instance s2-d-p-n-set-e (point (r-1*wb-1-1-witness p)))
                 )
           )
          ))

(defthmd r-1-diff-s2-iff-s2
  (iff (r-1-diff-s2 p)
       (wit-inv*s2-d-p-n-set-e-p p)))

(defun diff-s2 (p)
  (or (m0 p)
      (r-1*m1 p)
      (wa-0 p)
      (r-1*wa-1 p)
      (wa-inv-0 p)
      (r-1*wa-inv-1 p)
      (wb-0 p)
      (r-1*wb-1 p)
      (wb-inv-0 p)
      (r-1*wb-inv-1 p)))

(defthmd s2-iff-diff-s2
  (iff (s2-def-p p)
       (diff-s2 p))
  :hints (("goal"
           :use ((:instance diff-s2 (p p))
                 (:instance r-1-diff-s2 (p p))
                 (:instance iff-s2-s2-e-or-witinv*s2-d-n-e (point p))
                 (:instance s2-not-d-n-s2-not-e (point p))
                 (:instance r-1-diff-s2-iff-s2 (p p))
                 (:instance s2-d-p-equivalence-1 (p p))
                 (:instance m0 (p p))
                 (:instance wa-0 (p p))
                 (:instance wb-0 (p p))
                 (:instance wa-inv-0 (p p))
                 (:instance wb-inv-0 (p p))
                 )
           :in-theory nil
           )))

(defun-sk rot-a*s2-not-e-1 (point)
  (exists p
          (and (s2-not-e p)
               (m-= (m-* (a-rotation (acl2-sqrt 2)) p)
                    point))))

(defun rot-a*s2-not-e (p)
  (and (point-in-r3 p)
       (rot-a*s2-not-e-1 p)))

(defun-sk rot-a*-e-1 (point)
  (exists p
          (and (set-e-p p)
               (m-= (m-* (a-rotation (acl2-sqrt 2)) p)
                    point))))

(defun rot-a*-e (p)
  (and (point-in-r3 p)
       (rot-a*-e-1 p)))

(defun rot-a*s2-e-or-e (p)
  (or (rot-a*s2-not-e p)
      (rot-a*-e p)))

(defthmd s2-iff-rot-a*s2-e-or-e-1
  (implies (point-in-r3 p)
           (m-= (m-* (a-rotation (acl2-sqrt 2))
                     (a-inv-rotation (acl2-sqrt 2))
                     p)
                p))
  :hints (("goal"
           :use ((:instance funs-lemmas-2 (x (acl2-sqrt 2)))
                 (:instance m-*point-id=point (p1 p))
                 (:instance efunc-not-d=>rot-witness*e-func-3-1
                            (a (a-rotation (acl2-sqrt 2)))
                            (b (a-inv-rotation (acl2-sqrt 2)))
                            (c p))
                 )
           :in-theory (e/d () (a-rotation a-inv-rotation m-* m-= id-rotation acl2-sqrt point-in-r3 array2p m-*point-id=point aref2 b-rotation b-inv-rotation (:executable-counterpart id-rotation)))
           )))

(defthmd s2-iff-rot-a*s2-e-or-e
  (iff (s2-def-p p)
       (rot-a*s2-e-or-e p))
  :hints (("goal"
           :in-theory nil
           )
          ("subgoal 1"
           :use ((:instance rot-a*s2-e-or-e (p p))
                 (:instance rot-a*-e (p p))
                 (:instance rot-a*s2-not-e (p p))
                 (:instance rot-a*-e-1-suff (point p)
                            (p (m-* (a-inv-rotation (acl2-sqrt 2)) p)))
                 (:instance rot-a*s2-not-e-1-suff (point p)
                            (p (m-* (a-inv-rotation (acl2-sqrt 2)) p)))
                 (:instance s2-iff-rot-a*s2-e-or-e-1 (p p))
                 (:instance s2-not-e (point (m-* (a-inv-rotation (acl2-sqrt 2)) p)))
                 (:instance s2-def-p (point p))
                 (:instance rot*p-on-s2 (p p)
                            (rot (a-inv-rotation (acl2-sqrt 2))))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance s2-def-p (point (m-* (a-inv-rotation (acl2-sqrt 2)) p)))
                 )
           )
          ("subgoal 2"
           :use ((:instance rot-a*s2-not-e (p p))
                 (:instance rot-a*s2-not-e-1 (point p))
                 (:instance s2-not-e (point (rot-a*s2-not-e-1-witness p)))
                 (:instance s2-def-p-p=>p1
                            (p (m-* (a-rotation (acl2-sqrt 2))
                                                   (rot-a*s2-not-e-1-witness p)))
                            (p1 p))
                 (:instance rot*p-on-s2 (p (rot-a*s2-not-e-1-witness p))
                            (rot (a-rotation (acl2-sqrt 2))))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance rot-a*s2-e-or-e (p p))

                 (:instance rot-a*-e (p p))
                 (:instance rot-a*-e-1 (point p))
                 (:instance set-e-p (point (rot-a*-e-1-witness p)))
                 (:instance efunc=> (point (rot-a*-e-1-witness p)))
                 (:instance r3-rotationp-r-theta
                            (angle (* (efunc-witness (rot-a*-e-1-witness p))
                                       (exists-in-interval-but-not-in-angle-sequence-witness
                                        0 (* 2 (acl2-pi))))))
                 (:instance set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-2-2
                            (n (efunc-witness (rot-a*-e-1-witness p)))
                            (x (exists-in-interval-but-not-in-angle-sequence-witness
                                0 (* 2 (acl2-pi)))))
                 (:instance witness-not-in-angle-sequence)
                 (:instance rot*p-on-s2 (p (exists-d-p-witness (efunc-witness (rot-a*-e-1-witness p))
                                                               (rot-a*-e-1-witness p)))
                            (rot (rotation-about-witness (* (efunc-witness (rot-a*-e-1-witness p))
                                       (exists-in-interval-but-not-in-angle-sequence-witness
                                        0 (* 2 (acl2-pi))))
                                                         (point-on-s2-not-d))))
                 (:instance s2-def-p-p=>p1 (p (m-* (rotation-about-witness (* (efunc-witness (rot-a*-e-1-witness p))
                                                                              (exists-in-interval-but-not-in-angle-sequence-witness
                                                                               0 (* 2 (acl2-pi))))
                                                                           (point-on-s2-not-d))
                                                   (exists-d-p-witness (efunc-witness (rot-a*-e-1-witness p))
                                                                       (rot-a*-e-1-witness p))))
                            (p1 (rot-a*-e-1-witness p)))
                 (:instance rot*p-on-s2 (p (rot-a*-e-1-witness p))
                            (rot (a-rotation (acl2-sqrt 2))))
                 (:instance d-p (point (exists-d-p-witness (efunc-witness (rot-a*-e-1-witness p))
                                                           (rot-a*-e-1-witness p))))
                 (:instance s2-def-p-p=>p1 (p (m-* (a-rotation (acl2-sqrt 2))
                                                   (rot-a*-e-1-witness p)))
                            (p1 p))
                 )
           )
          ))

(defthmd p1=p2-n-e-p1=>e-p2
  (implies (and (m-= p1 p2)
                (point-in-r3 p1)
                (point-in-r3 p2)
                (set-e-p p1))
           (set-e-p p2))
  :hints (("Goal"
           :use ((:instance set-e-p (point p1))
                 (:instance efunc=> (point p1))
                 (:instance set-e-p (point p2))
                 (:instance efunc-suff (point p2) (n (EFUNC-WITNESS P1)))
                 (:instance exists-d-p-suff (point p2)
                            (n (EFUNC-WITNESS P1))
                            (p (EXISTS-D-P-WITNESS (EFUNC-WITNESS P1)
                                                   P1)))
                 )
           :in-theory nil
           )))

(defthmd p1=p2-n-s2-e-p1=>s2-e-p2
  (implies (and (m-= p1 p2)
                (point-in-r3 p1)
                (point-in-r3 p2)
                (s2-not-e p1))
           (s2-not-e p2))
  :hints (("Goal"
           :use ((:instance s2-not-e (point p1))
                 (:instance s2-not-e (point p2))
                 (:instance s2-def-p-p=>p1 (p p1) (p1 p2))
                 (:instance p1=p2-n-e-p1=>e-p2 (p2 p1) (p1 p2))
                 )
           :in-theory nil
           ))
  )

(defthmd a*p1=p-n-a*p2=p=>p1=p2-1
  (implies (and (m-= m1 m2)
                (m-= m3 m2))
           (m-= m1 m3)))

(defthmd a*p1=p-n-a*p2=p=>p1=p2-2
  (implies (and (m-= (m-* a b c) (m-* p q r))
                (m-= (m-* a b) d)
                (m-= (m-* p q) s)
                (m-= (m-* d c) e)
                (m-= (m-* s r) t1))
           (m-= e t1)))

(defthmd a*p1=p-n-a*p2=p=>p1=p2
  (implies (and (point-in-r3 point)
                (point-in-r3 p1)
                (point-in-r3 p2)
                (m-= (m-* (a-rotation (acl2-sqrt 2)) p1) point)
                (m-= (m-* (a-rotation (acl2-sqrt 2)) p2) point))
           (m-= p1 p2))
  :hints (("Goal"
           :use ((:instance rot-angle-witness*p1!=p2-intmn-1
                            (m (m-* (a-rotation (acl2-sqrt 2)) p1))
                            (n (m-* (a-rotation (acl2-sqrt 2)) p2))
                            (p (a-inv-rotation (acl2-sqrt 2))))
                 (:instance funs-lemmas-2 (x (acl2-sqrt 2)))
                 (:instance m-*point-id=point (p1 p1))
                 (:instance efunc-not-d=>rot-witness*e-func-3-1
                            (a (a-inv-rotation (acl2-sqrt 2)))
                            (b (a-rotation (acl2-sqrt 2)))
                            (c p1))
                 (:instance m-*point-id=point (p1 p2))
                 (:instance efunc-not-d=>rot-witness*e-func-3-1
                            (a (a-inv-rotation (acl2-sqrt 2)))
                            (b (a-rotation (acl2-sqrt 2)))
                            (c p2))
                 (:instance a*p1=p-n-a*p2=p=>p1=p2-1 (m1 (M-* (A-ROTATION (ACL2-SQRT 2)) P1))
                            (m2 point)
                            (m3 (M-* (A-ROTATION (ACL2-SQRT 2)) P2)))
                 (:instance a*p1=p-n-a*p2=p=>p1=p2-2
                            (a (A-INV-ROTATION (ACL2-SQRT 2)))
                            (b (A-ROTATION (ACL2-SQRT 2)))
                            (c p1)
                            (p (A-INV-ROTATION (ACL2-SQRT 2)))
                            (q (A-ROTATION (ACL2-SQRT 2)))
                            (r p2)
                            (d (id-rotation))
                            (s (id-rotation))
                            (e p1)
                            (t1 p2))
                 )
           :in-theory nil
           )))

(defthmd rot-a*-e=>not-rot-a*s2-not-e
  (implies (rot-a*-e p)
           (not (rot-a*s2-not-e p)))
  :hints (("Goal"
           :use ((:instance rot-a*-e (p p))
                 (:instance rot-a*-e-1 (point p))
                 (:instance set-e-p (point (ROT-A*-E-1-WITNESS P)))
                 (:instance rot-a*s2-not-e (p p))
                 (:instance rot-a*s2-not-e-1 (point p))
                 (:instance s2-not-e (point (ROT-A*S2-NOT-E-1-WITNESS P)))
                 (:instance s2-def-p (point (ROT-A*S2-NOT-E-1-WITNESS P)))
                 (:instance a*p1=p-n-a*p2=p=>p1=p2 (point p)
                            (p1 (ROT-A*-E-1-WITNESS P))
                            (p2 (ROT-A*S2-NOT-E-1-WITNESS P)))
                 (:instance p1=p2-n-e-p1=>e-p2 (p1 (ROT-A*-E-1-WITNESS P))
                            (p2 (ROT-A*S2-NOT-E-1-WITNESS P)))
                 )
           :in-theory nil
           )))

(defun-sk rot-b*s2-not-e-1 (point)
  (exists p
          (and (s2-not-e p)
               (m-= (m-* (b-rotation (acl2-sqrt 2)) p)
                    point))))

(defun rot-b*s2-not-e (p)
  (and (point-in-r3 p)
       (rot-b*s2-not-e-1 p)))

(defun-sk rot-b*-e-1 (point)
  (exists p
          (and (set-e-p p)
               (m-= (m-* (b-rotation (acl2-sqrt 2)) p)
                    point))))

(defun rot-b*-e (p)
  (and (point-in-r3 p)
       (rot-b*-e-1 p)))

(defun rot-b*s2-e-or-e (p)
  (or (rot-b*s2-not-e p)
      (rot-b*-e p)))

(defthmd s2-iff-rot-b*s2-e-or-e-1-1
  (implies (and (m-= (m-* b b-inv) id)
                (m-= (m-* id p) p1))
           (m-= (m-* b b-inv p) p1)))

(defthmd s2-iff-rot-b*s2-e-or-e-1
  (implies (point-in-r3 p)
           (m-= (m-* (b-rotation (acl2-sqrt 2))
                     (b-inv-rotation (acl2-sqrt 2))
                     p)
                p))
  :hints (("goal"
           :use ((:instance funs-lemmas-2 (x (acl2-sqrt 2)))
                 (:instance m-*point-id=point (p1 p))
                 (:instance efunc-not-d=>rot-witness*e-func-3-1
                            (a (b-rotation (acl2-sqrt 2)))
                            (b (b-inv-rotation (acl2-sqrt 2)))
                            (c p))
                 (:instance efunc-not-d=>rot-witness*e-func-3-1
                            (a (b-rotation (acl2-sqrt 2)))
                            (b (b-inv-rotation (acl2-sqrt 2)))
                            (c p))
                 (:instance s2-iff-rot-b*s2-e-or-e-1-1
                            (b (b-rotation (acl2-sqrt 2)))
                            (b-inv (b-inv-rotation (acl2-sqrt 2)))
                            (id (id-rotation))
                            (p p)
                            (p1 p))
                 )
           :in-theory nil
           )))

(defthmd s2-iff-rot-b*s2-e-or-e
  (iff (s2-def-p p)
       (rot-b*s2-e-or-e p))
  :hints (("goal"
           :in-theory nil
           )
          ("subgoal 1"
           :use ((:instance rot-b*s2-e-or-e (p p))
                 (:instance rot-b*-e (p p))
                 (:instance rot-b*s2-not-e (p p))
                 (:instance rot-b*-e-1-suff (point p)
                            (p (m-* (b-inv-rotation (acl2-sqrt 2)) p)))
                 (:instance rot-b*s2-not-e-1-suff (point p)
                            (p (m-* (b-inv-rotation (acl2-sqrt 2)) p)))
                 (:instance s2-iff-rot-b*s2-e-or-e-1 (p p))
                 (:instance s2-not-e (point (m-* (b-inv-rotation (acl2-sqrt 2)) p)))
                 (:instance s2-def-p (point p))
                 (:instance rot*p-on-s2 (p p)
                            (rot (b-inv-rotation (acl2-sqrt 2))))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance s2-def-p (point (m-* (b-inv-rotation (acl2-sqrt 2)) p)))
                 )
           )
          ("subgoal 2"
           :use ((:instance rot-b*s2-not-e (p p))
                 (:instance rot-b*s2-not-e-1 (point p))
                 (:instance s2-not-e (point (rot-b*s2-not-e-1-witness p)))
                 (:instance s2-def-p-p=>p1
                            (p (m-* (b-rotation (acl2-sqrt 2))
                                                   (rot-b*s2-not-e-1-witness p)))
                            (p1 p))
                 (:instance rot*p-on-s2 (p (rot-b*s2-not-e-1-witness p))
                            (rot (b-rotation (acl2-sqrt 2))))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance rot-b*s2-e-or-e (p p))

                 (:instance rot-b*-e (p p))
                 (:instance rot-b*-e-1 (point p))
                 (:instance set-e-p (point (rot-b*-e-1-witness p)))
                 (:instance efunc=> (point (rot-b*-e-1-witness p)))
                 (:instance r3-rotationp-r-theta
                            (angle (* (efunc-witness (rot-b*-e-1-witness p))
                                       (exists-in-interval-but-not-in-angle-sequence-witness
                                        0 (* 2 (acl2-pi))))))
                 (:instance set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-2-2
                            (n (efunc-witness (rot-b*-e-1-witness p)))
                            (x (exists-in-interval-but-not-in-angle-sequence-witness
                                0 (* 2 (acl2-pi)))))
                 (:instance witness-not-in-angle-sequence)
                 (:instance rot*p-on-s2 (p (exists-d-p-witness (efunc-witness (rot-b*-e-1-witness p))
                                                               (rot-b*-e-1-witness p)))
                            (rot (rotation-about-witness (* (efunc-witness (rot-b*-e-1-witness p))
                                       (exists-in-interval-but-not-in-angle-sequence-witness
                                        0 (* 2 (acl2-pi))))
                                                         (point-on-s2-not-d))))
                 (:instance s2-def-p-p=>p1 (p (m-* (rotation-about-witness (* (efunc-witness (rot-b*-e-1-witness p))
                                                                              (exists-in-interval-but-not-in-angle-sequence-witness
                                                                               0 (* 2 (acl2-pi))))
                                                                           (point-on-s2-not-d))
                                                   (exists-d-p-witness (efunc-witness (rot-b*-e-1-witness p))
                                                                       (rot-b*-e-1-witness p))))
                            (p1 (rot-b*-e-1-witness p)))
                 (:instance rot*p-on-s2 (p (rot-b*-e-1-witness p))
                            (rot (b-rotation (acl2-sqrt 2))))
                 (:instance d-p (point (exists-d-p-witness (efunc-witness (rot-b*-e-1-witness p))
                                                           (rot-b*-e-1-witness p))))
                 (:instance s2-def-p-p=>p1 (p (m-* (b-rotation (acl2-sqrt 2))
                                                   (rot-b*-e-1-witness p)))
                            (p1 p))
                 )
           )
          ))

(defthmd b*p1=p-n-b*p2=p=>p1=p2
  (implies (and (point-in-r3 point)
                (point-in-r3 p1)
                (point-in-r3 p2)
                (m-= (m-* (b-rotation (acl2-sqrt 2)) p1) point)
                (m-= (m-* (b-rotation (acl2-sqrt 2)) p2) point))
           (m-= p1 p2))
  :hints (("Goal"
           :use ((:instance rot-angle-witness*p1!=p2-intmn-1
                            (m (m-* (b-rotation (acl2-sqrt 2)) p1))
                            (n (m-* (b-rotation (acl2-sqrt 2)) p2))
                            (p (b-inv-rotation (acl2-sqrt 2))))
                 (:instance funs-lemmas-2 (x (acl2-sqrt 2)))
                 (:instance m-*point-id=point (p1 p1))
                 (:instance efunc-not-d=>rot-witness*e-func-3-1
                            (a (b-inv-rotation (acl2-sqrt 2)))
                            (b (b-rotation (acl2-sqrt 2)))
                            (c p1))
                 (:instance m-*point-id=point (p1 p2))
                 (:instance efunc-not-d=>rot-witness*e-func-3-1
                            (a (b-inv-rotation (acl2-sqrt 2)))
                            (b (b-rotation (acl2-sqrt 2)))
                            (c p2))
                 (:instance a*p1=p-n-a*p2=p=>p1=p2-1 (m1 (M-* (b-ROTATION (ACL2-SQRT 2)) P1))
                            (m2 point)
                            (m3 (M-* (b-ROTATION (ACL2-SQRT 2)) P2)))
                 (:instance a*p1=p-n-a*p2=p=>p1=p2-2
                            (a (b-INV-ROTATION (ACL2-SQRT 2)))
                            (b (b-ROTATION (ACL2-SQRT 2)))
                            (c p1)
                            (p (b-INV-ROTATION (ACL2-SQRT 2)))
                            (q (b-ROTATION (ACL2-SQRT 2)))
                            (r p2)
                            (d (id-rotation))
                            (s (id-rotation))
                            (e p1)
                            (t1 p2))
                 )
           :in-theory nil
           )))

(defthmd rot-b*-e=>not-rot-b*s2-not-e
  (implies (rot-b*-e p)
           (not (rot-b*s2-not-e p)))
  :hints (("Goal"
           :use ((:instance rot-b*-e (p p))
                 (:instance rot-b*-e-1 (point p))
                 (:instance set-e-p (point (ROT-b*-E-1-WITNESS P)))
                 (:instance rot-b*s2-not-e (p p))
                 (:instance rot-b*s2-not-e-1 (point p))
                 (:instance s2-not-e (point (ROT-b*S2-NOT-E-1-WITNESS P)))
                 (:instance s2-def-p (point (ROT-b*S2-NOT-E-1-WITNESS P)))
                 (:instance b*p1=p-n-b*p2=p=>p1=p2 (point p)
                            (p1 (ROT-b*-E-1-WITNESS P))
                            (p2 (ROT-b*S2-NOT-E-1-WITNESS P)))
                 (:instance p1=p2-n-e-p1=>e-p2 (p1 (ROT-b*-E-1-WITNESS P))
                            (p2 (ROT-b*S2-NOT-E-1-WITNESS P)))
                 )
           :in-theory nil
           )))

(defun wa-00 (p)
  (and (wa-0 p)
       (rot-a*s2-not-e p)))

(defun wa-01 (p)
  (and (wa-0 p)
       (rot-a*-e p)))

(defun wa-10 (p)
  (and (wa-1 p)
       (rot-a*s2-not-e p)))

(defun wa-11 (p)
  (and (wa-1 p)
       (rot-a*-e p)))

(defun wb-00 (p)
  (and (wb-0 p)
       (rot-b*s2-not-e p)))

(defun wb-01 (p)
  (and (wb-0 p)
       (rot-b*-e p)))

(defun wb-10 (p)
  (and (wb-1 p)
       (rot-b*s2-not-e p)))

(defun wb-11 (p)
  (and (wb-1 p)
       (rot-b*-e p)))

(defthmd wa-0-iff-wa00-or-wa01
  (iff (wa-0 p)
       (or (wa-00 p)
           (wa-01 p)))
  :hints (("Goal"
           :use ((:instance wa-00 (p p))
                 (:instance wa-01 (p p))
                 (:instance s2-iff-rot-a*s2-e-or-e (p p))
                 (:instance wa-0 (p p))
                 (:instance s2-not-e (point p))
                 (:instance s2-d-p-equivalence-1 (p p))
                 (:instance s2-d-p (point p))
                 (:instance rot-a*s2-e-or-e (p p))
                 )
           :in-theory nil
           )))

(defthmd wa-1-iff-wa10-or-wa11
  (iff (wa-1 p)
       (or (wa-10 p)
           (wa-11 p)))
  :hints (("Goal"
           :use ((:instance wa-10 (p p))
                 (:instance wa-11 (p p))
                 (:instance s2-iff-rot-a*s2-e-or-e (p p))
                 (:instance wa-1 (p p))
                 (:instance s2-d-p-equivalence-1 (p p))
                 (:instance s2-d-p (point p))
                 (:instance rot-a*s2-e-or-e (p p))
                 (:instance set-e-p=>s2-def-p (point p))
                 )
           :in-theory nil
           )))

(defthmd wb-0-iff-wb00-or-wb01
  (iff (wb-0 p)
       (or (wb-00 p)
           (wb-01 p)))
  :hints (("Goal"
           :use ((:instance wb-00 (p p))
                 (:instance wb-01 (p p))
                 (:instance s2-iff-rot-b*s2-e-or-e (p p))
                 (:instance wb-0 (p p))
                 (:instance s2-not-e (point p))
                 (:instance s2-d-p-equivalence-1 (p p))
                 (:instance s2-d-p (point p))
                 (:instance rot-b*s2-e-or-e (p p))
                 )
           :in-theory nil
           )))

(defthmd wb-1-iff-wb10-or-wb11
  (iff (wb-1 p)
       (or (wb-10 p)
           (wb-11 p)))
  :hints (("Goal"
           :use ((:instance wb-10 (p p))
                 (:instance wb-11 (p p))
                 (:instance s2-iff-rot-b*s2-e-or-e (p p))
                 (:instance wb-1 (p p))
                 (:instance s2-d-p-equivalence-1 (p p))
                 (:instance s2-d-p (point p))
                 (:instance rot-b*s2-e-or-e (p p))
                 (:instance set-e-p=>s2-def-p (point p))
                 )
           :in-theory nil
           )))

(defun set-a1 (p)
  (m0 p))

(defun set-a2 (p)
  (r-1*m1 p))

(defun set-a3 (p)
  (wa-00 p))

(defun-sk set-a4-1 (point)
  (exists p
          (and (wa-10 p)
               (m-= (m-* (rotation-about-witness (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d)) p) point))))

(defun set-a4 (p)
  (and (point-in-r3 p)
       (set-a4-1 p)))

(defun set-a5 (p)
  (wa-01 p))

(defun-sk set-a6-1 (point)
  (exists p
          (and (wa-11 p)
               (m-= (m-* (rotation-about-witness (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d)) p) point))))

(defun set-a6 (p)
  (and (point-in-r3 p)
       (set-a6-1 p)))

(defun set-a7 (p)
  (wa-inv-0 p))

(defun set-a8 (p)
  (r-1*wa-inv-1 p))

(defun set-a9 (p)
  (wb-00 p))

(defun-sk set-a10-1 (point)
  (exists p
          (and (wb-10 p)
               (m-= (m-* (rotation-about-witness (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d)) p) point))))

(defun set-a10 (p)
  (and (point-in-r3 p)
       (set-a10-1 p)))

(defun set-a11 (p)
  (wb-01 p))

(defun-sk set-a12-1 (point)
  (exists p
          (and (wb-11 p)
               (m-= (m-* (rotation-about-witness (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d)) p) point))))

(defun set-a12 (p)
  (and (point-in-r3 p)
       (set-a12-1 p)))

(defun set-a13 (p)
  (wb-inv-0 p))

(defun set-a14 (p)
  (r-1*wb-inv-1 p))

(defun r-1-setas (p)
  (or (set-a2 p)
      (set-a4 p)
      (set-a6 p)
      (set-a8 p)
      (set-a10 p)
      (set-a12 p)
      (set-a14 p)))

(defthmd r-1-setas-iff-r-1-diff-s2-1
  (implies (r-1-setas p)
           (r-1-diff-s2 p))
  :hints (("Goal"
           :cases ((set-a2 p)
                   (set-a4 p)
                   (set-a6 p)
                   (set-a8 p)
                   (set-a10 p)
                   (set-a12 p)
                   (set-a14 p))
           :use ((:instance r-1-setas (p p))
                 (:instance r-1-diff-s2 (p p)))
           :in-theory nil
           )
          ("Subgoal 7"
           :use ((:instance set-a2 (p p))
                 )
           )
          ("Subgoal 6"
           :use ((:instance set-a4 (p p))
                 (:instance set-a4-1 (point p))
                 (:instance r-1*wa-1 (p p))
                 (:instance r-1*wa-1-1-suff (point p) (p (SET-A4-1-WITNESS P)))
                 (:instance wa-1-iff-wa10-or-wa11 (p (SET-A4-1-WITNESS P)))
                 )
           )
          ("Subgoal 5"
           :use ((:instance set-a6 (p p))
                 (:instance set-a6-1 (point p))
                 (:instance r-1*wa-1 (p p))
                 (:instance r-1*wa-1-1-suff (point p) (p (SET-A6-1-WITNESS P)))
                 (:instance wa-1-iff-wa10-or-wa11 (p (SET-A6-1-WITNESS P)))
                 )
           )
          ("Subgoal 4"
           :use ((:instance set-a8 (p p))
                 )
           )
          ("Subgoal 3"
           :use ((:instance set-a10 (p p))
                 (:instance set-a10-1 (point p))
                 (:instance r-1*wb-1 (p p))
                 (:instance r-1*wb-1-1-suff (point p) (p (SET-A10-1-WITNESS P)))
                 (:instance wb-1-iff-wb10-or-wb11 (p (SET-A10-1-WITNESS P)))
                 )
           )
          ("Subgoal 2"
           :use ((:instance set-a12 (p p))
                 (:instance set-a12-1 (point p))
                 (:instance r-1*wb-1 (p p))
                 (:instance r-1*wb-1-1-suff (point p) (p (SET-A12-1-WITNESS P)))
                 (:instance wb-1-iff-wb10-or-wb11 (p (SET-A12-1-WITNESS P)))
                 )
           )
          ("Subgoal 1"
           :use (:instance set-a14 (p p))
           )
          ))

(defthmd r-1-setas-iff-r-1-diff-s2-2
  (implies (r-1-diff-s2 p)
           (r-1-setas p))
  :hints (("Goal"
           :use ((:instance r-1-diff-s2 (p p))
                 (:instance r-1-setas (p p)))
           :cases ((r-1*m1 p)
                   (r-1*wa-1 p)
                   (r-1*wa-inv-1 p)
                   (r-1*wb-1 p)
                   (r-1*wb-inv-1 p))
           :in-theory nil
           )
          ("Subgoal 5"
           :use (:instance set-a2 (p p))
           )
          ("Subgoal 4"
           :use ((:instance r-1*wa-1 (p p))
                 (:instance r-1*wa-1-1 (point p))
                 (:instance wa-1-iff-wa10-or-wa11 (p (R-1*WA-1-1-WITNESS P)))
                 (:instance set-a4 (p p))
                 (:instance set-a4-1-suff (point p) (p (R-1*WA-1-1-WITNESS P)))
                 (:instance set-a6 (p p))
                 (:instance set-a6-1-suff (point p) (p (R-1*WA-1-1-WITNESS P)))
                 )
           )
          ("Subgoal 3"
           :use (:instance set-a8 (p p))
           )
          ("Subgoal 2"
           :use ((:instance r-1*wb-1 (p p))
                 (:instance r-1*wb-1-1 (point p))
                 (:instance wb-1-iff-wb10-or-wb11 (p (R-1*Wb-1-1-WITNESS P)))
                 (:instance set-a10 (p p))
                 (:instance set-a10-1-suff (point p) (p (R-1*Wb-1-1-WITNESS P)))
                 (:instance set-a12 (p p))
                 (:instance set-a12-1-suff (point p) (p (R-1*Wb-1-1-WITNESS P)))
                 )
           )
          ("Subgoal 1"
           :use (:instance set-a14 (p p))
           )
          ))

(defthmd r-1-setas-iff-r-1-diff
  (iff (r-1-diff-s2 p)
       (r-1-setas p)))

(defthmd s2-iff-setas
  (iff (s2-def-p p)
       (or (set-a1 p)
           (set-a2 p)
           (set-a3 p)
           (set-a4 p)
           (set-a5 p)
           (set-a6 p)
           (set-a7 p)
           (set-a8 p)
           (set-a9 p)
           (set-a10 p)
           (set-a11 p)
           (set-a12 p)
           (set-a13 p)
           (set-a14 p)))
  :hints (("Goal"
           :use ((:instance r-1-setas-iff-r-1-diff (p p))
                 (:instance s2-iff-diff-s2 (p p))
                 (:instance r-1-diff-s2 (p p))
                 (:instance r-1-setas (p p))
                 (:instance diff-s2 (p p))
                 (:instance set-a1 (p p))
                 (:instance set-a3 (p p))
                 (:instance set-a5 (p p))
                 (:instance set-a7 (p p))
                 (:instance wa-0-iff-wa00-or-wa01 (p p))
                 (:instance wb-0-iff-wb00-or-wb01 (p p))
                 (:instance set-a9 (p p))
                 (:instance set-a11 (p p))
                 (:instance set-a13 (p p))
                 )
           :in-theory nil
           )))

  -----

;; (defun-sk rot-a*set-e-1 (point)
;;   (exists p
;;           (and (s2-not-e p)
;;                (m-= (m-* (a-rotation (acl2-sqrt 2)) p)
;;                     point))))

;; (defun rot-a*set-e (p)
;;   (and (point-in-r3 p)
;;        (rot-a*set-e-1 p)))


  :hints (("Goal"
           :use ((:instance iff-s2-s2-e-or-witinv*s2-d-n-e (point p))
                 (:instance s2-not-d-n-s2-not-e (point p))
                 (:instance s2-d-p-equivalence-1)
                 (:instance diff-s2 (p p))
                 (:instance m0 (p p)))
           :in-theory nil
           )
          ("Subgoal 5"
           :use ((:instance set-a2 (p p))
                 (:instance wa-1-iff-wa10-or-wa11 (p (R-1*WA-1-1-WITNESS P))))
           )
          ))













--------------

(defun-sk exists-d-p (n point)
  (exists p
          (and (d-p p)
               (m-= (m-* (rotation-about-witness
                          (* n (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))
                          (point-on-s2-not-d))
                         p)
                    point))))

(defthmd exists-d-p=>
  (implies (exists-d-p n point)
           (and (d-p (exists-d-p-witness n point))
                (m-= (m-* (rotation-about-witness
                           (* n (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))
                           (point-on-s2-not-d))
                          (exists-d-p-witness n point))
                     point)))
  :hints (("goal"
           :in-theory (disable d-p point-on-s2-not-d rotation-about-witness)
           )))

(defun-sk efunc (point)
  (exists n
          (and (natp n)
               (exists-d-p n point))))

(defthmd efunc=>
  (implies (efunc point)
           (and (m-= (m-* (rotation-about-witness
                           (* (efunc-witness point)
                              (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))
                           (point-on-s2-not-d))
                          (exists-d-p-witness (efunc-witness point) point))
                     point)
                (natp (efunc-witness point))
                (d-p (exists-d-p-witness (efunc-witness point) point))))
  :hints (("goal"
           :in-theory (disable d-p point-on-s2-not-d rotation-about-witness)
           )))

(defun set-e-p (point)
  (and (point-in-r3 point)
       (efunc point)))

(defun-sk seq-witness*e-func (point)
  (exists p
          (and (set-e-p p)
               (m-= (m-* (rotation-about-witness
                          (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))
                          (point-on-s2-not-d))
                         p)
                    point))))

(defthmd seq-witness*e-func=>
  (implies (seq-witness*e-func point)
           (and (set-e-p (seq-witness*e-func-witness point))
                (m-= (m-* (rotation-about-witness
                           (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))
                           (point-on-s2-not-d))
                          (seq-witness*e-func-witness point))
                     point)))
  :hints (("goal"
           :in-theory (disable d-p point-on-s2-not-d rotation-about-witness efunc)
           )))

(defun rot-witness*e-func (point)
  (and (point-in-r3 point)
       (seq-witness*e-func point)))

(defun efunc-not-d (point)
  (and (set-e-p point)
       (not (d-p point))))

(defthmd seq-witness*e-func=>enotd-1
  (implies (natp n)
           (natp (+ n 1))))

(defthmd seq-witness*e-func=>enotd-2
  (implies (and (m-= (m-* rn1 y) z)
                (m-= (m-* r1 z) point))
           (m-= (m-* (m-* r1 rn1) y) point)))

(defthmd seq-witness*e-func=>enotd-3
  (implies (and (natp n)
                (realp x))
           (realp (* n x))))

(defthmd rot-witness*e-func=>e
  (implies (rot-witness*e-func point)
           (set-e-p point))
  :hints (("goal"
           :use ((:instance seq-witness*e-func=> (point point))
                 (:instance efunc=> (point (seq-witness*e-func-witness point)))
                 (:instance exists-d-p-suff
                            (n (+ (efunc-witness (seq-witness*e-func-witness point)) 1))
                            (point point)
                            (p (exists-d-p-witness
                                (efunc-witness (seq-witness*e-func-witness point))
                                (seq-witness*e-func-witness point))))
                 (:instance efunc-suff (point point) (n (+ (efunc-witness (seq-witness*e-func-witness point)) 1)))
                 (:instance seq-witness*e-func=>enotd-1
                            (n (efunc-witness (seq-witness*e-func-witness point))))
                 (:instance seq-witness*e-func=>enotd-2
                            (rn1 (rotation-about-witness
                                  (* (efunc-witness (seq-witness*e-func-witness point))
                                     (exists-in-interval-but-not-in-angle-sequence-witness
                                      0 (* 2 (acl2-pi))))
                                  (point-on-s2-not-d)))
                            (y (exists-d-p-witness (efunc-witness (seq-witness*e-func-witness point))
                                                   (seq-witness*e-func-witness point)))
                            (z (seq-witness*e-func-witness point))
                            (r1 (rotation-about-witness
                                 (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))
                                 (point-on-s2-not-d)))
                            (point point))
                 (:instance r-t1*r-t2=r-t1+t2
                            (angle1 (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))
                            (angle2 (* (efunc-witness (seq-witness*e-func-witness point))
                                       (exists-in-interval-but-not-in-angle-sequence-witness
                                        0 (* 2 (acl2-pi)))))
                            (u (point-on-s2-not-d)))
                 (:instance exists-point-on-s2-not-d-2)
                 (:instance s2-def-p (point (point-on-s2-not-d)))
                 (:instance point-on-s2-not-d-on-s2 (u (point-on-s2-not-d)))
                 (:instance witness-not-in-angle-sequence)
                 (:instance seq-witness*e-func=>enotd-3
                            (n (efunc-witness (seq-witness*e-func-witness point)))
                            (x (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))))
                 )
           :in-theory (disable rotation-about-witness d-p point-on-s2-not-d m-* exists-d-p efunc seq-witness*e-func
                               point-in-r3 point-in-r3-x1 point-in-r3-y1 point-in-r3-z1 efunc aref2 m-= s2-def-p
                               nth-angle-exists)
           )))

(defthmd rot-witness*e-func=>notd
  (implies (rot-witness*e-func point)
           (not (d-p point)))
  :hints (("goal"
           :use ((:instance seq-witness*e-func=> (point point))
                 (:instance efunc=> (point (seq-witness*e-func-witness point)))
                 (:instance exists-d-p-suff
                            (n (+ (efunc-witness (seq-witness*e-func-witness point)) 1))
                            (point point)
                            (p (exists-d-p-witness
                                (efunc-witness (seq-witness*e-func-witness point))
                                (seq-witness*e-func-witness point))))
                 (:instance seq-witness*e-func=>enotd-1
                            (n (efunc-witness (seq-witness*e-func-witness point))))
                 (:instance seq-witness*e-func=>enotd-2
                            (rn1 (rotation-about-witness
                                  (* (efunc-witness (seq-witness*e-func-witness point))
                                     (exists-in-interval-but-not-in-angle-sequence-witness
                                      0 (* 2 (acl2-pi))))
                                  (point-on-s2-not-d)))
                            (y (exists-d-p-witness (efunc-witness (seq-witness*e-func-witness point))
                                                   (seq-witness*e-func-witness point)))
                            (z (seq-witness*e-func-witness point))
                            (r1 (rotation-about-witness
                                 (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))
                                 (point-on-s2-not-d)))
                            (point point))
                 (:instance r-t1*r-t2=r-t1+t2
                            (angle1 (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))
                            (angle2 (* (efunc-witness (seq-witness*e-func-witness point))
                                       (exists-in-interval-but-not-in-angle-sequence-witness
                                        0 (* 2 (acl2-pi)))))
                            (u (point-on-s2-not-d)))
                 (:instance exists-point-on-s2-not-d-2)
                 (:instance s2-def-p (point (point-on-s2-not-d)))
                 (:instance point-on-s2-not-d-on-s2 (u (point-on-s2-not-d)))
                 (:instance witness-not-in-angle-sequence)
                 (:instance seq-witness*e-func=>enotd-3
                            (n (efunc-witness (seq-witness*e-func-witness point)))
                            (x (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))))
                 (:instance rot-angle-witness*p1!=p2
                            (p1 (exists-d-p-witness (efunc-witness (seq-witness*e-func-witness point))
                                                    (seq-witness*e-func-witness point)))
                            (p2 point)
                            (n (+ (efunc-witness (seq-witness*e-func-witness point))
                                  1)))
                 )
           :in-theory (disable rotation-about-witness d-p point-on-s2-not-d m-* exists-d-p efunc seq-witness*e-func
                               point-in-r3 point-in-r3-x1 point-in-r3-y1 point-in-r3-z1 efunc aref2 m-= s2-def-p
                               nth-angle-exists)
           )))

(defthmd rot-witness*e-func=>efunc-not-d
  (implies (rot-witness*e-func point)
           (efunc-not-d point))
  :hints (("goal"
           :use ((:instance rot-witness*e-func=>e)
                 (:instance rot-witness*e-func=>notd))
           :in-theory (disable rotation-about-witness d-p point-on-s2-not-d m-* exists-d-p efunc seq-witness*e-func
                               point-in-r3 point-in-r3-x1 point-in-r3-y1 point-in-r3-z1 efunc aref2 m-= s2-def-p
                               nth-angle-exists)
           )))

(encapsulate
  ()

  (local (include-book "arithmetic/top" :dir :system))

  (defthmd efunc-not-d=>rot-witness*e-func-1
    (implies (efunc-not-d point)
             (posp (efunc-witness point)))
    :hints (("goal"
             :use ((:instance efunc=> (point point))
                   (:instance diff-d-p-p=>d-p-p1 (p (exists-d-p-witness (efunc-witness point) point))
                              (p1 point))
                   (:instance rotation-a-witn-of0 (p (exists-d-p-witness (efunc-witness point) point))
                              (u (point-on-s2-not-d)))
                   (:instance exists-point-on-s2-not-d-2)
                   (:instance s2-def-p (point (point-on-s2-not-d)))
                   (:instance efunc-not-d (point point))
                   (:instance d-p (point (exists-d-p-witness (efunc-witness point) point)))
                   (:instance s2-def-p (point (exists-d-p-witness (efunc-witness point) point)))
                   )
             :in-theory (disable rotation-about-witness d-p point-on-s2-not-d m-* exists-d-p efunc seq-witness*e-func
                                 point-in-r3 point-in-r3-x1 point-in-r3-y1 point-in-r3-z1 efunc aref2 m-= s2-def-p
                                 nth-angle-exists exists-d-p m-=)
             )))
  )

(defthmd efunc-not-d=>rot-witness*e-func-2-1
  (implies (posp n)
           (natp (- n 1))))

(defthmd efunc-not-d=>rot-witness*e-func-2
  (implies (efunc-not-d point)
           (efunc (m-* (rotation-about-witness (* (+ -1 (efunc-witness point))
                                                  (exists-in-interval-but-not-in-angle-sequence-witness
                                                   0 (* 2 (acl2-pi))))
                                               (point-on-s2-not-d))
                       (exists-d-p-witness (efunc-witness point) point))))
  :hints (("goal"
           :use ((:instance efunc=> (point point))
                 (:instance set-e-p (point point))
                 (:instance efunc-not-d=>rot-witness*e-func-1 (point point))
                 (:instance exists-d-p-suff
                            (point (m-* (rotation-about-witness (* (+ -1 (efunc-witness point))
                                                                   (exists-in-interval-but-not-in-angle-sequence-witness
                                                                    0 (* 2 (acl2-pi))))
                                                                (point-on-s2-not-d))
                                        (exists-d-p-witness (efunc-witness point) point)))
                            (p (exists-d-p-witness (efunc-witness point) point))
                            (n (+ -1 (efunc-witness point))))
                 (:instance efunc-suff
                            (point (m-* (rotation-about-witness (* (+ -1 (efunc-witness point))
                                                                   (exists-in-interval-but-not-in-angle-sequence-witness
                                                                    0 (* 2 (acl2-pi))))
                                                                (point-on-s2-not-d))
                                        (exists-d-p-witness (efunc-witness point) point)))
                            (n (+ -1 (efunc-witness point))))
                 (:instance efunc-not-d=>rot-witness*e-func-2-1
                            (n (efunc-witness point)))
                 (:instance efunc-not-d (point point)))
           :in-theory nil
           )))

(defthmd efunc-not-d=>rot-witness*e-func-3-1
  (equal (m-* a b c)
         (m-* (m-* a b) c)))

(encapsulate
  ()

  (local (include-book "arithmetic/top" :dir :system))

  (defthmd efunc-not-d=>rot-witness*e-func-3
    (implies (and (efunc point)
                  (point-in-r3 point)
                  (realp (* (+ -1 (efunc-witness point))
                            (exists-in-interval-but-not-in-angle-sequence-witness
                             0 (* 2 (acl2-pi)))))
                  (not (d-p point)))
             (rot-witness*e-func point))
    :hints (("goal"
             :use ((:instance efunc-not-d=>rot-witness*e-func-3-1
                              (a (rotation-about-witness (exists-in-interval-but-not-in-angle-sequence-witness
                                                          0 (* 2 (acl2-pi)))
                                                         (point-on-s2-not-d)))
                              (b (rotation-about-witness (* (+ -1 (efunc-witness point))
                                                            (exists-in-interval-but-not-in-angle-sequence-witness
                                                             0 (* 2 (acl2-pi))))
                                                         (point-on-s2-not-d)))
                              (c (exists-d-p-witness (efunc-witness point)
                                                     point)))
                   (:instance seq-witness*e-func-suff
                              (p (m-* (rotation-about-witness (* (+ -1 (efunc-witness point))
                                                                 (exists-in-interval-but-not-in-angle-sequence-witness
                                                                  0 (* 2 (acl2-pi))))
                                                              (point-on-s2-not-d))
                                      (exists-d-p-witness (efunc-witness point) point)))
                              (point point))
                   (:instance rot-witness*e-func (point point))
                   (:instance efunc-not-d (point point))
                   (:instance efunc-not-d=>rot-witness*e-func-2 (point point))
                   (:instance efunc=> (point point))
                   (:instance r-t1*r-t2=r-t1+t2
                              (angle1 (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))
                              (angle2 (* (+ -1 (efunc-witness point))
                                         (exists-in-interval-but-not-in-angle-sequence-witness
                                          0 (* 2 (acl2-pi)))))
                              (u (point-on-s2-not-d)))
                   (:instance rot*p-on-s2 (p (exists-d-p-witness (efunc-witness point) point))
                              (rot (rotation-about-witness (* (+ -1 (efunc-witness point))
                                                              (exists-in-interval-but-not-in-angle-sequence-witness
                                                               0 (* 2 (acl2-pi))))
                                                           (point-on-s2-not-d))))
                   (:instance s2-def-p (point (m-* (rotation-about-witness (* (+ -1 (efunc-witness point))
                                                                              (exists-in-interval-but-not-in-angle-sequence-witness
                                                                               0 (* 2 (acl2-pi))))
                                                                           (point-on-s2-not-d))
                                                   (exists-d-p-witness (efunc-witness point)
                                                                       point))))
                   (:instance d-p (point (exists-d-p-witness (efunc-witness point) point)))
                   (:instance point-on-s2-not-d-on-s2 (u (point-on-s2-not-d)))
                   (:instance exists-point-on-s2-not-d-2)
                   (:instance s2-def-p (point (point-on-s2-not-d)))
                   (:instance witness-not-in-angle-sequence)
                   (:instance set-e-p (point (m-* (rotation-about-witness (* (+ -1 (efunc-witness point))
                                                                             (exists-in-interval-but-not-in-angle-sequence-witness
                                                                              0 (* 2 (acl2-pi))))
                                                                          (point-on-s2-not-d))
                                                  (exists-d-p-witness (efunc-witness point)
                                                                      point))))
                   (:instance r3-rotationp-r-theta (angle (* (+ -1 (efunc-witness point))
                                                             (exists-in-interval-but-not-in-angle-sequence-witness
                                                              0 (* 2 (acl2-pi))))))
                   )
             :in-theory(disable rotation-about-witness d-p point-on-s2-not-d m-* exists-d-p efunc seq-witness*e-func
                                point-in-r3 point-in-r3-x1 point-in-r3-y1 point-in-r3-z1 efunc aref2 m-= s2-def-p
                                nth-angle-exists exists-d-p m-= r3-rotationp)
             )))

  (defthmd efunc-not-d=>rot-witness*e-func
    (implies (efunc-not-d point)
             (rot-witness*e-func point))
    :hints (("goal"
             :use ((:instance efunc-not-d=>rot-witness*e-func-3 (point point))
                   (:instance efunc=> (point point))
                   (:instance witness-not-in-angle-sequence))
             :in-theory (disable efunc d-p rot-witness*e-func point-in-r3)
             )))
  )

(defthmd efunc-not-d-iff-rot-witness*e-func
  (iff (efunc-not-d point)
       (rot-witness*e-func point))
  :hints (("goal"
           :use ((:instance efunc-not-d=>rot-witness*e-func)
                 (:instance rot-witness*e-func=>efunc-not-d))
           )))

(encapsulate
  ()

  (local (include-book "arithmetic/top" :dir :system))

  (defthmd d-p=>set-e
    (implies (d-p point)
             (set-e-p point))
    :hints (("goal"
             :use ((:instance set-e-p (point point))
                   (:instance efunc-suff (point point) (n 0))
                   (:instance d-p (point point))
                   (:instance s2-def-p (point point))
                   (:instance rotation-a-witn-of0 (p point)
                              (u (point-on-s2-not-d)))
                   (:instance exists-point-on-s2-not-d-2)
                   (:instance s2-def-p (point (point-on-s2-not-d)))
                   (:instance exists-d-p-suff (point point) (n 0) (p point)))
             :in-theory(disable rotation-about-witness d-p point-on-s2-not-d m-* exists-d-p efunc seq-witness*e-func
                                point-in-r3 point-in-r3-x1 point-in-r3-y1 point-in-r3-z1 efunc aref2 m-= s2-def-p
                                nth-angle-exists exists-d-p m-= r3-rotationp)
             )))
  )

(defun s2-not-e (point)
  (and (s2-def-p point)
       (not (set-e-p point))))

(defthmd s2-not-e=>s2-not-d
  (implies (s2-not-e point)
           (s2-d-p point))
  :hints (("goal"
           :use ((:instance d-p=>set-e (point point)))
           :in-theory (disable s2-def-p d-p set-e-p)
           )))

(defun s2-not-d-n-s2-not-e (point)
  (and (s2-d-p point)
       (s2-not-e point)))

(defthmd s2-not-e=>s2-not-d-n-s2-not-e
  (iff (s2-not-e point)
       (s2-not-d-n-s2-not-e point))
  :hints (("goal"
           :use ((:instance s2-not-e=>s2-not-d))
           )))

(defun s2-d-p-n-set-e (point)
  (and (s2-d-p point)
       (set-e-p point)))

(encapsulate
  ()

  (local (include-book "arithmetic/top" :dir :system))

  (defthmd set-e-p=>s2-def-p
    (implies (set-e-p point)
             (s2-def-p point))
    :hints (("goal"
             :use ((:instance s2-def-p-p=>p1
                              (p (m-* (rotation-about-witness
                                       (* (efunc-witness point)
                                          (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))
                                       (point-on-s2-not-d))
                                      (exists-d-p-witness (efunc-witness point) point)))
                              (p1 point))
                   (:instance set-e-p (point point))
                   (:instance efunc (point point))
                   (:instance exists-d-p (n (efunc-witness point))
                              (point point))
                   (:instance d-p (point (exists-d-p-witness (efunc-witness point) point)))
                   (:instance rot*p-on-s2 (p (exists-d-p-witness (efunc-witness point) point))
                              (rot (rotation-about-witness (* (efunc-witness point)
                                                              (exists-in-interval-but-not-in-angle-sequence-witness
                                                               0 (* 2 (acl2-pi))))
                                                           (point-on-s2-not-d))))
                   (:instance r3-rotationp-r-theta (angle (* (efunc-witness point)
                                                             (exists-in-interval-but-not-in-angle-sequence-witness
                                                              0 (* 2 (acl2-pi))))))
                   (:instance witness-not-in-angle-sequence)
                   )
             :in-theory (disable rotation-about-witness d-p point-on-s2-not-d m-* exists-d-p efunc seq-witness*e-func point-in-r3 point-in-r3-x1 point-in-r3-y1 point-in-r3-z1 efunc aref2 nth-angle-exists exists-d-p m-= r3-rotationp)
             )))
  )


(defthmd enotd=>s2-d-p-n-set-e
  (iff (efunc-not-d point)
       (s2-d-p-n-set-e point))
  :hints (("goal"
           :use ((:instance s2-d-p (point point))
                 (:instance set-e-p=>s2-def-p (point point)))
           :in-theory (disable set-e-p d-p s2-d-p s2-def-p)
           )))

(defun-sk wit-inv*s2-d-p-n-set-e-1 (point)
  (exists p
          (and (s2-d-p-n-set-e p)
               (m-= (m-* (rotation-about-witness
                          (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))
                          (point-on-s2-not-d)) p)
                    point))))

(defun wit-inv*s2-d-p-n-set-e-p (point)
  (and (point-in-r3 point)
       (wit-inv*s2-d-p-n-set-e-1 point)))


(defthmd set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-1-1
  (implies (and (point-in-r3 p1)
                (r3-matrixp rot))
           (point-in-r3 (m-* rot p1)))
  :hints (("goal"
           :use ((:instance array2p-alist2p (name :fake-name) (l rot))
                 (:instance array2p-alist2p (name :fake-name) (l p1))
                 (:instance aref2-m-* (name :fake-name)
                            (m1 rot) (m2 p1) (i 0) (j 0))
                 (:instance aref2-m-* (name :fake-name)
                            (m1 rot) (m2 p1) (i 1) (j 0))
                 (:instance aref2-m-* (name :fake-name)
                            (m1 rot) (m2 p1) (i 2) (j 0)))
           :in-theory (e/d (m-* array2p header dimensions) (aref2-m-* array2p-alist2p r3-m-determinant r3-m-inverse m-trans))
           )))

(encapsulate
  ()

  (local (include-book "arithmetic/top" :dir :system))

  (defthmd set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-1
    (implies (set-e-p point)
             (wit-inv*s2-d-p-n-set-e-p point))
    :hints (("goal"
             :use ((:instance wit-inv*s2-d-p-n-set-e-p (point point))
                   (:instance wit-inv*s2-d-p-n-set-e-1-suff
                              (point point)
                              (p (m-* (rotation-about-witness
                                       (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))
                                       (point-on-s2-not-d)) point)))
                   (:instance enotd=>s2-d-p-n-set-e
                              (point (m-* (rotation-about-witness
                                           (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))
                                           (point-on-s2-not-d)) point)))
                   (:instance efunc-not-d-iff-rot-witness*e-func
                              (point (m-* (rotation-about-witness
                                           (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))
                                           (point-on-s2-not-d)) point)))
                   (:instance rot-witness*e-func
                              (point (m-* (rotation-about-witness
                                           (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))
                                           (point-on-s2-not-d)) point)))
                   (:instance seq-witness*e-func-suff (p point)
                              (point (m-* (rotation-about-witness
                                           (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))
                                           (point-on-s2-not-d)) point)))
                   (:instance set-e-p (point point))
                   (:instance set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-1-1
                              (p1 point)
                              (rot (rotation-about-witness
                                    (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))
                                    (point-on-s2-not-d))))
                   (:instance r3-rotationp-r-theta (angle (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))))
                   (:instance witness-not-in-angle-sequence)
                   (:instance r-t1*r-t2=r-t1+t2
                              (angle1 (- (exists-in-interval-but-not-in-angle-sequence-witness
                                          0 (* 2 (acl2-pi)))))
                              (angle2 (exists-in-interval-but-not-in-angle-sequence-witness
                                       0 (* 2 (acl2-pi))))
                              (u (point-on-s2-not-d)))
                   (:instance exists-point-on-s2-not-d-2)
                   (:instance s2-def-p (point (point-on-s2-not-d)))
                   (:instance point-on-s2-not-d-on-s2 (u (point-on-s2-not-d)))
                   (:instance rotation-a-witn-of0 (p point)
                              (u (point-on-s2-not-d)))
                   (:instance r3-rotationp (m (rotation-about-witness
                                               (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))
                                               (point-on-s2-not-d))))
                   )
             :in-theory (disable r3-m-determinant r3-matrixp r3-m-inverse
                                 m-trans rotation-about-witness d-p point-on-s2-not-d m-* exists-d-p efunc seq-witness*e-func point-in-r3 point-in-r3-x1 point-in-r3-y1 point-in-r3-z1 efunc aref2 nth-angle-exists exists-d-p m-= r3-rotationp)
             )))
  )

(encapsulate
  ()

  (local (include-book "arithmetic/top" :dir :system))

  (defthmd set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-2-1
    (implies (and (m-= (m-* rn dpp) seq)
                  (m-= (m-* r1 seq) witn)
                  (m-= (m-* r-1 witn) point))
             (m-= (m-* (m-* r-1 r1) rn dpp) point)))

  (defthmd set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-2-2
    (implies (and (natp n)
                  (realp x))
             (realp (* n x))))

  (defthmd set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-2-3-1
    (implies (and (m-= (m-* r-1 r1) r0)
                  (m-= (m-* (m-* r-1 r1) rnx dpp) point)
                  (m-= (m-* r0 rnx) rnx1))
             (m-= (m-* rnx1 dpp) point)))

  (defthmd set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-2-3
    (implies
     (and (natp (efunc-witness
                 (seq-witness*e-func-witness (wit-inv*s2-d-p-n-set-e-1-witness point))))
          (m-=
           (m-*
            (m-* (rotation-about-witness (- (exists-in-interval-but-not-in-angle-sequence-witness
                                             0 (* 2 (acl2-pi))))
                                         (point-on-s2-not-d))
                 (rotation-about-witness (exists-in-interval-but-not-in-angle-sequence-witness
                                          0 (* 2 (acl2-pi)))
                                         (point-on-s2-not-d)))
            (rotation-about-witness
             (*
              (efunc-witness
               (seq-witness*e-func-witness (wit-inv*s2-d-p-n-set-e-1-witness point)))
              (exists-in-interval-but-not-in-angle-sequence-witness
               0 (* 2 (acl2-pi))))
             (point-on-s2-not-d))
            (exists-d-p-witness
             (efunc-witness
              (seq-witness*e-func-witness (wit-inv*s2-d-p-n-set-e-1-witness point)))
             (seq-witness*e-func-witness (wit-inv*s2-d-p-n-set-e-1-witness point))))
           point))
     (m-= (m-* (rotation-about-witness
                (*
                 (efunc-witness
                  (seq-witness*e-func-witness (wit-inv*s2-d-p-n-set-e-1-witness point)))
                 (exists-in-interval-but-not-in-angle-sequence-witness
                  0 (* 2 (acl2-pi))))
                (point-on-s2-not-d))
               (exists-d-p-witness
                (efunc-witness
                 (seq-witness*e-func-witness (wit-inv*s2-d-p-n-set-e-1-witness point)))
                (seq-witness*e-func-witness (wit-inv*s2-d-p-n-set-e-1-witness point))))
          point))
    :hints (("goal"
             :use ((:instance r-t1*r-t2=r-t1+t2
                              (angle1 (- (exists-in-interval-but-not-in-angle-sequence-witness
                                          0 (* 2 (acl2-pi)))))
                              (angle2 (exists-in-interval-but-not-in-angle-sequence-witness
                                       0 (* 2 (acl2-pi))))
                              (u (point-on-s2-not-d)))
                   (:instance r-t1*r-t2=r-t1+t2
                              (angle1 0)
                              (angle2 (*
                                       (efunc-witness
                                        (seq-witness*e-func-witness (wit-inv*s2-d-p-n-set-e-1-witness point)))
                                       (exists-in-interval-but-not-in-angle-sequence-witness
                                        0 (* 2 (acl2-pi)))))
                              (u (point-on-s2-not-d)))
                   (:instance witness-not-in-angle-sequence)
                   (:instance exists-point-on-s2-not-d-2)
                   (:instance s2-def-p (point (point-on-s2-not-d)))
                   (:instance point-on-s2-not-d-on-s2 (u (point-on-s2-not-d)))
                   (:instance set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-2-2
                              (n (efunc-witness
                                  (seq-witness*e-func-witness (wit-inv*s2-d-p-n-set-e-1-witness point))))
                              (x (exists-in-interval-but-not-in-angle-sequence-witness
                                  0 (* 2 (acl2-pi)))))
                   (:instance efunc-not-d=>rot-witness*e-func-3-1
                              (a (rotation-about-witness 0 (point-on-s2-not-d)))
                              (b (rotation-about-witness
                                  (*
                                   (efunc-witness
                                    (seq-witness*e-func-witness (wit-inv*s2-d-p-n-set-e-1-witness point)))
                                   (exists-in-interval-but-not-in-angle-sequence-witness
                                    0 (* 2 (acl2-pi))))
                                  (point-on-s2-not-d)))
                              (c (exists-d-p-witness
                                  (efunc-witness
                                   (seq-witness*e-func-witness (wit-inv*s2-d-p-n-set-e-1-witness point)))
                                  (seq-witness*e-func-witness (wit-inv*s2-d-p-n-set-e-1-witness point)))))
                   (:instance set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-2-3-1
                              (r-1 (rotation-about-witness (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                               0 (* 2 (acl2-pi))))
                                                           (point-on-s2-not-d)))
                              (r1 (rotation-about-witness (exists-in-interval-but-not-in-angle-sequence-witness
                                                           0 (* 2 (acl2-pi)))
                                                          (point-on-s2-not-d)))
                              (point point)
                              (r0 (rotation-about-witness 0 (point-on-s2-not-d)))
                              (rnx (rotation-about-witness
                                    (* (efunc-witness (seq-witness*e-func-witness
                                                       (wit-inv*s2-d-p-n-set-e-1-witness point)))
                                       (exists-in-interval-but-not-in-angle-sequence-witness
                                        0 (* 2 (acl2-pi))))
                                    (point-on-s2-not-d)))
                              (rnx1 (rotation-about-witness
                                     (* (efunc-witness (seq-witness*e-func-witness
                                                        (wit-inv*s2-d-p-n-set-e-1-witness point)))
                                        (exists-in-interval-but-not-in-angle-sequence-witness
                                         0 (* 2 (acl2-pi))))
                                     (point-on-s2-not-d)))
                              (dpp (exists-d-p-witness
                                    (efunc-witness
                                     (seq-witness*e-func-witness (wit-inv*s2-d-p-n-set-e-1-witness point)))
                                    (seq-witness*e-func-witness (wit-inv*s2-d-p-n-set-e-1-witness point)))))
                   )
             :in-theory (disable r3-m-determinant r3-matrixp r3-m-inverse m-trans rotation-about-witness d-p point-on-s2-not-d m-* exists-d-p efunc seq-witness*e-func point-in-r3 point-in-r3-x1 point-in-r3-y1 point-in-r3-z1 efunc aref2 nth-angle-exists exists-d-p r3-rotationp efunc-not-d s2-d-p-n-set-e wit-inv*s2-d-p-n-set-e-p wit-inv*s2-d-p-n-set-e-1 rot-witness*e-func seq-witness*e-func set-e-p aref2 s2-def-p aref2))
            )))

(defthmd set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-2
  (implies (wit-inv*s2-d-p-n-set-e-p point)
           (set-e-p point))
  :hints (("goal"
           :use ((:instance wit-inv*s2-d-p-n-set-e-p (point point))
                 (:instance wit-inv*s2-d-p-n-set-e-1 (point point))
                 (:instance enotd=>s2-d-p-n-set-e (point (wit-inv*s2-d-p-n-set-e-1-witness point)))
                 (:instance efunc-not-d-iff-rot-witness*e-func (point (wit-inv*s2-d-p-n-set-e-1-witness point)))
                 (:instance rot-witness*e-func (point (wit-inv*s2-d-p-n-set-e-1-witness point)))
                 (:instance seq-witness*e-func (point (wit-inv*s2-d-p-n-set-e-1-witness point)))
                 (:instance set-e-p (point (seq-witness*e-func-witness (wit-inv*s2-d-p-n-set-e-1-witness point))))
                 (:instance efunc=> (point (seq-witness*e-func-witness (wit-inv*s2-d-p-n-set-e-1-witness point))))
                 (:instance set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-2-1
                            (rn (rotation-about-witness
                                 (*
                                  (efunc-witness
                                   (seq-witness*e-func-witness (wit-inv*s2-d-p-n-set-e-1-witness point)))
                                  (exists-in-interval-but-not-in-angle-sequence-witness
                                   0 (* 2 (acl2-pi))))
                                 (point-on-s2-not-d)))
                            (dpp (exists-d-p-witness
                                  (efunc-witness
                                   (seq-witness*e-func-witness (wit-inv*s2-d-p-n-set-e-1-witness point)))
                                  (seq-witness*e-func-witness (wit-inv*s2-d-p-n-set-e-1-witness point))))
                            (r-1 (rotation-about-witness (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                             0 (* 2 (acl2-pi))))
                                                         (point-on-s2-not-d)))
                            (r1 (rotation-about-witness (exists-in-interval-but-not-in-angle-sequence-witness
                                                         0 (* 2 (acl2-pi)))
                                                        (point-on-s2-not-d)))
                            (point point)
                            (seq (seq-witness*e-func-witness (wit-inv*s2-d-p-n-set-e-1-witness point)))
                            (witn (wit-inv*s2-d-p-n-set-e-1-witness point))
                            )
                 (:instance r-t1*r-t2=r-t1+t2
                            (angle1 (- (exists-in-interval-but-not-in-angle-sequence-witness
                                        0 (* 2 (acl2-pi)))))
                            (angle2 (exists-in-interval-but-not-in-angle-sequence-witness
                                     0 (* 2 (acl2-pi))))
                            (u (point-on-s2-not-d)))
                 (:instance exists-point-on-s2-not-d-2)
                 (:instance s2-def-p (point (point-on-s2-not-d)))
                 (:instance point-on-s2-not-d-on-s2 (u (point-on-s2-not-d)))
                 (:instance witness-not-in-angle-sequence)
                 (:instance set-e-p (point (seq-witness*e-func-witness (wit-inv*s2-d-p-n-set-e-1-witness point))))
                 (:instance r-t1*r-t2=r-t1+t2
                            (angle1 0)
                            (angle2 (*
                                     (efunc-witness
                                      (seq-witness*e-func-witness (wit-inv*s2-d-p-n-set-e-1-witness point)))
                                     (exists-in-interval-but-not-in-angle-sequence-witness
                                      0 (* 2 (acl2-pi)))))
                            (u (point-on-s2-not-d)))
                 (:instance efunc-suff (point point)
                            (n (efunc-witness
                                (seq-witness*e-func-witness (wit-inv*s2-d-p-n-set-e-1-witness point))))
                            )
                 (:instance set-e-p (point point))
                 (:instance exists-d-p-suff (n (efunc-witness
                                                (seq-witness*e-func-witness (wit-inv*s2-d-p-n-set-e-1-witness point))))
                            (point point)
                            (p (exists-d-p-witness
                                (efunc-witness
                                 (seq-witness*e-func-witness (wit-inv*s2-d-p-n-set-e-1-witness point)))
                                (seq-witness*e-func-witness (wit-inv*s2-d-p-n-set-e-1-witness point)))))
                 (:instance set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-2-2
                            (n (efunc-witness
                                (seq-witness*e-func-witness (wit-inv*s2-d-p-n-set-e-1-witness point))))
                            (x (exists-in-interval-but-not-in-angle-sequence-witness
                                0 (* 2 (acl2-pi)))))
                 (:instance set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-2-3)
                 )
           :in-theory nil
           ))
  )

(defthmd set-e-p-iff-wit-inv*s2-d-p-n-set-e-p
  (iff (wit-inv*s2-d-p-n-set-e-p point)
       (set-e-p point)))






---------------------

(defthmd efunc-not-d-iff-rot-witness*e-func
  (iff (efunc-not-d point)
       (rot-witness*e-func point))
  :hints (("Goal"
;:use ((:instance efunc-not-d=>rot-witness*e-func))
;(:instance rot-witness*e-func=>efunc-not-d))
           ))
  )

---------------------







----------------------------------------------

(defthmd rot-angle-witness*p1!=p2-intmn-1
  (implies (m-= m n)
           (m-= (m-* p m) (m-* p n))))

(defthmd rot-angle-witness*p1!=p2-intmn-2
  (implies (and (integerp m)
                (posp n))
           (REALP (* (+ M N)
                     (EXISTS-IN-INTERVAL-BUT-NOT-IN-ANGLE-SEQUENCE-WITNESS
                      0 (* 2 (ACL2-PI))))))
  :hints (("Goal"
           :use ((:instance witness-not-in-angle-sequence))
           )))

(defthmd rot-angle-witness*p1!=p2-intmn-3
  (equal (m-* p (m-* m1 m2))
         (m-* (m-* p m1) m2)))

(defthmd rot-angle-witness*p1!=p2-intmn-4
  (implies (m-= x y)
           (m-= (m-* x p1) (m-* y p1))))

(encapsulate
  ()

  (local (include-book "arithmetic/top" :dir :system))

  (defthmd rot-angle-witness*p1!=p2-intmn-5
    (equal (ROTATION-ABOUT-WITNESS (+ (* (- M)
                                         (EXISTS-IN-INTERVAL-BUT-NOT-IN-ANGLE-SEQUENCE-WITNESS
                                          0 (* 2 (ACL2-PI))))
                                      (* (+ M N)
                                         (EXISTS-IN-INTERVAL-BUT-NOT-IN-ANGLE-SEQUENCE-WITNESS
                                          0 (* 2 (ACL2-PI)))))
                                   (POINT-ON-S2-NOT-D))
           (ROTATION-ABOUT-WITNESS (* N
                                      (EXISTS-IN-INTERVAL-BUT-NOT-IN-ANGLE-SEQUENCE-WITNESS
                                       0 (* 2 (ACL2-PI))))
                                   (POINT-ON-S2-NOT-D)))
    :hints (("Goal"
             :in-theory (disable rotation-about-witness)
             )))
  )


(defthmd rot-angle-witness*p1!=p2-intmn-6
  (implies (and (d-p p1)
                (d-p p2)
                (integerp m)
                (posp n))
           (m-= (m-*
                 (rotation-about-witness (* (- m) (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d))
                 (m-* (rotation-about-witness (* (+ m n) (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d))
                      p1))
                (m-* (rotation-about-witness (* n (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d)) p1)))
  :hints (("Goal"
           :use ((:instance rot-angle-witness*p1!=p2-intmn-3
                            (p (rotation-about-witness (* (- m) (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d)))
                            (m1 (rotation-about-witness (* (+ m n) (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d)))
                            (m2 p1))
                 (:instance rot-angle-witness*p1!=p2-intmn-5)
                 (:instance point-on-s2-not-d-on-s2 (u (point-on-s2-not-d)))
                 (:instance exists-point-on-s2-not-d-2)
                 (:instance r-t1*r-t2=r-t1+t2
                            (angle1 (* (- m) (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))))
                            (angle2 (* (+ m n) (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))))
                            (u (point-on-s2-not-d)))
                 (:instance witness-not-in-angle-sequence)
                 (:instance s2-def-p (point (point-on-s2-not-d)))
                 (:instance rot-angle-witness*p1!=p2-intmn-2 (m m) (n n))
                 (:instance rot-angle-witness*p1!=p2-intmn-4
                            (x (M-* (ROTATION-ABOUT-WITNESS (* (- M)
                                                               (EXISTS-IN-INTERVAL-BUT-NOT-IN-ANGLE-SEQUENCE-WITNESS
                                                                0 (* 2 (ACL2-PI))))
                                                            (POINT-ON-S2-NOT-D))
                                    (ROTATION-ABOUT-WITNESS (* (+ M N)
                                                               (EXISTS-IN-INTERVAL-BUT-NOT-IN-ANGLE-SEQUENCE-WITNESS
                                                                0 (* 2 (ACL2-PI))))
                                                            (POINT-ON-S2-NOT-D))))
                            (y (ROTATION-ABOUT-WITNESS (+ (* (- M)
                                                             (EXISTS-IN-INTERVAL-BUT-NOT-IN-ANGLE-SEQUENCE-WITNESS
                                                              0 (* 2 (ACL2-PI))))
                                                          (* (+ M N)
                                                             (EXISTS-IN-INTERVAL-BUT-NOT-IN-ANGLE-SEQUENCE-WITNESS
                                                              0 (* 2 (ACL2-PI)))))
                                                       (POINT-ON-S2-NOT-D)))
                            (p1 p1))
                 )
           :in-theory nil
           )))

(defthmd rot-angle-witness*p1!=p2-intmn-7
  (implies (and (m-= x y)
                (m-= y p2))
           (m-= x p2)))

(encapsulate
  ()

  (local (include-book "arithmetic/top" :dir :system))
  (defthmd rot-angle-witness*p1!=p2-intmn-8
    (equal
     (ROTATION-ABOUT-WITNESS (+ (* (- M)
                                   (EXISTS-IN-INTERVAL-BUT-NOT-IN-ANGLE-SEQUENCE-WITNESS
                                    0 (* 2 (ACL2-PI))))
                                (* M
                                   (EXISTS-IN-INTERVAL-BUT-NOT-IN-ANGLE-SEQUENCE-WITNESS
                                    0 (* 2 (ACL2-PI)))))
                             (POINT-ON-S2-NOT-D))
     (rotation-about-witness 0 (point-on-s2-not-d))))
  )

(defthmd rot-angle-witness*p1!=p2-intmn-9
  (implies (and (d-p p1)
                (d-p p2)
                (integerp m)
                (posp n))
           (m-= (m-*
                 (rotation-about-witness (* (- m) (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d))
                 (m-* (rotation-about-witness (* m (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d))
                      p2))
                p2))
  :hints (("Goal"
           :use ((:instance rot-angle-witness*p1!=p2-intmn-3
                            (p (rotation-about-witness (* (- m) (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d)))
                            (m1 (rotation-about-witness (* m (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d)))
                            (m2 p2))
                 (:instance rot-angle-witness*p1!=p2-intmn-7 (x (M-* (M-* (ROTATION-ABOUT-WITNESS (* (- M)
                                                                                                     (EXISTS-IN-INTERVAL-BUT-NOT-IN-ANGLE-SEQUENCE-WITNESS
                                                                                                      0 (* 2 (ACL2-PI))))
                                                                                                  (POINT-ON-S2-NOT-D))
                                                                          (ROTATION-ABOUT-WITNESS (* M
                                                                                                     (EXISTS-IN-INTERVAL-BUT-NOT-IN-ANGLE-SEQUENCE-WITNESS
                                                                                                      0 (* 2 (ACL2-PI))))
                                                                                                  (POINT-ON-S2-NOT-D)))
                                                                     P2))
                            (y (M-* (ROTATION-ABOUT-WITNESS (+ (* (- M)
                                                                  (EXISTS-IN-INTERVAL-BUT-NOT-IN-ANGLE-SEQUENCE-WITNESS
                                                                   0 (* 2 (ACL2-PI))))
                                                               (* M
                                                                  (EXISTS-IN-INTERVAL-BUT-NOT-IN-ANGLE-SEQUENCE-WITNESS
                                                                   0 (* 2 (ACL2-PI)))))
                                                            (POINT-ON-S2-NOT-D))
                                    P2))
                            (p2 p2))
                 (:instance point-on-s2-not-d-on-s2 (u (point-on-s2-not-d)))
                 (:instance exists-point-on-s2-not-d-2)
                 (:instance r-t1*r-t2=r-t1+t2
                            (angle1 (* (- m) (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))))
                            (angle2 (* m (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))))
                            (u (point-on-s2-not-d)))
                 (:instance witness-not-in-angle-sequence)
                 (:instance s2-def-p (point (point-on-s2-not-d)))
                 (:instance rot-angle-witness*p1!=p2-intmn-4
                            (x (M-* (ROTATION-ABOUT-WITNESS (* (- M)
                                                               (EXISTS-IN-INTERVAL-BUT-NOT-IN-ANGLE-SEQUENCE-WITNESS
                                                                0 (* 2 (ACL2-PI))))
                                                            (POINT-ON-S2-NOT-D))
                                    (ROTATION-ABOUT-WITNESS (* m
                                                               (EXISTS-IN-INTERVAL-BUT-NOT-IN-ANGLE-SEQUENCE-WITNESS
                                                                0 (* 2 (ACL2-PI))))
                                                            (POINT-ON-S2-NOT-D))))
                            (y (ROTATION-ABOUT-WITNESS (+ (* (- M)
                                                             (EXISTS-IN-INTERVAL-BUT-NOT-IN-ANGLE-SEQUENCE-WITNESS
                                                              0 (* 2 (ACL2-PI))))
                                                          (* m
                                                             (EXISTS-IN-INTERVAL-BUT-NOT-IN-ANGLE-SEQUENCE-WITNESS
                                                              0 (* 2 (ACL2-PI)))))
                                                       (POINT-ON-S2-NOT-D)))
                            (p1 p2))
                 (:instance rot-angle-witness*p1!=p2-intmn-8)
                 (:instance rotation-a-witn-of0 (u (point-on-s2-not-d)) (p p2))
                 (:instance d-p (point p2))
                 (:instance s2-def-p (point p2))
                 )
           :in-theory nil
           )))

(defthmd rot-angle-witness*p1!=p2-intmn
  (implies (and (d-p p1)
                (d-p p2)
                (integerp m)
                (posp n))
           (not (m-= (m-*
                      (rotation-about-witness (* (+ m n) (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d))
                      p1)
                     (m-* (rotation-about-witness (* m (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d)) p2))))
  :hints (("goal"
           :use ((:instance rot-angle-witness*p1!=p2-intmn-1
                            (m (m-* (rotation-about-witness (* (+ m n) (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d)) p1))
                            (p (rotation-about-witness (* (- m) (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d)))
                            (n (rotation-about-witness (* m (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d))))
                 (:instance rot-angle-witness*p1!=p2 (p1 p1) (p2 p2) (n n))
                 (:instance rot-angle-witness*p1!=p2-intmn-9)
                 (:instance rot-angle-witness*p1!=p2-intmn-6)
                 )
           :in-theory (disable m-= d-p m-* nth-angle-exists rotation-about-witness point-in-r3 aref2 point-on-s2-not-d)
           )))

(encapsulate
  ()

  (local (include-book "arithmetic/top" :dir :system))

  (defthmd rot-angle-witness*p1!=p2-pospmn
    (implies (and (d-p p1)
                  (d-p p2)
                  (posp m)
                  (< m n)
                  (posp n))
             (not (m-= (m-*
                        (rotation-about-witness (* n (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d))
                        p1)
                       (m-* (rotation-about-witness (* m (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d)) p2))))
    :hints (("Goal"
             :use ((:instance rot-angle-witness*p1!=p2-intmn (p1 p1) (p2 p2) (m m) (n (- n m))))
             :in-theory (disable m-= d-p m-* nth-angle-exists rotation-about-witness point-in-r3 aref2 point-on-s2-not-d)
             )))
  )














---------------------

(encapsulate
  ()

  (local (include-book "arithmetic/top" :dir :system))

  (defthm p1p2-n-p-seq-lemma*1/2.2-1
    (IMPLIES (AND (NOT (ZP N))
                  (NOT (POSP (+ -1 N)))
                  (POSP N))
             (equal n 1))
    :rule-classes nil)

  (defthmd p1p2-n-p-seq-lemma*1/2.2-2
    (IMPLIES (AND (NOT (ZP N))
                  (NOT (POSP (+ -1 N)))
                  (POSP N))
             (EQUAL (NTH (+ -1 N) (P1P2-N-P-SEQ N))
                    (NTH 0 (P1P2-N-P-SEQ-I N)))))
  )

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd p1p2-n-p-seq-lemma-1
    (implies (posp n)
             (realp (cadar (p1p2-n-p-seq-i n)))))

  (defthmd p1p2-n-p-seq-2-len
    (implies (natp n)
             (equal (len (p1p2-n-p-seq-2 n)) n)))
  )

(defthmd p1p2-n-p-seq-lemma-2
  (implies (and (posp n)
                (equal (append a b) c)
                (equal (len a) (- n 1)))
           (equal (nth (- n 1) c)
                  (nth 0 b))))

(defthmd p1p2-n-p-seq-lemma-3
  (implies (posp n)
           (equal (p1p2-n-p-seq-2 n)
                  (append (p1p2-n-p-seq-2 (- n 1)) (p1p2-n-p-seq-i n))))
  :hints (("Goal"
           :in-theory (disable p1p2-n-p-seq-i)
           )))

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd p1p2-n-p-seq-lemma
    (implies (posp n)
             (equal (nth (- n 1) (p1p2-n-p-seq n))
                    (nth 0 (p1p2-n-p-seq-i n))))
    :hints (("Goal"
             :in-theory (disable P1P2-N-P-SEQ-i)
             :induct (P1P2-N-P-SEQ-2 N)
             )
            ("Subgoal *1/2"
             :in-theory nil
             )
            ("Subgoal *1/2.1"
             :use ((:instance p1p2-n-p-seq-lemma-2 (n n)
                              (a (p1p2-n-p-seq-2 (- n 1)))
                              (b (p1p2-n-p-seq-i n))
                              (c (p1p2-n-p-seq-2 n)))
                   (:instance p1p2-n-p-seq-2-len (n (- n 1)))
                   (:instance p1p2-n-p-seq-lemma-3
                              (n n)))
             :in-theory (e/d (p1p2-n-p-seq natp) (P1P2-N-P-SEQ-i))
             )
            ("Subgoal *1/2.2"
             :use (:instance p1p2-n-p-seq-lemma*1/2.2-2)
             )
            ))
  )

(defthmd realp-pos-p1p2-n-p-sequence
  (implies (posp n)
           (realp (cadr (P1P2-N-P-SEQUENCE N))))
  :hints (("Goal"
           :use ((:instance p1p2-n-p-seq-lemma (n n))
                 (:instance p1p2-n-p-seq-lemma-1 (n n)))
           :in-theory (disable p1p2-n-p-seq-i)
           )))

(encapsulate
  ()

  (local (include-book "arithmetic/top" :dir :system))

  (defthm p1p2-n-seq-lemma*1/2.2-1
    (IMPLIES (AND (NOT (ZP N))
                  (NOT (POSP (+ -1 N)))
                  (POSP N))
             (equal n 1))
    :rule-classes nil)

  (defthmd p1p2-n-seq-lemma*1/2.2-2
    (IMPLIES (AND (NOT (ZP N))
                  (NOT (POSP (+ -1 N)))
                  (POSP N))
             (EQUAL (NTH (+ -1 N) (P1P2-N-SEQ N))
                    (NTH 0 (P1P2-N-SEQ-I N)))))
  )

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd p1p2-n-seq-lemma-1
    (implies (posp n)
             (realp (cadar (p1p2-n-seq-i n)))))

  (defthmd p1p2-n-seq-2-len
    (implies (natp n)
             (equal (len (p1p2-n-seq-2 n)) n)))
  )

(defthmd p1p2-n-seq-lemma-3
  (implies (posp n)
           (equal (p1p2-n-seq-2 n)
                  (append (p1p2-n-seq-2 (- n 1)) (p1p2-n-seq-i n))))
  :hints (("Goal"
           :in-theory (disable p1p2-n-seq-i)
           )))

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd p1p2-n-seq-lemma
    (implies (posp n)
             (equal (nth (- n 1) (p1p2-n-seq n))
                    (nth 0 (p1p2-n-seq-i n))))
    :hints (("Goal"
             :in-theory (disable P1P2-N-SEQ-i)
             :induct (P1P2-N-SEQ-2 N)
             )
            ("Subgoal *1/2"
             :in-theory nil
             )
            ("Subgoal *1/2.1"
             :use ((:instance p1p2-n-p-seq-lemma-2 (n n)
                              (a (p1p2-n-seq-2 (- n 1)))
                              (b (p1p2-n-seq-i n))
                              (c (p1p2-n-seq-2 n)))
                   (:instance p1p2-n-seq-2-len (n (- n 1)))
                   (:instance p1p2-n-seq-lemma-3
                              (n n)))
             :in-theory (e/d (p1p2-n-seq natp) (P1P2-N-SEQ-i))
             )
            ("Subgoal *1/2.2"
             :use (:instance p1p2-n-seq-lemma*1/2.2-2)
             )
            ))
  )

(defthmd realp-nat-p1p2-n-sequence
  (implies (posp n)
           (realp (cadr (P1P2-N-SEQUENCE N))))
  :hints (("Goal"
           :use ((:instance p1p2-n-seq-lemma (n n))
                 (:instance p1p2-n-seq-lemma-1 (n n)))
           :in-theory (disable p1p2-n-seq-i)
           )))

(defthmd realp-natp-p1p2-n-p-sequence-1
  (implies (realp (cadar (nth 0 (p1p2-n-p-seq-i n))))
           (realp (cadar (p1p2-n-p-sequence n))))
  :hints (("Goal"
           :use ((:instance p1p2-n-p-seq-lemma (n n)))
           :in-theory (disable p1p2-n-p-seq-i)
           )))

(defthmd realp-natp-p1p2-n-p-sequence-2
  (implies (posp n)
           (equal (cadar (nth 0 (p1p2-n-p-seq-i n)))
                  (car (cdr (p1p2-n-sequence (nth 0 (mod-remainder-2 0 n)))))))
  :hints (("Goal"
           :in-theory (disable mod-remainder-2 mod-remainder-3)
           )))

(encapsulate
  ()

  (local (include-book "arithmetic/top" :dir :system))

  (defthmd pip2-n-p-sequence-pos-realp
    (realp (cadr (p1p2-n-p-sequence n)))
    :hints (("Goal"
             :use ((:instance realp-pos-p1p2-n-p-sequence (n n)))
             :in-theory (disable p1p2-n-seq p1p2-n-p-seq p1p2-n-p-seq-i p1p2-n-seq-i mod-remainder-2)
             ))))

(encapsulate
  ()

  (local (include-book "arithmetic/top" :dir :system))

  (defthmd pip2-n-p-sequence-nat-realp
    (realp (cadar (p1p2-n-p-sequence n)))
    :hints (("Goal"
             :use ((:instance realp-natp-p1p2-n-p-sequence-1 (n n))
                   (:instance realp-natp-p1p2-n-p-sequence-2 (n n))
                   (:instance realp-nat-p1p2-n-sequence (n (nth 0 (mod-remainder-2 0 n)))))
             :in-theory (disable p1p2-n-seq p1p2-n-p-seq p1p2-n-p-seq-i p1p2-n-seq-i mod-remainder-2)
             ))))

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd angle-sequence-realp
    (realp (angles-seq n))
    :hints (("Goal"
             :use ((:instance angles-countable-thm-2 (n n) (q (- n 1)))
                   (:instance pip2-n-p-sequence-pos-realp)
                   (:instance pip2-n-p-sequence-nat-realp)
                   (:instance generate-angles-lemma1 (n (- n 1)))
                   (:instance generate-angles-lemma1 (n n)))
             :in-theory (disable generate-angles p1p2-n-p-sequence EXISTS-ANGLE>=0<2PI)
             )
            ("Subgoal 2"
             :cases ((EXISTS-ANGLE>=0<2PI (CAR (CAR (CAR (P1P2-N-P-SEQUENCE N))))
                                          (CADR (CAR (CAR (P1P2-N-P-SEQUENCE N)))))))
            ("Subgoal 2.1"
             :use ((:instance angles-countable-9 (p1 (CAR (CAR (CAR (P1P2-N-P-SEQUENCE N)))))
                              (p2 (CADR (CAR (CAR (P1P2-N-P-SEQUENCE N)))))))
             )
            ))
  )

(defun-sk exists-in-interval-but-not-in-angle-sequence (a b)
  (exists angle
          (and (realp angle)
               (< a angle)
               (< angle b)
               (not (nth-angle-exists angle)))))

(encapsulate
  ()

  (local (include-book "nonstd/transcendentals/reals-are-uncountable-1" :dir :system))

  (defthmd existence-of-angle-not-in-sequence
    (exists-in-interval-but-not-in-angle-sequence 0 (* 2 (acl2-pi)))
    :hints (("goal"
             :use ((:functional-instance reals-are-not-countable
                                         (seq angles-seq)
                                         (a (lambda () 0))
                                         (b (lambda () (* 2 (acl2-pi))))
                                         (exists-in-sequence nth-angle-exists)
                                         (exists-in-sequence-witness nth-angle-exists-witness)
                                         (exists-in-interval-but-not-in-sequence exists-in-interval-but-not-in-angle-sequence)
                                         (exists-in-interval-but-not-in-sequence-witness exists-in-interval-but-not-in-angle-sequence-witness)))
             )
            ("subgoal 4"
             :use (
                   (:instance exists-in-interval-but-not-in-angle-sequence-suff (angle x))
                   )
             )
            ("Subgoal 3"
             :in-theory (disable nth-angle-exists)
             )
            ("Subgoal 2"
             :use (:instance nth-angle-exists-suff (n i) (angle x))
             :in-theory (disable angles-seq)
             )
            ("Subgoal 1"
             :in-theory (disable angles-seq)
             )
            ))
  )

(defthmd witness-not-in-angle-sequence
  (and (realp (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))
       (<= 0 (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))
       (< (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))) (* 2 (acl2-pi)))
       (not (nth-angle-exists (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))))
  :hints (("goal"
           :use ((:instance existence-of-angle-not-in-sequence))
           )))

(defthmd rot-angle-witness*p1!=p2
  (implies (and (d-p p1)
                (d-p p2)
                (posp n))
           (not (m-= (m-* (rotation-about-witness (* n (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))
                                                  (point-on-s2-not-d)) p1) p2)))
  :hints (("Goal"
           :use ((:instance witness-not-in-angle-sequence)
                 (:instance angles-countable (angle (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))
                            (p1 p1)
                            (p2 p2)
                            (n n)))
           )))





-------------

(defthmd p1p2-n-p-sequence-lemma
  (implies (posp n)
           (equal (P1P2-N-P-SEQUENCE N)
                  (nth 0 (p1p2-n-p-seq-i n))))
  :hints (("Goal"
           :in-theory (disable P1P2-N-P-SEQ-i)
           :induct (P1P2-N-P-SEQ-2 N)
           )
          ("Subgoal *1/2"
           :in-theory nil
           )
          ))
)

---

(encapsulate
  ()

  (local (include-book "arithmetic/top" :dir :system))

  (defthmd p1p2-n-p-sequence-lemma-1
    (implies (posp n)
             (equal (len (p1p2-n-p-seq n))
                    n)))

  (defthmd p1p2-n-p-sequence-lemma-2
    (implies (endp l)
             (equal (len l) 0)))

  (defthmd p1p2-n-p-sequence-lemma-3
    (implies (posp n)
             (not (endp (p1p2-n-p-seq n)))))

  (defthmd p1p2-n-p-sequence-lemma-4
    (true-listp (p1p2-n-p-seq n)))

  (defthmd p1p2-n-p-sequence-lemma-5
    (implies (not (consp l))
             (atom l)))

  (defthmd p1p2-n-p-sequence-lemma-6
    (implies (and (posp (- n 1))
                  (natp q)
                  (< q (len (p1p2-n-p-seq (- n 1)))))
             (equal (nth q (p1p2-n-p-seq n))
                    (nth q (p1p2-n-p-seq (- n 1)))))
    :hints (("Goal"
             :in-theory (disable p1p2-n-p-seq-i)
             )))
  )

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd p1p2-n-p-sequence-lemma-7
    (implies (and (integerp n)
                  (< 0 n))
             (not (zp n))))

  )

(encapsulate
  ()

  (local (include-book "arithmetic/top" :dir :system))

  (defthmd p1p2-n-p-sequence-lemma
    (implies (posp n)
             (equal (P1P2-N-P-SEQUENCE N)
                    (nth 0 (p1p2-n-p-seq-i n))))
    :hints (("Goal"
             :in-theory (disable P1P2-N-P-SEQ-i)
             :induct (P1P2-N-P-SEQ-2 N)
             )
            ("Subgoal *1/2"
             :in-theory nil
             )
            ))
  )

---

(defthmd angle-sequence-realp-1
  (realp (cadar (P1P2-N-P-SEQUENCE N)))
  :hints (("Goal"
           :in-theory (disable mod-remainder-2 mod-remainder-3)
           )))
)

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

;(defthmd EXISTS-ANGLE>=0<2PI

  (defthmd angle-sequence-realp
    (implies (and (realp (cadar (p1p2-n-p-sequence n)))
                  (realp (cadr (p1p2-n-p-sequence n))))
             (realp (angles-seq n))
             :hints (("Goal"
;:cases (())
                      :use ((:instance angles-countable-thm-2 (n n) (q (- n 1)))
                            (:instance generate-angles-lemma1 (n (- n 1)))
                            (:instance generate-angles-lemma1 (n n)))
                      :in-theory (disable generate-angles p1p2-n-p-sequence EXISTS-ANGLE>=0<2PI)
                      )
                     ("Subgoal 2"
                      :cases ((EXISTS-ANGLE>=0<2PI (CAR (CAR (CAR (P1P2-N-P-SEQUENCE N))))
                                                   (CADR (CAR (CAR (P1P2-N-P-SEQUENCE N)))))))
                     ("Subgoal 2.1"
                      :use ((:instance angles-countable-9 (p1 (CAR (CAR (CAR (P1P2-N-P-SEQUENCE N)))))
                                       (p2 (CADR (CAR (CAR (P1P2-N-P-SEQUENCE N)))))))
                      :in-theory nil
                      )
                     ))
    )

  ----

  (defun-sk exists-in-interval-but-not-in-angle-sequence (a b)
    (exists angle
            (and (realp angle)
                 (< a angle)
                 (< angle b)
                 (not (nth-angle-exists angle)))))

  (encapsulate
    ()

    (local (include-book "nonstd/transcendentals/reals-are-uncountable-1" :dir :system))

    (defthmd existence-of-angle-not-in-sequence
      (exists-in-interval-but-not-in-angle-sequence 0 (* 2 (acl2-pi)))
      :hints (("goal"
               :use ((:functional-instance reals-are-not-countable
                                           (seq angles-seq)
                                           (a (lambda () 0))
                                           (b (lambda () (* 2 (acl2-pi))))
                                           (exists-in-sequence nth-angle-exists)
                                           (exists-in-sequence-witness nth-angle-exists-witness)
                                           (exists-in-interval-but-not-in-sequence exists-in-interval-but-not-in-angle-sequence)
                                           (exists-in-interval-but-not-in-sequence-witness exists-in-interval-but-not-in-angle-sequence-witness)))
               ))))











  -----------------------------

  (defthm r-theta*p=p=>angle>=0<2pi=>0
    (implies (and (point-in-r3 p)
                  (point-in-r3 u)
                  (realp angle)
                  (or (not (equal (point-in-r3-x1 p)
                                  (point-in-r3-x1 u)))
                      (not (equal (point-in-r3-y1 p)
                                  (point-in-r3-y1 u)))
                      (not (equal (point-in-r3-z1 p)
                                  (point-in-r3-z1 u))))
                  (or (not (equal (point-in-r3-x1 p)
                                  (- (point-in-r3-x1 u))))
                      (not (equal (point-in-r3-y1 p)
                                  (- (point-in-r3-y1 u))))
                      (not (equal (point-in-r3-z1 p)
                                  (- (point-in-r3-z1 u)))))
                  (equal (+ (* (point-in-r3-x1 p) (point-in-r3-x1 p))
                            (* (point-in-r3-y1 p) (point-in-r3-y1 p))
                            (* (point-in-r3-z1 p) (point-in-r3-z1 p)))
                         1)
                  (equal (+ (* (point-in-r3-x1 u) (point-in-r3-x1 u))
                            (* (point-in-r3-y1 u) (point-in-r3-y1 u))
                            (* (point-in-r3-z1 u) (point-in-r3-z1 u)))
                         1)
                  (equal (point-in-r3-y1 u) 0)
                  (>= angle 0)
                  (< angle (* 2 (acl2-pi)))
                  (m-= (m-* (rotation-about-witness angle u) p) p))
             (equal angle 0))
    :hints (("Goal"
             :use ((:instance r-theta*p=p=>cosine=1 (p p) (u u))
                   (:instance r-theta*p=p=>sine=0 (p p) (u u))
                   (:instance sin=0-cos=1 (x angle)))
             :in-theory (e/d () (m-= m-* rotation-about-witness point-in-r3-x1 point-in-r3-y1 point-in-r3-z1))
             ))
    :rule-classes nil)

  (defthm r-theta1*p=p-r-theta2*p=p=>1=2
    (implies (and (realp angle1)
                  (realp angle2)
                  (>= angle1 0)
                  (< angle1 (* 2 (acl2-pi)))
                  (>= angle2 0)
                  (< angle2 (* 2 (acl2-pi)))
                  (point-in-r3 p)
                  (point-in-r3 u)
                  (or (not (equal (point-in-r3-x1 p)
                                  (point-in-r3-x1 u)))
                      (not (equal (point-in-r3-y1 p)
                                  (point-in-r3-y1 u)))
                      (not (equal (point-in-r3-z1 p)
                                  (point-in-r3-z1 u))))
                  (or (not (equal (point-in-r3-x1 p)
                                  (- (point-in-r3-x1 u))))
                      (not (equal (point-in-r3-y1 p)
                                  (- (point-in-r3-y1 u))))
                      (not (equal (point-in-r3-z1 p)
                                  (- (point-in-r3-z1 u)))))
                  (equal (+ (* (point-in-r3-x1 p) (point-in-r3-x1 p))
                            (* (point-in-r3-y1 p) (point-in-r3-y1 p))
                            (* (point-in-r3-z1 p) (point-in-r3-z1 p)))
                         1)
                  (equal (+ (* (point-in-r3-x1 u) (point-in-r3-x1 u))
                            (* (point-in-r3-y1 u) (point-in-r3-y1 u))
                            (* (point-in-r3-z1 u) (point-in-r3-z1 u)))
                         1)
                  (equal (point-in-r3-y1 u) 0)
                  (m-= (m-* (rotation-about-witness angle1 u) p)
                       (m-* (rotation-about-witness angle2 u) p)))
             (equal angle1 angle2))
    :hints (("Goal"
             :use ((:instance r-theta1*p=r-theta2*p=>r-theta1-theta2*p=p (angle1 angle1)
                              (angle2 angle2)
                              (u u) (p p))
                   (:instance r-theta1*p=r-theta2*p=>r-theta1-theta2*p=p (angle1 angle2)
                              (angle2 angle1)
                              (u u) (p p))
                   (:instance r-theta*p=p=>angle>=0<2pi=>0 (p p) (u u) (angle (- angle1 angle2)))
                   (:instance r-theta*p=p=>angle>=0<2pi=>0 (p p) (u u) (angle (- angle2 angle1))))
             :in-theory (e/d () (m-= m-* rotation-about-witness point-in-r3-x1 point-in-r3-y1 point-in-r3-z1))
             ))
    :rule-classes nil)

  (defthmd point-on-s2-not-d-on-s2
    (implies (equal (point-on-s2-not-d) u)
             (and (equal (+ (* (point-in-r3-x1 u) (point-in-r3-x1 u))
                            (* (point-in-r3-y1 u) (point-in-r3-y1 u))
                            (* (point-in-r3-z1 u) (point-in-r3-z1 u)))
                         1)
                  (not (d-p u))))
    :hints (("Goal"
             :use ((:instance r3-rotationp-r-theta-2 (point (point-on-s2-not-d)))
                   (:instance r3-rotationp-r-theta-5 (point (point-on-s2-not-d)))
                   (:instance exists-in-x-coord-sequence-lemma (p u))
                   (:instance exists-point-on-s2-not-d-3)
                   (:instance witness-not-in-x-coord-sequence))
             :in-theory (disable point-on-s2-not-d point-in-r3-x1 point-in-r3-y1 point-in-r3-z1 aref2 d-p)
             )))

  (defthmd d-p=>notm-=u--u-1
    (implies (and (d-p p)
                  (point-in-r3 u)
                  (not (d-p u)))
             (and (or (not (equal (point-in-r3-x1 p)
                                  (point-in-r3-x1 u)))
                      (not (equal (point-in-r3-y1 p)
                                  (point-in-r3-y1 u)))
                      (not (equal (point-in-r3-z1 p)
                                  (point-in-r3-z1 u))))
                  (or (not (equal (point-in-r3-x1 p)
                                  (- (point-in-r3-x1 u))))
                      (not (equal (point-in-r3-y1 p)
                                  (- (point-in-r3-y1 u))))
                      (not (equal (point-in-r3-z1 p)
                                  (- (point-in-r3-z1 u)))))))
    :hints (("Goal"
             :use ((:instance d-p=>notm-=u--u (p p) (u u)))
             :in-theory (e/d (m-=) (word-exists))
             )))

  (defthm r-theta1*p=p-r-theta2*p=p=>1=2-d-p-1
    (implies (d-p p)
             (and (equal (+ (* (point-in-r3-x1 p) (point-in-r3-x1 p))
                            (* (point-in-r3-y1 p) (point-in-r3-y1 p))
                            (* (point-in-r3-z1 p) (point-in-r3-z1 p)))
                         1)
                  (point-in-r3 p))))

  (defthm r-theta1*p=p-r-theta2*p=p=>1=2-d-p
    (implies (and (realp angle1)
                  (realp angle2)
                  (>= angle1 0)
                  (< angle1 (* 2 (acl2-pi)))
                  (>= angle2 0)
                  (< angle2 (* 2 (acl2-pi)))
                  (d-p p)
                  (equal (point-on-s2-not-d) u)
                  (m-= (m-* (rotation-about-witness angle1 u) p)
                       (m-* (rotation-about-witness angle2 u) p)))
             (equal angle1 angle2))
    :hints (("Goal"
             :use ((:instance r-theta1*p=p-r-theta2*p=p=>1=2 (angle1 angle1)
                              (angle2 angle2)
                              (u (point-on-s2-not-d)) (p p))
                   (:instance d-p (point p))
                   (:instance s2-def-p (point p))
                   (:instance exists-point-on-s2-not-d-2)
                   (:instance s2-def-p (point u))
                   (:instance r3-rotationp-r-theta-5 (point (point-on-s2-not-d)))
                   (:instance r-theta1*p=p-r-theta2*p=p=>1=2-d-p-1 (p p))
                   (:instance point-on-s2-not-d-on-s2 (u (point-on-s2-not-d)))
                   (:instance d-p=>notm-=u--u-1 (p p) (u (point-on-s2-not-d))))
             :in-theory nil
             ))
    :rule-classes nil)

  (encapsulate
    ()

    (local (include-book "arithmetic/top" :dir :system))

    (defthmd angles-countable-1
      (implies (and (realp angle)
                    (posp n)
                    (>= angle 0)
                    (< angle (* 2 (acl2-pi))))
               (and (NATP (* (+ (* N ANGLE)
                                (- (MOD (* N ANGLE) (* 2 (ACL2-PI)))))
                             (/ (* 2 (ACL2-PI)))))
                    (REALP (MOD (* N ANGLE) (* 2 (ACL2-PI))))
                    (REALP (* N ANGLE))
                    (REALP (* 2 (ACL2-PI)))))
      :hints (("Goal"
               :use (:instance k-range-3 (n n) (x (mod (* n angle) (* 2 (acl2-pi)))) (angle angle)
                               (k (/ (- (* n angle) (mod (* n angle) (* 2 (acl2-pi))))
                                     (* 2 (acl2-pi)))))
               )))

    (defthmd angles-countable-2
      (implies (and (d-p p1)
                    (d-p p2)
                    (NTH-POLE-EXISTS P1)
                    (NTH-POLE-EXISTS P2)
                    (EXISTS-ANGLE>=0<2PI P1 P2))
               (and (REALP (EXISTS-ANGLE>=0<2PI-WITNESS P1 P2))
                    (m-= (pole-seq (NTH-POLE-EXISTS-WITNESS P1)) p1)
                    (m-= (pole-seq (NTH-POLE-EXISTS-WITNESS P2)) p2)
                    (POSP (NTH-POLE-EXISTS-WITNESS P1))
                    (POSP (NTH-POLE-EXISTS-WITNESS P2))))
      :hints (("Goal"
               :in-theory (disable d-p)
               )))
    )

  (defthmd angles-countable-3
    (implies (and (d-p p1)
                  (d-p p2)
                  (realp angle)
                  (posp n)
                  (>= angle 0)
                  (< angle (* 2 (acl2-pi)))
                  (m-= (m-* (rotation-about-witness (* n angle) (point-on-s2-not-d)) p1) p2))
             (M-= (M-* (ROTATION-ABOUT-WITNESS (MOD (* N ANGLE) (* 2 (ACL2-PI)))
                                               (POINT-ON-S2-NOT-D))
                       P1)
                  P2))
    :hints (("Goal"
             :use ((:instance realnum-equiv (r (* n angle)) (x (* 2 (acl2-pi))))
                   (:instance k-range-3 (n n) (x (mod (* n angle) (* 2 (acl2-pi)))) (angle angle)
                              (k (/ (- (* n angle) (mod (* n angle) (* 2 (acl2-pi))))
                                    (* 2 (acl2-pi)))))
                   (:instance integerp-r-mod-r-x/x (r (* n angle)) (x (* 2 (acl2-pi))))
                   (:instance exists-point-on-s2-not-d-2)
                   (:instance s2-def-p (point (point-on-s2-not-d)))
                   (:instance rotation-angle=2pik
                              (k (* (+ (* N ANGLE)
                                       (- (MOD (* N ANGLE) (* 2 (ACL2-PI)))))
                                    (/ (* 2 (ACL2-PI)))))
                              (x (MOD (* N ANGLE) (* 2 (ACL2-PI))))
                              (u (point-on-s2-not-d))))
             :in-theory (disable rotation-about-witness point-on-s2-not-d acl2-sqrt word-exists d-p)
             )))

  (defthmd angles-countable-4
    (implies (NUM>=0-EXISTS p)
             (posp (NUM>=0-EXISTS-WITNESS p))))

  (defthmd angles-countable-5
    (implies (NUM>=1-EXISTS n)
             (posp (NUM>=1-EXISTS-WITNESS n))))

  (defthmd angles-countable-6
    (implies (NUM>=0-EXISTS p)
             (equal (natp-seq (num>=0-exists-witness p)) p)))

  (defthmd angles-countable-7
    (implies (NUM>=1-EXISTS n)
             (equal (posp-seq (num>=1-exists-witness n)) n)))

  (defthmd angles-countable-8
    (implies (and (m-= witp1 p1)
                  (m-= witp2 p2)
                  (m-= (m-* p3 p1) p2))
             (m-= (m-* p3 witp1) witp2)))

  (defthmd angles-countable-9
    (implies (EXISTS-ANGLE>=0<2PI P1 P2)
             (and (realp (EXISTS-ANGLE>=0<2PI-witness P1 P2))
                  (>= (EXISTS-ANGLE>=0<2PI-witness P1 P2) 0)
                  (< (EXISTS-ANGLE>=0<2PI-witness P1 P2) (* 2 (acl2-pi)))
                  (m-= (m-* (rotation-about-witness (EXISTS-ANGLE>=0<2PI-witness P1 P2)
                                                    (point-on-s2-not-d)) p1) p2)))
    :hints (("Goal"
             :in-theory (disable rotation-about-witness)
             )))

  (defthmd angles-countable-10
    (implies (and (m-= (m-* x p1) p2)
                  (m-= (m-* y witp1) witp2)
                  (m-= witp1 p1)
                  (m-= witp2 p2))
             (m-= (m-* x p1) (m-* y p1))))

  (encapsulate
    ()

    (local (include-book "arithmetic-5/top" :dir :system))
    (defthm angles-countable-11
      (implies (and (posp n)
                    (realp angle)
                    (EQUAL (+ (* (* 2 (ACL2-PI))
                                 (+ (* N ANGLE)
                                    (- (EXISTS-ANGLE>=0<2PI-WITNESS P1 P2)))
                                 (/ (* 2 (ACL2-PI))))
                              (EXISTS-ANGLE>=0<2PI-WITNESS P1 P2))
                           (* N ANGLE)))
               (equal angle
                      (* (+ (* 2 (ACL2-PI)
                               (+ (* N ANGLE)
                                  (- (EXISTS-ANGLE>=0<2PI-WITNESS P1 P2)))
                               (/ (* 2 (ACL2-PI))))
                            (EXISTS-ANGLE>=0<2PI-WITNESS P1 P2))
                         (/ N))))
      :rule-classes nil)
    )

  (defthmd angles-countable-12
    (implies
     (EQUAL (+ (* (* 2 (ACL2-PI))
                  (+ (* N ANGLE)
                     (- (EXISTS-ANGLE>=0<2PI-WITNESS P1 P2)))
                  (/ (* 2 (ACL2-PI))))
               (EXISTS-ANGLE>=0<2PI-WITNESS P1 P2))
            (* N ANGLE))
     (EQUAL (* N ANGLE)
            (+ (* 2 (ACL2-PI)
                  (+ (* N ANGLE)
                     (- (EXISTS-ANGLE>=0<2PI-WITNESS P1 P2)))
                  (/ (* 2 (ACL2-PI))))
               (EXISTS-ANGLE>=0<2PI-WITNESS P1 P2)))))

  (defthmd angles-countable
    (implies (and (d-p p1)
                  (d-p p2)
                  (realp angle)
                  (posp n)
                  (>= angle 0)
                  (< angle (* 2 (acl2-pi)))
                  (m-= (m-* (rotation-about-witness (* n angle) (point-on-s2-not-d)) p1) p2))
             (nth-angle-exists angle))
    :hints (("Goal"
             :use ((:instance poles-countable-thm (p p1))
                   (:instance poles-countable-thm (p p2))
                   (:instance natnum-countable-thm (num (/ (- (* n angle) (mod (* n angle) (* 2 (acl2-pi))))
                                                           (* 2 (acl2-pi)))))
                   (:instance k-range-3 (n n) (x (mod (* n angle) (* 2 (acl2-pi)))) (angle angle)
                              (k (/ (- (* n angle) (mod (* n angle) (* 2 (acl2-pi))))
                                    (* 2 (acl2-pi)))))
                   (:instance integerp-r-mod-r-x/x (r (* n angle)) (x (* 2 (acl2-pi))))
                   (:instance realnum-equiv (r (* n angle)) (x (* 2 (acl2-pi))))
                   (:instance posp-countable-thm (num n))
                   (:instance exists-angle>=0<2pi-suff (p1 p1) (p2 p2) (angle (mod (* n angle) (* 2 (acl2-pi)))))
                   (:instance range-mod-r-x (r (* n angle)) (x (* 2 (acl2-pi))))
                   (:instance angles-countable-1)
                   (:instance angles-countable-2)
                   (:instance angles-countable-8 (p1 p1) (p2 p2)
                              (p3 (ROTATION-ABOUT-WITNESS (MOD (* N ANGLE) (* 2 (ACL2-PI)))
                                                          (POINT-ON-S2-NOT-D)))
                              (witp1 (POLE-SEQ (NTH-POLE-EXISTS-WITNESS P1)))
                              (witp2 (POLE-SEQ (NTH-POLE-EXISTS-WITNESS P2))))
                   (:instance r-theta1*p=p-r-theta2*p=p=>1=2-d-p
                              (angle1 (mod (* n angle) (* 2 (acl2-pi))))
                              (angle2 (exists-angle>=0<2pi-witness p1 p2))
                              (u (point-on-s2-not-d))
                              (p p1))
                   (:instance r-theta1*p=p-r-theta2*p=p=>1=2-d-p
                              (angle1 (EXISTS-ANGLE>=0<2PI-WITNESS P1 P2))
                              (angle2 (EXISTS-ANGLE>=0<2PI-WITNESS (POLE-SEQ (NTH-POLE-EXISTS-WITNESS P1))
                                                                   (POLE-SEQ (NTH-POLE-EXISTS-WITNESS P2))))
                              (u (point-on-s2-not-d))
                              (p p1))
                   (:instance angles-countable-11)
                   (:instance rotation-angle=2pik
                              (k (* (+ (* N ANGLE)
                                       (- (MOD (* N ANGLE) (* 2 (ACL2-PI)))))
                                    (/ (* 2 (ACL2-PI)))))
                              (x (MOD (* N ANGLE) (* 2 (ACL2-PI))))
                              (u (point-on-s2-not-d)))
                   (:instance angles-countable-3)
                   (:instance angles-countable-5)
                   (:instance angles-countable-7)
                   (:instance angles-countable-9)
                   (:instance angles-countable-12)
                   (:instance angles-countable-4 (p (* (+ (* N ANGLE)
                                                          (- (MOD (* N ANGLE) (* 2 (ACL2-PI)))))
                                                       (/ (* 2 (ACL2-PI))))))
                   (:instance angles-countable-6 (p (* (+ (* N ANGLE)
                                                          (- (MOD (* N ANGLE) (* 2 (ACL2-PI)))))
                                                       (/ (* 2 (ACL2-PI))))))
                   (:instance exists-point-on-s2-not-d-2)
                   (:instance s2-def-p (point (point-on-s2-not-d)))
                   (:instance EXISTS-ANGLE>=0<2PI-suff
                              (angle (EXISTS-ANGLE>=0<2PI-WITNESS P1 P2))
                              (p1 (POLE-SEQ (NTH-POLE-EXISTS-WITNESS P1)))
                              (p2 (POLE-SEQ (NTH-POLE-EXISTS-WITNESS P2))))
                   (:instance EXISTS-ANGLE>=0<2PI
                              (p1 (POLE-SEQ (NTH-POLE-EXISTS-WITNESS P1)))
                              (p2 (POLE-SEQ (NTH-POLE-EXISTS-WITNESS P2))))
                   (:instance angles-countable-10
                              (y (ROTATION-ABOUT-WITNESS (EXISTS-ANGLE>=0<2PI-WITNESS
                                                          (POLE-SEQ (NTH-POLE-EXISTS-WITNESS P1))
                                                          (POLE-SEQ (NTH-POLE-EXISTS-WITNESS P2)))
                                                         (POINT-ON-S2-NOT-D)))
                              (x (ROTATION-ABOUT-WITNESS (EXISTS-ANGLE>=0<2PI-WITNESS P1 P2)
                                                         (POINT-ON-S2-NOT-D)))
                              (p1 p1)
                              (p2 p2)
                              (witp1 (POLE-SEQ (NTH-POLE-EXISTS-WITNESS P1)))
                              (witp2 (POLE-SEQ (NTH-POLE-EXISTS-WITNESS P2))))
                   (:instance angles-countable-thm
                              (n1 (nth-pole-exists-witness p1))
                              (n2 (nth-pole-exists-witness p2))
                              (n3 (num>=0-exists-witness (/ (- (* n angle) (mod (* n angle) (* 2 (acl2-pi))))
                                                            (* 2 (acl2-pi)))))
                              (n4 (num>=1-exists-witness n))
                              (p1 (pole-seq (nth-pole-exists-witness p1)))
                              (p2 (pole-seq (nth-pole-exists-witness p2)))
                              (nat (/ (- (* n angle) (mod (* n angle) (* 2 (acl2-pi))))
                                      (* 2 (acl2-pi))))
                              (pos n)
                              (angle (mod (* n angle) (* 2 (acl2-pi))))))
             :in-theory nil
             ))
    )






  -------------------------

  (defthmd d-p=>notm-=u--u
    (implies (and (d-p p)
                  (point-in-r3 u)
                  (not (d-p u)))
             (and (not (m-= p u))
                  (or (not (equal (point-in-r3-x1 p)
                                  (- (point-in-r3-x1 u))))
                      (not (equal (point-in-r3-y1 p)
                                  (- (point-in-r3-y1 u))))
                      (not (equal (point-in-r3-z1 p)
                                  (- (point-in-r3-z1 u)))))))
    :hints (("Goal"
             :use ((:instance diff-d-p-p=>d-p-p1 (p p) (p1 u))
                   (:instance d-p=>d-p-p (p1 p) (p2 u)))
             :in-theory (e/d (m-=) (d-p))
             )))

  (encapsulate
    ()

    (local (include-book "arithmetic/inequalities" :dir :system))
    (local (include-book "arithmetic-5/top" :dir :system))

    (defthmd r-theta1*p1=r-theta2*p1=>theta1=theta2-1
      (implies (and (realp angle)
                    (integerp k)
                    (< angle (* 2 (acl2-pi))))
               (< (+ (* 2 (acl2-pi) k) angle) (+ (* 2 (acl2-pi) k) (* 2 (acl2-pi))))))

    (defthmd r-theta1*p1=r-theta2*p1=>theta1=theta2-2
      (implies (and (realp angle)
                    (integerp k)
                    (< angle (* 2 (acl2-pi)))
                    (>= (+ (* 2 (acl2-pi) k) angle) 0))
               (> (+ (* 2 (acl2-pi) k) (* 2 (acl2-pi))) 0))
      :hints (("Goal"
               :use ((:instance r-theta1*p1=r-theta2*p1=>theta1=theta2-1))
               )))

    (defthmd r-theta1*p1=r-theta2*p1=>theta1=theta2-3
      (implies (and (integerp k)
                    (> (+ (* 2 (acl2-pi) k) (* 2 (acl2-pi))) 0))
               (> k -1)))

    (defthmd r-theta1*p1=r-theta2*p1=>theta1=theta2-4
      (implies (and (realp angle)
                    (integerp k)
                    (>= angle 0))
               (>= (+ (* 2 (acl2-pi) k) angle) (* 2 (acl2-pi) k))))

    (defthmd r-theta1*p1=r-theta2*p1=>theta1=theta2-5
      (implies (and (realp angle)
                    (integerp k)
                    (>= angle 0)
                    (< (+ (* 2 (acl2-pi) k) angle) (* 2 (acl2-pi))))
               (< (* 2 (acl2-pi) k) (* 2 (acl2-pi))))
      :hints (("Goal"
               :use ((:instance r-theta1*p1=r-theta2*p1=>theta1=theta2-4))
               )))

    (defthmd r-theta1*p1=r-theta2*p1=>theta1=theta2-6
      (implies (and (integerp k)
                    (< (* 2 (acl2-pi) k) (* 2 (acl2-pi))))
               (< k 1)))

    (defthm r-theta1*p1=r-theta2*p1=>theta1=theta2-7
      (implies (and (realp angle)
                    (integerp k)
                    (< angle (* 2 (acl2-pi)))
                    (>= angle 0)
                    (>= (+ (* 2 (acl2-pi) k) angle) 0)
                    (< (+ (* 2 (acl2-pi) k) angle) (* 2 (acl2-pi))))
               (equal k 0))
      :hints (("Goal"
               :use ((:instance r-theta1*p1=r-theta2*p1=>theta1=theta2-2)
                     (:instance r-theta1*p1=r-theta2*p1=>theta1=theta2-3)
                     (:instance r-theta1*p1=r-theta2*p1=>theta1=theta2-5)
                     (:instance r-theta1*p1=r-theta2*p1=>theta1=theta2-6))
               ))
      :rule-classes nil)
    )
















  --------------------------------------
  (include-book "countable-sets")

  (defun pole-seq (n)
    (if (posp n)
        (nth (- n 1) (poles-list (generate-words-main n)))
      0))

  (defun-sk nth-pole-exists (p)
    (exists n
            (and (posp n)
                 (m-= (pole-seq n) p))))


  (defthmd poles-countable-thm
    (implies (d-p p)
             (nth-pole-exists p))
    :hints (("Goal"
             :use ((:instance exists-pole-n-thm (p p))
                   (:instance exists-pole-n (pole p))
                   (:instance nth-pole-exists-suff (p p) (n (+ (exists-pole-n-witness p) 1))))
             :in-theory (e/d () (poles-list generate-words-main))
             )))

  (defun p1-*-p2-seq-i (i)
    (let ((rm-2 (mod-remainder-2 0 i)))
      (let ((rm-3 (mod-remainder-3 0 (nth 1 rm-2))))
        (if (equal (nth 1 rm-3) 1)
            (if (or (equal (nth 0 rm-2) 0)
                    (equal (nth 0 rm-3) 0))
                (list (list 0 0))
              (list (list (pole-seq (nth 0 rm-2)) (pole-seq (nth 0 rm-3)))))
          (list (list 0 0))))))

  (encapsulate
    ()

    (local (include-book "arithmetic/top" :dir :system))

    (defun p1*p2-seq-2 (i)
      (if (zp i)
          nil
        (append (p1*p2-seq-2 (- i 1)) (p1-*-p2-seq-i i))))
    )

  (defun p1-*-p2-seq (i)
    (if (posp i)
        (p1*p2-seq-2 i)
      nil))

  (defun p1-*-p2-sequence (n)
    (if (posp n)
        (nth (- n 1) (p1-*-p2-seq n))
      0))

  (defun-sk p1-*-p2-countable (x)
    (exists n
            (and (posp n)
                 (equal (p1-*-p2-sequence n) x))))

  (defthmd p1-*-p2-seq-exists
    (implies (and (posp n1)
                  (posp n2)
                  (equal (pole-seq n1) p)
                  (equal (pole-seq n2) q))
             (p1-*-p2-countable (list p q)))
    :hints (("Goal"
             :use (:functional-instance f-*-g-seq-exists
                                        (f pole-seq)
                                        (g pole-seq)
                                        (f-*-g-countable p1-*-p2-countable)
                                        (f-*-g-sequence p1-*-p2-sequence)
                                        (f-*-g-seq p1-*-p2-seq)
                                        (f-*-g-seq-2 p1*p2-seq-2)
                                        (f-*-g-seq-i p1-*-p2-seq-i)
                                        (f-*-g-countable-witness p1-*-p2-countable-witness))
             )))

  (defun natp-seq (n)
    (if (posp n)
        (- n 1)
      0))

  (defun-sk num>=0-exists (num)
    (exists n
            (and (posp n)
                 (equal (natp-seq n) num))))


  (defthmd natnum-countable-thm
    (implies (natp num)
             (num>=0-exists num))
    :hints (("Goal"
             :use (:instance num>=0-exists-suff (n (+ num 1)) (num num))
             )))

  (defun p1p2-n-seq-i (i)
    (let ((rm-2 (mod-remainder-2 0 i)))
      (let ((rm-3 (mod-remainder-3 0 (nth 1 rm-2))))
        (if (equal (nth 1 rm-3) 1)
            (if (or (equal (nth 0 rm-2) 0)
                    (equal (nth 0 rm-3) 0))
                (list (list 0 0))
              (list (list (p1-*-p2-sequence (nth 0 rm-2)) (natp-seq (nth 0 rm-3)))))
          (list (list 0 0))))))

  (encapsulate
    ()

    (local (include-book "arithmetic/top" :dir :system))

    (defun p1p2-n-seq-2 (i)
      (if (zp i)
          nil
        (append (p1p2-n-seq-2 (- i 1)) (p1p2-n-seq-i i))))
    )

  (defun p1p2-n-seq (i)
    (if (posp i)
        (p1p2-n-seq-2 i)
      nil))

  (defun p1p2-n-sequence (n)
    (if (posp n)
        (nth (- n 1) (p1p2-n-seq n))
      0))

  (defun-sk p1p2-n-countable (x)
    (exists n
            (and (posp n)
                 (equal (p1p2-n-sequence n) x))))

  (defthmd p1p2-n-seq-exists
    (implies (and (posp n1)
                  (posp n2)
                  (equal (p1-*-p2-sequence n1) p)
                  (equal (natp-seq n2) q))
             (p1p2-n-countable (list p q)))
    :hints (("Goal"
             :use (:functional-instance f-*-g-seq-exists
                                        (f p1-*-p2-sequence)
                                        (g natp-seq)
                                        (f-*-g-countable p1p2-n-countable)
                                        (f-*-g-sequence p1p2-n-sequence)
                                        (f-*-g-seq p1p2-n-seq)
                                        (f-*-g-seq-2 p1p2-n-seq-2)
                                        (f-*-g-seq-i p1p2-n-seq-i)
                                        (f-*-g-countable-witness p1p2-n-countable-witness))
             )))

  (defun posp-seq (n)
    (if (posp n)
        n
      0))

  (defun-sk num>=1-exists (num)
    (exists n
            (and (posp n)
                 (equal (posp-seq n) num))))


  (defthmd posp-countable-thm
    (implies (posp num)
             (num>=1-exists num))
    :hints (("Goal"
             :use (:instance num>=1-exists-suff (n num) (num num))
             )))

  (defun p1p2-n-p-seq-i (i)
    (let ((rm-2 (mod-remainder-2 0 i)))
      (let ((rm-3 (mod-remainder-3 0 (nth 1 rm-2))))
        (if (equal (nth 1 rm-3) 1)
            (if (or (equal (nth 0 rm-2) 0)
                    (equal (nth 0 rm-3) 0))
                (list (list 0 0))
              (list (list (p1p2-n-sequence (nth 0 rm-2)) (posp-seq (nth 0 rm-3)))))
          (list (list 0 0))))))

  (encapsulate
    ()

    (local (include-book "arithmetic/top" :dir :system))

    (defun p1p2-n-p-seq-2 (i)
      (if (zp i)
          nil
        (append (p1p2-n-p-seq-2 (- i 1)) (p1p2-n-p-seq-i i))))
    )

  (defun p1p2-n-p-seq (i)
    (if (posp i)
        (p1p2-n-p-seq-2 i)
      nil))

  (defun p1p2-n-p-sequence (n)
    (if (posp n)
        (nth (- n 1) (p1p2-n-p-seq n))
      0))

  (defun-sk p1p2-n-p-countable (x)
    (exists n
            (and (posp n)
                 (equal (p1p2-n-p-sequence n) x))))

  (defthmd p1p2-n-p-seq-exists
    (implies (and (posp n1)
                  (posp n2)
                  (equal (p1p2-n-sequence n1) p)
                  (equal (posp-seq n2) q))
             (p1p2-n-p-countable (list p q)))
    :hints (("Goal"
             :use (:functional-instance f-*-g-seq-exists
                                        (f p1p2-n-sequence)
                                        (g posp-seq)
                                        (f-*-g-countable p1p2-n-p-countable)
                                        (f-*-g-sequence p1p2-n-p-sequence)
                                        (f-*-g-seq p1p2-n-p-seq)
                                        (f-*-g-seq-2 p1p2-n-p-seq-2)
                                        (f-*-g-seq-i p1p2-n-p-seq-i)
                                        (f-*-g-countable-witness p1p2-n-p-countable-witness))
             )))

  (defthmd p1p2-n-p-in-the-list
    (implies (and (posp n1)
                  (posp n2)
                  (posp n3)
                  (posp n4)
                  (equal (pole-seq n1) p1)
                  (equal (pole-seq n2) p2)
                  (equal (natp-seq n3) nat)
                  (equal (posp-seq n4) pos))
             (p1p2-n-p-countable (list (list (list p1 p2) nat) pos)))
    :hints (("Goal"
             :use ((:instance p1-*-p2-seq-exists (n1 n1) (n2 n2) (p (pole-seq n1)) (q (pole-seq n2)))
                   (:instance p1p2-n-seq-exists (n1 (p1-*-p2-countable-witness (list p1 p2)))
                              (p (list (pole-seq n1) (pole-seq n2)))
                              (q (natp-seq n3))
                              (n2 n3))
                   (:instance p1p2-n-p-seq-exists
                              (n1 (p1p2-n-countable-witness (list (list (pole-seq n1) (pole-seq n2)) nat)))
                              (p (list (list (pole-seq n1) (pole-seq n2)) nat))
                              (q (posp-seq n4))
                              (n2 n4))
                   (:instance P1-*-P2-COUNTABLE (x (LIST (POLE-SEQ N1) (POLE-SEQ N2))))
                   (:instance P1P2-N-COUNTABLE (x (LIST (LIST (POLE-SEQ N1) (POLE-SEQ N2))
                                                        (NATP-SEQ N3))))
                   )
             :in-theory nil
             )))

  (defun-sk exists-angle>=0<2pi (p1 p2)
    (exists angle
            (and (realp angle)
                 (>= angle 0)
                 (< angle (* 2 (acl2-pi)))
                 (m-= (m-* (rotation-about-witness angle (point-on-s2-not-d)) p1) p2))))

  (defun angle-p1p2 (angle nat pos)
    (/ (+ (* 2 (acl2-pi) nat) angle) pos))

  (defun generate-angles (n)
    (if (zp n)
        nil
      (let ((p1 (caaar (p1p2-n-p-sequence n)))
            (p2 (cadaar (p1p2-n-p-sequence n)))
            (nat (cadar (p1p2-n-p-sequence n)))
            (pos (cadr (p1p2-n-p-sequence n))))
        (if (exists-angle>=0<2pi p1 p2)
            (append (generate-angles (- n 1)) (list (angle-p1p2 (exists-angle>=0<2pi-witness p1 p2) nat pos)))
          (append (generate-angles (- n 1)) (list nil))))))

  (defthmd realp-angle-p1p2
    (implies (and (realp angle)
                  (realp nat)
                  (realp pos))
             (realp (angle-p1p2 angle nat pos))))

  (defun angles-seq (n)
    (if (posp n)
        (nth (- n 1) (generate-angles n))
      0))

  (defun-sk nth-angle-exists (angle)
    (exists n
            (and (posp n)
                 (equal (angles-seq n) angle))))

  (encapsulate
    ()

    (local (include-book "arithmetic-5/top" :dir :system))

    (defthmd generate-angles-lemma1
      (implies (natp n)
               (equal (len (generate-angles n)) n))
      :hints (("Goal"
               :in-theory (disable p1p2-n-p-sequence rotation-about-witness point-on-s2-not-d)
               :induct (generate-angles n)
               )))
    )

  (encapsulate
    ()

    (local (include-book "arithmetic-5/top" :dir :system))

    (defthmd angles-countable-thm-1
      (implies (and (posp (- n 1))
                    (natp q)
                    (< q (len (generate-angles (- n 1)))))
               (equal (nth q (generate-angles n))
                      (nth q (generate-angles (- n 1)))))
      :hints (("Goal"
               :in-theory (disable p1p2-n-p-sequence rotation-about-witness point-on-s2-not-d angle-p1p2)
               )))
    )

  (encapsulate
    ()

    (local (include-book "arithmetic/top" :dir :system))

    (defthmd angles-countable-thm-2
      (implies (and (posp n)
                    (natp q)
                    (< q (len (generate-angles n))))
               (equal (nth q (generate-angles n))
                      (let ((p1 (caaar (p1p2-n-p-sequence (+ q 1))))
                            (p2 (cadaar (p1p2-n-p-sequence (+ q 1))))
                            (nat (cadar (p1p2-n-p-sequence (+ q 1))))
                            (pos (cadr (p1p2-n-p-sequence (+ q 1)))))
                        (if (exists-angle>=0<2pi p1 p2)
                            (angle-p1p2 (exists-angle>=0<2pi-witness p1 p2) nat pos)
                          nil))))
      :hints (("Goal"
               :in-theory (disable p1p2-n-p-sequence rotation-about-witness point-on-s2-not-d angle-p1p2)
               )
              ("Subgoal *1/3"
               :use ((:instance angles-countable-thm-1 (n n) (q q))
                     (:instance generate-angles-lemma1 (n n))
                     (:instance generate-angles-lemma1 (n (- n 1))))
               )
              ("Subgoal *1/2"
               :use ((:instance angles-countable-thm-1 (n n) (q q))
                     (:instance generate-angles-lemma1 (n n))
                     (:instance generate-angles-lemma1 (n (- n 1))))
               )
              ))
    )

  (defthmd angles-countable-thm
    (implies (and (posp n1)
                  (posp n2)
                  (posp n3)
                  (posp n4)
                  (equal (pole-seq n1) p1)
                  (equal (pole-seq n2) p2)
                  (equal (natp-seq n3) nat)
                  (equal (posp-seq n4) pos)
                  (realp angle)
                  (>= angle 0)
                  (< angle (* 2 (acl2-pi)))
                  (m-= (m-* (rotation-about-witness angle (point-on-s2-not-d)) p1) p2))
             (nth-angle-exists (/ (+ (* 2 (acl2-pi) nat) (exists-angle>=0<2pi-witness p1 p2)) pos)))
    :hints (("Goal"
             :use ((:instance p1p2-n-p-in-the-list (n1 n1) (n2 n2) (n3 n3) (n4 n4)
                              (p1 (pole-seq n1))
                              (p2 (pole-seq n2))
                              (nat (natp-seq n3))
                              (pos (posp-seq n4)))
                   (:instance angles-countable-thm-2
                              (q (- (p1p2-n-p-countable-witness (list (list (list p1 p2) nat) pos)) 1))
                              (n (p1p2-n-p-countable-witness (list (list (list p1 p2) nat) pos))))
                   (:instance generate-angles-lemma1
                              (n (p1p2-n-p-countable-witness (list (list (list p1 p2) nat) pos))))
                   (:instance nth-angle-exists-suff
                              (n (p1p2-n-p-countable-witness (list (list (list p1 p2) nat) pos)))
                              (angle angle))
                   (:instance exists-angle>=0<2pi-suff (p1 p1) (p2 p2)
                              (angle angle)))
             :in-theory (e/d () (p1p2-n-p-sequence pole-seq point-on-s2-not-d rotation-about-witness natp-seq posp-seq m-* m-= acl2-sqrt))
             )))

  (encapsulate
    ()

    (local (include-book "arithmetic/inequalities" :dir :system))

    (defthmd k-range-1
      (implies (and (integerp y)
                    (>= y (- x))
                    (< x 1))
               (>= y 0)))
    )

  (encapsulate
    ()

    (local (include-book "arithmetic-5/top" :dir :system))

    (defthmd k-range-2
      (implies (and (posp n)
                    (realp x)
                    (realp angle)
                    (>= angle 0)
                    (< angle (* 2 (acl2-pi)))
                    (>= x 0)
                    (integerp k)
                    (< x (* 2 (acl2-pi)))
                    (equal (* n angle)
                           (+ (* 2 (acl2-pi) k) x)))
               (equal (/ (- (* n angle) x) (* 2 (acl2-pi))) k)))
    )

  (encapsulate
    ()

    (local (include-book "arithmetic/inequalities" :dir :system))

    (defthmd k-range-3
      (implies (and (posp n)
                    (realp x)
                    (realp angle)
                    (>= angle 0)
                    (< angle (* 2 (acl2-pi)))
                    (>= x 0)
                    (integerp k)
                    (< x (* 2 (acl2-pi)))
                    (equal (* n angle)
                           (+ (* 2 (acl2-pi) k) x)))
               (>= k 0))
      :hints (("Goal"
               :use ((:instance k-range-1 (y k) (x (/ x (* 2 (acl2-pi)))))
                     (:instance k-range-2 (n n) (x x) (angle angle) (k k)))
               )))
    )

  ------------------------

  ;; (defun-sk nth-pole-exists (p)
  ;;   (exists n
  ;;           (and (posp n)
  ;;                (m-= (pole-seq n) p))))


  ;; (defthmd poles-countable-thm
  ;;   (implies (d-p p)
  ;;            (nth-pole-exists p))

  ;; (defthmd natnum-countable-thm
  ;;   (implies (natp num)
  ;;            (num>=0-exists num))
  (encapsulate
    ()

    (local (include-book "arithmetic/top" :dir :system))

    (defthmd angles-countable
      (implies (and (d-p p1)
                    (d-p p2)
                    (realp angle)
                    (posp n)
                    (>= angle 0)
                    (< angle (* 2 (acl2-pi)))
                    (m-= (m-* (rotation-about-witness (* n angle) (point-on-s2-not-d)) p1) p2))
               (nth-angle-exists angle))
      :hints (("Goal"
               :use ((:instance poles-countable-thm (p p1))
                     (:instance poles-countable-thm (p p2))
                     (:instance natnum-countable-thm (num (/ (- (* n angle) (mod (* n angle) (* 2 (acl2-pi))))
                                                             (* 2 (acl2-pi)))))
                     (:instance k-range-3 (n n) (x (mod (* n angle) (* 2 (acl2-pi)))) (angle angle)
                                (k (/ (- (* n angle) (mod (* n angle) (* 2 (acl2-pi))))
                                      (* 2 (acl2-pi)))))
                     (:instance integerp-r-mod-r-x/x (r (* n angle)) (x (* 2 (acl2-pi))))
                     (:instance realnum-equiv (r (* n angle)) (x (* 2 (acl2-pi))))
                     (:instance posp-countable-thm (num n))
                     (:instance exists-angle>=0<2pi-suff (p1 p1) (p2 p2) (angle (mod (* n angle) (* 2 (acl2-pi)))))
                     (:instance range-mod-r-x (r (* n angle)) (x (* 2 (acl2-pi))))
                     (:instance angles-countable-thm
                                (n1 (nth-pole-exists-witness p1))
                                (n2 (nth-pole-exists-witness p2))
                                (n3 (num>=0-exists-witness (/ (- (* n angle) (mod (* n angle) (* 2 (acl2-pi))))
                                                              (* 2 (acl2-pi)))))
                                (n4 (num>=1-exists-witness n))
                                (p1 (pole-seq (nth-pole-exists-witness p1)))
                                (p2 (pole-seq (nth-pole-exists-witness p2)))
                                (nat (/ (- (* n angle) (mod (* n angle) (* 2 (acl2-pi))))
                                        (* 2 (acl2-pi))))
                                (pos n)
                                (angle (mod (* n angle) (* 2 (acl2-pi))))))
               :in-theory (e/d () (d-p rotation-about-witness point-on-s2-not-d m-* acl2-sqrt mod EXISTS-ANGLE>=0<2PI-SUFF))

               )))
    )
















  -------------------------------------

  (defun-sk exists-angle-p1-p2 (p1 p2)
    (exists angle
            (and (>= angle 0)
                 (< angle (* 2 (acl2-pi)))
                 (m-= (m-* (rotation-about-witness angle (point-on-s2-not-d)) p1)
                      p2))))

  (defun angle-between-p1-p2 (p1 p2)
    (if (exists-angle-p1-p2 p1 p2)
        (exists-angle-p1-p2-witness p1 p2)
      0))

  (defun generate-angle-2 (point poles-list2)
    (if (atom poles-list2)
        nil
      (append (list (angle-between-p1-p2 point (car poles-list2)))
              (generate-angle-2 point (cdr poles-list2)))))

  (defun generate-angle-1 (poles-list1 poles-list2)
    (if (atom poles-list1)
        nil
      (append (generate-angle-2 (car poles-list1) poles-list2)
              (generate-angle-1 (cdr poles-list1) poles-list2))))

  (defun generate-angles (poles-list)
    (if (atom poles-list)
        nil
      (generate-angle-1 poles-list poles-list)))


  (defun angle-0-2pi-sequence (n)
    (nth n (generate-angles (poles-list (generate-words-main (+ n 1))))))

  (defun-sk exists-angle0-2pi (angle)
    (exists n
            (and (natp n)
                 (equal (angle-0-2pi-sequence n) angle))))

  (defthmd exists-angle-0-2pi-thm
    (implies (and (d-p p1)
                  (d-p p2)
                  (realp angle)
                  (>= angle 0)
                  (< angle (* 2 (acl2-pi)))
                  (m-= (m-* (rotation-about-witness angle (point-on-s2-not-d)) p1)
                       p2))
             (exists-angle0-2pi angle)))

  -----

  (encapsulate
    ()

    (local (include-book "arithmetic-5/top" :dir :system))

    (defthmd k-range-1
      (implies (and (posp n)
                    (realp den)
                    (> den 0)
                    (realp x)
                    (< x den))
               (> (- n (/ x den)) 0)))
    )

  (defthmd k-range
    (implies (and (posp n)
                  (realp x)
                  (realp angle)
                  (>= angle 0)
                  (< angle (* 2 (acl2-pi)))
                  (>= x 0)
                  (integerp k)
                  (< x (* 2 (acl2-pi)))
                  (equal (* n angle)
                         (+ (* 2 (acl2-pi) k) x)))
             (and (>= k 0)
                  (< k (- n (/ x (* 2 (acl2-pi))))))))
  )









































---------------------------
(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd realnum-equiv
    (implies (and (realp r)
                  (realp x)
                  (> x 0))
             (equal (+ (* x (/ (- r (mod r x)) x)) (mod r x))
                    r))))

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd r-theta*p=p=>theta=2kpi
    (implies (and (point-in-r3 p)
                  (point-in-r3 u)
                  (realp angle)
                  (or (not (equal (point-in-r3-x1 p)
                                  (point-in-r3-x1 u)))
                      (not (equal (point-in-r3-x1 p)
                                  (point-in-r3-x1 u)))
                      (not (equal (point-in-r3-x1 p)
                                  (point-in-r3-x1 u))))
                  (or (not (equal (point-in-r3-x1 p)
                                  (- (point-in-r3-x1 u))))
                      (not (equal (point-in-r3-x1 p)
                                  (- (point-in-r3-x1 u))))
                      (not (equal (point-in-r3-x1 p)
                                  (- (point-in-r3-x1 u)))))
                  (equal (+ (* (point-in-r3-x1 p) (point-in-r3-x1 p))
                            (* (point-in-r3-y1 p) (point-in-r3-y1 p))
                            (* (point-in-r3-z1 p) (point-in-r3-z1 p)))
                         1)
                  (equal (+ (* (point-in-r3-x1 u) (point-in-r3-x1 u))
                            (* (point-in-r3-y1 u) (point-in-r3-y1 u))
                            (* (point-in-r3-z1 u) (point-in-r3-z1 u)))
                         1)
                  (equal (point-in-r3-y1 u) 0)
                  (m-= (m-* (rotation-about-witness angle u) p) p))
             (equal (* 2 (acl2-pi) (/ (- angle (mod angle (* 2 (acl2-pi)))) (* 2 (acl2-pi))))
                    angle))
    :hints (("Goal"
             :use ((:instance realnum-equiv (r angle) (x (* 2 (acl2-pi))))
                   (:instance integerp-r-mod-r-x/x (r angle) (x (* 2 (acl2-pi))))
                   (:instance range-mod-r-x (r angle) (x (* 2 (acl2-pi))))
                   (:instance rotation-angle=2pik
                              (k (/ (- angle (mod angle (* 2 (acl2-pi)))) (* 2 (acl2-pi))))
                              (u u)
                              (x (mod angle (* 2 (acl2-pi)))))
                   (:instance r-theta*p=p=>sine=0 (p p) (u u) (angle (mod angle (* 2 (acl2-pi)))))
                   (:instance r-theta*p=p=>cosine=1 (p p) (u u) (angle (mod angle (* 2 (acl2-pi)))))
                   (:instance sin=0-cos=1 (x (mod angle (* 2 (acl2-pi))))))
             :in-theory (e/d () (rotation-about-witness point-in-r3 point-in-r3-x1 point-in-r3-y1 point-in-r3-z1 aref2 m-= mod))
             )))
  )

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd r-theta1*p=r-theta2*p=>r-theta1-theta2*p=p
    (implies (and (realp angle1)
                  (realp angle2)
                  (point-in-r3 u)
                  (point-in-r3 p)
                  (equal (+ (* (point-in-r3-x1 u) (point-in-r3-x1 u))
                            (* (point-in-r3-y1 u) (point-in-r3-y1 u))
                            (* (point-in-r3-z1 u) (point-in-r3-z1 u)))
                         1)
                  (m-= (m-* (rotation-about-witness angle1 u) p)
                       (m-* (rotation-about-witness angle2 u) p)))
             (m-= (m-* (rotation-about-witness (- angle1 angle2) u) p)
                  p))
    :hints (("Goal"
             :use ((:instance r-t1*r-t2=r-t1+t2 (angle1 (- angle2)) (angle2 angle1) (u u))
                   (:instance r-t1*r-t2=r-t1+t2 (angle1 (- angle2)) (angle2 angle2) (u u))
                   (:instance r-theta*p=p=>r--theta*p=p-1
                              (m1 (m-* (rotation-about-witness angle1 u) p))
                              (m2 (m-* (rotation-about-witness angle2 u) p))
                              (m3 (m-* (rotation-about-witness (- angle2) u) p)))
                   (:instance r-theta*p=p=>r--theta*p=p-2
                              (m1 (rotation-about-witness (- angle2) u))
                              (m2 (rotation-about-witness angle1 u))
                              (m3 p)
                              (m4 (rotation-about-witness (- angle2) u))
                              (m5 (m-* (rotation-about-witness angle2 u) p)))
                   (:instance rotation-a-witn-of0 (p p) (u u)))
             :in-theory (e/d () (aref2 m-= m-* rotation-about-witness point-in-r3 point-in-r3-x1 point-in-r3-y1 point-in-r3-z1))
             ))
    )
  )

(encapsulate
  ()
  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd d-p=>d-p-p-1
    (implies (and (s2-def-p p1)
                  (point-in-r3 p2)
                  (equal (aref2 :fake-name p2 0 0) (- (aref2 :fake-name p1 0 0)))
                  (equal (aref2 :fake-name p2 1 0) (- (aref2 :fake-name p1 1 0)))
                  (equal (aref2 :fake-name p2 2 0) (- (aref2 :fake-name p1 2 0))))
             (s2-def-p p2))
    :hints (("Goal"
             :in-theory (disable aref2)
             )))
  )

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd d-p=>d-p-p-2-1
    (implies (r3-matrixp m)
             (and (equal (aref2 :fake-name (second (f-poles m)) 0 0)
                         (- (aref2 :fake-name (first (f-poles m)) 0 0)))
                  (equal (aref2 :fake-name (second (f-poles m)) 1 0)
                         (- (aref2 :fake-name (first (f-poles m)) 1 0)))
                  (equal (aref2 :fake-name (second (f-poles m)) 2 0)
                         (- (aref2 :fake-name (first (f-poles m)) 2 0)))))
    :hints (("Goal"
             :use ((:instance f-poles-prop-2 (m m)))
             :in-theory (disable aref2 f-poles acl2-sqrt square)
             )))

  (defthmd d-p=>d-p-p-2-2
    (implies (and (point-in-r3 p1)
                  (point-in-r3 p2)
                  (equal (aref2 :fake-name p2 0 0) (aref2 :fake-name p1 0 0))
                  (equal (aref2 :fake-name p2 1 0) (aref2 :fake-name p1 1 0))
                  (equal (aref2 :fake-name p2 2 0) (aref2 :fake-name p1 2 0)))
             (m-= p1 p2))
    :hints (("Goal"
             :in-theory (enable m-=)
             )))
  )

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd d-p=>d-p-p-2
    (implies (and (d-p p1)
                  (point-in-r3 p2)
                  (equal (aref2 :fake-name p2 0 0) (- (aref2 :fake-name p1 0 0)))
                  (equal (aref2 :fake-name p2 1 0) (- (aref2 :fake-name p1 1 0)))
                  (equal (aref2 :fake-name p2 2 0) (- (aref2 :fake-name p1 2 0)))
                  (m-= (first (poles (word-exists-witness p1))) p1))
             (m-= p2 (second (poles (word-exists-witness p1)))))
    :hints (("Goal"
             :use ((:instance s2-def-p (point p1))
                   (:instance point-in-r3 (x p1))
                   (:instance d-p=>d-p-p-2-2 (p1 p2) (p2 (second (poles (word-exists-witness p1)))))
                   (:instance d-p (point p1))
                   (:instance poles (w (word-exists-witness p1)))
                   (:instance word-exists (point p1))
                   (:instance d-p=>d-p-p-2-1 (m (rotation (word-exists-witness p1) (acl2-sqrt 2))))
                   (:instance r3-rotationp (m (rotation (word-exists-witness p1) (acl2-sqrt 2))))
                   (:instance f-poles-prop-3 (m (rotation (word-exists-witness p1) (acl2-sqrt 2))))
                   (:instance rotation-is-r3-rotationp (w (word-exists-witness p1)) (x (acl2-sqrt 2))))
             :in-theory (e/d (m-=) (aref2 reducedwordp rotation acl2-sqrt square aref2 m-trans r3-m-inverse r3-m-determinant r3-matrixp f-poles word-exists d-p d-p-implies))
             ))
    )

  (defthmd d-p=>d-p-p-3
    (implies (and (d-p p1)
                  (point-in-r3 p2)
                  (equal (aref2 :fake-name p2 0 0) (- (aref2 :fake-name p1 0 0)))
                  (equal (aref2 :fake-name p2 1 0) (- (aref2 :fake-name p1 1 0)))
                  (equal (aref2 :fake-name p2 2 0) (- (aref2 :fake-name p1 2 0)))
                  (m-= (second (poles (word-exists-witness p1))) p1))
             (m-= p2 (first (poles (word-exists-witness p1)))))
    :hints (("Goal"
             :use ((:instance s2-def-p (point p1))
                   (:instance point-in-r3 (x p1))
                   (:instance d-p=>d-p-p-2-2 (p1 p2) (p2 (first (poles (word-exists-witness p1)))))
                   (:instance d-p (point p1))
                   (:instance poles (w (word-exists-witness p1)))
                   (:instance word-exists (point p1))
                   (:instance d-p=>d-p-p-2-1 (m (rotation (word-exists-witness p1) (acl2-sqrt 2))))
                   (:instance r3-rotationp (m (rotation (word-exists-witness p1) (acl2-sqrt 2))))
                   (:instance f-poles-prop-3 (m (rotation (word-exists-witness p1) (acl2-sqrt 2))))
                   (:instance rotation-is-r3-rotationp (w (word-exists-witness p1)) (x (acl2-sqrt 2))))
             :in-theory (e/d (m-=) (aref2 reducedwordp rotation acl2-sqrt square aref2 m-trans r3-m-inverse r3-m-determinant r3-matrixp f-poles word-exists d-p d-p-implies))
             ))
    )
  )

(defthmd d-p=>d-p-p-4
  (implies (and (m-= p2 pole)
                (m-= (m-* rot pole) pole))
           (m-= (m-* rot p2) p2)))

(defthmd d-p=>d-p-p
  (implies (and (d-p p1)
                (point-in-r3 p2)
                (equal (aref2 :fake-name p2 0 0) (- (aref2 :fake-name p1 0 0)))
                (equal (aref2 :fake-name p2 1 0) (- (aref2 :fake-name p1 1 0)))
                (equal (aref2 :fake-name p2 2 0) (- (aref2 :fake-name p1 2 0))))
           (d-p p2))
  :hints (("Goal"
           :use ((:instance two-poles-for-all-rotations (p p1)))
           :cases ((m-= (first (poles (word-exists-witness p1))) p1)
                   (m-= (second (poles (word-exists-witness p1))) p1))
           :in-theory (disable reducedwordp d-p word-exists square s2-def-p wordp array2p word-exists-suff)
           )
          ("Subgoal 2"
           :use ((:instance d-p=>d-p-p-2 (p1 p1) (p2 p2))
                 (:instance d-p (point p1))
                 (:instance d-p (point p2))
                 (:instance word-exists-suff (point p2) (w (word-exists-witness p1)))
                 (:instance word-exists (point p1))
                 (:instance d-p=>d-p-p-1 (p1 p1) (p2 p2))
                 (:instance f-returns-poles-1-second (w  (word-exists-witness p1)))
                 (:instance d-p=>d-p-p-4 (p2 p2) (pole (second (poles (word-exists-witness p1))))
                            (rot (rotation (word-exists-witness p1) (acl2-sqrt 2))))
                 )
           :in-theory nil
           )
          ("Subgoal 1"
           :use ((:instance d-p=>d-p-p-3 (p1 p1) (p2 p2))
                 (:instance d-p (point p1))
                 (:instance d-p (point p2))
                 (:instance word-exists-suff (point p2) (w (word-exists-witness p1)))
                 (:instance word-exists (point p1))
                 (:instance d-p=>d-p-p-1 (p1 p1) (p2 p2))
                 (:instance f-returns-poles-1-first (w  (word-exists-witness p1)))
                 (:instance d-p=>d-p-p-4 (p2 p2) (pole (first (poles (word-exists-witness p1))))
                            (rot (rotation (word-exists-witness p1) (acl2-sqrt 2))))
                 )
           :in-theory nil
           )))

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd diff-d-p-p=>d-p-p1
    (implies (and (d-p p)
                  (point-in-r3 p1)
                  (m-= p p1))
             (d-p p1))
    :hints (("goal"
             :use ((:instance d-p (point p1))
                   (:instance word-exists-suff (w (word-exists-witness p)) (point p1))
                   (:instance d-p-p=>d-p-p1-lemma (m1 (rotation (word-exists-witness p) (acl2-sqrt 2)))
                              (m2 p) (m3 p1))
                   (:instance s2-def-p-p=>p1 (p p) (p1 p1)))

             :in-theory (e/d () (m-* acl2-sqrt reducedwordp rotation r3-rotationp acl2-sqrt word-exists-suff d-p))
             )))
  )

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd d-p-not-equal-to-u-n-u
    (implies (and (d-p p)
                  (point-in-r3 u)
                  (not (d-p u))
                  (point-in-r3 m-u)
                  (equal (aref2 :fake-name m-u 0 0)
                         (- (aref2 :fake-name u 0 0)))
                  (equal (aref2 :fake-name m-u 1 0)
                         (- (aref2 :fake-name u 1 0)))
                  (equal (aref2 :fake-name m-u 2 0)
                         (- (aref2 :fake-name u 2 0)))
                  )
             (and (not (m-= p u))
                  (not (m-= p m-u))))
    :hints (("Goal"
             :use ((:instance diff-d-p-p=>d-p-p1 (p p) (p1 u))
                   (:instance diff-d-p-p=>d-p-p1 (p p) (p1 m-u))
                   (:instance d-p=>d-p-p (p1 m-u) (p2 u)))
             :in-theory (e/d () (m-* acl2-sqrt reducedwordp rotation r3-rotationp acl2-sqrt word-exists-suff d-p))
             )))
  )

(defun angle-seq (n)
  (if (posp n)
      (nth (- n 1) (poles-list (generate-words-main n)))
    0))

(defun-sk nth-pole-exists (p)
  (exists n
          (and (posp n)
               (m-= (pole-seq n) p))))


(defthmd poles-countable-thm
  (implies (d-p p)
           (nth-pole-exists p))
  :hints (("Goal"
           :use ((:instance exists-pole-n-thm (p p))
                 (:instance exists-pole-n (pole p))
                 (:instance nth-pole-exists-suff (p p) (n (+ (exists-pole-n-witness p) 1))))
           :in-theory (e/d () (poles-list generate-words-main))
           )))






















































------------------------

(defthmd cos2pik+x
  (implies (integerp k)
           (equal (acl2-cosine (+ (* 2 (acl2-pi) k) x))
                  (acl2-cosine x)))
  :hints (("Goal"
           :use ((:instance cos-2npi (n k)))
           :in-theory (disable SINE-2X)
           )))

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd sin2pik+x
    (implies (integerp k)
             (equal (acl2-sine (+ (* 2 (acl2-pi) k) x))
                    (acl2-sine x)))
    :hints (("Goal"
             :use ((:instance sin-2npi (n k))
                   (:instance cos-2npi (n k)))
             :in-theory (disable sin-2npi COSINE-2X sine-2x)
             )))
  )


(defthmd rotation-a-witn-of0
  (implies (and (point-in-r3 p)
                (point-in-r3 u))
           (m-= (m-* (rotation-about-witness 0 u) p)
                p))
  :hints (("Goal"
           :use ((:instance m-*point-id=point (p1 p))
                 (:instance r-theta-0=id (u u)))
           :in-theory (e/d () (ASSOCIATIVITY-OF-M-* m-* aref2 rotation-about-witness point-in-r3-x1 point-in-r3-y1 point-in-r3-z1 id-rotation point-in-r3 (:EXECUTABLE-COUNTERPART ID-ROTATION)))
           )))

(defthmd rotation-angle=2pik
  (implies (and (integerp k)
                (point-in-r3 u))
           (equal (rotation-about-witness (+ (* 2 (acl2-pi) k) x) u)
                  (rotation-about-witness x u)))
  :hints (("Goal"
           :use ((:instance cos2pik+x (k k) (x x))
                 (:instance sin2pik+x (k k) (x x))
                 )
           )))

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd integerp-r-mod-r-x/x
    (implies (and (realp r)
                  (not (equal x 0))
                  (realp x))
             (integerp (/ (- r (mod r x)) x))))
  )

(encapsulate
  ()
  (local (include-book "workshops/1999/embedded/Exercises/Exercise1-2/Exercise1.2" :dir :system))
  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd range-mod-r-x
    (implies (and (realp r)
                  (realp x)
                  (> x 0))
             (and (>= (mod r x) 0)
                  (realp (mod r x))
                  (< (mod r x) x)))
    :hints (("Goal"
             :in-theory (enable mod floor1)
             )))
  )


----

(defthmd test-2002
  (implies (and (realp r)
;(>= r 0)
                (realp x)
;(not (equal x 0)))
                (< x 0))
           (and (>= (mod r x) 0)
                (realp (mod r x))))
;(< (mod r x) (- x))))
  :hints (("Goal"
           :in-theory (enable mod floor1)
           )))
)

(encapsulate
  ()
  (local (include-book "workshops/1999/embedded/Exercises/Exercise1-2/Exercise1.2" :dir :system))
  (defthmd test-200
    (implies (and (realp r)
                  (>= r 0)
                  (realp x)
                  (> x 0))
             (natp (/ (- r (mod r x)) x)))
    :hints (("Goal"
             :in-theory (enable mod)
             )))
  )

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))
;(local (include-book "workshops/1999/embedded/Exercises/Exercise1-2/Exercise1.2" :dir :system))

  (defthmd integerp-r-mod-r-x/x
    (implies (and (realp r)
                  (not (equal x 0))
                  (realp x))
             (integerp (/ (- r (mod r x)) x))))

  (local (include-book "workshops/1999/embedded/Exercises/Exercise1-2/Exercise1.2" :dir :system))

  (defthmd range-mod-r-x
    (implies (and (realp r)
                  (realp x)
                  (> x 0))
             (and (>= (mod r x) 0)
                  (< (mod r x) x)))
    :hints (("Goal"
             :in-theory (enable mod floor1)
             )))
  )











































-------------------------------------------------

(encapsulate
  ()

  (local (include-book "arithmetic/top" :dir :system))

  (defthmd sine-p2=0-lemma-4-2
    (implies (and (realp p)
                  (realp q)
                  (realp r)
                  (equal (* p q) r)
                  (not (equal q 0)))
             (equal (/ r q) p)))

  (defthmd sine-p2=0-lemma-4-1
    (IMPLIES (AND (NOT (EQUAL X 0))
                  (REALP X)
                  (REALP Z)
                  (REALP P1)
                  (REALP P3)
                  (EQUAL (* P1 Z) (* P3 X)))
             (equal (/ (* p1 z) x) p3))
    :hints (("Goal"
             :use ((:instance sine-p2=0-lemma-4-2 (r (* p1 z)) (p p3) (q x)))
             )))

  (defthmd sine-p2=0-lemma-4-3-1
    (implies (equal x y)
             (equal (* x z) (* y z))))

  (defthmd sine-p2=0-lemma-4-3
    (IMPLIES (AND (NOT (EQUAL X 0))
                  (EQUAL (* P1 (/ X) Z) P3)
                  (REALP X)
                  (REALP Z)
                  (REALP P1)
                  (REALP P3)
                  (EQUAL (+ (EXPT X 2) (EXPT Z 2)) 1)
                  (EQUAL (+ (EXPT P1 2) (EXPT P3 2)) 1)
                  (EQUAL (* P1 Z) (* P3 X)))
             (equal (+ (* p1 p1 x x) (* p1 p1 z z)) (* x x)))
    :hints (("Subgoal 1"
             :use ((:instance sine-p2=0-lemma-4-3-1
                              (x (+ (EXPT P1 2)
                                    (* (EXPT P1 2) (EXPT Z 2) (EXPT X -2))))
                              (y 1)
                              (z (expt x 2))))
             )
            ))

  (defthmd sine-p2=0-lemma-4-4
    (EQUAL (+ (* (EXPT P1 2) (EXPT X 2))
              (* (EXPT P1 2) (EXPT Z 2)))
           (* p1 p1 (+ (* x x) (* z z)))))

  (defthm sine-p2=0-lemma-4-5
    (implies (and (realp x)
                  (realp p1)
                  (equal (expt p1 2) (expt x 2)))
             (or (equal p1 x)
                 (equal p1 (- x))))
    :hints (("Goal"
             :use ((:instance sqrt-*-x-x (x x))
                   (:instance sqrt-*-x-x (x p1)))
             :in-theory (disable sqrt-*-x-x y-=-sqrt sqrt-=-y)
             ))
    :rule-classes nil)
  )

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd sine-p2=0-lemma
    (implies (and (realp x)
                  (realp z)
                  (equal (+ (* x x) (* z z)) 1)
                  (realp s)
                  (realp p2)
                  (equal (* z s p2) 0)
                  (equal (* x s p2) 0))
             (equal (* s p2) 0)))

  (defthm sine-p2=0-lemma-1
    (implies (and (realp x)
                  (realp z)
                  (equal (+ (* x x) (* z z)) 1)
                  (realp s)
                  (realp p2)
                  (equal (* z s p2) 0)
                  (equal (* x s p2) 0))
             (or (equal s 0)
                 (equal p2 0)))
    :rule-classes nil
    )

  (defthm sine-p2=0-lemma-2
    (implies (and (realp x)
                  (realp z)
                  (realp s)
                  (realp p1)
                  (realp p3)
                  (equal (- (* z s p1)
                            (* x s p3))
                         0))
             (or (equal s 0)
                 (equal (* z p1) (* x p3))))
    :rule-classes nil
    )

  (defthm sine-p2=0-lemma-3
    (implies (and (realp x)
                  (realp y)
                  (realp z)
                  (realp p1)
                  (realp p2)
                  (realp p3)
                  (equal y 0)
                  (equal p2 0)
                  (equal (+ (* x x) (* y y) (* z z)) 1)
                  (equal (+ (* p1 p1) (* p2 p2) (* p3 p3)) 1)
                  (equal (* z p1) (* x p3))
                  (equal x 0))
             (and (or (equal p3 z)
                      (equal p3 (- z)))
                  (equal p1 0)))
    :rule-classes nil)

  (defthm sine-p2=0-lemma-4
    (implies (and (realp x)
                  (realp y)
                  (realp z)
                  (realp p1)
                  (realp p2)
                  (realp p3)
                  (equal p2 0)
                  (equal y 0)
                  (equal (+ (* x x) (* y y) (* z z)) 1)
                  (equal (+ (* p1 p1) (* p2 p2) (* p3 p3)) 1)
                  (equal (* z p1) (* x p3)))
             (or (and (equal p1 x)
                      (equal p3 z))
                 (and (equal p1 (- x))
                      (equal p3 (- z)))))
    :hints (("Goal"
             :use ((:instance sine-p2=0-lemma-3 (x x) (y y) (z z) (p1 p1) (p2 p2) (p3 p3))
                   (:instance sine-p2=0-lemma-4-1 (x x) (z z) (p1 p1) (p3 p3))
                   (:instance sine-p2=0-lemma-4-3 (x x) (z z) (p1 p1) (p3 p3))
                   (:instance sine-p2=0-lemma-4-4 (p1 p1) (x x) (z z))
                   (:instance sine-p2=0-lemma-4-5)
                   )
             ))
    :rule-classes nil)
  )

(defthmd r-theta*p=p=>sine=0
  (implies (and (point-in-r3 p)
                (point-in-r3 u)
                (realp angle)
                (or (not (equal (point-in-r3-x1 p)
                                (point-in-r3-x1 u)))
                    (not (equal (point-in-r3-x1 p)
                                (point-in-r3-x1 u)))
                    (not (equal (point-in-r3-x1 p)
                                (point-in-r3-x1 u))))
                (or (not (equal (point-in-r3-x1 p)
                                (- (point-in-r3-x1 u))))
                    (not (equal (point-in-r3-x1 p)
                                (- (point-in-r3-x1 u))))
                    (not (equal (point-in-r3-x1 p)
                                (- (point-in-r3-x1 u)))))
                (equal (+ (* (point-in-r3-x1 p) (point-in-r3-x1 p))
                          (* (point-in-r3-y1 p) (point-in-r3-y1 p))
                          (* (point-in-r3-z1 p) (point-in-r3-z1 p)))
                       1)
                (equal (+ (* (point-in-r3-x1 u) (point-in-r3-x1 u))
                          (* (point-in-r3-y1 u) (point-in-r3-y1 u))
                          (* (point-in-r3-z1 u) (point-in-r3-z1 u)))
                       1)
                (equal (point-in-r3-y1 u) 0)
                (m-= (m-* (rotation-about-witness angle u) p) p))
           (equal (acl2-sine angle) 0))
  :hints (("Goal"
           :use ((:instance r-theta*p=p=>r--theta*p=p (p p) (u u) (angle angle))
                 (:instance r-theta*p=p-lemma1 (p p) (u u) (angle angle))
                 (:instance r-theta*p=p-lemma2 (p p) (u u) (angle angle))
                 (:instance sine-p2=0-lemma
                            (x (point-in-r3-x1 u))
                            (z (point-in-r3-z1 u))
                            (s (acl2-sine angle))
                            (p2 (point-in-r3-y1 p)))
                 (:instance sine-p2=0-lemma-1
                            (x (point-in-r3-x1 u))
                            (z (point-in-r3-z1 u))
                            (s (acl2-sine angle))
                            (p2 (point-in-r3-y1 p)))
                 (:instance sine-p2=0-lemma-2
                            (x (point-in-r3-x1 u))
                            (z (point-in-r3-z1 u))
                            (s (acl2-sine angle))
                            (p1 (point-in-r3-x1 p))
                            (p3 (point-in-r3-z1 p)))
                 (:instance sine-p2=0-lemma-4
                            (x (point-in-r3-x1 u))
                            (y (point-in-r3-y1 u))
                            (z (point-in-r3-z1 u))
                            (p1 (point-in-r3-x1 p))
                            (p2 (point-in-r3-y1 p))
                            (p3 (point-in-r3-z1 p)))
                 )
           :in-theory (disable aref2 m-= m-* r3-rotationp rotation-about-witness r3-matrixp)
           )))

(encapsulate
  ()

  (local (include-book "arithmetic/top" :dir :system))

  (defthmd r-theta*p=p=>cosine=1-lemma1
    (implies (and (point-in-r3 p)
                  (point-in-r3 u)
                  (realp angle)
                  (equal (point-in-r3-y1 u) 0)
                  (m-= (m-* (rotation-about-witness angle u) p) p)
                  (equal (acl2-sine angle) 0))
             (or (equal (acl2-cosine angle) 1)
                 (equal (point-in-r3-y1 p) 0)))
    :hints (("Goal"
             :use ((:instance m-=p1p2-implies
                              (p1 (m-* (rotation-about-witness angle u) p))
                              (p2 p))
                   (:instance r-theta*p=p-lemma2-1 (u u) (p p) (angle angle))
                   (:instance r-theta*p=p-lemma1-1 (m (rotation-about-witness angle u)) (p p))
                   (:instance r3-rotationp-r-theta-10 (angle angle) (p u))
                   (:instance r-theta*p=p-lemma1-2 (angle angle) (u u))
                   (:instance r-theta*p=p-lemma1-3 (u u) (p p) (angle angle))
                   )
             :in-theory (e/d () (m-= alist2p array2p m-* rotation-about-witness aref2-m-* aref2))
             )))

  (defthmd r-theta*p=p=>cosine=1-lemma2-1
    (implies (equal (- 1 (* x x)) (* z z))
             (equal (- (* 2 p1) (* 2 p1 x x))
                    (* 2 p1 z z))))

  (defthmd r-theta*p=p=>cosine=1-lemma2-2
    (implies (and (realp p1)
                  (realp p3)
                  (realp x)
                  (realp z)
                  (equal (+ (* x x) (* z z)) 1)
                  (equal (- (* 2 p1) (* 2 p1 x x))
                         (* 2 x p3 z)))
             (equal (* p1 z z) (* x p3 z)))
    :hints (("Goal"
             :use ((:instance r-theta*p=p=>cosine=1-lemma2-1 (p1 p1) (x x)))
             )))
  )

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd r-theta*p=p=>cosine=1-lemma2
    (implies (and (point-in-r3 p)
                  (point-in-r3 u)
                  (realp angle)
                  (equal (+ (* (point-in-r3-x1 u) (point-in-r3-x1 u))
                            (* (point-in-r3-y1 u) (point-in-r3-y1 u))
                            (* (point-in-r3-z1 u) (point-in-r3-z1 u)))
                         1)
                  (equal (point-in-r3-y1 u) 0)
                  (equal (point-in-r3-y1 p) 0)
                  (equal (acl2-cosine angle) -1)
                  (m-= (m-* (rotation-about-witness angle u) p) p)
                  (equal (acl2-sine angle) 0))
             (equal (* (point-in-r3-x1 p) (point-in-r3-z1 u) (point-in-r3-z1 u))
                    (* (point-in-r3-z1 p) (point-in-r3-x1 u) (point-in-r3-z1 u))))
    :hints (("Goal"
             :use ((:instance m-=p1p2-implies
                              (p1 (m-* (rotation-about-witness angle u) p))
                              (p2 p))
                   (:instance r-theta*p=p-lemma1-4 (u u) (p p) (angle angle))
                   (:instance r-theta*p=p-lemma1-1 (m (rotation-about-witness angle u)) (p p))
                   (:instance r3-rotationp-r-theta-10 (angle angle) (p u))
                   (:instance r-theta*p=p-lemma1-2 (angle angle) (u u))
                   (:instance r-theta*p=p-lemma1-3 (u u) (p p) (angle angle))
                   (:instance r-theta*p=p=>cosine=1-lemma2-2
                              (p1 (point-in-r3-x1 p))
                              (p3 (point-in-r3-z1 p))
                              (x (point-in-r3-x1 u))
                              (z (point-in-r3-z1 u)))
                   )
             :in-theory (e/d () (m-= alist2p array2p m-* rotation-about-witness aref2-m-* aref2))
             )))
  )

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd r-theta*p=p=>cosine=1-lemma3
    (implies (and (point-in-r3 p)
                  (point-in-r3 u)
                  (realp angle)
                  (equal (+ (* (point-in-r3-x1 u) (point-in-r3-x1 u))
                            (* (point-in-r3-y1 u) (point-in-r3-y1 u))
                            (* (point-in-r3-z1 u) (point-in-r3-z1 u)))
                         1)
                  (equal (point-in-r3-y1 u) 0)
                  (equal (point-in-r3-y1 p) 0)
                  (equal (acl2-cosine angle) -1)
                  (m-= (m-* (rotation-about-witness angle u) p) p)
                  (equal (acl2-sine angle) 0))
             (equal (* (point-in-r3-z1 p) (point-in-r3-x1 u) (point-in-r3-x1 u))
                    (* (point-in-r3-x1 p) (point-in-r3-z1 u) (point-in-r3-x1 u))))
    :hints (("Goal"
             :use ((:instance m-=p1p2-implies
                              (p1 (m-* (rotation-about-witness angle u) p))
                              (p2 p))
                   (:instance r-theta*p=p-lemma1-5 (u u) (p p) (angle angle))
                   (:instance r-theta*p=p-lemma1-1 (m (rotation-about-witness angle u)) (p p))
                   (:instance r3-rotationp-r-theta-10 (angle angle) (p u))
                   (:instance r-theta*p=p-lemma1-2 (angle angle) (u u))
                   (:instance r-theta*p=p-lemma1-3 (u u) (p p) (angle angle))
                   (:instance r-theta*p=p=>cosine=1-lemma2-2
                              (p3 (point-in-r3-x1 p))
                              (p1 (point-in-r3-z1 p))
                              (z (point-in-r3-x1 u))
                              (x (point-in-r3-z1 u)))
                   )
             :in-theory (e/d () (m-= alist2p array2p m-* rotation-about-witness aref2-m-* aref2))
             )))
  )

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd r-theta*p=p=>cosine=1-lemma4
    (implies (and (point-in-r3 p)
                  (point-in-r3 u)
                  (realp angle)
                  (equal (+ (* (point-in-r3-x1 u) (point-in-r3-x1 u))
                            (* (point-in-r3-y1 u) (point-in-r3-y1 u))
                            (* (point-in-r3-z1 u) (point-in-r3-z1 u)))
                         1)
                  (equal (+ (* (point-in-r3-x1 p) (point-in-r3-x1 p))
                            (* (point-in-r3-y1 p) (point-in-r3-y1 p))
                            (* (point-in-r3-z1 p) (point-in-r3-z1 p)))
                         1)
                  (or (not (equal (point-in-r3-x1 p)
                                  (point-in-r3-x1 u)))
                      (not (equal (point-in-r3-x1 p)
                                  (point-in-r3-x1 u)))
                      (not (equal (point-in-r3-x1 p)
                                  (point-in-r3-x1 u))))
                  (or (not (equal (point-in-r3-x1 p)
                                  (- (point-in-r3-x1 u))))
                      (not (equal (point-in-r3-x1 p)
                                  (- (point-in-r3-x1 u))))
                      (not (equal (point-in-r3-x1 p)
                                  (- (point-in-r3-x1 u)))))
                  (equal (* (point-in-r3-x1 p) (point-in-r3-z1 u) (point-in-r3-z1 u))
                         (* (point-in-r3-z1 p) (point-in-r3-x1 u) (point-in-r3-z1 u)))
                  (equal (* (point-in-r3-z1 p) (point-in-r3-x1 u) (point-in-r3-x1 u))
                         (* (point-in-r3-x1 p) (point-in-r3-z1 u) (point-in-r3-x1 u)))
                  (equal (point-in-r3-y1 u) 0)
                  (equal (point-in-r3-y1 p) 0))
             (and (not (equal (point-in-r3-z1 u) 0))
                  (not (equal (point-in-r3-x1 u) 0))))
    :hints (("Goal"
             :use ((:instance sine-p2=0-lemma-4-5
                              (x (point-in-r3-x1 u))
                              (p1 (point-in-r3-x1 p)))
                   (:instance sine-p2=0-lemma-4-5
                              (x (point-in-r3-z1 u))
                              (p1 (point-in-r3-z1 p)))
                   )
             )))
  )

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd r-theta*p=p=>cosine=1-lemma5
    (implies (and (point-in-r3 p)
                  (point-in-r3 u)
                  (realp angle)
                  (equal (+ (* (point-in-r3-x1 u) (point-in-r3-x1 u))
                            (* (point-in-r3-y1 u) (point-in-r3-y1 u))
                            (* (point-in-r3-z1 u) (point-in-r3-z1 u)))
                         1)
                  (equal (+ (* (point-in-r3-x1 p) (point-in-r3-x1 p))
                            (* (point-in-r3-y1 p) (point-in-r3-y1 p))
                            (* (point-in-r3-z1 p) (point-in-r3-z1 p)))
                         1)
                  (or (not (equal (point-in-r3-x1 p)
                                  (point-in-r3-x1 u)))
                      (not (equal (point-in-r3-x1 p)
                                  (point-in-r3-x1 u)))
                      (not (equal (point-in-r3-x1 p)
                                  (point-in-r3-x1 u))))
                  (or (not (equal (point-in-r3-x1 p)
                                  (- (point-in-r3-x1 u))))
                      (not (equal (point-in-r3-x1 p)
                                  (- (point-in-r3-x1 u))))
                      (not (equal (point-in-r3-x1 p)
                                  (- (point-in-r3-x1 u)))))
                  (equal (* (point-in-r3-x1 p) (point-in-r3-z1 u) (point-in-r3-z1 u))
                         (* (point-in-r3-z1 p) (point-in-r3-x1 u) (point-in-r3-z1 u)))
                  (equal (* (point-in-r3-z1 p) (point-in-r3-x1 u) (point-in-r3-x1 u))
                         (* (point-in-r3-x1 p) (point-in-r3-z1 u) (point-in-r3-x1 u)))
                  (equal (point-in-r3-y1 u) 0)
                  (equal (point-in-r3-y1 p) 0))
             (equal (* (point-in-r3-z1 u) (point-in-r3-x1 p))
                    (* (point-in-r3-x1 u) (point-in-r3-z1 p))))
    :hints (("Goal"
             :use (:instance r-theta*p=p=>cosine=1-lemma4 (p p) (u u))
             ))))

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))
  (defthmd r-theta*p=p=>cosine=1-1
    (implies (and (realp angle)
                  (equal (acl2-sine angle) 0))
             (or (equal (acl2-cosine angle) 1)
                 (equal (acl2-cosine angle) -1)))
    :hints (("Goal"
             :use ((:instance sin**2+cos**2 (x angle))
                   (:instance sine-p2=0-lemma-4-5 (p1 (acl2-cosine angle)) (x 1)))
             :in-theory (disable sin**2+cos**2)
             )))
  )


(defthmd r-theta*p=p=>cosine=1
  (implies (and (point-in-r3 p)
                (point-in-r3 u)
                (realp angle)
                (or (not (equal (point-in-r3-x1 p)
                                (point-in-r3-x1 u)))
                    (not (equal (point-in-r3-x1 p)
                                (point-in-r3-x1 u)))
                    (not (equal (point-in-r3-x1 p)
                                (point-in-r3-x1 u))))
                (or (not (equal (point-in-r3-x1 p)
                                (- (point-in-r3-x1 u))))
                    (not (equal (point-in-r3-x1 p)
                                (- (point-in-r3-x1 u))))
                    (not (equal (point-in-r3-x1 p)
                                (- (point-in-r3-x1 u)))))
                (equal (+ (* (point-in-r3-x1 p) (point-in-r3-x1 p))
                          (* (point-in-r3-y1 p) (point-in-r3-y1 p))
                          (* (point-in-r3-z1 p) (point-in-r3-z1 p)))
                       1)
                (equal (+ (* (point-in-r3-x1 u) (point-in-r3-x1 u))
                          (* (point-in-r3-y1 u) (point-in-r3-y1 u))
                          (* (point-in-r3-z1 u) (point-in-r3-z1 u)))
                       1)
                (equal (point-in-r3-y1 u) 0)
                (m-= (m-* (rotation-about-witness angle u) p) p))
           (equal (acl2-cosine angle) 1))
  :hints (("Goal"
           :use ((:instance r-theta*p=p=>sine=0 (p p) (u u))
                 (:instance r-theta*p=p=>cosine=1-lemma1 (p p) (u u))
                 (:instance r-theta*p=p=>cosine=1-lemma2 (p p) (u u))
                 (:instance r-theta*p=p=>cosine=1-lemma3 (p p) (u u))
                 (:instance r-theta*p=p=>cosine=1-lemma5 (p p) (u u))
                 (:instance r-theta*p=p=>cosine=1-1 (angle angle))
                 (:instance sine-p2=0-lemma-4
                            (x (point-in-r3-x1 u))
                            (y (point-in-r3-y1 u))
                            (z (point-in-r3-z1 u))
                            (p1 (point-in-r3-x1 p))
                            (p2 (point-in-r3-y1 p))
                            (p3 (point-in-r3-z1 p)))
                 )
           :in-theory (disable aref2 m-= m-* r3-rotationp rotation-about-witness r3-matrixp)
           )))

;;;;sin t = 0, cos t =1 => t=0 if t in [0,2*pi)


(defthmd sine-is-0-in-0<2pi=>x=0orpi-1
  (implies (and (realp x)
                (< 0 x)
                (< x (acl2-pi)))
           (> (acl2-sine x) 0))
  :hints (("Goal"
           :use ((:instance sine-positive-in-0-pi/2 (x x))
                 (:instance sine-positive-in-pi/2-pi (x x)))
           )))

;;is this true?

(defthmd sine-is-0-in-0<2pi=>x=0orpi-2
  (implies (and (realp x)
                (<= 0 x)
                (< x (acl2-pi))
                (equal (acl2-sine x) 0))
           (equal (* x x) 0))
  :hints (("Goal"
           :use ((:instance sine-is-0-in-0<2pi=>x=0orpi-1 (x x)))
           )))

(defthmd sine-is-0-in-0<2pi=>x=0orpi-3
  (implies (and (realp x)
                (< (acl2-pi) x)
                (< x (* 2 (acl2-pi))))
           (< (acl2-sine x) 0))
  :hints (("Goal"
           :use ((:instance sine-negative-in-pi-3pi/2 (x x))
                 (:instance sine-negative-in-3pi/2-2pi (x x)))
           )))

;;is this true?

(defthmd sine-is-0-in-0<2pi=>x=0orpi-4
  (implies (and (realp x)
                (<= (acl2-pi) x)
                (equal (acl2-sine x) 0)
                (< x (* 2 (acl2-pi))))
           (equal (* x x) (* (acl2-pi) (acl2-pi))))
  :hints (("Goal"
           :use ((:instance sine-is-0-in-0<2pi=>x=0orpi-3 (x x)))
           ))
  )

(defthmd sine-is-0-in-0<2pi=>x=0orpi-5
  (implies (and (realp x)
                (<= 0 x)
                (equal (acl2-sine x) 0)
                (< x (* 2 (acl2-pi))))
           (or (equal (* x x) 0)
               (equal (* x x) (* (acl2-pi) (acl2-pi)))))
  :hints (("Goal"
           :use ((:instance sine-is-0-in-0<2pi=>x=0orpi-2)
                 (:instance sine-is-0-in-0<2pi=>x=0orpi-4))
           )))

(encapsulate
  ()

  (local (include-book "nonstd/nsa/inverse-trig" :dir :system))

  (defthmd cosine-is-1-in-0<2pi=>x=0-1
    (implies (and (realp x)
                  (<= 0 x)
                  (equal (acl2-cosine x) 1)
                  (<= x (acl2-pi)))
             (equal (* x x) 0))
    :hints (("Goal"
             :cases ((equal x 0)
                     (not (equal x 0)))
             :use ((:instance cosine-positive-in-0-pi/2 (x x))
                   (:instance cosine-pi/2)
                   (:instance cosine-pi)
                   (:instance cosine-negative-in-pi/2-pi (x x)))
             )
            ("Subgoal 1"
             :use ((:instance cosine-is-1-1-on-domain (x1 0) (x2 x)))
             :in-theory (enable inside-interval-p)
             ))
    )

  (defthmd cosine-is-1-in-0<2pi=>x=0-5
    (implies (and (realp x)
                  (>= (acl2-pi) x)
                  (>= x 0)
                  (equal (acl2-cosine x) -1))
             (equal (* x x) (* (acl2-pi) (acl2-pi))))
    :hints (("Goal"
             :cases ((equal x (acl2-pi))
                     (not (equal x (acl2-pi))))
             )
            ("subgoal 1"
             :use ((:instance cosine-is-1-1-on-domain (x1 (acl2-pi)) (x2 x))
                   (:instance cosine-pi))
             :in-theory (e/d (inside-interval-p) (cosine-pi))
             )

            ))
  )

(encapsulate
  ()
  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd cosine-is-1-in-0<2pi=>x=0-2
    (implies (and (realp r)
                  (> r x)
                  (realp x)
                  (>= r 0)
                  (< r (* 2 x)))
             (equal (mod r x) (- r x))))

  (defthmd cosine-is-1-in-0<2pi=>x=0-3
    (implies (and (realp r)
                  (> r x)
                  (realp x)
                  (>= r 0)
                  (< r (* 2 x)))
             (and (equal (+ x (mod r x)) r)
                  (> (mod r x) 0)
                  (< (mod r x) x))))

  (defthmd cosine-is-1-in-0<2pi=>x=0-4
    (implies (and (realp x)
                  (< (acl2-pi) x)
                  (< x (* 2 (acl2-pi))))
             (equal (acl2-cosine x)
                    (- (acl2-cosine (mod x (acl2-pi))))))
    :hints (("Goal"
             :use ((:instance cosine-is-1-in-0<2pi=>x=0-3
                              (r x) (x (acl2-pi)))
                   (:instance cos-pi+x (x (mod x (acl2-pi)))))
             ))
    )

  (defthmd cosine-is-1-in-0<2pi=>x=0-6
    (implies (and (realp x)
                  (>= x 0)
                  (< x (* 2 (acl2-pi)))
                  (equal (acl2-cosine x) 1))
             (equal (* x x) 0))
    :hints (("Goal"
             :use ((:instance cosine-is-1-in-0<2pi=>x=0-1 (x x))
                   (:instance cosine-is-1-in-0<2pi=>x=0-4 (x x))
                   (:instance cosine-is-1-in-0<2pi=>x=0-3 (r x) (x (acl2-pi)))
                   (:instance cosine-is-1-in-0<2pi=>x=0-5 (x (mod x (acl2-pi))))
                   )
             )))
  )

(defthmd sin=0-cos=1
  (implies (and (realp x)
                (>= x 0)
                (< x (* 2 (acl2-pi)))
                (equal (acl2-sine x) 0)
                (equal (acl2-cosine x) 1))
           (equal (* x x) 0))
  :hints (("Goal"
           :use ((:instance sine-is-0-in-0<2pi=>x=0orpi-5 (x x))
                 (:instance cosine-is-1-in-0<2pi=>x=0-6 (x x)))
           )))

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd cos-2npi-n>=0-1
    (implies (and (integerp n)
                  (EQUAL (ACL2-COSINE (+ (* 2 (ACL2-PI))
                                         (* 2 (ACL2-PI) (+ N -1))))
                         1))
             (EQUAL (ACL2-COSINE (* 2 (ACL2-PI) N)) 1))
    :hints (("Goal"
             :in-theory (disable COSINE-OF-SUMS COS-2PI+X COSINE-2X)
             ))))

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (local
   (defun induction-hint (n)
     (if (and (integerp n)
              (< 0 n))
         (1+ (induction-hint (+ n -1)))
       1)))

  (local
   (defthm *-x-0
     (equal (* x 0) 0)))

  (local
   (defthm cos-2npi-n>=0
     (implies (and (integerp n)
                   (<= 0 n))
              (equal (acl2-cosine (* 2 (acl2-pi) n))
                     1))
     :hints (("Goal"
              :induct (induction-hint n))
             ("Subgoal *1/1"
              :use ((:instance cos-2pi+x (x (* 2 (ACL2-PI) (+ N -1))))
                    (:instance cos-2npi-n>=0-1 (n n)))
              :in-theory nil
              ))))

  (defthm cos-2npi
    (implies (integerp n)
             (equal (acl2-cosine (* 2 (acl2-pi) n))
                    1))
    :hints (("Goal"
             :cases ((< n 0)
                     (= n 0)
                     (> n 0)))
            ("Subgoal 3"
             :use ((:instance cos-uminus
                              (x (* 2 (acl2-pi) n)))
                   (:instance cos-2npi-n>=0 (n (- n))))
             :in-theory (disable cos-uminus cos-2npi-n>=0 COSINE-2X))))

  )












-------------
;;is this true?

(defthmd sine-is-0-in-0<2pi=>x=0orpi-2
  (implies (and (realp x)
                (<= 0 x)
                (< x (acl2-pi))
                (equal (acl2-sine x) 0))
           (equal (* x x) 0))
  :hints (("Goal"
           :cases ((equal x 0)
                   (not (equal x 0)))
           :use ((:instance sine-is-0-in-0<2pi=>x=0orpi-1 (x x)))
           )))

(defthmd sine-is-0-in-0<2pi=>x=0orpi-3
  (implies (and (realp x)
                (< (acl2-pi) x)
                (< x (* 2 (acl2-pi))))
           (< (acl2-sine x) 0))
  :hints (("Goal"
           :use ((:instance sine-negative-in-pi-3pi/2 (x x))
                 (:instance sine-negative-in-3pi/2-2pi (x x)))
           )))

;;is this true?

(defthmd sine-is-0-in-0<2pi=>x=0orpi-4
  (implies (and (realp x)
                (<= (acl2-pi) x)
                (equal (acl2-sine x) 0)
                (< x (* 2 (acl2-pi))))
           (equal (* x x) (* (acl2-pi) (acl2-pi))))
  :hints (("Goal"
           :use ((:instance sine-is-0-in-0<2pi=>x=0orpi-3 (x x)))
;(:instance sine-negative-in-3pi/2-2pi (x x)))
           ))
;:rule-classes nil
  )

(defthmd sine-is-0-in-0<2pi=>x=0orpi-5
  (implies (and (realp x)
                (<= 0 x)
                (equal (acl2-sine x) 0)
                (< x (* 2 (acl2-pi))))
           (or (equal (* x x) 0)
               (equal (* x x) (* (acl2-pi) (acl2-pi)))))
  :hints (("Goal"
           :use ((:instance sine-is-0-in-0<2pi=>x=0orpi-2)
                 (:instance sine-is-0-in-0<2pi=>x=0orpi-4))
           )))

-----

(encapsulate
  ()

  (local (include-book "arithmetic/top" :dir :system))

  (defthmd cosine-is-1-in-0<2pi=>x=0-1
    (implies (and (realp x)
                  (equal (acl2-cosine x) 1)
                  (<= 0 x)
                  (< x (* 2 (acl2-pi))))
             (equal (* x x) 0))
    :hints (("Goal"
             ;; :cases ((and (> x 0) (< x (* 1/2 (acl2-pi))))
             ;;         (and (> x (* 1/2 (acl2-pi))) (< x (acl2-pi)))
             ;;         (and (> x (* 3/2 (acl2-pi))) (< x (* 2 (acl2-pi))))
             ;;         (and (> x (acl2-pi)) (< x (* 3/2 (acl2-pi))))
             ;;         (equal x 0)
             ;;         (equal x (* 1/2 (acl2-pi)))
             ;;         (equal x (* 3/2 (acl2-pi))))
             :use ((:instance cosine-positive-in-0-pi/2 (x x))
                   (:instance cosine-positive-in-3pi/2-2pi (x x))
                   (:instance cosine-negative-in-pi/2-pi (x x))
                   (:instance cosine-0)
                   (:instance cosine-pi/2)
                   (:instance cosine-3pi/2)
                   (:instance cosine-negative-in-pi/2-pi (x x)))
             :in-theory (disable cosine-positive-in-0-pi/2 cosine-positive-in-3pi/2-2pi cosine-negative-in-pi/2-pi cosine-0 cosine-pi/2 cosine-3pi/2 cosine-negative-in-pi/2-pi)
             )
            ("Subgoal 2"
             :cases ((equal x (* 1/2 (acl2-pi)))
                     (equal x 0))
             :use ((:instance cosine-positive-in-0-pi/2 (x x))
                   (:instance cosine-0)
                   (:instance cosine-pi/2))
             )
            ))
  )

;;is this true?

(defthmd sine-is-0-in-0<pi=>x=0orpi-2
  (implies (and (realp x)
                (<= 0 x)
                (< x (acl2-pi))
                (equal (acl2-sine x) 0))
           (equal (* x x) 0))
  :hints (("Goal"
           :use ((:instance sine-is-0-in-0<pi=>x=0orpi-1 (x x)))
           )))

(defthmd sine-is-0-in-0<pi=>x=0orpi-3
  (implies (and (realp x)
                (< (acl2-pi) x)
                (< x (* 2 (acl2-pi))))
           (< (acl2-sine x) 0))
  :hints (("Goal"
           :use ((:instance sine-negative-in-pi-3pi/2 (x x))
                 (:instance sine-negative-in-3pi/2-2pi (x x)))
           )))

;;is this true?

(defthmd sine-is-0-in-0<pi=>x=0orpi-4
  (implies (and (realp x)
                (<= (acl2-pi) x)
                (equal (acl2-sine x) 0)
                (< x (* 2 (acl2-pi))))
           (equal (* x x) (* (acl2-pi) (acl2-pi))))
  :hints (("Goal"
           :use ((:instance sine-is-0-in-0<pi=>x=0orpi-3 (x x)))
;(:instance sine-negative-in-3pi/2-2pi (x x)))
           ))
;:rule-classes nil
  )

(defthmd sine-is-0-in-0<pi=>x=0orpi-5
  (implies (and (realp x)
                (<= 0 x)
                (equal (acl2-sine x) 0)
                (< x (* 2 (acl2-pi))))
           (or (equal (* x x) 0)
               (equal (* x x) (* (acl2-pi) (acl2-pi)))))
  :hints (("Goal"
           :use ((:instance sine-is-0-in-0<pi=>x=0orpi-2)
                 (:instance sine-is-0-in-0<pi=>x=0orpi-4))
           )))


----






--------------

(defthmd sine-is-0-in-0<pi=>x=0-1
  (implies (and (realp x)
                (< 0 x)
                (< x (acl2-pi)))
           (> (acl2-sine x) 0))
  :hints (("Goal"
           :use ((:instance sine-positive-in-0-pi/2 (x x))
                 (:instance sine-positive-in-pi/2-pi (x x)))
           )))


(defthmd sine-is-0-in-0<pi=>x=0
  (implies (and (realp x)
                (<= 0 x)
                (< x (acl2-pi))
                (equal (acl2-sine x) 0))
           (equal (* x x) 0))
  :hints (("Goal"
           :use ((:instance sine-is-0-in-0<pi=>x=0-1 (x x)))
           ))
  )

----


; Added by Matt K. for v2-7.
(add-match-free-override :once t)
(set-match-free-default :once)

(local
 (defun sine-interval (y)
   (declare (ignore y))
   (interval (- (/ (acl2-pi) 2)) (/ (acl2-pi) 2))))

(local
 (defun cosine-interval (y)
   (declare (ignore y))
   (interval 0 (acl2-pi))))

(local
 (defthm trivial-subinterval
   (implies (and (realp x)
                 (realp y)
                 (< x y))
            (subinterval-p (interval x y) (interval x y)))
   :hints (("Goal"
	    :in-theory (enable interval-definition-theory)))))

(local
 (defthm *-x-0
   (equal (* x 0) 0)))

(local
 (defthm-std standard-pi
   (standardp (acl2-pi))))

(local
 (defthm-std standard-exp
   (implies (standardp x)
            (standardp (acl2-exp x)))))


(local
 (defthm-std standard-cosine
   (implies (standardp x)
            (standardp (acl2-cosine x)))))


(encapsulate
  ()
  (local
   (defthm lemma-1
     (implies (and (realp c)
                   (realp s)
                   (equal (+ (* s s) (* c c)) 1))
              (<= c 1))))
  (local
   (defthm lemma-2
     (implies (and (realp c)
                   (realp s)
                   (equal (+ (* s s) (* c c)) 1))
              (<= -1 c))
     :hints (("Goal"
              :use ((:instance lemma-1 (c (- c))))
              :in-theory (disable lemma-1)))))
  (defthm cosine-bound
    (implies (realp x)
             (and (<= -1 (acl2-cosine x))
                  (<= (acl2-cosine x) 1)))
    :hints (("Goal"
             :use ((:instance lemma-1
                              (s (acl2-sine x))
                              (c (acl2-cosine x)))
                   (:instance lemma-2
                              (s (acl2-sine x))
                              (c (acl2-cosine x))))
             :in-theory (disable lemma-1 lemma-2))))
  )

(local
 (defthm standard-part-<=-acl2-pi
   (implies (and (realp x)
                 (<= x (acl2-pi)))
            (<= (standard-part x) (acl2-pi)))
   :hints (("Goal"
            :use ((:instance standard-part-<=
                             (x x)
                             (y (acl2-pi))))
            :in-theory (disable standard-part-<=)))))

(encapsulate
  ()
  (local
   (defthm lemma-1-1-1
     (implies (and (realp x)
                   (realp y)
                   (<= 0 x)
                   (< x y)
                   (<= y (acl2-pi)))
              (and (<= 0 (- y x))
                   (<= (- y x) (acl2-pi))))))
  (local
   (defthm lemma-1-1-2
     (equal (acl2-sine (* 1/2 (acl2-pi))) 1)))
  (local
   (defthm lemma-1-1-3
     (implies (and (realp x)
                   (<= 0 x)
                   (<= x (acl2-pi)))
              (<= 0 (acl2-sine x)))
     :hints (("goal"
              :use ((:instance sine-positive-in-0-pi/2)
                    (:instance sine-positive-in-pi/2-pi))
              :in-theory (disable sine-positive-in-0-pi/2
                                  sine-positive-in-pi/2-pi
                                  sine-2x
                                  sine-3x)))))

  (defthm test-case
    (implies (and (realp x)
                  (< 0 x)
                  (< x (acl2-pi)))
             (> (acl2-sine x) 0)))
;(or (equal (* x x) 0)
;   (equal (acl2-pi) x))))
  )

---

(include-book "hausdorff-paradox-2")
(include-book "nonstd/nsa/trig" :dir :system)

;; Title: A Formal Proof of the Banach-Tarski Theorem in ACL2(r)

;; Abstract: The Banach-Tarski theorem states that a solid ball can be partitioned into a finite number of pieces which can be rotated to form two identical copies of the ball. The proof of the Banach-Tarski theorem involves generating a free group of rotations and then decomposing the ball using these rotations and rearranging them to get two copies of the ball. The key ingredients to the proof are the Hausdorff paradox and the proof that the reals are uncountable. Denumerability of reals has already been proved in ACL2(r) and now we have proved the Hausdorff and currently, we are working to prove the Banach-Tarski theorem for a solid ball centered at the origin with radius equal to 1. In this paper we present a formal proof of the Hausdorff Paradox in ACL2(r).

(defthmd test-202
  (implies (and (not (equal th1 th2))
                (>= th1 0)
                (< th1 (* 2 (acl2-pi)))
                (>= th2 0)
                (< th2 (* 2 (acl2-pi))))
           (not (equal (acl2-sine th1) (acl2-sine th2))))
  :hints (("Goal"
           :use ((:instance acl2-sine (x th1))
                 (:instance acl2-sine (x th2)))
           :in-theory (enable (acl2-sine))
           )))

---

(encapsulate
  ()
  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd d-p=>d-p-p-1
    (implies (and (s2-def-p p1)
                  (point-in-r3 p2)
                  (equal (aref2 :fake-name p2 0 0) (- (aref2 :fake-name p1 0 0)))
                  (equal (aref2 :fake-name p2 1 0) (- (aref2 :fake-name p1 1 0)))
                  (equal (aref2 :fake-name p2 2 0) (- (aref2 :fake-name p1 2 0))))
             (s2-def-p p2))
    :hints (("Goal"
             :in-theory (disable aref2)
             )))
  )

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd d-p=>d-p-p-2-1
    (implies (r3-matrixp m)
             (and (equal (aref2 :fake-name (second (f-poles m)) 0 0)
                         (- (aref2 :fake-name (first (f-poles m)) 0 0)))
                  (equal (aref2 :fake-name (second (f-poles m)) 1 0)
                         (- (aref2 :fake-name (first (f-poles m)) 1 0)))
                  (equal (aref2 :fake-name (second (f-poles m)) 2 0)
                         (- (aref2 :fake-name (first (f-poles m)) 2 0)))))
    :hints (("Goal"
             :use ((:instance f-poles-prop-2 (m m)))
             :in-theory (disable aref2 f-poles acl2-sqrt square)
             )))

  (defthmd d-p=>d-p-p-2-2
    (implies (and (point-in-r3 p1)
                  (point-in-r3 p2)
                  (equal (aref2 :fake-name p2 0 0) (aref2 :fake-name p1 0 0))
                  (equal (aref2 :fake-name p2 1 0) (aref2 :fake-name p1 1 0))
                  (equal (aref2 :fake-name p2 2 0) (aref2 :fake-name p1 2 0)))
             (m-= p1 p2))
    :hints (("Goal"
             :in-theory (enable m-=)
             )))
  )

(defthmd test-202
  (implies (and (not (equal th1 th2))
                (>= th1 0)
                (< th1 (* 2 (acl2-pi)))
                (>= th2 0)
                (< th2 (* 2 (acl2-pi))))
           (not (equal (acl2-sine th1) (acl2-sine th2))))
  :hints (("Goal"
           :use ((:instance acl2-sine (x th1))
                 (:instance acl2-sine (x th2)))
           :in-theory (enable (acl2-sine))
           )))

----

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd d-p=>d-p-p-2
    (implies (and (d-p p1)
                  (point-in-r3 p2)
                  (equal (aref2 :fake-name p2 0 0) (- (aref2 :fake-name p1 0 0)))
                  (equal (aref2 :fake-name p2 1 0) (- (aref2 :fake-name p1 1 0)))
                  (equal (aref2 :fake-name p2 2 0) (- (aref2 :fake-name p1 2 0)))
                  (m-= (first (poles (word-exists-witness p1))) p1))
             (m-= p2 (second (poles (word-exists-witness p1)))))
    :hints (("Goal"
             :use ((:instance s2-def-p (point p1))
                   (:instance point-in-r3 (x p1))
                   (:instance d-p=>d-p-p-2-2 (p1 p2) (p2 (second (poles (word-exists-witness p1)))))
                   (:instance d-p (point p1))
                   (:instance poles (w (word-exists-witness p1)))
                   (:instance word-exists (point p1))
                   (:instance d-p=>d-p-p-2-1 (m (rotation (word-exists-witness p1) (acl2-sqrt 2))))
                   (:instance r3-rotationp (m (rotation (word-exists-witness p1) (acl2-sqrt 2))))
                   (:instance f-poles-prop-3 (m (rotation (word-exists-witness p1) (acl2-sqrt 2))))
                   (:instance rotation-is-r3-rotationp (w (word-exists-witness p1)) (x (acl2-sqrt 2))))
             :in-theory (e/d (m-=) (aref2 reducedwordp rotation acl2-sqrt square aref2 m-trans r3-m-inverse r3-m-determinant r3-matrixp f-poles word-exists d-p d-p-implies))
             ))
    )

  (defthmd d-p=>d-p-p-3
    (implies (and (d-p p1)
                  (point-in-r3 p2)
                  (equal (aref2 :fake-name p2 0 0) (- (aref2 :fake-name p1 0 0)))
                  (equal (aref2 :fake-name p2 1 0) (- (aref2 :fake-name p1 1 0)))
                  (equal (aref2 :fake-name p2 2 0) (- (aref2 :fake-name p1 2 0)))
                  (m-= (second (poles (word-exists-witness p1))) p1))
             (m-= p2 (first (poles (word-exists-witness p1)))))
    :hints (("Goal"
             :use ((:instance s2-def-p (point p1))
                   (:instance point-in-r3 (x p1))
                   (:instance d-p=>d-p-p-2-2 (p1 p2) (p2 (first (poles (word-exists-witness p1)))))
                   (:instance d-p (point p1))
                   (:instance poles (w (word-exists-witness p1)))
                   (:instance word-exists (point p1))
                   (:instance d-p=>d-p-p-2-1 (m (rotation (word-exists-witness p1) (acl2-sqrt 2))))
                   (:instance r3-rotationp (m (rotation (word-exists-witness p1) (acl2-sqrt 2))))
                   (:instance f-poles-prop-3 (m (rotation (word-exists-witness p1) (acl2-sqrt 2))))
                   (:instance rotation-is-r3-rotationp (w (word-exists-witness p1)) (x (acl2-sqrt 2))))
             :in-theory (e/d (m-=) (aref2 reducedwordp rotation acl2-sqrt square aref2 m-trans r3-m-inverse r3-m-determinant r3-matrixp f-poles word-exists d-p d-p-implies))
             ))
    )
  )

(defthmd d-p=>d-p-p-4
  (implies (and (m-= p2 pole)
                (m-= (m-* rot pole) pole))
           (m-= (m-* rot p2) p2)))

(defthmd d-p=>d-p-p
  (implies (and (d-p p1)
                (point-in-r3 p2)
                (equal (aref2 :fake-name p2 0 0) (- (aref2 :fake-name p1 0 0)))
                (equal (aref2 :fake-name p2 1 0) (- (aref2 :fake-name p1 1 0)))
                (equal (aref2 :fake-name p2 2 0) (- (aref2 :fake-name p1 2 0))))
           (d-p p2))
  :hints (("Goal"
           :use ((:instance two-poles-for-all-rotations (p p1)))
           :cases ((m-= (first (poles (word-exists-witness p1))) p1)
                   (m-= (second (poles (word-exists-witness p1))) p1))
           :in-theory (disable reducedwordp d-p word-exists square s2-def-p wordp array2p word-exists-suff)
           )
          ("Subgoal 2"
           :use ((:instance d-p=>d-p-p-2 (p1 p1) (p2 p2))
                 (:instance d-p (point p1))
                 (:instance d-p (point p2))
                 (:instance word-exists-suff (point p2) (w (word-exists-witness p1)))
                 (:instance word-exists (point p1))
                 (:instance d-p=>d-p-p-1 (p1 p1) (p2 p2))
                 (:instance f-returns-poles-1-second (w  (word-exists-witness p1)))
                 (:instance d-p=>d-p-p-4 (p2 p2) (pole (second (poles (word-exists-witness p1))))
                            (rot (rotation (word-exists-witness p1) (acl2-sqrt 2))))
                 )
           :in-theory nil
           )
          ("Subgoal 1"
           :use ((:instance d-p=>d-p-p-3 (p1 p1) (p2 p2))
                 (:instance d-p (point p1))
                 (:instance d-p (point p2))
                 (:instance word-exists-suff (point p2) (w (word-exists-witness p1)))
                 (:instance word-exists (point p1))
                 (:instance d-p=>d-p-p-1 (p1 p1) (p2 p2))
                 (:instance f-returns-poles-1-first (w  (word-exists-witness p1)))
                 (:instance d-p=>d-p-p-4 (p2 p2) (pole (first (poles (word-exists-witness p1))))
                            (rot (rotation (word-exists-witness p1) (acl2-sqrt 2))))
                 )
           :in-theory nil
           )

          )
  )

----

(defthmd witness-not-in-x-coord-sequence-1
  (and (realp (exists-in-interval-but-not-in-x-coord-sequence-witness -1 1))
       (realp (acl2-sqrt (- 1 (* (exists-in-interval-but-not-in-x-coord-sequence-witness -1 1)
                                 (exists-in-interval-but-not-in-x-coord-sequence-witness -1 1))))))
  ;; (<= -1 (exists-in-interval-but-not-in-x-coord-sequence-witness -1 1))
  ;; (<= (exists-in-interval-but-not-in-x-coord-sequence-witness -1 1) 1))
  :hints (("goal"
           :use ((:instance witness-not-in-x-coord-sequence)
                 (:instance exists-point-on-s2-not-d-2))
           )))

(defun rotation-about-witness (angle point)
  `((:header :dimensions (3 3)
             :maximum-length 10)
    ((0 . 0) . ,(+ (acl2-cosine angle)
                   (* (point-in-r3-x1 point) (point-in-r3-x1 point) (- 1 (acl2-cosine angle)))) )
    ((0 . 1) . ,(- (* (point-in-r3-x1 point) (point-in-r3-y1 point) (- 1 (acl2-cosine angle)))
                   (* (point-in-r3-z1 point) (acl2-sine angle))) )
    ((0 . 2) . ,(+ (* (point-in-r3-x1 point) (point-in-r3-z1 point) (- 1 (acl2-cosine angle)))
                   (* (point-in-r3-y1 point) (acl2-sine angle))) )
    ((1 . 0) . ,(+ (* (point-in-r3-y1 point) (point-in-r3-x1 point) (- 1 (acl2-cosine angle)))
                   (* (point-in-r3-z1 point) (acl2-sine angle))) )
    ((1 . 1) . ,(+ (acl2-cosine angle)
                   (* (point-in-r3-y1 point) (point-in-r3-y1 point) (- 1 (acl2-cosine angle)))) )
    ((1 . 2) . ,(- (* (point-in-r3-y1 point) (point-in-r3-z1 point) (- 1 (acl2-cosine angle)))
                   (* (point-in-r3-x1 point) (acl2-sine angle))) )
    ((2 . 0) . ,(- (* (point-in-r3-z1 point) (point-in-r3-x1 point) (- 1 (acl2-cosine angle)))
                   (* (point-in-r3-y1 point) (acl2-sine angle))) )
    ((2 . 1) . ,(+ (* (point-in-r3-z1 point) (point-in-r3-y1 point) (- 1 (acl2-cosine angle)))
                   (* (point-in-r3-x1 point) (acl2-sine angle))) )
    ((2 . 2) . ,(+ (acl2-cosine angle)
                   (* (point-in-r3-z1 point) (point-in-r3-z1 point) (- 1 (acl2-cosine angle)))) )
    )
  )

(encapsulate
  ()
  (local (include-book "workshops/1999/embedded/Exercises/Exercise1-2/Exercise1.2" :dir :system))
  (defthmd test-200
    (implies (and (realp r)
                  (>= r 0)
                  (realp x)
                  (> x 0))
             (natp (/ (- r (mod r x)) x)))
    :hints (("Goal"
             :in-theory (enable mod)
             )))
  )

(encapsulate
  ()
  (local (include-book "workshops/1999/embedded/Exercises/Exercise1-2/Exercise1.2" :dir :system))
  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd test-201
    (implies (and (realp r)
                  (>= r 0)
                  (realp x)
                  (> x 0))
             (and (>= (mod r x) 0)
                  (realp (mod r x))
                  (< (mod r x) x)))
    :hints (("Goal"
             :in-theory (enable mod floor1)
             )))
  )

---

(defun-sk exists-int-k (theta1 theta2)
  (exists k
          (and (integerp k)
               (equal (+ theta2 (* 2 k (acl2-pi)))
                      theta1))))


(defthmd test-202
  (implies (and (point-in-r3 p)
                (not (m-= (point-on-s2-not-d) p))
                (realp theta1)
                (realp theta2)
                (m-= (m-* (rotation-about-witness theta1 (point-on-s2-not-d)) p)
                     (m-* (rotation-about-witness theta2 (point-on-s2-not-d)) p)))
           (exists-int-k theta1 theta2)))

(defthmd test-202
  (implies (and (not (equal th1 th2))
                (>= th1 0)
                (< th1 (* 2 (acl2-pi)))
                (>= th2 0)
                (< th2 (* 2 (acl2-pi))))
           (not (equal (acl2-sine th1) (acl2-sine th2))))
  :hints (("Goal"
           :use ((:instance acl2-sine (x th1))
                 (:instance acl2-sine (x th2)))
           :in-theory (enable (acl2-sine))
           )))

(defun-sk exists-natp-x (theta1 k)
  (exists x
          (and (natp x)
               (>= x 0)
               (< x (* 2 (acl2-pi)))
               (equal (acl2-sine (+ (* 2 (acl2-pi) k) x))
                      (acl2-sine theta1)))))

(defun-sk exists-int-k (theta1)
  (exists k
          (and (natp k)
               (>= (- theta1 (* 2 (acl2-pi) k)) 0)
               (< (- theta1 (* 2 (acl2-pi) k)) (* 2 (acl2-pi))))))


(defthmd test-1000
  (implies (realp theta1)
           (exists-int-k theta1))
  :hints

  (defun-sk exists-int-k (theta1 theta2)
    (exists k
            (and (integerp k)
                 (equal (+ (* 2 (acl2-pi) k) theta1)
                        theta2))))

  (defthmd test-1000
    (implies (and (point-in-r3 p1)
                  (realp theta1)
                  (>= theta1 0)
                  (realp theta2)
                  (>= theta2 0)
                  (m-= (rotation-about-witness theta1 p1)
                       (rotation-about-witness theta2 p1)))
             (exists-int-k theta1 theta2)))

  -----

  (defthmd r3-matrixp-rotation-witness
    (r3-matrixp (rotation-about-witness (acl2-pi) (point-on-s2-not-d)))
    :hints (("Goal"
             :use ((:instance witness-not-in-x-coord-sequence))
             :in-theory (e/d (aref2 header dimensions array2p) (acl2-sqrt))
             )))

  (defun-sk choose-angle (n dp1 dp2)
    (exists theta
            (and (realp theta)
                 (<= 0 theta)
                 (< theta (acl2-pi))
                 (m-= (m-* (rotation-about-witness (* theta n) (point-on-s2-not-d)) dp1)
                      dp2))))

  (defun generate-angles-1 (n dp1 poles-list)
    (if (atom poles-list)
        nil
      (if (choose-angle n dp1 (car poles-list))
          (append (list (choose-angle-witness n dp1 (car poles-list)))
                  (generate-angles-1 n dp1 (cdr poles-list)))
        (append (list nil)
                (generate-angles-1 n dp1 (cdr poles-list))))))

  (defun generate-angles (n poles-list1 poles-list2)
    (if (atom poles-list1)
        nil
      (append (generate-angles-1 n (car poles-list1) poles-list2)
              (generate-angles n (cdr poles-list1) poles-list2))))
