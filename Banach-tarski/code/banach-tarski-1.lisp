
(include-book "banach-tarski")

(defthmd b3-0-n-b3-f=>1-14
  (implies (b3-0-n-b3-f p)
           (or (b3-00 p)
               (b3-01 p)))
  :hints (("goal"
           :cases ((b3-0-set-a3 p)
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
                   (b3-0-set-a14 p)
                   (b3-0-set-a1 p)
                   (b3-0-set-a2 p))
           :use ((:instance b3-0-n-b3-f (p p))
                 (:instance b3-0-iff-a1-to-a14 (p p))
                 )
           :in-theory nil
           )
          ("Subgoal 14"
           :use ((:instance b3-0-n-b3-f (p p))
                 (:instance b3-00 (p p))
                 (:instance b3-01 (p p))
                 (:instance b3-f (p p))
                 (:instance rot-3)
                 (:instance rotp-rot=>b3=>rot*b3-f-or-rot-sf
                            (rot (r3-m-inverse (rot-3)))
                            (p p))
                 (:instance rot-m=>rot-m-inv
                            (m (rot-3)))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance ROT*SET-F (rot (r3-m-inverse (rot-3))) (p p))
                 (:instance ROT*SET-F-1 (rot (r3-m-inverse (rot-3))) (point p))
                 (:instance ROT*b3-F (rot (r3-m-inverse (rot-3))) (p p))
                 (:instance ROT*b3-F-1 (rot (r3-m-inverse (rot-3))) (point p))
                 (:instance rot-3-inv*f-suff (point p) (p (ROT*SET-F-1-WITNESS (R3-M-INVERSE (ROT-3))
                                                                               P)))
                 (:instance rot-3-inv*b3-f-suff (point p) (p (ROT*b3-F-1-WITNESS (R3-M-INVERSE (ROT-3))
                                                                               P)))
                 )
           :in-theory nil
           )

          ))
;; (defun rot-9 ()
;;   (b-inv-rotation (acl2-sqrt 2)))

;; (defun rot-10 ()
;;   (m-* (b-inv-rotation (acl2-sqrt 2))
;;        (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))) (point-on-s2-not-d))))

;; (defun rot-11 ()
;;   (m-* (rotation-3d
;;         (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d))
;;        (b-inv-rotation (acl2-sqrt 2))))

;; (defun rot-12 ()
;;   (m-* (rotation-3d
;;         (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d))
;;        (b-inv-rotation (acl2-sqrt 2))
;;        (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))) (point-on-s2-not-d))))

;; (defun rot-13 ()
;;   (id-rotation))

;; (defun rot-14 ()
;;   (id-rotation))

;; (defun-sk rot-9-inv*f (point)
;;   (exists p
;;           (and (set-f-p p)
;;                (m-= (m-* (r3-m-inverse (rot-9)) p) point))))

;; (defun b9-01 (p)
;;   (and (b3-0-set-a9 p)
;;        (b3-f p)
;;        (rot-9-inv*f p)))

;; (defun b9-11 (p)
;;   (and (b3-0-set-a9 p)
;;        (set-f-p p)
;;        (rot-9-inv*f p)))

;; (defun-sk rota-1-rot-9-b9-01-1 (point)
;;   (exists p
;;           (and (b9-01 p)
;;                (m-= (rotation-about-arbitrary-line (- (angle-const)) (m-p) (n-p)
;;                                                    (m-* (rot-9) p))
;;                     point))))

;; (defun rota-1-rot-9-b9-01 (p)
;;   (and (point-in-r3 p)
;;        (rota-1-rot-9-b9-01-1 p)))

;; (defun-sk rota-1-rot-9-b9-11-1 (point)
;;   (exists p
;;           (and (b9-11 p)
;;                (m-= (rotation-about-arbitrary-line (- (angle-const)) (m-p) (n-p)
;;                                                    (m-* (rot-9) p))
;;                     point))))

;; (defun rota-1-rot-9-b9-11 (p)
;;   (and (point-in-r3 p)
;;        (rota-1-rot-9-b9-11-1 p)))

;; (defun-sk rot-10-inv*f (point)
;;   (exists p
;;           (and (set-f-p p)
;;                (m-= (m-* (r3-m-inverse (rot-10)) p) point))))

;; (defun b10-01 (p)
;;   (and (b3-0-set-a10 p)
;;        (b3-f p)
;;        (rot-10-inv*f p)))

;; (defun b10-11 (p)
;;   (and (b3-0-set-a10 p)
;;        (set-f-p p)
;;        (rot-10-inv*f p)))

;; (defun-sk rota-1-rot-10-b10-01-1 (point)
;;   (exists p
;;           (and (b10-01 p)
;;                (m-= (rotation-about-arbitrary-line (- (angle-const)) (m-p) (n-p)
;;                                                    (m-* (rot-10) p))
;;                     point))))

;; (defun rota-1-rot-10-b10-01 (p)
;;   (and (point-in-r3 p)
;;        (rota-1-rot-10-b10-01-1 p)))

;; (defun-sk rota-1-rot-10-b10-11-1 (point)
;;   (exists p
;;           (and (b10-11 p)
;;                (m-= (rotation-about-arbitrary-line (- (angle-const)) (m-p) (n-p)
;;                                                    (m-* (rot-10) p))
;;                     point))))

;; (defun rota-1-rot-10-b10-11 (p)
;;   (and (point-in-r3 p)
;;        (rota-1-rot-10-b10-11-1 p)))

;; (defun-sk rot-11-inv*f (point)
;;   (exists p
;;           (and (set-f-p p)
;;                (m-= (m-* (r3-m-inverse (rot-11)) p) point))))

;; (defun b11-01 (p)
;;   (and (b3-0-set-a11 p)
;;        (b3-f p)
;;        (rot-11-inv*f p)))

;; (defun b11-11 (p)
;;   (and (b3-0-set-a11 p)
;;        (set-f-p p)
;;        (rot-11-inv*f p)))

;; (defun-sk rota-1-rot-11-b11-01-1 (point)
;;   (exists p
;;           (and (b11-01 p)
;;                (m-= (rotation-about-arbitrary-line (- (angle-const)) (m-p) (n-p)
;;                                                    (m-* (rot-11) p))
;;                     point))))

;; (defun rota-1-rot-11-b11-01 (p)
;;   (and (point-in-r3 p)
;;        (rota-1-rot-11-b11-01-1 p)))

;; (defun-sk rota-1-rot-11-b11-11-1 (point)
;;   (exists p
;;           (and (b11-11 p)
;;                (m-= (rotation-about-arbitrary-line (- (angle-const)) (m-p) (n-p)
;;                                                    (m-* (rot-11) p))
;;                     point))))

;; (defun rota-1-rot-11-b11-11 (p)
;;   (and (point-in-r3 p)
;;        (rota-1-rot-11-b11-11-1 p)))

;; (defun-sk rot-12-inv*f (point)
;;   (exists p
;;           (and (set-f-p p)
;;                (m-= (m-* (r3-m-inverse (rot-12)) p) point))))

;; (defun b12-01 (p)
;;   (and (b3-0-set-a12 p)
;;        (b3-f p)
;;        (rot-12-inv*f p)))

;; (defun b12-11 (p)
;;   (and (b3-0-set-a12 p)
;;        (set-f-p p)
;;        (rot-12-inv*f p)))

;; (defun-sk rota-1-rot-12-b12-01-1 (point)
;;   (exists p
;;           (and (b12-01 p)
;;                (m-= (rotation-about-arbitrary-line (- (angle-const)) (m-p) (n-p)
;;                                                    (m-* (rot-12) p))
;;                     point))))

;; (defun rota-1-rot-12-b12-01 (p)
;;   (and (point-in-r3 p)
;;        (rota-1-rot-12-b12-01-1 p)))

;; (defun-sk rota-1-rot-12-b12-11-1 (point)
;;   (exists p
;;           (and (b12-11 p)
;;                (m-= (rotation-about-arbitrary-line (- (angle-const)) (m-p) (n-p)
;;                                                    (m-* (rot-12) p))
;;                     point))))

;; (defun rota-1-rot-12-b12-11 (p)
;;   (and (point-in-r3 p)
;;        (rota-1-rot-12-b12-11-1 p)))

;; (defun-sk rot-13-inv*f (point)
;;   (exists p
;;           (and (set-f-p p)
;;                (m-= (m-* (r3-m-inverse (rot-13)) p) point))))

;; (defun b13-01 (p)
;;   (and (b3-0-set-a13 p)
;;        (b3-f p)
;;        (rot-13-inv*f p)))

;; (defun b13-11 (p)
;;   (and (b3-0-set-a13 p)
;;        (set-f-p p)
;;        (rot-13-inv*f p)))

;; (defun-sk rota-1-rot-13-b13-01-1 (point)
;;   (exists p
;;           (and (b13-01 p)
;;                (m-= (rotation-about-arbitrary-line (- (angle-const)) (m-p) (n-p)
;;                                                    (m-* (rot-13) p))
;;                     point))))

;; (defun rota-1-rot-13-b13-01 (p)
;;   (and (point-in-r3 p)
;;        (rota-1-rot-13-b13-01-1 p)))

;; (defun-sk rota-1-rot-13-b13-11-1 (point)
;;   (exists p
;;           (and (b13-11 p)
;;                (m-= (rotation-about-arbitrary-line (- (angle-const)) (m-p) (n-p)
;;                                                    (m-* (rot-13) p))
;;                     point))))

;; (defun rota-1-rot-13-b13-11 (p)
;;   (and (point-in-r3 p)
;;        (rota-1-rot-13-b13-11-1 p)))

;; (defun-sk rot-14-inv*f (point)
;;   (exists p
;;           (and (set-f-p p)
;;                (m-= (m-* (r3-m-inverse (rot-14)) p) point))))

;; (defun b14-01 (p)
;;   (and (b3-0-set-a14 p)
;;        (b3-f p)
;;        (rot-14-inv*f p)))

;; (defun b14-11 (p)
;;   (and (b3-0-set-a14 p)
;;        (set-f-p p)
;;        (rot-14-inv*f p)))

;; (defun-sk rota-1-rot-14-b14-01-1 (point)
;;   (exists p
;;           (and (b14-01 p)
;;                (m-= (rotation-about-arbitrary-line (- (angle-const)) (m-p) (n-p)
;;                                                    (m-* (rot-14) p))
;;                     point))))

;; (defun rota-1-rot-14-b14-01 (p)
;;   (and (point-in-r3 p)
;;        (rota-1-rot-14-b14-01-1 p)))

;; (defun-sk rota-1-rot-14-b14-11-1 (point)
;;   (exists p
;;           (and (b14-11 p)
;;                (m-= (rotation-about-arbitrary-line (- (angle-const)) (m-p) (n-p)
;;                                                    (m-* (rot-14) p))
;;                     point))))

;; (defun rota-1-rot-14-b14-11 (p)
;;   (and (point-in-r3 p)
;;        (rota-1-rot-14-b14-11-1 p)))

;; (defthmd a9-a14-rot-a-inv-b3-0-nf=>
;;   (implies (rota-inv-b3-0-n-f p)
;;            (or (rota-1-rot-9-b9-11 p)
;;                (rota-1-rot-9-b9-01 p)
;;                (rota-1-rot-10-b10-11 p)
;;                (rota-1-rot-10-b10-01 p)
;;                (rota-1-rot-11-b11-11 p)
;;                (rota-1-rot-11-b11-01 p)
;;                (rota-1-rot-12-b12-11 p)
;;                (rota-1-rot-12-b12-01 p)
;;                (rota-1-rot-13-b13-11 p)
;;                (rota-1-rot-13-b13-01 p)
;;                (rota-1-rot-14-b14-11 p)
;;                (rota-1-rot-14-b14-01 p)))
;;   :hints (("Goal"
;;            :cases ((b3-0-b-inv-b3-0-set-a9 (ROTA-INV-B3-0-N-F-1-WITNESS P))
;;                    (b3-0-b-inv-r-b3-0-set-a10 (ROTA-INV-B3-0-N-F-1-WITNESS P))
;;                    (b3-0-r-1-b-inv-b3-0-set-a11 (ROTA-INV-B3-0-N-F-1-WITNESS P))
;;                    (b3-0-r-1-b-inv-r-b3-0-set-a12 (ROTA-INV-B3-0-N-F-1-WITNESS P))
;;                    (b3-0-set-a13 (ROTA-INV-B3-0-N-F-1-WITNESS P))
;;                    (b3-0-set-a14 (ROTA-INV-B3-0-N-F-1-WITNESS P)))
;;            :use ((:instance ROTA-INV-B3-0-N-F (p p))
;;                  (:instance ROTA-INV-B3-0-N-F-1 (point p))
;;                  (:instance b3-0-n-f (p (ROTA-INV-B3-0-N-F-1-WITNESS P)))
;;                  (:instance b3-0-iff-a9-to-a14 (p (ROTA-INV-B3-0-N-F-1-WITNESS P)))
;;                  )
;;            :in-theory nil
;;            )
;;           ("Subgoal 6"
;;            :use((:instance b3-0-b-inv-b3-0-set-a9 (p (ROTA-INV-B3-0-N-F-1-WITNESS P)))
;;                 (:instance b3-0-b-inv-b3-0-set-a9-1 (p (ROTA-INV-B3-0-N-F-1-WITNESS P)))
;;                 (:instance rota-1-rot-9-b9-01 (p p))
;;                 (:instance rota-1-rot-9-b9-11 (p p))
;;                 (:instance rota-1-rot-9-b9-01-1-suff
;;                            (point p)
;;                            (p (B3-0-b-INV-B3-0-SET-A9-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
;;                 (:instance b9-01
;;                            (p (B3-0-b-INV-B3-0-SET-A9-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
;;                 (:instance rota-1-rot-9-b9-11-1-suff
;;                            (point p)
;;                            (p (B3-0-b-INV-B3-0-SET-A9-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
;;                 (:instance b9-11
;;                            (p (B3-0-b-INV-B3-0-SET-A9-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
;;                 (:instance b3-f
;;                            (p (B3-0-b-INV-B3-0-SET-A9-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
;;                 (:instance b3-0-iff-a1-to-a14
;;                            (p (B3-0-b-INV-B3-0-SET-A9-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
;;                 (:instance b3-0
;;                            (p (B3-0-b-INV-B3-0-SET-A9-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
;;                 (:instance b3 (p (B3-0-b-INV-B3-0-SET-A9-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
;;                 (:instance rot-9-inv*f-suff
;;                            (point (B3-0-b-INV-B3-0-SET-A9-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P)))
;;                            (p (ROTA-INV-B3-0-N-F-1-WITNESS P)))
;;                 (:instance rot-9)
;;                 (:instance a3-a8-rot-a-inv-b3-0-nf=>1
;;                            (m1 (ROT-9))
;;                            (m2 (B3-0-b-INV-B3-0-SET-A9-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P)))
;;                            (m3 (ROTA-INV-B3-0-N-F-1-WITNESS P))
;;                            (m4 (R3-M-INVERSE (ROT-9)))
;;                            (m5 (id-rotation))
;;                            (m6 (B3-0-b-INV-B3-0-SET-A9-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
;;                 (:instance m-*-m-inverse-m
;;                            (m (rot-9)))
;;                 (:instance m-*point-id=point
;;                            (p1 (B3-0-b-INV-B3-0-SET-A9-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
;;                 (:instance base-rotations
;;                            (x (acl2-sqrt 2)))
;;                 (:instance r3-rotationp (m (b-INV-ROTATION (ACL2-SQRT 2))))
;;                 (:instance rotation-about-arbitrary-line=>1
;;                            (p1 (M-* (ROT-9)
;;                                     (B3-0-b-INV-B3-0-SET-A9-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
;;                            (p2 (ROTA-INV-B3-0-N-F-1-WITNESS P))
;;                            (angle (- (angle-const)))
;;                            (m (m-p))
;;                            (n (n-p)))
;;                 (:instance set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-1-1
;;                            (p1 (B3-0-b-INV-B3-0-SET-A9-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P)))
;;                            (rot (rot-9)))
;;                 )
;;            :in-theory nil
;;            )
;;           ("Subgoal 5"
;;            :use((:instance B3-0-b-INV-R-B3-0-SET-A10 (p (ROTA-INV-B3-0-N-F-1-WITNESS P)))
;;                 (:instance B3-0-b-INV-R-B3-0-SET-A10-1 (p (ROTA-INV-B3-0-N-F-1-WITNESS P)))
;;                 (:instance rota-1-rot-10-b10-01 (p p))
;;                 (:instance rota-1-rot-10-b10-11 (p p))
;;                 (:instance rota-1-rot-10-b10-01-1-suff
;;                            (point p)
;;                            (p (B3-0-b-INV-R-B3-0-SET-A10-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
;;                 (:instance b10-01
;;                            (p (B3-0-b-INV-R-B3-0-SET-A10-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
;;                 (:instance rota-1-rot-10-b10-11-1-suff
;;                            (point p)
;;                            (p (B3-0-b-INV-R-B3-0-SET-A10-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
;;                 (:instance b10-11
;;                            (p (B3-0-b-INV-R-B3-0-SET-A10-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
;;                 (:instance b3-f
;;                            (p (B3-0-b-INV-R-B3-0-SET-A10-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
;;                 (:instance b3-0-iff-a1-to-a14
;;                            (p (B3-0-b-INV-R-B3-0-SET-A10-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
;;                 (:instance b3-0
;;                            (p (B3-0-b-INV-R-B3-0-SET-A10-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
;;                 (:instance b3 (p (B3-0-b-INV-R-B3-0-SET-A10-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
;;                 (:instance rot-10-inv*f-suff
;;                            (point (B3-0-b-INV-R-B3-0-SET-A10-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P)))
;;                            (p (ROTA-INV-B3-0-N-F-1-WITNESS P)))
;;                 (:instance rot-10)
;;                 (:instance a3-a8-rot-a-inv-b3-0-nf=>1
;;                            (m1 (ROT-10))
;;                            (m2 (B3-0-b-INV-R-B3-0-SET-A10-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P)))
;;                            (m3 (ROTA-INV-B3-0-N-F-1-WITNESS P))
;;                            (m4 (R3-M-INVERSE (ROT-10)))
;;                            (m5 (id-rotation))
;;                            (m6 (B3-0-b-INV-R-B3-0-SET-A10-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
;;                 (:instance associativity-of-m-*
;;                            (m1 (b-INV-ROTATION (ACL2-SQRT 2)))
;;                            (m2 (ROTATION-3D
;;                                 (EXISTS-IN-INTERVAL-BUT-NOT-IN-ANGLE-SEQUENCE-WITNESS 0 (* 2 (ACL2-PI)))
;;                                 (POINT-ON-S2-NOT-D)))
;;                            (m3 (B3-0-b-INV-R-B3-0-SET-A10-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
;;                 (:instance m-*-m-inverse-m
;;                            (m (rot-10)))
;;                 (:instance rot*rot-is-rot
;;                            (m1 (b-inv-rotation (acl2-sqrt 2)))
;;                            (m2 (ROTATION-3D
;;                                 (EXISTS-IN-INTERVAL-BUT-NOT-IN-ANGLE-SEQUENCE-WITNESS 0 (* 2 (ACL2-PI)))
;;                                 (POINT-ON-S2-NOT-D))))
;;                 (:instance m-*point-id=point
;;                            (p1 (B3-0-b-INV-R-B3-0-SET-A10-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
;;                 (:instance base-rotations
;;                            (x (acl2-sqrt 2)))
;;                 (:instance r3-rotationp (m (rot-10)))
;;                 (:instance r3-rotationp-r-theta
;;                            (angle (EXISTS-IN-INTERVAL-BUT-NOT-IN-ANGLE-SEQUENCE-WITNESS 0 (* 2 (ACL2-PI)))))
;;                 (:instance witness-not-in-angle-sequence)
;;                 (:instance rotation-about-arbitrary-line=>1
;;                            (p1 (M-* (ROT-10)
;;                                     (B3-0-b-INV-R-B3-0-SET-A10-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
;;                            (p2 (ROTA-INV-B3-0-N-F-1-WITNESS P))
;;                            (angle (- (angle-const)))
;;                            (m (m-p))
;;                            (n (n-p)))
;;                 (:instance set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-1-1
;;                            (p1 (B3-0-b-INV-R-B3-0-SET-A10-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P)))
;;                            (rot (rot-10)))
;;                 )
;;            :in-theory nil
;;            )
;;           ("Subgoal 4"
;;            :use((:instance b3-0-r-1-b-inv-b3-0-set-a11 (p (ROTA-INV-B3-0-N-F-1-WITNESS P)))
;;                 (:instance b3-0-r-1-b-inv-b3-0-set-a11-1 (p (ROTA-INV-B3-0-N-F-1-WITNESS P)))
;;                 (:instance rota-1-rot-11-b11-01 (p p))
;;                 (:instance rota-1-rot-11-b11-11 (p p))
;;                 (:instance rota-1-rot-11-b11-01-1-suff
;;                            (point p)
;;                            (p (b3-0-r-1-b-inv-b3-0-set-a11-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
;;                 (:instance b11-01
;;                            (p (b3-0-r-1-b-inv-b3-0-set-a11-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
;;                 (:instance rota-1-rot-11-b11-11-1-suff
;;                            (point p)
;;                            (p (b3-0-r-1-b-inv-b3-0-set-a11-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
;;                 (:instance b11-11
;;                            (p (b3-0-r-1-b-inv-b3-0-set-a11-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
;;                 (:instance b3-f
;;                            (p (b3-0-r-1-b-inv-b3-0-set-a11-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
;;                 (:instance b3-0-iff-a1-to-a14
;;                            (p (b3-0-r-1-b-inv-b3-0-set-a11-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
;;                 (:instance b3-0
;;                            (p (b3-0-r-1-b-inv-b3-0-set-a11-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
;;                 (:instance b3 (p (b3-0-r-1-b-inv-b3-0-set-a11-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
;;                 (:instance rot-11-inv*f-suff
;;                            (point (b3-0-r-1-b-inv-b3-0-set-a11-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P)))
;;                            (p (ROTA-INV-B3-0-N-F-1-WITNESS P)))
;;                 (:instance rot-11)
;;                 (:instance a3-a8-rot-a-inv-b3-0-nf=>1
;;                            (m1 (ROT-11))
;;                            (m2 (b3-0-r-1-b-inv-b3-0-set-a11-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P)))
;;                            (m3 (ROTA-INV-B3-0-N-F-1-WITNESS P))
;;                            (m4 (R3-M-INVERSE (ROT-11)))
;;                            (m5 (id-rotation))
;;                            (m6 (b3-0-r-1-b-inv-b3-0-set-a11-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
;;                 (:instance associativity-of-m-*
;;                            (m2 (b-INV-ROTATION (ACL2-SQRT 2)))
;;                            (m1 (ROTATION-3D
;;                                 (- (EXISTS-IN-INTERVAL-BUT-NOT-IN-ANGLE-SEQUENCE-WITNESS 0 (* 2 (ACL2-PI))))
;;                                 (POINT-ON-S2-NOT-D)))
;;                            (m3 (b3-0-r-1-b-inv-b3-0-set-a11-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
;;                 (:instance m-*-m-inverse-m
;;                            (m (rot-11)))
;;                 (:instance rot*rot-is-rot
;;                            (m2 (b-inv-rotation (acl2-sqrt 2)))
;;                            (m1 (ROTATION-3D
;;                                 (- (EXISTS-IN-INTERVAL-BUT-NOT-IN-ANGLE-SEQUENCE-WITNESS 0 (* 2 (ACL2-PI))))
;;                                 (POINT-ON-S2-NOT-D))))
;;                 (:instance m-*point-id=point
;;                            (p1 (b3-0-r-1-b-inv-b3-0-set-a11-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
;;                 (:instance base-rotations
;;                            (x (acl2-sqrt 2)))
;;                 (:instance r3-rotationp (m (rot-11)))
;;                 (:instance r3-rotationp-r-theta
;;                            (angle (- (EXISTS-IN-INTERVAL-BUT-NOT-IN-ANGLE-SEQUENCE-WITNESS 0 (* 2 (ACL2-PI))))))
;;                 (:instance witness-not-in-angle-sequence)
;;                 (:instance rotation-about-arbitrary-line=>1
;;                            (p1 (M-* (ROT-11)
;;                                     (b3-0-r-1-b-inv-b3-0-set-a11-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
;;                            (p2 (ROTA-INV-B3-0-N-F-1-WITNESS P))
;;                            (angle (- (angle-const)))
;;                            (m (m-p))
;;                            (n (n-p)))
;;                 (:instance set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-1-1
;;                            (p1 (b3-0-r-1-b-inv-b3-0-set-a11-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P)))
;;                            (rot (rot-11)))
;;                 )
;;            :in-theory nil
;;            )
;;           ("Subgoal 3"
;;            :use((:instance B3-0-R-1-b-INV-R-B3-0-SET-A12 (p (ROTA-INV-B3-0-N-F-1-WITNESS P)))
;;                 (:instance B3-0-R-1-b-INV-R-B3-0-SET-A12-1 (p (ROTA-INV-B3-0-N-F-1-WITNESS P)))
;;                 (:instance rota-1-rot-12-b12-01 (p p))
;;                 (:instance rota-1-rot-12-b12-11 (p p))
;;                 (:instance rota-1-rot-12-b12-01-1-suff
;;                            (point p)
;;                            (p (B3-0-R-1-b-INV-R-B3-0-SET-A12-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
;;                 (:instance b12-01
;;                            (p (B3-0-R-1-b-INV-R-B3-0-SET-A12-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
;;                 (:instance rota-1-rot-12-b12-11-1-suff
;;                            (point p)
;;                            (p (B3-0-R-1-b-INV-R-B3-0-SET-A12-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
;;                 (:instance b12-11
;;                            (p (B3-0-R-1-b-INV-R-B3-0-SET-A12-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
;;                 (:instance b3-f
;;                            (p (B3-0-R-1-b-INV-R-B3-0-SET-A12-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
;;                 (:instance b3-0-iff-a1-to-a14
;;                            (p (B3-0-R-1-b-INV-R-B3-0-SET-A12-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
;;                 (:instance b3-0
;;                            (p (B3-0-R-1-b-INV-R-B3-0-SET-A12-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
;;                 (:instance b3 (p (B3-0-R-1-b-INV-R-B3-0-SET-A12-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
;;                 (:instance rot-12-inv*f-suff
;;                            (point (B3-0-R-1-b-INV-R-B3-0-SET-A12-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P)))
;;                            (p (ROTA-INV-B3-0-N-F-1-WITNESS P)))
;;                 (:instance rot-12)
;;                 (:instance a3-a8-rot-a-inv-b3-0-nf=>1
;;                            (m1 (ROT-12))
;;                            (m2 (B3-0-R-1-b-INV-R-B3-0-SET-A12-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P)))
;;                            (m3 (ROTA-INV-B3-0-N-F-1-WITNESS P))
;;                            (m4 (R3-M-INVERSE (ROT-12)))
;;                            (m5 (id-rotation))
;;                            (m6 (B3-0-R-1-b-INV-R-B3-0-SET-A12-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
;;                 (:instance associativity-of-m-*
;;                            (m2 (b-INV-ROTATION (ACL2-SQRT 2)))
;;                            (m1 (ROTATION-3D
;;                                 (- (EXISTS-IN-INTERVAL-BUT-NOT-IN-ANGLE-SEQUENCE-WITNESS 0 (* 2 (ACL2-PI))))
;;                                 (POINT-ON-S2-NOT-D)))
;;                            (m3 (b3-0-r-1-a-inv-b3-0-set-a5-1-WITNESS
;;                                 (ROTA-INV-B3-0-N-F-1-WITNESS P))))
;;                 (:instance a3-a8-rot-a-inv-b3-0-nf=>sub-3
;;                            (m1 (ROTATION-3D (- (EXISTS-IN-INTERVAL-BUT-NOT-IN-ANGLE-SEQUENCE-WITNESS
;;                                                 0 (* 2 (ACL2-PI))))
;;                                             (POINT-ON-S2-NOT-D)))
;;                            (m2 (b-INV-ROTATION (ACL2-SQRT 2)))
;;                            (m3 (ROTATION-3D (EXISTS-IN-INTERVAL-BUT-NOT-IN-ANGLE-SEQUENCE-WITNESS
;;                                              0 (* 2 (ACL2-PI)))
;;                                             (POINT-ON-S2-NOT-D)))
;;                            (m4 (B3-0-R-1-b-INV-R-B3-0-SET-A12-1-WITNESS
;;                                 (ROTA-INV-B3-0-N-F-1-WITNESS P))))
;;                 (:instance m-*-m-inverse-m
;;                            (m (rot-12)))
;;                 (:instance b3-0-r-1-a-inv-r-b3-0-a6-iff-b3-0-r-1-a-1-r-a6-1
;;                            (m2 (b-inv-rotation (acl2-sqrt 2)))
;;                            (m1 (ROTATION-3D
;;                                 (- (EXISTS-IN-INTERVAL-BUT-NOT-IN-ANGLE-SEQUENCE-WITNESS 0 (* 2 (ACL2-PI))))
;;                                 (POINT-ON-S2-NOT-D)))
;;                            (m3 (ROTATION-3D
;;                                 (EXISTS-IN-INTERVAL-BUT-NOT-IN-ANGLE-SEQUENCE-WITNESS 0 (* 2 (ACL2-PI)))
;;                                 (POINT-ON-S2-NOT-D))))
;;                 (:instance m-*point-id=point
;;                            (p1 (B3-0-R-1-b-INV-R-B3-0-SET-A12-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
;;                 (:instance base-rotations
;;                            (x (acl2-sqrt 2)))
;;                 (:instance r3-rotationp (m (rot-12)))
;;                 (:instance r3-rotationp-r-theta
;;                            (angle (- (EXISTS-IN-INTERVAL-BUT-NOT-IN-ANGLE-SEQUENCE-WITNESS 0 (* 2 (ACL2-PI))))))
;;                 (:instance r3-rotationp-r-theta
;;                            (angle (EXISTS-IN-INTERVAL-BUT-NOT-IN-ANGLE-SEQUENCE-WITNESS 0 (* 2 (ACL2-PI)))))
;;                 (:instance witness-not-in-angle-sequence)
;;                 (:instance rotation-about-arbitrary-line=>1
;;                            (p1 (M-* (ROT-12)
;;                                     (B3-0-R-1-b-INV-R-B3-0-SET-A12-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P))))
;;                            (p2 (ROTA-INV-B3-0-N-F-1-WITNESS P))
;;                            (angle (- (angle-const)))
;;                            (m (m-p))
;;                            (n (n-p)))
;;                 (:instance set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-1-1
;;                            (p1 (B3-0-R-1-b-INV-R-B3-0-SET-A12-1-WITNESS (ROTA-INV-B3-0-N-F-1-WITNESS P)))
;;                            (rot (rot-12)))
;;                 )
;;            :in-theory nil
;;            )
;;           ("Subgoal 2"
;;            :use((:instance b3-0-set-a13 (p (ROTA-INV-B3-0-N-F-1-WITNESS P)))
;;                 (:instance rota-1-rot-13-b13-01 (p p))
;;                 (:instance rota-1-rot-13-b13-11 (p p))
;;                 (:instance rota-1-rot-13-b13-01-1-suff
;;                            (point p)
;;                            (p (ROTA-INV-B3-0-N-F-1-WITNESS P)))
;;                 (:instance b13-01
;;                            (p (ROTA-INV-B3-0-N-F-1-WITNESS P)))
;;                 (:instance rota-1-rot-13-b13-11-1-suff
;;                            (point p)
;;                            (p (ROTA-INV-B3-0-N-F-1-WITNESS P)))
;;                 (:instance b13-11
;;                            (p (ROTA-INV-B3-0-N-F-1-WITNESS P)))
;;                 (:instance b3-f
;;                            (p (ROTA-INV-B3-0-N-F-1-WITNESS P)))
;;                 (:instance b3-0-iff-a1-to-a14
;;                            (p (ROTA-INV-B3-0-N-F-1-WITNESS P)))
;;                 (:instance b3-0
;;                            (p (ROTA-INV-B3-0-N-F-1-WITNESS P)))
;;                 (:instance b3 (p (ROTA-INV-B3-0-N-F-1-WITNESS P)))
;;                 (:instance rot-13-inv*f-suff
;;                            (point (ROTA-INV-B3-0-N-F-1-WITNESS P))
;;                            (p (ROTA-INV-B3-0-N-F-1-WITNESS P)))
;;                 (:instance rot-13)
;;                 (:instance a3-a8-rot-a-inv-b3-0-nf=>1
;;                            (m1 (ROT-13))
;;                            (m2 (ROTA-INV-B3-0-N-F-1-WITNESS P))
;;                            (m3 (ROTA-INV-B3-0-N-F-1-WITNESS P))
;;                            (m4 (R3-M-INVERSE (ROT-13)))
;;                            (m5 (id-rotation))
;;                            (m6 (ROTA-INV-B3-0-N-F-1-WITNESS P)))
;;                 (:instance m-*-m-inverse-m
;;                            (m (rot-13)))
;;                 (:instance m-*point-id=point
;;                            (p1 (ROTA-INV-B3-0-N-F-1-WITNESS P)))
;;                 (:instance base-rotations
;;                            (x (acl2-sqrt 2)))
;;                 (:instance r3-rotationp (m (id-rotation)))
;;                 (:instance rotation-about-arbitrary-line=>1
;;                            (p1 (M-* (ROT-13)
;;                                     (ROTA-INV-B3-0-N-F-1-WITNESS P)))
;;                            (p2 (ROTA-INV-B3-0-N-F-1-WITNESS P))
;;                            (angle (- (angle-const)))
;;                            (m (m-p))
;;                            (n (n-p)))
;;                 (:instance set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-1-1
;;                            (p1 (ROTA-INV-B3-0-N-F-1-WITNESS P))
;;                            (rot (rot-13)))
;;                 )
;;            :in-theory nil
;;            )
;;           ("Subgoal 1"
;;            :use((:instance b3-0-set-a14 (p (ROTA-INV-B3-0-N-F-1-WITNESS P)))
;;                 (:instance rota-1-rot-14-b14-01 (p p))
;;                 (:instance rota-1-rot-14-b14-11 (p p))
;;                 (:instance rota-1-rot-14-b14-01-1-suff
;;                            (point p)
;;                            (p (ROTA-INV-B3-0-N-F-1-WITNESS P)))
;;                 (:instance b14-01
;;                            (p (ROTA-INV-B3-0-N-F-1-WITNESS P)))
;;                 (:instance rota-1-rot-14-b14-11-1-suff
;;                            (point p)
;;                            (p (ROTA-INV-B3-0-N-F-1-WITNESS P)))
;;                 (:instance b14-11
;;                            (p (ROTA-INV-B3-0-N-F-1-WITNESS P)))
;;                 (:instance b3-f
;;                            (p (ROTA-INV-B3-0-N-F-1-WITNESS P)))
;;                 (:instance b3-0-iff-a1-to-a14
;;                            (p (ROTA-INV-B3-0-N-F-1-WITNESS P)))
;;                 (:instance b3-0
;;                            (p (ROTA-INV-B3-0-N-F-1-WITNESS P)))
;;                 (:instance b3 (p (ROTA-INV-B3-0-N-F-1-WITNESS P)))
;;                 (:instance rot-14-inv*f-suff
;;                            (point (ROTA-INV-B3-0-N-F-1-WITNESS P))
;;                            (p (ROTA-INV-B3-0-N-F-1-WITNESS P)))
;;                 (:instance rot-14)
;;                 (:instance a3-a8-rot-a-inv-b3-0-nf=>1
;;                            (m1 (ROT-14))
;;                            (m2 (ROTA-INV-B3-0-N-F-1-WITNESS P))
;;                            (m3 (ROTA-INV-B3-0-N-F-1-WITNESS P))
;;                            (m4 (R3-M-INVERSE (ROT-14)))
;;                            (m5 (id-rotation))
;;                            (m6 (ROTA-INV-B3-0-N-F-1-WITNESS P)))
;;                 (:instance m-*-m-inverse-m
;;                            (m (rot-14)))
;;                 (:instance m-*point-id=point
;;                            (p1 (ROTA-INV-B3-0-N-F-1-WITNESS P)))
;;                 (:instance base-rotations
;;                            (x (acl2-sqrt 2)))
;;                 (:instance r3-rotationp (m (id-rotation)))
;;                 (:instance rotation-about-arbitrary-line=>1
;;                            (p1 (M-* (ROT-14)
;;                                     (ROTA-INV-B3-0-N-F-1-WITNESS P)))
;;                            (p2 (ROTA-INV-B3-0-N-F-1-WITNESS P))
;;                            (angle (- (angle-const)))
;;                            (m (m-p))
;;                            (n (n-p)))
;;                 (:instance set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-1-1
;;                            (p1 (ROTA-INV-B3-0-N-F-1-WITNESS P))
;;                            (rot (rot-14)))
;;                 )
;;            :in-theory nil
;;            )
;;           ))

;; (defthmd rota-1-rot-9-14-b-9-14-01-or-11=>
;;   (implies (or (rota-1-rot-9-b9-11 p)
;;                (rota-1-rot-9-b9-01 p)
;;                (rota-1-rot-10-b10-11 p)
;;                (rota-1-rot-10-b10-01 p)
;;                (rota-1-rot-11-b11-11 p)
;;                (rota-1-rot-11-b11-01 p)
;;                (rota-1-rot-12-b12-11 p)
;;                (rota-1-rot-12-b12-01 p)
;;                (rota-1-rot-13-b13-11 p)
;;                (rota-1-rot-13-b13-01 p)
;;                (rota-1-rot-14-b14-11 p)
;;                (rota-1-rot-14-b14-01 p))
;;            (rota-inv-b3-0-n-f p))
;;   :hints (("goal"
;;            :cases ((or (rota-1-rot-9-b9-11 p)
;;                        (rota-1-rot-9-b9-01 p))
;;                    (or (rota-1-rot-10-b10-11 p)
;;                        (rota-1-rot-10-b10-01 p))
;;                    (or (rota-1-rot-11-b11-11 p)
;;                        (rota-1-rot-11-b11-01 p))
;;                    (or (rota-1-rot-12-b12-11 p)
;;                        (rota-1-rot-12-b12-01 p))
;;                    (or (rota-1-rot-13-b13-11 p)
;;                        (rota-1-rot-13-b13-01 p))
;;                    (or (rota-1-rot-14-b14-11 p)
;;                        (rota-1-rot-14-b14-01 p)))
;;            :in-theory nil)
;;           ("subgoal 6"
;;            :use ((:instance rota-1-rot-9-b9-11 (p p))
;;                  (:instance rota-1-rot-9-b9-11-1 (point p))
;;                  (:instance rota-inv-b3-0-n-f (p p))
;;                  (:instance rota-inv-b3-0-n-f-1-suff
;;                             (point p)
;;                             (p (m-* (rot-9)
;;                                     (rota-1-rot-9-b9-11-1-witness p))))
;;                  (:instance b9-11 (p (rota-1-rot-9-b9-11-1-witness p)))
;;                  (:instance rot*b3-0-set=>b3-0
;;                             (rot (rot-9))
;;                             (p (rota-1-rot-9-b9-11-1-witness p)))
;;                  (:instance b3-0-set-a9 (p (rota-1-rot-9-b9-11-1-witness p)))
;;                  (:instance b3-0-n-f (p (m-* (rot-9)
;;                                              (rota-1-rot-9-b9-11-1-witness p))))
;;                  (:instance rot-9-inv*f (point (rota-1-rot-9-b9-11-1-witness p)))
;;                  (:instance rota-1-rot-3-b3-01-or-11=>2
;;                             (rot (rot-9))
;;                             (p1 (rot-9-inv*f-witness (rota-1-rot-9-b9-11-1-witness p)))
;;                             (p2 (rota-1-rot-9-b9-11-1-witness p)))
;;                  (:instance base-rotations (x (acl2-sqrt 2)))
;;                  (:instance rot-9)
;;                  (:instance rota-1-rot-9-b9-01 (p p))
;;                  (:instance rota-1-rot-9-b9-01-1 (point p))
;;                  (:instance rota-inv-b3-0-n-f-1-suff
;;                             (point p)
;;                             (p (m-* (rot-9)
;;                                     (rota-1-rot-9-b9-01-1-witness p))))
;;                  (:instance b9-01 (p (rota-1-rot-9-b9-01-1-witness p)))
;;                  (:instance rot*b3-0-set=>b3-0
;;                             (rot (rot-9))
;;                             (p (rota-1-rot-9-b9-01-1-witness p)))
;;                  (:instance b3-0-set-a9 (p (rota-1-rot-9-b9-01-1-witness p)))
;;                  (:instance b3-0-n-f (p (m-* (rot-9)
;;                                              (rota-1-rot-9-b9-01-1-witness p))))
;;                  (:instance rot-9-inv*f (point (rota-1-rot-9-b9-01-1-witness p)))
;;                  (:instance rota-1-rot-3-b3-01-or-11=>2
;;                             (rot (rot-9))
;;                             (p1 (rot-9-inv*f-witness (rota-1-rot-9-b9-01-1-witness p)))
;;                             (p2 (rota-1-rot-9-b9-01-1-witness p))))
;;            :in-theory nil
;;            )
;;           ("subgoal 5"
;;            :use ((:instance rota-1-rot-10-b10-11 (p p))
;;                  (:instance rota-1-rot-10-b10-11-1 (point p))
;;                  (:instance rota-inv-b3-0-n-f (p p))
;;                  (:instance rota-inv-b3-0-n-f-1-suff
;;                             (point p)
;;                             (p (m-* (rot-10)
;;                                     (rota-1-rot-10-b10-11-1-witness p))))
;;                  (:instance b10-11 (p (rota-1-rot-10-b10-11-1-witness p)))
;;                  (:instance rot*b3-0-set=>b3-0
;;                             (rot (rot-10))
;;                             (p (rota-1-rot-10-b10-11-1-witness p)))
;;                  (:instance b3-0-set-a10 (p (rota-1-rot-10-b10-11-1-witness p)))
;;                  (:instance b3-0-n-f (p (m-* (rot-10)
;;                                              (rota-1-rot-10-b10-11-1-witness p))))
;;                  (:instance rot-10-inv*f (point (rota-1-rot-10-b10-11-1-witness p)))
;;                  (:instance rota-1-rot-3-b3-01-or-11=>2
;;                             (rot (rot-10))
;;                             (p1 (rot-10-inv*f-witness (rota-1-rot-10-b10-11-1-witness p)))
;;                             (p2 (rota-1-rot-10-b10-11-1-witness p)))
;;                  (:instance base-rotations (x (acl2-sqrt 2)))
;;                  (:instance rot-10)
;;                  (:instance rot*rot-is-rot
;;                             (m1 (b-inv-rotation (acl2-sqrt 2)))
;;                             (m2 (rotation-3d
;;                                  (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))
;;                                  (point-on-s2-not-d))))
;;                  (:instance base-rotations (x (acl2-sqrt 2)))
;;                  (:instance r3-rotationp-r-theta
;;                             (angle (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))))
;;                  (:instance witness-not-in-angle-sequence)
;;                  (:instance rota-1-rot-10-b10-01 (p p))
;;                  (:instance rota-1-rot-10-b10-01-1 (point p))
;;                  (:instance rota-inv-b3-0-n-f-1-suff
;;                             (point p)
;;                             (p (m-* (rot-10)
;;                                     (rota-1-rot-10-b10-01-1-witness p))))
;;                  (:instance b10-01 (p (rota-1-rot-10-b10-01-1-witness p)))
;;                  (:instance rot*b3-0-set=>b3-0
;;                             (rot (rot-10))
;;                             (p (rota-1-rot-10-b10-01-1-witness p)))
;;                  (:instance b3-0-set-a10 (p (rota-1-rot-10-b10-01-1-witness p)))
;;                  (:instance b3-0-n-f (p (m-* (rot-10)
;;                                              (rota-1-rot-10-b10-01-1-witness p))))
;;                  (:instance rot-10-inv*f (point (rota-1-rot-10-b10-01-1-witness p)))
;;                  (:instance rota-1-rot-3-b3-01-or-11=>2
;;                             (rot (rot-10))
;;                             (p1 (rot-10-inv*f-witness (rota-1-rot-10-b10-01-1-witness p)))
;;                             (p2 (rota-1-rot-10-b10-01-1-witness p)))
;;                  )
;;            :in-theory nil
;;            )
;;           ("subgoal 4"
;;            :use ((:instance rota-1-rot-11-b11-11 (p p))
;;                  (:instance rota-1-rot-11-b11-11-1 (point p))
;;                  (:instance rota-inv-b3-0-n-f (p p))
;;                  (:instance rota-inv-b3-0-n-f-1-suff
;;                             (point p)
;;                             (p (m-* (rot-11)
;;                                     (rota-1-rot-11-b11-11-1-witness p))))
;;                  (:instance b11-11 (p (rota-1-rot-11-b11-11-1-witness p)))
;;                  (:instance rot*b3-0-set=>b3-0
;;                             (rot (rot-11))
;;                             (p (rota-1-rot-11-b11-11-1-witness p)))
;;                  (:instance b3-0-set-a11 (p (rota-1-rot-11-b11-11-1-witness p)))
;;                  (:instance b3-0-n-f (p (m-* (rot-11)
;;                                              (rota-1-rot-11-b11-11-1-witness p))))
;;                  (:instance rot-11-inv*f (point (rota-1-rot-11-b11-11-1-witness p)))
;;                  (:instance rota-1-rot-3-b3-01-or-11=>2
;;                             (rot (rot-11))
;;                             (p1 (rot-11-inv*f-witness (rota-1-rot-11-b11-11-1-witness p)))
;;                             (p2 (rota-1-rot-11-b11-11-1-witness p)))
;;                  (:instance base-rotations (x (acl2-sqrt 2)))
;;                  (:instance rot-11)
;;                  (:instance rot*rot-is-rot
;;                             (m2 (b-inv-rotation (acl2-sqrt 2)))
;;                             (m1 (rotation-3d
;;                                  (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))
;;                                  (point-on-s2-not-d))))
;;                  (:instance base-rotations (x (acl2-sqrt 2)))
;;                  (:instance r3-rotationp-r-theta
;;                             (angle (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))))
;;                  (:instance witness-not-in-angle-sequence)
;;                  (:instance rota-1-rot-11-b11-01 (p p))
;;                  (:instance rota-1-rot-11-b11-01-1 (point p))
;;                  (:instance rota-inv-b3-0-n-f-1-suff
;;                             (point p)
;;                             (p (m-* (rot-11)
;;                                     (rota-1-rot-11-b11-01-1-witness p))))
;;                  (:instance b11-01 (p (rota-1-rot-11-b11-01-1-witness p)))
;;                  (:instance rot*b3-0-set=>b3-0
;;                             (rot (rot-11))
;;                             (p (rota-1-rot-11-b11-01-1-witness p)))
;;                  (:instance b3-0-set-a11 (p (rota-1-rot-11-b11-01-1-witness p)))
;;                  (:instance b3-0-n-f (p (m-* (rot-11)
;;                                              (rota-1-rot-11-b11-01-1-witness p))))
;;                  (:instance rot-11-inv*f (point (rota-1-rot-11-b11-01-1-witness p)))
;;                  (:instance rota-1-rot-3-b3-01-or-11=>2
;;                             (rot (rot-11))
;;                             (p1 (rot-11-inv*f-witness (rota-1-rot-11-b11-01-1-witness p)))
;;                             (p2 (rota-1-rot-11-b11-01-1-witness p)))
;;                  )
;;            :in-theory nil
;;            )
;;           ("subgoal 3"
;;            :use ((:instance rota-1-rot-12-b12-11 (p p))
;;                  (:instance rota-1-rot-12-b12-11-1 (point p))
;;                  (:instance rota-inv-b3-0-n-f (p p))
;;                  (:instance rota-inv-b3-0-n-f-1-suff
;;                             (point p)
;;                             (p (m-* (rot-12)
;;                                     (rota-1-rot-12-b12-11-1-witness p))))
;;                  (:instance b12-11 (p (rota-1-rot-12-b12-11-1-witness p)))
;;                  (:instance rot*b3-0-set=>b3-0
;;                             (rot (rot-12))
;;                             (p (rota-1-rot-12-b12-11-1-witness p)))
;;                  (:instance b3-0-set-a12 (p (rota-1-rot-12-b12-11-1-witness p)))
;;                  (:instance b3-0-n-f (p (m-* (rot-12)
;;                                              (rota-1-rot-12-b12-11-1-witness p))))
;;                  (:instance rot-12-inv*f (point (rota-1-rot-12-b12-11-1-witness p)))
;;                  (:instance rota-1-rot-3-b3-01-or-11=>2
;;                             (rot (rot-12))
;;                             (p1 (rot-12-inv*f-witness (rota-1-rot-12-b12-11-1-witness p)))
;;                             (p2 (rota-1-rot-12-b12-11-1-witness p)))
;;                  (:instance base-rotations (x (acl2-sqrt 2)))
;;                  (:instance rot-12)
;;                  (:instance b3-0-r-1-a-inv-r-b3-0-a6-iff-b3-0-r-1-a-1-r-a6-1
;;                             (m2 (b-inv-rotation (acl2-sqrt 2)))
;;                             (m1 (rotation-3d
;;                                  (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))
;;                                  (point-on-s2-not-d)))
;;                             (m3 (rotation-3d
;;                                  (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))
;;                                  (point-on-s2-not-d))))
;;                  (:instance base-rotations (x (acl2-sqrt 2)))
;;                  (:instance r3-rotationp-r-theta
;;                             (angle (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))))
;;                  (:instance r3-rotationp-r-theta
;;                             (angle (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))))
;;                  (:instance witness-not-in-angle-sequence)
;;                  (:instance rota-1-rot-12-b12-01 (p p))
;;                  (:instance rota-1-rot-12-b12-01-1 (point p))
;;                  (:instance rota-inv-b3-0-n-f-1-suff
;;                             (point p)
;;                             (p (m-* (rot-12)
;;                                     (rota-1-rot-12-b12-01-1-witness p))))
;;                  (:instance b12-01 (p (rota-1-rot-12-b12-01-1-witness p)))
;;                  (:instance rot*b3-0-set=>b3-0
;;                             (rot (rot-12))
;;                             (p (rota-1-rot-12-b12-01-1-witness p)))
;;                  (:instance b3-0-set-a12 (p (rota-1-rot-12-b12-01-1-witness p)))
;;                  (:instance b3-0-n-f (p (m-* (rot-12)
;;                                              (rota-1-rot-12-b12-01-1-witness p))))
;;                  (:instance rot-12-inv*f (point (rota-1-rot-12-b12-01-1-witness p)))
;;                  (:instance rota-1-rot-3-b3-01-or-11=>2
;;                             (rot (rot-12))
;;                             (p1 (rot-12-inv*f-witness (rota-1-rot-12-b12-01-1-witness p)))
;;                             (p2 (rota-1-rot-12-b12-01-1-witness p)))
;;                  )
;;            :in-theory nil
;;            )
;;           ("subgoal 2"
;;            :use ((:instance rota-1-rot-13-b13-11 (p p))
;;                  (:instance rota-1-rot-13-b13-11-1 (point p))
;;                  (:instance rota-inv-b3-0-n-f (p p))
;;                  (:instance rota-inv-b3-0-n-f-1-suff
;;                             (point p)
;;                             (p (m-* (rot-13)
;;                                     (rota-1-rot-13-b13-11-1-witness p))))
;;                  (:instance b13-11 (p (rota-1-rot-13-b13-11-1-witness p)))
;;                  (:instance rot*b3-0-set=>b3-0
;;                             (rot (rot-13))
;;                             (p (rota-1-rot-13-b13-11-1-witness p)))
;;                  (:instance b3-0-set-a13 (p (rota-1-rot-13-b13-11-1-witness p)))
;;                  (:instance b3-0-n-f (p (m-* (rot-13)
;;                                              (rota-1-rot-13-b13-11-1-witness p))))
;;                  (:instance rot-13-inv*f (point (rota-1-rot-13-b13-11-1-witness p)))
;;                  (:instance rota-1-rot-3-b3-01-or-11=>2
;;                             (rot (rot-13))
;;                             (p1 (rot-13-inv*f-witness (rota-1-rot-13-b13-11-1-witness p)))
;;                             (p2 (rota-1-rot-13-b13-11-1-witness p)))
;;                  (:instance base-rotations (x (acl2-sqrt 2)))
;;                  (:instance rot-13)
;;                  (:instance rota-1-rot-13-b13-01 (p p))
;;                  (:instance rota-1-rot-13-b13-01-1 (point p))
;;                  (:instance rota-inv-b3-0-n-f-1-suff
;;                             (point p)
;;                             (p (m-* (rot-13)
;;                                     (rota-1-rot-13-b13-01-1-witness p))))
;;                  (:instance b13-01 (p (rota-1-rot-13-b13-01-1-witness p)))
;;                  (:instance rot*b3-0-set=>b3-0
;;                             (rot (rot-13))
;;                             (p (rota-1-rot-13-b13-01-1-witness p)))
;;                  (:instance b3-0-set-a13 (p (rota-1-rot-13-b13-01-1-witness p)))
;;                  (:instance b3-0-n-f (p (m-* (rot-13)
;;                                              (rota-1-rot-13-b13-01-1-witness p))))
;;                  (:instance rot-13-inv*f (point (rota-1-rot-13-b13-01-1-witness p)))
;;                  (:instance rota-1-rot-3-b3-01-or-11=>2
;;                             (rot (rot-13))
;;                             (p1 (rot-13-inv*f-witness (rota-1-rot-13-b13-01-1-witness p)))
;;                             (p2 (rota-1-rot-13-b13-01-1-witness p)))
;;                  )
;;            :in-theory nil
;;            )
;;           ("subgoal 1"
;;            :use ((:instance rota-1-rot-14-b14-11 (p p))
;;                  (:instance rota-1-rot-14-b14-11-1 (point p))
;;                  (:instance rota-inv-b3-0-n-f (p p))
;;                  (:instance rota-inv-b3-0-n-f-1-suff
;;                             (point p)
;;                             (p (m-* (rot-14)
;;                                     (rota-1-rot-14-b14-11-1-witness p))))
;;                  (:instance b14-11 (p (rota-1-rot-14-b14-11-1-witness p)))
;;                  (:instance rot*b3-0-set=>b3-0
;;                             (rot (rot-14))
;;                             (p (rota-1-rot-14-b14-11-1-witness p)))
;;                  (:instance b3-0-set-a14 (p (rota-1-rot-14-b14-11-1-witness p)))
;;                  (:instance b3-0-n-f (p (m-* (rot-14)
;;                                              (rota-1-rot-14-b14-11-1-witness p))))
;;                  (:instance rot-14-inv*f (point (rota-1-rot-14-b14-11-1-witness p)))
;;                  (:instance rota-1-rot-3-b3-01-or-11=>2
;;                             (rot (rot-14))
;;                             (p1 (rot-14-inv*f-witness (rota-1-rot-14-b14-11-1-witness p)))
;;                             (p2 (rota-1-rot-14-b14-11-1-witness p)))
;;                  (:instance base-rotations (x (acl2-sqrt 2)))
;;                  (:instance rot-14)
;;                  (:instance rota-1-rot-14-b14-01 (p p))
;;                  (:instance rota-1-rot-14-b14-01-1 (point p))
;;                  (:instance rota-inv-b3-0-n-f-1-suff
;;                             (point p)
;;                             (p (m-* (rot-14)
;;                                     (rota-1-rot-14-b14-01-1-witness p))))
;;                  (:instance b14-01 (p (rota-1-rot-14-b14-01-1-witness p)))
;;                  (:instance rot*b3-0-set=>b3-0
;;                             (rot (rot-14))
;;                             (p (rota-1-rot-14-b14-01-1-witness p)))
;;                  (:instance b3-0-set-a14 (p (rota-1-rot-14-b14-01-1-witness p)))
;;                  (:instance b3-0-n-f (p (m-* (rot-14)
;;                                              (rota-1-rot-14-b14-01-1-witness p))))
;;                  (:instance rot-14-inv*f (point (rota-1-rot-14-b14-01-1-witness p)))
;;                  (:instance rota-1-rot-3-b3-01-or-11=>2
;;                             (rot (rot-14))
;;                             (p1 (rot-14-inv*f-witness (rota-1-rot-14-b14-01-1-witness p)))
;;                             (p2 (rota-1-rot-14-b14-01-1-witness p)))
;;                  )
;;            :in-theory nil
;;            )
;;           ))

;; (defun-sk rot-9-inv*b3-f (point)
;;   (exists p
;;           (and (b3-f p)
;;                (m-= (m-* (r3-m-inverse (rot-9)) p) point))))

;; (defun b9-00 (p)
;;   (and (b3-0-set-a9 p)
;;        (b3-f p)
;;        (rot-9-inv*b3-f p)))

;; (defun b9-10 (p)
;;   (and (b3-0-set-a9 p)
;;        (set-f-p p)
;;        (rot-9-inv*b3-f p)))

;; (defun-sk rot-9-b9-00-1 (point)
;;   (exists p
;;           (and (b9-00 p)
;;                (m-= (m-* (rot-9) p) point))))

;; (defun rot-9-b9-00 (p)
;;   (and (point-in-r3 p)
;;        (rot-9-b9-00-1 p)))

;; (defun-sk rot-9-b9-10-1 (point)
;;   (exists p
;;           (and (b9-10 p)
;;                (m-= (m-* (rot-9) p) point))))

;; (defun rot-9-b9-10 (p)
;;   (and (point-in-r3 p)
;;        (rot-9-b9-10-1 p)))

;; (defun-sk rot-10-inv*b3-f (point)
;;   (exists p
;;           (and (b3-f p)
;;                (m-= (m-* (r3-m-inverse (rot-10)) p) point))))

;; (defun b10-00 (p)
;;   (and (b3-0-set-a10 p)
;;        (b3-f p)
;;        (rot-10-inv*b3-f p)))

;; (defun b10-10 (p)
;;   (and (b3-0-set-a10 p)
;;        (set-f-p p)
;;        (rot-10-inv*b3-f p)))

;; (defun-sk rot-10-b10-00-1 (point)
;;   (exists p
;;           (and (b10-00 p)
;;                (m-= (m-* (rot-10) p) point))))

;; (defun rot-10-b10-00 (p)
;;   (and (point-in-r3 p)
;;        (rot-10-b10-00-1 p)))

;; (defun-sk rot-10-b10-10-1 (point)
;;   (exists p
;;           (and (b10-10 p)
;;                (m-= (m-* (rot-10) p) point))))

;; (defun rot-10-b10-10 (p)
;;   (and (point-in-r3 p)
;;        (rot-10-b10-10-1 p)))

;; (defun-sk rot-11-inv*b3-f (point)
;;   (exists p
;;           (and (b3-f p)
;;                (m-= (m-* (r3-m-inverse (rot-11)) p) point))))

;; (defun b11-00 (p)
;;   (and (b3-0-set-a11 p)
;;        (b3-f p)
;;        (rot-11-inv*b3-f p)))

;; (defun b11-10 (p)
;;   (and (b3-0-set-a11 p)
;;        (set-f-p p)
;;        (rot-11-inv*b3-f p)))

;; (defun-sk rot-11-b11-00-1 (point)
;;   (exists p
;;           (and (b11-00 p)
;;                (m-= (m-* (rot-11) p) point))))

;; (defun rot-11-b11-00 (p)
;;   (and (point-in-r3 p)
;;        (rot-11-b11-00-1 p)))

;; (defun-sk rot-11-b11-10-1 (point)
;;   (exists p
;;           (and (b11-10 p)
;;                (m-= (m-* (rot-11) p) point))))

;; (defun rot-11-b11-10 (p)
;;   (and (point-in-r3 p)
;;        (rot-11-b11-10-1 p)))

;; (defun-sk rot-12-inv*b3-f (point)
;;   (exists p
;;           (and (b3-f p)
;;                (m-= (m-* (r3-m-inverse (rot-12)) p) point))))

;; (defun b12-00 (p)
;;   (and (b3-0-set-a12 p)
;;        (b3-f p)
;;        (rot-12-inv*b3-f p)))

;; (defun b12-10 (p)
;;   (and (b3-0-set-a12 p)
;;        (set-f-p p)
;;        (rot-12-inv*b3-f p)))

;; (defun-sk rot-12-b12-00-1 (point)
;;   (exists p
;;           (and (b12-00 p)
;;                (m-= (m-* (rot-12) p) point))))

;; (defun rot-12-b12-00 (p)
;;   (and (point-in-r3 p)
;;        (rot-12-b12-00-1 p)))

;; (defun-sk rot-12-b12-10-1 (point)
;;   (exists p
;;           (and (b12-10 p)
;;                (m-= (m-* (rot-12) p) point))))

;; (defun rot-12-b12-10 (p)
;;   (and (point-in-r3 p)
;;        (rot-12-b12-10-1 p)))

;; (defun-sk rot-13-inv*b3-f (point)
;;   (exists p
;;           (and (b3-f p)
;;                (m-= (m-* (r3-m-inverse (rot-13)) p) point))))

;; (defun b13-00 (p)
;;   (and (b3-0-set-a13 p)
;;        (b3-f p)
;;        (rot-13-inv*b3-f p)))

;; (defun b13-10 (p)
;;   (and (b3-0-set-a13 p)
;;        (set-f-p p)
;;        (rot-13-inv*b3-f p)))

;; (defun-sk rot-13-b13-00-1 (point)
;;   (exists p
;;           (and (b13-00 p)
;;                (m-= (m-* (rot-13) p) point))))

;; (defun rot-13-b13-00 (p)
;;   (and (point-in-r3 p)
;;        (rot-13-b13-00-1 p)))

;; (defun-sk rot-13-b13-10-1 (point)
;;   (exists p
;;           (and (b13-10 p)
;;                (m-= (m-* (rot-13) p) point))))

;; (defun rot-13-b13-10 (p)
;;   (and (point-in-r3 p)
;;        (rot-13-b13-10-1 p)))

;; (defun-sk rot-14-inv*b3-f (point)
;;   (exists p
;;           (and (b3-f p)
;;                (m-= (m-* (r3-m-inverse (rot-14)) p) point))))

;; (defun b14-00 (p)
;;   (and (b3-0-set-a14 p)
;;        (b3-f p)
;;        (rot-14-inv*b3-f p)))

;; (defun b14-10 (p)
;;   (and (b3-0-set-a14 p)
;;        (set-f-p p)
;;        (rot-14-inv*b3-f p)))

;; (defun-sk rot-14-b14-00-1 (point)
;;   (exists p
;;           (and (b14-00 p)
;;                (m-= (m-* (rot-14) p) point))))

;; (defun rot-14-b14-00 (p)
;;   (and (point-in-r3 p)
;;        (rot-14-b14-00-1 p)))

;; (defun-sk rot-14-b14-10-1 (point)
;;   (exists p
;;           (and (b14-10 p)
;;                (m-= (m-* (rot-14) p) point))))

;; (defun rot-14-b14-10 (p)
;;   (and (point-in-r3 p)
;;        (rot-14-b14-10-1 p)))

;; (defthmd a9-a14-b3-0-n-b3-f=>
;;   (implies (b3-0-n-b3-f p)
;;            (or (rot-9-b9-00 p)
;;                (rot-9-b9-10 p)
;;                (rot-10-b10-00 p)
;;                (rot-10-b10-10 p)
;;                (rot-11-b11-00 p)
;;                (rot-11-b11-10 p)
;;                (rot-12-b12-00 p)
;;                (rot-12-b12-10 p)
;;                (rot-13-b13-00 p)
;;                (rot-13-b13-10 p)
;;                (rot-14-b14-00 p)
;;                (rot-14-b14-10 p)))
;;   :hints (("goal"
;;            :cases ((b3-0-b-inv-b3-0-set-a9 p)
;;                    (b3-0-b-inv-r-b3-0-set-a10 p)
;;                    (b3-0-r-1-b-inv-b3-0-set-a11 p)
;;                    (b3-0-r-1-b-inv-r-b3-0-set-a12 p)
;;                    (b3-0-set-a13 p)
;;                    (b3-0-set-a14 p))
;;            :use ((:instance b3-0-n-b3-f (p p))
;;                  (:instance b3-0-iff-a9-to-a14 (p p))
;;                  )
;;            :in-theory nil
;;            )
;;           ("subgoal 6"
;;            :use ((:instance b3-0-b-inv-b3-0-set-a9 (p p))
;;                  (:instance b3-0-b-inv-b3-0-set-a9-1 (p p))
;;                  (:instance rot-9-b9-10 (p p))
;;                  (:instance rot-9-b9-10-1-suff (point p) (p (b3-0-b-inv-b3-0-set-a9-1-witness p)))
;;                  (:instance b9-10 (p (b3-0-b-inv-b3-0-set-a9-1-witness p)))
;;                  (:instance b3-f (p (b3-0-b-inv-b3-0-set-a9-1-witness p)))
;;                  (:instance rot-9-b9-00 (p p))
;;                  (:instance rot-9-b9-00-1-suff (point p) (p (b3-0-b-inv-b3-0-set-a9-1-witness p)))
;;                  (:instance b9-00 (p (b3-0-b-inv-b3-0-set-a9-1-witness p)))
;;                  (:instance rot-9)
;;                  (:instance rot-9-inv*b3-f-suff (p p) (point (b3-0-b-inv-b3-0-set-a9-1-witness p)))
;;                  (:instance a3-a8-rot-a-inv-b3-0-nf=>1
;;                             (m1 (rot-9))
;;                             (m2 (b3-0-b-inv-b3-0-set-a9-1-witness p))
;;                             (m3 p)
;;                             (m4 (r3-m-inverse (rot-9)))
;;                             (m5 (id-rotation))
;;                             (m6 (b3-0-b-inv-b3-0-set-a9-1-witness p)))
;;                  (:instance m-*point-id=point (p1 (b3-0-b-inv-b3-0-set-a9-1-witness p)))
;;                  (:instance b3-0-set-a9 (p (b3-0-b-inv-b3-0-set-a9-1-witness p)))
;;                  (:instance m-*-m-inverse-m
;;                             (m (rot-9)))
;;                  (:instance base-rotations (x (acl2-sqrt 2)))
;;                  (:instance r3-rotationp (m (b-inv-rotation (acl2-sqrt 2))))
;;                  (:instance b3 (p (b3-0-b-inv-b3-0-set-a9-1-witness p)))
;;                  )
;;            :in-theory nil
;;            )
;;           ("subgoal 5"
;;            :use ((:instance b3-0-b-inv-r-b3-0-set-a10 (p p))
;;                  (:instance b3-0-b-inv-r-b3-0-set-a10-1 (p p))
;;                  (:instance rot-10-b10-10 (p p))
;;                  (:instance rot-10-b10-10-1-suff (point p) (p (b3-0-b-inv-r-b3-0-set-a10-1-witness p)))
;;                  (:instance b10-10 (p (b3-0-b-inv-r-b3-0-set-a10-1-witness p)))
;;                  (:instance b3-f (p (b3-0-b-inv-r-b3-0-set-a10-1-witness p)))
;;                  (:instance rot-10-b10-00 (p p))
;;                  (:instance rot-10-b10-00-1-suff (point p) (p (b3-0-b-inv-r-b3-0-set-a10-1-witness p)))
;;                  (:instance b10-00 (p (b3-0-b-inv-r-b3-0-set-a10-1-witness p)))
;;                  (:instance rot-10)
;;                  (:instance rot-10-inv*b3-f-suff (p p) (point (b3-0-b-inv-r-b3-0-set-a10-1-witness p)))
;;                  (:instance a3-a8-rot-a-inv-b3-0-nf=>1
;;                             (m1 (rot-10))
;;                             (m2 (b3-0-b-inv-r-b3-0-set-a10-1-witness p))
;;                             (m3 p)
;;                             (m4 (r3-m-inverse (rot-10)))
;;                             (m5 (id-rotation))
;;                             (m6 (b3-0-b-inv-r-b3-0-set-a10-1-witness p)))
;;                  (:instance associativity-of-m-*
;;                             (m1 (b-inv-rotation (acl2-sqrt 2)))
;;                             (m2 (rotation-3d
;;                                  (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))
;;                                  (point-on-s2-not-d)))
;;                             (m3 (b3-0-b-inv-r-b3-0-set-a10-1-witness p)))
;;                  (:instance m-*point-id=point (p1 (b3-0-b-inv-r-b3-0-set-a10-1-witness p)))
;;                  (:instance b3-0-set-a10 (p (b3-0-b-inv-r-b3-0-set-a10-1-witness p)))
;;                  (:instance m-*-m-inverse-m
;;                             (m (rot-10)))
;;                  (:instance base-rotations (x (acl2-sqrt 2)))
;;                  (:instance r3-rotationp-r-theta
;;                             (angle (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))))
;;                  (:instance rot*rot-is-rot
;;                             (m1 (b-inv-rotation (acl2-sqrt 2)))
;;                             (m2 (rotation-3d
;;                                  (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))
;;                                  (point-on-s2-not-d))))
;;                  (:instance witness-not-in-angle-sequence)
;;                  (:instance r3-rotationp (m (rot-10)))
;;                  (:instance b3 (p (b3-0-b-inv-r-b3-0-set-a10-1-witness p)))
;;                  )
;;            :in-theory nil
;;            )
;;           ("subgoal 4"
;;            :use ((:instance b3-0-r-1-b-inv-b3-0-set-a11 (p p))
;;                  (:instance b3-0-r-1-b-inv-b3-0-set-a11-1 (p p))
;;                  (:instance rot-11-b11-10 (p p))
;;                  (:instance rot-11-b11-10-1-suff (point p) (p (b3-0-r-1-b-inv-b3-0-set-a11-1-witness p)))
;;                  (:instance b11-10 (p (b3-0-r-1-b-inv-b3-0-set-a11-1-witness p)))
;;                  (:instance b3-f (p (b3-0-r-1-b-inv-b3-0-set-a11-1-witness p)))
;;                  (:instance rot-11-b11-00 (p p))
;;                  (:instance rot-11-b11-00-1-suff (point p) (p (b3-0-r-1-b-inv-b3-0-set-a11-1-witness p)))
;;                  (:instance b11-00 (p (b3-0-r-1-b-inv-b3-0-set-a11-1-witness p)))
;;                  (:instance rot-11)
;;                  (:instance rot-11-inv*b3-f-suff (p p) (point (b3-0-r-1-b-inv-b3-0-set-a11-1-witness p)))
;;                  (:instance a3-a8-rot-a-inv-b3-0-nf=>1
;;                             (m1 (rot-11))
;;                             (m2 (b3-0-r-1-b-inv-b3-0-set-a11-1-witness p))
;;                             (m3 p)
;;                             (m4 (r3-m-inverse (rot-11)))
;;                             (m5 (id-rotation))
;;                             (m6 (b3-0-r-1-b-inv-b3-0-set-a11-1-witness p)))
;;                  (:instance associativity-of-m-*
;;                             (m2 (b-inv-rotation (acl2-sqrt 2)))
;;                             (m1 (rotation-3d
;;                                  (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))
;;                                  (point-on-s2-not-d)))
;;                             (m3 (b3-0-r-1-b-inv-b3-0-set-a11-1-witness p)))
;;                  (:instance m-*point-id=point (p1 (b3-0-r-1-b-inv-b3-0-set-a11-1-witness p)))
;;                  (:instance b3-0-set-a11 (p (b3-0-r-1-b-inv-b3-0-set-a11-1-witness p)))
;;                  (:instance m-*-m-inverse-m
;;                             (m (rot-11)))
;;                  (:instance base-rotations (x (acl2-sqrt 2)))
;;                  (:instance r3-rotationp-r-theta
;;                             (angle (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))))
;;                  (:instance rot*rot-is-rot
;;                             (m2 (b-inv-rotation (acl2-sqrt 2)))
;;                             (m1 (rotation-3d
;;                                  (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))
;;                                  (point-on-s2-not-d))))
;;                  (:instance witness-not-in-angle-sequence)
;;                  (:instance r3-rotationp (m (rot-11)))
;;                  (:instance b3 (p (b3-0-r-1-b-inv-b3-0-set-a11-1-witness p)))
;;                  )
;;            :in-theory nil
;;            )
;;           ("subgoal 3"
;;            :use ((:instance b3-0-r-1-b-inv-r-b3-0-set-a12 (p p))
;;                  (:instance b3-0-r-1-b-inv-r-b3-0-set-a12-1 (p p))
;;                  (:instance rot-12-b12-10 (p p))
;;                  (:instance rot-12-b12-10-1-suff (point p) (p (b3-0-r-1-b-inv-r-b3-0-set-a12-1-witness p)))
;;                  (:instance b12-10 (p (b3-0-r-1-b-inv-r-b3-0-set-a12-1-witness p)))
;;                  (:instance b3-f (p (b3-0-r-1-b-inv-r-b3-0-set-a12-1-witness p)))
;;                  (:instance rot-12-b12-00 (p p))
;;                  (:instance rot-12-b12-00-1-suff (point p) (p (b3-0-r-1-b-inv-r-b3-0-set-a12-1-witness p)))
;;                  (:instance b12-00 (p (b3-0-r-1-b-inv-r-b3-0-set-a12-1-witness p)))
;;                  (:instance rot-12)
;;                  (:instance rot-12-inv*b3-f-suff (p p) (point (b3-0-r-1-b-inv-r-b3-0-set-a12-1-witness p)))
;;                  (:instance a3-a8-rot-a-inv-b3-0-nf=>1
;;                             (m1 (rot-12))
;;                             (m2 (b3-0-r-1-b-inv-r-b3-0-set-a12-1-witness p))
;;                             (m3 p)
;;                             (m4 (r3-m-inverse (rot-12)))
;;                             (m5 (id-rotation))
;;                             (m6 (b3-0-r-1-b-inv-r-b3-0-set-a12-1-witness p)))
;;                  (:instance a3-a8-rot-a-inv-b3-0-nf=>sub-3
;;                             (m1 (rotation-3d
;;                                  (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))
;;                                             (point-on-s2-not-d)))
;;                             (m2 (b-inv-rotation (acl2-sqrt 2)))
;;                             (m3 (rotation-3d
;;                                  (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))
;;                                  (point-on-s2-not-d)))
;;                             (m4 (b3-0-r-1-b-inv-r-b3-0-set-a12-1-witness p)))
;;                  (:instance m-*point-id=point (p1 (b3-0-r-1-b-inv-r-b3-0-set-a12-1-witness p)))
;;                  (:instance b3-0-set-a12 (p (b3-0-r-1-b-inv-r-b3-0-set-a12-1-witness p)))
;;                  (:instance m-*-m-inverse-m
;;                             (m (rot-12)))
;;                  (:instance base-rotations (x (acl2-sqrt 2)))
;;                  (:instance r3-rotationp-r-theta
;;                             (angle (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))))
;;                  (:instance r3-rotationp-r-theta
;;                             (angle (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))))
;;                  (:instance b3-0-r-1-a-inv-r-b3-0-a6-iff-b3-0-r-1-a-1-r-a6-1
;;                             (m2 (b-inv-rotation (acl2-sqrt 2)))
;;                             (m1 (rotation-3d
;;                                  (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))
;;                                  (point-on-s2-not-d)))
;;                             (m3 (rotation-3d
;;                                  (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))
;;                                  (point-on-s2-not-d))))
;;                  (:instance witness-not-in-angle-sequence)
;;                  (:instance r3-rotationp (m (rot-12)))
;;                  (:instance b3 (p (b3-0-r-1-b-inv-r-b3-0-set-a12-1-witness p)))
;;                  )
;;            :in-theory nil
;;            )
;;           ("subgoal 2"
;;            :use ((:instance rot-13-b13-10 (p p))
;;                  (:instance rot-13-b13-10-1-suff (point p) (p p))
;;                  (:instance b13-10 (p p))
;;                  (:instance b3-f (p p))
;;                  (:instance b3-0-set-a13 (p p))
;;                  (:instance rot-13-b13-00 (p p))
;;                  (:instance rot-13-b13-00-1-suff (point p) (p p))
;;                  (:instance b13-00 (p p))
;;                  (:instance rot-13)
;;                  (:instance rot-13-inv*b3-f-suff (p p) (point p))
;;                  (:instance a3-a8-rot-a-inv-b3-0-nf=>1
;;                             (m1 (rot-13))
;;                             (m2 p)
;;                             (m3 p)
;;                             (m4 (r3-m-inverse (rot-13)))
;;                             (m5 (id-rotation))
;;                             (m6 p))
;;                  (:instance m-*point-id=point (p1 p))
;;                  (:instance m-*-m-inverse-m
;;                             (m (rot-13)))
;;                  (:instance base-rotations (x (acl2-sqrt 2)))
;;                  (:instance r3-rotationp (m (id-rotation)))
;;                  )
;;            :in-theory nil
;;            )
;;           ("subgoal 1"
;;            :use ((:instance rot-14-b14-10 (p p))
;;                  (:instance rot-14-b14-10-1-suff (point p) (p p))
;;                  (:instance b14-10 (p p))
;;                  (:instance b3-f (p p))
;;                  (:instance b3-0-set-a14 (p p))
;;                  (:instance rot-14-b14-00 (p p))
;;                  (:instance rot-14-b14-00-1-suff (point p) (p p))
;;                  (:instance b14-00 (p p))
;;                  (:instance rot-14)
;;                  (:instance rot-14-inv*b3-f-suff (p p) (point p))
;;                  (:instance a3-a8-rot-a-inv-b3-0-nf=>1
;;                             (m1 (rot-14))
;;                             (m2 p)
;;                             (m3 p)
;;                             (m4 (r3-m-inverse (rot-14)))
;;                             (m5 (id-rotation))
;;                             (m6 p))
;;                  (:instance m-*point-id=point (p1 p))
;;                  (:instance m-*-m-inverse-m
;;                             (m (rot-14)))
;;                  (:instance base-rotations (x (acl2-sqrt 2)))
;;                  (:instance r3-rotationp (m (id-rotation)))
;;                  )
;;            :in-theory nil
;;            )
;;           ))

;; (defthmd rot-9-14-b-9-14-01-or-11=>
;;   (implies (or (rot-9-b9-00 p)
;;                (rot-9-b9-10 p)
;;                (rot-10-b10-00 p)
;;                (rot-10-b10-10 p)
;;                (rot-11-b11-00 p)
;;                (rot-11-b11-10 p)
;;                (rot-12-b12-00 p)
;;                (rot-12-b12-10 p)
;;                (rot-13-b13-00 p)
;;                (rot-13-b13-10 p)
;;                (rot-14-b14-00 p)
;;                (rot-14-b14-10 p))
;;            (b3-0-n-b3-f p))
;;   :hints (("goal"
;;            :cases ((rot-9-b9-00 p)
;;                    (rot-9-b9-10 p)
;;                    (rot-10-b10-00 p)
;;                    (rot-10-b10-10 p)
;;                    (rot-11-b11-00 p)
;;                    (rot-11-b11-10 p)
;;                    (rot-12-b12-00 p)
;;                    (rot-12-b12-10 p)
;;                    (rot-13-b13-00 p)
;;                    (rot-13-b13-10 p)
;;                    (rot-14-b14-00 p)
;;                    (rot-14-b14-10 p))
;;            :in-theory nil
;;            )
;;           ("subgoal 12"
;;            :use ((:instance rot-9-b9-00 (p p))
;;                  (:instance rot-9-b9-00-1 (point p))
;;                  (:instance b9-00 (p (rot-9-b9-00-1-witness p)))
;;                  (:instance rot-9-inv*b3-f (point (rot-9-b9-00-1-witness p)))
;;                  (:instance b3-0-n-b3-f (p p))
;;                  (:instance rot*b3-0-set=>b3-0
;;                             (p (rot-9-b9-00-1-witness p))
;;                             (rot (rot-9)))
;;                  (:instance rot-9)
;;                  (:instance base-rotations (x (acl2-sqrt 2)))
;;                  (:instance b3-0 (p (m-* (rot-9) (rot-9-b9-00-1-witness p))))
;;                  (:instance b3-0 (p p))
;;                  (:instance cal-radius-p1=p2
;;                             (p1 (m-* (rot-9) (rot-9-b9-00-1-witness p)))
;;                             (p2 p))
;;                  (:instance b3-f (p p))
;;                  (:instance b3 (p p))
;;                  (:instance rot-3-8-b-3-8-01-or-11=>1
;;                             (rot (rot-9))
;;                             (wit (rot-9-b9-00-1-witness p))
;;                             (p p)
;;                             (wit-wit (rot-9-inv*b3-f-witness (rot-9-b9-00-1-witness p))))
;;                  (:instance b3 (p (rot-9-inv*b3-f-witness (rot-9-b9-00-1-witness p))))
;;                  (:instance b3-f (p (rot-9-inv*b3-f-witness (rot-9-b9-00-1-witness p))))
;;                  )
;;            :in-theory nil
;;            )
;;           ("subgoal 11"
;;            :use ((:instance rot-9-b9-10 (p p))
;;                  (:instance rot-9-b9-10-1 (point p))
;;                  (:instance b9-10 (p (rot-9-b9-10-1-witness p)))
;;                  (:instance rot-9-inv*b3-f (point (rot-9-b9-10-1-witness p)))
;;                  (:instance b3-0-n-b3-f (p p))
;;                  (:instance rot*b3-0-set=>b3-0
;;                             (p (rot-9-b9-10-1-witness p))
;;                             (rot (rot-9)))
;;                  (:instance rot-9)
;;                  (:instance base-rotations (x (acl2-sqrt 2)))
;;                  (:instance b3-0 (p (m-* (rot-9) (rot-9-b9-10-1-witness p))))
;;                  (:instance b3-0 (p p))
;;                  (:instance cal-radius-p1=p2
;;                             (p1 (m-* (rot-9) (rot-9-b9-10-1-witness p)))
;;                             (p2 p))
;;                  (:instance b3-f (p p))
;;                  (:instance b3 (p p))
;;                  (:instance rot-3-8-b-3-8-01-or-11=>1
;;                             (rot (rot-9))
;;                             (wit (rot-9-b9-10-1-witness p))
;;                             (p p)
;;                             (wit-wit (rot-9-inv*b3-f-witness (rot-9-b9-10-1-witness p))))
;;                  (:instance b3 (p (rot-9-inv*b3-f-witness (rot-9-b9-10-1-witness p))))
;;                  (:instance b3-f (p (rot-9-inv*b3-f-witness (rot-9-b9-10-1-witness p))))
;;                  )
;;            :in-theory nil
;;            )
;;           ("subgoal 10"
;;            :use ((:instance rot-10-b10-00 (p p))
;;                  (:instance rot-10-b10-00-1 (point p))
;;                  (:instance b10-00 (p (rot-10-b10-00-1-witness p)))
;;                  (:instance rot-10-inv*b3-f (point (rot-10-b10-00-1-witness p)))
;;                  (:instance b3-0-n-b3-f (p p))
;;                  (:instance rot*b3-0-set=>b3-0
;;                             (p (rot-10-b10-00-1-witness p))
;;                             (rot (rot-10)))
;;                  (:instance rot-10)
;;                  (:instance rot*rot-is-rot
;;                             (m1 (b-inv-rotation (acl2-sqrt 2)))
;;                             (m2 (rotation-3d
;;                                  (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))
;;                                  (point-on-s2-not-d))))
;;                  (:instance r3-rotationp-r-theta
;;                             (angle (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))))
;;                  (:instance base-rotations (x (acl2-sqrt 2)))
;;                  (:instance witness-not-in-angle-sequence)
;;                  (:instance b3-0 (p (m-* (rot-10) (rot-10-b10-00-1-witness p))))
;;                  (:instance b3-0 (p p))
;;                  (:instance cal-radius-p1=p2
;;                             (p1 (m-* (rot-10) (rot-10-b10-00-1-witness p)))
;;                             (p2 p))
;;                  (:instance b3-f (p p))
;;                  (:instance b3 (p p))
;;                  (:instance rot-3-8-b-3-8-01-or-11=>1
;;                             (rot (rot-10))
;;                             (wit (rot-10-b10-00-1-witness p))
;;                             (p p)
;;                             (wit-wit (rot-10-inv*b3-f-witness (rot-10-b10-00-1-witness p))))
;;                  (:instance b3 (p (rot-10-inv*b3-f-witness (rot-10-b10-00-1-witness p))))
;;                  (:instance b3-f (p (rot-10-inv*b3-f-witness (rot-10-b10-00-1-witness p))))
;;                  )
;;            :in-theory nil
;;            )
;;           ("subgoal 9"
;;            :use ((:instance rot-10-b10-10 (p p))
;;                  (:instance rot-10-b10-10-1 (point p))
;;                  (:instance b10-10 (p (rot-10-b10-10-1-witness p)))
;;                  (:instance rot-10-inv*b3-f (point (rot-10-b10-10-1-witness p)))
;;                  (:instance b3-0-n-b3-f (p p))
;;                  (:instance rot*b3-0-set=>b3-0
;;                             (p (rot-10-b10-10-1-witness p))
;;                             (rot (rot-10)))
;;                  (:instance rot-10)
;;                  (:instance rot*rot-is-rot
;;                             (m1 (b-inv-rotation (acl2-sqrt 2)))
;;                             (m2 (rotation-3d
;;                                  (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))
;;                                  (point-on-s2-not-d))))
;;                  (:instance r3-rotationp-r-theta
;;                             (angle (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))))
;;                  (:instance base-rotations (x (acl2-sqrt 2)))
;;                  (:instance witness-not-in-angle-sequence)
;;                  (:instance b3-0 (p (m-* (rot-10) (rot-10-b10-10-1-witness p))))
;;                  (:instance b3-0 (p p))
;;                  (:instance cal-radius-p1=p2
;;                             (p1 (m-* (rot-10) (rot-10-b10-10-1-witness p)))
;;                             (p2 p))
;;                  (:instance b3-f (p p))
;;                  (:instance b3 (p p))
;;                  (:instance rot-3-8-b-3-8-01-or-11=>1
;;                             (rot (rot-10))
;;                             (wit (rot-10-b10-10-1-witness p))
;;                             (p p)
;;                             (wit-wit (rot-10-inv*b3-f-witness (rot-10-b10-10-1-witness p))))
;;                  (:instance b3 (p (rot-10-inv*b3-f-witness (rot-10-b10-10-1-witness p))))
;;                  (:instance b3-f (p (rot-10-inv*b3-f-witness (rot-10-b10-10-1-witness p))))
;;                  )
;;            :in-theory nil
;;            )
;;           ("subgoal 8"
;;            :use ((:instance rot-11-b11-00 (p p))
;;                  (:instance rot-11-b11-00-1 (point p))
;;                  (:instance b11-00 (p (rot-11-b11-00-1-witness p)))
;;                  (:instance rot-11-inv*b3-f (point (rot-11-b11-00-1-witness p)))
;;                  (:instance b3-0-n-b3-f (p p))
;;                  (:instance rot*b3-0-set=>b3-0
;;                             (p (rot-11-b11-00-1-witness p))
;;                             (rot (rot-11)))
;;                  (:instance rot-11)
;;                  (:instance rot*rot-is-rot
;;                             (m2 (b-inv-rotation (acl2-sqrt 2)))
;;                             (m1 (rotation-3d
;;                                  (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))
;;                                  (point-on-s2-not-d))))
;;                  (:instance r3-rotationp-r-theta
;;                             (angle (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))))
;;                  (:instance base-rotations (x (acl2-sqrt 2)))
;;                  (:instance witness-not-in-angle-sequence)
;;                  (:instance b3-0 (p (m-* (rot-11) (rot-11-b11-00-1-witness p))))
;;                  (:instance b3-0 (p p))
;;                  (:instance cal-radius-p1=p2
;;                             (p1 (m-* (rot-11) (rot-11-b11-00-1-witness p)))
;;                             (p2 p))
;;                  (:instance b3-f (p p))
;;                  (:instance b3 (p p))
;;                  (:instance rot-3-8-b-3-8-01-or-11=>1
;;                             (rot (rot-11))
;;                             (wit (rot-11-b11-00-1-witness p))
;;                             (p p)
;;                             (wit-wit (rot-11-inv*b3-f-witness (rot-11-b11-00-1-witness p))))
;;                  (:instance b3 (p (rot-11-inv*b3-f-witness (rot-11-b11-00-1-witness p))))
;;                  (:instance b3-f (p (rot-11-inv*b3-f-witness (rot-11-b11-00-1-witness p))))
;;                  )
;;            :in-theory nil
;;            )
;;           ("subgoal 7"
;;            :use ((:instance rot-11-b11-10 (p p))
;;                  (:instance rot-11-b11-10-1 (point p))
;;                  (:instance b11-10 (p (rot-11-b11-10-1-witness p)))
;;                  (:instance rot-11-inv*b3-f (point (rot-11-b11-10-1-witness p)))
;;                  (:instance b3-0-n-b3-f (p p))
;;                  (:instance rot*b3-0-set=>b3-0
;;                             (p (rot-11-b11-10-1-witness p))
;;                             (rot (rot-11)))
;;                  (:instance rot-11)
;;                  (:instance rot*rot-is-rot
;;                             (m2 (b-inv-rotation (acl2-sqrt 2)))
;;                             (m1 (rotation-3d
;;                                  (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))
;;                                  (point-on-s2-not-d))))
;;                  (:instance r3-rotationp-r-theta
;;                             (angle (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))))
;;                  (:instance base-rotations (x (acl2-sqrt 2)))
;;                  (:instance witness-not-in-angle-sequence)
;;                  (:instance b3-0 (p (m-* (rot-11) (rot-11-b11-10-1-witness p))))
;;                  (:instance b3-0 (p p))
;;                  (:instance cal-radius-p1=p2
;;                             (p1 (m-* (rot-11) (rot-11-b11-10-1-witness p)))
;;                             (p2 p))
;;                  (:instance b3-f (p p))
;;                  (:instance b3 (p p))
;;                  (:instance rot-3-8-b-3-8-01-or-11=>1
;;                             (rot (rot-11))
;;                             (wit (rot-11-b11-10-1-witness p))
;;                             (p p)
;;                             (wit-wit (rot-11-inv*b3-f-witness (rot-11-b11-10-1-witness p))))
;;                  (:instance b3 (p (rot-11-inv*b3-f-witness (rot-11-b11-10-1-witness p))))
;;                  (:instance b3-f (p (rot-11-inv*b3-f-witness (rot-11-b11-10-1-witness p))))
;;                  )
;;            :in-theory nil
;;            )
;;           ("subgoal 6"
;;            :use ((:instance rot-12-b12-00 (p p))
;;                  (:instance rot-12-b12-00-1 (point p))
;;                  (:instance b12-00 (p (rot-12-b12-00-1-witness p)))
;;                  (:instance rot-12-inv*b3-f (point (rot-12-b12-00-1-witness p)))
;;                  (:instance b3-0-n-b3-f (p p))
;;                  (:instance rot*b3-0-set=>b3-0
;;                             (p (rot-12-b12-00-1-witness p))
;;                             (rot (rot-12)))
;;                  (:instance rot-12)
;;                  (:instance b3-0-r-1-a-inv-r-b3-0-a6-iff-b3-0-r-1-a-1-r-a6-1
;;                             (m2 (b-inv-rotation (acl2-sqrt 2)))
;;                             (m1 (rotation-3d
;;                                  (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))
;;                                  (point-on-s2-not-d)))
;;                             (m3 (rotation-3d
;;                                  (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))
;;                                  (point-on-s2-not-d))))
;;                  (:instance r3-rotationp-r-theta
;;                             (angle (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))))
;;                  (:instance r3-rotationp-r-theta
;;                             (angle (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))))
;;                  (:instance base-rotations (x (acl2-sqrt 2)))
;;                  (:instance witness-not-in-angle-sequence)
;;                  (:instance b3-0 (p (m-* (rot-12) (rot-12-b12-00-1-witness p))))
;;                  (:instance b3-0 (p p))
;;                  (:instance cal-radius-p1=p2
;;                             (p1 (m-* (rot-12) (rot-12-b12-00-1-witness p)))
;;                             (p2 p))
;;                  (:instance b3-f (p p))
;;                  (:instance b3 (p p))
;;                  (:instance rot-3-8-b-3-8-01-or-11=>1
;;                             (rot (rot-12))
;;                             (wit (rot-12-b12-00-1-witness p))
;;                             (p p)
;;                             (wit-wit (rot-12-inv*b3-f-witness (rot-12-b12-00-1-witness p))))
;;                  (:instance b3 (p (rot-12-inv*b3-f-witness (rot-12-b12-00-1-witness p))))
;;                  (:instance b3-f (p (rot-12-inv*b3-f-witness (rot-12-b12-00-1-witness p))))
;;                  )
;;            :in-theory nil
;;            )
;;           ("subgoal 5"
;;            :use ((:instance rot-12-b12-10 (p p))
;;                  (:instance rot-12-b12-10-1 (point p))
;;                  (:instance b12-10 (p (rot-12-b12-10-1-witness p)))
;;                  (:instance rot-12-inv*b3-f (point (rot-12-b12-10-1-witness p)))
;;                  (:instance b3-0-n-b3-f (p p))
;;                  (:instance rot*b3-0-set=>b3-0
;;                             (p (rot-12-b12-10-1-witness p))
;;                             (rot (rot-12)))
;;                  (:instance rot-12)
;;                  (:instance b3-0-r-1-a-inv-r-b3-0-a6-iff-b3-0-r-1-a-1-r-a6-1
;;                             (m2 (b-inv-rotation (acl2-sqrt 2)))
;;                             (m1 (rotation-3d
;;                                  (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))
;;                                  (point-on-s2-not-d)))
;;                             (m3 (rotation-3d
;;                                  (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))
;;                                  (point-on-s2-not-d))))
;;                  (:instance r3-rotationp-r-theta
;;                             (angle (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))))
;;                  (:instance r3-rotationp-r-theta
;;                             (angle (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))))
;;                  (:instance base-rotations (x (acl2-sqrt 2)))
;;                  (:instance witness-not-in-angle-sequence)
;;                  (:instance b3-0 (p (m-* (rot-12) (rot-12-b12-10-1-witness p))))
;;                  (:instance b3-0 (p p))
;;                  (:instance cal-radius-p1=p2
;;                             (p1 (m-* (rot-12) (rot-12-b12-10-1-witness p)))
;;                             (p2 p))
;;                  (:instance b3-f (p p))
;;                  (:instance b3 (p p))
;;                  (:instance rot-3-8-b-3-8-01-or-11=>1
;;                             (rot (rot-12))
;;                             (wit (rot-12-b12-10-1-witness p))
;;                             (p p)
;;                             (wit-wit (rot-12-inv*b3-f-witness (rot-12-b12-10-1-witness p))))
;;                  (:instance b3 (p (rot-12-inv*b3-f-witness (rot-12-b12-10-1-witness p))))
;;                  (:instance b3-f (p (rot-12-inv*b3-f-witness (rot-12-b12-10-1-witness p))))
;;                  )
;;            :in-theory nil
;;            )
;;           ("subgoal 4"
;;            :use ((:instance rot-13-b13-00 (p p))
;;                  (:instance rot-13-b13-00-1 (point p))
;;                  (:instance b13-00 (p (rot-13-b13-00-1-witness p)))
;;                  (:instance rot-13-inv*b3-f (point (rot-13-b13-00-1-witness p)))
;;                  (:instance b3-0-n-b3-f (p p))
;;                  (:instance rot*b3-0-set=>b3-0
;;                             (p (rot-13-b13-00-1-witness p))
;;                             (rot (rot-13)))
;;                  (:instance rot-13)
;;                  (:instance base-rotations (x (acl2-sqrt 2)))
;;                  (:instance b3-0 (p (m-* (rot-13) (rot-13-b13-00-1-witness p))))
;;                  (:instance b3-0 (p p))
;;                  (:instance cal-radius-p1=p2
;;                             (p1 (m-* (rot-13) (rot-13-b13-00-1-witness p)))
;;                             (p2 p))
;;                  (:instance b3-f (p p))
;;                  (:instance b3 (p p))
;;                  (:instance rot-3-8-b-3-8-01-or-11=>1
;;                             (rot (rot-13))
;;                             (wit (rot-13-b13-00-1-witness p))
;;                             (p p)
;;                             (wit-wit (rot-13-inv*b3-f-witness (rot-13-b13-00-1-witness p))))
;;                  (:instance b3 (p (rot-13-inv*b3-f-witness (rot-13-b13-00-1-witness p))))
;;                  (:instance b3-f (p (rot-13-inv*b3-f-witness (rot-13-b13-00-1-witness p))))
;;                  )
;;            :in-theory nil
;;            )
;;           ("subgoal 3"
;;            :use ((:instance rot-13-b13-10 (p p))
;;                  (:instance rot-13-b13-10-1 (point p))
;;                  (:instance b13-10 (p (rot-13-b13-10-1-witness p)))
;;                  (:instance rot-13-inv*b3-f (point (rot-13-b13-10-1-witness p)))
;;                  (:instance b3-0-n-b3-f (p p))
;;                  (:instance rot*b3-0-set=>b3-0
;;                             (p (rot-13-b13-10-1-witness p))
;;                             (rot (rot-13)))
;;                  (:instance rot-13)
;;                  (:instance base-rotations (x (acl2-sqrt 2)))
;;                  (:instance b3-0 (p (m-* (rot-13) (rot-13-b13-10-1-witness p))))
;;                  (:instance b3-0 (p p))
;;                  (:instance cal-radius-p1=p2
;;                             (p1 (m-* (rot-13) (rot-13-b13-10-1-witness p)))
;;                             (p2 p))
;;                  (:instance b3-f (p p))
;;                  (:instance b3 (p p))
;;                  (:instance rot-3-8-b-3-8-01-or-11=>1
;;                             (rot (rot-13))
;;                             (wit (rot-13-b13-10-1-witness p))
;;                             (p p)
;;                             (wit-wit (rot-13-inv*b3-f-witness (rot-13-b13-10-1-witness p))))
;;                  (:instance b3 (p (rot-13-inv*b3-f-witness (rot-13-b13-10-1-witness p))))
;;                  (:instance b3-f (p (rot-13-inv*b3-f-witness (rot-13-b13-10-1-witness p))))
;;                  )
;;            :in-theory nil
;;            )
;;           ("subgoal 2"
;;            :use ((:instance rot-14-b14-00 (p p))
;;                  (:instance rot-14-b14-00-1 (point p))
;;                  (:instance b14-00 (p (rot-14-b14-00-1-witness p)))
;;                  (:instance rot-14-inv*b3-f (point (rot-14-b14-00-1-witness p)))
;;                  (:instance b3-0-n-b3-f (p p))
;;                  (:instance rot*b3-0-set=>b3-0
;;                             (p (rot-14-b14-00-1-witness p))
;;                             (rot (rot-14)))
;;                  (:instance rot-14)
;;                  (:instance base-rotations (x (acl2-sqrt 2)))
;;                  (:instance b3-0 (p (m-* (rot-14) (rot-14-b14-00-1-witness p))))
;;                  (:instance b3-0 (p p))
;;                  (:instance cal-radius-p1=p2
;;                             (p1 (m-* (rot-14) (rot-14-b14-00-1-witness p)))
;;                             (p2 p))
;;                  (:instance b3-f (p p))
;;                  (:instance b3 (p p))
;;                  (:instance rot-3-8-b-3-8-01-or-11=>1
;;                             (rot (rot-14))
;;                             (wit (rot-14-b14-00-1-witness p))
;;                             (p p)
;;                             (wit-wit (rot-14-inv*b3-f-witness (rot-14-b14-00-1-witness p))))
;;                  (:instance b3 (p (rot-14-inv*b3-f-witness (rot-14-b14-00-1-witness p))))
;;                  (:instance b3-f (p (rot-14-inv*b3-f-witness (rot-14-b14-00-1-witness p))))
;;                  )
;;            :in-theory nil
;;            )
;;           ("subgoal 1"
;;            :use ((:instance rot-14-b14-10 (p p))
;;                  (:instance rot-14-b14-10-1 (point p))
;;                  (:instance b14-10 (p (rot-14-b14-10-1-witness p)))
;;                  (:instance rot-14-inv*b3-f (point (rot-14-b14-10-1-witness p)))
;;                  (:instance b3-0-n-b3-f (p p))
;;                  (:instance rot*b3-0-set=>b3-0
;;                             (p (rot-14-b14-10-1-witness p))
;;                             (rot (rot-14)))
;;                  (:instance rot-14)
;;                  (:instance base-rotations (x (acl2-sqrt 2)))
;;                  (:instance b3-0 (p (m-* (rot-14) (rot-14-b14-10-1-witness p))))
;;                  (:instance b3-0 (p p))
;;                  (:instance cal-radius-p1=p2
;;                             (p1 (m-* (rot-14) (rot-14-b14-10-1-witness p)))
;;                             (p2 p))
;;                  (:instance b3-f (p p))
;;                  (:instance b3 (p p))
;;                  (:instance rot-3-8-b-3-8-01-or-11=>1
;;                             (rot (rot-14))
;;                             (wit (rot-14-b14-10-1-witness p))
;;                             (p p)
;;                             (wit-wit (rot-14-inv*b3-f-witness (rot-14-b14-10-1-witness p))))
;;                  (:instance b3 (p (rot-14-inv*b3-f-witness (rot-14-b14-10-1-witness p))))
;;                  (:instance b3-f (p (rot-14-inv*b3-f-witness (rot-14-b14-10-1-witness p))))
;;                  )
;;            :in-theory nil
;;            )
;;           ))

;; (defthmd b3-equiv-3
;;   (iff (b3 p)
;;        (or (rot-9-b9-00 p)
;;            (rot-9-b9-10 p)
;;            (rot-10-b10-00 p)
;;            (rot-10-b10-10 p)
;;            (rot-11-b11-00 p)
;;            (rot-11-b11-10 p)
;;            (rot-12-b12-00 p)
;;            (rot-12-b12-10 p)
;;            (rot-13-b13-00 p)
;;            (rot-13-b13-10 p)
;;            (rot-14-b14-00 p)
;;            (rot-14-b14-10 p)
;;            (rota-1-rot-9-b9-11 p)
;;            (rota-1-rot-9-b9-01 p)
;;            (rota-1-rot-10-b10-11 p)
;;            (rota-1-rot-10-b10-01 p)
;;            (rota-1-rot-11-b11-11 p)
;;            (rota-1-rot-11-b11-01 p)
;;            (rota-1-rot-12-b12-11 p)
;;            (rota-1-rot-12-b12-01 p)
;;            (rota-1-rot-13-b13-11 p)
;;            (rota-1-rot-13-b13-01 p)
;;            (rota-1-rot-14-b14-11 p)
;;            (rota-1-rot-14-b14-01 p)))
;;        :hints (("Goal"
;;                 :use ((:instance rot-9-14-b-9-14-01-or-11=>)
;;                       (:instance a9-a14-b3-0-n-b3-f=>)
;;                       (:instance rota-1-rot-9-14-b-9-14-01-or-11=>)
;;                       (:instance a9-a14-rot-a-inv-b3-0-nf=>)
;;                       (:instance b3-iff-b3-0-n-b3-f-or-rota-inv-b3-0-n-f)
;;                       )
;;                 :in-theory nil
;;                 )))
