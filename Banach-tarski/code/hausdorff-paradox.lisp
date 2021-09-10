(in-package "ACL2")

(include-book "supportive-theorems")
(include-book "rotations")

(defun point-in-r3 (x)
  (and (array2p :fake-name x)
       (equal (car (dimensions :fake-name x)) 3)
       (equal (cadr (dimensions :fake-name x)) 1)
       (realp (aref2 :fake-name x 0 0))
       (realp (aref2 :fake-name x 1 0))
       (realp (aref2 :fake-name x 2 0))))

(defthm m-*point1^t-point1
  (implies (point-in-r3 x)
           (equal (aref2 :fake-name (m-* (m-trans x) x) 0 0)
                  (+ (* (aref2 :fake-name x 0 0) (aref2 :fake-name x 0 0))
                     (* (aref2 :fake-name x 1 0) (aref2 :fake-name x 1 0))
                     (* (aref2 :fake-name x 2 0) (aref2 :fake-name x 2 0)))))
  :hints (("Goal"
           :use (:instance point-in-r3 (x x))
           :do-not-induct t
           )))

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthm m-*point-id=point
    (implies (point-in-r3 p1)
             (m-= (m-* (id-rotation) p1) p1))
    :hints (("Goal"
             :use (:instance point-in-r3 (x p1))
             :in-theory (e/d (m-* m-= alist2p dimensions header aref2) ())
             :do-not-induct t
             )))
  )

(encapsulate
  ()

  (local
   (defthm rotation*point-on-s2-1
     (implies (and (array2p :fake-name p1)
                   (array2p :fake-name p2)
                   (equal (car (dimensions :fake-name p1)) 1)
                   (equal (cadr (dimensions :fake-name p1)) 1)
                   (realp (aref2 :fake-name p1 0 0))
                   (realp (aref2 :fake-name p2 0 0))
                   (m-= p1 p2))
              (equal (aref2 :fake-name p1 0 0)
                     (aref2 :fake-name p2 0 0)))
     :hints (("Goal"
              :in-theory (enable m-= dimensions)
              ))))

  (defthm rotation*point-on-s2-2
    (implies (r3-matrixp m1)
             (m-= (m-* m1 (id-rotation)) m1))
    :hints (("Goal"
             :use ((:instance right-unity-of-m-1-for-m-* (m1 m1) (name :fake-name))
                   (:instance normalize-dimensions-name (name '$arg) (l m1))
                   (:instance array2p-alist2p-fname (l m1)))
             :in-theory (e/d (header dimensions default m-*) ())
             )))

  (local
   (defthm rotation*point-on-s2-3
     (implies (and (array2p :fake-name a)
                   (array2p :fake-name b)
                   (array2p :fake-name c)
                   (array2p :fake-name x)
                   (m-= b x))
              (equal (m-* a b c) (m-* a x c)))))

  (local
   (defthm rotation*point-on-s2-4
     (implies (and (point-in-r3 p1)
                   (r3-rotationp rot))
              (equal (m-* (m-trans (m-* rot p1)) (m-* rot p1))
                     (m-* (m-trans p1) (m-trans rot) rot p1)))
     :hints (("Goal"
              :use ((:instance m-trans-m-*=m-*-m-trans (m1 rot) (m2 p1) (name :fake-name)))
              :in-theory (e/d () (rotation*point-on-s2-3))))))

  (local
   (defthm rotation*point-on-s2-5
     (implies (and (array2p :fake-name m1)
                   (array2p :fake-name m2)
                   (array2p :fake-name m3)
                   (array2p :fake-name m4))
              (equal (m-* m1 m2 m3 m4) (m-* m1 (m-* m2 m3) m4)))
     :hints (("Goal"
              :in-theory (e/d () (rotation*point-on-s2-3))
              ))))

  (local
   (defthm rotation*point-on-s2-6
     (implies (point-in-r3 p1)
              (ARRAY2P :FAKE-NAME (M-TRANS P1)))))

  (local
   (defthm rotation*point-on-s2-7
     (implies (and (point-in-r3 p1)
                   (r3-rotationp rot))
              (m-= (m-* (m-trans (m-* rot p1)) (m-* rot p1))
                   (m-* (m-trans p1) p1)))
     :hints (("Goal"
              :use ((:instance rotation*point-on-s2-4 (p1 p1) (rot rot))
                    (:instance rotation*point-on-s2-5 (m1 (m-trans p1)) (m2 (m-trans rot)) (m3 rot) (m4 p1))
                    (:instance r3-rotationp (m rot))
                    (:instance m-*-m-inverse-m (m rot))
                    (:instance rotation*point-on-s2-3 (a (m-trans p1)) (b (m-* (r3-m-inverse rot) rot))
                               (c p1) (x (id-rotation)))
                    (:instance associativity-of-m-*-2 (m1 (m-trans p1)) (m2 (id-rotation))
                               (m3 p1))
                    (:instance m-*point-id=point (p1 p1))
                    (:instance rotation*point-on-s2-6 (p1 p1))
                    (:instance array2p-alist2p-fname (l rot)))
              :in-theory (disable m-= m-* aref2 array2p ASSOCIATIVITY-OF-M-*-2 M-*-M-INVERSE-M M-*POINT-ID=POINT
                                  ROTATION*POINT-ON-S2-3 ROTATION*POINT-ON-S2-4 ROTATION*POINT-ON-S2-5 ROTATION*POINT-ON-S2-6)
              ))))

  (defthm rotation*point-on-s2
    (implies (and (point-in-r3 p1)
                  (r3-rotationp rot)
                  (equal (m-* rot p1) p2))
             (equal (+ (* (aref2 :fake-name p1 0 0) (aref2 :fake-name p1 0 0))
                       (* (aref2 :fake-name p1 1 0) (aref2 :fake-name p1 1 0))
                       (* (aref2 :fake-name p1 2 0) (aref2 :fake-name p1 2 0)))
                    (+ (* (aref2 :fake-name p2 0 0) (aref2 :fake-name p2 0 0))
                       (* (aref2 :fake-name p2 1 0) (aref2 :fake-name p2 1 0))
                       (* (aref2 :fake-name p2 2 0) (aref2 :fake-name p2 2 0)))))
    :hints (("Goal"
             :use ((:instance rotation*point-on-S2-7 (p1 p1) (rot rot))
                   (:instance m-*point1^t-point1 (x (m-* rot p1)))
                   (:instance rotation*point-on-S2-1 (p1 (m-* (m-trans (m-* rot p1)) (m-* rot p1)))
                              (p2 (m-* (m-trans p1) p1)))
                   (:instance m-*point1^t-point1 (x p1)))
             :in-theory (e/d () (m-* m-= m-trans rotation*point-on-s2-5 rotation*point-on-s2-4 rotation*point-on-s2-3 rotation*point-on-s2-2))
             )))
  )

(defun s2-def-p (point)
  (and (point-in-r3 point)
       (equal (+ (* (aref2 :fake-name point 0 0) (aref2 :fake-name point 0 0))
                 (* (aref2 :fake-name point 1 0) (aref2 :fake-name point 1 0))
                 (* (aref2 :fake-name point 2 0) (aref2 :fake-name point 2 0)))
              1)))

(defun-sk word-exists (point)
  (exists w
          (and (reducedwordp w)
               w
               (m-= (m-* (rotation w (acl2-sqrt 2)) point)
                    point))))

(defun d-p (point)
  (and (s2-def-p point)
       (word-exists point)))


(defun s2-d-p (point)
  (and (s2-def-p point)
       (not (d-p point))))

(defthmd s2-def-p-equiv
  (equal (s2-def-p p)
         (or (d-p p)
             (s2-d-p p))))

(defthm rot*p-on-s2
  (implies (and (s2-def-p p)
                (r3-rotationp rot))
           (s2-def-p (m-* rot p)))
  :hints (("Goal"
           :use (:instance rotation*point-on-s2 (p1 p) (p2 (m-* rot p)))
           )))

(defthm d-p-implies
  (implies (d-p p)
           (let ((w (word-exists-witness p)))
             (and (s2-def-p p)
                  (reducedwordp w)
                  (not (equal w nil))
                  (m-= (m-* (rotation w (acl2-sqrt 2)) p)
                       p)))))

(defthmd d-p-implies-1
  (implies (and (s2-def-p point)
                (word-exists point))
           (d-p point)))

(defthm point-on-d=>rot*p-on-d
  (implies (and (reducedwordp w)
                (d-p (m-* (rotation w (acl2-sqrt 2)) p)))
           (let ((w1 (word-exists-witness (m-* (rotation w (acl2-sqrt 2)) p))))
             (and (reducedwordp w1)
                  (not (equal w1 nil))
                  (m-= (m-* (rotation w1 (acl2-sqrt 2))
                            (m-* (rotation w (acl2-sqrt 2)) p))
                       (m-* (rotation w (acl2-sqrt 2)) p)))))
  :hints (("Goal"
           :use ((:instance d-p-implies
                            (p (m-* (rotation w (acl2-sqrt 2)) p))))
           :in-theory nil
           )))

(defthm p-in-d-=>rot*p-in-d-lemma-1
  (implies (and (point-in-r3 p)
                (m-= (m-* m1 m2 p) (m-* m2 p)))
           (m-= (m-* m4 m1 m2 p) (m-* m4 m2 p))))

(defthmd p-in-d-=>rot*p-in-d-lemma-2
  (implies (and (reducedwordp w)
                (reducedwordp w1))
           (reducedwordp (compose (word-inverse w) (append w1 w))))
  :hints (("Goal"
           :use ((:instance compose-assoc-lemma-export
                            (x (word-inverse w))
                            (y (append w1 w)))
                 (:instance reducedwordp=>weak-wordp (x w))
                 (:instance reducedwordp=>weak-wordp (x w1))
                 (:instance reducedwordp=>weak-wordp (x (word-inverse w)))
                 (:instance reducedwordp-word-inverse (x w))
                 (:instance closure-prop (x (word-inverse w)) (y (word-fix (append w1 w))))
                 (:instance closure-prop (x w1) (y w))
                 (:instance compose (x (word-inverse w)) (y (append w w1)))
                 (:instance compose (x w1) (y w))))))

(defthmd p-in-d-=>rot*p-in-d-lemma-3
  (implies (and (reducedwordp w)
                (reducedwordp w1))
           (m-= (rotation (compose (word-inverse w) (append w1 w)) (acl2-sqrt 2))
                (m-* (rotation (word-inverse w) (acl2-sqrt 2))
                     (rotation w1 (acl2-sqrt 2))
                     (rotation w (acl2-sqrt 2)))))
  :hints (("Goal"
           :use ((:instance compose (x (word-inverse w)) (y (append w1 w)))
                 (:instance compose (x w1) (y w))
                 (:instance reducedwordp=>weak-wordp (x (word-inverse w)))
                 (:instance compose-assoc-lemma-export
                            (x (word-inverse w))
                            (y (append w1 w)))
                 (:instance rot-a*rot-b-= (a (word-inverse w)) (b (word-fix (append w1 w))) (x (acl2-sqrt 2)))
                 (:instance rot-a*rot-b-= (a w1) (b w) (x (acl2-sqrt 2)))
                 (:instance closure-prop (x w1) (y w))
                 (:instance closure-lemma (x w1) (y w))
                 (:instance compose (x w1) (y w))
                 (:instance reducedwordp-word-inverse (x w)))
           :do-not-induct t
           )))

(defthmd p-in-d-=>rot*p-in-d-lemma-4-1
  (implies (m-= m1 (m-* m2 m3 m4))
           (m-= (m-* m5 m1) (m-* (m-* m5 m2) m3 m4))))

(defthmd p-in-d-=>rot*p-in-d-lemma-4-2
  (implies (r3-matrixp m1)
           (m-= (m-* (id-rotation) m1) m1))
  :hints (("Goal"
           :use ((:instance left-unity-of-m-1-for-m-* (m1 m1) (name :fake-name))
                 (:instance normalize-dimensions-name (name '$arg) (l m1))
                 (:instance array2p-alist2p-fname (l m1)))
           :in-theory (e/d (header dimensions default m-*) ())
           )))

(defthmd p-in-d-=>rot*p-in-d-lemma-4-3
  (implies (m-= m1 (m-* m2 m3))
           (m-= (m-* m1 m4) (m-* m2 m3 m4))))

(defthmd p-in-d-=>rot*p-in-d-lemma-4-4
  (implies (and (m-= (m-* m1 (id-rotation)) m5)
                (r3-matrixp m1)
                (r3-matrixp m3)
                (r3-matrixp m4)
                (m-= m2 (id-rotation))
                (m-= (m-* m1 (id-rotation)) (m-* m2 m3 m4)))
           (m-= m5 (m-* m3 m4)))
  :hints (("Goal"
           :use ((:instance p-in-d-=>rot*p-in-d-lemma-4-2 (m1 m3))
                 (:instance p-in-d-=>rot*p-in-d-lemma-4-2 (m1 m4)))
           :in-theory (e/d (m-=) (m-* id-rotation))
           )))

(defthmd p-in-d-=>rot*p-in-d-lemma-4-5
  (m-= (m-* m1 m2 m3) (m-* m1 (m-* m2 m3))))

(defthmd p-in-d-=>rot*p-in-d-lemma-4-6
  (implies (and (r3-matrixp m1)
                (m-= m2 (id-rotation))
                (m-= m2 (m-* m1 m2)))
           (m-= m1 (id-rotation)))
  :hints (("Goal"
           :in-theory (enable m-=)
           )))

(encapsulate
  ()

  (local (in-theory nil))
  (local (include-book "supportive-theorems"))

  (defthmd p-in-d-=>rot*p-in-d-lemma-4
    (implies (and (reducedwordp w)
                  (reducedwordp w1)
                  (m-= (rotation (compose (word-inverse w) (append w1 w)) (acl2-sqrt 2))
                       (m-* (rotation (word-inverse w) (acl2-sqrt 2))
                            (rotation w1 (acl2-sqrt 2))
                            (rotation w (acl2-sqrt 2))))
                  (equal (compose (word-inverse w) (append w1 w)) nil))
             (m-= (rotation w1 (acl2-sqrt 2)) (id-rotation)))
    :hints (("Goal"
             :use ((:instance p-in-d-=>rot*p-in-d-lemma-4-1
                              (m1 (id-rotation))
                              (m2 (rotation (word-inverse w) (acl2-sqrt 2)))
                              (m3 (rotation w1 (acl2-sqrt 2)))
                              (m4 (rotation w (acl2-sqrt 2)))
                              (m5 (rotation w (acl2-sqrt 2))))
                   (:instance rotation*point-on-s2-2 (m1 (rotation w (acl2-sqrt 2))))
                   (:instance rotation-is-r3-rotationp (x (acl2-sqrt 2)) (w w))
                   (:instance rotation-is-r3-rotationp (x (acl2-sqrt 2)) (w w1))
                   (:instance rot-a*rot-b-= (a w) (b (word-inverse w)) (x (acl2-sqrt 2)))
                   (:instance reduced-inverse (x w))
                   (:instance p-in-d-=>rot*p-in-d-lemma-4-3
                              (m1 (rotation w (acl2-sqrt 2)))
                              (m2 (rotation w1 (acl2-sqrt 2)))
                              (m3 (rotation w (acl2-sqrt 2)))
                              (m4 (rotation (word-inverse w) (acl2-sqrt 2))))
                   (:instance p-in-d-=>rot*p-in-d-lemma-4-2 (m1 (rotation w1 (acl2-sqrt 2))))
                   (:instance rotation*point-on-s2-2 (m1 (rotation w1
                                                                   (acl2-sqrt 2))))
                   (:instance rotation*point-on-s2-2 (m1 (rotation w (acl2-sqrt 2))))
                   (:instance r3-rotationp (m (ROTATION W (ACL2-SQRT 2))))
                   (:instance r3-rotationp (m (ROTATION W1 (ACL2-SQRT 2))))
                   (:instance reducedwordp-word-inverse (x w))
                   (:instance rotation (w nil) (x (acl2-sqrt 2)))
                   (:instance r3-matrixp (m (ROTATION W (ACL2-SQRT 2))))
                   (:instance r3-matrixp (m (ROTATION W1 (ACL2-SQRT 2))))
                   (:instance p-in-d-=>rot*p-in-d-lemma-4-4
                              (m5 (ROTATION W (ACL2-SQRT 2)))
                              (m1 (ROTATION W (ACL2-SQRT 2)))
                              (m2 (M-* (ROTATION W (ACL2-SQRT 2))
                                       (ROTATION (WORD-INVERSE W)
                                                 (ACL2-SQRT 2))))
                              (m3 (ROTATION W1 (ACL2-SQRT 2)))
                              (m4 (ROTATION W (ACL2-SQRT 2))))
                   (:instance p-in-d-=>rot*p-in-d-lemma-4-5
                              (m1 (ROTATION W1 (ACL2-SQRT 2)))
                              (m2 (ROTATION W (ACL2-SQRT 2)))
                              (m3 (ROTATION (word-inverse w) (ACL2-SQRT 2))))
                   (:instance p-in-d-=>rot*p-in-d-lemma-4-6
                              (m1 (ROTATION W1 (ACL2-SQRT 2)))
                              (m2 (m-* (ROTATION W (ACL2-SQRT 2)) (ROTATION (word-inverse w) (ACL2-SQRT 2)))))
                   )))))

(defthmd p-in-d-=>rot*p-in-d-lemma-6
  (implies (and (reducedwordp w)
                w)
           (and (>= (len w) 0)
                (not (<= (len w) 0)))))

(defthmd p-in-d-=>rot*p-in-d-lemma-7
  (implies (m-= (m-* m1 m2 m3) (m-* m2 m3))
           (m-= (m-* (m-* m4 m1 m2) m3) (m-* (m-* m4 m2) m3))))

(defthmd p-in-d-=>rot*p-in-d-lemma-8
  (implies (and (m-= m1 m2)
                (m-= m3 m4)
                (m-= (m-* m4 m5) m6)
                (m-= (m-* m1 m5) (m-* m3 m5)))
           (m-= (m-* m2 m5) m6)))

(defthmd p-in-d-=>rot*p-in-d-lemma
  (implies (and (reducedwordp w)
                (s2-def-p point)
                (d-p (m-* (rotation w (acl2-sqrt 2)) point)))
           (d-p point))
  :hints (("Goal"
           :use ((:instance word-exists-suff
                            (w (compose (word-inverse w)
                                        (append (word-exists-witness (m-* (rotation w (acl2-sqrt 2)) point)) w)))
                            (point point))
                 (:instance p-in-d-=>rot*p-in-d-lemma-2
                            (w w)
                            (w1 (word-exists-witness (m-* (rotation w (acl2-sqrt 2)) point))))
                 (:instance p-in-d-=>rot*p-in-d-lemma-4 (w w)
                            (w1 (word-exists-witness (m-* (rotation w (acl2-sqrt 2)) point))))
                 (:instance rotaion-not=id
                            (w (word-exists-witness (m-* (rotation w (acl2-sqrt 2)) point)))
                            (x (acl2-sqrt 2)))
                 (:instance point-on-d=>rot*p-on-d (w w) (p point))
                 (:instance p-in-d-=>rot*p-in-d-lemma-6
                            (w (word-exists-witness (m-* (rotation w (acl2-sqrt 2)) point))))
                 (:instance p-in-d-=>rot*p-in-d-lemma-3
                            (w w)
                            (w1 (word-exists-witness (m-* (rotation w (acl2-sqrt 2)) point))))
                 (:instance d-p-implies-1)
                 (:instance s2-def-p)
                 (:instance p-in-d-=>rot*p-in-d-lemma-7
                            (m1 (ROTATION (WORD-EXISTS-WITNESS (M-* (ROTATION W (ACL2-SQRT 2)) POINT))
                                          (ACL2-SQRT 2)))
                            (m2 (ROTATION W (ACL2-SQRT 2)))
                            (m3 point)
                            (m4 (ROTATION (word-inverse W) (ACL2-SQRT 2))))
                 (:instance p-in-d-=>rot*p-in-d-lemma-8
                            (m1 (M-*
                                 (ROTATION (WORD-INVERSE W)
                                           (ACL2-SQRT 2))
                                 (ROTATION (WORD-EXISTS-WITNESS (M-* (ROTATION W (ACL2-SQRT 2)) POINT))
                                           (ACL2-SQRT 2))
                                 (ROTATION W (ACL2-SQRT 2))))
                            (m2 (ROTATION
                                 (COMPOSE
                                  (WORD-INVERSE W)
                                  (APPEND (WORD-EXISTS-WITNESS (M-* (ROTATION W (ACL2-SQRT 2)) POINT))
                                          W))
                                 (ACL2-SQRT 2)))
                            (m3 (M-* (ROTATION (WORD-INVERSE W)
                                               (ACL2-SQRT 2))
                                     (ROTATION W (ACL2-SQRT 2))))
                            (m4 (id-rotation))
                            (m6 point)
                            (m5 point))
                 (:instance rot-a*rot-b-= (a (word-inverse w)) (b w) (x (acl2-sqrt 2)))
                 (:instance reducedwordp-word-inverse (x w))
                 (:instance reducedwordp=>weak-wordp (x w))
                 (:instance reducedwordp=>weak-wordp (x (word-inverse w)))
                 (:instance inv-inv-x=x (x w))
                 (:instance reduced-inverse (x (word-inverse w)))
                 (:instance rotation (w nil) (x (acl2-sqrt 2)))
                 (:instance m-*point-id=point (p1 point))
                 )
           :in-theory nil
           )))

(defthmd s2-d-p=>p
  (implies (and (s2-d-p point)
                (reducedwordp w))
           (s2-d-p (m-* (rotation w (acl2-sqrt 2)) point)))
  :hints (("Goal"
           :use ((:instance p-in-d-=>rot*p-in-d-lemma (w w) (point point))
                 (:instance s2-d-p (point point))
                 (:instance s2-d-p (point (M-* (ROTATION W (ACL2-SQRT 2)) POINT)))
                 (:instance rot*p-on-s2 (p point) (rot (rotation w (acl2-sqrt 2))))
                 (:instance rotation-is-r3-rotationp (w w) (x (acl2-sqrt 2)))
                 (:instance s2-def-p-equiv (p point)))
           :in-theory nil
           )))

(defthmd s2-def-p-p=>p1
  (implies (and (s2-def-p p)
                (m-= p p1)
                (point-in-r3 p1))
           (s2-def-p p1))
  :hints (("Goal"
           :in-theory (enable m-=)
           )))

(defthmd d-p-p=>d-p-p1-lemma
  (implies (and (m-= (m-* m1 m2) m2)
                (m-= m2 m3))
           (m-= (m-* m1 m3) m3)))

(defthmd d-p-p=>d-p-p1
  (implies (and (d-p p)
                (s2-def-p p1)
                (m-= p p1))
           (d-p p1))
  :hints (("Goal"
           :use ((:instance d-p (point p1))
                 (:instance word-exists-suff (w (word-exists-witness p)) (point p1))
                 (:instance d-p-p=>d-p-p1-lemma (m1 (rotation (word-exists-witness p) (acl2-sqrt 2)))
                            (m2 p) (m3 p1)))

           :in-theory (disable acl2-sqrt)
           )))

(defthmd d-p-p=>d-p-p1-1
  (implies (and (d-p p)
                (s2-def-p p1)
                (m-= p1 p))
           (d-p p1))
  :hints (("Goal"
           :use ((:instance d-p-p=>d-p-p1 (p p) (p1 p1)))
           )))

(defun-sk orbit-point-p-q (o-point point)
  (exists w
          (and (reducedwordp w)
               (m-= (m-* (rotation w (acl2-sqrt 2)) point) o-point))))

(defchoose choice-set-s2-d-p (c-point) (p)
  (orbit-point-p-q c-point p))

(defun-sk diff-s2-d-p-q (p)
  (exists (p1 w)
          (and (reducedwordp w)
               (s2-def-p p1)
               (m-= (m-* (rotation w (acl2-sqrt 2)) (choice-set-s2-d-p p1)) p))))

(defun diff-s2-d-p (p)
  (and (point-in-r3 p)
       (diff-s2-d-p-q p)))

;; ---

;; (defthmd diff-s2-d-p-equiv
;;   (implies (and (point-in-r3 p)
;;                 (diff-s2-d-p-q p))
;;            (diff-s2-d-p p)))

;; (defun diff-s2-d-p-w-nil (p)
;;   (and (point-in-r3 p)
;;        (m-= (m-* (rotation nil (acl2-sqrt 2)) (choice-set-s2-d-p p)) p)))

;; (defun-sk diff-s2-d-p-w-a-q (p)
;;   (exists w
;;           (and (a-wordp w)
;;                (m-= (m-* (rotation w (acl2-sqrt 2)) (choice-set-s2-d-p p)) p))))

;; (defun diff-s2-d-p-w-a (p)
;;   (and (point-in-r3 p)
;;        (diff-s2-d-p-w-a-q p)))

;; (defun-sk diff-s2-d-p-w-a-inv-q (p)
;;   (exists w
;;           (and (a-inv-wordp w)
;;                (m-= (m-* (rotation w (acl2-sqrt 2)) (choice-set-s2-d-p p)) p))))

;; (defun diff-s2-d-p-w-a-inv (p)
;;   (and (point-in-r3 p)
;;        (diff-s2-d-p-w-a-inv-q p)))

;; (defun-sk diff-s2-d-p-w-b-q (p)
;;   (exists w
;;           (and (b-wordp w)
;;                (m-= (m-* (rotation w (acl2-sqrt 2)) (choice-set-s2-d-p p)) p))))

;; (defun diff-s2-d-p-w-b (p)
;;   (and (point-in-r3 p)
;;        (diff-s2-d-p-w-b-q p)))

;; (defun-sk diff-s2-d-p-w-b-inv-q (p)
;;   (exists w
;;           (and (b-inv-wordp w)
;;                (m-= (m-* (rotation w (acl2-sqrt 2)) (choice-set-s2-d-p p)) p))))

;; (defun diff-s2-d-p-w-b-inv (p)
;;   (and (point-in-r3 p)
;;        (diff-s2-d-p-w-b-inv-q p)))

;; (defthmd diff-s2-d-p-equiv-1
;;   (implies (orbit-point-p o-point point)
;;            (s2-d-p point)))

;; (defthmd diff-s2-d-p-equiv-2
;;   (implies (diff-s2-d-p p)
;;            (s2-d-p p))
;;   :hints (("Goal"
;;            :in-theory (disable acl2-sqrt reducedwordp)
;;            )))

;; ---

;; (defun-sk choice-set-s2-d-p (c-point)
;;   (exists point
;;           (and (s2-d-p point)
;;                (orbit-point-p c-point point))))

;; (defun-sk diff-s2-d-p-q (p)
;;   (exists (c-point w)
;;           (and (choice-set-s2-d-p c-point)
;;                (reducedwordp w)
;;                (m-= (m-* (rotation w (acl2-sqrt 2)) c-point) p))))

;; (defun diff-s2-d-p (p)
;;   (and (point-in-r3 p)
;;        (diff-s2-d-p-q p)))

;; (defthmd diff-s2-d-p-equiv
;;   (implies (and (point-in-r3 p)
;;                 (diff-s2-d-p-q p))
;;            (diff-s2-d-p p)))

;; (defun-sk diff-s2-d-p-w-nil-q (p)
;;   (exists (c-point w)
;;           (and (choice-set-s2-d-p c-point)
;;                (equal w nil)
;;                (m-= (m-* (rotation w (acl2-sqrt 2)) c-point) p))))

;; (defun diff-s2-d-p-w-nil (p)
;;   (and (point-in-r3 p)
;;        (diff-s2-d-p-w-nil-q p)))

;; (defun-sk diff-s2-d-p-w-a-q (p)
;;   (exists (c-point w)
;;           (and (choice-set-s2-d-p c-point)
;;                (a-wordp w)
;;                (m-= (m-* (rotation w (acl2-sqrt 2)) c-point) p))))

;; (defun diff-s2-d-p-w-a (p)
;;   (and (point-in-r3 p)
;;        (diff-s2-d-p-w-a-q p)))

;; (defun-sk diff-s2-d-p-w-a-inv-q (p)
;;   (exists (c-point w)
;;           (and (choice-set-s2-d-p c-point)
;;                (a-inv-wordp w)
;;                (m-= (m-* (rotation w (acl2-sqrt 2)) c-point) p))))

;; (defun diff-s2-d-p-w-a-inv (p)
;;   (and (point-in-r3 p)
;;        (diff-s2-d-p-w-a-inv-q p)))

;; (defun-sk diff-s2-d-p-w-b-q (p)
;;   (exists (c-point w)
;;           (and (choice-set-s2-d-p c-point)
;;                (b-wordp w)
;;                (m-= (m-* (rotation w (acl2-sqrt 2)) c-point) p))))

;; (defun diff-s2-d-p-w-b (p)
;;   (and (point-in-r3 p)
;;        (diff-s2-d-p-w-b-q p)))

;; (defun-sk diff-s2-d-p-w-b-inv-q (p)
;;   (exists (c-point w)
;;           (and (choice-set-s2-d-p c-point)
;;                (b-inv-wordp w)
;;                (m-= (m-* (rotation w (acl2-sqrt 2)) c-point) p))))

;; (defun diff-s2-d-p-w-b-inv (p)
;;   (and (point-in-r3 p)
;;        (diff-s2-d-p-w-b-inv-q p)))

;; (defthmd diff-s2-d-p-equiv-1
;;   (implies (DIFF-S2-D-P p)
;;            (and (point-in-r3 p)
;;                 (choice-set-s2-d-p (MV-NTH 0 (DIFF-S2-D-P-q-WITNESS P)))
;;                 (reducedwordp (MV-NTH 1 (DIFF-S2-D-P-q-WITNESS P)))
;;                 (M-= (M-* (ROTATION (MV-NTH 1 (DIFF-S2-D-P-q-WITNESS P)) (ACL2-SQRT 2))
;;                           (MV-NTH 0 (DIFF-S2-D-P-q-WITNESS P)))
;;                      P))))

;; (defthmd diff-s2-d-p-equiv-lemma1
;;   (implies (diff-s2-d-p p)
;;            (or (diff-s2-d-p-w-nil p)
;;                (diff-s2-d-p-w-a p)
;;                (diff-s2-d-p-w-a-inv p)
;;                (diff-s2-d-p-w-b p)
;;                (diff-s2-d-p-w-b-inv p)))
;;   :hints (("Goal"
;;            :use ((:instance DIFF-S2-D-P-w-nil-q-suff (c-point (MV-NTH 0 (DIFF-S2-D-P-q-WITNESS P)))
;;                             (w (MV-NTH 1 (DIFF-S2-D-P-q-WITNESS P))))
;;                  (:instance diff-s2-d-p-equiv-1 (p p))
;;                  (:instance DIFF-S2-D-P-w-a-q-suff (c-point (MV-NTH 0 (DIFF-S2-D-P-q-WITNESS P)))
;;                             (w (MV-NTH 1 (DIFF-S2-D-P-q-WITNESS P))))
;;                  (:instance DIFF-S2-D-P-w-a-inv-q-suff (c-point (MV-NTH 0 (DIFF-S2-D-P-q-WITNESS P)))
;;                             (w (MV-NTH 1 (DIFF-S2-D-P-q-WITNESS P))))
;;                  (:instance DIFF-S2-D-P-w-b-q-suff (c-point (MV-NTH 0 (DIFF-S2-D-P-q-WITNESS P)))
;;                             (w (MV-NTH 1 (DIFF-S2-D-P-q-WITNESS P))))
;;                  (:instance DIFF-S2-D-P-w-b-inv-q-suff (c-point (MV-NTH 0 (DIFF-S2-D-P-q-WITNESS P)))
;;                             (w (MV-NTH 1 (DIFF-S2-D-P-q-WITNESS P))))
;;                  )
;;            :in-theory (e/d (reducedwordp) (choice-set-s2-d-p rotation acl2-sqrt))
;;            )))

;; (defthmd diff-s2-d-p-equiv-2
;;   (implies (DIFF-S2-D-P-w-nil p)
;;            (and (point-in-r3 p)
;;                 (choice-set-s2-d-p (MV-NTH 0 (DIFF-S2-D-P-w-nil-q-WITNESS P)))
;;                 (reducedwordp (MV-NTH 1 (DIFF-S2-D-P-w-nil-q-WITNESS P)))
;;                 (M-= (M-* (ROTATION (MV-NTH 1 (DIFF-S2-D-P-w-nil-q-WITNESS P)) (ACL2-SQRT 2))
;;                           (MV-NTH 0 (DIFF-S2-D-P-w-nil-q-WITNESS P)))
;;                      P))))

;; (defthmd diff-s2-d-p-equiv-3
;;   (implies (DIFF-S2-D-P-w-a p)
;;            (and (point-in-r3 p)
;;                 (choice-set-s2-d-p (MV-NTH 0 (DIFF-S2-D-P-w-a-q-WITNESS P)))
;;                 (reducedwordp (MV-NTH 1 (DIFF-S2-D-P-w-a-q-WITNESS P)))
;;                 (M-= (M-* (ROTATION (MV-NTH 1 (DIFF-S2-D-P-w-a-q-WITNESS P)) (ACL2-SQRT 2))
;;                           (MV-NTH 0 (DIFF-S2-D-P-w-a-q-WITNESS P)))
;;                      P))))

;; (defthmd diff-s2-d-p-equiv-4
;;   (implies (DIFF-S2-D-P-w-a-inv p)
;;            (and (point-in-r3 p)
;;                 (choice-set-s2-d-p (MV-NTH 0 (DIFF-S2-D-P-w-a-inv-q-WITNESS P)))
;;                 (reducedwordp (MV-NTH 1 (DIFF-S2-D-P-w-a-inv-q-WITNESS P)))
;;                 (M-= (M-* (ROTATION (MV-NTH 1 (DIFF-S2-D-P-w-a-inv-q-WITNESS P)) (ACL2-SQRT 2))
;;                           (MV-NTH 0 (DIFF-S2-D-P-w-a-inv-q-WITNESS P)))
;;                      P))))

;; (defthmd diff-s2-d-p-equiv-5
;;   (implies (DIFF-S2-D-P-w-b p)
;;            (and (point-in-r3 p)
;;                 (choice-set-s2-d-p (MV-NTH 0 (DIFF-S2-D-P-w-b-q-WITNESS P)))
;;                 (reducedwordp (MV-NTH 1 (DIFF-S2-D-P-w-b-q-WITNESS P)))
;;                 (M-= (M-* (ROTATION (MV-NTH 1 (DIFF-S2-D-P-w-b-q-WITNESS P)) (ACL2-SQRT 2))
;;                           (MV-NTH 0 (DIFF-S2-D-P-w-b-q-WITNESS P)))
;;                      P))))

;; (defthmd diff-s2-d-p-equiv-6
;;   (implies (DIFF-S2-D-P-w-b-inv p)
;;            (and (point-in-r3 p)
;;                 (choice-set-s2-d-p (MV-NTH 0 (DIFF-S2-D-P-w-b-inv-q-WITNESS P)))
;;                 (reducedwordp (MV-NTH 1 (DIFF-S2-D-P-w-b-inv-q-WITNESS P)))
;;                 (M-= (M-* (ROTATION (MV-NTH 1 (DIFF-S2-D-P-w-b-inv-q-WITNESS P)) (ACL2-SQRT 2))
;;                           (MV-NTH 0 (DIFF-S2-D-P-w-b-inv-q-WITNESS P)))
;;                      P))))

;; (defthmd diff-s2-d-p-equiv-lemma2
;;   (implies (or (diff-s2-d-p-w-nil p)
;;                (diff-s2-d-p-w-a p)
;;                (diff-s2-d-p-w-a-inv p)
;;                (diff-s2-d-p-w-b p)
;;                (diff-s2-d-p-w-b-inv p))
;;            (diff-s2-d-p p))
;;   :hints (("Goal"
;;            :cases ((diff-s2-d-p-w-nil p)
;;                    (diff-s2-d-p-w-a p)
;;                    (diff-s2-d-p-w-a-inv p)
;;                    (diff-s2-d-p-w-b p)
;;                    (diff-s2-d-p-w-b-inv p))
;;            :use ((:instance diff-s2-d-p-equiv-2)
;;                  (:instance diff-s2-d-p-equiv (p p))
;;                  (:instance diff-s2-d-p-equiv-3)
;;                  (:instance diff-s2-d-p-equiv-4)
;;                  (:instance diff-s2-d-p-equiv-5)
;;                  (:instance diff-s2-d-p-equiv-6))
;;            )
;;           ("Subgoal 5"
;;            :use ((:instance DIFF-S2-D-P-q-suff (c-point (MV-NTH 0 (DIFF-S2-D-P-w-nil-q-WITNESS P)))
;;                             (w (MV-NTH 1 (DIFF-S2-D-P-w-nil-q-WITNESS P)))))
;;            )
;;           ("Subgoal 4"
;;            :use ((:instance DIFF-S2-D-P-q-suff (c-point (MV-NTH 0 (DIFF-S2-D-P-w-a-q-WITNESS P)))
;;                             (w (MV-NTH 1 (DIFF-S2-D-P-w-a-q-WITNESS P)))))
;;            )
;;           ("Subgoal 3"
;;            :use ((:instance DIFF-S2-D-P-q-suff (c-point (MV-NTH 0 (DIFF-S2-D-P-w-a-inv-q-WITNESS P)))
;;                             (w (MV-NTH 1 (DIFF-S2-D-P-w-a-inv-q-WITNESS P)))))
;;            )
;;           ("Subgoal 2"
;;            :use ((:instance DIFF-S2-D-P-q-suff (c-point (MV-NTH 0 (DIFF-S2-D-P-w-b-q-WITNESS P)))
;;                             (w (MV-NTH 1 (DIFF-S2-D-P-w-b-q-WITNESS P)))))
;;            )
;;           ("Subgoal 1"
;;            :use ((:instance DIFF-S2-D-P-q-suff (c-point (MV-NTH 0 (DIFF-S2-D-P-w-b-inv-q-WITNESS P)))
;;                             (w (MV-NTH 1 (DIFF-S2-D-P-w-b-inv-q-WITNESS P)))))
;;            )))

;; (defthmd diff-s2-d-p-=
;;   (iff (diff-s2-d-p p)
;;        (or (diff-s2-d-p-w-nil p)
;;            (diff-s2-d-p-w-a p)
;;            (diff-s2-d-p-w-a-inv p)
;;            (diff-s2-d-p-w-b p)
;;            (diff-s2-d-p-w-b-inv p)))
;;   :hints (("Goal"
;;            :use ((:instance diff-s2-d-p-equiv-lemma1 (p p))
;;                  (:instance diff-s2-d-p-equiv-lemma2 (p p)))
;;            )))

;; (defthmd s2-def-p-p=>p1
;;   (implies (and (s2-def-p p)
;;                 (m-= p p1)
;;                 (point-in-r3 p1))
;;            (s2-def-p p1))
;;   :hints (("Goal"
;;            :in-theory (enable m-=)
;;            )))

;; ;; ---

;; ;; ;; ---

;; ;; ;; (defthmd disjoint-1-lemma1
;; ;; ;;   (IMPLIES (AND (CHOICE-SET-S2-D-P C-POINT)
;; ;; ;;                 (a-wordp w)
;; ;; ;;                 (not (M-= (M-* (ROTATION W (ACL2-SQRT 2)) C-POINT)
;; ;; ;;                           P)))
;; ;; ;;            (not (DIFF-S2-D-P-W-A P)))
;; ;; ;;   :hints (("Goal"
;; ;; ;;            :use (:instance DIFF-S2-D-P-W-A-SUFF (c-point c-point) (w w))
;; ;; ;;            :in-theory nil
;; ;; ;;            )))

;; (defthmd disjoint-1
;;   (implies (diff-s2-d-p-w-nil p)
;;            (not (diff-s2-d-p-w-a p))))

;; (defthmd s2-def-p=diff-s2-def
;;   (implies (s2-d-p point)
;;            (diff-s2-d-p point))
;;   :hints (("Goal"
;;            :use ((:instance s2-d-p (point point))
;;                  (:instance diff-s2-d-p-q-suff (c-point point)
;;                             (w (id-rotation))
;;                             (p point))
;;                  (:instance choice-set-s2-d-p-suff
;;                             (c-point point)
;;                             (point point))
;;                  (:instance ORBIT-POINT-P-SUFF
;;                             (w (id-rotation))
;;                             (point point)
;;                             (o-point point))))))
;;            :in-theory nil)))

;; (skip-proofs
;;  (defthmd s2-def-p=diff-s2-def-1
;;    (implies (diff-s2-d-p point)
;;             (s2-d-p point)))
;;  )

;; (defthmd equal-s2-def-p-diff-s2-def
;;   (iff (s2-d-p p)
;;        (diff-s2-d-p p))
;;   :hints (("Goal"
;;            :use ((:instance s2-def-p=diff-s2-def (point p))
;;                  (:instance s2-def-p=diff-s2-def-1 (point p)))
;;            :in-theory nil
;;            )))
