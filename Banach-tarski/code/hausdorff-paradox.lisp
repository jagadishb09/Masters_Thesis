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
               (point-in-r3 point)
               w
               (m-= (m-* (rotation w (acl2-sqrt 2)) point)
                    point))))

(defun d-p (point)
  (and (s2-def-p point)
       (word-exists point)))


(defun s2-d-p (point)
  (and (s2-def-p point)
       (not (d-p point))))

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

(defthm point-on-d=>rot*p-on-d
  (implies (and (reducedwordp w)
                (s2-def-p p)
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
                   (:instance rotation*point-on-s2-2 (m1 (rotation w1 (acl2-sqrt 2))))
                   (:instance r3-rotationp (m (ROTATION W (ACL2-SQRT 2))))
                   (:instance r3-rotationp (m (ROTATION W1 (ACL2-SQRT 2))))
                   (:instance reducedwordp-word-inverse (x w))
                   (:instance rotation (w nil) (x (acl2-sqrt 2)))
                   )
             ;:in-theory nil
             )
            ("Subgoal 2"
             :use (
                   (:instance r3-matrixp (m (ROTATION W (ACL2-SQRT 2))))
                   (:instance r3-matrixp (m (ROTATION W1 (ACL2-SQRT 2))))
                   )
             :in-theory (e/d () ())
             )
            ))
)
           ;)))
           ;(e/d () (rotation id-rotation word-inverse acl2-sqrt r3-matrixp r3-rotationp reducedwordp compose m-= m-* aref2)))))
