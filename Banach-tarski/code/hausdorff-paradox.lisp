(in-package "ACL2")

(include-book "free-group")
(include-book "supportive-theorems")

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

  (local
   (defthm rotation*point-on-s2-1
     (implies (and (alist2p :fake-name p1)
                   (alist2p :fake-name p2)
                   (equal (car (dimensions :fake-name p1)) 1)
                   (equal (cadr (dimensions :fake-name p1)) 1)
                   (realp (aref2 :fake-name p1 0 0))
                   (realp (aref2 :fake-name p2 0 0))
                   (m-= p1 p2))
              (equal (aref2 :fake-name p1 0 0)
                     (aref2 :fake-name p2 0 0)))
     :hints (("Goal"
              :in-theory (enable m-=)
              ))))

  (local
   (defthm rotation*point-on-s2-2-1
     (implies (and (array2p :fake-name a)
                   (array2p :fake-name b)
                   (array2p :fake-name c)
                   (array2p :fake-name x)
                   (m-= a x))
              (m-= (m-* a b c) (m-* x b c)))))


  (local (include-book "rotations"))

  (skip-proofs
   (local
    (defthm rotation*point-on-s2-2
      (implies (and (point-in-r3 p1)
                    (r3-rotationp rot))
               (m-= (m-* (m-trans (m-* rot p1)) (m-* rot p1))
                    (m-* (m-trans p1) p1)))
      :hints (("Goal"
               :use ((:instance m-trans-m-*=m-*-m-trans (m1 rot) (m2 p1) (name :fake-name))
                     (:instance m-*-m-inverse-m (m rot))
                     (:instance rotation*point-on-s2-2-1 (b rot) (c p1)
                                (a (m-trans (m-* rot p1)))
                                (x (m-* (m-trans p1) (m-trans rot))))
                     (:instance array2p-alist2p-fname (l rot)))
               :in-theory (e/d () (r3-m-inverse m-trans m-=))
               )))))

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
             :use ((:instance rotation*point-on-S2-2 (p1 p1) (rot rot))
                   (:instance m-*point1^t-point1 (x (m-* rot p1)))
                   (:instance rotation*point-on-S2-1 (p1 (m-* (m-trans (m-* rot p1)) (m-* rot p1)))
                              (p2 (m-* (m-trans p1) p1)))
                   (:instance m-*point1^t-point1 (x p1)))
             :in-theory (e/d () (m-* m-= m-trans))
             ))
    )
  )
