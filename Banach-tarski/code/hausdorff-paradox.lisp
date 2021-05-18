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

(defthm m-*point1^T-point1
  (implies (point-in-r3 x)
           (equal (aref2 :fake-name (m-* (m-trans x) x) 0 0)
                  (+ (* (aref2 :fake-name x 0 0) (aref2 :fake-name x 0 0))
                     (* (aref2 :fake-name x 1 0) (aref2 :fake-name x 1 0))
                     (* (aref2 :fake-name x 2 0) (aref2 :fake-name x 2 0)))))
  :hints (("Goal"
           :use (:instance point-in-r3 (x x))
           :do-not-induct t
           )))
