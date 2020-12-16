
(local (include-book "arithmetic-5/support/expt" :dir :system))

(defthmd intep-expt-n
  (implies (and (integerp n)
		(> n 0))
	   (integerp (expt 3 n)))
  :hints (("Goal"
	   :in-theory (enable expt)
	   ))
  )


(defthmd 31/3-integerp
  (implies (integerp c)
	   (equal (* 1/3 3 c) c))
  )

(local
 (defthmd 3*int-mod-=0
   (implies (and (integerp c)
		 (>= c 0))
	    (equal (mod (* 3 c) 3)
		   0
		   )
	    )
   :hints (("Goal"
	    :use (:instance 31/3-integerp (c c))
	    :in-theory (enable mod)
	    ))
   )
 )

(defthmd expt-3-n-lemma
  (implies (integerp n)
	   (equal (* 3 (expt 3 (+ n -1))) (expt 3 n)))
  )

(defthmd n-mod3-3-n-=0-1
  (implies (acl2-numberp y)
	   (and (equal (* 3 1/3 3 1/3 y) y)
		(equal (* 3 1/3 y) y)))
  )

(defthmd n-mod3-3-n-=0
  (implies (and (integerp n)
		(> n 0))
	   (equal (mod (expt 3 n) 3) 0))  
  :hints (("Goal"
	   :in-theory (disable mod)
	   )
	  ("Subgoal *1/5"
	   :use (
		 (:instance 3*int-mod-=0 (c (expt 3 (- n 1))))
		 (:instance intep-expt-n (n (- n 1)))
		 (:instance n-mod3-3-n-=0-1 (y (expt 3 n)))
		 (:instance expt-3-n-lemma (n n)))
	   )
	  )
  )

(defthmd n-mod3-rotation=id-1
  (implies (and (array2p name m1)
		(acl2-numberp (aref2 name m1 0 0))
		(acl2-numberp (aref2 name m1 1 0))
		(acl2-numberp (aref2 name m1 2 0))
		(equal (first (dimensions name m1)) 3)
		(equal (second (dimensions name m1)) 1)
		(m-= m1 (point-p)))
	   (and (equal (aref2 name m1 0 0) 0)
		(equal (aref2 name m1 1 0) 1)
		(equal (aref2 name m1 2 0) 0)))
  :hints (("Goal"
	   :use (:instance array2p-alist2p (name name) (l m1))
	   :in-theory (enable aref2 default header alist2p array2p m-= m-=-row-1 m-=-row)
	   :do-not-induct t
	   )
	  )
  )

(defthmd n-mod3-rotation=id-2
  (implies (and (reducedwordp w)
		(equal x (acl2-sqrt 2))
		(symbolp name)
		(m-= (rotation w x) (id-rotation)))
	   (and (m-= (m-* (rotation w x) (point-p)) (point-p))
		(array2p name (m-* (rotation w x) (point-p)))
		(equal (first (dimensions name (m-* (rotation w x) (point-p)))) 3)
		(equal (second (dimensions name (m-* (rotation w x) (point-p)))) 1)
		)
	   )
  :hints (("Goal"
	   :use ((:instance rotation-props (w w) (name name))
		 (:instance reducedwordp=>weak-wordp (x w))
		 )
	   :in-theory (enable array2p dimensions header)
	   :do-not-induct t
		 
	   ))
  )

(defthmd n-mod3-rotation=id-4
  (implies (reducedwordp w)
	   (integerp (len w))))

(defthmd n-mod3-rotation=id
  (implies (and (reducedwordp w)
		(equal x (acl2-sqrt 2))
		(> (len w) 0)
		(m-= (rotation w x) (id-rotation)))
	   (equal (n-mod3 w x) '(0 0 0)))
  :hints (("Goal"
	   :use (
		 (:instance n-mod3-rotation=id-2 (w w) (x x) (name '$arg1))
		 (:instance acl2-nump-rot (w w) (name '$arg1) (x x))
		 (:instance n-mod3-rotation=id-1 (m1 (m-* (rotation w x) (point-p))) (name '$arg1))		 
		 (:instance sqrt-2-lemmas)
		 (:instance rotation-props (w w) (name '$arg1))
		 (:instance n-mod3-3-n-=0 (n (len w)))
		 (:instance reducedwordp=>weak-wordp (x w))		 
		 )
	   :do-not-induct t
	   )
	  
	  )
  )

