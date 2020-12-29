(include-book "free-group")

(skip-proofs
 (defthmd rot-a-rot-fix-a
   (implies (and (weak-wordp a)
		 (equal x (acl2-sqrt 2)))
	    (m-= (rotation a x) (rotation (word-fix a) x))
	    )
   :hints (("Goal"
	    :in-theory (disable acl2-sqrt)
	    :do-not-induct nil
	    )
	   )
   )
 )

(defthmd rot-a+b
  (implies (and (reducedwordp a)
		(reducedwordp b)
		(equal x (acl2-sqrt 2)))
	   (m-= (rotation (append a b) x) (rotation (compose a b) x)))
  :hints (("Goal"
	   :use ((:instance closure-weak-word (x a) (y b))
		 (:instance reducedwordp=>weak-wordp (x a))
		 (:instance reducedwordp=>weak-wordp (x b))
		 (:instance rot-a-rot-fix-a (a (append a b)))
		 )
	   :in-theory (disable acl2-sqrt rotation)
	   :do-not-induct nil
	   )
	  )
  )

(defthmd rot-a*rot-b=rot-a+b
  (implies (and (reducedwordp a)
		(reducedwordp b)
		(equal x (acl2-sqrt 2)))
	   (m-= (m-* (rotation a x) (rotation b x)) (rotation (append a b) x)))
  :hints (("Goal"
	   :in-theory (disable acl2-sqrt)
	   )
	  ("Subgoal *1/1"
	   :use (:instance funs-lemmas-1 (x x))
	   :in-theory (disable acl2-sqrt)
	   )
	  )
  )

(defthmd rot-a*rot-b-=
  (implies (and (reducedwordp a)
		(reducedwordp b)
		(equal x (acl2-sqrt 2)))
	   (m-= (m-* (rotation a x) (rotation b x)) (rotation (compose a b) x)))
  :hints (("Goal"
	   :use ((:instance rot-a*rot-b=rot-a+b (a a) (b b) (x x))
		 (:instance rot-a+b (a a) (b b) (x x)))
	   :in-theory (disable acl2-sqrt)
	   ))
  )

(defthmd m-*rot-rot-inv=id
  (implies (and (reducedwordp p)
		(equal x (acl2-sqrt 2)))
	   (m-= (m-* (rotation p x) (rotation (word-inverse p) x)) (id-rotation)))
  :hints (("Goal"
	   :use ((:instance rot-a*rot-b-= (a p) (b (word-inverse p)))
		 (:instance reduced-inverse (x p))
		 (:instance reducedwordp-word-inverse (x p)))
	   :in-theory (disable acl2-sqrt compose word-inverse reducedwordp)
	   ))
  )

(defthmd array2p=>a=b=>a*c=b*c
  (implies (and (array2p name a)
		(array2p name b)
		(array2p name c)
		(m-= a b))
	   (m-= (m-* a c) (m-* b c)))
  )

(defthmd rot-a*rot-b=id
  (implies (and (reducedwordp a)
		(reducedwordp b)	 
		(equal x (acl2-sqrt 2))
		(m-= (rotation a x) (rotation b x)))
	   (m-= (rotation (compose a (word-inverse b)) x) (id-rotation)))
  :hints (("Goal"
	   :use ((:instance array2p=>a=b=>a*c=b*c
			    (a (rotation a x))
			    (name '$arg1)
			    (b (rotation b x))
			    (c (rotation (word-inverse b) x)))
		 (:instance rot-a*rot-b-= (a a) (b (word-inverse b)))
		 (:instance rot-a*rot-b-= (a b) (b (word-inverse b)))
		 (:instance reducedwordp-word-inverse (x b))
		 (:instance m-*rot-rot-inv=id (p b))
		 (:instance rotation-props (w a) (name '$arg1))
		 (:instance rotation-props (w b) (name '$arg1))
		 (:instance reducedwordp=>weak-wordp (x a))
		 (:instance reducedwordp=>weak-wordp (x b))
		 (:instance reducedwordp=>weak-wordp (x (word-inverse b)))
		 (:instance rotation-props (w (word-inverse b)) (name '$arg1))
		 )
	   :in-theory (disable acl2-sqrt compose word-inverse reducedwordp)
	   ))
  )

(defthmd redword-a-b-len=0
  (implies (and (reducedwordp a)
		(reducedwordp b)
		(equal (len (compose a (word-inverse b))) 0))
	   (equal (compose a (word-inverse b)) '()))
  )

(skip-proofs
 (defthmd word-inv-word-inv-=x
   (implies (reducedwordp x)
	    (equal (word-inverse (word-inverse x)) x))
   )
 )

(defthmd a!=b=>rot-a!=rot-b-1
  (implies (and (reducedwordp a)
		(reducedwordp b)
		(not (atom a))
		(not (atom b))		
		(not (equal a b))
		(equal x (acl2-sqrt 2)))
	   (not (m-= (rotation a x) (rotation b x))))
  :hints (("Goal"
	   :cases ((> (len (compose a (word-inverse b))) 0)
		   (= (len (compose a (word-inverse b))) 0))
	   :do-not-induct t
	   )
	  ("Subgoal 2"
	   :use ((:instance rot-a*rot-b=id (a a) (b b) (x x))
		 (:instance reducedwordp-word-inverse (x b))
		 (:instance closure-prop (x a) (y (word-inverse b)))
		 (:instance rotaion-not=id (w (compose a (word-inverse b))) (x x))
		 )

	   )
	  ("Subgoal 1"
	   :use ((:instance reducedwordp-word-inverse (x b))
		 (:instance assoc-prop (x a) (y (word-inverse b)) (z b))
		 (:instance redword-a-b-len=0 (a a) (b b))
		 (:instance word-inv-word-inv-=x (x b))
		 (:instance reduced-inverse (x (word-inverse b)))
		 (:instance word-fix=reducedwordp (x a))
		 (:instance word-fix=reducedwordp (x b)))
	   :in-theory (disable acl2-sqrt word-fix rotation reducedwordp word-inverse)
	   :do-not-induct t
	   )
	  )
  )

(defthmd a!=b=>rot-a!=rot-b
  (implies (and (reducedwordp a)
		(reducedwordp b)
     		(not (equal a b))
		(equal x (acl2-sqrt 2)))
	   (not (m-= (rotation a x) (rotation b x))))
  :hints (("Goal"
	   :cases ((and (not (atom a)) (not (atom b)))
		   (and (not (atom a)) (atom b))
		   (and (atom a) (not (atom b))))
	   :in-theory (disable acl2-sqrt)
	   :do-not-induct t
	   )
	  ("Subgoal 3"
	   :use ((:instance a!=b=>rot-a!=rot-b-1 (a a) (b b) (x x))
		 )	   
	   )
	  ("Subgoal 2"
	   :use ((:instance rotaion-not=id (w a))
		 )	   
	   )
	  ("Subgoal 1"
	   :use ((:instance rotaion-not=id (w b))
		 )	   
	   )
	  )
  )
