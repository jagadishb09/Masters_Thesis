(in-package "ACL2")

(local (include-book "arithmetic/top" :dir :system))

(defun real-polynomial-p (poly)
  (if (consp poly)
      (and (realp (car poly))
           (real-polynomial-p (cdr poly)))
    (null poly)))

(defun rational-polynomial-p (poly)
  (if (consp poly)
      (and (rationalp (car poly))
           (rational-polynomial-p (cdr poly)))
    (null poly)))

(defun integer-polynomial-p (poly)
  (if (consp poly)
      (and (integerp (car poly))
           (integer-polynomial-p (cdr poly)))
    (null poly)))

(defun non-trivial-polynomial-p (poly)
  (and (real-polynomial-p poly)
       (< 1 (len poly))
       (not (equal 0 (car (last poly))))))

(defun eval-polynomial (poly x)
  (if (consp poly)
      (+ (* x (eval-polynomial (cdr poly) x))
         (car poly))
    0))

(defun polynomial-root-p (poly x)
  (and (realp x)
       (equal (eval-polynomial poly x) 0)))

(defun non-trivial-polynomial-root-p (poly x)
  (and (non-trivial-polynomial-p poly)
       (polynomial-root-p poly x)))

(defun prod-denoms (list)
  (if (consp list)
      (* (denominator (car list))
         (prod-denoms (cdr list)))
    1))

(defun scale-polynomial (poly c)
  (if (consp poly)
      (cons (* c (car poly))
            (scale-polynomial (cdr poly) c))
    nil))

(defthm scale-integer-polynomial
  (implies (and (integer-polynomial-p poly)
                (integerp c))
           (integer-polynomial-p (scale-polynomial poly c))))

(defthm scale-scale-polynomial
  (equal (scale-polynomial (scale-polynomial poly c1) c2)
         (scale-polynomial poly (* c1 c2))))

(defthm convert-rational-to-integer-polynomial
  (implies (rational-polynomial-p poly)
           (integer-polynomial-p (scale-polynomial poly (prod-denoms poly))))
  :hints (("Subgoal *1/2.1"
           :use ((:instance scale-integer-polynomial
                            (poly (scale-polynomial (cdr poly)
                                                    (prod-denoms (cdr poly))))
                            (c (denominator (car poly)))))
           :in-theory (disable scale-integer-polynomial)))
  )

(defthm rational-scale-polynomial
  (implies (and (rational-polynomial-p poly)
                (rationalp c))
           (rational-polynomial-p (scale-polynomial poly c))))

(defthm integer-polynomials-are-rational
  (implies (integer-polynomial-p poly)
           (rational-polynomial-p poly))
  :rule-classes (:rewrite :type-prescription))

(defthm rational-polynomials-are-reals
  (implies (rational-polynomial-p poly)
           (real-polynomial-p poly))
  :rule-classes (:rewrite :type-prescription))

(defthm eval-scale-polynomial
  (equal (eval-polynomial (scale-polynomial poly c) x)
         (* c (eval-polynomial poly x))))

(defun-sk algebraic-numberp (x)
  (exists poly
          (and (rational-polynomial-p poly)
               (non-trivial-polynomial-p poly)
               (polynomial-root-p poly x))))

(defun-sk weak-algebraic-numberp (x)
  (exists poly
          (and (integer-polynomial-p poly)
               (non-trivial-polynomial-p poly)
               (polynomial-root-p poly x))))

(defthm scale-non-trivial
  (implies (and (real-polynomial-p poly)
                (not (equal (car (last poly)) 0))
                (realp x)
                (not (equal x 0)))
           (not (equal (car (last (scale-polynomial poly x))) 0)))
  )
           
(defthm length-scale
  (equal (len (scale-polynomial poly x))
         (len poly)))

(defthm algebraic-numbers-are-weak-algebraic
  (implies (algebraic-numberp x)
           (weak-algebraic-numberp x))
  :hints (("Goal"
           :use ((:instance weak-algebraic-numberp-suff
                            (poly (scale-polynomial (algebraic-numberp-witness x) (prod-denoms (algebraic-numberp-witness x)))))))))

(defun divide-polynomial-with-remainder-by-x+a (poly a)
  (if (consp poly)
      (let ((rest (divide-polynomial-with-remainder-by-x+a (cdr poly) a)))
        (if (consp rest)
            (cons (- (car poly)
                     (* a (car rest)))
                  rest)
          (list (car poly))))
    nil))

(defthm eval-divide-poly
  (equal (+ (* (eval-polynomial (cdr (divide-polynomial-with-remainder-by-x+a poly a)) x)
               (+ x a))
            (car (divide-polynomial-with-remainder-by-x+a poly a)))
         (eval-polynomial poly x)))

(defthm root-remainder
  (implies (and (consp poly)
                (real-polynomial-p poly)
                (equal (eval-polynomial poly a) 0))
           (equal (car (divide-polynomial-with-remainder-by-x+a poly (- a))) 0))
  :hints (("Goal" :do-not-induct t
           :use ((:instance eval-divide-poly (x a) (a (- a))))
           :in-theory (disable eval-divide-poly
                               eval-polynomial
                               divide-polynomial-with-remainder-by-x+a))))

(defthm real-eval-poly
  (implies (and (realp x)
                (real-polynomial-p poly))
           (realp (eval-polynomial poly x)))
  :rule-classes (:rewrite :type-prescription))

(defthm real-poly-divide
  (implies (and (realp a)
                (real-polynomial-p poly))
           (real-polynomial-p (divide-polynomial-with-remainder-by-x+a poly a)))
  :rule-classes (:rewrite :type-prescription))

(local
 (defthm real-eval-poly-useful-rewrite-rule
   (implies (and (real-polynomial-p poly)
                 (realp a)
                 (realp b))
            (realp (eval-polynomial (cdr (divide-polynomial-with-remainder-by-x+a poly (- a))) b)))
   :hints (("Goal"
            :use ((:instance real-poly-divide (poly poly) (a (- a))))
            :in-theory (disable real-poly-divide eval-polynomial divide-polynomial-with-remainder-by-x+a)))))

(defthm other-roots-also-roots-of-quotient
  (implies (and (consp poly)
                (real-polynomial-p poly)
                (equal (eval-polynomial poly a) 0)
                (equal (eval-polynomial poly b) 0)
                (realp a)
                (realp b)
                (not (equal a b)))
           (equal (eval-polynomial (cdr (divide-polynomial-with-remainder-by-x+a poly (- a))) b) 0))
  :hints (("Goal" :do-not-induct t
           :use ((:instance root-remainder)
                 (:instance eval-divide-poly (x b) (a (- a)))
                 (:instance (:theorem (implies (and (realp x) (realp y)
                                                    (equal (* x y) 0)
                                                    (not (equal y 0)))
                                               (equal x 0)))
                            (x (eval-polynomial (cdr (divide-polynomial-with-remainder-by-x+a poly (- a))) b))
                            (y (+ b (- a))))
                 )
           :in-theory (disable eval-divide-poly
                               eval-polynomial
                               divide-polynomial-with-remainder-by-x+a))))

(defun divide-polynomial-by-roots (poly roots)
  (if (consp roots)
      (divide-polynomial-by-roots (cdr (divide-polynomial-with-remainder-by-x+a poly (- (car roots))))
                                  (cdr roots))
    poly))

(defthm length-divide-polynomial-with-remainder
  (implies (real-polynomial-p poly)
           (equal (length (divide-polynomial-with-remainder-by-x+a poly a))
                  (length poly))))
                                

(defthm real-polynomials-of-zero-length
  (implies (and (real-polynomial-p poly)
                (equal 0 (len poly)))
           (not (consp poly))))

(defthm length-divide-polynomial-without-remainder
  (implies (and (consp poly)
                (real-polynomial-p poly))
           (equal (len (cdr (divide-polynomial-with-remainder-by-x+a poly a)))
                  (1- (length poly))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance length-divide-polynomial-with-remainder))
           :in-theory (disable length-divide-polynomial-with-remainder
                               divide-polynomial-with-remainder-by-x+a))))

(defthm real-poly-divide-without-remainder
  (implies (and (realp a)
                (real-polynomial-p poly))
           (real-polynomial-p (cdr (divide-polynomial-with-remainder-by-x+a poly a))))
  :hints (("Goal"
           :use ((:instance real-poly-divide))
           :in-theory (disable real-poly-divide divide-polynomial-with-remainder-by-x+a))))

(defthm positive-len-implies-consp
  (implies (< (+ 1 (len x)) (len y))
           (consp y)))

(defthm length-divide-polynomial-by-roots
  (implies (and (real-polynomial-p poly)
                (real-listp roots)
                (< (length roots) (length poly)))
           (equal (length (divide-polynomial-by-roots poly roots))
                  (- (length poly)
                     (length roots)))))




(defthm eval-null-poly
  (implies (equal (len poly) 0)
           (equal (eval-polynomial poly x) 0)))

(defthm roots-of-monomial-are-equal-lemma
  (implies (and (equal (len poly) 2)
                (real-polynomial-p poly))
           (equal (eval-polynomial poly x)
                  (+ (car poly)
                     (* x (car (cdr poly))))))
  :hints (("Goal" :do-not-induct t
           :expand ((eval-polynomial poly x)
                    (eval-polynomial (cdr poly) x))))
  )

(defthm roots-of-monomial-are-equal-algebra-lemma
  (implies (and (realp x)
                (realp y)
                (not (equal y 0))
                (realp a)
                (realp b)
                (equal (+ x (* a y))
                       (+ x (* b y))))
           (equal (equal a b) t)))

(defthm roots-of-monomial-are-equal
  (implies (and (equal (len poly) 2)
                (non-trivial-polynomial-p poly)
                (realp a)
                (realp b)
                (equal (eval-polynomial poly a) 0)
                (equal (eval-polynomial poly b) 0))
           (equal (equal a b) t))
  :hints (("Goal" :do-not-induct t
           :use ((:instance roots-of-monomial-are-equal-lemma (x a))
                 (:instance roots-of-monomial-are-equal-lemma (x b))
                 (:instance roots-of-monomial-are-equal-algebra-lemma
                            (x (car poly))
                            (y (cadr poly))))
           :in-theory (disable roots-of-monomial-are-equal-lemma
                               roots-of-monomial-are-equal-algebra-lemma
                               eval-polynomial
                               right-cancellation-for-*
                               left-cancellation-for-+))))

(defthm consp-divide-poly
  (implies (consp poly)
           (consp (divide-polynomial-with-remainder-by-x+a poly a))))

(defthm non-trivial-quotient-with-remainder
  (implies (and (realp a)
                (real-polynomial-p poly)
                (< 1 (len poly))
                (not (equal (car (last poly)) 0)))
           (not (equal (car (last (divide-polynomial-with-remainder-by-x+a poly (- a)))) 0))))

(defthm non-trivial-quotient
  (implies (and (realp a)
                (real-polynomial-p poly)
                (< 1 (len poly))
                (not (equal (car (last poly)) 0)))
           (not (equal (car (last (cdr (divide-polynomial-with-remainder-by-x+a poly (- a))))) 0)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance non-trivial-quotient-with-remainder)
                 (:instance (:theorem (implies (and (consp x) (consp (cdr x)))
                                               (equal (last (cdr x)) (last x))))
                            (x (divide-polynomial-with-remainder-by-x+a poly (- a)))))
           :in-theory (disable non-trivial-quotient-with-remainder
                               divide-polynomial-with-remainder-by-x+a))))
           

(defthm other-non-trivial-roots-also-non-trivial-roots-of-quotient
  (implies (and (non-trivial-polynomial-p poly)
                (polynomial-root-p poly a)
                (polynomial-root-p poly b)
                (not (equal a b)))
           (non-trivial-polynomial-root-p (cdr (divide-polynomial-with-remainder-by-x+a poly (- a)))
                                          b))
  :hints (("Goal" :do-not-induct t
           :use ((:instance other-roots-also-roots-of-quotient))
           :in-theory (disable other-roots-also-roots-of-quotient
                               divide-polynomial-with-remainder-by-x+a
                               rational-polynomial-p))
          ("Goal'''"
           :cases ((< 2 (len poly))))
          ("Subgoal 1"
           :use ((:instance length-divide-polynomial-without-remainder (a (- a))))
           :in-theory (disable length-divide-polynomial-without-remainder
                               divide-polynomial-with-remainder-by-x+a))
          ))

(defun distinct-non-trivial-polynomial-root-list-p (poly roots)
  (if (consp roots)
      (and (non-trivial-polynomial-root-p poly (car roots))
           (not (member (car roots) (cdr roots)))
           (distinct-non-trivial-polynomial-root-list-p poly (cdr roots)))
    (null roots)))

(defthm real-polynomial-divide-by-roots
  (implies (and (real-polynomial-p poly)
                (real-listp roots))
           (real-polynomial-p (divide-polynomial-by-roots poly roots))))

(defthm list-of-roots-is-list-of-reals
  (implies (distinct-non-trivial-polynomial-root-list-p poly roots)
           (real-listp roots))
  :rule-classes (:rewrite :type-prescription))

(defthm distinct-non-trivial-stepper
  (implies (and (distinct-non-trivial-polynomial-root-list-p poly roots)
                (non-trivial-polynomial-root-p poly a)
                (not (member a roots)))
           (distinct-non-trivial-polynomial-root-list-p (cdr (divide-polynomial-with-remainder-by-x+a poly (- a)))
                                                        roots))
  :hints (("Goal" :do-not-induct t
           :induct (distinct-non-trivial-polynomial-root-list-p poly roots))
          ("Subgoal *1/1.3"
           :use ((:instance other-non-trivial-roots-also-non-trivial-roots-of-quotient (a a) (b (car roots))))
           :in-theory (disable other-non-trivial-roots-also-non-trivial-roots-of-quotient
                               divide-polynomial-with-remainder-by-x+a))))

(defthm other-non-trivial-roots-also-non-trivial-roots-of-quotient-list
  (implies (and (non-trivial-polynomial-p poly)
                (polynomial-root-p poly a)
                (distinct-non-trivial-polynomial-root-list-p poly roots)
                (not (member a roots)))
           (non-trivial-polynomial-root-p (divide-polynomial-by-roots poly roots)
                                          a))
  :hints (("Goal" :do-not-induct t
           :induct (divide-polynomial-by-roots poly roots))
          ("Subgoal *1/1.12"
           :use ((:instance other-non-trivial-roots-also-non-trivial-roots-of-quotient (a (car roots)) (b a)))
           :in-theory (disable other-non-trivial-roots-also-non-trivial-roots-of-quotient
                               divide-polynomial-with-remainder-by-x+a))
          ("Subgoal *1/1.11"
           :use ((:instance other-non-trivial-roots-also-non-trivial-roots-of-quotient (a (car roots)) (b a)))
           :in-theory (disable other-non-trivial-roots-also-non-trivial-roots-of-quotient
                               divide-polynomial-with-remainder-by-x+a))
          ("Subgoal *1/1.10"
           :use ((:instance other-non-trivial-roots-also-non-trivial-roots-of-quotient (a (car roots)) (b a)))
           :in-theory (disable other-non-trivial-roots-also-non-trivial-roots-of-quotient
                               divide-polynomial-with-remainder-by-x+a))
          ("Subgoal *1/1.6"
           :use ((:instance other-roots-also-roots-of-quotient
                            (poly poly)
                            (a (car roots))
                            (b a)))
           :in-theory (disable other-roots-also-roots-of-quotient
                               divide-polynomial-with-remainder-by-x+a))
          ("Subgoal *1/1.5"
           :use ((:instance other-roots-also-roots-of-quotient
                            (poly poly)
                            (a (car roots))
                            (b a)))
           :in-theory (disable other-roots-also-roots-of-quotient
                               divide-polynomial-with-remainder-by-x+a))
          ("Subgoal *1/1.4"
           :use ((:instance other-roots-also-roots-of-quotient
                            (poly poly)
                            (a (car roots))
                            (b a)))
           :in-theory (disable other-roots-also-roots-of-quotient
                               divide-polynomial-with-remainder-by-x+a))))

(defthm divide-nil-by-roots
  (equal (divide-polynomial-by-roots nil roots)
         nil))

(defthm open-divide-polynomial-by-roots
  (equal (divide-polynomial-by-roots poly (cons roots1 roots2))
         (divide-polynomial-by-roots (cdr (divide-polynomial-with-remainder-by-x+a poly (- roots1)))
                                     roots2))
  :hints (("Goal"
           :expand ((DIVIDE-POLYNOMIAL-BY-ROOTS POLY (CONS ROOTS1 ROOTS2))))))

(defthm length-divide-polynomial-by-roots-2
  (implies (and (real-polynomial-p poly)
                (real-listp roots)
                (< 1 (length (divide-polynomial-by-roots poly roots))))
           (equal (length (divide-polynomial-by-roots poly roots))
                  (- (length poly)
                     (length roots))))
  :hints (("Subgoal *1/6"
           :use ((:instance length-divide-polynomial-without-remainder (a (- (car roots)))))
           :in-theory (disable length-divide-polynomial-without-remainder
                               divide-polynomial-with-remainder-by-x+a
                               divide-polynomial-by-roots)))
  )

(defthm polynomial-order-at-least-number-of-roots-lemma
  (implies (and (non-trivial-polynomial-p poly)
                (distinct-non-trivial-polynomial-root-list-p poly roots)
                (polynomial-root-p poly a)
                (not (member a roots)))
           (< (1+ (length roots)) (length poly)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance length-divide-polynomial-by-roots-2)
                 (:instance other-non-trivial-roots-also-non-trivial-roots-of-quotient-list))
           :in-theory (disable length-divide-polynomial-by-roots-2
                               other-non-trivial-roots-also-non-trivial-roots-of-quotient-list
                               divide-polynomial-by-roots))))

(defthm polynomial-order-at-least-number-of-roots
  (implies (and (non-trivial-polynomial-p poly)
                (distinct-non-trivial-polynomial-root-list-p poly roots))
           (< (length roots) (length poly)))
  :hints (("Goal" :do-not-induct t
           :cases ((consp roots)))
          ("Subgoal 1"
           :use ((:instance polynomial-order-at-least-number-of-roots-lemma
                            (poly poly)
                            (a (car roots))
                            (roots (cdr roots)))))))

(defchoose choose-new-root (x) (poly roots)
  (and (polynomial-root-p poly x)
       (not (member x roots))))

(defun-sk exists-another-root (poly roots)
  (exists x
          (and (polynomial-root-p poly x)
               (not (member x roots)))))

(defun choose-n-roots (n poly roots)
  (if (zp n)
      roots
    (if (exists-another-root poly roots)
        (choose-n-roots (1- n)
                        poly
                        (cons (choose-new-root poly roots)
                              roots))
      roots)))

(defthm choose-new-root-valid
  (implies (exists-another-root poly roots)
           (and (polynomial-root-p poly (choose-new-root poly roots))
                (not (member (choose-new-root poly roots) roots))))
  :hints (("Goal"
           :use ((:instance choose-new-root
                            (x (exists-another-root-witness poly roots)))))))

(defthm choose-n-roots-valid
  (implies (and (non-trivial-polynomial-p poly)
                (distinct-non-trivial-polynomial-root-list-p poly roots))
           (distinct-non-trivial-polynomial-root-list-p poly (choose-n-roots n poly roots))))

(defthm realp-choose-new-root
  (implies (exists-another-root poly roots)
           (realp (choose-new-root poly roots)))
  :hints (("Goal"
           :use ((:instance CHOOSE-NEW-ROOT
                            (x (exists-another-root-witness poly roots))))
           :in-theory (disable choose-new-root-valid))))

(defthm length-choose-n-roots
  (implies (and (real-listp roots)
                (natp n))
           (<= (length (choose-n-roots n poly roots))
               (+ (length roots) n)))
  :hints (("Goal"
           :do-not-induct t
           :induct (choose-n-roots n poly roots))))

(defun find-roots-of-poly (poly)
  (choose-n-roots (1- (length poly)) poly nil))

(defthm find-roots-of-poly-contains-only-roots
  (implies (non-trivial-polynomial-p poly)
           (distinct-non-trivial-polynomial-root-list-p poly (find-roots-of-poly poly))))

(defthm choose-n-roots-poly-contains-all-roots-case-1-lemma
  (implies (and (real-listp roots)
                (natp n)
                (< (length (choose-n-roots n poly roots))
                   (+ (length roots) n)))
           (not (exists-another-root poly (choose-n-roots n poly roots))))
  :hints (("Goal"
           :in-theory (disable exists-another-root))))

(defthm choose-n-roots-poly-contains-all-roots-case-1-lemma-stronger
  (implies (and (non-trivial-polynomial-p poly)
                (< (length (find-roots-of-poly poly))
                   (1- (length poly))))
           (not (exists-another-root poly (find-roots-of-poly poly))))
  :hints (("Goal"
           :use ((:instance choose-n-roots-poly-contains-all-roots-case-1-lemma
                            (roots nil)
                            (n (1- (length poly)))))
           :in-theory (disable choose-n-roots-poly-contains-all-roots-case-1-lemma
                               choose-n-roots))))

(defthm not-exists-another-root-then-no-more-roots
  (implies (and (realp x)
                (not (member x roots))
                (not (exists-another-root poly roots)))
           (not (polynomial-root-p poly x)))
  :hints (("Goal"
           :use ((:instance exists-another-root-suff)))))

(defthm choose-n-roots-poly-contains-all-roots-case-1
  (implies (and (non-trivial-polynomial-p poly)
                (< (length (find-roots-of-poly poly))
                   (1- (length poly)))
                (realp x)
                (not (member x (find-roots-of-poly poly))))
           (not (polynomial-root-p poly x)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance choose-n-roots-poly-contains-all-roots-case-1-lemma-stronger)
                 (:instance not-exists-another-root-then-no-more-roots
                            (roots (find-roots-of-poly poly))))
           :in-theory (disable choose-n-roots-poly-contains-all-roots-case-1-lemma-stronger
                               not-exists-another-root-then-no-more-roots
                               find-roots-of-poly
                               polynomial-root-p
                               exists-another-root))))


(defthm choose-n-roots-poly-contains-all-roots-case-2
  (implies (and (non-trivial-polynomial-p poly)
                (equal (length (find-roots-of-poly poly))
                       (1- (length poly)))
                (realp x)
                (not (member x (find-roots-of-poly poly))))
           (not (polynomial-root-p poly x)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance polynomial-order-at-least-number-of-roots
                            (poly poly)
                            (roots (cons x (find-roots-of-poly poly)))))
           :in-theory (disable polynomial-order-at-least-number-of-roots
                               choose-n-roots
                               polynomial-root-p))))

(defthm polys-are-not-strings
  (implies (non-trivial-polynomial-p poly)
           (not (stringp poly))))

#|
(defthm roots-are-real
  (implies (polynomial-root-p poly x)
           (realp x))
  :rule-classes (:rewrite :forward-chaining))
|#

(defthm choose-n-roots-poly-contains-all-roots
  (implies (and (non-trivial-polynomial-p poly)
                (realp x)
                (polynomial-root-p poly x))
           (member x (find-roots-of-poly poly)))
  :hints (("Goal" :do-not-induct t
           :cases ((= (length (find-roots-of-poly poly))
                      (1- (length poly)))
                   (< (length (find-roots-of-poly poly))
                      (1- (length poly)))
                   (> (length (find-roots-of-poly poly))
                      (1- (length poly))))
           :in-theory (disable find-roots-of-poly
                               non-trivial-polynomial-p
                               polynomial-root-p))
          ("Subgoal 1"
           :use ((:instance polynomial-order-at-least-number-of-roots
                            (poly poly)
                            (roots (find-roots-of-poly poly))))
           :in-theory (disable polynomial-order-at-least-number-of-roots
                               choose-n-roots
                               polynomial-root-p))))

(defthm length-find-roots-poly
  (implies (non-trivial-polynomial-p poly)
           (< (length (find-roots-of-poly poly)) (length poly)))
  :hints (("Goal"
           :use ((:instance polynomial-order-at-least-number-of-roots
                            (poly poly)
                            (roots (find-roots-of-poly poly))))
           :in-theory (disable polynomial-order-at-least-number-of-roots
                               non-trivial-polynomial-p
                               choose-n-roots))))

(in-theory (disable find-roots-of-poly (find-roots-of-poly)))

(defun polynomial-height-aux (poly)
  (if (consp poly)
      (+ (abs (car poly))
         (polynomial-height-aux (cdr poly)))
    0))

(defun polynomial-height (poly)
  (+ (polynomial-height-aux poly)
     (- (length poly) 2)))

(defthm integer-height-of-integer-polynomials-aux
  (implies (integer-polynomial-p poly)
           (and (integerp (polynomial-height-aux poly))
                (<= 0 (polynomial-height-aux poly))))
  :rule-classes (:rewrite :type-prescription))

(defthm integer-height-of-integer-polynomials-lemma
  (implies (and (integer-polynomial-p poly)
                (consp poly))
           (<= (abs (car (last poly)))
               (polynomial-height-aux poly))))

(defthm last-car-poly-is-number
  (implies (and (integer-polynomial-p poly)
                (< 1 (len poly)))
           (integerp (car (last poly)))))

(defthm abs-0-only-for-0
  (implies (and (integerp x)
                (<= (abs x) 0))
           (equal (equal 0 x) t)))

(defthm integer-height-of-integer-polynomials-lemma-stronger
  (implies (and (integer-polynomial-p poly)
                (non-trivial-polynomial-p poly))
           (<= 1
               (polynomial-height-aux poly)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance integer-height-of-integer-polynomials-lemma))
           :in-theory (disable integer-height-of-integer-polynomials-lemma
                               integer-polynomial-p
                               polynomial-height-aux
                               abs))))

(defthm integer-height-of-integer-polynomials
  (implies (and (integer-polynomial-p poly)
                (non-trivial-polynomial-p poly))
           (and (integerp (polynomial-height poly))
                (< 0 (polynomial-height poly))))
  :hints (("Goal"
           :use ((:instance integer-height-of-integer-polynomials-lemma-stronger))
           :in-theory (disable integer-height-of-integer-polynomials-lemma-stronger
                               integer-polynomial-p
                               polynomial-height-aux)))
  :rule-classes (:rewrite :type-prescription))

(defthm maximum-order-of-poly-with-height
  (implies (and (integer-polynomial-p poly)
                (non-trivial-polynomial-p poly))
           (<=  (length poly)
                (1+ (polynomial-height poly))))
  :hints (("Goal"
           :use ((:instance integer-height-of-integer-polynomials-lemma-stronger))
           :in-theory (disable integer-height-of-integer-polynomials-lemma-stronger
                               integer-polynomial-p
                               polynomial-height-aux)))
  )

(defun mapcons (first list)
  (if (consp list)
      (cons (cons first (car list))
            (mapcons first (cdr list)))
    nil))

(defun generate-polys-of-length-with-sum (first sum length)
  (declare (xargs :measure (cons (cons 1 (1+ (nfix length))) (nfix first))))
  (if (and (integerp length) 
           (< 1 length))
      (if (zp first)
          (mapcons 0 (generate-polys-of-length-with-sum sum sum (1- length)))
        (append (generate-polys-of-length-with-sum (1- first) sum length)
                (mapcons first     (generate-polys-of-length-with-sum (- sum first) (- sum first) (1- length)))
                (mapcons (- first) (generate-polys-of-length-with-sum (- sum first) (- sum first) (1- length)))))
    (if (equal sum 0)
        (list (list sum))
      (list (list sum)
            (list (- sum))))))

(defun generate-polys-with-height-and-max-length (height length)
  (if (and (integerp length) (< 1 length))
      (append (generate-polys-with-height-and-max-length height (1- length))
              (generate-polys-of-length-with-sum (+ height (- length) 2) (+ height (- length) 2) length))
    nil))

(defun generate-polys-with-height (height)
  (generate-polys-with-height-and-max-length height (1+ height)))


(defthm poly-must-have-length-one
  (implies (and (consp poly)
                (<= (len poly) 1))
           (not (consp (cdr poly)))))

(defthm member-mapcons
  (implies (and (consp poly)
                (member (cdr poly) polys))
           (member poly (mapcons (car poly) polys))))

(defthmd member-append3-1
  (implies (member x y1)
           (member x (append y1 y2 y3))))

(defthmd member-append3-2
  (implies (member x y2)
           (member x (append y1 y2 y3))))

(defthmd member-append3-3
  (implies (member x y3)
           (member x (append y1 y2 y3))))

(defun generate-polys-of-length-with-sum-induction-hint (first sum length poly)
  (declare (xargs :measure (cons (cons 1 (1+ (nfix length))) (nfix first))))
  (if (and (integerp length) 
           (< 1 length))
      (if (zp first)
          (mapcons 0 (generate-polys-of-length-with-sum-induction-hint sum sum (1- length) (cdr poly)))
        (append (generate-polys-of-length-with-sum-induction-hint (1- first) sum length poly)
                (mapcons first     (generate-polys-of-length-with-sum-induction-hint (- sum first) (- sum first) (1- length) (cdr poly)))
                (mapcons (- first) (generate-polys-of-length-with-sum-induction-hint (- sum first) (- sum first) (1- length) (cdr poly)))))
    poly))

(defthm lists-of-length-with-sum-valid
  (implies (and (consp poly)
                (integer-polynomial-p poly)
                (natp first)
                (<= (abs (car poly)) first)
                (equal sum  (polynomial-height-aux poly))
                (equal length (length poly)))
           (member poly (generate-polys-of-length-with-sum first sum length)))
  :hints (("Goal" :do-not-induct t
           :induct (generate-polys-of-length-with-sum-induction-hint first sum length poly))
          ("Subgoal *1/4"
           :use ((:instance poly-must-have-length-one))
           :in-theory (disable poly-must-have-length-one))
          ("Subgoal *1/3"
           :use ((:instance poly-must-have-length-one))
           :in-theory (disable poly-must-have-length-one))
          ("Subgoal *1/2.22"
           :use ((:instance member-mapcons 
                            (poly poly)
                            (polys (generate-polys-of-length-with-sum (+ (- first)
                                                                         (- (car poly))
                                                                         (polynomial-height-aux (cdr poly))) 
                                                                      (+ (- first)
                                                                         (- (car poly))
                                                                         (polynomial-height-aux (cdr poly)))
                                                                      (len (cdr poly)))))
                 (:instance member-append3-3
                            (x poly)
                            (y1 (generate-polys-of-length-with-sum (1- first) 
                                                                   (polynomial-height-aux poly)
                                                                   (len poly)))
                            (y2 (mapcons first
                                         (generate-polys-of-length-with-sum (+ (- first)
                                                                               (- (car poly))
                                                                               (polynomial-height-aux (cdr poly))) 
                                                                            (+ (- first)
                                                                               (- (car poly))
                                                                               (polynomial-height-aux (cdr poly)))
                                                                            (len (cdr poly)))))
                            (y3 (mapcons (- first)
                                         (generate-polys-of-length-with-sum (+ (- first)
                                                                               (- (car poly))
                                                                               (polynomial-height-aux (cdr poly))) 
                                                                            (+ (- first)
                                                                               (- (car poly))
                                                                               (polynomial-height-aux (cdr poly)))
                                                                            (len (cdr poly)))))))
           :in-theory (disable member-mapcons))
          ("Subgoal *1/2.17"
           :use ((:instance member-append3-1
                            (x poly)
                            (y1 (generate-polys-of-length-with-sum (1- first) 
                                                                   (polynomial-height-aux poly)
                                                                   (len poly)))
                            (y2 (mapcons first
                                         (generate-polys-of-length-with-sum (+ (- first)
                                                                               (car poly)
                                                                               (polynomial-height-aux (cdr poly))) 
                                                                            (+ (- first)
                                                                               (car poly)
                                                                               (polynomial-height-aux (cdr poly)))
                                                                            (len (cdr poly)))))
                            (y3 (mapcons (- first)
                                         (generate-polys-of-length-with-sum (+ (- first)
                                                                               (car poly)
                                                                               (polynomial-height-aux (cdr poly))) 
                                                                            (+ (- first)
                                                                               (car poly)
                                                                               (polynomial-height-aux (cdr poly)))
                                                                            (len (cdr poly)))))))
           )
          ("Subgoal *1/2.16"
           :use ((:instance member-append3-1
                            (x poly)
                            (y1 (generate-polys-of-length-with-sum (1- first) 
                                                                   (polynomial-height-aux poly)
                                                                   (len poly)))
                            (y2 (mapcons first
                                         (generate-polys-of-length-with-sum (+ (- first)
                                                                               (car poly)
                                                                               (polynomial-height-aux (cdr poly))) 
                                                                            (+ (- first)
                                                                               (car poly)
                                                                               (polynomial-height-aux (cdr poly)))
                                                                            (len (cdr poly)))))
                            (y3 (mapcons (- first)
                                         (generate-polys-of-length-with-sum (+ (- first)
                                                                               (car poly)
                                                                               (polynomial-height-aux (cdr poly))) 
                                                                            (+ (- first)
                                                                               (car poly)
                                                                               (polynomial-height-aux (cdr poly)))
                                                                            (len (cdr poly)))))))
           )
          ("Subgoal *1/2.15"
           :use ((:instance member-append3-1
                            (x poly)
                            (y1 (generate-polys-of-length-with-sum (1- first) 
                                                                   (polynomial-height-aux poly)
                                                                   (len poly)))
                            (y2 (mapcons first
                                         (generate-polys-of-length-with-sum (+ (- first)
                                                                               (car poly)
                                                                               (polynomial-height-aux (cdr poly))) 
                                                                            (+ (- first)
                                                                               (car poly)
                                                                               (polynomial-height-aux (cdr poly)))
                                                                            (len (cdr poly)))))
                            (y3 (mapcons (- first)
                                         (generate-polys-of-length-with-sum (+ (- first)
                                                                               (car poly)
                                                                               (polynomial-height-aux (cdr poly))) 
                                                                            (+ (- first)
                                                                               (car poly)
                                                                               (polynomial-height-aux (cdr poly)))
                                                                            (len (cdr poly)))))))
           )
          ("Subgoal *1/2.14"
           :use ((:instance member-append3-1
                            (x poly)
                            (y1 (generate-polys-of-length-with-sum (1- first) 
                                                                   (polynomial-height-aux poly)
                                                                   (len poly)))
                            (y2 (mapcons first
                                         (generate-polys-of-length-with-sum (+ (- first)
                                                                               (car poly)
                                                                               (polynomial-height-aux (cdr poly))) 
                                                                            (+ (- first)
                                                                               (car poly)
                                                                               (polynomial-height-aux (cdr poly)))
                                                                            (len (cdr poly)))))
                            (y3 (mapcons (- first)
                                         (generate-polys-of-length-with-sum (+ (- first)
                                                                               (car poly)
                                                                               (polynomial-height-aux (cdr poly))) 
                                                                            (+ (- first)
                                                                               (car poly)
                                                                               (polynomial-height-aux (cdr poly)))
                                                                            (len (cdr poly)))))))
           )
          ("Subgoal *1/2.13"
           :use ((:instance member-append3-1
                            (x poly)
                            (y1 (generate-polys-of-length-with-sum (1- first) 
                                                                   (polynomial-height-aux poly)
                                                                   (len poly)))
                            (y2 (mapcons first
                                         (generate-polys-of-length-with-sum (+ (- first)
                                                                               (car poly)
                                                                               (polynomial-height-aux (cdr poly))) 
                                                                            (+ (- first)
                                                                               (car poly)
                                                                               (polynomial-height-aux (cdr poly)))
                                                                            (len (cdr poly)))))
                            (y3 (mapcons (- first)
                                         (generate-polys-of-length-with-sum (+ (- first)
                                                                               (car poly)
                                                                               (polynomial-height-aux (cdr poly))) 
                                                                            (+ (- first)
                                                                               (car poly)
                                                                               (polynomial-height-aux (cdr poly)))
                                                                            (len (cdr poly)))))))
           )      
          ("Subgoal *1/2.11"
           :use ((:instance member-append3-1
                            (x poly)
                            (y1 (generate-polys-of-length-with-sum (1- first) 
                                                                   (polynomial-height-aux poly)
                                                                   (len poly)))
                            (y2 (mapcons first
                                         (generate-polys-of-length-with-sum (+ (- first)
                                                                               (- (car poly))
                                                                               (polynomial-height-aux (cdr poly))) 
                                                                            (+ (- first)
                                                                               (- (car poly))
                                                                               (polynomial-height-aux (cdr poly)))
                                                                            (len (cdr poly)))))
                            (y3 (mapcons (- first)
                                         (generate-polys-of-length-with-sum (+ (- first)
                                                                               (- (car poly))
                                                                               (polynomial-height-aux (cdr poly))) 
                                                                            (+ (- first)
                                                                               (- (car poly))
                                                                               (polynomial-height-aux (cdr poly)))
                                                                            (len (cdr poly)))))))
           )
          ("Subgoal *1/2.10"
           :use ((:instance member-append3-1
                            (x poly)
                            (y1 (generate-polys-of-length-with-sum (1- first) 
                                                                   (polynomial-height-aux poly)
                                                                   (len poly)))
                            (y2 (mapcons first
                                         (generate-polys-of-length-with-sum (+ (- first)
                                                                               (- (car poly))
                                                                               (polynomial-height-aux (cdr poly))) 
                                                                            (+ (- first)
                                                                               (- (car poly))
                                                                               (polynomial-height-aux (cdr poly)))
                                                                            (len (cdr poly)))))
                            (y3 (mapcons (- first)
                                         (generate-polys-of-length-with-sum (+ (- first)
                                                                               (- (car poly))
                                                                               (polynomial-height-aux (cdr poly))) 
                                                                            (+ (- first)
                                                                               (- (car poly))
                                                                               (polynomial-height-aux (cdr poly)))
                                                                            (len (cdr poly)))))))
           )
          ("Subgoal *1/2.9"
           :use ((:instance member-append3-1
                            (x poly)
                            (y1 (generate-polys-of-length-with-sum (1- first) 
                                                                   (polynomial-height-aux poly)
                                                                   (len poly)))
                            (y2 (mapcons first
                                         (generate-polys-of-length-with-sum (+ (- first)
                                                                               (- (car poly))
                                                                               (polynomial-height-aux (cdr poly))) 
                                                                            (+ (- first)
                                                                               (- (car poly))
                                                                               (polynomial-height-aux (cdr poly)))
                                                                            (len (cdr poly)))))
                            (y3 (mapcons (- first)
                                         (generate-polys-of-length-with-sum (+ (- first)
                                                                               (- (car poly))
                                                                               (polynomial-height-aux (cdr poly))) 
                                                                            (+ (- first)
                                                                               (- (car poly))
                                                                               (polynomial-height-aux (cdr poly)))
                                                                            (len (cdr poly)))))))
           )
          ("Subgoal *1/2.8"
           :use ((:instance member-append3-1
                            (x poly)
                            (y1 (generate-polys-of-length-with-sum (1- first) 
                                                                   (polynomial-height-aux poly)
                                                                   (len poly)))
                            (y2 (mapcons first
                                         (generate-polys-of-length-with-sum (+ (- first)
                                                                               (- (car poly))
                                                                               (polynomial-height-aux (cdr poly))) 
                                                                            (+ (- first)
                                                                               (- (car poly))
                                                                               (polynomial-height-aux (cdr poly)))
                                                                            (len (cdr poly)))))
                            (y3 (mapcons (- first)
                                         (generate-polys-of-length-with-sum (+ (- first)
                                                                               (- (car poly))
                                                                               (polynomial-height-aux (cdr poly))) 
                                                                            (+ (- first)
                                                                               (- (car poly))
                                                                               (polynomial-height-aux (cdr poly)))
                                                                            (len (cdr poly)))))))
           )
          ("Subgoal *1/2.7"
           :use ((:instance member-append3-1
                            (x poly)
                            (y1 (generate-polys-of-length-with-sum (1- first) 
                                                                   (polynomial-height-aux poly)
                                                                   (len poly)))
                            (y2 (mapcons first
                                         (generate-polys-of-length-with-sum (+ (- first)
                                                                               (- (car poly))
                                                                               (polynomial-height-aux (cdr poly))) 
                                                                            (+ (- first)
                                                                               (- (car poly))
                                                                               (polynomial-height-aux (cdr poly)))
                                                                            (len (cdr poly)))))
                            (y3 (mapcons (- first)
                                         (generate-polys-of-length-with-sum (+ (- first)
                                                                               (- (car poly))
                                                                               (polynomial-height-aux (cdr poly))) 
                                                                            (+ (- first)
                                                                               (- (car poly))
                                                                               (polynomial-height-aux (cdr poly)))
                                                                            (len (cdr poly)))))))
           )
          ("Subgoal *1/2.3"
           :use ((:instance member-mapcons 
                            (poly poly)
                            (polys (generate-polys-of-length-with-sum (+ (- first)
                                                                         (car poly)
                                                                         (polynomial-height-aux (cdr poly))) 
                                                                      (+ (- first)
                                                                         (car poly)
                                                                         (polynomial-height-aux (cdr poly)))
                                                                      (len (cdr poly)))))
                 (:instance member-append3-2
                            (x poly)
                            (y1 (generate-polys-of-length-with-sum (1- first) 
                                                                   (polynomial-height-aux poly)
                                                                   (len poly)))
                            (y2 (mapcons first
                                         (generate-polys-of-length-with-sum (+ (- first)
                                                                               (car poly)
                                                                               (polynomial-height-aux (cdr poly))) 
                                                                            (+ (- first)
                                                                               (car poly)
                                                                               (polynomial-height-aux (cdr poly)))
                                                                            (len (cdr poly)))))
                            (y3 (mapcons (- first)
                                         (generate-polys-of-length-with-sum (+ (- first)
                                                                               (car poly)
                                                                               (polynomial-height-aux (cdr poly))) 
                                                                            (+ (- first)
                                                                               (car poly)
                                                                               (polynomial-height-aux (cdr poly)))
                                                                            (len (cdr poly)))))))
           :in-theory (disable member-mapcons))
          ("Subgoal *1/1"
           :use ((:instance member-mapcons 
                            (poly poly)
                            (polys (generate-polys-of-length-with-sum sum sum (1- length))))
                 )
           :in-theory (disable member-mapcons))
          )
  )

(defun generate-polys-with-height-and-max-length-induction-hint (height length poly)
  (if (and (integerp length) (< 1 length))
      (append (generate-polys-with-height-and-max-length-induction-hint height (1- length) (cdr poly))
              (generate-polys-of-length-with-sum (+ height (- length) 2) (+ height (- length) 2) length))
    poly))

(defthmd member-append2-1
  (implies (member x y1)
           (member x (append y1 y2))))

(defthmd member-append2-2
  (implies (member x y2)
           (member x (append y1 y2))))

(defthm lists-with-height-and-max-length-valid
  (implies (and (consp poly)
                (consp (cdr poly))
                (integer-polynomial-p poly)
                (equal height (polynomial-height poly))
                (integerp length)
                (<= 1 length)
                (<= (length poly) length))
           (member poly (generate-polys-with-height-and-max-length height length)))
  :hints (("Goal" :do-not-induct t
           :induct (generate-polys-with-height-and-max-length height length)
           :in-theory (disable generate-polys-of-length-with-sum))
          ("Subgoal *1/1.4"
           :use ((:instance lists-of-length-with-sum-valid
                            (poly poly)
                            (first (+ (- (car poly))
                                      (polynomial-height-aux (cdr poly))))
                            (sum (+ (- (car poly))
                                    (polynomial-height-aux (cdr poly))))
                            (length length))
                 (:instance member-append2-2
                            (x poly)
                            (y1 (generate-polys-with-height-and-max-length
                                 (+ -2 length (- (car poly))
                                    (polynomial-height-aux (cdr poly)))
                                 (+ -1 length)))
                            (y2 (generate-polys-of-length-with-sum (+ (- (car poly))
                                                                      (polynomial-height-aux (cdr poly)))
                                                                   (+ (- (car poly))
                                                                      (polynomial-height-aux (cdr poly)))
                                                                   length)))
                 )
           :in-theory (disable lists-of-length-with-sum-valid
                               generate-polys-of-length-with-sum))
          ("Subgoal *1/1.3"
           :use ((:instance lists-of-length-with-sum-valid
                            (poly poly)
                            (first (+ (car poly)
                                      (polynomial-height-aux (cdr poly))))
                            (sum (+ (car poly)
                                    (polynomial-height-aux (cdr poly))))
                            (length length))
                 (:instance member-append2-2
                            (x poly)
                            (y1 (generate-polys-with-height-and-max-length
                                 (+ -2 length (car poly)
                                    (polynomial-height-aux (cdr poly)))
                                 (+ -1 length)))
                            (y2 (generate-polys-of-length-with-sum (+ (car poly)
                                                                      (polynomial-height-aux (cdr poly)))
                                                                   (+ (car poly)
                                                                      (polynomial-height-aux (cdr poly)))
                                                                   length)))
                 )
           :in-theory (disable lists-of-length-with-sum-valid
                               generate-polys-of-length-with-sum))
          ("Subgoal *1/1.2"
           :use ((:instance member-append2-1
                            (x poly)
                            (y1 (generate-polys-with-height-and-max-length
                                 (+ -1 (len (cdr poly)) (- (car poly))
                                    (polynomial-height-aux (cdr poly)))
                                 (+ -1 length)))
                            (y2 (generate-polys-of-length-with-sum (+ 1 (- length)
                                                                      (- (car poly))
                                                                      (len (cdr poly))
                                                                      (polynomial-height-aux (cdr poly)))
                                                                   (+ 1 (- length)
                                                                      (- (car poly))
                                                                      (len (cdr poly))
                                                                      (polynomial-height-aux (cdr poly)))
                                                                   length)))
                 )
           :in-theory (disable lists-of-length-with-sum-valid
                               generate-polys-of-length-with-sum))
          ("Subgoal *1/1.1"
           :use ((:instance member-append2-1
                            (x poly)
                            (y1 (generate-polys-with-height-and-max-length
                                 (+ -1 (len (cdr poly)) (car poly)
                                    (polynomial-height-aux (cdr poly)))
                                 (+ -1 length)))
                            (y2 (generate-polys-of-length-with-sum (+ 1 (- length)
                                                                      (car poly)
                                                                      (len (cdr poly))
                                                                      (polynomial-height-aux (cdr poly)))
                                                                   (+ 1 (- length)
                                                                      (car poly)
                                                                      (len (cdr poly))
                                                                      (polynomial-height-aux (cdr poly)))
                                                                   length)))
                 )
           :in-theory (disable lists-of-length-with-sum-valid
                               generate-polys-of-length-with-sum))))

(defthm generate-polys-with-height-valid
  (implies (and (integer-polynomial-p poly)
                (non-trivial-polynomial-p poly))
           (member poly (generate-polys-with-height (polynomial-height poly))))
  :hints (("Goal"
           :use ((:instance lists-with-height-and-max-length-valid
                            (poly poly)
                            (length (1+ (polynomial-height poly)))
                            (height (polynomial-height poly)))
                 (:instance integer-height-of-integer-polynomials)
                 (:instance integer-height-of-integer-polynomials-lemma-stronger))
           :in-theory (disable lists-with-height-and-max-length-valid
                               integer-height-of-integer-polynomials
                               integer-height-of-integer-polynomials-lemma-stronger
                               generate-polys-with-height-and-max-length
                               polynomial-height-aux
                               integer-polynomial-p
                               integer-height-of-integer-polynomials-aux))))



(defun nth-real (n list)
  (if (endp list)
      0
    (if (zp n)
        (car list)
      (nth-real (1- n) (cdr list)))))

(defun pad-list (n list)
  (if (zp n)
      nil
    (cons (nth-real 0 list)
          (pad-list (1- n) (cdr list)))))

(defthm member-pad-list
  (implies (and (integerp n)
                (<= (length list) n)
                (member x list))
           (member x (pad-list n list))))

(defthm nth-pad-list
  (implies (and (integerp n)
                (<= (length list) n)
                (natp m)
                (< m (length list))
                (consp list))
           (equal (nth m (pad-list n list))
                  (nth m list))))

(defthm len-pad-list
  (implies (natp n)
           (equal (len (pad-list n list))
                  n)))

(in-theory (disable pad-list))

(defun enumerate-roots-of-polys (polys)
  (if (consp polys)
      (append (pad-list (length (car polys))
                        (find-roots-of-poly (car polys)))
              (enumerate-roots-of-polys (cdr polys)))
    nil))

(defthm len-append
  (equal (len (append x y))
         (+ (len x) (len y))))

(defthm length-enumerate-roots-of-polys-lemma
  (implies (and (consp poly)
                (member poly polys))
           (<= (length poly)
               (length (enumerate-roots-of-polys polys)))))

(defthm exists-poly-with-given-height
  (implies (and (integerp height)
                (<= 1 height))
           (equal (polynomial-height (list 0 height)) height)))

(defthm find-roots-of-poly-fits-at-least-one-poly
  (implies (and (integerp height)
                (<= 1 height))
           (consp (generate-polys-with-height height)))
  :hints (("Goal" 
           :use ((:instance exists-poly-with-given-height)
                 (:instance generate-polys-with-height-valid (poly (list 0 height))))
           :in-theory (disable exists-poly-with-given-height
                               generate-polys-with-height-valid
                               generate-polys-with-height))))


(defun enumerate-roots-of-polys-of-height (height)
  (enumerate-roots-of-polys (generate-polys-with-height height)))

(defthm length-enumerate-roots-of-polys-of-height
  (implies (and (integerp height)
                (<= 1 height))
           (<= 2 (length (enumerate-roots-of-polys-of-height height))))
  :hints (("Goal"
           :use ((:instance length-enumerate-roots-of-polys-lemma
                            (poly (list 0 height))
                            (polys (generate-polys-with-height height)))
                 (:instance exists-poly-with-given-height)
                 (:instance generate-polys-with-height-valid
                            (poly (list 0 height))))
           :in-theory (disable length-enumerate-roots-of-polys-lemma
                               exists-poly-with-given-height
                               generate-polys-with-height-valid
                               generate-polys-with-height))))


(defthm enumerate-roots-valid-lemma
  (implies (and (non-trivial-polynomial-p poly)
                (polynomial-root-p poly root)
                (member poly polys))
           (member root (enumerate-roots-of-polys polys)))
  :hints (("Subgoal *1/2"
           :use ((:instance member-append2-2
                            (x root)
                            (y1 (PAD-LIST (length (car polys))
                                          (FIND-ROOTS-OF-POLY (car polys))))
                            (y2 (ENUMERATE-ROOTS-OF-POLYS (CDR POLYS))))))
          ("Subgoal *1/1"
           :use ((:instance member-append2-1
                            (x root)
                            (y1 (PAD-LIST (length (car polys))
                                          (FIND-ROOTS-OF-POLY (car polys))))
                            (y2 (ENUMERATE-ROOTS-OF-POLYS (CDR POLYS))))
                 (:instance member-pad-list
                            (x root)
                            (n (length (car polys)))
                            (list (FIND-ROOTS-OF-POLY (car polys))))
                 (:instance length-find-roots-poly
                            (poly (car polys)))
                 (:instance choose-n-roots-poly-contains-all-roots
                            (x root)
                            (poly (car polys))))
           :in-theory (disable member-pad-list
                               length-find-roots-poly
                               choose-n-roots-poly-contains-all-roots))))


(defthm enumerate-roots-valid
  (implies (and (integer-polynomial-p poly)
                (non-trivial-polynomial-p poly)
                (polynomial-root-p poly root))
           (member root (enumerate-roots-of-polys-of-height (polynomial-height poly))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance enumerate-roots-valid-lemma
                            (root root)
                            (poly poly)
                            (polys (generate-polys-with-height (polynomial-height poly)))))
           :in-theory (disable polynomial-height
                               generate-polys-with-height))))

(defun enumerate-roots-of-polys-up-to-height (height)
  (if (zp height)
      nil
    (append (enumerate-roots-of-polys-up-to-height (1- height))
            (enumerate-roots-of-polys-of-height height))))

(defthm enumerate-roots-up-to-height-valid
  (implies (and (integer-polynomial-p poly)
                (non-trivial-polynomial-p poly)
                (polynomial-root-p poly root)
                (integerp height)
                (<= (polynomial-height poly) height))
           (member root (enumerate-roots-of-polys-up-to-height height)))
  :hints (("Goal" :do-not-induct t
           :induct (enumerate-roots-of-polys-up-to-height height)
           :in-theory (disable enumerate-roots-of-polys-of-height
                               polynomial-root-p
                               non-trivial-polynomial-p
                               integer-polynomial-p
                               polynomial-height))
          ("Subgoal *1/2"
           :use ((:instance (:instance member-append2-1
                            (x root)
                            (y1 (ENUMERATE-ROOTS-OF-POLYS-UP-TO-HEIGHT (+ -1 HEIGHT)))
                            (y2 (ENUMERATE-ROOTS-OF-POLYS-OF-HEIGHT HEIGHT))))
                 (:instance (:instance member-append2-2
                            (x root)
                            (y1 (ENUMERATE-ROOTS-OF-POLYS-UP-TO-HEIGHT (+ -1 (POLYNOMIAL-HEIGHT POLY))))
                            (y2 (ENUMERATE-ROOTS-OF-POLYS-OF-HEIGHT (POLYNOMIAL-HEIGHT POLY)))))
                 (:instance enumerate-roots-valid))
           :in-theory (disable member-append2-1 
                               member-append2-2 
                               enumerate-roots-valid
                               polynomial-root-p
                               non-trivial-polynomial-p
                               integer-polynomial-p
                               polynomial-height
                               enumerate-roots-of-polys-of-height))))


(defthm nth-append
  (implies (natp n)
           (equal (nth n (append l1 l2))
                  (if (< n (len l1))
                      (nth n l1)
                    (nth (- n (len l1)) l2)))))

(defthm nth-append-2
  (implies (and (natp n)
                (< n (+ (len l1) (len l2)))
                (<= (len l1) n))
           (equal (nth n (append l1 l2))
                  (nth (- n (len l1)) l2))))

(defthmd len-enumerate-roots-up-to-height-monotonic
  (implies (and (integerp height1)
                (integerp height2)
                (<= 0 height1)
                (<= height1 height2))
           (<= (len (enumerate-roots-of-polys-up-to-height height1))
               (len (enumerate-roots-of-polys-up-to-height height2))))
  :hints (("Goal"
           :induct (enumerate-roots-of-polys-up-to-height height2)
           :in-theory (disable enumerate-roots-of-polys-of-height))))

(defthm enumerate-roots-up-to-height-monotonic
  (implies (and (integerp height1)
                (integerp height2)
                (<= 0 height1)
                (<= height1 height2)
                (natp n)
                (< n (length (enumerate-roots-of-polys-up-to-height height1))))
           (equal (nth n (enumerate-roots-of-polys-up-to-height height2))
                  (nth n (enumerate-roots-of-polys-up-to-height height1))))
  :hints (("Goal"
           :induct (enumerate-roots-of-polys-up-to-height height2)
           :in-theory (disable enumerate-roots-of-polys-of-height))
          ("Subgoal *1/2.1"
           :use ((:instance len-enumerate-roots-up-to-height-monotonic
                            (height1 height1)
                            (height2 (1- height2)))))))
                       
(defun get-index-in-list (x list)
  (if (consp list)
      (if (equal x (car list))
          0
        (1+ (get-index-in-list x (cdr list))))
    0))

(defthm nth-get-index-in-list
  (implies (member x list)
           (equal (nth (get-index-in-list x list) list) x)))

(defthm get-index-in-list-upper-bound
  (implies (member x list)
           (< (get-index-in-list x list) (len list))))

(defthm nth-enumerate-roots-returns-root
  (implies (and (integer-polynomial-p poly)
                (non-trivial-polynomial-p poly)
                (polynomial-root-p poly root))
           (equal (nth (get-index-in-list root (enumerate-roots-of-polys-up-to-height (polynomial-height poly)))
                       (enumerate-roots-of-polys-up-to-height (polynomial-height poly)))
                  root))
  :hints (("Goal" :do-not-induct t
           :use ((:instance nth-get-index-in-list
                            (x root)
                            (list (enumerate-roots-of-polys-up-to-height (polynomial-height poly))))
                 (:instance enumerate-roots-up-to-height-valid
                            (poly poly)
                            (root root)
                            (height (polynomial-height poly))))
           :in-theory (disable enumerate-roots-up-to-height-valid
                               nth-get-index-in-list
                               enumerate-roots-of-polys-up-to-height))))
                               
(defun get-index-in-last-list (root poly)
  (+ (len (enumerate-roots-of-polys-up-to-height (1- (polynomial-height poly))))
     (get-index-in-list root (enumerate-roots-of-polys-of-height (polynomial-height poly)))))

(defthm get-index-in-last-list-upper-bound
  (implies (and (integer-polynomial-p poly)
                (non-trivial-polynomial-p poly)
                (polynomial-root-p poly root))
           (< (get-index-in-last-list root poly)
              (len (enumerate-roots-of-polys-up-to-height (polynomial-height poly)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance get-index-in-list-upper-bound
                            (x root)
                            (list (enumerate-roots-of-polys-of-height (polynomial-height poly))))
                 (:instance enumerate-roots-valid
                            (poly poly)
                            (root root))
                 )
           :in-theory (disable get-index-in-list-upper-bound
                               enumerate-roots-valid
                               enumerate-roots-of-polys-of-height
                               polynomial-height
                               integer-polynomial-p
                               non-trivial-polynomial-p))))

(defthm nth-last-list-enumerate-roots-returns-root
  (implies (and (integer-polynomial-p poly)
                (non-trivial-polynomial-p poly)
                (polynomial-root-p poly root))
           (equal (nth (get-index-in-last-list root poly)
                       (enumerate-roots-of-polys-up-to-height (polynomial-height poly)))
                  root))
  :hints (("Goal" :do-not-induct t
           :use ((:instance nth-get-index-in-list
                            (x root)
                            (list (enumerate-roots-of-polys-of-height (polynomial-height poly))))
                 (:instance enumerate-roots-valid
                            (poly poly)
                            (root root)))
           :in-theory (disable enumerate-roots-valid
                               nth-get-index-in-list
                               enumerate-roots-of-polys-of-height))))


(defthm length-enumerate-roots-of-polys-up-to-height
  (implies (natp height)
           (<= (* 2 height)
               (length (enumerate-roots-of-polys-up-to-height height))))
  :hints (("Goal"
           :in-theory (disable enumerate-roots-of-polys-of-height))
          ("Subgoal *1/3"
           :use ((:instance length-enumerate-roots-of-polys-of-height))
           :in-theory (disable length-enumerate-roots-of-polys-of-height
                               enumerate-roots-of-polys-of-height))))

(defthm index-in-last-list-lower-bound
  (implies (and (integer-polynomial-p poly)
                (non-trivial-polynomial-p poly))
           (<= (* 2 (1- (polynomial-height poly)))
               (get-index-in-last-list root poly)))
  :hints (("Goal"
           :use ((:instance length-enumerate-roots-of-polys-up-to-height
                            (height (1- (polynomial-height poly))))
                 (:instance integer-height-of-integer-polynomials))
           :in-theory (disable length-enumerate-roots-of-polys-up-to-height
                               integer-height-of-integer-polynomials
                               enumerate-roots-of-polys-of-height
                               enumerate-roots-of-polys-up-to-height
                               get-index-in-list
                               polynomial-height))))


(defthmd useful-natp-inequality
  (implies (posp h)
           (<= h (1- (* 2 h)))))

(defthm get-index-in-last-list-at-least-height
  (implies (and (integer-polynomial-p poly)
                (non-trivial-polynomial-p poly)
                (polynomial-root-p poly root))
           (<= (polynomial-height poly)
               (1+ (get-index-in-last-list root poly))))
  :hints (("Goal"
           :use ((:instance index-in-last-list-lower-bound)
                 (:instance useful-natp-inequality
                            (h (polynomial-height poly))))
           :in-theory (disable index-in-last-list-lower-bound
                               useful-natp-inequality
                               integer-polynomial-p
                               non-trivial-polynomial-p
                               polynomial-height
                               get-index-in-last-list))))

(defthm algebraic-number-sequence-valid-lemma
  (implies (and (integer-polynomial-p poly)
                (non-trivial-polynomial-p poly)
                (polynomial-root-p poly root))
           (equal (nth (get-index-in-last-list root poly)
                       (enumerate-roots-of-polys-up-to-height (1+ (get-index-in-last-list root poly))))
                  root))
  :hints (("Goal" :do-not-induct t
           :use ((:instance nth-last-list-enumerate-roots-returns-root)
                 (:instance enumerate-roots-up-to-height-monotonic
                            (n (get-index-in-last-list root poly))
                            (height1 (polynomial-height poly))
                            (height2 (1+ (get-index-in-last-list root poly))))
                 (:instance get-index-in-last-list-at-least-height))
           :in-theory (disable nth-last-list-enumerate-roots-returns-root
                               enumerate-roots-up-to-height-monotonic
                               get-index-in-last-list-at-least-height
                               enumerate-roots-of-polys-up-to-height
                               get-index-in-last-list
                               polynomial-height
                               non-trivial-polynomial-p
                               polynomial-root-p))))

(defun algebraic-number-sequence (idx)
  (if (posp idx)
      (nth (1- idx) (enumerate-roots-of-polys-up-to-height idx))
    0))
                            
(defthm algebraic-number-sequence-valid
  (implies (and (integer-polynomial-p poly)
                (non-trivial-polynomial-p poly)
                (polynomial-root-p poly root))
           (equal (algebraic-number-sequence (1+ (get-index-in-last-list root poly)))
                  root))
  :hints (("Goal"
           :use ((:instance algebraic-number-sequence-valid-lemma))
           :in-theory (disable algebraic-number-sequence-valid-lemma
                               enumerate-roots-of-polys-up-to-height
                               get-index-in-last-list))))
                               
(defthm algebraic-number-sequence-enumerates-weak-algebraic-numbers
  (implies (weak-algebraic-numberp x)
           (equal (algebraic-number-sequence (1+ (get-index-in-last-list x (weak-algebraic-numberp-witness x))))
                  x))
  :hints (("Goal"
           :use ((:instance algebraic-number-sequence-valid
                            (root x)
                            (poly weak-algebraic-numberp-witness)))
           :in-theory (disable algebraic-number-sequence
                               get-index-in-last-list
                               integer-polynomial-p
                               non-trivial-polynomial-p
                               polynomial-root-p))))

(defthm algebraic-number-sequence-enumerates-algebraic-numbers
  (implies (algebraic-numberp x)
           (equal (algebraic-number-sequence (1+ (get-index-in-last-list x (weak-algebraic-numberp-witness x))))
                  x))
  :hints (("Goal"
           :use ((:instance algebraic-number-sequence-enumerates-weak-algebraic-numbers))
           :in-theory (disable algebraic-number-sequence
                               get-index-in-last-list
                               integer-polynomial-p
                               non-trivial-polynomial-p
                               polynomial-root-p))))

                            
(defun-sk exists-in-algebraic-number-sequence (x)
  (exists i
          (and (posp i)
               (equal (algebraic-number-sequence i) x))))

(defun-sk exists-in-interval-but-not-in-algebraic-number-sequence (A B)
  (exists x
          (and (realp x)
               (< A x)
               (< x B)
               (not (exists-in-algebraic-number-sequence x)))))

(defthm real-listp-choose-n-roots
  (implies (real-listp roots)
           (real-listp (choose-n-roots n poly roots))))


(defthm real-listp-find-roots-of-poly
  (real-listp (find-roots-of-poly poly))
  :hints (("Goal"
           :expand ((find-roots-of-poly poly)))))

(defthm real-listp-pad-list
  (implies (real-listp list)
           (real-listp (pad-list n list)))
  :hints (("Goal"
           :in-theory (enable pad-list))))

(defthm real-listp-append
  (implies (and (real-listp x)
                (real-listp y))
           (real-listp (append x y))))

(defthm real-listp-enumerate-roots-of-polys
  (real-listp (enumerate-roots-of-polys polys)))

(defthm real-listp-enumerate-roots-of-polys-of-height
  (real-listp (enumerate-roots-of-polys-of-height height)))

(defthm real-listp-enumerate-roots-of-polys-up-to-height
  (real-listp (enumerate-roots-of-polys-up-to-height height)))

(defthm real-nth-of-real-listp
  (implies (and (real-listp list)
                (natp n)
                (< n (length list)))
           (realp (nth n list))))


(defthm realp-algebraic-number-sequence
  (realp (algebraic-number-sequence idx))
  :hints (("Goal"
           :use ((:instance real-nth-of-real-listp
                            (n (1- idx))
                            (list (enumerate-roots-of-polys-up-to-height idx)))
                 (:instance length-enumerate-roots-of-polys-up-to-height
                            (height idx))
                 )
           :in-theory (disable real-nth-of-real-listp
                               length-enumerate-roots-of-polys-up-to-height
                               enumerate-roots-of-polys-up-to-height))))


(encapsulate
 ()

 (local (include-book "reals-are-uncountable-1"))

 (defthm existence-of-trascendental-numbers-lemma
   (exists-in-interval-but-not-in-algebraic-number-sequence 0 1)
   :hints (("Goal"
            :use ((:functional-instance reals-are-not-countable
                                        (seq algebraic-number-sequence)
                                        (a (lambda () 0))
                                        (b (lambda () 1))
                                        (exists-in-sequence exists-in-algebraic-number-sequence)
                                        (exists-in-sequence-witness exists-in-algebraic-number-sequence-witness)
                                        (exists-in-interval-but-not-in-sequence exists-in-interval-but-not-in-algebraic-number-sequence)
                                        (exists-in-interval-but-not-in-sequence-witness exists-in-interval-but-not-in-algebraic-number-sequence-witness))))
           ))
 )


(defthm witness-not-in-algebraic-number-sequence
  (and (realp (exists-in-interval-but-not-in-algebraic-number-sequence-witness 0 1))
       (< 0 (exists-in-interval-but-not-in-algebraic-number-sequence-witness 0 1))
       (< (exists-in-interval-but-not-in-algebraic-number-sequence-witness 0 1) 1)
       (not (exists-in-algebraic-number-sequence (exists-in-interval-but-not-in-algebraic-number-sequence-witness 0 1))))
  :hints (("Goal"
           :use ((:instance existence-of-trascendental-numbers-lemma))
           :in-theory (disable existence-of-trascendental-numbers-lemma
                               algebraic-number-sequence))))

(defthm not-exists-in-algebraic-number-sequence-forward
  (implies (and (posp i)
                (realp x)
                (< 0 x)
                (< x 1)
                (not (exists-in-algebraic-number-sequence x)))
           (not (equal (algebraic-number-sequence i) x))) 
  :hints (("Goal"
           :in-theory (disable algebraic-number-sequence))))

(defthm witness-not-an-algebraic-number
  (not (algebraic-numberp (exists-in-interval-but-not-in-algebraic-number-sequence-witness 0 1)))
  :hints (("Goal"
           :use ((:instance witness-not-in-algebraic-number-sequence)
                 (:instance not-exists-in-algebraic-number-sequence-forward
                            (x (exists-in-interval-but-not-in-algebraic-number-sequence-witness 0 1))
                            (i (1+ (get-index-in-last-list (exists-in-interval-but-not-in-algebraic-number-sequence-witness 0 1)
                                                           (weak-algebraic-numberp-witness
                                                            (exists-in-interval-but-not-in-algebraic-number-sequence-witness 0 1))))))
                 (:instance algebraic-number-sequence-enumerates-algebraic-numbers
                            (x (exists-in-interval-but-not-in-algebraic-number-sequence-witness 0 1))))
           :in-theory (disable witness-not-in-algebraic-number-sequence
                               not-exists-in-algebraic-number-sequence-forward
                               algebraic-number-sequence-enumerates-algebraic-numbers
                               algebraic-number-sequence
                               algebraic-numberp
                               exists-in-algebraic-number-sequence
                               enumerate-roots-of-polys-of-height
                               get-index-in-last-list
                               ))))

(defun-sk exists-transcendental-number ()
  (exists x
          (and (realp x)
               (not (algebraic-numberp x)))))

(defthm existence-of-transcendental-numbers
  (exists-transcendental-number)
  :hints (("Goal"
           :use ((:instance exists-transcendental-number-suff
                            (x (exists-in-interval-but-not-in-algebraic-number-sequence-witness 0 1))))
           :in-theory (disable exists-transcendental-number-suff
                               algebraic-numberp))))
