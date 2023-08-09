;;; fng.scm
;;;
;;; The strange fixed point we discussed in class:
;;; lambda f g.f(g(f(g(g(f(g(g(g(...
;;;
;;; Programmer: Mayer Goldberg, 2013

(define c1 (lambda (x) x))

(define succ
  (lambda (n)
    (lambda (s)
      (lambda (z)
	(s ((n s) z))))))

(define the-elegant-solution-by-michal-converted-to-applicative-order
  (lambda (f g)
    (((lambda (x) (x x))
      (lambda (x)
	(lambda (h)
	  (f (h (lambda s
		  (apply ((x x) (lambda (x) (g (h x))))
			 s)))))))
     g)))
     
(define my-solution
  (((lambda (x) (x x))
    (lambda (x)
      (lambda (n)
	(lambda (f g)
	  (f ((n g) (lambda s (apply (((x x) (succ n)) f g) s))))))))
   c1))

(define trace-f
  (lambda (x)
    (lambda (n)
      (string-append
       "(f "
       (x n)
       ")"))))

(define trace-g
  (lambda (x)
    (lambda (n)
      (if (zero? n)
	  "... "
	  (string-append
	   "(g "
	   (x (- n 1))
	   ")")))))

(define test
  (lambda (n)
    (let ((x1 ((my-solution trace-f trace-g) n))
	  (x2 ((the-elegant-solution-by-michal-converted-to-applicative-order
		trace-f trace-g) n)))
      `((my solution: ,x1)
	(michals solution: ,x2)
	(both solutions are ,(if (string=? x1 x2) 'equal 'unequal))))))

;;; How to run the code:
;;;
;;; > (test 10)
;;; ((my solution:
;;;      "(f (g (f (g (g (f (g (g (g (f (g (g (g (g (f ... )))))))))))))))")
;;;  (michals solution:
;;;      "(f (g (f (g (g (f (g (g (g (f (g (g (g (g (f ... )))))))))))))))")
;;;  (both solutions are equal))
;;;
;;; When you eval (test n), n corresponds to the total number of g's...

