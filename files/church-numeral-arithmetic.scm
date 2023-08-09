;;; church.scm
;;; Church numerals
;;;
;;; Programmer: Mayer Goldberg, 2008

(define c0
  (lambda (s)
    (lambda (z) z)))

(define succ
  (lambda (n)
    (lambda (s)
      (lambda (z)
	(s ((n s) z))))))

(define integer->church
  (lambda (n)
    (if (zero? n) c0
	(let ((cn-1 (integer->church (- n 1))))
	  (succ cn-1)))))

(define church->integer
  (let ((add1 (lambda (n) (+ n 1))))
    (lambda (cn)
      ((cn add1) 0))))

(define c1 (succ c0))

(define alt-succ
  (lambda (n)
    (lambda (s)
      (lambda (z)
	((n s) (s z))))))

(define add
  (lambda (a)
    (lambda (b)
      ((a succ) b))))

(define alt-add
  (lambda (a)
    (lambda (b)
      (lambda (s)
	(lambda (z)
	  ((a s) ((b s) z)))))))

(define mul
  (lambda (a)
    (lambda (b)
      ((b (add a)) c0))))

(define alt-mul
  (lambda (a)
    (lambda (b)
      (lambda (s)
	(lambda (z)
	  ((a (b s)) z))))))

(define pow
  (lambda (a)
    (lambda (b)
      ((b (mul a)) c1))))

(define alt-pow
  (lambda (a)
    (lambda (b)
      (b a))))

(define pair
  (lambda (a)
    (lambda (b)
      (lambda (x)
	((x a) b)))))

(define pi12
  (lambda (p)
    (p (lambda (a)
	 (lambda (b) a)))))

(define pi22
  (lambda (p)
    (p (lambda (a)
	 (lambda (b) b)))))

(define fact #f)
(define fib #f)
(define pred #f)

(define fact
  (lambda (cn)
    (pi22
     ((cn (lambda (p)
	    ((pair (succ (pi12 p)))
	     ((mul (pi12 p))
	      (pi22 p)))))
      ((pair c1) c1)))))

(define fib
  (lambda (cn)
    (pi22
     ((cn (lambda (p)
	    ((pair (pi22 p))
	     ((add (pi12 p))
	      (pi22 p)))))
      ((pair c0) c1)))))

(define pred
  (lambda (cn)
    (pi22
     ((cn (lambda (p)
	    ((pair (succ (pi12 p)))
	     (pi12 p))))
      ((pair c0) c0)))))

(define true
  (lambda (x)
    (lambda (y) x)))

(define false
  (lambda (x)
    (lambda (y) y)))

(define neg
  (lambda (a)
    ((a false) true)))

(define conj
  (lambda (a)
    (lambda (b)
      ((a b) false))))

(define disj
  (lambda (a)
    (lambda (b)
      ((a true) b))))

;;; testing the results

(define curried-apply
  (lambda (f s)
    (if (null? s) f
	(curried-apply (f (car s)) (cdr s)))))

(define test-arith
  (lambda (f input output)
    (= output
       (church->integer
	(curried-apply f (map integer->church input))))))

(define test
  (lambda ()
    (and
     (test-arith succ '(0) 1)
     (test-arith succ '(5) 6)
     (test-arith alt-succ '(5) 6)
     (test-arith add '(2 3) 5)
     (test-arith alt-add '(2 3) 5)
     (test-arith mul '(2 3) 6)
     (test-arith alt-mul '(4 5) 20)
     (test-arith pow '(2 3) 8)
     (test-arith alt-pow '(3 4) 81)
     (test-arith pred '(0) 0)
     (test-arith pred '(5) 4)
     (test-arith fact '(0) 1)
     (test-arith fact '(5) 120)
     (test-arith fib '(10) 89)
     )))
