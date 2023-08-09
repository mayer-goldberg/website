;;; fib.scm
;;; The most efficient implementation of Fibonacci numbers uses continuations!
;;;
;;; Programmer: Mayer Goldberg, 2008

(define fib
  (lambda (n)
    (fib$ n (lambda (x1 x2 x3 x4) x1))))

(define fib$
  (lambda (n ret)
    (if (< n 2) (ret 1 1 1 0)
        (fib$ (quotient n 2)
              (lambda (x1 x2 x3 x4)
                (let ((*x2x3 (* x2 x3)))
                  (let ((z1 (+ (* x1 x1) *x2x3))
                        (z2 (+ (* x1 x3) (* x3 x4)))
                        (z3 (+ (* x1 x2) (* x2 x4)))
                        (z4 (+ *x2x3 (* x4 x4))))
                    (if (even? n) (ret z1 z2 z3 z4)
                      (ret (+ z1 z2) (+ z3 z4) z1 z3)))))))))
