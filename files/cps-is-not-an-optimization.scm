;;; cps-is-not-an-optimization.scm
;;;
;;; Programmer: Mayer Goldberg, 2009

(define fib
  (lambda (n)
    (if (< n 2) n
	(+ (fib (- n 1))
	   (fib (- n 2))))))

(define fib$
  (lambda (n k)
    (if (< n 2) (k n)
	(fib$ (- n 1)
	      (lambda (x)
		(fib$ (- n 2)
		      (lambda (y)
			(k (+ x y)))))))))

;; And here are the measurements, under Petite Chez Scheme,
;; using the special form (time <expr>):

;; (time (begin (fib 30) 'ok))
;; (time (begin (fib 30) ...))
;;     61 collections
;;     1557 ms elapsed cpu time, including 1 ms collecting
;;     1733 ms elapsed real time, including 1 ms collecting
;;     64636968 bytes allocated, including 65013320 bytes reclaimed
;; ok
;; > (time (begin (fib$ 30 (lambda (x) x)) 'ok))
;; (time (begin (fib$ 30 ...) ...))
;;     141 collections
;;     1712 ms elapsed cpu time, including 5 ms collecting
;;     1778 ms elapsed real time, including 7 ms collecting
;;     150819248 bytes allocated, including 150251920 bytes reclaimed
;; ok
;; > (time (begin (fib 35) 'ok))
;; (time (begin (fib 35) ...))
;;     672 collections
;;     17293 ms elapsed cpu time, including 28 ms collecting
;;     18513 ms elapsed real time, including 28 ms collecting
;;     716834256 bytes allocated, including 716176824 bytes reclaimed
;; ok
;; > (time (begin (fib$ 35 (lambda (x) x)) 'ok))
;; (time (begin (fib$ 35 ...) ...))
;;     1570 collections
;;     18901 ms elapsed cpu time, including 75 ms collecting
;;     19890 ms elapsed real time, including 68 ms collecting
;;     1672624096 bytes allocated, including 1673046480 bytes reclaimed
;; ok