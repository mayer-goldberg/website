;;; letrec-expansion-using-y.scm
;;; Using a variadic, applicative-order, multiple fixed-point extension to
;;; Curry's fixed-point combinator for expansion of letrec...
;;;
;;; Programmer: Mayer Goldberg, 2012

(define with (lambda (s f) (apply f s)))

(define Yn
  (lambda fs
    (let ((ms (map
		  (lambda (fi)
		    (lambda ms
		      (apply fi
			     (map (lambda (mi)
				    (lambda args
				      (apply (apply mi ms) args)))
			       ms))))
		fs)))
      (apply (car ms) ms))))

(define expand-letrec
  (lambda (e)
    (with e
      (lambda (_letrec ribs . exprs)
	(let* ((names `(,(gensym) ,@(map car ribs)))
	       (fs `((lambda ,names ,@exprs)
		     ,@(map (lambda (rib) `(lambda ,names ,(cadr rib)))
			 ribs))))
	  `(Yn ,@fs))))))

  
;;; Example: Try evaluating
;;;   (eval recursive-nonsense-1)
;;;   (eval recursive-nonsense-2)

(define recursive-nonsense-1
  (expand-letrec
   '(letrec ((even?
	      (lambda (n)
		(or (zero? n)
		    (odd? (- n 1)))))
	     (odd?
	      (lambda (n)
		(and (positive? n)
		     (even? (- n 1))))))
      (and (even? 6)
	   (odd? 9)))))

(define recursive-nonsense-2
  (expand-letrec
   '(letrec ((my-cos
	      (lambda (x)
		(if (< x 1e-6)
		    (let ((sinx (my-sin x)))
		      (sqrt (- 1.0 (square sinx))))
		    (- (square (my-cos (/ x 2.0)))
		       (square (my-sin (/ x 2.0)))))))
	     (my-sin
	      (lambda (x)
		(if (< x 1e-6)
		    x
		    (* 2.0
		       (my-sin (/ x 2.0))
		       (my-cos (/ x 2.0))))))
	     (square (lambda (x) (* x x))))
      `(the difference between this sin function and the builtin one
	    (for input 0.3) is ,(- (sin 0.3) (my-sin 0.3))))))