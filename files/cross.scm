;;; cross.scm
;;; Cross product mapping/filtering
;;; This routine should eliminate certain nested for-loops, and should
;;; be very convenient for deeply-nested loops
;;;
;;; Programmer: Mayer Goldberg, 2011

(define cross
  (lambda (s f . p?s)
    (let ((p? (if (null? p?s) (lambda as #t) (car p?s))))
      (letrec ((run-h
		(lambda (s args)
		  (if (null? s)
		      (let ((args (reverse args)))
			(if (apply p? args)
			    (list (apply f args))
			    '()))
		      (run-v (car s) (cdr s) args))))
	       (run-v
		(lambda (n s args)
		  (if (zero? n)
		      '()
		      (append
		       (run-h s (cons (- n 1) args))
		       (run-v (- n 1) s args))))))
	(run-h s '())))))

(define cross-list
  (lambda (s f . p?s)
    (let ((p? (if (null? p?s) (lambda as #t) (car p?s))))
      (letrec ((run-h
		(lambda (s args)
		  (if (null? s)
		      (let ((args (reverse args)))
			(if (apply p? args)
			    (list (apply f args))
			    '()))
		      (run-v (car s) (cdr s) args))))
	       (run-v
		(lambda (a s args)
		  (if (null? a)
		      '()
		      (append
		       (run-h s (cons (car a) args))
		       (run-v (cdr a) s args))))))
	(run-h s '())))))
