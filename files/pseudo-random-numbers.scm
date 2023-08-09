;;; random-monad.scm
;;; Threading a computation with a seed
;;;
;;; Programmer: Mayer Goldberg, 2013

(define return (lambda (a) (lambda (b) (lambda (c) (c a b)))))
(define pipe (lambda (a b) (lambda (c) ((a c) (lambda (x y) ((b x) y))))))

(define sequence
  (letrec ((loop
	    (lambda (m fs)
	      (if (null? fs) m
		  (loop (pipe m (car fs))
			(cdr fs))))))
    (lambda fs
      (loop start-here fs))))

(define start-here
  (let ((void-object (if #f #f)))
    (lambda (w)
      (lambda (u)
	(u void-object w)))))
;;;
(define show
  (lambda (v w)
    `((value: ,v)
      (prng-seed: ,w))))

(define with (lambda (s f) (apply f s)))

(define *initial-seed* 143303810838398927)

(define seed->random+seed
  (let* ((p0 373587911)
	 (p1 373587923)
	 (p0p1 (* p0 p1)))
    (letrec ((step
	      (lambda (seed)
		(list seed (remainder (* seed seed) p0p1))))
	     (run
	      (lambda (n m k seed)
		(if (zero? n)
		    (list (exact->inexact (/ m k)) seed)
		    (with (step seed)
		      (lambda (r seed)
			(run (- n 1)
			     (+ r (* p0p1 m))
			     (* k p0p1)
			     seed)))))))
      (lambda (seed)
	(run 4 0 1 seed)))))

(define random-real
  (lambda (_)
    (lambda (w)
      (with (seed->random+seed w)
	(lambda (x seed)
	  (lambda (u)
	    (u x seed)))))))

(define example
  (((sequence
      random-real
      (lambda (x)
	(sequence
	  random-real
	  (lambda (y)
	    (return (list x y))))))
    *initial-seed*)
   show))