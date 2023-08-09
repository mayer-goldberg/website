;;; cps-examples.scm
;;; Examples of converting procedures from direct style, through
;;; CPS, arriving at the stack machine.
;;;
;;; Programmer: Mayer Goldberg, 2013

;;; This file contains several functions, each implemented
;;; differently in Scheme. To keep the code reasonably neat,
;;; each implementation is "buried" within a letrec. This is
;;; a bit different from what you saw in class, but it's neater.

;;; Each implementation is indexed by a number. Here is the key:
;;;   1 -- The function in direct style
;;;   2 -- The function in CPS
;;;   3 -- The function in CPS, with the representation
;;;        of the continuation abstracted away behind an
;;;        interface
;;;   4 -- The function in CPS, using records in place of closures
;;;   5 -- The function in CPS, using a flat structure rather than
;;;        nested records
;;;   6 -- The function in pseudo-assembly -- the stack machine

;;; Global helper procedures

(define with (lambda (s f) (apply f s)))

(define *stack* 'moshe)

(define push (lambda (x) (set! *stack* (cons x *stack*))))

(define pop
  (lambda ()
    (let ((x (car *stack*)))
      (set! *stack* (cdr *stack*))
      x)))

(define reset-stack (lambda () (set! *stack* '())))

;;; The examples start here:

;;; Factorial

(define fact-1
  (letrec ((fact
	    (lambda (n)
	      (if (zero? n)
		  1
		  (* n (fact (- n 1)))))))
    fact))

(define fact-2
  (letrec ((fact
	    (lambda (n k)
	      (if (zero? n)
		  (k 1)
		  (fact (- n 1)
			(lambda (x)
			  (k (* n x))))))))
    (lambda (n)
      (fact n (lambda (x) x)))))

(define fact-3
  (letrec ((fact
	    (lambda (n k)
	      (if (zero? n)
		  (apply-k k 1)
		  (fact (- n 1)
			(make-k-fact n k)))))
	   (apply-k (lambda (k x) (k x)))
	   (make-k-init (lambda () (lambda (x) x)))
	   (make-k-fact (lambda (n k) (lambda (x) (apply-k k (* n x))))))
    (lambda (n)
      (fact n (make-k-init)))))

(define fact-4
  (letrec ((fact
	    (lambda (n k)
	      (if (zero? n)
		  (apply-k k 1)
		  (fact (- n 1)
			(make-k-fact n k)))))
	   (apply-k
	    (lambda (k x)
	      (cond ((eq? (car k) 'k-init) x)
		    ((eq? (car k) 'k-fact)
		     (with k
		       (lambda (_ n k)
			 (apply-k k (* n x)))))
		    (else (error 'apply-k
				 "Unknown continuation")))))
	   (make-k-init (lambda () `(k-init)))
	   (make-k-fact (lambda (n k) `(k-fact ,n ,k))))
    (lambda (n)
      (fact n (make-k-init)))))

(define fact-5
  (letrec ((fact
	    (lambda (n k)
	      (if (zero? n)
		  (apply-k k 1)
		  (fact (- n 1)
			(make-k-fact n k)))))
	   (apply-k
	    (lambda (k x)
	      (cond ((eq? (car k) 'k-init) x)
		    ((eq? (car k) 'k-fact)
		     (with k
		       (lambda (_ n . k)
			 (apply-k k (* n x)))))
		    (else (error 'apply-k
				 "Unknown continuation")))))
	   (make-k-init (lambda () `(k-init)))
	   (make-k-fact (lambda (n k) `(k-fact ,n . ,k))))
    (lambda (n)
      (fact n (make-k-init)))))

(define fact-6
  ;; these are the registers
  (let ((n 'moshe)
	(k 'moshe)
	(x 'moshe))
    (letrec ((fact
	      (lambda ()
		(if (zero? n)
		    (begin
		      (set! x 1)
		      (apply-k))
		    (begin
		      (push n)
		      (push 'k-fact)
		      (set! n (- n 1))
		      (fact)))))
	     (apply-k
	      (lambda ()
		(set! k (pop))
		(cond ((eq? k 'k-init) x)
		      ((eq? k 'k-fact)
		       (set! n (pop))
		       (set! x (* n x))
		       (apply-k))
		      (else (error 'apply-k
				   "Unknown continuation"))))))
      (lambda (_n)
	(set! n _n)
	(reset-stack)
	(push 'k-init)
	(fact)))))

;;; Fibonacci

(define fib-1
  (letrec ((fib
	    (lambda (n)
	      (if (< n 2)
		  n
		  (+ (fib (- n 1))
		     (fib (- n 2)))))))
    fib))

(define fib-2
  (letrec ((fib
	    (lambda (n k)
	      (if (< n 2)
		  (k n)
		  (fib (- n 1)
		       (lambda (x)
			 (fib (- n 2)
			      (lambda (y)
				(k (+ x y))))))))))
    (lambda (n)
      (fib n (lambda (x) x)))))

(define fib-3
  (letrec ((fib
	    (lambda (n k)
	      (if (< n 2)
		  (apply-k k n)
		  (fib (- n 1)
		       (make-k-fib-1 n k)))))
	   (apply-k (lambda (k x) (k x)))
	   (make-k-init (lambda () (lambda (x) x)))
	   (make-k-fib-1
	    (lambda (n k)
	      (lambda (x)
		(fib (- n 2)
		     (make-k-fib-2 x k)))))
	   (make-k-fib-2
	    (lambda (y k)
	      (lambda (x)
		(apply-k k (+ x y))))))
    (lambda (n)
      (fib n (make-k-init)))))

(define fib-4
  (letrec ((fib
	    (lambda (n k)
	      (if (< n 2)
		  (apply-k k n)
		  (fib (- n 1)
		       (make-k-fib-1 n k)))))
	   (apply-k
	    (lambda (k x)
	      (cond ((eq? (car k) 'k-init) x)
		    ((eq? (car k) 'k-fib-1)
		     (with k
		       (lambda (_ n k)
			 (fib (- n 2)
			      (make-k-fib-2 x k)))))
		    ((eq? (car k) 'k-fib-2)
		     (with k
		       (lambda (_ y k)
			 (apply-k k (+ x y)))))
		    (else (error 'apply-k
				 "Unknown continuation")))))
	   (make-k-init (lambda () `(k-init)))
	   (make-k-fib-1 (lambda (n k) `(k-fib-1 ,n ,k)))
	   (make-k-fib-2 (lambda (y k) `(k-fib-2 ,y ,k))))
    (lambda (n)
      (fib n (make-k-init)))))

(define fib-5
  (letrec ((fib
	    (lambda (n k)
	      (if (< n 2)
		  (apply-k k n)
		  (fib (- n 1)
		       (make-k-fib-1 n k)))))
	   (apply-k
	    (lambda (k x)
	      (cond ((eq? (car k) 'k-init) x)
		    ((eq? (car k) 'k-fib-1)
		     (with k
		       (lambda (_ n . k)
			 (fib (- n 2)
			      (make-k-fib-2 x k)))))
		    ((eq? (car k) 'k-fib-2)
		     (with k
		       (lambda (_ y . k)
			 (apply-k k (+ x y)))))
		    (else (error 'apply-k
				 "Unknown continuation")))))
	   (make-k-init (lambda () `(k-init)))
	   (make-k-fib-1 (lambda (n k) `(k-fib-1 ,n . ,k)))
	   (make-k-fib-2 (lambda (y k) `(k-fib-2 ,y . ,k))))
    (lambda (n)
      (fib n (make-k-init)))))

(define fib-6
  ;; these are the registers
  (let ((n 'moshe)
	(k 'moshe)
	(x 'moshe)
	(y 'moshe))
    (letrec ((fib
	      (lambda ()
		(if (< n 2)
		    (begin
		      (set! x n)
		      (apply-k))
		    (begin
		      (push n)
		      (push 'k-fib-1)
		      (set! n (- n 1))
		      (fib)))))
	     (apply-k
	      (lambda ()
		(set! k (pop))
		(cond ((eq? k 'k-init) x)
		      ((eq? k 'k-fib-1)
		       (set! n (pop))
		       (push x)
		       (push 'k-fib-2)
		       (set! n (- n 2))
		       (fib))
		      ((eq? k 'k-fib-2)
		       (set! y (pop))
		       (set! x (+ x y))
		       (apply-k))
		      (else (error 'apply-k
				   "Unknown continuation"))))))
      (lambda (_n)
	(set! n _n)
	(reset-stack)
	(push 'k-init)
	(fib)))))

(define ack-1
  (letrec ((ack
	    (lambda (a b)
	      (cond ((zero? a) (+ b 1))
		    ((zero? b) (ack (- a 1) 1))
		    (else (ack (- a 1)
			       (ack a (- b 1))))))))
    ack))

(define ack-2
  (letrec ((ack
	    (lambda (a b k)
	      (cond ((zero? a) (k (+ b 1)))
		    ((zero? b) (ack (- a 1) 1 k))
		    (else (ack a (- b 1)
			       (lambda (x)
				 (ack (- a 1) x k))))))))
    (lambda (a b)
      (ack a b (lambda (x) x)))))

(define ack-3
  (letrec ((ack
	    (lambda (a b k)
	      (cond ((zero? a) (apply-k k (+ b 1)))
		    ((zero? b) (ack (- a 1) 1 k))
		    (else (ack a (- b 1) (make-k-ack a k))))))
	   (apply-k (lambda (k x) (k x)))
	   (make-k-init (lambda () (lambda (x) x)))
	   (make-k-ack (lambda (a k) (lambda (x) (ack (- a 1) x k)))))
    (lambda (a b)
      (ack a b (make-k-init)))))

(define ack-4
  (letrec ((ack
	    (lambda (a b k)
	      (cond ((zero? a) (apply-k k (+ b 1)))
		    ((zero? b) (ack (- a 1) 1 k))
		    (else (ack a (- b 1) (make-k-ack a k))))))
	   (apply-k
	    (lambda (k x)
	      (cond ((eq? (car k) 'k-init) x)
		    ((eq? (car k) 'k-ack)
		     (with k
		       (lambda (_ a k)
			 (ack (- a 1) x k))))
		    (else (error 'apply-k
				 "Unknown continuation")))))
	   (make-k-init (lambda () `(k-init)))
	   (make-k-ack (lambda (a k) `(k-ack ,a ,k))))
    (lambda (a b)
      (ack a b (make-k-init)))))

(define ack-5
  (letrec ((ack
	    (lambda (a b k)
	      (cond ((zero? a) (apply-k k (+ b 1)))
		    ((zero? b) (ack (- a 1) 1 k))
		    (else (ack a (- b 1) (make-k-ack a k))))))
	   (apply-k
	    (lambda (k x)
	      (cond ((eq? (car k) 'k-init) x)
		    ((eq? (car k) 'k-ack)
		     (with k
		       (lambda (_ a . k)
			 (ack (- a 1) x k))))
		    (else (error 'apply-k
				 "Unknown continuation")))))
	   (make-k-init (lambda () `(k-init)))
	   (make-k-ack (lambda (a k) `(k-ack ,a . ,k))))
    (lambda (a b)
      (ack a b (make-k-init)))))

(define ack-6
  ;; these are the registers
  (let ((a 'moshe)
	(b 'moshe)
	(k 'moshe)
	(x 'moshe))
    (letrec ((ack
	      (lambda ()
		(cond ((zero? a)
		       (set! x (+ b 1))
		       (apply-k))
		      ((zero? b)
		       (set! b 1)
		       (set! a (- a 1))
		       (ack))
		      (else
		       (push a)
		       (push 'k-ack)
		       (set! b (- b 1))
		       (ack)))))
	     (apply-k
	      (lambda ()
		(set! k (pop))
		(cond ((eq? k 'k-init) x)
		      ((eq? k 'k-ack)
		       (set! a (pop))
		       (set! b x)
		       (set! a (- a 1))
		       (ack))
		      (else (error 'apply-k
				   "Unknown continuation"))))))
      (lambda (_a _b)
	(set! a _a)
	(set! b _b)
	(reset-stack)
	(push 'k-init)
	(ack)))))

;;; Length

(define length-1
  (letrec ((length
	    (lambda (s)
	      (if (null? s)
		  0
		  (+ 1 (length (cdr s)))))))
    length))

(define length-2
  (letrec ((length
	    (lambda (s k)
	      (if (null? s)
		  (k 0)
		  (length (cdr s)
			  (lambda (x)
			    (k (+ x 1))))))))
    (lambda (s)
      (length s (lambda (x) x)))))

(define length-3
  (letrec ((length
	    (lambda (s k)
	      (if (null? s)
		  (apply-k k 0)
		  (length (cdr s)
			  (make-k-length k)))))
	   (apply-k (lambda (k x) (k x)))
	   (make-k-init (lambda () (lambda (x) x)))
	   (make-k-length (lambda (k) (lambda (x) (apply-k k (+ x 1))))))
    (lambda (s)
      (length s (make-k-init)))))

(define length-4
  (letrec ((length
	    (lambda (s k)
	      (if (null? s)
		  (apply-k k 0)
		  (length (cdr s)
			  (make-k-length k)))))
	   (apply-k 
	    (lambda (k x)
	      (cond ((eq? (car k) 'k-init) x)
		    ((eq? (car k) 'k-length)
		     (with k
		       (lambda (_ k)
			 (apply-k k (+ x 1)))))
		    (else (error 'apply-k
				 "Unknown continuation")))))
	   (make-k-init (lambda () `(k-init)))
	   (make-k-length (lambda (k) `(k-length ,k))))
    (lambda (s)
      (length s (make-k-init)))))

(define length-5
  (letrec ((length
	    (lambda (s k)
	      (if (null? s)
		  (apply-k k 0)
		  (length (cdr s)
			  (make-k-length k)))))
	   (apply-k 
	    (lambda (k x)
	      (cond ((eq? (car k) 'k-init) x)
		    ((eq? (car k) 'k-length)
		     (with k
		       (lambda (_ . k)
			 (apply-k k (+ x 1)))))
		    (else (error 'apply-k
				 "Unknown continuation")))))
	   (make-k-init (lambda () `(k-init)))
	   (make-k-length (lambda (k) `(k-length . ,k))))
    (lambda (s)
      (length s (make-k-init)))))

(define length-6
  ;; these are the registers
  (let ((s 'moshe)
	(k 'moshe)
	(x 'moshe))
    (letrec ((length
	      (lambda ()
		(if (null? s)
		    (begin
		      (set! x 0)
		      (apply-k))
		    (begin
		      (push 'k-length)
		      (set! s (cdr s))
		      (length)))))
	     (apply-k
	      (lambda ()
		(set! k (pop))
		(cond ((eq? k 'k-init) x)
		      ((eq? k 'k-length)
		       (set! x (+ x 1))
		       (apply-k))
		      (else (error 'apply-k
				   "Unknown continuation"))))))
      (lambda (_s)
	(set! s _s)
	(reset-stack)
	(push 'k-init)
	(length)))))

;;; Flat replace-first

(define replace-first-1
  (letrec ((rep
	    (lambda (a b s)
	      (cond ((null? s) '())
		    ((eq? (car s) a)
		     (cons b (cdr s)))
		    (else (cons (car s)
			    (rep a b (cdr s))))))))
    rep))

(define replace-first-2
  (letrec ((rep
	    (lambda (a b s k)
	      (cond ((null? s) (k '()))
		    ((eq? (car s) a)
		     (k (cons b (cdr s))))
		    (else (rep a b (cdr s)
			       (lambda (x)
				 (k (cons (car s) x)))))))))
    (lambda (a b s)
      (rep a b s (lambda (x) x)))))

(define replace-first-3
  (letrec ((rep
	    (lambda (a b s k)
	      (cond ((null? s) (apply-k k '()))
		    ((eq? (car s) a)
		     (apply-k k (cons b (cdr s))))
		    (else (rep a b (cdr s)
			       (make-k-rep s k))))))
	   (apply-k (lambda (k x) (k x)))
	   (make-k-init (lambda () (lambda (x) x)))
	   (make-k-rep
	    (lambda (s k)
	      (lambda (x)
		(apply-k k (cons (car s) x))))))
    (lambda (a b s)
      (rep a b s (make-k-init)))))

(define replace-first-4
  (letrec ((rep
	    (lambda (a b s k)
	      (cond ((null? s) (apply-k k '()))
		    ((eq? (car s) a)
		     (apply-k k (cons b (cdr s))))
		    (else (rep a b (cdr s)
			       (make-k-rep s k))))))
	   (apply-k
	    (lambda (k x)
	      (cond ((eq? (car k) 'k-init) x)
		    ((eq? (car k) 'k-rep)
		     (with k
		       (lambda (_ s k)
			 (apply-k k (cons (car s) x)))))
		    (else (error 'apply-k
				 "Unknown continuation")))))
	   (make-k-init (lambda () `(k-init)))
	   (make-k-rep (lambda (s k) `(k-rep ,s ,k))))
    (lambda (a b s)
      (rep a b s (make-k-init)))))

(define replace-first-5
  (letrec ((rep
	    (lambda (a b s k)
	      (cond ((null? s) (apply-k k '()))
		    ((eq? (car s) a)
		     (apply-k k (cons b (cdr s))))
		    (else (rep a b (cdr s)
			       (make-k-rep s k))))))
	   (apply-k
	    (lambda (k x)
	      (cond ((eq? (car k) 'k-init) x)
		    ((eq? (car k) 'k-rep)
		     (with k
		       (lambda (_ s . k)
			 (apply-k k (cons (car s) x)))))
		    (else (error 'apply-k
				 "Unknown continuation")))))
	   (make-k-init (lambda () `(k-init)))
	   (make-k-rep (lambda (s k) `(k-rep ,s . ,k))))
    (lambda (a b s)
      (rep a b s (make-k-init)))))

(define replace-first-6
  ;; these are the registers
  (let ((a 'moshe)
	(b 'moshe)
	(s 'moshe)
	(k 'moshe)
	(x 'moshe))
    (letrec ((rep
	      (lambda ()
		(cond ((null? s)
		       (set! x '())
		       (apply-k))
		      ((eq? (car s) a)
		       (set! x (cons b (cdr s)))
		       (apply-k))
		      (else (push s)
			    (push 'k-rep)
			    (set! s (cdr s))
			    (rep)))))
	     (apply-k
	      (lambda ()
		(set! k (pop))
		(cond ((eq? k 'k-init) x)
		      ((eq? k 'k-rep)
		       (set! s (pop))
		       (set! x (cons (car s) x))
		       (apply-k))
		      (else (error 'apply-k
				   "Unknown continuation"))))))
      (lambda (_a _b _s)
	(set! a _a)
	(set! b _b)
	(set! s _s)
	(reset-stack)
	(push 'k-init)
	(rep)))))

;;; Replacing all occurrences of a in s with b; s is a flat list

(define replace-all-flat-1
  (letrec ((rep
	    (lambda (a b s)
	      (cond ((null? s) '())
		    ((eq? (car s) a)
		     (cons b (rep a b (cdr s))))
		    (else (cons (car s) (rep a b (cdr s))))))))
    rep))

(define replace-all-flat-2
  (letrec ((rep
	    (lambda (a b s k)
	      (cond ((null? s) (k '()))
		    ((eq? (car s) a)
		     (rep a b (cdr s)
			  (lambda (x)
			    (k (cons b x)))))
		    (else (rep a b (cdr s)
			       (lambda (x)
				 (k (cons (car s) x)))))))))
    (lambda (a b s)
      (rep a b s (lambda (x) x)))))

(define replace-all-flat-3
  (letrec ((rep
	    (lambda (a b s k)
	      (cond ((null? s) (apply-k k '()))
		    ((eq? (car s) a)
		     (rep a b (cdr s)
			  (make-k-rep-1 b k)))
		    (else (rep a b (cdr s)
			       (make-k-rep-2 s k))))))
	   (apply-k (lambda (k x) (k x)))
	   (make-k-init (lambda () (lambda (x) x)))
	   (make-k-rep-1 (lambda (b k) (lambda (x) (apply-k k (cons b x)))))
	   (make-k-rep-2 (lambda (s k) (lambda (x) (apply-k k (cons (car s) x))))))
    (lambda (a b s)
      (rep a b s (make-k-init)))))

(define replace-all-flat-4
  (letrec ((rep
	    (lambda (a b s k)
	      (cond ((null? s) (apply-k k '()))
		    ((eq? (car s) a)
		     (rep a b (cdr s)
			  (make-k-rep-1 b k)))
		    (else (rep a b (cdr s)
			       (make-k-rep-2 s k))))))
	   (apply-k
	    (lambda (k x)
	      (cond ((eq? (car k) 'k-init) x)
		    ((eq? (car k) 'k-rep-1)
		     (with k
		       (lambda (_ b k)
			 (apply-k k (cons b x)))))
		    ((eq? (car k) 'k-rep-2)
		     (with k
		       (lambda (_ s k)
			 (apply-k k (cons (car s) x)))))
		    (else (error 'apply-k
				 "Unknown continuation")))))
	   (make-k-init (lambda () `(k-init)))
	   (make-k-rep-1 (lambda (b k) `(k-rep-1 ,b ,k)))
	   (make-k-rep-2 (lambda (s k) `(k-rep-2 ,s ,k))))
    (lambda (a b s)
      (rep a b s (make-k-init)))))

(define replace-all-flat-5
  (letrec ((rep
	    (lambda (a b s k)
	      (cond ((null? s) (apply-k k '()))
		    ((eq? (car s) a)
		     (rep a b (cdr s)
			  (make-k-rep-1 b k)))
		    (else (rep a b (cdr s)
			       (make-k-rep-2 s k))))))
	   (apply-k
	    (lambda (k x)
	      (cond ((eq? (car k) 'k-init) x)
		    ((eq? (car k) 'k-rep-1)
		     (with k
		       (lambda (_ b . k)
			 (apply-k k (cons b x)))))
		    ((eq? (car k) 'k-rep-2)
		     (with k
		       (lambda (_ s . k)
			 (apply-k k (cons (car s) x)))))
		    (else (error 'apply-k
				 "Unknown continuation")))))
	   (make-k-init (lambda () `(k-init)))
	   (make-k-rep-1 (lambda (b k) `(k-rep-1 ,b . ,k)))
	   (make-k-rep-2 (lambda (s k) `(k-rep-2 ,s . ,k))))
    (lambda (a b s)
      (rep a b s (make-k-init)))))

(define replace-all-flat-6
  ;; these are the registers
  (let ((a 'moshe)
	(b 'moshe)
	(s 'moshe)
	(k 'moshe)
	(x 'moshe))
    (letrec ((rep
	      (lambda ()
		(cond ((null? s)
		       (set! x '())
		       (apply-k))
		      ((eq? (car s) a)
		       (push b)
		       (push 'k-rep-1)
		       (set! s (cdr s))
		       (rep))
		      (else (push s)
			    (push 'k-rep-2)
			    (set! s (cdr s))
			    (rep)))))
	     (apply-k
	      (lambda ()
		(set! k (pop))
		(cond ((eq? k 'k-init) x)
		      ((eq? k 'k-rep-1)
		       (set! b (pop))
		       (set! x (cons b x))
		       (apply-k))
		      ((eq? k 'k-rep-2)
		       (set! s (pop))
		       (set! x (cons (car s) x))
		       (apply-k))
		      (else (error 'apply-k
				   "Unknown continuation"))))))
      (lambda (_a _b _s)
	(set! a _a)
	(set! b _b)
	(set! s _s)
	(reset-stack)
	(push 'k-init)
	(rep)))))

;;; Solving the Towers of Hanoi

(define hanoi-1
  (letrec ((hanoi
	    (lambda (n from to using)
	      (if (zero? n)
		  '()
		  `(,@(hanoi (- n 1) from using to)
		    (move a disk from ,from to ,to)
		    ,@(hanoi (- n 1) using to from))))))
    (lambda (n)
      (hanoi n 'peg-a 'peg-b 'peg-c))))

(define hanoi-2
  (letrec ((hanoi
	    (lambda (n from to using k)
	      (if (zero? n)
		  (k '())
		  (hanoi (- n 1) from using to
			 (lambda (x)
			   (hanoi (- n 1) using to from
				  (lambda (y)
				    (k `(,@x (move a disk from ,from to ,to) ,@y))))))))))
    (lambda (n)
      (hanoi n 'peg-a 'peg-b 'peg-c (lambda (x) x)))))

(define hanoi-3
  (letrec ((hanoi
	    (lambda (n from to using k)
	      (if (zero? n)
		  (apply-k k '())
		  (hanoi (- n 1) from using to
			 (make-k-hanoi-1 n from to using k)))))
	   (apply-k (lambda (k x) (k x)))
	   (make-k-init (lambda () (lambda (x) x)))
	   (make-k-hanoi-1
	    (lambda (n from to using k)
	      (lambda (x)
		(hanoi (- n 1) using to from
		       (make-k-hanoi-2 x from to k)))))
	   (make-k-hanoi-2
	    (lambda (x from to k)
	      (lambda (y)
		(apply-k k `(,@x (move a disk from ,from to ,to) ,@y))))))
    (lambda (n)
      (hanoi n 'peg-a 'peg-b 'peg-c (make-k-init)))))

(define hanoi-4
  (letrec ((hanoi
	    (lambda (n from to using k)
	      (if (zero? n)
		  (apply-k k '())
		  (hanoi (- n 1) from using to
			 (make-k-hanoi-1 n from to using k)))))
	   (apply-k
	    (lambda (k x)
	      (cond ((eq? (car k) 'k-init) x)
		    ((eq? (car k) 'k-hanoi-1)
		     (with k
		       (lambda (_ n from to using k)
			 (hanoi (- n 1) using to from
				(make-k-hanoi-2 x from to k)))))
		    ((eq? (car k) 'k-hanoi-2)
		     (with k
		       (lambda (_ y from to k)
			 (apply-k k `(,@y (move a disk from ,from to ,to) ,@x)))))
		    (else (error 'apply-k
				 "Unknown continuation")))))
	   (make-k-init (lambda () `(k-init)))
	   (make-k-hanoi-1 (lambda (n from to using k) `(k-hanoi-1 ,n ,from ,to ,using ,k)))
	   (make-k-hanoi-2 (lambda (x from to k) `(k-hanoi-2 ,x ,from ,to ,k))))
    (lambda (n)
      (hanoi n 'peg-a 'peg-b 'peg-c (make-k-init)))))

(define hanoi-5
  (letrec ((hanoi
	    (lambda (n from to using k)
	      (if (zero? n)
		  (apply-k k '())
		  (hanoi (- n 1) from using to
			 (make-k-hanoi-1 n from to using k)))))
	   (apply-k
	    (lambda (k x)
	      (cond ((eq? (car k) 'k-init) x)
		    ((eq? (car k) 'k-hanoi-1)
		     (with k
		       (lambda (_ n from to using . k)
			 (hanoi (- n 1) using to from
				(make-k-hanoi-2 x from to k)))))
		    ((eq? (car k) 'k-hanoi-2)
		     (with k
		       (lambda (_ y from to . k)
			 (apply-k k `(,@y (move a disk from ,from to ,to) ,@x)))))
		    (else (error 'apply-k
				 "Unknown continuation")))))
	   (make-k-init (lambda () `(k-init)))
	   (make-k-hanoi-1 (lambda (n from to using k) `(k-hanoi-1 ,n ,from ,to ,using . ,k)))
	   (make-k-hanoi-2 (lambda (x from to k) `(k-hanoi-2 ,x ,from ,to . ,k))))
    (lambda (n)
      (hanoi n 'peg-a 'peg-b 'peg-c (make-k-init)))))

(define hanoi-6
  ;; these are the registers
  (let ((n 'moshe)
	(from 'moshe)
	(to 'moshe)
	(using 'moshe)
	(k 'moshe)
	(x 'moshe)
	(y 'moshe)
	(tmp 'moshe))
    (letrec ((hanoi
	      (lambda ()
		(if (zero? n)
		    (begin
		      (set! x '())
		      (apply-k))
		    (begin
		      (push using)
		      (push to)
		      (push from)
		      (push n)
		      (push 'k-hanoi-1)
		      (set! tmp to)
		      (set! to using)
		      (set! using tmp)
		      (set! n (- n 1))
		      (hanoi)))))
	     (apply-k
	      (lambda ()
		(set! k (pop))
		(cond ((eq? k 'k-init) x)
		      ((eq? k 'k-hanoi-1)
		       (set! n (pop))
		       (set! from (pop))
		       (set! to (pop))
		       (set! using (pop))
		       (push to)
		       (push from)
		       (push x)
		       (push 'k-hanoi-2)
		       (set! tmp from)
		       (set! from using)
		       (set! using tmp)
		       (set! n (- n 1))
		       (hanoi))
		      ((eq? k 'k-hanoi-2)
		       (set! y (pop))
		       (set! from (pop))
		       (set! to (pop))
		       (set! x `(,@y (move a disk from ,from to ,to) ,@x))
		       (apply-k))
		      (else (error 'apply-k
				   "Unknown continuation"))))))
      (lambda (_n)
	(set! n _n)
	(reset-stack)
	(push 'k-init)
	(set! from 'peg-a)
	(set! to 'peg-b)
	(set! using 'peg-c)
	(hanoi)))))

;;; Testing

;;; Run (test) --
;;; If you get #t then all is well; If you get #f or an error message, then all is not well.

(define test
  (lambda ()
    (and ((lambda facts (andmap (lambda (fact) (= (fact 5) 120)) facts))
	  fact-1 fact-2 fact-3 fact-4 fact-5 fact-6)
	 ((lambda fibs (andmap (lambda (fib) (= (fib 10) 55)) fibs))
	  fib-1 fib-2 fib-3 fib-4 fib-5 fib-6)
	 ((lambda acks (andmap (lambda (ack) (= (ack 3 3) 61)) acks))
	  ack-1 ack-2 ack-3 ack-4 ack-5 ack-6)
	 ((lambda lengths (andmap (lambda (length) (= (length '(a b c d e)) 5)) lengths))
	  length-1 length-2 length-3 length-4 length-5 length-6)
	 ((lambda replace-firsts (andmap (lambda (replace-first)
				      (and (equal? (replace-first 'a 'b '(a b a))
						   '(b b a))
					   (equal? (replace-first 'a 'b '(c))
						   '(c))
					   (equal? (replace-first 'a 'b '(moshe a (a) a))
						   '(moshe b (a) a))))
				    replace-firsts))
	  replace-first-1 replace-first-2 replace-first-3 replace-first-4 replace-first-5 replace-first-6)
	 ((lambda replace-all-flats (andmap (lambda (replace-all-flat)
					 (and (equal? (replace-all-flat 'a 'b '(a b a))
						      '(b b b))
					      (equal? (replace-all-flat 'a 'b '(c))
						      '(c))
					      (equal? (replace-all-flat 'a 'b '(moshe a (a) a))
						      '(moshe b (a) b))))
				       replace-all-flats))
	  replace-all-flat-1 replace-all-flat-2 replace-all-flat-3 replace-all-flat-4 replace-all-flat-5 replace-all-flat-6)
	 ((lambda hanois (andmap (lambda (hanoi) (equal? (hanoi 3)
					       '((move a disk from peg-a to peg-b)
						 (move a disk from peg-a to peg-c)
						 (move a disk from peg-b to peg-c)
						 (move a disk from peg-a to peg-b)
						 (move a disk from peg-c to peg-a)
						 (move a disk from peg-c to peg-b)
						 (move a disk from peg-a to peg-b))))
			    hanois))
	  hanoi-1 hanoi-2 hanoi-3 hanoi-4 hanoi-5 hanoi-6)
	 )))

