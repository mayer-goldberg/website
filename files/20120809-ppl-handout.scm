;;; 20120809-ppl-handout.scm
;;;
;;; Programmer: Mayer Goldberg, 2012

(define len
  (lambda (s)
    (if (null? s)
	0
	(+ 1 (len (cdr s))))))

;;; The iota function generates a list of numbers up to, but
;;; not including, its argument. Example:
;;;
;;; > (iota 10)
;;; (0 1 2 3 4 5 6 7 8 9)

(define iota
  (lambda (to)
    (letrec ((loop
	      (lambda (n)
		(if (= n to) '()
		    (cons n (loop (+ n 1)))))))
      (loop 0))))

;;;

(define append-lists
  (lambda (s1 s2)
    (if (null? s1)
	s2
	(cons (car s1)
	      (append-lists (cdr s1) s2)))))

(define duplicate-list
  (lambda (s)
    (if (null? s)
	'()
	(cons (car s)
	      (cons (car s)
		    (duplicate-list (cdr s)))))))

(define insert-before
  (lambda (a b s)
    (cond ((null? s) '())
	  ((eq? (car s) a)
	   (cons b s))
	  (else (cons (car s)
		      (insert-before a b (cdr s)))))))

(define insert-after
  (lambda (a b s)
    (cond ((null? s) '())
	  ((eq? (car s) a)
	   (cons (car s)
		 (cons b (cdr s))))
	  (else (cons (car s)
		      (insert-after a b (cdr s)))))))

(define delete-first
  (lambda (a s)
    (cond ((null? s) '())
	  ((eq? (car s) a) (cdr s))
	  (else (cons (car s)
		      (delete-first a (cdr s)))))))

(define delete-all
  (lambda (a s)
    (cond ((null? s) '())
	  ((eq? (car s) a)
	   (delete-all a (cdr s)))
	  (else (cons (car s)
		      (delete-all a (cdr s)))))))

(define nth
  (lambda (n s)
    (if (zero? n)
	(car s)
	(nth (- n 1) (cdr s)))))

(define remove-nth
  (lambda (n s)
    (if (zero? n)
	(cdr s)
	(cons (car s)
	      (remove-nth (- n 1) (cdr s))))))

;;; Working with different counting bases (besisey sfirah).
;;; Example:
;;;
;;; > (base->base 10 '(1 3) 2)
;;; (1 1 0 1)
;;; > (base->base 7 '(1 0 0) 10)
;;; (4 9)
;;; > (base->base 7 '(4 6 3 5 1) 10)
;;; (1 1 8 4 5)
;;; > (base->base 10 '(1 1 8 4 5) 7)
;;; (4 6 3 5 1)

(define integer->base
  (lambda (base n)
    (if (zero? n)
	'(0)
	(integer->base-helper base n '()))))

(define integer->base-helper
  (lambda (base n s)
    (if (zero? n)
	s
	(integer->base-helper
	 base
	 (quotient n base)
	 (cons (remainder n base) s)))))

(define base->integer
  (lambda (base s)
    (base->integer-helper base s 0)))

(define base->integer-helper
  (lambda (base s n)
    (if (null? s)
	n
	(base->integer-helper
	 base
	 (cdr s)
	 (+ (* n base) (car s))))))

(define base->base
  (lambda (base-1 s base-2)
    (integer->base base-2 (base->integer base-1 s))))

;;; This is the power-set function (kvutsat chezkah)
;;; Example: 
;;; 
;;; > (power '(a b c))
;;; (() (c) (b) (b c) (a) (a c) (a b) (a b c))

(define power
  (lambda (s)
    (if (null? s)
	'(())
	(let ((w (power (cdr s))))
	  (append w (map (lambda (v) (cons (car s) v)) w))))))
