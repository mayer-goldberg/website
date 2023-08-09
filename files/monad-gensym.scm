;;; gensym.scm
;;; A monadic version of gensym. Of course,
;;; this approach does not guarantee the
;;; creation of UNINTERNED symbols, which is
;;; the whole point of gensym; It just
;;; generates enumerated symbols...
;;;
;;; Programmer: Mayer Goldberg, 2009

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

(define show
  (lambda (v w)
    `((value: ,v)
      (gensym-index: ,w))))

;;;

(define symbol
  (lambda (v)
    (lambda (w)
      (lambda (u)
	(u (string->symbol
	    (string-append
	     "g"
	     (number->string w)))
	   (+ w 1))))))

(define symbols
  (lambda (n)
    (if (zero? n)
	(lambda (v)
	  (return '()))
	(lambda (_)
	  (sequence
	    symbol
	    (lambda (a)
	      (sequence
		(symbols (- n 1))
		(lambda (s)
		  (return (cons a s))))))))))

(define example
  (((sequence
      (symbols 6)
      (lambda (s)
	(return (map (lambda (si) `(symbol is ,si)) s))))
    0)
   show))


   