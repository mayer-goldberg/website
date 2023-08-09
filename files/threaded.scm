;;; threaded.scm
;;; An attempt to capture the sprit of threaded code in forth
;;;
;;; Programmer: Mayer Goldberg, 2013

(define with (lambda (s f) (apply f s)))

(define ^d1r1
  (lambda (op)
    (lambda (d c)
      (with d
       (lambda (a . d)
	 (with c
          (lambda (ret . c) 	       
	    (ret `(,(op a) . ,d) c))))))))

(define ^d1rn
  (lambda (op)
    (lambda (d c)
      (with d
       (lambda (a . d)
	 (with c
          (lambda (ret . c) 	       
	    (ret `(,@(op a) . ,d) c))))))))

(define ^d2r1
  (lambda (op)
    (lambda (d c)
      (with d
       (lambda (a1 a2 . d)
	 (with c
          (lambda (ret . c) 	       
	    (ret `(,(op a2 a1) . ,d) c))))))))

(define ^d2rn
  (lambda (op)
    (lambda (d c)
      (with d
       (lambda (a1 a2 . d)
	 (with c
          (lambda (ret . c) 	       
	    (ret `(,@(op a2 a1) . ,d) c))))))))

(define ^d3r1
  (lambda (op)
    (lambda (d c)
      (with d
       (lambda (a1 a2 a3 . d)
	 (with c
          (lambda (ret . c) 	       
	    (ret `(,(op a3 a2 a1) . ,d) c))))))))

(define ^d3rn
  (lambda (op)
    (lambda (d c)
      (with d
       (lambda (a1 a2 a3 . d)
	 (with c
          (lambda (ret . c) 	       
	    (ret `(,@(op a3 a2 a1) . ,d) c))))))))

(define ^d4r1
  (lambda (op)
    (lambda (d c)
      (with d
       (lambda (a1 a2 a3 a4 . d)
	 (with c
          (lambda (ret . c) 	       
	    (ret `(,(op a4 a3 a2 a1) . ,d) c))))))))

(define ^d4rn
  (lambda (op)
    (lambda (d c)
      (with d
       (lambda (a1 a2 a3 a4 . d)
	 (with c
          (lambda (ret . c) 	       
	    (ret `(,@(op a4 a3 a2 a1) . ,d) c))))))))

(define sub1 (lambda (n) (- n 1)))
(define add1 (lambda (n) (+ n 1)))

(define _dup (^d1rn (lambda (n) `(,n ,n))))
(define _?dup (^d1rn (lambda (n) (if (zero? n) `(,n) `(,n ,n)))))
(define _pop (^d1rn (lambda (n) `()))) ; this is the postscript name
(define _drop _pop) ; this is the forth name

(define _2dup (^d2rn (lambda (n m) `(,m ,n ,m ,n))))
(define _swap (^d2rn (lambda (n m) `(,n ,m))))
(define _over (^d2rn (lambda (n m) `(,n ,m ,n))))
(define _2pop (^d2rn (lambda (n m) `()))) ; this is the postscript name
(define _2drop _2pop) ; this is the forth name

(define _2swap (^d4rn (lambda (n1 n2 n3 n4) `(,n2 ,n1 ,n4 ,n3))))

(define _incr (^d1r1 add1))
(define _decr (^d1r1 sub1))
(define _zero? (^d1r1 zero?))
(define _not (^d1r1 not))

(define _neg (^d1r1 -))
(define _abs (^d1r1 abs))
(define _add (^d2r1 +))
(define _sub (^d2r1 -))
(define _mul (^d2r1 *))
(define _div (^d2r1 /))
(define _max (^d2r1 max))
(define _min (^d2r1 min))

(define _nip (^d2r1 (lambda (n m) m)))

(define _mod
  (^d2rn
   (lambda (a b)
     (let ((q (quotient a b))
	   (r (remainder a b)))
       (list q r)))))

(define _/mod
  (^d2rn
   (lambda (a b)
     (let ((q (quotient a b))
	   (r (remainder a b)))
       (list r q)))))

(define _*/
  (^d3r1
   (lambda (a b c)
     (quotient (* a b) c))))

(define _push
  (lambda (a)
    (lambda (d c)
      (with c
       (lambda (ret . c)
	 (ret `(,a . ,d) c))))))

(define _if-then-else
  (lambda (d c)
    (with d
     (lambda (else-code then-code a . d)
       (if a
	   (then-code d c)
	   (else-code d c))))))

(define _sequence
  (lambda (first . rest)
    (lambda (d c)
      (first d (append rest c)))))

(define _double
  (_sequence
   _dup
   _add))

(define _square
  (_sequence
   _dup
   _mul))

(define *quitting-words*
  '(bye done exit off out q quit stop))

(define _show
  (lambda (message)
    (lambda (d c)
      (display
       (format ";;; ~a~%;;; d = ~a~%;;; c = ~a~%~%" message d c))
      (let ((user-response (read)))
	(if (ormap
	     (lambda (out) (eq? user-response out))
	     *quitting-words*)
	    'bye
	    (with c
             (lambda (ret . c)
	       (ret d c))))))))

(define _fact
  (_sequence
   _?dup
   _zero?
   (_push
    (_push 1))
   (_push
    (_sequence
     _dup
     _decr
     (lambda (d c) (_fact d c)) ; recurse
     _mul))
   _if-then-else))

;;; an interface
(define fact
  (lambda (n)
    (_fact `(,n)
	   `(,(lambda (d c)
		(with d
                 (lambda (a . d)
		   (and (null? d) (null? c) a))))))))

(define _ack
  (_sequence
   _2dup
   _pop
   _zero?
   (_push
    (_sequence
     _incr
     _nip))
   (_push
    (_sequence
     _2dup
     _zero?
     (_push
      (_sequence
       _pop
       _pop
       _decr
       (_push 1)
       (lambda (d c) (_ack d c)) ; recurse
       ))
     (_push
      (_sequence
       _pop
       _swap
       _decr
       _swap
       _over
       _incr
       _swap
       _decr
       (lambda (d c) (_ack d c)) ; recurse
       (lambda (d c) (_ack d c)) ; recurse
       ))
     _if-then-else))
   _if-then-else))

;;; an interface
(define ack
  (lambda (a b)
    (_ack `(,b ,a)
	  `(,(lambda (d c)
	       (with d
                (lambda (a . d)
		  (and (null? d) (null? c) a))))))))

;;; Think Why!
(define _while
  (let ((callback
	 (lambda (d c)
	   (with d
            (lambda (test-result . d)
	      (with c
               (lambda (_callback test body . c)
		 (if test-result
		     (body d
		      `(,test ,_callback ,_callback ,test ,body . ,c))
		     (with c
                      (lambda (ret . c)
			(ret d c)))))))))))
    (lambda (d c)
      (with d
       (lambda (body test . d)
	 (test d
          `(,callback ,callback ,test ,body . ,c)))))))	       

(define while-test
  (lambda (n)
    ((_sequence
      (_push
       ;; test code
       (_sequence
	_dup
	_zero?
	_not))
      (_push
       ;; body code
       (_sequence
	_dup
	_decr))
      _while
      )
     `(,n)
     (list list))))

