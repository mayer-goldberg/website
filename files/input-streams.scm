;;; input-streams.scm
;;; A uniform mechanism for input

;;; (^cis->line-chars list->something)
;;; (^file->is read)
;;; (^input-stream raw-get)
;;; (^is->container list->container)
;;; (cis->line-chars-list ...)
;;; (cis->line-is ...)
;;; (console->cis)
;;; (file->cis ...)
;;; (file->sexpr-is ...)
;;; (input-port->cis input-port)
;;; (is->list ...)
;;; (is->n-list-is is n pad)
;;; (is->n-list-is is n)
;;; (is->string ...)
;;; (list->is s)
;;; (sexpr->cis e)
;;; (string->cis string)

(define ^input-stream
  (lambda (raw-get)
    (let ((unget-buffer '()))
      (let ((get
	     (lambda (return-object return-none)
	       (if (pair? unget-buffer)
		   (let ((obj (car unget-buffer)))
		     (set! unget-buffer (cdr unget-buffer))
		     (return-object obj))
		   (raw-get return-object return-none))))
	    (unget
	     (lambda (obj)
	       (set! unget-buffer (cons obj unget-buffer)))))
	(lambda (user)
	  (user get unget))))))

(define string->cis
  (lambda (string)
    (let ((length (string-length string))
	  (position 0))
      (let ((get
	     (lambda (return-object return-if-not-available)
	       (if (< position length)
		   (let ((ch (string-ref string position)))
		     (set! position (add1 position))
		     (return-object ch))
		   (return-if-not-available)))))
	(^input-stream get)))))

(define ^file->is
  (lambda (read)
    (lambda (file-name)
      (let ((input-port (open-input-file file-name)))
	(letrec ((get-if-port-closed
		  (lambda (return-object return-if-not-available)
		    (return-if-not-available)))
		 (get
		  (letrec ((get
			    (lambda (return-object return-if-not-available)
			      (let ((ch (read input-port)))
				(if (eof-object? ch)
				    (begin
				      (close-input-port input-port)
				      (set! get get-if-port-closed)
				      (return-if-not-available))
				    (return-object ch))))))
		    (lambda (return-object return-if-not-available)
		      (get return-object return-if-not-available)))))
	  (^input-stream get))))))

(define file->cis (^file->is read-char))
(define file->sexpr-is (^file->is read))

(define console->cis
  (lambda ()
    (let ((input-port (current-input-port)))
      (input-port->cis input-port))))

(define input-port->cis
  (lambda (input-port)
    (letrec ((get
	      (lambda (return-object return-if-not-available)
		(let ((ch (read-char input-port)))
		  (if (eof-object? ch)
		      (return-if-not-available)
		      (return-object ch))))))
      (^input-stream get))))

(define sexpr->cis (lambda (e) (string->cis (sexpr->string e))))

(define ^cis->line-chars
  (lambda (list->something)
    (lambda (cis)
      (cis
       (lambda (get-char unget-char)
	 (letrec ((get
		   (lambda (ret-line ret-none)
		     (let ((line-buffer '()))
		       (letrec ((loop
				 (lambda ()
				   (get-char
				    (lambda (ch)
				      (if (not (char=? ch #\newline))
					  (begin
					    (set! line-buffer
						  (cons ch line-buffer))
					    (loop))))
				    (lambda () (void))))))
			 (let ((line (loop)))
			   (if (null? line-buffer)
			       (ret-none)
			       (ret-line
				(list->something
				 (reverse
				  (if (char=? (car line-buffer) #\newline)
				      (cdr line-buffer)
				      line-buffer)))))))))))
	   (^input-stream get)))))))

(define cis->line-is (^cis->line-chars list->string))
(define cis->line-chars-list (^cis->line-chars (lambda (x) x)))

(define ^is->container
  (lambda (list->container)
    (lambda (is)
      (is
       (lambda (get unget)
	 (letrec ((loop
		   (lambda ()
		     (get
		      (lambda (x)
			(cons x (loop)))
		      (lambda () '())))))
	   (list->container (loop))))))))

(define is->list (^is->container (lambda (x) x)))
(define is->string (^is->container list->string))
(define is->vector (^is->container list->vector))

(define list->is
  (lambda (s)
    (letrec ((raw-get
	      (lambda (ret-expr ret-end)
		(if (null? s) (ret-end)
		    (let ((expr (car s)))
		      (set! s (cdr s))
		      (ret-expr expr))))))
      (^input-stream raw-get))))

(define is->n-list-is
  (lambda (is n)
    (is
     (lambda (get unget)
       (letrec ((get-list
		 (lambda (ret-list ret-end)
		   (get (lambda (x) (ret-list (loop x n)))
			ret-end)))
		(loop
		 (lambda (x n)
		   (cons x
		    (if (zero? n) '()
			(get (lambda (y) (loop y (- n 1)))
			     (lambda () '())))))))
	 (^input-stream get-list))))))

(define is->n-list-is
  (lambda (is n pad)
    (is
     (lambda (get unget)
       (letrec ((get-list
		 (lambda (ret-list ret-end)
		   (get (lambda (x) (ret-list (loop x n)))
			ret-end)))
		(loop
		 (lambda (x n)
		   (cons x
		    (if (zero? n) '()
			(get (lambda (y) (loop y (- n 1)))
			     (lambda () (loop pad (- n 1)))))))))
	 (^input-stream get-list))))))


