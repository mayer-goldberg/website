;;; "decomp.scm"
;;; Programmer: Mayer Goldberg, 1993.

(define make-make-nu
  (lambda ()
    (let ((n -1))
      (lambda ()
	(set! n (add1 n))
	(string->symbol
	 (format "x~a" n))))))

(define make-make-vlist
  (lambda (make-nu)
    (letrec ((loop
	      (lambda (n)
		(if (zero? n) '()
		    ;; get order of eval right
		    (let ((nu (make-nu)))
		      (cons nu (loop (sub1 n))))))))
      loop)))

(define make-make-vlists
  (lambda (make-vlist)
    (letrec ((loop
	      (lambda (s)
		(if (null? s) '()
		    ;; get order of eval right
		    (let ((vlist (make-vlist (car s))))
		      (cons vlist (loop (cdr s))))))))
      loop)))

(define make-agent
  (lambda (a b)
    (lambda args
      (let ((proc (car args))
	    (args (append (cdr args) (list a b))))
	(apply proc args)))))

(define pick
  (lambda (s)
    (if (null? (cdr s)) s
	(cons (car s)
	      (pick (cddr s))))))

(define apply-proc
  (lambda (proc s)
    (if (null? s) proc
	(apply-proc (apply proc (car s))
		    (cdr s)))))

(define wrap
  (lambda (s body)
    (letrec ((wrap
	      (lambda (s)
		(if (null? s) body
		    `(lambda ,(car s)
		       ,(wrap (cdr s)))))))
      (wrap s))))
		     
(define decomp
  (let ((M (lambda args
	     (let ((proc (cadr args))
		   (A (pick args)))
	       (make-agent proc A)))))
    (lambda (arityl proc)
      (let ((vlists ((make-make-vlists
		      (make-make-vlist
		       (make-make-nu))) arityl)))
	((apply-proc proc
	  (map (lambda (s)
		 (map (lambda (nu)
			(make-agent M nu)) s)) vlists))
	 (lambda (m a) (wrap vlists a)))))))

(define id (lambda (x) x))

(define left-assoc
  (lambda (A B)
    (if (null? B) A
	(left-assoc (A (car B)) (cdr B)))))

(define normalise
  (let ((M (lambda args
	     (let ((proc (cadr args))
		   (A (pick args)))
	       (make-agent proc (left-assoc (car A) (cdr A)))))))
    (lambda (arityl proc)
      (letrec ((wrap-ribs
		(lambda (proc s)
		  (if (null? s) (proc (lambda (m a) a))
		      (wrap-rib (car s) id
		       (lambda (vars)
			 (let ((args
				(map (lambda (var) (make-agent M var)) vars)))
			   (wrap-ribs (apply proc args) (cdr s))))))))
	       (wrap-rib
		(lambda (n w bring-back)
		  (letrec ((wrap-rib
			    (lambda (n w)
			      (if (zero? n) (bring-back (w '()))
				  (lambda (v)
				    (wrap-rib (sub1 n)
				     (lambda (x)
				       (w (cons v x)))))))))
		    (wrap-rib n w)))))
	(wrap-ribs proc arityl)))))


