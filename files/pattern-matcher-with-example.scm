;;; matcher.scm
;;;
;;; Programmer: Mayer Goldberg, 2012

(define match
  (letrec ((match
	    (lambda (pat e ret-vals ret-fail)
	      (cond ((and (pair? pat) (pair? e))
		     (match (car pat) (car e)
			    (lambda (vals-car)
			      (match (cdr pat) (cdr e)
				     (lambda (vals-cdr)
				       (ret-vals
					(append vals-car vals-cdr)))
				     ret-fail))
			    ret-fail))
		    ((and (vector? pat) (vector? e)
			  (= (vector-length pat) (vector-length e))
			  (match (vector->list pat) (vector->list e)
				 ret-vals ret-fail)))
		    ((procedure? pat)
		     (let ((v (pat e)))
		       (if v (ret-vals v) (ret-fail))))
		    ((equal? pat e) (ret-vals '()))
		    (else (ret-fail))))))
    (lambda (pat e ret-with ret-fail)
      (match pat e
	     (lambda (vals) (apply ret-with vals))
	     ret-fail))))

(define ?
  (lambda (name . guards)
    (let ((guard?
	   (lambda (e)
	     (andmap 
	      (lambda (g?) (g? e))
	      guards))))
      (lambda (value)
	(if (guard? value)
	    (list value)
	    #f)))))

;;; composing patterns

(define pattern-rule
  (lambda (pat handler)
    (lambda (e failure)
      (match pat e handler failure))))

(define compose-patterns
  (letrec ((match-nothing
	    (lambda (e failure)
	      (failure)))
	   (loop
	    (lambda (s)
	      (if (null? s)
		  match-nothing
		  (let ((match-rest
			 (loop (cdr s)))
			(match-first (car s)))
		    (lambda (e failure)
		      (match-first e
		       (lambda ()
			 (match-rest e failure)))))))))
    (lambda patterns
      (loop patterns))))

;;; Example: A tag-parser for Scheme

(define *void-object* (if #f #f))

(define simple-const?
  (let ((preds (list boolean? char? number? string?)))
    (lambda (e)
      (ormap (lambda (p?) (p? e)) preds))))

(define var?
  (lambda (e)
    (and (symbol? e)
	 (not (reserved-word? e)))))

(define reserved-word?
  (lambda (e)
    (ormap
     (lambda (kw) (eq? e kw))
     *reserved-words*)))

(define *reserved-words*
  '(and begin cond define do else if lambda
	let let* letrec or quasiquote
	quote set! unquote unquote-splicing))

(define parse
  (let ((run
	 (compose-patterns
	  (pattern-rule
	   (? 'c simple-const?)
	   (lambda (c) `(const ,c)))
	  (pattern-rule
	   `(quote ,(? 'c))
	   (lambda (c) `(const ,c)))
	  (pattern-rule
	   (? 'v var?)
	   (lambda (v) `(var ,v)))
	  (pattern-rule
	   `(if ,(? 'test) ,(? 'dit))
	   (lambda (test dit)
	     `(if ,(parse test) ,(parse dit) (const ,*void-object*))))
	  (pattern-rule
	   `(if ,(? 'test) ,(? 'dit) ,(? 'dif))
	   (lambda (test dit dif)
	     `(if ,(parse test) ,(parse dit) ,(parse dif))))
	  ;; let*
	  (pattern-rule
	   `(let* () ,(? 'expr) . ,(? 'exprs list?))
	   (lambda (expr exprs)
	     (parse (beginify (cons expr exprs)))))
	  (pattern-rule
	   `(let* ((,(? 'var var?) ,(? 'val)) . ,(? 'rest)) . ,(? 'exprs))
	   (lambda (var val rest exprs)
	     (parse `(let ((,var ,val))
		       (let* ,rest . ,exprs)))))
	  ;; add more rules here
	  )))
    (lambda (e)
      (run e
	   (lambda ()
	     (error 'parse
		    (format "I can't recognize this: ~s" e)))))))

(define beginify
  (lambda (s)
    (cond ((null? s) *void-object*)
	  ((null? (cdr s)) (car s))
	  (else `(begin ,@s)))))