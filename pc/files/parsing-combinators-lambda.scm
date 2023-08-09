;;; parsing-combinators-lambda.scm
;;; A parser for the lambda calculus
;;;
;;; Programmer: Mayer Goldberg, 2013

(load "parsing-combinators.scm")

;;;

(define ^applic
  (lambda (proc arg)
    `(applic ,proc ,arg)))

(define ^abst
  (lambda (var expr)
    `(lambda ,var ,expr)))

(define ^var
  (lambda (symbol)
    `(var ,symbol)))

(define var->name
  (lambda (var)
    (with var
      (lambda (_var name) name))))

(define ^assignment
  (lambda (var expr)
    `(define ,(var->name var) ,expr)))

(define ^load-file
  (lambda (string)
    `(load ,string)))

(define curry-abstractions
  (lambda (vars expr)
    (if (null? vars)
	expr
	(^abst (car vars)
	       (curry-abstractions (cdr vars) expr)))))

(define ^church-numeral
  (letrec ((loop
	    (lambda (n)
	      (if (zero? n)
		  (^var 'z)
		  (^applic (^var 's)
			   (loop (- n 1)))))))
    (lambda (n)
      (if (= n 1)
	  (^abst 's (^var 's))
	  (^abst 's (^abst 'z (loop n)))))))

(define digit->integer
  (let ((zero (char->integer #\0)))
    (lambda (ch)
      (- (char->integer ch) zero))))

(define ^indexed-var
  (lambda (prefix n)
    (string->symbol
     (format "~a~a" prefix n))))

(define ^indexed-vars
  (lambda (prefix n)
    (letrec ((loop
	      (lambda (n s)
		(if (zero? n)
		    s
		    (loop (- n 1)
			  `(,(^indexed-var "x" n) ,@s))))))
      (loop n '()))))
      
(define ^projection
  (lambda (n1 n2)
    (let ((n1 (max n1 n2))
	  (n2 (min n1 n2)))
      (let ((var 'z)
	    (vars (^indexed-vars "x" n1))
	    (expr (^var (^indexed-var "x" n2))))
	(^abst var
	       (^applic (^var var)
			(curry-abstractions vars expr)))))))

(define left-associate
  (letrec ((loop
	    (lambda (a s)
	      (if (null? s)
		  a
		  (with s
		    (lambda (b . s)
		      (loop (^applic a b) s)))))))
    loop))

(define ^n-tuple
  (lambda (s)
    (let* ((var (gensym))
	   (expr (left-associate (^var var) s)))
      (^abst var expr))))

;;;

(define <lambda>
  ((disj (word-ci "lambda")
	 (word-ci "lam")
	 (word "L")
	 (word "\\")
	 (word "&")
	 (word "λ"))
   (lambda (_) 'lambda)))

(define <assign>
  ((disj (word "::=")
	 (word ":=")
	 (word "::")
	 (word "==")
	 (word "=")
	 (word "<-")
	 (word "←")
	 (word "≣"))
   (lambda (_) 'assign)))

(define <expr>
  (lambda $
    (apply
     ((caten __
	     ((disj <church-numeral>
		    <projection>
		    <n-tuple>
		    <lambda-expr>
		    <var-expr>
		    <parenthesised-expr>))
	     __)
      (lambda (_1 expr _2) expr))
     $)))

(define <white>
  (const (lambda (ch) (char<=? ch #\space))))

(define <line-comment>
  ((caten ((disj (word ";") (word "#")))
	  (star
	   (const
	    (lambda (ch) (not (char=? ch #\newline))))))))

(define <lexpr-comment>
  ((caten (word "#;")
	  <expr>)))

(define <xml-comment>
  ((caten (word-ci "<comment>")
	  (star (diff <any-char> (word-ci "</comment>")))
	  (word-ci "</comment>"))))

(define <skip>
  ((disj <white>
	 <line-comment>
	 <lexpr-comment>
	 <xml-comment>)))

(define __
  (star <skip>))

(define __+
  (plus <skip>))

(define <sequence>
  ((caten <expr>
	  (star
	   ((caten __ (word ",") <expr>)
	    (lambda (_1 _2 expr) expr))))
   cons))

(define <n-tuple>
  ((disj
    ((caten (word "[") <sequence> __ (word "]")))
    ((caten (word "<") <sequence> __ (word ">")))
    ((caten (word "〈") <sequence> __ (word "〉"))))
   (lambda (s)
     (with s
       (lambda (_1 s _2 _3) (^n-tuple s))))))

(define <parenthesised-expr>
  ((caten (word "(")
	  (plus ((caten __ <expr>)
		 (lambda (_ expr) expr)))
	  __
	  (word ")"))
   (lambda (_1 exprs _2 _3)
     (with exprs
       (lambda (a . s)
	 (left-associate a s))))))

(define <letter> ((^^char-between char-ci<=?) #\a #\z))

(define <non-zero-digit> ((^^char-between char<=?) #\1 #\9))

(define <digit> ((^^char-between char<=?) #\0 #\9))

(define <var-special-char> (^one-of-chars "+_?$=*^!/"))

(define <sep> ((disj (word "-") (word "_"))))

(define <nat>
  ((disj (word "0" (lambda (_) 0))
	 ((caten <non-zero-digit>
		 (star <digit>))
	  (lambda (d1 ds)
	    (string->number (list->string (cons d1 ds))))))))

(define <church-numeral>
  ((caten (maybe ((caten ((disj (word-ci "church") (word-ci "c")))
			 (maybe <sep>))))
	  <nat>)
   (lambda (_ n) (^church-numeral n))))

(define <proj>
  ((disj (word-ci "proj")
	 (word-ci "pi")
	 (word-ci "p")
	 (word "π"))))

(define <projection>
  ((disj ((caten <proj>
		 (maybe <sep>)
		 <non-zero-digit>
		 <non-zero-digit>)
	  (lambda (_1 _2 d1 d2)
	    (let ((n1 (digit->integer d1))
		  (n2 (digit->integer d2)))
	      (^projection n1 n2))))
	 ((caten (maybe ((caten <proj>
				(maybe <sep>))))
		 <nat>
		 <sep>
		 <nat>)
	  (lambda (_1 n1 _2 n2) (^projection n1 n2))))))

(define <var-expr>
  ((disj
    ((caten <letter>
	    (star ((disj <letter>
			 <digit>
			 (word "-")
			 <var-special-char>))))
     (lambda (a s)
       (string->symbol
	(list->string (cons a s)))))
    (word "-" (lambda (_) '-))
    ((caten <var-special-char>
	    (star ((disj <letter>
			 <digit>
			 <var-special-char>
			 (word "-")))))
     (lambda (a s)
       (string->symbol
	(list->string (cons a s))))))
   (lambda (v) (^var v))))

(define <dot>
  ((disj (word ".")
	 (word ":")
	 (word "·"))
   (lambda (_) 'dot)))

(define <lambda-expr>
  ((disj
    ((caten <lambda>
	    (plus ((caten __ <var-expr>)
		   (lambda (_ var) (var->name var))))
	    __
	    <dot>
	    __
	    <expr>)
     (lambda (_1 vars _2 _3 _4 expr)
       (curry-abstractions vars expr)))
    ((caten <lambda>
	    __
	    <var-expr>
	    __+
	    <var-expr>)
     (lambda (_1 _2 var _3 expr)
       (^abst (var->name var) expr))))))

(define <definition>
  ((caten __ <var-expr> __ <assign> __ <expr>)
   (lambda (_1 var _2 _3 _4 expr)
     (^assignment var expr))))

(define <string>
  (plus ((disj <letter>
	       <digit>
	       (^one-of-chars ".-_$/\\,")))
	list->string))

(define <string-with-quotes>
  ((disj
    ((caten __ (char #\") <string> (char #\") __))
    ((caten __ (char #\[) <string> (char #\]) __))
    ((caten __ (char #\') <string> (char #\') __)))
   (lambda (s)
     (with s
       (lambda (_1 _2 string _3 _4) string)))))

(define <load-file-1>
  ((caten __
	  (word "(")
	  __
	  (word-ci "load")
	  __
	  <string-with-quotes>
	  __
	  (word ")")
	  __)
   (lambda (_1 _2 _3 _4 _5 string _6 _7 _8) string)))

(define <load-file-2>
  ((caten __
	  (word-ci "load")
	  __
	  <string-with-quotes>
	  __)
   (lambda (_1 _2 _3 string _4) string)))

(define <load-file-3> <string-with-quotes>)

(define <load-file>
  ((disj <load-file-1>
	 <load-file-2>
	 <load-file-3>)
   ^load-file))

(define <file>
  ((caten (star
	   ((disj <load-file>
		  <definition>)))
	  (maybe <expr>))
   (lambda (s w)
     `(,@s ,@w))))

