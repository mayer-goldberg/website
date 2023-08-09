;;; stream-examples.scm
;;; Examples of using the input-stream package
;;;
;;; Programmer: Mayer Goldberg, 1998

(load "input-streams.scm")

; > (define show
;     (show-chars
;      (string->char-input-stream
;       "This is a somewhat long string of text ... ")))
; > (show 1)
; Up to 1 chars or end: "T"
; > (show 5)
; Up to 5 chars or end: "his i"
; > (show 6)
; Up to 6 chars or end: "s a so"
; > (show 10)
; Up to 10 chars or end: "mewhat lon"
; > (show 10)
; Up to 10 chars or end: "g string o"
; > (show 20)
; Up to 20 chars or end: "f text ... "

(define show-chars
  (lambda (stream)
    (lambda (n)
      (stream
       (lambda (get unget)
	 (letrec ((peek
		   (lambda (n)
		     (if (zero? n) '()
			 (get
			  (lambda (char)
			    (cons char (peek (sub1 n))))
			  (lambda () '()))))))
	   (display (format "Up to ~a chars or end: " n))
	   (display (format "\"~a\"~%" (list->string (peek n))))
	   ))))))

