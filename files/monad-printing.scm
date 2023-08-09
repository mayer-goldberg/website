;;; println.scm
;;; A monadic "print" routine
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

;;; printf in c returns the number of chars printed, so print does the same
(define print
  (lambda (str)
    (lambda (v)
      (lambda (w)
	(lambda (u)
	  (u (string-length str)
	     (string-append w str)))))))

(define blank-screen "")

(define show
  (lambda (v w)
    `((value: ,v)
      (display: ,w))))

;;; load the file and check out the value of the example
(define example
  (((sequence
      (print "hello")
      (print " world!")
      (print "\n")
      (print "This is really cool!\n")
      (lambda (len) ; capture the number of chars printed
	(sequence
	  (print "You just printed ")
	  (print (number->string len))
	  (print " chars!\n")
	  ))
      (lambda (_)
	(return 'ok)))
    blank-screen)
   show))