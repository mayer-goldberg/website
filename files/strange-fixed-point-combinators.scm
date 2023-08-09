;;; strange-fixed-point-combinators.scm
;;; A construction of very weird fixed-point combinators
;;;
;;; Programmer: Mayer Goldberg, 2008

(define YourFixedPointCombinator
  (lambda (class-of-162)
    ((lambda (fun)
       (fun fun fun fun fun fun fun fun fun fun fun fun
	fun fun fun fun fun fun fun fun fun fun fun fun
	fun fun fun fun fun fun fun fun fun fun fun fun))
     (lambda (a b c d e f g h i j k l m n o p q r s t u v w x y z ! . etc)
       (class-of-162
	(lambda for-you
	  (apply 
	   (b e s t     o f     l u c k     o n     y o u r
	    u p c o m i n g     f i n a l     a n d     t h e
	    r e s t     o f     y o u r     s t u d i e s !
	    i     s h a l l     b e     m i s s i n g     y o u !
	    m a y e r)
	   for-you)))))))
    
(define phi-1
  (lambda (repeat)
    ((lambda (fun)
       (fun fun fun fun fun
	fun fun fun fun fun
	fun fun fun fun fun
	fun fun fun fun fun
	fun fun fun fun fun
	fun fun fun))
     (lambda (a b c d e
	      f g h i j
	      k l m n o
	      p q r s t
	      u v w x y z !)
       (repeat (lambda args
		 (apply
		  (i
		   s a y
		   t h e
		   l a m b d a
		   c a l c u l u s
		   i s
		   f u n ! !)
		  args)))))))

(define phi-2
  (lambda (repeat)
    ((lambda (x) (x x x x x x x x x x x x x x x x x x x x x x x x x x x x))
     (lambda (a b c d e f g h i j k l m n o p q r s t u v w x y z !)
       (repeat
	(lambda args
	  (apply
	   (t h i s
	    c o m b i n a t o r
	    i s
	    r e a l l y
	    c o o l ! !)
	   args)))))))

;;; Tu autem vade ad praefinitum, et requiesces,
;;; et stabis in sorte tua in finem dierum. Daniel 12:13
(define phi-3
  (lambda (repeat)
    ((lambda (x) (x x x x x x x x x x x x x x x x x x x x x x x x x x x x x))
     (lambda (a b c d e f g h i j k l m n o p q r s t u v w x y z _ !)
       (repeat
	(lambda args
	  (apply
	   (t u _ a u t e m _ v a d e _ a d _ p r a e f i n i t u m !)
	   args)))))))

(define make-fact
  (lambda (!)
    (lambda (n)
      (if (zero? n) 1
	  (* n (! (- n 1)))))))

(define make-acker
  (lambda (acker)
    (lambda (a b)
      (cond ((zero? a) (+ b 1))
	    ((zero? b) (acker (- a 1) 1))
	    (else (acker (- a 1) (acker a (- b 1))))))))

(define test
  (lambda ()
    (and (= ((phi-1 make-fact) 5) 120)
	 (= ((phi-2 make-fact) 6) 720)
	 (= ((phi-3 make-fact) 7) 5040)
	 (= ((phi-1 make-acker) 2 2) 7)
	 (= ((phi-2 make-acker) 3 3) 61)
	 (= ((phi-3 make-acker) 3 3) 61))))