;;; tic-tac-toe.scm
;;; A lambda-calculus version of the popular game
;;; Programmer: Mayer Goldberg, 1999

;;; > (define q 
;;;     (lambda (x o _)
;;;       ((x _ x)
;;;        (o x o)
;;;        (_ o o))))
;;; > q
;;; #<procedure>
;;; > (show q)
;;; (lambda (x o _) ((x _ x) (o x o) (_ o o)))
;;; > (set! q1 (move q (lambda (x o) x))) ; x's turn
;;; > (set! q2 (move q (lambda (x o) o))) ; o's turn
;;; > q1
;;; #<procedure>
;;; > q2
;;; #<procedure>
;;; > (show q1)
;;; (lambda (x o _) ((x x x) (o x o) (_ o o)))
;;; > (show q2)
;;; (lambda (x o _) ((x _ x) (o x o) (o o o)))

(define show
  ((lambda (ma)
     ((lambda (ai)
	(lambda (board)
	  ((board (ma ai 'x) (ma ai 'o) (ma ai'_))
	   (lambda (x y) (lambda (r) `(lambda (x o _) ,r)))
	   #f)))
      (lambda (m1 m2)
	(lambda (c)
	  (lambda (b)
	    (lambda (a)
	      (ma m1 (list a b c))))))))
   (lambda (m r) (lambda (x y) ((x y m) r)))))

(define move
  ((lambda (ma)
     ((lambda (ai)
	(lambda (board player)
	  ((lambda (make-board)
	     ((lambda (move-flat)
		((board (ma ai 1) (ma ai -1) (ma ai 0))
		 (lambda (x y)
		   (lambda (b)
		     (b (lambda (b123 b456 b789)
			  (b123
			   (lambda (b1 b2 b3)
			     (b456
			      (lambda (b4 b5 b6)
				(b789
				 (lambda (b7 b8 b9)
				   (move-flat
				    b1 b2 b3
				    b4 b5 b6
				    b7 b8 b9)))))))))))
		 #f))
	      (lambda (b1 b2 b3 b4 b5 b6 b7 b8 b9)
		((lambda (r1 r2 r3 c1 c2 c3 d1 d2 p)
		   ((lambda (g 2p -2p)
		      (cond ((or (= (abs r1) 3) (= (abs r2) 3) (= (abs r3) 3)
				 (= (abs c1) 3) (= (abs c2) 3) (= (abs c3) 3)
				 (= (abs d1) 3) (= (abs d2) 3))
			     (make-board b1 b2 b3 b4 b5 b6 b7 b8 b9))
			    ((= r1 2p)
			     (g b1 b2 b3
				(lambda (b1 b2 b3)
				  (make-board b1 b2 b3 b4 b5 b6 b7 b8 b9))))
			    ((= r2 2p)
			     (g b4 b5 b6
				(lambda (b4 b5 b6)
				  (make-board b1 b2 b3 b4 b5 b6 b7 b8 b9))))
			    ((= r3 2p)
			     (g b7 b8 b9
				(lambda (b7 b8 b9)
				  (make-board b1 b2 b3 b4 b5 b6 b7 b8 b9))))
			    ((= c1 2p)
			     (g b1 b4 b7
				(lambda (b1 b4 b7)
				  (make-board b1 b2 b3 b4 b5 b6 b7 b8 b9))))
			    ((= c2 2p)
			     (g b2 b5 b8
				(lambda (b2 b5 b8)
				  (make-board b1 b2 b3 b4 b5 b6 b7 b8 b9))))
			    ((= c3 2p)
			     (g b3 b6 b9
				(lambda (b3 b6 b9)
				  (make-board b1 b2 b3 b4 b5 b6 b7 b8 b9))))
			    ((= d1 2p)
			     (g b1 b5 b9
				(lambda (b1 b5 b9)
				  (make-board b1 b2 b3 b4 b5 b6 b7 b8 b9))))
			    ((= d2 2p)
			     (g b3 b5 b7
				(lambda (b3 b5 b7)
				  (make-board b1 b2 b3 b4 b5 b6 b7 b8 b9))))
			    ((= r1 -2p)
			     (g b1 b2 b3
				(lambda (b1 b2 b3)
				  (make-board b1 b2 b3 b4 b5 b6 b7 b8 b9))))
			    ((= r2 -2p)
			     (g b4 b5 b6
				(lambda (b4 b5 b6)
				  (make-board b1 b2 b3 b4 b5 b6 b7 b8 b9))))
			    ((= r3 -2p)
			     (g b7 b8 b9
				(lambda (b7 b8 b9)
				  (make-board b1 b2 b3 b4 b5 b6 b7 b8 b9))))
			    ((= c1 -2p)
			     (g b1 b4 b7
				(lambda (b1 b4 b7)
				  (make-board b1 b2 b3 b4 b5 b6 b7 b8 b9))))
			    ((= c2 -2p)
			     (g b2 b5 b8
				(lambda (b2 b5 b8)
				  (make-board b1 b2 b3 b4 b5 b6 b7 b8 b9))))
			    ((= c3 -2p)
			     (g b3 b6 b9
				(lambda (b3 b6 b9)
				  (make-board b1 b2 b3 b4 b5 b6 b7 b8 b9))))
			    ((= d1 -2p)
			     (g b1 b5 b9
				(lambda (b1 b5 b9)
				  (make-board b1 b2 b3 b4 b5 b6 b7 b8 b9))))
			    ((= d2 -2p)
			     (g b3 b5 b7
				(lambda (b3 b5 b7)
				  (make-board b1 b2 b3 b4 b5 b6 b7 b8 b9))))
			    ((zero? b5) (make-board b1 b2 b3 b4 p b6 b7 b8 b9))
			    ((zero? b1) (make-board p b2 b3 b4 b5 b6 b7 b8 b9))
			    ((zero? b3) (make-board b1 b2 p b4 b5 b6 b7 b8 b9))
			    ((zero? b7) (make-board b1 b2 b3 b4 b5 b6 p b8 b9))
			    ((zero? b9) (make-board b1 b2 b3 b4 b5 b6 b7 b8 p))
			    (else (make-board b1 b2 b3 b4 b5 b6 b7 b8 b9))))
		    (lambda (x y z f)
		      (cond ((zero? x) (f p y z))
			    ((zero? y) (f x p z))
			    ((zero? z) (f x y p))
			    (else (error 'move))))
		    (* 2 p)
		    (* -2 p)))
		 (+ b1 b2 b3) (+ b4 b5 b6) (+ b7 b8 b9)
		 (+ b1 b4 b7) (+ b2 b5 b8) (+ b3 b6 b9)
		 (+ b1 b5 b9) (+ b3 b5 b7)
		 (player 1 -1)))))
	   ((lambda (f)
	      (lambda (b1 b2 b3 b4 b5 b6 b7 b8 b9)
		((lambda (b1 b2 b3 b4 b5 b6 b7 b8 b9)
		   (lambda (x o _)
		     (((b1 x o _) (b2 x o _) (b3 x o _))
		      ((b4 x o _) (b5 x o _) (b6 x o _))
		      ((b7 x o _) (b8 x o _) (b9 x o _)))))
		 (f b1) (f b2) (f b3)
		 (f b4) (f b5) (f b6)
		 (f b7) (f b8) (f b9))))
	    (lambda (i)
	      (cond ((= i 0) (lambda (x o _) _))
		    ((= i 1) (lambda (x o _) x))
		    ((= i -1) (lambda (x o _) o))
		    (else (error 'move))))))))
      (lambda (m1 m2)
	(lambda (c)
	  (lambda (b)
	    (lambda (a)
	      (ma m1 (lambda (z) (z a b c)))))))))
   (lambda (m r) (lambda (x y) ((x y m) r)))))