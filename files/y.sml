(* y.sml
 * Curry's and Turing's fixed-point combinators, for single, double, 
 * and triple mutually-recursive functions, as well as functions 
 * on which to test these FPCs.
 *
 * Programmer: Mayer Goldberg, 2008
 *)

fun rel() = use "/Users/admin/gmayer/work/lang/ml/y.sml";

signature BOX1 = 
sig 
    datatype 'a box = Box of 'a box -> 'a;
end;

structure Box1 = 
struct 
    datatype 'a box = Box of 'a box -> 'a;
end;

signature SINGLE_FIXED_POINT_COMBINATOR = 
sig
    val y : (('a -> 'b) -> 'a -> 'b) -> 'a -> 'b;
end;

functor F_YCURRY(B : BOX1) : SINGLE_FIXED_POINT_COMBINATOR = 
struct
fun y f =
    (fn (B.Box x) => (f (fn a => x (B.Box x) a)))
	(B.Box (fn (B.Box x) => (f (fn a => x (B.Box x) a))));
end; 

structure Ycurry = F_YCURRY(Box1 : BOX1) : SINGLE_FIXED_POINT_COMBINATOR;

functor F_YTURING(B : BOX1) : SINGLE_FIXED_POINT_COMBINATOR = 
struct

fun y f = 
    (fn (B.Box x) =>
	(fn f => f(fn a => x (B.Box x) f a)))
	(B.Box (fn (B.Box x) =>
		 (fn f => f(fn a => x (B.Box x) f a))))
    f;
end;

structure Yturing = F_YTURING(Box1 : BOX1) : SINGLE_FIXED_POINT_COMBINATOR;

functor F_SingleRecursiveProcedures(Y : SINGLE_FIXED_POINT_COMBINATOR) = 
struct

val fact = 
    (Y.y (fn fac =>
	     (fn 0 => 1
	       | n => (n * (fac (n - 1))))));

val ack = 
    Y.y (fn acker =>
	    (fn (0, b) => b + 1
	      | (a, 0) => acker (a - 1, 1)
	      | (a, b) => acker (a - 1, acker(a, b - 1))));
end;

structure SingleRecursiveProceduresUsingCurry = 
F_SingleRecursiveProcedures(Ycurry);

structure SingleRecursiveProceduresUsingTuring = 
F_SingleRecursiveProcedures(Yturing);

signature BOX2 = 
sig
    datatype 'a box2 = Box of 'a box2 -> 'a box2 -> 'a;
end;

structure Box2 = 
struct
    datatype 'a box2 = Box of 'a box2 -> 'a box2 -> 'a;
end;

signature DOUBLE_FIXED_POINT_COMBINATOR = 
sig
    val y2 : (('a -> 'b) * ('a -> 'b) -> 'a -> 'b) * 
	     (('a -> 'b) * ('a -> 'b) -> 'a -> 'b)
	     -> 'a -> 'b
end;

functor F_YCURRY2(B : BOX2) : DOUBLE_FIXED_POINT_COMBINATOR = 
struct
fun y2 (f, g) = 
    (fn (B.Box x) => 
	(fn (B.Box y) => 
	    (f ((fn a => (x (B.Box x) (B.Box y) a)),
		(fn a => (y (B.Box x) (B.Box y) a))))))
	(B.Box (fn (B.Box x) => 
		  (fn (B.Box y) => 
		      (f ((fn a => (x (B.Box x) (B.Box y) a)),
			  (fn a => (y (B.Box x) (B.Box y) a)))))))
	(B.Box (fn (B.Box x) => 
		  (fn (B.Box y) => 
		      (g ((fn a => (x (B.Box x) (B.Box y) a)),
			  (fn a => (y (B.Box x) (B.Box y) a)))))));
end;

functor F_YTURING2(B : BOX2) : DOUBLE_FIXED_POINT_COMBINATOR = 
struct
fun y2 (f, g) =
    (fn (B.Box x) =>
	(fn (B.Box y) =>
	    (fn (f, g) =>
		(f ((fn a => (x (B.Box x)
				(B.Box y)
				(f, g) a)),
		    (fn a => (y (B.Box x)
				(B.Box y)
				(f, g) a)))))))
	(B.Box (fn (B.Box x) =>
		  (fn (B.Box y) =>
		      (fn (f, g) =>
			  (f ((fn a => (x (B.Box x)
					  (B.Box y)
					  (f, g) a)),
			      (fn a => (y (B.Box x)
					  (B.Box y)
					  (f, g) a))))))))
	(B.Box (fn (B.Box x) =>
		  (fn (B.Box y) =>
		      (fn (f, g) =>
			  (g ((fn a => (x (B.Box x)
					  (B.Box y)
					  (f, g) a)),
			      (fn a => (y (B.Box x)
					  (B.Box y)
					  (f, g) a))))))))
	(f, g);
end;

structure Ycurry2 = F_YCURRY2(Box2);
structure Yturing2 = F_YTURING2(Box2);

functor F_DoubleRecursiveProcedures(Y2 : DOUBLE_FIXED_POINT_COMBINATOR) = 
struct

val isEven = 
    (Y2.y2 ((fn (even, odd) =>
		(fn 0 => true
		  | n => (odd (n - 1)))),
	    (fn (even, odd) =>
		(fn 0 => false
		  | n => (even (n - 1))))));
end;

structure DoubleRecursiveProceduresUsingCurry =
F_DoubleRecursiveProcedures(Ycurry2);

structure DoubleRecursiveProceduresUsingTuring = 
F_DoubleRecursiveProcedures(Yturing2);

signature BOX3 = 
sig
    datatype 'a box3 = Box of 'a box3 -> 'a box3 -> 'a box3 -> 'a;
end;

structure Box3 = 
struct
    datatype 'a box3 = Box of 'a box3 -> 'a box3 -> 'a box3 -> 'a;
end;

signature TRIPLE_FIXED_POINT_COMBINATOR = 
sig
    val y3 : (('a -> 'b) * ('a -> 'b) * ('a -> 'b) -> 'a -> 'b) * 
             (('a -> 'b) * ('a -> 'b) * ('a -> 'b) -> 'a -> 'b) * 
             (('a -> 'b) * ('a -> 'b) * ('a -> 'b) -> 'a -> 'b)
             -> 'a -> 'b
end;

functor F_YCURRY3(B : BOX3) : TRIPLE_FIXED_POINT_COMBINATOR = 
struct
fun y3 (f, g, h) = 
    (fn (B.Box x) =>
	(fn (B.Box y) =>
	    (fn (B.Box z) =>
		(f ((fn a => (x (B.Box x) (B.Box y) (B.Box z) a)),
		    (fn a => (y (B.Box x) (B.Box y) (B.Box z) a)),
		    (fn a => (z (B.Box x) (B.Box y) (B.Box z) a)))))))
    (B.Box (fn (B.Box x) =>
	      (fn (B.Box y) =>
		  (fn (B.Box z) =>
		      (f ((fn a => (x (B.Box x) (B.Box y) (B.Box z) a)),
			  (fn a => (y (B.Box x) (B.Box y) (B.Box z) a)),
			  (fn a => (z (B.Box x) (B.Box y) (B.Box z) a))))))))
    (B.Box (fn (B.Box x) =>
	      (fn (B.Box y) =>
		  (fn (B.Box z) =>
		      (g ((fn a => (x (B.Box x) (B.Box y) (B.Box z) a)),
			  (fn a => (y (B.Box x) (B.Box y) (B.Box z) a)),
			  (fn a => (z (B.Box x) (B.Box y) (B.Box z) a))))))))
    (B.Box (fn (B.Box x) =>
	      (fn (B.Box y) =>
		  (fn (B.Box z) =>
		      (h ((fn a => (x (B.Box x) (B.Box y) (B.Box z) a)),
			  (fn a => (y (B.Box x) (B.Box y) (B.Box z) a)),
			  (fn a => (z (B.Box x) (B.Box y) (B.Box z) a))))))));
end;

functor F_YTURING3(B : BOX3) : TRIPLE_FIXED_POINT_COMBINATOR = 
struct
fun y3 (f, g, h) = 
    (fn (B.Box x) =>
	(fn (B.Box y) =>
	    (fn (B.Box z) =>
		(fn (f, g, h) =>
		    (f ((fn a => (x (B.Box x) 
				    (B.Box y)
				    (B.Box z)
				    (f, g, h) a)),
			(fn a => (y (B.Box x)
				    (B.Box y) 
				    (B.Box z) 
				    (f, g, h) a)),
			(fn a => (z (B.Box x)
				    (B.Box y)
				    (B.Box z) 
				    (f, g, h) a))))))))
	(B.Box (fn (B.Box x) =>
		  (fn (B.Box y) =>
		      (fn (B.Box z) =>
			  (fn (f, g, h) =>
			      (f ((fn a => (x (B.Box x)
					      (B.Box y) 
					      (B.Box z)
					      (f, g, h) a)),
				  (fn a => (y (B.Box x) 
					      (B.Box y)
					      (B.Box z)
					      (f, g, h) a)),
				  (fn a => (z (B.Box x)
					      (B.Box y) 
					      (B.Box z)
					      (f, g, h) a)))))))))
	(B.Box (fn (B.Box x) =>
		    (fn (B.Box y) =>
			(fn (B.Box z) =>
			    (fn (f, g, h) =>
				(g ((fn a => (x (B.Box x)
						(B.Box y)
						(B.Box z) 
						(f, g, h) a)),
				    (fn a => (y (B.Box x)
						(B.Box y) 
						(B.Box z) 
						(f, g, h) a)),
				    (fn a => (z (B.Box x)
						(B.Box y) 
						(B.Box z)
						(f, g, h) a)))))))))
	(B.Box (fn (B.Box x) =>
		    (fn (B.Box y) =>
			(fn (B.Box z) =>
			    (fn (f, g, h) =>
				(h ((fn a => (x (B.Box x) 
						(B.Box y)
						(B.Box z)
						(f, g, h) a)),
				    (fn a => (y (B.Box x)
						(B.Box y)
						(B.Box z)
						(f, g, h) a)),
				    (fn a => (z (B.Box x)
						(B.Box y)
						(B.Box z)
						(f, g, h) a)))))))))
	(f, g, h);
end;

structure Ycurry3 = F_YCURRY3(Box3);
structure Yturing3 = F_YTURING3(Box3);

functor F_TripleRecursiveProcedures(Y3 : TRIPLE_FIXED_POINT_COMBINATOR) =
struct

val fact = 
    (Y3.y3 ((fn (f1, f2, f3) =>
		(fn 0 => 1
		  | n => n * (f2 (n - 1)))),
	    (fn (f1, f2, f3) =>
		(fn 0 => 1
		  | n => n * (f3 (n - 1)))),
	    (fn (f1, f2, f3) =>
		(fn 0 => 1
		  | n => n * (f1 (n - 1))))));
end;

structure TripleRecursiveProceduresUsingCurry = 
F_TripleRecursiveProcedures(Ycurry3);

structure TripleRecursiveProceduresUsingTuring = 
F_TripleRecursiveProcedures(Yturing3);
