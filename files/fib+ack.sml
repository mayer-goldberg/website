(* fib+ack.sml
 * Threading Fibonacci & Ackermann:
 * 
 * f(a, b, c) = 0      if ( |Fib(a)| < |Ack(b, c)|)
 *            = 1      otherwise
 * where | f(x) | is the number of function calls
 * made by computing f(x). Our computation assumes
 * the tail-call optimization. 
 *
 * Programmer: Mayer Goldberg, 2012
 *)

fun rel() = use "/Users/gmayer/work/research/threading-computation/fib+ack.sml";

fun f (a, b, c) = Fib (a, [0], [9, b, c])
and Fib (0, k, t) = G (t, (0 :: 0 :: k))
  | Fib (1, k, t) = G (t, (1 :: 1 :: k))
  | Fib (n, k, t) = G (t, (2 :: n :: k))
and Ack (0, b, k, t) = G (t, (0 :: 0 :: k))
  | Ack (a, 0, k, t) = G (t, (6 :: a :: k))
  | Ack (a, b, k, t) = G (t, (7 :: a :: b :: k))
and R (x, [0], t) = 0
  | R (x, [1], t) = 1
  | R (x, (2 :: n :: k), t) = G (t, (3 :: x :: n :: k))
  | R (x, (3 :: y :: k), t) = G (t, (4 :: x :: y :: k))
  | R (x, (4 :: a :: k), t) = G (t, (8 :: a :: x :: k))
and G ((0 :: 0 :: k), t) = R (0, k, t)
  | G ((1 :: 1 :: k), t) = R (1, k, t)
  | G ((2 :: n :: k), t) = Fib (n-1, (2 :: n :: k), t)
  | G ((3 :: x :: n :: k), t) = Fib (n - 1, (3 :: x :: k), t)
  | G ((4 :: x :: y :: k), t) = R (x + y, k, t)
  | G ((5 :: b :: k), t) = R (b + 1, k, t)
  | G ((6 :: a :: k), t) = Ack (a - 1, 1, k, t)
  | G ((7 :: a :: b :: k), t) = Ack (a, b - 1, (4 :: a :: k), t)
  | G ((8 :: a :: x :: k), t) = Ack (a - 1, x, k, t)
  | G ([9, b, c], t) = Ack (b, c, [1], t);
