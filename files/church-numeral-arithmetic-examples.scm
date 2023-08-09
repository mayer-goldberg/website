;;; church-examples.scm
;;; Demonstrate how to use Church numerals in Scheme
;;;
;;; Programmer: Mayer Goldberg, 2011

> (church->integer c0)
0
> (church->integer (succ c0))
1
> (church->integer (succ (succ c0)))
2
> (church->integer (integer->church 496351))
496351
> (church->integer ((add (integer->church 3)) (integer->church 5)))
8
> (church->integer ((mul (integer->church 3)) (integer->church 7)))
21
> (church->integer ((mul (integer->church 7)) (integer->church 3)))
21
> (church->integer ((pow (integer->church 2)) (integer->church 3)))
8
> (church->integer ((pow (integer->church 3)) (integer->church 2)))
9
> (church->integer (fact (integer->church 6)))
720
> 