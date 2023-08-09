;;; reader-examples.scm
;;;
;;; Programmer: Mayer Goldberg, 2012

Chez Scheme Version 8.2
Copyright (c) 1985-2010 Cadence Research Systems

> (load "compiler.scm")
> (define test (lambda (string) (tokens->sexprs (string->tokens string))))
> (test "(a b c)")
((a b c))
> (test "'a")
('a)
> (test "a 'a ''a 4 '4 ''4")
(a 'a ''a 4 '4 ''4)
> (test "#(1 2 #f #\\A () (a b . c)) \"moshe was here!\" yossi")
(#(1 2 #f #\A () (a b . c)) "moshe was here!" yossi)
> (test "(a . (b . (c . ()))) (a . (b . (c))) (a . (b c)) (a b c)")
((a b c) (a b c) (a b c) (a b c))
> (test "'a `a ,a ,@a")
('a `a ,a ,@a)