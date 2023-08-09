;;; tag-parser-examples.scm
;;; Examples of the Scheme tag parser

> (parse '4)
(const 4)

> (parse '"abc")
(const "abc")

> (parse '#\t)
(const #\t)

> (parse '#\A)
(const #\A)

> (parse '#t)
(const #t)

> (parse '#f)
(const #f)

> (parse '#\newline)
(const #\newline)

> (parse 'a)
(var a)

> (parse ''a)
(const a)

> (parse ''(a b c))
(const (a b c))

> (parse '(a b c))
(applic (var a) ((var b) (var c)))

> (parse ''#(a b c))
(const #3(a b c))

> (parse ''234)
(const 234)

> (parse ''#t)
(const #t)

> (parse ''"abc")
(const "abc")

> (parse '''a)
(const 'a)

> (parse '''(a b c))
(const '(a b c))

> (parse '''234)
(const '234)

> (parse '(zero? n))
(applic (var zero?) ((var n)))

> (parse '(if (zero? n) 1 (* n (fact (- n 1)))))
(if-3
  (applic (var zero?) ((var n)))
  (const 1)
  (applic
    (var *)
    ((var n)
      (applic
        (var fact)
        ((applic (var -) ((var n) (const 1))))))))

> (parse '(lambda () 'nothing))
(lambda-simple () (const nothing))

> (parse '(lambda (a b c) ((a c) (b c))))
(lambda-simple
  (a b c)
  (applic
    (applic (var a) ((var c)))
    ((applic (var b) ((var c))))))

> (parse '(lambda (a b c d . rest) (list a b c d rest)))
(lambda-opt
  (a b c d)
  rest
  (applic
    (var list)
    ((var a) (var b) (var c) (var d) (var rest))))

> (parse '(lambda args args))
(lambda-variadic args (var args))

> (parse '(define list (lambda args args)))
(define (var list) (lambda-variadic args (var args)))

> (parse
  '(define fib
     (lambda (n)
       (if (< n 2) n (+ (fib (- n 1)) (fib (- n 2)))))))
(define (var fib)
     (lambda-simple
       (n)
       (if-3
         (applic (var <) ((var n) (const 2)))
         (var n)
         (applic
           (var +)
           ((applic (var fib) ((applic (var -) ((var n) (const 1)))))
             (applic
               (var fib)
               ((applic (var -) ((var n) (const 2))))))))))

> (parse
  '(define length
     (lambda (s) (if (null? s) 0 (+ 1 (length (cdr s)))))))
(define (var length)
     (lambda-simple
       (s)
       (if-3
         (applic (var null?) ((var s)))
         (const 0)
         (applic
           (var +)
           ((const 1)
             (applic (var length) ((applic (var cdr) ((var s))))))))))

> (parse '(let ([a 3] [b 5]) (+ a b)))
(applic
  (lambda-simple (a b) (applic (var +) ((var a) (var b))))
  ((const 3) (const 5)))

> (parse
  '(let* ([a 3] [a (+ a 5)] [a (* a 7)] [b (+ a a 13)])
     (list a b)))
(applic
  (lambda-simple
    (a)
    (applic
      (lambda-simple
        (a)
        (applic
          (lambda-simple
            (a)
            (applic
              (lambda-simple (b) (applic (var list) ((var a) (var b))))
              ((applic (var +) ((var a) (var a) (const 13))))))
          ((applic (var *) ((var a) (const 7))))))
      ((applic (var +) ((var a) (const 5))))))
  ((const 3)))
> (parse
  '(begin
     (display "hello")
     (display " ")
     (display "world!\n")
     'done))
(seq ((applic (var display) ((const "hello")))
       (applic (var display) ((const " ")))
       (applic (var display) ((const "world!\n")))
       (const done)))

> (parse '(set-car! x '(a b c)))
(applic (var set-car!) ((var x) (const (a b c))))

> (parse '(or (zero? x) (zero? y) (zero? z)))
(or ((applic (var zero?) ((var x)))
      (applic (var zero?) ((var y)))
      (applic (var zero?) ((var z)))))

;;;




