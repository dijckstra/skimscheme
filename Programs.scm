;; Specification example
(begin (define f (lambda (x) (+ x 10))) (define result (f (car '(50 34 567 433 22 23 2345 (6 87 6))))) result)
;; Conditional expressions
(begin (define a 10) (define b 20) (if (lt? a b) a b))
;; Recursion (fibonacci sequence)
(begin (define (fib n) (if (lt? n 3) 1 (+ (fib (- n 1)) (fib (- n 2))))) (fib 10))
;; set! + comment
(begin (comment the quick brown fox jumps over the lazy dog) (define x 2) (+ x 1) (set! x (+ 2 2)) (+ x 1))
;; let + lt?
(begin (define x 8) (let ((x 3)) (define result x)) (define result2 (lt? result x)) result2)
;; cons - result: ((a s) b c d)
(begin (cons '(a s) '(b c d)))
;; numerical operations - result: 2 ~ (2 % (100 /10))
(begin (define f (lambda (x) (/ x 10))) (define result (% (f 100) 2)) result)
;; eqv - result: #t
(begin (let ((p (lambda (x) x))) (eqv? p p)))
;; quicksort
(begin (define part (lambda (comp l) (if (eqv? l '()) '() (if (comp (car l)) (cons (car l) (part comp (cdr l))) (part comp (cdr l)))))) (define qsort (lambda (l) (if (eqv? l '()) '() (let ((p (car l))) (cons (cons (qsort (part (lambda (x) (lt? x p)) l)) (part (lambda (x) (eqv? x p)) l)) (qsort (part (lambda (x) (lt? p x)) l))))))) (qsort '(0 1 10 3 1 23 4)))