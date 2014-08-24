#lang plai-typed

;; Comp314 - Week 06
;; - Modified Version
;; Kemal Akkoyun
;; 11076004

;; Sources : Chris Stephenson's Comp314 Lectures, Videos and Notes.
;; Book : http://cs.brown.edu/courses/cs173/2012/book
;; .plt Source : http://cs.brown.edu/courses/cs173/2012/lang/

;; =========================================================== ;;
;;   ClASSWORK
;; =========================================================== ;;

;; Since plai-typed some how does not provide an exponentiation function, also square function, 
;; --- here is my own implementations.

;; expt : number number -> number
;; Purpose: To calculate exponentiation of given two number, first number base and second is power.
(define (expt (a : number) (b : number)) : number
  (cond
    ((= b 0) 1)
    ((even? b) (sqr (expt a (/ b 2))))
    (else (* a (expt a (- b 1))))))

;; sqr : number -> number
;; Purpose: To calculate square of given number.
(define (sqr (a : number)) : number
  (* a a))

;; Pair is a well-known data structure in Lisp/Scheme family languages,
;; - since we do not have a data structure in plai-type, 
;; - this is an basic implementation of it.
(define-type pair
  (sym-op (sym : symbol)(op : (number number -> number))))

;; A table for operations, 
;; - by changing just this data structure,
;; - you can add any binary operations.

;; A list of pair(sym-op) as table of operations.
;; Handycap of this is, 
;; - it is complety depending on host language's operations.
(define ops
  (list
   (sym-op '+ +)
   (sym-op '* *)
   ;; Several binary operations added as it seen below
   (sym-op '- -)
   (sym-op '/ /)
   (sym-op '^ expt)
   (sym-op 'custom (λ (x y) (+ (* 2 x) y)))
   ))

;; get-op : symbol -> ((number number) -> number)
;; Purpose : To obtain binary defined operation from operation definition table.
(define (get-op (sym : symbol)) : (number number -> number)
  (sym-op-op (assoc sym ops)))

;; assoc : symbol (listof pair) -> pair
;; Purpose : To associate given symbol with operation defined in a listof pairs.
(define (assoc (s : symbol) (lp : (listof pair))) : pair
  (let ((list-op (filter (lambda (x) (eq? s (sym-op-sym x))) lp)))
    (if (empty? list-op)
        (error 'assoc "Operation not defined")
        (first list-op))))

; Grammar for ExprC.
(define-type ExprC
  [numC (n : number)]
  [idC (s : symbol)]
  [appC (fun : symbol)(args : (listof ExprC))]
  [binaryOpC (op : symbol)(l : ExprC)(r : ExprC)]
  [ifZeroC (pred : ExprC)(trueState : ExprC)(falseState : ExprC)])

;; parse : s-exp -> ExprC
;; Purpose : To parse given s-exp to abstract syntax ExprC
;; Template : 
;(define (parse [s : s-expression]) : ExprC
;  (cond
;    [n ...]
;    [id ...]
;    any unary or binary function
;    ))

(define (parse [s : s-expression]) : ExprC
  (cond
    [(s-exp-number? s) (numC (s-exp->number s))]
    [(s-exp-symbol? s) (idC (s-exp->symbol s))]
    [(s-exp-list? s)
     (let ([sl (s-exp->list s)])
       (cond
         [(= (length sl) 4)
          (if (symbol=? 'ifzero (s-exp->symbol (first sl)))
              (ifZeroC (parse (second sl))
                       (parse (third sl))
                       (parse (fourth sl)))
              (error 'parse "invalid expression as input"))]
         [(= (length sl) 3)
          (binaryOpC (s-exp->symbol (first sl)) 
                     (parse (second sl)) (parse (third sl)))]
         [(= (length sl) 2)
          (appC (s-exp->symbol (first sl))
                (foldr (lambda (x y) (cons (parse x) y))
                       empty 
                       (s-exp->list (second sl))))]
         [else (error 'parse "invalid list input")])
       )]
    [else (error 'parse "invalid input")]))

;; Tests :
(test (parse (number->s-exp 5))(numC 5))
(test (parse (symbol->s-exp 'x))(idC 'x))
(test (parse '(+ 3 4))(binaryOpC '+ (numC 3)(numC 4)))
(test (parse '(* 3 4))(binaryOpC '* (numC 3)(numC 4)))
(test (parse '(+ x x))(binaryOpC '+ (idC 'x)(idC 'x)))
(test (parse '(* x x))(binaryOpC '* (idC 'x)(idC 'x)))
(test (parse '(f ((* x x))))(appC 'f (list (binaryOpC '* (idC 'x)(idC 'x)))))

(test (parse '(ifzero 4 5 6))(ifZeroC (numC 4)(numC 5)(numC 6)))
(test (parse '(ifzero (- 3 4) 5 6))(ifZeroC 
                                    (binaryOpC '- (numC 3)(numC 4))
                                    (numC 5)(numC 6)))

;; Function Definition Structure
(define-type FunDefC
  [fdC (name : symbol) (args : (listof symbol)) (body : ExprC)])

; Example function definition namespace.
(define FuncDefNameSpace
  (list
   (fdC 'sqr (list 'x)(parse '(* x x)))
   (fdC 'sub1 (list 'x)(parse '(+ x -1)))
   (fdC 'neg (list 'x)(parse '(* x -1)))
   (fdC 'double (list 'x)(parse '(+ x x)))
   (fdC 'const5 (list '_)(parse (number->s-exp 5)))
   (fdC 'factorial (list 'n)
        (parse 
         '(ifzero n 1
                  (* n (factorial ((- n 1)))))))
   (fdC 'factorial-acc (list 'n 'acc)
        (parse 
         '(ifzero n acc
                  (factorial-acc ((- n 1)(* n acc))))))
   (fdC 'fibonacci (list 'n)
        (parse 
         '(ifzero n 1
                  (ifzero (- n 1) 1
                          (ifzero (- n 2) 1
                                  (+ (fibonacci ((- n 1)))
                                     (fibonacci ((- n 2)))
                                     ))))))
   (fdC 'fibonacci-acc (list 'n 'acc1 'acc2)
        (parse 
         '(ifzero n acc2
                  (ifzero (- n 1) acc2
                          (ifzero (- n 2) acc2
                                  (fibonacci-acc ((- n 1) 
                                             acc2 
                                             (+ acc1 acc2))))))))
   ))



;; get-fundef : symbol (listof FunDefC) -> FunDefC
;; Purpose : To find given symbol's(function name/identifier) function definition
;; - from function definition namespace.
;; Template : Basic Structural Recursion
; (define (get-fundef [n : symbol] [fds : (listof FunDefC)]) : FunDefC
;  (cond
;    [(empty? fds) ...]
;    [else ...(first fds) ...(get-fundef (rest fds))])

(define (get-fundef [n : symbol] [fds : (listof FunDefC)]) : FunDefC
  (cond
    [(empty? fds) (error 'get-fundef "reference to undefined function")]
    [(cons? fds) (cond
                   [(equal? n (fdC-name (first fds))) (first fds)]
                   [else (get-fundef n (rest fds))])]))
;; Tests:
(test (get-fundef 'sub1 FuncDefNameSpace) 
      (fdC 'sub1 (list 'x) (parse '(+ x -1))))
(test (get-fundef 'neg FuncDefNameSpace)
      (fdC 'neg (list 'x) (parse '(* x -1))))
(test (get-fundef 'sqr FuncDefNameSpace) 
      (fdC 'sqr (list 'x) (parse '(* x x))))

;; Binding is a data type to bind value with identifiers.
(define-type Binding
  [bind (name : symbol) (val : number)])

;; Just an alias to keep it clean, wrapper around listof Bindings.
(define-type-alias Environment (listof Binding))

;; Empty environment.
(define mt-env empty)

;; Extending environment a wrapper around cons.
(define extend-env cons)

;; Example Environment.
(define EnvNameSpace
  (list
   (bind 'x 5)
   (bind 'y 6)
   (bind 'z 7)
   ))

;; bindAgruments : (listof symbol) (listof number) Environment -> Environment
;; Purpose : To bind multiple arguments with values in this case numbers.
(define (bindArguments (fa : (listof symbol))(ra : (listof number))(env : Environment)) : Environment
  (cond
    [(not (= (length fa)(length ra)))
     (error 'bindArguments "Invalid number of arguments!")]
    [(or (empty? fa)(empty? ra)) env]
    [else (extend-env (bind (first fa)(first ra)) 
                      (bindArguments (rest fa)(rest ra) env))]
    ))

;; Tests:
(test (bindArguments (list 'x)(list 5) empty)(list (bind 'x 5)))
(test (bindArguments (list 'x 'y)(list 5 6) empty)
      (list (bind 'x 5) (bind 'y 6)))
(test/exn (bindArguments (list 'x 'y)(list 5 6 7) empty)
          "Invalid number of arguments!")
(test/exn (bindArguments (list 'x 'y)(list 5 ) empty)
          "Invalid number of arguments!")


;; lookup : symbol (listof Bindings) -> number
;; Purpose : To find given symbol's value
;; - from environment(listof bindings).
;; Template : Basic Structural Recursion
; (define (lookup [for : symbol] [env : Environment]) : number
;  (cond
;    [(empty? env) ...]
;    [else ...(first env) ...(lookup (rest env))])

(define (lookup [for : symbol] [env : Environment]) : number
  (cond
    [(empty? env) (error 'lookup "name not found")]
    [else (cond
            [(symbol=? for (bind-name (first env)))
             (bind-val (first env))]
            [else (lookup for (rest env))])]))

;; Tests:
(test (lookup 'x EnvNameSpace) 5)
(test (lookup 'y EnvNameSpace) 6)
(test (lookup 'z EnvNameSpace) 7)
(test/exn (lookup 'w EnvNameSpace) "name not found")

;; interp : ExprC (listof FunDefC) -> number
;; Purpose : To evaluate expressions to numbers.
;; Template :
; (define (interp [e : ExprC] [fds : (listof FunDefC)]) : number
;  (type-case ExprC in
;    [numC (n) ...]
;    [idC (s) ...]
;    [appC (f a) ...]
;    [binaryOpC (l r) ...]

(define (interp [e : ExprC] [env : Environment][fds : (listof FunDefC)]) : number
  (type-case ExprC e
    [numC (n) n]
    [idC (s) (lookup s env)]
    [appC (f args) (local ([define fd (get-fundef f fds)])
                     (interp (fdC-body fd)
                             (bindArguments 
                              (fdC-args fd)       
                              (map 
                               (lambda (x) (interp x env fds)) args)
                              mt-env)
                             fds))]
    [binaryOpC (op l r)((get-op op)
                        (interp l env fds)
                        (interp r env fds))]
    [ifZeroC (pred t f)
             (if (= 0 (interp pred env fds))
                 (interp t env fds)
                 (interp f env fds))]
    ))

;; Tests:
(test (interp (parse '(+ 10 (const5 (10))))
              mt-env
              FuncDefNameSpace) 15)
(test (interp (parse '(+ 10 (double ((+ 1 2)))))
              mt-env
              FuncDefNameSpace) 16)

;; eval : s-exp -> number
;; Purpose : A wrapper function to evaluate s-exp through our language.
(define (eval (sexp : s-expression)) : number
  (interp (parse sexp) mt-env FuncDefNameSpace))

;; Tests:
;;; SAME TEST CASES THAT WE DID WITH SUBSTITUTION MODEL SO TO OBSERVE,
;;; -- SAME BEHAVIOUR !!!

;; Also it includes performance tests.

(test (interp (parse (number->s-exp 3)) mt-env empty) 3)
(test (eval '(+ 3 4)) 7)
(test (eval '(* 3 4)) 12)
(test (eval '(sqr (4))) 16)
(test (eval '(neg (4))) -4)
(test (eval '(/ 3 4)) (/ 3 4))
(test (eval '(^ 3 4)) 81)
(test (eval '(- 3 4)) -1)
(test (eval '(custom 3 4)) 10)

(time (test (eval '(factorial (0))) 1))
(time (test (eval '(factorial (1))) 1))
(time (test (eval '(factorial (5))) 120))
(time (test (eval '(factorial (7))) 5040))
(time (test (eval '(factorial (9))) 3628800))
(time (eval '(factorial (99))))
(time (eval '(factorial (999))))
; (time (eval '(factorial (9999))))
; (time (eval '(factorial (99999)))) ; It's better not go this large.

(time (test (eval '(factorial-acc (0 1))) 1))
(time (test (eval '(factorial-acc (1 1))) 1))
(time (test (eval '(factorial-acc (5 1))) 120))
(time (test (eval '(factorial-acc (7 1))) 5040))
(time (test (eval '(factorial-acc (9 1))) 3628800))
(time (eval '(factorial-acc (99 1))))
(time (eval '(factorial-acc (999 1))))
; (time (eval '(factorial-acc (9999 1))))
; (time (eval '(factorial-acc (99999 1))))

(test (eval '(fibonacci (0))) 1)
(test (eval '(fibonacci (1))) 1)
(test (eval '(fibonacci (2))) 1)
(test (eval '(fibonacci (3))) 2)
(test (eval '(fibonacci (4))) 3)
(test (eval '(fibonacci (5))) 5)
(test (eval '(fibonacci (6))) 8)

(time (eval '(fibonacci (9))))
(time (eval '(fibonacci (15))))
(time (eval '(fibonacci (24)))) ;; Don't go further!!
;(time (eval '(fibonacci (32))))
;(time (eval '(fibonacci (43))))
;(time (eval '(fibonacci (99))))


(test (eval '(fibonacci-acc (0 1 1))) 1)
(test (eval '(fibonacci-acc (1 1 1))) 1)
(test (eval '(fibonacci-acc (2 1 1))) 1)
(test (eval '(fibonacci-acc (3 1 1))) 2)
(test (eval '(fibonacci-acc (4 1 1))) 3)
(test (eval '(fibonacci-acc (5 1 1))) 5)
(test (eval '(fibonacci-acc (6 1 1))) 8)

(time (eval '(fibonacci-acc (9 1 1))))
(time (eval '(fibonacci-acc (99 1 1))))
(time (eval '(fibonacci-acc (999 1 1))))
(time (eval '(fibonacci-acc (9999 1 1))))
(time (eval '(fibonacci-acc (99999 1 1))))


