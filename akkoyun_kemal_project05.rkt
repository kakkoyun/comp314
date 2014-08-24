#lang plai-typed

;; Comp314 - 5th Project
;; - Modified Version
;; Kemal Akkoyun
;; 11076004

;; Sources : Chris Stephenson's Comp314 Lectures, Videos and Notes.
;; Book : http://cs.brown.edu/courses/cs173/2012/book
;; .plt Source : http://cs.brown.edu/courses/cs173/2012/lang/

;; =========================================================== ;;
;;   ClASSWORK & ASSIGNMENT
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
  [appC (fun : symbol) (arg : ExprC)]
  [binaryOpC (op : symbol) (l : ExprC) (r : ExprC)]
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
          (appC (s-exp->symbol (first sl)) (parse (second sl)))]
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
(test (parse '(f (* x x)))(appC 'f (binaryOpC '* (idC 'x)(idC 'x))))

(test (parse '(ifzero 4 5 6))(ifZeroC (numC 4)(numC 5)(numC 6)))
(test (parse '(ifzero (- 3 4) 5 6))(ifZeroC 
                                    (binaryOpC '- (numC 3)(numC 4))
                                    (numC 5)(numC 6)))
(test
 (parse 
  '(ifzero (factorial n) 1
           (* n (factorial (sub1 n)))))
 (ifZeroC
  (appC 'factorial (idC 'n))
  (numC 1)
  (binaryOpC
   '*
   (idC 'n)
   (appC 'factorial (appC 'sub1 (idC 'n))))))

;; Function Definition Structure
(define-type FunDefC
  [fdC (name : symbol) (arg : symbol) (body : ExprC)])

; Example function definition namespace.
(define FuncDefNameSpace
  (list
   (fdC 'sqr 'x (parse '(* x x)))
   (fdC 'sub1 'x (parse '(+ x -1)))
   (fdC 'neg 'x (parse '(* x -1)))
   (fdC 'double 'x (parse '(+ x x)))
   (fdC 'quadruple 'x (parse '(double (double x))))
   (fdC 'const5 '_ (parse (number->s-exp 5)))
   (fdC 'factorial 'n (parse 
                       '(ifzero n 1
                                (* n (factorial (sub1 n))))))
   (fdC 'fibonacci 'n (parse 
                       '(ifzero n 1
                                (ifzero (- n 1) 1
                                        (ifzero (- n 2) 1
                                                (+ (fibonacci (- n 1))
                                                   (fibonacci (- n 2))
                                                   ))))))))



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
      (fdC 'sub1 'x (parse '(+ x -1))))
(test (get-fundef 'neg FuncDefNameSpace) 
      (fdC 'neg 'x (parse '(* x -1))))
(test (get-fundef 'sqr FuncDefNameSpace) 
      (fdC 'sqr 'x (parse '(* x x))))

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
; ERROR CASE : (test (lookup 'w EnvNameSpace) 'error)

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
    [appC (f a) (local ([define fd (get-fundef f fds)])
                  (interp (fdC-body fd)
                          (extend-env 
                           (bind (fdC-arg fd)(interp a env fds))
                           mt-env)
                          fds))]
    [binaryOpC (op l r)((get-op op)
                        (interp l env fds)
                        (interp r env fds))]
    ;; ifZero : ExprC Expr ExprC -> ExprC
    ;; an f statement that controls if first argument is zero 
    ;; -- or not, if it is zero that returns second argunment,
    ;; --- otherwise third argument. Partially lazy.
    [ifZeroC (pred t f)
             (if (= 0 (interp pred env fds))
                 (interp t env fds)
                 (interp f env fds))]
    ))

;; Tests:
;; From book as is stated in worksheet !
(test (interp (parse '(+ 10 (const5 10)))
              mt-env
              FuncDefNameSpace) 15)
(test (interp (parse '(+ 10 (double (+ 1 2))))
              mt-env
              FuncDefNameSpace) 16)
(test (interp (parse '(+ 10 (quadruple (+ 1 2))))
              mt-env
              FuncDefNameSpace) 22)
; ERROR CASE : (interp (parse '(f1 3))
;        mt-env
;        (list (fdC 'f1 'x (parse '(f2 4)))
;              (fdC 'f2 'y (parse '(+ x y)))))


;; eval : s-exp -> number
;; Purpose : A wrapper function to evaluate s-exp through our language.
(define (eval (sexp : s-expression)) : number
  ;(interp (parse sexp) empty))
  (interp (parse sexp) mt-env FuncDefNameSpace))

;; Tests:
;;; SAME TEST CASES THAT WE DID WITH SUBSTITUTION MODEL SO TO OBSERVE,
;;; -- SAME BEHAVIOUR !!!

(test (interp (parse (number->s-exp 3)) mt-env empty) 3)
;ERROR CASE : (test (interp (parse (symbol->s-exp 'x)) empty) 
;  (error 'interp "shouldn't get here"))
(test (eval '(+ 3 4)) 7)
(test (eval '(* 3 4)) 12)
(test (eval '(sqr 4)) 16)
(test (eval '(neg 4)) -4)
(test (eval '(/ 3 4)) (/ 3 4)) ;; Racket numbers and operations rocks !!
(test (eval '(^ 3 4)) 81)
(test (eval '(- 3 4)) -1)
(test (eval '(custom 3 4)) 10)
(test (eval '(factorial 0)) 1)
(test (eval '(factorial 1)) 1)
(test (eval '(factorial 5)) 120)
(test (eval '(factorial 7)) 5040)
(test (eval '(fibonacci 0)) 1)
(test (eval '(fibonacci 1)) 1)
(test (eval '(fibonacci 2)) 1)
(test (eval '(fibonacci 3)) 2)
(test (eval '(fibonacci 4)) 3)
(test (eval '(fibonacci 5)) 5)
(test (eval '(fibonacci 6)) 8)
(test (eval '(fibonacci 7)) 13)
(test (eval '(fibonacci 8)) 21)
(test (eval '(fibonacci 9)) 34)