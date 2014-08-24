#lang plai-typed

;; Comp314 

;; Kemal Akkoyun
;; 11076004

;; Sources : Chris Stephenson's Comp314 Lectures, Videos and Notes.
;; Book : http://cs.brown.edu/courses/cs173/2012/book
;; .plt Source : http://cs.brown.edu/courses/cs173/2012/lang/

;; =========================================================== ;;
;;   ClASSWORK & ASSIGNMENT
;; =========================================================== ;;

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
  [appC (fun : ExprC)(arg : ExprC)]
  [lamC (arg : symbol) (body : ExprC)]
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
          (case (s-exp->symbol (first sl))
            [(lambda!)(lamC (s-exp->symbol (second sl))
                            (parse (third sl)))]
            [else (binaryOpC (s-exp->symbol (first sl)) 
                             (parse (second sl)) (parse (third sl)))])]
         [(= (length sl) 2)
          (appC (parse (first sl)) (parse (second sl)))]
         [else (error 'parse "invalid list input")])
       )]
    [else (error 'parse "invalid input")]))

;; Tests :
; <<<<<< ADD TESTS >>>>>>>>
(test (parse (number->s-exp 5))(numC 5))
(test (parse (symbol->s-exp 'x))(idC 'x))
(test (parse '(+ 3 4))(binaryOpC '+ (numC 3)(numC 4)))
(test (parse '(* 3 4))(binaryOpC '* (numC 3)(numC 4)))
(test (parse '(+ x x))(binaryOpC '+ (idC 'x)(idC 'x)))
(test (parse '(* x x))(binaryOpC '* (idC 'x)(idC 'x)))
(test (parse '(ifzero 4 5 6))(ifZeroC (numC 4)(numC 5)(numC 6)))
(test (parse '(ifzero (- 3 4) 5 6))(ifZeroC 
                                    (binaryOpC '- (numC 3)(numC 4))
                                    (numC 5)(numC 6)))


;; BinaryOperationWrapper : (number number -> number) numV numV -> numv
;; Purpose :
;; Template :
;(define (BinaryOperationWrapper [l : Value] [r : Value]) : Value
;  (cond
;    [(and (numV? l) (numV? r))
;     (numV (... (numV-n l) (numV-n r)))]
;    [else
;     (error 'BinaryOperationWrapper "one argument was not a number")]))

(define (BinaryOperationWrapper (op : (number number -> number)) [l : Value] [r : Value]) : Value
  (cond
    [(and (numV? l) (numV? r))
     (numV (op (numV-n l) (numV-n r)))]
    [else
     (error 'BinaryOperationWrapper "one argument was not a number")]))

;; Tests :
; <<<<<< ADD TESTS >>>>>>>>

;; A data-type for values in language.
(define-type Value
  [numV (n : number)]
  [closV (arg : symbol) (body : ExprC) (env : Environment)])

;; Binding is a data type to bind value with identifiers.
(define-type Binding
  [bind (name : symbol) (val : Value)])

;; Just an alias to keep it clean, wrapper around listof Bindings.
(define-type-alias Environment (listof Binding))

;; Empty environment.
(define mt-env empty)

;; Extending environment a wrapper around cons.
(define extend-env cons)

;; Example Environment.
(define EnvNameSpace
  (list
   (bind 'x (numV 5))
   (bind 'y (numV 6))
   (bind 'z (numV 7))
   ))

;; lookup : symbol (listof Bindings) -> number
;; Purpose : To find given symbol's value
;; - from environment(listof bindings).
;; Template : Basic Structural Recursion
; (define (lookup [for : symbol] [env : Environment]) : number
;  (cond
;    [(empty? env) ...]
;    [else ...(first env) ...(lookup (rest env))])

(define (lookup [for : symbol] [env : Environment]) : Value
  (cond
    [(empty? env) (error 'lookup "name not found")]
    [else (cond
            [(symbol=? for (bind-name (first env)))
             (bind-val (first env))]
            [else (lookup for (rest env))])]))

;; Tests:
; <<<<<< ADD TESTS >>>>>>>>
(test (lookup 'x EnvNameSpace) (numV 5))
(test (lookup 'y EnvNameSpace) (numV 6))
(test (lookup 'z EnvNameSpace) (numV 7))
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

(define (interp [e : ExprC] [env : Environment]) : Value
  (type-case ExprC e
    [numC (n) (numV n)]
    [idC (s) (lookup s env)]
    [appC (f a) (local ([define f-value (interp f env)])
                  (interp (closV-body f-value)
                          (extend-env 
                           (bind (closV-arg f-value)
                                 (interp a env))
                           env)))]
    [binaryOpC (op l r)(BinaryOperationWrapper (get-op op)
                                               (interp l env)
                                               (interp r env))]
    [lamC (a b) (closV a b env)]
    [ifZeroC (pred t f)
             (if (= 0 (numV-n (interp pred env)))
                 (interp t env)
                 (interp f env))]
    ))

;; Tests:
;; From book as is stated in worksheet ! 
; <<<<<< ADD TESTS >>>>>>>>


;; eval : s-exp -> number
;; Purpose : A wrapper function to evaluate s-exp through our language.
(define (eval (sexp : s-expression)) : Value
  (interp (parse sexp) mt-env))

;; Tests:
;(test (interp (parse (number->s-exp 3)) mt-env) 3)
;(test (eval '(+ 3 4)) 7)
;(test (eval '(* 3 4)) 12)
;(test (eval '(sqr 4)) 16)
;(test (eval '(neg 4)) -4)
;(test (eval '(/ 3 4)) (/ 3 4))
;(test (eval '(^ 3 4)) 81)
;(test (eval '(- 3 4)) -1)
;(test (eval '(custom 3 4)) 10)
;(test (eval '(factorial 0)) 1)
;(test (eval '(factorial 1)) 1)
;(test (eval '(factorial 5)) 120)
;(test (eval '(factorial 7)) 5040)
;(test (eval '(fibonacci 0)) 1)
;(test (eval '(fibonacci 1)) 1)
;(test (eval '(fibonacci 2)) 1)
;(test (eval '(fibonacci 3)) 2)
;(test (eval '(fibonacci 4)) 3)
;(test (eval '(fibonacci 5)) 5)
;(test (eval '(fibonacci 6)) 8)
;(test (eval '(fibonacci 7)) 13)
;(test (eval '(fibonacci 8)) 21)
;(test (eval '(fibonacci 9)) 34)