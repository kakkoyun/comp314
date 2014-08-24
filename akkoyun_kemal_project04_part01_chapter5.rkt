#lang plai-typed

;; Comp314 - 4th Project - PART 01
;; - PLAI, 2nd ed. Chapter 4 & 5 implementation
;; Kemal Akkoyun
;; 11076004

;; Sources : Chris Stephenson's Comp314 Lectures, Videos and Notes.
;; Book : http://cs.brown.edu/courses/cs173/2012/book
;; .plt Source : http://cs.brown.edu/courses/cs173/2012/lang/

;; =========================================================== ;;
;;   CLASSWORK and ASSIGNMENT
;; =========================================================== ;;

;; Grammar of Arith language with Function definitions.
(define-type ExprC
  [numC (n : number)]
  [idC (s : symbol)]
  [appC (fun : symbol) (arg : ExprC)]
  [plusC (l : ExprC) (r : ExprC)]
  [multC (l : ExprC) (r : ExprC)])

;; parse : s-exp -> ExprC
;; Purpose : To parse given s-exp to abstract syntax ExprC
;; Template : 
;(define (parse [s : s-expression]) : ExprC
;  (cond
;    [n ...]
;    [id ...]
;    [f ...]
;    [+ ...]
;    [- ...]
;    ))

(define (parse [s : s-expression]) : ExprC
  (cond
    [(s-exp-number? s) (numC (s-exp->number s))]
    [(s-exp-symbol? s) (idC (s-exp->symbol s))]
    [(s-exp-list? s)
     (let ([sl (s-exp->list s)])
       (cond
         [(= (length sl) 3)
          (case (s-exp->symbol (first sl))
            [(+) (plusC (parse (second sl)) (parse (third sl)))]
            [(*) (multC (parse (second sl)) (parse (third sl)))]
            [else (error 'parse "invalid list input!")]
            )]
         [(= (length sl) 2)
          (appC (s-exp->symbol (first sl)) (parse (second sl)))]
         [else (error 'parse "invalid number of inputs")]
         ))]
    [else (error 'parse "invalid input!")]))

;; Tests :
(test (parse (number->s-exp 5))(numC 5))
(test (parse (symbol->s-exp 'x))(idC 'x))
(test (parse '(+ 3 4))(plusC (numC 3)(numC 4)))
(test (parse '(* 3 4))(multC (numC 3)(numC 4)))
(test (parse '(+ x x))(plusC (idC 'x)(idC 'x)))
(test (parse '(* x x))(multC (idC 'x)(idC 'x)))
(test (parse '(f (* x x)))(appC 'f (multC (idC 'x)(idC 'x))))

;; Function Definition Structure
(define-type FunDefC
  [fdC (name : symbol) (arg : symbol) (body : ExprC)])

; Example function definition namespace.
(define FuncDefNameSpace
  (list
   (fdC 'sqr 'x (parse '(* x x)))
   (fdC 'sub1 'x (parse '(+ x -1)))
   (fdC 'neg 'x (parse '(* x -1)))))

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

;; subst : ExprC symbol ExprC -> ExprC
;; Purpose : To substitute symbols with expressions.
;; Template :
; (define (subst [what : ExprC] [for : symbol] [in : ExprC]) : ExprC
;  (type-case ExprC in
;    [numC (n) ...]
;    [idC (s) ...]
;    [appC (f a) ...]
;    [plusC (l r) ...]
;    [multC (l r) ...])

;; An improved version of this proposed at the next stage !!
(define (subst [what : ExprC] [for : symbol] [in : ExprC]) : ExprC
  (type-case ExprC in
    [numC (n) in]
    [idC (s) (cond
               [(symbol=? s for) what]
               [else in])]
    [appC (f a) (appC f (subst what for a))]
    [plusC (l r) (plusC (subst what for l)
                        (subst what for r))]
    [multC (l r) (multC (subst what for l)
                        (subst what for r))]))

;; Tests:
(test (subst (numC 4) 'x (numC 5))(numC 5))
(test (subst (numC 4) 'x (idC 'y)) (idC 'y))
(test (subst (numC 4) 'x (idC 'x)) (numC 4))
(test (subst (numC 4) 'x (parse '(f (* x x))))
      (appC 'f (multC (numC 4) (numC 4))))
(test (subst (numC 4) 'y (parse '(f (* x x))))
      (appC 'f (multC (idC 'x) (idC 'x))))
(test (subst (numC 4) 'x (parse '(* x x)))
      (multC (numC 4) (numC 4)))
(test (subst (numC 4) 'x (parse '(+ x x)))
      (plusC (numC 4) (numC 4)))

;; interp : ExprC (listof FunDefC) -> number
;; Purpose : To evaluate expressions to numbers.
;; Template :
; (define (interp [e : ExprC] [fds : (listof FunDefC)]) : number
;  (type-case ExprC in
;    [numC (n) ...]
;    [idC (s) ...]
;    [appC (f a) ...]
;    [plusC (l r) ...]
;    [multC (l r) ...])

(define (interp [e : ExprC] [fds : (listof FunDefC)]) : number
  (type-case ExprC e
    [numC (n) n]
    [idC (_) (error 'interp "shouldn't get here")]
    [appC (f a) (local ([define fd (get-fundef f fds)])
                  (interp (subst 
                           (numC (interp a fds)) ;; Make it eager evaluation !!
                           ;; a - if it is lazy !
                           (fdC-arg fd)
                           (fdC-body fd))
                          fds))]
    [plusC (l r) (+ (interp l fds) (interp r fds))]
    [multC (l r) (* (interp l fds) (interp r fds))]))

;; Tests:
(test (interp (parse (number->s-exp 3)) empty) 3)
;ERROR CASE : (test (interp (parse (symbol->s-exp 'x)) empty) 
;      (error 'interp "shouldn't get here"))
(test (interp (parse '(+ 3 4)) empty) 7)
(test (interp (parse '(* 3 4)) empty) 12)
(test (interp (parse '(sqr 4)) FuncDefNameSpace) 16)
(test (interp (parse '(neg 4)) FuncDefNameSpace) -4)
      