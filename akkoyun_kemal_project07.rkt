#lang plai-typed

;; Comp314 - 7th Project - Week08

;; Kemal Akkoyun
;; 11076004

;; Sources : Chris Stephenson's Comp314 Lectures, Videos and Notes.
;; Book : http://cs.brown.edu/courses/cs173/2012/book
;; Additional Source : http://www.cs.indiana.edu/eopl/
;; .plt Source : http://cs.brown.edu/courses/cs173/2012/lang/

;; =========================================================== ;;
;;  ASSIGNMENT and PROJECT
;; =========================================================== ;;

;; Pair is a well-known data structure in Lisp/Scheme family languages,
;; - since we do not have a data structure in plai-type, 
;; - this is an basic implementation of it.
(define-type Pair
  (sym-op (sym : symbol) (op : (number number -> number)))
  ; Added new for de bruijn numbering, since it is a pair this a prober place 
  ; - for data definition.
  (de-bruijn (param-pos : number) (env-depth : number))
  (name-bruijn (name : symbol) (db : Pair)))

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
   ))

;; assoc-op : symbol (listof pair) -> pair
;; Purpose : To associate given symbol with operation defined in a listof pairs.
(define (assoc-op (s : symbol) (lp : (listof Pair))) : Pair
  (let ((list-op (filter (lambda (x) (eq? s (sym-op-sym x))) lp)))
    (if (empty? list-op)
        (error 'assoc-op "Operation not found!")
        (first list-op))))

;; Tests :
(test (assoc-op '+ ops) (sym-op '+ +))
(test (assoc-op '- ops) (sym-op '- -))
(test (assoc-op '* ops) (sym-op '* *))
(test (assoc-op '/ ops) (sym-op '/ /))

;; get-op : symbol -> ((number number) -> number)
;; Purpose : To obtain binary defined operation from operation definition table.
(define (get-op (sym : symbol)) : (number number -> number)
  (sym-op-op (assoc-op sym ops)))

;; Tests :
(test (get-op '-) -)
(test (get-op '+) +)
(test (get-op '*) *)
(test (get-op '/) /)

;; A grammar for our surface language, an implementation for macros.
;; Also this approach will use for de-bruijnizing identifiers.
; Grammar for ExprS.
(define-type ExprS
  [numS (n : number)]
  [idS (s : symbol)]
  [appS (fun : ExprS)(params : (listof ExprS))]
  [lamS (params : (listof symbol)) (body : ExprS)]
  [binaryOpS (op : symbol)(l : ExprS)(r : ExprS)]
  [ifZeroS (pred : ExprS)(trueState : ExprS)(falseState : ExprS)])

;; parse : s-exp -> ExprS
;; Purpose : To parse given s-exp to abstract syntax ExprS
;; Template : 
;(define (parse [s : s-expression]) : ExprS
;  (cond
;  [numS (n) ...]
;  [idS (s) ...]
;  [appS (fun params) ...]
;  [lamS (params body) ...]
;  [binaryOpS (op l r ) ...]
;  [ifZeroS (pred trueState falseState) ...]
;    ))

(define (parse [s : s-expression]) : ExprS
  (cond
    [(s-exp-number? s) (numS (s-exp->number s))]
    [(s-exp-symbol? s) (idS (s-exp->symbol s))]
    [(s-exp-list? s)
     (let ([sl (s-exp->list s)])
       (cond
         [(= (length sl) 4)
          (if (symbol=? 'ifzero (s-exp->symbol (first sl)))
              (ifZeroS (parse (second sl))
                       (parse (third sl))
                       (parse (fourth sl)))
              (error 'parse "invalid expression as input"))]
         [(= (length sl) 3)
          (case (s-exp->symbol (first sl))
            [(λ)(lamS (map (lambda (x)(s-exp->symbol x)) 
                           (s-exp->list (second sl)))
                      (parse (third sl)))]
            [else (binaryOpS (s-exp->symbol (first sl)) 
                             (parse (second sl)) (parse (third sl)))])]
         [(= (length sl) 2)
          (appS (parse (first sl))
                (map (lambda (x) (parse x))
                     (s-exp->list (second sl))))]
         [else (error 'parse "invalid list input")])
       )]
    [else (error 'parse "invalid input")]))

;; Tests :
(test (parse (number->s-exp 3))(numS 3))
(test (parse (symbol->s-exp 'x))(idS 'x))
(test (parse '(+ 3 4))(binaryOpS '+ (numS 3)(numS 4)))
(test (parse '(* 3 4))(binaryOpS '* (numS 3)(numS 4)))
(test (parse '(- x x))(binaryOpS '- (idS 'x)(idS 'x)))
(test (parse '(/ x x))(binaryOpS '/ (idS 'x)(idS 'x)))
(test (parse '(λ (x y)(λ (a b)(+ (* x y)(* a b)))))
      (lamS
       (list 'x 'y)
       (lamS
        (list 'a 'b)
        (binaryOpS
         '+
         (binaryOpS '* (idS 'x) (idS 'y))
         (binaryOpS '* (idS 'a) (idS 'b))))))
(test (parse '(ifzero 4 5 6))(ifZeroS (numS 4)(numS 5)(numS 6)))
(test (parse '(ifzero (- 3 4) 5 6))(ifZeroS
                                    (binaryOpS '- (numS 3)(numS 4))
                                    (numS 5)(numS 6)))


; Grammar for ExprC.
(define-type ExprC
  [numC (n : number)]
  [idC (id : Pair)]
  [appC (fun : ExprC)(params : (listof ExprC))]
  [lamC (params : number) (body : ExprC)]
  [binaryOpC (op : symbol)(l : ExprC)(r : ExprC)]
  [ifZeroC (pred : ExprC)(trueState : ExprC)(falseState : ExprC)])

;; A data-type for values in language.
(define-type Value
  [numV (n : number)]
  [closV (params : number) (body : ExprC) (env : Environment)])

;; Binding is a data type to bind value with de Bruijn numbers.
(define-type Binding
  [bind (actual-params : (vectorof Value))])

;; Just an alias to keep it clean, wrapper around listof Bindings.
(define-type-alias Environment (listof Binding))

;; Empty environment.
(define mt-env empty)

;; Extending environment a wrapper around cons.
(define extend-env cons)

;; index-of : x (listOf x) -> number
;; Purpose: To find the index of the given element
;; Template:
;(define (index-of x lox)
;  (let ((pointer 0))
;  (cond
;    [(empty? lox)...]
;    [else]
;  )))

(define (index-of x lox)
  (local ([define (index-of-inner x pointer lox)
            (if (eq? x (first lox)) 
                pointer
                (index-of-inner x (+ pointer 1) (rest lox)))])
    (cond
      [(empty? lox)(error 'index "Element at given index not found!")]
      [else (index-of-inner x 0 lox)])))

;; Tests :
(test (index-of 'x (list 'x 'y 'z)) 0)
(test (index-of 'y (list 'x 'y 'z)) 1)
(test (index-of 'z (list 'x 'y 'z)) 2)

;; name-pair-member? : (listof Pair) x -> boolean
;; Purpose : To check if the given element is in the list or not
;; Template :
;(define (name-pair-member? lp x)
;  (cond
;    ((empty? l) ...)
;    ((symbol=? x (name-bruijn-name (first lp))) ...)
;    (else ...(pair-member? (rest lp) ...))))

(define (name-pair-member? lp x)
  (cond
    ((empty? lp) false)
    ((symbol=? x (name-bruijn-name (first lp))) true)
    (else (name-pair-member? (rest lp) x))))

;; Tests:
(test (name-pair-member? (list (name-bruijn 'x (de-bruijn 1 1))) 'x) true)
(test (name-pair-member? (list (name-bruijn 'x (de-bruijn 1 1))) 'y) false)
(test (name-pair-member? empty 'x) false)

;; assoc-name : symbol (listof (listof pair)) -> pair
;; Purpose : To associate given symbol with name-pair defined in a listof pairs.
;; Template : 
;(define (assoc-name (s : symbol) (llp : (listof (listof Pair)))) : Pair
;  (cond
;    [(empty? llp) (error 'assoc-name "Pair is not found!")]
;    [(name-pair-member? (first llp) s) ...]
;    [else (assoc-name- s (rest llp))]))

(define (assoc-name (s : symbol) (llp : (listof (listof Pair)))) : Pair
  (local (
          ; assoc-name-helper: symbol (listof symbol) number number -> ExprB
          (define (assoc-name-helper s pair depth)
            (cond
              [(empty? pair) (error 'assoc-name "Name-pair not found!")]
              [(symbol=? (name-bruijn-name (first pair)) s)
               (de-bruijn (de-bruijn-param-pos (name-bruijn-db (first pair))) depth)]
              [else (assoc-name-helper s (rest pair) depth)]))
          ; assoc-name-inner symbol (listof (listof symbol)) number -> ExprB
          (define (assoc-name-inner s llp depth)
            (cond
              [(empty? llp) (error 'assoc-name "Name-pair not found!")]
              [(name-pair-member? (first llp) s) (assoc-name-helper s (first llp) depth)]
              [else (assoc-name-inner s (rest llp) (add1 depth))])))
    (assoc-name-inner s llp 0)))


;; Tests :
(test (assoc-name 'x (list (list (name-bruijn 'x (de-bruijn 1 0))))) (de-bruijn 1 0))
(test (assoc-name 'y (list (list (name-bruijn 'x (de-bruijn 1 0))
                                 (name-bruijn 'y (de-bruijn 0 0)))))(de-bruijn 0 0))
(test/exn (assoc-name 'x (list (list (name-bruijn 'y (de-bruijn 1 0)))))
          "Name-pair not found!")

;; convert-params : (listOf symbol) number (listof (listOf Pair)) -> (listof (listOf Pair))
;; Purpose:
;; Template:
;(define (convert-params [params: listOfSymbol] [name-pairs : listOf (listOf Pair)]) : lisOf (listOf Pair)
;(cons ... (foldr ...params ...name-pairs)))

(define (convert-params [params : (listof symbol)] [name-pairs : (listof (listof Pair))]) : (listof (listof Pair))
  (cons (foldr 
         (λ (x y) (cons (name-bruijn x (de-bruijn (index-of x params) 0)) y))
         empty 
         params) name-pairs))

;; Tests :
(test (convert-params (list 'x) empty) 
      (list (list (name-bruijn 'x (de-bruijn 0 0)))))
(test (convert-params (list 'x 'y) empty)
      (list (list (name-bruijn 'x (de-bruijn 0 0))
                  (name-bruijn 'y (de-bruijn 1 0)))))
(test (convert-params (list 'x 'y 'z) empty)
      (list (list (name-bruijn 'x (de-bruijn 0 0))
                  (name-bruijn 'y (de-bruijn 1 0))
                  (name-bruijn 'z (de-bruijn 2 0)))))

;; desugar-helper : ExprS number (listof (listof Pair)) -> ExprC
;; Purpose : Make if macro expansions if there is and change identifiers with de bruijn numbers.
;; Template : 
;(define (desugar-helper [exprS : ExprS] [name-pairs : (listof (listOf Pair))) : ExprC
;  (type-case ExprS exprS
;    [numS (n) ...]
;    [idS (s) ...]
;    [appS (fun params) ...]
;    [lamS (params body) ...]
;    [binaryOpS (op l r) ...]
;    [ifZeroS (pred trueState falseState) ...]
;    ))

(define (desugar-helper [exprS : ExprS] [name-pairs : (listof (listof Pair))]) : ExprC
  (type-case ExprS exprS
    [numS (n) (numC n)]
    [idS (s) (idC (assoc-name s name-pairs))]
    [appS (fun params) (appC 
                        (desugar-helper fun name-pairs)
                        (map (λ (x) (desugar-helper x name-pairs)) params))]
    [lamS (params body)(let 
                           ((new-name-pairs (convert-params params name-pairs)))
                         (lamC 
                          (length params)
                          (desugar-helper body new-name-pairs)))] 
    [binaryOpS (op l r)(binaryOpC op
                                  (desugar-helper l name-pairs)
                                  (desugar-helper r name-pairs))]
    [ifZeroS (pred trueState falseState)
             (ifZeroC (desugar-helper pred name-pairs)
                      (desugar-helper trueState name-pairs)
                      (desugar-helper falseState name-pairs))]
    ))

;; Tests :
(test (desugar-helper (parse (number->s-exp 5)) empty)(numC 5))
(test/exn (desugar-helper (parse (symbol->s-exp 'x)) empty) 
          "Name-pair not found!")
(test (desugar-helper (parse (symbol->s-exp 'x))
                      (list (list (name-bruijn 'x (de-bruijn 1 2)))))
      (idC (de-bruijn 1 0)))
(test (desugar-helper (parse '(+ 3 4)) empty)(binaryOpC '+ (numC 3)(numC 4)))
(test (desugar-helper (parse '(* 3 4)) empty)(binaryOpC '* (numC 3)(numC 4)))
(test (desugar-helper (parse '(- x x)) 
                      (list (list (name-bruijn 'x (de-bruijn 1 2)))))
      (binaryOpC '- 
                 (idC (de-bruijn 1 0))
                 (idC (de-bruijn 1 0))))
(test (desugar-helper (parse '(/ x x)) 
                      (list (list (name-bruijn 'x (de-bruijn 1 2)))))
      (binaryOpC '/ 
                 (idC (de-bruijn 1 0))
                 (idC (de-bruijn 1 0))))
(test (desugar-helper (parse '(ifzero 4 5 6)) empty) 
      (ifZeroC (numC 4)(numC 5)(numC 6)))
(test (desugar-helper (parse
                       '((((λ (x) (λ (y) (λ (z) (+ (+ x y) z))))(3))(4))(5))) 
                      empty)
      (appC (appC (appC (lamC 1 (lamC 1 (lamC 1 
                                              (binaryOpC '+ 
                                                         (binaryOpC '+ 
                                                                    (idC (de-bruijn 0 2))
                                                                    (idC (de-bruijn 0 1)))
                                                         (idC (de-bruijn 0 0))))))
                        (list (numC 3))) (list (numC 4))) (list (numC 5))))
(test (desugar-helper (parse 
                       '(((λ (a b c) (λ (d e)(+ d e)))(3 4 5))(8 10))) empty)
      (appC (appC (lamC 3 (lamC 2 
                                (binaryOpC '+ (idC (de-bruijn 0 0))
                                           (idC (de-bruijn 1 0)))))
                  (list (numC 3) (numC 4) (numC 5))) (list (numC 8) (numC 10))))


;; desugar : ExprS -> ExprC
;; Purpose : To desugar given ExprS which is surface language to abstract syntax ExprC.
;;           - Kind of macro expansion.  
;; Template : 
;(define (desugar [exprS : ExprS]) : ExprC
;  (type-case ExprS exprS
;    [numS (n) ...]
;    [idS (s) ...]
;    [appS (fun params) ...]
;    [lamS (params body) ...]
;    [binaryOpS (op l r) ...]
;    [ifZeroS (pred trueState falseState) ...]
;    ))

;; Old version !
;(define (desugar [exprS : ExprS]) : ExprC
;  (type-case ExprS exprS
;    [numS (n) (numC n)]
;    [idS (s)]
;    [appS (fun params)(appC (desugar fun)
;                          (map (lambda (x)(desugar x)) params))]
;    [lamS (params body)(lamC params (desugar body))]
;    [binaryOpS (op l r)(binaryOpC op
;                                  (desugar l)
;                                  (desugar r))]
;    [ifZeroS (pred trueState falseState)
;             (ifZeroC (desugar pred)
;                      (desugar trueState)
;                      (desugar falseState))]
;    ))

;; For modularity concerns function divided because there may be more macros to add.
(define (desugar [exprS : ExprS]) : ExprC
  (desugar-helper exprS empty))

;; Tests are included above with helper since this just a call for it.

;; bin-op-wrap : (number number -> number) numV numV -> numv
;; Purpose : Since our number values now differ from host languages(racket)'s
;;           - numbers with this is a wrapper for number operations. 
;; Template :
;(define (bin-op-wrap [l : Value] [r : Value]) : Value
;  (cond
;    [(and (numV? l) (numV? r))
;     (numV (... (numV-n l) (numV-n r)))]
;    [else
;     (error 'BinaryOperationWrapper "one parameter was not a number")]))

(define (bin-op-wrap (op : (number number -> number)) [l : Value] [r : Value]) : Value
  (cond
    [(and (numV? l) (numV? r))
     (numV (op (numV-n l) (numV-n r)))]
    [else
     (error 'Binary-operation-wrapper "One of parameters was not a number")]))

;; Tests :
(test (bin-op-wrap + (numV 3)(numV 4))(numV 7))
(test (bin-op-wrap * (numV 3)(numV 4))(numV 12))
(test (bin-op-wrap - (numV 3)(numV 4))(numV -1))
(test (bin-op-wrap / (numV 3)(numV 3))(numV 1))

;; copy-list: (listof x) number (vectorof x) -> (vectorof x)
;; Purpose: To copy to list elements to the given vector starting with the given index

(define (copy-list l index v)
  (if (empty? l) v (copy-list (rest l) (add1 index) (begin (vector-set! v index (first l)) v))))

;; list->vector : list -> vector
;; Purpose : Convert a list to a vector
(define (list->vector l)
  (copy-list l 0
             (make-vector (length l) (numV 0))))

;; Tests:
(test (copy-list (list 1 3) 0 (make-vector 2 0)) (vector 1 3))
(test (copy-list (list 1 2 3 4 5) 0 (make-vector 5 0)) (vector 1 2 3 4 5))
(test (copy-list empty 0 (make-vector 0 0)) (make-vector 0 0))

;; bind-parameters : (listof symbol) (listof Value) Environment -> Environment
;; Purpose : To bind multiple formal parameters with values as actual parameters.
;; Template:
;(define (bind-parameters (number-of-formal-param : number)(actual-param : (listof Value))(env : Environment)) : Environment
;  (cond
;    [(not (= number-of-formal-param (length actual-param)))
;     (error 'bind-parameters "Invalid number of parameters!")]
;    [else (extend-env ... env)]))

(define (bind-parameters (number-of-formal-param : number)(actual-param : (listof Value))(env : Environment)) : Environment
  (cond
    [(not (= number-of-formal-param (length actual-param)))
     (error 'bind-parameters "Invalid number of parameters!")]
    [else 
     (extend-env (bind (list->vector actual-param)) env)]
    ))

;; Tests:
(test (bind-parameters 1 (list (numV 5)) empty)
      (list (bind (vector (numV 5)))))
(test (bind-parameters 2 (list (numV 5) (numV 6)) empty)
      (list (bind (vector (numV 5) (numV 6)))))
(test/exn (bind-parameters 2 (list (numV 5)(numV 6) (numV 7)) empty)
          "Invalid number of parameters!")
(test/exn (bind-parameters 2 (list (numV 5)) empty)
          "Invalid number of parameters!")

;; lookup : symbol (listof Bindings) -> Value
;; Purpose : To find given symbol's value
;;           - from environment(listof bindings).
;; Template : Basic Structural Recursion
; (define (lookup [for : symbol] [env : Environment]) : Value
;  (cond
;    [(empty? env) ...]
;    [else ...(first env) ...(lookup (rest env))])

(define (lookup [for : Pair] [env : Environment]) : Value
  (vector-ref 
   (bind-actual-params (list-ref env (de-bruijn-env-depth for)))
   (de-bruijn-param-pos for)))


;; Tests :
(test (lookup (de-bruijn 0 0)(list (bind (vector (numV 5) (numV 6)))))
      (numV 5))
(test (lookup (de-bruijn 1 0)(list (bind (vector (numV 5) (numV 6)))))
      (numV 6))
(test (lookup (de-bruijn 1 0)(list 
                              (bind (vector (numV 2) (numV 3)(numV 3)))
                              (bind (vector (numV 5) (numV 6)))))
      (numV 3))
(test (lookup (de-bruijn 1 1)(list 
                              (bind (vector (numV 2) (numV 3)(numV 3)))
                              (bind (vector (numV 5) (numV 6)))))
      (numV 6))
(test (lookup (de-bruijn 2 0)(list 
                              (bind (vector (numV 2) (numV 3)(numV 7)))
                              (bind (vector (numV 5) (numV 6)))))
      (numV 7))


;; interp : ExprC (listof FunDefC) -> Value
;; Purpose : To evaluate expressions to values.
;; Template :
; (define (interp [expr : ExprC] [env : Environment]) : Value
;  (type-case ExprC in
;    [numC (n) ...]
;    [idC (s) ...]
;    [appC (fun params) ...]
;    [binaryOpC (l r) ...]

(define (interp [expr : ExprC] [env : Environment]) : Value
  (type-case ExprC expr
    [numC (n) (numV n)]
    [idC (s) (lookup s env)]
    [appC (fun params) (local ([define f-value (interp fun env)])
                         (interp (closV-body f-value)
                                 (bind-parameters 
                                  (closV-params f-value)
                                  (map 
                                   (lambda (x) 
                                     (interp x env)) params) 
                                  (closV-env f-value))))]      
    [binaryOpC (op l r)(bin-op-wrap (get-op op)
                                    (interp l env)
                                    (interp r env))]
    [lamC (params body) (closV params body env)]
    [ifZeroC (pred t f)
             (if (= 0 (numV-n (interp pred env)))
                 (interp t env)
                 (interp f env))]
    ))

;; eval : s-exp -> number
;; Purpose : A wrapper function to evaluate s-exp through our language.
(define (eval (sexp : s-expression)) : number
  (numV-n (interp (desugar (parse sexp)) mt-env)))

;; Tests:
(test (eval '(+ 3 4)) 7)
(test (eval '(* 3 4)) 12)
(test (eval '(/ 3 4)) (/ 3 4))
(test (eval '(- 3 4)) -1)
(test (eval '((λ (x) (* x x)) (4))) 16)
(test (eval '((λ (x) (* x -1)) (4))) -4)
(test (eval '(((λ (x) (λ (y) (+ x y))) (3)) (4))) 7)
(test (eval '((((λ (x) (λ (y) (λ (z) (+ (+ x y) z))))(3))(4))(5))) 12)
(test (eval '(((λ (a b c) (λ (d e)(+ a e)))(3 4 5))(8 10))) 13)
(test (eval '(((λ (a b c) (λ (d e)(+ d e)))(3 4 5))(8 10))) 18)
