#lang plai-typed

;; Comp314 - 9th Project

;; Kemal Akkoyun
;; 11076004

;; Sources : Chris Stephenson's Comp314 Lectures, Videos and Notes.
;; Book : http://cs.brown.edu/courses/cs173/2012/book
;; Additional Source : http://www.cs.indiana.edu/eopl/
;; .plt Source : http://cs.brown.edu/courses/cs173/2012/lang/

;; =========================================================== ;;
;;  ASSIGNMENT and PROJECT
;; =========================================================== ;;


;; ===================================================================================
;; ===================================================================================
;; ==== Utilities
;; ===================================================================================
;; ===================================================================================

;; Pair is a well-known data structure in Lisp/Scheme family languages,
;; - since we do not have a data structure in plai-type, 
;; - this is an basic implementation of it.
(define-type Pair
  (sym-op (sym : symbol) (op : (number number -> number)))
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

;; new-loc : _ -> void
;; Purpose : To store a global value(mutative) that represents,
;; - first available abstract memory address of our interpreter's runtime environment.
;; ATTENTION : As it seen clearly, 
;; - it relies on host language's(racket) boxes and mutation features.

(define new-loc
  (let ([n (box 0)])
    (lambda ()(begin
                (set-box! n (add1 (unbox n)))
                (unbox n)))))
;; Tests:
(test (new-loc) 1)
(test (new-loc) 2)
(test (new-loc) 3)

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

;; copy-list: (listof x) number (vectorof x) -> (vectorof x)
;; Purpose: To copy to list elements to the given vector starting with the given index

(define (copy-list l index v)
  (if (empty? l) v (copy-list (rest l) (add1 index) (begin (vector-set! v index (first l)) v))))

;; Tests:
(test (copy-list (list 1 3) 0 (make-vector 2 0)) (vector 1 3))
(test (copy-list (list 1 2 3 4 5) 0 (make-vector 5 0)) (vector 1 2 3 4 5))
(test (copy-list empty 0 (make-vector 0 0)) (make-vector 0 0))

;; list->vector : list -> vector
;; Purpose : Convert a list to a vector
(define (list->vector l)
  (copy-list l 0
             (make-vector (length l) 0)))

;; Tests :
(test (list->vector (list 1 2 3))(vector 1 2 3))
(test (list->vector (list 0)) (vector 0))

;; ===================================================================================
;; ===================================================================================
;; ==== Pre-Interpretation phase
;; ===================================================================================
;; ===================================================================================

;; A grammar for our surface language, an implementation for macros.
;; Also this approach will use for de-bruijnizing identifiers.
;; Grammar for ExprS. (Surface abstract language)
(define-type ExprS
  [numS (n : number)]
  [varS (s : symbol)]
  [appS (fun : ExprS)(params : (listof ExprS))]
  [lamS (params : (listof symbol)) (body : ExprS)]
  [binaryOpS (op : symbol)(l : ExprS)(r : ExprS)]
  [ifZeroS (pred : ExprS)(trueState : ExprS)(falseState : ExprS)]
  [setS (s : symbol)(v : ExprS)]
  [seqS (s1 : ExprS)(s2 : ExprS)]
  [recS (n : symbol)(v : ExprS)(b : ExprS)])

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
;  [setS (s v) ...]
;  [seqS (s1 s2) ...]
;  [recS (n v b ) ...]
;    ))

(define (parse [s : s-expression]) : ExprS
  (cond
    [(s-exp-number? s) (numS (s-exp->number s))]
    [(s-exp-symbol? s) (varS (s-exp->symbol s))]
    [(s-exp-list? s)
     (let ([sl (s-exp->list s)])
       (cond
         [(= (length sl) 4)
          (cond
            [(symbol=? 'ifzero (s-exp->symbol (first sl)))
             (ifZeroS (parse (second sl))
                      (parse (third sl))
                      (parse (fourth sl)))]
            [(symbol=? 'rec (s-exp->symbol (first sl)))
             (recS (s-exp->symbol (second sl))
                   (parse (third sl))
                   (parse (fourth sl)))]
            [else (error 'parse "invalid expression as input")])]
         [(= (length sl) 3)
          (case (s-exp->symbol (first sl))
            [(λ)(lamS (map (lambda (x)(s-exp->symbol x)) 
                           (s-exp->list (second sl)))
                      (parse (third sl)))]
            [(set!)(setS (s-exp->symbol (second sl))(parse (third sl)))]
            [(seq!)(seqS (parse (second sl))(parse (third sl)))]
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
(test (parse (symbol->s-exp 'x))(varS 'x))
(test (parse '(+ 3 4))(binaryOpS '+ (numS 3)(numS 4)))
(test (parse '(* 3 4))(binaryOpS '* (numS 3)(numS 4)))
(test (parse '(- x x))(binaryOpS '- (varS 'x)(varS 'x)))
(test (parse '(/ x x))(binaryOpS '/ (varS 'x)(varS 'x)))
(test (parse '(λ (x y)(λ (a b)(+ (* x y)(* a b)))))
      (lamS
       (list 'x 'y)
       (lamS
        (list 'a 'b)
        (binaryOpS
         '+
         (binaryOpS '* (varS 'x) (varS 'y))
         (binaryOpS '* (varS 'a) (varS 'b))))))
(test (parse '(ifzero 4 5 6))(ifZeroS (numS 4)(numS 5)(numS 6)))
(test (parse '(ifzero (- 3 4) 5 6))(ifZeroS
                                    (binaryOpS '- (numS 3)(numS 4))
                                    (numS 5)(numS 6)))
(test (parse '(set! x 6)) (setS 'x (numS 6)))
(test (parse '(seq! (set! x 7) (+ 3 4))) (seqS (setS 'x (numS 7))
                                               (binaryOpS '+ (numS 3)(numS 4))))
(test (parse '(rec fact 
                (λ (n) (ifzero n 1 (* n (fact ((- n 1))))))
                (fact (10)))) (recS 'fact (lamS (list 'n)
                                                (ifZeroS (varS 'n) (numS 1)
                                                         (binaryOpS
                                                          '*
                                                          (varS 'n)
                                                          (appS (varS 'fact) (list (binaryOpS '- (varS 'n) (numS 1)))))))
                                    (appS (varS 'fact) (list (numS 10)))))

; Grammar for ExprD. (Desugared abstract syntax)
(define-type ExprD
  [numD (n : number)]
  [varD (s : symbol)]
  [appD (fun : ExprD)(params : (listof ExprD))]
  [lamD (params : (listof symbol)) (body : ExprD)]
  [binaryOpD (op : symbol)(l : ExprD)(r : ExprD)]
  [ifZeroD (pred : ExprD)(trueState : ExprD)(falseState : ExprD)]
  [setD (var : symbol)(val : ExprD)]
  [seqD (b1 : ExprD)(b2 : ExprD)]
  [dumD (s : symbol)])

;; desugar : ExprS -> ExprD
;; Purpose : To desugar given ExprS which is surface language to desugared abstract syntax ExprD.
;;           - Kind of macro expansion.  
;; Template : 
;(define (desugar [exprS : ExprS]) : ExprD
;  (type-case ExprS exprS
;    [numS (n) ...]
;    [varS (s) ...]
;    [appS (fun params) ...]
;    [lamS (params body) ...]
;    [binaryOpS (op l r) ...]
;    [ifZeroS (pred trueState falseState) ...]
;    [setS (s v) ...]
;    [seqS (s1 s2) ...]
;    [recS (n v b ) ...]
;    ))

(define (desugar [exprS : ExprS]) : ExprD
  (type-case ExprS exprS
    [numS (n) (numD n)]
    [varS (s) (varD s)]
    [appS (fun params)(appD (desugar fun)
                            (map (lambda (x)(desugar x)) params))]
    [lamS (params body)(lamD params (desugar body))]
    [binaryOpS (op l r)(binaryOpD op
                                  (desugar l)
                                  (desugar r))]
    [ifZeroS (pred trueState falseState)
             (ifZeroD (desugar pred)
                      (desugar trueState)
                      (desugar falseState))]
    [setS (s v)(setD s (desugar v))]
    [seqS (s1 s2)(seqD (desugar s1) (desugar s2))]
    [recS (n v b)(appD (lamD (list n)
                             (seqD (setD n (desugar v)) (desugar b)))
                       (list (dumD 'dummy)))]
    ))

;; Tests :
(test (desugar (parse (number->s-exp 3)))(numD 3))
(test (desugar (parse (symbol->s-exp 'x)))(varD 'x))
(test (desugar (parse '(+ 3 4)))(binaryOpD '+ (numD 3)(numD 4)))
(test (desugar (parse '(λ (x y)(λ (a b)(+ (* x y)(* a b))))))
      (lamD
       (list 'x 'y)
       (lamD
        (list 'a 'b)
        (binaryOpD
         '+
         (binaryOpD '* (varD 'x) (varD 'y))
         (binaryOpD '* (varD 'a) (varD 'b))))))
(test (desugar (parse '(ifzero 4 5 6)))(ifZeroD (numD 4)(numD 5)(numD 6)))
(test (desugar (parse '(set! x 6))) (setD 'x (numD 6)))
(test (desugar (parse '(seq! (set! x 7) (+ 3 4)))) (seqD (setD 'x (numD 7))
                                                         (binaryOpD '+ (numD 3)(numD 4))))
(test (desugar (parse '(rec fact (λ (n) (ifzero n 1 (* n (fact ((- n 1))))))(fact (10)))))
      (appD (lamD (list 'fact) (seqD (setD 'fact (lamD (list 'n)
                                                       (ifZeroD (varD 'n) (numD 1)
                                                                (binaryOpD
                                                                 '*
                                                                 (varD 'n)
                                                                 (appD (varD 'fact) (list (binaryOpD '- (varD 'n) (numD 1))))))))
                                     (appD (varD 'fact) (list (numD 10))))) (list (dumD 'dummy))))



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


; Grammar for ExprC.
(define-type ExprC
  [numC (n : number)]
  [varC (id : Pair)]
  [appC (fun : ExprC)(params : (listof ExprC))]
  [lamC (params : number) (body : ExprC)]
  [binaryOpC (op : symbol)(l : ExprC)(r : ExprC)]
  [ifZeroC (pred : ExprC)(trueState : ExprC)(falseState : ExprC)]
  [setC (var : Pair)(val : ExprC)]
  [seqC (b1 : ExprC)(b2 : ExprC)]
  [dumC (s : symbol)])

;; debruijnize-helper : ExprD number (listof (listof Pair)) -> ExprC
;; Purpose : Change variables with de bruijn numbers.
;; Template : 
;(define (debruijnize-helper [exprD : ExprD] [name-pairs : (listof (listOf Pair))) : ExprC
;  (type-case ExprD exprD
;    [numD (n) ...]
;    [idD (s) ...]
;    [appD (fun params) ...]
;    [lamD (params body) ...]
;    [binaryOpD (op l r) ...]
;    [ifZeroD (pred trueState falseState) ...]
;    [setD (s v) ...]
;    [seqD (s1 s2) ...]
;    [dumD (s) ...]
;    ))

(define (debruijnize-helper [exprD : ExprD] [name-pairs : (listof (listof Pair))]) : ExprC
  (type-case ExprD exprD
    [numD (n) (numC n)]
    [varD (s) (varC (assoc-name s name-pairs))]
    [appD (fun params) (appC 
                        (debruijnize-helper fun name-pairs)
                        (map (λ (x) (debruijnize-helper x name-pairs)) params))]
    [lamD (params body)(let 
                           ((new-name-pairs (convert-params params name-pairs)))
                         (lamC 
                          (length params)
                          (debruijnize-helper body new-name-pairs)))] 
    [binaryOpD (op l r)(binaryOpC op
                                  (debruijnize-helper l name-pairs)
                                  (debruijnize-helper r name-pairs))]
    [ifZeroD (pred trueState falseState)
             (ifZeroC (debruijnize-helper pred name-pairs)
                      (debruijnize-helper trueState name-pairs)
                      (debruijnize-helper falseState name-pairs))]
    [setD (s v)(setC (assoc-name s name-pairs)(debruijnize-helper v name-pairs))]
    [seqD (s1 s2)(seqC 
                  (debruijnize-helper s1 name-pairs)
                  (debruijnize-helper s2 name-pairs))]
    [dumD (s)(dumC s)]
    ))

;; Tests :
(test (debruijnize-helper (desugar (parse (number->s-exp 5))) empty)(numC 5))
(test/exn (debruijnize-helper (desugar (parse (symbol->s-exp 'x))) empty) 
          "Name-pair not found!")
(test (debruijnize-helper (desugar (parse (symbol->s-exp 'x)))
                          (list (list (name-bruijn 'x (de-bruijn 1 2)))))
      (varC (de-bruijn 1 0)))
(test (debruijnize-helper (desugar (parse '(+ 3 4))) empty)(binaryOpC '+ (numC 3)(numC 4)))
(test (debruijnize-helper (desugar (parse '(* 3 4))) empty)(binaryOpC '* (numC 3)(numC 4)))
(test (debruijnize-helper (desugar (parse '(- x x)))
                          (list (list (name-bruijn 'x (de-bruijn 1 2)))))
      (binaryOpC '- 
                 (varC (de-bruijn 1 0))
                 (varC (de-bruijn 1 0))))
(test (debruijnize-helper (desugar (parse '(/ x x))) 
                          (list (list (name-bruijn 'x (de-bruijn 1 2)))))
      (binaryOpC '/ 
                 (varC (de-bruijn 1 0))
                 (varC (de-bruijn 1 0))))
(test (debruijnize-helper (desugar (parse '(ifzero 4 5 6))) empty) 
      (ifZeroC (numC 4)(numC 5)(numC 6)))
(test (debruijnize-helper (desugar (parse
                                    '((((λ (x) (λ (y) (λ (z) (+ (+ x y) z))))(3))(4))(5)))) 
                          empty)
      (appC (appC (appC (lamC 1 (lamC 1 (lamC 1 
                                              (binaryOpC '+ 
                                                         (binaryOpC '+ 
                                                                    (varC (de-bruijn 0 2))
                                                                    (varC (de-bruijn 0 1)))
                                                         (varC (de-bruijn 0 0))))))
                        (list (numC 3))) (list (numC 4))) (list (numC 5))))
(test (debruijnize-helper (desugar (parse 
                                    '(((λ (a b c) (λ (d e)(+ d e)))(3 4 5))(8 10)))) empty)
      (appC (appC (lamC 3 (lamC 2 
                                (binaryOpC '+ (varC (de-bruijn 0 0))
                                           (varC (de-bruijn 1 0)))))
                  (list (numC 3) (numC 4) (numC 5))) (list (numC 8) (numC 10))))
(test (debruijnize-helper (desugar (parse '(set! x 6)))
                          (list (list (name-bruijn 'x (de-bruijn 1 2)))))
      (setC (de-bruijn 1 0) (numC 6)))
(test (debruijnize-helper (desugar (parse '(seq! (set! x 7) (+ 3 4))))
                          (list (list (name-bruijn 'x (de-bruijn 1 2))))) 
      (seqC (setC (de-bruijn 1 0) (numC 7))
            (binaryOpC '+ (numC 3)(numC 4))))
(test (debruijnize-helper (desugar (parse '(rec fact 
                                             (λ (n) (ifzero n 1 (* n (fact ((- n 1))))))
                                             (fact (10))))) empty)
      (appC (lamC 1 (seqC (setC (de-bruijn 0 0)
                                (lamC 1
                                      (ifZeroC (varC (de-bruijn 0 0)) (numC 1)
                                               (binaryOpC
                                                '*
                                                (varC (de-bruijn 0 0))
                                                (appC
                                                 (varC (de-bruijn 0 1))
                                                 (list (binaryOpC '- (varC (de-bruijn 0 0)) (numC 1))))))))
                          (appC (varC (de-bruijn 0 0)) (list (numC 10))))) (list (dumC 'dummy))))

;; debruijnize : ExprD -> ExprC
;; Purpose : To debruijnize (identifiers or variables) given ExprD which is desugared language to core abstract syntax ExprC.
;; Template : 
;(define (debruijnize [exprD : ExprD]) : ExprC
;  (type-case ExprD exprD
;    [numS (n) ...]
;    [idS (s) ...]
;    [appS (fun params) ...]
;    [lamS (params body) ...]
;    [binaryOpS (op l r) ...]
;    [ifZeroS (pred trueState falseState) ...]
;    [setS (s v) ...]
;    [seqS (s1 s2) ...]
;    ))

(define (debruijnize [exprD : ExprD]) : ExprC
  (debruijnize-helper exprD empty))

;; Tests are included above with helper since this just a call for it.


;; ===================================================================================
;; ===================================================================================
;; ==== Interpretation phase
;; ===================================================================================
;; ===================================================================================


;; Location is an abstract name for a number, which represents location of
;; - a variable stored in memory.
(define-type-alias Location number)

;; A data-type for values in language.
(define-type Value
  [numV (n : number)]
  [closV (params : number) (body : ExprC) (env : Environment)]
  [dummyV (s : symbol)])

;; A data-type for results in language,
;; - since it has an interpreter with store-passing.
(define-type Result
  [v*s (v : Value)(s : Store)])

;; Binding is a data type to bind location of value in the storage with de Bruijn numbers,
;; - which are lexical informatio of identifiers.
(define-type Binding
  [bind (actual-params : (vectorof Location))])

;; Environment is a repository for lexical information, which represented as list.
;; - but as special kind of list which contains only bindings.
(define-type-alias Environment (listof Binding))

;; Empty environment.
(define mt-env empty)

;; Extending environment a wrapper around cons.
(define extend-env cons)

;; Storage is an another kind of data-type which holds values of identifiers,
;; - in the context.
(define-type Storage
  [cell (location : Location)(value : Value)])

;; Store is an another kind of repository which holds Storages.
(define-type-alias Store (listof Storage))

;; Empty store.
(define mt-sto empty)

;; Overriding store or extending store in case of some sense of transactional memmory.
;; If we want to switch between strategies magic happens here.
(define override-store cons)

; bin-op-wrap : (number number -> number) numV numV -> numv
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

;; lookup : Pair (listof Bindings) -> Location
;; Purpose : To find given de Bruijn pair's location
;;           - from environment(listof bindings).
;; Template : Basic Structural Recursion
; (define (lookup [for : Pair] [env : Environment]) : Location
;  (cond
;    [(empty? env) ...]
;    [else ...(first env) ...(lookup (rest env))])

(define (lookup [for : Pair] [env : Environment]) : Location
  (vector-ref 
   (bind-actual-params (list-ref env (de-bruijn-env-depth for)))
   (de-bruijn-param-pos for)))


;; Tests :
(test (lookup (de-bruijn 0 0)(list (bind (vector 5 6)))) 5)
(test (lookup (de-bruijn 1 0)(list (bind (vector 5 6)))) 6)
(test (lookup (de-bruijn 1 0)(list 
                              (bind (vector 2 3 3))
                              (bind (vector 5 6)))) 3)
(test (lookup (de-bruijn 1 1)(list 
                              (bind (vector 2 3 3))
                              (bind (vector 5 6)))) 6)
(test (lookup (de-bruijn 2 0)(list 
                              (bind (vector 2 3 7))
                              (bind (vector 5 6)))) 7)


;; fetch : number (listof Storage) -> Value
;; Purpose : To find value in the store(listof Storage) at given location.
;; Template
;(define (fetch [loc : Location] [sto : Store]) : Value
;    ...)

(define (fetch [loc : Location] [sto : Store]) : Value
  (cond
    [(empty? sto)(error 'fetch "No value found at given location.")]
    [else (if (= loc (cell-location (first sto)))
              (cell-value (first sto))
              (fetch loc (rest sto)))]))

;; NOTE THAT: This piece of code works fine with both transactional memmory approach and
;; - find and replace approach (mutative storage).
;; Because linearly searching and finding first occurence of given location.

;; Tests:
(test/exn (fetch 1 empty) "No value found at given location.")
(test (fetch 1 (list (cell 1 (numV 5)))) (numV 5))
(test (fetch 1 (list (cell 2 (numV 3))(cell 1 (numV 5)))) (numV 5))
(test/exn (fetch 3 (list (cell 2 (numV 3))(cell 1 (numV 5)))) "No value found at given location.")
(test (fetch 1 (list (cell 1 (numV 3))(cell 2 (numV 3))(cell 1 (numV 5)))) (numV 3))

;; Interpreter has deBruijnized identifiers and multiple parameters,
;; - therefore, it has a need for a wrapper type to pass them througly. 
(define-type FunctionApplicationWrapper
  [str*env (str : Store)(env : Environment)])

;; interp : ExprC (listof Bindings) -> Result
;; Purpose : To interpret expressions to results.
;; Template :
; (define (interp [expr : ExprC] [env : Environment][sto : Store]) : Value
;  (type-case ExprC in
;    [numC (n) ...]
;    [varC (s) ...]
;    [appC (fun params) ...]
;    [binaryOpC (l r) ...]
;    [lamC (params body) ...]
;    [ifZeroC (pred t f)...]
;    [setC (var val) ...]
;    [seqC (b1 b2) ...]))

(define (interp [expr : ExprC] [env : Environment] [sto : Store]) : Result
  (local
    ;; NOTE THAT: Unfortunately this is here, because plai-typed language doesn't allow
    ;; -- mutually recursive function. It has to be here !! Also it is written in a mutative
    ;; -- approach since topic is mutation it perfectly fits.
    ;; bind-parameters : number (listof ExprC) Environment Store -> FunctionApplicationWrapper
    ;; Purpose : To bind multiple formal parameters with interpreted actual parameters.
    ([define (bind-parameters 
              [number-of-formal-param : number][actual-params : (listof ExprC)]
              [env : Environment][sto : Store]) : FunctionApplicationWrapper                                      
       (cond
         [(not (= number-of-formal-param (length actual-params)))
          (error 'bind-parameters "Invalid number of parameters!")]
         [else 
          ;; param-locs => (listof Locations)
          (let ([param-locs empty]
                [param-store sto])
            (str*env
             (begin
               (map (λ (x)
                      (type-case Result (interp x env param-store)
                        [v*s (v-x s-x)
                             (let ([where (new-loc)])
                               (begin
                                 (set!
                                  param-locs
                                  (cons where param-locs))
                                 (set!
                                  param-store
                                  (override-store (cell where v-x) param-store))))]))
                    actual-params)
               param-store)
             (extend-env (bind (list->vector (reverse param-locs))) env)))]
         )])
    (type-case ExprC expr
      [numC (n) (v*s (numV n) sto)]
      [varC (s) (v*s (fetch (lookup s env) sto) sto)]
      [appC (f params)
            (type-case Result (interp f env sto)
              [v*s (v-f s-f)
                   (let ([interpreted-parameters 
                          (bind-parameters
                           (closV-params v-f)
                           params
                           (closV-env v-f)
                           s-f)])
                     (interp (closV-body v-f)
                             (str*env-env interpreted-parameters)
                             (str*env-str interpreted-parameters)
                             ))])]
      [binaryOpC (op l r)(type-case Result (interp l env sto)
                           [v*s (v-l s-l)
                                (type-case Result (interp r env s-l)
                                  [v*s (v-r s-r)
                                       (v*s 
                                        (bin-op-wrap (get-op op) v-l v-r)
                                        s-r)])])]
      [lamC (params body) (v*s (closV params body env) sto)]
      [ifZeroC (pred t f)(type-case Result (interp pred env sto)
                           [v*s (v-p s-p)
                                (if (= (numV-n v-p) 0)
                                    (interp t env s-p)
                                    (interp f env s-p))])]
      [setC (var val) (type-case Result (interp val env sto)
                        [v*s (v-val s-val)
                             (let ([where (lookup var env)])
                               (v*s v-val
                                    (override-store (cell where v-val)
                                                    s-val)))])]
      [seqC (b1 b2) (type-case Result (interp b1 env sto)
                      [v*s (v-b1 s-b1)
                           (interp b2 env s-b1)])]
      [dumC (s)(v*s (dummyV s) sto)]
      )))

;; eval : s-exp -> number
;; Purpose : A wrapper function to evaluate s-exp through our language.
(define (eval (sexp : s-expression)) : number
  (numV-n (v*s-v (interp (debruijnize (desugar (parse sexp))) mt-env mt-sto))))

;; Tests:
(test (eval '(+ 3 4)) 7)
(test (eval '(* 3 4)) 12)
(test (eval '(/ 3 4)) (/ 3 4))
(test (eval '(- 3 4)) -1)
(test (eval '((λ (x) x) (5))) 5)
(test (eval '((λ (x) (* x x)) (4))) 16)
(test (eval '((λ (x) (* x -1)) (4))) -4)
(test (eval '(((λ (x) (λ (y) (+ x y))) (3)) (4))) 7)
(test (eval '((((λ (x) (λ (y) (λ (z) (+ (+ x y) z))))(3))(4))(5))) 12)
(test (eval '(((λ (a b c) (λ (d e)(+ a e)))(3 4 5))(8 10))) 13)
(test (eval '(((λ (a b c) (λ (d e)(+ d e)))(3 4 5))(8 10))) 18)
(test/exn (eval '(set! x 5)) "Name-pair not found!")
;; Ab uno disce omnes !!!
(test (eval '((λ (x)(seq! (set! x 3) (+ x 3))) (5))) 6)
(test (eval '(((λ (a b c)
                 (λ (d e)
                   (seq! (seq! (set! d 1)(set! e 1))(+ d e))))(3 4 5))(8 10))) 2)
(test (eval '(rec fact 
               (λ (n) (ifzero n 1 (* n (fact ((- n 1))))))
               (fact (0)))) 1)
(test (eval '(rec fact 
               (λ (n) (ifzero n 1 (* n (fact ((- n 1))))))
               (fact (1)))) 1)