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

;; Grammar of surface language for Arith.
(define-type ArithS
  [numS (n : number)]
  [plusS (l : ArithS) (r : ArithS)]
  [bminusS (l : ArithS) (r : ArithS)]
  [multS (l : ArithS) (r : ArithS)]
  [uminusS (e : ArithS)]
  )

;; Grammar of core language for Arith.
(define-type ArithC
  [numC (n : number)]
  [plusC (l : ArithC) (r : ArithC)]
  [multC (l : ArithC) (r : ArithC)])

;; parse : s-exp -> ArithS
;; Purpose : To parse given s-exp to surface abstract syntax of Arith.
;; Template :
;(define (parse [s : s-expression]) : ArithS
;  (type-case
;    [numS ...]
;    [plusS ...l ...r]
;    [bminusS ...l ...r]
;    [multS ...l ...r]
;    [uminusS ...e]
;    ))

(define (parse [s : s-expression]) : ArithS
  (cond
    [(s-exp-number? s) (numS (s-exp->number s))]
    [(s-exp-list? s)
     (let ([sl (s-exp->list s)])
       (cond 
         [(= (length sl) 3)
          (case (s-exp->symbol (first sl))
            [(+) (plusS (parse (second sl)) (parse (third sl)))]
            [(*) (multS (parse (second sl)) (parse (third sl)))]
            [(-) (bminusS (parse (second sl)) (parse (third sl)))]
            [else (error 'parse "invalid list input")]
            )]
         [(= (length sl) 2)
          (case (s-exp->symbol (first sl))
            [(-) (uminusS (parse (second sl)))]
            [else (error 'parse "invalid list input")])]
         [else (error 'parse "invalid list input")]
         ))]
    [else (error 'parse "invalid input")]))

;; Tests:
(test (parse (number->s-exp 5))(numS 5))
(test (parse '(+ 3 4))(plusS (numS 3)(numS 4)))
(test (parse '(* (+ 3 4) 5))(multS (plusS (numS 3)(numS 4))(numS 5)))
(test (parse '(- (* (+ 3 4) 5) (+ 3 4)))
      (bminusS (multS (plusS (numS 3)(numS 4))(numS 5))
               (plusS (numS 3)(numS 4))))
(test (parse '(- 5))(uminusS (numS 5)))
(test (parse '(- (- (* (+ 3 4) 5) (+ 3 4))))
      (uminusS(bminusS (multS (plusS (numS 3)(numS 4))(numS 5))
                       (plusS (numS 3)(numS 4)))))

;; unparse : ArithS -> s-exp
;; Purpose : To produce concrete syntax from given abstract syntax.
;; Template :
;(define (unparse (as : ArithS)) : s-expression
;  (type-case
;    [numS ...]
;    [plusS ...l ...r]
;    [bminusS ...l ...r]
;    [multS ...l ...r]
;    [uminusS ...e]
;    ))

(define (unparse (as : ArithS)) : s-expression
  (type-case ArithS as
    [numS (n) (number->s-exp n)]
    [plusS (l r) (list->s-exp (list 
                               (symbol->s-exp '+)
                               (unparse l)
                               (unparse r)))]
    [multS (l r) (list->s-exp (list 
                               (symbol->s-exp '*)
                               (unparse l)
                               (unparse r)))]
    [bminusS (l r) (list->s-exp (list 
                                 (symbol->s-exp '-) 
                                 (unparse l)
                                 (unparse r)))]
    [uminusS (e) (list->s-exp (list 
                               (symbol->s-exp '-) 
                               (unparse e)))] 
    ))

;; Tests:
(test (unparse (numS 5))(number->s-exp 5))
(test (unparse (plusS (numS 3)(numS 4))) '(+ 3 4))
(test (unparse (multS (plusS (numS 3)(numS 4))(numS 5))) '(* (+ 3 4) 5))
(test (unparse (uminusS (numS 5))) '(- 5))
(test (unparse (parse '(- (- (* (+ 3 4) 5) (+ 3 4)))))
      '(- (- (* (+ 3 4) 5) (+ 3 4))))
(test (unparse (parse '(- (* (+ 3 4) 5) (+ 3 4))))
      '(- (* (+ 3 4) 5) (+ 3 4)))


;; desugar : ArithS -> ArihtC
;; Purpose : To desugar(which is a concept that explained in the book)
;; - given surface abstract syntax of language to core abstract syntax.
;; Template :
; (define (desugar [as : ArithS]) : ArithC
;  (type-case
;    [numS ...]
;    [plusS ...l ...r]
;    [bminusS ...l ...r]
;    [multS ...l ...r]
;    [uminusS ...e]
;    ))

(define (desugar [as : ArithS]) : ArithC
  (type-case ArithS as
    [numS (n) (numC n)]
    [plusS (l r) (plusC (desugar l)
                        (desugar r))]
    [multS (l r) (multC (desugar l)
                        (desugar r))]
    [bminusS (l r) (plusC (desugar l)
                          (multC (numC -1) (desugar r)))]
    [uminusS (e) (desugar (multS (numS -1) e))] 
    ))

;; Tests:
(test (desugar (numS 5))(numC 5))
(test (desugar (uminusS (numS 5))) (multC (numC -1) (numC 5)))
(test (desugar (parse '(+ 3 4)))
      (plusC (numC 3) (numC 4)))
(test (desugar (parse '(* (+ 3 4) 5))) 
      (multC (plusC (numC 3) (numC 4)) (numC 5)))
(test (desugar (parse '(- (* (+ 3 4) 5) (+ 3 4))))
      (plusC (multC (plusC (numC 3)(numC 4))(numC 5))
             (multC (numC -1)(plusC (numC 3)(numC 4)))))
(test (desugar (parse '(- (- (* (+ 3 4) 5) (+ 3 4)))))
      (multC (numC -1)(plusC (multC (plusC (numC 3)(numC 4))(numC 5))
                             (multC (numC -1)(plusC (numC 3)(numC 4))))))

;; interp : ArithC -> number
;; Purpose : To evaluate given abstract core syntax to number
;; Template :
;(define (interp [a : ArithC]) : number
;  (type-case ArithC a
;    [numC (n) n]
;    [plusC (l r) ... (interp l) ... (interp r) ...]
;    [multC (l r) ... (interp l) ... (interp r) ...]))

(define (interp [a : ArithC]) : number
  (type-case ArithC a
    [numC (n) n]
    [plusC (l r) (+ (interp l) (interp r))]
    [multC (l r) (* (interp l) (interp r))]))

;; Tests:
(test (interp (desugar (parse (number->s-exp 5)))) 5)
(test (interp (desugar (parse '(+ 3 4)))) 7)
(test (interp (desugar (parse '(* (+ 3 4) 5)))) 35)
(test (interp (desugar (parse '(- (* (+ 3 4) 5) (+ 3 4))))) 28)
(test (interp (desugar (parse '(- 5)))) -5)
(test (interp (desugar (parse '(- (- (* (+ 3 4) 5) (+ 3 4)))))) -28)

