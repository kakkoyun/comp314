#lang plai-typed

;; 1st Chanpeter
;; =========================================================== ;;
(define-type MisspelledAnimal  
  [caml (humps : number)]
  [yacc (height : number)])

(caml 2)
(yacc 1.9)

(define ma1 : MisspelledAnimal (caml 2))
(define ma2 : MisspelledAnimal (yacc 1.9))

(define ma3 (caml 2))
(define ma4 (yacc 1.9))

(define (good? [ma : MisspelledAnimal]) : boolean
  (type-case MisspelledAnimal ma
    [caml (humps) (>= humps 2)]
    [yacc (height) (> height 2.1)]))

(test (good? ma1) #t)
(test (good? ma2) #f)

(define (good?-better [ma : MisspelledAnimal]) : boolean
  (type-case MisspelledAnimal ma
    [caml (h) (>= h 2)]
    [yacc (h) (> h 2.1)]))

(define (good?-without-pattern-matching [ma : MisspelledAnimal]) : boolean
  (cond
    [(caml? ma) (>= (caml-humps ma) 2)]
    [(yacc? ma) (> (yacc-height ma) 2.1)]))

;; 2nd Chapter
;; =========================================================== ;;

(define-type ArithC
  [numC (n : number)]
  [plusC (l : ArithC) (r : ArithC)]
  [multC (l : ArithC) (r : ArithC)])

(define (parse-v1 [s : s-expression]) : ArithC
  (cond
    [(s-exp-number? s) (numC (s-exp->number s))]
    [(s-exp-list? s)
     (let ([sl (s-exp->list s)])
       (case (s-exp->symbol (first sl))
         [(+) (plusC (parse-v1 (second sl)) (parse-v1 (third sl)))]
         [(*) (multC (parse-v1 (second sl)) (parse-v1 (third sl)))]
         [else (error 'parse-v1 "invalid list input")]))]
    [else (error 'parse-v1 "invalid input")]))

(test (parse-v1 '(+ (* 1 2) (+ 2 3)))
      (plusC
       (multC (numC 1) (numC 2))
       (plusC (numC 2) (numC 3))))

;; 3rd Chapter
;; =========================================================== ;;

;; Template
;(define (interp [a : ArithC]) : number
;  (type-case ArithC a
;    [numC (n) n]
;    [plusC (l r) ...]
;    [multC (l r) ...]))

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

;; 4th Chapter
;; =========================================================== ;;

(define-type ArithS
  [numS (n : number)]
  [plusS (l : ArithS) (r : ArithS)]
  [bminusS (l : ArithS) (r : ArithS)]
  [multS (l : ArithS) (r : ArithS)]
  [uminusS (e : ArithS)]
  )


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

(define (set-union s1 s2)
 (foldr (lambda (x y)
          (if (member x y)
              y
              (cons x y))) empty
                           (append s1 s2)))

(define (set-difference s1 s2)
  (filter (lambda (x)
            (not (member x s2)))
          s1))

(define (free-identifier (le : λ-exp))
 (type-case λ-exp le
   (λ-sym (v) (list v))
   (λ-app (l r)(set-union 
                (free-identifier l)
                (free-identifier l)))
   (λ-def (v p)(set-difference (free-identifier p)
                               (list v)))
  ))
