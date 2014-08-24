; Grammar for ExprC.
(define-type ExprC
  [numC (n : number)]
  [idC (s : symbol)]
  [appC (fun : ExprC)(args : (listof ExprC))]
  [lamC (args : (listof symbol)) (body : ExprC)]
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
            [(λ)(lamC (map (lambda (x)(s-exp->symbol x)) 
                           (s-exp->list (second sl)))
                      (parse (third sl)))]
            [else (binaryOpC (s-exp->symbol (first sl)) 
                             (parse (second sl)) (parse (third sl)))])]
         [(= (length sl) 2)
          (appC (parse (first sl))
                (map (lambda (x) (parse x))
                     (s-exp->list (second sl))))]
         [else (error 'parse "invalid list input")])
       )]
    [else (error 'parse "invalid input")]))

