#lang plai-typed

;; Comp314 - 2nd Project
;; Kemal Akkoyun
;; 11076004

;; Sources : Chris Stephenson's Comp314 Lectures, Videos and Notes.
;; Book : http://cs.brown.edu/courses/cs173/2012/book
;; .plt Source : http://cs.brown.edu/courses/cs173/2012/lang/
;; =========================================================== ;;


;; CLASSWORK 
;; =========================================================== ;;

;; λ-expression grammar
;; λ-exp -> v
;; λ-exp -> (λ-exp λ-exp)
;; λ-exp -> (λ v λ-exp)
;; where v is a symbol.

;; λ-exp is an abstract syntax grammar or a parse tree definition for
;; - λ-exp that defined above.
(define-type λ-exp
  (λ-sym (v : symbol))
  (λ-app (l : λ-exp)(r : λ-exp))
  (λ-def (v : symbol)(p : λ-exp))
  )

;; Tests:
(λ-sym 'x)
(λ-app (λ-sym 'x)(λ-sym 'y))
(λ-def 'v (λ-app (λ-sym 'x)(λ-sym 'y)))

;; parse : s-exp -> λ-exp
;; Purpose : To transform given s-expression to corresponding
(define (parse (sexp : s-expression)) : λ-exp
  (cond
    [(s-exp-symbol? sexp)(λ-sym (s-exp->symbol sexp))]
    [(s-exp-list? sexp)
     (let ([sexp-list (s-exp->list sexp)])
       (cond
         [(= 2 (length sexp-list))
          (λ-app (parse (first sexp-list))(parse (second sexp-list)))]
         [(= 3 (length sexp-list))
          (if (and (symbol=? 'λ (s-exp->symbol (first sexp-list)))
                   (s-exp-symbol? (second sexp-list)))
              (λ-def (s-exp->symbol(second sexp-list))
                     (parse (third sexp-list)))
              (error 'parse "Not valid λ-definition")
              )]
         [else (error 'parse "Not valid length λ-exp")]
         ))]
    [else (error 'parse "Not valid λ-exp")]
    ))

;; Tests:
(test (parse (symbol->s-exp 'y))(λ-sym 'y))
(test (parse '(λ x x))(λ-def 'x (λ-sym 'x)))
(test (parse '((λ x x) y))(λ-app (λ-def 'x (λ-sym 'x)) (λ-sym 'y)))
(test (parse '((λ x x)(λ y y)))
      (λ-app (λ-def 'x (λ-sym 'x))(λ-def 'y (λ-sym 'y))))
(test (parse '(λ x (λ y (y x))))
      (λ-def 'x (λ-def 'y (λ-app (λ-sym 'y) (λ-sym 'x)))))


;; unparse : λ-exp -> s-exp
;; Purpose : To produce concrete syntax from given abstract syntax.
(define (unparse (le : λ-exp)) : s-expression
  (type-case λ-exp le
    (λ-sym (v) (symbol->s-exp v))
    (λ-app (l r)(list->s-exp (list (unparse l)(unparse r))))
    (λ-def (v p)(list->s-exp 
                 (list (symbol->s-exp 'λ)(symbol->s-exp v)(unparse p))))
    ))

;; Test:
(test (unparse (λ-sym 'y))(symbol->s-exp 'y))
(test (unparse (λ-def 'x (λ-sym 'x))) '(λ x x))
(test (unparse (λ-app (λ-def 'x (λ-sym 'x)) (λ-sym 'y)))
      '((λ x x) y))
(test (unparse (λ-app (λ-def 'x (λ-sym 'x))(λ-def 'y (λ-sym 'y))))
      '((λ x x)(λ y y)))
(test (unparse (λ-def 'x (λ-def 'y (λ-app (λ-sym 'y) (λ-sym 'x)))))
      '(λ x (λ y (y x))))

;; =========================================================== ;;

;; ASSIGNMENT
;; =========================================================== ;;

;; FUNCTION SQUARER : (λ f (λ x (f (f x))))
;; FUNCTION CUBER : (λ g (λ x (g (g (g x)))))

;; NAIVE ALPHA-TRANSFORMATION: (λ x M) --> (λ y [M:x=y])
;; NAIVE BETA-TRANSFORMATION : ((λ x M) N) --> [M:x=N]

;; Examples:
;; (1)
;; (SQUARER (CUBER g))
;; (SQUARER (λ g (λ x (g (g (g x))))))
;; ((λ f (λ x (f (f x)))) (λ g (λ x (g (g (g x))))))
;; Apply (SQUARER ((CUBER g) x))
;; ((λ f (λ x (f (f x)))) ((λ g (λ x (g (g (g x)))) x)))
;; NAIVE BETA-TRANSFORMATION ((CUBER g) x))
;; ((λ f (λ x (f (f x)))) (g (g (g x))))
;; NAIVE BETA-TRANSFORMATION ((SQUARER f)(g (g (g x)))))
;; (λ x (g (g (g (g (g (g (g (g (g x)))))))))

;; (2)
;; (CUBER (SQUARER g))
;; (CUBER (λ g (λ x (g (g x)))))
;; ((λ f (λ x (f (f (f x))))) (λ g (λ x (g (g x)))))
;; Apply (CUBER ((SQUARER g) x))
;; ((λ f (λ x (f (f (f x))))) (λ g ((λ x (g (g x))) x)))
;; NAIVE BETA-TRANSFORMATION ((SQUARER g) x))
;; ((λ f (λ x (f (f (f x))))) (g (g x))))
;; NAIVE BETA-TRANSFORMATION ((CUBER f)(g (g x))))
;; (λ x (g (g (g (g (g (g (g (g (g x)))))))))


;; substituter : λ-exp  symbol  λ-exp -> λ-exp

;; Purpose : Substitution is the act of replacing a name 
;; - (in this case, that of the formal parameter) in an expression 
;; - (in this case, the body of the function) with another expression 
;; - (in this case, the actual parameter). [Directly from book.]

;; Template:
;; (define 
;; (substituter [what : λ-exp] [for : symbol] [in : λ-exp]) : λ-exp  
;; <subst-body>
;;)

(define (substituter [what : λ-exp] [for : symbol] [in : λ-exp]) : λ-exp 
  (type-case λ-exp in
    (λ-sym (v) (if (symbol=? v for) 
                   what
                   in))
    (λ-app (l r) (λ-app (substituter what for l)
                        (substituter what for r)))
    (λ-def (v p)(λ-def v (substituter what for p)))
    )
  )

;; beta-transformer : ((λ x M) N) --> [M:x=N]
;; beta-transformer : λ-exp -> λ-exp

;; Purpose : λ-calculus beta-reduction naive implementation.

;; Template :
;(define (beta-transform (le : λ-exp)) : λ-exp
;  (type-case λ-exp le
;    (λ-sym (v) ...)
;    (λ-app (l r)
;                  ... l
;                  ... r
;    ))

(define (beta-transformer (le : λ-exp)) : λ-exp
  (type-case λ-exp le
    (λ-sym (v) le) ;; or (λ-sym v)
    (λ-app (l r) (if (λ-def? l)
                     (substituter r (λ-def-v l) (λ-def-p l))
                     (λ-app (beta-transformer l) (beta-transformer r))))
    (λ-def (v p) (λ-def v (beta-transformer p)))))

;; Test and Examples:
;; Because of unhandled identifier capture problem,
;; - need different identifiers.
; DOUBLE
(define SQUARER
  (parse '(λ f (λ x (f (f x))))))
; TRIPLE
(define CUBER
  (parse '(λ f (λ x (f (f (f x)))))))

(define SQUARER-2 
  (parse '(λ g (λ y (g (g y))))))

(define CUBER-2
  (parse '(λ g (λ y (g (g (g y)))))))

(define EX1 
  (λ-app SQUARER CUBER-2))

(define EX2
  (λ-app SQUARER SQUARER-2))

;; Example 1)
(test
 (beta-transformer
  (beta-transformer 
   (beta-transformer 
    (beta-transformer 
     (beta-transformer 
      (beta-transformer 
       (beta-transformer 
        (beta-transformer 
         (beta-transformer EX1)))))))))
 (λ-def 'x 
        (λ-def 'y 
               (λ-app (λ-sym 'x)
                      (λ-app (λ-sym 'x)
                             (λ-app (λ-sym 'x)
                                    (λ-app (λ-sym 'x)
                                           (λ-app (λ-sym 'x)
                                                  (λ-app (λ-sym 'x)
                                                         (λ-app (λ-sym 'x)(λ-app (λ-sym 'x)(λ-app (λ-sym 'x) (λ-sym 'y)))))))))))))

;; Example 2)
(test (beta-transformer 
       (beta-transformer 
        (beta-transformer 
         (beta-transformer 
          (beta-transformer EX2)))))
      (λ-def 'x (λ-def 'y (λ-app (λ-sym 'x)(λ-app (λ-sym 'x)(λ-app (λ-sym 'x)(λ-app (λ-sym 'x) (λ-sym 'y))))))))
      