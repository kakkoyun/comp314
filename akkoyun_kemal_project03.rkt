#lang plai-typed

;; Comp314 - 3rd Project
;; Kemal Akkoyun
;; 11076004

;; Sources : Chris Stephenson's Comp314 Lectures, Videos and Notes.
;; Book : http://cs.brown.edu/courses/cs173/2012/book
;; .plt Source : http://cs.brown.edu/courses/cs173/2012/lang/

;; =========================================================== ;;
;; CLASSWORK and ASSIGNMENT
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

;; A set represented as a list.
;; set-union : (listof symbol) (listof symbol) -> (listof symbol)
;; Purpose : To find the union of two sets.
(define (set-union (s1 : (listof symbol)) (s2 : (listof symbol))) : (listof symbol)
  (foldr (lambda (x y)
           (if (member x y)
               y
               (cons x y))) 
         empty
         (append s1 s2)))

;; Tests:
(test (set-union empty empty) empty)
(test (set-union empty (list 'x)) (list 'x))
(test (set-union (list 'x)(list 'x 'y)) (list 'x 'y))


;; set-difference : (listof symbol) (listof symbol) -> (listof symbol)
;; Purpose : To find the set difference of two sets.
(define (set-difference (s1 : (listof symbol))  (s2 : (listof symbol))) : (listof symbol)
  (filter (lambda (x)
            (not (member x s2)))
          s1))

;; Tests:
(test (set-difference empty (list 'x)) empty)
(test (set-difference (list 'x) empty) (list 'x))
(test (set-difference (list 'x)(list 'x 'y)) empty)
(test (set-difference (list 'x 'y)(list 'x))(list 'y))

;; free-identifier : λ-exp -> (listof symbol)
;; Purpose : To find free identifiers in given λ expression.
(define (free-identifier (le : λ-exp)) : (listof symbol)
  (type-case λ-exp le
    (λ-sym (v) (list v))
    (λ-app (l r)(set-union 
                 (free-identifier l)
                 (free-identifier r)))
    (λ-def (v p)(set-difference (free-identifier p)
                                (list v)))
    ))

;; Tests:
(test (free-identifier (parse (symbol->s-exp 'x))) (list 'x))
(test (free-identifier (parse '(λ x x))) empty)
(test (free-identifier (parse '(λ x y))) (list 'y))
(test (free-identifier (parse '((λ x y)(λ y z)))) (list 'y 'z))
(test (free-identifier (parse '((λ f y)(λ z z)))) (list 'y))
(test (free-identifier (parse '(λ x (λ y (y x))))) empty)
(test (free-identifier (parse '(λ x (λ y z)))) (list 'z))


;; bounded-identifier : λ-exp -> (listof symbol)
;; Purpose : To find bounded identifiers in given λ expression.
(define (bounded-identifier (le : λ-exp)) : (listof symbol)
  (type-case λ-exp le
    (λ-sym (v) empty)
    (λ-app (l r)(set-union 
                 (bounded-identifier l)
                 (bounded-identifier r)))
    (λ-def (v p)(set-union (bounded-identifier p)
                           (list v)))
    ))

;; Tests:
(test (bounded-identifier (parse (symbol->s-exp 'x))) empty)
(test (bounded-identifier (parse '(λ x x))) (list 'x))
(test (bounded-identifier (parse '(λ x y))) (list 'x))
(test (bounded-identifier (parse '((λ x y)(λ y z)))) (list 'x 'y))
(test (bounded-identifier (parse '((λ f y)(λ z z)))) (list 'f 'z))
(test (bounded-identifier (parse '(λ x (λ y (y x))))) (list 'y 'x))
(test (bounded-identifier (parse '(λ x (λ y z)))) (list 'y 'x))

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
    (λ-def (v p) (if (symbol=? v for)
                     in
                     (if (not (member v (free-identifier what)))
                         (λ-def v (substituter what for p))
                         (if (member for (free-identifier p))
                             (substituter what for 
                                          (alpha-transformer
                                           (generate-identifier in) in))
                             in))))
    )
  )

;; change-identifier : symbol symbol λ-exp -> λ-exp
;; Purpose: A helper function for alpha transformer,
;; - makes symbolic computation for changing given symbol in given λ-expression.
(define (change-identifier (what : symbol) (for : symbol) (in : λ-exp)) : λ-exp
  (type-case λ-exp in
    (λ-sym (v) (if (symbol=? v for) (λ-sym what) in))
    (λ-app (l r) (λ-app (change-identifier what for l)
                        (change-identifier what for r)))
    (λ-def (v p) (λ-def (if (symbol=? v for) what v)
                        (change-identifier what for p)))
    )
  )

;; Tests:
(test (change-identifier 'x 'v (parse '(λ v v)))(parse '(λ x x)))
(test (change-identifier 's 'y (λ-sym 'x)) (λ-sym 'x))
(test (change-identifier 's 'x (parse '(λ x x))) (parse '(λ s s)))
(test (change-identifier 's 'x (parse '((λ x x)(λ x x)))) 
      (parse '((λ s s)(λ s s))))

;; alpha-transformer : λ-exp -> λ-exp
;; Purpose : To apply alpha transformation on given λ-expression
;; (λ x M) --> (λ y [M:x=y])
(define (alpha-transformer (s : symbol) (le : λ-exp)) : λ-exp
  (type-case λ-exp le
    (λ-sym (v) le)
    (λ-app (l r) (λ-app (alpha-transformer s l)
                        (alpha-transformer s r)))
    (λ-def (v p) (λ-def s (change-identifier s v p)))
    ))

;; Test:
(test (alpha-transformer 's (λ-sym 'x)) (λ-sym 'x))
(test (alpha-transformer 's (parse '(λ x x))) (parse '(λ s s)))
(test (alpha-transformer 's (parse '((λ x x)(λ x x)))) 
      (parse '((λ s s)(λ s s))))

;; generate-identifier : λ-exp -> symbol
;; Purpose : To generate unpresented identifier.
(define (generate-identifier (le : λ-exp)) : symbol
  (let ((generated-symbol 'gensym))
    (if (or (member generated-symbol (bounded-identifier le))
            (member generated-symbol (free-identifier le)))
        (begin
          (set! generated-symbol 
                (string->symbol 
                 (string-append (symbol->string generated-symbol) "*")))
          generated-symbol)
        generated-symbol)
    )
  )

;; Test:
(test (generate-identifier (parse '(λ x (λ y (λ z x))))) 'gensym)
(test (generate-identifier (parse '(λ x (λ gensym (λ z x))))) 'gensym*)
(test (generate-identifier (parse '(λ x (λ y (λ z gensym))))) 'gensym)


;; UPDATED !!
;; beta-transformer : ((λ x M) N) --> [M:x=N]
;; beta-transformer : λ-exp -> λ-exp
;; Purpose : λ-calculus beta-reduction naive implementation.
;; Template :
;(define (beta-transform (le : λ-exp)) : λ-exp
;  (type-case λ-exp le
;    (λ-sym (v) ...)
;    (λ-app (l r) ... l ... r)
;    (λ-def (v p) ...v ...p)
;    ))
(define (beta-transformer (le : λ-exp)) : λ-exp
  (type-case λ-exp le
    (λ-sym (v) le)
    (λ-app (l r) 
           (if (λ-def? l)
               (beta-transformer
                (substituter r (λ-def-v l) (λ-def-p l)))
               (if (λ-def? (beta-transformer l))
                   (beta-transformer 
                    (λ-app (beta-transformer l) (beta-transformer r)))
                   (λ-app (beta-transformer l) (beta-transformer r)))))
    (λ-def (v p) (λ-def v (beta-transformer p)))))

;; General Tests and Examples:
(define SQUARER
  (parse '(λ f (λ x (f (f x))))))

(define CUBER
  (parse '(λ f (λ x (f (f (f x)))))))

(test (beta-transformer (parse '((λ x x) a)))
      (parse (symbol->s-exp 'a)))

(test (beta-transformer (parse '((λ x y) a)))
      (parse (symbol->s-exp 'y)))

(test (beta-transformer (parse '((λ x (a b)) k)))
      (parse '(a b)))

(test (beta-transformer (parse '((λ x (λ x y)) k)))
      (parse '(λ x y)))

(test (beta-transformer (parse '((λ x (λ y x)) k)))
      (parse '(λ y k)))

(test (beta-transformer (parse '((λ x (λ y (x y))) k)))
      (parse '(λ y (k y))))

(test (beta-transformer (parse '(((λ x (λ y (y x))) y ) x)))
      (parse '(x y)))

(test (beta-transformer (parse '((λ x (λ x x)) 'z)))
      (parse '(λ x x)))

(test (beta-transformer (parse '((λ x (λ y (x y))) y) ))
      (parse '(λ gensym (y gensym))))

(test (beta-transformer (parse '((λ x ((λ y z)(λ z x))) z)))
      (parse (symbol->s-exp 'z)))

(test (beta-transformer (λ-app SQUARER CUBER))
      (parse 
       '(λ x (λ gensym (x (x (x (x (x (x (x (x (x gensym)))))))))))))

(test (beta-transformer (λ-app SQUARER SQUARER))
      (parse '(λ x (λ gensym (x (x (x (x gensym))))))))

(test (beta-transformer (λ-app CUBER SQUARER))
      (parse '(λ x (λ gensym (x (x (x (x (x (x (x (x gensym))))))))))))
