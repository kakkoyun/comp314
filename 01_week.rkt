#lang plai-typed

;; Comp314 - 1st Project
;; Kemal Akkoyun
;; 11076004

;; Sources : Chris Stephenson's Comp314 Lectures, Videos and Notes.
;; Book : http://cs.brown.edu/courses/cs173/2012/book
;; .plt Source : http://cs.brown.edu/courses/cs173/2012/lang/

;; ======================================================================================= ;;

;; AE : Stands for Arithmetic Expression.
;; AE is a typed defined as follows,
;; Grammar in Backus-Naur Form:
;; AE ::= <number>
;; AE ::= (add <AE> <AE>)
;;      | (mul <AE> <AE>)
;;      | (sub <AE> <AE>)
;;      | (exp <AE> <AE>)
;;      | (div <AE> <AE>)
;;      | (exp <AE> <AE>)

(define-type AE
  (AEnumber (n : number))
  (AEadd (l : AE)(r : AE))
  (AEmultp (l : AE)(r : AE))
  (AEsubs (l : AE)(r : AE))
  (AEdiv (l : AE)(r : AE))
  (AEexp (l : AE)(r : AE))
  )

;; Tests:
(AEnumber 4)
(AEadd (AEnumber 3) (AEnumber 4))
(AEsubs (AEnumber 3) (AEnumber 4))
(AEmultp (AEnumber 3) (AEnumber 4))
(AEdiv (AEnumber 3) (AEnumber 4))
(AEexp (AEnumber 3) (AEnumber 4))
(AEadd (AEadd (AEnumber 3) (AEnumber 4)) (AEexp (AEnumber 3) (AEnumber 4)))

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

;; AE-Eval : AE -> number
;; Purpose: Arithmetic expression evaluator for AE type.
;; Template:
;(define (AE-Eval (ae : AE)) : number
;  (type-case AE ae
;    (AEnumber (n) n)
;    (AEadd (l r) ...)
;    (AEmultp (l r) ...)
;    (AEdiv (l r) ...)
;    (AEsubs (l r) ...)
;    (AEexp (l r) ...)
;    ))

(define (AE-Eval (ae : AE)) : number
  (type-case AE ae
    (AEnumber (n) n)
    (AEadd (l r) (+ (AE-Eval l) (AE-Eval r)))
    (AEmultp (l r) (* (AE-Eval l) (AE-Eval r)))
    (AEdiv (l r) (/ (AE-Eval l) (AE-Eval r)))
    (AEsubs (l r) (- (AE-Eval l) (AE-Eval r)))
    (AEexp (l r) (expt (AE-Eval l) (AE-Eval r)))
    ))

;; OR more prescriptively

(define (AE-Eval-2 (ae : AE)) : number
  (cond
    ((AEnumber? ae)(AEnumber-n ae))
    ((AEadd? ae) (+ (AE-Eval-2 (AEadd-l ae)) (AE-Eval-2 (AEadd-r ae))))
    ((AEmultp? ae) (* (AE-Eval-2 (AEmultp-l ae)) (AE-Eval-2 (AEmultp-r ae))))
    ((AEdiv? ae) (/ (AE-Eval-2 (AEdiv-l ae)) (AE-Eval-2 (AEdiv-r ae))))
    ((AEsubs? ae) (- (AE-Eval-2 (AEsubs-l ae)) (AE-Eval-2 (AEsubs-r ae))))
    ((AEexp? ae) (expt (AE-Eval-2 (AEexp-l ae)) (AE-Eval-2 (AEexp-r ae))))
    ))

;; Tests:
(test (AE-Eval (AEnumber 5)) 5)
(test (AE-Eval-2 (AEnumber 5)) 5)

(test (AE-Eval (AEadd (AEnumber 3) (AEnumber 4))) 7)
(test (AE-Eval-2 (AEadd (AEnumber 3) (AEnumber 4))) 7)

(test (AE-Eval (AEmultp (AEnumber 3) (AEnumber 4))) 12)
(test (AE-Eval-2 (AEmultp (AEnumber 3) (AEnumber 4))) 12)

(test (AE-Eval (AEsubs (AEnumber 4) (AEnumber 4))) 0)
(test (AE-Eval-2 (AEsubs (AEnumber 4) (AEnumber 3))) 1)

(test (AE-Eval (AEdiv (AEexp (AEnumber 3) (AEnumber 4)) (AEnumber 9))) 9)
(test (AE-Eval-2 (AEdiv (AEexp (AEnumber 3) (AEnumber 4)) (AEnumber 9))) 9)

;; parse-prefix : list of s-exp -> AE
;; Purpose: To parse given list of s-expression in prefix notation as string and cast it to AE.
(define (parse-prefix [s : s-expression]) : AE
  (cond
    [(s-exp-number? s) (AEnumber (s-exp->number s))]
    [(s-exp-list? s)
     (let ([sl (s-exp->list s)])
       (if (or (not (= (length sl) 3))(not (s-exp-symbol? (first sl))))
           (error 'parse-prefix "input contract violation!")
           (case (s-exp->symbol (first sl))
             [(+) (AEadd (parse-prefix (second sl)) (parse-prefix (third sl)))]
             [(*) (AEmultp (parse-prefix (second sl)) (parse-prefix (third sl)))]
             [(/) (AEdiv (parse-prefix (second sl)) (parse-prefix (third sl)))]
             [(-) (AEsubs (parse-prefix (second sl)) (parse-prefix (third sl)))]
             [(^) (AEexp (parse-prefix (second sl)) (parse-prefix (third sl)))]
             [else (error 'parse-prefix "invalid list input")])))]
    (else (error 'parse "invalid input"))))

;; Test:
(test (parse-prefix '(+ 2 3)) (AEadd (AEnumber 2)(AEnumber 3)))
(test (parse-prefix '(^ 2 (* 3 4))) (AEexp (AEnumber 2)(AEmultp (AEnumber 3)(AEnumber 4))))
(test (parse-prefix '(^ (+ 2 3) (* 3 4))) (AEexp  (AEadd (AEnumber 2)(AEnumber 3))(AEmultp (AEnumber 3)(AEnumber 4))))
;; (parse '(+ 2 3 3))
;; (parse '(2 3 3))

;; parse-infix : list of s-exp -> AE
;; Purpose: To parse given list of s-expression in infix notation as string and cast it to AE.
(define (parse-infix [s : s-expression]) : AE
  (cond
    [(s-exp-number? s) (AEnumber (s-exp->number s))]
    [(s-exp-list? s)
     (let ([sl (s-exp->list s)])
       (if (or (not (= (length sl) 3))(not (s-exp-symbol? (second sl))))
           (error 'parse-infix "input contract violation!")
           (case (s-exp->symbol (second sl))
             [(+) (AEadd (parse-infix (first sl)) (parse-infix (third sl)))]
             [(*) (AEmultp (parse-infix (first sl)) (parse-infix (third sl)))]
             [(/) (AEdiv (parse-infix (first sl)) (parse-infix (third sl)))]
             [(-) (AEsubs (parse-infix (first sl)) (parse-infix (third sl)))]
             [(^) (AEexp (parse-infix (first sl)) (parse-infix (third sl)))]
             [else (error 'parse-infix "invalid list input")])))]
    (else (error 'parse "invalid input"))))

;; Test:
(test (parse-infix '(2 + 3)) (AEadd (AEnumber 2)(AEnumber 3)))
(test (parse-infix '(2 ^ (3 * 4))) (AEexp (AEnumber 2)(AEmultp (AEnumber 3)(AEnumber 4))))
(test (parse-infix '((2 + 3) ^ (3 * 4))) (AEexp  (AEadd (AEnumber 2)(AEnumber 3))(AEmultp (AEnumber 3)(AEnumber 4))))
;; (parse '(2 + 3 3))
;; (parse '(2 3 3))

;; parse-postfix : s-exp -> AE
;; Purpose: To parse given s-expression in postfix notation as string and cast it to AE.
(define (parse-postfix [s : s-expression]) : AE
  (cond
    [(s-exp-number? s) (AEnumber (s-exp->number s))]
    [(s-exp-list? s)
     (let ([sl (s-exp->list s)])
       (if (or (not (= (length sl) 3))(not (s-exp-symbol? (third sl))))
           (error 'parse-postfix "input contract violation!")
           (case (s-exp->symbol (third sl))
             [(+) (AEadd (parse-postfix (first sl)) (parse-postfix (second sl)))]
             [(*) (AEmultp (parse-postfix (first sl)) (parse-postfix (second sl)))]
             [(/) (AEdiv (parse-postfix (first sl)) (parse-postfix (second sl)))]
             [(-) (AEsubs (parse-postfix (first sl)) (parse-postfix (second sl)))]
             [(^) (AEexp (parse-postfix (first sl)) (parse-postfix (second sl)))]
             [else (error 'parse-postfix "invalid list input")])))]
    (else (error 'parse "invalid input"))))

;; Test:
(test (parse-postfix '(2 3 +)) (AEadd (AEnumber 2)(AEnumber 3)))
(test (parse-postfix '(2 (3 4 *) ^)) (AEexp (AEnumber 2)(AEmultp (AEnumber 3)(AEnumber 4))))
(test (parse-postfix '((2 3 +) (3 4 *) ^)) (AEexp  (AEadd (AEnumber 2)(AEnumber 3))(AEmultp (AEnumber 3)(AEnumber 4))))
;; (parse '(2 + 3 3))
;; (parse '(2 3 3 +))
;; (parse '(2 3 3))

;; NOT NECESSARY, SELF AMUSEMENT !!
;; parse : s-exp -> number
;; Purpose: To parse given s-expression as string and cast it to AE.
(define (parse [s : s-expression]) : AE
  (cond
    [(s-exp-number? s) (AEnumber (s-exp->number s))]
    [(s-exp-list? s)
     (let ([sl (s-exp->list s)])
       (cond
         ((not (= (length sl) 3)) (error 'parse "invalid number of inputs"))
         ((s-exp-number? (first sl))
          (if (s-exp-number? (second sl))
              (parse-postfix s)
              (parse-infix s)))
         (else (parse-prefix s))))]
    (else (error 'parse "invalid input"))))

;; Test:
(test (parse '(+ 2 3)) (AEadd (AEnumber 2)(AEnumber 3)))
(test (parse '(2 3 +)) (AEadd (AEnumber 2)(AEnumber 3)))
(test (parse '(2 + 3)) (AEadd (AEnumber 2)(AEnumber 3)))
;; Error:
;; (parse '(2 + 3 3))
;; (parse '(2 3 3))

;; unparse-prefix: AE -> s-exp
;; Purpose: To unparse given AE to s-expression.
(define (unparse-prefix (ae : AE)) : s-expression
  (type-case AE ae
    (AEnumber (n) (number->s-exp n))
    (AEadd (l r) (list->s-exp (list (symbol->s-exp '+) (unparse-prefix l) (unparse-prefix r))))
    (AEmultp (l r) (list->s-exp (list (symbol->s-exp '*) (unparse-prefix l) (unparse-prefix r))))
    (AEdiv (l r) (list->s-exp (list (symbol->s-exp '/) (unparse-prefix l) (unparse-prefix r))))
    (AEsubs (l r) (list->s-exp (list (symbol->s-exp '-) (unparse-prefix l) (unparse-prefix r))))
    (AEexp (l r) (list->s-exp (list (symbol->s-exp 'expt) (unparse-prefix l) (unparse-prefix r))))
    ))

;; Tests:
(test (unparse-prefix (parse-prefix '(+ 2 3))) '(+ 2 3))
(test (unparse-prefix (parse-prefix '(^ 2 (* 3 4)))) '(expt 2 (* 3 4)))
(test (unparse-prefix (parse-prefix '(^ (+ 2 3) (* 3 4)))) '(expt (+ 2 3) (* 3 4)))

;; unparse-infix : AE -> s-exp
;; Purpose: To unparse given AE to s-expression.
(define (unparse-infix (ae : AE)) : s-expression
  (type-case AE ae
    (AEnumber (n) (number->s-exp n))
    (AEadd (l r) (list->s-exp (list (unparse-infix l) (symbol->s-exp '+) (unparse-infix r))))
    (AEmultp (l r) (list->s-exp (list (unparse-infix l) (symbol->s-exp '*) (unparse-infix r))))
    (AEdiv (l r) (list->s-exp (list (unparse-infix l) (symbol->s-exp '/) (unparse-infix r))))
    (AEsubs (l r) (list->s-exp (list (unparse-infix l) (symbol->s-exp '-) (unparse-infix r))))
    (AEexp (l r) (list->s-exp (list (unparse-infix l) (symbol->s-exp 'expt) (unparse-infix r))))
    ))

;; Tests:
(test (unparse-infix (parse-infix '(2 + 3))) '(2 + 3))
(test (unparse-infix (parse-infix '(2 ^ (3 * 4)))) '(2 expt (3 * 4)))
(test (unparse-infix (parse-infix '((2 + 3) ^ (3 * 4)))) '((2 + 3) expt (3 * 4)))


;; unparse-postfix : AE -> s-exp
;; Purpose: To unparse given AE to s-expression.
(define (unparse-postfix (ae : AE)) : s-expression
  (type-case AE ae
    (AEnumber (n) (number->s-exp n))
    (AEadd (l r) (list->s-exp (list (unparse-postfix l) (unparse-postfix r) (symbol->s-exp '+))))
    (AEmultp (l r) (list->s-exp (list (unparse-postfix l)(unparse-postfix r) (symbol->s-exp '*))))
    (AEdiv (l r) (list->s-exp (list (unparse-postfix l)(symbol->s-exp '/) (unparse-postfix r))))
    (AEsubs (l r) (list->s-exp (list (unparse-postfix l)(unparse-postfix r) (symbol->s-exp '-))))
    (AEexp (l r) (list->s-exp (list (unparse-postfix l)(unparse-postfix r) (symbol->s-exp 'expt))))
    ))

;; Tests:
(test (unparse-postfix (parse-postfix '(2 3 +))) '(2 3 +))
(test (unparse-postfix (parse-postfix '(2 (3 4 *) ^))) '(2 (3 4 *) expt))
(test (unparse-postfix (parse-postfix '((2 3 +)(3 4 *) ^))) '((2 3 +) (3 4 *) expt))

;; ========================================================================================== ;;