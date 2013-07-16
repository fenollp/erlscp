;; -*- coding: utf-8; mode: scheme -*-

;; Copyright (C) 2012-2013 Göran Weinholt <goran@weinholt.se>

;; Permission is hereby granted, free of charge, to any person obtaining a
;; copy of this software and associated documentation files (the "Software"),
;; to deal in the Software without restriction, including without limitation
;; the rights to use, copy, modify, merge, publish, distribute, sublicense,
;; and/or sell copies of the Software, and to permit persons to whom the
;; Software is furnished to do so, subject to the following conditions:

;; The above copyright notice and this permission notice shall be included in
;; all copies or substantial portions of the Software.

;; THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;; IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;; FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
;; THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;; LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;; FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;; DEALINGS IN THE SOFTWARE.
#!r6rs

;; A prototype of the supercompiler in Peter Jonsson's dissertation

;; I wrote this prototype in order to understand how to implement
;; supercompilation. The language is more or less a Scheme without any
;; side-effects, and with heavy use of the match macro. The goal was
;; to implement and understand the transformation. The code has not
;; been cleaned up.

(import (rnrs)
        (only (srfi :1 lists) delete-duplicates)
        ;; guile:
        (ice-9 pretty-print)
        (only (guile) gensym)
        (ice-9 match)
        ;; ikarus:
        ;; (only (ikarus) pretty-print gensym)
        ;; (xitomatl AS-match)
        )

(define (print . x) (for-each display x) (newline))

(define (print* x . y) (display x) (for-each write y) (newline))

;; (define (pretty-print x) (write x) (newline))

(define (gensym* x)
  (if (symbol? x)
      (gensym (symbol->string x))
      (gensym x)))

;; Standard definitions
(define G
  '((square . (lambda (x) (primop * x x)))
    (map . (lambda (f xs)
             (match xs
               ([] '())
               ([x . xs] (call cons (call f x)
                               (call map f xs))))))
    (sum . (lambda (xs)
             (match xs
               ([] '0)
               ([x . xs]
                (primop + x (call sum xs))))))
    (zip . (lambda (xs ys)
             (match xs
               ([] '())
               ([x . xs]
                (match ys
                  ([] '())
                  ([y . ys]
                   (call cons (call cons x y)
                         (call zip xs ys))))))))
    (append . (lambda (xs ys)
                (match xs
                  ([] ys)
                  ([x . xs]
                   (call cons x (call append xs ys))))))
    ;; foldr
    ;; fac
    (const . (lambda (x y)
               x))
    (rev . (lambda (xs ys)
             (match xs
               ([] ys)
               ([x . xs]
                (call rev xs (call cons x ys))))))
    (zipWith . (lambda (f xs ys)
                 (match xs
                   ([] '())
                   ([x . xs]
                    (match ys
                      ([] '())
                      ([y . ys]
                       (call cons (call f x y)
                             (call zipWith f xs ys))))))))
    (fst . (lambda (p)
             (match p
               ([x . y] x))))
    (snd . (lambda (p)
             (match p
               ([x . y] y))))
    (mapsq . (lambda (xs)
               (match xs
                 ([] '())
                 ([x . xs]
                  (call cons (primop * x x)
                        (call mapsq xs))))))
    (f . (lambda (xs)
           (match xs
             ([] '())
             ([x . xs]
              (call cons (primop * '2 x)
                    (call g xs))))))
    (g . (lambda (xs)
           (match xs
             ([] '())
             ([x . xs]
              (call cons (primop * '3 x)
                    (call f xs))))))
    (* . (lambda (x y) (primop * x y)))
    (= . (lambda (x y) (primop = x y)))
    (+ . (lambda (x y) (primop + x y)))
    (- . (lambda (x y) (primop - x y)))
    (mod . (lambda (x y) (primop mod x y)))
    (even? . (lambda (x) (primop = (primop mod x '2) '0)))
    (odd? . (lambda (x) (primop = (primop mod x '2) '1)))
    (shorter? . (lambda (xs ys)
                  (match ys
                    ([] '#f)
                    ([y . ys]
                     (match xs
                       ([] '#t)
                       ([x . xs]
                        (call shorter? xs ys)))))))
    (not . (lambda (x)
             (match x
               (#f '#t)
               (else '#f))))
    (null? . (lambda (xs)
               (match xs
                 ([] '#t)
                 (else '#f))))
    (filter . (lambda (f xs)
                (match xs
                  ([] '())
                  ([x . xs]
                   (match (call f x)
                     (#f (call filter f xs))
                     (_ (call cons x (call filter f xs))))))))
    (flatmap . (lambda (f xs)
                 (match xs
                   ([] '())
                   ([x . xs]
                    (call append (call f x)
                          (call flatmap f xs))))))
    ;; from deforestation
    (flatten . (lambda (xss)
                 (match xss
                   ([] '())
                   ([xs . xss]
                    (call append xs (call flatten xss))))))))

(define-record-type env
  (fields ls
          ;; When an expression has been split, these variables are
          ;; the ones used in the substitution.
          split-variables
          ;; Keeps track of which variables are in scope.
          inset
          ;; Tracks function names
          fun*
          ;; TODO: "hasH"
          ))

(define (make-empty-env)
  (make-env '() '() '() '()))

(define (extend-env env name binding)
  (make-env (cons `(,name . #(FOO FOO ,binding))
                  (env-ls env))
            (env-split-variables env)
            (env-inset env)
            (env-fun* env)))

(define (extend-env-split-variables env vars)
  (make-env (env-ls env)
            (append vars (env-split-variables env))
            (env-inset env)
            (env-fun* env)))

(define (extend-env-inset env vars)
  (make-env (env-ls env)
            (env-split-variables env)
            (append vars (env-inset env))
            (env-fun* env)))


(define (literal=? x y) (equal? x y))

(define (strip-gensyms x)
  (define names (make-eq-hashtable))
  (define (strip1 x)
    (read
     (open-string-input-port
      (call-with-string-output-port
        (lambda (p) (display x p))))))
  (define (make-sym base nums)
    (if (null? nums)
        (strip1 base)
        (string->symbol
         (string-append (symbol->string (strip1 base))
                        "_"
                        (number->string (length nums))))))
  (define (strip x)
    (cond ((pair? x)
           (cons (strip (car x)) (strip (cdr x))))
          ((vector? x)
           (vector-map strip x))
          ((symbol? x)
           (let* ((base (strip1 x))
                  (nums (hashtable-ref names base '())))
             (cond ((eq? base x) x)
                   ((assq x nums) => cdr)
                   (else
                    (let ((name (make-sym x nums)))
                      (hashtable-set! names base (cons (cons x name) nums))
                      name)))))
          (else x)))
  (strip x))

(define (prettify x)
  ;; Just turns it into Scheme
  (define (E x)
    (match x
      (('letrec ((lhs* rhs*) ...) body)
       `(letrec (,@(map (lambda (lhs rhs)
                          (list lhs (E rhs)))
                        lhs* rhs*))
          ,(E body)))
      (('call . xs)
       (map E xs))
      (('quote (? (lambda (x) (or (number? x) (boolean? x)))
                  x))
       x)
      (('lambda x e)
       `(lambda ,x ,(E e)))
      (('primop k . e*)
       `(,k ,@(map E e*)))
      (('match e
         (#f e0)
         ((? symbol? s) e1))
       (if (not (memq s (free-variables e1)))
           `(if ,(E e) ,(E e1) ,(E e0))
           `(let ((,s ,(E e)))
              (if ,s ,(E e1) ,(E e0)))))
      (('match e (p* e*) ...)
       `(match ,(E e)
          ,@(map (lambda (p e)
                   (list p (E e)))
                 p* e*)))
      (('let ((x* e*) ...) f)
       `(let ,(map (lambda (x e)
                     (list x (E e)))
                   x* e*)
          ,(E f)))
      (x x)))
  (E x))

(define (primop? x)
  (memq x '(+ - * = mod)))

(define (constructor? x)
  (memq x '(cons)))

(define (pattern-variables x)
  (cond ((null? x) '())
        ((pair? x)
         (append (pattern-variables (car x))
                 (pattern-variables (cdr x))))
        ((symbol? x)
         (list x))
        ((or (number? x)
             (boolean? x))
         '())
        (else
         (error 'pattern-variables "Bad pattern" x))))

(define (subst expr var rep)
  (define (E expr)
    (match expr
      ((? variable? x)
       (if (eq? x var)
           rep
           x))
      (('quote n)
       expr)
      (('lambda x e)
       (if (memq var x)
           expr
           `(lambda ,x
              ,(E e))))
      (('primop k . e*)
       `(primop ,k ,@(map E e*)))
      (('match e (p* e*) ...)
       `(match ,(E e)
          ,@(map (lambda (p e)
                   (if (memq var (pattern-variables p))
                       (list p e)
                       (list p (E e))))
                 p* e*)))
      (('let ((x* e*) ...) f)
       `(let ,(map (lambda (x e)
                     (list x (E e)))
                   x* e*)
          ,(if (memq var x*)
               f
               (E f))))
      (('letrec ((x e)) f)
       (if (eq? x var)
           expr
           `(letrec ((,x ,(E e)))
              ,(E f))))
      (('call . e*)
       (cons 'call (map E e*)))
      (x
       (error 'subst "No matching pattern" expr var rep))))
  (E expr))

(define (subst-all expr env)
  ;; XXX: this is lame.
  ;; env here is a lexical environment.
  (if (null? env)
      expr
      (subst-all (subst expr (caar env) (cdar env))
                 (cdr env))))

;; (subst-all '(+ x y) '((x . X) (y . Y)))

;; (subst '(letrec ((xs (lambda (ys)
;;                        xs)))
;;           xs)
;;        'xs 'YO)

;; (subst '(let ((xs (lambda (ys)
;;                     xs)))
;;           xs)
;;        'xs 'YO)

;; (subst '(match xs
;;           ([] xs)
;;           ([x . xs] (cons (f x) ((map f) xs))))
;;        'xs 'YO)

(define (free-variables expr)
  (define (E expr b*)
    (match expr
      ((? variable? v)
       (cond ((memq v b*)
              '())                      ;it's bound
             ((assq v G)
              ;; XXX: is this right?
              '())                      ;it's a global function
             ((constructor? v)
              '())
             (else
              (list v))))               ;it's free
      (('quote n) '())
      (('lambda x* e)
       (E e (append x* b*)))
      (('primop k . e*)
       (apply append
              (map (lambda (e)
                     (E e b*))
                   e*)))
      (('match e (p* e*) ...)
       (apply append
              (E e b*)
              (map (lambda (p e)
                     (E e (append (pattern-variables p) b*)))
                   p* e*)))
      (('let ((x* e*) ...) f)
       (apply append
              (E f (append x* b*))
              (map (lambda (e)
                     (E e b*))
                   e*)))
      (('letrec ((x e)) f)
       (let ((b* (cons x b*)))
         (append (E e b*)
                 (E f b*))))
      (('call . e*)
       (apply append (map (lambda (e) (E e b*)) e*)))
      (x
       (error 'free-variables "No matching pattern" x))))
  ;;(delete-duplicates (E expr '()))
  (E expr '()))

;; (free-variables '(let ((t '1))
;;                    (match x
;;                      ((g . y) (+ g y)))))

;; (free-variables '(let ((h (lambda (x)
;;                             (call h x))))
;;                    (call h '1)))

;; (free-variables '(letrec ((h (lambda (x)
;;                                (call h x))))
;;                    (call h '1)))


(define (alpha-convert expr)
  ;; env here is a lexical environment
  (define (pattern-subst p env)
    (cond ((or (null? p) (boolean? p) (number? p)) p)
          ((symbol? p)
           (cond ((assq p env) => cdr)
                 (else p)))
          ((pair? p)
           (cons (pattern-subst (car p) env)
                 (pattern-subst (cdr p) env)))
          (else
           (error 'pattern-subst "Unknown pattern" p env))))
  (define (E expr env)
    (match expr
      ((? variable? v)
       (cond ((assq v env) => cdr)
             (else v)))
      (('quote n) expr)
      (('lambda x* e)
       (let ((t* (map gensym* x*)))
         `(lambda ,t*
            ,(E e (append (map cons x* t*) env)))))
      (('primop (? primop? k) . e*)
       `(primop ,k ,@(map (lambda (e) (E e env)) e*)))
      #;(('primop (? primop? k) e0 e1)
       (list 'primop k (E e0 env) (E e1 env)))
      (('match e (p* e*) ...)
       `(match ,(E e env)
          ,@(map (lambda (p e)
                   (let* ((v* (pattern-variables p))
                          (t* (map gensym* v*))
                          (env (append (map cons v* t*) env)))
                     (list (pattern-subst p env)
                           (E e env))))
                 p* e*)))
      (('let ((x* e*) ...) f)
       (let ((t* (map gensym* x*)))
         `(let ,(map (lambda (t e)
                       (list t (E e env)))
                     t* e*)
            ,(E f (append (map cons x* t*) env)))))
      (('letrec ((x e)) f)
       (let* ((t (gensym* x))
              (env (cons (cons x t) env)))
         `(letrec ((,t ,(E e env)))
            ,(E f env))))
      (('call . e*)
       (cons 'call (map (lambda (e) (E e env)) e*)))
      (x
       (error 'alpha-convert "No matching pattern" x))))
  (E expr '()))

;; (alpha-convert '(letrec ((h (lambda (x)
;;                               (call h x))))
;;                   (call h '1)))

;; (alpha-convert '(let ((h (lambda (x)
;;                            (call h x))))
;;                   (call h '1)))


;; (alpha-convert '(let ((x '5))
;;                   (let ((x '4))
;;                     (primop + x '3))))

;; (alpha-convert '(match x
;;                   ((x . y) (cons x y))
;;                   ((a . b) (cons x a))))


(define (find-letrecs expr)
  (define (E expr)
    (match expr
      ((? variable? v) '())
      (('quote n) '())
      (('lambda x* e) (E e))
      (('primop (? primop? k) . e*)
       (apply append (map E e*)))
      (('match e (p* e*) ...)
       (append (E e) (apply append (map E e*))))
      (('let ((x* e*) ...) f)
       (apply append (E f) (map E e*)))
      (('letrec ((x e)) f)
       (cons (cons x e) (append (E e) (E f))))
      (('call . e*)
       (apply append (map E e*)))
      (x
       (error 'find-letrecs "No matching pattern" x))))
  (E expr))

(define (remove-letrecs expr)
  (define (E expr)
    (match expr
      ((? variable? v) expr)
      (('quote n) expr)
      (('lambda x* e)
       `(lambda ,x* ,(E e)))
      (('primop (? primop? k) . e*)
       `(primop ,k ,@(map E e*)))
      (('match e (p* e*) ...)
       `(match ,(E e)
          ,@(map (lambda (p e) (list p (E e)))
                 p* e*)))
      (('let ((x* e*) ...) f)
       `(let ,(map (lambda (x e)
                     (list x (E e)))
                   x* e*)
          ,(E f)))
      (('letrec ((x e)) f)
       (E f))
      (('call . e*)
       (cons 'call (map E e*)))
      (x
       (error 'remove-letrecs "No matching pattern" x))))
  (E expr))

(define (float-letrecs expr)
  ;; Since all the letrecs that are residualized by the supercompiler
  ;; bind lambdas with no free variables, they can be moved to the top
  ;; level.
  `(letrec ,(map (lambda (def)
                   (list (car def)
                         (remove-letrecs (cdr def))))
                 (find-letrecs expr))
     ,(remove-letrecs expr)))


(define (apply-op op x y)
  (case op
    ((+) `(quote ,(+ x y)))
    ((-) `(quote ,(- x y)))
    ((*) `(quote ,(* x y)))
    ((=) `(quote ,(= x y)))
    ((mod) `(quote ,(mod x y)))
    (else
     (error 'apply-op "Unknown primitive operator" op x y))))

(define (variable? x) (symbol? x))

(define (linear? var expr)
  ;; Based on linear in Timber's Scp.hs.
  (define (E expr)
    (match expr
      ((? variable? v)
       (if (eq? v var) 1 0))
      (('quote n) 0)
      (('lambda x* e)
       (if (memq var x*)
           0
           (* 2 (E e))))  ;if var is in e then it's not linear
      (('primop (? primop? k) . e*)
       (fold-left + 0 (map E e*)))
      (('match e (p* e*) ...)
       (+ (E e)
          (fold-left max 0
                     (map (lambda (p e)
                            (if (memq var (pattern-variables p))
                                0
                                (E e)))
                          p* e*))))
      (('let ((lhs* rhs*) ...) body)
       (if (memq var lhs*)
           (apply + (map E rhs*))       ;XXX: bug in timber?
           (apply + (E body) (map E rhs*))))
      (('letrec ((lhs* rhs*) ...) body)
       (if (memq var lhs*)
           0
           (apply + (E body) (map E rhs*))))
      (('call . e*)
       (fold-left + 0 (map E e*)))
      (x
       (error 'linear? "No matching pattern" x))))
  (<= (E expr) 1))

;; (linear? 'x '(primop + '1 x))

;; (linear? 'x '(let ((y (primop + x z))) y))

;; (linear? 'x '(let ((y (primop + x x))) y))

;; (linear? 'x '(let ((x (primop + x y))) (primop + x x)))

;; (linear? 'x '(let ((y (primop + x y))) (primop + x x)))

;; (linear? 'x '(let ((x (primop + x y))
;;                    (y (primop + x y)))
;;                (primop + x x)))

;; (linear? 'x '(match x
;;                ([] '0)
;;                ([x . xs] (primop + '1 x))))

;; (linear? 'x '(match y
;;                ([] x)
;;                ([x . xs] (primop + '1 x))))

;; (linear? 'x '(match y
;;                ([] x)
;;                ([y . xs] (primop + '1 x))))

;; (linear? 'x '(let ((g (call cons '1 x)))
;;                (call cons g x)))

;; (linear? 'x '(let ((g (call cons '1 x)))
;;                (call cons g g)))

;; (linear? 'x '(let ((x (call cons '1 x)))
;;                (call cons x x)))

;; (linear? 'x '(letrec ((x (call cons '1 x)))
;;                (call cons x x)))

;; (linear? 'x '(letrec ((z (call cons '1 x)))
;;                (call cons z x)))

;; (linear? 'x '(call (lambda (g) x)
;;                    g))


(define (strict? var expr)
  ;; An approximation based on _Strengthening Supercompilation For
  ;; Call-By-Value Languages_. "If a free variable appears no more
  ;; than once in a term, that term is said to be linear with respect
  ;; to that variable. Like Wadler [1], we extend the definition
  ;; slightly for linear case expressions: no variable may appear in
  ;; both the scrutinee and a branch, although a variable may appear
  ;; in more than one branch."
  (define (E expr)
    (match expr
      ((? variable? v)
       (eq? var expr))
      (('quote n) #f)
      (('lambda x* e) #f)
      (('primop (? primop? k) . e*)
       (exists E e*))
      (('match e (p* e*) ...)
       (or (E e)
           (for-all (lambda (p e)
                      (and (not (memq var (pattern-variables p)))
                           (E e)))
                    p* e*)))
      (('let ((x e)) f)
       (or (E e)
           (and (not (eq? x var))
                (E f))))
      (('letrec ((x e)) f)
       (E f))
      (('call . e*)
       (exists E e*))
      (x
       (error 'strict? "No matching pattern" x))))
  (E expr))

(define (terminates? expr env)
  (define (E expr)
    (match expr
      ((? variable? v)
       ;; TODO: "maybeInline"
       (cond ((memq v (env-split-variables env))
              #f)
             (else
              #t)))
      (('quote n) #t)
      (('lambda x* e) #t)
      (('primop (? primop? k) . e*)
       ;; XXX: might not terminate due to runtime errors
       #f)
      (('match e (p* e*) ...) #f)
      (('let ((x e)) f) #f)
      (('letrec ((x e)) f) #f)
      (('call 'cons . e*)
       ;; XXX: was not in the papers? In Timber cons is considered to
       ;; always terminate, for some reason.
       (for-all E e*))
      (('call . e*) #f)
      (x
       (error 'terminates? "No matching pattern" x))))
  (E expr))


;; (strict? 'x
;;          '(match (call g x)
;;             ([] x)
;;             ([g . gs] r)))

(define (split expr)
  ;; This takes an expression and "splits" it into smaller parts. The
  ;; original expression can be recovered using the substitution.
  ;; Returns an expression and a substitution.
  (match expr
    ((? variable? x)
     (values expr '()))
    ((? constructor? x)
     (values expr '()))
    (('quote n)
     (values expr '()))
    (('lambda x e)
     (let ((tmp (gensym* "tmp")))
       (values `(lambda ,x ,tmp)
               (list (cons tmp e)))))
    (('primop k . e*)
     (let ((x* (map (lambda (_) (gensym* "tmp")) e*)))
       (values `(primop ,k ,@x*)
               (map cons x* e*))))
    (('match e (p* e*) ...)
     ;; XXX: should this go into the alternatives?
     (let ((x (gensym* "tmp")))
       (values `(match ,x
                  ,@(map list p* e*))
               (list (cons x e)))))
    (((and (or 'let 'letrec) let-type) ((lhs* rhs*) ...) f)
     (let ((x (gensym* "tmp"))
           (x* (map (lambda (_) (gensym* "tmp")) lhs*)))
       (values `(,let-type ,(map list lhs* x*)
                           ,x)
               (cons (cons x f)
                     (map cons x* rhs*)))))
    (('call e . e*)
     (let ((x (gensym* "tmp"))
           (x* (map (lambda (_) (gensym* "tmp")) e*)))
       (values `(call ,x ,@x*)
               (cons (cons x e)
                     (map cons x* e*)))))
    (x
     (error 'split "No matching pattern" expr))))


(define (global-name? g)
  (assq g G))

(define (lookup-case const c*)
  ;; This looks up cases only where const is non-composite (e.g. a
  ;; number or the empty list).
  (display ";;; lookup-case ")
  (write (list 'constant: const 'cases: c*))
  (newline)
  (let lp ((c* c*))
    (match c*
      ([] #f)
      ([((? (lambda (x)
              (and (or (null? x) (boolean? x) (number? x))
                   (eqv? x const)))
            x)
         e) . c*]
       ;; The pattern is the same constant as the constant being
       ;; matched against.
       e)
      ([((x . y) e) . c*]
       (match const
         ([a . d]
          (make-let (list x y) (list `',a `',d) e))
         (_ (lp c*))))
      ([((? symbol? x) e) . c*]
       ;; A symbol binds the whole expression. XXX: only needs to be
       ;; residualized if the variable is used in the body.
       (make-let (list x)
                 (list `',const) e))
      ([_ . c*]
       (lp c*)))))

;; (lookup-case '(a b c)
;;              '([#t  true]
;;                [#f  false]
;;                [()  empty]
;;                [(x . y) list]
;;                [_  whatever]))



(define (make-let x* e* body)
  (match x*
    ([] body)
    ([x . x*]
     `(let ((,x ,(car e*)))
        ,(make-let x* (cdr e*) body)))))

(define (lookup-cons-case k e* c*)
  ;; k is a constructor and e* its argument. c* are cases from a
  ;; match. Match k e* against a case. Returns a let expression or #f
  ;; if there was no match.
  (let lp ((c* c*))
    (match c*
      ([] #f)
      ([((x . y) e) . c*]
       (if (and (eq? k 'cons) (= (length e*) 2))
           (make-let (list x y) e* e)
           (lp c*)))
      ([((? symbol? x) e) . c*]
       ;; A symbol binds the whole expression
       (if (and (eq? k 'cons) (= (length e*) 2))
           (make-let (list x) (list `(call ,k ,@e*)) e)
           (lp c*)))
      ([_ . c*]
       (lp c*)))))

;; (lookup-cons-case 'cons '('1 xs)
;;                   '((#f (call foo))
;;                     (_ (call jones xs))))

(define (drive expr env ctxt)
  (display "\nDRIVE:\n")
  (pretty-print expr)
  (pretty-print ctxt)
  (match (vector expr ctxt)
    ;; "Evaluation rules"

    (#( ('quote n)
        (('match 'HOLE . c*) . R))
     ;; R1. Look up cases with non-composed constants (e.g. numbers,
     ;; empty list). Has been extended to handle pairs and "else"
     ;; cases.
     (display "R1\n")
     (let ((let-expr (lookup-case n c*)))
       (if let-expr
           (drive let-expr env R)
           (build expr env ctxt))))   ;fallthrough on match error

    (#( ('quote n)
        (('primop op ('quote n1) 'HOLE) . R))
     ;; R2
     (display "R2\n")
     (drive (apply-op op n1 n) env R))

    (#( (? global-name? g)
        R)
     ;; R3
     (display "R3\n")
     (drive-app g env R)
     #;
     (if (eq? R 'empty)
         (build g env R) ;app in empty context is pretty useless (or is it boring?)
         (drive-app g env R)))

    (#( (? constructor? k)
        (('call 'HOLE . e*) ('match 'HOLE . c*) . R))
     ;; R4. Look up a case with a known constructor.
     (display "R4\n")
     ;; TODO: use the fallthrough if there's no match
     (let ((let-expr (lookup-cons-case k e* c*)))
       (if let-expr
           (drive let-expr env R)
           (build expr env ctxt))))   ;fallthrough on match error

    (#( ('lambda x* e)
        (('call 'HOLE . e*) . R))
     ;; R5. Let.
     (display "R5\n")
     (drive `(let ,(map list x* e*)
               ,e)
            env R))

    (#( ('lambda x* e)
        R)
     ;; R6. Lambda.
     (display "R6\n")
     (let*-values (((body used0) (drive e (extend-env-inset env x*) 'empty))
                   ((e used1) (build `(lambda ,x* ,body)
                                     env R)))
       (values e (append used0 used1))))

    (#( ('let ((x ('quote n))) e)
        R)
     ;; R7
     (display "R7\n")
     (drive (subst e x `(quote ,n)) env R))

    (#( ('let () body)
        R)
     ;; R8/R9 finish
     (display "R8/R9 finish\n")
     (drive body env R))

    (#( ('let ((x e1) (x* e*) ...) e2)
        R)
     ;; R8/R9. Handles one variable in a let.
     (display "R8/R9\n")
     (if (or (and (linear? x e2)
                  (strict? x e2))
             ;; (value? e1)
             (terminates? e1 env))
         (drive `(let ,(map list x* e*)
                   ,(subst e2 x e1))
                env R)
         ;; XXX: "x" will now be visible
         ;; in e*, which it wasn't earlier. Better be alpha
         ;; converted first. TODO: is this tested?
         (let-values (((rhs used0) (drive e1 env 'empty))
                      ((body used1) (drive `(let ,(map list x* e*)
                                              ,e2)
                                           (extend-env-inset env (list x)) R)))
           (values `(let ((,x ,rhs))
                      ,body)
                   (append used0 used1)))))

    (#( ('letrec ((x (and ('lambda y* f) fun))) e2)
        R)
     ;; R9, modified for letrec.
     (display "R9rec\n")
     ;; TODO: extend the environment with these local functions
     (set! G (cons (cons x fun) G))
     (let-values (((rhs used0) (drive fun env 'empty))
                  ((body used1) (drive e2 env R)))
       (values `(letrec ((,x ,rhs)) ,body)
               (append used0 used1))))

    ;; "Focusing rules"

    (#( ('quote n)
        (('primop op 'HOLE e2) . R))
     ;; R10
     (display "R10\n")
     (drive e2 env (cons `(primop ,op (quote ,n) HOLE) R)))

    (#( ('primop op e1 e2)
        R)
     ;; R11
     (display "R11\n")
     (drive e1 env (cons `(primop ,op HOLE ,e2) R)))

    (#( ('call e1 . e*)
        R)
     ;; R12.
     (display "R12\n")
     (drive e1 env (cons `(call HOLE . ,e*) R)))

    (#( ('match e . c*)
        R)
     ;; R13
     (display "R13\n")
     (drive e env (cons `(match HOLE . ,c*) R)))

    ;; Fallthrough

    ( #(e
        R)
      ;; R14
      (display "R14\n")
      (build e env R))))


(define (map2 f . xs*)
  (let lp ((a* '())
           (b* '())
           (xs* xs*))
    (if (for-all null? xs*)
        (values (reverse a*) (reverse b*))
        (let-values (((a b) (apply f (map car xs*))))
          (lp (cons a a*)
              (cons b b*)
              (map cdr xs*))))))

;; "Rebuilding Expressions"
(define (build expr env ctxt)
  (match ctxt
    ([('primop op 'HOLE e2) . R]
     (display "R15\n")
     (let*-values (((e used0) (drive e2 env 'empty))
                   ((ret used1) (build `(primop ,op ,expr ,e) env R)))
       (values ret (append used0 used1))))
    ([('primop op e1 'HOLE) . R]
     (display "R15b\n")
     (let*-values (((e used0) (drive e1 env 'empty))
                   ((ret used1) (build `(primop ,op ,e ,expr) env R)))
       (values ret (append used0 used1))))
    ([('call 'HOLE . e*) . R]
     ;; R17
     (display "R17\n")
     (let*-values (((arg* used*) (map2 (lambda (e)
                                         (drive e env 'empty))
                                       e*))
                   ((ret used1) (build `(call ,expr ,@arg*)
                                       env R)))
       (values ret (apply append used1 used*))))
    ([('match 'HOLE (p* e*) ...) . R]
     (cond ((variable? expr)
            ;; TODO: check out if this can be improved
            (display "R18\n")
            (let-values (((rhs* used*)
                          (map2 (lambda (p e)
                                  ;; Here there is a match on a variable. Where
                                  ;; the variable is found in the case
                                  ;; expressions it should be replaced by the
                                  ;; pattern. That can only happen if the
                                  ;; pattern and the variable agree somehow... I
                                  ;; think this is where the positive
                                  ;; information is propagated.
                                  (let ((env (extend-env-inset env (pattern-variables p))))
                                    (cond ((null? p)
                                           (drive (subst e expr '(quote ()))
                                                  env
                                                  (ctxt-subst R expr '(quote ()))))
                                          (else
                                           (drive e env R)))))
                                p* e*)))
              (values `(match ,expr
                         ,@(map list p* rhs*))
                      (apply append used*))))
           (else
            (display "R19\n")
            (let-values (((rhs* used*)
                          (map2 (lambda (p e)
                                  (let ((env (extend-env-inset env (pattern-variables p))))
                                    (drive e env R)))
                                p* e*)))
              (values `(match ,expr
                         ,@(map list p* rhs*))
                      (apply append used*))))))
    ('empty
     (display "R20\n")
     ;; R20
     (values expr '()))
    (x
     (error 'build "TODO: unimplemented context" ctxt expr env))))


(define (plug ctxt e)
  ;; [g]R. "plug" e into the HOLE in ctxt.
  (match ctxt
    ('empty e)
    ((frame . c)
     (plug c (map (lambda (x) (if (eq? x 'HOLE) e x))
                  frame)))))

(define (ctxt-subst ctxt variable replacement)
  (let lp ((ctxt ctxt))
    (match ctxt
      ('empty 'empty)
      ([x . c]
       ;; XXX: does not work if variable = HOLE
       (cons (subst x variable replacement) (lp c)))
      (x
       (error 'ctxt-subst "Unimplemented context" x variable replacement)))))

(define (lookup-renaming env expr)
  ;; TODO: in timber he looks up things in both ls and memo...
  (define fun* (append (map car (env-ls env)) (map car G)))
  (let lp ((env (env-ls env)))
    (match env
      ([] #f)
      ([(fname . #(__ _ old-expr)) . env]
       (print* ";; RENAMING? " expr #\≡ old-expr)
       ;; Is the old expression a renaming of the new expression?
       (cond ((renaming? fun* old-expr expr)
              (print* ";; RENAMING OF " fname)
              fname)
             (else
              (lp env)))))))

;; This is also from Timber. It checks if e1 is the same as e2 up to
;; renaming of variables. E builds a substitution.
(define (renaming? fun* e1 e2)
  (define (subst-cons s s*)
    (and s* (cons s s*)))
  (define (E t*)
    ;; t* is a list of expressions.
    (match t*
      (()
       ;; No more work to do.
       '())

      ((#(('quote n1)
          ('quote n2))
        . t*)
       ;; Two constants must be the same constant. They do not result
       ;; in a substitution.
       (and (literal=? n1 n2)
            (E t*)))

      ((#((? constructor? c1)
          (? constructor? c2))
        . t*)
       ;; Same as for constants.
       (and (eq? c1 c2)
            (E t*)))

      ((#((? variable? v1)
          (? variable? v2))
        . t*)
       (cond ((eq? v1 v2)
              ;; The same variable in both expressions. No need for a
              ;; substitution.
              (E t*))
             ((or (memq v1 fun*)
                  (memq v2 fun*))
              ;; Two variables that refer to different functions. The
              ;; expressions are probably calling different functions.
              #f)
             (else
              ;; Make a substitution from v1 to v2. Apply that
              ;; substitution to the unprocessed work.
              (subst-cons (cons v1 v2)
                          (E (map (lambda (x)
                                    (match x
                                      (#(e0 e1)
                                       (vector
                                        (subst e0 v1 v2)
                                        (subst e1 v1 v2)))))
                                  t*))))))

      ((#(('call op0 . e0*)
          ('call op1 . e1*))
        . t*)
       ;; Add the work of checking if op0 is a renaming of op1 and if
       ;; the arguments are pairwise renamings.
       (and (= (length e0*) (length e1*))
            (E (cons (vector op0 op1)
                     (append (map vector e0* e1*)
                             t*)))))

      ((#(('match e0 (pat0* rhs0*) ...)
          ('match e1 (pat1* rhs1*) ...))
        . t*)
       ;; XXX: renamings of pattern variables? this demands that the
       ;; patterns are exactly the same. also, what about:
       ;; (renaming? '() '(match xs ((x) x)) '(match xs ((x) y)))
       (and (equal? pat0* pat1*)
            (E (cons (vector e0 e1)
                     (append (map vector rhs0* rhs1*)
                             t*)))))

      ((#(('primop k0 . e0*)
          ('primop k1 . e1*))
        . t*)
       (and (eq? k0 k1)
            (= (length e0*) (length e1*))
            (E (append (map vector e0* e1*)
                       t*))))

      ((#(('lambda f0* e0)
          ('lambda f1* e1))
        . t*)
       ;; First make the e1 use the same names as e0 and then check if
       ;; e0 and e1 are equal up to renaming.
       (and (= (length f0*) (length f1*))
            (E (cons (vector e0 (subst-all e1 (map cons f0* f1*)))
                     t*))))

      ((#(((and let-type0 (or 'let 'letrec)) ((x0* e0*) ...) f0)
          ((and let-type1 (or 'let 'letrec)) ((x1* e1*) ...) f1))
        . t*)
       ;; XXX: untested and peculiarly different
       (and (eq? let-type0 let-type1)
            (= (length x0*) (length x1*))
            (E (append (map vector e0* e1*)
                       (cons (vector f0 f1) t*)))))

      ((#(e1 e2) . t*)
       ;; Two expressions of different types. Can't be a renaming.
       ;; (print "default in renaming: " e1 "  " e2)
       #f)))

  ;; Build a substitution...
  (let ((s (E (list (vector e1 e2)))))
    (print* "substitution: " s)
    (and s (equal? (subst-all e2 s) e2))))

;; (renaming? '()
;;            '(call append xs xs)
;;            '(call append xs* xs))

;; (renaming? '()
;;            '(match xs ((x) x))
;;            '(match xs ((x) y)))

;; (renaming? '(append map)
;;            '(let ((x '2)) (primop + x x))
;;            '(let ((y '2)) (primop + y y)))

;; (renaming? '(append map)
;;            '(call append xs ys)
;;            '(call append XS YS))

;; (renaming? '(append)
;;            '(call append ys zs)
;;            '(call append xs (call append ys zs)))

;; (renaming? '()
;;            '(call append xs xs)
;;            '(call append ys xs))

;; (renaming? '()
;;            '(call append xs ys)
;;            '(call append xs xs))


;; Returns a list or #f.
(define (lookup-homeomorphically-embedded env expr)
  (define fun* (append (map car (env-ls env)) (map car G)))
  (print ";;;;;;; is it embedded? " expr)
  (let lp ((env (env-ls env)))
    (match env
      ([] #f)
      ([(fname . #(_ __ old-expr%)) . env]
       (print ";;; WHISTLE? " old-expr% " ⊴ " expr)
       (cond ((whistle? fun* old-expr% expr)
              (print ";;; WHISTLE! " (list 'fname: fname
                                           ;;'formals: formals
                                           'old-expr: old-expr%))
              (cons (cons fname old-expr%)
                    (or (lp env) '())))
             (else
              (lp env)))))))

(define (free-vars env exp)
  (let* ((invar* (env-inset env))
         (fv* (delete-duplicates (free-variables exp)))
         (res* (filter (lambda (x) (memq x invar*))
                       fv*)))
    (print* "free-vars. exp: " exp)
    (print* "invar*: " invar*)
    (print* "fv*: " fv*)
    (print* "res*: " res*)
    res*))

(define (drive-app g env ctxt)
  (display "APP: ")
  (write g)
  (display " CTXT: ")
  (write ctxt)
  (newline)
  (let* ((body (cdr (assq g G)))        ;XXX: global AND new functions
         (l (plug ctxt g))
         (fv* (free-vars env l)))
    (cond ((lookup-renaming env l) =>
           (lambda (fname)
             (display ";;; Folding.\n")
             (print* ";;; fname: " fname)
             (print* ";;; fv*: " fv*)
             (let ((newterm
                    ;; TODO: test this
                    (if (null? fv*)
                        fname
                        `(call ,fname ,@fv*))))
               (values newterm (list (cons fname #f))))))
          ((lookup-homeomorphically-embedded env l) =>
           (lambda (emb)
             ;; Here it is supposed to be safe to return l. emb is a
             ;; list of (fname . old-expression).
             (define fun* (append (map car (env-ls env)) (map car G)))
             (print* ";;; Homeomorphically embedded! " emb)
             (let ((refl (filter (lambda (name+expr)
                                   (whistle? fun* l (cdr name+expr)))
                                 emb)))
               (print* "refl: " refl)
               (if (null? refl)
                   (generalize env fun* l (cdar emb))
                   ;; Case 2, figure 7, p277-jonsson
                   (begin
                     ;; This is used for upwards generalization. It is
                     ;; triggered by e.g. (append xs xs).
                     (print* "Upwards generalization: " (car refl) "   " fv*)
                     ;; (values l '())
                     ;; this goes into w...
                     (values (gensym* "intermediate")
                             (list (cons (caar refl) l))))))))
          (else
           (print* "making a new function for: " l)
           (let* ((fname (gensym* "h"))
                  (body% (alpha-convert body))
                  (env% (extend-env env fname l)))
             (let-values (((e% used) (drive body% env% ctxt)))
               (print* "e%: " e%)
               (print* "used: " used)
               (print* "fname in used? " (assq fname used))
               (let ((w (find (lambda (name+expr)
                                ;; for upwards generalization
                                (and (cdr name+expr)
                                     (eq? fname (car name+expr))))
                              used))
                     (found (find (lambda (name+expr)
                                    ;; See if the function was folded
                                    ;; against anywhere.
                                    (and (not (cdr name+expr))
                                         (eq? fname (car name+expr))))
                                  used)))
                 (cond (w
                        (let ()
                          (define fun* (append (map car (env-ls env)) (map car G)))
                          (print* "Upwards generalization..." w)
                          (generalize env fun* l (cdr w))))
                       ((not found)
                        (print ";; (not found)")
                        (values e% used))
                       (else
                        (let* ((fv* fv*)
                               (bodyfv* (remp (lambda (x) (memq x fv*))
                                              (free-vars env e%)))
                               (x* (map gensym* fv*))
                               (newbody (alpha-convert
                                         (if (null? fv*)
                                             e%
                                             `(lambda ,x*
                                                ,(subst-all e% (map cons fv* x*))))))
                               (newterm (if (null? fv*)
                                            fname
                                            `(call ,fname ,@fv*))))
                          (print* "a new function was made: " fname)
                          ;;(print* "free variables in newbody: " (free-variables newbody))
                          (print* "fv*: " fv*)
                          (print* "bodyfv*: " bodyfv*)
                          (cond (#f
                                 ;; TODO: "addToStore"
                                 (null? bodyfv*)
                                 (values newterm used))
                                (else
                                 (values `(letrec ((,fname ,newbody))
                                            ,newterm)
                                         used)))))))))))))


;; Is e1 homeomorphically embedded in e2?
(define (whistle? fun* e1 e2)
  (define (dive e2)
    ;; This implements the diving part of the embedding. e1 can still
    ;; be embedded in e2 if e1 is embedded in one of the items
    ;; returned by this procedure.
    (match e2
      (('lambda x* e)               e)
      (('primop k . e*)             e*)
      (('match e (p* e*) ...)       (cons e e*))
      (('let ((x* e*) ...) f)       (cons f e*))
      (('letrec ((x* e*) ...) f)    (cons f e*))
      (('call . e*)                 e*)
      (x                            '())))
  (define (peel e1 e2)
    (match (vector e1 e2)
      (#(('quote n1)
         ('quote n2))
       #t)
      (#((? constructor? c1)
         (? constructor? c2))
       (eq? c1 c2))
      (#((? variable? v1)
         (? variable? v2))
       ;; What variable names are used doesn't matter, but this has to
       ;; catch the case where the variables refer to functions. If
       ;; it's the same function it's fine.
       (or (eq? v1 v2)
           (not (or (memq v1 fun*)
                    (memq v2 fun*)))))
      (#(('call op0 . e0*)
         ('call op1 . e1*))
       (and (= (length e0*) (length e1*))
            (whistle? fun* op0 op1)
            (for-all (lambda (e0 e1)
                       (whistle? fun* e0 e1))
                      e0* e1*)))
      (#(('match e0 . c0*)
         ('match e1 . c1*))
       (and (= (length c0*) (length c1*))
            (whistle? fun* e0 e1)
            (for-all (lambda (c0 c1)
                       (define match-rhs cadr)
                       (whistle? fun*
                                 (match-rhs c0)
                                 (match-rhs c1)))
                     c0* c1*)))
      (#(('primop k0 . e0*)
         ('primop k1 . e1*))
       (and (eq? k0 k1)
            (= (length e0*) (length e1*))
            (for-all (lambda (e0 e1)
                       (whistle? fun* e0 e1))
                     e0* e1*)))
      (#(('lambda f0* #|.|# e0)
         ('lambda f1* #|.|# e1))
       (and (= (length f0*) (length f1*))
            (whistle? fun* e0 e1)))
      (#(((and let-type0 (or 'let 'letrec)) ((x0* e0*) ...) f0)
         ((and let-type1 (or 'let 'letrec)) ((x1* e1*) ...) f1))
       (and (eq? let-type0 let-type1)
            (= (length x0*) (length x1*))
            (whistle? fun* f0 f1)
            (for-all (lambda (e0 e1)
                       (whistle? fun* e0 e1))
                     e0* e1*)))
      (x
       (print "default in peel: " x)
       #f)))
  ;; Either e1 is embedded directly in e2, or in a subterm.
  (or (peel e1 e2)
      (exists (lambda (e)
                (whistle? fun* e1 e))
              (dive e2))))




(define (generalize env fun* e1 e2)
  ;; First try to find the most specific generalization of e1 and e2.
  ;; If that is a variable, then split e1 instead into smaller
  ;; expressions. Now we have a term and a substitution environment (a
  ;; mapping from temporary names to expressions). Do driving on the
  ;; term and the expressions and then substitute back the results
  ;; into the term so that all temporary names disappear. The
  ;; temporary names must be passed to drive in the environment
  ;; variable split-variables. XXX: Perhaps they must also be
  ;; available to free-variables (see "inSet").
  (print* "generalize. env: " env)
  (print* "fun*: " fun*)
  (print* "e1: " e1)
  (print* "e2: " e2)
  (let-values (((term subst) (msg env e1 e2)))
    (print "\nmsg returned:")
    (print* "term: " term)
    (print* "subst: " subst)
    (let-values (((term subst)
                  (if (variable? term)
                      (begin (print "SPLITTING") (split e1))
                      (values term subst))))
      (print* "term: " term)
      (print* "subst: " subst)
      ;; now drive term and the right-hand sides of subst in the
      ;; empty context. extend the split-variables env first.
      (let ((env (extend-env-split-variables env (map car subst))))
        (let*-values (((term used) (drive term (extend-env-inset env (map car subst))
                                          'empty))
                      ((rhs* used*) (map2 (lambda (s) (drive (cdr s) env 'empty))
                                          subst)))
          (let ((subst
                 (map (lambda (s rhs)
                        (cons (car s) rhs))
                      subst rhs*)))
            (print* "new term: " term)
            (print* "new subst: " subst)
            (values (subst-all term subst)
                    (apply append used used*))))))))


;; (define TEST-ENV
;;   (make-env '((#{g19 |<>hjrqNZHpAzBlO/|} . #((ys) (match (call map square Canonicalized-0) (() '0) ((#{x |!L!V4$EI&O5b<&JH|} . #{xs |PB4cER&9y%SWMm2X|}) (primop + #{x |!L!V4$EI&O5b<&JH|} (call sum #{xs |PB4cER&9y%SWMm2X|})))) (match (call map square ys) (() '0) ((#{x |!L!V4$EI&O5b<&JH|} . #{xs |PB4cER&9y%SWMm2X|}) (primop + #{x |!L!V4$EI&O5b<&JH|} (call sum #{xs |PB4cER&9y%SWMm2X|})))))) (#{g18 |Gwku?a%p14KAlT4q|} . #((ys) (call sum (call map square Canonicalized-0)) (call sum (call map square ys)))) (#{g20 |kjr=>ZiH9ge5nioG|} . #((ys) (call #{g17 |CYKu/lR$BmzQ<v8g|} Canonicalized-0) (call #{g17 |CYKu/lR$BmzQ<v8g|} ys))))
;;             '()))

;; (define TEST-FUN*
;;   '(#{g19 |<>hjrqNZHpAzBlO/|} #{g18 |Gwku?a%p14KAlT4q|} #{g20 |kjr=>ZiH9ge5nioG|}
;;     #{g17 |CYKu/lR$BmzQ<v8g|} #{g12 |DW2K=kTVX<&q11g!|} square map sum zip append
;;     const rev zipWith fst snd mapsq f g * = + - mod even? odd? shorter? mas flatten filter))

;; (generalize TEST-ENV TEST-FUN*
;;             '(primop + (call square x) (call sum (call map square xs)))
;;             '(call sum (call map square ys)))


;; The most specific generalization
(define (msg env e1 e2)
  (msg* env (free-vars env e1) e1 e2))

;; Create a new expression and a substitution. The differences between
;; the expressions are replaced by variables. Applying the
;; substitution to the expression gives you e1 back.
(define (msg* env infv* e1 e2)
  (define (delete e* x*)
    (match x*
      (() '())
      ((h . t*)
       (if (memq h e*)
           (delete e* t*)
           (cons h (delete e* t*))))))
  (define (fallthrough)
    ;; Returns a call to a new function that wraps e1.
    (let ((n (gensym* "v"))              ;will be residualized
          (fv* (delete infv* (free-vars env e1))))
      (let ((lterm (if (null? fv*)
                       e1
                       `(lambda ,fv* ,e1)))
            (newterm (if (null? fv*)
                         n
                         `(call ,n ,@fv*))))
        (values newterm (list (cons n lterm))))))
  (match (vector e1 e2)
    (#( (? constructor? n1) (? constructor? n2))
     (if (eq? n1 n2) (values e1 '()) (fallthrough)))
    (#( ('quote n1) ('quote n2))
     (if (literal=? n1 n2) (values e1 '()) (fallthrough)))
    (#( (? variable? n1) (? variable? n2))
     (if (eq? n1 n2) (values e1 '()) (fallthrough)))
    (#( ((or 'let 'letrec) . _) ((or 'let 'letrec) . _))
     (error 'msg "Well... msg on let expressions, what about it?"
            e1 e2))
    (#(('call (? variable? op1) . e1*)
       ('call (? variable? op2) . e2*))
     (cond ((and (equal? op1 op2)
                 (= (length e1*) (length e2*)))
            (let lp ((e1* e1*)
                     (e2* e2*)
                     (arg* '())
                     (subst* '()))
              (if (pair? e1*)
                  (let-values (((arg subst) (msg* env infv* (car e1*) (car e2*))))
                    (lp (cdr e1*)
                        (cdr e2*)
                        (cons arg arg*)
                        (append subst subst*)))
                  (values `(call ,op1 ,@(reverse arg*))
                          subst*))))
           (else
            (fallthrough))))
    (#(('match c1 (p1* e1*) ...)
       ('match c2 (p2* e2*) ...))
     (cond ((equal? p1* p2*)
            (let lp ((p1* p1*)
                     (e1* e1*)
                     (e2* e2*)
                     (case* '())
                     (subst* '()))
              (if (pair? e1*)
                  (let-values (((e subst) (msg* (extend-env-inset env (pattern-variables (car p1*)))
                                                infv* (car e1*) (car e2*))))
                    (lp (cdr p1*)
                        (cdr e1*)
                        (cdr e2*)
                        (cons (list (car p1*) e) case*)
                        (append subst subst*)))
                  (let-values (((c subst) (msg* env infv* c1 c2)))
                    (values `(match ,c ,@(reverse case*))
                            (append subst subst*))))))
           ;; TODO: msg when the patterns don't match exactly
           (else
            (fallthrough))))
    (#(('lambda x1* b1)
       ('lambda x2* b2))
     (cond ((equal? x1* x2*)
            (let-values (((body subst) (msg* (extend-env-inset env x1*) infv* b1 b2)))
              (values `(lambda ,x1* ,body)
                      subst)))
           (else
            (fallthrough))))

    (_
     (fallthrough))))

(define (scp expr)
  (let ((old-G G))                      ;very ugly, should be in env.
    (let-values (((expr-s used)
                  (drive (alpha-convert expr) (make-empty-env) 'empty)))
      (let ((ret (float-letrecs expr-s)))
        (set! G old-G)
        (prettify (strip-gensyms ret))))))

(let* ((code '(lambda (xs)
                (call map square (call map square xs))))
       (code^ (scp code)))
  (newline)
  (pretty-print code)
  (display "=>\n")
  (pretty-print code^))


;; And to finish this off, there is lots of code that was tested
;; during the development.

;; (generalize (make-empty-env)
;;             '(append)
;;             '(lambda (x Y) (call append x Y))
;;             '(lambda (x y) (call append x y)))

;; (msg (make-empty-env)
;;      '(lambda (x Y) (call append x (call append Y Y)))
;;      '(lambda (x y) (call append x y)))

;; (msg (make-empty-env)
;;      '(call append x y)
;;      '(call append a (call append b c)))

;; (whistle? '(append)
;;           '(call append x y)
;;           '(call append a (call append b c)))

;; (split '(call append (call cons x (call append xs ys)) zs))

;; (split '(primop + (call square x) (call sum (call map square xs))))

;; (let-values (((term subst)
;;               (msg (extend-env-inset (make-empty-env)
;;                                      '(xs x))
;;                    '(match (call rev xs (call cons x '()))
;;                       (() '())
;;                       ((x . xs) (call rev xs (call cons x '()))))
;;                    '(match (call rev xs '())
;;                       (() '())
;;                       ((x . xs) (call rev xs (call cons x '())))))))
;;   (subst-all term subst))


;; (let-values (((term subst)
;;               (msg (make-empty-env)
;;                    '(call rev #{xs |c/qDI5%Vh0PxD/?a|} (call cons #{x |CZHvvEFbIgJNA%WG|} '()))
;;                    '(call rev xs '()))))
;;   (subst-all term subst))


;; (scp '(lambda (xs ys zs)
;;         (call append (call append xs ys) zs)))

;; (lambda (xs ys zs)
;;   (append (append xs ys) zs))
;; =>
;; (letrec ((h
;;           (lambda (xs ys zs)
;;             (match xs
;;               (()
;;                (match ys
;;                  (() zs)
;;                  ((x . xs_1) (cons x (h_1 xs_1 zs)))))
;;               ((x_1 . xs_2) (cons x_1 (h xs_2 ys zs))))))
;;          (h_1
;;           (lambda (xs_3 zs_1)
;;             (match xs_3
;;               (() zs_1)
;;               ((x_2 . xs_4) (cons x_2 (h_1 xs_4 zs_1)))))))
;;   (lambda (xs_5 ys_1 zs_2)
;;     (h xs_5 ys_1 zs_2)))

;; (scp '(lambda (xs ys zs)
;;         (call append xs (call append ys zs))))

;; (scp '(lambda (ys)
;;         (call sum (call map square ys))))
;; =>
;; (letrec ((h
;;           (lambda (ys)
;;             (match ys
;;               (() 0)
;;               ((x . xs) (+ (* x x) (h xs)))))))
;;   (lambda (ys_1)
;;     (h ys_1)))


;; (scp '(lambda (xs ys zs)
;;         (call map (lambda (x)
;;                     (primop + x '1))
;;               (call append xs (call append ys zs)))))

;; (lambda (xs ys zs)
;;   (map (lambda (x) (+ x 1))
;;        (append xs (append ys zs))))
;; =>
;; (letrec ((h
;;           (lambda (xs ys zs)
;;             (match xs
;;               (()
;;                (match ys
;;                  (()
;;                   (match zs
;;                     (() '())
;;                     ((x . xs_1) (cons (+ x 1) (h_1 xs_1)))))
;;                  ((x_1 . xs_2) (cons (+ x_1 1) (h_2 xs_2 zs)))))
;;               ((x_2 . xs_3) (cons (+ x_2 1) (h xs_3 ys zs))))))
;;          (h_1
;;           (lambda (xs_4)
;;             (match xs_4
;;               (() '())
;;               ((x_3 . xs_5) (cons (+ x_3 1) (h_1 xs_5))))))
;;          (h_2
;;           (lambda (xs_6 zs_1)
;;             (match xs_6
;;               (()
;;                (match zs_1
;;                  (() '())
;;                  ((x_4 . xs_7) (cons (+ x_4 1) (h_3 xs_7)))))
;;               ((x_5 . xs_8) (cons (+ x_5 1) (h_2 xs_8 zs_1))))))
;;          (h_3
;;           (lambda (xs_9)
;;             (match xs_9
;;               (() '())
;;               ((x_6 . xs_10) (cons (+ x_6 1) (h_3 xs_10)))))))
;;   (lambda (xs_11 ys_1 zs_2)
;;     (h xs_11 ys_1 zs_2)))



;; ;; =>
;; ;; (letrec ((g24
;; ;;           (lambda (ys)
;; ;;             (match ys
;; ;;               (() 0)
;; ;;               ((x . xs) (+ (* x x) (g24 xs)))))))
;; ;;   (g24 ys))

;; (scp '(lambda (xs)
;;         (call map square (call map square xs))))

;; (scp '(lambda (xs)
;;         (call sum (call f xs))))

;; (scp '(lambda (xs ys)
;;         (call sum (call zipWith *
;;                         xs ys))))

;; (scp '(lambda (XS YS)
;;         (call sum (call zipWith *
;;                         (call cons '4 XS)
;;                         (call cons '4 (call cons '5 YS))))))


;; (scp '(lambda (XS YS)
;;         (primop + (call sum (call map snd (call zip XS YS)))
;;                 (call sum (call map fst (call zip XS YS))))))

;; (scp '(lambda (fun xs)
;;         (call rev (call map fun xs) '())))

;; (letrec ((g956
;;           (lambda (fun g954 g955)
;;             (match g954
;;               (() g955)
;;               ((x . xs) (g956 fun xs (cons (fun x) g955)))))))
;;   (let ((xs '(1 2 3))
;;         (fun (lambda (x) (* x 10))))
;;     (match xs
;;       (() '())
;;       ((x_1 . xs_1) (g956 fun xs_1 (cons (fun x_1) '()))))))

;; (scp '(lambda (xs ys zs)
;;         (call mas xs ys zs)))

;; (scp '(lambda ()
;;         (let ((l18 (call listn '18)))
;;           (let ((l12 (call listn '12)))
;;             (let ((l6 (call listn '6)))
;;               ;; NTAKL. code explosion. the expected result is '(7 6 5
;;               ;; 4 3 2 1).
;;               (call mas l18 l12 l6))))))

;; (scp '(lambda (xs)
;;         (call rev xs '())))


;; (letrec ((g924
;;           (lambda (g922 g923)
;;             (match g922
;;               (() g923)
;;               ((x . xs) (g924 xs (cons x g923)))))))
;;   (let ((xs '(1 2 3)))
;;     (match xs
;;       (() '())
;;       ((x_1 . xs_1) (g924 xs_1 (cons x_1 '()))))))


;; (scp '(call filter (lambda (x)
;;                      (match x
;;                        (4 '#t)
;;                        (5 '#f)))
;;             '(1 2 3 4)))

;; (scp '(call filter (lambda (x)
;;                      (match x
;;                        (4 '#t)
;;                        (5 '#f)
;;                        (x '#f)))
;;             '(1 2 3 4 5 4)))

;; (scp '(lambda (xs)
;;         (call rev (call rev xs '()) '())))

;; these are not improved:
;; (scp '(lambda (XS) (call flatten XS)))   ;already optimal

;; (scp '(lambda (XS) (call flatten (call append XS XS))))

;; (scp '(lambda (xs) (call append xs xs))) ; upwards generalization

;; (scp '(lambda (xs ys) (call append xs ys)))


;; (letrec ((g361
;;           (lambda (XS XS_1)
;;             (match XS
;;               (() '())
;;               ((x . xs)
;;                (append x (g361 xs XS)))))))
;;   (let ((XS '((1 2 3 4) (10 20 30 40))))
;;     (g361 XS XS)))

;; superbug..
;; (letrec ((g336
;;           (lambda (XS)
;;             (match XS
;;               (() '())
;;               ((x . xs)
;;                (append x (g336 xs XS)))))))
;;   (g336 XS))


;; alternative code for (call flatten (call append XS XS)):
;; (letrec ((g332
;;           (lambda (x xs XS)
;;             (match x
;;               (()
;;                 (match xs
;;                   (()
;;                     (match XS (() '())
;;                       ((xs_1 . xss) (g333 xs_1 xss))))
;;                   ((x_1 . xs_2) (g332 x_1 xs_2 XS))))
;;               ((x_2 . xs_3) (cons x_2 (g332 xs_3 xs XS))))))
;;          (g333
;;           (lambda (xs_4 xss_1)
;;             (match xs_4
;;               (()
;;                 (match xss_1 (() '())
;;                   ((xs_5 . xss_2) (g333 xs_5 xss_2))))
;;               ((x_3 . xs_6) (cons x_3 (g333 xs_6 xss_1)))))))
;;   (let ((XS '((1 2 3 4) (10 20 30 40))))
;;     (match XS
;;       (() '())
;;       ((x_4 . xs_7)
;;        (g332 x_4 xs_7 XS)))))


;; big code:
;; (scp '(lambda (XS YS)
;;         (primop + (call sum (call rev (call map snd (call zip XS YS)) '()))
;;                 (call sum (call rev (call map fst (call zip XS YS)) '())))))



;; this code will do two passes over the list (supercompilation is not
;; clever enough to invent an accumulating variable):

;; (scp '(lambda (XS YS)
;;         (call append
;;               (call filter even? XS)
;;               (call filter odd? XS))))


;;; Whistle?

;; (whistle? '(rev)
;;           '(match (call rev xs '())
;;              (() '())
;;              ((x . xs) (call rev xs (call cons x '()))))
;;           '(match (call rev xs (call cons x '()))
;;              (() '())
;;              ((x . xs) (call rev xs (call cons x '())))))

;; (whistle? '(rev)
;;           '(call rev xs '())
;;           '(call rev xs (call cons x '())))


#|
;; should be true:
(whistle? '(a)
          'b '(call a b))

(whistle? '(a c)
          '(call c b) '(call c (call a b)))

(whistle? '(a c)
          '(call d b b)
          '(call d (call a b) (call a b)))

(whistle? '(rev cons)
          '(call rev xs '())
          '(call rev xs (call cons x '())))

(whistle? '(fac)
          '(call fac y)
          '(call fac (primop - y '1)))

;; Should be false (if a and c are global functions):
(whistle? '(a c) '(call a (call c b)) '(call c b))
(whistle? '(a c) '(call a (call c b)) '(call c (call a b)))
(whistle? '(a c) '(call a (call c b)) '(call a (call a (call a b))))



(whistle? '(ap)
          '(call ap Xs Ys)
          '(call ap Xs (call Ys Zs)))

(whistle? '(ap)
          '(call ap (call ap Xs Ys) Zs)
          '(call ap (call cons X (call ap Xs Ys)) Zs))

|#

;; true:

;; (whistle? '(rev)
;;           '(match (call rev xs '())
;;              (() '())
;;              ((x . xs) (call rev xs (call cons x '()))))
;;           '(match (call rev xs (call cons x '()))
;;              (() '())
;;              ((x . xs) (call rev xs (call cons x '())))))

;; (scp '(lambda (xs) (call cons append xs)))


;;; Upwards generalization.

;; (scp '(lambda (xs) (call append xs xs)))

;; (scp '(lambda (YS) (call append YS YS)))

;; (scp '(lambda (xs) (call append xs (call append xs xs))))


;; ((letrec ((h
;;           (lambda (v xs)
;;             (match v
;;               (() (h_1 xs xs))
;;               ((x . xs_1) (cons x (h xs_1 xs))))))
;;          (h_1
;;           (lambda (v_1 xs_2)
;;             (match v_1
;;               (() xs_2)
;;               ((x_1 . xs_3) (cons x_1 (h_1 xs_3 xs_2)))))))
;;   (lambda (xs_4) (h xs_4 xs_4)))
;;  '(1 2))


;; (scp '(lambda (xs)
;;         (call flatmap (lambda (x) (call cons (primop + x '1) '())) xs)))

;; (whistle? '(flatmap append)
;;           '(call flatmap (lambda (x) (call cons (primop + x '1) '())) xs)
;;           '(call append (call (lambda (x) (call cons (primop + x '1) '())) x)
;;                  (call flatmap (lambda (x) (call cons (primop + x '1) '())) xs)))
