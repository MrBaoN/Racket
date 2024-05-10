#lang racket

;; definition of structures for MUPL programs
(struct var  (string) #:transparent)  ;; a variable, e.g., (var "foo")
(struct int  (num)    #:transparent)  ;; a constant number, e.g., (int 17)
(struct add  (e1 e2)  #:transparent)  ;; add two expressions
(struct sub  (e1 e2)  #:transparent)  ;; subtract two expressions
(struct isgreater (e1 e2)  #:transparent) ;; if e1 > e2 then 1 else 0
(struct ifnz (e1 e2 e3) #:transparent) ;; if not zero e1 then e2 else e3
(struct call (funexp actual)  #:transparent) ;; function call
(struct mlet (var e body) #:transparent) ;; a local binding (let var = e in body) 
(struct apair   (e1 e2) #:transparent) ;; make a new pair
(struct first   (e)     #:transparent) ;; get first part of a pair
(struct second  (e)     #:transparent) ;; get second part of a pair
(struct munit   ()      #:transparent) ;; MUPL equivalence of null
(struct ismunit (e)     #:transparent) ;; if e1 is munit then 1 else 0
(struct fun  (nameopt arg body) #:transparent) ;; a 1 argument function, name of function could be null,
                                               ;; arg must be string, body is expr

;; a closure is not in "source" programs; it is what functions evaluate to
(struct closure (env fun) #:transparent) 

(define (racketlist->mupllist racklist)
  (if (null? racklist) (munit)
      (apair (car racklist) (racketlist->mupllist (cdr racklist)))))

(define (mupllist->racketlist mupllist)
  (if (munit? mupllist) null
      (cons (apair-e1 mupllist) (mupllist->racketlist (apair-e2 mupllist)))))

;; Lookup a variable in an environment
(define (envlookup env str)
  (cond [(null? env) (error "unbound variable during evaluation" str)]
        [(equal? (car (car env)) str) (cdr (car env))]
        [#t (envlookup (cdr env) str)]))

;; Evaluating MUPL
(define (eval-under-env e env)
  (cond [(var? e) 
         (envlookup env (var-string e))]

        [(int? e) e]
        
        [(add? e) 
         (let ([v1 (eval-under-env (add-e1 e) env)]
               [v2 (eval-under-env (add-e2 e) env)])
           (if (and (int? v1)
                    (int? v2))
               (int (+ (int-num v1) 
                       (int-num v2)))
               (error "MUPL addition applied to non-int")))]

        [(sub? e)
         (let ([v1 (eval-under-env (sub-e1 e) env)]
               [v2 (eval-under-env (sub-e2 e) env)])
           (if (and (int? v1)
                    (int? v2))
               (int (- (int-num v1) 
                       (int-num v2)))
               (error "MUPL subtraction applied to non-int")))]

        [(munit? e) e]
        
        [(fun? e) (closure env e)]

        [(isgreater? e) (let ([left (eval-under-env (isgreater-e1 e) env)]
                              [right (eval-under-env (isgreater-e2 e) env)])
                          (if (and (int? left) (int? right))
                              (if (> (int-num left) (int-num right)) (int 1) (int 0))
                              (error "Using MUPL isgreater with non-int")))]
        
        [(ifnz? e) (let ([if-bool (eval-under-env (ifnz-e1 e) env)])
                     (if (int? if-bool)
                         (if (= 0 (int-num if-bool)) (eval-under-env (ifnz-e3 e) env)
                             (eval-under-env (ifnz-e2 e) env))
                         (error "e1 is not MUPL int")))]
        
        [(mlet? e) (if (string? (mlet-var e)) (eval-under-env (mlet-body e) (cons (cons (mlet-var e)(eval-under-env (mlet-e e) env)) env))
                       (error "Variable name is not string"))]

        [(call? e) (let ([funcEval (eval-under-env (call-funexp e) env)])
                     (if (closure? funcEval)
                         (eval-under-env (fun-body (closure-fun funcEval))
                                         (if (null? (fun-nameopt (closure-fun funcEval)))
                                              (cons(cons(fun-arg(closure-fun funcEval)) (eval-under-env (call-actual e) env)) (closure-env funcEval))
                                              (append (list(cons(fun-nameopt (closure-fun funcEval)) funcEval) (cons(fun-arg(closure-fun funcEval)) (eval-under-env (call-actual e) env))) (closure-env funcEval))))
                         (error "Function call on non-function")))]

        [(apair? e) (apair (eval-under-env (apair-e1 e) env) (eval-under-env (apair-e2 e) env))]
        
        [(first? e) (let ([maybe-pair (eval-under-env (first-e e) env)])
                      (if (apair? maybe-pair) (apair-e1 maybe-pair)
                          (error "Call first on non-pair")))]

        [(second? e) (let ([maybe-pair (eval-under-env (second-e e) env)])
                       (if (apair? maybe-pair) (apair-e2 maybe-pair)
                           (error "Call second on non-pair")))]

        [(ismunit? e) (let ([is-null (eval-under-env (ismunit-e e) env)])
                        (if (munit? is-null) (int 1) (int 0)))]
        
        [#t (error (format "bad MUPL expression: ~v" e))]))


;; Calling naive evaluation
(define (eval-exp e)
  (eval-under-env e null))

;; "Macros" in MUPL is Racket function
(define (ifmunit e1 e2 e3) (ifnz (ismunit e1) e2 e3)) ;; if statement using munit

(define (mlet* bs e2) ;;let* but in MUPL
  (if (null? bs) e2
      (mlet (car (car bs)) (cdr (car bs)) (mlet* (cdr bs) e2))))

(define (ifeq e1 e2 e3 e4) ;; if e1 = e2 then e3 else e4
  (mlet* (list (cons "_x" e1)(cons "_y" e2))
         (ifnz (isgreater (var "_x") (var "_y")) e4
               (ifnz (isgreater (var "_y") (var "_x")) e4
                     e3))))


;; Challenge -- Making a more efficient closure that only store "free variables"
;; in the function instead of evaluating it under the environment every call

(struct fun-challenge (nameopt arg body freevars) #:transparent) ;; include all free variable in the body

;; Helper that finds all free variables in MUPL expression
;; Implement using mutable-set
(define (compute-free-vars e)
  (letrec ([not-free (mutable-set)]
           [free (mutable-set)]
           [check-inside (λ(supposed-func) (let ([another-fun (compute-free-vars supposed-func)])
                                      (begin (set-for-each (fun-challenge-freevars another-fun)
                                                           (λ(x) (if (and (not(set-member? free x)) (not(set-member? not-free x)))
                                                                     (set-add! free x)
                                                                      (set! free free)))) another-fun)))]
           [f (λ(ee)
                (cond [(fun? ee) (begin (set-add! not-free (fun-arg ee)) (if (not (null? (fun-nameopt ee))) (set-add! not-free (fun-nameopt ee)) (set! free free))
                                        (if (fun? (fun-body ee)) (let ([another-fun (compute-free-vars(fun-body ee))])
                                            (fun-challenge (fun-nameopt ee) (fun-arg ee) another-fun (list->set (append (foldl (λ(x acc) (if (null? x) acc
                                                                                                                         (if (and (not(set-member? free x)) (not(set-member? not-free x))) (cons x acc)
                                                                                                                             acc))) null (set->list(fun-challenge-freevars another-fun))) (set->list free)))))
                                            (fun-challenge (fun-nameopt ee)(fun-arg ee) (f(fun-body ee)) (list->set(set->list free)))))]
                      [(mlet? ee) (begin (set-add! not-free (mlet-var ee)) (mlet (mlet-var ee)
                                                                                 (if (fun? (mlet-e ee)) (check-inside (mlet-e ee))
                                                                                     (f (mlet-e ee)))
                                                                                 (if (fun? (mlet-body ee)) (check-inside (mlet-body ee))
                                                                                     (f (mlet-body ee)))))]
                      [(var? ee) (if (and (not(set-member? free (var-string ee))) (not(set-member? not-free (var-string ee)))) (begin (set-add! free (var-string ee)) ee) ee)]
                      [(add? ee) (add  (f(add-e1 ee)) (f(add-e2 ee)))]
                      [(sub? ee) (sub  (f(sub-e1 ee)) (f(sub-e2 ee)))]
                      [(call? ee) (call (if (fun?(call-funexp ee)) (check-inside (call-funexp ee)) (f(call-funexp ee)))
                                        (if (fun?(call-actual ee)) (check-inside (call-actual ee))                                                                                                                                    
                                            (f(call-actual ee))))]
                      [(ifnz? ee) (ifnz (f (ifnz-e1 ee)) (if (fun? (ifnz-e2 ee)) (check-inside (ifnz-e2 ee)) (f(ifnz-e2 ee))) (if (fun? (ifnz-e3 ee)) (check-inside (ifnz-e3 ee)) (f(ifnz-e3 ee))))]
                      [(isgreater? ee) (isgreater (f (isgreater-e1 ee)) (f (isgreater-e2 ee)))]
                      [(apair? ee) (apair (f (apair-e1 ee)) (f (apair-e2 ee)))]
                      [(ismunit? ee) (ismunit (f (ismunit-e ee)))]
                      [(first? ee) (first (f (first-e ee)))]
                      [(second? ee) (second (f (second-e ee)))]
                      [(int? ee) ee]
                      [(munit? ee) ee]
                      
                      ))])
    (f e)))

;; Implemented using non-mutable set
(define (compute-free-vars2 e)
  (letrec ([helper (λ(expr)
                     (cond
                       [(var? expr) (cons expr (set (var-string expr)))]

                       [(int? expr) (cons expr (set))]

                       [(munit? expr) (cons expr (set))]

                       [(isgreater? expr) (let ([result-e1 (helper (isgreater-e1 expr))]
                                                [result-e2 (helper (isgreater-e2 expr))])
                                            (cons (isgreater (car result-e1) (car result-e2)) (set-union (cdr result-e1) (cdr result-e2))))]

                       [(ifnz? expr) (let ([result-e1 (helper (ifnz-e1 expr))]
                                           [result-e2 (helper (ifnz-e2 expr))]
                                           [result-e3 (helper (ifnz-e3 expr))])
                                            (cons (ifnz (car result-e1) (car result-e2) (car result-e3)) (set-union (set-union (cdr result-e1) (cdr result-e2)) (cdr result-e3))))]

                       [(apair? expr) (let ([result-e1 (helper (apair-e1 expr))]
                                            [result-e2 (helper (apair-e2 expr))])
                                        (cons (apair (car result-e1) (car result-e2)) (set-union (cdr result-e1) (cdr result-e2))))]

                       [(ismunit? expr) (let ([result (helper (ismunit-e expr))])
                                          (cons (ismunit (car result)) (cdr result)))]

                       [(call? expr) (let ([result-e1 (helper (call-funexp expr))]
                                           [result-e2 (helper (call-actual expr))])
                                       (cons (call (car result-e1) (car result-e2)) (set-union (cdr result-e1) (cdr result-e2))))]

                       [(first? expr) (let ([result (helper (first-e expr))])
                                        (cons (first (car result)) (cdr result)))]

                       [(second? expr) (let ([result (helper (second-e expr))])
                                         (cons (second (car result)) (cdr result)))]

                       [(add? expr) (let ([result-e1 (helper (add-e1 expr))]
                                                [result-e2 (helper (add-e2 expr))])
                                            (cons (add (car result-e1) (car result-e2)) (set-union (cdr result-e1) (cdr result-e2))))]

                       [(sub? expr) (let ([result-e1 (helper (sub-e1 expr))]
                                                [result-e2 (helper (sub-e2 expr))])
                                            (cons (sub (car result-e1) (car result-e2)) (set-union (cdr result-e1) (cdr result-e2))))]
                       
                       [(fun? expr) (let* ([result (helper (fun-body expr))]
                                          [free (if (null? (fun-nameopt expr)) (set-remove (cdr result) (fun-arg expr)) (set-remove (set-remove (cdr result) (fun-nameopt expr)) (fun-arg expr)))])
                                      (cons (fun-challenge (fun-nameopt expr) (fun-arg expr) (car result) free) free))]

                       [(mlet? expr) (let ([result-e (helper (mlet-e expr))]
                                           [result-body (helper (mlet-body expr))])
                                       (cons (mlet (mlet-var expr) (car result-e) (car result-body)) (set-remove (set-union (cdr result-e) (cdr result-body)) (mlet-var expr))))]

                       ))])
    (car (helper e))))


;; New eval-under-env specially made for fun-challenge
(define (eval-under-env-c e env)
  (cond [(var? e) 
         (envlookup env (var-string e))]

        [(int? e) e]
        
        [(add? e) 
         (let ([v1 (eval-under-env-c (add-e1 e) env)]
               [v2 (eval-under-env-c (add-e2 e) env)])
           (if (and (int? v1)
                    (int? v2))
               (int (+ (int-num v1) 
                       (int-num v2)))
               (error "MUPL addition applied to non-number")))]

        [(sub? e)
         (let ([v1 (eval-under-env (sub-e1 e) env)]
               [v2 (eval-under-env (sub-e2 e) env)])
           (if (and (int? v1)
                    (int? v2))
               (int (- (int-num v1) 
                       (int-num v2)))
               (error "MUPL subtraction applied to non-int")))]

        [(munit? e) e]
        
        [(fun-challenge? e) (closure (map (λ(x) (if (null? x) null (cons x (envlookup env x)))) (set->list (fun-challenge-freevars e))) e)]
    
        [(isgreater? e) (let ([left (eval-under-env-c (isgreater-e1 e) env)]
                              [right (eval-under-env-c (isgreater-e2 e) env)])
                          (if (and (int? left) (int? right))
                              (if (> (int-num left) (int-num right)) (int 1) (int 0))
                              (error "Using MUPL isgreater with non-int")))]
        
        [(ifnz? e) (let ([if-bool (eval-under-env-c (ifnz-e1 e) env)])
                     (if (int? if-bool)
                         (if (= 0 (int-num if-bool)) (eval-under-env-c (ifnz-e3 e) env)
                             (eval-under-env-c (ifnz-e2 e) env))
                         (error "e1 does not evaluate to MUPL int")))]
        
        [(mlet? e) (if (string? (mlet-var e)) (eval-under-env-c (mlet-body e) (cons (cons (mlet-var e)(eval-under-env-c (mlet-e e) env)) env))
                       (error "Variable name is non-string"))]

        [(call? e) (let ([funcEval (eval-under-env-c (call-funexp e) env)])
                     (if (closure? funcEval)
                         (eval-under-env-c (fun-challenge-body (closure-fun funcEval))
                                         (if (null? (fun-challenge-nameopt (closure-fun funcEval)))
                                              (append (list(cons(fun-challenge-arg (closure-fun funcEval)) (eval-under-env-c (call-actual e) env))) (closure-env funcEval))
                                              (append (list(cons(fun-challenge-nameopt (closure-fun funcEval)) funcEval) (cons(fun-challenge-arg(closure-fun funcEval)) (eval-under-env-c (call-actual e) env))) (closure-env funcEval))))
                         (error "Function call on non-function")))]

        [(apair? e) (apair (eval-under-env-c (apair-e1 e) env) (eval-under-env-c (apair-e2 e) env))]
        
        [(first? e) (let ([maybe-pair (eval-under-env-c (first-e e) env)])
                      (if (apair? maybe-pair) (apair-e1 maybe-pair)
                          (error "Call first on non-pair")))]

        [(second? e) (let ([maybe-pair (eval-under-env-c (second-e e) env)])
                       (if (apair? maybe-pair) (apair-e2 maybe-pair)
                           (error "Call second on non-pair")))]

        [(ismunit? e) (let ([is-null (eval-under-env-c (ismunit-e e) env)])
                        (if (munit? is-null) (int 1) (int 0)))]

        [#t (error (format "bad MUPL expression: ~v" e))]))

;; Call compute-free-vars helper that use mutable-set
(define (eval-mutable e)
  (eval-under-env-c (compute-free-vars e) null))

;; Call compute-free-vars helper that use non-mutable-set
(define (eval-non-mutable e)
  (eval-under-env-c (compute-free-vars2 e) null))

;; Hall of Fame function
(define mupl-filter
  (fun null "func"
       (fun "traverse" "val-list" (ifmunit (var "val-list") (munit)
                                           (ifeq (int 0) (call (var "func") (first (var "val-list")))
                                                 (call (var "traverse") (second (var "val-list")))
                                                 (apair (first (var "val-list")) (call (var "traverse")(second (var "val-list")))))))))
                  
(define mupl-all-gt ;; filter out number less than num in num-list
  (mlet "filter" mupl-filter
        (fun null "num"
             (fun null "num-list"
                  (call(call (var "filter") (fun null "x" (isgreater (var "x") (var "num")))) (var "num-list"))))))

(define mupl-foldl
  (fun "mupl-foldl" "func"
       (fun null "acc"
            (fun null "mupl-list"
                 (ifmunit (var "mupl-list") (var "acc")
                          (call (call (call (var "mupl-foldl") (var "func")) (call (call (var "func") (first (var "mupl-list"))) (var "acc"))) (second (var "mupl-list"))))))))

(define mupl-map
  (fun "mupl-map" "func"
       (fun null "mupl-list"
            (ifmunit (var "mupl-list") (munit)
            (apair (call (var "func") (first (var "mupl-list"))) (call (call (var "mupl-map")(var "func")) (second (var "mupl-list"))))))))


(define naive-nth-fib
  (fun "nth-fib" "n"
       (ifeq (var "n") (int 1) (int 0)
             (ifeq (var "n") (int 2) (int 1) (add (call (var "nth-fib") (sub (var "n") (int 1))) (call (var "nth-fib") (sub (var "n") (int 2))))))))
