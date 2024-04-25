#lang racket

;; definition of structures for MUPL programs
(struct var  (string) #:transparent)  ;; a variable, e.g., (var "foo")
(struct int  (num)    #:transparent)  ;; a constant number, e.g., (int 17)
(struct add  (e1 e2)  #:transparent)  ;; add two expressions
(struct isgreater (e1 e2)    #:transparent) ;; if e1 > e2 then 1 else 0
(struct ifnz (e1 e2 e3) #:transparent) ;; if not zero e1 then e2 else e3
(struct call (funexp actual)       #:transparent) ;; function call
(struct mlet (var e body) #:transparent) ;; a local binding (let var = e in body) 
(struct apair   (e1 e2) #:transparent) ;; make a new pair
(struct first   (e)     #:transparent) ;; get first part of a pair
(struct second  (e)     #:transparent) ;; get second part of a pair
(struct munit   ()      #:transparent) ;; unit value -- good for ending a list
(struct ismunit (e)     #:transparent) ;; if e1 is unit then 1 else 0
(struct fun  (nameopt formal body) #:transparent) ;; a recursive(?) 1-argument function, e.g., (fun "add-1" "x" (add (var "x") (int 1))) --
                                                  ;;since function have a name ("add-1"), it is a recursive funciton. Otherwise if it have null, it's an anonymous function


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
        [(add? e) 
         (let ([v1 (eval-under-env (add-e1 e) env)]
               [v2 (eval-under-env (add-e2 e) env)])
           (if (and (int? v1)
                    (int? v2))
               (int (+ (int-num v1) 
                       (int-num v2)))
               (error "MUPL addition applied to non-number")))]

        [(munit? e) e]
        
        [(fun? e) (closure env e)]
    
        [(int? e) e]
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
                                              (cons(cons(fun-formal(closure-fun funcEval)) (eval-under-env (call-actual e) env)) (closure-env funcEval))
                                              (append (list(cons(fun-nameopt (closure-fun funcEval)) funcEval) (cons(fun-formal(closure-fun funcEval)) (eval-under-env (call-actual e) env))) (closure-env funcEval))))
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

;; "Macros" in MUPL is Racket function

(define (eval-exp e)
  (eval-under-env e null))

(define (ifmunit e1 e2 e3) (ifnz (ismunit e1) e2 e3)) ;; if statement using munit

(define (mlet* bs e2) ;;let* but in MUPL
  (if (null? bs) e2
      (mlet (car (car bs)) (cdr (car bs)) (mlet* (cdr bs) e2))))

(define (ifeq e1 e2 e3 e4) ;; if e1 = e2 then e3 else e4
  (mlet* (list (cons "_x" e1)(cons "_y" e2))
         (ifnz (isgreater (var "_x") (var "_y")) e4
               (ifnz (isgreater (var "_y") (var "_x")) e4
                     e3))))


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



;; Challenge -- Making a more efficient closure that only store "free variables"
;; in the function instead of evaluating it under the environment every call

(struct fun-challenge (nameopt formal body freevars) #:transparent) ;; a recursive(?) 1-argument function

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
                (cond [(fun? ee) (begin (set-add! not-free (fun-formal ee)) (if (not (null? (fun-nameopt ee))) (set-add! not-free (fun-nameopt ee)) (set! free free))
                                        (if (fun? (fun-body ee)) (let ([another-fun (compute-free-vars(fun-body ee))])
                                            (fun-challenge (fun-nameopt ee) (fun-formal ee) another-fun (list->set (append (foldl (λ(x acc) (if (null? x) acc
                                                                                                                         (if (and (not(set-member? free x)) (not(set-member? not-free x))) (cons x acc)
                                                                                                                             acc))) null (set->list(fun-challenge-freevars another-fun))) (set->list free)))))
                                            (fun-challenge (fun-nameopt ee)(fun-formal ee) (f(fun-body ee)) (list->set(set->list free)))))]
                      [(mlet? ee) (begin (set-add! not-free (mlet-var ee)) (mlet (mlet-var ee)
                                                                                 (if (fun? (mlet-e ee)) (check-inside (mlet-e ee))
                                                                                     (f (mlet-e ee)))
                                                                                 (if (fun? (mlet-body ee)) (check-inside (mlet-body ee))
                                                                                     (f (mlet-body ee)))))]
                      [(var? ee) (if (and (not(set-member? free (var-string ee))) (not(set-member? not-free (var-string ee)))) (begin (set-add! free (var-string ee)) ee) ee)]
                      [(add? ee) (add  (f(add-e1 ee)) (f(add-e2 ee)))] 
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
  (letrec ([cross-check (λ(cross-check-list set-free set-not-free) ;; list -> set -> set -> set
                          (foldl (λ(z acc) (if (null? z) acc (set-add acc z))) set-free (filter (λ(x) (not (or (set-member? set-free x) (set-member? set-not-free x)))) cross-check-list)))]
           [helper (λ(expression free not-free)
                     (cond
                       [(munit? expression) (cons expression (set->list free))]
                       [(var? expression) (cons expression (set->list(cross-check (list (var-string expression)) free not-free)))]

                       [(int? expression) (cons expression (set->list free))]

                       [(isgreater? expression)
                        (let ([e1-notfunc (helper (isgreater-e1 expression) free not-free)]
                              [e2-notfunc (helper (isgreater-e2 expression) free not-free)])
                          (cons (isgreater (car e1-notfunc) (car e2-notfunc)) (set->list (cross-check (cdr e1-notfunc) (set->list (cross-check (cdr e2-notfunc) free not-free)) not-free))))]

                       [(apair? expression)
                        (let ([e1-notfunc (helper (apair-e1 expression) free not-free)]
                              [e2-notfunc (helper (apair-e2 expression) free not-free)])
                          (cons (apair (car e1-notfunc) (car e2-notfunc)) (set->list (cross-check (cdr e1-notfunc) (set->list (cross-check (cdr e2-notfunc) free not-free)) not-free))))]

                       [(ismunit? expression)
                        (let ([e1-notfunc (helper (ismunit-e expression) free not-free)])
                          (cons (ismunit (car e1-notfunc)) (set->list (cross-check (cdr e1-notfunc)free not-free))))]

                       [(first? expression)
                        (let ([e1-notfunc (helper (first-e expression) free not-free)])
                          (cons (first (car e1-notfunc)) (set->list (cross-check (cdr e1-notfunc)free not-free))))]

                       [(second? expression)
                        (let ([e1-notfunc (helper (second-e expression) free not-free)])
                          (cons (second (car e1-notfunc)) (set->list (cross-check (cdr e1-notfunc)free not-free))))]
                        
                       [(ifnz? expression)
                        (let* ([e1-notfunc (helper (ifnz-e1 expression) free not-free)]
                              [new-free (cross-check (cdr e1-notfunc) free not-free)])
                          (if (fun? (ifnz-e2 expression))
                              (let* ([e2-func (helper (ifnz-e2 expression) (set) (set))]
                                     [newer-new-free (cross-check (set->list (fun-challenge-freevars e2-func)) new-free not-free)])

                                (if (fun? (ifnz-e3 expression))
                                    (let ([e3-func (helper (ifnz-e3 expression) (set) (set))])
                                      (cons (ifnz (car e1-notfunc) e2-func e3-func) (set->list (cross-check (set->list(fun-challenge-freevars e3-func)) newer-new-free  not-free))))

                                    (let ([e3-notfunc (helper (ifnz-e3 expression) newer-new-free not-free)])
                                      (cons (ifnz (car e1-notfunc) e2-func (car e3-notfunc)) (set->list (cross-check (cdr e3-notfunc) newer-new-free not-free))))))

                              (let* ([e2-notfunc (helper (ifnz-e2 expression) new-free not-free)]
                                     [newer-new-free (cross-check (cdr e2-notfunc) new-free not-free)])

                                (if (fun? (ifnz-e3 expression))
                                    (let ([e3-func (helper (ifnz-e3 expression) (set) (set))])
                                      (cons (ifnz (car e1-notfunc) (car e2-notfunc) e3-func) (set->list (cross-check (set->list(fun-challenge-freevars e3-func)) newer-new-free  not-free))))

                                    (let ([e3-notfunc (helper (ifnz-e3 expression) newer-new-free not-free)])
                                      (cons (ifnz (car e1-notfunc) (car e2-notfunc) (car e3-notfunc)) (set->list (cross-check (cdr e3-notfunc) newer-new-free not-free))))))))]
                          
                          

                       [(add? expression)
                        (let* ([e1-notfunc (helper (add-e1 expression) free not-free)]
                               [new-free (cross-check (cdr e1-notfunc) free not-free)])
                          (let ([e2-notfunc (helper (add-e2 expression) new-free not-free)])
                            (cons (add (car e1-notfunc) (car e2-notfunc)) (set->list (cross-check (cdr e2-notfunc) new-free not-free)))))]

                       [(call? expression)
                        (if (fun? (call-funexp expression))
                            (let* ([e1-func (helper (call-funexp expression) (set) (set))]
                                   [new-free (cross-check (set->list (fun-challenge-freevars e1-func)) free not-free)])

                              (if (fun? (call-actual expression))
                                  (let ([e2-func (helper (call-actual expression) (set) (set))])
                                    (cons (call e1-func e2-func)(set->list (cross-check (set->list (fun-challenge-freevars e2-func)) new-free not-free))))

                                  (let ([e2-notfunc (helper (call-actual expression) free not-free)])
                                    (cons (call e1-func (car e2-notfunc)) (set->list (cross-check (cdr e2-notfunc) new-free not-free))))))

                            (let* ([e1-notfunc (helper (call-funexp expression) free not-free)]
                                   [new-free (cross-check (cdr e1-notfunc) free not-free)])

                              (if (fun? (call-actual expression))
                                  (let ([e2-func (helper (call-actual expression) (set) (set))])
                                    (cons (call (car e1-notfunc) e2-func) (set->list (cross-check (set->list(fun-challenge-freevars e2-func)) new-free not-free))))

                                  (let ([e2-notfunc (helper (call-actual expression) free not-free)])
                                    (cons (call (car e1-notfunc) (car e2-notfunc)) (set->list (cross-check (cdr e2-notfunc) new-free not-free)))))))]

                       [(fun? expression)
                        (let ([new-not-free (if (null? (fun-nameopt expression)) (set-add not-free (fun-formal expression)) (set-add (set-add not-free (fun-formal expression)) (fun-nameopt expression)))])

                          (if (fun? (fun-body expression))
                              (let ([new-body (helper (fun-body expression)(set)(set))])
                                (fun-challenge (fun-nameopt expression) (fun-formal expression) new-body (cross-check (set->list(fun-challenge-freevars new-body)) free new-not-free)))
                              (let ([new-body (helper (fun-body expression) free new-not-free)])
                                (fun-challenge (fun-nameopt expression) (fun-formal expression) (car new-body) (cross-check (cdr new-body) free new-not-free)))))]

                           [(mlet? expression)
                            (let ([new-not-free (set-add not-free (mlet-var expression))])
                              
                              (if (fun? (mlet-e expression))
                                  (let* ([e-isfunc (helper (mlet-e expression) (set) (set))]
                                         [new-free (cross-check (set->list(fun-challenge-freevars e-isfunc)) free new-not-free)])
                                    
                                    (if (fun? (mlet-body expression))
                                        (let ([body-func (helper (mlet-body expression) (set)(set))])
                                          (cons (mlet (mlet-var expression) e-isfunc body-func) (set->list(cross-check (set->list (fun-challenge-freevars body-func)) new-free new-not-free))))
                                        (let ([body-not-func (helper (mlet-body expression) new-free new-not-free)])
                                          (cons (mlet (mlet-var expression) e-isfunc (car body-not-func)) (set->list(cross-check (cdr body-not-func) new-free new-not-free))))))

                                  (let* ([e-notfunc (helper (mlet-e expression) free new-not-free)]
                                         [new-free (cross-check (cdr e-notfunc) free new-not-free)])

                                    (if (fun? (mlet-body expression))
                                        (let ([body-func (helper (mlet-body expression) (set)(set))])
                                          (cons (mlet (mlet-var expression) (car e-notfunc) body-func) (set->list(cross-check (set->list (fun-challenge-freevars body-func)) new-free new-not-free))))
                                        (let ([body-not-func (helper (mlet-body expression) new-free new-not-free)])
                                          (cons (mlet (mlet-var expression) (car e-notfunc) (car body-not-func)) (set->list(cross-check (cdr body-not-func) new-free new-not-free))))))))]))])

    (if (fun? e) (helper e (set)(set)) (car (helper e (set) (set))))))

;; New eval-under-env specially made for fun-challenge that have free var
(define (eval-under-env-c e env)
  (cond [(var? e) 
         (envlookup env (var-string e))]
        [(add? e) 
         (let ([v1 (eval-under-env-c (add-e1 e) env)]
               [v2 (eval-under-env-c (add-e2 e) env)])
           (if (and (int? v1)
                    (int? v2))
               (int (+ (int-num v1) 
                       (int-num v2)))
               (error "MUPL addition applied to non-number")))]

        [(munit? e) e]
        
        [(fun-challenge? e) (closure (map (λ(x) (if (null? x) null (cons x (envlookup env x)))) (set->list (fun-challenge-freevars e))) e)]
    
        [(int? e) e]
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
                                              (append (list(cons(fun-challenge-formal (closure-fun funcEval)) (eval-under-env-c (call-actual e) env))) (closure-env funcEval))
                                              (append (list(cons(fun-challenge-nameopt (closure-fun funcEval)) funcEval) (cons(fun-challenge-formal(closure-fun funcEval)) (eval-under-env-c (call-actual e) env))) (closure-env funcEval))))
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
(define (eval-exp-mutable e)
  (eval-under-env-c (compute-free-vars e) null))

;; Call compute-free-vars helper that use non-mutable-set
(define (eval-exp-non-mutable e)
  (eval-under-env-c (compute-free-vars2 e) null))
