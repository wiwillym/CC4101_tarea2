#lang play

;################################ Interprete visto en clases ###########################

#|
<expr> ::= (num <num>)
         | (add <expr> <expr>)
         | (sub <expr> <expr>)
         | (if0 <expr> <expr> <expr>)
         | (id <id>)
         | (fun <sym> <expr>)
         | (app <expr> <expr>)
|#
(deftype Expr
  (num n)
  (add l r)
  (sub l r)
  (if0 c t f)
  (id x)
  (fun arg body)
  (app f-name f-arg))


;; parse :: s-expr -> Expr
;; converts s-exprs into Exprs where
#|
<s-expr> ::= <num>
           | <sym>
           | (list '+  <s-expr> <s-expr>)
           | (list '-  <s-expr> <s-expr>)
           | (list 'if0  <s-expr> <s-expr> <s-expr>)
           | (list 'fun (list <sym>) <s-expr>)
           | (list <s-expr> <s-expr>)
           | (list 'with (list <sym> <s-expr>) <s-expr>)
|#
(define (parse s-expr)
  (match s-expr
    [ n #:when (number? n) (num n)]
    [ x #:when (symbol? x) (id x)]
    [(list '+ l r) (add (parse l) (parse r))]
    [(list '- l r) (sub (parse l) (parse r))]
    [(list 'if0 c t f) (if0 (parse c) (parse t) (parse f))]
    [(list 'fun (list x) b) (fun x (parse b))]
    [(list f a) (app (parse f) (parse a))]    
    [(list 'with (list x e) b) #:when (symbol? x)
         (app (fun x (parse b)) (parse e))]))


;; Abstract Dada Type (ADT) for handling environments 
;; empty-env  :: Env
;; extend-env :: Symbol Value Env -> Env
;; env-lookup :: Symbol Env -> Value

;; <env> ::= mtEnv
;;         | (aEnv <id> <value> <env>)
(deftype Env
  (mtEnv)
  (aEnv id val env))

(define empty-env (mtEnv))
 
(define extend-env aEnv)
 
(define (env-lookup x env)
  (match env
    [(mtEnv) (error 'env-lookup "free identifier: ~a" x)]
    [(aEnv id val rest) (if (symbol=? id x)
                            val
                            (env-lookup x rest))]))


;; Values of expressions 
;; <value> ::= (numV <number>)
;;          |  (closureV <sym> <s-expr> <env>) 
(deftype Value
  (numV n)
  (closureV id body env))

;; Auxiliary functions handling numeric Values
(define (op-bin f n1 n2)
  (numV (f (numV-n n1) (numV-n n2))))

(define (op-un f n)
  (numV (f (numV-n n))))


;; eval :: Expr Env -> Value
;; evaluates an expression in a given
;; environment using static scoping 
(define (eval expr env)
  (match expr
    [(num n) (numV n)]
    [(fun id body) (closureV id body env)]
    [(id x) (env-lookup x env)]
    [(add l r) (op-bin + (eval l env) (eval r env))]
    [(sub l r) (op-bin - (eval l env) (eval r env))]
    [(if0 c t f) (if  (op-un zero? (eval c env))
                      (eval t env)
                      (eval f env))]
    [(app f e) (def (closureV the-arg the-body the-claus-env) (eval f env))
               (def the-ext-env (extend-env the-arg (eval e env) the-claus-env))
               (eval the-body the-ext-env)]))


;; run :: s-expr -> Value
(define (run prog)
  (eval (parse prog) (mtEnv)))





;################################ Definiciones ###########################

(deftype Type
  (TNum)
  (TFun Targ Tret)
  (TVar Symbol))

(deftype Constraint
  (Cnst T1 T2))

(deftype TEnv
  (mtTEnv)
  (anTEnv id Type env))

(define count 0)

(define (get-id)
  (begin
    (set! count (add1 count))
    count))

(define (reset)
  (set! count 0))

(define (prettyfy T)
  (match T
    [(TNum) "num"]
    [(TVar x) (string-append "(TVar "(number->string x) ")")]
    [(TFun T1 T2) (string-append "(TFun " (prettyfy T1) " " (prettyfy T2) ")")]))




;################################ Su código va aquí ###########################

(define emptyT-env
  mtTEnv)

(define extendT-env
  anTEnv)

(define (lookupT-env x env)
  (match env
    [(mtTEnv) (error "Exception: free identifier" x)]
    [(anTEnv id Type rest) (if (symbol=? id x)
                            Type
                            (lookupT-env x rest))]))

(define (typeof expr env)
  (match expr
    [(num n) (list (TNum))]
    [(id x) (list(lookupT-env x env))]
    [(add expr1 expr2) (append(list (TNum)) (list (Cnst (car(typeof expr1 env))(TNum))(Cnst (car(typeof expr2 env)) (TNum))))]
    [(sub expr1 expr2) (append(list (TNum)) (list (Cnst (car(typeof expr1 env))(TNum))(Cnst (car(typeof expr2 env)) (TNum))))]
    [(if0 c t f) (append (typeof t env) (list(Cnst (car(typeof c env))(TNum))(Cnst (car(typeof t env))(car(typeof f env)))))]
    [(fun arg body)
     (def new-env (extendT-env arg (TVar (get-id)) env))
     (def new-body (typeof body new-env))
     (append(list(TFun (car(typeof (id arg) new-env)) (car new-body)))(cdr new-body))]
    [(app fun arg)
     (def appType (TVar (get-id)))
     (def funType (typeof fun env))
     (def argType (typeof arg env))
     (append(list appType)(cdr funType)(cdr argType)(list(Cnst (car funType)(TFun (car argType) appType))))]))

(define (substitute from to _list)
  (cond
    [(empty? _list) _list]
    [else (append (list (replacebycons (car _list) from to)) (substitute from to (cdr _list)))]))

(define (replacebytype type from to)
  (match type
    [(TNum) (TNum)]
    [(TVar n) (if (equalTVar type from)
                  to
                  type)]
    [(TFun A B) (TFun (replacebytype A from to) (replacebytype B from to))]))

(define (replacebycons cnst from to)
  (match cnst
    [(Cnst A B) (Cnst (replacebytype A from to) (replacebytype B from to))]))

(define (equalTVar tvar1 tvar2)
  (match tvar1
    [(TVar n1)
     (match tvar2
       [(TVar n2)(equal? n1 n2)])]))

(define (occurs-in? tvar t)
  (match t
    [(TNum) #f]
    [(TVar n) (equalTVar tvar t)]
    [(TFun T1 T2)(if (occurs-in? tvar T1)
                     #t
                     (occurs-in? tvar T2))]))


(define (equalT? t1 t2)
  (match t1
    [(TNum) (match t2
              [(TNum) #t]
              [(TVar n) #f]
              [(TFun A B) #f]
              )]
    [(TVar n1) (match t2
                [(TVar n2) (equal? n1 n2)]
                [(TNum) #f]
                [(TFun A B) #f]
                 )]
    [(TFun A1 B1) (match t2
                  [(TNum) #f]
                  [(TVar n) #f]
                  [(TFun A2 B2) (and (equalT? A1 A2) (equalT? B1 B2))])]))

(define (isTVar? t)
  (match t
    [(TNum) #f]
    [(TVar n) #t]
    [(TFun A B) #f]))

(define (unify _list)
  (cond [(empty? _list) empty]
        [else (def head (car _list))
              (def rest (cdr _list))
              (match head
                [(Cnst T1 T2)(if (equal? T1 T2)
                                 (unify rest)
                                 (if (and (isTVar? T1) (not(occurs-in? T1 T2)))
                                     (append (unify (substitute T1 T2 rest))(list (Cnst T1 T2)))
                                     (if (and (isTVar? T2) (not (occurs-in? T2 T1)))
                                         (append (unify (substitute T2 T1 rest))(list (Cnst T2 T1)))
                                         (match T1
                                           [(TNum) (error (string-append "Exception: Type error: cannot unify " (prettyfy T1) " with " (prettyfy T2)))]
                                           [(TVar n) (error (string-append "Exception: Type error: cannot unify " (prettyfy T1) " with " (prettyfy T1)))]
                                           [(TFun T1a T1r)
                                            (match T2
                                              [(TNum) (error (string-append "Exception: Type error: cannot unify " (prettyfy (TNum)) " with " (prettyfy T2)))]
                                              [(TVar n) (error (string-append "Exception: Type error: cannot unify " (prettyfy T1) " with " (prettyfy T2)))]
                                              [(TFun T2a T2r) (unify (append rest (list (Cnst T1a T2a) (Cnst T1r T2r))))])]))))])]))
                                            

(define (auxRun type cnstList in-cnstList)
  (match type
    [(TNum) type]
    [(TFun A B) (TFun (auxRun A cnstList in-cnstList) (auxRun B cnstList in-cnstList))]
    [(TVar n) (if (empty? cnstList)
                  type
                  (match (car cnstList)
                    [(Cnst T1 T2)
                     (if (and (isTVar? T1) (equalTVar type T1))
                     (auxRun T2 in-cnstList in-cnstList)
                     (auxRun type (cdr cnstList) in-cnstList))
                     ])
                  )]
                
  ))

(define (runType s-expr)
  (reset)
  (def type_of (typeof (parse s-expr) (emptyT-env)))
  (def unified (unify (cdr type_of)))
  (auxRun (car type_of) unified unified))

