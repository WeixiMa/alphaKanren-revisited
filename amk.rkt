;#lang typed/racket
#lang typed/racket/no-check

(provide (all-defined-out))

(struct name
  ([symb : Symbol])
  #:transparent)
(define-type Name name)
(struct variable
  ([symb : Symbol])
  #:transparent)
(define-type Variable variable)
(define (constant? x)
  (or (symbol? x)
      (boolean? x)
      (integer? x)
      (null? x)))
(struct tie
  ([name : Name]
   [term : Term])
  #:transparent)
(define-type Tie tie)
(define-type Term
  (U Symbol Boolean Integer Null
     Variable
     Name
     Tie
     (Pairof Term Term)))

(struct Scope
  ([name->level : (Immutable-HashTable Name Integer)]
   [level->name : (Immutable-HashTable Integer Name)]))
(: show-scope (-> Scope (Listof Name)))
(define (show-scope φ)
  (let ([level->name (Scope-level->name φ)])
    (letrec ([loop : (-> Integer (Listof Name))
                   (λ (n)
                     (cond
                       [(zero? n)  '()]
                       [else (cons (hash-ref level->name (sub1 n))
                                   (loop (sub1 n)))]))])
      (loop (hash-count level->name)))))
(: empty-scope? (-> Scope Boolean))
(define (empty-scope? φ)
  (eqv? (hash-count (Scope-level->name φ)) 0))
(define (init-scope)
  (Scope (make-immutable-hasheqv) (make-immutable-hasheqv)))
(: ext-scp (-> Scope Name Scope))
(define (ext-scp φ n)
  (let ([l (hash-count (Scope-name->level φ))])
    (Scope (hash-set (Scope-name->level φ) n l)
           (hash-set (Scope-level->name φ) l n))))
(: bound? (-> Scope Name (U Integer False)))
(define (bound? φ n)
  (hash-ref (Scope-name->level φ) n #f))
(: free? (-> Scope Name Boolean))
(define (free? φ n)
  (not (bound? φ n)))
(: find-name (-> Scope Integer (U Name False)))
(define (find-name φ l)
  (let ([n (hash-ref (Scope-level->name φ) l #f)])
    (and n
         (eqv? (hash-ref (Scope-name->level φ) n) l)
         n)))
(: same-name? (-> Scope Name Scope Name Boolean))
(define (same-name? φ₁ n₁ φ₂ n₂)
  (let ([l₁ (bound? φ₁ n₁)]
        [l₂ (bound? φ₂ n₂)])
    (cond
      [(and l₁ l₂) (eqv? l₁ l₂)]
      [(and (not l₁) (not l₂)) (eqv? l₁ l₂)]
      [else #f])))
(: gen-name (-> Scope Name Scope (U Name False)))
(define (gen-name φ₁ n₁ φ₂)
  (cond
    [(bound? φ₁ n₁)
     =>
     (λ (l) (find-name φ₂ l))]
    [(free? φ₂ n₁) n₁]
    [else #f]))

(define-type Substitution
  (Immutable-HashTable Variable Term))
(define-type Partition
  (Immutable-HashTable Variable (Listof (List Scope Scope Variable))))
(: ext-subst (-> Substitution Variable Term Substitution))
(define (ext-subst σ v t)
  (hash-set σ v t))
(: walk (-> Substitution Term Term))
(define (walk σ t)
  (cond
    [(and (variable? t) (hash-ref σ t #f))
     =>
     (λ (t) (walk σ t))]
    [else t]))
(: ext-par (-> Partition Scope Variable Scope Variable Partition))
(define (ext-par χ φ₁ v₁ φ₂ v₂)
  (let ([ls₁ (or (hash-ref χ v₁ #f) '())]
        [ls₂ (or (hash-ref χ v₂ #f) '())])
    (hash-set (hash-set χ v₁ (cons `(,φ₁ ,φ₂ ,v₂) ls₁))
              v₂ (cons `(,φ₂ ,φ₁ ,v₁) ls₂))))

(: unif (-> Scope Term Scope Term Substitution Partition (Listof Variable)
            (U (List Substitution Partition (Listof Variable)) False)))
(define (unif φ₁ t₁ φ₂ t₂ σ χ xs)
  (let ([t₁ (walk σ t₁)]
        [t₂ (walk σ t₂)])
    (if (empty-scope? φ₁) #|if it's just first-order|#
        (cond
          [(eqv? t₁ t₂) (list σ χ xs)]
          [(variable? t₁) (list (ext-subst σ t₁ t₂) χ (cons t₁ xs))]
          [(variable? t₂) (list (ext-subst σ t₂ t₁) χ (cons t₂ xs))]
          [(and (pair? t₁) (pair? t₂))
           (match (unif φ₁ (car t₁) φ₂ (car t₂) σ χ xs)
             [#f #f]
             [`(,σ ,χ ,xs) (unif φ₁ (cdr t₁) φ₂ (cdr t₂) σ χ xs)])]
          [(and (tie? t₁) (tie? t₂))
           (unif (ext-scp φ₁ (tie-name t₁))
                 (tie-term t₁)
                 (ext-scp φ₂ (tie-name t₂))
                 (tie-term t₂)
                 σ χ xs)]
          [(and (variable? t₁) (tie? t₂))
           (let ([n₁ (name (gensym (name-symb (tie-name t₂))))]
                 [v₁ (variable (gensym))])
             (unif (ext-scp φ₁ n₁)
                   v₁
                   (ext-scp φ₂ (tie-name t₂))
                   (tie-term t₂)
                   (ext-subst σ t₁ (tie n₁ v₁))
                   χ
                   xs))]
          [(and (tie? t₁) (variable? t₂))
           (let ([n₂ (name (gensym (name-symb (tie-name t₁))))]
                 [v₂ (variable (gensym))])
             (unif (ext-scp φ₁ (tie-name t₁))
                   (tie-term t₁)
                   (ext-scp φ₂ n₂)
                   v₂
                   (ext-subst σ t₂ (tie n₂ v₂))
                   χ
                   xs))]
          [else #f])
        (cond
          [(and (constant? t₁) (constant? t₂))
           (and (eqv? t₁ t₂)
                (list σ χ xs))]
          [(and (constant? t₁) (variable? t₂))
           (list (ext-subst σ t₂ t₁) χ (cons t₂ xs))]
          [(and (variable? t₁) (constant? t₂))
           (list (ext-subst σ t₁ t₂) χ (cons t₁ xs))]
          [(and (variable? t₁) (variable? t₂))
           (list σ (ext-par χ φ₁ t₁ φ₂ t₂) xs)]
          [(and (name? t₁) (name? t₂))
           (and (same-name? φ₁ t₁ φ₂ t₂)
                (list σ χ xs))]
          [(and (name? t₁) (variable? t₂))
           (let ([n₂ (gen-name φ₁ t₁ φ₂)])
             (and n₂
                  (list (ext-subst σ t₂ n₂) χ (cons t₂ xs))))]
          [(and (variable? t₁) (name? t₂))
           (let ([n₁ (gen-name φ₂ t₂ φ₁)])
             (and n₁
                  (list (ext-subst σ t₁ n₁) χ (cons t₁ xs))))]
          [(and (tie? t₁) (tie? t₂))
           (unif (ext-scp φ₁ (tie-name t₁))
                 (tie-term t₁)
                 (ext-scp φ₂ (tie-name t₂))
                 (tie-term t₂)
                 σ χ xs)]
          [(and (pair? t₁) (pair? t₂))
           (match (unif φ₁ (car t₁) φ₂ (car t₂) σ χ xs)
             [#f #f]
             [`(,σ ,χ ,xs) (unif φ₁ (cdr t₁) φ₂ (cdr t₂) σ χ xs)])]
          [(and (variable? t₁) (tie? t₂))
           (let* ([n₁ (or (gen-name φ₂ (tie-name t₂) φ₁)
                          (name (gensym (name-symb (tie-name t₂)))))]
                  [v₁ (variable (gensym))])
             (unif (ext-scp φ₁ n₁)
                   v₁
                   (ext-scp φ₂ (tie-name t₂))
                   (tie-term t₂)
                   (ext-subst σ t₁ (tie n₁ v₁))
                   χ
                   (cons t₁ xs)))]
          [(and (tie? t₁) (variable? t₂))
           (let* ([n₂ (or (gen-name φ₁ (tie-name t₁) φ₂)
                          (name (gensym (name-symb (tie-name t₁)))))]
                  [v₂ (variable (gensym))])
             (unif (ext-scp φ₁ (tie-name t₁))
                   (tie-term t₁)
                   (ext-scp φ₂ n₂)
                   v₂
                   (ext-subst σ t₂ (tie n₂ v₂))
                   χ
                   (cons t₂ xs)))]
          [(and (variable? t₁) (pair? t₂))
           (let ([v₁ (variable (gensym))]
                 [v₂ (variable (gensym))])
             (match (unif φ₁ v₁ φ₂ (car t₂) (ext-subst σ t₁ (cons v₁ v₂)) χ xs)
               [#f #f]
               [`(,σ ,χ ,xs) (unif φ₁ v₂ φ₂ (cdr t₂) σ χ xs)]))]
          [(and (pair? t₁) (variable? t₂))
           (let ([v₁ (variable (gensym))]
                 [v₂ (variable (gensym))])
             (match (unif φ₁ (car t₁) φ₂ v₁ (ext-subst σ t₂ (cons v₁ v₂)) χ xs)
               [#f #f]
               [`(,σ ,χ ,xs) (unif φ₁ (cdr t₁) φ₂ v₂ σ χ xs)]))]
          [else #f]))))

#|
(: pull (-> Name (Listof (List Scope Scope Variable)) Substitution (Listof Variable)
            (U (Pairof Substitution (Listof Variable)) False)))
(define (pull n₁ ls σ xs)
  (match ls
    ['() (cons σ xs)]
    [`((,φ₁ ,φ₂ ,v₂) . ,ls)
     (cond
       [(hash-ref σ v₂ #f)
        =>
        (λ (n₂) (and (name? n₂) (same-name? φ₁ n₁ φ₂ n₂) (pull n₁ ls σ xs)))]
       [(gen-name φ₁ n₁ φ₂)
        =>
        (λ (n₂) (pull n₁ ls (ext-subst σ v₂ n₂) (cons v₂ xs)))]
       [else #f])]))
(: refine (-> (Listof Variable) Substitution Partition
              (U (Pairof Substitution Partition) False)))
(define (refine xs σ χ)
  (cond
    [(null? xs) (cons σ χ)]
    [(eqv? (hash-count χ) 0) (cons σ χ)]
    [else (let* ([v (car xs)]
                 [n (hash-ref σ v)]
                 [par (or (hash-ref χ v #f) '())])
            (if (name? n)
                (match (pull n par σ (cdr xs))
                  [#f #f]
                  [(cons σ xs) (refine xs σ (hash-remove χ v))])
                (refine (cdr xs) σ (hash-remove χ v))))]))
|#

(: refine (-> (Listof Variable) Substitution Partition
              (U (List Substitution Partition) False)))
(define (refine xs σ χ)
  (cond
    [(null? xs) (list σ χ)]
    [(zero? (hash-count χ)) (list σ χ)]
    [else (let* ([x (car xs)]
                 [t (hash-ref σ x)]
                 [slice (or (hash-ref χ x #f) '())])
            (match (unif-all t slice (cdr xs) σ (hash-remove χ x))
              [#f #f]
              [`(,xs ,σ ,χ) (refine xs σ χ)]))]))
(: unif-all (-> Term (Listof (List Scope Scope Variable))
                (Listof Variable) Substitution Partition
                (U (List (Listof Variable) Substitution Partition) False)))
(define (unif-all t₁ ls xs σ χ)
  (match ls
    ['() (list xs σ χ)]
    [`((,φ₁ ,φ₂ ,v₂) . ,ls)
     (cond
       [(hash-ref σ v₂ #f)
        =>
        (λ (t₂)
          (match (unif φ₁ t₁ φ₂ t₂ σ χ '())
            [`(,σ ,χ _) (unif-all t₁ ls xs σ χ)]
            [#f #f]))]
       [else (match (unif φ₁ t₁ φ₂ v₂ σ χ '())
               [`(,σ ,χ _) (unif-all t₁ ls (cons v₂ xs) σ χ)]
               [#f #f])])]))

(: unify (-> Scope Term Scope Term Substitution Partition
             (U (List Substitution Partition (Listof Variable)) False)))
(define (unify φ₁ t₁ φ₂ t₂ σ χ)
  (match (unif φ₁ t₁ φ₂ t₂ σ χ '())
    [#f #f]
    [`(,σ ,χ ,xs)
     (match (refine xs σ χ)
       [#f #f]
       [`(,σ ,χ) (list σ χ xs)])]))

(define-type FEnv
  #|name is fresh in the var|#
  (Immutable-HashTable Variable (Listof (Pairof Name Scope))))
(define-type FEnv2
  #|var is fresh in the term|#
  (Immutable-HashTable Variable (Listof Term)))
(: ext-fenv (-> FEnv Variable Name Scope FEnv))
(define (ext-fenv fenv v n φ)
  (let ([ls (or (hash-ref fenv v #f) '())])
    (hash-set fenv v (cons (cons n φ) ls))))

(struct State
  ([σ : Substitution]
   [χ : Partition]
   [fenv : FEnv]
   [fenv2 : FEnv2])
  #:transparent)
(define-type (Streamof A)
  (U Null
     (Pairof A (Streamof A))
     (-> (Streamof A))))
(define-type Goal
  (-> State (Streamof State)))
(: succeed Goal)
(define (succeed s) (list s))
(: fail Goal)
(define (fail s) (list))
(: $merge (All (A) (-> (Streamof A) (Streamof A) (Streamof A))))
(define ($merge $₁ $₂)
  (cond
    [(null? $₁) $₂]
    [(pair? $₁) (cons (car $₁) ($merge (cdr $₁) $₂))]
    [else (λ () ($merge $₂ ($₁)))]))
(: $merge-map (All (A) (-> (-> A (Streamof A)) (Streamof A) (Streamof A))))
(define ($merge-map f $)
  (cond
    [(null? $) '()]
    [(pair? $) ($merge (f (car $))
                       ($merge-map f (cdr $)))]
    [else (λ () ($merge-map f ($)))]))
(: $take (All (A) (-> Integer (Streamof A) (Listof A))))
(define ($take i $)
  (cond
    [(and i (zero? i)) '()]
    [(null? $) '()]
    [(pair? $) (cons (car $) ($take (and i (sub1 i)) (cdr $)))]
    [else ($take i ($))]))
(: disj₂ (-> Goal Goal Goal))
(define ((disj₂ g₁ g₂) S)
  ($merge (g₁ S) (g₂ S)))
(: conj₂ (-> Goal Goal Goal))
(define ((conj₂ g₁ g₂) S)
  ($merge-map g₂ (g₁ S)))

(: walk* (-> Substitution Term Term))
(define (walk* σ t)
  (let ([t (walk σ t)])
    (cond
      [(pair? t) (cons (walk* σ (car t))
                       (walk* σ (cdr t)))]
      [(tie? t) (tie (tie-name t)
                     (walk* σ (tie-term t)))]
      [else t])))
(: reify-s (-> Substitution Term Substitution))
(define (reify-s σ t)
  (let ([t (walk σ t)])
    (cond
      [(variable? t) (let* ([n (hash-count σ)]
                            [rn (string->symbol
                                 (string-append "_" (number->string n)))])
                       (hash-set σ t rn))]
      [(pair? t) (let ([σ (reify-s σ (car t))])
                   (reify-s σ (cdr t)))]
      [(tie? t) (reify-s σ (tie-term t))]
      [else σ])))
(: reify (-> Term (-> State Term)))
(define ((reify t) state)
  (match state
    [(State σ χ fenv fenv2)
     (let* ([t (walk* σ t)]
            [names (reify-s (make-immutable-hasheqv) t)])
       #;
       `(,(walk* names t) (,σ ,χ ,fenv ,fenv2))
       (walk* names t))]))

(: call/fresh (-> Symbol (-> Name Goal) Goal))
(define (call/fresh symb f)
  (f (name symb)))
(: call/exist (-> Symbol (-> Variable Goal) Goal))
(define (call/exist symb f)
  (f (variable symb)))
(define (init-state)
  (State (make-immutable-hasheqv)
         (make-immutable-hasheqv)
         (make-immutable-hasheqv)
         (make-immutable-hasheqv)))
(: run-goal (-> Integer Goal (Listof State)))
(define (run-goal i g)
  ($take i (g (init-state))))

(: == (-> Term Term Goal))
(define ((== t₁ t₂) state)
  (match state
    [(State σ χ fenv fenv2)
     (match (unify (init-scope) t₁
                   (init-scope) t₂
                   σ χ)
       [#f (list)]
       [(list σ χ xs)
        (let ([fenv (validate-fenv xs σ fenv)])
          (if fenv
              (match (validate-fenv2 xs σ fenv fenv2)
                [(cons fenv fenv2) (list (State σ χ fenv fenv2))]
                [#f (list)])
              (list)))])]))

(: validate-fenv2 (-> (Listof Variable) Substitution FEnv FEnv2
                      (U (Pairof FEnv FEnv2) False)))
(define (validate-fenv2 xs σ fenv fenv2)
  (cond
    [(null? xs) (cons fenv fenv2)]
    [(hash-ref fenv2 (car xs) #f)
     =>
     (λ ([ls : (Listof Term)])
       (let ([n (hash-ref σ (car xs))])
         (cond
           [(name? n)
            (let ([fenv (validate-fenv2-each n ls fenv)])
              (and fenv
                   (cons
                    fenv
                    (hash-remove fenv2 (car xs)))))]
           [(variable? n) (validate-fenv2 (cdr xs) σ fenv fenv2)]
           [else #f])))]
    [else (validate-fenv2 (cdr xs) σ fenv fenv2)]))

(: validate-fenv2-each (-> Name (Listof Term) FEnv
                           (U FEnv False)))
(define (validate-fenv2-each n ts fenv)
  (cond
    [(null? ts) fenv]
    [else (let ([r (free-in? n (car ts) (init-scope) fenv)])
            (cond
              [(not r) (validate-fenv2-each n (cdr ts) fenv)]
              [(eqv? r #t) #f]
              [else (validate-fenv2-each n (cdr ts) r)]))]))

(: validate-fenv (-> (Listof Variable) Substitution FEnv
                     (U FEnv False)))
(define (validate-fenv xs σ fenv)
  (cond
    [(null? xs) fenv]
    [(hash-ref fenv (car xs) #f)
     =>
     (λ ([ls : (Listof (Pairof Name Scope))])
       (let ([fenv (validate-fenv-each (hash-ref σ (car xs))
                                       ls
                                       (hash-remove fenv (car xs)))])
         (and fenv (validate-fenv (cdr xs) σ fenv))))]
    [else (validate-fenv (cdr xs) σ fenv)]))

(: validate-fenv-each (-> Term (Listof (Pairof Name Scope)) FEnv
                          (U FEnv False)))
(define (validate-fenv-each t prs fenv)
  (match prs
    ['() fenv]
    [`((,n . ,φ) . ,prs)
     (let ([r (free-in? n t φ fenv)])
       (cond
         [(not r) (validate-fenv-each t prs fenv)]
         [(eqv? r #t) #f]
         [else (validate-fenv-each t prs r)]))]))

(define-syntax disj
  (syntax-rules ()
    [(disj) fail]
    [(disj g) g]
    [(disj g₀ g ...) (disj₂ g₀ (disj g ...))]))
(define-syntax conj
  (syntax-rules ()
    [(conj) succeed]
    [(conj g) g]
    [(conj g₀ g ...) (conj₂ g₀ (conj g ...))]))
(define-syntax defrel
  (syntax-rules ()
    [(defrel (name x ...) g ...)
     (define (name x ...)
       (λ (s)
         (λ ()
           ((conj g ...) s))))]))
(define-syntax run
  (syntax-rules ()
    [(run n (x₀ x ...) g ...)
     (run n q (exist (x₀ x ...)
                     (== `(,x₀ ,x ...) q)
                     g ...))]
    [(run n q g ...)
     (let ([q (variable 'q)])
       (map (reify q) (run-goal n (conj g ...))))]))
(define-syntax run*
  (syntax-rules ()
    [(run* q g ...) (run #f q g ...)]))
(define-syntax fresh
  (syntax-rules ()
    [(fresh () g ...) (conj g ...)]
    [(fresh (x₀ x ...) g ...)
     (call/fresh 'x₀
                 (λ (x₀)
                   (fresh (x ...) g ...)))]))
(define-syntax exist
  (syntax-rules ()
    [(exist () g ...) (conj g ...)]
    [(exist (x₀ x ...) g ...)
     (call/exist 'x₀
                 (λ (x₀)
                   (exist (x ...) g ...)))]))
(define-syntax conde
  (syntax-rules ()
    [(conde (g ...) ...) (disj (conj g ...) ...)]))

#|availableo is the freshness constraint|#
(: free-in? (-> Name Term Scope FEnv
                (U FEnv Boolean)))
(define (free-in? n t φ fenv)
  (cond
    [(constant? t) #f]
    [(name? t) (eqv? t n)]
    [(tie? t) (and (not (eqv? (tie-name t) n))
                   (free-in? n (tie-term t) (ext-scp φ (tie-name t)) fenv))]
    [(pair? t)
     (let ([r (free-in? n (car t) φ fenv)])
       (cond
         [(not r) (free-in? n (cdr t) φ fenv)]
         [(eqv? r #t) #t]
         [else (free-in? n (cdr t) φ r)]))]
    [(variable? t) (ext-fenv fenv t n φ)]))
(: availableo (-> Term Term Goal))
(define ((availableo n t) state)
  (match state
    [(State σ χ fenv fenv2)
     (let ([n (walk σ n)]
           [t (walk σ t)])
       (cond
         [(name? n)
          (let ([r (free-in? n t (init-scope) fenv)])
            (cond
              [(not r) (list (State σ χ fenv fenv2))]
              [(eqv? r #t) (list)]
              [else (list (State σ χ r fenv2))]))]
         [(variable? n)
          (let ([ls (or (hash-ref fenv2 n #f) (list))])
            (list (State σ χ fenv (hash-set fenv2 n (cons t ls)))))]
         [else '()]))]))

(define availableᵒ availableo)
