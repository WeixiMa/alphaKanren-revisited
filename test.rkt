#lang racket

(require "amk.rkt")

(defrel (rename e new a out)
  (conde
   [(== `(var ,a) e)
    (== `(var ,new) out)]
   [(exist (y)
           (== `(var ,y) e)
           (== `(var ,y) out)
           (availableᵒ a y))]
   [(exist (rator rand ratorᵒ randᵒ)
           (== `(app ,rator ,rand) e)
           (== `(app ,ratorᵒ ,randᵒ) out)
           (rename rator new a ratorᵒ)
           (rename rand new a randᵒ))]
   [(exist (body r bodyᵒ)
           (fresh (c c^)
             (== (tie c body) e)
             (rename body c^ c r)
             (rename r new a bodyᵒ)
             (== (tie c^ bodyᵒ) out)))]))

(defrel (subst e new a out)
  (conde
   [(== `(var ,a) e)
    (== new out)]
   [(exist (y)
           (== `(var ,y) e)
           (== `(var ,y) out)
           (availableᵒ a y))]
   [(exist (rator rand ratorᵒ randᵒ)
           (== `(app ,rator ,rand) e)
           (== `(app ,ratorᵒ ,randᵒ) out)
           (rename rator new a ratorᵒ)
           (rename rand new a randᵒ))]
   [(exist (body r bodyᵒ)
           (fresh (c c^)
             (== (tie c body) e)
             (rename body c^ c r)
             (subst r new a bodyᵒ)
             (== (tie c^ bodyᵒ) out)))]))

(run* q
      (fresh (a b)
        (rename (tie b `(app (var ,b) (var ,a))) b a q)))

(run* q
      (fresh (a b)
        (subst
         (tie a `(app (var ,a) (var ,b)))
         `(var ,b)
         a
         q)))
#;
(run 1 q
  (fresh (a b c)
    (== `(lam ,(tie a `(app (var ,a) (var ,b))))
        `(lam ,(tie c q)))))
