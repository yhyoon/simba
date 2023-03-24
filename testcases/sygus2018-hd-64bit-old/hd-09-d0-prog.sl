(set-logic BV)

(define-fun hd09 ((x (BitVec 64))) (BitVec 64)
    (bvsub (bvxor x (bvashr x #x000000000000001F)) (bvashr x #x000000000000001F)))
(synth-fun f ((x (BitVec 64))) (BitVec 64)
    ((Start (BitVec 64) ((bvsub Start Start) (bvashr Start Start) (bvxor Start Start) #x000000000000001F x))))

(declare-var x (BitVec 64))
(constraint (= (hd09 x) (f x)))

(check-synth)

