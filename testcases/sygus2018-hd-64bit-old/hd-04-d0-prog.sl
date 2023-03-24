(set-logic BV)

(define-fun hd04 ((x (BitVec 64))) (BitVec 64)
    (bvxor x (bvsub x #x0000000000000001)))
(synth-fun f ((x (BitVec 64))) (BitVec 64)
    ((Start (BitVec 64) ((bvsub Start Start) (bvxor Start Start) #x0000000000000001 x))))

(declare-var x (BitVec 64))
(constraint (= (hd04 x) (f x)))

(check-synth)

