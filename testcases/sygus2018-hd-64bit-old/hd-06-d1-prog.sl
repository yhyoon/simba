(set-logic BV)

(define-fun hd06 ((x (BitVec 64))) (BitVec 64)
    (bvor x (bvadd x #x0000000000000001)))
(synth-fun f ((x (BitVec 64))) (BitVec 64)
    ((Start (BitVec 64) ((bvadd Start Start) (bvsub Start Start) (bvxor Start Start) (bvand Start Start) (bvneg Start) (bvor Start Start) #x0000000000000000 #xFFFFFFFFFFFFFFFF #x0000000000000001 x))))

(declare-var x (BitVec 64))
(constraint (= (hd06 x) (f x)))

(check-synth)

