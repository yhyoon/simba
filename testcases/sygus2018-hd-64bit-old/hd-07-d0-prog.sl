(set-logic BV)

(define-fun hd07 ((x (BitVec 64))) (BitVec 64)
    (bvand (bvnot x) (bvadd x #x0000000000000001)))
(synth-fun f ((x (BitVec 64))) (BitVec 64)
    ((Start (BitVec 64) ((bvadd Start Start) (bvnot Start) (bvand Start Start) #x0000000000000001 x))))

(declare-var x (BitVec 64))
(constraint (= (hd07 x) (f x)))

(check-synth)

