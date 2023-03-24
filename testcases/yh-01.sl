(set-logic BV)

(define-fun yh01 ((x (BitVec 64))) (BitVec 64)
    (bvadd (bvmul (bvadd (bvmul x x) #x0000000000000001) (bvsub (bvmul x x) #x0000000000000001)) #x0000000000000001))
(synth-fun f ((x (BitVec 64))) (BitVec 64)
    ((Start (BitVec 64) ((bvnot Start) (bvand Start Start) (bvxor Start Start) (bvor Start Start) (bvneg Start) (bvadd Start Start) (bvmul Start Start) (bvudiv Start Start) (bvurem Start Start) (bvlshr Start Start) (bvashr Start Start) (bvshl Start Start) (bvsdiv Start Start) (bvsrem Start Start) (bvsub Start Start) #x0000000000000001 #x0000000000000000 #x000000000000001F #xFFFFFFFFFFFFFFFF x))))

(declare-var x (BitVec 64))
(constraint (= (yh01 x) (f x)))

(check-synth)

