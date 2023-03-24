; Hacker's delight 17, minimal grammar
; turn off the rightmost string of contiguous ones

(set-logic BV)

(define-fun hd17 ((x (BitVec 64))) (BitVec 64) (bvand (bvadd (bvor x (bvsub x #x0000000000000001)) #x0000000000000001) x))

(synth-fun f ((x (BitVec 64))) (BitVec 64)
    ((Start (BitVec 64) ((bvand Start Start)
						 (bvadd Start Start)
						 (bvsub Start Start)
						 (bvor Start Start)
						 x
						 #x0000000000000001))))

(declare-var x (BitVec 64))
(constraint (= (hd17 x) (f x)))
(check-synth)

