; Hacker's delight 08, difficulty 1
; Form a mask that identifies the trailing zeros

(set-logic BV)

(define-fun hd08 ((x (BitVec 64))) (BitVec 64) (bvand (bvnot x) (bvsub x #x0000000000000001)))

(synth-fun f ((x (BitVec 64))) (BitVec 64)
    ((Start (BitVec 64) ((bvsub Start Start)
						 (bvadd Start Start)
						 (bvnot Start)
						 (bvneg Start)
                         (bvand Start Start)
						 (bvor Start Start)
						 (bvxor Start Start)
						 #x0000000000000000
						 #x0000000000000001
						 #xFFFFFFFFFFFFFFFF
                         x))))

(declare-var x (BitVec 64))
(constraint (= (hd08 x) (f x)))
(check-synth)

