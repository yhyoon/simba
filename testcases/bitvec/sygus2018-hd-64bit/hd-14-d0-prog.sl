; Hacker's delight 14, minimal grammar
; floor of average of two integers

(set-logic BV)

(define-fun hd14 ((x (BitVec 64)) (y (BitVec 64))) (BitVec 64) (bvadd (bvand x y) (bvlshr (bvxor x y) #x0000000000000001)))

(synth-fun f ((x (BitVec 64)) (y (BitVec 64))) (BitVec 64)
    ((Start (BitVec 64) ((bvlshr Start Start)
						 (bvxor Start Start)
						 (bvadd Start Start)
						 (bvand Start Start)
						 x
						 y
						 #x0000000000000001))))

(declare-var x (BitVec 64))
(declare-var y (BitVec 64))
(constraint (= (hd14 x y) (f x y)))
(check-synth)

