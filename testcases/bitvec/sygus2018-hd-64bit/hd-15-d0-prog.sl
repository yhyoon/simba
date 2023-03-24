; Hacker's delight 15, minimal grammar
; ceil of average of two integers

(set-logic BV)

(define-fun hd15 ((x (BitVec 64)) (y (BitVec 64))) (BitVec 64) (bvsub (bvor x y) (bvlshr (bvxor x y) #x0000000000000001)))

(synth-fun f ((x (BitVec 64)) (y (BitVec 64))) (BitVec 64)
    ((Start (BitVec 64) ((bvlshr Start Start)
						 (bvxor Start Start)
						 (bvsub Start Start)
						 (bvor Start Start)
						 x
						 y
						 #x0000000000000001))))

(declare-var x (BitVec 64))
(declare-var y (BitVec 64))
(constraint (= (hd15 x y) (f x y)))
(check-synth)

