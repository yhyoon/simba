; Hacker's delight 14, difficulty 5
; floor of average of two integers

(set-logic BV)

(define-fun hd14 ((x (BitVec 64)) (y (BitVec 64))) (BitVec 64) (bvadd (bvand x y) (bvlshr (bvxor x y) #x0000000000000001)))

(synth-fun f ((x (BitVec 64)) (y (BitVec 64))) (BitVec 64)
    ((Start (BitVec 64) ((bvnot Start)
						 (bvxor Start Start)
						 (bvand Start Start)
						 (bvor Start Start)
						 (bvneg Start)
						 (bvadd Start Start)
						 (bvmul Start Start)
						 (bvudiv Start Start)
						 (bvurem Start Start)
						 (bvlshr Start Start)
						 (bvashr Start Start)
						 (bvshl Start Start)
						 (bvsdiv Start Start)
						 (bvsrem Start Start)
						 (bvsub Start Start)
                         x
						 y
						 #x000000000000003F
						 #x0000000000000001
						 #x0000000000000000
						 #xFFFFFFFFFFFFFFFF))))

(declare-var x (BitVec 64))
(declare-var y (BitVec 64))
(constraint (= (hd14 x y) (f x y)))
(check-synth)

