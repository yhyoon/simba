; Hacker's delight 13, difficulty 1
; sign function

(set-logic BV)

(define-fun hd13 ((x (BitVec 64))) (BitVec 64) (bvor (bvashr x #x000000000000003F) (bvlshr (bvneg x) #x000000000000003F)))

(synth-fun f ((x (BitVec 64))) (BitVec 64)
    ((Start (BitVec 64) ((bvlshr Start Start)
						 (bvashr Start Start)
						 (bvand Start Start)
						 (bvxor Start Start)
						 (bvor Start Start)
						 (bvneg Start)
						 (bvnot Start)
						 (bvadd Start Start)
						 (bvsub Start Start)
						 x
						 #x000000000000003F
						 #x0000000000000001
						 #x0000000000000000
						 #xFFFFFFFFFFFFFFFF))))

(declare-var x (BitVec 64))
(constraint (= (hd13 x) (f x)))
(check-synth)

