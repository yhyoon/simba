; Hacker's delight 09, difficulty 1
; Absolute value function

(set-logic BV)

(define-fun hd09 ((x (BitVec 64))) (BitVec 64) (bvsub (bvxor x (bvashr x #x000000000000003F)) (bvashr x #x000000000000003F)))

(synth-fun f ((x (BitVec 64))) (BitVec 64)
    ((Start (BitVec 64) ((bvsub Start Start)
						 (bvadd Start Start)
						 (bvashr Start Start)
						 (bvlshr Start Start)
                         (bvxor Start Start)
						 (bvand Start Start)
						 (bvor Start Start)
						 #x0000000000000001
						 #x0000000000000000
						 #x000000000000003F
						 #xFFFFFFFFFFFFFFFF
                         x))))

(declare-var x (BitVec 64))
(constraint (= (hd09 x) (f x)))
(check-synth)

