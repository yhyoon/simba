; Hacker's delight 09, minimal grammar
; Absolute value function

(set-logic BV)

(define-fun hd09 ((x (BitVec 64))) (BitVec 64) (bvsub (bvxor x (bvashr x #x000000000000003F)) (bvashr x #x000000000000003F)))

(synth-fun f ((x (BitVec 64))) (BitVec 64)
    ((Start (BitVec 64) ((bvsub Start Start)
						 (bvashr Start Start)
                         (bvxor Start Start)
						 #x000000000000003F
                         x))))

(declare-var x (BitVec 64))
(constraint (= (hd09 x) (f x)))
(check-synth)

