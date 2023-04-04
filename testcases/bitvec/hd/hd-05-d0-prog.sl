; Hacker's delight 05, minimal grammar
; Right propagate the rightmost one bit

(set-logic BV)

(define-fun hd05 ((x (BitVec 64))) (BitVec 64) (bvor x (bvsub x #x0000000000000001)))

(synth-fun f ((x (BitVec 64))) (BitVec 64)
    ((Start (BitVec 64) ((bvsub Start Start)
                         (bvor Start Start)
						 #x0000000000000001
                         x))))

(declare-var x (BitVec 64))
(constraint (= (hd05 x) (f x)))
(check-synth)

