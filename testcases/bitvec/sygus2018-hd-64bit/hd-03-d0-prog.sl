; Hacker's delight 03, minimal grammar
; Isolate the right most one bit

(set-logic BV)

(define-fun hd03 ((x (BitVec 64))) (BitVec 64) (bvand x (bvneg x)))

(synth-fun f ((x (BitVec 64))) (BitVec 64)
    ((Start (BitVec 64) ((bvneg Start)
                         (bvand Start Start)
                         x))))

(declare-var x (BitVec 64))
(constraint (= (hd03 x) (f x)))
(check-synth)

