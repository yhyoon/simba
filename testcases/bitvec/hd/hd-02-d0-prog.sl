; Hacker's delight 02, minimal grammar
; Test if unsigned int is of form 2^n - 1

(set-logic BV)

(define-fun hd02 ((x (BitVec 64))) (BitVec 64) (bvand x (bvadd x #x0000000000000001)))

(synth-fun f ((x (BitVec 64))) (BitVec 64)
    ((Start (BitVec 64) ((bvand Start Start)
                         (bvadd Start Start)
                         x
                         #x0000000000000001))))

(declare-var x (BitVec 64))
(constraint (= (hd02 x) (f x)))
(check-synth)

