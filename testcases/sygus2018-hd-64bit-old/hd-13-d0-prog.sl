(set-logic BV)

(define-fun hd13 ((x (BitVec 64))) (BitVec 64)
    (bvor (bvashr x #x000000000000001F) (bvlshr (bvneg x) #x000000000000001F)))
(synth-fun f ((x (BitVec 64))) (BitVec 64)
    ((Start (BitVec 64) ((bvlshr Start Start) (bvashr Start Start) (bvor Start Start) (bvneg Start) x #x000000000000001F))))

(declare-var x (BitVec 64))
(constraint (= (hd13 x) (f x)))

(check-synth)

