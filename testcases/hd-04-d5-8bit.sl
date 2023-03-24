; Hacker's delight 04, difficulty 5
; Form a bit mask that identifies the rightmost one bit and trailing zeros

(set-logic BV)

(define-fun hd04 ((x (BitVec 8))) (BitVec 8) (bvxor x (bvsub x #x01)))

(synth-fun f ((x (BitVec 8))) (BitVec 8)
    ((Start (BitVec 8) ((bvnot Start)
						 (bvand Start Start)
						 (bvxor Start Start)
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
                         #x00
						 #x01
						 #xFF
                         x))))

(declare-var x (BitVec 8))
(constraint (= (hd04 x) (f x)))
(check-synth)

