; Hacker's delight 20, minimal grammar
; next higher unsigned number with same number of 1 bits

(set-logic BV)

(define-fun hd20 ((x (BitVec 64))) (BitVec 64) 
  (bvor (bvadd x (bvand (bvneg x) x)) (bvudiv (bvlshr (bvxor x (bvand (bvneg x) x)) #x0000000000000002) (bvand (bvneg x) x))))

(synth-fun f ((x (BitVec 64))) (BitVec 64)
		   ((Start (BitVec 64) ((bvand Start Start)
								(bvxor Start Start)
								(bvor Start Start)
								(bvadd Start Start)
								(bvlshr Start Start)
								(bvneg Start)
								(bvudiv Start Start)
								x
								#x0000000000000002))))



(declare-var x (BitVec 64))

(constraint (= (hd20 x) (f x)))
(check-synth)

