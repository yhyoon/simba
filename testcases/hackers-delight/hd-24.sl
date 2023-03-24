; Round up to the next higher power of 2.

(set-logic BV)

(define-fun hd24 ((x (BitVec 64))) (BitVec 64)
(bvadd (bvor (bvor (bvor (bvor (bvor (bvsub x #x0000000000000001) (bvlshr (bvsub x #x0000000000000001) #x0000000000000001))
(bvlshr (bvor (bvsub x #x0000000000000001) (bvlshr (bvsub x #x0000000000000001) #x0000000000000001)) #x0000000000000002))
(bvlshr (bvor (bvor (bvsub x #x0000000000000001) (bvlshr (bvsub x #x0000000000000001) #x0000000000000001))
(bvlshr (bvor (bvsub x #x0000000000000001) (bvlshr (bvsub x #x0000000000000001) #x0000000000000001)) #x0000000000000002)) #x0000000000000004))
(bvlshr (bvor (bvor (bvor (bvsub x #x0000000000000001) (bvlshr (bvsub x #x0000000000000001) #x0000000000000001))
(bvlshr (bvor (bvsub x #x0000000000000001) (bvlshr (bvsub x #x0000000000000001) #x0000000000000001)) #x0000000000000002))
(bvlshr (bvor (bvor (bvsub x #x0000000000000001) (bvlshr (bvsub x #x0000000000000001) #x0000000000000001))
(bvlshr (bvor (bvsub x #x0000000000000001) (bvlshr (bvsub x #x0000000000000001) #x0000000000000001)) #x0000000000000002)) #x0000000000000004)) #x0000000000000008))
(bvlshr (bvor (bvor (bvor (bvor (bvsub x #x0000000000000001) (bvlshr (bvsub x #x0000000000000001) #x0000000000000001))
(bvlshr (bvor (bvsub x #x0000000000000001) (bvlshr (bvsub x #x0000000000000001) #x0000000000000001)) #x0000000000000002))
(bvlshr (bvor (bvor (bvsub x #x0000000000000001) (bvlshr (bvsub x #x0000000000000001) #x0000000000000001))
(bvlshr (bvor (bvsub x #x0000000000000001) (bvlshr (bvsub x #x0000000000000001) #x0000000000000001)) #x0000000000000002)) #x0000000000000004))
(bvlshr (bvor (bvor (bvor (bvsub x #x0000000000000001) (bvlshr (bvsub x #x0000000000000001) #x0000000000000001))
(bvlshr (bvor (bvsub x #x0000000000000001) (bvlshr (bvsub x #x0000000000000001) #x0000000000000001)) #x0000000000000002))
(bvlshr (bvor (bvor (bvsub x #x0000000000000001) (bvlshr (bvsub x #x0000000000000001) #x0000000000000001))
(bvlshr (bvor (bvsub x #x0000000000000001) (bvlshr (bvsub x #x0000000000000001) #x0000000000000001)) #x0000000000000002)) #x0000000000000004))
#x0000000000000008)) #x0000000000000010)) #x0000000000000001))

(synth-fun f ((x (BitVec 64))) (BitVec 64)
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
						 #x0000000000000000
                         #x0000000000000001
                         #x0000000000000002
                         #x0000000000000004
                         #x0000000000000008
                         #x0000000000000010
                         #xffffffffffffffff
))

                         (StartBool Bool
                         ((= Start Start)
                         ))))

(declare-var x (BitVec 64))
(constraint (= (hd24 x) (f x)))
(check-synth)

