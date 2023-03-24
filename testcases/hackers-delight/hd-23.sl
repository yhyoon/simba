; Counting number of set bits.

(set-logic BV)

(define-fun hd23 ((x (BitVec 64))) (BitVec 64)
(bvand (bvadd (bvadd (bvand (bvadd (bvlshr (bvadd (bvand (bvsub x (bvand (bvlshr x #x0000000000000001)
#x0000000055555555)) #x0000000033333333) (bvand (bvlshr (bvsub x (bvand (bvlshr x #x0000000000000001) #x0000000055555555))
#x0000000000000002) #x0000000033333333)) #x0000000000000004) (bvadd (bvand (bvsub x (bvand (bvlshr x #x0000000000000001)
#x0000000055555555)) #x0000000033333333) (bvand (bvlshr (bvsub x (bvand (bvlshr x #x0000000000000001) #x0000000055555555))
#x0000000000000002) #x0000000033333333))) #x0000000f0f0f0f0f)
(bvlshr (bvand (bvadd (bvlshr (bvadd (bvand (bvsub x (bvand (bvlshr x #x0000000000000001) #x0000000055555555)) #x0000000033333333)
(bvand (bvlshr (bvsub x (bvand (bvlshr x #x0000000000000001) #x0000000055555555)) #x0000000000000002) #x0000000033333333)) #x0000000000000004) (bvadd (bvand (bvsub x (bvand (bvlshr x #x0000000000000001) #x0000000055555555)) #x0000000033333333)
(bvand (bvlshr (bvsub x (bvand (bvlshr x #x0000000000000001) #x0000000055555555)) #x0000000000000002) #x0000000033333333))) #x0000000f0f0f0f0f) #x0000000000000008))
(bvlshr (bvadd (bvand (bvadd (bvlshr (bvadd (bvand (bvsub x (bvand (bvlshr x #x0000000000000001) #x0000000055555555)) #x0000000033333333)
(bvand (bvlshr (bvsub x (bvand (bvlshr x #x0000000000000001) #x0000000055555555)) #x0000000000000002) #x0000000033333333)) #x0000000000000004)
(bvadd (bvand (bvsub x (bvand (bvlshr x #x0000000000000001) #x0000000055555555)) #x0000000033333333)
(bvand (bvlshr (bvsub x (bvand (bvlshr x #x0000000000000001) #x0000000055555555)) #x0000000000000002) #x0000000033333333))) #x0000000f0f0f0f0f)
(bvlshr (bvand (bvadd (bvlshr (bvadd (bvand (bvsub x (bvand (bvlshr x #x0000000000000001) #x0000000055555555)) #x0000000033333333)
(bvand (bvlshr (bvsub x (bvand (bvlshr x #x0000000000000001) #x0000000055555555)) #x0000000000000002) #x0000000033333333)) #x0000000000000004)
(bvadd (bvand (bvsub x (bvand (bvlshr x #x0000000000000001) #x0000000055555555)) #x0000000033333333) (bvand (bvlshr (bvsub x (bvand
(bvlshr x #x0000000000000001) #x0000000055555555)) #x0000000000000002) #x0000000033333333))) #x0000000f0f0f0f0f) #x0000000000000008))
#x0000000000000010)) #x000000000000003f))

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
                         #x0000000000000001
                         #x0000000000000002
                         #x0000000000000004
                         #x0000000000000008
                         #x000000000000003f
                         #x0000000055555555
                         #x0000000f0f0f0f0f
                         #x0000000033333333
                         #x0000000000000010
))
                         (StartBool Bool
                         ((= Start Start)
                         ))))

(declare-var x (BitVec 64))
(constraint (= (hd23 x) (f x)))
(check-synth)

