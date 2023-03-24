(set-logic BV)
(synth-fun f ( (x (BitVec 64)) ) (BitVec 64)
((Start (BitVec 64)
((bvnot Start)
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
#x0000000000000003
#x0000000000000004
#x0000000000000005
#x0000000000000006
#x0000000000000007
#x0000000000000008
#x0000000000000009
#x0000000000000009
#x0000000000000009
#x000000000000000A
#x000000000000000B
#x000000000000000C
#x000000000000000D
#x000000000000000E
#x000000000000000F
#x0000000000000010
(ite StartBool Start Start)
))
(StartBool Bool
((= Start Start)
(not StartBool)
(and StartBool StartBool)
(or StartBool StartBool)
))))
(constraint (= (f #x539baa47cce652eb) #xa20a5367007f9e97))
(constraint (= (f #x1830a28d0397ede3) #x78f32cc111f7a56f))
(constraint (= (f #xce446c93184237e3) #x07561edf794b176f))
(constraint (= (f #x4c5db01617c2543a) #x4c5db01617c2543a))
(constraint (= (f #x5b91db88014c9bea) #x5b91db88014c9bea))
(constraint (= (f #xdeb38e93e565aadb) #x5981c8e37afc5647))
(constraint (= (f #x9ecddee93607e0e9) #x1a055a8e0e27648d))
(constraint (= (f #x33b5e3eae3c68e7c) #x33b5e3eae3c68e7c))
(constraint (= (f #x09ee594e3446334e) #x09ee594e3446334e))
(constraint (= (f #x5d3800240bda631e) #x5d3800240bda631e))
(check-synth)
(define-fun f_1 ((x (BitVec 64))) (BitVec 64) (ite (= (bvor #x0000000000000001 x) x) (bvmul #x0000000000000005 x) x))
