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
(constraint (= (f #x2b05bd2e856b2961) #xfe1ffeff1ffef7c4))
(constraint (= (f #x0bae48b4ebedaa3a) #x230ada1ec3c8feae))
(constraint (= (f #xe37be040e010403e) #xaa73a0c2a030c0ba))
(constraint (= (f #x30317b894e415a15) #x9094729beac40e3f))
(constraint (= (f #xeab36cc765ab9e4d) #xffeffb9fdfff7dbc))
(constraint (= (f #xa058eee8103cc077) #xe10accb830b64165))
(constraint (= (f #x1be4c90a3904457b) #x53ae5b1eab0cd071))
(constraint (= (f #x71d9eb4ee5010700) #xe7f7ffbfde061e02))
(constraint (= (f #x65ec20d363989eed) #xdff8c3efcf737ffc))
(constraint (= (f #xa0856d714ee6608a) #xc31fffe7bfddc33e))
(check-synth)
