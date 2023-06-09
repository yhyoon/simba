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
(constraint (= (f #x544b5bbdc571c6b2) #x000002a25addee2b))
(constraint (= (f #xb0e3e76e26dec17d) #x41878c98093900f0))
(constraint (= (f #xaa57bd1e9404189e) #x00000552bde8f4a0))
(constraint (= (f #xee8945eee40843e9) #x000007744a2f7720))
(constraint (= (f #x7765687d88e2b740) #x000003bb2b43ec47))
(constraint (= (f #xb8a35d2394b12601) #x000005c51ae91ca5))
(constraint (= (f #xbde490e51eee6803) #x7380018039988004))
(constraint (= (f #x944b84dc0d85e3aa) #x0006013012038600))
(constraint (= (f #x67e425422e8a5b77) #x0000033f212a1174))
(constraint (= (f #x4426a656eeeb0ae3) #x0008080999840184))
(check-synth)
