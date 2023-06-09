(set-logic BV)

(synth-fun deobfucated ( (a (BitVec 64))  (b (BitVec 64))  ) (BitVec 64)
	(
		(Start (BitVec 64)
			(
				(bvnot Start)
				(bvxor Start Start)
				(bvand Start Start)
				(bvor Start Start)
				(bvneg Start)
				(bvadd Start Start)
				(bvmul Start Start)
				(bvsub Start Start)
				a b
			)
		)
	)
)

(constraint (= (deobfucated #x00000000248f53f2 #x0000000010e7c4a2) #xffffffffdf78be1e))
(constraint (= (deobfucated #x000000000bf0592b #x000000000637ab4c) #xfffffffffd5ffee4))
(constraint (= (deobfucated #x000000001bc72927 #x00000000386809cf) #xfffffffff6fff6db))
(constraint (= (deobfucated #x000000001f765817 #x000000001ad4e9e5) #xffffffffef89e7f9))
(constraint (= (deobfucated #x00000000116b9533 #x0000000003284256) #xfffffffffe977afe))
(constraint (= (deobfucated #x000000001fd7d3d2 #x000000002c1808f3) #xfffffffffbbfed31))
(constraint (= (deobfucated #x000000001e17836c #x0000000005e266b4) #xffffffffeff8fff4))
(constraint (= (deobfucated #x00000000224391cf #x0000000032d65d6a) #xfffffffffffceff2))
(constraint (= (deobfucated #x0000000017f6a736 #x0000000026d860cd) #xffffffffeb7fdddb))
(constraint (= (deobfucated #x0000000020b80b54 #x0000000013b96a08) #xffffffffdfd7f5f8))
(constraint (= (deobfucated #x000000002a818409 #x000000001185de2c) #xffffffffdf7eda24))
(constraint (= (deobfucated #x0000000023b00201 #x000000002d965e57) #xffffffffff7ffdff))
(constraint (= (deobfucated #x0000000027172d26 #x000000002446281d) #xffffffffdbedd7fb))
(constraint (= (deobfucated #x0000000008d5135a #x0000000000bc4a59) #xffffffffffebecf7))
(constraint (= (deobfucated #x0000000030460de4 #x0000000019ed87f3) #xffffffffffbffa53))
(constraint (= (deobfucated #x0000000008cbee3c #x000000002c2a1841) #xffffffffffb5b841))
(constraint (= (deobfucated #x00000000210022c6 #x000000001526ad14) #xffffffffdefffdfc))
(constraint (= (deobfucated #x00000000143da724 #x000000001cc54989) #xffffffffebf27c89))
(constraint (= (deobfucated #x000000002590ba46 #x000000000f669db9) #xffffffffdbef67ff))
(constraint (= (deobfucated #x000000002696a5fd #x000000002b5ecc14) #xfffffffffdebdbc4))
(check-synth)