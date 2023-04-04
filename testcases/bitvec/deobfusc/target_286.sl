(set-logic BV)

(synth-fun deobfucated ( (b (BitVec 64))  (d (BitVec 64))  ) (BitVec 64)
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
				b d
			)
		)
	)
)

(constraint (= (deobfucated #x000000000aff338e #x00000000252ddcea) #x0000000010008850))
(constraint (= (deobfucated #x0000000017e71944 #x0000000034f4d160) #x000000000808a018))
(constraint (= (deobfucated #x000000002b76ccb8 #x0000000027fea3d8) #xffffffffd4811300))
(constraint (= (deobfucated #x000000001224ea84 #x000000002b00892c) #x0000000008db1428))
(constraint (= (deobfucated #x000000000be2a5fd #x00000000210a543a) #x0000000014050a00))
(constraint (= (deobfucated #x0000000027b585b5 #x000000000eb56ef0) #xffffffffc04a680a))
(constraint (= (deobfucated #x0000000036194253 #x00000000049115ff) #xffffffffc86691ac))
(constraint (= (deobfucated #x000000001918542d #x000000003560b66e) #x0000000004402240))
(constraint (= (deobfucated #x000000002dab9c08 #x000000002ad1092e) #xffffffffd0046126))
(constraint (= (deobfucated #x000000000e58bd7f #x00000000255a14a6) #x0000000011014200))
(constraint (= (deobfucated #x0000000018c0b3bb #x00000000024cc00e) #xffffffffe10c0c40))
(constraint (= (deobfucated #x00000000066e4b2f #x000000000381466c) #xfffffffff910b010))
(constraint (= (deobfucated #x000000002a30cf7b #x00000000369a6aaf) #x0000000004491004))
(constraint (= (deobfucated #x0000000009474bb6 #x000000002d470157) #x0000000022b8b401))
(constraint (= (deobfucated #x000000002f9e75c9 #x000000000f3b245e) #xffffffffd0008a14))
(constraint (= (deobfucated #x00000000241e6816 #x000000001f5862c7) #xffffffffdb2192a1))
(constraint (= (deobfucated #x000000001995e8cb #x000000000720fc3c) #xffffffffe40a1330))
(constraint (= (deobfucated #x00000000009269f2 #x00000000297f64cf) #x00000000286c920d))
(constraint (= (deobfucated #x000000000de82c2d #x000000002defb674) #x0000000020078242))
(constraint (= (deobfucated #x000000000bb65691 #x000000002080e38e) #x000000001448886c))
(check-synth)