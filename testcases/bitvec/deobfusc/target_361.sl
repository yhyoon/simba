(set-logic BV)

(synth-fun deobfucated ( (c (BitVec 64))  (b (BitVec 64))  ) (BitVec 64)
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
				c b
			)
		)
	)
)

(constraint (= (deobfucated #x00000000059bbb46 #x00000000032fae22) #x0000000002ae3c04))
(constraint (= (deobfucated #x0000000037403d27 #x0000000033c16d2e) #x0000000021c03404))
(constraint (= (deobfucated #x00000000162d8c0e #x000000001d53df22) #x0000000006084004))
(constraint (= (deobfucated #x000000002c425f76 #x00000000341f047a) #x0000000024000a24))
(constraint (= (deobfucated #x000000002d46524a #x000000002f321185) #x000000002f264309))
(constraint (= (deobfucated #x000000002a1159df #x0000000006067bd3) #x000000002c006bc9))
(constraint (= (deobfucated #x000000000194a86d #x000000000ba2f8b9) #x000000000182f0b1))
(constraint (= (deobfucated #x0000000020fc16db #x000000001d58731c) #x000000002d002310))
(constraint (= (deobfucated #x00000000097c1ed9 #x0000000025ac1fc4) #x0000000009500e10))
(constraint (= (deobfucated #x000000001f1f0c22 #x00000000368ce93b) #x0000000011046119))
(constraint (= (deobfucated #x00000000072c6643 #x0000000015aaed97) #x00000000070cef11))
(constraint (= (deobfucated #x0000000004250bd9 #x000000001b913c46) #x0000000019342304))
(constraint (= (deobfucated #x000000000e807268 #x0000000033b83503) #x0000000031083609))
(constraint (= (deobfucated #x000000000fdb94da #x00000000010fe695) #x000000000f061299))
(constraint (= (deobfucated #x000000000351372c #x00000000266b1c4e) #x0000000004512744))
(constraint (= (deobfucated #x000000002c3a4f11 #x0000000039ec5257) #x0000000028e25911))
(constraint (= (deobfucated #x000000001ebf1a39 #x0000000026fa0af6) #x0000000030f00064))
(constraint (= (deobfucated #x00000000336af20e #x0000000009e440be) #x000000003ace8004))
(constraint (= (deobfucated #x000000000fd4f52b #x000000003a5556ce) #x000000001a1105c4))
(constraint (= (deobfucated #x000000002f042344 #x000000001e05da39) #x000000001c052031))
(check-synth)