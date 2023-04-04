(set-logic BV)

(synth-fun deobfucated ( (c (BitVec 64))  (d (BitVec 64))  ) (BitVec 64)
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
				c d
			)
		)
	)
)

(constraint (= (deobfucated #x00000000269841ce #x000000003641671c) #x0000000036d967de))
(constraint (= (deobfucated #x000000001b397b1a #x0000000003c27440) #x000000001bfb7f5a))
(constraint (= (deobfucated #x000000001d971e75 #x000000000f5a488f) #x000000001fdf5eff))
(constraint (= (deobfucated #x000000002dfe948e #x000000000aeefc31) #x000000002ffefcbf))
(constraint (= (deobfucated #x000000001f5f0283 #x000000000639f630) #x000000001f7ff6b3))
(constraint (= (deobfucated #x000000002b0af7cf #x000000002a174378) #x000000002b1ff7ff))
(constraint (= (deobfucated #x000000000e73877f #x0000000033e38ffb) #x000000003ff38fff))
(constraint (= (deobfucated #x000000001013be03 #x0000000025c25221) #x0000000035d3fe23))
(constraint (= (deobfucated #x000000001d778721 #x000000000914d73e) #x000000001d77d73f))
(constraint (= (deobfucated #x000000000f6642d4 #x000000000ad3078a) #x000000000ff747de))
(constraint (= (deobfucated #x0000000015830569 #x000000002ee91a0c) #x000000003feb1f6d))
(constraint (= (deobfucated #x0000000030d53a31 #x000000000980fec6) #x0000000039d5fef7))
(constraint (= (deobfucated #x000000002e67dd74 #x0000000034413608) #x000000003e67ff7c))
(constraint (= (deobfucated #x00000000058626ee #x000000000d53e029) #x000000000dd7e6ef))
(constraint (= (deobfucated #x0000000008cceb14 #x00000000263c7da9) #x000000002efcffbd))
(constraint (= (deobfucated #x0000000032d4d60d #x000000000004ad70) #x0000000032d4ff7d))
(constraint (= (deobfucated #x000000001dd899ba #x0000000016570ddd) #x000000001fdf9dff))
(constraint (= (deobfucated #x000000001a636126 #x000000003703d097) #x000000003f63f1b7))
(constraint (= (deobfucated #x000000000319c79a #x00000000146cf71a) #x00000000177df79a))
(constraint (= (deobfucated #x000000002cbc21d7 #x0000000008ddee35) #x000000002cfdeff7))
(check-synth)