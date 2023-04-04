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

(constraint (= (deobfucated #x00000000164e36d9 #x00000000156196bd) #x0000000001218026))
(constraint (= (deobfucated #x000000002cbbf4f5 #x0000000019ef54f7) #x0000000011440002))
(constraint (= (deobfucated #x000000000b86cd83 #x00000000036e3618) #x000000000068321f))
(constraint (= (deobfucated #x0000000023116676 #x00000000220bd9dc) #x00000000000a9989))
(constraint (= (deobfucated #x00000000387d4a7f #x0000000026fd82c4) #x00000000068080bb))
(constraint (= (deobfucated #x0000000001bbc5ec #x000000000e2960b5) #x000000000e002011))
(constraint (= (deobfucated #x000000002f39e121 #x0000000015bd0cc8) #x0000000010840ccb))
(constraint (= (deobfucated #x000000002f9be0bf #x000000002e179e41) #x0000000000041e7e))
(constraint (= (deobfucated #x00000000247e7d0b #x000000002530f6e4) #x00000000010082e7))
(constraint (= (deobfucated #x000000001f1838ff #x00000000145bea37) #x000000000043c3c8))
(constraint (= (deobfucated #x00000000179d792a #x00000000042183db) #x00000000002082d1))
(constraint (= (deobfucated #x0000000008e46614 #x0000000015e87ca7) #x00000000150818a3))
(constraint (= (deobfucated #x00000000355ea4ce #x000000001b0d2001) #x000000000a010001))
(constraint (= (deobfucated #x00000000266ba515 #x00000000224dded2) #x0000000000045ac3))
(constraint (= (deobfucated #x00000000079edcfb #x000000001e675e4c) #x0000000018610207))
(constraint (= (deobfucated #x0000000013d5d43e #x000000000c1be2d4) #x000000000c0a22c1))
(constraint (= (deobfucated #x000000001418f9f0 #x000000002a96d2e4) #x000000002a860205))
(constraint (= (deobfucated #x0000000034c4027d #x00000000113b51f7) #x00000000013b5182))
(constraint (= (deobfucated #x0000000011a1a3cd #x000000000b25e970) #x000000000a044833))
(constraint (= (deobfucated #x0000000005e15509 #x0000000037f4457c) #x0000000032140077))
(check-synth)