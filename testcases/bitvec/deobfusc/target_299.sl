(set-logic BV)

(synth-fun deobfucated ( (e (BitVec 64))  (a (BitVec 64))  (b (BitVec 64))  ) (BitVec 64)
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
				e a b
			)
		)
	)
)

(constraint (= (deobfucated #x00000000315ea808 #x00000000366bdf99 #x00000000290a7547) #x54b9b02e4b88c18f))
(constraint (= (deobfucated #x0000000022394526 #x000000000dc48e9b #x000000000d5335a8) #x2ce86ea5bf1a0b71))
(constraint (= (deobfucated #x000000003886ee4d #x0000000016959616 #x000000000d35278f) #x6e7b33e8c7e3f1a4))
(constraint (= (deobfucated #x000000000c2966f4 #x00000000165f11b3 #x000000003366bb24) #xda1f2b1dc6fc6385))
(constraint (= (deobfucated #x000000002fa19101 #x0000000017189a42 #x000000001f05634c) #x8541cbfdd5af5af0))
(constraint (= (deobfucated #x000000003645e14c #x0000000029be5d3f #x0000000006f8544e) #x64d3f5a756ee603b))
(constraint (= (deobfucated #x0000000001376796 #x0000000026f5a394 #x000000003acbb992) #x936999329e15c3e0))
(constraint (= (deobfucated #x0000000006632d84 #x0000000017c8c81f #x0000000005a608f3) #x1724928bec4a2c9d))
(constraint (= (deobfucated #x000000001a4dd385 #x0000000001f7210d #x00000000189bf979) #xdc9d1f9de9c9f2c7))
(constraint (= (deobfucated #x0000000014f726f4 #x00000000129df39f #x0000000037d3f816) #x4785e53fb3fd903b))
(constraint (= (deobfucated #x0000000014523323 #x000000001a32d7e9 #x000000003adaa6bf) #xa4d09560a24348e1))
(constraint (= (deobfucated #x00000000298a77a1 #x00000000124961be #x0000000004d02c64) #x40907da84ef67a70))
(constraint (= (deobfucated #x00000000208a4522 #x0000000029fe314c #x000000001880a8ee) #x6fda217b2e13ac20))
(constraint (= (deobfucated #x0000000024d8032c #x00000000240432a6 #x0000000021ca672a) #x8306e49262ce6718))
(constraint (= (deobfucated #x00000000106fe79d #x00000000246d0033 #x000000001dc5f42d) #xed40bcf025fcd2cb))
(constraint (= (deobfucated #x000000001fa7838d #x000000001b48bd38 #x000000003b2d88e4) #xce3a520c86f97780))
(constraint (= (deobfucated #x0000000016994dc5 #x00000000114ac5e0 #x0000000011f4c034) #x4d6c502a43ca7800))
(constraint (= (deobfucated #x000000002edff283 #x00000000170c1deb #x000000002c1a31e6) #x8fed421c2c7de867))
(constraint (= (deobfucated #x000000000632b55f #x000000003b292638 #x000000001fa5f7b9) #x19145c7c3940e7c0))
(constraint (= (deobfucated #x000000001c9f429d #x000000002a9ea1d8 #x0000000028ab4263) #x4844a887580219c0))
(check-synth)