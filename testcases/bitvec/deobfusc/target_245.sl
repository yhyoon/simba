(set-logic BV)

(synth-fun deobfucated ( (d (BitVec 64))  (b (BitVec 64))  ) (BitVec 64)
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
				d b
			)
		)
	)
)

(constraint (= (deobfucated #x000000001fb8625f #x000000001d4046f9) #x0071f6a832608e5d))
(constraint (= (deobfucated #x00000000037cdf7b #x0000000014cd0f66) #x0044a68c7f54d47d))
(constraint (= (deobfucated #x00000000088622e1 #x0000000022e104d6) #x0161e6d979402281))
(constraint (= (deobfucated #x000000002031d473 #x000000002a0c7f5e) #x0145c1fab074243d))
(constraint (= (deobfucated #x0000000016a1aa81 #x0000000021088ea7) #x00ebb7c251cbeb8f))
(constraint (= (deobfucated #x0000000010c30c59 #x000000000d779af1) #x01f94a56a2cd382b))
(constraint (= (deobfucated #x000000000e0769ba #x0000000019a56594) #x01a3066c329a0130))
(constraint (= (deobfucated #x00000000251a0b67 #x000000000bee2ce9) #x04da2ac4663024e5))
(constraint (= (deobfucated #x00000000011568a1 #x00000000307f1608) #x0035a1cf30245041))
(constraint (= (deobfucated #x000000000a3277dd #x000000000f2a105b) #x00fd5aa4392d2eab))
(constraint (= (deobfucated #x0000000001589169 #x000000002d2e73ef) #x003d1fd2e9297d07))
(constraint (= (deobfucated #x00000000221ca795 #x0000000016b7a98e) #x078d70c2b10a37e1))
(constraint (= (deobfucated #x00000000041488d1 #x000000002f5487df) #x00d1bbe9c486278f))
(constraint (= (deobfucated #x000000000d933598 #x0000000016b3b79f) #x018c665e2d79f0b7))
(constraint (= (deobfucated #x00000000016596cb #x00000000369d7157) #x004dbac4bc092fad))
(constraint (= (deobfucated #x0000000013df01d3 #x000000002587c2a6) #x03631870f267025d))
(constraint (= (deobfucated #x000000001330b570 #x000000001384091f) #x0006c770d91d728f))
(constraint (= (deobfucated #x000000000fc6140c #x000000001272a4e1) #x01da325af9d3cbfd))
(constraint (= (deobfucated #x000000000e9485f6 #x000000000ee71950) #x000ddc1b45084354))
(constraint (= (deobfucated #x00000000164d81d1 #x000000003addde74) #x04d18a743d733ba1))
(check-synth)