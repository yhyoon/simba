(set-logic BV)

(synth-fun deobfucated ( (e (BitVec 64))  (a (BitVec 64))  ) (BitVec 64)
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
				e a
			)
		)
	)
)

(constraint (= (deobfucated #x0000000009847aed #x000000000f0b4f87) #x008f2eda187e8f15))
(constraint (= (deobfucated #x00000000120d5322 #x000000002a2cb204) #x02f9567b7bd7a3a9))
(constraint (= (deobfucated #x000000002c4e253b #x00000000125e310f) #x032dcbcd73105c4d))
(constraint (= (deobfucated #x000000003889a330 #x0000000001341bb7) #x00440bb77cd0145f))
(constraint (= (deobfucated #x000000001c9ba548 #x000000002b2f2ef6) #x04d36a95f9e06677))
(constraint (= (deobfucated #x000000000d2abac9 #x0000000005d93f03) #x004d021be1f21d91))
(constraint (= (deobfucated #x0000000015eb512c #x0000000030eadacc) #x04303b0c5937763b))
(constraint (= (deobfucated #x000000000318e7e8 #x0000000024afb6a4) #x0071a0d8db736747))
(constraint (= (deobfucated #x00000000010a71dc #x00000000277e3f1f) #x00291abe419a9c77))
(constraint (= (deobfucated #x000000000438ed7e #x000000001691b429) #x005f4ba008404c4f))
(constraint (= (deobfucated #x000000003441a0a8 #x0000000014c2c54a) #x043ce28e4ea81837))
(constraint (= (deobfucated #x00000000040e27f2 #x00000000294d863c) #x00a77ec8260a2f49))
(constraint (= (deobfucated #x0000000024b61641 #x0000000033352cb5) #x0757e68aebb3f1b3))
(constraint (= (deobfucated #x00000000155b2d61 #x0000000011a8ff07) #x0179271fb502f1c5))
(constraint (= (deobfucated #x0000000017f9c91a #x00000000270bd6c5) #x03a8297bcc88b417))
(constraint (= (deobfucated #x000000003aa39552 #x00000000128bdcc9) #x043f89e44ceb202f))
(constraint (= (deobfucated #x000000000f0ea271 #x00000000270e2ce0) #x024c102fc6e92c90))
(constraint (= (deobfucated #x00000000124cf288 #x000000000913482f) #x00a61565da22346f))
(constraint (= (deobfucated #x0000000017a06c90 #x00000000082b8293) #x00c10763d3cf1a1f))
(constraint (= (deobfucated #x00000000266b4edd #x000000002dc6650f) #x06dea306483f812d))
(check-synth)