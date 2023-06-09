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

(constraint (= (deobfucated #x000000001b6aaeee #x000000001aa32504) #x0000000051f983e0))
(constraint (= (deobfucated #x0000000009c9fafc #x0000000000216171) #x0000000013d5586a))
(constraint (= (deobfucated #x00000000115d5807 #x0000000027c22c7f) #x0000000070ff0105))
(constraint (= (deobfucated #x00000000040bd36a #x00000000377ced66) #x000000007308c03e))
(constraint (= (deobfucated #x0000000028fae4a4 #x0000000028f72d92) #x000000007af1ffec))
(constraint (= (deobfucated #x0000000031d32423 #x0000000030a82c43) #x0000000094767cc9))
(constraint (= (deobfucated #x00000000337f068b #x000000003ad1238c) #x00000000aa4f51a6))
(constraint (= (deobfucated #x00000000308a7f30 #x000000001fc0c6df) #x000000009016460e))
(constraint (= (deobfucated #x000000000d81485b #x000000001a5190fd) #x0000000047a4b257))
(constraint (= (deobfucated #x000000002197efa5 #x0000000038911521) #x0000000093c1046b))
(constraint (= (deobfucated #x000000002ad9e317 #x000000001070fabe) #x000000007644d994))
(constraint (= (deobfucated #x0000000021a80079 #x00000000195143a1) #x0000000074f28813))
(constraint (= (deobfucated #x000000002e6b0181 #x0000000010cfd997) #x000000007e2ab4af))
(constraint (= (deobfucated #x000000000c067643 #x0000000038a55a74) #x0000000081534f2e))
(constraint (= (deobfucated #x0000000027ef459f #x000000000ded90d4) #x0000000065ccac52))
(constraint (= (deobfucated #x000000001843b917 #x000000001a165aef) #x000000004cb21005))
(constraint (= (deobfucated #x000000001983feaf #x0000000012bc29cf) #x000000004800286d))
(constraint (= (deobfucated #x000000002eadc63f #x000000003acbecde) #x00000000a869a21c))
(constraint (= (deobfucated #x0000000009d4774b #x000000001da3afea) #x0000000045702720))
(constraint (= (deobfucated #x00000000197471b8 #x0000000007f87f88) #x00000000416970f8))
(check-synth)