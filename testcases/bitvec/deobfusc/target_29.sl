(set-logic BV)

(synth-fun deobfucated ( (c (BitVec 64))  (a (BitVec 64))  (b (BitVec 64))  ) (BitVec 64)
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
				c a b
			)
		)
	)
)

(constraint (= (deobfucated #x000000001b10e503 #x0000000038ba2091 #x0000000034845590) #x0000000000000000))
(constraint (= (deobfucated #x0000000039c396a5 #x00000000085d4640 #x000000000316b055) #x0000000000000000))
(constraint (= (deobfucated #x0000000012ba40b4 #x0000000011b513fc #x00000000307fae8f) #x0000000000000000))
(constraint (= (deobfucated #x0000000025bc6ef6 #x00000000269e03f8 #x0000000026d5dba0) #x0000000000000000))
(constraint (= (deobfucated #x000000000ed76931 #x000000002d18f38f #x000000003233fa29) #x0000000000000000))
(constraint (= (deobfucated #x0000000020e1eef3 #x000000003055e244 #x000000002d3d6f87) #x0000000000000000))
(constraint (= (deobfucated #x00000000019054b9 #x000000000a207ff1 #x000000001ae704a9) #x0000000000000000))
(constraint (= (deobfucated #x0000000003e29111 #x0000000014943f8e #x000000002b2eff4d) #x0000000000000000))
(constraint (= (deobfucated #x0000000035bb2186 #x000000000646530d #x0000000020c99c94) #x0000000000000000))
(constraint (= (deobfucated #x0000000017cb5d90 #x0000000029a9df24 #x000000001435e741) #x0000000000000000))
(constraint (= (deobfucated #x00000000321bff91 #x000000000de240c6 #x000000000eb668f4) #x0000000000000000))
(constraint (= (deobfucated #x000000000098d478 #x0000000023f74294 #x00000000356e2301) #x0000000000000000))
(constraint (= (deobfucated #x0000000019cd3122 #x00000000174e57b8 #x000000002e26dbab) #x0000000000000000))
(constraint (= (deobfucated #x00000000208e6e01 #x000000001a40efde #x0000000034ff55af) #x0000000000000000))
(constraint (= (deobfucated #x000000000bad4eb8 #x0000000000f27321 #x000000002bd9044e) #x0000000000000000))
(constraint (= (deobfucated #x00000000276e0beb #x0000000024674601 #x0000000003eb837c) #x0000000000000000))
(constraint (= (deobfucated #x0000000020bca218 #x0000000000ee1140 #x000000002f98aed7) #x0000000000000000))
(constraint (= (deobfucated #x0000000033cfb385 #x000000001f826907 #x000000001e40a442) #x0000000000000000))
(constraint (= (deobfucated #x00000000247b23bf #x000000002d6a65e0 #x00000000081ea343) #x0000000000000000))
(constraint (= (deobfucated #x0000000001708d3f #x0000000039045851 #x000000002dd99646) #x0000000000000000))
(check-synth)