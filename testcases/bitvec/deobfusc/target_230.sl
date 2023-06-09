(set-logic BV)

(synth-fun deobfucated ( (a (BitVec 64))  (b (BitVec 64))  (d (BitVec 64))  ) (BitVec 64)
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
				a b d
			)
		)
	)
)

(constraint (= (deobfucated #x0000000033112b29 #x0000000033d1d7ef #x000000001252d761) #x0630b0293dd12d6c))
(constraint (= (deobfucated #x0000000037d9b995 #x000000001657d3fb #x00000000083c8660) #x08982202bd7f1c94))
(constraint (= (deobfucated #x000000000bf2776c #x0000000019e45fd4 #x00000000301026a5) #x090467addce407e1))
(constraint (= (deobfucated #x000000002b2b9801 #x000000001d6196f8 #x000000002a11415e) #x0965454aeb932c02))
(constraint (= (deobfucated #x00000000283e57f6 #x00000000224c4352 #x000000000a3b3d44) #x00155e0cc3eee910))
(constraint (= (deobfucated #x0000000019b492c6 #x0000000012df86d1 #x0000000016a1e06e) #x02b82a5741ba2944))
(constraint (= (deobfucated #x000000003a6b0db3 #x000000000b8ce959 #x000000000f794ac2) #x0409d9f16fe3dcb2))
(constraint (= (deobfucated #x0000000009f9bfef #x0000000023ff3d70 #x0000000034d88772) #x0721de285385d8aa))
(constraint (= (deobfucated #x000000002e8f1b25 #x000000000a7601f5 #x000000001ef4056e) #x0705c7ebf0924afe))
(constraint (= (deobfucated #x000000001b89c282 #x0000000009786f84 #x000000001f3fc808) #x01b65a46eb011ae0))
(constraint (= (deobfucated #x000000002753f12f #x00000000184168de #x000000001d8ce524) #x041098ad43dc4cf0))
(constraint (= (deobfucated #x0000000001e3df74 #x0000000001547e9e #x000000001cfd516e) #x036cd189c6966668))
(constraint (= (deobfucated #x00000000287fc9b5 #x000000001b552bff #x000000001193be00) #x052b478ffb4ff16c))
(constraint (= (deobfucated #x0000000018b2b688 #x0000000028d90ca3 #x000000002c09526e) #x05102c0934ff3570))
(constraint (= (deobfucated #x00000000051b7072 #x000000001a6c385a #x0000000016e9c5db) #x0176a2fa4938a0f9))
(constraint (= (deobfucated #x000000001a2c1898 #x0000000036234890 #x000000001c91a175) #x12644902004d09a1))
(constraint (= (deobfucated #x0000000023df7458 #x0000000000f8a011 #x0000000035e807f7) #x04d0aa623abcd932))
(constraint (= (deobfucated #x000000001ca7a4c0 #x000000002a05af03 #x000000003af75c54) #x02d7505767107416))
(constraint (= (deobfucated #x0000000039bac852 #x0000000000bee1e3 #x000000001e86e8fd) #x04c76e91dbf30c92))
(constraint (= (deobfucated #x0000000020cab694 #x0000000030124815 #x0000000025ab308d) #x0e92c1988c4e1e88))
(check-synth)