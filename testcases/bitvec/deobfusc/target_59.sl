(set-logic BV)

(synth-fun deobfucated ( (e (BitVec 64))  (c (BitVec 64))  ) (BitVec 64)
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
				e c
			)
		)
	)
)

(constraint (= (deobfucated #x00000000224a4c30 #x0000000013af6f4d) #x0497d1ccccb2cdb4))
(constraint (= (deobfucated #x0000000025fac93e #x000000003703e297) #x05a273d93b43c858))
(constraint (= (deobfucated #x000000001862726f #x000000003135746a) #x02529b505ecd274e))
(constraint (= (deobfucated #x000000001564b660 #x0000000030549733) #x01c9ad8a7c5376ae))
(constraint (= (deobfucated #x000000003372a307 #x0000000014cabf46) #x0a56e04a3f0087e6))
(constraint (= (deobfucated #x0000000020366258 #x0000000021eaf96f) #x040da42360da248a))
(constraint (= (deobfucated #x000000001610e8f3 #x000000002db8366e) #x01e6e9278490ffda))
(constraint (= (deobfucated #x0000000004e2ec07 #x00000000311fc9a3) #x0017e0859cd6568c))
(constraint (= (deobfucated #x0000000031160a9e #x000000001e25a007) #x096971f6216f1978))
(constraint (= (deobfucated #x000000000cb4968c #x0000000019f2c9e9) #x00a16d810ac51220))
(constraint (= (deobfucated #x0000000011ca3af1 #x00000000168bf84d) #x013c7b94eccfe654))
(constraint (= (deobfucated #x000000000fd66ef1 #x000000001ca5a96b) #x00fad49dbfd62d16))
(constraint (= (deobfucated #x0000000020265f89 #x0000000011aaa751) #x04099da2ae864900))
(constraint (= (deobfucated #x000000002f8f28cb #x000000000c2a32d8) #x08d5e1090b15bd5a))
(constraint (= (deobfucated #x00000000028abb1b #x0000000023bf6691) #x0006761a8792ec38))
(constraint (= (deobfucated #x000000002b526d6b #x00000000324f0fd6) #x0754cb4be4bf2da2))
(constraint (= (deobfucated #x000000001179a6c4 #x0000000012eb65f6) #x013161f4f6963b57))
(constraint (= (deobfucated #x000000002d6a1d6e #x000000002eaed159) #x080e7a54b3a138a4))
(constraint (= (deobfucated #x0000000000be77e3 #x000000002756c745) #x00008db605abc4c4))
(constraint (= (deobfucated #x000000002d0f9851 #x000000003a6d7c56) #x07ee7c7f4ba3b4fc))
(check-synth)