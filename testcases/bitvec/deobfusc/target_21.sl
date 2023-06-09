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

(constraint (= (deobfucated #x000000001134429d #x0000000005461cd5) #x0127fb840f8f8b39))
(constraint (= (deobfucated #x00000000327600ff #x000000001bc5325d) #x09f24ec8cf47cd5b))
(constraint (= (deobfucated #x0000000030677d4a #x000000003403cae8) #x0926f8d22b4610d4))
(constraint (= (deobfucated #x0000000028558ed2 #x000000003133bc6b) #x065ad93a1e67a6f9))
(constraint (= (deobfucated #x0000000019b1f674 #x0000000016cb3dab) #x02943dd991120f97))
(constraint (= (deobfucated #x000000000b050c69 #x000000003050b203) #x00796f2abde9bd7b))
(constraint (= (deobfucated #x000000001e3b8465 #x000000001ba2571a) #x039200de0adf9d26))
(constraint (= (deobfucated #x000000001c92b274 #x000000002bc52c9e) #x03306b1960035a84))
(constraint (= (deobfucated #x0000000038764d09 #x000000000a414431) #x0c73f85f39b17b69))
(constraint (= (deobfucated #x000000002ddefa5f #x0000000002be875e) #x0838263cc2fe227c))
(constraint (= (deobfucated #x000000000bf79884 #x000000000c956d78) #x008f369318f801fa))
(constraint (= (deobfucated #x00000000319ba349 #x000000002f208faa) #x099cf3216d4828c2))
(constraint (= (deobfucated #x0000000024a4bfb7 #x000000002be82b8d) #x053ebff1a6877f13))
(constraint (= (deobfucated #x000000000db986e2 #x00000000318c0048) #x00bc5e2729f2e6ac))
(constraint (= (deobfucated #x0000000022f8453c #x00000000378e5601) #x04c6e32a346f7549))
(constraint (= (deobfucated #x000000002513fef1 #x00000000059783e6) #x055ec9419f529bf6))
(constraint (= (deobfucated #x0000000025ff75dc #x0000000021ca357d) #x05a3d6fde140564d))
(constraint (= (deobfucated #x00000000205a46d8 #x00000000139e1105) #x0416b18c113f0e11))
(constraint (= (deobfucated #x000000000521accc #x00000000327b9ede) #x001a552dd063091c))
(constraint (= (deobfucated #x000000000b5c6075 #x0000000023a95f03) #x0081119fb1230aef))
(check-synth)