(set-logic BV)

(synth-fun deobfucated ( (a (BitVec 64))  (e (BitVec 64))  (d (BitVec 64))  ) (BitVec 64)
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
				a e d
			)
		)
	)
)

(constraint (= (deobfucated #x000000002d8f9529 #x000000001cc0d5ef #x00000000357d9650) #x0000000016375ae0))
(constraint (= (deobfucated #x000000001bd7bd96 #x00000000232d62dd #x000000001970c7d2) #x00000000041001b2))
(constraint (= (deobfucated #x0000000011a16836 #x000000003958a4ef #x000000000b5bc0bf) #x000000000218f41d))
(constraint (= (deobfucated #x00000000009ce57d #x000000001fe17663 #x00000000280bbcb1) #x000000000e5aacb1))
(constraint (= (deobfucated #x00000000086c622f #x00000000340555de #x0000000010d54a3a) #x0000000000dc0128))
(constraint (= (deobfucated #x000000000eb54334 #x00000000040a2823 #x000000000b521f54) #x000000000a42071c))
(constraint (= (deobfucated #x0000000035c7e008 #x000000002fdf16e2 #x00000000330bca9d) #x000000000340407b))
(constraint (= (deobfucated #x000000000f41f39f #x000000001629cb22 #x00000000067bfb5f) #x000000000aca7a02))
(constraint (= (deobfucated #x00000000361d5596 #x0000000012c1e5ea #x000000002aa51358) #x0000000046264014))
(constraint (= (deobfucated #x00000000243a863a #x000000002d67c676 #x00000000033d0cbf) #x00000000051c0a2d))
(constraint (= (deobfucated #x00000000096abab6 #x0000000028fba01c #x0000000009b045e5) #x000000000a828545))
(constraint (= (deobfucated #x000000001fc51b64 #x000000001838beef #x0000000021723e91) #x0000000006321e83))
(constraint (= (deobfucated #x000000000263648b #x0000000036252402 #x0000000004433610) #x0000000020e11214))
(constraint (= (deobfucated #x0000000012391a6c #x0000000001370339 #x0000000034119721) #x00000000105106c1))
(constraint (= (deobfucated #x000000003436de2b #x0000000010a226a3 #x000000001f73caa1) #x000000002c898065))
(constraint (= (deobfucated #x000000003a40f1b5 #x000000000a03e560 #x00000000015eab27) #x0000000017d22b06))
(constraint (= (deobfucated #x000000002020be18 #x0000000017d50fe6 #x0000000036439b49) #x0000000074c591cf))
(constraint (= (deobfucated #x00000000105113fd #x000000000d59ce56 #x000000002c6d60ab) #x0000000025734006))
(constraint (= (deobfucated #x0000000019d5064a #x0000000029d3d2c4 #x000000002fd5b7b3) #x0000000020f4fe83))
(constraint (= (deobfucated #x0000000004a65b9d #x0000000018334e08 #x00000000361d1daa) #x0000000013404902))
(check-synth)