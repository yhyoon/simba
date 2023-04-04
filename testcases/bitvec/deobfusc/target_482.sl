(set-logic BV)

(synth-fun deobfucated ( (c (BitVec 64))  (b (BitVec 64))  ) (BitVec 64)
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
				c b
			)
		)
	)
)

(constraint (= (deobfucated #x00000000155acbc2 #x000000001aea913f) #xffffffffe5156ec0))
(constraint (= (deobfucated #x0000000028d6338f #x0000000031857e1a) #xffffffffce7a81e5))
(constraint (= (deobfucated #x0000000035ec0f47 #x000000001f265e03) #xffffffffe0d9a1fc))
(constraint (= (deobfucated #x00000000211afe1c #x000000002170e1ee) #xffffffffde8f1e11))
(constraint (= (deobfucated #x00000000037a028e #x000000002eae61f8) #xffffffffd1519e07))
(constraint (= (deobfucated #x00000000266e7204 #x0000000014a10b3f) #xffffffffeb5ef4c0))
(constraint (= (deobfucated #x00000000016a596e #x000000001e2e4afe) #xffffffffe1d1b501))
(constraint (= (deobfucated #x000000001e3bf0f3 #x000000000afb8f75) #xfffffffff504708a))
(constraint (= (deobfucated #x0000000011f5486d #x00000000200c17e4) #xffffffffdff3e81b))
(constraint (= (deobfucated #x000000002bc41f59 #x000000002cc02a5f) #xffffffffd33fd5a0))
(constraint (= (deobfucated #x00000000057ac2d3 #x0000000037c25f58) #xffffffffc83da0a7))
(constraint (= (deobfucated #x0000000038112b04 #x0000000017248969) #xffffffffe8db7696))
(constraint (= (deobfucated #x00000000324aaa24 #x00000000013adc74) #xfffffffffec5238b))
(constraint (= (deobfucated #x000000001f1673c8 #x0000000003150f0c) #xfffffffffceaf0f3))
(constraint (= (deobfucated #x0000000010bca58d #x0000000007e73942) #xfffffffff818c6bd))
(constraint (= (deobfucated #x0000000036e25a33 #x0000000038251877) #xffffffffc7dae788))
(constraint (= (deobfucated #x0000000025fb56c9 #x000000000890b089) #xfffffffff76f4f76))
(constraint (= (deobfucated #x000000003583950c #x000000000558a798) #xfffffffffaa75867))
(constraint (= (deobfucated #x00000000128ecee1 #x0000000018556094) #xffffffffe7aa9f6b))
(constraint (= (deobfucated #x000000001ff36b0c #x00000000163c4f13) #xffffffffe9c3b0ec))
(check-synth)