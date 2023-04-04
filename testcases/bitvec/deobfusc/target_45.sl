(set-logic BV)

(synth-fun deobfucated ( (e (BitVec 64))  (a (BitVec 64))  (c (BitVec 64))  ) (BitVec 64)
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
				e a c
			)
		)
	)
)

(constraint (= (deobfucated #x000000000e8f9f7a #x000000002c9180c3 #x000000002d7446c9) #x00173eedcf475f90))
(constraint (= (deobfucated #x00000000362d6229 #x0000000001e5ba77 #x0000000020bcd818) #x003cc91c8c204dae))
(constraint (= (deobfucated #x000000001f001d3d #x000000002dfac76e #x00000000150a137d) #x044f864cddcb1a5d))
(constraint (= (deobfucated #x0000000025c8b212 #x000000002b54af8e #x0000000018a0d1d3) #x05b6729e25a0893f))
(constraint (= (deobfucated #x000000002a38e584 #x000000001692c754 #x0000000019bbea1b) #x00e545fbf30d6669))
(constraint (= (deobfucated #x0000000000f9c64e #x0000000027b22d0a #x000000001b3b4e51) #x001548a18efefbad))
(constraint (= (deobfucated #x000000003286f521 #x0000000034005e90 #x0000000004961f00) #x09db5720c4155190))
(constraint (= (deobfucated #x000000000501a235 #x000000000af0f261 #x000000001c014834) #xffd42a582376ada2))
(constraint (= (deobfucated #x00000000384597d4 #x000000001fecff96 #x00000000178a652e) #x0107f537ca06f588))
(constraint (= (deobfucated #x000000000b7acd46 #x00000000397300f2 #x00000000207fed63) #x020704a18e46e793))
(constraint (= (deobfucated #x00000000116c1abc #x000000001a0ab2fd #x000000002db3f9a5) #xfe41376a4c286710))
(constraint (= (deobfucated #x000000002c20b19e #x000000000f013014 #x00000000034f0599) #x00b4112845287377))
(constraint (= (deobfucated #x0000000038f89b17 #x0000000004ef0a51 #x00000000371b2fab) #x00f1720e1dfde418))
(constraint (= (deobfucated #x0000000026153bee #x000000002158bed1 #x0000000032c38532) #x0044f02f008cd1e1))
(constraint (= (deobfucated #x000000002bfdeb2e #x000000002c19a2e5 #x00000000361ddd8d) #x01b9c33912af7160))
(constraint (= (deobfucated #x0000000036413bdb #x00000000261e0f90 #x000000000ee42807) #x04cd4ec19859870f))
(constraint (= (deobfucated #x00000000246b6479 #x00000000392fef4e #x000000000e22ffe4) #x080cc05f3a2853aa))
(constraint (= (deobfucated #x0000000004771a49 #x00000000017dfe74 #x000000001dfb0b29) #xfff9fef9f001d8c9))
(constraint (= (deobfucated #x000000001a04a985 #x000000000fbdb948 #x00000000311a237f) #xfe6673daacee48a3))
(constraint (= (deobfucated #x000000001615bc4b #x0000000015a4733b #x0000000007005e25) #x0185ea653d8ac964))
(check-synth)