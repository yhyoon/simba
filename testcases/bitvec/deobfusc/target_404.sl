(set-logic BV)

(synth-fun deobfucated ( (b (BitVec 64))  ) (BitVec 64)
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
				b
			)
		)
	)
)

(constraint (= (deobfucated #x0000000037e9d178) #x000000003028d139))
(constraint (= (deobfucated #x000000000782a1b0) #x00000000030020b1))
(constraint (= (deobfucated #x000000001aa90c1c) #x0000000012210c0d))
(constraint (= (deobfucated #x000000000b8d2ceb) #x000000000b002043))
(constraint (= (deobfucated #x0000000034e22b72) #x0000000030400133))
(constraint (= (deobfucated #x00000000197c3fd6) #x0000000008443913))
(constraint (= (deobfucated #x0000000021503345) #x0000000020102345))
(constraint (= (deobfucated #x000000001397662e) #x000000001093462b))
(constraint (= (deobfucated #x00000000132fa039) #x00000000100aa009))
(constraint (= (deobfucated #x000000001f69f83a) #x000000000329901b))
(constraint (= (deobfucated #x00000000153723a9) #x0000000004220229))
(constraint (= (deobfucated #x0000000004a4d467) #x0000000000841407))
(constraint (= (deobfucated #x000000000fb293f6) #x0000000004228393))
(constraint (= (deobfucated #x00000000226e947f) #x000000000028807f))
(constraint (= (deobfucated #x0000000036e283ec) #x000000003640826d))
(constraint (= (deobfucated #x00000000090c3de6) #x0000000001081543))
(constraint (= (deobfucated #x0000000014c1f5f0) #x0000000014c0b4f1))
(constraint (= (deobfucated #x000000002dc766b8) #x00000000248042b9))
(constraint (= (deobfucated #x000000000fbfe6a0) #x000000000d3c02a1))
(constraint (= (deobfucated #x00000000336111bd) #x0000000033011035))
(check-synth)