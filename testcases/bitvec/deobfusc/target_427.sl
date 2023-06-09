(set-logic BV)

(synth-fun deobfucated ( (e (BitVec 64))  (c (BitVec 64))  (a (BitVec 64))  ) (BitVec 64)
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
				e c a
			)
		)
	)
)

(constraint (= (deobfucated #x000000002b52c3b4 #x0000000010b0517b #x00000000248fecf4) #xffffffffdc9faba4))
(constraint (= (deobfucated #x000000000937fe29 #x0000000005542c9a #x00000000009f284d) #x0000000000bf23c5))
(constraint (= (deobfucated #x00000000391ab103 #x0000000037641d2c #x0000000012957212) #x00000000029bdef2))
(constraint (= (deobfucated #x0000000029909a79 #x000000000b3b7fdc #x0000000014758ed3) #xfffffffff5bca94b))
(constraint (= (deobfucated #x00000000087c8233 #x0000000034331a3d #x000000001a0b3e0f) #x0000000005ffe3f2))
(constraint (= (deobfucated #x000000000ca8a8f4 #x0000000017bed961 #x000000002689ccc0) #xfffffffff33144a0))
(constraint (= (deobfucated #x000000001d2dbe89 #x0000000027e2dded #x000000000a44d1c9) #x000000001f5e9040))
(constraint (= (deobfucated #x0000000034ba5623 #x0000000003983574 #x000000000bf24d30) #xfffffffffce7d950))
(constraint (= (deobfucated #x000000002acd1195 #x00000000178a5214 #x00000000223ccd72) #xffffffffe4fbcde2))
(constraint (= (deobfucated #x000000003722dc14 #x0000000018b9a923 #x000000000838c726) #x000000001818dffe))
(constraint (= (deobfucated #x0000000020f515dc #x000000002f5953b8 #x000000001fe6c355) #xfffffffff0f6d0ef))
(constraint (= (deobfucated #x0000000015e8bec4 #x0000000020f418df #x0000000025aa8957) #xffffffffff877f1b))
(constraint (= (deobfucated #x000000002666ef56 #x000000003983a16a #x0000000031c65cf0) #x00000000167cbbd2))
(constraint (= (deobfucated #x000000001e04f5ad #x000000002770629d #x000000000d0656b5) #x000000001afe3d60))
(constraint (= (deobfucated #x0000000001803a84 #x000000000680e4fa #x0000000018af1f25) #xfffffffff97f3ba3))
(constraint (= (deobfucated #x00000000078effc2 #x0000000015d0c0ed #x0000000023bbde38) #xffffffffdf2ffeb8))
(constraint (= (deobfucated #x0000000007b93470 #x00000000157f10ff #x000000001f54c160) #xffffffffef0ccfd0))
(constraint (= (deobfucated #x000000000d8e3892 #x00000000110077a2 #x0000000029c9d074) #xffffffffefff80de))
(constraint (= (deobfucated #x00000000073a20a4 #x0000000016125c02 #x000000001a8f3d05) #xffffffffe57d3ffb))
(constraint (= (deobfucated #x000000000a42fffc #x0000000027c2d74d #x000000003b7e8f5f) #xffffffffdd7c7ffb))
(check-synth)