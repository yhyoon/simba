(set-logic BV)

(synth-fun deobfucated ( (e (BitVec 64))  (b (BitVec 64))  ) (BitVec 64)
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
				e b
			)
		)
	)
)

(constraint (= (deobfucated #x000000000b7a0cb6 #x00000000358e2bfa) #x000000008b766cb2))
(constraint (= (deobfucated #x000000000dfd13d9 #x0000000015d2191b) #x0000000049fb4b8f))
(constraint (= (deobfucated #x0000000038cc5abb #x000000001521f2c1) #x00000000b4a850b1))
(constraint (= (deobfucated #x000000002480fafe #x0000000023d521d2) #x00000000742cf2fa))
(constraint (= (deobfucated #x0000000026166676 #x000000000031b164) #x0000000072865562))
(constraint (= (deobfucated #x0000000013ebcfe1 #x000000001715bb0b) #x0000000043ebcfb7))
(constraint (= (deobfucated #x000000000ff19230 #x000000002afb85d3) #x000000006fe8c216))
(constraint (= (deobfucated #x00000000172b46aa #x00000000346cc92b) #x00000000860ae600))
(constraint (= (deobfucated #x0000000016a744a4 #x0000000002d3e83a) #x0000000044971e20))
(constraint (= (deobfucated #x0000000019ed5846 #x0000000013084c68) #x0000000051c81122))
(constraint (= (deobfucated #x0000000031643d20 #x0000000008f6e85a) #x00000000a5523814))
(constraint (= (deobfucated #x0000000022387947 #x000000001d6dc136) #x00000000a1346c35))
(constraint (= (deobfucated #x0000000036c9e2cd #x00000000165bdefa) #x00000000a481e0cb))
(constraint (= (deobfucated #x00000000225c4fe1 #x000000001f3b38dd) #x00000000a15b4fdb))
(constraint (= (deobfucated #x0000000024d40ca4 #x000000000d5cc247) #x00000000808daa72))
(constraint (= (deobfucated #x0000000016807a4e #x00000000366091c9) #x00000000844271ec))
(constraint (= (deobfucated #x000000000fb2a977 #x0000000039ecebbd) #x000000008fb08175))
(constraint (= (deobfucated #x0000000024a516b2 #x000000000e313501) #x00000000820f8618))
(constraint (= (deobfucated #x0000000023e439da #x000000001933c81d) #x000000009bd42d98))
(constraint (= (deobfucated #x000000003743e63c #x000000003b00433e) #x00000000b5cbb4b8))
(check-synth)