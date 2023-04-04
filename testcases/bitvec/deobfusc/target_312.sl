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

(constraint (= (deobfucated #x000000001eaeb62d #x000000001a5c7184) #x00000000120c2000))
(constraint (= (deobfucated #x000000000c3c54bc #x000000001cc318f6) #x000000000c0010a0))
(constraint (= (deobfucated #x000000002869c5ef #x000000001e702b59) #x000000000860004a))
(constraint (= (deobfucated #x00000000069abd63 #x000000000d9d9632) #x0000000000189020))
(constraint (= (deobfucated #x000000000b7c012f #x000000002a067f69) #x000000000804002a))
(constraint (= (deobfucated #x00000000019f3c13 #x0000000020464562) #x0000000000060400))
(constraint (= (deobfucated #x00000000106f622f #x00000000304f9e7d) #x0000000010440006))
(constraint (= (deobfucated #x000000001d33c189 #x0000000020ab37fe) #x0000000000000108))
(constraint (= (deobfucated #x000000002fc70f39 #x0000000006528568) #x0000000002420400))
(constraint (= (deobfucated #x00000000136809cc #x0000000001ed2185) #x0000000000680080))
(constraint (= (deobfucated #x00000000044bbf6e #x0000000015cb6be7) #x00000000040b2060))
(constraint (= (deobfucated #x0000000037cc3895 #x000000001d82aac0) #x0000000014002880))
(constraint (= (deobfucated #x0000000034537c38 #x00000000338a2be5) #x0000000020002800))
(constraint (= (deobfucated #x0000000037bf4a4e #x0000000034e0bf3a) #x0000000030200208))
(constraint (= (deobfucated #x000000002efc11e2 #x000000002af1d900) #x0000000020300000))
(constraint (= (deobfucated #x000000003b365c8c #x000000000dec0f76) #x0000000008000c00))
(constraint (= (deobfucated #x000000002076b630 #x000000002f7ae040) #x0000000000420000))
(constraint (= (deobfucated #x0000000023b534c9 #x0000000035d58431) #x0000000000010000))
(constraint (= (deobfucated #x000000001aa997aa #x00000000271594ff) #x0000000002011480))
(constraint (= (deobfucated #x00000000268f329b #x00000000388f0616) #x0000000020080200))
(check-synth)