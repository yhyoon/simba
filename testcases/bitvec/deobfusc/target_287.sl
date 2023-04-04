(set-logic BV)

(synth-fun deobfucated ( (a (BitVec 64))  (b (BitVec 64))  ) (BitVec 64)
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
				a b
			)
		)
	)
)

(constraint (= (deobfucated #x000000000c67b201 #x000000003ac93ca4) #x10590c59ee1db110))
(constraint (= (deobfucated #x0000000026dba401 #x0000000027117629) #x0be46fb2c0c3fa93))
(constraint (= (deobfucated #x00000000079102b6 #x000000001d51c70d) #x0439794b055c14ea))
(constraint (= (deobfucated #x000000001ae97f54 #x000000000516885c) #x00a2d132982ecb1c))
(constraint (= (deobfucated #x000000003402809e #x000000001c2f0ac1) #x08d427b54313c25e))
(constraint (= (deobfucated #x000000001b2826f1 #x000000000120eee5) #x001fec9dd14d928b))
(constraint (= (deobfucated #x00000000383158a1 #x0000000014048dd5) #x05f59111fe9b33fb))
(constraint (= (deobfucated #x0000000005781999 #x0000000035a7e5cb) #x0c6466d1e5a81d87))
(constraint (= (deobfucated #x000000000b681372 #x0000000035993d82) #x0d9c2f2a0d50026a))
(constraint (= (deobfucated #x000000001557309c #x000000002a1ae567) #x0a6f620d64ff6f52))
(constraint (= (deobfucated #x000000000b389987 #x000000000ffbbf12) #x01b2d1d1c330ded0))
(constraint (= (deobfucated #x00000000137d5c15 #x00000000354531c4) #x0f23f1f32fdd12e0))
(constraint (= (deobfucated #x0000000037f98f55 #x00000000013d7434) #x0046f317ec56bfe0))
(constraint (= (deobfucated #x0000000015e6327b #x0000000023a66a38) #x0803a27ac7100f10))
(constraint (= (deobfucated #x0000000009ee7413 #x0000000037fa048f) #x0e69501d390beef1))
(constraint (= (deobfucated #x0000000026607940 #x000000001818a0cb) #x05e15d08ab4e2672))
(constraint (= (deobfucated #x0000000005cc50fb #x0000000038d0dfe0) #x0de5792969d95b40))
(constraint (= (deobfucated #x0000000009c227a9 #x000000000be23e55) #x010130c8ff675f03))
(constraint (= (deobfucated #x00000000299b1e84 #x000000003328e547) #x1289de772951410a))
(constraint (= (deobfucated #x000000002b08a075 #x0000000016b91069) #x05d62e62e1547b67))
(check-synth)