(set-logic BV)

(synth-fun deobfucated ( (e (BitVec 64))  (d (BitVec 64))  ) (BitVec 64)
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
				e d
			)
		)
	)
)

(constraint (= (deobfucated #x000000002b944544 #x000000001e221284) #xffffffffe2f1ed7c))
(constraint (= (deobfucated #x00000000177e0714 #x000000001e7ad755) #xffffffffe8e729bb))
(constraint (= (deobfucated #x000000001a1828f1 #x00000000018b958b) #x00000000008c8b56))
(constraint (= (deobfucated #x0000000004aa1041 #x000000003a3d71be) #xffffffffc9ca9e43))
(constraint (= (deobfucated #x0000000034c05a08 #x00000000002ce86f) #x0000000020531791))
(constraint (= (deobfucated #x000000003480d02a #x000000000ab1ad5f) #x00000000154e92c1))
(constraint (= (deobfucated #x0000000000b167c8 #x0000000002388bbe) #xfffffffffe677882))
(constraint (= (deobfucated #x00000000354bc5d2 #x000000001d174e75) #x00000000183171cb))
(constraint (= (deobfucated #x0000000014b2291c #x00000000069e7a78) #x0000000009e1ae98))
(constraint (= (deobfucated #x00000000345c3fc5 #x00000000083f1a52) #x000000001c18f32f))
(constraint (= (deobfucated #x000000000915edb0 #x000000001b447bd3) #xffffffffedc0cd2d))
(constraint (= (deobfucated #x0000000036cc2880 #x000000003acf8591) #xffffffffd7787a6f))
(constraint (= (deobfucated #x0000000023b41c7d #x0000000033f669ad) #xffffffffccb9aa5c))
(constraint (= (deobfucated #x0000000034706325 #x0000000000e10a26) #x00000000235f18db))
(constraint (= (deobfucated #x000000000e6325f2 #x000000001f4d8bb9) #xffffffffe6f57507))
(constraint (= (deobfucated #x000000002ba59593 #x0000000033c5d887) #xffffffffd4da377a))
(constraint (= (deobfucated #x0000000006ca4645 #x0000000007be468f) #xfffffffffc49ff72))
(constraint (= (deobfucated #x00000000362a6bc7 #x0000000034cc284a) #x00000000015e3837))
(constraint (= (deobfucated #x0000000034b37de3 #x000000000b3caf0b) #xfffffffff4d4c636))
(constraint (= (deobfucated #x0000000002ee6dd7 #x0000000036d1f037) #xffffffffcc12585a))
(check-synth)