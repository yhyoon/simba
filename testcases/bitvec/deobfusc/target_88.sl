(set-logic BV)

(synth-fun deobfucated ( (c (BitVec 64))  (d (BitVec 64))  (b (BitVec 64))  ) (BitVec 64)
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
				c d b
			)
		)
	)
)

(constraint (= (deobfucated #x0000000039b6dc05 #x00000000119667bb #x000000000820f70e) #x0017641cd96437e0))
(constraint (= (deobfucated #x000000002cf29748 #x000000002ca2098a #x00000000299892ca) #xf946ff2ee52c9226))
(constraint (= (deobfucated #x000000000f3b095f #x0000000006cca372 #x000000003836e6a7) #xfd31c926dc10eb7a))
(constraint (= (deobfucated #x0000000026003b6d #x0000000013f9d914 #x0000000033ccc1b8) #xf9798925ac9c8de4))
(constraint (= (deobfucated #x000000001754b957 #x000000000e3a5a82 #x000000002d5d0914) #xfbbf93f99f32bc36))
(constraint (= (deobfucated #x0000000024b572b1 #x000000002ecf60a5 #x00000000338241af) #xf5b8eb93b5f39f68))
(constraint (= (deobfucated #x0000000000f49972 #x000000001b1904a2 #x0000000001679c36) #x0292282f444316ce))
(constraint (= (deobfucated #x000000003483e5c7 #x0000000009cbde8f #x000000001955121b) #xfe6fa3c45acf2446))
(constraint (= (deobfucated #x000000000654fbce #x0000000030b657a4 #x00000000218a7f8a) #xfc812b06378c03e4))
(constraint (= (deobfucated #x000000003b39b96f #x0000000039ac914c #x000000000ce3a96a) #x072f8b093abd14ec))
(constraint (= (deobfucated #x0000000039c35efe #x0000000002140df1 #x0000000000ca414c) #x00010914892dc1ba))
(constraint (= (deobfucated #x000000003397979d #x000000000d23d88f #x0000000026aeb0c8) #xfcb415d8d9447900))
(constraint (= (deobfucated #x0000000024dc32cb #x000000000ff37c40 #x0000000008398a62) #xfff80cb4a0e16b40))
(constraint (= (deobfucated #x000000001863d787 #x0000000012e34438 #x00000000252bc564) #xfbe898285d0594b8))
(constraint (= (deobfucated #x0000000018f7c43f #x0000000012091c0b #x0000000007902320) #x00347989738f7fc4))
(constraint (= (deobfucated #x000000002aa16eda #x000000002777c479 #x000000001a1f74db) #xfe07aef30a7976a4))
(constraint (= (deobfucated #x000000002678f8a8 #x00000000016ec200 #x000000000062a01f) #x0000f2d7f91fc600))
(constraint (= (deobfucated #x00000000019ddc2b #x00000000114caf2e #x00000000378dcf17) #xf9a92880ccbcbd2e))
(constraint (= (deobfucated #x000000002ab0b145 #x000000002cd77078 #x0000000019123943) #xff124da4de1659e8))
(constraint (= (deobfucated #x000000001263dbcf #x0000000016b40791 #x0000000018ce3ffb) #xfd9d196728b9135c))
(check-synth)