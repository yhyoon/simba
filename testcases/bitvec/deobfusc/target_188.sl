(set-logic BV)

(synth-fun deobfucated ( (e (BitVec 64))  (a (BitVec 64))  (b (BitVec 64))  ) (BitVec 64)
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
				e a b
			)
		)
	)
)

(constraint (= (deobfucated #x000000000a90bb20 #x0000000025435ce0 #x00000000007c338d) #xffffffffff83cc73))
(constraint (= (deobfucated #x00000000223d3bc2 #x000000001546098f #x000000000102296d) #xfffffffffefdd693))
(constraint (= (deobfucated #x0000000035a75986 #x0000000010f6eede #x0000000000b19ef6) #xffffffffff4e610a))
(constraint (= (deobfucated #x00000000133272e1 #x0000000032ec367c #x0000000002d951ab) #xfffffffffd26ae55))
(constraint (= (deobfucated #x00000000314c5755 #x0000000026895da9 #x000000000d8a30e7) #xfffffffff275cf19))
(constraint (= (deobfucated #x000000002377fe4e #x00000000032fa2aa #x000000000c3d2fd3) #xfffffffff3c2d02d))
(constraint (= (deobfucated #x0000000027830f46 #x000000002c139342 #x000000000c5cb261) #xfffffffff3a34d9f))
(constraint (= (deobfucated #x00000000018df610 #x00000000351ed931 #x000000001bfba799) #xffffffffe4045867))
(constraint (= (deobfucated #x00000000396e0486 #x000000001336aa16 #x00000000373be8cc) #xffffffffc8c41736))
(constraint (= (deobfucated #x0000000005564cc7 #x000000000182b645 #x000000000c0589c7) #xfffffffff3fa7639))
(constraint (= (deobfucated #x000000001c0c67da #x00000000220fb37c #x0000000001124e7b) #xfffffffffeedb185))
(constraint (= (deobfucated #x000000002f3beddf #x000000001e1b63b9 #x000000002cf8cb53) #xffffffffd30734ad))
(constraint (= (deobfucated #x0000000008e4a7a3 #x0000000030f860e5 #x0000000000714a50) #xffffffffff8eb5b1))
(constraint (= (deobfucated #x000000002a5552c8 #x0000000032cb46e3 #x000000001ce5ca3c) #xffffffffe31a35c4))
(constraint (= (deobfucated #x00000000335267d5 #x000000000f582094 #x000000001f088763) #xffffffffe0f7789d))
(constraint (= (deobfucated #x0000000000d64cc2 #x0000000025dee1a2 #x000000000432875d) #xfffffffffbcd78a3))
(constraint (= (deobfucated #x000000002c18cf83 #x0000000036d35921 #x000000000de6200b) #xfffffffff219dff5))
(constraint (= (deobfucated #x0000000016922e93 #x000000001a672934 #x000000002722ddb8) #xffffffffd8dd2248))
(constraint (= (deobfucated #x000000001edaee94 #x0000000033d22e84 #x000000003042369a) #xffffffffcfbdc966))
(constraint (= (deobfucated #x000000001fddc21b #x000000000f38bd49 #x000000000d7ad3b0) #xfffffffff2852c59))
(check-synth)