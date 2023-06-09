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

(constraint (= (deobfucated #x0000000025f2683e #x0000000034012f72) #xffffffffcbfed08e))
(constraint (= (deobfucated #x000000000690f547 #x000000001e3b2b72) #xffffffffe1c4d48e))
(constraint (= (deobfucated #x00000000016f52bc #x0000000022ceef2c) #xffffffffdd3110d4))
(constraint (= (deobfucated #x00000000398815eb #x000000002a624032) #xffffffffd59dbfce))
(constraint (= (deobfucated #x00000000171df3b5 #x000000000a0dfe90) #xfffffffff5f20170))
(constraint (= (deobfucated #x000000002e477ddc #x000000001c9557d8) #xffffffffe36aa828))
(constraint (= (deobfucated #x00000000194e8e03 #x000000000ca944a7) #xfffffffff356bb59))
(constraint (= (deobfucated #x0000000034eb7866 #x000000001829c236) #xffffffffe7d63dca))
(constraint (= (deobfucated #x00000000160d5290 #x000000002d72a30b) #xffffffffd28d5cf5))
(constraint (= (deobfucated #x000000001d80c72a #x0000000035d51b30) #xffffffffca2ae4d0))
(constraint (= (deobfucated #x000000002cfbc3ed #x00000000327ad0e3) #xffffffffcd852f1d))
(constraint (= (deobfucated #x000000002b0a7ef8 #x00000000006415f4) #xffffffffff9bea0c))
(constraint (= (deobfucated #x000000001e694dd1 #x000000001cebb649) #xffffffffe31449b7))
(constraint (= (deobfucated #x00000000143f7cf8 #x000000002b24e843) #xffffffffd4db17bd))
(constraint (= (deobfucated #x000000000a76f229 #x0000000013d3d3d6) #xffffffffec2c2c2a))
(constraint (= (deobfucated #x000000002233e85c #x000000001be625a9) #xffffffffe419da57))
(constraint (= (deobfucated #x000000001e3e29ed #x000000001a64b427) #xffffffffe59b4bd9))
(constraint (= (deobfucated #x000000000a5c0137 #x00000000355dffe2) #xffffffffcaa2001e))
(constraint (= (deobfucated #x0000000002b545b1 #x000000001a937608) #xffffffffe56c89f8))
(constraint (= (deobfucated #x00000000113386cf #x00000000234459ed) #xffffffffdcbba613))
(check-synth)