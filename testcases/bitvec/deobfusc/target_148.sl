(set-logic BV)

(synth-fun deobfucated ( (c (BitVec 64))  (a (BitVec 64))  ) (BitVec 64)
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
				c a
			)
		)
	)
)

(constraint (= (deobfucated #x0000000034933aee #x000000001110479d) #x0000000020e00f3b))
(constraint (= (deobfucated #x0000000004052d49 #x0000000003b86eb2) #x000000000001f801))
(constraint (= (deobfucated #x00000000379290d8 #x000000001ea97af5) #x000000003d00ffef))
(constraint (= (deobfucated #x0000000029f2f81e #x0000000032f3f624) #xffffffffc1ffe00b))
(constraint (= (deobfucated #x000000000d57304d #x000000002b5e35ab) #xfffffffff7fde077))
(constraint (= (deobfucated #x000000001ff89e21 #x0000000034979639) #xffffffffe92fefff))
(constraint (= (deobfucated #x0000000007809283 #x000000002c8317be) #xfffffffff900fffd))
(constraint (= (deobfucated #x000000002268d9d6 #x0000000014b1e2f6) #x00000000004f81ff))
(constraint (= (deobfucated #x00000000342a88e1 #x000000001613cc35) #x00000000380ff07f))
(constraint (= (deobfucated #x00000000134d7669 #x000000000622e290) #x000000001c01c401))
(constraint (= (deobfucated #x0000000030484aca #x0000000001d8fac8) #x000000001ffffff3))
(constraint (= (deobfucated #x000000003907894d #x000000003b311705) #xfffffffffe020e0f))
(constraint (= (deobfucated #x000000001aa55ff0 #x00000000088628ba) #x000000001338117f))
(constraint (= (deobfucated #x000000001f6fd4a0 #x000000000d43a85b) #x000000001b87003f))
(constraint (= (deobfucated #x0000000035e7ffe2 #x0000000012771899) #x0000000020fe3103))
(constraint (= (deobfucated #x0000000001ca3296 #x000000003883ac3d) #x00000000010fc0fb))
(constraint (= (deobfucated #x00000000236c9f9d #x000000001d7075f2) #x0000000003c0ebe1))
(constraint (= (deobfucated #x0000000005bef9a6 #x00000000214c600b) #x000000000618c007))
(constraint (= (deobfucated #x00000000162eddeb #x000000003aef3d68) #xffffffffe7fc7ef1))
(constraint (= (deobfucated #x000000002ef459b0 #x00000000353bc278) #xffffffffc86780ff))
(check-synth)