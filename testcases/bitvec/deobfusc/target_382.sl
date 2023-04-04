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

(constraint (= (deobfucated #x0000000014380f95 #x00000000183c39ee) #xffffffffeffc29c4))
(constraint (= (deobfucated #x000000003141b590 #x000000001bef36f2) #xffffffffd96cecd2))
(constraint (= (deobfucated #x0000000010e7e007 #x0000000016a6425e) #xfffffffff59e4256))
(constraint (= (deobfucated #x0000000009973d82 #x000000001ebeed66) #x000000000c96ab62))
(constraint (= (deobfucated #x00000000356c0743 #x0000000035a2c9d6) #xffffffffeb12c152))
(constraint (= (deobfucated #x0000000028bae548 #x0000000005eaf1b2) #xffffffffb4a5e722))
(constraint (= (deobfucated #x0000000010d5c65d #x000000001874404a) #xfffffffff74a37a8))
(constraint (= (deobfucated #x0000000001851ce0 #x0000000015856854) #x00000000137b4754))
(constraint (= (deobfucated #x0000000035399dd4 #x0000000007aa34d1) #xffffffffbd6812a9))
(constraint (= (deobfucated #x000000003aa5e4bc #x0000000034f52d49) #xffffffffefab2409))
(constraint (= (deobfucated #x0000000031a45336 #x0000000030a99c89) #xffffffffee60f841))
(constraint (= (deobfucated #x0000000014bde183 #x0000000000dc0590) #xffffffffd79a038c))
(constraint (= (deobfucated #x00000000311c6c24 #x00000000374f9f57) #xfffffffff52f0f0f))
(constraint (= (deobfucated #x000000003052fd63 #x00000000364517fc) #xfffffffff5a01578))
(constraint (= (deobfucated #x000000000b8acccc #x000000000f5d55dc) #xfffffffffb4844cc))
(constraint (= (deobfucated #x000000002a6ba294 #x0000000027263078) #xffffffffd291eb50))
(constraint (= (deobfucated #x000000002f57d80b #x0000000032d701d0) #xffffffffe22ee1bc))
(constraint (= (deobfucated #x0000000032375616 #x000000001995666b) #xffffffffd54cbe43))
(constraint (= (deobfucated #x000000000a6e7977 #x0000000034c6dddd) #x0000000020365b55))
(constraint (= (deobfucated #x000000002310eb33 #x000000000f5adfae) #xffffffffcb39cb6a))
(check-synth)