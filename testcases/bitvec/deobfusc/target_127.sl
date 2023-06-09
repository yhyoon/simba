(set-logic BV)

(synth-fun deobfucated ( (a (BitVec 64))  (d (BitVec 64))  ) (BitVec 64)
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
				a d
			)
		)
	)
)

(constraint (= (deobfucated #x00000000232273ed #x00000000147ee528) #x09a4e0ab9ac7f3fa))
(constraint (= (deobfucated #x0000000024ac3a95 #x00000000144cc114) #x0a81c8b15f33b566))
(constraint (= (deobfucated #x00000000305de24f #x000000001627b8cb) #x1246ae97baee8889))
(constraint (= (deobfucated #x000000001cef3729 #x0000000022c5b69f) #x068a673204247f2b))
(constraint (= (deobfucated #x000000001912c2b2 #x0000000022573388) #x04e956cd72268508))
(constraint (= (deobfucated #x0000000002af5b25 #x0000000012e305ba) #x000e6b14a0b1a792))
(constraint (= (deobfucated #x0000000025572906 #x000000000e270837) #x0ae49f114d4ad04e))
(constraint (= (deobfucated #x00000000010d3c40 #x000000002a15d08e) #x0002364f59593000))
(constraint (= (deobfucated #x0000000024fac141 #x000000000d7b5593) #x0aaef7f09dd46403))
(constraint (= (deobfucated #x00000000225bb616 #x000000001b307830) #x0938fa71985ea3d8))
(constraint (= (deobfucated #x000000000120a371 #x00000000144033a4) #x00028ae04d320ce2))
(constraint (= (deobfucated #x0000000031fcbf07 #x0000000022edf381) #x13857552844a5763))
(constraint (= (deobfucated #x00000000330d48ea #x00000000038be18f) #x145c977b7219ab42))
(constraint (= (deobfucated #x000000002a7dc060 #x000000001ea8ad4b) #x0e1b01c9d688c840))
(constraint (= (deobfucated #x000000001f44a64f #x00000000373b6e0b) #x07a3655fc7053ec9))
(constraint (= (deobfucated #x0000000039549cb7 #x000000002288f3ff) #x19ad93814c0f8515))
(constraint (= (deobfucated #x000000001f579b54 #x000000000010128d) #x07acab3292bdb524))
(constraint (= (deobfucated #x000000002ddf5a0d #x0000000006db7693) #x1070910d2c7d1b53))
(constraint (= (deobfucated #x000000003935c85e #x0000000013ed7d79) #x1991fd0cce5b4d50))
(constraint (= (deobfucated #x000000002be42d54 #x000000000b0e4ae1) #x0f0ce535f0494f60))
(check-synth)