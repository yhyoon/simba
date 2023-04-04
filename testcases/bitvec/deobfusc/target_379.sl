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

(constraint (= (deobfucated #x0000000019b09502 #x0000000014e45712) #xffffffffefdfbdfe))
(constraint (= (deobfucated #x000000000574dbe8 #x000000001dd984b8) #xffffffffe7bf7f78))
(constraint (= (deobfucated #x000000002cc5bc5b #x000000001a1027b7) #xfffffffff7ffdced))
(constraint (= (deobfucated #x0000000004ceb89e #x000000002ee2b8e5) #xffffffffd5ffffb9))
(constraint (= (deobfucated #x0000000027813d80 #x00000000061d1cce) #xfffffffff9e6e3fe))
(constraint (= (deobfucated #x0000000002a1d088 #x0000000032805cad) #xffffffffdd7ff3df))
(constraint (= (deobfucated #x000000000b0e8444 #x000000000d874d92) #xffffffffffffb6fa))
(constraint (= (deobfucated #x00000000100e434e #x000000001ae40279) #xfffffffff53bfdd5))
(constraint (= (deobfucated #x000000000dfeb606 #x0000000007fd30f8) #xfffffffffe03cf0e))
(constraint (= (deobfucated #x00000000109adb6d #x000000002aca7668) #xfffffffff5f5ed97))
(constraint (= (deobfucated #x000000003b1fb4d6 #x0000000009013a80) #xfffffffff6feff7e))
(constraint (= (deobfucated #x00000000087d5dd8 #x000000002f972472) #xffffffffd8eefbe6))
(constraint (= (deobfucated #x000000003a5b3078 #x0000000021f40331) #xffffffffde6ffdc7))
(constraint (= (deobfucated #x000000001265750c #x000000003a4e6069) #xffffffffddb79fb3))
(constraint (= (deobfucated #x0000000024820d3e #x0000000025857b84) #xfffffffffefe95fa))
(constraint (= (deobfucated #x0000000004e70385 #x000000003243339d) #xffffffffdfbfcfeb))
(constraint (= (deobfucated #x000000000bc9e640 #x000000002509ed35) #xfffffffffefffbbf))
(constraint (= (deobfucated #x00000000213c8542 #x0000000021eb8cfb) #xffffffffff54fb47))
(constraint (= (deobfucated #x00000000246eb7bb #x00000000330714bd) #xfffffffffdffebff))
(constraint (= (deobfucated #x000000000063d6d6 #x000000002352610a) #xffffffffddbdfffe))
(check-synth)