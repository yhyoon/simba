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

(constraint (= (deobfucated #x00000000181ae6ad #x000000000b087218) #x02450e13f5d1f5a7))
(constraint (= (deobfucated #x000000001069242a #x000000002cb1f38a) #x010d4fb3fb6f821a))
(constraint (= (deobfucated #x00000000367ede04 #x0000000024fc8c03) #x0b99c488b479c00b))
(constraint (= (deobfucated #x0000000031b7bfb0 #x000000000fc0f48b) #x09a7db44a9798e2b))
(constraint (= (deobfucated #x000000000efe67b5 #x000000001f5f5de5) #x00e0d029c291b474))
(constraint (= (deobfucated #x00000000004928d0 #x0000000025fede8c) #x000014e8728e35ec))
(constraint (= (deobfucated #x0000000039b58d7e #x00000000398e29cf) #x0d0259c3448318d7))
(constraint (= (deobfucated #x000000000eda82a3 #x000000003032b61d) #x00dca0cca6c3a4a0))
(constraint (= (deobfucated #x000000002f780570 #x000000003ac2e8d9) #x08cd4a4414f06ef9))
(constraint (= (deobfucated #x0000000028fec274 #x000000003aac78b5) #x06909a4a9a92f85d))
(constraint (= (deobfucated #x0000000014982197 #x00000000130ab7ba) #x01a81fa76992bb9d))
(constraint (= (deobfucated #x0000000015d47485 #x0000000027e9a4a6) #x01dc8b6eff9188b5))
(constraint (= (deobfucated #x000000002a93f229 #x00000000159fa850) #x0714e0f5349f4e8f))
(constraint (= (deobfucated #x000000000c739818 #x00000000269366bd) #x009b0a744d98b8cd))
(constraint (= (deobfucated #x00000000363097e7 #x0000000023fbbe99) #x0b78894e7c5ce13c))
(constraint (= (deobfucated #x000000002d883040 #x0000000001826d92) #x08192969738a1d12))
(constraint (= (deobfucated #x000000001fc90788 #x0000000002164bb8) #x03f24daf864cf4e8))
(constraint (= (deobfucated #x00000000239d754f #x000000000f907642) #x04f46eec7afcda05))
(constraint (= (deobfucated #x000000002aaff407 #x00000000012abc1c) #x071e350181fa2c3f))
(constraint (= (deobfucated #x000000000b4f8411 #x0000000004822140) #x007fee0c2a82a23f))
(check-synth)