(set-logic BV)

(synth-fun deobfucated ( (c (BitVec 64))  (d (BitVec 64))  ) (BitVec 64)
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
				c d
			)
		)
	)
)

(constraint (= (deobfucated #x000000001aea3f5e #x000000002bfb6b34) #xffffffffc57dbf7f))
(constraint (= (deobfucated #x000000003b67165e #x000000000f0f8e18) #xf237522dab7fb77f))
(constraint (= (deobfucated #x000000000a2dfac9 #x000000000fb89758) #xffffffffffedfe2f))
(constraint (= (deobfucated #x0000000022f6d6e0 #x0000000022733274) #xfb3980eaf7f4bfff))
(constraint (= (deobfucated #x0000000015d9084d #x000000000c813180) #xfe22aca44ff7ffdf))
(constraint (= (deobfucated #x00000000285c97c9 #x0000000022ce45ce) #xf9a2ef13bfc9543f))
(constraint (= (deobfucated #x000000001784192a #x000000000249b478) #xfdd6ff507f77d5db))
(constraint (= (deobfucated #x0000000000051e73 #x0000000005d3e1a5) #xffffffffffe2dd7f))
(constraint (= (deobfucated #x00000000012cbcc9 #x000000001225d11f) #xfffffffffdb33abf))
(constraint (= (deobfucated #x0000000028f91341 #x000000002c80ed30) #xfffffffffafbcb7f))
(constraint (= (deobfucated #x000000001fc01d0d #x0000000035feb33c) #xffffffffdf3fdfff))
(constraint (= (deobfucated #x0000000022271c47 #x000000003b0a29e4) #xffffffffdf3effcf))
(constraint (= (deobfucated #x000000002395da88 #x000000000774e5c0) #xfb0dae86bb7417bf))
(constraint (= (deobfucated #x00000000278bf6a5 #x0000000009de234d) #xf9e40e53f573f9b7))
(constraint (= (deobfucated #x00000000291648d7 #x0000000017f22791) #xf967daba8ed65fff))
(constraint (= (deobfucated #x00000000280ad1b8 #x0000000018df7dfc) #xf9bc9e0177f62fff))
(constraint (= (deobfucated #x0000000012003943 #x000000002c600e1c) #xffffffffcff13d7f))
(constraint (= (deobfucated #x0000000010729ccd #x0000000017bda569) #xffffffffff69d3df))
(constraint (= (deobfucated #x00000000220aab9d #x00000000324d0512) #xfffffffffdf0e3bf))
(constraint (= (deobfucated #x0000000000d068aa #x00000000083e996d) #xfffffffff0ff7f5b))
(check-synth)