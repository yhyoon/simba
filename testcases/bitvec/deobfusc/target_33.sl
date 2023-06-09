(set-logic BV)

(synth-fun deobfucated ( (a (BitVec 64))  (e (BitVec 64))  (b (BitVec 64))  ) (BitVec 64)
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
				a e b
			)
		)
	)
)

(constraint (= (deobfucated #x0000000028724998 #x0000000003c3b8d8 #x000000000aad26aa) #xfe8281458a8d218a))
(constraint (= (deobfucated #x0000000024292f65 #x0000000011ad4db2 #x000000000ce2a41c) #xfbdc0be9eca28216))
(constraint (= (deobfucated #x0000000026d879dd #x000000000d0cd0c5 #x000000001a0669a7) #xfc80ec7739755e8d))
(constraint (= (deobfucated #x0000000029879ad7 #x0000000031a62cf7 #x000000000c11d6cb) #xf5fcd7930a0896cb))
(constraint (= (deobfucated #x000000000fc8fba0 #x000000001cf2d175 #x00000000045ce48e) #xfe7a6a7a0458e00e))
(constraint (= (deobfucated #x000000001a213741 #x0000000014e4afd4 #x0000000029614667) #xf9b86ab987590647))
(constraint (= (deobfucated #x0000000029b33244 #x000000003af36d51 #x000000000a055aab) #xf8064b42c604c883))
(constraint (= (deobfucated #x000000001e40be72 #x0000000033b97a2e #x0000000000af0c67) #xf9f6728474ac8be5))
(constraint (= (deobfucated #x00000000081b43d4 #x000000001aefd04f #x000000001eae577e) #xffdd7fbcba9e4fee))
(constraint (= (deobfucated #x0000000027ed8be8 #x000000001dd76100 #x00000000078165c5) #xfbe4753f25595cc5))
(constraint (= (deobfucated #x0000000025be1e05 #x000000002d32ff56 #x000000000f236fe8) #xfafa290c7ee36f46))
(constraint (= (deobfucated #x0000000000ddb559 #x000000001931fc86 #x00000000232d4dfa) #xffcdac107eab4de2))
(constraint (= (deobfucated #x000000003a9099dc #x0000000031399fd1 #x00000000072c3002) #xf3a0897602ec0ffe))
(constraint (= (deobfucated #x0000000008168f6e #x00000000083157fe #x0000000034169cd2) #xfe19748752c7fcd2))
(constraint (= (deobfucated #x0000000035da2f07 #x000000001beb552a #x0000000010bb16c4) #xfd9ebd81f0a68e42))
(constraint (= (deobfucated #x00000000008f7e9a #x000000001f3b45ef #x000000002df1bcdc) #xffe387808dedbadc))
(constraint (= (deobfucated #x0000000001e4f44b #x000000000f11f171 #x00000000240e7334) #xffae4f473346652d))
(constraint (= (deobfucated #x00000000188b3ae7 #x0000000037969348 #x000000000201abe7) #xfadcad3f39c1633f))
(constraint (= (deobfucated #x000000001d0ab2e6 #x000000001369489d #x000000002ddacc69) #xf8e30b1c41d8b949))
(constraint (= (deobfucated #x000000002fa28120 #x000000002937b1d6 #x0000000008974026) #xf9be1ac5b1cf3226))
(check-synth)