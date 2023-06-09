(set-logic BV)

(synth-fun deobfucated ( (a (BitVec 64))  (e (BitVec 64))  (d (BitVec 64))  ) (BitVec 64)
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
				a e d
			)
		)
	)
)

(constraint (= (deobfucated #x0000000007d1a116 #x0000000011ec7cec #x000000003671ba7a) #x8bea085f2360709d))
(constraint (= (deobfucated #x00000000148334b9 #x00000000331d7dbc #x000000001bb178b2) #x5a00f05e9f607caa))
(constraint (= (deobfucated #x000000002f59944b #x0000000013600ea7 #x0000000006b22566) #x38d272116b75b213))
(constraint (= (deobfucated #x0000000015486ef7 #x00000000068f12bc #x0000000037df4e4f) #x82efc7039910893c))
(constraint (= (deobfucated #x0000000021f67909 #x0000000029b9f2bc #x000000002d32328d) #xfcbdfd0652a36f0a))
(constraint (= (deobfucated #x00000000216d0e3b #x00000000230e9d41 #x0000000010e162e4) #xf0a2aae8e16f1167))
(constraint (= (deobfucated #x000000000e944bee #x0000000026e9e844 #x0000000024b66d22) #x151a3fc7b94381ed))
(constraint (= (deobfucated #x00000000280c4233 #x0000000025ca23a4 #x00000000056566f2) #x510be5d20ccf7b48))
(constraint (= (deobfucated #x0000000007d5ed12 #x000000003533c5a0 #x000000002951cabc) #x81708f4fe0dabd4d))
(constraint (= (deobfucated #x0000000010970512 #x0000000031db3d2e #x0000000038cdadff) #xd3b03b0942b5017b))
(constraint (= (deobfucated #x00000000206083a0 #x0000000001c9663e #x000000000e699c0e) #x8b6fe2c8c9b50859))
(constraint (= (deobfucated #x000000001287c324 #x000000001e615846 #x0000000023260b9e) #x05ac5565ff4900cd))
(constraint (= (deobfucated #x00000000181a06f3 #x0000000037c3f31b #x00000000306e6200) #xf0e7ca614bbb17f1))
(constraint (= (deobfucated #x000000000bb9029b #x000000002072fb7d #x00000000261c99e0) #x0c35520dfd480ac7))
(constraint (= (deobfucated #x00000000373fb666 #x00000000055fcc79 #x0000000031429cf6) #xea8877056956de36))
(constraint (= (deobfucated #x000000001fed7901 #x0000000002f5d722 #x0000000000437c5e) #x68ba00df62f89054))
(constraint (= (deobfucated #x0000000002e0d67b #x0000000017b2f3ee #x00000000179878e0) #x65d4812ce5df3116))
(constraint (= (deobfucated #x0000000002e7e705 #x00000000020c9db6 #x000000001b9ee2eb) #x92c5ae288c0b9e10))
(constraint (= (deobfucated #x000000000c94620d #x000000000374185f #x0000000008d2274a) #x2f5d115979f8bd5d))
(constraint (= (deobfucated #x00000000356500e4 #x000000000ce57e48 #x000000002d05faa9) #x17a1ad624a473f13))
(check-synth)