(set-logic BV)

(synth-fun deobfucated ( (e (BitVec 64))  (c (BitVec 64))  ) (BitVec 64)
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
				e c
			)
		)
	)
)

(constraint (= (deobfucated #x000000002d142b1c #x00000000246508e0) #xffffffffff50dfdc))
(constraint (= (deobfucated #x000000003af5c620 #x000000002f65c9a3) #xfffffffff4f18783))
(constraint (= (deobfucated #x00000000365f3600 #x0000000032a525a6) #xfffffffffc5fefa6))
(constraint (= (deobfucated #x00000000090b93c5 #x00000000299bbd7f) #x0000000020932bba))
(constraint (= (deobfucated #x0000000005031df5 #x000000002e5ddb6c) #x00000000295abdf7))
(constraint (= (deobfucated #x000000000a4f141f #x000000000f3b33cb) #x0000000004ee1fbe))
(constraint (= (deobfucated #x0000000035d4b666 #x000000000e931b76) #xfffffffff9be6554))
(constraint (= (deobfucated #x0000000038bbfb1e #x0000000012ae2caa) #xfffffffff9f3f39c))
(constraint (= (deobfucated #x00000000309b2cfa #x0000000023918813) #xfffffffff2f65bf9))
(constraint (= (deobfucated #x000000001d2f0f07 #x00000000068d1b86) #xfffffffff95e0e7f))
(constraint (= (deobfucated #x000000002143440d #x00000000330fd2ca) #x0000000011ce8ebd))
(constraint (= (deobfucated #x00000000227bece1 #x000000001d32bc37) #xfffffffffaf7cfd6))
(constraint (= (deobfucated #x000000003b9644b4 #x000000003a31ba08) #xffffffffff9f7574))
(constraint (= (deobfucated #x000000002aa2c12d #x0000000022177c2b) #xfffffffff774bafe))
(constraint (= (deobfucated #x000000000bb379c3 #x000000002c1f405c) #x00000000236bf79b))
(constraint (= (deobfucated #x000000002d88c2b6 #x00000000036608a4) #xffffffffddddc5ee))
(constraint (= (deobfucated #x000000001101b659 #x000000000713f493) #xfffffffff6133e3a))
(constraint (= (deobfucated #x0000000029be6cfc #x00000000209f1d92) #xfffffffff7fcf8fe))
(constraint (= (deobfucated #x0000000023168a64 #x00000000082b74e6) #xffffffffe714eac2))
(constraint (= (deobfucated #x00000000208b54a8 #x0000000017a21d18) #xfffffffff716c870))
(check-synth)