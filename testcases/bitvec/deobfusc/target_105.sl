(set-logic BV)

(synth-fun deobfucated ( (c (BitVec 64))  (b (BitVec 64))  ) (BitVec 64)
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
				c b
			)
		)
	)
)

(constraint (= (deobfucated #x0000000006c96f6f #x00000000382836ba) #xfffffffff37fa122))
(constraint (= (deobfucated #x00000000345cbf11 #x000000002d291c5e) #xffffffffd7c6c1fe))
(constraint (= (deobfucated #x0000000017bd7169 #x000000000e2d27ce) #xfffffffff0c79d3e))
(constraint (= (deobfucated #x0000000039d33fc4 #x00000000266e2b01) #xffffffffcc59c080))
(constraint (= (deobfucated #x0000000026f94626 #x00000000012ae770) #xfffffffffa0d7bbc))
(constraint (= (deobfucated #x0000000000fc0599 #x000000003b4e3ae5) #xfffffffffe07f4d0))
(constraint (= (deobfucated #x00000000120552ff #x000000003a8270ec) #xffffffffdffddf02))
(constraint (= (deobfucated #x000000001898d56f #x0000000007d69614) #xffffffffeeef7da2))
(constraint (= (deobfucated #x000000000a778d0e #x0000000016e4675a) #xffffffffeb18f5e4))
(constraint (= (deobfucated #x000000002b0b2718 #x0000000013a4962f) #xffffffffedf9f9d0))
(constraint (= (deobfucated #x0000000017995dd5 #x0000000033f7fa16) #xffffffffd8cd447e))
(constraint (= (deobfucated #x000000003af3d845 #x0000000019ee776f) #xffffffffce184ff6))
(constraint (= (deobfucated #x0000000003531007 #x00000000091edd06) #xfffffffffdf9fffa))
(constraint (= (deobfucated #x0000000022725d91 #x00000000312762bc) #xffffffffff9bc4e0))
(constraint (= (deobfucated #x000000002b3a83c0 #x000000001575884d) #xffffffffe98afc80))
(constraint (= (deobfucated #x000000002b2840e6 #x0000000014962e63) #xffffffffe9efff3c))
(constraint (= (deobfucated #x0000000030b94679 #x000000003b54dd68) #xffffffffde8f7390))
(constraint (= (deobfucated #x0000000039012a44 #x0000000001ba1180) #xffffffffcffdef80))
(constraint (= (deobfucated #x000000001228ba23 #x00000000070a1386) #xfffffffffbffcffa))
(constraint (= (deobfucated #x00000000257d96ac #x000000002a0b4587) #xfffffffff584faf8))
(check-synth)