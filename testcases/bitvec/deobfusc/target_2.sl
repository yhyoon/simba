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

(constraint (= (deobfucated #x0000000033780743 #x00000000364753c6) #xffffffffc9b8ac3a))
(constraint (= (deobfucated #x000000003115a5cf #x000000000d799dc7) #xfffffffff2866239))
(constraint (= (deobfucated #x000000002c654c48 #x00000000290915a4) #xffffffffd6f6ea5c))
(constraint (= (deobfucated #x000000002a319f7b #x0000000003a15a69) #xfffffffffc5ea597))
(constraint (= (deobfucated #x0000000023259ff2 #x0000000023078c67) #xffffffffdcf87399))
(constraint (= (deobfucated #x0000000007919e0d #x000000000f4e3d74) #xfffffffff0b1c28c))
(constraint (= (deobfucated #x0000000030a290b3 #x00000000080f1948) #xfffffffff7f0e6b8))
(constraint (= (deobfucated #x0000000007daa3e9 #x0000000006919deb) #xfffffffff96e6215))
(constraint (= (deobfucated #x0000000033be2ef7 #x000000001dcee5ae) #xffffffffe2311a52))
(constraint (= (deobfucated #x00000000314c02eb #x0000000015baf21a) #xffffffffea450de6))
(constraint (= (deobfucated #x00000000264dccd7 #x000000000686ceed) #xfffffffff9793113))
(constraint (= (deobfucated #x00000000172927ed #x00000000059d31de) #xfffffffffa62ce22))
(constraint (= (deobfucated #x000000000daee417 #x0000000018fc6e20) #xffffffffe70391e0))
(constraint (= (deobfucated #x000000002e2f58a0 #x000000000718407b) #xfffffffff8e7bf85))
(constraint (= (deobfucated #x000000002b8232d4 #x000000000403d532) #xfffffffffbfc2ace))
(constraint (= (deobfucated #x000000001312406c #x000000002188d61a) #xffffffffde7729e6))
(constraint (= (deobfucated #x000000002d78ac76 #x0000000016c149cb) #xffffffffe93eb635))
(constraint (= (deobfucated #x000000002b192f40 #x000000001f76254c) #xffffffffe089dab4))
(constraint (= (deobfucated #x000000002ecea8bf #x00000000380ebe15) #xffffffffc7f141eb))
(constraint (= (deobfucated #x0000000027455b17 #x0000000035a266fe) #xffffffffca5d9902))
(check-synth)