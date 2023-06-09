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

(constraint (= (deobfucated #x00000000315bd85a #x0000000012ad3dcb) #xfffffffff57ffd7b))
(constraint (= (deobfucated #x0000000027f41a7b #x00000000391d572c) #xf9c3b72c3ffffeff))
(constraint (= (deobfucated #x0000000022f9b26b #x0000000039034fcc) #xfb38b90f37f9bf6f))
(constraint (= (deobfucated #x00000000320e93fe #x000000001cc1d282) #xfffffffffabfffff))
(constraint (= (deobfucated #x000000002bbb929b #x00000000201b80ce) #xfffffffffffffebf))
(constraint (= (deobfucated #x00000000124958d6 #x00000000263cb947) #xfeb19a7e1ffb7dff))
(constraint (= (deobfucated #x00000000136f01e7 #x0000000014b8e252) #xfe8655951fefe1ef))
(constraint (= (deobfucated #x000000002d17813b #x000000000b7ddad9) #xffffffffff7ffdff))
(constraint (= (deobfucated #x000000000a44b91d #x0000000021cd53e2) #xff968f16dffdbbff))
(constraint (= (deobfucated #x0000000037edd5b0 #x0000000000c5c939) #xfffffffffffff7ff))
(constraint (= (deobfucated #x00000000115dbb13 #x000000002c5951b7) #xfed26ad61fffbfb7))
(constraint (= (deobfucated #x0000000025794e3f #x00000000296fa571) #xfa83b5e6bfffdf7f))
(constraint (= (deobfucated #x0000000024cd1311 #x000000002e51c3f9) #xfab5ae5baddffbff))
(constraint (= (deobfucated #x000000000bbcee10 #x000000002197f8f1) #xff76381c1ffffeff))
(constraint (= (deobfucated #x000000002dc882a6 #x000000000be9c829) #xfffffffffffbffff))
(constraint (= (deobfucated #x00000000145f18af #x0000000008a58a24) #xfffffffff7fff9ff))
(constraint (= (deobfucated #x000000002fb528d3 #x0000000034cddabf) #xf71bfacfefbffbff))
(constraint (= (deobfucated #x0000000007a661a6 #x000000000b922d1b) #xffc57a8627ffebff))
(constraint (= (deobfucated #x00000000287445a7 #x00000000214915fd) #xfffffffffdf4ddff))
(constraint (= (deobfucated #x0000000007bb896f #x0000000032454be9) #xffc43519ffbfcbff))
(check-synth)