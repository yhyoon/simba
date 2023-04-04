(set-logic BV)

(synth-fun deobfucated ( (c (BitVec 64))  (a (BitVec 64))  (b (BitVec 64))  ) (BitVec 64)
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
				c a b
			)
		)
	)
)

(constraint (= (deobfucated #x00000000098e8666 #x0000000001f185dc #x000000001c2c679b) #xfffffffff447ffbc))
(constraint (= (deobfucated #x0000000023528514 #x0000000038f317ba #x0000000004fbc167) #xffffffff9b9862b4))
(constraint (= (deobfucated #x000000001c5ed69c #x000000000d808089 #x0000000019e5bd67) #xfffffffff521ae1d))
(constraint (= (deobfucated #x0000000015942616 #x00000000186d235e #x0000000005d5de40) #xffffffffd2853a74))
(constraint (= (deobfucated #x0000000017c026e8 #x000000000a225da3 #x000000000f4276a5) #xffffffffd21924ab))
(constraint (= (deobfucated #x0000000013ff1ec1 #x00000000055a6b71 #x0000000035c2e7a0) #xffffffffe1a57cb2))
(constraint (= (deobfucated #x000000002abdc53c #x0000000029b9d2eb #x00000000115d7e90) #xffffffff8b380fe7))
(constraint (= (deobfucated #x000000000a6aa0e0 #x0000000027436bfb #x0000000025c39721) #xffffffff8cd0cb63))
(constraint (= (deobfucated #x0000000019231585 #x000000001afb7f99 #x00000000331273ac) #xffffffff89c16996))
(constraint (= (deobfucated #x0000000016e7bd20 #x000000000ef6f2fb #x000000002e59e338) #xffffffff96134ddb))
(constraint (= (deobfucated #x00000000196bd52d #x00000000320616de #x000000003a29c4d6) #xffffffff909e13f3))
(constraint (= (deobfucated #x000000001570e002 #x000000001e4f8960 #x000000001c70d6d2) #xffffffffc4c0e91e))
(constraint (= (deobfucated #x0000000021a938ad #x0000000016370208 #x0000000035df6a32) #xffffffffe08dc169))
(constraint (= (deobfucated #x0000000031a41690 #x000000000e01d32a #x0000000002301f5c) #xffffffffbc5a3c52))
(constraint (= (deobfucated #x000000002f45e47f #x000000002da75507 #x00000000031ad9bf) #xffffffffa6e3b486))
(constraint (= (deobfucated #x000000000bc63f9f #x0000000011f469c3 #x000000001014dbef) #xffffffffc22c6a22))
(constraint (= (deobfucated #x000000000e387de9 #x000000001f3399dc #x000000003a8c2e1a) #xffffffff96943c29))
(constraint (= (deobfucated #x000000002202b3af #x000000000093a33d #x000000000eec52b2) #xffffffffdc912914))
(constraint (= (deobfucated #x000000002da987cb #x000000000409c6c3 #x000000002cf71e02) #xffffffffd6608172))
(constraint (= (deobfucated #x0000000019eb0a15 #x000000000e5cd79d #x00000000159e7f41) #xfffffffff0b3cc4e))
(check-synth)