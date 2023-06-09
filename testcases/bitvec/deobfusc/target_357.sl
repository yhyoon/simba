(set-logic BV)

(synth-fun deobfucated ( (e (BitVec 64))  (a (BitVec 64))  (c (BitVec 64))  ) (BitVec 64)
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
				e a c
			)
		)
	)
)

(constraint (= (deobfucated #x0000000009f614a7 #x000000002da141a5 #x0000000002a96d16) #x000000001449daf3))
(constraint (= (deobfucated #x000000002e57ba25 #x000000001a80810c #x000000001f39e854) #x000000004196e2cd))
(constraint (= (deobfucated #x0000000001305551 #x000000000332dd21 #x00000000000732a5) #x00000000075d8ab5))
(constraint (= (deobfucated #x0000000001098f86 #x000000001d50dc34 #x000000001f1d3bcb) #x00000000213560f4))
(constraint (= (deobfucated #x0000000032c693f8 #x000000003ab0064a #x000000001ce209f4) #xffffffff8268a418))
(constraint (= (deobfucated #x000000001a9bbfe3 #x00000000251297f2 #x0000000005ca8ab5) #x000000006159a01a))
(constraint (= (deobfucated #x0000000004f44520 #x00000000239fd030 #x00000000396c39ba) #x000000005a23ba90))
(constraint (= (deobfucated #x0000000024d243a5 #x0000000003107f82 #x000000001fce4192) #x0000000055b73cab))
(constraint (= (deobfucated #x0000000035dda6e3 #x000000003380655f #x000000001317713a) #xffffffff988d28a5))
(constraint (= (deobfucated #x0000000003cd1668 #x0000000012c12c14 #x000000002f267663) #x00000000796fcfc8))
(constraint (= (deobfucated #x000000000663aae0 #x000000002053a8df #x0000000028e43313) #x0000000067488b0d))
(constraint (= (deobfucated #x0000000013c2df29 #x0000000020aef23f #x0000000008023c39) #x000000001b8f0287))
(constraint (= (deobfucated #x0000000026f18ec1 #x0000000031f158f5 #x000000000acbe032) #x000000005514bf1f))
(constraint (= (deobfucated #x0000000020852ef0 #x0000000025e4687a #x0000000022cf15da) #xffffffffad56c40e))
(constraint (= (deobfucated #x00000000395b31f0 #x000000002f950fee #x000000001440ef16) #xffffffff9324a01a))
(constraint (= (deobfucated #x000000001a9226f0 #x0000000035f8405b #x0000000035538233) #x0000000040349a95))
(constraint (= (deobfucated #x0000000039d721a3 #x000000001f9506b1 #x000000001dd6d424) #xffffffffa2d32bad))
(constraint (= (deobfucated #x00000000127ef2f4 #x000000002a6d8b74 #x000000002dfdae5e) #x0000000045006184))
(constraint (= (deobfucated #x000000001f89a4f4 #x000000001d87186c #x000000002444833a) #x0000000040935a94))
(constraint (= (deobfucated #x0000000020f0a704 #x000000002fa70b6d #x0000000002287b76) #x000000007d4f358c))
(check-synth)