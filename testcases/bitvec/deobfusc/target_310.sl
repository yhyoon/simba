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

(constraint (= (deobfucated #x0000000024ca99f0 #x000000000fe3e3f5) #x02489f6e38db9735))
(constraint (= (deobfucated #x0000000034b89cec #x00000000277b7519) #x08218cb8e29690cd))
(constraint (= (deobfucated #x0000000008ffae01 #x0000000017e91eed) #x00d72a6dd8fe99d9))
(constraint (= (deobfucated #x0000000001233196 #x000000002baaee21) #x0031abc227c5a75f))
(constraint (= (deobfucated #x000000003b81990d #x00000000089e4f06) #x0200d9237a68be40))
(constraint (= (deobfucated #x000000000c5a2e8d #x0000000039dea0d5) #x02cad254991b74a9))
(constraint (= (deobfucated #x0000000004a2062e #x00000000294c8b3e) #x00bf559c6d8d0648))
(constraint (= (deobfucated #x000000000a00a4c6 #x000000001b67d896) #x01122019ba78f098))
(constraint (= (deobfucated #x00000000363b3521 #x0000000031655083) #x0a76cb95b10b8a25))
(constraint (= (deobfucated #x0000000033dae1f3 #x00000000212cdac9) #x06b84d1077aeae2f))
(constraint (= (deobfucated #x000000002dfcb25c #x00000000250d455b) #x06a7e811e26b33e7))
(constraint (= (deobfucated #x000000001badff69 #x0000000020a5d698) #x0387ae46dad392a0))
(constraint (= (deobfucated #x00000000182012e8 #x00000000204be21c) #x030b29117e36d384))
(constraint (= (deobfucated #x00000000170aebde #x00000000275138cd) #x0389f98074ee8b17))
(constraint (= (deobfucated #x0000000028b5bbe9 #x000000000dbef04b) #x022f97a29fa18695))
(constraint (= (deobfucated #x000000000c838cbf #x000000001ba0d1eb) #x0159bc5303297ca9))
(constraint (= (deobfucated #x0000000026f7715b #x0000000021bd51bb) #x0522b6bc0933da9d))
(constraint (= (deobfucated #x000000001833900f #x000000000ef29cb6) #x0169c16fb76bbb54))
(constraint (= (deobfucated #x000000001a7e0049 #x000000001b548200) #x02d408d3f8659448))
(constraint (= (deobfucated #x0000000014ea5a87 #x0000000037c318ff) #x048e4a010e268dfd))
(check-synth)