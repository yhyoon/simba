(set-logic BV)

(synth-fun deobfucated ( (c (BitVec 64))  (a (BitVec 64))  ) (BitVec 64)
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
				c a
			)
		)
	)
)

(constraint (= (deobfucated #x000000000f4c7824 #x000000001601ca0c) #x0000000010059a2c))
(constraint (= (deobfucated #x000000002a999837 #x000000001e75cd6a) #x000000003ceddd59))
(constraint (= (deobfucated #x00000000229e0932 #x000000000f940b32) #x000000002f020b32))
(constraint (= (deobfucated #x0000000019cdc21e #x000000000a0a00f4) #x000000001a0602e2))
(constraint (= (deobfucated #x000000002eab6792 #x000000002bdced0b) #x0000000007fde81b))
(constraint (= (deobfucated #x000000002bd3b684 #x0000000030620252) #x0000000030e000d6))
(constraint (= (deobfucated #x000000001e598688 #x0000000006e2a391) #x000000000eeba799))
(constraint (= (deobfucated #x00000000321a7839 #x000000003b0d1786) #x000000003b1f0f8f))
(constraint (= (deobfucated #x0000000010d95928 #x0000000034ae40c1) #x00000000347e01c9))
(constraint (= (deobfucated #x0000000005f7f25a #x000000002562fb96) #x000000002001fb8e))
(constraint (= (deobfucated #x0000000024ae1ea1 #x00000000142d4a2b) #x00000000300340ab))
(constraint (= (deobfucated #x0000000026f2f2fb #x0000000008703ec2) #x0000000028007c01))
(constraint (= (deobfucated #x0000000026150f8c #x000000000b6a3c8e) #x000000002f7f318e))
(constraint (= (deobfucated #x000000001855359c #x000000002e20c7ac) #x000000003e61d7bc))
(constraint (= (deobfucated #x000000002d6a5a14 #x000000002e1a8bb6) #x000000002e3a9bb6))
(constraint (= (deobfucated #x00000000082890bc #x0000000010ac2d53) #x0000000018acbdc7))
(constraint (= (deobfucated #x000000000916fdb5 #x00000000089cf57a) #x00000000019800ff))
(constraint (= (deobfucated #x00000000368b4e7c #x000000002a67da4c) #x0000000018efd01c))
(constraint (= (deobfucated #x0000000012dc8fe9 #x000000000bc2ab54) #x000000001b06a03d))
(constraint (= (deobfucated #x0000000013845f5c #x000000001dc0666b) #x000000001fc46167))
(check-synth)