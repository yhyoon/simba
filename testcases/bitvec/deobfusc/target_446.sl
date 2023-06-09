(set-logic BV)

(synth-fun deobfucated ( (e (BitVec 64))  (d (BitVec 64))  (c (BitVec 64))  ) (BitVec 64)
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
				e d c
			)
		)
	)
)

(constraint (= (deobfucated #x000000000075bb50 #x000000000b13074d #x0000000037af7342) #x0000000042f7fbde))
(constraint (= (deobfucated #x000000000d4c8962 #x000000000fb6172e #x000000002f9c10a3) #x000000003f5eaff2))
(constraint (= (deobfucated #x000000000543f1c8 #x000000000485ed2f #x0000000007434a95) #x000000000fcbf7cb))
(constraint (= (deobfucated #x0000000004a0dc8d #x000000000ce20a03 #x000000000156f220) #x000000000eb8fcaf))
(constraint (= (deobfucated #x000000003644841f #x0000000005ccc882 #x0000000019b71278) #x000000003fc7deff))
(constraint (= (deobfucated #x000000003317bcdc #x0000000004d3ee5e #x0000000034e31c4d) #x000000003bb7befe))
(constraint (= (deobfucated #x000000001ddcd64e #x000000001391f0fd #x00000000346f5eb3) #x000000005ddddfef))
(constraint (= (deobfucated #x000000002d867ddb #x000000002674b402 #x0000000008b1afa4) #x000000002fa67fff))
(constraint (= (deobfucated #x000000000291eb18 #x000000002828833a #x0000000022930b6f) #x000000004abbefb8))
(constraint (= (deobfucated #x00000000046d053c #x000000002f175c7e #x00000000382eda78) #x00000000676f37fd))
(constraint (= (deobfucated #x000000002aa6f25a #x0000000000c9172e #x000000003749d746) #x000000003ab6fe7b))
(constraint (= (deobfucated #x000000002f8bc5d4 #x0000000034e144fb #x0000000011254ceb) #x000000006f8fd5f5))
(constraint (= (deobfucated #x0000000035481b95 #x00000000049437e0 #x00000000280109be) #x000000003ddd5b9d))
(constraint (= (deobfucated #x00000000097f238e #x0000000027edcd19 #x00000000245c61b8) #x000000004d7f2fde))
(constraint (= (deobfucated #x0000000005ba0952 #x00000000056b2e85 #x0000000026e388d8) #x000000002dfebf5e))
(constraint (= (deobfucated #x000000000f6489bd #x000000002947212d #x0000000034eb5d88) #x000000005f76ffbd))
(constraint (= (deobfucated #x000000002bfb01dc #x000000000faa6c94 #x0000000007937c12) #x000000003fffe9fd))
(constraint (= (deobfucated #x000000001e395cd4 #x000000000143ae2e #x0000000032bf74d1) #x000000003e3b7efe))
(constraint (= (deobfucated #x000000000f8fa9ff #x0000000007f26ec9 #x0000000005c83b45) #x000000000fbfabff))
(constraint (= (deobfucated #x000000000f626f4d #x000000001588ca8d #x000000001ece5f28) #x000000003f776ffd))
(check-synth)