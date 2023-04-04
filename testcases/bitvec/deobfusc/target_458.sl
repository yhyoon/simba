(set-logic BV)

(synth-fun deobfucated ( (e (BitVec 64))  (c (BitVec 64))  (a (BitVec 64))  ) (BitVec 64)
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
				e c a
			)
		)
	)
)

(constraint (= (deobfucated #x0000000006620791 #x000000003b3a8e1a #x000000000fcf1662) #x000000004328a40c))
(constraint (= (deobfucated #x000000003066d971 #x000000002949e332 #x00000000355613da) #x000000005ec0bc2c))
(constraint (= (deobfucated #x000000000f6c46fd #x000000000155c165 #x00000000351439a7) #x0000000040c24164))
(constraint (= (deobfucated #x0000000028716028 #x00000000398d6935 #x000000002b5c7ab1) #x00000000440aa000))
(constraint (= (deobfucated #x00000000061b7c03 #x000000001955d76f #x000000003b90da88) #x0000000048e195f8))
(constraint (= (deobfucated #x0000000022819afe #x0000000028510ae6 #x000000002c262b90) #x0000000056f8c6e0))
(constraint (= (deobfucated #x000000001b562bea #x0000000029b50e8a #x000000002e3c61fe) #x0000000041331a88))
(constraint (= (deobfucated #x000000000492ce98 #x00000000349fd07b #x00000000142a0dac) #x000000004952a030))
(constraint (= (deobfucated #x0000000028b07ea6 #x0000000016b24f5f #x0000000017e21ace) #x0000000052a4c644))
(constraint (= (deobfucated #x000000000483fa39 #x00000000041093ee #x00000000231b877b) #x0000000029ac9000))
(constraint (= (deobfucated #x0000000007ecc3af #x000000000898471b #x000000000f5ea13d) #x0000000010910aca))
(constraint (= (deobfucated #x000000002a23fec7 #x0000000030e8aab3 #x0000000006e2978c) #x000000005d4ca880))
(constraint (= (deobfucated #x0000000005c82cfb #x000000001950e74e #x0000000039558974) #x00000000462a9400))
(constraint (= (deobfucated #x00000000291525f2 #x0000000025a6ca11 #x000000002f5631e4) #x0000000050ba0000))
(constraint (= (deobfucated #x0000000015b5953f #x000000000a2463f8 #x000000003817a595) #x0000000047cc0000))
(constraint (= (deobfucated #x00000000114b149b #x0000000030d5735e #x00000000134ef294) #x0000000044254980))
(constraint (= (deobfucated #x00000000341861d1 #x00000000290eb1ca #x000000002e17356f) #x00000000672a0280))
(constraint (= (deobfucated #x00000000387e53ae #x000000001d48805c #x000000000ee30a63) #x000000005846dc00))
(constraint (= (deobfucated #x0000000017eb242b #x0000000001158794 #x00000000372e1505) #x000000000904a8c0))
(constraint (= (deobfucated #x000000002b9427e7 #x00000000376e08a0 #x000000001f79b976) #x000000007363c080))
(check-synth)