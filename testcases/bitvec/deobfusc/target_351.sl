(set-logic BV)

(synth-fun deobfucated ( (a (BitVec 64))  (e (BitVec 64))  (d (BitVec 64))  ) (BitVec 64)
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
				a e d
			)
		)
	)
)

(constraint (= (deobfucated #x000000003552ebe5 #x00000000055f4ac0 #x00000000359eb280) #x000000006b7ead40))
(constraint (= (deobfucated #x00000000074b9d6e #x000000003436b63a #x0000000036a98e7b) #x000000006d694cf6))
(constraint (= (deobfucated #x00000000369eecd6 #x0000000029253448 #x000000003a3a4c98) #x000000007579c970))
(constraint (= (deobfucated #x000000001c529299 #x0000000011a8f6bd #x000000002e015e03) #x000000006dab5cc2))
(constraint (= (deobfucated #x0000000035ac3ada #x00000000211dfe41 #x0000000034992c0f) #x000000006a372a5e))
(constraint (= (deobfucated #x000000002026d6d2 #x0000000028737ece #x00000000057f8303) #x0000000032ff82d2))
(constraint (= (deobfucated #x0000000021063841 #x000000003957442a #x000000001ecd8ab5) #x000000005ead5974))
(constraint (= (deobfucated #x00000000156112f9 #x000000001883e6bd #x0000000037f1b73b) #x0000000077e5aefa))
(constraint (= (deobfucated #x0000000005afe787 #x000000001b1883fb #x000000001cb5a321) #x000000003c73471c))
(constraint (= (deobfucated #x000000001bf9fb12 #x0000000017a0160b #x000000000ceb30b9) #x000000002cd66774))
(constraint (= (deobfucated #x00000000374b7354 #x00000000348c4c7b #x000000002d7e185e) #x000000006b7c74dd))
(constraint (= (deobfucated #x0000000008e757d8 #x0000000033342f17 #x00000000394e767d) #x0000000074ccf5fc))
(constraint (= (deobfucated #x0000000008564242 #x000000000f070091 #x0000000033e107a0) #x0000000073c80f51))
(constraint (= (deobfucated #x0000000028524a47 #x00000000107b821d #x0000000014e49e2c) #x0000000029e43c69))
(constraint (= (deobfucated #x0000000031409c24 #x000000003606a1e2 #x000000002147a7cc) #x00000000588f4fba))
(constraint (= (deobfucated #x000000002de1de74 #x000000002326aa3a #x0000000030c920a0) #x0000000064b8cb5a))
(constraint (= (deobfucated #x00000000271c18ed #x000000002d04cae9 #x000000001104cdeb) #x000000004e099dd6))
(constraint (= (deobfucated #x00000000147d20e0 #x00000000374cb8ca #x000000002e441e44) #x000000006d90dd12))
(constraint (= (deobfucated #x000000001ac96caf #x00000000239fb05e #x000000003547d0f5) #x000000006d27c1f4))
(constraint (= (deobfucated #x00000000060dd3dc #x0000000005315911 #x0000000005762750) #x000000000aeda6a1))
(check-synth)