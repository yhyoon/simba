(set-logic BV)

(synth-fun deobfucated ( (a (BitVec 64))  (c (BitVec 64))  (d (BitVec 64))  ) (BitVec 64)
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
				a c d
			)
		)
	)
)

(constraint (= (deobfucated #x000000000f93027e #x000000001362e957 #x0000000030a76846) #xffffffffefdfbc9c))
(constraint (= (deobfucated #x000000002738b5d0 #x000000002d25d068 #x0000000024ca01dc) #xfffffffffffffff8))
(constraint (= (deobfucated #x0000000017243c60 #x000000001bc80e43 #x000000001c15cc14) #xfffffffffb468e5c))
(constraint (= (deobfucated #x0000000038bdd4f3 #x0000000030a869fd #x000000002d707e4d) #xffffffffffffd7f4))
(constraint (= (deobfucated #x0000000036ef7693 #x0000000012b19ad4 #x0000000018513633) #xfffffffffff42ff8))
(constraint (= (deobfucated #x00000000067d9acc #x000000002f4f90cb #x0000000017dfed0e) #xfffffffffefffffe))
(constraint (= (deobfucated #x0000000030a993f7 #x000000002c665be4 #x000000001e911db2) #xfffffffff3fffd84))
(constraint (= (deobfucated #x0000000021ce93a6 #x000000001b086957 #x000000003b45e19d) #xffffffffe5ffdfef))
(constraint (= (deobfucated #x000000002454fc79 #x0000000027f7dacd #x00000000137e28c3) #xfffffffffefdff8c))
(constraint (= (deobfucated #x000000000f9180a9 #x0000000039143482 #x0000000029d4ce67) #xfffffffffffbfffe))
(constraint (= (deobfucated #x000000001d7231ce #x000000000576b821 #x000000002fd8c116) #xffffffffffffaf64))
(constraint (= (deobfucated #x00000000217dab8d #x000000000f8140aa #x000000000101d73e) #xffffffffffffbfde))
(constraint (= (deobfucated #x0000000014d63b0f #x000000000ed35d0c #x0000000028a20a7c) #xfffffffffe77c184))
(constraint (= (deobfucated #x0000000003c42bf2 #x0000000016986b76 #x0000000001cf5982) #xfffffffffff7ff78))
(constraint (= (deobfucated #x00000000337e1553 #x000000002bd313aa #x000000001b496b06) #xfffffffffffefe1a))
(constraint (= (deobfucated #x0000000010b83651 #x000000003593021e #x00000000153daf51) #xfffffffffeff2cfc))
(constraint (= (deobfucated #x000000000cb4c817 #x0000000028fe6914 #x000000001f6f5798) #xfffffffffff7ffac))
(constraint (= (deobfucated #x0000000038ca8249 #x000000000a55249f #x00000000397127a1) #xffffffffffeffbd6))
(constraint (= (deobfucated #x00000000319c5d19 #x0000000035c6517c #x0000000005efff99) #xffffffffffff3838))
(constraint (= (deobfucated #x000000002dc5c806 #x000000001539d69b #x0000000039c452fb) #xffffffffffffefff))
(check-synth)