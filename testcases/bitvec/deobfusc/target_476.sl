(set-logic BV)

(synth-fun deobfucated ( (a (BitVec 64))  (c (BitVec 64))  (b (BitVec 64))  ) (BitVec 64)
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
				a c b
			)
		)
	)
)

(constraint (= (deobfucated #x000000000939ca37 #x00000000174178c2 #x000000003192d79f) #xff7dffeeea77fa71))
(constraint (= (deobfucated #x000000002071072b #x000000001bd49230 #x0000000036e93d70) #xfdff2c9dfd1ca3ef))
(constraint (= (deobfucated #x000000001a034af7 #x0000000010197937 #x0000000031b638aa) #xfefd77ed5ebde7ff))
(constraint (= (deobfucated #x000000000aed0bf1 #x0000000013cd8016 #x0000000031115919) #xffafe6ffdeabffcf))
(constraint (= (deobfucated #x0000000023e1b46d #x0000000032162c35 #x0000000021a922c9) #xf9ffff3efbe6f96e))
(constraint (= (deobfucated #x0000000010e5459a #x000000003aff87b9 #x0000000006b208c4) #xff7bfbe7ab3e7fbf))
(constraint (= (deobfucated #x0000000017ecdbcc #x000000000eaf1f83 #x000000003ad5360d) #xffe5ae9eefb9dafb))
(constraint (= (deobfucated #x0000000016cd88e1 #x0000000030aa63a5 #x0000000016cc28f9) #xfffb79fcfc3fd7fa))
(constraint (= (deobfucated #x0000000039af57bc #x000000001b648bf7 #x00000000138ec347) #xfdf7ddff6dbf4dbb))
(constraint (= (deobfucated #x000000002eef9036 #x000000002defefd9 #x000000000537d21a) #xff93efef7ee259bd))
(constraint (= (deobfucated #x00000000056e98de #x00000000229deb50 #x000000000f32c7c0) #xfffbffe3baf778bf))
(constraint (= (deobfucated #x000000000f39f0cc #x000000001ca31f1d #x0000000037a52999) #xfffbfdffa07bd4e3))
(constraint (= (deobfucated #x000000000d2548d6 #x0000000036ac53b6 #x0000000036174d12) #xfd77fdc9fdd8f7fb))
(constraint (= (deobfucated #x000000001aee8115 #x000000002e7db777 #x000000000000041e) #xffffff4e2fdefffd))
(constraint (= (deobfucated #x0000000002bba4c5 #x000000002d1f1d99 #x000000000beaa943) #xffecafffb7553566))
(constraint (= (deobfucated #x0000000010f85b76 #x000000001189becd #x0000000039af1a4e) #xfede75de4d17afa1))
(constraint (= (deobfucated #x000000000c7ca8af #x000000002e26dd61 #x0000000010718085) #xffffb473af2b22ba))
(constraint (= (deobfucated #x000000002f015293 #x00000000245c66a4 #x00000000291a3fd8) #xfb73dd19d36cc7f7))
(constraint (= (deobfucated #x000000001bad4379 #x00000000030b9f25 #x00000000105b0226) #xfffffeffb5da5ccb))
(constraint (= (deobfucated #x000000001625783b #x000000003043cb5f #x000000001e2b42dd) #xfffb3dffaad0b93a))
(check-synth)