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

(constraint (= (deobfucated #x000000002a5f9e0e #x000000001a7fcf8f) #xfb9d22286957023c))
(constraint (= (deobfucated #x0000000030bc7bfd #x0000000005903aa9) #xfef0dc63a1e74ff8))
(constraint (= (deobfucated #x000000000f4bc91a #x000000001a9dc219) #xfe68e0803a217390))
(constraint (= (deobfucated #x0000000039445f8b #x0000000038e66b22) #xf3457fb4cbdeb615))
(constraint (= (deobfucated #x00000000215e725d #x0000000003702ea3) #xff8d4542cc1eefc8))
(constraint (= (deobfucated #x00000000017cf931 #x0000000019225f22) #xffda98838ce8b3b1))
(constraint (= (deobfucated #x0000000000935822 #x00000000024acfa7) #xfffeae40be5ddbf8))
(constraint (= (deobfucated #x0000000034973100 #x00000000394ccc26) #xf43a8f4468222b00))
(constraint (= (deobfucated #x000000003904b13b #x000000002fd15686) #xf559835c48dc5c5d))
(constraint (= (deobfucated #x00000000072b5ee9 #x000000001ed917d5) #xff22d672715d791c))
(constraint (= (deobfucated #x00000000228f5f03 #x000000002029d270) #xfba86ec0d06ad7b3))
(constraint (= (deobfucated #x000000000babb785 #x0000000026ef11f1) #xfe399ca098ed1e50))
(constraint (= (deobfucated #x00000000278b839c #x000000000b1a75e0) #xfe48eaf7c08a133c))
(constraint (= (deobfucated #x000000002d6b1308 #x00000000312c510c) #xf746a4936e04a6a8))
(constraint (= (deobfucated #x0000000026dd8286 #x00000000079b8233) #xfed8558c3c5475d4))
(constraint (= (deobfucated #x000000001390216f #x0000000037a461fa) #xfbbf78ff3c28ac99))
(constraint (= (deobfucated #x00000000204c5a95 #x000000000446a929) #xff75e45d73881ce0))
(constraint (= (deobfucated #x000000002f1b0583 #x000000002a1236f5) #xf842371585df1f28))
(constraint (= (deobfucated #x000000001c5b5124 #x00000000153c3cd3) #xfda5d6345dc720b8))
(constraint (= (deobfucated #x000000003b37c014 #x0000000029a4dddb) #xf65def3430e52b00))
(check-synth)