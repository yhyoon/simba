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

(constraint (= (deobfucated #x000000002b24f307 #x0000000028e094e9) #xf91c6099a0bec2a1))
(constraint (= (deobfucated #x000000003acafc31 #x0000000033e9627a) #xf413f664fb200ea6))
(constraint (= (deobfucated #x0000000016b541ed #x0000000028a26935) #xfc6545aa347524ef))
(constraint (= (deobfucated #x000000002cc86c1d #x000000003927f671) #xf6006248b6396933))
(constraint (= (deobfucated #x000000002eb6b090 #x0000000032a1f360) #xf6c2c435e7551a00))
(constraint (= (deobfucated #x0000000004ee4884 #x0000000025691a78) #xff478946aacc9a20))
(constraint (= (deobfucated #x0000000007fe6fc5 #x0000000011956db5) #xff73700fe0db18b7))
(constraint (= (deobfucated #x0000000023793a85 #x0000000031da0430) #xf91795fc2a18f310))
(constraint (= (deobfucated #x000000002b9971bf #x0000000023eb6eb7) #xf9e1ecbc5f1a9e77))
(constraint (= (deobfucated #x0000000013eb93f8 #x00000000259ec097) #xfd12993b6601b8b8))
(constraint (= (deobfucated #x000000002e99bce8 #x000000003032bd89) #xf739f00d29f29fd8))
(constraint (= (deobfucated #x000000000aeeb84b #x000000000c1d7fb2) #xff7b8cdd9417a6da))
(constraint (= (deobfucated #x0000000015abb4bc #x00000000167f99da) #xfe1871431b7fbbe8))
(constraint (= (deobfucated #x000000000d85364b #x000000002e67d79e) #xfd8c9442750280b6))
(constraint (= (deobfucated #x000000000382c87f #x0000000021b8f487) #xff899acd04a73907))
(constraint (= (deobfucated #x00000000017e9e2f #x0000000016b7ef94) #xffde0b7ecf85abd4))
(constraint (= (deobfucated #x000000000e1c1c24 #x00000000058672fb) #xffb20a66371060b4))
(constraint (= (deobfucated #x0000000017393d82 #x000000001c29dd77) #xfd71f103b8792e92))
(constraint (= (deobfucated #x0000000000c7b236 #x00000000129c9ff6) #xfff17b4ad383361c))
(constraint (= (deobfucated #x000000000117d88c #x000000000ec8c5e1) #xffefd6aedb06f0f4))
(check-synth)