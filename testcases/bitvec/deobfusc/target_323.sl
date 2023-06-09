(set-logic BV)

(synth-fun deobfucated ( (e (BitVec 64))  (a (BitVec 64))  (d (BitVec 64))  ) (BitVec 64)
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
				e a d
			)
		)
	)
)

(constraint (= (deobfucated #x0000000030d65c8b #x000000002a40c77c #x00000000344df0c1) #xfffffffffff9cffe))
(constraint (= (deobfucated #x0000000000f8ac9f #x000000001c8c69b0 #x000000002d4de067) #xffffffffffeffff8))
(constraint (= (deobfucated #x0000000028213653 #x000000001549556c #x000000000b6add77) #xffffffffdf6ff56c))
(constraint (= (deobfucated #x0000000025ba07a3 #x0000000030302c21 #x00000000379752a5) #xffffffffb9fead7f))
(constraint (= (deobfucated #x000000000b4fda16 #x000000001c40b342 #x000000003664676d) #xfffffffffffff75b))
(constraint (= (deobfucated #x00000000069ca73b #x0000000023610a3f #x0000000024a67b24) #xfffffffffbf9ffff))
(constraint (= (deobfucated #x000000002ba1db20 #x00000000008406d4 #x000000001963f5ae) #xfffffffff7dc6ffe))
(constraint (= (deobfucated #x0000000015e5cc52 #x000000002931e81a #x0000000038b9ee1f) #xffffffffff77f9ff))
(constraint (= (deobfucated #x0000000023047293 #x0000000020138788 #x000000001ef72583) #xffffffffe7f7d7f8))
(constraint (= (deobfucated #x0000000029906b86 #x000000001066089d #x000000002d885b6b) #xfffffffff2f7eefd))
(constraint (= (deobfucated #x0000000018fd46da #x0000000007de55ea #x0000000010d92728) #xffffffffeffedffe))
(constraint (= (deobfucated #x0000000035267a40 #x0000000003cacbc5 #x0000000026e48c55) #xffffffffd7dbffe7))
(constraint (= (deobfucated #x0000000034f544bd #x00000000279539fa #x00000000328b4e1f) #xffffffffeffd7bfe))
(constraint (= (deobfucated #x00000000277c3591 #x000000001db0ba7e #x0000000039872896) #xfffffffffdfbfeff))
(constraint (= (deobfucated #x000000001d247689 #x0000000005ee3eeb #x0000000002996cff) #xffffffffffffffff))
(constraint (= (deobfucated #x00000000100df616 #x00000000362b95da #x000000000c60bba1) #xffffffffffffffff))
(constraint (= (deobfucated #x000000002d072090 #x000000003375967d #x00000000098360c3) #xfffffffff7ff9efd))
(constraint (= (deobfucated #x0000000016cf13fe #x00000000253afc9a #x000000003a45f8f0) #xffffffffbfbbff9e))
(constraint (= (deobfucated #x000000002835a3f1 #x000000000be11856 #x0000000020bfab99) #xffffffffffe97dfe))
(constraint (= (deobfucated #x000000000da303d7 #x000000002d697b2e #x000000000da139e8) #xffffffffffffffef))
(check-synth)