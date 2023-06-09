(set-logic BV)

(synth-fun deobfucated ( (e (BitVec 64))  (d (BitVec 64))  ) (BitVec 64)
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
				e d
			)
		)
	)
)

(constraint (= (deobfucated #x000000001fe6b2d2 #x00000000028ce3ec) #xffaea40960218d55))
(constraint (= (deobfucated #x000000000192488f #x000000001c600a03) #xffd3692568af47c3))
(constraint (= (deobfucated #x0000000002097308 #x000000002643fbf8) #xffb20e7273ed1531))
(constraint (= (deobfucated #x0000000025459d78 #x000000001e217377) #xfb9cf8c2e4e4c291))
(constraint (= (deobfucated #x0000000023296278 #x00000000385ed3e9) #xf841ec2834eab611))
(constraint (= (deobfucated #x000000000f977b7f #x00000000262c22c6) #xfdacd383a0710903))
(constraint (= (deobfucated #x00000000378b5949 #x0000000002f9eea3) #xff5aaefc50b4a73d))
(constraint (= (deobfucated #x000000000631be13 #x0000000033e8a939) #xfebe75f5b1d842b3))
(constraint (= (deobfucated #x000000003a61f6e4 #x000000000cd3442f) #xfd133a21ca201121))
(constraint (= (deobfucated #x000000000e3f438f #x00000000258c2c02) #xfde90e30524160d3))
(constraint (= (deobfucated #x000000002a946fe0 #x00000000099a000f) #xfe672ac32974a041))
(constraint (= (deobfucated #x000000003505df9b #x000000000b3e7c19) #xfdabce43d38a20ab))
(constraint (= (deobfucated #x00000000141833b1 #x000000000a38287a) #xff32a582578b5055))
(constraint (= (deobfucated #x00000000132c05a5 #x0000000039c72fb5) #xfbac47f31967acaf))
(constraint (= (deobfucated #x000000002a5ddf52 #x00000000023902b6) #xffa1d4e795a42151))
(constraint (= (deobfucated #x0000000039745d56 #x0000000007ea2108) #xfe3945ab471444b5))
(constraint (= (deobfucated #x000000001303ead9 #x00000000231854d5) #xfd64a83911501a4b))
(constraint (= (deobfucated #x0000000011e7257e #x000000001086ec64) #xfed81e225828ed05))
(constraint (= (deobfucated #x00000000378f14e9 #x00000000218367a8) #xf8ba0996d0e1732f))
(constraint (= (deobfucated #x000000001c7762af #x000000001e8cbd3a) #xfc9a5c1ac688aea3))
(check-synth)