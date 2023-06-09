(set-logic BV)

(synth-fun deobfucated ( (a (BitVec 64))  (d (BitVec 64))  ) (BitVec 64)
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
				a d
			)
		)
	)
)

(constraint (= (deobfucated #x0000000000030407 #x000000000df79a99) #xfffffff6ea315d56))
(constraint (= (deobfucated #x000000002562ce84 #x00000000283b89ef) #xfa8a4a2b1c4e4a84))
(constraint (= (deobfucated #x00000000057eb3f2 #x00000000027d22ca) #xffe1ce42e94aaf33))
(constraint (= (deobfucated #x000000000e5bcd9f #x00000000246f34a9) #xff31d496e7e9c71e))
(constraint (= (deobfucated #x0000000004570e98 #x000000000d030742) #xffed29f05adb04fd))
(constraint (= (deobfucated #x0000000004b4bd7c #x0000000036c7dfde) #xffe9da792f1ce96d))
(constraint (= (deobfucated #x0000000009c616e1 #x000000000ae45f0c) #xffa0791cc5c8c732))
(constraint (= (deobfucated #x000000002bf1a25e #x0000000005e48c63) #xf874ef61540ce95a))
(constraint (= (deobfucated #x000000003550c11a #x000000002102eaaa) #xf4e57691fa15e3fb))
(constraint (= (deobfucated #x00000000050a30f7 #x000000001926c38a) #xffe699ae6572b2a6))
(constraint (= (deobfucated #x0000000012e9f769 #x000000000afebc6e) #xfe9a4360e7d43ee8))
(constraint (= (deobfucated #x000000001698696c #x000000002b125764) #xfe0173243d542c6f))
(constraint (= (deobfucated #x000000000a292dc2 #x00000000214d6508) #xff98c1cd06ea78f3))
(constraint (= (deobfucated #x0000000020b7e5cc #x00000000317f5046) #xfbd18272b959756d))
(constraint (= (deobfucated #x0000000038ad3e11 #x00000000070a36ab) #xf373bf9b9afbc274))
(constraint (= (deobfucated #x000000001137c6ad #x0000000034906a83) #xfed78b7629f9c714))
(constraint (= (deobfucated #x0000000005cf69e4 #x00000000088a9b8c) #xffde3dd0a57bbee7))
(constraint (= (deobfucated #x0000000025df809f #x000000001b7a59d6) #xfa65a1b0ae7ec47e))
(constraint (= (deobfucated #x0000000038e4af72 #x000000002507348b) #xf35b26f521b1e1b2))
(constraint (= (deobfucated #x0000000037f48ac4 #x00000000198cf562) #xf3c502c6ff206ccd))
(check-synth)