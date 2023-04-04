(set-logic BV)

(synth-fun deobfucated ( (e (BitVec 64))  (a (BitVec 64))  (b (BitVec 64))  ) (BitVec 64)
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
				e a b
			)
		)
	)
)

(constraint (= (deobfucated #x000000001ec19c60 #x0000000006efc76e #x0000000005fc3f6c) #x0000000018001803))
(constraint (= (deobfucated #x000000000c7f7ea3 #x0000000024f82409 #x000000000281e5ea) #x0000000008075aa3))
(constraint (= (deobfucated #x00000000249ec64f #x00000000385001b9 #x0000000039c0cbc6) #x00000000048ec647))
(constraint (= (deobfucated #x000000003af062d3 #x0000000034b8ec42 #x0000000033804b73) #x000000000a400292))
(constraint (= (deobfucated #x000000002bc1a924 #x00000000166bd28c #x00000000142bb8c2) #x0000000029802927))
(constraint (= (deobfucated #x00000000310dd4a9 #x000000001c7abc5f #x00000000016b269e) #x00000000210540a1))
(constraint (= (deobfucated #x000000003811ab9f #x000000001f2728bd #x000000000d4b8a16) #x0000000020108303))
(constraint (= (deobfucated #x000000001ce6b536 #x0000000036b06136 #x000000002f3523c5) #x0000000008469403))
(constraint (= (deobfucated #x0000000036f18bb2 #x00000000084aaef5 #x0000000007b7b89e) #x0000000036b10103))
(constraint (= (deobfucated #x000000000d9a07dd #x000000000bc825a2 #x000000002d161644) #x000000000412025e))
(constraint (= (deobfucated #x000000001c2b22f1 #x0000000030d928a3 #x000000000228b835) #x000000000c220251))
(constraint (= (deobfucated #x000000003a3cfcd4 #x000000000b425239 #x000000000a1cda08) #x00000000303cacc5))
(constraint (= (deobfucated #x000000000c8f4841 #x00000000289b9bd0 #x000000000a517b22) #x000000000404401e))
(constraint (= (deobfucated #x000000000f25867e #x000000000f71ac1e #x00000000198500c0) #x0000000000040263))
(constraint (= (deobfucated #x0000000035ca5717 #x000000000a4fdec0 #x000000002e50be2a) #x0000000035800168))
(constraint (= (deobfucated #x0000000033f96e92 #x000000002cbe1bd8 #x0000000014fc54bd) #x000000001341640d))
(constraint (= (deobfucated #x000000000e467394 #x000000002a873cb5 #x00000000229516f2) #x0000000004404301))
(constraint (= (deobfucated #x0000000012db1706 #x000000003600dd30 #x000000003822aed9) #x0000000000db0219))
(constraint (= (deobfucated #x000000001bfc3883 #x0000000016bea3fa #x000000001d6769ef) #x0000000009401802))
(constraint (= (deobfucated #x0000000002a32a5b #x00000000064a3efe #x0000000023f5fb1d) #x0000000000a10002))
(check-synth)