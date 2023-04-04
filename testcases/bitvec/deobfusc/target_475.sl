(set-logic BV)

(synth-fun deobfucated ( (c (BitVec 64))  (a (BitVec 64))  (d (BitVec 64))  ) (BitVec 64)
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
				c a d
			)
		)
	)
)

(constraint (= (deobfucated #x00000000223e9101 #x000000002b02a929 #x00000000167e80f8) #xffffffffb2bec5d0))
(constraint (= (deobfucated #x000000001266b6c0 #x0000000033a88ba6 #x000000002953c34f) #xffffffffb9f0bd9a))
(constraint (= (deobfucated #x000000000cf3dbc0 #x0000000026e416d5 #x000000002f990572) #xffffffffcc280d6a))
(constraint (= (deobfucated #x000000002aeb72fc #x0000000010e411d3 #x000000001109f37c) #xffffffffc4307b30))
(constraint (= (deobfucated #x000000001910fa3b #x00000000271f2356 #x00000000178de208) #xffffffffbfcfe26b))
(constraint (= (deobfucated #x00000000200a81b7 #x00000000223cef48 #x0000000008baef32) #xffffffffbdb88f01))
(constraint (= (deobfucated #x00000000211a6ce3 #x00000000235b13ed #x00000000278b4667) #xffffffffbb8a7f30))
(constraint (= (deobfucated #x000000001afca303 #x0000000014d5375f #x000000001ff13637) #xffffffffd02e259e))
(constraint (= (deobfucated #x0000000005440d1c #x0000000028c0b13b #x000000001681f361) #xffffffffd1fb41a9))
(constraint (= (deobfucated #x000000001bbea136 #x0000000019c6575a #x0000000016035a16) #xffffffffca7b0770))
(constraint (= (deobfucated #x000000001be94fa9 #x000000002b7c6891 #x0000000003549406) #xffffffffb89a47c6))
(constraint (= (deobfucated #x0000000039ac527c #x000000000b2d0e5f #x0000000003114b06) #xffffffffbb269f24))
(constraint (= (deobfucated #x000000000ccc153e #x0000000007c48bc9 #x0000000006a5e9ce) #xffffffffeb6f5ef8))
(constraint (= (deobfucated #x000000000abf4960 #x000000001c2fa843 #x000000001232878f) #xffffffffd9110e5d))
(constraint (= (deobfucated #x0000000038868afc #x000000001b329569 #x000000000329436c) #xffffffffac46df98))
(constraint (= (deobfucated #x0000000027d21243 #x0000000003a1015c #x0000000012ccab32) #xffffffffd48cec61))
(constraint (= (deobfucated #x00000000038b20c0 #x000000001a760927 #x00000000133b1c3b) #xffffffffe1fed619))
(constraint (= (deobfucated #x000000001530b3a2 #x000000001d550547 #x000000000ca93669) #xffffffffcd7a4717))
(constraint (= (deobfucated #x000000001e32ea55 #x00000000206afe44 #x000000000a6d97c5) #xffffffffc1621767))
(constraint (= (deobfucated #x000000000a3501f3 #x00000000156234dc #x000000000f6f7b18) #xffffffffe068c931))
(check-synth)