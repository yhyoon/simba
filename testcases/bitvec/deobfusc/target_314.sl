(set-logic BV)

(synth-fun deobfucated ( (e (BitVec 64))  (a (BitVec 64))  ) (BitVec 64)
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
				e a
			)
		)
	)
)

(constraint (= (deobfucated #x0000000011d0357b #x000000002d2c641d) #xfcdb4fd8e9323ea5))
(constraint (= (deobfucated #x000000000d50ef83 #x0000000013ba9a62) #xfef949638722fb5f))
(constraint (= (deobfucated #x00000000267eadd2 #x00000000258f8844) #xfa5a1ba052417a4a))
(constraint (= (deobfucated #x000000001641b120 #x00000000199e509f) #xfdc5d2265a5abe40))
(constraint (= (deobfucated #x0000000028b51e74 #x00000000077d8668) #xfecf165bc6c10db4))
(constraint (= (deobfucated #x000000002b318d07 #x0000000030b79949) #xf7c7bb463cf7b009))
(constraint (= (deobfucated #x000000001ee2d5d9 #x0000000029d545e2) #xfaf3f0961131d507))
(constraint (= (deobfucated #x0000000013f70f0e #x00000000029ff766) #xffcb98244ce59480))
(constraint (= (deobfucated #x00000000275a7b77 #x000000001d98109c) #xfb735fbcbfefdf07))
(constraint (= (deobfucated #x00000000361e96e3 #x000000000a990a18) #xfdc273b0e7c8959b))
(constraint (= (deobfucated #x000000001d8377ed #x000000001d63fb76) #xfc9c94957fb14513))
(constraint (= (deobfucated #x000000002ed823e1 #x0000000017717c20) #xfbb5d0a89b71cbe1))
(constraint (= (deobfucated #x0000000021d1bdfa #x00000000288ccf4b) #xfaa4a03acc8a7d06))
(constraint (= (deobfucated #x00000000010cfd3b #x0000000000ce17b0) #xffff277357f0acdb))
(constraint (= (deobfucated #x000000001c6ce980 #x0000000030653166) #xfaa057c3e13a8180))
(constraint (= (deobfucated #x00000000206b3528 #x0000000026ac5e67) #xfb1a4220310c3630))
(constraint (= (deobfucated #x00000000144c008e #x000000001044fb95) #xfeb5c7d4ca10746c))
(constraint (= (deobfucated #x000000001574dbb7 #x0000000010892118) #xfe9d33f50d3eac9f))
(constraint (= (deobfucated #x000000002c8ce22b #x000000000eea74b6) #xfd677e8ba122fbbb))
(constraint (= (deobfucated #x000000000d12c498 #x0000000003ede0dc) #xffcca1d69d359290))
(check-synth)