(set-logic BV)

(synth-fun deobfucated ( (a (BitVec 64))  ) (BitVec 64)
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
				a
			)
		)
	)
)

(constraint (= (deobfucated #x00000000006490f3) #xffffffffff76defb))
(constraint (= (deobfucated #x000000002d7329ba) #xffffffffad7badbb))
(constraint (= (deobfucated #x0000000030874dce) #xffffffffbef76def))
(constraint (= (deobfucated #x00000000157142a7) #xffffffffd57d7ab7))
(constraint (= (deobfucated #x000000001e0a8665) #xffffffffdfeaf775))
(constraint (= (deobfucated #x0000000032117ed1) #xffffffffbbdd7edd))
(constraint (= (deobfucated #x0000000036258517) #xffffffffb7b5f5d7))
(constraint (= (deobfucated #x000000000ae200d7) #xffffffffeafbfed7))
(constraint (= (deobfucated #x000000002ea68595) #xffffffffaeb6f5d5))
(constraint (= (deobfucated #x000000000dd10a71) #xffffffffedddeb7d))
(constraint (= (deobfucated #x000000001d4dcaa3) #xffffffffdd6deabb))
(constraint (= (deobfucated #x0000000030121ffb) #xffffffffbfdbdffb))
(constraint (= (deobfucated #x000000000be34b78) #xffffffffebfb6b7f))
(constraint (= (deobfucated #x000000000b8eff83) #xffffffffebeefffb))
(constraint (= (deobfucated #x0000000036c132ce) #xffffffffb6fdbaef))
(constraint (= (deobfucated #x0000000039a46f24) #xffffffffbdb76fb7))
(constraint (= (deobfucated #x00000000358f5b80) #xffffffffb5ef5bff))
(constraint (= (deobfucated #x0000000016f38d35) #xffffffffd6fbedb5))
(constraint (= (deobfucated #x00000000025b024d) #xfffffffffb5bfb6d))
(constraint (= (deobfucated #x0000000037497033) #xffffffffb76d7fbb))
(check-synth)