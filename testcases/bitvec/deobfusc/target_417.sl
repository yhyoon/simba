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

(constraint (= (deobfucated #x000000001faa1d4b #x000000002aae7a99) #xd8c7ebf797d9b8c9))
(constraint (= (deobfucated #x0000000004b86250 #x0000000029aacd42) #x0a118fcce73e9d21))
(constraint (= (deobfucated #x00000000108da66c #x000000000e37b81e) #x0a32347156f5e439))
(constraint (= (deobfucated #x00000000090e26b2 #x0000000031c6b5ec) #xb885f3fac7065899))
(constraint (= (deobfucated #x0000000020831832 #x0000000008d6f94b) #xe349687dcedc7e55))
(constraint (= (deobfucated #x0000000004dbc669 #x000000000ccb82af) #xf38ff6b3a86f745f))
(constraint (= (deobfucated #x000000002f01e39b #x000000000106ec65) #x3a46074318aa6235))
(constraint (= (deobfucated #x0000000027805c33 #x0000000039ba9c47) #x977be19e7c859035))
(constraint (= (deobfucated #x0000000013a4da21 #x000000001845dc68) #x837d335892eae7e1))
(constraint (= (deobfucated #x000000002cb09f60 #x0000000007526e21) #xee11faf5329cab41))
(constraint (= (deobfucated #x000000002b1763ed #x0000000003cfa133) #x7e5ce88c1dfd9d97))
(constraint (= (deobfucated #x000000002e038b6f #x000000000fb34681) #x0a177b02c3931da1))
(constraint (= (deobfucated #x000000003594b7bc #x0000000000a8faa6) #x6b31eabfb72fa399))
(constraint (= (deobfucated #x0000000006adbc9d #x000000000bf64415) #x3d324da39bb08ea9))
(constraint (= (deobfucated #x000000000f1da5ff #x000000003716e71f) #x1a88c3fe0747de01))
(constraint (= (deobfucated #x0000000029dc5beb #x0000000020746c04) #xc7037dabcea7c591))
(constraint (= (deobfucated #x00000000015ac0ed #x0000000026547db6) #xfee466c65ebb90cd))
(constraint (= (deobfucated #x000000003374798d #x000000000c4effe8) #x0364444c3f50ec41))
(constraint (= (deobfucated #x000000001f3aaf0b #x00000000369d9420) #x7d21d5430ce2bf01))
(constraint (= (deobfucated #x0000000035aa09ee #x0000000023c5bcc2) #xeab5f9a178448405))
(check-synth)