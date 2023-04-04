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

(constraint (= (deobfucated #x00000000071bc5a3 #x000000002125daa3) #x0000000000000000))
(constraint (= (deobfucated #x00000000151dfd29 #x000000002a2a4ca9) #x0000000000000000))
(constraint (= (deobfucated #x00000000336a786e #x000000001fb731df) #x0000000000000000))
(constraint (= (deobfucated #x000000002b2c6858 #x000000002cee3e89) #x0000000000000000))
(constraint (= (deobfucated #x0000000033b36e1b #x00000000170b87c4) #x0000000000000000))
(constraint (= (deobfucated #x000000001e203e44 #x0000000004dfc08e) #x0000000000000000))
(constraint (= (deobfucated #x000000001a0bced5 #x0000000001aadbfd) #x0000000000000000))
(constraint (= (deobfucated #x0000000027ffb125 #x00000000135edfe5) #x0000000000000000))
(constraint (= (deobfucated #x0000000015eb99ca #x0000000029080a62) #x0000000000000000))
(constraint (= (deobfucated #x0000000011b64982 #x0000000023cbdf5b) #x0000000000000000))
(constraint (= (deobfucated #x000000000810d24a #x000000002622744d) #x0000000000000000))
(constraint (= (deobfucated #x000000002b883167 #x000000001e1383f5) #x0000000000000000))
(constraint (= (deobfucated #x0000000004866a17 #x000000002ff03860) #x0000000000000000))
(constraint (= (deobfucated #x0000000029491334 #x000000003615382a) #x0000000000000000))
(constraint (= (deobfucated #x000000001d78f622 #x0000000032e436e6) #x0000000000000000))
(constraint (= (deobfucated #x000000000f2dbbfc #x0000000018010539) #x0000000000000000))
(constraint (= (deobfucated #x0000000018995ed9 #x000000000f7dca24) #x0000000000000000))
(constraint (= (deobfucated #x0000000002d6f2af #x0000000016108a5e) #x0000000000000000))
(constraint (= (deobfucated #x000000000137ad44 #x000000000928b326) #x0000000000000000))
(constraint (= (deobfucated #x0000000028452475 #x00000000055407be) #x0000000000000000))
(check-synth)