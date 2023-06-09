(set-logic BV)

(synth-fun deobfucated ( (c (BitVec 64))  (b (BitVec 64))  ) (BitVec 64)
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
				c b
			)
		)
	)
)

(constraint (= (deobfucated #x000000000eac72e3 #x00000000211e309e) #xfd436c5384804960))
(constraint (= (deobfucated #x0000000037e22255 #x00000000154c304d) #xf3ca6b654a12cd12))
(constraint (= (deobfucated #x000000002052f2a5 #x000000001802be4a) #xf8e36029a4f541b4))
(constraint (= (deobfucated #x000000001390b708 #x0000000023cf2701) #xfc09127cd410d8b6))
(constraint (= (deobfucated #x0000000011499adf #x000000000171832d) #xfed1e664348234d2))
(constraint (= (deobfucated #x000000000013a488 #x000000000cc4e036) #xffff03b8e02a0309))
(constraint (= (deobfucated #x0000000026e3f743 #x00000000283040cd) #xf8ddf988d3802b12))
(constraint (= (deobfucated #x0000000020366ce8 #x00000000106d1ef5) #xf9e5c099c9802002))
(constraint (= (deobfucated #x00000000182de110 #x000000003b7a26f5) #xfa6158760400090a))
(constraint (= (deobfucated #x000000000abb3611 #x0000000004d8d2d3) #xff5f33245103092c))
(constraint (= (deobfucated #x0000000010e19f70 #x000000002efcf59b) #xfbd89b8701000824))
(constraint (= (deobfucated #x0000000014af2324 #x0000000039b03da4) #xfb02d0d0c24b804b))
(constraint (= (deobfucated #x000000001ce8ca2e #x00000000325593c0) #xf8e2f42305282c3b))
(constraint (= (deobfucated #x0000000008871a6a #x000000002223d1df) #xfe943e344c8c0220))
(constraint (= (deobfucated #x000000002878b05b #x000000000639766e) #xf8a7084c39860090))
(constraint (= (deobfucated #x000000002bfe0592 #x000000000039a51b) #xf870669391040280))
(constraint (= (deobfucated #x00000000091653d3 #x000000003a167a54) #xfde70e5dc4c1008a))
(constraint (= (deobfucated #x000000001ab25682 #x000000002cc85cac) #xf96eb30440112303))
(constraint (= (deobfucated #x0000000015dc12e1 #x00000000205bee3a) #xfb664f9d0f241144))
(constraint (= (deobfucated #x0000000026af9992 #x00000000207f7fd8) #xfa1b3fa080008023))
(check-synth)