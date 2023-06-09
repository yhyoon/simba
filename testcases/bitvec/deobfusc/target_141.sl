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

(constraint (= (deobfucated #x0000000013f2aaff) #xfe7214967a5eff00))
(constraint (= (deobfucated #x000000000e5ce86f) #xff31b4dbf77277b0))
(constraint (= (deobfucated #x000000000930a607) #xffab8b14da824dc8))
(constraint (= (deobfucated #x0000000003a7e791) #xfff2a272aafd184e))
(constraint (= (deobfucated #x0000000017c6adca) #xfdcab2947e4bf152))
(constraint (= (deobfucated #x0000000018d97a1c) #xfd96805a9a9036f4))
(constraint (= (deobfucated #x000000002d73c897) #xf7ee171d385a7e78))
(constraint (= (deobfucated #x000000001a9fd717) #xfd3b24826a298cf8))
(constraint (= (deobfucated #x00000000122e0259) #xfeb57f66b1d07f56))
(constraint (= (deobfucated #x0000000037c0f9e9) #xf3db832627481006))
(constraint (= (deobfucated #x0000000032a2f833) #xf5fbef4d3073dde4))
(constraint (= (deobfucated #x000000002144538a) #xfbad5039ce296a12))
(constraint (= (deobfucated #x000000000893801e) #xffb67301b5fe7c66))
(constraint (= (deobfucated #x000000002ea369c4) #xf780ddad9a16c82c))
(constraint (= (deobfucated #x0000000001099f6c) #xfffeec648e293504))
(constraint (= (deobfucated #x000000003af83f66) #xf26a928ad8549c3e))
(constraint (= (deobfucated #x000000000665ae1e) #xffd71373bb829a66))
(constraint (= (deobfucated #x0000000017cca53f) #xfdc996b6f1211f40))
(constraint (= (deobfucated #x000000000020d00e) #xfffffbcb5349ef36))
(constraint (= (deobfucated #x00000000328f335a) #xf603bfd65da83702))
(check-synth)