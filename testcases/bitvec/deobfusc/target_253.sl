(set-logic BV)

(synth-fun deobfucated ( (b (BitVec 64))  (d (BitVec 64))  ) (BitVec 64)
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
				b d
			)
		)
	)
)

(constraint (= (deobfucated #x000000001f00e868 #x00000000019fbae9) #xffce455dddeeff67))
(constraint (= (deobfucated #x000000000fb4650a #x000000002219d9f3) #xf9ea500bf7fe58b9))
(constraint (= (deobfucated #x00000000161b3607 #x00000000095ccd5a) #xfedb2133ee32945c))
(constraint (= (deobfucated #x000000003b454fa2 #x0000000028b15cba) #xfcd40a094cc01fd4))
(constraint (= (deobfucated #x000000001c7558e7 #x0000000014ff522a) #xff4cb2e9d49c422c))
(constraint (= (deobfucated #x000000002ca54a49 #x0000000002577f70) #xff920fe71e8d04a2))
(constraint (= (deobfucated #x000000001a6afafc #x000000001a4786d9) #xfffb54af0f095c9b))
(constraint (= (deobfucated #x000000001ef5f24f #x000000002087c25b) #xf8109c5da859a582))
(constraint (= (deobfucated #x000000002a80be96 #x0000000006f516e5) #xfecaad798b38ec4d))
(constraint (= (deobfucated #x0000000036b86116 #x000000001cd7dc19) #xfb37fefed67567b5))
(constraint (= (deobfucated #x0000000038785ecb #x0000000039bca836) #xff99d73318829c38))
(constraint (= (deobfucated #x00000000264448d0 #x000000001266fca3) #xfc409608f4fc7867))
(constraint (= (deobfucated #x000000001251362e #x000000000367fca2) #xffc55d982e406fc4))
(constraint (= (deobfucated #x00000000068259a3 #x000000002c14a491) #xf8aa9d4ed36341f4))
(constraint (= (deobfucated #x00000000399ec75d #x00000000187418c1) #xfcc29954e9845a1e))
(constraint (= (deobfucated #x0000000017d88b5f #x00000000309182ab) #xf88bf9b677a588c2))
(constraint (= (deobfucated #x000000002ac7d9a0 #x000000003ac37cda) #xfc52b728c185b15c))
(constraint (= (deobfucated #x0000000024472d3e #x0000000021ec0c70) #xff3fb6ac0638205c))
(constraint (= (deobfucated #x0000000010394d91 #x000000002b889bd2) #xf5d94633673e472c))
(constraint (= (deobfucated #x000000002227c0f2 #x000000000c482f8e) #xfdc5a8aaca60e71c))
(check-synth)