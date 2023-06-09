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

(constraint (= (deobfucated #x000000000f6597ed #x00000000249df4c1) #xfffffffff99b790f))
(constraint (= (deobfucated #x00000000278cc29f #x0000000036d89a22) #xffffffffdbfe7e67))
(constraint (= (deobfucated #x0000000027a5cfac #x0000000023cc1785) #xfa74b8d55ca0bdd5))
(constraint (= (deobfucated #x0000000004ca10cd #x000000003831260a) #x00000000018700f5))
(constraint (= (deobfucated #x000000001adab270 #x000000000473687a) #xff887a0247cda5ca))
(constraint (= (deobfucated #x000000000a2af815 #x000000001d370b90) #xfffffffffeff691b))
(constraint (= (deobfucated #x000000000b3540eb #x000000002cb8a7fa) #xffffffffff50449f))
(constraint (= (deobfucated #x00000000024f3e71 #x000000000b26d5e2) #xfffffffffe056d11))
(constraint (= (deobfucated #x0000000013b3f533 #x000000001f6e5820) #xfffffffffcd69c6d))
(constraint (= (deobfucated #x000000003a69fc72 #x0000000022bc50b6) #xf812f438bdd9b014))
(constraint (= (deobfucated #x000000001111ead2 #x000000000d3290fe) #xff1eb7e863f01f54))
(constraint (= (deobfucated #x00000000162a884d #x000000001be51c05) #xffffffffeffe022f))
(constraint (= (deobfucated #x00000000317e68dc #x0000000032432266) #xfffffffffee9d772))
(constraint (= (deobfucated #x00000000259c878a #x00000000295c7988) #xffffffffe02fbfae))
(constraint (= (deobfucated #x0000000002a14845 #x0000000023b53b85) #x000000001d5f80e7))
(constraint (= (deobfucated #x000000001b56c4a5 #x000000002fa45dcc) #x000000000103185f))
(constraint (= (deobfucated #x0000000030e3e266 #x000000001e7ab98a) #xfa2ddb6eecad54a4))
(constraint (= (deobfucated #x0000000007322ffe #x0000000033573d0a) #x0000000004e004f4))
(constraint (= (deobfucated #x0000000004ad796e #x000000000a8705cd) #x000000000003431f))
(constraint (= (deobfucated #x000000002956f6d9 #x00000000219537a1) #xfa93b1948037b9ff))
(check-synth)