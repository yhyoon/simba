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

(constraint (= (deobfucated #x000000001c2374ea #x000000003a929895 #x000000002e6a1857) #x000000007e269dfb))
(constraint (= (deobfucated #x000000000130201f #x000000000e434181 #x000000003b7c6625) #x0000000007706020))
(constraint (= (deobfucated #x000000002c20b7b3 #x000000000c7b3b90 #x0000000024c8a9d6) #x0000000038d8d243))
(constraint (= (deobfucated #x0000000021e4d15c #x000000002455cdea #x00000000191ed62e) #x00000000626e1b4e))
(constraint (= (deobfucated #x000000000eb04a84 #x000000000d63e11c #x00000000195a9257) #x0000000018364ab0))
(constraint (= (deobfucated #x000000000f8cf6d9 #x0000000006692927 #x0000000021f6b0ff) #x0000000015bf2826))
(constraint (= (deobfucated #x000000002dede1f0 #x0000000032461c3e #x00000000107ecd5c) #x000000006277f634))
(constraint (= (deobfucated #x0000000012161cd9 #x000000001dbbc082 #x0000000000089b5a) #x0000000032519ddb))
(constraint (= (deobfucated #x000000002d759839 #x0000000023a86dcb #x000000002d5e2fb0) #x00000000501e0b4f))
(constraint (= (deobfucated #x000000002532fdfd #x00000000383db355 #x0000000021e10896) #x00000000456c0213))
(constraint (= (deobfucated #x00000000303eb188 #x0000000004d61757 #x000000003016fa0e) #x0000000031d0d99a))
(constraint (= (deobfucated #x000000003a958d9c #x000000002ca6b7f8 #x0000000030679414) #x000000006b3a419c))
(constraint (= (deobfucated #x00000000390d26a9 #x000000002a8b6df5 #x000000001cd72086) #x00000000619a98ef))
(constraint (= (deobfucated #x000000002def3979 #x000000000e871fc5 #x00000000100dbd0c) #x0000000032f245ff))
(constraint (= (deobfucated #x0000000023980e30 #x000000000bef11b0 #x000000000cad4be1) #x00000000270b0e70))
(constraint (= (deobfucated #x0000000009bae6ad #x0000000033b91614 #x000000000a95ef23) #x000000000f7af8d5))
(constraint (= (deobfucated #x000000002fa546ef #x0000000039521bd5 #x000000002143bb76) #x0000000070e77185))
(constraint (= (deobfucated #x000000000ba3e46d #x000000003565cd61 #x000000001a956c4f) #x000000004468b8ee))
(constraint (= (deobfucated #x000000001132d1f3 #x00000000218487df #x000000001b4cd296) #x0000000012375b87))
(constraint (= (deobfucated #x000000002683a1a7 #x00000000337c553a #x00000000090cd437) #x0000000069f7f7d1))
(check-synth)