(set-logic BV)

(synth-fun deobfucated ( (e (BitVec 64))  (c (BitVec 64))  (b (BitVec 64))  ) (BitVec 64)
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
				e c b
			)
		)
	)
)

(constraint (= (deobfucated #x000000003589bbe8 #x000000000ec7eae7 #x000000001ad99099) #x00f4700373f5bab8))
(constraint (= (deobfucated #x000000002d6c8155 #x000000000c4d873b #x0000000017176edc) #x003db4de4d5c5f5c))
(constraint (= (deobfucated #x000000001a7e648b #x00000000251eff49 #x00000000187e782f) #x038d3b1db5fe5823))
(constraint (= (deobfucated #x00000000267c3f40 #x00000000152c5a9d #x0000000027bdd384) #x03298d6ad585a700))
(constraint (= (deobfucated #x000000001129d32f #x00000000399786ef #x000000001b55fe64) #x03d378d3cbee079c))
(constraint (= (deobfucated #x00000000064644f8 #x0000000018424e4d #x0000000020132acb) #x0000309790672c28))
(constraint (= (deobfucated #x000000001de7395f #x000000002fec4872 #x000000000e6d5718) #x0251fed11bf05cb0))
(constraint (= (deobfucated #x000000003b507b32 #x0000000005b014ca #x00000000164905f8) #x0067cd822798afe0))
(constraint (= (deobfucated #x000000002343541a #x000000003a9e0c88 #x0000000017890fad) #x00b015aff1aa8440))
(constraint (= (deobfucated #x0000000015858b22 #x000000002fe61578 #x0000000017dbdaa1) #x04061c8badcd5f00))
(constraint (= (deobfucated #x000000002df9eece #x000000002e95c3dc #x00000000284ae85a) #x0754aafea6a9fd98))
(constraint (= (deobfucated #x000000000ba630c9 #x0000000037670d98 #x00000000141f500d) #x00014fe2b508fa58))
(constraint (= (deobfucated #x000000002b2b1ba3 #x0000000014db5517 #x000000000d9a7b87) #x00bc88ccf01bf7c5))
(constraint (= (deobfucated #x000000002b195ddb #x000000000125948e #x0000000023fb39f7) #x0028401889594f0a))
(constraint (= (deobfucated #x00000000003c6490 #x000000000efe9bf7 #x0000000007ea04c8) #x0002580bd855d780))
(constraint (= (deobfucated #x000000000dc03585 #x000000002985d761 #x000000000a843fc0) #x0160fa543102c580))
(constraint (= (deobfucated #x0000000009fdb3c2 #x0000000021cc65f1 #x0000000027dc173e) #x003eda8ffb45aee2))
(constraint (= (deobfucated #x000000003507a1cc #x000000002495d475 #x0000000024a7ab25) #x052628fc1027e6d4))
(constraint (= (deobfucated #x000000001b48d9c0 #x000000002abfd412 #x0000000021ec38b6) #x0036c9df12dbb900))
(constraint (= (deobfucated #x00000000005f3784 #x000000000f265e6d #x0000000002aa2cc5) #x000099a8e5520434))
(check-synth)