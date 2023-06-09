(set-logic BV)

(synth-fun deobfucated ( (e (BitVec 64))  (a (BitVec 64))  (b (BitVec 64))  ) (BitVec 64)
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
				e a b
			)
		)
	)
)

(constraint (= (deobfucated #x00000000246026dd #x0000000019939703 #x000000000575d4e9) #xffffffffc2080601))
(constraint (= (deobfucated #x0000000035cc1246 #x000000001c63eee2 #x000000000cbeb195) #xffffffffb1bffdc7))
(constraint (= (deobfucated #x000000001d4cd724 #x0000000020a101c6 #x0000000019597bd2) #xffffffffc2020006))
(constraint (= (deobfucated #x00000000144f03e6 #x00000000093807e8 #x000000002634d56c) #xffffffffc0782592))
(constraint (= (deobfucated #x0000000001e32729 #x00000000204b43ed #x000000000e5acff9) #xffffffffd0031003))
(constraint (= (deobfucated #x000000001f3634c9 #x0000000017c0386b #x0000000029c64b88) #xffffffffaa094fd4))
(constraint (= (deobfucated #x0000000036c5f679 #x0000000015708be8 #x00000000135de330) #xffffffffc401ffbf))
(constraint (= (deobfucated #x000000002b0554db #x0000000013cadd56 #x000000000aa042c2) #xffffffffc3100c11))
(constraint (= (deobfucated #x000000003a0a3089 #x000000001fd7dab5 #x000000001ee4fc3e) #xffffffffbffe00c0))
(constraint (= (deobfucated #x0000000014ee4629 #x0000000001ac0e03 #x000000003b8a712f) #xffffffffbfed7ad1))
(constraint (= (deobfucated #x000000001678f991 #x000000000542805b #x0000000007ef0d63) #xffffffffe7ff81f5))
(constraint (= (deobfucated #x0000000010de6152 #x000000000d6a4576 #x000000001b272c32) #xffffffffdfb8514a))
(constraint (= (deobfucated #x0000000006268800 #x000000003156275d #x000000001416701f) #xffffffffc88900a1))
(constraint (= (deobfucated #x00000000249c12fa #x0000000033d35d59 #x000000001ad70211) #xffffffffa0208fbd))
(constraint (= (deobfucated #x00000000264c6bea #x000000003283ca13 #x0000000005fefed7) #xffffffffa6000001))
(constraint (= (deobfucated #x0000000017aae71b #x00000000391872df #x0000000022f27c6f) #xffffffffaefcfdf1))
(constraint (= (deobfucated #x000000002d72dfc6 #x000000000d463b59 #x000000002579de2b) #xffffffffca7dfec1))
(constraint (= (deobfucated #x00000000317e0057 #x00000000279c611e #x000000001bc6ba38) #xffffffff9fe9047b))
(constraint (= (deobfucated #x0000000000d199cf #x000000000605e5ad #x000000002f4c376b) #xffffffffd0207f8d))
(constraint (= (deobfucated #x000000002f849886 #x000000000f3b0563 #x000000000f7ce673) #xffffffffd0000009))
(check-synth)