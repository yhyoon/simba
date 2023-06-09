(set-logic BV)

(synth-fun deobfucated ( (e (BitVec 64))  (a (BitVec 64))  ) (BitVec 64)
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
				e a
			)
		)
	)
)

(constraint (= (deobfucated #x00000000363ae46f #x000000001d3a50ff) #xfffffffff6ffef6f))
(constraint (= (deobfucated #x0000000031edbea6 #x000000003523e081) #xfffffffffbfdbfff))
(constraint (= (deobfucated #x000000003a72bc27 #x00000000313371b0) #xfffffffffefebe70))
(constraint (= (deobfucated #x0000000006771e6a #x0000000000bf3aaf) #xffffffffff77df79))
(constraint (= (deobfucated #x000000002685a3cb #x000000002b82d55f) #xfffffffff6fdabeb))
(constraint (= (deobfucated #x00000000182d396c #x000000003263b265) #xffffffffddbd7df9))
(constraint (= (deobfucated #x0000000027e22953 #x0000000002a1bb0a) #xfffffffffffe6df4))
(constraint (= (deobfucated #x0000000018ff3eec #x000000000b37e9d9) #xfffffffffcff3eed))
(constraint (= (deobfucated #x000000003b8484df #x000000001165cf39) #xffffffffff9eb4df))
(constraint (= (deobfucated #x0000000011378d05 #x00000000255202d4) #xffffffffdbbffd28))
(constraint (= (deobfucated #x0000000028faba49 #x000000001525aa8b) #xffffffffeafaff7d))
(constraint (= (deobfucated #x000000001015bd84 #x000000002857b5ea) #xffffffffd7bdff97))
(constraint (= (deobfucated #x00000000343b14e6 #x000000001d14909e) #xfffffffff6fb7fe7))
(constraint (= (deobfucated #x0000000015306017 #x00000000373c23ab) #xffffffffddf3fc57))
(constraint (= (deobfucated #x0000000019a20672 #x000000000b29d562) #xfffffffffdf62eff))
(constraint (= (deobfucated #x000000002709ce47 #x000000000cda9eb3) #xfffffffff72def4f))
(constraint (= (deobfucated #x000000000368cfa1 #x0000000029411c90) #xffffffffd7feeff0))
(constraint (= (deobfucated #x0000000036a3d4fb #x000000001c33a3eb) #xfffffffff7efdcff))
(constraint (= (deobfucated #x0000000001343008 #x000000001340b0e2) #xffffffffedbf7f1b))
(constraint (= (deobfucated #x0000000000caf126 #x000000001bd4244f) #xffffffffe4ebfbb5))
(check-synth)