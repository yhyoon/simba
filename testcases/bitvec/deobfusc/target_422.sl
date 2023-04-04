(set-logic BV)

(synth-fun deobfucated ( (e (BitVec 64))  (c (BitVec 64))  ) (BitVec 64)
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
				e c
			)
		)
	)
)

(constraint (= (deobfucated #x000000002fca727e #x000000003196ca60) #x0000000000000000))
(constraint (= (deobfucated #x00000000314caf37 #x00000000042cdc4c) #x0000000000000000))
(constraint (= (deobfucated #x000000002ed17a02 #x00000000379bf053) #x0000000000000000))
(constraint (= (deobfucated #x000000001bdf0dbb #x000000001193db38) #x0000000000000000))
(constraint (= (deobfucated #x0000000017eeddec #x0000000003d25316) #x0000000000000000))
(constraint (= (deobfucated #x000000001b1b1ed4 #x000000002cf79d70) #x0000000000000000))
(constraint (= (deobfucated #x000000000c906049 #x0000000039f9f53e) #x0000000000000000))
(constraint (= (deobfucated #x000000000e508417 #x000000001b88515d) #x0000000000000000))
(constraint (= (deobfucated #x000000000a4964b4 #x0000000039308026) #x0000000000000000))
(constraint (= (deobfucated #x0000000008ec2b85 #x00000000010f89a1) #x0000000000000000))
(constraint (= (deobfucated #x00000000362351ed #x000000002db1a8aa) #x0000000000000000))
(constraint (= (deobfucated #x00000000217b026a #x000000000ba48db0) #x0000000000000000))
(constraint (= (deobfucated #x000000001425c1e0 #x0000000010872901) #x0000000000000000))
(constraint (= (deobfucated #x000000001766f69c #x000000001b4bb8d7) #x0000000000000000))
(constraint (= (deobfucated #x000000002e66e876 #x0000000016897d3c) #x0000000000000000))
(constraint (= (deobfucated #x00000000028dc628 #x0000000033b2dc18) #x0000000000000000))
(constraint (= (deobfucated #x000000001a3a310a #x0000000014ed8ebe) #x0000000000000000))
(constraint (= (deobfucated #x000000001e862e3c #x000000000fdc235f) #x0000000000000000))
(constraint (= (deobfucated #x0000000038fd0fdf #x0000000015caabac) #x0000000000000000))
(constraint (= (deobfucated #x000000002d7421db #x0000000023c14d39) #x0000000000000000))
(check-synth)