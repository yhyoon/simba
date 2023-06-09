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

(constraint (= (deobfucated #x000000000385f14e #x000000001da2667a) #x0000498072122180))
(constraint (= (deobfucated #x0000000038b1d492 #x0000000000dc81dc) #x0c8e400082600244))
(constraint (= (deobfucated #x000000002f5a9882 #x0000000033c89996) #x0082640d42028200))
(constraint (= (deobfucated #x0000000000077a1c #x000000000a34419d) #x000000350342a110))
(constraint (= (deobfucated #x0000000013f39eb9 #x000000001645e471) #x000e0126009a01a1))
(constraint (= (deobfucated #x0000000037071fe4 #x0000000022b8f97d) #x0b40080212210310))
(constraint (= (deobfucated #x0000000021a24dd9 #x000000002aa1670a) #x0062246890500091))
(constraint (= (deobfucated #x000000001aaee618 #x0000000010a0d473) #x02c3802247400040))
(constraint (= (deobfucated #x0000000027880172 #x000000000db39dee) #x060000a200221440))
(constraint (= (deobfucated #x0000000022f49135 #x000000002dcb6f15) #x04c4c00121240431))
(constraint (= (deobfucated #x0000000020f65c54 #x0000000002717955) #x043a040a10043110))
(constraint (= (deobfucated #x00000000200e5e77 #x000000003b4ccdb2) #x0003802404dd0001))
(constraint (= (deobfucated #x00000000291dccb7 #x0000000004536cde) #x06880908012a22c1))
(constraint (= (deobfucated #x000000001695a997 #x0000000021f239e1) #x017e00a082149611))
(constraint (= (deobfucated #x000000000ed4d43d #x0000000012b7c5ea) #x0081a02680dd0081))
(constraint (= (deobfucated #x000000000aac8211 #x000000000ccc45f7) #x0050266018ac4101))
(constraint (= (deobfucated #x0000000031d6dee2 #x00000000177a491a) #x0990c4238104a100))
(constraint (= (deobfucated #x0000000011edd85d #x0000000015ab7c3f) #x000062b60d0f1041))
(constraint (= (deobfucated #x00000000166ab325 #x0000000033853a53) #x01a0814134000311))
(constraint (= (deobfucated #x000000000438ef0b #x0000000033a63edb) #x0010542108050219))
(check-synth)