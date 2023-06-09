(set-logic BV)

(synth-fun deobfucated ( (c (BitVec 64))  (a (BitVec 64))  ) (BitVec 64)
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
				c a
			)
		)
	)
)

(constraint (= (deobfucated #x0000000026b0502f #x0000000017ad1dd9) #xff63239ebffc737f))
(constraint (= (deobfucated #x0000000023d5e18c #x0000000017a19031) #xffad2714fff80000))
(constraint (= (deobfucated #x000000002dc8a364 #x0000000028021d8f) #xf9bfab392dd9fbe4))
(constraint (= (deobfucated #x0000000003da4222 #x0000000016b16b81) #xffc5d382c7fb0000))
(constraint (= (deobfucated #x0000000030f62a97 #x0000000012441eec) #xfed6e338f4fefee0))
(constraint (= (deobfucated #x0000000012828725 #x0000000016d1199b) #xfe59e38f7697cf65))
(constraint (= (deobfucated #x000000000ed8cb29 #x0000000013c039dd) #xffc9aeae6efdfb3b))
(constraint (= (deobfucated #x0000000023a6bfcd #x000000002a0aaab3) #xfa6a253ebfffbfcd))
(constraint (= (deobfucated #x0000000032727fa0 #x000000001bf051f1) #xfdfcd830b67fffe0))
(constraint (= (deobfucated #x00000000318cd4c7 #x000000000272d50b) #xfffffdf8f1bef4df))
(constraint (= (deobfucated #x0000000035cd8e25 #x0000000022a4f297) #xfb997307bdff9f2d))
(constraint (= (deobfucated #x000000002d84a4e2 #x0000000029bac9cb) #xf93c234cbf8db4ea))
(constraint (= (deobfucated #x000000001155fbe7 #x000000000e514a4d) #xfffb7420337fffff))
(constraint (= (deobfucated #x000000001f0e77f1 #x00000000061a08fe) #xffdb26bfffaff800))
(constraint (= (deobfucated #x0000000001f5dd95 #x000000003051f843) #xfff08d4b19f7ffbd))
(constraint (= (deobfucated #x000000003739427a #x0000000027cc927e) #xf9ee96e7bf7d73fc))
(constraint (= (deobfucated #x00000000014483f7 #x000000000ad2863c) #xfffd45dd5756c400))
(constraint (= (deobfucated #x0000000031352d8d #x000000000fdeb1b6) #xffeee1d4b53fedb0))
(constraint (= (deobfucated #x0000000014ba80e0 #x00000000056dc302) #xffe96d169ebf0000))
(constraint (= (deobfucated #x000000001fbbed25 #x0000000015414702) #xfe418a30fffbfe00))
(check-synth)