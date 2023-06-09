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

(constraint (= (deobfucated #x0000000020d6e9a4 #x000000001d12dbbd) #xffffffffffed365d))
(constraint (= (deobfucated #x000000001bca9316 #x000000001edc188b) #xffffffffe537efff))
(constraint (= (deobfucated #x00000000102f5474 #x0000000029e0194b) #xffffffffffdfefc1))
(constraint (= (deobfucated #x0000000027053adb #x000000002ea23d80) #xffffffffd9ffc781))
(constraint (= (deobfucated #x000000000f41afdf #x000000001014e2b8) #xffffffffffff5d69))
(constraint (= (deobfucated #x000000003ae0571c #x000000001b671c25) #xffffffffe59febfd))
(constraint (= (deobfucated #x0000000016503247 #x0000000005834edc) #xfffffffffbfffdbd))
(constraint (= (deobfucated #x000000001f383294 #x0000000019e5a70f) #xffffffffe6dfddfd))
(constraint (= (deobfucated #x0000000010e3a419 #x00000000260d02b1) #xfffffffffffefff0))
(constraint (= (deobfucated #x000000000b67351a #x000000001cbf68a3) #xfffffffff7d8dfff))
(constraint (= (deobfucated #x0000000002e9d3c1 #x0000000005788979) #xffffffffff977ec0))
(constraint (= (deobfucated #x0000000017b21bf0 #x00000000260b50eb) #xfffffffff9fdef21))
(constraint (= (deobfucated #x0000000026035781 #x000000000d31c37a) #xfffffffffbfebd01))
(constraint (= (deobfucated #x0000000018edf338 #x0000000033dc64ed) #xffffffffef339fd9))
(constraint (= (deobfucated #x0000000030e9b187 #x000000002b118e12) #xffffffffdffe7fff))
(constraint (= (deobfucated #x0000000030bebab1 #x000000000ef6a927) #xffffffffff4957e0))
(constraint (= (deobfucated #x0000000022abc0ac #x000000003005b4d6) #xffffffffdffe7f7d))
(constraint (= (deobfucated #x0000000030a957e6 #x0000000026a55696) #xffffffffdf5ea97b))
(constraint (= (deobfucated #x000000000437fa29 #x000000001ad8bd9b) #xffffffffffef47f8))
(constraint (= (deobfucated #x000000001cd18d8e #x0000000026492e6f) #xfffffffffbbef3f3))
(check-synth)