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

(constraint (= (deobfucated #x00000000298ba388 #x000000000f70243e) #x00000000411706ff))
(constraint (= (deobfucated #x000000002f10ad93 #x000000000e9ad547) #x000000004200511f))
(constraint (= (deobfucated #x000000001da25d83 #x0000000027a80c50) #x000000003004a305))
(constraint (= (deobfucated #x00000000169fc7cf #x000000000791fcbb) #x00000000201c0687))
(constraint (= (deobfucated #x000000002b19d84f #x000000000e7b4eab) #x0000000042012087))
(constraint (= (deobfucated #x0000000019bd7bfc #x000000002db43180) #x00000000201294f7))
(constraint (= (deobfucated #x000000000c6a264a #x00000000119bb977) #x0000000018c00c0f))
(constraint (= (deobfucated #x000000001adc4644 #x000000001d95462c) #x000000000490007f))
(constraint (= (deobfucated #x0000000037a7cbbb #x000000003959d12b) #x000000000d4c151f))
(constraint (= (deobfucated #x000000001f8b7948 #x00000000316b8b0e) #x000000001d00e07f))
(constraint (= (deobfucated #x0000000019763fdb #x000000002a4b9440) #x0000000022685735))
(constraint (= (deobfucated #x0000000031f3bb80 #x000000001989c888) #x0000000040e465ff))
(constraint (= (deobfucated #x000000002b136bec #x000000000c17c605) #x00000000460053cf))
(constraint (= (deobfucated #x000000001f29b380 #x000000002b197423) #x00000000284106ff))
(constraint (= (deobfucated #x0000000003f2f335 #x00000000238babd2) #x0000000000e0a049))
(constraint (= (deobfucated #x00000000205d8964 #x0000000019c70cbb) #x0000000040310287))
(constraint (= (deobfucated #x0000000032224b50 #x0000000014cf6399) #x000000004440107f))
(constraint (= (deobfucated #x0000000023041ce7 #x000000002f1b555f) #x000000000008113f))
(constraint (= (deobfucated #x000000000112b36e #x000000000438ea34) #x0000000002042293))
(constraint (= (deobfucated #x000000001d8212a6 #x0000000035963462) #x0000000010000507))
(check-synth)