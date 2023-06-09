(set-logic BV)

(synth-fun deobfucated ( (a (BitVec 64))  (c (BitVec 64))  (b (BitVec 64))  ) (BitVec 64)
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
				a c b
			)
		)
	)
)

(constraint (= (deobfucated #x0000000033236892 #x000000002c89b8f5 #x000000000e5d058d) #x08e598de5cf3be44))
(constraint (= (deobfucated #x0000000039f4f758 #x000000001ad08821 #x000000003709a641) #x061216f9bca30c36))
(constraint (= (deobfucated #x000000002092575d #x000000000b052cb5 #x0000000028e2aa3a) #x0166f24cc9ab6e7f))
(constraint (= (deobfucated #x00000000048ce5d9 #x000000003058e094 #x000000003b51d91c) #x00dbff85a67338ef))
(constraint (= (deobfucated #x000000002a02a125 #x00000000293d56cd #x0000000024739e4d) #x06c47cadf471a66d))
(constraint (= (deobfucated #x000000000a4e1672 #x000000000a8ee4b3 #x00000000038239ad) #x006ccd65ac5dc40a))
(constraint (= (deobfucated #x0000000018b0c954 #x00000000175f39d8 #x00000000011e5594) #x024111456376ef03))
(constraint (= (deobfucated #x00000000221bd7a8 #x0000000039bc96d6 #x000000001e5d70f5) #x07b1538fa4ff4098))
(constraint (= (deobfucated #x000000000cc435eb #x0000000031b82dc1 #x0000000039a5cd2b) #x027abda0e0f318c1))
(constraint (= (deobfucated #x0000000023de611c #x0000000009377c22 #x000000002fb9b89f) #x014a97957c298908))
(constraint (= (deobfucated #x000000000f06b675 #x000000000d58eaac #x000000002e92bea8) #x00c88f58cb5b7637))
(constraint (= (deobfucated #x000000002b9eef10 #x000000002769fd4b #x000000002c75292a) #x06b745c4781f24c4))
(constraint (= (deobfucated #x000000002d07972c #x0000000010b2f191 #x00000000312d9a4f) #x02eff337b28af034))
(constraint (= (deobfucated #x00000000092f67f1 #x000000000f28aed6 #x0000000002eb6b90) #x008b3cc54d055ea3))
(constraint (= (deobfucated #x0000000032ebc742 #x000000000b1db6fc #x00000000055462fe) #x02360aab2766e609))
(constraint (= (deobfucated #x000000002d257e3d #x00000000284885ab #x0000000012daa604) #x071aa5d79113a411))
(constraint (= (deobfucated #x000000003b0c9725 #x000000002eb2d550 #x0000000015c97ee3) #x0ac5831d9490fb7c))
(constraint (= (deobfucated #x000000001ff3e3ca #x000000001d488de7 #x00000000308d320b) #x03a7af1c219572aa))
(constraint (= (deobfucated #x00000000022408e6 #x00000000025b681a #x0000000015b7573e) #x00050bbfc6f72865))
(constraint (= (deobfucated #x000000000c9fb9bd #x000000002358e599 #x00000000049641df) #x01be389f3b4af72b))
(check-synth)