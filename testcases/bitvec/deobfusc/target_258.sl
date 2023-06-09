(set-logic BV)

(synth-fun deobfucated ( (c (BitVec 64))  (b (BitVec 64))  (d (BitVec 64))  ) (BitVec 64)
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
				c b d
			)
		)
	)
)

(constraint (= (deobfucated #x000000001255e5dc #x0000000013855686 #x00000000281df656) #xffffffffea3fefde))
(constraint (= (deobfucated #x000000001afa5365 #x0000000007663d02 #x00000000313053c3) #xffffffffe9d9ffba))
(constraint (= (deobfucated #x000000003696f9b5 #x0000000003e0d1ff #x000000000926f644) #xff2c4a30ed710371))
(constraint (= (deobfucated #x00000000276ea6db #x0000000007126e1a #x0000000031531cde) #xfffffffff6bf89fd))
(constraint (= (deobfucated #x000000001616cc60 #x0000000010b66583 #x000000003a6e5d83) #xfffffffffba9fefd))
(constraint (= (deobfucated #x0000000021336696 #x000000002000addb #x000000000c876a4e) #xfbd97ca11cbffc49))
(constraint (= (deobfucated #x00000000393bd619 #x000000001266805f #x000000000c512f8b) #xfbe2e067ecebaf8e))
(constraint (= (deobfucated #x0000000029c1bcfe #x000000000b5e93db #x000000000374f71f) #xfe253f9fe6cccddf))
(constraint (= (deobfucated #x0000000013bba218 #x0000000017b769ea #x0000000028de9137) #xffffffffeadd16f3))
(constraint (= (deobfucated #x000000003b0f8c28 #x000000003035a7ed #x0000000023e3ff66) #xf4e0b4c2df2bccc3))
(constraint (= (deobfucated #x000000001e3f2066 #x00000000040ec3ee #x000000001ed144ae) #xffffffffff7dfbba))
(constraint (= (deobfucated #x0000000022352415 #x00000000196ac32d #x00000000074e04a0) #xfc9a8b649ee73f75))
(constraint (= (deobfucated #x000000000ad2caa1 #x0000000016e8a22f #x00000000221846f6) #xffffffffe8bb8fab))
(constraint (= (deobfucated #x0000000011b3abc3 #x000000003819eeb2 #x00000000393c34b7) #xffffffffd977770c))
(constraint (= (deobfucated #x000000001cc9faeb #x0000000027b6dd2f #x0000000015c95fd7) #xfb88aa4e5740bb14))
(constraint (= (deobfucated #x000000000f4d1aaa #x000000000f2f0689 #x0000000001dfc751) #xff17abe43d7dd35f))
(constraint (= (deobfucated #x000000002effc4aa #x000000002a4deee6 #x000000000ada1f7e) #xf83bbaf234a7b52e))
(constraint (= (deobfucated #x0000000024167537 #x000000001fb23f51 #x0000000034c964d9) #xffffffffef4d90fe))
(constraint (= (deobfucated #x0000000034d36683 #x000000001a9689ba #x00000000349bda80) #xfa83774d207ffe07))
(constraint (= (deobfucated #x000000002eaa26a0 #x000000000743ae9d #x0000000039dd4d9a) #xfffffffff4ccd967))
(check-synth)