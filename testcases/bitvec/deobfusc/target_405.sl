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

(constraint (= (deobfucated #x0000000025c38559 #x0000000032682fc9) #x000000007edfdfbb))
(constraint (= (deobfucated #x0000000011124c4c #x000000000286633a) #xfffffffff7fef7fc))
(constraint (= (deobfucated #x0000000007043963 #x000000000377379e) #xffffffffffefffbd))
(constraint (= (deobfucated #x00000000298b7d2c #x000000000f32dab4) #xfffffffffeffdf7c))
(constraint (= (deobfucated #x000000000cd7e0bc #x000000001adb0ee0) #x000000003dfafddc))
(constraint (= (deobfucated #x00000000259ae5b8 #x000000002df8a10e) #x000000007ff79edc))
(constraint (= (deobfucated #x000000002a05e63b #x0000000016587d46) #xfffffffffebefecd))
(constraint (= (deobfucated #x000000000b3a1b68 #x0000000002577a74) #xfffffffffddef5f8))
(constraint (= (deobfucated #x000000000fc9150d #x0000000000eccfd0) #xfffffffff1dfffbf))
(constraint (= (deobfucated #x00000000381faee1 #x000000000386a680) #xffffffffffe6557f))
(constraint (= (deobfucated #x0000000038fed9cc #x0000000022325316) #xffffffffdf312efc))
(constraint (= (deobfucated #x0000000026f219cd #x0000000018f2ae43) #xfffffffffff77e37))
(constraint (= (deobfucated #x000000003b88a800 #x00000000369845de) #xffffffffffb7fbbc))
(constraint (= (deobfucated #x0000000022d31614 #x000000003505cd85) #x000000006ffffffe))
(constraint (= (deobfucated #x000000001109bd02 #x0000000021937016) #x00000000733fef2e))
(constraint (= (deobfucated #x0000000011b3027a #x00000000365a1e02) #x000000007efd3dfe))
(constraint (= (deobfucated #x000000000abab40a #x00000000310644ad) #x000000007fcdfd5e))
(constraint (= (deobfucated #x000000003805aa8f #x000000002a8358f4) #xfffffffffdfff7f3))
(constraint (= (deobfucated #x0000000030aef260 #x0000000020d60275) #xffffffffd1f5f6ea))
(constraint (= (deobfucated #x000000003af20e05 #x000000002c08cff6) #xffffffffff1f9fef))
(check-synth)