(set-logic BV)

(synth-fun deobfucated ( (a (BitVec 64))  ) (BitVec 64)
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
				a
			)
		)
	)
)

(constraint (= (deobfucated #x0000000030be1ac6) #x0000000030be1ac5))
(constraint (= (deobfucated #x0000000001b2fddb) #x0000000001b2fdda))
(constraint (= (deobfucated #x0000000016f96963) #x0000000016f96962))
(constraint (= (deobfucated #x000000000834d13f) #x000000000834d13e))
(constraint (= (deobfucated #x0000000021ae6f9d) #x0000000021ae6f9c))
(constraint (= (deobfucated #x000000002990b462) #x000000002990b461))
(constraint (= (deobfucated #x000000003b5a8528) #x000000003b5a8527))
(constraint (= (deobfucated #x000000001f247c7b) #x000000001f247c7a))
(constraint (= (deobfucated #x000000000a37cf74) #x000000000a37cf73))
(constraint (= (deobfucated #x000000000beb0527) #x000000000beb0526))
(constraint (= (deobfucated #x0000000011281376) #x0000000011281375))
(constraint (= (deobfucated #x0000000029d8ccec) #x0000000029d8cceb))
(constraint (= (deobfucated #x0000000039aca6d6) #x0000000039aca6d5))
(constraint (= (deobfucated #x00000000035b461c) #x00000000035b461b))
(constraint (= (deobfucated #x000000000162cb19) #x000000000162cb18))
(constraint (= (deobfucated #x0000000032b0ae51) #x0000000032b0ae50))
(constraint (= (deobfucated #x000000001dde762e) #x000000001dde762d))
(constraint (= (deobfucated #x000000003a283aaf) #x000000003a283aae))
(constraint (= (deobfucated #x000000000522434f) #x000000000522434e))
(constraint (= (deobfucated #x0000000021422a29) #x0000000021422a28))
(check-synth)