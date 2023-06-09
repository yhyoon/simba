(set-logic BV)

(synth-fun deobfucated ( (e (BitVec 64))  (b (BitVec 64))  ) (BitVec 64)
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
				e b
			)
		)
	)
)

(constraint (= (deobfucated #x0000000028fa7afd #x000000002fac5cc8) #xf0bed258846a7555))
(constraint (= (deobfucated #x000000000fba9a54 #x000000001ff45a8f) #xfdf474cf08286c18))
(constraint (= (deobfucated #x0000000015c84cbf #x0000000009b25611) #xff72cefdd0d560b0))
(constraint (= (deobfucated #x0000000020dae0be #x000000002ced912e) #xfdd96246d75c3b5e))
(constraint (= (deobfucated #x0000000034000615 #x0000000003e1e87d) #xff390e63a718fc50))
(constraint (= (deobfucated #x000000002c933a3e #x000000002fd8ac4a) #xff5a78b3884fc9f2))
(constraint (= (deobfucated #x0000000039f6ff40 #x000000001c9b7630) #xfab7a8873661ae40))
(constraint (= (deobfucated #x000000000e0c1ae9 #x00000000060fc400) #xff8e67cf2bba86e9))
(constraint (= (deobfucated #x000000001ea7d080 #x000000000fc7b5b3) #xfee5438587168f08))
(constraint (= (deobfucated #x0000000028dd5408 #x000000001fb9ad48) #xf901f19b294219d8))
(constraint (= (deobfucated #x0000000037996bde #x000000000d2f5729) #xfd8f3af7e87473cc))
(constraint (= (deobfucated #x0000000010fe0a90 #x000000002f3ee397) #xf465086988a918a0))
(constraint (= (deobfucated #x000000001567a708 #x000000003580e1e9) #xf0a85dd94be99eb0))
(constraint (= (deobfucated #x000000002c4cfdb7 #x0000000019b14b80) #xf919d76538ae8537))
(constraint (= (deobfucated #x0000000034903b1b #x000000001949e784) #xf8b1391db4acf41f))
(constraint (= (deobfucated #x000000000b68066a #x000000002a435881) #xf8e7c406b756f3fc))
(constraint (= (deobfucated #x00000000133ede86 #x000000001104628c) #xff99ebfcff5b3d36))
(constraint (= (deobfucated #x0000000012cc947b #x000000001f57dfe5) #xfe64a06ed388a364))
(constraint (= (deobfucated #x0000000016c2fe2c #x000000000bbce4cc) #xfe7d1483ec2d40d4))
(constraint (= (deobfucated #x0000000014a58b56 #x000000001365da3e) #xff173955b7a59f86))
(check-synth)