(set-logic BV)

(synth-fun deobfucated ( (c (BitVec 64))  (a (BitVec 64))  (d (BitVec 64))  ) (BitVec 64)
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
				c a d
			)
		)
	)
)

(constraint (= (deobfucated #x000000000f2153c4 #x000000002c62d5d4 #x000000001c3adbba) #xffffffffd099a7d7))
(constraint (= (deobfucated #x000000002211dcd1 #x0000000038b88ee4 #x000000002668b94b) #xffffffffc50e1c8b))
(constraint (= (deobfucated #x0000000006320658 #x000000002dcf17e8 #x00000000022664ce) #xffffffffcbfce587))
(constraint (= (deobfucated #x0000000012b9dd9e #x00000000304c8533 #x000000002637d47f) #xffffffff9cf6211f))
(constraint (= (deobfucated #x000000001a8aa8e2 #x0000000005e9943b #x000000002b295e69) #xffffffffde72aef9))
(constraint (= (deobfucated #x0000000019897f96 #x00000000145bb9f4 #x00000000154726a9) #xffffffffddd9e6d7))
(constraint (= (deobfucated #x000000000f76017d #x000000003add9367 #x0000000011382266) #xffffffffa5b4697d))
(constraint (= (deobfucated #x00000000364b6349 #x00000000189b500c #x000000001c25e546) #xffffffffb91a8ca7))
(constraint (= (deobfucated #x000000001a2d1d1f #x000000002dcccde7 #x000000001330c9da) #xffffffffb7055d3b))
(constraint (= (deobfucated #x00000000128955f8 #x000000002b5a948c #x000000000626a3c9) #xffffffffc4199603))
(constraint (= (deobfucated #x000000001a951136 #x0000000012112acd #x000000001e36e075) #xffffffffe569a3bf))
(constraint (= (deobfucated #x000000002e4c75d3 #x0000000028ca2ee9 #x0000000013d3a3d6) #xffffffffa8a77a03))
(constraint (= (deobfucated #x0000000002bf2ef4 #x000000000bdda5a8 #x0000000016e9fe3f) #xfffffffff3abcf7f))
(constraint (= (deobfucated #x000000000603323b #x000000002d4718e7 #x0000000035757d8f) #xffffffffaf72bc5c))
(constraint (= (deobfucated #x0000000019ef2f70 #x000000001dc2031b #x000000001f344cdd) #xffffffffdd4ecd7b))
(constraint (= (deobfucated #x0000000023bd5b88 #x000000000d718812 #x000000000657ea9f) #xffffffffcaa1a453))
(constraint (= (deobfucated #x000000002df6937f #x0000000031cfb31b #x00000000393f66e9) #xffffffffb1369b6e))
(constraint (= (deobfucated #x0000000028379990 #x00000000157df34b #x0000000006e8b0e2) #xffffffffbe22e2e2))
(constraint (= (deobfucated #x0000000022dfdfab #x0000000020263f2a #x0000000029e9d4f7) #xffffffffdcd9f54d))
(constraint (= (deobfucated #x0000000010c0c0ef #x0000000035009724 #x0000000005e5e64d) #xffffffffb53f21f3))
(check-synth)