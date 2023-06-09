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

(constraint (= (deobfucated #x0000000028093034 #x0000000006107d7f #x0000000005b8d9c1) #x0000000027b1bcaa))
(constraint (= (deobfucated #x0000000009bd733b #x0000000032feadb9 #x000000003959d831) #x0000000010d4beec))
(constraint (= (deobfucated #x000000000f13d0c9 #x0000000007aee744 #x0000000002f0f9df) #x000000001158a3a4))
(constraint (= (deobfucated #x000000001566465c #x0000000017f10a48 #x000000000f790c1e) #x00000000224e4a7a))
(constraint (= (deobfucated #x000000002d9ecf54 #x000000003b650bde #x000000000469ac84) #x000000001fa77b4e))
(constraint (= (deobfucated #x0000000030ae7beb #x0000000003df0531 #x000000001ecb0e30) #x000000004c28860b))
(constraint (= (deobfucated #x00000000028bdb09 #x00000000165c708d #x0000000031973d93) #x000000001fcef818))
(constraint (= (deobfucated #x000000003a0472c7 #x000000001db00898 #x0000000000fd5526) #x000000003551bfd5))
(constraint (= (deobfucated #x000000002206a179 #x00000000065029a2 #x0000000001a20a83) #x000000001f58a37a))
(constraint (= (deobfucated #x000000001c9a5c9a #x0000000014554993 #x000000000ee0077d) #x000000002b356316))
(constraint (= (deobfucated #x0000000024f8b81d #x000000001ca06a8e #x0000000010b4cb2f) #x000000001dad40ca))
(constraint (= (deobfucated #x000000000f60659d #x00000000209d6e04 #x000000001eab3203) #x000000000d6e8da0))
(constraint (= (deobfucated #x0000000014c061e0 #x0000000034d05f3e #x00000000009f0ad8) #xfffffffff54f4e9a))
(constraint (= (deobfucated #x0000000023af8f3d #x000000003488f0b1 #x000000000b2683e1) #x000000001ad5a29e))
(constraint (= (deobfucated #x0000000008cb6e7d #x0000000002c87228 #x00000000065ed30d) #x000000000d2a318a))
(constraint (= (deobfucated #x000000003a384923 #x0000000034742ec4 #x0000000001a8009e) #x00000000379c22fd))
(constraint (= (deobfucated #x0000000002fbefab #x000000002d910065 #x000000002abe64c5) #x0000000000ba542c))
(constraint (= (deobfucated #x000000001fe62956 #x00000000231c121a #x000000002d9c332a) #x000000002d6a4a78))
(constraint (= (deobfucated #x000000000cb81fc3 #x000000002dee4f0c #x000000001c6c2104) #x0000000007de00bb))
(constraint (= (deobfucated #x00000000288780bc #x000000003a761a9e #x0000000028aad4ad) #x000000003ec23b67))
(check-synth)