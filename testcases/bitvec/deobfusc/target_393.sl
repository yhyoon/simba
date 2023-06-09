(set-logic BV)

(synth-fun deobfucated ( (a (BitVec 64))  (c (BitVec 64))  (d (BitVec 64))  ) (BitVec 64)
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
				a c d
			)
		)
	)
)

(constraint (= (deobfucated #x000000002053ec08 #x00000000056eedba #x000000003a616018) #x088d3f689a90955f))
(constraint (= (deobfucated #x000000003411799e #x0000000018358906 #x00000000198a155b) #x0601bf7eec5d156c))
(constraint (= (deobfucated #x0000000038fe58e1 #x00000000071d83b6 #x000000002a65461d) #x0a994b8f932d87be))
(constraint (= (deobfucated #x000000001844543e #x0000000034be915c #x00000000336be816) #x0c407a5769e2f4fb))
(constraint (= (deobfucated #x000000003a4506e2 #x00000000244b365e #x000000002b54ca0a) #x0a8bf167b4c4cec3))
(constraint (= (deobfucated #x0000000006afabae #x000000002e4c4744 #x000000002316c294) #x066efa190295fab1))
(constraint (= (deobfucated #x000000001e80407f #x000000000731703a #x000000001ff55f16) #x03f4dd359b14ad52))
(constraint (= (deobfucated #x00000000070949ee #x000000001ea35282 #x0000000007381c6c) #x00e4a083b839fde9))
(constraint (= (deobfucated #x000000000f3c5d70 #x000000003288cd4e #x0000000010294637) #x04061492ae65214a))
(constraint (= (deobfucated #x00000000379c8691 #x000000003a681bec #x0000000000f2cf45) #x003cb09df848697c))
(constraint (= (deobfucated #x000000000f2dc4c0 #x0000000009bb0654 #x000000003560e464) #x0348aa21414b5b2b))
(constraint (= (deobfucated #x0000000023a1f945 #x0000000033a4a209 #x0000000015f08ef1) #x046d260fa787b3d0))
(constraint (= (deobfucated #x000000002cee62e6 #x0000000003d827f4 #x00000000360dc170) #x0a223e1cee0c9315))
(constraint (= (deobfucated #x000000000043d2da #x0000000032ec30a8 #x000000002222a4fd) #x06cac2f7662076ee))
(constraint (= (deobfucated #x0000000001984563 #x0000000037dfd786 #x000000002a55a2a1) #x093d6a3d375c9908))
(constraint (= (deobfucated #x0000000011ea309a #x000000000b4f00b2 #x0000000025703073) #x0415cff9856fc3b4))
(constraint (= (deobfucated #x000000002181259d #x00000000222bb9b3 #x000000001187168d) #x02713a4f3698fb42))
(constraint (= (deobfucated #x0000000002adb661 #x0000000027993a8f #x000000001cb344ab) #x047495377d8d775a))
(constraint (= (deobfucated #x00000000161561e5 #x00000000048f6e1d #x0000000003a282f7) #x00523ac7b2406608))
(constraint (= (deobfucated #x00000000162b73e3 #x000000002e86f747 #x0000000007433743) #x01c7455d77adbf14))
(check-synth)