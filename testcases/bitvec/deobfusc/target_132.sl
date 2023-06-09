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

(constraint (= (deobfucated #x0000000030abdcb8 #x0000000010a84534 #x000000002ddb1ed5) #x9c27575bc815bf1f))
(constraint (= (deobfucated #x00000000059e5f3a #x0000000027c59757 #x00000000205fad36) #x52faf57c36a80f9b))
(constraint (= (deobfucated #x0000000036b1b492 #x0000000021d637d0 #x000000002d8d9674) #x60f6afa7f978e77f))
(constraint (= (deobfucated #x000000002e044245 #x00000000118520b0 #x00000000010e0333) #x74b919819d4b3caf))
(constraint (= (deobfucated #x0000000019d6b43e #x0000000001340820 #x000000000179505e) #x2b1d9683f0c8077f))
(constraint (= (deobfucated #x0000000027ee9cbf #x0000000025c74107 #x000000000d6c9cb7) #x8cfc025103452340))
(constraint (= (deobfucated #x000000000502eef4 #x000000000ef23cdf #x00000000376806d1) #x5e8df67881eb0fb3))
(constraint (= (deobfucated #x00000000232eee54 #x000000000a3de8be #x000000002826692e) #xca9686f9aeb37c2f))
(constraint (= (deobfucated #x0000000018801e2c #x0000000030cfd73c #x000000000561b8b3) #x4e2d3cf239ec160f))
(constraint (= (deobfucated #x00000000263e794b #x0000000011cda78b #x000000002ae4b63b) #xec885914b55c375c))
(constraint (= (deobfucated #x0000000025e1f998 #x000000001429b01d #x0000000021c2b5f9) #x86bc7fa21b689b87))
(constraint (= (deobfucated #x0000000018795b1d #x000000001e2ebd12 #x000000001f54cd0f) #x0ab782c0a728be69))
(constraint (= (deobfucated #x000000001d9129c0 #x000000001632f0ab #x000000002153a8b9) #x5f0afe2fef2fc6bf))
(constraint (= (deobfucated #x000000002eafa1ad #x000000002e2dea57 #x0000000018863332) #x1820bcf248d6b159))
(constraint (= (deobfucated #x0000000028345875 #x000000000026bd5d #x0000000008150dcb) #xd555cb0fc0c52bb4))
(constraint (= (deobfucated #x00000000128bdfc1 #x0000000022688bc0 #x0000000035e83642) #x6e3e13710023587f))
(constraint (= (deobfucated #x000000000a9131a3 #x000000001973de42 #x0000000006d2db9f) #xc9a282e133484045))
(constraint (= (deobfucated #x000000002bca6624 #x0000000009ada441 #x000000003296145b) #x4faafc92f91c7e33))
(constraint (= (deobfucated #x0000000010dca54b #x000000002eda1401 #x0000000034b8ccab) #xde299bd1ce2ddee6))
(constraint (= (deobfucated #x00000000157d01dc #x000000000e5341d7 #x0000000028394d52) #xb20bbbf2456d8737))
(check-synth)