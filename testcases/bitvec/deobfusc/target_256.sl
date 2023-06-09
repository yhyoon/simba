(set-logic BV)

(synth-fun deobfucated ( (c (BitVec 64))  (d (BitVec 64))  ) (BitVec 64)
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
				c d
			)
		)
	)
)

(constraint (= (deobfucated #x000000002da371eb #x00000000258d9d0b) #xfffffffff75d9efe))
(constraint (= (deobfucated #x000000002689ed5e #x000000002996c4fe) #xffffffffd76eb3fd))
(constraint (= (deobfucated #x0000000007cfaf5f #x000000000cffcd37) #xfffffffffcffbcf6))
(constraint (= (deobfucated #x000000002aac7ebc #x000000001289c4b0) #xffffffffef73c3eb))
(constraint (= (deobfucated #x0000000014b37bf6 #x0000000009e1a0e5) #xfffffffff3cd9cda))
(constraint (= (deobfucated #x00000000075f0564 #x000000000732a307) #xfffffffffef15ede))
(constraint (= (deobfucated #x0000000014f777ad #x00000000308a8432) #xffffffffeb797bec))
(constraint (= (deobfucated #x0000000011740ca2 #x000000001053f1eb) #xffffffffefcfebde))
(constraint (= (deobfucated #x0000000036166b03 #x00000000012f32bf) #xffffffffeedfad7e))
(constraint (= (deobfucated #x000000000ad39c24 #x00000000357d7319) #xffffffffeb7ceef2))
(constraint (= (deobfucated #x00000000222c3eb1 #x00000000103d7c3e) #xffffffffedfaf9fc))
(constraint (= (deobfucated #x000000000111fdc2 #x000000000e6f9cdf) #xfffffffffcdf9ebe))
(constraint (= (deobfucated #x000000000db03a68 #x0000000004c9e65e) #xfffffffff6b7ddbd))
(constraint (= (deobfucated #x00000000197bc9e7 #x00000000114ab7df) #xffffffffe7ce6fbe))
(constraint (= (deobfucated #x0000000028e52d3f #x000000000c992213) #xfffffffffb76dcd2))
(constraint (= (deobfucated #x000000001a0a2581 #x0000000033d72f93) #xffffffffefaedf6e))
(constraint (= (deobfucated #x0000000022e92fe9 #x0000000026e9abde) #xffffffffdff7fbbc))
(constraint (= (deobfucated #x0000000009b1ce3d #x0000000009bc4bad) #xfffffffff7fe3bee))
(constraint (= (deobfucated #x000000002045fc5d #x0000000031bc08ca) #xffffffffef7e03e4))
(constraint (= (deobfucated #x00000000263dcf2b #x0000000028ba9d7c) #xffffffffd5f63cfa))
(check-synth)