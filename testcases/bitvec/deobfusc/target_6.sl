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

(constraint (= (deobfucated #x000000002bf799c3 #x000000001de55a77) #x078d1d21dddcd630))
(constraint (= (deobfucated #x0000000006bb25c2 #x00000000216a765e) #x002d4e9568611e28))
(constraint (= (deobfucated #x000000000364a12b #x00000000171a6d18) #x000b83554a741251))
(constraint (= (deobfucated #x000000001de5228f #x00000000123d9e2d) #x037db6eb122289de))
(constraint (= (deobfucated #x000000003601393b #x00000000376335d7) #x0b6484262c242d90))
(constraint (= (deobfucated #x000000003371fee3 #x000000000a65a152) #x0a569e5179dba13f))
(constraint (= (deobfucated #x0000000008d6c175 #x0000000029055db0) #x004e203f60d5012f))
(constraint (= (deobfucated #x000000003a45b947 #x000000000fc36486) #x0d43aaf1ca111d7f))
(constraint (= (deobfucated #x0000000009499868 #x000000001c060d58) #x005641dfb34d87d0))
(constraint (= (deobfucated #x0000000018cf81c6 #x0000000003d94bec) #x026790883b98e996))
(constraint (= (deobfucated #x000000001a4f7eb6 #x000000000f57602e) #x02b43e6c48a65fa0))
(constraint (= (deobfucated #x000000001479efdb #x0000000024fb8d32) #x01a3478ef8f57d0f))
(constraint (= (deobfucated #x000000002bf590ca #x0000000029347a06) #x078c6a32052845f8))
(constraint (= (deobfucated #x000000001f3a35dc #x0000000017bc9025) #x03cf264796f20609))
(constraint (= (deobfucated #x000000002acb025c #x00000000156efd7c) #x07273dc2851d6ed0))
(constraint (= (deobfucated #x00000000181818cb #x000000000e3da97a) #x024486ea86336277))
(constraint (= (deobfucated #x000000003aa7f24d #x0000000024e334ff) #x0d7087f89ec32e6e))
(constraint (= (deobfucated #x0000000012721dc8 #x0000000030096ed2) #x01543f0eebff6c8a))
(constraint (= (deobfucated #x0000000001da4bfc #x000000000c6f6a21) #x00036ebd786c1615))
(constraint (= (deobfucated #x000000000bf7cbc1 #x0000000038fa49d3) #x008f3b5d20fa3196))
(check-synth)