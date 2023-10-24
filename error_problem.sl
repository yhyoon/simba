(set-logic BV)
(define-fun obfucated (  (x (BitVec 64)) (y (BitVec 64)) ) (BitVec 64) 
  (bvadd (bvnot (bvmul #x0000000000000003 (bvxor x y))) (bvmul #x0000000000000003 (bvand y (bvnot x))))
)

(synth-fun deobfucated (  (x (BitVec 64)) (y (BitVec 64)) ) (BitVec 64)
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
          (bvsrem Start Start)
    	    (bvlshr Start Start)
          (bvsdiv Start Start)
           x y
           #x0000000000000000 #x0000000000000001 #x0000000000000002 #x0000000000000003 #x0000000000000004 #x0000000000000008
        )
      )
  )
)

(declare-var x (BitVec 64))
(declare-var y (BitVec 64))

(constraint (= (obfucated  x y) (deobfucated  x y)))
(check-synth)