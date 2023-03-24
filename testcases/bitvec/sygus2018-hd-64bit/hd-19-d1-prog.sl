; Hacker's delight 19, difficulty 1

(set-logic BV)

(define-fun hd19 ((x (BitVec 64)) (m (BitVec 64)) (k (BitVec 64))) (BitVec 64) 
  (bvxor x (bvxor (bvshl (bvand (bvxor (bvlshr x k) x) m) k) (bvand (bvxor (bvlshr x k) x) m))))

(synth-fun f ((x (BitVec 64)) (m (BitVec 64)) (k (BitVec 64))) (BitVec 64)
		   ((Start (BitVec 64) ((bvand Start Start)
								(bvsub Start Start)
								(bvxor Start Start)
								(bvor Start Start)
								(bvand Start Start)
								(bvshl Start Start)
								(bvlshr Start Start)
								(bvashr Start Start)
								(bvnot Start)
								(bvneg Start)
								x
								m
								k))))


(declare-var x (BitVec 64))
(declare-var m (BitVec 64))
(declare-var k (BitVec 64))

(constraint (= (hd19 x m k) (f x m k)))
(check-synth)

