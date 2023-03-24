

(set-logic BV)

(define-fun origCir ((n71 Bool) (n102 Bool) (n87 Bool) (n59 Bool) (i_3 Bool) )  Bool
  (and (xor (xor n102 (and n87 n59)) n71) i_3)
)


(synth-fun skel ((n71 Bool) (n102 Bool) (n87 Bool) (n59 Bool) (i_3 Bool) )  Bool (
(Start Bool (depth4) )
 
    (depth4 Bool (
      (and depth3 depth3)
      (or depth3 depth3)
      (xor depth4 depth4)
      (not depth4)
      depth3
      
      )
    )
    
    (depth3 Bool (
      (and depth2 depth2)
      (or depth2 depth2)
      (xor depth3 depth3)
      (not depth3)
      depth2
      n71 n102 n87 
      )
    )
    
    (depth2 Bool (
      (and depth1 depth1)
      (or depth1 depth1)
      (xor depth2 depth2)
      (not depth2)
      depth1
      n59 
      )
    )
    
    (depth1 Bool (
      (and depth0 depth0)
      (or depth0 depth0)
      (xor depth1 depth1)
      (not depth1)
      depth0
      
      )
    )
     
    (depth0 Bool (
      true
      false
      (xor depth0 depth0)
      (not depth0)
      i_3  
    )
  )
  
 )
)
(declare-var n71 Bool)
(declare-var n102 Bool)
(declare-var n87 Bool)
(declare-var n59 Bool)
(declare-var i_3 Bool)

(constraint (= (origCir n71 n102 n87 n59 i_3 ) (skel n71 n102 n87 n59 i_3 )))
(check-synth)
