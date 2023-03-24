

(set-logic BV)

(define-fun origCir ((i_7 Bool) (i_8 Bool) (i_5 Bool) (i_6 Bool) )  Bool
  (and (not (and (not (and i_8 i_7)) i_5)) (xor (or (or (not i_6) i_5) (and (not i_8) i_7)) i_6))
)


(synth-fun skel ((i_7 Bool) (i_8 Bool) (i_5 Bool) (i_6 Bool) )  Bool (
(Start Bool (depth2) )
 
    (depth2 Bool (
      (and depth1 depth1)
      (or depth1 depth1)
      (xor depth2 depth2)
      (not depth2)
      depth1
      
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
      i_7 i_8 i_5 i_6  
    )
  )
  
 )
)
(declare-var i_7 Bool)
(declare-var i_8 Bool)
(declare-var i_5 Bool)
(declare-var i_6 Bool)

(constraint (= (origCir i_7 i_8 i_5 i_6 ) (skel i_7 i_8 i_5 i_6 )))
(check-synth)
