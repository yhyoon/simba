(set-logic BV)
(synth-fun f ( (x (BitVec 64)) ) (BitVec 64)
((Start (BitVec 64)
((bvnot Start)
(bvxor Start Start)
(bvand Start Start)
(bvor Start Start)
(bvneg Start)
(bvadd Start Start)
(bvmul Start Start)
(bvudiv Start Start)
(bvurem Start Start)
(bvlshr Start Start)
(bvashr Start Start)
(bvshl Start Start)
(bvsdiv Start Start)
(bvsrem Start Start)
(bvsub Start Start)
x
#x0000000000000000
#x0000000000000001
#x0000000000000002
#x0000000000000003
#x0000000000000004
#x0000000000000005
#x0000000000000006
#x0000000000000007
#x0000000000000008
#x0000000000000009
#x0000000000000009
#x0000000000000009
#x000000000000000A
#x000000000000000B
#x000000000000000C
#x000000000000000D
#x000000000000000E
#x000000000000000F
#x0000000000000010
(ite StartBool Start Start)
))
(StartBool Bool
((= Start Start)
(not StartBool)
(and StartBool StartBool)
(or StartBool StartBool)
))))
(constraint (= (f #x457B057107F39AD7) #x7509F51DF018CA50))
(constraint (= (f #x743B3001431E7554) #x17899FFD79C31556))
(constraint (= (f #x69C558012C26A3FE) #x2C754FFDA7B2B802))
(constraint (= (f #xD17E652A15796B75) #x5D0335ABD50D2914))
(constraint (= (f #x7DFD013E502E56B2) #x0405FD835FA3529A))
(constraint (= (f #x0893169B3C48F144) #x0000009314083040))
(constraint (= (f #x6F2A3E8AEB6019C7) #x00002E0A2A000940))
(constraint (= (f #xA3511C9243558506) #x0000001000100104))
(constraint (= (f #x2B350AFF8964ECEC) #x00000A3508648864))
(constraint (= (f #xCCB3B12B932ED32F) #x00008023912A932E))
(constraint (= (f #x86E1F3806023F03B) #x0000828060006023))
(constraint (= (f #x6417408A452B0C15) #x00004002400A0401))
(constraint (= (f #x014441C199713315) #x0000014001411111))
(constraint (= (f #x8F6BCA8400224797) #x00008A0000000002))
(constraint (= (f #xE12AF0C6806080D5) #x0000E00280408040))
(constraint (= (f #xFFFFFFFFFFFFFFFC) #x0000000000000006))
(constraint (= (f #xFFFFFFFFFFFFFFFD) #x0000000000000004))
(constraint (= (f #x04813A90E42A4081) #x0000008020004000))
(constraint (= (f #x5E00A004987A9B2D) #x0000000080009828))
(constraint (= (f #xBE4BFA0DA02600ED) #x0000BA09A0040024))
(constraint (= (f #xC7742180006195A5) #x0000010000000021))
(constraint (= (f #x7128087624B808C1) #x0000002000300080))
(constraint (= (f #x01E2F4874AC3936F) #x0000008240830243))
(constraint (= (f #xCF17F6447071B390) #x61D013771F1C98DE))
(constraint (= (f #xECEF6FEFD8AFAF83) #x00006CEF48AF8883))
(constraint (= (f #x5FB67FDE40F9C193) #x409300437E0C7CD8))
(constraint (= (f #x61CAEDAD9B03268D) #x0000618889010201))
(constraint (= (f #x61C55F08FDFDBB5E) #x3C7541EE04048942))
(constraint (= (f #x2C8067237171C6BA) #xA6FF31B91D1C728A))
(constraint (= (f #x3DCE236D252EEF84) #x0000214C212C2504))
(constraint (= (f #x3E419DEA79CC238D) #x00001C4019C8218C))
(constraint (= (f #xBBDA56251A8EFA9F) #x884B53B5CAE20AC0))
(constraint (= (f #x632040047CA0D81B) #x0000400040005800))
(constraint (= (f #x3870F407CD9A7FF1) #x8F1E17F064CB001C))
(constraint (= (f #x1524291698B3093B) #x0000010408120833))
(constraint (= (f #x2E73951F63E4771A) #xA318D5C1383711CA))
(constraint (= (f #x924485A41395777B) #xDB76F4B7D8D51108))
(constraint (= (f #xDB35D7547BF0BBD3) #x49945157081E8858))
(constraint (= (f #xB849C02C013282F7) #x0000800800200032))
(constraint (= (f #xFAAD7A4E7FAB7296) #x0AA50B6300A91AD2))
(constraint (= (f #x4A564905002706DF) #x0000480400050007))
(constraint (= (f #x7AFD2816D2B7093F) #x0A05AFD25A91ED80))
(constraint (= (f #x9768A12DBA3A1AB3) #xD12EBDA48B8BCA98))
(constraint (= (f #xA7243D619AB9BAF7) #xB1B7853CCA8C8A10))
(constraint (= (f #x40D5418104F307D9) #x00004081008104D1))
(constraint (= (f #x997153540F7CC63D) #xCD1D5957E1067384))
(constraint (= (f #x821E7F304B5B66B7) #xFBC3019F69493290))
(constraint (= (f #x0E189DEB08ED71F3) #xE3CEC429EE251C18))
(constraint (= (f #x38FE82100BE15401) #x0000001002000001))
(constraint (= (f #x366A5B220B9BC41B) #x932B49BBE8C877C8))
(check-synth)
(define-fun f_1 ((x (BitVec 64))) (BitVec 64) (ite (= (bvor #x0000000000000010 x) x) (ite (= (bvurem x #x0000000000000009) #x0000000000000002) (bvand (bvlshr x #x0000000000000010) x) (ite (= (bvor #x000000000000000c x) x) (bvmul (bvnot x) #x0000000000000002) (ite (= (bvand #x000000000000000c x) #x0000000000000000) (bvmul (bvnot x) #x0000000000000002) (ite (= (bvand #x0000000000000001 x) #x0000000000000000) (bvmul (bvnot x) #x0000000000000002) (ite (= (bvurem x #x0000000000000005) #x0000000000000000) (bvand (bvlshr x #x0000000000000010) x) (ite (= (bvurem x #x0000000000000003) #x0000000000000000) (ite (= (bvsrem x #x0000000000000003) #x0000000000000000) (bvand (bvlshr x #x0000000000000010) x) (ite (= (bvurem x #x000000000000000b) #x0000000000000002) (bvand (bvlshr x #x0000000000000010) x) (bvmul (bvnot x) #x0000000000000002))) (bvmul (bvnot x) #x0000000000000002))))))) (bvand (bvlshr x #x0000000000000010) x)))
