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
(constraint (= (f #x74b5dd6e211e692b) #x8b4a2291dee196d4))
(constraint (= (f #x769612e4089c8014) #x0000769612e4089c))
(constraint (= (f #xa33d5b39703e576e) #x0000a33d5b39703e))
(constraint (= (f #xeb95023997bb11da) #x0000eb95023997bb))
(constraint (= (f #x157c68418cbe07dc) #x0000157c68418cbe))
(constraint (= (f #xbbae517eaa5dea25) #x4451ae8155a215da))
(constraint (= (f #xddb0a8cb4a1de2e9) #x224f5734b5e21d16))
(constraint (= (f #x513ed8b75652094a) #x0000513ed8b75652))
(constraint (= (f #xe192497e1ec59eee) #x0000e192497e1ec5))
(constraint (= (f #x136ad8d8a6025d16) #x0000136ad8d8a602))
(constraint (= (f #xe94eec154b34c87e) #x0000e94eec154b34))
(constraint (= (f #x90370e7c0c2b8eab) #x6fc8f183f3d47154))
(constraint (= (f #x531e50092b587cda) #x0000531e50092b58))
(constraint (= (f #x2b6cd8e551500b25) #xd493271aaeaff4da))
(constraint (= (f #xcc0a2dee382c731e) #x0000cc0a2dee382c))
(constraint (= (f #xac96c136478b85ee) #x0000ac96c136478b))
(constraint (= (f #x60363caee25a8e6b) #x9fc9c3511da57194))
(constraint (= (f #xeb3c837627bdb136) #x0000eb3c837627bd))
(constraint (= (f #xe00e0342c22eb101) #x1ff1fcbd3dd14efe))
(constraint (= (f #xab0ebe1d1759e20c) #x0000ab0ebe1d1759))
(constraint (= (f #x80b0ecc262a83dce) #x000080b0ecc262a8))
(constraint (= (f #x312ea941c9942ce7) #xced156be366bd318))
(constraint (= (f #x4d01e5874d906655) #xb2fe1a78b26f99aa))
(constraint (= (f #x803aa5b2746206d1) #x7fc55a4d8b9df92e))
(constraint (= (f #x30ca83255ad8eeb5) #xcf357cdaa527114a))
(constraint (= (f #xa1a35c2a548c1c99) #x5e5ca3d5ab73e366))
(constraint (= (f #x37649a948a961e19) #xc89b656b7569e1e6))
(constraint (= (f #xae13cd0ab613a0e8) #x0000ae13cd0ab613))
(constraint (= (f #x8a752c6ee7be9427) #x758ad39118416bd8))
(constraint (= (f #x52859e0e30b0ca0d) #xad7a61f1cf4f35f2))
(constraint (= (f #xcd93103565e53ae6) #x0000cd93103565e5))
(constraint (= (f #xb6e94d3ea1c9bc86) #x0000b6e94d3ea1c9))
(constraint (= (f #x35e4e17ac20370e4) #x000035e4e17ac203))
(constraint (= (f #x4ce8026b278d4847) #xb317fd94d872b7b8))
(constraint (= (f #xa8d6bc08c2ecc23a) #x0000a8d6bc08c2ec))
(constraint (= (f #xd6bdad77113cdeb6) #x0000d6bdad77113c))
(constraint (= (f #xe50e902c9ba5e8d4) #x0000e50e902c9ba5))
(constraint (= (f #x90300bea4b87bde2) #x000090300bea4b87))
(constraint (= (f #x837c563bb7425302) #x0000837c563bb742))
(constraint (= (f #xddb7595aba792e8e) #x0000ddb7595aba79))
(constraint (= (f #xd877d68eeceb3745) #x278829711314c8ba))
(constraint (= (f #x6b720507589a3184) #x00006b720507589a))
(constraint (= (f #x15c7e5d824eed8e0) #x000015c7e5d824ee))
(constraint (= (f #x5014699e398358d6) #x00005014699e3983))
(constraint (= (f #x1e737bad8070e95c) #x00001e737bad8070))
(constraint (= (f #x54c390768ee53c33) #xab3c6f89711ac3cc))
(constraint (= (f #xe1eb7b7aaee1e99b) #x1e148485511e1664))
(constraint (= (f #x57b6e5e77c79e71e) #x000057b6e5e77c79))
(constraint (= (f #x937bd49727cbe5e7) #x6c842b68d8341a18))
(constraint (= (f #x41e50b1ca93ce21b) #xbe1af4e356c31de4))
(constraint (= (f #xa09506bcd504c100) #x0000a09506bcd504))
(constraint (= (f #x28e6d642b17b3a0e) #x000028e6d642b17b))
(constraint (= (f #x6ee2bb848240411c) #x00006ee2bb848240))
(constraint (= (f #x1e7b5430db9c3d7a) #x00001e7b5430db9c))
(constraint (= (f #x6ad23d832d56e71b) #x952dc27cd2a918e4))
(constraint (= (f #x6ad387a4312ecdac) #x00006ad387a4312e))
(constraint (= (f #x9b05d493acde45ba) #x00009b05d493acde))
(constraint (= (f #x5a0bbd901d0ed285) #xa5f4426fe2f12d7a))
(constraint (= (f #xe5be46c94700ee48) #x0000e5be46c94700))
(constraint (= (f #x05498706d6b5b25b) #xfab678f9294a4da4))
(constraint (= (f #x7ce481a378aeedd6) #x00007ce481a378ae))
(constraint (= (f #xb5d095e22a464903) #x4a2f6a1dd5b9b6fc))
(constraint (= (f #xe5bcec7dc51c9c70) #x0000e5bcec7dc51c))
(constraint (= (f #x262d5941eeb549d5) #xd9d2a6be114ab62a))
(constraint (= (f #xe2720909db8da628) #x0000e2720909db8d))
(constraint (= (f #x1402e019c104dd17) #xebfd1fe63efb22e8))
(constraint (= (f #xc90e5b680e1d24b5) #x36f1a497f1e2db4a))
(constraint (= (f #x1e96007808ed8d27) #xe169ff87f71272d8))
(constraint (= (f #x7dee3a430819e025) #x8211c5bcf7e61fda))
(constraint (= (f #xbc0b4db74ae7024c) #x0000bc0b4db74ae7))
(constraint (= (f #xd2d60e553e7e6dc2) #x0000d2d60e553e7e))
(constraint (= (f #x34e61d4451aac496) #x000034e61d4451aa))
(constraint (= (f #xc1108ce494889007) #x3eef731b6b776ff8))
(constraint (= (f #xa5e3deb96aeb1702) #x0000a5e3deb96aeb))
(constraint (= (f #x53d1ca9a7bbe5e26) #x000053d1ca9a7bbe))
(constraint (= (f #x216627d0a011abb8) #x0000216627d0a011))
(constraint (= (f #xe89c1a554794d6e4) #x0000e89c1a554794))
(constraint (= (f #x51b9a2bc42dc2d6d) #xae465d43bd23d292))
(constraint (= (f #xa1b5b527294d0ddb) #x5e4a4ad8d6b2f224))
(constraint (= (f #xa0ccecd3cecde32c) #x0000a0ccecd3cecd))
(constraint (= (f #x08e0983cc598d9d5) #xf71f67c33a67262a))
(constraint (= (f #xed52088e5c68baeb) #x12adf771a3974514))
(constraint (= (f #x04d8d3c041e9d788) #x000004d8d3c041e9))
(constraint (= (f #xb7ec7d0e5e3b0861) #x481382f1a1c4f79e))
(constraint (= (f #x5eee0d7ee2c7ea94) #x00005eee0d7ee2c7))
(constraint (= (f #xbd3aa5e4ce6d3ced) #x42c55a1b3192c312))
(constraint (= (f #x50775de64829b14e) #x000050775de64829))
(constraint (= (f #xe964ed4c9b78e15e) #x0000e964ed4c9b78))
(constraint (= (f #xec4b1d350cc470ee) #x0000ec4b1d350cc4))
(constraint (= (f #x47a5323ac529e249) #xb85acdc53ad61db6))
(constraint (= (f #x4837ad1dc4ecad3a) #x00004837ad1dc4ec))
(constraint (= (f #x08e4265857bc0cc4) #x000008e4265857bc))
(constraint (= (f #xd18a4682b4c352d9) #x2e75b97d4b3cad26))
(constraint (= (f #x258672ae16c72c2a) #x0000258672ae16c7))
(constraint (= (f #x78e0e09aee8c56d2) #x000078e0e09aee8c))
(constraint (= (f #x836c938ee7b7004d) #x7c936c711848ffb2))
(constraint (= (f #x0db8aba9a9ce89aa) #x00000db8aba9a9ce))
(constraint (= (f #xa9231b798ee8ce1c) #x0000a9231b798ee8))
(constraint (= (f #xbc05edb4e70e3ebd) #x43fa124b18f1c142))
(constraint (= (f #xe0e32146d0d17859) #x1f1cdeb92f2e87a6))
(check-synth)
(define-fun f_1 ((x (BitVec 64))) (BitVec 64) (ite (= (bvor #x0000000000000001 x) x) (bvnot x) (bvlshr x #x0000000000000010)))
