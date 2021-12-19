
(set-logic BV)

(define-fun shr1 ((x (BitVec 64))) (BitVec 64) (bvlshr x #x0000000000000001))
(define-fun shr4 ((x (BitVec 64))) (BitVec 64) (bvlshr x #x0000000000000004))
(define-fun shr16 ((x (BitVec 64))) (BitVec 64) (bvlshr x #x0000000000000010))
(define-fun shl1 ((x (BitVec 64))) (BitVec 64) (bvshl x #x0000000000000001))
(define-fun if0 ((x (BitVec 64)) (y (BitVec 64)) (z (BitVec 64))) (BitVec 64) (ite (= x #x0000000000000001) y z))

(synth-fun f ( (x (BitVec 64))) (BitVec 64)
(

(Start (BitVec 64) (#x0000000000000000 #x0000000000000001 x (bvnot Start)
                    (shl1 Start)
 		    (shr1 Start)
		    (shr4 Start)
		    (shr16 Start)
		    (bvand Start Start)
		    (bvor Start Start)
		    (bvxor Start Start)
		    (bvadd Start Start)
		    (if0 Start Start Start)
 ))
)
)


(constraint (= (f #x4566bad4eeeee029) #x0000000000000000))
(constraint (= (f #xee3e1d44d6810569) #x0000000000000000))
(constraint (= (f #x3100ec92a3797305) #x01000c8022311300))
(constraint (= (f #x3ba2c6e646d4b42b) #x0000000000000000))
(constraint (= (f #x0c9bacee90edde40) #x0089a8ce800cdc40))
(constraint (= (f #xd73b73917b49c3d4) #x0533331113008014))
(constraint (= (f #xe8e578a9ee24723b) #x0000000000000000))
(constraint (= (f #x524b13a91969e0d1) #x0000112811008001))
(constraint (= (f #xd2321cc06ce70e7c) #x0000000000000001))
(constraint (= (f #x4439c84686d455e3) #x0401880400444542))
(constraint (= (f #xed47d86a900502c5) #x0c44580280000004))
(constraint (= (f #x3ae7719de4e2a318) #x0000000000000001))
(constraint (= (f #xe45e0eb9eaa23250) #x044400a98aa22200))
(constraint (= (f #x40d066c93ea01da2) #x0000064812a00182))
(constraint (= (f #xde9ea2ce6be9e361) #x0c88a20c62a88220))
(constraint (= (f #xe8c30c60521123d5) #x0880004000010215))
(constraint (= (f #x69a478bbb7aec5c7) #x0080408bb32ac444))
(constraint (= (f #x3c17710ac7c6c922) #x0001710084444802))
(constraint (= (f #xcee0acee958c3ad8) #x0000000000000001))
(constraint (= (f #x86be551d5b70ae3e) #x0000000000000001))
(constraint (= (f #xabdd35ccd6ee354b) #x0000000000000000))
(constraint (= (f #x855459ca63041743) #x0054418822000140))
(constraint (= (f #x0694127677eed9d8) #x0000000000000001))
(constraint (= (f #x04c529ec36d838ce) #x0000000000000001))
(constraint (= (f #xe159711e4ee799e1) #x0011111044e61980))
(constraint (= (f #x5ceb31a74abb5eab) #x0000000000000000))
(constraint (= (f #x1aae9e09e395e680) #x00aa880082114600))
(constraint (= (f #xb37ed2ece0e5524e) #x0000000000000001))
(constraint (= (f #x2dadecba96c72d0c) #x0000000000000001))
(constraint (= (f #xed489597389cee58) #x0000000000000001))
(constraint (= (f #xc0e78ecc304d5768) #x0000000000000001))
(constraint (= (f #x8793d186e3705866) #x0011110062300006))
(constraint (= (f #x46b8328d55681276) #x0428020855400026))
(constraint (= (f #x0a0a11193192cd09) #x0000000000000000))
(constraint (= (f #xe53a26e97c696cea) #x0000000000000001))
(constraint (= (f #xe637516c7337c24d) #x0000000000000000))
(constraint (= (f #x671ec3cba0ebe47e) #x0000000000000001))
(constraint (= (f #xd515e7436091aa06) #x0511464020010a00))
(constraint (= (f #x66786be9addb0382) #x066002a888d90000))
(constraint (= (f #x2a35b6c1c8a80eec) #x0000000000000001))
(constraint (= (f #x8dd3465128eb355a) #x0000000000000001))
(constraint (= (f #x9e9e3c43d2be1e30) #x08882040102a0020))
(constraint (= (f #x4560c97e3c0ba3e5) #x044008162000a224))
(constraint (= (f #x3d3bc55d07345bde) #x0000000000000001))
(constraint (= (f #xeabbbdbeb53e1eeb) #x0000000000000000))
(constraint (= (f #x9a03786ca70c62e9) #x0000000000000000))
(constraint (= (f #xeccad11d425da913) #x0cc8811140058811))
(constraint (= (f #xe8e1260ee2aae327) #x08800200e22aa222))
(constraint (= (f #x4b425aa4b4297e63) #x000000a000001662))
(constraint (= (f #xeebeb92808015b4a) #x0000000000000001))
(constraint (= (f #xe11b7352e8973032) #x0011331028813002))
(constraint (= (f #x1611526ae6552860) #x00011022a6450000))
(constraint (= (f #x130dc28c8ce67e3b) #x0000000000000000))
(constraint (= (f #xd97e1d5328ce75e2) #x09160151208c6542))
(constraint (= (f #x773a0c3beb2b61b4) #x07320003aa222010))
(constraint (= (f #x0a7914c7ceb489d1) #x002110444ca00891))
(constraint (= (f #x8073cbe968b4b45c) #x0000000000000001))
(constraint (= (f #x7ddd27486e9e9580) #x05dd024006888100))
(constraint (= (f #x28016a169eb2b4e5) #x0000020008a22044))
(constraint (= (f #xeea8e46112445ce2) #x0ea88440100444c2))
(constraint (= (f #x4d1ec29b72c96850) #x0410c00932080000))
(constraint (= (f #x42966540a7c734e7) #x0000644002443046))
(constraint (= (f #x80748e3620e76496) #x0004082220066400))
(constraint (= (f #x819bbd60309edd32) #x0019b9400008cd12))
(constraint (= (f #x913b9453ce69ddae) #x0000000000000001))
(constraint (= (f #xde2ee2aee7abeda0) #x0c22e22ae62aac80))
(constraint (= (f #xab40d9730488c572) #x0a00091300088452))
(constraint (= (f #x1964c0b383e0b303) #x0104400300200300))
(constraint (= (f #x2576b223b5a5b4cc) #x0000000000000001))
(constraint (= (f #xe838b17558de515b) #x0000000000000000))
(constraint (= (f #x8d9797504a30d375) #x0891115000200135))
(constraint (= (f #x31232c9e3619e142) #x0102208822018000))
(constraint (= (f #x7a5b1d53ae1d66d9) #x0000000000000000))
(constraint (= (f #x3bc0581444ae10dd) #x0000000000000000))
(constraint (= (f #x2e7b37de14ebe2dd) #x0000000000000000))
(constraint (= (f #x890931aec28749d8) #x0000000000000001))
(constraint (= (f #xe8cc15304c4e761a) #x0000000000000001))
(constraint (= (f #xb56bdb306e89ae53) #x0142993006888a41))
(constraint (= (f #xb66852e61dec18ee) #x0000000000000001))
(constraint (= (f #xbdeea2e313d6b33d) #x0000000000000000))
(constraint (= (f #x815d4d694422d432) #x0015444004020402))
(constraint (= (f #xb20945d7e2d6e334) #x0200045562046230))
(constraint (= (f #x4a56a410c59d24b7) #x0004200004190003))
(constraint (= (f #x93c0838d580803b0) #x0100000850000030))
(constraint (= (f #xdd14114c999e0766) #x0d10010489980066))
(constraint (= (f #x04e5eeee2677aa14) #x00444eee22672a00))
(constraint (= (f #xa1aae2ae615e0080) #x000aa22a60140000))
(constraint (= (f #x75d5c6b5be93c6ed) #x0000000000000000))
(constraint (= (f #x86032ea7ee7b56e8) #x0000000000000001))
(constraint (= (f #xe4dba4e23e4b2317) #x0449a04222402211))
(constraint (= (f #xe9d86992733cc216) #x089800902330c000))
(constraint (= (f #x779a25754180e184) #x0718205540000000))
(constraint (= (f #x9e598056520ec388) #x0000000000000001))
(constraint (= (f #x8ee965dba20495e5) #x08e80459a2000144))
(constraint (= (f #x9ce2039ac1e3a1ea) #x0000000000000001))
(constraint (= (f #x5582570d39a9ab95) #x0500050011888a91))
(constraint (= (f #x75cae0eabec9216e) #x0000000000000001))
(constraint (= (f #xe7a5de03ee828527) #x06205c002e800002))
(constraint (= (f #xac605d2bddcc2cd3) #x084005029dcc00c1))
(constraint (= (f #xc61cc0e1addb9205) #x0400c00008d99000))
(check-synth)
