import Synthesis.LinearConsumerKernelQuotient
import Synthesis.LinearConsumerSyntheticBidiSeed
import Mathlib.Tactic.NativeDecide

/-!
# Finite two-V synthetic bidi joint-kernel certificate

Application-level verifier for the deterministic certificate emitted by
`dashiRTX` commit `49071484843451af16e99e21df4e2f1bb391303a`, source
`rsa260_bidi_two_v_joint_kernel_certificate.py`.

The certificate uses the baseline seed and

    V' = build_block(BASEY xor (1 << 40))

and the selected stacked rows

    0..124, 126, 127, 128, 924..931.

The runtime selected-square array digest is
`697631f5406a4e996b42ad21c92a57dc9a0e4a7a247e664d054d9522258faa9b`.
The packed inverse-byte SHA-256 is
`384bdc1cdc03392950082e0497919885310facfd99b0fd610cbfc2e76b606861`.

This file reconstructs the selected square from the existing formal incidence,
prepared operator and deterministic seed semantics; only the producer-supplied
finite inverse is embedded.  This remains synthetic evidence: it does not bind
historical CADO artifacts or production RSA-260 identity.
-/

namespace Synthesis

abbrev SyntheticBidiColumnBits := Fin 136
abbrev SyntheticBidiColumnVector := SyntheticBidiColumnBits → ZMod 2
abbrev SyntheticBidiWord136 := BitVec 136

def syntheticBidiWord136OfNat (n : Nat) : SyntheticBidiWord136 :=
  BitVec.ofNat 136 n

/-- The second deterministic runtime seed, `BASEY xor (1 << 40)`. -/
def syntheticBidiSecondBaseY : SyntheticBidiWord :=
  syntheticBidiBaseY ^^^ (syntheticBidiWordOfNat 1 <<< 40)

/-- Generic deterministic seed word with an explicit base seed. -/
def syntheticBidiSeedWordFrom
    (base : SyntheticBidiWord) (j : SyntheticBidiBlock) (w : Nat) : SyntheticBidiWord :=
  let columnSeed := base ^^^ (syntheticBidiWordOfNat j.val <<< 32)
  let wordSalt :=
    syntheticBidiWordOfNat 0x9E3779B97F4A7C15 * syntheticBidiWordOfNat (w + 1)
  syntheticBidiMix64 (columnSeed ^^^ wordSalt)

/-- Exact formal mirror of `build_block(BASEY xor (1 << 40))`. -/
def syntheticBidiSecondSeedBlock :
    Matrix SyntheticBidiRows SyntheticBidiBlock (ZMod 2) :=
  fun r j =>
    if (syntheticBidiSeedWordFrom syntheticBidiSecondBaseY j (r.val / 64)).getLsbD
        (r.val % 64)
    then 1
    else 0

/-- Selected stacked row number in `[K(V); K(V')]`. -/
def syntheticBidiSelectedStackedRowNat (i : SyntheticBidiColumnBits) : Nat :=
  if i.val < 125 then i.val
  else if i.val < 128 then i.val + 1
  else 924 + (i.val - 128)

/-- Which of the two seed contexts owns the selected row. -/
def syntheticBidiSelectedContext (i : SyntheticBidiColumnBits) : Fin 2 :=
  if syntheticBidiSelectedStackedRowNat i < 924 then 0 else 1

/-- Local row number inside one 924-row Krylov context. -/
def syntheticBidiSelectedLocalRow (i : SyntheticBidiColumnBits) : SyntheticBidiRows :=
  ⟨syntheticBidiSelectedStackedRowNat i % 924, Nat.mod_lt _ (by decide)⟩

/-- Flattened coefficient-column coordinate: layer `q / 8`. -/
def syntheticBidiColumnLayer (q : SyntheticBidiColumnBits) : Fin 17 :=
  ⟨(q.val / 8) % 17, Nat.mod_lt _ (by decide)⟩

/-- Flattened coefficient-column coordinate: block row `q % 8`. -/
def syntheticBidiColumnInner (q : SyntheticBidiColumnBits) : SyntheticBidiBlock :=
  ⟨q.val % 8, Nat.mod_lt _ (by decide)⟩

/-- Seed selected by the two-context certificate. -/
def syntheticBidiSeedForContext (k : Fin 2) :
    Matrix SyntheticBidiRows SyntheticBidiBlock (ZMod 2) :=
  if k.val = 0 then syntheticBidiSeedBlock else syntheticBidiSecondSeedBlock

/-- Exact 136x136 selected minor reconstructed from formal `M`, `V`, and `V'`. -/
def syntheticBidiSelectedSquare :
    Matrix SyntheticBidiColumnBits SyntheticBidiColumnBits (ZMod 2) :=
  fun i q =>
    ((syntheticBidiPreparedOperator ^ (syntheticBidiColumnLayer q : Nat))
      (syntheticBidiSeedForContext (syntheticBidiSelectedContext i)))
      (syntheticBidiSelectedLocalRow i)
      (syntheticBidiColumnInner q)

/-- Producer-supplied inverse rows, packed as 136-bit little-endian bit vectors. -/
def syntheticBidiSelectedSquareInverseRow
    (i : SyntheticBidiColumnBits) : SyntheticBidiWord136 :=
  match i.val with
    | 0 => syntheticBidiWord136OfNat 0x00619400000000000000301A1FC5531865
    | 1 => syntheticBidiWord136OfNat 0x006E94000000000000003235E0C5D71BA5
    | 2 => syntheticBidiWord136OfNat 0x00CA30000000000000006216CC73BC028C
    | 3 => syntheticBidiWord136OfNat 0x0061940000000000000032A21FC5FD1865
    | 4 => syntheticBidiWord136OfNat 0x00520400000000000000264DCFD5C42C81
    | 5 => syntheticBidiWord136OfNat 0x00A03C0000000000000057D08AB1F4280F
    | 6 => syntheticBidiWord136OfNat 0x00A1B000000000000000540359B233306C
    | 7 => syntheticBidiWord136OfNat 0x00B66400000000000000532D2DB6BA9D99
    | 8 => syntheticBidiWord136OfNat 0x0092200000000000000040F489A20C0488
    | 9 => syntheticBidiWord136OfNat 0x009BE000000000000000400FDC5DC586F8
    | 10 => syntheticBidiWord136OfNat 0x0036840000000000000011CFA514211DA1
    | 11 => syntheticBidiWord136OfNat 0x0054C4000000000000002641652A3FAD31
    | 12 => syntheticBidiWord136OfNat 0x0043040000000000000025E5CED53E28C1
    | 13 => syntheticBidiWord136OfNat 0x00539C000000000000002294C32D6B1CE7
    | 14 => syntheticBidiWord136OfNat 0x0077CC0000000000000036BFB8C28BADF3
    | 15 => syntheticBidiWord136OfNat 0x00E0EC0000000000000076D19B9F5BA83B
    | 16 => syntheticBidiWord136OfNat 0x0F2C9456A9B34E7A61B66201042056D801
    | 17 => syntheticBidiWord136OfNat 0xDBF4934BDA8963E3B7ECA64C27899951D9
    | 18 => syntheticBidiWord136OfNat 0x9C92D638BDA42187C9D862501456F9C5F1
    | 19 => syntheticBidiWord136OfNat 0x82FB020971160BC9650CBD77D3D3086321
    | 20 => syntheticBidiWord136OfNat 0xCAB18A0570EA7242DA06344438C1D994A8
    | 21 => syntheticBidiWord136OfNat 0x03938E49D3B1B4610560978FCC020DC800
    | 22 => syntheticBidiWord136OfNat 0x8E5CE91BF4BA4FCE9176559D7ECDE37CE6
    | 23 => syntheticBidiWord136OfNat 0xDC5D06924E312CB6D3B1A375CE81EECF9F
    | 24 => syntheticBidiWord136OfNat 0x23242404B418C317374399EDF7C8182A4A
    | 25 => syntheticBidiWord136OfNat 0xEC45737D581EB657B43EA9E90A9B580254
    | 26 => syntheticBidiWord136OfNat 0xE63E9EF2B834216FA8C366160DC32FD41F
    | 27 => syntheticBidiWord136OfNat 0x6C8547F754D6A186EA332B896997C89650
    | 28 => syntheticBidiWord136OfNat 0x60513D408096C7D1159DBF64D8EB47BB04
    | 29 => syntheticBidiWord136OfNat 0x7875E348D8B9EF81A2BCDE929F7833AD22
    | 30 => syntheticBidiWord136OfNat 0x66C95FB8E4008D3E8B667D337F0B3F7577
    | 31 => syntheticBidiWord136OfNat 0x65E141AE5A8125CB7FDA2D066E6F6507BF
    | 32 => syntheticBidiWord136OfNat 0x06AC188A5FD108BC999B461BBF66C03846
    | 33 => syntheticBidiWord136OfNat 0x78718D73DC27E590C7F7073A4FD73B03E6
    | 34 => syntheticBidiWord136OfNat 0x80446BEDB39E34CE5A2A1917E7F11A6913
    | 35 => syntheticBidiWord136OfNat 0x6B970223BA71A3774A95E404369F992F51
    | 36 => syntheticBidiWord136OfNat 0xF65CFD65A6D2585DA94B2503607C1F157B
    | 37 => syntheticBidiWord136OfNat 0x04158FCD4539C5E56F39429C977EF9438D
    | 38 => syntheticBidiWord136OfNat 0x0340FA04C818849ED2508036D33612BF16
    | 39 => syntheticBidiWord136OfNat 0x2E7162E55EA1EF81A67801A80FA91610AD
    | 40 => syntheticBidiWord136OfNat 0xBEAC18F8B8AD85B846B6BB6B936223DBEB
    | 41 => syntheticBidiWord136OfNat 0x167650ED1761EAFBF43D8559B069B3DEEA
    | 42 => syntheticBidiWord136OfNat 0x506BFD832633F9C80DE06671A41DA3947C
    | 43 => syntheticBidiWord136OfNat 0x951C3165612950B6AD01870893AC7FB527
    | 44 => syntheticBidiWord136OfNat 0x5ADBCB950BD636FDC5956E4FED20A220C6
    | 45 => syntheticBidiWord136OfNat 0x7726D10646B43643C65D8D124EA9D8218E
    | 46 => syntheticBidiWord136OfNat 0xD3B8840B5E21F1ABCCF7F2F6247F259728
    | 47 => syntheticBidiWord136OfNat 0x8D1F913CECC637BBC19D5790D9582B1721
    | 48 => syntheticBidiWord136OfNat 0xB53504D578819E213E7265E60FB03AAC30
    | 49 => syntheticBidiWord136OfNat 0x8F62953420E42734484ECAF15E89A245A3
    | 50 => syntheticBidiWord136OfNat 0xE7504923C3CC2F7DF5BFD99969CCD1A6A5
    | 51 => syntheticBidiWord136OfNat 0xDB3B4EE7EB2EDD9A1F19C5E896F1F9F478
    | 52 => syntheticBidiWord136OfNat 0x959ADB5A5FEDE2A808300E3E5900E007D8
    | 53 => syntheticBidiWord136OfNat 0x7EEB52B20E1EB6DBC41EAE010403C9C63B
    | 54 => syntheticBidiWord136OfNat 0x3AE30E384FDBDB87FBC990F8161F5E8A82
    | 55 => syntheticBidiWord136OfNat 0xFABB5EE52E42C97483B66372663D121591
    | 56 => syntheticBidiWord136OfNat 0xB74483CF1A2F2EB6673CA0C2D7174150E4
    | 57 => syntheticBidiWord136OfNat 0x782D383222094D070C22B6D060472EA1CB
    | 58 => syntheticBidiWord136OfNat 0xE9F1809701AECA22535E726333B94E4904
    | 59 => syntheticBidiWord136OfNat 0x5E5BB4D7E9D4A29E1BC35D564068AAE35A
    | 60 => syntheticBidiWord136OfNat 0xD49A149C9DE66BB0BAA0BF9FA72B400AD5
    | 61 => syntheticBidiWord136OfNat 0x4FE39CF1CAECD0352ED6ACB2F1F615DC8C
    | 62 => syntheticBidiWord136OfNat 0xE24FAA75669EF1583E5CED506B6E6F0833
    | 63 => syntheticBidiWord136OfNat 0x68ACC6C64C5CD487FDE02D954069DC7B3E
    | 64 => syntheticBidiWord136OfNat 0x7D4A9103D40D84C86C7ACD0819F6E333FD
    | 65 => syntheticBidiWord136OfNat 0xC64FD49271106F1017010F001CA32B371E
    | 66 => syntheticBidiWord136OfNat 0xBDA52C86C23155538130EC1BD4DB966825
    | 67 => syntheticBidiWord136OfNat 0x92DBD6FC0A0F7C6A7DAA3D655D0A7CFA9B
    | 68 => syntheticBidiWord136OfNat 0x0174EAAD30BD1ACD625C406CE2710C969F
    | 69 => syntheticBidiWord136OfNat 0x22E45BF8D834AFF03112F0C7AC14B28310
    | 70 => syntheticBidiWord136OfNat 0x0EF398E67BF109A7C798DC680F02D8CFBF
    | 71 => syntheticBidiWord136OfNat 0x5B218EE9905B7AF8582152D2DB0B3FED24
    | 72 => syntheticBidiWord136OfNat 0xC5B9B1FEDBFBC0C580192AC0262A97467E
    | 73 => syntheticBidiWord136OfNat 0x3C0B56BAB4989F242BBA9ED37B6848093D
    | 74 => syntheticBidiWord136OfNat 0x2586025BC63C61E9677D5F77D5E0CB90EB
    | 75 => syntheticBidiWord136OfNat 0xAF95BF5D385BC4127C9210B9E70894138B
    | 76 => syntheticBidiWord136OfNat 0x8923E0304542D94C0583DB44C63C41B67B
    | 77 => syntheticBidiWord136OfNat 0xB8C81315C9A07F98B1D09AA6CB7D79DEBC
    | 78 => syntheticBidiWord136OfNat 0x42E150A7619807687C99E77EE99971EC3F
    | 79 => syntheticBidiWord136OfNat 0x87F6A1658E61AF1A443FA5E19020CED7D0
    | 80 => syntheticBidiWord136OfNat 0x2A2069AED9DAD76EE3CEE2223C3932D8F0
    | 81 => syntheticBidiWord136OfNat 0xC4FDA1239214133525650E1C0F5B5518CA
    | 82 => syntheticBidiWord136OfNat 0xED1687EEA722F756E94DAB1C3B6988A611
    | 83 => syntheticBidiWord136OfNat 0x8B0EFEF8745FE2D5F8B1651CD424C669E3
    | 84 => syntheticBidiWord136OfNat 0xC63B9449F5FC6059535E03045C6EF721A1
    | 85 => syntheticBidiWord136OfNat 0xB679EA82677D8669E23E6FC92DBAC93387
    | 86 => syntheticBidiWord136OfNat 0x796720852E30941AFB43A1CD8FFAAC35EB
    | 87 => syntheticBidiWord136OfNat 0xF7857BD1FB5223788EEF921EE8B89862E6
    | 88 => syntheticBidiWord136OfNat 0x48EB875AB7DF6200E4B964D5D6B0FDE662
    | 89 => syntheticBidiWord136OfNat 0xAC1033A7E6F9063FD1E6EFDDA632B8DA3D
    | 90 => syntheticBidiWord136OfNat 0xD070566ECD95B16F17ECB073B86B4B66EE
    | 91 => syntheticBidiWord136OfNat 0x85AECC25AA1638ED2818E8AEDC33C12008
    | 92 => syntheticBidiWord136OfNat 0x116FCFEB957BF2A1D1C29A691E929DAEC3
    | 93 => syntheticBidiWord136OfNat 0xBBB17503EA9264851ED912851FA98E11EA
    | 94 => syntheticBidiWord136OfNat 0xF19AAFDA0DA98DDBEB8B476904786692A8
    | 95 => syntheticBidiWord136OfNat 0x9B5A3CC5C00100027211913C23B59A3E2D
    | 96 => syntheticBidiWord136OfNat 0xD09655BB3B7304E03CFA1E7736DEF74DEA
    | 97 => syntheticBidiWord136OfNat 0xADFA1500F77015535CC7AF9E9A97E73F9A
    | 98 => syntheticBidiWord136OfNat 0x7932078F06A71AA84B96AAF5981B2E5740
    | 99 => syntheticBidiWord136OfNat 0x711175DDA8FCA887FB53CCEEF57608566A
    | 100 => syntheticBidiWord136OfNat 0x49AE61F25162EC91FA6043DF0C082A0D9F
    | 101 => syntheticBidiWord136OfNat 0xB52ACA9876CE5260AA044FEE75878F7E4A
    | 102 => syntheticBidiWord136OfNat 0x5DDDC72A64359D21B64B7B6EF427600130
    | 103 => syntheticBidiWord136OfNat 0x6B40142BEF79724170D30F6EE43BFC1339
    | 104 => syntheticBidiWord136OfNat 0xAA924447AE567A9C776EF006D0354A0E50
    | 105 => syntheticBidiWord136OfNat 0x7DED1020C5E7BEDEF76309C68D5E41E99C
    | 106 => syntheticBidiWord136OfNat 0xAFDE158CF4895BF78148AA594BC28A4EF1
    | 107 => syntheticBidiWord136OfNat 0x1B633E183590C74858C5D29986E1EEE63B
    | 108 => syntheticBidiWord136OfNat 0xC60BD84B0EF3747DB14FEA92BCF458B8D5
    | 109 => syntheticBidiWord136OfNat 0x46C4A3EF7F49437E3C594338E4F22E2303
    | 110 => syntheticBidiWord136OfNat 0x016CBD153808D0298FDD25CBFFB714D96E
    | 111 => syntheticBidiWord136OfNat 0x06E7F122BAAC7E0A1B2964FCA8A3300369
    | 112 => syntheticBidiWord136OfNat 0xB857A43268EF924FEF69A2E71590954C59
    | 113 => syntheticBidiWord136OfNat 0xE847E47A3452B3B6B0469E74E358761604
    | 114 => syntheticBidiWord136OfNat 0xD108DD9CF06A474C0C2699D003D683BE9E
    | 115 => syntheticBidiWord136OfNat 0x1A8AC4B5FA763130AE7F4CE281808653F3
    | 116 => syntheticBidiWord136OfNat 0x080D6DB27AF0BF60C01F78C04ADF880621
    | 117 => syntheticBidiWord136OfNat 0x42B1662665562D835E0B6528738344271F
    | 118 => syntheticBidiWord136OfNat 0x89781697D35C76D1B25D90817345D72812
    | 119 => syntheticBidiWord136OfNat 0x74DA4903033868ED26B59C6B5CF6BBD3BF
    | 120 => syntheticBidiWord136OfNat 0x2D2CA03D4776FA19F4A57BD11DA019A4E3
    | 121 => syntheticBidiWord136OfNat 0x4B4284BACA73EB1138CD8CB9DA80ADE000
    | 122 => syntheticBidiWord136OfNat 0x72615056279EE94A875CBDEFD91A62FCC5
    | 123 => syntheticBidiWord136OfNat 0xC51DC189FF0F7409805B49687C3C799255
    | 124 => syntheticBidiWord136OfNat 0x3A910F1B9CE050161385142089EA3610BC
    | 125 => syntheticBidiWord136OfNat 0x6BE07D0366514F86C40A97C435F47DD7A8
    | 126 => syntheticBidiWord136OfNat 0x0B37581FE774C769B189CB7FA2B1983F9F
    | 127 => syntheticBidiWord136OfNat 0x685BFB92CB9B628BA64BFF83980673A2E1
    | 128 => syntheticBidiWord136OfNat 0x30165CDB6586A92964B500F77E9129B6FB
    | 129 => syntheticBidiWord136OfNat 0x29F764E0692850E5D3123CF39A1E3B3D4D
    | 130 => syntheticBidiWord136OfNat 0xEA1E8ECB0C5A74B9CB621E3962E02ABC2A
    | 131 => syntheticBidiWord136OfNat 0x1AE9ACA8C21E66DF3F85ECB3CF1B74A679
    | 132 => syntheticBidiWord136OfNat 0x2CEA338E8FD472E96DAD556323D813FEBE
    | 133 => syntheticBidiWord136OfNat 0x35DE590C1ACDFE8EB8DA329826BED0F82F
    | 134 => syntheticBidiWord136OfNat 0x028029D349DFEEB1C8A474FC90E51BFF98
    | 135 => syntheticBidiWord136OfNat 0xBFE4F1C7D4AB7743B617326BDA25DBE9F2
    | _ => syntheticBidiWord136OfNat 0

/-- Explicit inverse matrix over GF(2). -/
def syntheticBidiSelectedSquareInverse :
    Matrix SyntheticBidiColumnBits SyntheticBidiColumnBits (ZMod 2) :=
  fun i j => if (syntheticBidiSelectedSquareInverseRow i).getLsbD j.val then 1 else 0

/-- Kernel-checked finite inverse certificate.  This is the only computationally
heavy leaf: no Gaussian elimination or trusted runtime rank scalar is imported. -/
theorem syntheticBidiSelectedSquare_inverse_mul :
    syntheticBidiSelectedSquareInverse * syntheticBidiSelectedSquare = 1 := by
  native_decide

/-- Selected-square column action. -/
def syntheticBidiTwoVColumnAction :
    SyntheticBidiColumnVector →ₗ[ZMod 2] SyntheticBidiColumnVector :=
  syntheticBidiSelectedSquare.mulVecLin

/-- A one-element generic consumer family whose sole consumer is the stacked
selected two-V action. -/
def syntheticBidiTwoVColumnConsumer :
    Fin 1 → SyntheticBidiColumnVector →ₗ[ZMod 2] SyntheticBidiColumnVector :=
  fun _ => syntheticBidiTwoVColumnAction

theorem syntheticBidiSelectedSquare_mulVec_injective :
    Function.Injective syntheticBidiSelectedSquare.mulVec := by
  intro x y h
  have h' := congrArg (fun v => syntheticBidiSelectedSquareInverse *ᵥ v) h
  simpa [Matrix.mulVec_mulVec, syntheticBidiSelectedSquare_inverse_mul] using h'

/-- The finite two-context selected column map has trivial joint kernel. -/
theorem syntheticBidiTwoVJointKernel_eq_bot :
    jointKernel syntheticBidiTwoVColumnConsumer = ⊥ := by
  apply le_antisymm
  · intro x hx
    have hz : syntheticBidiTwoVColumnAction x = 0 :=
      (mem_jointKernel_iff syntheticBidiTwoVColumnConsumer x).mp hx 0
    have hzero : x = 0 := by
      apply syntheticBidiSelectedSquare_mulVec_injective
      simpa [syntheticBidiTwoVColumnAction] using hz
    simpa [hzero]
  · exact bot_le

/-- Generic compiler output: trivial joint kernel implies injectivity. -/
theorem syntheticBidiTwoVJointlyInjective
    {x y : SyntheticBidiColumnVector}
    (h : ∀ i, syntheticBidiTwoVColumnConsumer i x =
      syntheticBidiTwoVColumnConsumer i y) :
    x = y :=
  jointly_injective_of_iInf_ker_eq_bot
    syntheticBidiTwoVColumnConsumer
    syntheticBidiTwoVJointKernel_eq_bot
    h

end Synthesis
