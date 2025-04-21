package bfv

import (
	"crypto/rand"
	"math"
	"math/big"

	"github.com/sp301415/ringo-snark/bigring"
	"github.com/sp301415/ringo-snark/buckler"
	"github.com/sp301415/ringo-snark/csprng"
	"github.com/tuneinsight/lattigo/v6/core/rlwe"
)

type KeyGenerator struct {
	Degree  int
	Modulus *big.Int
	RingQ   *bigring.BigRing

	RNSModuli []uint64
	Gadget    []*big.Int

	UniformSampler *csprng.UniformSampler
}

func NewBFVKeyGenerator(degree int, modulus *big.Int) *KeyGenerator {
	level := int(math.Ceil(float64(modulus.BitLen()) / 60))
	logQ := make([]int, level)
	for i := 0; i < level; i++ {
		logQ[i] = 60
	}

	rnsModuli, _, err := rlwe.GenModuli(int(math.Log(float64(degree)))+1, logQ, nil)
	if err != nil {
		panic(err)
	}

	rnsProd := big.NewInt(1)
	for _, q := range rnsModuli {
		rnsProd.Mul(rnsProd, big.NewInt(0).SetUint64(q))
	}

	gadget := make([]*big.Int, level)
	for i := 0; i < level; i++ {
		gadget[i] = big.NewInt(0).Div(rnsProd, big.NewInt(0).SetUint64(rnsModuli[i]))
	}

	return &KeyGenerator{
		Degree:  degree,
		Modulus: big.NewInt(0).Set(modulus),
		RingQ:   bigring.NewBigRing(degree, modulus),

		RNSModuli: rnsModuli,
		Gadget:    gadget,

		UniformSampler: csprng.NewUniformSampler(),
	}
}

func (kg *KeyGenerator) GenSecretKey() SecretKeyCircuit {
	sk := kg.RingQ.NewPoly()
	for i := 0; i < kg.Degree; i++ {
		sk.Coeffs[i].SetInt64(int64(kg.UniformSampler.Sample()) % 2)
	}
	skNTT := kg.RingQ.ToNTTPoly(sk)

	return SecretKeyCircuit{
		Coeffs: sk.Coeffs,
		NTT:    skNTT.Coeffs,
	}
}

func (kg *KeyGenerator) GenPublicKey(sk SecretKeyCircuit) PublicKeyCircuit {
	maskNTT := kg.RingQ.NewNTTPoly()
	for i := 0; i < kg.Degree; i++ {
		maskNTT.Coeffs[i], _ = rand.Int(kg.UniformSampler, kg.Modulus)
	}

	errCoeffs := kg.RingQ.NewPoly()
	for i := 0; i < kg.Degree; i++ {
		errCoeffs.Coeffs[i].SetInt64(int64(kg.UniformSampler.Sample()) % 2)
	}
	errNTT := kg.RingQ.ToNTTPoly(errCoeffs)

	bodyNTT := kg.RingQ.NewNTTPoly()
	kg.RingQ.MulSubNTTAssign(bigring.BigNTTPoly{Coeffs: sk.NTT}, maskNTT, bodyNTT)
	kg.RingQ.AddNTTAssign(bodyNTT, errNTT, bodyNTT)

	return PublicKeyCircuit{
		SecretKeyCircuit: sk,

		PublicKeyNTT: [2]buckler.PublicWitness{
			bodyNTT.Coeffs,
			maskNTT.Coeffs,
		},

		ErrorCoeffs: errCoeffs.Coeffs,
		ErrorNTT:    errNTT.Coeffs,
	}
}

func (kg *KeyGenerator) GenRandomCiphertext(pk PublicKeyCircuit) EncryptionCircuit {
	auxKeyCoeffs := kg.RingQ.NewPoly()
	for i := 0; i < kg.Degree; i++ {
		auxKeyCoeffs.Coeffs[i].SetInt64(int64(kg.UniformSampler.Sample()) % 2)
	}
	auxKeyNTT := kg.RingQ.ToNTTPoly(auxKeyCoeffs)

	delta := big.NewInt(0).Div(kg.Modulus, big.NewInt(65537))
	msgCoeffs := kg.RingQ.NewPoly()
	for i := 0; i < kg.Degree; i++ {
		msgCoeffs.Coeffs[i].SetUint64(kg.UniformSampler.Sample() % 65537)
	}
	msgNTT := kg.RingQ.ToNTTPoly(msgCoeffs)

	errBodyCoeffs := kg.RingQ.NewPoly()
	errMaskCoeffs := kg.RingQ.NewPoly()
	for i := 0; i < kg.Degree; i++ {
		errBodyCoeffs.Coeffs[i].SetInt64(int64(kg.UniformSampler.Sample()) % 2)
		errMaskCoeffs.Coeffs[i].SetInt64(int64(kg.UniformSampler.Sample()) % 2)
	}
	errBodyNTT := kg.RingQ.ToNTTPoly(errBodyCoeffs)
	errMaskNTT := kg.RingQ.ToNTTPoly(errMaskCoeffs)

	bodyNTT := kg.RingQ.NewNTTPoly()
	kg.RingQ.MulSubNTTAssign(bigring.BigNTTPoly{Coeffs: pk.PublicKeyNTT[0]}, auxKeyNTT, bodyNTT)
	kg.RingQ.ScalarMulAddNTTAssign(msgNTT, delta, bodyNTT)
	kg.RingQ.AddNTTAssign(bodyNTT, errBodyNTT, bodyNTT)

	maskNTT := kg.RingQ.NewNTTPoly()
	kg.RingQ.MulSubNTTAssign(bigring.BigNTTPoly{Coeffs: pk.PublicKeyNTT[1]}, auxKeyNTT, maskNTT)
	kg.RingQ.AddNTTAssign(maskNTT, errMaskNTT, maskNTT)

	return EncryptionCircuit{
		PublicKeyCircuit: pk,

		CiphertextNTT: [2]buckler.PublicWitness{
			bodyNTT.Coeffs,
			maskNTT.Coeffs,
		},

		AuxKeyCoeffs: auxKeyCoeffs.Coeffs,
		AuxKeyNTT:    auxKeyNTT.Coeffs,

		Delta:         delta,
		MessageCoeffs: msgCoeffs.Coeffs,
		MessageNTT:    msgNTT.Coeffs,

		ErrorCoeffs: [2]buckler.Witness{
			errBodyCoeffs.Coeffs,
			errMaskCoeffs.Coeffs,
		},
		ErrorNTT: [2]buckler.Witness{
			errBodyNTT.Coeffs,
			errMaskNTT.Coeffs,
		},
	}
}

func (kg *KeyGenerator) GenDecryption(sk SecretKeyCircuit, pk PublicKeyCircuit, ct EncryptionCircuit) DecryptionCircuit {
	maskNTT := bigring.BigNTTPoly{Coeffs: ct.CiphertextNTT[1]}
	skNTT := bigring.BigNTTPoly{Coeffs: sk.NTT}

	decMaskCoeffs := kg.RingQ.NewPoly()
	decBound := big.NewInt(0).Lsh(big.NewInt(1), 128)
	for i := 0; i < kg.Degree; i++ {
		decMaskCoeffs.Coeffs[i], _ = rand.Int(kg.UniformSampler, decBound)
	}
	decMaskNTT := kg.RingQ.ToNTTPoly(decMaskCoeffs)

	auxKeyCoeffs := kg.RingQ.NewPoly()
	for i := 0; i < kg.Degree; i++ {
		auxKeyCoeffs.Coeffs[i].SetInt64(int64(kg.UniformSampler.Sample()) % 2)
	}
	auxKeyNTT := kg.RingQ.ToNTTPoly(auxKeyCoeffs)

	errCoeffs := kg.RingQ.NewPoly()
	for i := 0; i < kg.Degree; i++ {
		errCoeffs.Coeffs[i].SetInt64(int64(kg.UniformSampler.Sample()) % 2)
	}
	errNTT := kg.RingQ.ToNTTPoly(errCoeffs)

	errFullNTT := kg.RingQ.NewNTTPoly()
	kg.RingQ.MulNTTAssign(decMaskNTT, auxKeyNTT, errFullNTT)
	kg.RingQ.AddNTTAssign(errNTT, errFullNTT, errFullNTT)
	errFullCoeffs := kg.RingQ.ToPoly(errFullNTT)

	quoCoeffs, remCoeffs := kg.RingQ.NewPoly(), kg.RingQ.NewPoly()
	qHalf := big.NewInt(0).Div(kg.Modulus, big.NewInt(2))
	for i := 0; i < kg.Degree; i++ {
		if errFullCoeffs.Coeffs[i].Cmp(qHalf) > 0 {
			errFullCoeffs.Coeffs[i].Sub(errFullCoeffs.Coeffs[i], kg.Modulus)
		}
		quoCoeffs.Coeffs[i].DivMod(errFullCoeffs.Coeffs[i], decBound, remCoeffs.Coeffs[i])
	}
	quoNTT, remNTT := kg.RingQ.ToNTTPoly(quoCoeffs), kg.RingQ.ToNTTPoly(remCoeffs)

	bodyNTT := kg.RingQ.NewNTTPoly()
	kg.RingQ.MulNTTAssign(maskNTT, skNTT, bodyNTT)
	kg.RingQ.AddNTTAssign(bodyNTT, remNTT, bodyNTT)

	return DecryptionCircuit{
		Degree: kg.Degree,

		PublicKeyCircuit: pk,

		MaskNTT:    maskNTT.Coeffs,
		DecMaskNTT: decMaskNTT.Coeffs,
		BodyNTT:    bodyNTT.Coeffs,

		AuxKeyCoeffs: auxKeyCoeffs.Coeffs,
		AuxKeyNTT:    auxKeyNTT.Coeffs,

		ErrorCoeffs: errCoeffs.Coeffs,
		ErrorNTT:    errNTT.Coeffs,

		QuoCoeffs: quoCoeffs.Coeffs,
		QuoNTT:    quoNTT.Coeffs,
	}
}

func (kg *KeyGenerator) GenRelinKey(sk SecretKeyCircuit) RelinKeyCircuit {
	level := len(kg.Gadget)

	auxKeyCoeffs := kg.RingQ.NewPoly()
	for i := 0; i < kg.Degree; i++ {
		auxKeyCoeffs.Coeffs[i].SetInt64(int64(kg.UniformSampler.Sample()) % 2)
	}
	auxKeyNTT := kg.RingQ.ToNTTPoly(auxKeyCoeffs)

	maskNTT := [2][]buckler.PublicWitness{
		make([]buckler.PublicWitness, level),
		make([]buckler.PublicWitness, level),
	}
	for i := 0; i < level; i++ {
		maskNTT0 := kg.RingQ.NewNTTPoly()
		maskNTT1 := kg.RingQ.NewNTTPoly()
		for j := 0; j < kg.Degree; j++ {
			maskNTT0.Coeffs[j], _ = rand.Int(kg.UniformSampler, kg.Modulus)
			maskNTT1.Coeffs[j], _ = rand.Int(kg.UniformSampler, kg.Modulus)
		}
		maskNTT[0][i] = maskNTT0.Coeffs
		maskNTT[1][i] = maskNTT1.Coeffs
	}

	errCoeffs := [3][]buckler.Witness{
		make([]buckler.Witness, level),
		make([]buckler.Witness, level),
		make([]buckler.Witness, level),
	}
	for i := 0; i < level; i++ {
		errCoeffs0 := kg.RingQ.NewNTTPoly()
		errCoeffs1 := kg.RingQ.NewNTTPoly()
		errCoeffs2 := kg.RingQ.NewNTTPoly()
		for j := 0; j < kg.Degree; j++ {
			errCoeffs0.Coeffs[j].SetInt64(int64(kg.UniformSampler.Sample()) % 2)
			errCoeffs1.Coeffs[j].SetInt64(int64(kg.UniformSampler.Sample()) % 2)
			errCoeffs2.Coeffs[j].SetInt64(int64(kg.UniformSampler.Sample()) % 2)
		}
		errCoeffs[0][i] = errCoeffs0.Coeffs
		errCoeffs[1][i] = errCoeffs1.Coeffs
		errCoeffs[2][i] = errCoeffs2.Coeffs
	}
	errNTT := [3][]buckler.Witness{
		make([]buckler.Witness, level),
		make([]buckler.Witness, level),
		make([]buckler.Witness, level),
	}
	for i := 0; i < level; i++ {
		errNTT[0][i] = kg.RingQ.ToNTTPoly(bigring.BigPoly{Coeffs: errCoeffs[0][i]}).Coeffs
		errNTT[1][i] = kg.RingQ.ToNTTPoly(bigring.BigPoly{Coeffs: errCoeffs[1][i]}).Coeffs
		errNTT[2][i] = kg.RingQ.ToNTTPoly(bigring.BigPoly{Coeffs: errCoeffs[2][i]}).Coeffs
	}

	bodyNTT := [3][]buckler.PublicWitness{
		make([]buckler.PublicWitness, level),
		make([]buckler.PublicWitness, level),
		make([]buckler.PublicWitness, level),
	}

	for i := 0; i < level; i++ {
		bodyNTT0 := kg.RingQ.NewNTTPoly()
		bodyNTT1 := kg.RingQ.NewNTTPoly()
		bodyNTT2 := kg.RingQ.NewNTTPoly()

		maskNTT0 := bigring.BigNTTPoly{Coeffs: maskNTT[0][i]}
		maskNTT1 := bigring.BigNTTPoly{Coeffs: maskNTT[1][i]}

		errNTT0 := bigring.BigNTTPoly{Coeffs: errNTT[0][i]}
		errNTT1 := bigring.BigNTTPoly{Coeffs: errNTT[1][i]}
		errNTT2 := bigring.BigNTTPoly{Coeffs: errNTT[2][i]}

		kg.RingQ.MulSubNTTAssign(bigring.BigNTTPoly{Coeffs: sk.NTT}, maskNTT0, bodyNTT0)
		kg.RingQ.AddNTTAssign(bodyNTT0, errNTT0, bodyNTT0)

		kg.RingQ.MulSubNTTAssign(auxKeyNTT, maskNTT0, bodyNTT1)
		kg.RingQ.ScalarMulAddNTTAssign(bigring.BigNTTPoly{Coeffs: sk.NTT}, kg.Gadget[i], bodyNTT1)
		kg.RingQ.AddNTTAssign(bodyNTT1, errNTT1, bodyNTT1)

		kg.RingQ.MulSubNTTAssign(bigring.BigNTTPoly{Coeffs: sk.NTT}, maskNTT1, bodyNTT2)
		kg.RingQ.ScalarMulSubNTTAssign(auxKeyNTT, kg.Gadget[i], bodyNTT2)
		kg.RingQ.AddNTTAssign(bodyNTT2, errNTT2, bodyNTT2)

		bodyNTT[0][i] = bodyNTT0.Coeffs
		bodyNTT[1][i] = bodyNTT1.Coeffs
		bodyNTT[2][i] = bodyNTT2.Coeffs
	}

	return RelinKeyCircuit{
		SecretKeyCircuit: sk,

		Gadget: kg.Gadget,

		MaskNTT: maskNTT,
		BodyNTT: bodyNTT,

		AuxKeyCoeffs: auxKeyCoeffs.Coeffs,
		AuxKeyNTT:    auxKeyNTT.Coeffs,

		ErrorCoeffs: errCoeffs,
		ErrorNTT:    errNTT,
	}
}

func (kg *KeyGenerator) GenAutKey(sk SecretKeyCircuit, d int) AutKeyCircuit {
	level := len(kg.Gadget)

	skAutNTT := kg.RingQ.AutomorphismNTT(bigring.BigNTTPoly{Coeffs: sk.NTT}, d)

	maskNTT := make([]buckler.PublicWitness, level)
	for i := 0; i < level; i++ {
		maskNTTi := kg.RingQ.NewNTTPoly()
		for j := 0; j < kg.Degree; j++ {
			maskNTTi.Coeffs[j], _ = rand.Int(kg.UniformSampler, kg.Modulus)
		}
		maskNTT[i] = maskNTTi.Coeffs
	}

	errCoeffs := make([]buckler.Witness, level)
	errNTT := make([]buckler.Witness, level)
	for i := 0; i < level; i++ {
		errCoeffsi := kg.RingQ.NewPoly()
		for j := 0; j < kg.Degree; j++ {
			errCoeffsi.Coeffs[i].SetInt64(int64(kg.UniformSampler.Sample()) % 2)
		}
		errCoeffs[i] = errCoeffsi.Coeffs
		errNTT[i] = kg.RingQ.ToNTTPoly(errCoeffsi).Coeffs
	}

	bodyNTT := make([]buckler.PublicWitness, level)
	for i := 0; i < level; i++ {
		bodyNTTi := kg.RingQ.NewNTTPoly()

		skNTT := bigring.BigNTTPoly{Coeffs: sk.NTT}
		maskNTTi := bigring.BigNTTPoly{Coeffs: maskNTT[i]}
		errNTTi := bigring.BigNTTPoly{Coeffs: errNTT[i]}

		kg.RingQ.MulSubNTTAssign(maskNTTi, skNTT, bodyNTTi)
		kg.RingQ.ScalarMulAddNTTAssign(skAutNTT, kg.Gadget[i], bodyNTTi)
		kg.RingQ.AddNTTAssign(errNTTi, bodyNTTi, bodyNTTi)

		bodyNTT[i] = bodyNTTi.Coeffs
	}

	return AutKeyCircuit{
		SecretKeyCircuit: sk,

		AutIdx: d,

		Gadget: kg.Gadget,

		MaskNTT: maskNTT,
		BodyNTT: bodyNTT,

		SkAutNTT: skAutNTT.Coeffs,

		ErrorCoeffs: errCoeffs,
		ErrorNTT:    errNTT,
	}
}
