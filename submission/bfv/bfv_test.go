package bfv_test

import (
	"fmt"
	"math"
	"math/big"
	"testing"

	"github.com/sp301415/ringo-snark/buckler"
	"github.com/sp301415/ringo-snark/celpc"
	"github.com/sp301415/ringo-snark/submission/bfv"
	"github.com/stretchr/testify/assert"
)

var proof buckler.Proof
var verify bool

func TestBuckler(t *testing.T) {
	t.Run("PELTA", func(t *testing.T) {
		params := bfv.ParamsLogN14Compact.Compile()
		kg := bfv.NewBFVKeyGenerator(params.Degree(), params.Modulus())

		c := bfv.PELTACircuit{
			PublicKeyCircuit: bfv.PublicKeyCircuit{},
		}
		prv, vrf, err := buckler.Compile(params, &c)
		assert.NoError(t, err)

		ck := celpc.GenAjtaiCommitKey(params)

		sk := kg.GenSecretKey()
		pk := kg.GenPublicKey(sk)
		c = bfv.PELTACircuit{
			PublicKeyCircuit: pk,
		}

		t.Run("Prove", func(t *testing.T) {
			pf, err := prv.Prove(ck, &c)
			assert.NoError(t, err)
			assert.True(t, vrf.Verify(ck, pf))
		})

		t.Run("ProveParallel", func(t *testing.T) {
			pf, err := prv.ProveParallel(ck, &c)
			assert.NoError(t, err)
			assert.True(t, vrf.Verify(ck, pf))
		})
	})

	t.Run("Encryption", func(t *testing.T) {
		params := bfv.ParamsLogN14Compact.Compile()
		kg := bfv.NewBFVKeyGenerator(params.Degree(), params.Modulus())

		c := bfv.EncryptionCircuit{
			Delta: big.NewInt(0).Div(params.Modulus(), big.NewInt(65537)),
		}
		prv, vrf, err := buckler.Compile(params, &c)
		assert.NoError(t, err)

		ck := celpc.GenAjtaiCommitKey(params)

		sk := kg.GenSecretKey()
		pk := kg.GenPublicKey(sk)
		ct := kg.GenRandomCiphertext(pk)

		t.Run("Prove", func(t *testing.T) {
			pf, err := prv.Prove(ck, &ct)
			assert.NoError(t, err)
			assert.True(t, vrf.Verify(ck, pf))
		})

		t.Run("ProveParallel", func(t *testing.T) {
			pf, err := prv.ProveParallel(ck, &ct)
			assert.NoError(t, err)
			assert.True(t, vrf.Verify(ck, pf))
		})
	})

	t.Run("Decryption", func(t *testing.T) {
		params := bfv.ParamsLogN14Compact.Compile()
		kg := bfv.NewBFVKeyGenerator(params.Degree(), params.Modulus())

		c := bfv.DecryptionCircuit{
			Degree: kg.Degree,
		}
		prv, vrf, err := buckler.Compile(params, &c)
		assert.NoError(t, err)

		ck := celpc.GenAjtaiCommitKey(params)

		sk := kg.GenSecretKey()
		pk := kg.GenPublicKey(sk)
		ct := kg.GenRandomCiphertext(pk)
		dec := kg.GenDecryption(sk, pk, ct)

		t.Run("Prove", func(t *testing.T) {
			pf, err := prv.Prove(ck, &dec)
			assert.NoError(t, err)
			assert.True(t, vrf.Verify(ck, pf))
		})

		t.Run("ProveParallel", func(t *testing.T) {
			pf, err := prv.ProveParallel(ck, &dec)
			assert.NoError(t, err)
			assert.True(t, vrf.Verify(ck, pf))
		})
	})
}

func BenchmarkBuckler(b *testing.B) {
	b.Run("PELTA", func(b *testing.B) {
		for _, paramsLiteral := range []celpc.ParametersLiteral{bfv.ParamsLogN14Compact, bfv.ParamsLogN15Compact} {
			params := paramsLiteral.Compile()
			logN := int(math.Log2(float64(params.Degree())))

			b.Run(fmt.Sprintf("LogN%d", logN), func(b *testing.B) {
				kg := bfv.NewBFVKeyGenerator(params.Degree(), params.Modulus())
				c := bfv.PELTACircuit{
					PublicKeyCircuit: bfv.PublicKeyCircuit{},
				}
				prv, vrf, err := buckler.Compile(params, &c)
				assert.NoError(b, err)

				ck := celpc.GenAjtaiCommitKey(params)

				sk := kg.GenSecretKey()
				pk := kg.GenPublicKey(sk)
				c = bfv.PELTACircuit{
					PublicKeyCircuit: pk,
				}

				b.Run("Prove", func(b *testing.B) {
					for i := 0; i < b.N; i++ {
						proof, _ = prv.Prove(ck, &c)
					}
				})

				b.Run("ProveParallel", func(b *testing.B) {
					for i := 0; i < b.N; i++ {
						proof, _ = prv.ProveParallel(ck, &c)
					}
				})

				b.Run("Verify", func(b *testing.B) {
					for i := 0; i < b.N; i++ {
						verify = vrf.Verify(ck, proof)
					}
				})
			})
		}
	})

	b.Run("Encryption", func(b *testing.B) {
		for _, paramsLiteral := range []celpc.ParametersLiteral{bfv.ParamsLogN14Compact, bfv.ParamsLogN15Compact} {
			params := paramsLiteral.Compile()
			logN := int(math.Log2(float64(params.Degree())))

			b.Run(fmt.Sprintf("LogN%d", logN), func(b *testing.B) {
				kg := bfv.NewBFVKeyGenerator(params.Degree(), params.Modulus())

				c := bfv.EncryptionCircuit{
					Delta: big.NewInt(0).Div(params.Modulus(), big.NewInt(65537)),
				}
				prv, vrf, err := buckler.Compile(params, &c)
				assert.NoError(b, err)

				ck := celpc.GenAjtaiCommitKey(params)

				sk := kg.GenSecretKey()
				pk := kg.GenPublicKey(sk)
				ct := kg.GenRandomCiphertext(pk)

				b.Run("Prove", func(b *testing.B) {
					for i := 0; i < b.N; i++ {
						proof, _ = prv.Prove(ck, &ct)
					}
				})

				b.Run("ProveParallel", func(b *testing.B) {
					for i := 0; i < b.N; i++ {
						proof, _ = prv.ProveParallel(ck, &ct)
					}
				})

				b.Run("Verify", func(b *testing.B) {
					for i := 0; i < b.N; i++ {
						verify = vrf.Verify(ck, proof)
					}
				})
			})
		}
	})

	b.Run("Decryption", func(b *testing.B) {
		for _, paramsLiteral := range []celpc.ParametersLiteral{bfv.ParamsLogN14Compact, bfv.ParamsLogN15Compact} {
			params := paramsLiteral.Compile()
			logN := int(math.Log2(float64(params.Degree())))

			b.Run(fmt.Sprintf("LogN%d", logN), func(b *testing.B) {
				kg := bfv.NewBFVKeyGenerator(params.Degree(), params.Modulus())

				c := bfv.DecryptionCircuit{
					Degree: kg.Degree,
				}
				prv, vrf, err := buckler.Compile(params, &c)
				assert.NoError(b, err)

				ck := celpc.GenAjtaiCommitKey(params)

				sk := kg.GenSecretKey()
				pk := kg.GenPublicKey(sk)
				ct := kg.GenRandomCiphertext(pk)
				dec := kg.GenDecryption(sk, pk, ct)

				b.Run("Prove", func(b *testing.B) {
					for i := 0; i < b.N; i++ {
						proof, _ = prv.Prove(ck, &dec)
					}
				})

				b.Run("ProveParallel", func(b *testing.B) {
					for i := 0; i < b.N; i++ {
						proof, _ = prv.ProveParallel(ck, &dec)
					}
				})

				b.Run("Verify", func(b *testing.B) {
					for i := 0; i < b.N; i++ {
						verify = vrf.Verify(ck, proof)
					}
				})
			})
		}
	})

	b.Run("Setup", func(b *testing.B) {
		for _, paramsLiteral := range []celpc.ParametersLiteral{bfv.ParamsLogN14Compact, bfv.ParamsLogN15Compact} {
			params := paramsLiteral.Compile()
			logN := int(math.Log2(float64(params.Degree())))

			b.Run(fmt.Sprintf("LogN%d", logN), func(b *testing.B) {
				kg := bfv.NewBFVKeyGenerator(params.Degree(), params.Modulus())

				c := bfv.SetupCircuit{
					RelinKeyCircuit: bfv.RelinKeyCircuit{
						Gadget: kg.Gadget,

						MaskNTT: [2][]buckler.PublicWitness{
							make([]buckler.PublicWitness, len(kg.Gadget)),
							make([]buckler.PublicWitness, len(kg.Gadget)),
						},
						BodyNTT: [3][]buckler.PublicWitness{
							make([]buckler.PublicWitness, len(kg.Gadget)),
							make([]buckler.PublicWitness, len(kg.Gadget)),
							make([]buckler.PublicWitness, len(kg.Gadget)),
						},

						ErrorCoeffs: [3][]buckler.Witness{
							make([]buckler.Witness, len(kg.Gadget)),
							make([]buckler.Witness, len(kg.Gadget)),
							make([]buckler.Witness, len(kg.Gadget)),
						},
						ErrorNTT: [3][]buckler.Witness{
							make([]buckler.Witness, len(kg.Gadget)),
							make([]buckler.Witness, len(kg.Gadget)),
							make([]buckler.Witness, len(kg.Gadget)),
						},
					},

					AtkNegOne: bfv.AutKeyCircuit{
						AutIdx: 2*kg.Degree - 1,
						Gadget: kg.Gadget,

						MaskNTT: make([]buckler.PublicWitness, len(kg.Gadget)),
						BodyNTT: make([]buckler.PublicWitness, len(kg.Gadget)),

						ErrorCoeffs: make([]buckler.Witness, len(kg.Gadget)),
						ErrorNTT:    make([]buckler.Witness, len(kg.Gadget)),
					},

					AtkFive: bfv.AutKeyCircuit{
						AutIdx: 5,
						Gadget: kg.Gadget,

						MaskNTT: make([]buckler.PublicWitness, len(kg.Gadget)),
						BodyNTT: make([]buckler.PublicWitness, len(kg.Gadget)),

						ErrorCoeffs: make([]buckler.Witness, len(kg.Gadget)),
						ErrorNTT:    make([]buckler.Witness, len(kg.Gadget)),
					},
				}
				prv, vrf, err := buckler.Compile(params, &c)
				assert.NoError(b, err)

				ck := celpc.GenAjtaiCommitKey(params)

				sk := kg.GenSecretKey()
				pk := kg.GenPublicKey(sk)
				rlk := kg.GenRelinKey(sk)
				atkNegOne := kg.GenAutKey(sk, 2*kg.Degree-1)
				atkFive := kg.GenAutKey(sk, 5)
				c = bfv.SetupCircuit{
					PublicKeyCircuit: pk,
					RelinKeyCircuit:  rlk,
					AtkNegOne:        atkNegOne,
					AtkFive:          atkFive,
				}

				b.Run("Prove", func(b *testing.B) {
					for i := 0; i < b.N; i++ {
						proof, _ = prv.Prove(ck, &c)
					}
				})

				b.Run("ProveParallel", func(b *testing.B) {
					for i := 0; i < b.N; i++ {
						proof, _ = prv.ProveParallel(ck, &c)
					}
				})

				b.Run("Verify", func(b *testing.B) {
					for i := 0; i < b.N; i++ {
						verify = vrf.Verify(ck, proof)
					}
				})
			})
		}
	})
}
