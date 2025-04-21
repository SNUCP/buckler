package bfv

import (
	"math/big"

	"github.com/sp301415/ringo-snark/buckler"
)

type SecretKeyCircuit struct {
	Coeffs buckler.Witness
	NTT    buckler.Witness
}

func (c *SecretKeyCircuit) Define(ctx *buckler.Context) {
	ctx.AddNTTConstraint(c.Coeffs, c.NTT)
	ctx.AddInfNormConstraint(c.Coeffs, 1)
}

type PublicKeyCircuit struct {
	SecretKeyCircuit

	PublicKeyNTT [2]buckler.PublicWitness

	ErrorCoeffs buckler.Witness
	ErrorNTT    buckler.Witness
}

func (c *PublicKeyCircuit) Define(ctx *buckler.Context) {
	ctx.AddNTTConstraint(c.ErrorCoeffs, c.ErrorNTT)

	ctx.AddInfNormConstraint(c.ErrorCoeffs, 1)

	var pkConstraint buckler.ArithmeticConstraint
	pkConstraint.AddTerm(big.NewInt(1), c.PublicKeyNTT[0])
	pkConstraint.AddTerm(big.NewInt(1), c.PublicKeyNTT[1], c.SecretKeyCircuit.NTT)
	pkConstraint.AddTerm(big.NewInt(-1), nil, c.ErrorNTT)
	ctx.AddArithmeticConstraint(pkConstraint)
}

type PELTACircuit struct {
	PublicKeyCircuit
}

func (c *PELTACircuit) Define(ctx *buckler.Context) {
	c.SecretKeyCircuit.Define(ctx)
	c.PublicKeyCircuit.Define(ctx)
}

type EncryptionCircuit struct {
	PublicKeyCircuit

	CiphertextNTT [2]buckler.PublicWitness

	AuxKeyCoeffs buckler.Witness
	AuxKeyNTT    buckler.Witness

	Delta         *big.Int
	MessageCoeffs buckler.Witness
	MessageNTT    buckler.Witness

	ErrorCoeffs [2]buckler.Witness
	ErrorNTT    [2]buckler.Witness
}

func (c *EncryptionCircuit) Define(ctx *buckler.Context) {
	ctx.AddNTTConstraint(c.AuxKeyCoeffs, c.AuxKeyNTT)
	ctx.AddNTTConstraint(c.MessageCoeffs, c.MessageNTT)
	ctx.AddNTTConstraint(c.ErrorCoeffs[0], c.ErrorNTT[0])
	ctx.AddNTTConstraint(c.ErrorCoeffs[1], c.ErrorNTT[1])

	ctx.AddInfNormConstraint(c.AuxKeyCoeffs, 1)
	ctx.AddInfNormConstraint(c.MessageCoeffs, 1<<16)
	ctx.AddInfNormConstraint(c.ErrorCoeffs[0], 1)
	ctx.AddInfNormConstraint(c.ErrorCoeffs[1], 1)

	var bodyConstraint buckler.ArithmeticConstraint
	bodyConstraint.AddTerm(big.NewInt(1), c.CiphertextNTT[0])
	bodyConstraint.AddTerm(big.NewInt(1), c.PublicKeyCircuit.PublicKeyNTT[0], c.AuxKeyNTT)
	bodyConstraint.AddTerm(big.NewInt(0).Neg(c.Delta), nil, c.MessageNTT)
	bodyConstraint.AddTerm(big.NewInt(-1), nil, c.ErrorNTT[0])
	ctx.AddArithmeticConstraint(bodyConstraint)

	var maskConstraint buckler.ArithmeticConstraint
	maskConstraint.AddTerm(big.NewInt(1), c.CiphertextNTT[1])
	maskConstraint.AddTerm(big.NewInt(1), c.PublicKeyCircuit.PublicKeyNTT[1], c.AuxKeyNTT)
	maskConstraint.AddTerm(big.NewInt(-1), nil, c.ErrorNTT[1])
	ctx.AddArithmeticConstraint(maskConstraint)
}

type DecryptionCircuit struct {
	Degree int

	PublicKeyCircuit

	MaskNTT    buckler.PublicWitness
	DecMaskNTT buckler.PublicWitness
	BodyNTT    buckler.PublicWitness

	AuxKeyCoeffs buckler.Witness
	AuxKeyNTT    buckler.Witness

	ErrorCoeffs buckler.Witness
	ErrorNTT    buckler.Witness

	QuoCoeffs buckler.Witness
	QuoNTT    buckler.Witness
}

func (c *DecryptionCircuit) Define(ctx *buckler.Context) {
	c.PublicKeyCircuit.Define(ctx)

	ctx.AddNTTConstraint(c.AuxKeyCoeffs, c.AuxKeyNTT)
	ctx.AddNTTConstraint(c.ErrorCoeffs, c.ErrorNTT)
	ctx.AddNTTConstraint(c.QuoCoeffs, c.QuoNTT)

	ctx.AddInfNormConstraint(c.AuxKeyCoeffs, 1)
	ctx.AddInfNormConstraint(c.ErrorCoeffs, 1)
	ctx.AddInfNormConstraint(c.QuoCoeffs, uint64(1*(c.Degree+1)))

	var ddecConstraint buckler.ArithmeticConstraint
	ddecConstraint.AddTerm(big.NewInt(1), c.BodyNTT)
	ddecConstraint.AddTerm(big.NewInt(-1), c.MaskNTT, c.SecretKeyCircuit.NTT)
	ddecConstraint.AddTerm(big.NewInt(-1), c.DecMaskNTT, c.AuxKeyNTT)
	ddecConstraint.AddTerm(big.NewInt(-1), nil, c.ErrorNTT)
	ddecConstraint.AddTerm(big.NewInt(0).Lsh(big.NewInt(1), 128), nil, c.QuoNTT)
	ctx.AddArithmeticConstraint(ddecConstraint)
}

type RelinKeyCircuit struct {
	SecretKeyCircuit

	Gadget []*big.Int

	MaskNTT [2][]buckler.PublicWitness
	BodyNTT [3][]buckler.PublicWitness

	AuxKeyCoeffs buckler.Witness
	AuxKeyNTT    buckler.Witness

	ErrorCoeffs [3][]buckler.Witness
	ErrorNTT    [3][]buckler.Witness
}

func (c *RelinKeyCircuit) Define(ctx *buckler.Context) {
	level := len(c.Gadget)

	ctx.AddNTTConstraint(c.AuxKeyCoeffs, c.AuxKeyNTT)
	ctx.AddInfNormConstraint(c.AuxKeyCoeffs, 1)

	for i := 0; i < level; i++ {
		ctx.AddNTTConstraint(c.ErrorCoeffs[0][i], c.ErrorNTT[0][i])
		ctx.AddNTTConstraint(c.ErrorCoeffs[1][i], c.ErrorNTT[1][i])
		ctx.AddNTTConstraint(c.ErrorCoeffs[2][i], c.ErrorNTT[2][i])

		ctx.AddInfNormConstraint(c.ErrorCoeffs[0][i], 1)
		ctx.AddInfNormConstraint(c.ErrorCoeffs[1][i], 1)
		ctx.AddInfNormConstraint(c.ErrorCoeffs[2][i], 1)
	}

	for i := 0; i < level; i++ {
		negGadget := big.NewInt(0).Neg(c.Gadget[i])

		var rlk0Constraint buckler.ArithmeticConstraint
		rlk0Constraint.AddTerm(big.NewInt(1), c.BodyNTT[0][i])
		rlk0Constraint.AddTerm(big.NewInt(1), c.MaskNTT[0][i], c.SecretKeyCircuit.NTT)
		rlk0Constraint.AddTerm(big.NewInt(-1), nil, c.ErrorNTT[0][i])
		ctx.AddArithmeticConstraint(rlk0Constraint)

		var rlk1Constraint buckler.ArithmeticConstraint
		rlk1Constraint.AddTerm(big.NewInt(1), c.BodyNTT[1][i])
		rlk1Constraint.AddTerm(big.NewInt(1), c.MaskNTT[0][i], c.AuxKeyNTT)
		rlk1Constraint.AddTerm(negGadget, nil, c.SecretKeyCircuit.NTT)
		rlk1Constraint.AddTerm(big.NewInt(-1), nil, c.ErrorNTT[1][i])
		ctx.AddArithmeticConstraint(rlk1Constraint)

		var rlk2Constraint buckler.ArithmeticConstraint
		rlk2Constraint.AddTerm(big.NewInt(1), c.BodyNTT[2][i])
		rlk2Constraint.AddTerm(big.NewInt(1), c.MaskNTT[1][i], c.SecretKeyCircuit.NTT)
		rlk2Constraint.AddTerm(c.Gadget[i], nil, c.AuxKeyNTT)
		rlk2Constraint.AddTerm(big.NewInt(-1), nil, c.ErrorNTT[2][i])
		ctx.AddArithmeticConstraint(rlk2Constraint)
	}
}

type AutKeyCircuit struct {
	SecretKeyCircuit

	AutIdx int

	Gadget []*big.Int

	MaskNTT []buckler.PublicWitness
	BodyNTT []buckler.PublicWitness

	SkAutNTT buckler.Witness

	ErrorCoeffs []buckler.Witness
	ErrorNTT    []buckler.Witness
}

func (c *AutKeyCircuit) Define(ctx *buckler.Context) {
	level := len(c.Gadget)

	ctx.AddAutomorphismNTTConstraint(c.SecretKeyCircuit.NTT, c.AutIdx, c.SkAutNTT)

	for i := 0; i < level; i++ {
		ctx.AddNTTConstraint(c.ErrorCoeffs[i], c.ErrorNTT[i])
		ctx.AddInfNormConstraint(c.ErrorCoeffs[i], 1)

		var atkConstraint buckler.ArithmeticConstraint
		atkConstraint.AddTerm(big.NewInt(1), c.BodyNTT[i])
		atkConstraint.AddTerm(big.NewInt(1), c.MaskNTT[i], c.SecretKeyCircuit.NTT)
		atkConstraint.AddTerm(big.NewInt(0).Neg(c.Gadget[i]), nil, c.SkAutNTT)
		atkConstraint.AddTerm(big.NewInt(-1), nil, c.ErrorNTT[i])
		ctx.AddArithmeticConstraint(atkConstraint)
	}
}

type SetupCircuit struct {
	PublicKeyCircuit
	RelinKeyCircuit
	AtkNegOne AutKeyCircuit
	AtkFive   AutKeyCircuit
}

func (c *SetupCircuit) Define(ctx *buckler.Context) {
	c.PublicKeyCircuit.SecretKeyCircuit.Define(ctx)
	c.PublicKeyCircuit.Define(ctx)
	c.RelinKeyCircuit.Define(ctx)
	c.AtkNegOne.Define(ctx)
	c.AtkFive.Define(ctx)
}
