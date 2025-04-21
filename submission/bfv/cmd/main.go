package main

import (
	"fmt"
	"time"

	"github.com/sp301415/ringo-snark/buckler"
	"github.com/sp301415/ringo-snark/celpc"
	"github.com/sp301415/ringo-snark/submission/bfv"
)

func main() {
	params := bfv.ParamsLogN15.Compile()
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
	if err != nil {
		panic(err)
	}

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

	now := time.Now()
	pf, err := prv.ProveParallel(ck, &c)
	if err != nil {
		panic(err)
	}
	fmt.Println("Prove:", time.Since(now))

	vf := vrf.Verify(ck, pf)
	fmt.Println("Verify Result:", vf)
}
