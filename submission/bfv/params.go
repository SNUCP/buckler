package bfv

import (
	"math"

	"github.com/sp301415/ringo-snark/celpc"
)

var (
	ParamsLogN14Compact = celpc.ParametersLiteral{
		AjtaiSize:     1,
		AjtaiRandSize: 1 + 1,

		Degree:           1 << 14,
		BigIntCommitSize: 1 << 12,

		ModulusBase: 10792,
		Digits:      32,

		RingDegree:     1 << 12,
		LogRingModulus: []int{55, 55},

		CommitStdDev:       10,
		OpeningProofStdDev: 34,
		BlindStdDev:        math.Exp2(20),

		CommitRandStdDev:       20,
		OpeningProofRandStdDev: 68,
		BlindRandStdDev:        math.Exp2(21),

		OpenProofBound: math.Exp2(33.21),
		EvalProofBound: math.Exp2(50.30),
	}

	ParamsLogN14 = celpc.ParametersLiteral{
		AjtaiSize:     1,
		AjtaiRandSize: 1 + 1,

		Degree:           1 << 14,
		BigIntCommitSize: 1 << 13,

		ModulusBase: 10792,
		Digits:      32,

		RingDegree:     1 << 12,
		LogRingModulus: []int{55, 55},

		CommitStdDev:       10,
		OpeningProofStdDev: 34,
		BlindStdDev:        math.Exp2(20),

		CommitRandStdDev:       20,
		OpeningProofRandStdDev: 68,
		BlindRandStdDev:        math.Exp2(21),

		OpenProofBound: math.Exp2(34.75),
		EvalProofBound: math.Exp2(51.94),
	}

	ParamsLogN15Compact = celpc.ParametersLiteral{
		AjtaiSize:     1,
		AjtaiRandSize: 1 + 1,

		Degree:           1 << 15,
		BigIntCommitSize: 1 << 12,

		ModulusBase: 11710,
		Digits:      64,

		RingDegree:     1 << 12,
		LogRingModulus: []int{55, 55},

		CommitStdDev:       10,
		OpeningProofStdDev: 34,
		BlindStdDev:        math.Exp2(21),

		CommitRandStdDev:       20,
		OpeningProofRandStdDev: 68,
		BlindRandStdDev:        math.Exp2(22),

		OpenProofBound: math.Exp2(34.74),
		EvalProofBound: math.Exp2(53.03),
	}

	ParamsLogN15 = celpc.ParametersLiteral{
		AjtaiSize:     1,
		AjtaiRandSize: 1 + 1,

		Degree:           1 << 15,
		BigIntCommitSize: 1 << 14,

		ModulusBase: 11710,
		Digits:      64,

		RingDegree:     1 << 12,
		LogRingModulus: []int{55, 55},

		CommitStdDev:       10,
		OpeningProofStdDev: 34,
		BlindStdDev:        math.Exp2(21),

		CommitRandStdDev:       20,
		OpeningProofRandStdDev: 68,
		BlindRandStdDev:        math.Exp2(22),

		OpenProofBound: math.Exp2(36.67),
		EvalProofBound: math.Exp2(55.03),
	}
)
