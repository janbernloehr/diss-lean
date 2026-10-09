import NLS.ZakharovShabat.L2HermitianOperatorBound

/-! # Source Lemma G.1: the L2 fundamental-solution estimate

Printed page 135, on [0,1] × ℂ × L²_c. The actual remainder M-E and actual
first Born integral use the Hermitian induced operator norm, with weight
exp(-|Im z| t). The coefficient is the original Hilbert L2 norm times its
exponential. The source has no continuity hypothesis on the potential.
-/
noncomputable section
open Set MeasureTheory
open NLS.LinearVolterra
namespace NLS.ZakharovShabat

/-- Lemma G.1 on its full physical L2 domain, with the literal coefficient
and the square integral of the actual normalized first Born operator. -/
theorem sourceLemmaG1 (φ : IntervalPairL2) (z : ℂ) (t : Icc (0:ℝ) 1) :
    l2NormalizedHermitianRemainder φ z t ≤ l2NormalizedHermitianFirstBorn φ z t+
      ‖φ‖*Real.exp ‖φ‖*Real.sqrt (∫ s in (0:ℝ)..t.val,
        (extend (l2NormalizedHermitianFirstBorn φ z) s)^2) :=
  l2HermitianOperator_le_L2_firstBorn φ z t

end NLS.ZakharovShabat
