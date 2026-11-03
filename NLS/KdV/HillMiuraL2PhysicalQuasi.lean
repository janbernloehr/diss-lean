import NLS.KdV.HillMiuraL2Discriminant
import NLS.MKdV.L2QuasiHillDiscriminant
import NLS.ZakharovShabat.SourcePhysicalL2Equiv

/-! # The original L2 Miura trace is the actual rough quasi-Hill trace

The physical scalar profile is the unit-interval Fourier isometry of the
original coefficients. No regularity upgrade of the L2 lift is needed.
The equality includes zero energy and uses neither an unspecified
continuous extension nor a singular square-root state map.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
open NLS.Fourier NLS.ZakharovShabat NLS.MKdV
namespace NLS.KdV

theorem intervalL2Diagonal_unitSynthesis (u : Coeff 2) :
    intervalL2Diagonal (unitL2SynthesisEquiv u) = sourcePhysicalL2 (hillMiuraDiagonal u) := by
  rw [← sourcePhysicalL2Equiv_apply]
  apply WithLp.ofLp_injective
  change (unitL2SynthesisEquiv u,unitL2SynthesisEquiv u) =
    (unitL2SynthesisEquiv (hillMiuraDiagonal u).fst,unitL2SynthesisEquiv (hillMiuraDiagonal u).snd)
  rw [hillMiuraDiagonal_fst,hillMiuraDiagonal_snd]

/-- The all-energy trace of the actual rough quasi-derivative initial-value
problem is exactly the previously constructed L2 Miura discriminant. -/
theorem hillMiuraL2Discriminant_eq_physicalQuasi (u : Coeff 2) (lambda : ℂ) :
    hillMiuraL2Discriminant u lambda = l2QuasiHillDiscriminant (unitL2SynthesisEquiv u) lambda := by
  rw [hillMiuraL2Discriminant,hillMiuraFrequencyTrace,canonicalDiscriminant_eq_l2_source,
    ← intervalL2Diagonal_unitSynthesis,← l2QuasiHillDiscriminant_sq_eq_diagonal,
    NLS.ComplexAnalysis.complex_sqrt_sq]

end NLS.KdV
