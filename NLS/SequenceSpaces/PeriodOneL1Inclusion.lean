import NLS.SequenceSpaces.PeriodOneHminusOneDensity

/-! The dense literal inclusion of absolutely summable unit-period
coefficients in the native H-minus-one space. -/
noncomputable section
open scoped ENNReal
namespace NLS

def periodOneL1Inclusion : Coeff 1 →L[ℂ] PeriodOneHminusOne :=
  periodOneL2Inclusion.comp (Coeff.exponentInclusion (by norm_num : (1:ℝ≥0∞) ≤ 2))

@[simp] theorem periodOneL1Inclusion_apply (a : Coeff 1) (k : ℤ) :
    (periodOneL1Inclusion a).val k = a k := by
  rw [periodOneL1Inclusion,ContinuousLinearMap.comp_apply,periodOneL2Inclusion_apply,
    Coeff.exponentInclusion_apply]

theorem periodOneL1Inclusion_ofFinsupp (a : ℤ →₀ ℂ) :
    periodOneL1Inclusion (Coeff.ofFinsupp a) =
      WeightedCoeff.ofFinsupp (Weight.sobolev (-1)) 2 a := by
  apply Subtype.ext
  funext k
  rw [periodOneL1Inclusion_apply,Coeff.ofFinsupp_apply,WeightedCoeff.ofFinsupp_apply]

theorem denseRange_periodOneL1Inclusion : DenseRange periodOneL1Inclusion := by
  apply (WeightedCoeff.denseRange_ofFinsupp (Weight.sobolev (-1)) 2 (by norm_num)).mono
  rintro _ ⟨a,rfl⟩
  exact ⟨Coeff.ofFinsupp a,periodOneL1Inclusion_ofFinsupp a⟩

end NLS
