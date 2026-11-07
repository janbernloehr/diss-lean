import NLS.Articles.KdVKdV2Frequencies.OffDiagonalFrequencyPairCharts
import NLS.Articles.KdVKdV2Frequencies.WeightedPairDiscriminant
import NLS.KdV.PhysicalOffDiagonalIsospectral
import NLS.KdV.ClassicalPeriodOperator

/-! The stronger off-diagonal packet is invariant on every real action
fiber within its fixed native inverse and physical Miura chart. -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.KdV NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies.OffDiagonalFrequencyPairChart
variable {D : GlobalRoughAbelianForwardData} {β t ε : ℝ}

theorem correction_eq_of_real_actions (P : OffDiagonalFrequencyPairChart D β t ε)
    (z : Coeff 2 × Coeff 2) (hz : z∈P.domain) (w : Coeff 2 × Coeff 2) (hw : w∈P.domain)
    (hzr : z∈Coeff.realPairLocus 2) (hwr : w∈Coeff.realPairLocus 2)
    (ha : quadraticActionsExponent (q := 1) w=quadraticActionsExponent z) (n : ℕ+) :
    P.correction n w=P.correction n z := by
  apply P.physicalChart.offDiagonalCorrection_eq_of_discriminant_eq
    (P.roughPotential z) (P.roughPotential w) (P.rough_mem z hz) (P.rough_mem w hw)
    (P.rough_real z hz hzr) (P.rough_real w hw hwr)
  exact (discriminant_eq_of_weighted_pair_actions D t (P.roughPotential z) (P.roughPotential w)
    (P.rough_real z hz hzr) (P.rough_real w hw hwr) (P.rough_zero z hz) (P.rough_zero w hw)
    z w (P.rough_signed z hz hzr) (P.rough_signed w hw hwr) ha).symm

theorem packet_eq_of_real_actions (P : OffDiagonalFrequencyPairChart D β t ε)
    (z : Coeff 2 × Coeff 2) (hz : z∈P.domain) (w : Coeff 2 × Coeff 2) (hw : w∈P.domain)
    (hzr : z∈Coeff.realPairLocus 2) (hwr : w∈Coeff.realPairLocus 2)
    (ha : quadraticActionsExponent (q := 1) w=quadraticActionsExponent z) : P.packet w=P.packet z := by
  ext j
  by_cases hj : 0<j
  · let n := positiveIntegerIndex j hj
    have hnj : (n : ℤ)=j := positiveIntegerIndex_int j hj
    rw [←hnj,P.positive w hw n,P.positive z hz n]
    exact congrArg (fun v : ℂ => (Weight.sobolev (-(β-ε)) (n : ℤ) : ℂ)*v)
      (P.correction_eq_of_real_actions z hz w hw hzr hwr ha n)
  · rw [P.nonpositive w hw j (by omega),P.nonpositive z hz j (by omega)]

end NLS.Articles.KdVKdV2Frequencies.OffDiagonalFrequencyPairChart
