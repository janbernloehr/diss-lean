import NLS.SequenceSpaces.PositiveDeletedSpace

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal ComplexConjugate

namespace NLS.Coeff



def positiveDeletedConjugate (p : ℝ≥0∞) [Fact (1 ≤ p)] (n : ℤ) (a : PositiveDeletedCoeff p n) :
    PositiveDeletedCoeff p n := by
  have hfix : positiveDeletedProjection p n (star (a : Coeff p)) = star (a : Coeff p) := by
    apply (positiveDeletedProjection_eq_self_iff p n _).mpr
    intro m hm
    have hz := (positiveDeletedProjection_eq_self_iff p n _).mp (positiveDeleted_fixed p n a) m hm
    simp only [lp.star_apply,hz,star_zero]
  refine ⟨star (a : Coeff p),?_⟩
  change star (a : Coeff p)-positiveDeletedProjection p n (star (a : Coeff p)) = 0
  rw [hfix,sub_self]

theorem positiveDeletedConjugate_coe (p : ℝ≥0∞) [Fact (1 ≤ p)] (n : ℤ) (a : PositiveDeletedCoeff p n) :
    (positiveDeletedConjugate p n a : Coeff p) = star (a : Coeff p) := rfl

theorem positiveDeletedConjugate_zero (p : ℝ≥0∞) [Fact (1 ≤ p)] (n : ℤ) :
    positiveDeletedConjugate p n (0 : PositiveDeletedCoeff p n) = 0 := by
  apply Subtype.ext
  change star (0 : Coeff p) = 0
  exact star_zero _

theorem continuous_positiveDeletedConjugate (p : ℝ≥0∞) [Fact (1 ≤ p)] (n : ℤ) :
    Continuous (positiveDeletedConjugate p n) := by
  have hc : Continuous (fun a : PositiveDeletedCoeff p n => star (a : Coeff p)) := continuous_subtype_val.star
  exact hc.subtype_mk (fun a => (positiveDeletedConjugate p n a).property)

end NLS.Coeff
