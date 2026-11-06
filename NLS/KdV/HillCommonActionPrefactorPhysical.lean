import NLS.KdV.HillCommonComplexActionPrefactor
import NLS.KdV.HillActionGapPrefactor

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
open scoped ENNReal Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem exists_hillComplexActionGapPrefactor_bounded_real_physical_matching (B : ℝ) :
    ∃ N : ℕ, 1≤N ∧ ∀ q : WeightedCoeff SpectralWeight.one.toWeight 2,
      ∀ hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0,
      ∀ hr : IsRealHillPotential (SpectralWeight.one.toCoeff q), ‖SpectralWeight.one.toCoeff q‖≤B →
        ∀ k : ℕ, N≤k → hillComplexActionGapPrefactor h0q h0r k (SpectralWeight.one.toCoeff q)=
          hillActionGapPrefactor q hq hr k := by
  obtain ⟨N,hN,hmatch⟩ := exists_hillComplexActionGapRatio_bounded_real_physical_matching h0q h0r B
  refine ⟨N,hN,?_⟩
  intro q hq hr hp k hk
  have hR := hillActionGapRatio_real_positive q hq hr k (hN.trans hk)
  have he : hillActionGapRatio q hq hr k=((hillActionGapRatio q hq hr k).re:ℂ) := by
    apply Complex.ext <;> simp [hR.2]
  rw [hillComplexActionGapPrefactor,hmatch q hq hr hp k hk,he,← ofReal_ofNat,← ofReal_mul,
    Complex.sqrt_of_nonneg (by exact_mod_cast (mul_nonneg (by norm_num : (0:ℝ)≤2) hR.1.le)),ofReal_re]
  rfl

end NLS.KdV
