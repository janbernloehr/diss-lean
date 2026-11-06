import NLS.ZakharovShabat.SourceFullAbelianHamiltonianReduction

/-! # Actual normalized analytic inversion phases at every real finite-gap source -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The original finite-gap discriminant has a normalized analytic phase
at infinity. The primitive, its exterior analytic remainder and its zero
constant term are constructed from the actual source, with no phase input. -/
theorem exists_sourceFiniteGap_discriminant_phase
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    ∃ R : ℝ, 0 < R ∧ ∃ A : ℂ → ℂ, AnalyticAt ℂ A 0 ∧ A 0 = 0 ∧
      ∀ z : ℂ, R < ‖z‖ → 2*cosh (-I*z+A z⁻¹) =
        canonicalDiscriminant hp (periodOnePotential φ.val) z := by
  obtain ⟨W,_hW,_hreal,hfamilies⟩ := exists_sourceFullAbelianUniformCauchyFamilies hp hp1
  obtain ⟨C,hC⟩ := hfamilies φ
  have hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius := by
    rw [hC]
    exact mem_ball_self C.discs.sourceRadius_pos
  obtain ⟨R,hR,r,hr,_hrR,A,hA,hA0,hrep⟩ :=
    exists_sourceFullAbelian_finiteGap_inversion_remainder C φ hφ hf
  obtain ⟨T,_hT,houtside⟩ := exists_exterior_subset_sourceOpenGapComplement_finiteGap hp hp1 φ hf
  obtain ⟨D⟩ := C.charts φ.val hφ
  refine ⟨max R T,hR.trans_le (le_max_left _ _),A,hA 0 (mem_ball_self hr),hA0,?_⟩
  intro z hz
  rw [←hrep z ((le_max_left _ _).trans_lt hz)]
  exact two_cosh_sourceFullAbelianPrimitive_zero φ D z
    (houtside ((le_max_right _ _).trans_lt hz))

end NLS.ZakharovShabat
