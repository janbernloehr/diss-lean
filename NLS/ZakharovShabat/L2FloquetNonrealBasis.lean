import NLS.ZakharovShabat.FloquetHyperbolicBasis
import NLS.ZakharovShabat.L2WholeLineBandSpectrum

/-! # Hyperbolic physical Floquet modes at every nonreal parameter -/
noncomputable section
set_option autoImplicit false
open Complex Matrix Module
namespace NLS.ZakharovShabat

/-- A nonreal parameter has no nonzero unit-multiplier physical Floquet mode. -/
theorem l2Monodromy_nonreal_eigenvalue_norm_ne_one (u : IntervalPairL2)
    (hu : IsClassicalRealType (intervalL2Representative u)) (z : ℂ) (hz : z.im ≠ 0)
    (μ : ℂ) (v : Fin 2 → ℂ) (hv0 : v ≠ 0) (hv : l2Monodromy u z *ᵥ v = μ • v) :
    ‖μ‖ ≠ 1 := by
  intro hμ
  exact hz (wholeLineSpectrum_subset_real u hu
    (mem_wholeLineSpectrum_of_unit_floquet u hu z μ hμ v hv0 hv))

/-- No characteristic root lies on the unit circle at a nonreal parameter. -/
theorem l2Monodromy_nonreal_no_unit_characteristic_root (u : IntervalPairL2)
    (hu : IsClassicalRealType (intervalL2Representative u)) (z : ℂ) (hz : z.im ≠ 0) :
    ¬ ∃ μ : ℂ, ‖μ‖ = 1 ∧ (l2Monodromy u z-μ • 1).det = 0 := by
  rintro ⟨μ,hμ,hd⟩
  obtain ⟨v,hv0,hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
  simp only [Matrix.sub_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,sub_eq_zero] at hv
  exact l2Monodromy_nonreal_eigenvalue_norm_ne_one u hu z hz μ v hv0 hv hμ

/-- At every nonreal parameter the actual physical monodromy has reciprocal
stable and unstable multipliers and a full eigenbasis. -/
theorem l2Monodromy_nonreal_exists_stable_unstable_eigenbasis (u : IntervalPairL2)
    (hu : IsClassicalRealType (intervalL2Representative u)) (z : ℂ) (hz : z.im ≠ 0) :
    ∃ (μ ν : ℂ) (b : Basis (Fin 2) ℂ (Fin 2 → ℂ)),
      μ*ν = 1 ∧ 0 < ‖μ‖ ∧ ‖μ‖ < 1 ∧ 1 < ‖ν‖ ∧
      l2Monodromy u z *ᵥ b 0 = μ • b 0 ∧ l2Monodromy u z *ᵥ b 1 = ν • b 1 :=
  exists_stable_unstable_eigenbasis _ (det_l2Monodromy u z)
    (l2Monodromy_nonreal_no_unit_characteristic_root u hu z hz)

end NLS.ZakharovShabat
