import NLS.ZakharovShabat.FloquetHyperbolicBasis
import NLS.ZakharovShabat.L2FloquetBandCriterion
import NLS.ZakharovShabat.L2WholeLineFloquetMass

/-! # Stable and unstable physical monodromy directions inside real gaps -/
noncomputable section
set_option autoImplicit false
open Set Complex Matrix Module
namespace NLS.ZakharovShabat

/-- Outside the original closed bands, the actual physical monodromy has
reciprocal stable and unstable multipliers and an eigenbasis. -/
theorem source_gap_exists_stable_unstable_eigenbasis (φ : CoeffPair 2)
    (hφ : IsRealType (CoeffPair.toMax 2 φ)) (x : ℝ)
    (hx : x ∉ sourceFloquetBandSet (by simp) (by norm_num) φ) :
    ∃ (μ ν : ℂ) (b : Basis (Fin 2) ℂ (Fin 2 → ℂ)),
      μ * ν = 1 ∧ 0 < ‖μ‖ ∧ ‖μ‖ < 1 ∧ 1 < ‖ν‖ ∧
      l2Monodromy (sourcePhysicalL2 φ) x *ᵥ b 0 = μ • b 0 ∧
      l2Monodromy (sourcePhysicalL2 φ) x *ᵥ b 1 = ν • b 1 := by
  apply exists_stable_unstable_eigenbasis _ (det_l2Monodromy _ _)
  exact fun h => hx ((source_l2_unit_characteristic_root_iff_mem_band φ hφ x).mp h)

/-- The basis resolves every initial vector into the two actual monodromy
modes; it is a full decomposition, not just existence of separate roots. -/
theorem l2WholeLineSolution_eigenbasis_decomposition (u : IntervalPairL2) (z : ℂ)
    (b : Basis (Fin 2) ℂ (Fin 2 → ℂ)) (v : Fin 2 → ℂ) (t : ℝ) :
    l2WholeLineSolution u z v t =
      b.repr v 0 • l2WholeLineSolution u z (b 0) t +
      b.repr v 1 • l2WholeLineSolution u z (b 1) t := by
  have hv : v = b.repr v 0 • b 0 + b.repr v 1 • b 1 := by
    simpa only [Fin.sum_univ_two] using (b.sum_repr v).symm
  conv_lhs => rw [hv]
  simp only [l2WholeLineSolution,Matrix.mulVec_add,Matrix.mulVec_smul,
    Pi.add_apply,Pi.smul_apply,Prod.smul_mk,Prod.mk_add_mk]

end NLS.ZakharovShabat
