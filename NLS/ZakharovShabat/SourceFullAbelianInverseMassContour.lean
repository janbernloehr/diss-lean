import NLS.ZakharovShabat.SourceFullAbelianMassCoefficient
import NLS.ComplexAnalysis.InverseSquareMassContour
import NLS.ComplexAnalysis.FilledSquareOverZero

/-! The actual finite-gap full primitive has a physical mass contour with
weight 1/z. A collapsed central endpoint at zero supplies an analytic
filling on the ENTIRE original open-gap complement before decomposition. -/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
open NLS.ComplexAnalysis
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}

theorem exists_sourceFullAbelian_finiteGap_inverse_mass_contour
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (φ : realTypeSourceSubmodule p)
    (hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius)
    (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    ∃ T : ℝ, 0 < T ∧ ∀ R : ℝ, T ≤ R →
      (∮ z in C(0,R), (sourceFullAbelianPrimitive hp hp1 W 0 (z,φ.val))^2/z)=
        (2*Real.pi*I:ℂ)*(∑' k : ℤ, φ.val.fst k*φ.val.snd (-k)) := by
  obtain ⟨S,_,r,hr,_,A,hA,hA0,hder,hval⟩ := exists_sourceFullAbelian_finiteGap_mass_inversion C φ hφ hf
  obtain ⟨T,hT,hc⟩ := exists_phase_inverse_square_mass_contour A
    (hA 0 (mem_ball_self hr)) hA0 _ hder
  refine ⟨max (S+1) T,hT.trans_le (le_max_right _ _),?_⟩
  intro R hR
  rw [← hc R ((le_max_right _ _).trans hR)]
  apply circleIntegral.integral_congr (hT.trans_le ((le_max_right _ _).trans hR)).le
  intro z hz
  have hn : ‖z‖=R := by simpa only [mem_sphere,dist_zero_right] using hz
  have hSz : S < ‖z‖ := by rw [hn]; linarith [le_max_left (S+1) T]
  dsimp only
  rw [hval 0 z hSz]
  simp only [Int.cast_zero,mul_zero,add_zero]

namespace SourceFullAbelianUniformCauchyFamily

/-- The central normalization is an exact value at the filled endpoint. -/
theorem central_zero_value_and_mem (C : SourceFullAbelianUniformCauchyFamily hp hp1 W)
    (ψ : CoeffPair p) (hψ : ψ ∈ ball C.discs.source.val C.discs.sourceRadius)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) 0=0)
    (h0 : (0:ℂ) ∈ ({canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) 0,
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) 0} : Set ℂ)) :
    sourceFullAbelianPrimitive hp hp1 W 0 (0,ψ)=0 ∧ (0:ℂ) ∈ sourceOpenGapComplement hp hp1 ψ := by
  refine ⟨?_,C.ball_subset_openGapComplement_of_collapsed 0 ψ hψ hgap (C.endpoint_mem_ball 0 ψ hψ 0 h0)⟩
  simpa only [sub_self,mul_zero] using C.fullPrimitive_collapsed_endpoint_value 0 0 ψ hψ hgap 0 h0

/-- Remove the central pole BEFORE splitting the physical mass contour. -/
theorem analytic_filled_inverse_square_of_central_zero
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (φ : realTypeSourceSubmodule p)
    (hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) 0=0)
    (h0 : (0:ℂ) ∈ ({canonicalPeriodicLeft hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) 0,
      canonicalPeriodicRight hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) 0} : Set ℂ)) :
    AnalyticOnNhd ℂ (filledSquareOverZero (fun z => sourceFullAbelianPrimitive hp hp1 W 0 (z,φ.val)))
      (sourceOpenGapComplement hp hp1 φ.val) := by
  obtain ⟨D⟩ := C.charts φ.val hφ
  exact analyticOnNhd_filledSquareOverZero _ _
    (isOpen_sourceOpenGapComplement_of_realType hp hp1 φ.val φ.property)
    (C.central_zero_value_and_mem φ.val hφ hgap h0).2 (sourceFullAbelianPrimitive_spectral_analytic D 0)

end SourceFullAbelianUniformCauchyFamily
end NLS.ZakharovShabat
