import NLS.Articles.KdVKdV2Frequencies.SmoothSpectralStationarity
import NLS.KdV.HillTraceStationaryAbelianPrimitive

/-! # Actual normalized differentials stationary in both printed PDE fields

The physical Fourier KdV and KdV2 directions annihilate every trace. The
actual invertible period equation therefore supplies a single genuinely
analytic normalized differential germ with both source derivatives zero
and one nearby-real physical matching neighborhood.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ContDiff
open NLS.KdV NLS.ZakharovShabat
namespace NLS.Articles.KdVKdV2Frequencies

/-- One actual normalized differential germ is stationary in both literal
PDE directions, including where the selected or other gaps are closed. -/
theorem exists_hillAbelianSelectedGlobalPsi_both_pde_stationary_extension
    (Q : C(AddCircle (2:ℝ),ℂ))
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2:ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2:ℝ))) 1)
    (hreal : ∀ x : AddCircle (2:ℝ), (Q x).im=0) (n : ℕ) (hn : 1≤n) :
    ∃ G : ℂ × Coeff 2 → ℂ,
      (∀ E : ℂ, AnalyticAt ℂ G (E,SpectralWeight.one.toCoeff (hillContinuousCoefficients Q))) ∧
      (∀ E : ℂ,
        (fderiv ℂ (fun p : Coeff 2 => G (E,p)) (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))
          (kdvFourierDirection (fun x : ℝ => Q (x : AddCircle (2:ℝ))) hf)=0 ∧
        (fderiv ℂ (fun p : Coeff 2 => G (E,p)) (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))
          (kdv2FourierDirection (fun x : ℝ => Q (x : AddCircle (2:ℝ))) hf)=0) ∧
      ∀ᶠ p : RealPeriodOneHillPotential in 𝓝
        (⟨hillContinuousCoefficients Q,hillContinuousCoefficients_mem_even Q hp,
          isRealHillPotential_hillContinuousCoefficients Q hreal⟩ : RealPeriodOneHillPotential),
        ∀ E : ℂ, G (E,SpectralWeight.one.toCoeff p.val)=
          hillAbelianSelectedGlobalPsi p.val p.property.1 p.property.2 n hn E := by
  have h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0 := by
    rw [map_zero]
    exact (Coeff.paritySubspace 0).zero_mem
  have h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)) := by
    rw [map_zero]
    intro k
    simp
  obtain ⟨G,hG,hstat,hmatch⟩ :=
    exists_hillAbelianSelectedGlobalPsi_trace_stationary_joint_analytic_extension
      (hillContinuousCoefficients Q) (hillContinuousCoefficients_mem_even Q hp)
      (isRealHillPotential_hillContinuousCoefficients Q hreal) h0q h0r n hn
  refine ⟨G,hG,?_,hmatch⟩
  intro E
  exact ⟨hstat _ (fun z => fderiv_hillL2Discriminant_kdvFourierDirection_eq_zero Q hf hp z) E,
    hstat _ (fun z => fderiv_hillL2Discriminant_kdv2FourierDirection_eq_zero Q hf hp z) E⟩

end NLS.Articles.KdVKdV2Frequencies
