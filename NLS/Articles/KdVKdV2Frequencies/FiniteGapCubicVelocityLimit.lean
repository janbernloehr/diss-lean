import NLS.KdV.HillCubicFrequencyContourComparison
import NLS.Articles.KdVKdV2Frequencies.FiniteGapDirichletVelocityContours

/-! # Actual finite-gap KdV velocity as the limit of cubic spectral contours

The actual scalar coordinate jet coefficient is identified with the
article's outer cubic contour limit. Finite-hole deformation and the
Hamiltonian frequency identity (69) remain separate obligations.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat NLS.KdV
open scoped ContDiff
namespace NLS.Articles.KdVKdV2Frequencies

/-- The actual finite-gap Dirichlet velocity coefficient is the limit of
actual cubic outer periods, with the article's factor 4/(i*pi), including
a closed selected gap. -/
theorem tendsto_kdv_cubic_frequency_contour
    (Q : C(AddCircle (2:ℝ),ℂ))
    (hreal : ∀ x : AddCircle (2:ℝ), (Q x).im=0)
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2:ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2:ℝ))) 1)
    (hmean : (∫ x in (0:ℝ)..1, Q (x : AddCircle (2:ℝ)))=0)
    (n : ℕ) (hn : 1≤n) :
    let q : RealPeriodOneHillPotential := ⟨hillContinuousCoefficients Q,
      hillContinuousCoefficients_mem_even Q hp,isRealHillPotential_hillContinuousCoefficients Q hreal⟩
    ∀ N : ℕ, n≤N →
      (∀ (k : ℕ) (_hk : 1≤k), N<k → hillRealGapHalfLength q.val q.property.1 q.property.2 k=0) →
    Tendsto (fun M : ℕ => (4/(I*Real.pi) : ℂ)*
      (∮ E in C(0,(centralCircleRadius M)^2),
        hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q.val) E^3*
          hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n hn E/
            hillL2RealCutRoot (SpectralWeight.one.toCoeff q.val) E)) atTop
      (𝓝 (kdvDirichletVelocitySum Q q n hn N)) := by
  dsimp only
  intro N hnN hclosed
  let q : RealPeriodOneHillPotential := ⟨hillContinuousCoefficients Q,
    hillContinuousCoefficients_mem_even Q hp,isRealHillPotential_hillContinuousCoefficients Q hreal⟩
  let f := fun E => hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q.val) E^3*
    hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n hn E/
      hillL2RealCutRoot (SpectralWeight.one.toCoeff q.val) E
  let g := fun E => (-E/2-Q (0 : AddCircle (2:ℝ))/4)*
    (hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n hn E/
      hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q.val) E)
  let a : ℂ := 4/(I*Real.pi)
  have herror := (tendsto_hillL2CubicFrequency_contour_sub_dirichlet Q q.property.1 q.property.2
    hreal hf hp hmean n hn).const_mul a
  have hlim : Tendsto (fun M => a*((∮ E in C(0,(centralCircleRadius M)^2), f E)-
      (∮ E in C(0,(centralCircleRadius M)^2), g E))) atTop (𝓝 0) := by
    simpa only [mul_zero] using herror
  have heq : (fun M : ℕ => a*(∮ E in C(0,(centralCircleRadius M)^2), g E)) =ᶠ[atTop]
      (fun _ => kdvDirichletVelocitySum Q q n hn N) := by
    filter_upwards [eventually_kdvDirichletVelocitySums_eq_contours Q q n hn N hnN hclosed] with M hM
    have htest : (fun E : ℂ => (-2*(Q (0 : AddCircle (2:ℝ))+2*E))*
        (hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n hn E/
          hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q.val) E))=(fun E => 8*g E) := by
      funext E
      dsimp only [g]
      ring
    have hv := hM.1
    rw [htest,circleIntegral.integral_const_mul] at hv
    have hc : (2*Real.pi*I : ℂ)⁻¹*8=a := by
      dsimp only [a]
      field_simp
      ring
    rw [← mul_assoc,hc] at hv
    exact hv.symm
  have hg : Tendsto (fun M : ℕ => a*(∮ E in C(0,(centralCircleRadius M)^2), g E)) atTop
      (𝓝 (kdvDirichletVelocitySum Q q n hn N)) := tendsto_const_nhds.congr' heq.symm
  have hh := hlim.add hg
  simp only [zero_add] at hh
  convert hh using 1
  funext M
  ring

end NLS.Articles.KdVKdV2Frequencies
