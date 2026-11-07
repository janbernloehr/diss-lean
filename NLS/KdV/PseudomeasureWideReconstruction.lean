import NLS.KdV.PseudomeasureWideH1Analytic
import NLS.KdV.PseudomeasureWideCouplingRadius
import NLS.KdV.PseudomeasureInhomogeneousReduction

/-! The original H1 reconstruction family on the full 12n strip, with its
exact resonant coordinates and physical residual, including determinant zeros. -/
noncomputable section
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue
variable (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
variable (n : ℕ) (hn : 2 ≤ n) (z : ℂ) (hz : z ∈ wideHillStrip n)
variable (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
variable (hs : 13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2)

def wideEndpointHillResonantResidual (u : ℂ × ℂ) : FourierLebesgueSpace (2:ℝ) (-1) 2 :=
  singularHillDomainInclusion (endpointHillH1Modes n
    (wideEndpointHillReducedOperator r hr hr1 n hn z hz q hs u))

/-- Every reconstructed amplitude solves the full physical equation with its actual finite residual. -/
theorem wideEndpointHillReconstruct_residual_equation (u : ℂ × ℂ) :
    z • singularHillDomainInclusion (wideEndpointHillReconstruct r hr hr1 n hn z hz q hs u) -
      singularHillOperator (endpointHillHminusOne SpectralWeight.one r hr1 q)
        (wideEndpointHillReconstruct r hr hr1 n hn z hz q hs u) =
      wideEndpointHillResonantResidual r hr hr1 n hn z hz q hs u := by
  have hp := endpointH1Multiplication_physical r hr hr1 q
    (wideEndpointHillReconstruct r hr hr1 n hn z hz q hs u)
  rw [endpointH1Multiplication_wideReconstruct r hr hr1 n hn z hz q hs u] at hp
  apply Subtype.ext
  apply Distribution.ext_coefficients
  intro k
  change z * (singularHillDomainInclusion _).val (mode (-k)) -
    ((singularHillLaplacian _).val (mode (-k)) +
      (hminusOneMultiplication _ _).val (mode (-k))) = _
  rw [singularHillDomainInclusion_coefficient, singularHillLaplacian_coefficient, ← hp,
    endpointHillHminusOne_coefficient]
  change _ = (singularHillDomainInclusion (endpointHillH1Modes n
    (wideEndpointHillReducedOperator r hr hr1 n hn z hz q hs u))).val (mode (-k))
  rw [singularHillDomainInclusion_coefficient, endpointHillH1Modes_coefficient,
    wideEndpointHillReconstruct_coefficient]
  by_cases hkp : k = (n:ℤ)
  · subst k
    simp [wideHillSymbol, show (n:ℤ) ≠ -(n:ℤ) by omega]
    change z*u.1 - ((freeHillValue n:ℂ)*u.1 +
      (wideEndpointHillEffectivePotential r hr hr1 n hn z hz q hs u).val n) =
      (z-(freeHillValue n:ℂ))*u.1 -
        (wideEndpointHillEffectivePotential r hr hr1 n hn z hz q hs u).val n
    ring
  by_cases hkm : k = -(n:ℤ)
  · subst k
    simp [wideHillSymbol, show -(n:ℤ) ≠ (n:ℤ) by omega]
    change z*u.2 - ((freeHillValue n:ℂ)*u.2 +
      (wideEndpointHillEffectivePotential r hr hr1 n hn z hz q hs u).val (-(n:ℤ))) =
      (z-(freeHillValue n:ℂ))*u.2 -
        (wideEndpointHillEffectivePotential r hr hr1 n hn z hz q hs u).val (-(n:ℤ))
    ring
  have hk : k.natAbs ≠ n := fun he => ((hill_resonance_iff n k).mp he).elim hkp hkm
  simp only [if_neg hkp, if_neg hkm, zero_add, wideHillSymbol, if_neg hk]
  have hd := wideHill_denominator_ne_zero n hn z hz k hk
  field_simp [hd]
  ring



theorem endpointReconstructionFamily_eq_wide (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (n : ℕ) (hn : 2 ≤ n)
    (p : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ × ℂ)
    (hz : p.2 ∈ wideHillStrip n)
    (hs : 13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖p.1‖ ≤ 1/2) :
    endpointReconstructionFamily r hr hr1 n p =
      wideEndpointHillReconstruct r hr hr1 n hn p.2 hz p.1 hs := by
  unfold endpointReconstructionFamily wideEndpointHillReconstruct
  rw [endpointH1ResolventFamily_eq_wide r hr1 n hn p.2 hz,
    endpointEffectiveFamily_eq_wide r hr hr1 n hn p hz hs]


theorem analyticAt_endpointReconstructionFamily_wide (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (n : ℕ) (hn : 2 ≤ n)
    (p : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ × ℂ)
    (hz : p.2 ∈ wideHillStrip n)
    (hs : 13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖p.1‖ ≤ 1/2) :
    AnalyticAt ℂ (endpointReconstructionFamily r hr hr1 n) p := by
  have hR := (analyticAt_endpointH1ResolventFamily_wide r hr1 n hn p.2 hz).comp
    ((ContinuousLinearMap.snd ℂ (WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) ℂ).analyticAt p)
  have hE := SchurComplement.analyticAt_compCLM
    (analyticAt_endpointInverseFamily_wide r hr hr1 n hn p hz hs)
    (analyticAt_endpointModePotentialFamily r hr hr1 n p)
  exact analyticAt_const.add (SchurComplement.analyticAt_compCLM hR hE)


theorem endpointReconstructionFamily_coordinates_wide (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (n : ℕ) (hn : 2 ≤ n)
    (p : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ × ℂ)
    (hz : p.2 ∈ wideHillStrip n)
    (hs : 13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖p.1‖ ≤ 1/2) :
    (endpointHillH1Coordinates n).comp (endpointReconstructionFamily r hr hr1 n p) =
      ContinuousLinearMap.id ℂ (ℂ × ℂ) := by
  rw [endpointReconstructionFamily_eq_wide r hr hr1 n hn p hz hs]
  apply ContinuousLinearMap.ext
  intro u
  exact endpointHillH1Coordinates_wideReconstruct r hr hr1 n hn p.2 hz p.1 hs u


theorem endpointReconstructionFamily_residual_wide (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (n : ℕ) (hn : 2 ≤ n)
    (p : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ × ℂ)
    (hz : p.2 ∈ wideHillStrip n)
    (hs : 13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖p.1‖ ≤ 1/2) :
    (endpointPhysicalPencilFamily r hr1 p).comp (endpointReconstructionFamily r hr hr1 n p) =
      singularHillDomainInclusion.comp ((endpointHillH1Modes n).comp (endpointReducedFamily r hr hr1 n p)) := by
  rw [endpointReconstructionFamily_eq_wide r hr hr1 n hn p hz hs,
    endpointReducedFamily_eq_wide r hr hr1 n hn p hz hs]
  apply ContinuousLinearMap.ext
  intro u
  exact wideEndpointHillReconstruct_residual_equation r hr hr1 n hn p.2 hz p.1 hs u


end NLS.KdV
