import NLS.Articles.KdVPseudomeasures.SourceWienerSpectralAdapter
import NLS.KdV.HillWienerCouplingEnvelope

/-! The common summable coupling envelope for the SAME full complex
original Wiener distribution used by the canonical spectral labels. -/
noncomputable section
open scoped ENNReal
open NLS.KdV NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue
namespace NLS.Articles.KdVPseudomeasures

theorem exists_uniform_sourceWienerCoupling_envelope (R : ℝ) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ w : SpectralWeight,
      ∀ q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev 0) 1, ‖q‖ ≤ R →
        ∃ H : Coeff 1, ‖H‖ ≤ 2*‖q‖ ∧
          ∀ n : ℕ, 1 ≤ n → N ≤ n → ∀ z : ℂ, z ∈ reducedHillStrip n →
            w (2*(n:ℤ))*‖endpointUpperCoupling 0 (by norm_num) (by norm_num) n
              (sourceEndpointCoefficients 0 (sourceWienerPlain w q),z)‖ ≤ ‖H (2*(n:ℤ))‖ ∧
            w (2*(n:ℤ))*‖endpointLowerCoupling 0 (by norm_num) (by norm_num) n
              (sourceEndpointCoefficients 0 (sourceWienerPlain w q),z)‖ ≤ ‖H (-(2*(n:ℤ)))‖ := by
  obtain ⟨N,hN,hbound⟩ := exists_uniform_hillWienerCoupling_envelope R
  refine ⟨N,hN,?_⟩
  intro w q hq
  have hcoef : ‖sourceWienerEndpointCoefficients w q‖ ≤ R := by
    rwa [norm_sourceWienerEndpointCoefficients]
  obtain ⟨H,hH,hHc⟩ := hbound w (sourceWienerEndpointCoefficients w q) hcoef
  refine ⟨H,by simpa only [norm_sourceWienerEndpointCoefficients] using hH,?_⟩
  intro n hn hNn z hz
  obtain ⟨hb,hc⟩ := hHc n hn hNn z hz
  have he := sourceWienerPlain_coefficients w q
  have heB := congrArg (fun a : WeightedCoeff (SpectralWeight.one.negativeSobolev 0) ⊤ =>
    endpointUpperCoupling 0 (by norm_num) (by norm_num) n (a,z)) he
  have heC := congrArg (fun a : WeightedCoeff (SpectralWeight.one.negativeSobolev 0) ⊤ =>
    endpointLowerCoupling 0 (by norm_num) (by norm_num) n (a,z)) he
  exact ⟨(congrArg (fun c : ℂ => w (2*(n:ℤ))*‖c‖) heB).le.trans hb,
    (congrArg (fun c : ℂ => w (2*(n:ℤ))*‖c‖) heC).le.trans hc⟩

end NLS.Articles.KdVPseudomeasures
