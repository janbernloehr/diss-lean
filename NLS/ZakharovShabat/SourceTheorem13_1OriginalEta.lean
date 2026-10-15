import NLS.ZakharovShabat.SourceAngularOriginalEtaIntegral

/-!
# Theorem 13.1(ii) for the literal eta integrals on the original domain

The same simply connected W and normalized psi family from Lemma 12.12
support actual eta integrals at all complex open gaps. These define one
class modulo 2π and have real analytic representatives modulo π. The
representatives and integral values are real on the real-type locus.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The original source domain supports literal eta integrals and analytic representatives. -/
theorem sourceTheorem13_1_original_eta (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W₀ : Set (CoeffPair p), IsOpen W₀ ∧ IsConnected W₀ ∧ realTypeSourceLocus p ⊆ W₀ ∧
      ∃ W : Set (CoeffPair p), IsOpen W ∧ IsSimplyConnected W ∧ realTypeSourceLocus p ⊆ W ∧
        ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
          SourceLemma12_12Data hp hp1 W₀ W s ∧
          (∀ ψ ∈ W, IsRealType (CoeffPair.toMax p ψ) → ∀ n m : ℤ, m ≠ n →
            (sourceAngularBeta hp hp1 n m s ψ).im = 0) ∧
          ∀ m : ℤ,
            IsOpen {ψ : CoeffPair p | ψ ∈ W ∧
              canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m ≠ 0} ∧
            AnalyticOnNhd ℂ (sourceAngularEtaAnalyticPhase hp hp1 m s)
              {ψ : CoeffPair p | ψ ∈ W ∧
                canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m ≠ 0} ∧
            ∀ φ ∈ W, canonicalPeriodicGap hp hp1
              (periodOnePotential φ) (periodOnePotential_mem φ) m ≠ 0 →
              sourceAngularOriginalEta hp hp1 m s φ ∈ sourceAngularOriginalEtaIntegralValues hp hp1 m s φ ∧
              Complex.exp (2*Complex.I*sourceAngularOriginalEta hp hp1 m s φ) =
                sourceAngularEtaAnalyticPhase hp hp1 m s φ ∧
              sourceAngularEtaAnalyticPhase hp hp1 m s φ ≠ 0 ∧
              (IsRealType (CoeffPair.toMax p φ) → (sourceAngularOriginalEta hp hp1 m s φ).im = 0) ∧
              ∃ U : Set (CoeffPair p), ∃ f : CoeffPair p → ℂ,
                IsOpen U ∧ φ ∈ U ∧ U ⊆ W ∧
                (∀ ψ ∈ U, canonicalPeriodicGap hp hp1
                  (periodOnePotential ψ) (periodOnePotential_mem ψ) m ≠ 0) ∧
                AnalyticOnNhd ℂ f U ∧
                (∀ ψ ∈ U, IsRealType (CoeffPair.toMax p ψ) → (f ψ).im = 0) ∧
                ∀ ψ ∈ U, ∃ k : ℤ, sourceAngularOriginalEta hp hp1 m s ψ-f ψ = (k:ℂ)*Real.pi := by
  obtain ⟨W₀,ho,hc,hr,W,hW,hs,hrW,s,H⟩ := sourceLemma12_12 hp hp1
  refine ⟨W₀,ho,hc,hr,W,hW,hs,hrW,s,H,H.beta_original_im_eq_zero,?_⟩
  intro m
  obtain ⟨hO,hA,hN⟩ := H.eta_original_phase_analytic m
  refine ⟨hO,hA,?_⟩
  intro φ hφ hgap
  exact ⟨H.eta_original_integral_mem φ hφ m hgap,H.eta_original_integral_phase φ hφ m hgap,
    hN φ hφ hgap,(fun hreal => H.eta_original_integral_im_eq_zero φ hφ hreal m hgap),
    H.eta_original_value_local_representative φ hφ m hgap⟩

end NLS.ZakharovShabat
