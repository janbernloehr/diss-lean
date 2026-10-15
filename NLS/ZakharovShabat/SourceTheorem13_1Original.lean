import NLS.ZakharovShabat.SourceAngularOriginalCanonicalDifferentials

/-!
# Theorem 13.1 on one retained source domain

The same W and normalized psi family from Lemma 12.12 carry the beta
estimates, absolutely and locally uniformly convergent correction series,
eta and theta phases, and real analytic representatives of the literal
theta sum. The series decays in both index directions. No summability,
phase, primitive, or bracket hypotheses are supplied by the caller.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- All four assertions use the same original domain and actual root family. -/
theorem sourceTheorem13_1_original (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W₀ : Set (CoeffPair p), IsOpen W₀ ∧ IsConnected W₀ ∧ realTypeSourceLocus p ⊆ W₀ ∧
      ∃ W : Set (CoeffPair p), IsOpen W ∧ IsSimplyConnected W ∧ realTypeSourceLocus p ⊆ W ∧
        ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
          SourceLemma12_12Data hp hp1 W₀ W s ∧
          SourceAngularThetaCommonDomainData hp hp1 W W W s ∧
          ∀ n : ℤ, ∀ φ ∈ W, canonicalPeriodicGap hp hp1
            (periodOnePotential φ) (periodOnePotential_mem φ) n ≠ 0 →
            (IsRealType (CoeffPair.toMax p φ) → (sourceAngularOriginalTheta hp hp1 n s φ).im = 0) ∧
            ∃ U : Set (CoeffPair p), ∃ f : CoeffPair p → ℂ,
              IsOpen U ∧ φ ∈ U ∧ U ⊆ W ∧ AnalyticOnNhd ℂ f U ∧
              (∀ ψ ∈ U, IsRealType (CoeffPair.toMax p ψ) → (f ψ).im = 0) ∧
              ∀ ψ ∈ U, (∃ k : ℤ, sourceAngularOriginalTheta hp hp1 n s ψ-f ψ = (k:ℂ)*Real.pi) ∧
                sourceAngularThetaDifferential hp hp1 n s ψ = fderiv ℂ f ψ := by
  obtain ⟨W₀,ho,hc,hr,W,hW,hs,hrW,s,H⟩ := sourceLemma12_12 hp hp1
  exact ⟨W₀,ho,hc,hr,W,hW,hs,hrW,s,H,H.original_theta_common_domain,
    fun n φ hφ hg => ⟨fun hreal => H.theta_original_im_eq_zero φ hφ hreal n hg,
      H.theta_original_local_differential_representative φ hφ n hg⟩⟩

end NLS.ZakharovShabat
