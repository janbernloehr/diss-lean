import NLS.ZakharovShabat.SourceAngularOriginalCanonicalDifferentials

/-!
# Corollary 13.2 for the retained domain and literal coordinate family

All finite p greater than one are covered by regular Fourier coefficient
witnesses. The mixed relation requires only the angle gap to be open;
action gaps may collapse.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceLemma12_12Data
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

theorem original_corollary13_2 (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (n m : ℤ) (φ : realTypeSourceLocus p) :
    (H.originalActionCotangent n φ).bivector (H.originalActionCotangent m φ) = 0 ∧
    (∀ hn : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0,
      ∀ hm : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) m ≠ 0,
      (H.original_theta_common_domain.thetaRegularCotangent n φ hn).bivector
        (H.original_theta_common_domain.thetaRegularCotangent m φ hm) = 0) ∧
    (∀ hn : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0,
      (H.original_theta_common_domain.thetaRegularCotangent n φ hn).bivector
        (H.originalActionCotangent m φ) = if n = m then 1 else 0) := by
  have hc := H.original_theta_common_domain.corollary13_2_regular n m φ
  simpa only [NLS.Poisson.RegularSourceCotangent.bivector, originalActionCotangent] using hc

end SourceLemma12_12Data

/-- The original-domain canonical relations for every finite source exponent above one. -/
theorem sourceCorollary13_2_original (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W₀ : Set (CoeffPair p), IsOpen W₀ ∧ IsConnected W₀ ∧ realTypeSourceLocus p ⊆ W₀ ∧
      ∃ W : Set (CoeffPair p), IsOpen W ∧ IsSimplyConnected W ∧ realTypeSourceLocus p ⊆ W ∧
        ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
          ∃ H : SourceLemma12_12Data hp hp1 W₀ W s, ∀ n m : ℤ, ∀ φ : realTypeSourceLocus p,
            (H.originalActionCotangent n φ).bivector (H.originalActionCotangent m φ) = 0 ∧
            (∀ hn : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0,
              ∀ hm : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) m ≠ 0,
              (H.original_theta_common_domain.thetaRegularCotangent n φ hn).bivector
                (H.original_theta_common_domain.thetaRegularCotangent m φ hm) = 0) ∧
            (∀ hn : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0,
              (H.original_theta_common_domain.thetaRegularCotangent n φ hn).bivector
                (H.originalActionCotangent m φ) = if n = m then 1 else 0) := by
  obtain ⟨W₀,ho,hc,hr,W,hW,hs,hrW,s,H⟩ := sourceLemma12_12 hp hp1
  exact ⟨W₀,ho,hc,hr,W,hW,hs,hrW,s,H,H.original_corollary13_2⟩

end NLS.ZakharovShabat
