import NLS.KdV.HillCompletePhaseActionSeries

/-! The full actual local Abelian phase cotangent series can be
 evaluated in any native Gardner Hamiltonian direction. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.LpSequence
open scoped ENNReal
namespace NLS.KdV

theorem tendsto_hillHminusOffIndex_functional_velocity_sums (n : ℕ+) (G : PeriodOneHminusOne → ℂ)
    (q : PeriodOneHminusOne) (hq : q ∈ hillHminusOffIndexAnalyticDomain)
    (V : ℕ+ → PeriodOneHminusOne → ℂ)
    (hbeta : ∀ m : ℕ+, m ≠ n → NLS.Poisson.hminusGardnerBracket
      (hillHminusPhysicalOffIndexAbelianValue n m) G q =
      hillHminusCanonicalPsi n (hillHminusCanonicalDirichlet m q,q)*V m q) :
    Tendsto (fun N : ℕ => ∑ j ∈ Finset.Icc (-(N:ℤ)) N,
      positiveScalarExtension (hillHminusOffIndexVelocityTerm n V q) j) atTop
        (𝓝 (NLS.Poisson.hminusGardnerBracket (hillHminusOffIndexAbelianCorrection n)
          G q)) := by
  have he (j : ℤ) : NLS.Poisson.hminusGardnerBracket
      (fun p => positiveScalarExtension (hillHminusOffIndexAbelianTerm n p) j)
      G q = positiveScalarExtension (hillHminusOffIndexVelocityTerm n V q) j := by
    by_cases hj : j ∈ range positiveEmbedding
    · obtain ⟨m,rfl⟩ := hj
      change NLS.Poisson.hminusGardnerBracket
        (fun p => positiveScalarExtension (hillHminusOffIndexAbelianTerm n p) ((m:ℕ):ℤ))
        G q = positiveScalarExtension (hillHminusOffIndexVelocityTerm n V q) ((m:ℕ):ℤ)
      simp only [positiveScalarExtension_apply,hillHminusOffIndexVelocityTerm]
      by_cases hmn : m = n
      · simp only [hillHminusOffIndexAbelianTerm,if_pos hmn]
        rw [← NLS.Poisson.fderiv_apply_gardnerHamiltonianVector]
        simp
      · simp only [hillHminusOffIndexAbelianTerm,if_neg hmn]
        exact hbeta m hmn
    · have hz : (fun p : PeriodOneHminusOne => positiveScalarExtension (hillHminusOffIndexAbelianTerm n p) j) =
          (fun _ => (0:ℂ)) := funext (fun _ => positiveScalarExtension_zero_of_not_mem_range _ j hj)
      rw [hz,positiveScalarExtension_zero_of_not_mem_range _ j hj,
        ← NLS.Poisson.fderiv_apply_gardnerHamiltonianVector]
      simp
  have ht := tendsto_hillHminusOffIndexAbelian_Gardner_sums n G q hq
  simpa only [he] using ht

namespace HillPhysicalOnIndexPhaseChart
variable {P : HillProductEquationPatch} {n : ℕ+}

theorem tendsto_completePhase_functional_series (C : HillPhysicalOnIndexPhaseChart P n)
    (G : PeriodOneHminusOne → ℂ) (q : PeriodOneHminusOne) (hq : q ∈ C.source)
    (hc : q ∈ hillHminusOffIndexAnalyticDomain) (V : ℕ+ → PeriodOneHminusOne → ℂ)
    (hphase : NLS.Poisson.hminusGardnerBracket C.phase G q =
      hillHminusCanonicalPsi n (hillHminusCanonicalDirichlet n q,q)*V n q)
    (hbeta : ∀ m : ℕ+, m ≠ n → NLS.Poisson.hminusGardnerBracket
      (hillHminusPhysicalOffIndexAbelianValue n m) G q =
      hillHminusCanonicalPsi n (hillHminusCanonicalDirichlet m q,q)*V m q) :
    Tendsto (fun N : ℕ => hillHminusCanonicalPsi n (hillHminusCanonicalDirichlet n q,q)*V n q+
      ∑ j ∈ Finset.Icc (-(N:ℤ)) N, positiveScalarExtension (hillHminusOffIndexVelocityTerm n V q) j) atTop
        (𝓝 (NLS.Poisson.hminusGardnerBracket C.completePhase G q)) := by
  have ht := (tendsto_const_nhds (x := hillHminusCanonicalPsi n (hillHminusCanonicalDirichlet n q,q)*V n q)).add
    (tendsto_hillHminusOffIndex_functional_velocity_sums n G q hc V hbeta)
  rw [← hphase,← C.completePhase_Gardner_eq_add G q hq hc] at ht
  simpa only [hphase] using ht

end HillPhysicalOnIndexPhaseChart
end NLS.KdV
