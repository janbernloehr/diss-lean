import NLS.KdV.HillOnIndexActionVelocity

/-! The actual complete local Abelian phase/action bracket is the
limit of its diagonal term and the literal finite off-index spectral
velocity sums. This uses the proved full correction cotangent limit;
evaluation of the normalized sum as a Kronecker value is not assumed. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.LpSequence
open scoped ENNReal
namespace NLS.KdV

def hillHminusOffIndexVelocityTerm (n : ℕ+) (V : ℕ+ → PeriodOneHminusOne → ℂ)
    (q : PeriodOneHminusOne) (m : ℕ+) : ℂ :=
  if m = n then 0 else hillHminusCanonicalPsi n (hillHminusCanonicalDirichlet m q,q)*V m q

theorem tendsto_hillHminusOffIndex_velocity_sums (n k : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ hillHminusOffIndexAnalyticDomain)
    (V : ℕ+ → PeriodOneHminusOne → ℂ)
    (hbeta : ∀ m : ℕ+, m ≠ n → NLS.Poisson.hminusGardnerBracket
      (hillHminusPhysicalOffIndexAbelianValue n m) (hillHminusCanonicalAction k) q =
      hillHminusCanonicalPsi n (hillHminusCanonicalDirichlet m q,q)*V m q) :
    Tendsto (fun N : ℕ => ∑ j ∈ Finset.Icc (-(N:ℤ)) N,
      positiveScalarExtension (hillHminusOffIndexVelocityTerm n V q) j) atTop
        (𝓝 (NLS.Poisson.hminusGardnerBracket (hillHminusOffIndexAbelianCorrection n)
          (hillHminusCanonicalAction k) q)) := by
  have he (j : ℤ) : NLS.Poisson.hminusGardnerBracket
      (fun p => positiveScalarExtension (hillHminusOffIndexAbelianTerm n p) j)
      (hillHminusCanonicalAction k) q = positiveScalarExtension (hillHminusOffIndexVelocityTerm n V q) j := by
    by_cases hj : j ∈ range positiveEmbedding
    · obtain ⟨m,rfl⟩ := hj
      change NLS.Poisson.hminusGardnerBracket
        (fun p => positiveScalarExtension (hillHminusOffIndexAbelianTerm n p) ((m:ℕ):ℤ))
        (hillHminusCanonicalAction k) q = positiveScalarExtension (hillHminusOffIndexVelocityTerm n V q) ((m:ℕ):ℤ)
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
  have ht := tendsto_hillHminusOffIndexAbelian_Gardner_sums n (hillHminusCanonicalAction k) q hq
  simpa only [he] using ht

namespace HillPhysicalOnIndexPhaseChart
variable {P : HillProductEquationPatch} {n : ℕ+}

theorem completePhase_Gardner_eq_add (C : HillPhysicalOnIndexPhaseChart P n)
    (G : PeriodOneHminusOne → ℂ) (q : PeriodOneHminusOne)
    (hq : q ∈ C.source) (hc : q ∈ hillHminusOffIndexAnalyticDomain) :
    NLS.Poisson.hminusGardnerBracket C.completePhase G q =
      NLS.Poisson.hminusGardnerBracket C.phase G q+
        NLS.Poisson.hminusGardnerBracket (hillHminusOffIndexAbelianCorrection n) G q := by
  have hd := (C.phase_analytic q hq).differentiableAt.hasFDerivAt.fun_add
    (analyticOnNhd_hillHminusOffIndexAbelianCorrection n q hc).differentiableAt.hasFDerivAt
  change HasFDerivAt C.completePhase _ q at hd
  change NLS.Poisson.gardnerCotangentBivector (fderiv ℂ C.completePhase q) (fderiv ℂ G q) = _
  rw [hd.fderiv,map_add,add_apply]
  rfl

theorem tendsto_completePhase_action_series (C : HillPhysicalOnIndexPhaseChart P n)
    (k : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ C.source)
    (hc : q ∈ hillHminusOffIndexAnalyticDomain) (V : ℕ+ → PeriodOneHminusOne → ℂ)
    (hphase : NLS.Poisson.hminusGardnerBracket C.phase (hillHminusCanonicalAction k) q =
      hillHminusCanonicalPsi n (hillHminusCanonicalDirichlet n q,q)*V n q)
    (hbeta : ∀ m : ℕ+, m ≠ n → NLS.Poisson.hminusGardnerBracket
      (hillHminusPhysicalOffIndexAbelianValue n m) (hillHminusCanonicalAction k) q =
      hillHminusCanonicalPsi n (hillHminusCanonicalDirichlet m q,q)*V m q) :
    Tendsto (fun N : ℕ => hillHminusCanonicalPsi n (hillHminusCanonicalDirichlet n q,q)*V n q+
      ∑ j ∈ Finset.Icc (-(N:ℤ)) N, positiveScalarExtension (hillHminusOffIndexVelocityTerm n V q) j) atTop
        (𝓝 (NLS.Poisson.hminusGardnerBracket C.completePhase (hillHminusCanonicalAction k) q)) := by
  have ht := (tendsto_const_nhds (x := hillHminusCanonicalPsi n (hillHminusCanonicalDirichlet n q,q)*V n q)).add
    (tendsto_hillHminusOffIndex_velocity_sums n k q hc V hbeta)
  rw [← hphase,← C.completePhase_Gardner_eq_add (hillHminusCanonicalAction k) q hq hc] at ht
  simpa only [hphase] using ht

end HillPhysicalOnIndexPhaseChart
end NLS.KdV
