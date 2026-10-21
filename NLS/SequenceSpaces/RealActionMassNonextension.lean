import NLS.SequenceSpaces.ActionMassNonextension
import NLS.SequenceSpaces.RealCoeffExponent

/-! # Total action has no continuous larger-exponent extension

Finite nonnegative blocks keep mass one while converging to zero in every
ell^q with q>1, including infinity. This is the introductory mass obstruction.
-/

noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.RealCoeff

/-- Real total action has no extension continuous at zero on the positive
ell^q cone for any q>1, including infinity. Only local agreement is needed. -/
theorem not_continuousWithinAt_mass_extension {q : ℝ≥0∞} [Fact (1 ≤ q)] (h1q : 1 < q)
    (G : RealCoeff q → ℝ) (U : Set (RealCoeff q)) (hU : U ∈ 𝓝 (0:RealCoeff q))
    (hagree : ∀ a : RealCoeff 1, (∀ n, 0 ≤ a n) →
      exponentInclusion h1q.le a ∈ U →
      G (exponentInclusion h1q.le a) = ∑' n : ℤ, a n) :
    ¬ ContinuousWithinAt G {a : RealCoeff q | ∀ n, 0 ≤ a n} 0 := by
  intro hG
  let b (p : ℝ≥0∞) [Fact (1 ≤ p)] (N : ℕ) := Coeff.reCLM p (Coeff.positiveMassBlock p N)
  have hp (p : ℝ≥0∞) [Fact (1 ≤ p)] (N : ℕ) (n : ℤ) : 0 ≤ b p N n :=
    (Coeff.positiveMassBlock_mem_nonnegativeLocus p N n).2
  have he (N : ℕ) : exponentInclusion h1q.le (b 1 N) = b q N := by
    ext n
    have h := congrArg (fun a : Coeff q => (a n).re)
      (Coeff.positiveMassBlock_exponent h1q.le N)
    simpa only [exponentInclusion_apply, b, Coeff.reCLM_apply, Coeff.exponentInclusion_apply] using h
  have hm (N : ℕ) : (∑' n : ℤ, b 1 N n) = 1 := by
    have hs := (Coeff.positiveMassBlock 1 N).property.norm.summable_of_one.of_norm
    change (∑' n : ℤ, (Coeff.positiveMassBlock 1 N n).re) = 1
    rw [← Complex.re_tsum hs, Coeff.tsum_positiveMassBlock]
    rfl
  have ht : Tendsto (b q) atTop (𝓝 0) := by
    simpa only [b, map_zero, Function.comp_def] using
      (Coeff.reCLM q).continuous.continuousAt.tendsto.comp (Coeff.tendsto_positiveMassBlock h1q)
  have hw : Tendsto (b q) atTop (𝓝[{a : RealCoeff q | ∀ n, 0 ≤ a n}] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨ht, Filter.Eventually.of_forall (hp q)⟩
  have hzero : G 0 = 0 := by
    have h := hagree 0 (fun _ => le_rfl) (by simpa using mem_of_mem_nhds hU)
    simpa using h
  have hlim : Tendsto (fun N => G (b q N)) atTop (𝓝 0) := by
    simpa only [hzero, Function.comp_def] using hG.tendsto.comp hw
  have hone : (fun N => G (b q N)) =ᶠ[atTop] fun _ => (1 : ℝ) := by
    filter_upwards [ht.eventually hU] with N hNU
    have h := hagree (b 1 N) (hp 1 N) (by rw [he]; exact hNU)
    simpa only [he, hm] using h
  have hlim1 : Tendsto (fun N => G (b q N)) atTop (𝓝 1) :=
    tendsto_const_nhds.congr' hone.symm
  exact zero_ne_one (tendsto_nhds_unique hlim hlim1)

end NLS.RealCoeff
