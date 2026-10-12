import NLS.ZakharovShabat.SourceContourReduction
import NLS.ZakharovShabat.SourcePeriodicCounting

/-! # Lemma 3.7 in the original source norms

The midpoint and half the squared gap are analytic on one common original-norm
potential neighborhood. They are defined by traces on the actual contour range
and identified with the enclosed eigenvalue pair, including collisions. The
source-domain action and both intrinsic and transported trace formulas are
established in `SourceContourTrace` and `SourceContourReduction`.
-/
noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Counted pairs give the actual source midpoint, squared gap, and centered-square trace. -/
theorem SourcePeriodicCountingData.midpoint_squaredGap_eq_pair
    {hp : p ≠ ⊤} {φ : CoeffPair p} {N : ℕ} (h : SourcePeriodicCountingData hp φ N)
    (n : ℤ) (hn : N < n.natAbs) (a b : ℂ)
    (hs : enclosedPeriodicSpectrum hp (CoeffPair.toMax p φ) ((Real.pi : ℂ)*n) (Real.pi/4) = {a,b}) :
    sourcePeriodicMidpoint hp φ n = (a+b)/2 ∧ sourcePeriodicSquaredGap hp φ n = (a-b)^2 ∧
      LinearMap.trace ℂ (sourceResolventCircleIntegral hp φ ((Real.pi : ℂ)*n) (Real.pi/4)).range
        (((sourceContourRestriction hp φ ((Real.pi : ℂ)*n) (Real.pi/4)).toLinearMap -
          sourcePeriodicMidpoint hp φ n • 1)^2) = (a-b)^2/2 :=
  sourceContourMidpoint_squaredGap_eq_pair hp φ _ _ (by positivity)
    (h.disk_resolvent n hn) (h.disk_rank n hn) a b hs

/-- Lemma 3.7: the two printed functions are analytic on a common source neighborhood,
with the actual rank-two trace formulas and algebraically counted eigenvalue pairs. -/
theorem sourceLemma3_7 (hp : p ≠ ⊤) (φ : CoeffPair p) :
    ∃ N : ℕ, ∃ U : Set (CoeffPair p), 0 < N ∧ IsOpen U ∧ Convex ℝ U ∧ IsConnected U ∧ φ ∈ U ∧ 0 ∈ U ∧
      (∀ n : ℤ, N < n.natAbs →
        AnalyticOnNhd ℂ (fun ψ => sourcePeriodicMidpoint hp ψ n) U ∧
        AnalyticOnNhd ℂ (fun ψ => sourcePeriodicSquaredGap hp ψ n / 2) U) ∧
      ∀ ψ ∈ U, SourcePeriodicCountingData hp ψ N ∧ ∀ n : ℤ, N < n.natAbs → ∃ a b : ℂ,
        enclosedPeriodicSpectrum hp (CoeffPair.toMax p ψ) ((Real.pi : ℂ)*n) (Real.pi/4) = {a,b} ∧
        sourcePeriodicMidpoint hp ψ n = (a+b)/2 ∧ sourcePeriodicSquaredGap hp ψ n = (a-b)^2 ∧
        LinearMap.trace ℂ (sourceResolventCircleIntegral hp ψ ((Real.pi : ℂ)*n) (Real.pi/4)).range
          (((sourceContourRestriction hp ψ ((Real.pi : ℂ)*n) (Real.pi/4)).toLinearMap -
            sourcePeriodicMidpoint hp ψ n • 1)^2) = (a-b)^2/2 ∧
        (if a = b then periodicAlgebraicMultiplicity hp (CoeffPair.toMax p ψ) a = 2 else
          periodicAlgebraicMultiplicity hp (CoeffPair.toMax p ψ) a = 1 ∧
          periodicAlgebraicMultiplicity hp (CoeffPair.toMax p ψ) b = 1) := by
  obtain ⟨N,U,hN,ho,hc,hconn,hφ,h0,h⟩ := exists_uniform_sourcePeriodicCountingData hp φ
  refine ⟨N,U,hN,ho,hc,hconn,hφ,h0,?_,?_⟩
  · intro n hn
    constructor <;> intro ψ hψ
    · exact (analyticAt_sourceContourMidpoint_and_halfSquaredGap hp ψ _ _ (by positivity)
        (((h N le_rfl).2.2 ψ hψ).disk_resolvent n hn)).1
    · exact (analyticAt_sourceContourMidpoint_and_halfSquaredGap hp ψ _ _ (by positivity)
        (((h N le_rfl).2.2 ψ hψ).disk_resolvent n hn)).2
  · intro ψ hψ
    have hd := (h N le_rfl).2.2 ψ hψ
    refine ⟨hd,?_⟩
    intro n hn
    obtain ⟨a,b,hs,hm⟩ := hd.coefficient_counts.disk_eigenvalue_pair n hn
    have ht := hd.midpoint_squaredGap_eq_pair n hn a b hs
    exact ⟨a,b,hs,ht.1,ht.2.1,ht.2.2,hm⟩

/-- The printed period-one setting follows with its original potential topology. -/
theorem sourceLemma3_7_periodOne (hp : p ≠ ⊤) (φ : CoeffPair p) :
    ∃ N : ℕ, ∃ U : Set (CoeffPair p), 0 < N ∧ IsOpen U ∧ Convex ℝ U ∧ IsConnected U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ n : ℤ, N < n.natAbs →
        AnalyticOnNhd ℂ (fun ψ => sourcePeriodicMidpoint hp (periodOnePair ψ) n) U ∧
        AnalyticOnNhd ℂ (fun ψ => sourcePeriodicSquaredGap hp (periodOnePair ψ) n / 2) U := by
  obtain ⟨N,V,hN,hVo,hVc,_,hφ,h0,han,_⟩ := sourceLemma3_7 hp (periodOnePair φ)
  let U : Set (CoeffPair p) := periodOnePair ⁻¹' V
  have ho : IsOpen U := hVo.preimage (periodOnePair (p := p)).continuous
  have hc : Convex ℝ U := hVc.linear_preimage
    ((periodOnePair (p := p)).toContinuousLinearMap.restrictScalars ℝ).toLinearMap
  have h0U : (0 : CoeffPair p) ∈ U := by simpa only [U,Set.mem_preimage,map_zero] using h0
  refine ⟨N,U,hN,ho,hc,⟨⟨0,h0U⟩,hc.isPreconnected⟩,hφ,h0U,?_⟩
  intro n hn
  constructor <;> intro ψ hψ
  · exact ((han n hn).1 _ hψ).comp ((periodOnePair (p := p)).toContinuousLinearMap.analyticAt ψ)
  · exact ((han n hn).2 _ hψ).comp ((periodOnePair (p := p)).toContinuousLinearMap.analyticAt ψ)

end NLS.ZakharovShabat
