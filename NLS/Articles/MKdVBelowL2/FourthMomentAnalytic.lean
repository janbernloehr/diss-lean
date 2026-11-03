import NLS.Articles.MKdVBelowL2.FourthMomentSummability
import NLS.ZakharovShabat.SourceAbelianMomentWeightedRows
import NLS.ZakharovShabat.SourceAngularOriginalDomain

/-! # Analyticity of the actual weighted H₄ candidate

Continuous summation of the analytic ℓ¹-valued weighted moment row gives
analyticity of the infinite candidate at every finite p > 1. This is the
literal -12 weighted sum, prior to identifying the physical H₄ derivative.
-/
noncomputable section
set_option autoImplicit false
open Set
open scoped ENNReal
namespace NLS.Articles.MKdVBelowL2
open NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
  {W W₀ V : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- Continuous ℓ¹ summation proves analyticity of the actual candidate,
with no assumption of uniform tails of the coefficient rows. -/
theorem exists_analytic_fourthFrequencyCandidate
    (A : SourceAbelianMomentAtlas hp hp1 W s)
    (H : SourceLemma12_11Data hp hp1 W₀ V s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 V s)
    (hV : IsOpen V) (hrealV : realTypeSourceLocus p ⊆ V) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ IsConnected U ∧ realTypeSourceLocus p ⊆ U ∧
      U ⊆ A.domain ∩ V ∧
      (∀ ψ ∈ U, ∀ n : ℤ, Summable (fun k : ℤ => ‖(k:ℂ)*A.moment n k 2 ψ‖)) ∧
      ∀ n : ℤ, AnalyticOnNhd ℂ (fourthFrequencyCandidate A n) U := by
  obtain ⟨U,hU,hUc,hreal,hUV,hcoord,han,_⟩ :=
    A.exists_analytic_weightedSecondMomentRows H hs hV hrealV
  refine ⟨U,hU,hUc,hreal,hUV,?_,?_⟩
  · intro ψ hψ n
    simpa only [hcoord ψ hψ n] using
      (lp.memℓp (A.weightedSecondMomentRow n ψ)).norm.summable_of_one
  · intro n ψ hψ
    have ha : AnalyticAt ℂ (fun χ => (-12:ℂ)*
        (lp.tsumCLM (α := ℤ) (𝕜 := ℂ) (E := ℂ)) (A.weightedSecondMomentRow n χ)) ψ :=
      analyticAt_const.mul (((lp.tsumCLM (α := ℤ) (𝕜 := ℂ) (E := ℂ)).analyticAt _).comp (han n ψ hψ))
    apply ha.congr
    filter_upwards [hU.mem_nhds hψ] with χ hχ
    change (-12:ℂ)*(∑' k, A.weightedSecondMomentRow n χ k) = fourthFrequencyCandidate A n χ
    unfold fourthFrequencyCandidate
    congr 1
    exact tsum_congr (fun k => hcoord χ hχ n k)

/-- Construct one actual analytic H₄ candidate chart at every finite exponent.
Its normalization, roots, and source domains are all supplied by verified data. -/
theorem exists_fourthMoment_analyticAtlas (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W V : Set (CoeffPair p), IsOpen V ∧ realTypeSourceLocus p ⊆ V ∧
      ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
        SourcePsiSquaredGapComplexExtension hp hp1 V s ∧
        ∃ A : SourceAbelianMomentAtlas hp hp1 W s,
        ∃ U : Set (CoeffPair p), IsOpen U ∧ IsConnected U ∧ realTypeSourceLocus p ⊆ U ∧
          U ⊆ A.domain ∩ V ∧
          (∀ ψ ∈ U, ∀ n : ℤ, Summable (fun k : ℤ => ‖(k:ℂ)*A.moment n k 2 ψ‖)) ∧
          ∀ n : ℤ, AnalyticOnNhd ℂ (fourthFrequencyCandidate A n) U := by
  classical
  obtain ⟨W₀,_,_,_,V,hV,_,hrealV,s,H⟩ := sourceLemma12_12 hp hp1
  have hs := H.angular_extension
  obtain ⟨W,_,_,hlocal⟩ := hs.toSourcePsiNormalizedComplexExtension.exists_moment_localCharts hV hrealV
  choose L hL using hlocal
  let A : SourceAbelianMomentAtlas hp hp1 W s := ⟨L⟩
  obtain ⟨U,hU,hUc,hreal,hUV,hconv,han⟩ := exists_analytic_fourthFrequencyCandidate A H.previous hs hV hrealV
  exact ⟨W,V,hV,hrealV,s,hs,A,U,hU,hUc,hreal,hUV,hconv,han⟩

end NLS.Articles.MKdVBelowL2
