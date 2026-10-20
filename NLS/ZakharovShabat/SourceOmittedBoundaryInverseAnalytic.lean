import NLS.ZakharovShabat.SourceOmittedBoundaryDecay
import NLS.SequenceSpaces.WeightedTailCompletion
import NLS.SequenceSpaces.WeightedAnalyticRealization

/-! # The complete analytic inverse-product error

Finite-head completion and weighted analytic realization give an order-one supremum multiplier on original Sobolev sources.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The inverse omitted product's literal signed free error at an
actual canonical boundary root of the original Sobolev source. -/
def sourceBoundaryOmittedInverseError (s : ℕ) (θ : BoundaryCondition) (n : ℤ)
    (ab : SobolevSource s) : ℂ :=
  (sourceStandardRootOmittedProduct (by norm_num) (by norm_num) n
    (higherSobolevSourceInclusion s ab)
    (canonicalPeriodOneBoundaryRoots (by norm_num) (by norm_num) θ
      (higherSobolevSourceInclusion s ab) n))⁻¹-(-1:ℂ)^n.natAbs

/-- The entire signed inverse-product error in the order-one weighted
supremum space, including its finite central coordinates. -/
def sourceBoundaryOmittedInverseRemainder (s : ℕ) (θ : BoundaryCondition)
    (ab : SobolevSource s) : WeightedCoeff (Weight.sobolev 1) ⊤ :=
  WeightedCoeff.ofFunctionOrZero (Weight.sobolev 1) ⊤
    (fun n => sourceBoundaryOmittedInverseError s θ n ab)

/-- The complete inverse omitted-product error is analytic and locally
bounded in the order-one weighted supremum norm near every real Hs
source. This is the multiplier regularity needed for one-smoothing. -/
theorem exists_local_sourceBoundaryOmittedInverseRemainder_analytic
    (s : ℕ) (hs : 1 ≤ s) (a₀ : realTypeHigherSobolevSourceLocus s) (θ : BoundaryCondition) :
    ∃ V : Set (SobolevSource s), IsOpen V ∧ a₀.val ∈ V ∧
      ∃ B : ℝ, 0 ≤ B ∧ AnalyticOnNhd ℂ (sourceBoundaryOmittedInverseRemainder s θ) V ∧
        ∀ ab ∈ V, ‖sourceBoundaryOmittedInverseRemainder s θ ab‖ ≤ B ∧
          ∀ n, (sourceBoundaryOmittedInverseRemainder s θ ab).val n =
            sourceBoundaryOmittedInverseError s θ n ab := by
  classical
  obtain ⟨U₀,hU₀,haU₀,K,_,C,hC,hbound⟩ :=
    exists_local_higherSobolev_omitted_boundary_error_bound s hs a₀ θ
  let J := higherSobolevSourceInclusion s
  obtain ⟨W,hW,haW,hdata⟩ := exists_local_source_omitted_boundary_analytic
    (by norm_num) (by norm_num) (J a₀.val) a₀.property
  let U := U₀ ∩ J ⁻¹' W
  have hU : IsOpen U := hU₀.inter (hW.preimage J.continuous)
  let f (ab : SobolevSource s) (n : ℤ) := sourceBoundaryOmittedInverseError s θ n ab
  have hf (n : ℤ) : AnalyticOnNhd ℂ (fun ab => f ab n) U := by
    intro ab hab
    have hd := (hdata (J ab) hab.2 θ n).2
    exact (((hd.1.comp (J.analyticAt ab)).inv hd.2).sub analyticAt_const)
  have htail (ab : SobolevSource s) (hab : ab ∈ U) :
      ∃ b : WeightedCoeff (Weight.sobolev 1) ⊤,
        (∀ n, b.val n = if K ≤ n.natAbs then f ab n else 0) ∧ ‖b‖ ≤ 2*C := by
    let g (n : ℤ) := if K ≤ n.natAbs then f ab n else 0
    have hg (n : ℤ) : ‖((Weight.sobolev 1) n:ℂ)*g n‖ ≤ 2*C := by
      by_cases hn : K ≤ n.natAbs
      · have he := (hbound ab hab.1 n hn).2
        have hq : 0 < 1+|(n:ℝ)| := by positivity
        have h := (le_div_iff₀ hq).mp he
        simpa only [g,if_pos hn,norm_mul,Complex.norm_real,Real.norm_eq_abs,
          abs_of_pos ((Weight.sobolev 1).positive n),Weight.sobolev_apply,Real.rpow_one,abs_of_pos hq,
          f,sourceBoundaryOmittedInverseError,mul_comm] using h
      · simp only [g,if_neg hn,mul_zero,norm_zero]
        positivity
    let b : WeightedCoeff (Weight.sobolev 1) ⊤ :=
      ⟨g,memℓp_infty ⟨2*C,by rintro _ ⟨n,rfl⟩; exact hg n⟩⟩
    refine ⟨b,fun _ => rfl,?_⟩
    change ‖WeightedCoeff.weightEquiv (Weight.sobolev 1) ⊤ b‖ ≤ 2*C
    apply lp.norm_le_of_forall_le (by positivity)
    exact hg
  obtain ⟨V,hV,haV,hVU,B,hB,hfull⟩ := WeightedCoeff.exists_local_full_bound_of_tail
    (p := ⊤) (Weight.sobolev 1) f hU (fun n => (hf n).continuousOn) K (2*C)
    (by positivity) htail a₀.val ⟨haU₀,haW⟩
  obtain ⟨han,hval⟩ := WeightedCoeff.analytic_realization_of_bound
    (p := ⊤) (Weight.sobolev 1) f hV (fun n ab hab => hf n ab (hVU hab)) B hfull
  exact ⟨V,hV,haV,B,hB,han,hval⟩

end NLS.ZakharovShabat
