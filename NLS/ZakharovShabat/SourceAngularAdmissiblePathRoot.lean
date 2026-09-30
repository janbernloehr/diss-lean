import NLS.ComplexAnalysis.ContinuousSquareRootPath
import NLS.ComplexAnalysis.CurveIntegralInteriorCongruence
import NLS.ZakharovShabat.SourceAngularEtaSheetChoicePathPeriod

/-!
# Continuous roots on admissible angular paths

An admissible path avoids the selected gap on its interior and stays in
its isolating disc. Its square root is required to be continuous along
the path, but no single prescribed root chart need contain that path.
The continued root has one fixed sign relative to the canonical root on
the path interior. The literal angular integral transports by that sign.
-/

noncomputable section
open Set Filter Topology Metric Complex NLS.ComplexAnalysis
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Root continuation data along the paper's admissible spectral path.
`Path.extend` is constant outside the unit interval, so continuity also
includes the root values at both endpoints. -/
structure SourceAngularAdmissiblePathRootData
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (ψ : CoeffPair p)
    (c : ℂ) (R : ℝ) (Q : ℂ × CoeffPair p → ℂ)
    {a b : ℂ} (γ : Path a b) : Prop where
  continuous_root : Continuous (fun t : ℝ => Q (γ.extend t,ψ))
  square_root : ∀ t ∈ Icc (0:ℝ) 1, Q (γ.extend t,ψ)^2 = sourceAngularRadicand hp (γ.extend t,ψ)
  interior : ∀ t ∈ Ioo (0:ℝ) 1, γ.extend t ∈ ball c R \ sourcePeriodicSegment hp hp1 ψ n

/-- Ordinary continuity on the closed path suffices for the root data:
clamping the parameter automatically makes the extension continuous. -/
theorem sourceAngularAdmissiblePathRootData_of_continuousOn
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (ψ : CoeffPair p)
    (c : ℂ) (R : ℝ) (Q : ℂ × CoeffPair p → ℂ) {a b : ℂ} (γ : Path a b)
    (hroot : ContinuousOn (fun t : ℝ => Q (γ.extend t,ψ)) (Icc (0:ℝ) 1))
    (hsq : ∀ t ∈ Icc (0:ℝ) 1, Q (γ.extend t,ψ)^2 = sourceAngularRadicand hp (γ.extend t,ψ))
    (hD : ∀ t ∈ Ioo (0:ℝ) 1, γ.extend t ∈ ball c R \ sourcePeriodicSegment hp hp1 ψ n) :
    SourceAngularAdmissiblePathRootData hp hp1 n ψ c R Q γ := by
  refine ⟨?_,hsq,hD⟩
  have hc : Continuous (fun t : I => Q (γ t,ψ)) := by
    convert hroot.comp_continuous continuous_subtype_val (fun t : I => t.property) using 1
    funext t
    dsimp only [Function.comp_def]
    rw [Path.extend_apply γ t.property]
  change Continuous (IccExtend zero_le_one (fun t : I => Q (γ t,ψ)))
  exact hc.Icc_extend'

namespace SourceAngularAdmissiblePathRootData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {n : ℤ} {ψ : CoeffPair p}
  {c : ℂ} {R : ℝ} {Q : ℂ × CoeffPair p → ℂ} {a b : ℂ} {γ : Path a b}

theorem interior_mem_canonicalRootDomain
    (hQ : SourceAngularAdmissiblePathRootData hp hp1 n ψ c R Q γ)
    (hother : closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n)
    (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :
    γ.extend t ∈ sourceCanonicalRootDomain hp hp1 ψ := by
  intro m
  by_cases hm : m = n
  · subst m; exact (hQ.interior t ht).2
  · exact hother (ball_subset_closedBall (hQ.interior t ht).1) m hm

/-- Continuing a square root across any number of local charts does
not change its relative sign on the admissible path interior. -/
theorem exists_fixed_sign
    (hQ : SourceAngularAdmissiblePathRootData hp hp1 n ψ c R Q γ)
    (hother : closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n) :
    ∃ κ : ℂ, (κ = 1 ∨ κ = -1) ∧ ∀ t ∈ Ioo (0:ℝ) 1,
      Q (γ.extend t,ψ) = κ*sourceCanonicalRoot hp hp1 ψ (γ.extend t) := by
  have hcan : ContinuousOn (fun t : ℝ => sourceCanonicalRoot hp hp1 ψ (γ.extend t))
      (Ioo (0:ℝ) 1) := by
    intro t ht
    exact (((sourceCanonicalRoot_analyticOnNhd hp hp1 ψ _
      (hQ.interior_mem_canonicalRootDomain hother t ht)).continuousAt).comp
      (γ.continuous_extend.continuousAt (x := t))).continuousWithinAt
  exact exists_fixed_sign_of_sq_eq_on_preconnected _ _ _ (convex_Ioo (0:ℝ) 1).isPreconnected
    hQ.continuous_root.continuousOn hcan
    (fun t ht => (hQ.square_root t (Ioo_subset_Icc_self ht)).trans
      (sourceCanonicalRoot_sq_eq_discriminant_sq_sub_four hp hp1 ψ _
        (hQ.interior_mem_canonicalRootDomain hother t ht)).symm)
    (fun t ht => sourceCanonicalRoot_ne_zero_off_gaps hp hp1 ψ _
      (hQ.interior_mem_canonicalRootDomain hother t ht))

/-- Every literal angular integral along a continued admissible root
equals one of the two signs of the canonical-sheet integral. Endpoint
values of the integrands do not affect this identity. -/
theorem pathIntegral_eq_signed_canonical
    (hQ : SourceAngularAdmissiblePathRootData hp hp1 n ψ c R Q γ)
    (hother : closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n)
    (m : ℤ) (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) :
    ∃ κ : ℂ, (κ = 1 ∨ κ = -1) ∧
      (∀ t ∈ Ioo (0:ℝ) 1, Q (γ.extend t,ψ) = κ*sourceCanonicalRoot hp hp1 ψ (γ.extend t)) ∧
      sourceAngularPathIntegral m s Q ψ γ = κ*
        sourceAngularPathIntegral m s (fun u => sourceCanonicalRoot hp hp1 u.2 u.1) ψ γ := by
  obtain ⟨κ,hκ,hroot⟩ := hQ.exists_fixed_sign hother
  refine ⟨κ,hκ,hroot,?_⟩
  let f : ℂ → ℂ := fun z => sourceAngularIntegrand m s Q (z,ψ)
  let g : ℂ → ℂ := fun z => sourceAngularIntegrand m s
    (fun u => sourceCanonicalRoot hp hp1 u.2 u.1) (z,ψ)
  have heq : ∀ t ∈ Ioo (0:ℝ) 1, f (γ.extend t) = κ*g (γ.extend t) := by
    intro t ht
    dsimp only [f,g,sourceAngularIntegrand]
    rw [hroot t ht]
    rcases hκ with rfl | rfl <;> simp only [one_mul,neg_one_mul,div_neg]
  have hω : holomorphicOneForm (fun z => κ*g z) = κ • holomorphicOneForm g := by
    funext z
    exact mul_smul κ (g z) (ContinuousLinearMap.id ℂ ℂ)
  change (∫ᶜ z in γ, holomorphicOneForm f z) = κ*(∫ᶜ z in γ, holomorphicOneForm g z)
  rw [curveIntegral_holomorphicOneForm_congr_interior f (fun z => κ*g z) γ heq,
    hω,curveIntegral_smul,smul_eq_mul]

end SourceAngularAdmissiblePathRootData
end NLS.ZakharovShabat
