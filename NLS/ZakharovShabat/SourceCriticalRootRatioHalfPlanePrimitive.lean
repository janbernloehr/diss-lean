import NLS.ComplexAnalysis.ConvexHolomorphicPrimitive
import NLS.ZakharovShabat.SourceCriticalRootRatioHalfPlanePaths
import NLS.ZakharovShabat.SourceCriticalRootRatioStadiumIntegral

/-!
# Holomorphic primitives above and below real-type gaps

The critical-root quotient has a primitive on each open half-plane.
This gives endpoint evaluation for every `C¹` regular path there,
including pieces of a path with corners.
-/

noncomputable section
open Set Complex
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The critical-root quotient has a holomorphic primitive throughout
the upper half-plane for a real-type source. -/
theorem exists_sourceCriticalRootRatio_upperHalfPlane_primitive
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ)) :
    ∃ F : ℂ → ℂ, ∀ z : ℂ, 0 < z.im →
      HasDerivAt F
        (deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
          sourceCanonicalRoot hp hp1 ψ z) z := by
  let U : Set ℂ := {z | 0 < z.im}
  have hconv : Convex ℝ U := by
    have hlin : IsLinearMap ℝ (fun z : ℂ => z.im) := by
      constructor
      · intro x y; simp
      · intro c x; simp
    exact convex_halfSpace_gt hlin 0
  have hopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
  have hf : DifferentiableOn ℂ
      (fun z => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
        sourceCanonicalRoot hp hp1 ψ z) U := by
    intro z hz
    exact (sourceCriticalRootRatio_analyticOnNhd hp hp1 ψ z
      (sourceCanonicalRootDomain_of_im_ne_zero hp hp1 ψ hreal z
        (ne_of_gt hz))).differentiableAt.differentiableWithinAt
  exact NLS.ComplexAnalysis.exists_primitive_on_convex _ U hconv hopen hf

/-- The analogous primitive on the lower half-plane. -/
theorem exists_sourceCriticalRootRatio_lowerHalfPlane_primitive
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ)) :
    ∃ F : ℂ → ℂ, ∀ z : ℂ, z.im < 0 →
      HasDerivAt F
        (deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
          sourceCanonicalRoot hp hp1 ψ z) z := by
  let U : Set ℂ := {z | z.im < 0}
  have hconv : Convex ℝ U := by
    have hlin : IsLinearMap ℝ (fun z : ℂ => z.im) := by
      constructor
      · intro x y; simp
      · intro c x; simp
    exact convex_halfSpace_lt hlin 0
  have hopen : IsOpen U := isOpen_lt Complex.continuous_im continuous_const
  have hf : DifferentiableOn ℂ
      (fun z => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
        sourceCanonicalRoot hp hp1 ψ z) U := by
    intro z hz
    exact (sourceCriticalRootRatio_analyticOnNhd hp hp1 ψ z
      (sourceCanonicalRootDomain_of_im_ne_zero hp hp1 ψ hreal z
        (ne_of_lt hz))).differentiableAt.differentiableWithinAt
  exact NLS.ComplexAnalysis.exists_primitive_on_convex _ U hconv hopen hf

/-- One upper-half-plane primitive evaluates the quotient integral
along every `C¹` path in that half-plane. -/
theorem exists_sourceCriticalRootRatio_upperHalfPlane_pathIntegral_eq_sub
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ)) :
    ∃ F : ℂ → ℂ, ∀ {a b : ℂ} (γ : Path a b),
      ContDiffOn ℝ 1 γ.extend (Icc 0 1) →
      (∀ u : I, 0 < (γ u).im) →
      (∫ᶜ z in γ, NLS.ComplexAnalysis.holomorphicOneForm
        (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
          sourceCanonicalRoot hp hp1 ψ w) z) = F b - F a := by
  obtain ⟨F,hF⟩ := exists_sourceCriticalRootRatio_upperHalfPlane_primitive
    hp hp1 ψ hreal
  refine ⟨F,?_⟩
  intro a b γ hγ hupper
  have hdom : range γ ⊆ sourceCanonicalRootDomain hp hp1 ψ := by
    rintro z ⟨u,rfl⟩
    exact sourceCanonicalRootDomain_of_im_ne_zero hp hp1 ψ hreal _
      (ne_of_gt (hupper u))
  have hint := sourceCriticalRootRatio_curveIntegrable_of_smoothPath
    hp hp1 ψ γ hγ hdom
  have hγU (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      γ.extend t ∈ ({z : ℂ | 0 < z.im} : Set ℂ) := by
    rw [Path.extend_apply γ ht]
    exact hupper ⟨t,ht⟩
  exact NLS.ComplexAnalysis.curveIntegral_eq_sub_of_primitive
    _ F _ (fun z hz => hF z hz) γ hγ hγU hint

/-- The same `C¹` endpoint evaluation below the real axis. -/
theorem exists_sourceCriticalRootRatio_lowerHalfPlane_pathIntegral_eq_sub
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ)) :
    ∃ F : ℂ → ℂ, ∀ {a b : ℂ} (γ : Path a b),
      ContDiffOn ℝ 1 γ.extend (Icc 0 1) →
      (∀ u : I, (γ u).im < 0) →
      (∫ᶜ z in γ, NLS.ComplexAnalysis.holomorphicOneForm
        (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
          sourceCanonicalRoot hp hp1 ψ w) z) = F b - F a := by
  obtain ⟨F,hF⟩ := exists_sourceCriticalRootRatio_lowerHalfPlane_primitive
    hp hp1 ψ hreal
  refine ⟨F,?_⟩
  intro a b γ hγ hlower
  have hdom : range γ ⊆ sourceCanonicalRootDomain hp hp1 ψ := by
    rintro z ⟨u,rfl⟩
    exact sourceCanonicalRootDomain_of_im_ne_zero hp hp1 ψ hreal _
      (ne_of_lt (hlower u))
  have hint := sourceCriticalRootRatio_curveIntegrable_of_smoothPath
    hp hp1 ψ γ hγ hdom
  have hγU (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      γ.extend t ∈ ({z : ℂ | z.im < 0} : Set ℂ) := by
    rw [Path.extend_apply γ ht]
    exact hlower ⟨t,ht⟩
  exact NLS.ComplexAnalysis.curveIntegral_eq_sub_of_primitive
    _ F _ (fun z hz => hF z hz) γ hγ hγU hint

/-- Four regular path pieces above the real axis have the same
oriented integral as a direct reference path, even with corners. -/
theorem sourceCriticalRootRatio_upperPiecewise_pathIntegral_eq
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    {a b c d : ℂ} (left : Path a b) (crossing : Path b c)
    (right : Path d c) (reference : Path a d)
    (hleft : ContDiffOn ℝ 1 left.extend (Icc 0 1))
    (hcross : ContDiffOn ℝ 1 crossing.extend (Icc 0 1))
    (hright : ContDiffOn ℝ 1 right.extend (Icc 0 1))
    (href : ContDiffOn ℝ 1 reference.extend (Icc 0 1))
    (hleftUpper : ∀ u : I, 0 < (left u).im)
    (hcrossUpper : ∀ u : I, 0 < (crossing u).im)
    (hrightUpper : ∀ u : I, 0 < (right u).im)
    (hrefUpper : ∀ u : I, 0 < (reference u).im) :
    (∫ᶜ z in left, NLS.ComplexAnalysis.holomorphicOneForm
      (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
        sourceCanonicalRoot hp hp1 ψ w) z) +
    (∫ᶜ z in crossing, NLS.ComplexAnalysis.holomorphicOneForm
      (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
        sourceCanonicalRoot hp hp1 ψ w) z) -
    (∫ᶜ z in right, NLS.ComplexAnalysis.holomorphicOneForm
      (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
        sourceCanonicalRoot hp hp1 ψ w) z) =
    (∫ᶜ z in reference, NLS.ComplexAnalysis.holomorphicOneForm
      (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
        sourceCanonicalRoot hp hp1 ψ w) z) := by
  obtain ⟨F,hpath⟩ :=
    exists_sourceCriticalRootRatio_upperHalfPlane_pathIntegral_eq_sub
      hp hp1 ψ hreal
  rw [hpath left hleft hleftUpper, hpath crossing hcross hcrossUpper,
    hpath right hright hrightUpper, hpath reference href hrefUpper]
  ring

/-- Four regular path pieces below the real axis have the same
oriented integral as a direct reference path, even with corners. -/
theorem sourceCriticalRootRatio_lowerPiecewise_pathIntegral_eq
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    {a b c d : ℂ} (left : Path a b) (crossing : Path b c)
    (right : Path d c) (reference : Path a d)
    (hleft : ContDiffOn ℝ 1 left.extend (Icc 0 1))
    (hcross : ContDiffOn ℝ 1 crossing.extend (Icc 0 1))
    (hright : ContDiffOn ℝ 1 right.extend (Icc 0 1))
    (href : ContDiffOn ℝ 1 reference.extend (Icc 0 1))
    (hleftLower : ∀ u : I, (left u).im < 0)
    (hcrossLower : ∀ u : I, (crossing u).im < 0)
    (hrightLower : ∀ u : I, (right u).im < 0)
    (hrefLower : ∀ u : I, (reference u).im < 0) :
    (∫ᶜ z in left, NLS.ComplexAnalysis.holomorphicOneForm
      (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
        sourceCanonicalRoot hp hp1 ψ w) z) +
    (∫ᶜ z in crossing, NLS.ComplexAnalysis.holomorphicOneForm
      (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
        sourceCanonicalRoot hp hp1 ψ w) z) -
    (∫ᶜ z in right, NLS.ComplexAnalysis.holomorphicOneForm
      (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
        sourceCanonicalRoot hp hp1 ψ w) z) =
    (∫ᶜ z in reference, NLS.ComplexAnalysis.holomorphicOneForm
      (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
        sourceCanonicalRoot hp hp1 ψ w) z) := by
  obtain ⟨F,hpath⟩ :=
    exists_sourceCriticalRootRatio_lowerHalfPlane_pathIntegral_eq_sub
      hp hp1 ψ hreal
  rw [hpath left hleft hleftLower, hpath crossing hcross hcrossLower,
    hpath right hright hrightLower, hpath reference href hrefLower]
  ring

end NLS.ZakharovShabat
