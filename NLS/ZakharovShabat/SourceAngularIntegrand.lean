import NLS.ZakharovShabat.SourceAngularRootSheet
import NLS.ZakharovShabat.SourcePsiLemma12_12
import NLS.ComplexAnalysis.ConvexHolomorphicPrimitive

/-!
# Angular integrands and regular path integrals

Use the actual analytic psi family from Section 12 on an explicitly
chosen root sheet. Its quotient is jointly analytic wherever the
sheet is analytic and nonzero. Curve integrals on regular parts of
the sheet have primitives and are independent of the regular path
inside convex charts. Integration from the singular periodic endpoint
and the global off-diagonal estimates are subsequent steps.
-/

noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual psi numerator divided by the chosen spectral root sheet. -/
def sourceAngularIntegrand (n : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (Q : ℂ × CoeffPair p → ℂ) :
    ℂ × CoeffPair p → ℂ :=
  fun t => sourcePsiCandidate n (t.1,(s n t.2 : Coeff p)) / Q t

/-- An angular integral along a specified path and specified root sheet.
Curve integrability is proved separately; the definition also accommodates
integrable singular endpoint paths. -/
def sourceAngularPathIntegral (n : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (Q : ℂ × CoeffPair p → ℂ)
    (ψ : CoeffPair p) {a b : ℂ} (γ : Path a b) : ℂ :=
  ∫ᶜ z in γ, holomorphicOneForm (fun w => sourceAngularIntegrand n s Q (w,ψ)) z

theorem sourceAngularIntegrand_neg_sheet (n : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (Q : ℂ × CoeffPair p → ℂ)
    (t : ℂ × CoeffPair p) :
    sourceAngularIntegrand n s (fun u => -Q u) t = -sourceAngularIntegrand n s Q t := by
  simp only [sourceAngularIntegrand, div_neg]

theorem sourceAngularIntegrand_canonical (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (t : ℂ × CoeffPair p) :
    sourceAngularIntegrand n s (fun u => sourceCanonicalRoot hp hp1 u.2 u.1) t =
      sourcePsiContourIntegrandJoint hp hp1 n (t.1,((s n t.2 : Coeff p),t.2)) := rfl

namespace SourcePsiIsolatingComplexExtension
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- Analyticity uses the proved entire numerator family, and needs no
canonical-cut restriction on the chosen local sheet. -/
theorem angular_integrand_analyticOnNhd
    (hs : SourcePsiIsolatingComplexExtension hp hp1 W s) (n : ℤ)
    (Q : ℂ × CoeffPair p → ℂ) (D : Set (ℂ × CoeffPair p))
    (hD : D ⊆ univ ×ˢ W) (hQ : AnalyticOnNhd ℂ Q D)
    (hne : ∀ t ∈ D, Q t ≠ 0) :
    AnalyticOnNhd ℂ (sourceAngularIntegrand n s Q) D := by
  intro t ht
  exact (hs.analytic_numerator_joint n t (hD ht)).div (hQ t ht) (hne t ht)

/-- The terminal-normalized sheet supports every angular integrand
on its intersection with the common actual psi source domain. -/
theorem angular_rootSheet_integrand_analyticOnNhd
    (hs : SourcePsiIsolatingComplexExtension hp hp1 W s) (n : ℤ)
    (w : ℂ) (hw : w ≠ 0) :
    AnalyticOnNhd ℂ (sourceAngularIntegrand n s (sourceAngularRootSheet hp w))
      (sourceAngularRootSheetDomain hp w ∩ (univ ×ˢ W)) :=
  hs.angular_integrand_analyticOnNhd n _ _ inter_subset_right
    ((analyticOnNhd_sourceAngularRootSheet hp hp1 w).mono inter_subset_left)
    (fun t ht => sourceAngularRootSheet_ne_zero hp w hw t ht.1)

/-- On a fixed spectral slice of a regular sheet, the angular
integrand is holomorphic in the spectral parameter. -/
theorem angular_integrand_analyticOnNhd_spectral
    (hs : SourcePsiIsolatingComplexExtension hp hp1 W s) (n : ℤ)
    (Q : ℂ × CoeffPair p → ℂ) (D : Set (ℂ × CoeffPair p))
    (hD : D ⊆ univ ×ˢ W) (hQ : AnalyticOnNhd ℂ Q D)
    (hne : ∀ t ∈ D, Q t ≠ 0)
    (ψ : CoeffPair p) (T : Set ℂ) (hT : ∀ z ∈ T, (z,ψ) ∈ D) :
    AnalyticOnNhd ℂ (fun z => sourceAngularIntegrand n s Q (z,ψ)) T := by
  intro z hz
  exact (hs.angular_integrand_analyticOnNhd n Q D hD hQ hne (z,ψ) (hT z hz)).comp
    (x := z) (f := fun w : ℂ => (w,ψ)) (analyticAt_id.prod analyticAt_const)

/-- Regular angular integrals exist for C¹ paths in a regular sheet chart. -/
theorem angular_curveIntegrable
    (hs : SourcePsiIsolatingComplexExtension hp hp1 W s) (n : ℤ)
    (Q : ℂ × CoeffPair p → ℂ) (D : Set (ℂ × CoeffPair p))
    (hD : D ⊆ univ ×ˢ W) (hQ : AnalyticOnNhd ℂ Q D)
    (hne : ∀ t ∈ D, Q t ≠ 0)
    (ψ : CoeffPair p) (T : Set ℂ) (hT : ∀ z ∈ T, (z,ψ) ∈ D)
    {a b : ℂ} (γ : Path a b) (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hγT : ∀ t : I, γ t ∈ T) :
    CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand n s Q (z,ψ))) γ := by
  have hf := (hs.angular_integrand_analyticOnNhd_spectral n Q D hD hQ hne ψ T hT).continuousOn
  have hω : ContinuousOn
      (holomorphicOneForm (fun z => sourceAngularIntegrand n s Q (z,ψ))) T := by
    exact hf.smul continuousOn_const
  exact hω.curveIntegrable_of_contDiffOn hγ hγT

/-- Within a convex regular chart, the actual angular integrals
are independent of the chosen C¹ regular path. -/
theorem angular_pathIntegral_eq_of_convex_paths
    (hs : SourcePsiIsolatingComplexExtension hp hp1 W s) (n : ℤ)
    (Q : ℂ × CoeffPair p → ℂ) (D : Set (ℂ × CoeffPair p))
    (hD : D ⊆ univ ×ˢ W) (hQ : AnalyticOnNhd ℂ Q D)
    (hne : ∀ t ∈ D, Q t ≠ 0)
    (ψ : CoeffPair p) (T : Set ℂ) (hT : ∀ z ∈ T, (z,ψ) ∈ D)
    (hconv : Convex ℝ T) (hopen : IsOpen T)
    {a b : ℂ} (γ₁ γ₂ : Path a b)
    (hγ₁ : ContDiffOn ℝ 1 γ₁.extend (Icc 0 1))
    (hγ₂ : ContDiffOn ℝ 1 γ₂.extend (Icc 0 1))
    (hγ₁T : ∀ t : I, γ₁ t ∈ T) (hγ₂T : ∀ t : I, γ₂ t ∈ T) :
    sourceAngularPathIntegral n s Q ψ γ₁ = sourceAngularPathIntegral n s Q ψ γ₂ := by
  have hf := hs.angular_integrand_analyticOnNhd_spectral n Q D hD hQ hne ψ T hT
  apply curveIntegral_eq_of_convex_paths_one _ T hconv hopen hf.differentiableOn
    γ₁ γ₂ hγ₁ hγ₂
  · intro t ht
    simpa only [Path.extend_apply γ₁ ht] using hγ₁T ⟨t,ht⟩
  · intro t ht
    simpa only [Path.extend_apply γ₂ ht] using hγ₂T ⟨t,ht⟩
  · exact hs.angular_curveIntegrable n Q D hD hQ hne ψ T hT γ₁ hγ₁ hγ₁T
  · exact hs.angular_curveIntegrable n Q D hD hQ hne ψ T hT γ₂ hγ₂ hγ₂T

end SourcePsiIsolatingComplexExtension

/-- Section 13 starts with the actual family satisfying Lemma 12.12,
not a postulated numerator family. All its regular sheet integrands are
jointly analytic on the same common complex source domain. -/
theorem exists_sourceAngularIntegrand_common_domain (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ U W : Set (CoeffPair p), SourceSpectralIsolationNeighborhood hp hp1 U ∧
      IsOpen W ∧ IsSimplyConnected W ∧ realTypeSourceLocus p ⊆ W ∧ W ⊆ U ∧
      ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
        SourcePsiSquaredGapComplexExtension hp hp1 W s ∧
          ∀ n : ℤ, ∀ w : ℂ, w ≠ 0 →
            AnalyticOnNhd ℂ (sourceAngularIntegrand n s (sourceAngularRootSheet hp w))
              (sourceAngularRootSheetDomain hp w ∩ (univ ×ˢ W)) := by
  obtain ⟨U,W,hU,hWopen,hWconn,hreal,hWU,s,hs⟩ := exists_sourcePsi_lemma12_12 hp hp1
  exact ⟨U,W,hU,hWopen,hWconn,hreal,hWU,s,hs,fun n w hw =>
    hs.toSourcePsiIsolatingComplexExtension.angular_rootSheet_integrand_analyticOnNhd n w hw⟩

end NLS.ZakharovShabat
