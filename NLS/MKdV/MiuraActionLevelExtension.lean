import NLS.MKdV.MiuraSpectralActionContours
import NLS.ZakharovShabat.SourceDiagonalLaurentCompatibility

/-! # The complex L² extension of every actual mKdV action level

The NLS Laurent functions are defined by their genuine local contours,
and are analytic on one ambient open L² source neighborhood containing
the entire real diagonal. On every original real H1 input their even
levels are exactly twice the physical Hill contour actions.
-/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem realDiagonalH1Source_mem_LaurentDomain (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) :
    (realDiagonalH1Source a ha).val ∈ sourceDiagonalLaurentDomain (by simp) (by norm_num) := by
  apply realDiagonal_subset_sourceDiagonalLaurentDomain
  exact ⟨(realDiagonalH1Source a ha).property,rfl⟩

theorem sourceDiagonalLaurentAction_eq_two_miuraActionLevel (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (n : ℕ) (hn : 1 ≤ n) (k : ℤ) :
    sourceDiagonalLaurentAction (by simp) (by norm_num) n (2*k-2)
        (sobolevSourceInclusion (a,a)) = 2*miuraMKdVActionLevel a ha n k := by
  let F := miuraActionContourFamily a ha
  change sourceDiagonalLaurentAction (by simp) (by norm_num) n (2*k-2)
    (realDiagonalH1Source a ha).val = _
  rw [sourceDiagonalLaurentAction_eq_real (by simp) (by norm_num)
    (realDiagonalH1Source a ha) (realDiagonalH1Source_mem_LaurentDomain a ha) n (2*k-2) (by omega)]
  simpa only [sourceRealLaurentAction,miuraMKdVActionLevel,F,show 2*k-2-1 = 2*k-3 by ring] using
    (F.two_mul_action_eq_realIntegral n hn k).symm

/-- The single ambient open source neighborhood is chosen before the
index and integer level, exactly as required by Lemma 7. -/
theorem exists_miuraActionLevel_analytic_extension :
    ∃ U : Set (CoeffPair 2), IsOpen U ∧ realDiagonalSourceLocus 2 ⊆ U ∧
      ∀ (n : ℕ), 1 ≤ n → ∀ k : ℤ,
        AnalyticOnNhd ℂ (sourceDiagonalLaurentAction (by simp) (by norm_num) n (2*k-2)) U ∧
          ∀ (a : ScalarDomain 2) (ha : ∀ j, a.val j = conj (a.val (-j))),
            sourceDiagonalLaurentAction (by simp) (by norm_num) n (2*k-2)
              (sobolevSourceInclusion (a,a)) = 2*miuraMKdVActionLevel a ha n k := by
  refine ⟨sourceDiagonalLaurentDomain (by simp) (by norm_num),
    isOpen_sourceDiagonalLaurentDomain _ _,realDiagonal_subset_sourceDiagonalLaurentDomain _ _,?_⟩
  intro n hn k
  exact ⟨analyticOnNhd_sourceDiagonalLaurentAction _ _ n (2*k-2) (by omega),
    fun a ha => sourceDiagonalLaurentAction_eq_two_miuraActionLevel a ha n hn k⟩

/-- The literal H1 coefficient diagonal, as a bounded complex-linear map. -/
def miuraActionSourceCLM : ScalarDomain 2 →L[ℂ] CoeffPair 2 :=
  sobolevSourceInclusion.comp
    ((ContinuousLinearMap.id ℂ (ScalarDomain 2)).prod (ContinuousLinearMap.id ℂ (ScalarDomain 2)))

@[simp] theorem miuraActionSourceCLM_apply (a : ScalarDomain 2) :
    miuraActionSourceCLM a = sobolevSourceInclusion (a,a) := rfl

def miuraComplexActionDomain : Set (ScalarDomain 2) :=
  miuraActionSourceCLM ⁻¹' sourceDiagonalLaurentDomain (by simp) (by norm_num)

/-- A complex extension of the independently defined physical contour
actions. Its real agreement is proved below, not used as its definition. -/
def miuraComplexActionLevel (n : ℕ) (k : ℤ) (a : ScalarDomain 2) : ℂ :=
  (1/2 : ℂ)*sourceDiagonalLaurentAction (by simp) (by norm_num) n (2*k-2) (miuraActionSourceCLM a)

theorem isOpen_miuraComplexActionDomain : IsOpen miuraComplexActionDomain :=
  (isOpen_sourceDiagonalLaurentDomain _ _).preimage miuraActionSourceCLM.continuous

theorem real_mem_miuraComplexActionDomain (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) : a ∈ miuraComplexActionDomain :=
  realDiagonalH1Source_mem_LaurentDomain a ha

theorem analyticOnNhd_miuraComplexActionLevel (n : ℕ) (hn : 1 ≤ n) (k : ℤ) :
    AnalyticOnNhd ℂ (miuraComplexActionLevel n k) miuraComplexActionDomain := by
  intro a ha
  exact analyticAt_const.mul
    ((analyticOnNhd_sourceDiagonalLaurentAction _ _ n (2*k-2) (by omega) _ ha).comp
      (miuraActionSourceCLM.analyticAt a))

theorem miuraComplexActionLevel_eq_real (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (n : ℕ) (hn : 1 ≤ n) (k : ℤ) :
    miuraComplexActionLevel n k a = miuraMKdVActionLevel a ha n k := by
  rw [miuraComplexActionLevel,miuraActionSourceCLM_apply,
    sourceDiagonalLaurentAction_eq_two_miuraActionLevel a ha n hn k]
  ring

/-- The actual Frechet derivative of the analytic extension, retaining
the coefficient-preserving diagonal and the action's exact factor 1/2. -/
theorem hasFDerivAt_miuraComplexActionLevel (n : ℕ) (hn : 1 ≤ n) (k : ℤ)
    (a : ScalarDomain 2) (ha : a ∈ miuraComplexActionDomain) :
    HasFDerivAt (miuraComplexActionLevel n k)
      ((1/2 : ℂ) • ((fderiv ℂ (sourceDiagonalLaurentAction (by simp) (by norm_num) n (2*k-2))
        (miuraActionSourceCLM a)).comp miuraActionSourceCLM)) a := by
  exact (((analyticOnNhd_sourceDiagonalLaurentAction _ _ n (2*k-2) (by omega) _ ha).differentiableAt.hasFDerivAt).comp
    a miuraActionSourceCLM.hasFDerivAt).const_mul (1/2 : ℂ)

end NLS.MKdV
