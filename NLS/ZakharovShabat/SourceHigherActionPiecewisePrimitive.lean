import NLS.ComplexAnalysis.PiecewisePolynomialIntegrationByParts
import NLS.ComplexAnalysis.PiecewiseContourCongruence
import NLS.ZakharovShabat.SourceHigherActionPiecewiseContour
import NLS.ZakharovShabat.SourceIndexedHigherActionAnalytic
import NLS.ZakharovShabat.SourceSection24Original

/-! # Higher actions and the original primitive on piecewise circuits

Formula (5.2) retains every printed level, the original primitive and
all winding-one isolating circuits, including corners. No analyticity
through the enclosed spectral cut is assumed.
-/
noncomputable section
open Set Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Formula (5.2) on any piecewise C¹ loop in the original root domain. -/
theorem sourceHigherActionContour_eq_primitive
    (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p)) (q : ℤ)
    (ψ : CoeffPair p) (D : SourceAbelianSpectralChart hp hp1 W ψ)
    (Γ : PiecewiseC1Loop) (hΓ : Γ.Inside (sourceCanonicalRootDomain hp hp1 ψ))
    (k : ℕ) :
    sourceHigherActionContour hp hp1 ψ Γ k = -(Real.pi : ℂ)⁻¹*
      Γ.integral (fun z => z^k*sourceFullAbelianPrimitive hp hp1 W q (z,ψ)) := by
  let F : ℂ → ℂ := fun z => sourceFullAbelianPrimitive hp hp1 W q (z,ψ)
  have hf : AnalyticOnNhd ℂ F (sourceCanonicalRootDomain hp hp1 ψ) :=
    (sourceFullAbelianPrimitive_spectral_analytic D q).mono
      (sourceCanonicalRootDomain_subset_openGapComplement hp hp1 ψ)
  have he : Γ.integral (fun z => z^(k+1)*sourceCriticalRootRatioJoint hp hp1 (z,ψ)) =
      Γ.integral (fun z => z^(k+1)*deriv F z) := by
    apply Γ.integral_congr hΓ
    intro z hz
    exact congrArg (fun v => z^(k+1)*v)
      (sourceFullAbelianPrimitive_hasDerivAt D q z hz).deriv.symm
  rw [sourceHigherActionContour,he,Γ.integral_pow_mul_deriv_eq_neg F _ hf hΓ k]
  have hk : (k+1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  dsimp only [F]
  field_simp

/-- Any winding-one original isolating circuit has the literal primitive formula. -/
theorem sourceIndexedHigherAction_eq_piecewise_primitive
    {hp : p ≠ ⊤} {hp1 : 1 < p} {ψ : CoeffPair p} {n : ℤ}
    (C : SourceCriticalRootPeriodCircle hp hp1 ψ n)
    {W : Set (CoeffPair p)} (D : SourceAbelianSpectralChart hp hp1 W ψ)
    (Γ : PiecewiseC1Loop)
    (hΓ : Γ.Inside (Metric.ball (C.center : ℂ) C.radius \ sourcePeriodicSegment hp hp1 ψ n))
    (hw : Γ.windingIntegral (canonicalPeriodicMidpoint hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) n) = 1)
    (k : ℕ) (q : ℤ) :
    sourceIndexedHigherAction hp hp1 n k ψ = -(Real.pi : ℂ)⁻¹*
      Γ.integral (fun z => z^k*sourceFullAbelianPrimitive hp hp1 W q (z,ψ)) := by
  have hr : Γ.Inside (sourceCanonicalRootDomain hp hp1 ψ) := by
    intro i u m
    by_cases hm : m = n
    · subst m
      exact (hΓ i u).2
    · exact C.closedBall_subset_omittedDomain (Metric.ball_subset_closedBall (hΓ i u).1) m hm
  rw [← C.higherActionContour_eq Γ k hΓ hw]
  exact sourceHigherActionContour_eq_primitive hp hp1 W q ψ D Γ hr k

/-- Formula (5.2) retains the chosen original family, primitive and source domain. -/
theorem SourceSection24Data.higherAction_eq_original_piecewise_primitive
    {W₀ W V Wa B U : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
    {D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s}
    {A : SourceAbelianMomentAtlas (by simp) (by norm_num) Wa s}
    (Q : SourceSection24Data D A B U) (ψ : CoeffPair 2) (hψ : ψ ∈ U)
    (n : ℤ) (k : ℕ) (q : ℤ)
    (C : SourceCriticalRootPeriodCircle (by simp) (by norm_num) ψ n)
    (Γ : PiecewiseC1Loop)
    (hΓ : Γ.Inside (Metric.ball (C.center : ℂ) C.radius \
      sourcePeriodicSegment (by simp) (by norm_num) ψ n))
    (hw : Γ.windingIntegral (canonicalPeriodicMidpoint (by simp) (by norm_num)
      (periodOnePotential ψ) (periodOnePotential_mem ψ) n) = 1) :
    sourceIndexedHigherAction (by simp) (by norm_num) n k ψ = -(Real.pi : ℂ)⁻¹*
      Γ.integral (fun z => z^k*sourceFullAbelianPrimitive (by simp) (by norm_num) B q (z,ψ)) := by
  obtain ⟨E⟩ := Q.charts ψ hψ
  exact sourceIndexedHigherAction_eq_piecewise_primitive C E Γ hΓ hw k q

end NLS.ZakharovShabat
