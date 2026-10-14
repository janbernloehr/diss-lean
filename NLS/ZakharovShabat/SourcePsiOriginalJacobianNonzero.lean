import NLS.ZakharovShabat.SourcePsiOriginalJacobianContour
import NLS.ZakharovShabat.SourcePsiOriginalZetaRegular

/-!
# Original diagonal mean value and nonvanishing

Lemma 12.3 applies to the rotated literal zeta on the filled original
disk. One proof covers open and collapsed real gaps and identifies an
actual point of the selected gap. Full root placement makes the product
nonzero there, so every retained diagonal Jacobian entry is nonzero.
-/

noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem SourceLemma12_4Data.originalJacobianEntry_diagonal_meanValue
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (H : SourceLemma12_4Data hp hp1 W)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (ψ : CoeffPair p) (hψW : ψ ∈ W) (hψV : ψ ∈ V)
    (hreal : IsRealType (CoeffPair.toMax p ψ)) (n m : ℤ) (hmn : m ≠ n)
    (a : Coeff p) (ha : a ∈ sourcePsiOriginalRootPlacement D)
    (haReal : ∀ k : ℤ, (a k).im = 0) :
    ∃ μ ∈ sourcePeriodicSegment hp hp1 ψ m,
      sourcePsiOriginalJacobianEntry hp hp1 n m m a ψ =
        -(2*(Real.pi:ℂ)*I)*(((n-m:ℤ):ℂ)*sourcePsiZeta hp hp1 n m a ψ μ) := by
  obtain ⟨d,r,hr,he⟩ := hD.discs m
  let P := hD.periodCircle ψ hψV m d r hr he
  let F : ℂ → ℂ := fun z => ((n-m:ℤ):ℂ)*sourcePsiZeta hp hp1 n m a ψ z
  let g : ℂ → ℂ := fun z => (-I)*F z
  let J := sourcePsiOriginalJacobianEntry hp hp1 n m m a ψ
  have hF := H.previous.quotients.originalZeta_analyticOnNhd hD ψ hψW hψV hreal n m hmn a ha d r hr he
  have hg : AnalyticOnNhd ℂ g (closedBall (P.center:ℂ) P.radius) := by
    intro z hz
    exact analyticAt_const.mul (analyticAt_const.mul (hF z hz))
  obtain ⟨_,_,_,_,hmean⟩ := P.lemma12_3_circle g hg
  obtain ⟨μ,hμ,hvalue⟩ := hmean
    (hD.originalZeta_rotated_real_on_gap ψ hψV hreal n m hmn a ha haReal)
  have hJ : J = ∮ z in C((d:ℂ),r), F z/sourceStandardRoot hp hp1 ψ m z :=
    H.originalJacobianEntry_diagonal_contour hD ψ hψW hψV hreal n m hmn a ha d r hr he
  have hInt : (∮ z in C((d:ℂ),r), g z/sourceStandardRoot hp hp1 ψ m z) = (-I)*J := by
    rw [hJ, ← circleIntegral.integral_const_mul]
    apply circleIntegral.integral_congr hr.le
    intro z _
    dsimp [g]
    ring
  let K : ℂ := 2*(Real.pi:ℂ)*I
  have hK : K ≠ 0 := mul_ne_zero
    (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) I_ne_zero
  have hv : K⁻¹*((-I)*J) = -g μ := by
    simpa only [PiecewiseC1Loop.normalizedIntegral, PiecewiseC1Loop.integral_circle,
      P, SourceIsolatingNeighborhoods.periodCircle, hInt, K] using hvalue
  have hs : (-I)*J = -(K*g μ) := by
    simpa [mul_assoc,hK] using congrArg (fun z : ℂ => K*z) hv
  refine ⟨μ,hμ,?_⟩
  apply mul_left_cancel₀ (neg_ne_zero.mpr I_ne_zero)
  calc
    (-I)*J = -(K*g μ) := hs
    _ = (-I)*(-(2*(Real.pi:ℂ)*I)*(((n-m:ℤ):ℂ)*sourcePsiZeta hp hp1 n m a ψ μ)) := by
      dsimp [K,g,F]
      ring

theorem SourceLemma12_4Data.originalJacobianEntry_diagonal_ne_zero
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (H : SourceLemma12_4Data hp hp1 W)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (ψ : CoeffPair p) (hψW : ψ ∈ W) (hψV : ψ ∈ V)
    (hreal : IsRealType (CoeffPair.toMax p ψ)) (n m : ℤ) (hmn : m ≠ n)
    (a : Coeff p) (ha : a ∈ sourcePsiOriginalRootPlacement D)
    (haReal : ∀ k : ℤ, (a k).im = 0) :
    sourcePsiOriginalJacobianEntry hp hp1 n m m a ψ ≠ 0 := by
  obtain ⟨μ,hμ,he⟩ := H.originalJacobianEntry_diagonal_meanValue hD ψ hψW hψV hreal n m hmn a ha haReal
  rw [he]
  exact mul_ne_zero (neg_ne_zero.mpr (mul_ne_zero
    (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) I_ne_zero))
    (mul_ne_zero (by exact_mod_cast sub_ne_zero.mpr hmn.symm)
      (hD.originalZeta_ne_zero_on_gap ψ hψV n m hmn a ha μ hμ))

end NLS.ZakharovShabat
