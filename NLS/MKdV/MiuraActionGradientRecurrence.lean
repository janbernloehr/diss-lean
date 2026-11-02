import NLS.MKdV.MiuraDiscriminantCotangent
import NLS.MKdV.MiuraActionLevelExtension
import NLS.ZakharovShabat.SourceDiagonalLaurentDerivative

/-! # Exact Fourier gradient recurrence for the actual Laurent actions

The physical discriminant recurrence is integrated on one zero-excluding
circle. The actual source Frechet derivatives, rather than prescribed
gradient coefficients, satisfy the identity at every Fourier mode and
every integer level on the original real H1 diagonal.
-/
noncomputable section
open Set Metric Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem localLaurentActionGradient_fourier (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) {φ : realDiagonalSourceLocus 2}
    (C : SourceDiagonalLaurentLocalChart (by simp) (by norm_num) φ)
    (hC : (realDiagonalH1Source a ha).val ∈ ball φ.val C.radius)
    (n k m : ℤ) (hn : n ≠ 0) :
    (2*I*(Real.pi : ℂ)*m) *
        ((CoeffPair.cotangentCoefficients le_rfl (fderiv ℂ (C.action n (k-1)) (sobolevSourceInclusion (a,a)))).1 (-m) +
         (CoeffPair.cotangentCoefficients le_rfl (fderiv ℂ (C.action n (k-1)) (sobolevSourceInclusion (a,a)))).2 (-m)) =
      2*I*((CoeffPair.cotangentCoefficients le_rfl (fderiv ℂ (C.action n k) (sobolevSourceInclusion (a,a)))).1 (-m) -
         (CoeffPair.cotangentCoefficients le_rfl (fderiv ℂ (C.action n k) (sobolevSourceInclusion (a,a)))).2 (-m)) := by
  let ψ := realDiagonalH1Source a ha
  let v₁ : CoeffPair 2 := CoeffPair.inlCLM (lp.single 2 (-m) 1)
  let v₂ : CoeffPair 2 := CoeffPair.inrCLM (lp.single 2 (-m) 1)
  simp only [CoeffPair.cotangentCoefficients_fst,CoeffPair.cotangentCoefficients_snd]
  change (2*I*(Real.pi : ℂ)*m) * ((fderiv ℂ (C.action n (k-1)) ψ.val) v₁+
    (fderiv ℂ (C.action n (k-1)) ψ.val) v₂) =
      2*I*((fderiv ℂ (C.action n k) ψ.val) v₁-(fderiv ℂ (C.action n k) ψ.val) v₂)
  rw [← map_add,← map_sub,C.fderiv_action ψ hC n (k-1) hn (v₁+v₂),C.fderiv_action ψ hC n k hn (v₁-v₂)]
  rw [mul_left_comm (2*I*(Real.pi : ℂ)*m),mul_left_comm (2*I)]
  congr 1
  rw [← circleIntegral.integral_const_mul,← circleIntegral.integral_const_mul]
  apply circleIntegral.integral_congr (C.contourRadius_pos n).le
  intro z hz
  have hz0 : z ≠ 0 := by intro he; exact C.zero_not_mem_contour_disc n hn (he ▸ sphere_subset_closedBall hz)
  have hp : z*z^(k-2) = z^(k-1) := by
    calc
      z*z^(k-2) = z^(1 : ℤ)*z^(k-2) := by rw [zpow_one]
      _ = z^(k-1) := by rw [← zpow_add₀ hz0]; congr 1; ring
  have hd := miuraDiscriminantCotangent_fourier a z m
  simp only [CoeffPair.cotangentCoefficients_fst,CoeffPair.cotangentCoefficients_snd] at hd
  change (2*I*(Real.pi : ℂ)*m) *
    (sourceDiscriminantCotangent (by simp) z ψ.val v₁+sourceDiscriminantCotangent (by simp) z ψ.val v₂) =
      2*I*z*(sourceDiscriminantCotangent (by simp) z ψ.val v₁-sourceDiscriminantCotangent (by simp) z ψ.val v₂) at hd
  dsimp only
  rw [show k-1-1 = k-2 by ring]
  calc
    _ = (z^(k-2)/sourceCanonicalRoot (by simp) (by norm_num) ψ.val z) *
        ((2*I*(Real.pi : ℂ)*m) *
          (sourceDiscriminantCotangent (by simp) z ψ.val v₁+sourceDiscriminantCotangent (by simp) z ψ.val v₂)) := by
      rw [map_add]; ring
    _ = _ := by rw [hd,map_sub,← hp]; ring

/-- The actual global Laurent-action gradients satisfy the diagonal
recurrence at every integer level, with the physical Fourier multiplier. -/
theorem miuraLaurentActionGradient_fourier (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n k m : ℤ) (hn : n ≠ 0) :
    (2*I*(Real.pi : ℂ)*m) *
        ((CoeffPair.cotangentCoefficients le_rfl (fderiv ℂ (sourceDiagonalLaurentAction (by simp) (by norm_num) n (k-1))
          (sobolevSourceInclusion (a,a)))).1 (-m) +
         (CoeffPair.cotangentCoefficients le_rfl (fderiv ℂ (sourceDiagonalLaurentAction (by simp) (by norm_num) n (k-1))
          (sobolevSourceInclusion (a,a)))).2 (-m)) =
      2*I*((CoeffPair.cotangentCoefficients le_rfl (fderiv ℂ (sourceDiagonalLaurentAction (by simp) (by norm_num) n k)
          (sobolevSourceInclusion (a,a)))).1 (-m) -
         (CoeffPair.cotangentCoefficients le_rfl (fderiv ℂ (sourceDiagonalLaurentAction (by simp) (by norm_num) n k)
          (sobolevSourceInclusion (a,a)))).2 (-m)) := by
  let ψ : realDiagonalSourceLocus 2 := ⟨(realDiagonalH1Source a ha).val,⟨(realDiagonalH1Source a ha).property,rfl⟩⟩
  let A := sourceDiagonalLaurentAtlas (by simp : (2 : ℝ≥0∞) ≠ ⊤) (by norm_num)
  let C := A.localChart ψ
  have he (j : ℤ) : sourceDiagonalLaurentAction (by simp) (by norm_num) n j =ᶠ[𝓝 ψ.val] C.action n j := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self C.radius_pos)] with χ hχ
    exact A.action_eq_local n j hn ψ hχ
  have hfd (j : ℤ) : fderiv ℂ (sourceDiagonalLaurentAction (by simp) (by norm_num) n j)
      (sobolevSourceInclusion (a,a)) = fderiv ℂ (C.action n j) (sobolevSourceInclusion (a,a)) := (he j).fderiv_eq
  rw [hfd (k-1),hfd k]
  exact localLaurentActionGradient_fourier a ha C (mem_ball_self C.radius_pos) n k m hn

end NLS.MKdV
