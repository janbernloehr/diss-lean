import NLS.ZakharovShabat.ClassicalDiscriminantCommutation
import NLS.ZakharovShabat.SourceAntiDiscriminantIdentity
import NLS.ZakharovShabat.SourceDiscriminantCotangent
import NLS.SequenceSpaces.SourceCotangent
import NLS.Fourier.IntervalBilinearParseval

/-! # The actual source discriminant gradient on finite Fourier input

Finite source realization is linear. Differentiating its exact discriminant
identity along finite affine lines identifies the actual source cotangent
with the classical physical variation. Testing the two Fourier coordinate
directions then recovers the physical gradient coefficients, with frequency
reversed as required by unconjugated complex duality.
-/

noncomputable section
set_option maxHeartbeats 800000
open Set Complex MeasureTheory NLS.LinearVolterra NLS.Fourier
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Finite physical Fourier realization is a complex linear map. -/
def finiteSourceCurveLinear : ((ℤ →₀ ℂ) × (ℤ →₀ ℂ)) →ₗ[ℂ] Curve (ℂ × ℂ) where
  toFun := finiteSourceCurve
  map_add' a b := by
    have hpoly (u v : ℤ →₀ ℂ) (x : ℝ) : polynomial (u+v) x = polynomial u x+polynomial v x := by
      exact Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)
    apply ContinuousMap.ext
    intro t
    apply Prod.ext <;> exact hpoly _ _ t
  map_smul' c a := by
    have hpoly (u : ℤ →₀ ℂ) (x : ℝ) : polynomial (c • u) x = c*polynomial u x := by
      unfold polynomial
      rw [Finsupp.sum_smul_index (fun _ => zero_mul _)]
      simp only [Finsupp.sum,Finset.mul_sum,mul_assoc]
    apply ContinuousMap.ext
    intro t
    apply Prod.ext <;> exact hpoly _ t

@[simp] theorem finiteSourceCurveLinear_apply (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) :
    finiteSourceCurveLinear a = finiteSourceCurve a := rfl

/-- Differentiating the actual finite-source identity in an arbitrary
finite direction identifies the two genuine Frechet derivatives. -/
theorem sourceDiscriminantCotangent_finite_direction
    (a b : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) (z : ℂ) :
    sourceDiscriminantCotangent (by simp) z (CoeffPair.ofFinsupp (p := 2) a)
      (CoeffPair.ofFinsupp (p := 2) b) =
        (fderiv ℂ (fun Ψ : Curve (ℂ × ℂ) => classicalDiscriminant Ψ z) (finiteSourceCurve a))
          (finiteSourceCurve b) := by
  let φ := CoeffPair.ofFinsupp (p := 2) a
  let h := CoeffPair.ofFinsupp (p := 2) b
  let Φ := finiteSourceCurve a
  let H := finiteSourceCurve b
  let F : CoeffPair 2 → ℂ := fun ψ => canonicalDiscriminant (by simp) (periodOnePotential ψ) z
  let G : Curve (ℂ × ℂ) → ℂ := fun Ψ => classicalDiscriminant Ψ z
  have hF : DifferentiableAt ℂ F φ :=
    ((analyticOnNhd_canonicalDiscriminant_periodOne (by simp) (by norm_num)
      (z,φ) (mem_univ _)).comp (f := fun ψ : CoeffPair 2 => (z,ψ))
      (analyticAt_const.prod analyticAt_id)).differentiableAt
  have hG : DifferentiableAt ℂ G Φ :=
    ((analyticOnNhd_classicalDiscriminant_joint (z,Φ) (mem_univ _)).comp
      (f := fun Ψ : Curve (ℂ × ℂ) => (z,Ψ)) (analyticAt_const.prod analyticAt_id)).differentiableAt
  have hφ : HasDerivAt (fun c : ℂ => φ+c • h) h 0 := by
    simpa only [one_smul] using! ((hasDerivAt_id (0 : ℂ)).smul_const h).const_add φ
  have hΦ : HasDerivAt (fun c : ℂ => Φ+c • H) H 0 := by
    simpa only [one_smul] using! ((hasDerivAt_id (0 : ℂ)).smul_const H).const_add Φ
  have h₁ : HasDerivAt (F ∘ fun c : ℂ => φ+c • h) ((fderiv ℂ F φ) h) 0 :=
    HasFDerivAt.comp_hasDerivAt_of_eq (𝕜 := ℂ) (E := ℂ) (F := CoeffPair 2)
      (0 : ℂ) hF.hasFDerivAt hφ (by simp only [zero_smul,add_zero])
  have h₂ : HasDerivAt (G ∘ fun c : ℂ => Φ+c • H) ((fderiv ℂ G Φ) H) 0 :=
    HasFDerivAt.comp_hasDerivAt_of_eq (𝕜 := ℂ) (E := ℂ) (F := Curve (ℂ × ℂ))
      (0 : ℂ) hG.hasFDerivAt hΦ (by ext t <;> simp)
  have heq : (fun c : ℂ => F (φ+c • h)) = (fun c => G (Φ+c • H)) := by
    funext c
    have hsrc : CoeffPair.ofFinsupp (p := 2) (a+c • b) = φ+c • h := by
      rw [map_add,map_smul]
    have hcurve : finiteSourceCurve (a+c • b) = Φ+c • H := by
      change finiteSourceCurveLinear (a+c • b) = Φ+c • H
      rw [map_add,map_smul]
      rfl
    have hfinite := canonicalDiscriminant_finite_eq_classical (a+c • b) z
    rw [hsrc,hcurve] at hfinite
    exact hfinite
  change HasDerivAt (fun c : ℂ => F (φ+c • h)) ((fderiv ℂ F φ) h) 0 at h₁
  change HasDerivAt (fun c : ℂ => G (Φ+c • H)) ((fderiv ℂ G Φ) H) 0 at h₂
  rw [heq] at h₁
  exact h₁.unique h₂

/-- The first actual source cotangent coefficient is the physical first
gradient coefficient at the reversed frequency. -/
theorem cotangentCoefficients_sourceDiscriminant_finite_fst
    (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) (z : ℂ) (n : ℤ) :
    (CoeffPair.cotangentCoefficients (by norm_num)
      (sourceDiscriminantCotangent (by simp) z (CoeffPair.ofFinsupp (p := 2) a))).1 n =
        unitFourierCoefficient (fun s => (classicalDiscriminantGradient (finiteSourceCurve a) z s).1) (-n) := by
  rw [CoeffPair.cotangentCoefficients_fst]
  have hdir : CoeffPair.inlCLM (lp.single (2 : ℝ≥0∞) n (1 : ℂ)) =
      CoeffPair.ofFinsupp (p := 2) (Finsupp.single n 1,0) := by
    apply (CoeffPair.toMax 2).injective
    apply Prod.ext <;> ext m <;> simp [lp.single_apply,Pi.single_apply,Finsupp.single_apply,eq_comm]
  rw [hdir,sourceDiscriminantCotangent_finite_direction,
    fderiv_classicalDiscriminant_eq_gradient_integral]
  unfold unitFourierCoefficient
  rw [show -(2*(-n)) = 2*n by ring]
  apply intervalIntegral.integral_congr
  intro s hs
  have hs' : s ∈ Icc (0 : ℝ) 1 := by
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hs
  simp [NLS.LinearVolterra.extend,projIcc_of_mem _ hs',finiteSourceCurve,
    BoundaryCondition.periodOnePair,polynomial]

/-- The second actual source cotangent coefficient has the same reversed
frequency, and the original second-component gradient sign. -/
theorem cotangentCoefficients_sourceDiscriminant_finite_snd
    (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) (z : ℂ) (n : ℤ) :
    (CoeffPair.cotangentCoefficients (by norm_num)
      (sourceDiscriminantCotangent (by simp) z (CoeffPair.ofFinsupp (p := 2) a))).2 n =
        unitFourierCoefficient (fun s => (classicalDiscriminantGradient (finiteSourceCurve a) z s).2) (-n) := by
  rw [CoeffPair.cotangentCoefficients_snd]
  have hdir : CoeffPair.inrCLM (lp.single (2 : ℝ≥0∞) n (1 : ℂ)) =
      CoeffPair.ofFinsupp (p := 2) (0,Finsupp.single n 1) := by
    apply (CoeffPair.toMax 2).injective
    apply Prod.ext <;> ext m <;> simp [lp.single_apply,Pi.single_apply,Finsupp.single_apply,eq_comm]
  rw [hdir,sourceDiscriminantCotangent_finite_direction,
    fderiv_classicalDiscriminant_eq_gradient_integral]
  unfold unitFourierCoefficient
  rw [show -(2*(-n)) = 2*n by ring]
  apply intervalIntegral.integral_congr
  intro s hs
  have hs' : s ∈ Icc (0 : ℝ) 1 := by
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hs
  simp [NLS.LinearVolterra.extend,projIcc_of_mem _ hs',finiteSourceCurve,
    BoundaryCondition.periodOnePair,polynomial]

end NLS.ZakharovShabat
