import NLS.ZakharovShabat.SourceBirkhoffFourierEquivalence
import NLS.ZakharovShabat.SourceBirkhoffLemma16_2

/-!
# Exact Fourier reconstruction in the gradient basis

The imaginary coordinate uses the negative y gradient in the inverse.
The series converges in the source norm for every finite Banach exponent.
-/

noncomputable section
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
theorem sourceBirkhoffFourierInverse_single (n : ℤ) (a b : ℂ) :
    sourceBirkhoffFourierInverse (lp.single p (-n) a, lp.single p (-n) b) =
      a • sourceBirkhoffFreeXGradient p n - b • sourceBirkhoffFreeYGradient p n := by
  apply (CoeffPair.toMax p).injective
  apply Prod.ext <;> ext k
  · change (sourceBirkhoffFourierInverse (lp.single p (-n) a, lp.single p (-n) b)).fst k = _
    rw [sourceBirkhoffFourierInverse_fst]
    change -((lp.single p (-n) a : Coeff p) (-k)-I*(lp.single p (-n) b : Coeff p) (-k))/(Real.sqrt 2 : ℂ) =
      a*((-(Real.sqrt 2 : ℂ)⁻¹)*((lp.single p n (1:ℂ) : Coeff p) k+0))-
        b*(((Real.sqrt 2 : ℂ)*I)⁻¹*((lp.single p n (1:ℂ) : Coeff p) k-0))
    by_cases hk : k = n
    · subst k
      simp only [lp.single_apply_self]
      simp only [mul_inv_rev, inv_I]
      ring
    · have hkn : -k ≠ -n := by omega
      simp [lp.single_apply, hk, hkn]
  · change (sourceBirkhoffFourierInverse (lp.single p (-n) a, lp.single p (-n) b)).snd k = _
    rw [sourceBirkhoffFourierInverse_snd]
    change -((lp.single p (-n) a : Coeff p) k+I*(lp.single p (-n) b : Coeff p) k)/(Real.sqrt 2 : ℂ) =
      a*((-(Real.sqrt 2 : ℂ)⁻¹)*(0+(lp.single p (-n) (1:ℂ) : Coeff p) k))-
        b*(((Real.sqrt 2 : ℂ)*I)⁻¹*(0-(lp.single p (-n) (1:ℂ) : Coeff p) k))
    by_cases hk : k = -n
    · subst k
      simp only [lp.single_apply_self]
      simp only [mul_inv_rev, inv_I]
      ring
    · simp [lp.single_apply, hk]

theorem sourceBirkhoffFourierInverse_hasSum (hp : p ≠ ⊤) (v : Coeff p × Coeff p) :
    HasSum (fun n : ℤ => v.1 (-n) • sourceBirkhoffFreeXGradient p n -
      v.2 (-n) • sourceBirkhoffFreeYGradient p n) (sourceBirkhoffFourierInverse v) := by
  have h := (HasSum.mapL (sourceBirkhoffFourierInverse (p := p))
    ((lp.hasSum_single hp v.1).prodMk (lp.hasSum_single hp v.2)))
  have hr := (Equiv.neg ℤ).hasSum_iff.mpr h
  convert hr using 1
  funext n
  exact (sourceBirkhoffFourierInverse_single n (v.1 (-n)) (v.2 (-n))).symm

theorem sourceBirkhoffFourierInverse_y_mode (n : ℤ) :
    sourceBirkhoffFourierInverse (0, lp.single p (-n) 1) = -sourceBirkhoffFreeYGradient p n := by
  simpa using (sourceBirkhoffFourierInverse_single (p := p) n 0 1)

theorem sourceBirkhoffFourier_freeY (n : ℤ) :
    sourceBirkhoffFourier (sourceBirkhoffFreeYGradient p n) = -(0, lp.single p (-n) 1) := by
  apply neg_injective
  rw [neg_neg, ← map_neg, ← sourceBirkhoffFourierInverse_y_mode]
  exact sourceBirkhoffFourier_fourierInverse _

theorem sourceBirkhoffFreeYGradient_ne_fourierInverse_y_mode (n : ℤ) :
    sourceBirkhoffFourierInverse (0, lp.single p (-n) 1) ≠ sourceBirkhoffFreeYGradient p n := by
  intro he
  have h := congrArg (fun v : CoeffPair p => (sourceBirkhoffFourier v).2 (-n)) he
  rw [sourceBirkhoffFourier_fourierInverse, sourceBirkhoffFourier_freeY] at h
  norm_num at h

end NLS.ZakharovShabat
