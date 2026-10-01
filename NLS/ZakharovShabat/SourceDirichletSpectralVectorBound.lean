import NLS.ZakharovShabat.SourceDiscriminantEnergyBound
import NLS.ZakharovShabat.SourceDirichletSpectralMassConservation
import NLS.ZakharovShabat.SourceDirichletSpectralSheet

/-! # Uniform speed bounds for actual Hilbert spectral curves

The actual Poisson direction is bounded by the source cotangent norm.
The discriminant energy estimate consequently controls the indexed field
on a source norm ball with bounded selected Dirichlet coordinate. Along
real integral curves, the conserved source norm and compact fixed sheet
provide those bounds on the whole interval. The resulting curve is
Lipschitz in the original Hilbert source norm.
-/

noncomputable section
open Set Metric Complex NLS.Poisson
open scoped ENNReal NNReal
namespace NLS
local instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

/-- A numerical bound for the actual Hilbert source Poisson direction
in the original source norm, including both reflected components. -/
theorem Poisson.norm_sourceHamiltonianDirection_two_le (L : CoeffPair 2 →L[ℂ] ℂ) :
    ‖sourceHamiltonianDirection (by norm_num) L‖ ≤ 2 * ‖L‖ := by
  let a := CoeffPair.cotangentCoefficients (by norm_num : (2 : ℝ≥0∞) ≤ 2) L
  have he : sourceHamiltonianDirection (by norm_num) L = hilbertPairHamiltonianDirection a := by
    apply (CoeffPair.toMax 2).injective
    apply Prod.ext <;> ext n <;> rfl
  rw [he]
  have hs := WithLp.prod_norm_sq_eq_of_L2 (hilbertPairHamiltonianDirection a)
  simp only [hilbertPairHamiltonianDirection_fst,hilbertPairHamiltonianDirection_snd,
    norm_smul,norm_neg,norm_I,Coeff.reflection.norm_map,one_mul] at hs
  have ha : ‖a‖ ≤ ‖L‖ := CoeffPair.norm_cotangentCoefficients_le (by norm_num) L
  have h₁ : ‖a.1‖ ≤ ‖L‖ := (norm_fst_le a).trans ha
  have h₂ : ‖a.2‖ ≤ ‖L‖ := (norm_snd_le a).trans ha
  have hs₁ := sq_le_sq₀ (norm_nonneg a.1) (norm_nonneg L) |>.mpr h₁
  have hs₂ := sq_le_sq₀ (norm_nonneg a.2) (norm_nonneg L) |>.mpr h₂
  nlinarith [norm_nonneg (hilbertPairHamiltonianDirection a),norm_nonneg L]

namespace ZakharovShabat

/-- The actual indexed field has an explicit uniform bound whenever
the original source norm and selected spectral coordinate are bounded. -/
theorem norm_sourceDirichletSpectralVector_le_of_bounds (k : ℤ) (φ : CoeffPair 2)
    (M R : ℝ) (hφ : ‖φ‖ ≤ M)
    (hμ : ‖canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet φ k‖ ≤ R) :
    ‖sourceDirichletSpectralVector (by simp) (by norm_num) (by norm_num) k φ‖ ≤
      8 * Real.exp (R + 1 + (M+1)^2) := by
  unfold sourceDirichletSpectralVector
  have h := (norm_sourceHamiltonianDirection_two_le _).trans
    (mul_le_mul_of_nonneg_left
      (norm_sourceDiscriminantCotangent_le_of_bounds φ _ M R hφ hμ) (by norm_num : (0 : ℝ) ≤ 2))
  simpa only [← mul_assoc,show (2 : ℝ)*4 = 8 by norm_num] using h

/-- The actual speed is uniformly bounded throughout every real indexed
Hilbert integral-curve interval. Source norm conservation and fixed-sheet
compactness supply the bounds; callers supply only the actual ODE. -/
theorem exists_bound_sourceDirichletSpectralVector_on_integralCurve
    (k : ℤ) (γ : ℝ → CoeffPair 2) (a b : ℝ)
    (hreal : ∀ t ∈ Ioo a b, IsRealType (CoeffPair.toMax 2 (γ t)))
    (hγ : ∀ t ∈ Ioo a b, HasDerivAt γ
      (sourceDirichletSpectralVector (by simp) (by norm_num) (by norm_num) k (γ t)) t)
    (u : ℝ) (hu : u ∈ Ioo a b) :
    ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Ioo a b,
      ‖sourceDirichletSpectralVector (by simp) (by norm_num) (by norm_num) k (γ t)‖ ≤ C := by
  obtain ⟨R,_,hR⟩ := exists_bound_dirichletTerminal_on_sourceDirichletSpectral_integralCurve
    (by simp) (by norm_num) (by norm_num) k γ a b hreal hγ u hu
  refine ⟨8 * Real.exp (R + 1 + (‖γ u‖+1)^2),by positivity,?_⟩
  intro t ht
  apply norm_sourceDirichletSpectralVector_le_of_bounds k (γ t) ‖γ u‖ R
  · exact (norm_eq_on_sourceDirichletSpectral_integralCurve k γ a b hreal hγ t u ht hu).le
  · exact (hR t ht).1

/-- The uniform actual speed gives a Lipschitz bound for the original
source curve on its entire interval, including intervals with collapsed
selected gaps or a zero initial source. -/
theorem exists_lipschitzOnWith_sourceDirichletSpectral_integralCurve
    (k : ℤ) (γ : ℝ → CoeffPair 2) (a b : ℝ)
    (hreal : ∀ t ∈ Ioo a b, IsRealType (CoeffPair.toMax 2 (γ t)))
    (hγ : ∀ t ∈ Ioo a b, HasDerivAt γ
      (sourceDirichletSpectralVector (by simp) (by norm_num) (by norm_num) k (γ t)) t)
    (u : ℝ) (hu : u ∈ Ioo a b) :
    ∃ C : ℝ≥0, 0 < C ∧ LipschitzOnWith C γ (Ioo a b) := by
  obtain ⟨C,hC,hbound⟩ := exists_bound_sourceDirichletSpectralVector_on_integralCurve
    k γ a b hreal hγ u hu
  refine ⟨⟨C,hC.le⟩,hC,?_⟩
  apply (convex_Ioo a b).lipschitzOnWith_of_nnnorm_deriv_le
    (fun t ht => (hγ t ht).differentiableAt)
  intro t ht
  change ‖deriv γ t‖ ≤ C
  rw [(hγ t ht).deriv]
  exact hbound t ht

end ZakharovShabat
end NLS
