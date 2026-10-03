import NLS.ZakharovShabat.SourceDiscriminantCoefficientContinuity
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-! # Spectral derivative convergence under Hilbert coefficient limits

Locally uniform convergence of the actual entire discriminants implies
locally uniform convergence of their spectral derivatives by the Cauchy
integral formula. The source potentials need only be bounded and converge
coefficientwise; their norms need not converge.
-/

noncomputable section
open Set Filter Topology Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
local instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

/-- The actual spectral derivatives converge locally uniformly on the
whole complex plane under bounded Hilbert coefficient convergence. -/
theorem tendstoLocallyUniformly_sourceDiscriminant_deriv_of_bounded_coefficientwise
    {α : Type*} {l : Filter α} (a : α → CoeffPair 2) (b : CoeffPair 2)
    (hb : Bornology.IsBounded (range a))
    (ht₁ : ∀ n : ℤ, Tendsto (fun k => (a k).fst n) l (𝓝 (b.fst n)))
    (ht₂ : ∀ n : ℤ, Tendsto (fun k => (a k).snd n) l (𝓝 (b.snd n))) :
    TendstoLocallyUniformly (fun k => deriv (canonicalDiscriminant (by simp) (periodOnePotential (a k))))
      (deriv (canonicalDiscriminant (by simp) (periodOnePotential b))) l := by
  apply tendstoLocallyUniformlyOn_univ.mp
  exact (tendstoLocallyUniformly_sourceDiscriminant_of_bounded_coefficientwise
    a b hb ht₁ ht₂).tendstoLocallyUniformlyOn.deriv
    (Eventually.of_forall fun k => (analyticOnNhd_canonicalDiscriminant (by simp) (by norm_num)
      (periodOnePotential (a k)) (periodOnePotential_mem (a k))).differentiableOn) isOpen_univ

/-- A single eventual estimate controls the derivative on every bounded
spectral set, including any of the common action circles. -/
theorem tendstoUniformlyOn_sourceDiscriminant_deriv_of_bounded_coefficientwise
    {α : Type*} {l : Filter α} (a : α → CoeffPair 2) (b : CoeffPair 2)
    (hb : Bornology.IsBounded (range a))
    (ht₁ : ∀ n : ℤ, Tendsto (fun k => (a k).fst n) l (𝓝 (b.fst n)))
    (ht₂ : ∀ n : ℤ, Tendsto (fun k => (a k).snd n) l (𝓝 (b.snd n)))
    (K : Set ℂ) (hK : Bornology.IsBounded K) :
    TendstoUniformlyOn (fun k => deriv (canonicalDiscriminant (by simp) (periodOnePotential (a k))))
      (deriv (canonicalDiscriminant (by simp) (periodOnePotential b))) l K :=
  (tendstoLocallyUniformly_iff_forall_isCompact.mp
    (tendstoLocallyUniformly_sourceDiscriminant_deriv_of_bounded_coefficientwise a b hb ht₁ ht₂)
    (closure K) hK.isCompact_closure).mono subset_closure

/-- Pointwise derivative convergence is an immediate specialization. -/
theorem tendsto_sourceDiscriminant_deriv_of_bounded_coefficientwise
    {α : Type*} {l : Filter α} (a : α → CoeffPair 2) (b : CoeffPair 2)
    (hb : Bornology.IsBounded (range a))
    (ht₁ : ∀ n : ℤ, Tendsto (fun k => (a k).fst n) l (𝓝 (b.fst n)))
    (ht₂ : ∀ n : ℤ, Tendsto (fun k => (a k).snd n) l (𝓝 (b.snd n))) (z : ℂ) :
    Tendsto (fun k => deriv (canonicalDiscriminant (by simp) (periodOnePotential (a k))) z) l
      (𝓝 (deriv (canonicalDiscriminant (by simp) (periodOnePotential b)) z)) :=
  (tendstoLocallyUniformly_sourceDiscriminant_deriv_of_bounded_coefficientwise
    a b hb ht₁ ht₂).tendstoLocallyUniformlyOn.tendsto_at (mem_univ z)

end NLS.ZakharovShabat
