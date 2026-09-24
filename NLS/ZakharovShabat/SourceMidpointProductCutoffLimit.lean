import NLS.ZakharovShabat.SourceMidpointProductFullDiscSup
import NLS.ZakharovShabat.SourceSingleRootMidpointBounds

/-!
# Literal midpoint cutoffs converge to the source midpoint product

On an isolating disc, separation makes the off-diagonal midpoint
perturbations absolutely summable. The symmetric finite midpoint
quotients therefore converge to the unconditional product used in the
disc-supremum estimate.
-/

noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- The off-diagonal midpoint perturbation at one source-disc point
has an absolutely summable row. -/
theorem summable_norm_sourceMidpointProductTerm
    (hq : q ≠ ⊤)
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ ψ : CoeffPair p)
    (N : ℕ) (ε C : ℝ) (hC : 1 ≤ C)
    (hsep : ∀ i j : ℤ, i ≠ j →
      ∀ w ∈ sourceIsolatingDisc hp hp1 φ N ε i,
        |((i-j : ℤ) : ℝ)| ≤ C *
          ‖canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
            (periodOnePotential_mem ψ) j-w‖)
    (α : Coeff q) (n : ℤ) (z : ℂ)
    (hz : z ∈ sourceIsolatingDisc hp hp1 φ N ε n) :
    Summable (fun m : ℤ => ‖if m = n then (0 : ℂ) else
      α m / (canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) m-z)‖) := by
  let τ : ℤ → ℂ := fun m => canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) m
  have hbound (m : ℤ) :
      ‖if m = n then (0 : ℂ) else α m/(τ m-z)‖ ≤
        C*(‖α m‖*‖Fourier.hilbertKernel (n-m)‖) := by
    by_cases hm : m = n
    · subst m
      simp [Fourier.hilbertKernel]
    have hk : ‖Fourier.hilbertKernel (n-m)‖ =
        |((m-n : ℤ) : ℝ)|⁻¹ := by
      simp only [Fourier.hilbertKernel, norm_neg, norm_inv, Complex.norm_intCast]
      rw [show n-m = -(m-n) by ring, Int.cast_neg, abs_neg]
    have h := norm_midpoint_displacement_div_le C hC n m (Ne.symm hm)
      (α m) (τ m) z (hsep n m (Ne.symm hm) z hz)
    simpa only [if_neg hm, hk, div_eq_mul_inv] using h
  exact ((Fourier.summable_absoluteSampledRow hq α n).mul_left C).of_nonneg_of_le
    (fun _ => norm_nonneg _) hbound

/-- The literal symmetric midpoint quotient converges to the
unconditional midpoint product on every separated source disc. -/
theorem tendsto_sourceSingleRootMidpointPartialProduct
    (hq : q ≠ ⊤)
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ ψ : CoeffPair p)
    (N : ℕ) (ε C : ℝ) (hC : 1 ≤ C)
    (hsep : ∀ i j : ℤ, i ≠ j →
      ∀ w ∈ sourceIsolatingDisc hp hp1 φ N ε i,
        |((i-j : ℤ) : ℝ)| ≤ C *
          ‖canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
            (periodOnePotential_mem ψ) j-w‖)
    (a : Coeff p) (α : Coeff q)
    (hα : ∀ m : ℤ,
      displacedRoots a m -
        canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
          (periodOnePotential_mem ψ) m = α m)
    (n : ℤ) (z : ℂ)
    (hz : z ∈ sourceIsolatingDisc hp hp1 φ N ε n) :
    Tendsto (fun M : ℕ =>
      sourceSingleRootMidpointPartialProduct hp hp1 n M (z,(a,ψ))) atTop
      (𝓝 (sourceMidpointProductRow hp hp1 ψ α n z+1)) := by
  let τ : ℤ → ℂ := fun m => canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) m
  let u (m : ℤ) : ℂ := if m = n then 0 else α m/(τ m-z)
  have hu : Summable (fun m => ‖u m‖) :=
    summable_norm_sourceMidpointProductTerm hq hp hp1 φ ψ N ε C hC
      hsep α n z hz
  have hden (m : ℤ) (hm : m ≠ n) : τ m ≠ z := by
    intro he
    have hd : 0 < |((n-m : ℤ) : ℝ)| := by
      apply abs_pos.mpr
      exact_mod_cast sub_ne_zero.mpr (Ne.symm hm)
    have hs := hsep n m (Ne.symm hm) z hz
    rw [← he, sub_self, norm_zero, mul_zero] at hs
    linarith
  have hprod (M : ℕ) :
      sourceSingleRootMidpointPartialProduct hp hp1 n M (z,(a,ψ)) =
        ∏ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), (1+u m) := by
    let s : Finset ℤ := Finset.Icc (-(M : ℤ)) (M : ℤ)
    calc
      sourceSingleRootMidpointPartialProduct hp hp1 n M (z,(a,ψ)) =
          ∏ m ∈ s.erase n, (1+u m) := by
        unfold sourceSingleRootMidpointPartialProduct
        apply Finset.prod_congr rfl
        intro m hm
        have hmn : m ≠ n := Finset.ne_of_mem_erase hm
        rw [midpoint_quotient_eq_one_add (displacedRoots a m) (τ m) z (hden m hmn)]
        simp only [hα m, u, if_neg hmn, τ]
      _ = ∏ m ∈ s, (1+u m) := Finset.prod_erase _ (by simp [u])
  have ht : Tendsto (fun M : ℕ =>
      ∏ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), (1+u m)) atTop
      (𝓝 (∏' m : ℤ, (1+u m))) :=
    (multipliable_one_add_of_summable hu).hasProd.comp Finset.tendsto_Icc_neg
  have htarget : sourceMidpointProductRow hp hp1 ψ α n z+1 =
      ∏' m : ℤ, (1+u m) := by
    unfold sourceMidpointProductRow u τ
    ring
  rw [htarget]
  exact ht.congr' (Filter.Eventually.of_forall fun M => (hprod M).symm)

end NLS.ZakharovShabat
