import NLS.ZakharovShabat.L2Discriminant
import NLS.ZakharovShabat.SourceCanonicalRootRealBand

/-! # The literal product and root sign in the Section 7 overview

Equation (2.1) is a locally uniform limit on the whole spectral plane of
the displayed symmetric products of the actual Hilbert endpoints. Its
limit is the physical monodromy trace squared minus four. The real-band
normalization gives the positive real value of i times the canonical root.
-/

noncomputable section
set_option autoImplicit false
open Set Filter Topology Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The displayed endpoint product converges locally uniformly to the physical trace expression. -/
theorem sourceSection7_periodic_product (φ : CoeffPair 2) :
    TendstoLocallyUniformlyOn (fun N : ℕ => fun z : ℂ =>
      -4 * ∏ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        ((canonicalPeriodicRight (by simp) (by norm_num) (periodOnePotential φ)
          (periodOnePotential_mem φ) n-z) *
         (canonicalPeriodicLeft (by simp) (by norm_num) (periodOnePotential φ)
          (periodOnePotential_mem φ) n-z)) / (singleSpectralDenominator n)^2)
      (fun z => (l2Discriminant (sourcePhysicalL2 φ) z)^2-4) atTop univ := by
  let ξ := canonicalPeriodicLeft (by simp) (by norm_num) (periodOnePotential φ)
    (periodOnePotential_mem φ)
  let η := canonicalPeriodicRight (by simp) (by norm_num) (periodOnePotential φ)
    (periodOnePotential_mem φ)
  have hlabels := canonicalPeriodicEndpoints_spec (by simp) (by norm_num)
    (periodOnePotential φ) (periodOnePotential_mem φ)
  have ht := tendstoLocallyUniformlyOn_entireSpectralPairProduct (by simp) ξ η
    hlabels.1.left_displacement hlabels.1.right_displacement
  have he : entireSpectralPairProduct ξ η =
      fun z => (l2Discriminant (sourcePhysicalL2 φ) z)^2-4 := by
    rw [canonicalPeriodicEndpoints_product]
    funext z
    exact canonicalPeriodicProduct_eq_l2Discriminant (periodOnePotential φ)
      (periodOnePotential_mem φ) z
  rw [he] at ht
  convert ht using 1
  funext N z
  unfold spectralPairPartialProduct
  congr 1
  apply Finset.prod_congr rfl
  intro n _
  have hd : (singleSpectralDenominator n)^2 = spectralPairDenominator n := by
    by_cases hn : n = 0 <;> simp [singleSpectralDenominator,spectralPairDenominator,hn]
  rw [spectralPairFactor_eq_div,hd]
  exact congrArg (fun x : ℂ => x/spectralPairDenominator n) (mul_comm _ _)

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The printed sign convention: i times the root is positive between gaps zero and one. -/
theorem sourceSection7_canonical_root_sign (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) (x : ℝ)
    (hx : x ∈ Ioo
      (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) 0).re
      (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) 1).re) :
    (I*sourceCanonicalRoot hp hp1 φ (x : ℂ)).im = 0 ∧
      0 < (I*sourceCanonicalRoot hp hp1 φ (x : ℂ)).re := by
  have h := sourceCanonicalRoot_realBand_sign hp hp1 φ hφ 0 x hx
  simpa only [Int.natAbs_zero,pow_zero,one_mul,Complex.mul_im,Complex.mul_re,
    Complex.I_re,Complex.I_im,zero_mul,one_mul,zero_add,zero_sub,neg_pos] using h

end NLS.ZakharovShabat
