import NLS.ZakharovShabat.BoundaryCharacteristicDiscLp

open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

example {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp1 : 1 < p) (hp : p ≠ ⊤)
    (a : Coeff p) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ (n : ℤ) (z : ℂ),
      ‖z-(Real.pi : ℂ)*n‖ ≤ Real.pi/2 → ‖freeSineQuotient n z‖ ≤ C)
    (n : ℤ) (z : ℂ) (hz : ‖z-(Real.pi : ℂ)*n‖ ≤ Real.pi/2) :
    ‖displacedBoundaryProduct a z-sin z‖ ≤
      ‖restoredSineProductMajorant hp1 hp C a n‖ :=
  norm_displacedBoundaryProduct_sub_sin_le hp1 hp a hC hbound n z hz

example {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp1 : 1 < p) (hp : p ≠ ⊤)
    (a : Coeff p) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ (n : ℤ) (z : ℂ),
      ‖z-(Real.pi : ℂ)*n‖ ≤ Real.pi/2 → ‖freeSineQuotient n z‖ ≤ C)
    (n : ℤ) (z : ℂ) (hz : ‖z-(Real.pi : ℂ)*n‖ ≤ Real.pi/4) :
    ‖deriv (displacedBoundaryProduct a) z-cos z‖ ≤
      (4/Real.pi)*‖restoredSineProductMajorant hp1 hp C a n‖ :=
  norm_deriv_displacedBoundaryProduct_sub_cos_le hp1 hp a hC hbound n z hz

example {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp1 : 1 < p) (hp : p ≠ ⊤)
    {R : ℝ} (hR : 0 ≤ R) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ a : Coeff p, ‖a‖ ≤ R →
      ∃ A : Coeff p, ‖A‖ ≤ K ∧
        (∀ (n : ℤ) (z : ℂ), ‖z-(Real.pi : ℂ)*n‖ ≤ Real.pi/2 →
          ‖displacedBoundaryProduct a z-sin z‖ ≤ ‖A n‖) ∧
        (∀ (n : ℤ) (z : ℂ), ‖z-(Real.pi : ℂ)*n‖ ≤ Real.pi/4 →
          ‖deriv (displacedBoundaryProduct a) z-cos z‖ ≤ (4/Real.pi)*‖A n‖) :=
  exists_uniform_displacedBoundaryProduct_majorants hp1 hp hR

example {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp1 : 1 < p) (hp : p ≠ ⊤)
    (a : Coeff p) (z : ℤ → ℂ)
    (hz : ∀ n : ℤ, ‖z n-(Real.pi : ℂ)*n‖ ≤ Real.pi/4) :
    Memℓp (fun n => displacedBoundaryProduct a (z n)-sin (z n)) p ∧
      Memℓp (fun n => deriv (displacedBoundaryProduct a) (z n)-cos (z n)) p :=
  memℓp_displacedBoundaryProduct_errors hp1 hp a z hz

end NLS.ZakharovShabat
