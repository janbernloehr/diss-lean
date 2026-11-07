import NLS.ZakharovShabat.SourceQuotientClosedDiscs

/-! Quantitative isolating discs have one pole distance and diameter
bound before ALL signed indices. These retain the original discs. -/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem SourceIsolatingNeighborhoods.uniform_pole_distance
    {hp : p ≠ ⊤} {hp1 : 1 < p} {V : Set (CoeffPair p)} {D : ℤ → Set ℂ} {C : ℝ}
    (hD : SourceIsolatingNeighborhoods hp hp1 V D C)
    (m n : ℤ) (hmn : m ≠ n) (z : ℂ) (hz : z ∈ closure (D m)) (ξ : ℂ) (hξ : ξ ∈ D n) :
    C⁻¹ ≤ ‖ξ-z‖ := by
  have hone : (1:ℝ) ≤ |((m-n:ℤ):ℝ)| := by exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hmn)
  have hC : 0 ≤ C⁻¹ := inv_nonneg.mpr (zero_le_one.trans hD.one_le)
  have hs := hD.closedDisc_separation m n hmn z hz ξ hξ
  rw [dist_eq_norm,norm_sub_rev] at hs
  have hsmall : C⁻¹ ≤ C⁻¹*|((m-n:ℤ):ℝ)| := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hone hC
  exact hsmall.trans hs

theorem SourceIsolatingNeighborhoods.uniform_disc_diameter
    {hp : p ≠ ⊤} {hp1 : 1 < p} {V : Set (CoeffPair p)} {D : ℤ → Set ℂ} {C : ℝ}
    (hD : SourceIsolatingNeighborhoods hp hp1 V D C)
    (m : ℤ) (z w : ℂ) (hz : z ∈ D m) (hw : w ∈ D m) : ‖z-w‖ ≤ 2*C := by
  obtain ⟨a,r,hr,he⟩ := hD.discs (m+1)
  have ha : (a:ℂ) ∈ D (m+1) := by rw [he]; exact mem_ball_self hr
  have hbound (v : ℂ) (hv : v ∈ D m) : dist v (a:ℂ) ≤ C := by
    have hs := (hD.pointwise_distance m (m+1) (by omega) v hv (a:ℂ) ha).2
    simpa only [show m-(m+1) = (-1:ℤ) by ring,Int.cast_neg,Int.cast_one,abs_neg,abs_one,mul_one] using hs
  calc
    ‖z-w‖ = dist z w := (dist_eq_norm z w).symm
    _ ≤ dist z (a:ℂ)+dist (a:ℂ) w := dist_triangle _ _ _
    _ ≤ C+C := add_le_add (hbound z hz) (by rw [dist_comm]; exact hbound w hw)
    _ = 2*C := by ring

end NLS.ZakharovShabat
