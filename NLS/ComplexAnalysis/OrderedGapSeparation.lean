import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! # Uniform separation and normalization of exterior gap kernels

The two neighboring intervals give a positive lower bound on the distance
from any fixed gap to all other gaps. This bounds the square-root factor
and normalized poles, and preserves the exact scale of the original kernel.
-/

noncomputable section
open Set
namespace NLS.ComplexAnalysis


/-- An ordered indexed family of closed gaps has a uniform positive distance from any fixed gap. -/
theorem ordered_gaps_uniform_exterior_separation (L R : ℤ → ℝ)
    (hab : ∀ n, L n ≤ R n) (hsep : ∀ i j, i < j → R i < L j) (n : ℤ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ m : ℤ, m ≠ n → ∀ x ∈ Icc (L m) (R m),
      δ ≤ |x-L n| ∧ δ ≤ |x-R n| ∧
        (R n-L n)/2+δ ≤ |x-(L n+R n)/2| := by
  have hL : Monotone L := by
    intro i j hij
    rcases eq_or_lt_of_le hij with rfl | hij
    · exact le_rfl
    · exact (hab i).trans (hsep i j hij).le
  have hR : Monotone R := by
    intro i j hij
    rcases eq_or_lt_of_le hij with rfl | hij
    · exact le_rfl
    · exact (hsep i j hij).le.trans (hab j)
  let δ := min (L n-R (n-1)) (L (n+1)-R n)
  have hd : 0 < δ := lt_min (sub_pos.mpr (hsep (n-1) n (by omega)))
    (sub_pos.mpr (hsep n (n+1) (by omega)))
  refine ⟨δ,hd,?_⟩
  intro m hm x hx
  rcases lt_or_gt_of_ne hm with hmn | hnm
  · have hxm : x ≤ R (n-1) := hx.2.trans (hR (by omega))
    have hδ : δ ≤ L n-R (n-1) := min_le_left _ _
    have ha : x-L n ≤ 0 := by linarith
    have hb : x-R n ≤ 0 := by linarith [hab n]
    have hc : x-(L n+R n)/2 ≤ 0 := by linarith [hab n]
    rw [abs_of_nonpos ha,abs_of_nonpos hb,abs_of_nonpos hc]
    exact ⟨by linarith,by linarith [hab n],by linarith⟩
  · have hxm : L (n+1) ≤ x := (hL (by omega)).trans hx.1
    have hδ : δ ≤ L (n+1)-R n := min_le_right _ _
    have ha : 0 ≤ x-L n := by linarith [hab n]
    have hb : 0 ≤ x-R n := by linarith
    have hc : 0 ≤ x-(L n+R n)/2 := by linarith [hab n]
    rw [abs_of_nonneg ha,abs_of_nonneg hb,abs_of_nonneg hc]
    exact ⟨by linarith [hab n],by linarith,by linarith⟩

/-- The exterior square root is bounded away from zero by the same separation. -/
theorem separated_gap_sqrt_lower_bound (a b x δ : ℝ) (hd : 0 ≤ δ)
    (ha : δ ≤ |x-a|) (hb : δ ≤ |x-b|) :
    δ ≤ Real.sqrt |(x-a)*(x-b)| := by
  have hprod : δ^2 ≤ |(x-a)*(x-b)| := by
    rw [abs_mul,pow_two]
    exact mul_le_mul ha hb hd (abs_nonneg _)
  calc
    δ = Real.sqrt (δ^2) := (Real.sqrt_sq hd).symm
    _ ≤ Real.sqrt |(x-a)*(x-b)| := Real.sqrt_le_sqrt hprod

/-- A separated exterior point has a normalized pole strictly beyond the unit interval. -/
theorem separated_gap_normalized_pole (r c x δ : ℝ) (hr : 0 < r) (hd : 0 < δ)
    (hx : r+δ ≤ |x-c|) : 1+δ/r ≤ |(x-c)/r| ∧ 1 < |(x-c)/r| := by
  rw [abs_div,abs_of_pos hr]
  have h : 1+δ/r ≤ |x-c|/r := by
    apply (le_div_iff₀ hr).mpr
    have he : (1+δ/r)*r = r+δ := by field_simp
    rw [he]
    exact hx
  exact ⟨h,lt_of_lt_of_le (by linarith [div_pos hd hr]) h⟩

/-- Uniform separation controls the majorant for the normalized exterior kernel. -/
theorem exterior_gap_kernel_majorant (d r v s δ : ℝ) (hd : 0 ≤ d) (hr : 0 < r)
    (hδ : 0 < δ) (hv : δ ≤ v) (hs : 1+δ/r ≤ |s|) :
    d/(r*v)/(|s|-1) ≤ d/δ^2 := by
  have he : r*(δ/r) = δ := by field_simp
  have hm := mul_le_mul_of_nonneg_left hs hr.le
  rw [mul_add,mul_one,he] at hm
  have hs0 : 0 < |s|-1 := by linarith [div_pos hδ hr]
  have hden : δ^2 ≤ r*v*(|s|-1) := by
    have hmul := mul_le_mul_of_nonneg_right (show δ ≤ r*(|s|-1) by nlinarith)
      (hδ.le.trans hv)
    nlinarith [mul_nonneg hδ.le (sub_nonneg.mpr hv)]
  rw [div_div]
  exact div_le_div_of_nonneg_left hd (sq_pos_of_pos hδ) hden



/-- Normalizing the exterior pole preserves the original real-gap kernel, including its scale. -/
theorem normalized_exterior_kernel_eq (d r v t c x : ℝ) (hr : 0 < r) :
    (d/(r*v))/|(t-c)/r-x| = d/(v*|t-(c+r*x)|) := by
  have h : (t-c)/r-x = (t-(c+r*x))/r := by
    field_simp
    ring
  rw [h,abs_div,abs_of_pos hr]
  simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
  calc
    d * (v⁻¹ * r⁻¹) * (r * |t - (c + r * x)|⁻¹) =
        (r⁻¹*r) * (d * (v⁻¹ * |t - (c + r * x)|⁻¹)) := by ring
    _ = d * (|t - (c + r * x)|⁻¹ * v⁻¹) := by rw [inv_mul_cancel₀ (ne_of_gt hr)]; ring


end NLS.ComplexAnalysis
