import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

/-!
# Discs with real diameters

Discs whose diameters have real endpoints isolate prefixes and suffixes
of a real root set. Their boundaries meet the real axis only at endpoints.
-/

open Set Complex Metric
namespace NLS.ComplexAnalysis

/-- A point of a disc with real diameter has real part between its endpoints. -/
theorem re_mem_Icc_of_mem_realDiameterDisc (a b : ℝ) (z : ℂ)
    (hz : z ∈ closedBall (((a+b)/2 : ℝ) : ℂ) ((b-a)/2)) : a ≤ z.re ∧ z.re ≤ b := by
  have hd : ‖z-(((a+b)/2 : ℝ) : ℂ)‖ ≤ (b-a)/2 := by simpa only [mem_closedBall, dist_eq_norm] using hz
  have hr := (Complex.abs_re_le_norm _).trans hd
  simp only [sub_re, ofReal_re] at hr
  obtain ⟨hl,hu⟩ := abs_le.mp hr
  constructor <;> linarith

/-- On the real axis, membership is exactly membership of the diameter interval. -/
theorem mem_realDiameterDisc_iff (a b : ℝ) (z : ℂ) (hz : z.im = 0) :
    z ∈ closedBall (((a+b)/2 : ℝ) : ℂ) ((b-a)/2) ↔ a ≤ z.re ∧ z.re ≤ b := by
  constructor
  · exact re_mem_Icc_of_mem_realDiameterDisc a b z
  · intro h
    have he : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hz]
    rw [he, mem_closedBall, dist_eq_norm, ← ofReal_sub, norm_real, Real.norm_eq_abs]
    apply abs_le.mpr
    constructor <;> linarith

/-- A real point on the boundary is one of the two endpoints. -/
theorem re_eq_endpoints_of_mem_realDiameterSphere (a b : ℝ) (z : ℂ) (hz : z.im = 0)
    (hs : z ∈ sphere (((a+b)/2 : ℝ) : ℂ) ((b-a)/2)) : z.re = a ∨ z.re = b := by
  have he : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hz]
  rw [he, mem_sphere, dist_eq_norm, ← ofReal_sub, norm_real, Real.norm_eq_abs] at hs
  rcases le_total 0 (z.re-(a+b)/2) with h | h
  · rw [abs_of_nonneg h] at hs
    exact Or.inr (by linarith)
  · rw [abs_of_nonpos h] at hs
    exact Or.inl (by linarith)

/-- A diameter inside a centered real interval gives a disc inside the centered disc. -/
theorem realDiameterDisc_subset_closedBall (a b R : ℝ) (ha : -R ≤ a) (hb : b ≤ R) :
    closedBall (((a+b)/2 : ℝ) : ℂ) ((b-a)/2) ⊆ closedBall (0 : ℂ) R := by
  apply closedBall_subset_closedBall'
  simp only [dist_zero_right, norm_real, Real.norm_eq_abs]
  rcases le_total 0 ((a+b)/2) with h | h
  · rw [abs_of_nonneg h]
    linarith
  · rw [abs_of_nonpos h]
    linarith

end NLS.ComplexAnalysis
