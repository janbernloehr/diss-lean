import NLS.Fourier.AbelBoundaryCoefficients
import NLS.Fourier.PeriodicHolomorphicCoefficients

noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal
namespace NLS.Fourier

/-- The physical Sobolev coefficient of the actual trace on the horizontal line y. -/
def sobolevHorizontalCoefficient (s : ℝ) (f : ℂ → ℂ) (y : ℝ) (n : ℤ) : ℂ :=
  (((1+|((2*n:ℤ):ℝ)*Real.pi|)^s:ℝ):ℂ)*
    periodOneCoefficient (fun x : ℝ => f ((x:ℂ)+y*I)) n

/-- The actual horizontal Fourier integrals agree with the abstract strip multipliers. -/
theorem sobolevHorizontalCoefficient_eq_abelBoundaryCoefficient
    (s : ℝ) (f : ℂ → ℂ) (hf : Function.Periodic f 1) (y : ℝ)
    (hd : DifferentiableOn ℂ f (uIcc (0:ℝ) 1 ×ℂ uIcc (0:ℝ) y)) :
    sobolevHorizontalCoefficient s f y =
      abelBoundaryCoefficient s y (periodOneCoefficient (fun x : ℝ => f x)) := by
  funext n
  simp only [sobolevHorizontalCoefficient,abelBoundaryCoefficient,
    periodOneCoefficient_horizontal f hf y hd,mul_assoc]

/-- Closed-strip differentiability supplies every rectangle used in Fourier transport. -/
theorem differentiableOn_horizontal_rectangle (a : ℝ) (ha : 0 ≤ a) (f : ℂ → ℂ)
    (hd : DifferentiableOn ℂ f (univ ×ℂ Icc (-a/Real.pi) (a/Real.pi)))
    (y : ℝ) (hy : |y| ≤ a/Real.pi) :
    DifferentiableOn ℂ f (uIcc (0:ℝ) 1 ×ℂ uIcc (0:ℝ) y) := by
  apply hd.mono
  intro z hz
  have hzero : (0:ℝ) ∈ Icc (-a/Real.pi) (a/Real.pi) := by
    constructor
    · exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha) Real.pi_pos.le
    · positivity
  have hy' : y ∈ Icc (-a/Real.pi) (a/Real.pi) := by
    simpa only [mem_Icc,neg_div] using abs_le.mp hy
  exact ⟨mem_univ _,uIcc_subset_Icc hzero hy' hz.2⟩

/-- For a periodic function holomorphic on the corrected closed strip, literal
Abel membership equals Sobolev coefficient membership of both actual boundary traces. -/
theorem memlp_abel_iff_physical_boundary_coefficients (p : ℝ≥0∞)
    (s a : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (f : ℂ → ℂ)
    (hf : Function.Periodic f 1)
    (hd : DifferentiableOn ℂ f (univ ×ℂ Icc (-a/Real.pi) (a/Real.pi))) :
    Memℓp (fun n => (SpectralWeight.abel s a hs ha (2*n):ℂ)*
      periodOneCoefficient (fun x : ℝ => f x) n) p ↔
      Memℓp (sobolevHorizontalCoefficient s f (a/Real.pi)) p ∧
      Memℓp (sobolevHorizontalCoefficient s f (-a/Real.pi)) p := by
  have hu : |a/Real.pi| ≤ a/Real.pi := by rw [abs_of_nonneg (by positivity)]
  have hl : |-a/Real.pi| ≤ a/Real.pi := by rw [neg_div,abs_neg,abs_of_nonneg (by positivity)]
  rw [sobolevHorizontalCoefficient_eq_abelBoundaryCoefficient s f hf _
      (differentiableOn_horizontal_rectangle a ha f hd _ hu),
    sobolevHorizontalCoefficient_eq_abelBoundaryCoefficient s f hf _
      (differentiableOn_horizontal_rectangle a ha f hd _ hl)]
  exact memlp_abel_iff_boundary_coefficients p s a hs ha _

/-- Original Abel coefficients control the actual Sobolev coefficient sequence
on every horizontal line of the corrected closed strip. -/
theorem memlp_sobolevHorizontalCoefficient (p : ℝ≥0∞)
    (s a : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (f : ℂ → ℂ)
    (hf : Function.Periodic f 1)
    (hd : DifferentiableOn ℂ f (univ ×ℂ Icc (-a/Real.pi) (a/Real.pi)))
    (hc : Memℓp (fun n => (SpectralWeight.abel s a hs ha (2*n):ℂ)*
      periodOneCoefficient (fun x : ℝ => f x) n) p)
    (y : ℝ) (hy : |y| ≤ a/Real.pi) : Memℓp (sobolevHorizontalCoefficient s f y) p := by
  rw [sobolevHorizontalCoefficient_eq_abelBoundaryCoefficient s f hf y
    (differentiableOn_horizontal_rectangle a ha f hd y hy)]
  exact memlp_abelBoundaryCoefficient p s a hs ha _ hc y hy

end NLS.Fourier
