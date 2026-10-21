import NLS.Fourier.AbelFourierExtension
import NLS.Fourier.AbelHorizontalCoefficients
import NLS.Fourier.AbelBoundaryNormContinuity

noncomputable section
set_option autoImplicit false
open Set Filter Topology Complex
open scoped ENNReal
namespace NLS.Fourier

/-- Sobolev norm traces mean that the pi-scaled actual Fourier coefficients
extend as a continuous l2-valued curve through both strip boundaries.
Values outside the closed strip only provide a harmless continuous extension. -/
def HasSobolevNormStripTraces (s a : ℝ) (f : ℂ → ℂ) : Prop :=
  ∃ g : ℝ → Coeff 2, Continuous g ∧ ∀ y : ℝ, |y| < a/Real.pi →
    ∀ n : ℤ, g y n = sobolevHorizontalCoefficient s f y n

/-- An interior horizontal rectangle lies entirely in the open analytic strip. -/
theorem differentiableOn_rectangle_of_analytic_strip (a : ℝ)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f {z : ℂ | |z.im| < a/Real.pi})
    (y : ℝ) (hy : |y| < a/Real.pi) :
    DifferentiableOn ℂ f (uIcc (0:ℝ) 1 ×ℂ uIcc (0:ℝ) y) := by
  apply hf.differentiableOn.mono
  intro z hz
  have hi : z.im ∈ Icc (-|y|) |y| :=
    uIcc_subset_Icc ⟨neg_nonpos.mpr (abs_nonneg y),abs_nonneg y⟩
      ⟨neg_abs_le y,le_abs_self y⟩ hz.2
  exact (abs_le.mpr hi).trans_lt hy

/-- For an existing periodic holomorphic function, genuine Sobolev norm traces
force membership of its actual height-zero coefficients in the original Abel space. -/
theorem memlp_abel_of_sobolevNormStripTraces (s a : ℝ) (hs : 0 ≤ s) (ha : 0 < a)
    (f : ℂ → ℂ) (hf : Function.Periodic f 1)
    (han : AnalyticOnNhd ℂ f {z : ℂ | |z.im| < a/Real.pi})
    (htrace : HasSobolevNormStripTraces s a f) :
    Memℓp (fun n => (SpectralWeight.abel s a hs ha.le (2*n):ℂ)*
      periodOneCoefficient (fun x : ℝ => f x) n) 2 := by
  obtain ⟨g,hg,hcoeff⟩ := htrace
  let c := periodOneCoefficient (fun x : ℝ => f x)
  have hh : 0 < a/Real.pi := div_pos ha Real.pi_pos
  have he (n : ℤ) : EqOn (fun y => g y n) (fun y => abelBoundaryCoefficient s y c n)
      (Ioo (-(a/Real.pi)) (a/Real.pi)) := by
    intro y hy
    change g y n = abelBoundaryCoefficient s y c n
    rw [hcoeff y (abs_lt.mpr hy)]
    exact congrFun (sobolevHorizontalCoefficient_eq_abelBoundaryCoefficient s f hf y
      (differentiableOn_rectangle_of_analytic_strip a f han y (abs_lt.mpr hy))) n
  have hclosed (y : ℝ) (hy : y ∈ Icc (-(a/Real.pi)) (a/Real.pi)) (n : ℤ) :
      g y n = abelBoundaryCoefficient s y c n := by
    have h := (he n).closure ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 n).continuous.comp hg)
      (by unfold abelBoundaryCoefficient; fun_prop)
    rw [closure_Ioo (by linarith : -(a/Real.pi) ≠ a/Real.pi)] at h
    exact h hy
  apply (memlp_abel_iff_boundary_coefficients 2 s a hs ha.le c).mpr
  constructor
  · convert lp.memℓp (g (a/Real.pi)) using 1
    funext n
    exact (hclosed _ ⟨by linarith,le_rfl⟩ n).symm
  · convert lp.memℓp (g (-a/Real.pi)) using 1
    funext n
    exact (hclosed _ ⟨by simp only [neg_div]; exact le_rfl,by rw [neg_div]; linarith⟩ n).symm

/-- Every original Abel datum has norm-convergent Sobolev traces on both
boundaries of its constructed holomorphic extension. -/
theorem hasSobolevNormStripTraces_abelFourierExtension (s a : ℝ) (hs : 0 ≤ s) (ha : 0 < a)
    (c : ℤ → ℂ)
    (hc : Memℓp (fun n => (SpectralWeight.abel s a hs ha.le (2*n):ℂ)*c n) 2) :
    HasSobolevNormStripTraces s a (periodOneComplexSynthesis c) := by
  have hh : 0 < a/Real.pi := div_pos ha Real.pi_pos
  let clamp : ℝ → {y : ℝ // |y| ≤ a/Real.pi} := fun y =>
    ⟨min (a/Real.pi) (max (-(a/Real.pi)) y),abs_le.mpr
      ⟨le_min (by linarith) (le_max_left _ _),min_le_left _ _⟩⟩
  have hclamp : Continuous clamp := by unfold clamp; fun_prop
  let g : ℝ → Coeff 2 := fun y => abelHorizontalData s a hs ha.le c hc (clamp y)
  refine ⟨g,(continuous_abelHorizontalData (by simp) s a hs ha.le c hc).comp hclamp,?_⟩
  intro y hy n
  have hy' := abs_lt.mp hy
  have hval : (clamp y).val = y := by
    simp only [clamp,max_eq_right hy'.1.le,min_eq_right hy'.2.le]
  change abelBoundaryCoefficient s (clamp y).val c n = _
  rw [hval,sobolevHorizontalCoefficient,
    periodOneCoefficient_abelFourierExtension s a hs ha.le c hc y hy n]
  simp only [abelBoundaryCoefficient,complexHorizontalCoefficients,mul_assoc]

/-- Exact corrected-width characterization using actual Fourier coefficients,
interior holomorphicity, and l2 Sobolev norm traces at both boundaries. -/
theorem memlp_abel_iff_exists_sobolev_strip (s a : ℝ) (hs : 0 ≤ s) (ha : 0 < a)
    (c : ℤ → ℂ) :
    Memℓp (fun n => (SpectralWeight.abel s a hs ha.le (2*n):ℂ)*c n) 2 ↔
      ∃ f : ℂ → ℂ, Function.Periodic f 1 ∧
        AnalyticOnNhd ℂ f {z : ℂ | |z.im| < a/Real.pi} ∧
        (∀ n : ℤ, periodOneCoefficient (fun x : ℝ => f x) n = c n) ∧
        HasSobolevNormStripTraces s a f := by
  constructor
  · intro hc
    exact ⟨periodOneComplexSynthesis c,periodOneComplexSynthesis_periodic c,
      analyticOnNhd_abelFourierExtension s a hs ha.le c hc,
      periodOneCoefficient_abelFourierExtension_zero s a hs ha c hc,
      hasSobolevNormStripTraces_abelFourierExtension s a hs ha c hc⟩
  · rintro ⟨f,hf,han,hc,htrace⟩
    simpa only [hc] using memlp_abel_of_sobolevNormStripTraces s a hs ha f hf han htrace

end NLS.Fourier
