import NLS.Fourier.AbelBoundaryCoefficients
import NLS.SequenceSpaces.DominatedConvergence

noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal
namespace NLS.Fourier

/-- The full Sobolev coefficient sequence on any height of the corrected closed strip. -/
def abelHorizontalData {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (s a : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (c : ℤ → ℂ)
    (hc : Memℓp (fun n => (SpectralWeight.abel s a hs ha (2*n):ℂ)*c n) p)
    (y : {y : ℝ // |y| ≤ a/Real.pi}) : Coeff p :=
  ⟨abelBoundaryCoefficient s y c,memlp_abelBoundaryCoefficient p s a hs ha c hc y y.property⟩

@[simp] theorem abelHorizontalData_apply {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (s a : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (c : ℤ → ℂ)
    (hc : Memℓp (fun n => (SpectralWeight.abel s a hs ha (2*n):ℂ)*c n) p)
    (y : {y : ℝ // |y| ≤ a/Real.pi}) (n : ℤ) :
    abelHorizontalData s a hs ha c hc y n = abelBoundaryCoefficient s y c n := rfl

/-- Finite-exponent Sobolev coefficient norms have genuine limits at both
corrected boundaries, by domination with the original Abel sequence. -/
theorem continuous_abelHorizontalData {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (s a : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (c : ℤ → ℂ)
    (hc : Memℓp (fun n => (SpectralWeight.abel s a hs ha (2*n):ℂ)*c n) p) :
    Continuous (abelHorizontalData s a hs ha c hc) := by
  let A := abelHorizontalData s a hs ha c hc
  let b : Coeff p := ⟨fun n => (SpectralWeight.abel s a hs ha (2*n):ℂ)*c n,hc⟩
  have hb (y : {y : ℝ // |y| ≤ a/Real.pi}) (n : ℤ) : ‖A y n‖ ≤ ‖b n‖ :=
    norm_abelBoundaryCoefficient_le s a hs ha y y.property c n
  have hcont (n : ℤ) : Continuous (fun y : {y : ℝ // |y| ≤ a/Real.pi} => A y n) := by
    change Continuous (fun y : {y : ℝ // |y| ≤ a/Real.pi} => abelBoundaryCoefficient s y c n)
    unfold abelBoundaryCoefficient
    fun_prop
  apply continuous_iff_continuousAt.mpr
  intro y₀
  have hz := Coeff.tendsto_zero_of_dominated hp (fun y => A y-A y₀) ((2:ℂ) • b)
    (l := 𝓝 y₀) (Eventually.of_forall fun y n => by
      change ‖A y n-A y₀ n‖ ≤ ‖(2:ℂ)*b n‖
      calc
        _ ≤ ‖A y n‖+‖A y₀ n‖ := norm_sub_le _ _
        _ ≤ ‖b n‖+‖b n‖ := add_le_add (hb y n) (hb y₀ n)
        _ = _ := by simp only [norm_mul,Complex.norm_ofNat]; ring)
    (fun n => by
      change Tendsto (fun y => A y n-A y₀ n) (𝓝 y₀) (𝓝 0)
      simpa only [sub_self] using ((hcont n).tendsto y₀).sub_const (A y₀ n))
  exact tendsto_sub_nhds_zero_iff.mp hz

end NLS.Fourier
