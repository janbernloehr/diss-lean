import NLS.ZakharovShabat.SourceStandardRootAlgebra
import NLS.ComplexAnalysis.SqrtSlitPreimage

/-!
# Principal-root branch cut and periodic gap segments

The normalized quadratic radicand avoids the principal square-root cut
outside the closed segment joining its two endpoints. The result applies
in particular to the canonical source periodic gap in equation (2.9).
-/

noncomputable section
open Set Complex
namespace NLS.ComplexAnalysis

private theorem inv_abs_le_one {x : ℝ} (h : 1 ≤ |x|) : |x⁻¹| ≤ 1 := by
  rw [abs_inv]
  exact inv_le_one_of_one_le₀ h

/-- If the normalized endpoint ratio is real with modulus at least one,
the spectral parameter lies on the closed endpoint segment. -/
theorem segment_of_centered_ratio_real_large
    (a b z : ℂ) (hz : z ≠ (a+b)/2)
    (hreal : (((b-a)/2)/(((a+b)/2)-z)).im = 0)
    (hlarge : 1 ≤ |(((b-a)/2)/(((a+b)/2)-z)).re|) :
    z ∈ segment ℝ a b := by
  let t : ℂ := (a+b)/2
  let d : ℂ := (b-a)/2
  let w : ℂ := d/(t-z)
  let x : ℝ := w.re
  have hw : w = (x : ℂ) := by
    apply Complex.ext
    · simp [x]
    · simpa [x, w, d, t] using hreal
  have hxabs : 1 ≤ |x| := hlarge
  have hx0 : x ≠ 0 := by
    intro he
    have hbad : (1:ℝ) ≤ 0 := by simpa [he] using hxabs
    linarith
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx0
  have htz : t-z ≠ 0 := sub_ne_zero.mpr (by simpa [t] using hz.symm)
  have hwd : (x : ℂ)*(t-z) = d := by
    calc
      (x : ℂ)*(t-z) = (d/(t-z))*(t-z) := by rw [← hw]
      _ = d := div_mul_cancel₀ d htz
  have htzd : t-z = d/(x:ℂ) := (eq_div_iff hxC).2 (by
    calc
      (t-z)*(x:ℂ) = (x:ℂ)*(t-z) := mul_comm _ _
      _ = d := hwd)
  have hzd : z = t-d/(x:ℂ) := by
    calc
      z = t-(t-z) := by ring
      _ = t-d/(x:ℂ) := by rw [htzd]
  have hrange := inv_abs_le_one hxabs
  let s : ℝ := (1-x⁻¹)/2
  have hs : s ∈ Set.Icc (0 : ℝ) 1 := by
    rcases abs_le.mp hrange with ⟨hlo,hhi⟩
    change 0 ≤ s ∧ s ≤ 1
    dsimp [s]
    constructor <;> linarith
  have hline : AffineMap.lineMap a b s = z := by
    rw [AffineMap.lineMap_apply_module']
    rw [Complex.real_smul]
    rw [hzd]
    dsimp [s, t, d]
    push_cast
    field_simp [hxC]
    ring
  rw [← hline]
  exact lineMap_mem_segment (𝕜 := ℝ) a b hs

private theorem complex_midpoint_mem_segment (a b : ℂ) :
    (a+b)/2 ∈ segment ℝ a b := by
  have hs : (1/2 : ℝ) ∈ Set.Icc (0:ℝ) 1 := by norm_num
  have h := lineMap_mem_segment (𝕜 := ℝ) a b hs
  convert h using 1
  rw [AffineMap.lineMap_apply_module', Complex.real_smul]
  norm_num
  ring

/-- The normalized quadratic radicand is in the principal slit plane
throughout the complement of the endpoint segment. -/
theorem normalized_radicand_mem_slitPlane
    (a b z : ℂ) (hz : z ∉ segment ℝ a b) :
    1 - (((b-a)/2)/(((a+b)/2)-z))^2 ∈ Complex.slitPlane := by
  have hmid : z ≠ (a+b)/2 := by
    intro he
    exact hz (he ▸ complex_midpoint_mem_segment a b)
  by_contra hcut
  obtain ⟨hreal, hlarge⟩ :=
    NLS.ComplexAnalysis.real_abs_ge_one_of_one_sub_sq_not_mem_slitPlane
      (((b-a)/2)/(((a+b)/2)-z)) hcut
  exact hz (segment_of_centered_ratio_real_large a b z hmid hreal hlarge)

private theorem radicand_eq (a b z : ℂ) :
    1-(b-a)^2/(4*(((a+b)/2)-z)^2) =
      1-(((b-a)/2)/(((a+b)/2)-z))^2 := by
  simp only [div_eq_mul_inv, mul_inv_rev, mul_pow, inv_pow]
  norm_num
  ring

/-- The gap-squared form of the radicand also avoids the branch cut. -/
theorem gap_radicand_mem_slitPlane
    (a b z : ℂ) (hz : z ∉ segment ℝ a b) :
    1-(b-a)^2/(4*(((a+b)/2)-z)^2) ∈ Complex.slitPlane := by
  rw [radicand_eq]
  exact normalized_radicand_mem_slitPlane a b z hz

end NLS.ComplexAnalysis

open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Equation (2.9)'s canonical source radicand avoids the principal
square-root cut off the periodic gap segment. -/
theorem sourceStandardRoot_radicand_mem_slitPlane
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ) (z : ℂ)
    (hz : z ∉ sourcePeriodicSegment hp hp1 ψ n) :
    1 - (canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n)^2 /
      (4*(canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n-z)^2) ∈ Complex.slitPlane := by
  unfold canonicalPeriodicGap canonicalPeriodicMidpoint
  exact NLS.ComplexAnalysis.gap_radicand_mem_slitPlane _ _ _ hz

end NLS.ZakharovShabat
