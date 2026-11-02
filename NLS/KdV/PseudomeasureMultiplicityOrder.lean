import NLS.KdV.PseudomeasureTaylorKernel
import NLS.KdV.PseudomeasureZeroCount

/-!
# Actual physical algebraic multiplicity equals determinant zero order

Every finite physical chain space is equivalent to the actual effective
matrix Taylor kernel. Passing to eventual dimensions proves the equality
for the full original singular Hill operator. The source's two analytic
zeros therefore count exactly two actual physical algebraic multiplicities.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal Matrix.Norms.Elementwise Classical
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue NLS.ComplexAnalysis

/-- The full corrected spectral strip is convex, including its boundary. -/
theorem convex_reducedHillStrip (n : ℕ) : Convex ℝ (reducedHillStrip n) := by
  have he : reducedHillStrip n = Complex.reCLM ⁻¹'
      Icc (freeHillValue n-6*(n:ℝ)) (freeHillValue n+6*(n:ℝ)) := by
    ext z
    change |z.re-freeHillValue n| ≤ 6*(n:ℝ) ↔ _
    rw [abs_le]
    change _ ↔ freeHillValue n-6*(n:ℝ) ≤ z.re ∧ z.re ≤ freeHillValue n+6*(n:ℝ)
    constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith
  rw [he]
  exact (convex_Icc _ _).linear_preimage Complex.reCLM.toLinearMap

variable (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2) (n : ℕ) (hn : 1 ≤ n)
variable (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
variable (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2)

include hn hs in
/-- The actual reduced determinant has finite analytic order everywhere on
the whole corrected strip, using a proved physical resolvent point. -/
theorem endpointReducedDeterminant_order_ne_top (z : ℂ) (hz : z ∈ reducedHillStrip n) :
    analyticOrderAt (fun y => endpointReducedDeterminant r hr hr1 n (q,y)) z ≠ ⊤ := by
  let w : ℂ := (freeHillValue n:ℂ)+(n:ℂ)*Complex.I
  have hw : w ∈ reducedHillStrip n := by
    change |w.re-freeHillValue n| ≤ 6*(n:ℝ)
    simp [w]
  have hres : w ∈ endpointHillResolventSet r hr1 q := endpointHill_resolvent_point r hr hr1 n hn q hs
  have hnon : endpointReducedDeterminant r hr hr1 n (q,w) ≠ 0 := by
    intro hd
    exact ((mem_endpointHillSpectrum_iff_determinant r hr hr1 n hn w hw q hs).mpr hd) hres
  exact analyticOrderAt_ne_top_on_connected (convex_reducedHillStrip n).isPreconnected
    (analyticOnNhd_endpointReducedDeterminant_spectral r hr hr1 n hn q hs) hw hnon hz

include hn hs in
/-- Every actual determinant zero is strictly inside the corrected strip. -/
theorem endpointReducedDeterminant_zero_interior (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (hd : endpointReducedDeterminant r hr hr1 n (q,z) = 0) :
    |z.re-freeHillValue n| < 6*(n:ℝ) := by
  have hL := endpointReducedDeterminant_zero_localization r hr hr1 n hn q hs z hz hd
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hS : Real.sqrt (n:ℝ) ≤ n := Real.sqrt_le_iff.mpr ⟨by positivity,by nlinarith⟩
  have hR : |z.re-freeHillValue n| ≤ ‖z-(freeHillValue n:ℂ)‖ := by
    simpa using Complex.abs_re_le_norm (z-(freeHillValue n:ℂ))
  linarith

include hn hs in
/-- In the interior, eventual physical chain dimensions and eventual formal
Taylor nullities give exactly the same full algebraic multiplicity. -/
theorem endpointHillAlgebraicMultiplicity_eq_order_interior (z : ℂ)
    (hz : |z.re-freeHillValue n| < 6*(n:ℝ)) :
    (endpointHillAlgebraicMultiplicity r hr hr1 q z : ℕ∞) =
      analyticOrderAt (fun y => endpointReducedDeterminant r hr hr1 n (q,y)) z := by
  let f := fun y => endpointReducedDeterminant r hr hr1 n (q,y)
  let A := endpointReducedMatrixSpectral r hr hr1 n q z
  obtain ⟨p,hp⟩ := analyticAt_endpointReducedMatrixSpectral r hr hr1 n hn q z hs hz.le
  have he : (fun t : ℂ => (A t).det) = (fun t : ℂ => f (z+t)) := by
    funext t
    exact det_pairOperatorMatrix (endpointReducedFamily r hr hr1 n (q,z+t))
  have hf : AnalyticAt ℂ f z := analyticOnNhd_endpointReducedDeterminant_spectral r hr hr1 n hn q hs z hz.le
  have ho : analyticOrderAt (fun t : ℂ => (A t).det) 0 = analyticOrderAt f z := by
    rw [he]
    exact analyticOrderAt_const_add_zero hf
  have hfin : analyticOrderAt (fun t : ℂ => (A t).det) 0 ≠ ⊤ := by
    rw [ho]
    exact endpointReducedDeterminant_order_ne_top r hr hr1 n hn q hs z hz.le
  have hT := eventually_matrixTaylorNullity_eq_analytic_det_order hp hfin
  have hC := eventually_finrank_endpointHillChainSpace r hr hr1 q z
  obtain ⟨N,hN1,hN2⟩ := (hT.and hC).exists
  have hd := (endpointChainTaylorKernelEquiv r hr hr1 n hn q z hs p hp N hz).finrank_eq
  rw [← hN2, hd]
  exact hN1.trans ho

include hn hs in
/-- On the entire closed corrected strip, the actual original operator's
algebraic multiplicity equals the actual effective determinant's analytic order. -/
theorem endpointHillAlgebraicMultiplicity_eq_analyticOrderAt (z : ℂ) (hz : z ∈ reducedHillStrip n) :
    (endpointHillAlgebraicMultiplicity r hr hr1 q z : ℕ∞) =
      analyticOrderAt (fun y => endpointReducedDeterminant r hr hr1 n (q,y)) z := by
  by_cases hd : endpointReducedDeterminant r hr hr1 n (q,z) = 0
  · exact endpointHillAlgebraicMultiplicity_eq_order_interior r hr hr1 n hn q hs z
      (endpointReducedDeterminant_zero_interior r hr hr1 n hn q hs z hz hd)
  · have hnot : z ∉ endpointHillSpectrum r hr1 q := by
      intro hspec
      exact hd ((mem_endpointHillSpectrum_iff_determinant r hr hr1 n hn z hz q hs).mp hspec)
    have hzero : endpointHillAlgebraicMultiplicity r hr hr1 q z = 0 := by
      apply Nat.eq_zero_of_not_pos
      intro hpos
      exact hnot ((endpointHillAlgebraicMultiplicity_pos_iff r hr hr1 q z).mp hpos)
    rw [hzero]
    exact ((analyticOrderAt_eq_zero
      (f := fun y : ℂ => endpointReducedDeterminant r hr hr1 n (q,y)) (z₀ := z)).mpr (Or.inr hd)).symm

include hn hs in
/-- Natural algebraic multiplicities and natural analytic orders also agree exactly. -/
theorem endpointHillAlgebraicMultiplicity_eq_analyticOrderNatAt (z : ℂ) (hz : z ∈ reducedHillStrip n) :
    endpointHillAlgebraicMultiplicity r hr hr1 q z =
      analyticOrderNatAt (fun y => endpointReducedDeterminant r hr hr1 n (q,y)) z := by
  simpa only [ENat.toNat_natCast, analyticOrderNatAt] using
    congrArg ENat.toNat (endpointHillAlgebraicMultiplicity_eq_analyticOrderAt r hr hr1 n hn q hs z hz)

include hn hs in
/-- The entire corrected strip contains exactly two actual physical eigenvalues
counted with the full original operator's algebraic multiplicities. -/
theorem endpointHill_strip_algebraic_count_two :
    (∑ᶠ z : ℂ, if z ∈ reducedHillStrip n then endpointHillAlgebraicMultiplicity r hr hr1 q z else 0) = 2 := by
  calc
    _ = analyticZeroCount (fun z => endpointReducedDeterminant r hr hr1 n (q,z)) (reducedHillStrip n) := by
      unfold analyticZeroCount
      apply finsum_congr
      intro z
      split_ifs with hz
      · exact endpointHillAlgebraicMultiplicity_eq_analyticOrderNatAt r hr hr1 n hn q hs z hz
      · rfl
    _ = 2 := endpointReducedDeterminant_strip_two_zeros r hr hr1 n hn q hs

end NLS.KdV
