import NLS.MKdV.MiuraFiniteGap
import NLS.MKdV.MiuraHillBoundaryExtension
import NLS.ZakharovShabat.SourceFullAbelianHamiltonianLaurent

/-! # Spectral calibration of the finite-gap Hill/Miura hierarchy

The independent physical Hill primitive has a convergent Laurent series
with coefficients from the independent scalar Hill recurrence. Its
nonreal-energy limit fills the exterior collapsed gaps automatically.
Neither a primitive asymptotic nor smoothness is an input hypothesis.
-/
noncomputable section
open Set Metric Complex NLS.Fourier NLS.KdV NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate ContDiff
namespace NLS.MKdV

/-- The independent Hill limit agrees with the filled NLS primitive even
at collapsed cuts, whenever the latter has an analytic germ. -/
theorem canonicalMiuraHillPrimitive_eq_full (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) {W : Set (CoeffPair 2)}
    (D : SourceAbelianSpectralChart (by simp) (by norm_num) W (realDiagonalH1Source a ha).val)
    (z : ℂ) (hzr : 0 < z.re)
    (hz : z ∈ sourceOpenGapComplement (by simp) (by norm_num) (realDiagonalH1Source a ha).val) :
    canonicalMiuraHillPrimitive a (z^2) =
      sourceFullAbelianPrimitive (by simp) (by norm_num) W 0 (z,(realDiagonalH1Source a ha).val) := by
  have hs : AnalyticAt ℂ Complex.sqrt (z^2) := Complex.differentiableOn_sqrt.analyticAt
    (isOpen_slitPlane.mem_nhds (sq_mem_slitPlane_of_re_pos z hzr))
  have hF : AnalyticAt ℂ (fun μ => sourceFullAbelianPrimitive (by simp) (by norm_num) W 0
      (Complex.sqrt μ,(realDiagonalH1Source a ha).val)) (z^2) := by
    have hf := sourceFullAbelianPrimitive_spectral_analytic D 0 z hz
    have hf' : AnalyticAt ℂ (fun w => sourceFullAbelianPrimitive (by simp) (by norm_num) W 0
        (w,(realDiagonalH1Source a ha).val)) (Complex.sqrt (z^2)) := by
      rw [sqrt_sq_of_re_pos z hzr]
      exact hf
    exact hf'.comp hs
  have he (μ : ℂ) (hi : μ.im ≠ 0) :
      miuraHillPrimitive (μ,periodOneMiuraCurve a) =
        sourceFullAbelianPrimitive (by simp) (by norm_num) W 0
          (Complex.sqrt μ,(realDiagonalH1Source a ha).val) := by
    have hr := sourceCanonicalRootDomain_of_im_ne_zero (by simp) (by norm_num)
      (realDiagonalH1Source a ha).val (realDiagonalH1Source a ha).property (Complex.sqrt μ)
        (sqrt_re_pos_of_im_ne_zero μ hi).2
    rw [sourceFullAbelianPrimitive_eq_real _ D 0 _
      (sourceCanonicalRootDomain_subset_openGapComplement _ _ _ hr)]
    simpa only [Int.cast_zero,mul_zero,add_zero] using (miuraHillSheets_nonreal_eq_sqrt_NLS a ha μ hi).2
  simpa only [canonicalMiuraHillPrimitive,sqrt_sq_of_re_pos z hzr] using
    nonrealBoundaryExtension_eq_of_continuousAt hF.continuousAt he

/-- Equation (12), in the stronger form of a convergent exterior series.
The domain includes the filled collapsed gaps and both nonreal quadrants
of the right frequency half-plane. -/
theorem exists_canonicalMiuraHillPrimitive_finiteGap_laurent (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (hf : miuraFiniteGap a ha) :
    ∃ R : ℝ, 0 < R ∧ ∀ z : ℂ, 0 < z.re → R < ‖z‖ →
      HasSum (fun k : ℕ => I*(2*classicalMiuraHillHamiltonian (miuraFiniteGapProfile a ha hf) (k+1)) /
        (2*z)^(2*k+1)) (canonicalMiuraHillPrimitive a (z^2)+I*z) := by
  let F := miuraActionContourFamily a ha
  let φ := realDiagonalH1Source a ha
  have hfinite := (miuraFiniteGap_iff_sourceFiniteGap a ha).mp hf
  obtain ⟨R,hR,_,hseries⟩ := exists_sourceFullAbelian_finiteGap_hamiltonian_laurent
    F.cauchy φ F.source_mem hfinite
  obtain ⟨T,_,hT⟩ := exists_exterior_subset_sourceOpenGapComplement_finiteGap
    (by simp) (by norm_num) φ hfinite
  obtain ⟨D⟩ := F.cauchy.charts φ.val F.source_mem
  refine ⟨max R T,hR.trans_le (le_max_left _ _),?_⟩
  intro z hzr hz
  have hzT : z ∈ sourceOpenGapComplement (by simp) (by norm_num) φ.val :=
    hT ((le_max_right _ _).trans_lt hz)
  have h := hseries 0 z ((le_max_left _ _).trans_lt hz)
  simp only [Int.cast_zero,mul_zero,sub_zero] at h
  rw [← canonicalMiuraHillPrimitive_eq_full a ha D z hzr hzT] at h
  let f : ℕ → ℂ := fun k => I*sourceFiniteGapNLSHamiltonian (by simp) (by norm_num)
    φ hfinite (k+1)/(2*z)^(k+1)
  have he : Summable (fun k : ℕ => f (2*k)) :=
    h.summable.comp_injective (by intro i j hij; omega)
  have hodd (k : ℕ) : f (2*k+1) = 0 := by
    dsimp only [f]
    rw [show 2*k+1+1 = 2*k+2 by omega,(sourceFiniteGapHamiltonians_miura a ha hf k).2,mul_zero,zero_div]
  have ho : HasSum (fun k : ℕ => f (2*k+1)) 0 := by
    simpa only [hodd] using (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℂ)) 0)
  have hsum := he.hasSum.even_add_odd ho
  rw [add_zero] at hsum
  have hval := hsum.unique h
  rw [← hval]
  apply he.hasSum.congr_fun
  intro k
  dsimp only [f]
  rw [(sourceFiniteGapHamiltonians_miura a ha hf k).1]

/-- All Laurent coefficients are the independently defined native K's
on the unchanged original finite-gap coefficients. -/
theorem exists_canonicalMiuraHillPrimitive_native_laurent (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (hf : miuraFiniteGap a ha) :
    ∃ R : ℝ, 0 < R ∧ ∀ z : ℂ, 0 < z.re → R < ‖z‖ →
      HasSum (fun k : ℕ => I*(2*nativeMiuraHillHamiltonian k (miuraFiniteGapSobolev a ha hf k)) /
        (2*z)^(2*k+1)) (canonicalMiuraHillPrimitive a (z^2)+I*z) := by
  obtain ⟨R,hR,h⟩ := exists_canonicalMiuraHillPrimitive_finiteGap_laurent a ha hf
  refine ⟨R,hR,?_⟩
  intro z hzr hz
  apply (h z hzr hz).congr_fun
  intro k
  rw [nativeMiuraHillHamiltonian_eq_finiteGapProfile a ha hf k _ (fun _ => rfl)]

end NLS.MKdV
