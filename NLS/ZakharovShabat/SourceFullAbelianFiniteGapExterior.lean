import NLS.ZakharovShabat.SourceFullAbelianRealBoundary
import NLS.ZakharovShabat.SourceFiniteGapExteriorCoefficients

/-! # The actual full primitive on the finite-gap exterior

At a real finite-gap source, a single exterior disc works for every
normalization index. The filled derivative is the regular Floquet
logarithmic derivative and has the previously constructed analytic
quadratic remainder at infinity. No cut-avoidance assumption is needed
at the infinitely many collapsed exterior spectral points.
-/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}

/-- The exterior analyticity assertion at the start of Lemma 19.2,
for the actual primitive and simultaneously for every signed index. -/
theorem exists_sourceFullAbelianPrimitive_finiteGap_exterior (φ : realTypeSourceSubmodule p)
    (E : SourceAbelianSpectralChart hp hp1 W φ.val) (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    ∃ R : ℝ, 0 < R ∧ ∀ n : ℤ,
      AnalyticOnNhd ℂ (fun z => sourceFullAbelianPrimitive hp hp1 W n (z,φ.val)) {z : ℂ | R < ‖z‖} ∧
      ∀ z : ℂ, R < ‖z‖ → HasDerivAt (fun w => sourceFullAbelianPrimitive hp hp1 W n (w,φ.val))
        (sourceFloquetLogDerivative hp hp1 φ.val z) z := by
  obtain ⟨R,hR,hsub⟩ := exists_exterior_subset_sourceOpenGapComplement_finiteGap hp hp1 φ hf
  exact ⟨R,hR,fun n => ⟨(sourceFullAbelianPrimitive_spectral_analytic E n).mono hsub,
    fun z hz => sourceFullAbelianPrimitive_real_hasDerivAt φ E n z (hsub hz)⟩⟩

/-- One analytic remainder controls the exterior derivative of every
normalization of the actual finite-gap primitive. There is no `1/z`
term in this derivative; the constant term is exactly `-i`. -/
theorem exists_sourceFullAbelianPrimitive_finiteGap_quadratic_derivative (φ : realTypeSourceSubmodule p)
    (E : SourceAbelianSpectralChart hp hp1 W φ.val) (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    ∃ R : ℝ, 0 < R ∧ ∃ r : ℝ, 0 < r ∧ r⁻¹ < R ∧ ∃ h : ℂ → ℂ,
      AnalyticOnNhd ℂ h (ball 0 r) ∧ ∀ n : ℤ,
        AnalyticOnNhd ℂ (fun z => sourceFullAbelianPrimitive hp hp1 W n (z,φ.val)) {z : ℂ | R < ‖z‖} ∧
        ∀ z : ℂ, R < ‖z‖ → HasDerivAt (fun w => sourceFullAbelianPrimitive hp hp1 W n (w,φ.val))
          (-I+z⁻¹^2*h z⁻¹) z := by
  obtain ⟨R₀,hR₀,hF⟩ := exists_sourceFullAbelianPrimitive_finiteGap_exterior φ E hf
  obtain ⟨r,hr,h,hh,he,_⟩ := exists_sourceFiniteGap_exterior_quadratic_remainder hp hp1 φ hf
  let R := max R₀ r⁻¹+1
  have hR₀R : R₀ < R := by dsimp [R]; linarith [le_max_left R₀ r⁻¹]
  have hrR : r⁻¹ < R := by dsimp [R]; linarith [le_max_right R₀ r⁻¹]
  refine ⟨R,hR₀.trans hR₀R,r,hr,hrR,h,hh,?_⟩
  intro n
  refine ⟨(hF n).1.mono (fun _ hz => hR₀R.trans hz),?_⟩
  intro z hz
  rw [← he z (hrR.trans hz)]
  exact (hF n).2 z (hR₀R.trans hz)

/-- The preceding exterior construction is available at every real
finite-gap source in one ambient neighborhood, with no supplied chart. -/
theorem exists_sourceFullAbelian_finiteGap_exterior_data (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧
      ∀ φ : realTypeSourceSubmodule p, φ ∈ sourceFiniteGapLocus hp hp1 →
        ∃ R : ℝ, 0 < R ∧ ∃ r : ℝ, 0 < r ∧ r⁻¹ < R ∧ ∃ h : ℂ → ℂ,
          AnalyticOnNhd ℂ h (ball 0 r) ∧ ∀ n : ℤ,
            AnalyticOnNhd ℂ (fun z => sourceFullAbelianPrimitive hp hp1 W n (z,φ.val)) {z : ℂ | R < ‖z‖} ∧
            ∀ z : ℂ, R < ‖z‖ → HasDerivAt (fun w => sourceFullAbelianPrimitive hp hp1 W n (w,φ.val))
              (-I+z⁻¹^2*h z⁻¹) z := by
  obtain ⟨W,hW,hreal,hfamilies⟩ := exists_sourceFullAbelianUniformCauchyFamilies hp hp1
  refine ⟨W,hW,hreal,?_⟩
  intro φ hf
  obtain ⟨C,hC⟩ := hfamilies φ
  obtain ⟨E⟩ := C.charts φ.val (by rw [hC]; exact mem_ball_self C.discs.sourceRadius_pos)
  exact exists_sourceFullAbelianPrimitive_finiteGap_quadratic_derivative φ E hf

end NLS.ZakharovShabat
