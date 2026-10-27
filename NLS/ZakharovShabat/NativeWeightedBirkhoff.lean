import NLS.ZakharovShabat.NativeWeightedFiniteGap
import NLS.ZakharovShabat.SourceBirkhoffSobolevGlobalInverse
import NLS.ZakharovShabat.SourceSection17Original
import NLS.ZakharovShabat.PhysicalBirkhoffIntrinsicProperties

/-! # Birkhoff coordinates on original periodic distributions

The original weighted distribution space carries the same Birkhoff map,
with its raw spectral coordinates and exact component-sum topology. One
constructed family works at every weight. Its Sobolev restrictions have
global real analytic inverses for every nonnegative real order and 1 < p ≤ 2.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology NLS.Fourier SmoothPeriodicTest
open scoped ENNReal
namespace NLS.ZakharovShabat.NativeWeightedPeriodic
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The original rectangular target, with the full weighted pair norm. -/
abbrev Target (w : SpectralWeight) (p : ℝ≥0∞) [Fact (1 ≤ p)] :=
  WithLp p (WeightedRealCoeff (sourceFrequencyWeight w) p ×
    WeightedRealCoeff (sourceFrequencyWeight w) p)

variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W V : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
  (D : SourceSection17OriginalData hp hp1 W₀ W V s)

/-- Birkhoff coordinates of the original distribution, with no change of raw coefficients. -/
def birkhoff (w : SpectralWeight) (φ : realSpace w p) : Target w p :=
  D.complex.originalWeightedRealMap w (realCoefficientsEquiv w φ)

@[simp] theorem birkhoff_fst (w : SpectralWeight) (φ : realSpace w p) (n : ℤ) :
    (birkhoff D w φ).fst.val.val n =
      ((sourceRealBirkhoffMap hp hp1 s (source w φ)).1 n : ℂ) :=
  D.complex.originalWeightedRealMap_fst w _ n

@[simp] theorem birkhoff_snd (w : SpectralWeight) (φ : realSpace w p) (n : ℤ) :
    (birkhoff D w φ).snd.val.val n =
      ((sourceRealBirkhoffMap hp hp1 s (source w φ)).2 n : ℂ) :=
  D.complex.originalWeightedRealMap_snd w _ n

/-- The target norm is exactly the weighted component-sum norm of the raw coordinates. -/
theorem birkhoff_norm_rpow (w : SpectralWeight) (φ : realSpace w p) :
    ‖birkhoff D w φ‖ ^ p.toReal = ∑' n : ℤ,
      (|w (2*n) * (sourceRealBirkhoffMap hp hp1 s (source w φ)).1 n| ^ p.toReal +
       |w (2*n) * (sourceRealBirkhoffMap hp hp1 s (source w φ)).2 n| ^ p.toReal) :=
  D.complex.originalWeightedRealMap_norm_rpow w _

theorem birkhoff_injective (w : SpectralWeight) : Function.Injective (birkhoff D w) :=
  (D.complex.originalWeightedRealMap_injective w).comp (realCoefficientsEquiv w).injective

/-- Spectral finite-gap membership is exactly finite support of the nonlinear output. -/
theorem birkhoff_finiteGap_iff (w : SpectralWeight) (φ : realSpace w p) :
    φ ∈ finiteGapLocus hp hp1 w ↔
      {n : ℤ | (birkhoff D w φ).fst.val.val n ≠ 0 ∨
        (birkhoff D w φ).snd.val.val n ≠ 0}.Finite := by
  change source w φ ∈ sourceFiniteGapLocus hp hp1 ↔ _
  rw [D.complex.finiteGap_iff_finite_pairSupport]
  simp only [RealCoeff.pairSupport, birkhoff_fst, birkhoff_snd, ne_eq, Complex.ofReal_eq_zero]

/-- Analyticity is in the original distribution norm on the entire real space. -/
theorem birkhoff_analytic (w : SpectralWeight) : AnalyticOnNhd ℝ (birkhoff D w) univ := by
  intro φ _
  exact (D.complex.originalWeightedRealMap_analytic w _ (mem_univ _)).comp
    ((realCoefficientsEquiv w).analyticAt φ)

theorem birkhoff_isOpenEmbedding (w : SpectralWeight) : IsOpenEmbedding (birkhoff D w) :=
  (D.complex.originalWeightedRealMap_isOpenEmbedding w).comp
    (realCoefficientsEquiv w).toHomeomorph.isOpenEmbedding

/-- Changing a weight changes the topology, not the coordinates of the same distribution. -/
theorem birkhoff_same_distribution (w v : SpectralWeight)
    (φ : realSpace w p) (ψ : realSpace v p)
    (hf : φ.val.fst.val = ψ.val.fst.val) (hg : φ.val.snd.val = ψ.val.snd.val) (n : ℤ) :
    (birkhoff D w φ).fst.val.val n = (birkhoff D v ψ).fst.val.val n ∧
    (birkhoff D w φ).snd.val.val n = (birkhoff D v ψ).snd.val.val n := by
  have he : source w φ = source v ψ := by
    apply Subtype.ext
    apply (CoeffPair.toMax p).injective
    apply Prod.ext
    · ext k
      exact (source_fst w φ k).trans ((congrArg (fun u => u (mode (-k))) hf).trans
        (source_fst v ψ k).symm)
    · ext k
      exact (source_snd w φ k).trans ((congrArg (fun u => u (mode (-k))) hg).trans
        (source_snd v ψ k).symm)
  simp only [birkhoff_fst, birkhoff_snd, he, and_self]

/-- The global Sobolev map and inverse act on original distributions. -/
def sobolevHomeomorph (hp2 : p ≤ 2) (t : ℝ) (ht : 0 ≤ t) :
    realSpace (sobolevWeight t ht) p ≃ₜ Target (sobolevWeight t ht) p :=
  (realCoefficientsEquiv (sobolevWeight t ht)).toHomeomorph.trans
    (D.complex.originalWeightedRealSobolevHomeomorph hp2 t ht)

@[simp] theorem sobolevHomeomorph_apply (hp2 : p ≤ 2) (t : ℝ) (ht : 0 ≤ t)
    (φ : realSpace (sobolevWeight t ht) p) :
    sobolevHomeomorph D hp2 t ht φ = birkhoff D (sobolevWeight t ht) φ := rfl

/-- Both directions are analytic for every real order t ≥ 0, including fractional orders. -/
theorem sobolevHomeomorph_analytic (hp2 : p ≤ 2) (t : ℝ) (ht : 0 ≤ t) :
    AnalyticOnNhd ℝ (sobolevHomeomorph D hp2 t ht) univ ∧
      AnalyticOnNhd ℝ (sobolevHomeomorph D hp2 t ht).symm univ := by
  refine ⟨birkhoff_analytic D _, ?_⟩
  intro z _
  exact ((realCoefficientsEquiv (sobolevWeight t ht)).symm.analyticAt _).comp
    (D.complex.originalWeightedRealSobolevHomeomorph_symm_analytic hp2 t ht z (mem_univ _))

/-- The inverse recovers every original smooth-test functional, not just its Fourier class. -/
theorem sobolevHomeomorph_inverse_test (hp2 : p ≤ 2) (t : ℝ) (ht : 0 ≤ t)
    (φ : realSpace (sobolevWeight t ht) p) (f : SmoothPeriodicTest 1) :
    ((sobolevHomeomorph D hp2 t ht).symm (birkhoff D _ φ)).val.fst.val f = φ.val.fst.val f ∧
    ((sobolevHomeomorph D hp2 t ht).symm (birkhoff D _ φ)).val.snd.val f = φ.val.snd.val f := by
  rw [← sobolevHomeomorph_apply D hp2 t ht φ, Homeomorph.symm_apply_apply]
  exact ⟨rfl, rfl⟩

/-- Construct one original family before selecting weights, orders or distributions. -/
theorem exists_birkhoff_family (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W₀ W V : Set (CoeffPair p), ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
      ∃ D : SourceSection17OriginalData hp hp1 W₀ W V s,
        (∀ w : SpectralWeight, AnalyticOnNhd ℝ (birkhoff D w) univ ∧
          IsOpenEmbedding (birkhoff D w)) ∧
        ∀ hp2 : p ≤ 2, ∀ t : ℝ, ∀ ht : 0 ≤ t,
          AnalyticOnNhd ℝ (sobolevHomeomorph D hp2 t ht) univ ∧
          AnalyticOnNhd ℝ (sobolevHomeomorph D hp2 t ht).symm univ := by
  obtain ⟨W₀,W,V,s,D⟩ := sourceSection17_original hp hp1
  exact ⟨W₀,W,V,s,D,fun w => ⟨birkhoff_analytic D w, birkhoff_isOpenEmbedding D w⟩,
    fun hp2 t ht => sobolevHomeomorph_analytic D hp2 t ht⟩

/-- The physical L2 realization of the same original weighted distribution. -/
def physical (w : SpectralWeight) (φ : realSpace w 2) : physicalRealSubmodule :=
  realSourcePhysicalL2Equiv (source w φ)

/-- The actual normalized physical Fourier integrals are the original test coefficients. -/
theorem physical_coefficients (w : SpectralWeight) (φ : realSpace w 2) (n : ℤ) :
    intervalFourierCoefficient 1 (physical w φ).val.fst n = φ.val.fst.val (mode (-n)) ∧
    intervalFourierCoefficient 1 (physical w φ).val.snd n = φ.val.snd.val (mode (-n)) := by
  change intervalFourierCoefficient 1 (sourcePhysicalL2Equiv (source w φ).val).fst n = _ ∧
    intervalFourierCoefficient 1 (sourcePhysicalL2Equiv (source w φ).val).snd n = _
  rw [sourcePhysicalL2Equiv_apply]
  exact ⟨(sourcePhysicalL2_coefficients (source w φ).val n).1.trans (source_fst w φ n),
    (sourcePhysicalL2_coefficients (source w φ).val n).2.trans (source_snd w φ n)⟩

/-- The physical representative agrees on every smooth test, not just on Fourier modes. -/
theorem physical_test (w : SpectralWeight) (φ : realSpace w 2) (f : SmoothPeriodicTest 1) :
    φ.val.fst.val f = ∫ x in (0 : ℝ)..1, (physical w φ).val.fst x * f x ∧
    φ.val.snd.val f = ∫ x in (0 : ℝ)..1, (physical w φ).val.snd x * f x := by
  have h₁ : IntervalIntegrable (physical w φ).val.fst MeasureTheory.volume 0 1 := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
    exact (MeasureTheory.Lp.memLp _).integrable (by norm_num)
  have h₂ : IntervalIntegrable (physical w φ).val.snd MeasureTheory.volume 0 1 := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
    exact (MeasureTheory.Lp.memLp _).integrable (by norm_num)
  have he₁ : Distribution.ofL1 (physical w φ).val.fst h₁ = φ.val.fst.val := by
    apply Distribution.ext_coefficients
    intro n
    rw [Distribution.ofL1_coefficient]
    exact (physical_coefficients w φ n).1
  have he₂ : Distribution.ofL1 (physical w φ).val.snd h₂ = φ.val.snd.val := by
    apply Distribution.ext_coefficients
    intro n
    rw [Distribution.ofL1_coefficient]
    exact (physical_coefficients w φ n).2
  rw [← he₁, ← he₂, Distribution.ofL1_apply, Distribution.ofL1_apply]
  simp

variable {A B C : Set (CoeffPair 2)} {r : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
  (E : SourceSection17OriginalData (by simp) (by norm_num) A B C r)

/-- At every weight the actual coordinates are the intrinsic physical contour coordinates. -/
theorem birkhoff_physical (w : SpectralWeight) (φ : realSpace w 2) (n : ℤ) :
    (birkhoff E w φ).fst.val.val n = ((intrinsicPhysicalBirkhoffMap (physical w φ)).fst n : ℂ) ∧
    (birkhoff E w φ).snd.val.val n = ((intrinsicPhysicalBirkhoffMap (physical w φ)).snd n : ℂ) := by
  let F := E.toSourceSection14OriginalData
  have he : (intrinsicPhysicalBirkhoffMap (physical w φ)).ofLp =
      sourceRealBirkhoffMap (by simp) (by norm_num) r (source w φ) := by
    rw [F.intrinsicPhysicalBirkhoffMap_eq, F.physicalRealActionAngleHomeomorph_apply,
      F.realActionAngleMap_eq]
    change sourceRealBirkhoffMap _ _ r
      (realSourcePhysicalL2Equiv.symm (realSourcePhysicalL2Equiv (source w φ))) = _
    rw [LinearIsometryEquiv.symm_apply_apply]
  rw [birkhoff_fst, birkhoff_snd, ← he]
  exact ⟨rfl, rfl⟩

/-- Nonlinear Parseval in the exact original unweighted distribution pair norm. -/
theorem birkhoff_parseval (φ : realSpace SpectralWeight.one 2) :
    ‖birkhoff E SpectralWeight.one φ‖ = ‖φ‖ := by
  have he : (source SpectralWeight.one φ).val =
      sourcePairWeightCoordinates SpectralWeight.one (coefficients SpectralWeight.one 2 φ.val) := by
    apply (CoeffPair.toMax 2).injective
    apply Prod.ext
    · ext n
      change (source SpectralWeight.one φ).val.fst n =
        (sourcePairWeightCoordinates SpectralWeight.one (coefficients SpectralWeight.one 2 φ.val)).fst n
      simp
    · ext n
      change (source SpectralWeight.one φ).val.snd n =
        (sourcePairWeightCoordinates SpectralWeight.one (coefficients SpectralWeight.one 2 φ.val)).snd n
      simp
  have hs : ‖(source SpectralWeight.one φ).val‖ = ‖φ‖ := by
    rw [he, (sourcePairWeightCoordinates SpectralWeight.one).norm_map,
      (coefficients SpectralWeight.one 2).norm_map]
    rfl
  let z := sourceRealBirkhoffMap (by simp) (by norm_num) r (source SpectralWeight.one φ)
  have hx : HasSum (fun n : ℤ => |z.1 n|^2) (‖z.1‖^2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs] using
      lp.hasSum_norm (p := 2) (by norm_num) z.1
  have hy : HasSum (fun n : ℤ => |z.2 n|^2) (‖z.2‖^2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs] using
      lp.hasSum_norm (p := 2) (by norm_num) z.2
  have hn := birkhoff_norm_rpow E SpectralWeight.one φ
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, SpectralWeight.one_apply, one_mul] at hn
  rw [(hx.add hy).tsum_eq, E.complex.hilbert_real_map_norm_sq, hs] at hn
  nlinarith [norm_nonneg (birkhoff E SpectralWeight.one φ), norm_nonneg φ]

end NLS.ZakharovShabat.NativeWeightedPeriodic
