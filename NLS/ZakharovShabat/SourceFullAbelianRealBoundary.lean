import NLS.ZakharovShabat.SourceFullAbelianUniformSquare

/-! # Real boundary values of the full canonical primitive

The full primitive inherits the signed arcosh limits of the real-source
construction, for arbitrary half-plane approaches and all closed-gap
points. Its derivative remains the regular Floquet logarithmic derivative
at collapsed gaps as well as off the cuts.
-/
noncomputable section
open Set Metric Filter Topology Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}

/-- Lemma 19.1(v) for the full primitive, including endpoints and collapsed gaps. -/
theorem sourceFullAbelianPrimitive_real_gap_boundary_limit (φ : realTypeSourceSubmodule p)
    (E : SourceAbelianSpectralChart hp hp1 W φ.val) (n : ℤ) (upper : Bool) (x : ℝ)
    (hx : x ∈ Icc
      (canonicalPeriodicLeft hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re) :
    Tendsto (fun z => sourceFullAbelianPrimitive hp hp1 W n (z,φ.val))
      (𝓝[sourceAbelianHalfPlane upper] (x:ℂ))
      (𝓝 (if upper then (sourceRealGapArcoshProfile hp φ.val n x : ℂ)
        else -(sourceRealGapArcoshProfile hp φ.val n x : ℂ))) := by
  apply (sourceAbelianPrimitive_gap_boundary_limit hp hp1 φ.val φ.property n upper x hx).congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (sourceFullAbelianPrimitive_eq_real φ E n z
    (sourceCanonicalRootDomain_subset_openGapComplement hp hp1 φ.val
      (sourceAbelianHalfPlane_subset_rootDomain hp hp1 φ.val φ.property upper hz))).symm

/-- On gap `n`, every other normalization index adds exactly `i*pi*(m-n)`. -/
theorem sourceFullAbelianPrimitive_real_gap_boundary_limit_index (φ : realTypeSourceSubmodule p)
    (E : SourceAbelianSpectralChart hp hp1 W φ.val) (n m : ℤ) (upper : Bool) (x : ℝ)
    (hx : x ∈ Icc
      (canonicalPeriodicLeft hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re) :
    Tendsto (fun z => sourceFullAbelianPrimitive hp hp1 W m (z,φ.val))
      (𝓝[sourceAbelianHalfPlane upper] (x:ℂ))
      (𝓝 ((if upper then (sourceRealGapArcoshProfile hp φ.val n x : ℂ)
        else -(sourceRealGapArcoshProfile hp φ.val n x : ℂ))+I*(Real.pi : ℂ)*(m-n))) := by
  apply ((sourceFullAbelianPrimitive_real_gap_boundary_limit φ E n upper x hx).add_const
    (I*(Real.pi : ℂ)*(m-n))).congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hzO := sourceCanonicalRootDomain_subset_openGapComplement hp hp1 φ.val
    (sourceAbelianHalfPlane_subset_rootDomain hp hp1 φ.val φ.property upper hz)
  rw [sourceFullAbelianPrimitive_index_shift E n z hzO,sourceFullAbelianPrimitive_index_shift E m z hzO]
  ring

/-- The full derivative uses the filled logarithmic derivative on the
whole real-source spectral domain, including collapsed spectral points. -/
theorem sourceFullAbelianPrimitive_real_hasDerivAt (φ : realTypeSourceSubmodule p)
    (E : SourceAbelianSpectralChart hp hp1 W φ.val) (n : ℤ) (z : ℂ)
    (hz : z ∈ sourceOpenGapComplement hp hp1 φ.val) :
    HasDerivAt (fun w => sourceFullAbelianPrimitive hp hp1 W n (w,φ.val))
      (sourceFloquetLogDerivative hp hp1 φ.val z) z := by
  apply ((sourceAbelianPrimitive_hasDerivAt hp hp1 φ.val φ.property z hz).add_const
    (I*(Real.pi : ℂ)*n)).congr_of_eventuallyEq
  filter_upwards [(isOpen_sourceOpenGapComplement_of_realType hp hp1 φ.val φ.property).mem_nhds hz] with w hw
  exact sourceFullAbelianPrimitive_eq_real φ E n w hw

/-- One ambient neighborhood supports both Lemma 19.1(v)'s real boundary
formula for every real source and (vi)'s exact free primitive. -/
theorem exists_sourceFullAbelian_real_boundary_and_zero (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧
      (∀ φ : realTypeSourceSubmodule p, ∀ n : ℤ, ∀ upper : Bool, ∀ x ∈ Icc
        (canonicalPeriodicLeft hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re
        (canonicalPeriodicRight hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re,
        Tendsto (fun z => sourceFullAbelianPrimitive hp hp1 W n (z,φ.val))
          (𝓝[sourceAbelianHalfPlane upper] (x:ℂ))
          (𝓝 (if upper then (sourceRealGapArcoshProfile hp φ.val n x : ℂ)
            else -(sourceRealGapArcoshProfile hp φ.val n x : ℂ)))) ∧
      ∀ (n : ℤ) (z : ℂ), sourceFullAbelianPrimitive hp hp1 W n (z,0) = -I*z+I*(Real.pi : ℂ)*n := by
  obtain ⟨W,hW,hreal,hfamilies⟩ := exists_sourceFullAbelianUniformCauchyFamilies hp hp1
  have hcharts (φ : realTypeSourceSubmodule p) : Nonempty (SourceAbelianSpectralChart hp hp1 W φ.val) := by
    obtain ⟨C,hC⟩ := hfamilies φ
    apply C.charts
    rw [hC]
    exact mem_ball_self C.discs.sourceRadius_pos
  refine ⟨W,hW,hreal,?_,?_⟩
  · intro φ n upper x hx
    obtain ⟨E⟩ := hcharts φ
    exact sourceFullAbelianPrimitive_real_gap_boundary_limit φ E n upper x hx
  · intro n z
    obtain ⟨E⟩ := hcharts 0
    exact sourceFullAbelianPrimitive_zero E n z

end NLS.ZakharovShabat
