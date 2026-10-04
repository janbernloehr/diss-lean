import NLS.ZakharovShabat.SourceAbelianSpectralChart

/-! # A canonical full spectral abelian primitive

Compatible spectral charts define one function on the whole complement of
noncollapsed cuts. Its values there are independent of both the chosen chart
and the ambient root neighborhood. Outside sources admitting a chart the
function is assigned the harmless default value zero.
-/
noncomputable section
open Set Metric Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def sourceFullAbelianPrimitive (hp : p ≠ ⊤) (hp1 : 1 < p)
    (W : Set (CoeffPair p)) (n : ℤ) (t : ℂ × CoeffPair p) : ℂ := by
  classical
  exact if h : Nonempty (SourceAbelianSpectralChart hp hp1 W t.2) then
    (Classical.choice h).primitive n t.1 else 0

variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)} {ψ : CoeffPair p}

theorem sourceFullAbelianPrimitive_eq_chart (D : SourceAbelianSpectralChart hp hp1 W ψ)
    (n : ℤ) (z : ℂ) (hz : z ∈ sourceOpenGapComplement hp hp1 ψ) :
    sourceFullAbelianPrimitive hp hp1 W n (z,ψ) = D.primitive n z := by
  classical
  have h : Nonempty (SourceAbelianSpectralChart hp hp1 W ψ) := ⟨D⟩
  rw [sourceFullAbelianPrimitive, dif_pos h]
  exact (Classical.choice h).eqOn D n hz

theorem sourceFullAbelianPrimitive_eventuallyEq_chart (D : SourceAbelianSpectralChart hp hp1 W ψ)
    (n : ℤ) (z : ℂ) (hz : z ∈ sourceOpenGapComplement hp hp1 ψ) :
    (fun w => sourceFullAbelianPrimitive hp hp1 W n (w,ψ)) =ᶠ[𝓝 z] D.primitive n := by
  filter_upwards [(D.discs.isOpen_openGapComplement ψ D.source_mem).mem_nhds hz] with w hw
  exact sourceFullAbelianPrimitive_eq_chart D n w hw

theorem sourceFullAbelianPrimitive_spectral_analytic (D : SourceAbelianSpectralChart hp hp1 W ψ)
    (n : ℤ) : AnalyticOnNhd ℂ (fun z => sourceFullAbelianPrimitive hp hp1 W n (z,ψ))
      (sourceOpenGapComplement hp hp1 ψ) := by
  intro z hz
  exact (D.analytic n z hz).congr (sourceFullAbelianPrimitive_eventuallyEq_chart D n z hz).symm

theorem sourceFullAbelianPrimitive_hasDerivAt (D : SourceAbelianSpectralChart hp hp1 W ψ)
    (n : ℤ) (z : ℂ) (hz : z ∈ sourceCanonicalRootDomain hp hp1 ψ) :
    HasDerivAt (fun w => sourceFullAbelianPrimitive hp hp1 W n (w,ψ))
      (deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z / sourceCanonicalRoot hp hp1 ψ z) z :=
  (D.derivative n z hz).congr_of_eventuallyEq
    (sourceFullAbelianPrimitive_eventuallyEq_chart D n z
      (sourceCanonicalRootDomain_subset_openGapComplement hp hp1 ψ hz))

theorem sourceFullAbelianPrimitive_independent_neighborhood
    (D : SourceAbelianSpectralChart hp hp1 W ψ) (E : SourceAbelianSpectralChart hp hp1 V ψ)
    (n : ℤ) (z : ℂ) (hz : z ∈ sourceOpenGapComplement hp hp1 ψ) :
    sourceFullAbelianPrimitive hp hp1 W n (z,ψ) = sourceFullAbelianPrimitive hp hp1 V n (z,ψ) := by
  rw [sourceFullAbelianPrimitive_eq_chart D n z hz, sourceFullAbelianPrimitive_eq_chart E n z hz]
  exact D.eqOn E n hz

theorem sourceFullAbelianPrimitive_index_shift (D : SourceAbelianSpectralChart hp hp1 W ψ)
    (n : ℤ) (z : ℂ) (hz : z ∈ sourceOpenGapComplement hp hp1 ψ) :
    sourceFullAbelianPrimitive hp hp1 W n (z,ψ) =
      sourceFullAbelianPrimitive hp hp1 W 0 (z,ψ)+I*(Real.pi : ℂ)*n := by
  rw [sourceFullAbelianPrimitive_eq_chart D n z hz, sourceFullAbelianPrimitive_eq_chart D 0 z hz]
  exact D.index_shift n z

theorem sourceFullAbelianPrimitive_eq_real (φ : realTypeSourceSubmodule p)
    (D : SourceAbelianSpectralChart hp hp1 W φ.val) (n : ℤ) (z : ℂ)
    (hz : z ∈ sourceOpenGapComplement hp hp1 φ.val) :
    sourceFullAbelianPrimitive hp hp1 W n (z,φ.val) =
      sourceAbelianPrimitive hp hp1 φ.val φ.property z+I*(Real.pi : ℂ)*n := by
  rw [sourceFullAbelianPrimitive_eq_chart D n z hz]
  exact D.discs.eq_real_of_exterior φ D.source_mem n (D.primitive n) (D.analytic n) (D.exterior_eq n) hz

theorem sourceFullAbelianPrimitive_zero (D : SourceAbelianSpectralChart hp hp1 W 0)
    (n : ℤ) (z : ℂ) :
    sourceFullAbelianPrimitive hp hp1 W n (z,0) = -I*z+I*(Real.pi : ℂ)*n := by
  have hz : z ∈ sourceOpenGapComplement hp hp1 (0 : CoeffPair p) := by
    rw [sourceOpenGapComplement_zero]; exact mem_univ z
  have h := sourceFullAbelianPrimitive_eq_real (0 : realTypeSourceSubmodule p) D n z hz
  change sourceFullAbelianPrimitive hp hp1 W n (z,0) =
    sourceAbelianPrimitive hp hp1 (0 : CoeffPair p) _ z+I*(Real.pi : ℂ)*n at h
  rw [sourceAbelianPrimitive_zero] at h
  exact h

end NLS.ZakharovShabat
