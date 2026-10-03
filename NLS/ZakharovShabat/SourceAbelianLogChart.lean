import NLS.ZakharovShabat.SourceFloquetJointLog
import NLS.ZakharovShabat.SourceAbelianPrimitiveProperties
import NLS.ComplexAnalysis.MixedSpectralSourceDerivative

/-! # Jointly analytic local charts for the normalized abelian integral

A real-source value anchors a local Floquet logarithm in both spectral
and complex-source variables. The chart matches the actual primitive
on the anchor source's spectral germ and has the exact joint differential.
Global compatibility as the source varies is a separate assertion.
-/
noncomputable section
open Set Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def sourceAbelianLogChart (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (a : ℂ) (n : ℤ) : ℂ × CoeffPair p → ℂ :=
  normalizedLogChart (sourceFloquetJointMultiplier hp hp1) (a,φ)
    (sourceAbelianPrimitive hp hp1 φ hφ a+I*(Real.pi : ℂ)*n)

/-- The additive normalization is exact at the real-source anchor. -/
theorem sourceAbelianLogChart_base (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (a : ℂ) (n : ℤ)
    (ha : a ∈ sourceCanonicalRootDomain hp hp1 φ) :
    sourceAbelianLogChart hp hp1 φ hφ a n (a,φ) = sourceAbelianPrimitive hp hp1 φ hφ a+I*(Real.pi : ℂ)*n :=
  normalizedLogChart_base _ _ _ (sourceFloquetMultiplier_ne_zero hp hp1 φ a ha)

/-- Changing the signed gap index changes only the required additive
constant; the same joint neighborhood works for every index. -/
theorem sourceAbelianLogChart_eq_zeroIndex_add
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (a : ℂ) (n : ℤ) (t : ℂ × CoeffPair p) :
    sourceAbelianLogChart hp hp1 φ hφ a n t = sourceAbelianLogChart hp hp1 φ hφ a 0 t+I*(Real.pi : ℂ)*n := by
  simp only [sourceAbelianLogChart,normalizedLogChart,Int.cast_zero,mul_zero,add_zero]
  ring

/-- These are actual continuations of the normalized primitive along
the anchor real source, not logarithms with an unspecified period. -/
theorem sourceAbelianLogChart_eventually_eq_anchor_primitive
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (a : ℂ) (n : ℤ)
    (ha : a ∈ sourceCanonicalRootDomain hp hp1 φ) :
    (fun z : ℂ => sourceAbelianLogChart hp hp1 φ hφ a n (z,φ)) =ᶠ[𝓝 a]
      (fun z => sourceAbelianPrimitive hp hp1 φ hφ z+I*(Real.pi : ℂ)*n) := by
  have haO := sourceCanonicalRootDomain_subset_openGapComplement hp hp1 φ ha
  have he : (fun z => exp (sourceAbelianPrimitive hp hp1 φ hφ z)) =ᶠ[𝓝 a] sourceFloquetMultiplier hp hp1 φ := by
    filter_upwards [(isOpen_sourceOpenGapComplement_of_realType hp hp1 φ hφ).mem_nhds haO] with z hz
    exact sourceAbelianPrimitive_exp hp hp1 φ hφ z hz
  have h := normalizedLogChart_eventually_eq (sourceFloquetMultiplier hp hp1 φ)
    (sourceAbelianPrimitive hp hp1 φ hφ) a
    (sourceAbelianPrimitive_analytic hp hp1 φ hφ a haO).continuousAt he
  filter_upwards [h] with z hz
  change (sourceAbelianPrimitive hp hp1 φ hφ a+I*(Real.pi : ℂ)*n)+
    log (sourceFloquetMultiplier hp hp1 φ z/sourceFloquetMultiplier hp hp1 φ a) = _
  change sourceAbelianPrimitive hp hp1 φ hφ a+
    log (sourceFloquetMultiplier hp hp1 φ z/sourceFloquetMultiplier hp hp1 φ a) = _ at hz
  linear_combination hz

/-- The exponential identity holds at complex sources with the exact
index factor and no undetermined multiplicative normalization. -/
theorem sourceAbelianLogChart_exp
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (a : ℂ) (n : ℤ) (t : ℂ × CoeffPair p)
    (ha : a ∈ sourceCanonicalRootDomain hp hp1 φ)
    (ht : t.1 ∈ sourceCanonicalRootDomain hp hp1 t.2) :
    exp (sourceAbelianLogChart hp hp1 φ hφ a n t) =
      exp (I*(Real.pi : ℂ)*n)*sourceFloquetJointMultiplier hp hp1 t := by
  have hane : sourceFloquetJointMultiplier hp hp1 (a,φ) ≠ 0 := sourceFloquetMultiplier_ne_zero hp hp1 φ a ha
  have htne : sourceFloquetJointMultiplier hp hp1 t ≠ 0 := sourceFloquetMultiplier_ne_zero hp hp1 t.2 t.1 ht
  change exp ((sourceAbelianPrimitive hp hp1 φ hφ a+I*(Real.pi : ℂ)*n)+
    log (sourceFloquetJointMultiplier hp hp1 t/sourceFloquetJointMultiplier hp hp1 (a,φ))) = _
  rw [exp_add,exp_log (div_ne_zero htne hane),exp_add,
    sourceAbelianPrimitive_exp hp hp1 φ hφ a (sourceCanonicalRootDomain_subset_openGapComplement hp hp1 φ ha)]
  change (sourceFloquetJointMultiplier hp hp1 (a,φ) * exp (I*(Real.pi : ℂ)*n)) *
    (sourceFloquetJointMultiplier hp hp1 t / sourceFloquetJointMultiplier hp hp1 (a,φ)) = _
  field_simp

/-- A genuine open neighborhood in spectral and complex-source space
supports all indexed charts and their exact joint differentials. -/
theorem exists_sourceAbelianLogChart_joint_neighborhood
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (a : ℂ)
    (ha : a ∈ sourceCanonicalRootDomain hp hp1 φ) :
    ∃ V : Set (ℂ × CoeffPair p), IsOpen V ∧ (a,φ) ∈ V ∧
      (∀ t ∈ V, t.1 ∈ sourceCanonicalRootDomain hp hp1 t.2) ∧
      ∀ n : ℤ, AnalyticOnNhd ℂ (sourceAbelianLogChart hp hp1 φ hφ a n) V ∧
        ∀ t ∈ V, HasFDerivAt (sourceAbelianLogChart hp hp1 φ hφ a n)
          ((sourceCanonicalRoot hp hp1 t.2 t.1)⁻¹ •
            fderiv ℂ (fun u : ℂ × CoeffPair p => canonicalDiscriminant hp (periodOnePotential u.2) u.1) t) t := by
  obtain ⟨W,_,_,hreal,hD,hroot,hM⟩ := exists_global_source_analytic_floquetMultiplier hp hp1
  have hpoint : (a,φ) ∈ sourceCanonicalRootJointDomain hp hp1 W := ⟨hreal hφ,ha⟩
  have hane : sourceFloquetJointMultiplier hp hp1 (a,φ) ≠ 0 := sourceFloquetMultiplier_ne_zero hp hp1 φ a ha
  have hc : ContinuousAt (fun t => sourceFloquetJointMultiplier hp hp1 t/sourceFloquetJointMultiplier hp hp1 (a,φ)) (a,φ) :=
    (hM (a,φ) hpoint).continuousAt.div_const _
  have hone : sourceFloquetJointMultiplier hp hp1 (a,φ)/sourceFloquetJointMultiplier hp hp1 (a,φ) ∈ slitPlane := by
    rw [div_self hane]
    simp
  have hgood := inter_mem (hD.mem_nhds hpoint)
    (hc.tendsto.eventually (isOpen_slitPlane.mem_nhds hone))
  obtain ⟨V,hVsub,hV,hbase⟩ := _root_.mem_nhds_iff.mp hgood
  refine ⟨V,hV,hbase,fun t ht => (hVsub ht).1.2,?_⟩
  intro n
  constructor
  · intro t ht
    exact normalizedLogChart_analyticAt _ _ _ _ (hM t (hVsub ht).1) (hVsub ht).2
  · intro t ht
    exact normalizedLogChart_sourceFloquet_hasFDerivAt hp hp1 W hD hroot (a,φ) t _ hpoint
      (hVsub ht).1 (hVsub ht).2

/-- Restricting the joint differential gives precisely the potential
Fréchet derivative `partial Delta / canonicalRoot` at complex sources. -/
theorem sourceAbelianLogChart_source_fderiv
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (a : ℂ) (n : ℤ) (z : ℂ) (ψ h : CoeffPair p)
    (hjoint : HasFDerivAt (sourceAbelianLogChart hp hp1 φ hφ a n)
      ((sourceCanonicalRoot hp hp1 ψ z)⁻¹ •
        fderiv ℂ (fun u : ℂ × CoeffPair p => canonicalDiscriminant hp (periodOnePotential u.2) u.1) (z,ψ)) (z,ψ)) :
    (fderiv ℂ (fun χ : CoeffPair p => sourceAbelianLogChart hp hp1 φ hφ a n (z,χ)) ψ) h =
      (fderiv ℂ (fun χ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential χ) z) ψ) h /
        sourceCanonicalRoot hp hp1 ψ z := by
  rw [fderiv_source_section_eq_joint _ z ψ hjoint.differentiableAt,hjoint.fderiv,
    fderiv_source_section_eq_joint _ z ψ
      (analyticOnNhd_canonicalDiscriminant_periodOne hp hp1 (z,ψ) (mem_univ _)).differentiableAt]
  simp only [ContinuousLinearMap.comp_apply,smul_apply,smul_eq_mul,div_eq_inv_mul]

/-- The other coordinate restriction recovers the spectral integrand. -/
theorem sourceAbelianLogChart_spectral_deriv
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (a : ℂ) (n : ℤ) (z : ℂ) (ψ : CoeffPair p)
    (hjoint : HasFDerivAt (sourceAbelianLogChart hp hp1 φ hφ a n)
      ((sourceCanonicalRoot hp hp1 ψ z)⁻¹ •
        fderiv ℂ (fun u : ℂ × CoeffPair p => canonicalDiscriminant hp (periodOnePotential u.2) u.1) (z,ψ)) (z,ψ)) :
    deriv (fun w : ℂ => sourceAbelianLogChart hp hp1 φ hφ a n (w,ψ)) z =
      deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z / sourceCanonicalRoot hp hp1 ψ z := by
  rw [deriv_spectral_section_eq_fderiv _ z ψ hjoint.differentiableAt,hjoint.fderiv]
  rw [deriv_spectral_section_eq_fderiv (fun u : ℂ × CoeffPair p => canonicalDiscriminant hp (periodOnePotential u.2) u.1)
    z ψ (analyticOnNhd_canonicalDiscriminant_periodOne hp hp1 (z,ψ) (mem_univ _)).differentiableAt]
  simp only [smul_apply,smul_eq_mul,div_eq_inv_mul]

end NLS.ZakharovShabat
