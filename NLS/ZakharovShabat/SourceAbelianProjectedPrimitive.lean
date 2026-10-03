import NLS.ZakharovShabat.SourceAbelianExteriorProduct
import NLS.ComplexAnalysis.MovingSourceLogarithm

/-! # A common abelian primitive normalized at each source's real projection

The real projection supplies a canonical real-source anchor for every
complex source. Straight-source transport gives a continuous logarithm
on an open joint domain. Local logarithm uniqueness then proves complex
analyticity and the exact joint differential, although the projection
used to define the function is only real linear.
-/
noncomputable section
open Set Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def sourceAbelianProjectionAnchor (hp : p ≠ ⊤) (t : ℂ × CoeffPair p) : CoeffPair p × (ℂ × CoeffPair p) :=
  ((sourceRealTypeProjection hp t.2).val,t)

def sourceAbelianProjectedDomain (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p)) : Set (ℂ × CoeffPair p) :=
  sourceAbelianProjectionAnchor hp ⁻¹' movingSourceLogDomain (sourceCanonicalRootJointDomain hp hp1 W)

/-- The common normalization uses the actual primitive at the terminal
potential's real projection, followed by straight-source transport. -/
def sourceAbelianProjectedPrimitive (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (t : ℂ × CoeffPair p) : ℂ :=
  sourceAbelianRadialPrimitive hp hp1 (sourceRealTypeProjection hp t.2) n t

theorem continuous_sourceAbelianProjectionAnchor (hp : p ≠ ⊤) :
    Continuous (sourceAbelianProjectionAnchor (p := p) hp) :=
  ((continuous_subtype_val.comp (sourceRealTypeProjection hp).continuous).comp continuous_snd).prodMk continuous_id

theorem isOpen_sourceAbelianProjectedDomain (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p))
    (hD : IsOpen (sourceCanonicalRootJointDomain hp hp1 W)) : IsOpen (sourceAbelianProjectedDomain hp hp1 W) :=
  (isOpen_movingSourceLogDomain _ hD).preimage (continuous_sourceAbelianProjectionAnchor hp)

theorem sourceAbelianProjectedDomain_start (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p))
    (t : ℂ × CoeffPair p) (ht : t ∈ sourceAbelianProjectedDomain hp hp1 W) :
    (t.1,(sourceRealTypeProjection hp t.2).val) ∈ sourceCanonicalRootJointDomain hp hp1 W :=
  sourceSegmentDomain_start _ _ t ht

theorem sourceAbelianProjectedDomain_end (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p)) :
    sourceAbelianProjectedDomain hp hp1 W ⊆ sourceCanonicalRootJointDomain hp hp1 W := by
  intro t ht
  exact sourceSegmentDomain_end (sourceRealTypeProjection hp t.2).val
    (sourceCanonicalRootJointDomain hp hp1 W) ht

@[simp] theorem mem_sourceAbelianProjectedDomain_real (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p))
    (φ : realTypeSourceSubmodule p) (z : ℂ) :
    (z,φ.val) ∈ sourceAbelianProjectedDomain hp hp1 W ↔ φ.val ∈ W ∧ z ∈ sourceCanonicalRootDomain hp hp1 φ.val := by
  simp only [sourceAbelianProjectedDomain,mem_preimage,sourceAbelianProjectionAnchor,
    sourceRealTypeProjection_subtype,movingSourceLogDomain,mem_ofPred_eq,mem_sourceSegmentDomain_base]
  rfl

@[simp] theorem sourceAbelianProjectedPrimitive_eq_real (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (φ : realTypeSourceSubmodule p) (z : ℂ) :
    sourceAbelianProjectedPrimitive hp hp1 n (z,φ.val) =
      sourceAbelianPrimitive hp hp1 φ.val φ.property z+I*(Real.pi : ℂ)*n := by
  simp [sourceAbelianProjectedPrimitive]

theorem sourceAbelianProjectedPrimitive_eq_zeroIndex_add (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (t : ℂ × CoeffPair p) :
    sourceAbelianProjectedPrimitive hp hp1 n t = sourceAbelianProjectedPrimitive hp hp1 0 t+I*(Real.pi : ℂ)*n := by
  simp only [sourceAbelianProjectedPrimitive,sourceAbelianRadialPrimitive,Int.cast_zero,mul_zero,add_zero]

/-- Moving-anchor regularity and real-source continuity give continuity
before any complex differentiability of the defining projection is used. -/
theorem continuousAt_sourceAbelianProjectedPrimitive (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p))
    (hD : IsOpen (sourceCanonicalRootJointDomain hp hp1 W))
    (hM : AnalyticOnNhd ℂ (sourceFloquetJointMultiplier hp hp1) (sourceCanonicalRootJointDomain hp hp1 W))
    (n : ℤ) (t : ℂ × CoeffPair p) (ht : t ∈ sourceAbelianProjectedDomain hp hp1 W) :
    ContinuousAt (sourceAbelianProjectedPrimitive hp hp1 n) t := by
  have hstart := sourceAbelianProjectedDomain_start hp hp1 W t ht
  have hm : Continuous (fun u : ℂ × CoeffPair p => (u.1,sourceRealTypeProjection hp u.2)) :=
    continuous_fst.prodMk ((sourceRealTypeProjection hp).continuous.comp continuous_snd)
  have hbase : ContinuousAt (fun u : ℂ × CoeffPair p =>
      sourceAbelianPrimitive hp hp1 (sourceRealTypeProjection hp u.2).val (sourceRealTypeProjection hp u.2).property u.1) t := by
    simpa only [Function.comp_def] using!
      ((continuousAt_sourceAbelianPrimitive_joint_real_source hp hp1 (sourceRealTypeProjection hp t.2) t.1 hstart.2).comp
        (f := fun u : ℂ × CoeffPair p => (u.1,sourceRealTypeProjection hp u.2)) (hm.continuousAt (x := t)))
  have hinc := (analyticOnNhd_parametricSourceLogIncrement_moving_anchor (sourceFloquetJointMultiplier hp hp1)
    _ hD hM (fun u hu => sourceFloquetMultiplier_ne_zero hp hp1 u.2 u.1 hu.2)
    (sourceAbelianProjectionAnchor hp t) ht).continuousAt.comp
      (f := sourceAbelianProjectionAnchor hp) ((continuous_sourceAbelianProjectionAnchor hp).continuousAt (x := t))
  exact (hbase.add hinc).add continuousAt_const

theorem sourceAbelianProjectedPrimitive_exp (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p))
    (hM : AnalyticOnNhd ℂ (sourceFloquetJointMultiplier hp hp1) (sourceCanonicalRootJointDomain hp hp1 W))
    (n : ℤ) (t : ℂ × CoeffPair p) (ht : t ∈ sourceAbelianProjectedDomain hp hp1 W) :
    exp (sourceAbelianProjectedPrimitive hp hp1 n t) = exp (I*(Real.pi : ℂ)*n)*sourceFloquetJointMultiplier hp hp1 t :=
  sourceAbelianRadialPrimitive_exp hp hp1 (sourceRealTypeProjection hp t.2) W hM n t ht

/-- The projected definition is locally the normalized holomorphic
Floquet logarithm, so its real-linear anchor does not obstruct analyticity. -/
theorem sourceAbelianProjectedPrimitive_zero_germ (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p))
    (hD : IsOpen (sourceCanonicalRootJointDomain hp hp1 W))
    (hM : AnalyticOnNhd ℂ (sourceFloquetJointMultiplier hp hp1) (sourceCanonicalRootJointDomain hp hp1 W))
    (t : ℂ × CoeffPair p) (ht : t ∈ sourceAbelianProjectedDomain hp hp1 W) :
    normalizedLogChart (sourceFloquetJointMultiplier hp hp1) t (sourceAbelianProjectedPrimitive hp hp1 0 t) =ᶠ[𝓝 t]
      sourceAbelianProjectedPrimitive hp hp1 0 := by
  apply normalizedLogChart_eventually_eq _ _ t (continuousAt_sourceAbelianProjectedPrimitive hp hp1 W hD hM 0 t ht)
  filter_upwards [(isOpen_sourceAbelianProjectedDomain hp hp1 W hD).mem_nhds ht] with u hu
  simpa only [Int.cast_zero,mul_zero,exp_zero,one_mul] using sourceAbelianProjectedPrimitive_exp hp hp1 W hM 0 u hu

theorem sourceAbelianProjectedPrimitive_analytic (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p))
    (hD : IsOpen (sourceCanonicalRootJointDomain hp hp1 W))
    (hM : AnalyticOnNhd ℂ (sourceFloquetJointMultiplier hp hp1) (sourceCanonicalRootJointDomain hp hp1 W))
    (n : ℤ) : AnalyticOnNhd ℂ (sourceAbelianProjectedPrimitive hp hp1 n) (sourceAbelianProjectedDomain hp hp1 W) := by
  intro t ht
  have htD := sourceAbelianProjectedDomain_end hp hp1 W ht
  have hne : sourceFloquetJointMultiplier hp hp1 t ≠ 0 := sourceFloquetMultiplier_ne_zero hp hp1 t.2 t.1 htD.2
  have hlog : sourceFloquetJointMultiplier hp hp1 t/sourceFloquetJointMultiplier hp hp1 t ∈ slitPlane := by
    rw [div_self hne]
    simp
  have h0 := (normalizedLogChart_analyticAt _ t t _ (hM t htD) hlog).congr
    (sourceAbelianProjectedPrimitive_zero_germ hp hp1 W hD hM t ht)
  simpa only [Pi.add_def,sourceAbelianProjectedPrimitive,sourceAbelianRadialPrimitive,Int.cast_zero,mul_zero,add_zero] using!
    h0.add (analyticAt_const (v := I*(Real.pi : ℂ)*n))

theorem sourceAbelianProjectedPrimitive_hasFDerivAt (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p))
    (hD : IsOpen (sourceCanonicalRootJointDomain hp hp1 W))
    (hroot : AnalyticOnNhd ℂ (sourceCanonicalRootJointProduct hp hp1) (sourceCanonicalRootJointDomain hp hp1 W))
    (n : ℤ) (t : ℂ × CoeffPair p) (ht : t ∈ sourceAbelianProjectedDomain hp hp1 W) :
    HasFDerivAt (sourceAbelianProjectedPrimitive hp hp1 n)
      ((sourceCanonicalRoot hp hp1 t.2 t.1)⁻¹ •
        fderiv ℂ (fun u : ℂ × CoeffPair p => canonicalDiscriminant hp (periodOnePotential u.2) u.1) t) t := by
  have hM := sourceFloquetJointMultiplier_analyticOnNhd hp hp1 W hroot
  have htD := sourceAbelianProjectedDomain_end hp hp1 W ht
  have hne : sourceFloquetJointMultiplier hp hp1 t ≠ 0 := sourceFloquetMultiplier_ne_zero hp hp1 t.2 t.1 htD.2
  have hlog : sourceFloquetJointMultiplier hp hp1 t/sourceFloquetJointMultiplier hp hp1 t ∈ slitPlane := by
    rw [div_self hne]
    simp
  have h0 := (normalizedLogChart_sourceFloquet_hasFDerivAt hp hp1 W hD hroot t t
    (sourceAbelianProjectedPrimitive hp hp1 0 t) htD htD hlog).congr_of_eventuallyEq
    (sourceAbelianProjectedPrimitive_zero_germ hp hp1 W hD hM t ht).symm
  simpa only [sourceAbelianProjectedPrimitive,sourceAbelianRadialPrimitive,Int.cast_zero,mul_zero,add_zero] using!
    h0.add_const (I*(Real.pi : ℂ)*n)

end NLS.ZakharovShabat
