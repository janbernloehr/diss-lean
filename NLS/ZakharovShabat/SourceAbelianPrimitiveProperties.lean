import NLS.ZakharovShabat.SourceAbelianPrimitive

/-! # The filled abelian primitive and its regular derivative

The Floquet identity persists through collapsed gaps. Differentiating
it identifies the extended derivative with the multiplier's logarithmic
derivative. Smooth paths may now pass directly through collapsed points.
-/
noncomputable section
open Set Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The Floquet logarithm identity holds on the entire enlarged domain,
including at the filled endpoints. -/
theorem sourceAbelianPrimitive_exp
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (z : ℂ)
    (hz : z ∈ sourceOpenGapComplement hp hp1 φ) :
    exp (sourceAbelianPrimitive hp hp1 φ hφ z) = sourceFloquetMultiplier hp hp1 φ z := by
  have hroot (w : ℂ) (hw : w ∈ sourceCanonicalRootDomain hp hp1 φ) :
      exp (sourceAbelianPrimitive hp hp1 φ hφ w) = sourceFloquetMultiplier hp hp1 φ w := by
    rw [sourceAbelianPrimitive_eq_global hp hp1 φ hφ hw]
    exact sourceAbelianGlobalPrimitive_exp hp hp1 φ hφ w hw
  by_cases hi : z.im = 0
  · have hU := isOpen_sourceOpenGapComplement_of_realType hp hp1 φ hφ
    exact eq_at_real_of_upperHalfPlane_extension
      (fun w => exp (sourceAbelianPrimitive hp hp1 φ hφ w))
      (sourceFloquetMultiplier hp hp1 φ) (sourceFloquetMultiplier hp hp1 φ)
      _ _ z hi hU hU hz hz
      (continuous_exp.continuousAt.comp (sourceAbelianPrimitive_analytic hp hp1 φ hφ z hz).continuousAt)
      (sourceFloquetMultiplier_analyticOnNhd_openGapComplement hp hp1 φ hφ z hz).continuousAt
      (fun w hw => hroot w (sourceAbelianHalfPlane_subset_rootDomain hp hp1 φ hφ true hw.2))
      (fun _ _ => rfl)
  · exact hroot z (sourceCanonicalRootDomain_of_im_ne_zero hp hp1 φ hφ z hi)

/-- The derivative at every point, including collapsed gaps, is the
regular Floquet logarithmic derivative. -/
theorem sourceAbelianPrimitive_hasDerivAt
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (z : ℂ)
    (hz : z ∈ sourceOpenGapComplement hp hp1 φ) :
    HasDerivAt (sourceAbelianPrimitive hp hp1 φ hφ) (sourceFloquetLogDerivative hp hp1 φ z) z := by
  have hf := (sourceAbelianPrimitive_analytic hp hp1 φ hφ z hz).differentiableAt.hasDerivAt
  have hm : HasDerivAt (sourceFloquetMultiplier hp hp1 φ)
      (exp (sourceAbelianPrimitive hp hp1 φ hφ z)*deriv (sourceAbelianPrimitive hp hp1 φ hφ) z) z := by
    apply hf.cexp.congr_of_eventuallyEq
    filter_upwards [(isOpen_sourceOpenGapComplement_of_realType hp hp1 φ hφ).mem_nhds hz] with w hw
    exact (sourceAbelianPrimitive_exp hp hp1 φ hφ w hw).symm
  have he := hm.deriv
  rw [sourceAbelianPrimitive_exp hp hp1 φ hφ z hz] at he
  have hq : sourceFloquetLogDerivative hp hp1 φ z = deriv (sourceAbelianPrimitive hp hp1 φ hφ) z := by
    rw [sourceFloquetLogDerivative,he]
    field_simp [sourceFloquetMultiplier_ne_zero_openGapComplement hp hp1 φ hφ z hz]
  rw [hq]
  exact hf

/-- Away from all cuts, the derivative remains the literal canonical
quotient from the dissertation. -/
theorem sourceAbelianPrimitive_hasDerivAt_quotient
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (z : ℂ)
    (hz : z ∈ sourceCanonicalRootDomain hp hp1 φ) :
    HasDerivAt (sourceAbelianPrimitive hp hp1 φ hφ)
      (deriv (canonicalDiscriminant hp (periodOnePotential φ)) z / sourceCanonicalRoot hp hp1 φ z) z := by
  rw [← sourceFloquetLogDerivative_eq_criticalRootRatio hp hp1 φ hφ z hz]
  exact sourceAbelianPrimitive_hasDerivAt hp hp1 φ hφ z
    (sourceCanonicalRootDomain_subset_openGapComplement hp hp1 φ hz)

/-- All endpoint limits remain valid for approaches in the enlarged
domain, including paths through other collapsed gaps. -/
theorem sourceAbelianPrimitive_endpoint_limit
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) (a : ℂ)
    (ha : a ∈ ({canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n,
      canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n} : Set ℂ)) :
    Tendsto (sourceAbelianPrimitive hp hp1 φ hφ)
      (𝓝[sourceOpenGapComplement hp hp1 φ] a) (𝓝 (-I*(Real.pi : ℂ)*n)) := by
  have hclosure : closure (sourceCanonicalRootDomain hp hp1 φ) = univ := by
    apply eq_univ_of_forall
    intro z
    exact mem_closure_iff_nhdsWithin_neBot.mpr (nhdsWithin_sourceCanonicalRootDomain_neBot hp hp1 φ hφ z)
  have h := tendsto_continuous_extension_on_closure
    (sourceAbelianGlobalPrimitive hp hp1 φ hφ) (sourceAbelianPrimitive hp hp1 φ hφ)
    (sourceCanonicalRootDomain hp hp1 φ) (sourceOpenGapComplement hp hp1 φ) a (-I*(Real.pi : ℂ)*n)
    (isOpen_sourceOpenGapComplement_of_realType hp hp1 φ hφ)
    (sourceAbelianPrimitive_analytic hp hp1 φ hφ).continuousOn
    (fun _ hw => sourceAbelianPrimitive_eq_global hp hp1 φ hφ hw.2)
    (sourceAbelianGlobalPrimitive_endpoint_limit hp hp1 φ hφ n a ha)
  simpa only [hclosure,inter_univ] using h

/-- The regular one-form integrates to the endpoint difference along
any smooth path avoiding noncollapsed cuts; collapsed points are allowed. -/
theorem sourceAbelianPrimitive_pathIntegral_eq_sub
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) {a b : ℂ}
    (γ : Path a b) (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hγD : ∀ t : unitInterval, γ t ∈ sourceOpenGapComplement hp hp1 φ) :
    CurveIntegrable (holomorphicOneForm (sourceFloquetLogDerivative hp hp1 φ)) γ ∧
    (∫ᶜ z in γ, holomorphicOneForm (sourceFloquetLogDerivative hp hp1 φ) z) =
      sourceAbelianPrimitive hp hp1 φ hφ b-sourceAbelianPrimitive hp hp1 φ hφ a := by
  have hω : ContinuousOn (holomorphicOneForm (sourceFloquetLogDerivative hp hp1 φ))
      (sourceOpenGapComplement hp hp1 φ) :=
    (sourceFloquetLogDerivative_analyticOnNhd hp hp1 φ hφ).continuousOn.smul continuousOn_const
  have hint := hω.curveIntegrable_of_contDiffOn hγ hγD
  exact ⟨hint,curveIntegral_eq_sub_of_primitive _ (sourceAbelianPrimitive hp hp1 φ hφ)
    (sourceOpenGapComplement hp hp1 φ) (sourceAbelianPrimitive_hasDerivAt hp hp1 φ hφ)
    γ hγ (fun t ht => by simpa only [Path.extend_apply γ ht] using hγD ⟨t,ht⟩) hint⟩

/-- At the free source every gap is collapsed, so the enlarged domain
is the whole complex plane. -/
@[simp] theorem sourceOpenGapComplement_zero (hp : p ≠ ⊤) (hp1 : 1 < p) :
    sourceOpenGapComplement hp hp1 (0 : CoeffPair p) = univ := by
  ext z
  simp [sourceOpenGapComplement,periodOnePotential]

/-- Lemma 19.1(vi) on the whole plane: filling all free periodic points
produces exactly the entire function `-i*lambda`. -/
@[simp] theorem sourceAbelianPrimitive_zero (hp : p ≠ ⊤) (hp1 : 1 < p) :
    sourceAbelianPrimitive hp hp1 (0 : CoeffPair p) (by simp) = fun z => -I*z := by
  funext z
  let := nhdsWithin_sourceCanonicalRootDomain_neBot hp hp1 (0 : CoeffPair p) (by simp) z
  have hlim : Tendsto (sourceAbelianGlobalPrimitive hp hp1 (0 : CoeffPair p) (by simp))
      (𝓝[sourceCanonicalRootDomain hp hp1 0] z) (𝓝 (-I*z)) := by
    have hc : Continuous (fun w : ℂ => -I*w) := continuous_const.mul continuous_id
    apply (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact (sourceAbelianGlobalPrimitive_zero hp hp1 hw).symm
  simpa only [sourceAbelianPrimitive] using! hlim.limUnder_eq

/-- The free regular logarithmic derivative is `-i` even at lattice
points, where the literal critical-root quotient has denominator zero. -/
@[simp] theorem sourceFloquetLogDerivative_zero (hp : p ≠ ⊤) (hp1 : 1 < p) (z : ℂ) :
    sourceFloquetLogDerivative hp hp1 (0 : CoeffPair p) z = -I := by
  have h := sourceAbelianPrimitive_hasDerivAt hp hp1 (0 : CoeffPair p) (by simp) z (by simp)
  rw [sourceAbelianPrimitive_zero] at h
  exact h.unique (by simpa only [mul_one] using! (hasDerivAt_id z).const_mul (-I))

end NLS.ZakharovShabat
