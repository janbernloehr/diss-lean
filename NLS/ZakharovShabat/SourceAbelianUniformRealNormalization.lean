import NLS.ZakharovShabat.SourceAbelianAlmostRealSpectralContinuation

/-! # The full spectral continuation retains the actual real values

The common exterior is nonempty. Its prescribed real normalization
therefore determines each real-source spectral primitive everywhere,
including analytically filled collapsed gaps.
-/
noncomputable section
open Set Metric Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceAbelianUniformDiscFamily
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}

theorem exterior_nonempty (D : SourceAbelianUniformDiscFamily hp hp1 W) : D.exterior.Nonempty := by
  let z : ℂ := D.center 0+(D.outer 0:ℂ)
  have hpos : 0 < D.outer 0 := (D.inner_pos 0).trans (D.inner_lt 0)
  have hdist : dist z (D.center 0) = D.outer 0 := by
    simp only [z,dist_eq_norm,add_sub_cancel_left,norm_real,Real.norm_eq_abs,abs_of_pos hpos]
  have hzcl : z ∈ closure (ball (D.center 0) (D.outer 0)) := by
    rw [closure_ball _ (ne_of_gt hpos)]
    exact mem_closedBall.mpr hdist.le
  refine ⟨z,?_⟩
  intro hz
  obtain ⟨j,hj⟩ := mem_iUnion.mp hz
  by_cases he : j = 0
  · subst j
    have hle := mem_closedBall.mp hj
    rw [hdist] at hle
    exact (not_le_of_gt (D.inner_lt 0)) hle
  · exact Set.disjoint_left.mp ((D.disjoint 0 j (fun h => he h.symm)).closure_left isOpen_ball)
      hzcl (closedBall_subset_ball (D.inner_lt j) hj)

/-- Agreement with the prescribed exterior fixes the real-source
primitive on its whole filled spectral domain. -/
theorem eq_real_of_exterior (D : SourceAbelianUniformDiscFamily hp hp1 W)
    (φ : realTypeSourceSubmodule p) (hφ : φ.val ∈ ball D.source.val D.sourceRadius) (n : ℤ)
    (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F (sourceOpenGapComplement hp hp1 φ.val))
    (hext : EqOn F (fun z => sourceAbelianProjectedPrimitive hp hp1 n (z,φ.val)) D.exterior) :
    EqOn F (fun z => sourceAbelianPrimitive hp hp1 φ.val φ.property z+I*(Real.pi : ℂ)*n)
      (sourceOpenGapComplement hp hp1 φ.val) := by
  let G : ℂ → ℂ := fun z => sourceAbelianPrimitive hp hp1 φ.val φ.property z+I*(Real.pi : ℂ)*n
  have hG : AnalyticOnNhd ℂ G (sourceOpenGapComplement hp hp1 φ.val) :=
    fun z hz => (sourceAbelianPrimitive_analytic hp hp1 φ.val φ.property z hz).add analyticAt_const
  have hsub := sourceCanonicalRootDomain_subset_openGapComplement hp hp1 φ.val
  obtain ⟨a,ha⟩ := D.exterior_nonempty
  have haroot : a ∈ sourceCanonicalRootDomain hp hp1 φ.val := by
    rw [D.rootDomain_eq_union φ.val hφ]
    exact Or.inl ha
  have hfg : F =ᶠ[𝓝 a] G := by
    filter_upwards [D.isOpen_exterior.mem_nhds ha] with z hz
    exact (hext hz).trans (sourceAbelianProjectedPrimitive_eq_real hp hp1 n φ z)
  have heq := (hF.mono hsub).eqOn_of_preconnected_of_eventuallyEq (hG.mono hsub)
    (isConnected_sourceCanonicalRootDomain_of_realType hp hp1 φ.val φ.property).isPreconnected haroot hfg
  apply continuous_eqOn_of_dense_on_open (sourceCanonicalRootDomain hp hp1 φ.val) _
    (dense_sourceCanonicalRootDomain_complex hp hp1 φ.val)
    (isOpen_sourceOpenGapComplement_of_realType hp hp1 φ.val φ.property) _ _ hF.continuousOn hG.continuousOn
  intro z hz
  exact heq hz.2

end NLS.ZakharovShabat.SourceAbelianUniformDiscFamily
