import NLS.ZakharovShabat.SourceFullAbelianAllGapMajorants

/-! # Lemma 19.4 on one almost-real source neighborhood

Both actual gap-side limits of `F_n-i*w_n` satisfy the mixed sequence
estimate, locally uniformly on an open connected neighborhood of the
real locus. The neighborhood, local radius, and gap coverage are chosen
before the auxiliary exponent `q>1`. Collapsed gaps use the filled value.
-/
noncomputable section
open Set Metric Filter Topology Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Lemma 19.4 with all indices, both sides of every closed gap, and
uniform bounds on the two majorant sequence norms. The same local ball
works for every finite auxiliary exponent strictly above one. -/
theorem exists_sourceFullAbelian_almostReal_refinedGapBound (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W U : Set (CoeffPair p), IsOpen U ∧ IsConnected U ∧ realTypeSourceLocus p ⊆ U ∧ U ⊆ W ∧
      (∀ n : ℤ, AnalyticOnNhd ℂ (sourceFullAbelianPrimitive hp hp1 W n)
        (sourceCanonicalRootJointDomain hp hp1 U)) ∧
      (∀ (n : ℤ) (z : ℂ), sourceFullAbelianPrimitive hp hp1 W n (z,0) =
        I*sourceStandardRoot hp hp1 (0 : CoeffPair p) n z ∧
        sourceFullAbelianPrimitive hp hp1 W n (z,0) = -I*z+I*(Real.pi:ℂ)*n) ∧
      ∀ φ ∈ U, ∃ r : ℝ, 0 < r ∧ ball φ r ⊆ U ∧
        ∀ q : ℝ≥0∞, q ≠ ⊤ → 1 < q → ∃ M : ℝ, 0 ≤ M ∧ ∀ ψ ∈ ball φ r,
          ∃ Bq : Coeff q, ∃ Bg : Coeff (ENNReal.ofReal (p.toReal/2)),
            ‖Bq‖ ≤ M ∧ ‖Bg‖ ≤ M ∧
            ∀ j : ℤ, ∀ z ∈ sourcePeriodicSegment hp hp1 ψ j, ∀ upper : Bool,
              ∃ b : ℂ, ‖b‖ ≤ ‖sourcePeriodicGapDisplacement hp hp1 ψ j‖*(‖Bq j‖+‖Bg j‖) ∧
                (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) j ≠ 0 →
                  Tendsto (fun z => sourceFullAbelianPrimitive hp hp1 W j (z,ψ)-I*sourceStandardRoot hp hp1 ψ j z)
                    (𝓝[sourceAbelianGapSide hp hp1 ψ j upper] z) (𝓝 b)) ∧
                (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) j = 0 →
                  sourceFullAbelianPrimitive hp hp1 W j (z,ψ)-I*sourceStandardRoot hp hp1 ψ j z = b) := by
  obtain ⟨W,_,_,hlocal⟩ := exists_sourceFullAbelian_all_gap_majorants hp hp1
  choose C V hV hφV hVC hmajor using hlocal
  let S : Set (CoeffPair p) := ⋃ φ : realTypeSourceSubmodule p, V φ
  have hS : IsOpen S := isOpen_iUnion hV
  have hrealS : realTypeSourceLocus p ⊆ S :=
    fun ψ hψ => mem_iUnion.mpr ⟨⟨ψ,hψ⟩,hφV ⟨ψ,hψ⟩⟩
  let U := connectedComponentIn S (0 : CoeffPair p)
  have hzero : (0 : CoeffPair p) ∈ realTypeSourceLocus p := by simp [realTypeSourceLocus]
  have hrealU : realTypeSourceLocus p ⊆ U :=
    isConnected_realTypeSourceLocus.isPreconnected.subset_connectedComponentIn hzero hrealS
  have hUS : U ⊆ S := connectedComponentIn_subset S 0
  have hU : IsOpen U := hS.connectedComponentIn
  refine ⟨W,U,hU,isConnected_connectedComponentIn_iff.mpr (hrealS hzero),hrealU,?_,?_,?_,?_⟩
  · intro ψ hψ
    obtain ⟨φ,hφ⟩ := mem_iUnion.mp (hUS hψ)
    exact (C φ).discs.source_subset (hVC φ hφ)
  · intro n t ht
    obtain ⟨φ,hφ⟩ := mem_iUnion.mp (hUS ht.1)
    exact (C φ).full_analytic n t ⟨hVC φ hφ,ht.2⟩
  · intro n z
    obtain ⟨D⟩ := (C (0 : realTypeSourceSubmodule p)).charts 0 (hVC 0 (hφV 0))
    exact ⟨sourceFullAbelianPrimitive_zero_eq_I_mul_standardRoot D n z,
      sourceFullAbelianPrimitive_zero D n z⟩
  intro χ hχ
  obtain ⟨φ,hφ⟩ := mem_iUnion.mp (hUS hχ)
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp ((hU.inter (hV φ)).mem_nhds ⟨hχ,hφ⟩)
  refine ⟨r,hr,fun ψ hψ => (hsub hψ).1,?_⟩
  intro q hq hq1
  obtain ⟨M,hM,hb⟩ := hmajor φ q hq hq1
  refine ⟨M,hM,?_⟩
  intro ψ hψ
  have hψV := (hsub hψ).2
  have hψC := hVC φ hψV
  obtain ⟨Bq,Bg,hBq,hBg,hbound⟩ := hb ψ hψV
  refine ⟨Bq,Bg,hBq,hBg,?_⟩
  intro j z hz upper
  obtain ⟨θ,hθ,rfl⟩ := exists_sourcePeriodicSegment_cosine_parameter hp hp1 ψ j z hz
  refine ⟨(C φ).gapBoundary j ψ θ upper-I*sourceStandardRootGapBoundary hp hp1 ψ j θ upper,
    hbound j θ hθ upper,?_,?_⟩
  · exact fun hg => (C φ).fullPrimitive_sub_root_tendsto_gapBoundary j ψ hψC hg θ hθ upper
  · intro hg
    rw [(C φ).fullPrimitive_sub_root_eq_zero_of_collapsed j ψ hψC hg θ,
      (C φ).gapBoundary_eq_zero_of_collapsed j ψ hg θ upper]
    simp only [sourceStandardRootGapBoundary,sourceStandardRootHalfGap,hg,zero_div,
      zero_mul,mul_zero,sub_self]

end NLS.ZakharovShabat
