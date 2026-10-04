import NLS.ZakharovShabat.SourceFullAbelianGapBoundary
import NLS.ZakharovShabat.SourceCriticalRootGapUniformBound

/-! # Uniform linear gap estimate for the full abelian primitive

Around every real source, one neighborhood, tail cutoff and positive
constant control both boundary values on all distant complex gaps.
The profiles are actual limits of the canonical normalized primitive.
-/
noncomputable section
open Set Metric Filter Topology Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The gap estimate of Lemma 19.1(iii), with one constant for both
sides, every angle, every sufficiently large signed index, and every
complex source in a common neighborhood of the real base source. -/
theorem exists_sourceFullAbelian_local_uniform_gap_bound (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧
      ∀ φ : realTypeSourceSubmodule p,
        ∃ C : SourceFullAbelianUniformCauchyFamily hp hp1 W,
        ∃ V : Set (CoeffPair p), IsOpen V ∧ φ.val ∈ V ∧
          V ⊆ ball C.discs.source.val C.discs.sourceRadius ∧
          ∃ K : ℕ, ∃ B : ℝ, 0 < B ∧
            ∀ ψ ∈ V, ∀ j : ℤ, K ≤ j.natAbs → ∀ θ ∈ Icc (0:ℝ) Real.pi, ∀ upper : Bool,
              ‖C.gapBoundary j ψ θ upper‖ ≤ B*‖sourcePeriodicGapDisplacement hp hp1 ψ j‖ ∧
              (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) j ≠ 0 →
                Tendsto (fun z => sourceFullAbelianPrimitive hp hp1 W j (z,ψ))
                  (𝓝[sourceAbelianGapSide hp hp1 ψ j upper]
                    (sourceStandardRootMidpoint hp hp1 ψ j+sourceStandardRootHalfGap hp hp1 ψ j*(Real.cos θ:ℂ)))
                  (𝓝 (C.gapBoundary j ψ θ upper))) := by
  obtain ⟨W,hW,hreal,hC⟩ := exists_sourceFullAbelianUniformCauchyFamilies hp hp1
  refine ⟨W,hW,hreal,?_⟩
  intro φ
  obtain ⟨C,hφ⟩ := hC φ
  obtain ⟨V,hV,hφV,K,B,hB,hb⟩ := exists_local_uniform_sourceCriticalRootGapNumerator_bound hp hp1 φ.val φ.property
  refine ⟨C,V ∩ ball C.discs.source.val C.discs.sourceRadius,hV.inter isOpen_ball,
    ⟨hφV,by rw [hφ]; exact mem_ball_self C.discs.sourceRadius_pos⟩,inter_subset_right,
    K,B*Real.pi,mul_pos hB Real.pi_pos,?_⟩
  intro ψ hψ j hj θ hθ upper
  constructor
  · have h := C.gapBoundary_norm_le j ψ hψ.2 (B*‖sourcePeriodicGapDisplacement hp hp1 ψ j‖)
      (mul_nonneg hB.le (norm_nonneg _)) (hb ψ hψ.1 j hj) θ hθ upper
    simpa only [mul_assoc,mul_comm,mul_left_comm] using h
  · exact fun hgap => C.fullPrimitive_tendsto_gapBoundary j ψ hψ.2 hgap θ hθ upper

/-- An open connected almost-real neighborhood carries locally uniform
linear gap bounds for the actual canonical primitive. Noncollapsed gaps
use side limits; collapsed gaps use the value of the filled function. -/
theorem exists_sourceFullAbelian_almostReal_uniformGapBound (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W U : Set (CoeffPair p), IsOpen U ∧ IsConnected U ∧ realTypeSourceLocus p ⊆ U ∧ U ⊆ W ∧
      (∀ n : ℤ, AnalyticOnNhd ℂ (sourceFullAbelianPrimitive hp hp1 W n)
        (sourceCanonicalRootJointDomain hp hp1 U)) ∧
      ∀ φ ∈ U, ∃ r : ℝ, 0 < r ∧ ball φ r ⊆ U ∧ ∃ K : ℕ, ∃ B : ℝ, 0 < B ∧
        ∀ ψ ∈ ball φ r, ∀ j : ℤ, K ≤ j.natAbs → ∀ z ∈ sourcePeriodicSegment hp hp1 ψ j, ∀ upper : Bool,
          ∃ b : ℂ, ‖b‖ ≤ B*‖sourcePeriodicGapDisplacement hp hp1 ψ j‖ ∧
            (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) j ≠ 0 →
              Tendsto (fun z => sourceFullAbelianPrimitive hp hp1 W j (z,ψ))
                (𝓝[sourceAbelianGapSide hp hp1 ψ j upper] z) (𝓝 b)) ∧
            (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) j = 0 →
              sourceFullAbelianPrimitive hp hp1 W j (z,ψ) = b) := by
  obtain ⟨W,_,_,hlocal⟩ := exists_sourceFullAbelian_local_uniform_gap_bound hp hp1
  choose C V hV hφV hVC K B hB hb using hlocal
  let S : Set (CoeffPair p) := ⋃ φ : realTypeSourceSubmodule p, V φ
  have hS : IsOpen S := isOpen_iUnion hV
  have hrealS : realTypeSourceLocus p ⊆ S := fun ψ hψ => mem_iUnion.mpr ⟨⟨ψ,hψ⟩,hφV ⟨ψ,hψ⟩⟩
  let U := connectedComponentIn S (0 : CoeffPair p)
  have hzero : (0 : CoeffPair p) ∈ realTypeSourceLocus p := by simp [realTypeSourceLocus]
  have hrealU : realTypeSourceLocus p ⊆ U :=
    isConnected_realTypeSourceLocus.isPreconnected.subset_connectedComponentIn hzero hrealS
  have hUS : U ⊆ S := connectedComponentIn_subset S 0
  have hU : IsOpen U := hS.connectedComponentIn
  refine ⟨W,U,hU,isConnected_connectedComponentIn_iff.mpr (hrealS hzero),hrealU,?_,?_,?_⟩
  · intro ψ hψ
    obtain ⟨φ,hφ⟩ := mem_iUnion.mp (hUS hψ)
    exact (C φ).discs.source_subset (hVC φ hφ)
  · intro n t ht
    obtain ⟨φ,hφ⟩ := mem_iUnion.mp (hUS ht.1)
    exact (C φ).full_analytic n t ⟨hVC φ hφ,ht.2⟩
  intro χ hχ
  obtain ⟨φ,hφ⟩ := mem_iUnion.mp (hUS hχ)
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp ((hU.inter (hV φ)).mem_nhds ⟨hχ,hφ⟩)
  refine ⟨r,hr,fun ψ hψ => (hsub hψ).1,K φ,B φ,hB φ,?_⟩
  intro ψ hψ j hj z hz upper
  obtain ⟨θ,hθ,rfl⟩ := exists_sourcePeriodicSegment_cosine_parameter hp hp1 ψ j z hz
  have hψV := (hsub hψ).2
  have h := hb φ ψ hψV j hj θ hθ upper
  exact ⟨(C φ).gapBoundary j ψ θ upper,h.1,h.2,
    fun hgap => (C φ).fullPrimitive_eq_gapBoundary_of_collapsed j ψ (hVC φ hψV) hgap θ upper⟩

end NLS.ZakharovShabat
