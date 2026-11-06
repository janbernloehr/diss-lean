import NLS.Articles.KdVPseudomeasures.MainTheorem14
import NLS.Articles.KdVPseudomeasures.SourceWeakStarTopology

/-! The literal two assertions of Remark 1.5: the full Hminus-one
isospectral image is its modulus torus, and the endpoint fiber has the
same weak-star and lower norm topologies. -/
noncomputable section
open Set NLS.KdV
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures

/-- Action products on the physical real form are exactly fixed moduli,
including both signed coordinates and the zero mode. -/
theorem mem_hillRealNativeActionTorus_iff_norms (q : HillRealMeanZeroSource) (z : HillRealSignedTarget) :
    z ∈ hillRealNativeActionTorus q ↔
      ∀ k : ℤ, ‖z.val.val.val k‖=‖(hillRealSignedMap q).val.val.val k‖ := by
  have hbase := hillRealSignedMap_mem_actionTorus_of_discriminant_eq q q rfl
  constructor
  · intro hz
    have hpos (n : ℕ+) : ‖z.val.val.val (n:ℤ)‖=‖(hillRealSignedMap q).val.val.val (n:ℤ)‖ := by
      apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      have he := (hz n).trans (hbase n).symm
      rw [z.property (n:ℤ),(hillRealSignedMap q).property (n:ℤ)] at he
      have hh := congrArg Complex.re he
      simpa only [Complex.mul_conj,Complex.ofReal_re,Complex.normSq_eq_norm_sq] using hh
    intro k
    by_cases hk : k=0
    · subst k
      have hz0 : z.val.val.val 0=0 := z.val.property
      have hq0 : (hillRealSignedMap q).val.val.val 0=0 := (hillRealSignedMap q).val.property
      rw [hz0,hq0]
    by_cases hp : 0<k
    · let n : ℕ+ := ⟨k.toNat,by omega⟩
      have hn : (n:ℤ)=k := Int.toNat_of_nonneg hp.le
      simpa only [hn] using hpos n
    · let n : ℕ+ := ⟨(-k).toNat,by omega⟩
      have hn : (n:ℤ)=-k := Int.toNat_of_nonneg (by omega)
      have hh := hpos n
      rw [hn,z.property k,(hillRealSignedMap q).property k] at hh
      simpa only [Complex.norm_conj] using hh
  · intro hz n
    have he : z.val.val.val (n:ℤ)*z.val.val.val (-(n:ℤ))=
        (hillRealSignedMap q).val.val.val (n:ℤ)*(hillRealSignedMap q).val.val.val (-(n:ℤ)) := by
      rw [z.property (n:ℤ),(hillRealSignedMap q).property (n:ℤ),Complex.mul_conj,Complex.mul_conj,
        Complex.normSq_eq_norm_sq,Complex.normSq_eq_norm_sq,hz (n:ℤ)]
    exact he.trans (hbase n)

theorem sourceRemark1_5_torus (q : HillRealMeanZeroSource) :
    hillRealSignedMap '' {p : HillRealMeanZeroSource | hillRealDiscriminantData p=hillRealDiscriminantData q}=
      {z : HillRealSignedTarget | ∀ k : ℤ, ‖z.val.val.val k‖=‖(hillRealSignedMap q).val.val.val k‖} := by
  rw [image_hillRealDiscriminant_fiber_eq_actionTorus]
  ext z
  exact mem_hillRealNativeActionTorus_iff_norms q z

theorem sourceRemark1_5_topologies (r : ℝ) (hr : AdmissiblePredualOrder r) (q : Potential r)
    (t : ℝ) {p : ℝ≥0∞} [Fact (1≤p)] (hp : p≠⊤) (h : 1<(-r-t)*p.toReal) :
    Topology.IsEmbedding (fun P : originalIsospectralEndpointSet (sourceOriginalPotential r hr q) r =>
      sourceLowerDistribution r t hp h P.val) := by
  have hg := sourceCanonicalGapValues_mem r hr q
  rw [← originalCanonicalGapValues_sourceOriginalPotential r hr q] at hg
  exact isEmbedding_sourceLowerDistribution_on_bounded r t hp h _
    (potentialNormBounded_originalIsospectralEndpointSet (sourceOriginalPotential r hr q) r hr hg)

/-- Full Remark 1.5, for every original Hminus-one source and all admissible
endpoint fibers. The topology assertion holds for every finite Banach p. -/
theorem sourceRemark1_5 :
    (∀ q : HillRealMeanZeroSource,
      hillRealSignedMap '' {p : HillRealMeanZeroSource | hillRealDiscriminantData p=hillRealDiscriminantData q}=
        {z : HillRealSignedTarget | ∀ k : ℤ, ‖z.val.val.val k‖=‖(hillRealSignedMap q).val.val.val k‖}) ∧
    (∀ (r : ℝ) (hr : AdmissiblePredualOrder r) (q : Potential r),
      ∃ C : ℝ, 0≤C ∧ ∀ P : OriginalHminusOnePotential,
        P ∈ originalIsospectralSet (sourceOriginalPotential r hr q) →
        ∃ p : Potential r, sourceOriginalPotential r hr p=P ∧ ‖p.val‖≤C) ∧
    (∀ (r : ℝ) (hr : AdmissiblePredualOrder r) (q : Potential r)
      (t : ℝ) (p : ℝ≥0∞) [Fact (1≤p)] (hp : p≠⊤) (h : 1<(-r-t)*p.toReal),
      Topology.IsEmbedding (fun P : originalIsospectralEndpointSet (sourceOriginalPotential r hr q) r =>
        sourceLowerDistribution r t hp h P.val)) :=
  ⟨sourceRemark1_5_torus,sourceTheorem1_4.full_original_isospectral_endpoint_bound,
    fun r hr q t _ _ hp h => sourceRemark1_5_topologies r hr q t hp h⟩

end NLS.Articles.KdVPseudomeasures
