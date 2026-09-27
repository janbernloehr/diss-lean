import NLS.ZakharovShabat.SourceNormalizedActionTailBound
import NLS.ZakharovShabat.SourceSingleRootQuotientAsymptoticDiscSup
import NLS.SequenceSpaces.Multiplier
import NLS.SequenceSpaces.ExponentEmbedding

/-!
# Sequence majorants for the normalized action factor

The critical-to-midpoint offset is the squared periodic gap times an
`ℓp` quotient. Therefore it belongs to every Banach sequence exponent
at least `p/2`. This permits the deleted-root product estimate to use
an exponent `q > 1`: choose `q = p/2` when `p > 2`, and any `q > 1`
when `p ≤ 2`. The resulting factor error has `ℓq + ℓ^(p/2)`
majorants along all sufficiently distant selected gaps.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The critical-to-midpoint offset at a Banach exponent containing
the squared-gap sequence. -/
def sourceCriticalMidpointOffsetAtExponent
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (hhalf : ENNReal.ofReal (p.toReal/2) ≤ q)
    (ψ : CoeffPair p) : Coeff q :=
  Coeff.multiplier
    (Coeff.exponentInclusion (le_top : p ≤ ⊤)
      (sourceCriticalGapQuotient hp hp1 ψ))
    ⟨fun n => sourcePeriodicSquaredGapCoeff hp hp1 ψ n,
      (lp.memℓp (sourcePeriodicSquaredGapCoeff hp hp1 ψ)).of_exponent_ge hhalf⟩

@[simp] theorem sourceCriticalMidpointOffsetAtExponent_apply
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (hhalf : ENNReal.ofReal (p.toReal/2) ≤ q)
    (ψ : CoeffPair p) (n : ℤ) :
    sourceCriticalMidpointOffsetAtExponent hp hp1 hhalf ψ n =
      (sourcePeriodicGapDisplacement hp hp1 ψ n)^2 *
        sourceCriticalGapQuotient hp hp1 ψ n := by
  simp only [sourceCriticalMidpointOffsetAtExponent,
    Coeff.multiplier_apply,Coeff.exponentInclusion_apply,
    sourcePeriodicSquaredGapCoeff_apply]
  ring

/-- On the common almost-real domain, this coefficient sequence is
the actual indexed critical-to-midpoint offset. -/
theorem exists_global_sourceCriticalMidpointOffsetAtExponent_eq
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (hhalf : ENNReal.ofReal (p.toReal/2) ≤ q) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧
      realTypeSourceLocus p ⊆ W ∧
      ∀ ψ ∈ W, ∀ n : ℤ,
        canonicalCriticalPoints hp hp1 (periodOnePotential ψ)
            (periodOnePotential_mem ψ) n -
          canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
            (periodOnePotential_mem ψ) n =
          sourceCriticalMidpointOffsetAtExponent hp hp1 hhalf ψ n := by
  obtain ⟨W,hWopen,_,hreal,hdata⟩ :=
    exists_global_sourceCriticalPoints_midpoint_gap_sq_exact hp hp1
  refine ⟨W,hWopen,hreal,?_⟩
  intro ψ hψ n
  simpa only [sourceCriticalMidpointOffsetAtExponent_apply,
    sourceCriticalGapQuotient_apply] using (hdata ψ hψ n).2

/-- The complementary factor on the actual cosine gap path has
`ℓq + ℓ^(p/2)` pointwise majorants at all sufficiently distant
indices. The exponent `q` can be any finite Banach exponent strictly
above one and at least `p/2`. -/
theorem exists_local_sourceNormalizedAction_factor_sequenceMajorants
    [Fact (1 ≤ q)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (hq1 : 1 < q) (hq : q ≠ ⊤)
    (hhalf : ENNReal.ofReal (p.toReal/2) ≤ q)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∃ K : ℕ, ∀ ψ ∈ V,
        ∃ Bq : Coeff q, ∃ Bg : Coeff (ENNReal.ofReal (p.toReal/2)),
          ∀ n : ℤ, K ≤ n.natAbs → ∀ θ : ℝ,
            ‖I * sourceCriticalRootRatioExtension hp hp1 n ψ
              (sourceStandardRootMidpoint hp hp1 ψ n +
                sourceStandardRootHalfGap hp hp1 ψ n * (Real.cos θ:ℂ)) - 1‖ ≤
              ‖Bq n‖ + ‖Bg n‖ := by
  obtain ⟨N,ε,_,_,V₁,hV₁open,_,hφV₁,C,R,H,hC,hR,hH,K₁,hNK,hmajor⟩ :=
    exists_local_sourceSingleRootQuotientDiscMajorants
      hp hp1 hq1 hq φ hφ
  obtain ⟨N₂,V₂,hV₂open,hφV₂,htail⟩ :=
    exists_uniform_source_tail_isolation hp hp1 φ
  obtain ⟨W,hWopen,hWreal,hOffset⟩ :=
    exists_global_sourceCriticalMidpointOffsetAtExponent_eq hp hp1 hhalf
  let V := (V₁ ∩ V₂) ∩ W
  let K := max K₁ (N₂+1)
  refine ⟨V,(hV₁open.inter hV₂open).inter hWopen,
    ⟨⟨hφV₁,hφV₂⟩,hWreal hφ⟩,K,?_⟩
  intro ψ hψ
  let a : Coeff p := canonicalCriticalDisplacement hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ)
  let α : Coeff q := sourceCriticalMidpointOffsetAtExponent
    hp hp1 hhalf ψ
  have hα (m : ℤ) :
      displacedRoots a m -
        canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
          (periodOnePotential_mem ψ) m = α m := by
    have hcrit : displacedRoots a m =
        canonicalCriticalPoints hp hp1 (periodOnePotential ψ)
          (periodOnePotential_mem ψ) m := by
      simp only [a,displacedRoots,canonicalCriticalDisplacement_apply]
      ring
    rw [hcrit]
    exact hOffset ψ hψ.2 m
  obtain ⟨Bq,Bg,hpoint,_,_⟩ :=
    hmajor ψ hψ.1.1 a α hα
  refine ⟨Bq,Bg,?_⟩
  intro n hn θ
  have hK₁ : K₁ ≤ n.natAbs := by dsimp [K] at hn; omega
  have hN : N < n.natAbs := hNK.trans_le hK₁
  have hN₂ : N₂ < n.natAbs := by dsimp [K] at hn; omega
  let z := sourceStandardRootMidpoint hp hp1 ψ n +
    sourceStandardRootHalfGap hp hp1 ψ n * (Real.cos θ:ℂ)
  have hend := htail ψ hψ.1.2 n hN₂
  have hconv : Convex ℝ (refinedResonantDisk n) := by
    unfold refinedResonantDisk
    exact convex_ball _ _
  have hsegment : sourcePeriodicSegment hp hp1 ψ n ⊆
      refinedResonantDisk n := by
    change segment ℝ
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n)
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n) ⊆ refinedResonantDisk n
    exact hconv.segment_subset hend.1 hend.2.1
  have hzseg : z ∈ sourcePeriodicSegment hp hp1 ψ n :=
    sourceCanonicalRootGapPoint_mem_segment hp hp1 ψ n (Real.cos θ)
      (Real.neg_one_le_cos θ) (Real.cos_le_one θ)
  have hzdisc : z ∈ sourceIsolatingDisc hp hp1 φ N ε n := by
    simpa [sourceIsolatingDisc, not_le.mpr hN] using hsegment hzseg
  have hfactor : I * sourceCriticalRootRatioExtension hp hp1 n ψ z =
      sourceSingleRootQuotientJointProduct hp hp1 n (z,(a,ψ)) := by
    change I * (-I *
      sourceSingleRootQuotientJointProduct hp hp1 n (z,(a,ψ))) = _
    calc
      I * (-I * sourceSingleRootQuotientJointProduct hp hp1 n (z,(a,ψ))) =
          -(I^2) * sourceSingleRootQuotientJointProduct hp hp1 n (z,(a,ψ)) := by ring
      _ = _ := by simp [Complex.I_sq]
  change ‖I * sourceCriticalRootRatioExtension hp hp1 n ψ z - 1‖ ≤ _
  rw [hfactor]
  exact hpoint n hK₁ z hzdisc

/-- The normalized action inherits the `ℓq + ℓ^(p/2)` factor
majorants on sufficiently distant open real-type gaps. The remaining
gap-squared critical-offset term is displayed explicitly. -/
theorem exists_local_sourceRawNormalizedAction_sequenceMajorants
    [Fact (1 ≤ q)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (hq1 : 1 < q) (hq : q ≠ ⊤)
    (hhalf : ENNReal.ofReal (p.toReal/2) ≤ q)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∃ K : ℕ, ∀ ψ ∈ V,
        ∃ Bq : Coeff q, ∃ Bg : Coeff (ENNReal.ofReal (p.toReal/2)),
          ∀ n : ℤ, K ≤ n.natAbs →
            IsRealType (CoeffPair.toMax p ψ) →
            (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
              (periodOnePotential_mem ψ) n).re <
              (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
                (periodOnePotential_mem ψ) n).re →
            ‖4 * sourceRawNormalizedAction hp hp1 n ψ - 1‖ ≤
              8 * ‖sourcePeriodicGapDisplacement hp hp1 ψ n‖^2 *
                ‖sourceCriticalGapQuotient hp hp1 ψ n‖^2 +
              2 * (2 * ‖sourcePeriodicGapDisplacement hp hp1 ψ n‖ *
                ‖sourceCriticalGapQuotient hp hp1 ψ n‖ + 1)^2 *
                  (‖Bq n‖ + ‖Bg n‖) := by
  obtain ⟨V,hVopen,hφV,K,hfactor⟩ :=
    exists_local_sourceNormalizedAction_factor_sequenceMajorants
      hp hp1 hq1 hq hhalf φ hφ
  refine ⟨V,hVopen,hφV,K,?_⟩
  intro ψ hψ
  obtain ⟨Bq,Bg,hB⟩ := hfactor ψ hψ
  refine ⟨Bq,Bg,?_⟩
  intro n hn hreal hopen
  exact norm_sourceRawNormalizedAction_sub_one_le_of_factor_bound
    hp hp1 ψ hreal n hopen (‖Bq n‖ + ‖Bg n‖)
    (hB n hn)

end NLS.ZakharovShabat
