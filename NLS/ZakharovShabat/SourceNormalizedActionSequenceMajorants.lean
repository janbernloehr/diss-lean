import NLS.ZakharovShabat.SourceNormalizedActionTailBound
import NLS.ZakharovShabat.SourceSingleRootQuotientAsymptoticDiscSup
import NLS.SequenceSpaces.Multiplier
import NLS.SequenceSpaces.ExponentEmbedding
import NLS.SequenceSpaces.SandwichMajorant
import NLS.SequenceSpaces.QuasiExponentEmbedding

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

/-- The critical-to-midpoint sequence norm is controlled by the
critical quotient and squared-gap norms, also when `p/2 < 1`. -/
theorem norm_sourceCriticalMidpointOffsetAtExponent_le
    [Fact (1 ≤ q)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (hq0 : 1 ≤ q) (hq : q ≠ ⊤)
    (hhalf : ENNReal.ofReal (p.toReal/2) ≤ q)
    (ψ : CoeffPair p) :
    ‖sourceCriticalMidpointOffsetAtExponent hp hp1 hhalf ψ‖ ≤
      ‖sourceCriticalGapQuotient hp hp1 ψ‖ *
        ‖sourcePeriodicSquaredGapCoeff hp hp1 ψ‖ := by
  let S := sourcePeriodicSquaredGapCoeff hp hp1 ψ
  let Sq : Coeff q :=
    ⟨fun n => S n, (lp.memℓp S).of_exponent_ge hhalf⟩
  let B := sourceCriticalGapQuotient hp hp1 ψ
  let Btop := Coeff.exponentInclusion (le_top : p ≤ ⊤) B
  have hpr : 0 < p.toReal :=
    ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans hp1)) hp
  have hhalfPos : 0 < ENNReal.ofReal (p.toReal/2) :=
    ENNReal.ofReal_pos.mpr (by positivity)
  have hSq : ‖Sq‖ ≤ ‖S‖ :=
    Coeff.norm_quasiExponentInclusion_le hhalfPos
      (zero_lt_one.trans_le hq0) hq hhalf S
  calc
    ‖sourceCriticalMidpointOffsetAtExponent hp hp1 hhalf ψ‖ =
        ‖Coeff.multiplier Btop Sq‖ := rfl
    _ ≤ ‖Btop‖ * ‖Sq‖ := Coeff.norm_multiplier_le Btop Sq
    _ ≤ ‖B‖ * ‖S‖ := by
      gcongr
      exact Coeff.norm_exponentInclusion_le le_top B

/-- The critical-to-midpoint offset has a common `ℓq` bound near
each real-type source. -/
theorem exists_local_sourceCriticalMidpointOffsetAtExponent_bound
    [Fact (1 ≤ q)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (hq0 : 1 ≤ q) (hq : q ≠ ⊤)
    (hhalf : ENNReal.ofReal (p.toReal/2) ≤ q)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∃ A : ℝ, 0 ≤ A ∧
        ∀ ψ ∈ V, ‖sourceCriticalMidpointOffsetAtExponent
          hp hp1 hhalf ψ‖ ≤ A := by
  obtain ⟨V₁,hV₁open,hφV₁,R,hR,hS⟩ :=
    exists_local_sourcePeriodicSquaredGapCoeff_bound hp hp1 φ
  obtain ⟨V₂,hV₂open,hφV₂,B,hB,hquot⟩ :=
    exists_local_uniform_sourceCriticalGapQuotient hp hp1 φ hφ
  refine ⟨V₁ ∩ V₂,hV₁open.inter hV₂open,⟨hφV₁,hφV₂⟩,
    B*R^2,by positivity,?_⟩
  intro ψ hψ
  exact (norm_sourceCriticalMidpointOffsetAtExponent_le
    hp hp1 hq0 hq hhalf ψ).trans
    (mul_le_mul (hquot ψ hψ.2).1 (hS ψ hψ.1)
      (lp.norm_nonneg' _) hB)

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

omit [Fact (1 ≤ p)] in
/-- For `p ≤ 2`, the squared-gap exponent embeds into `ℓ¹`. -/
theorem source_half_le_one (hp : p ≠ ⊤) (hp2 : p ≤ 2) :
    ENNReal.ofReal (p.toReal / 2) ≤ (1 : ℝ≥0∞) := by
  have hpr : p.toReal ≤ 2 :=
    (ENNReal.toReal_le_toReal hp (by norm_num)).mpr hp2
  calc
    ENNReal.ofReal (p.toReal / 2) ≤ ENNReal.ofReal 1 :=
      ENNReal.ofReal_le_ofReal (by linarith)
    _ = 1 := by norm_num

/-- For `1 < p ≤ 2`, the actual critical-to-midpoint offset is an
`ℓ¹` sequence with a locally uniform norm bound. This endpoint
sequence can be used for every target exponent above one. -/
theorem exists_local_sourceCriticalMidpointOffset_one_bound
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hp2 : p ≤ 2)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∃ A : ℝ, 0 ≤ A ∧
        ∀ ψ ∈ V,
          ‖sourceCriticalMidpointOffsetAtExponent hp hp1
              (q := 1) (source_half_le_one hp hp2) ψ‖ ≤ A ∧
          ∀ n : ℤ,
            canonicalCriticalPoints hp hp1 (periodOnePotential ψ)
                (periodOnePotential_mem ψ) n -
              canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
                (periodOnePotential_mem ψ) n =
              sourceCriticalMidpointOffsetAtExponent hp hp1
                (q := 1) (source_half_le_one hp hp2) ψ n := by
  have hhalf := source_half_le_one hp hp2
  obtain ⟨V₁,hV₁,hφ₁,A,hA,hbound⟩ :=
    exists_local_sourceCriticalMidpointOffsetAtExponent_bound
      hp hp1 le_rfl (by norm_num) hhalf φ hφ
  obtain ⟨W,hW,hreal,heq⟩ :=
    exists_global_sourceCriticalMidpointOffsetAtExponent_eq
      hp hp1 hhalf
  refine ⟨V₁ ∩ W,hV₁.inter hW,⟨hφ₁,hreal hφ⟩,A,hA,?_⟩
  intro ψ hψ
  exact ⟨hbound ψ hψ.1,heq ψ hψ.2⟩

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
      ∃ K : ℕ, ∃ C R H : ℝ,
        1 ≤ C ∧ 0 ≤ R ∧ 0 ≤ H ∧ ∀ ψ ∈ V,
        ∃ Bq : Coeff q, ∃ Bg : Coeff (ENNReal.ofReal (p.toReal/2)),
          (∀ n : ℤ, K ≤ n.natAbs → ∀ θ : ℝ,
            ‖I * sourceCriticalRootRatioExtension hp hp1 n ψ
              (sourceStandardRootMidpoint hp hp1 ψ n +
                sourceStandardRootHalfGap hp hp1 ψ n * (Real.cos θ:ℂ)) - 1‖ ≤
              ‖Bq n‖ + ‖Bg n‖) ∧
          ‖Bq‖ ≤
            (Real.pi⁻¹*(Fourier.hilbertTransformBound hq1 hq+
                ‖Fourier.hilbertSquareCoeffs‖)+
              C*R*‖Fourier.hilbertSquareCoeffs‖)*
                ‖sourceCriticalMidpointOffsetAtExponent hp hp1 hhalf ψ‖ +
              Real.exp ((C/2)*Fourier.absoluteSampledRowConstant hq*
                ‖sourceCriticalMidpointOffsetAtExponent hp hp1 hhalf ψ‖)*
                ((C/2)*Fourier.absoluteSampledRowConstant hq*
                  ‖sourceCriticalMidpointOffsetAtExponent hp hp1 hhalf ψ‖)^2 ∧
          ‖Bg‖ ≤
            (Real.exp (C*‖sourceCriticalMidpointOffsetAtExponent
                hp hp1 hhalf ψ‖*‖Coeff.puncturedLattice q.conjExponent
                  ((ENNReal.HolderConjugate.lt_top_iff_one_lt q q.conjExponent).mp
                    hq.lt_top)‖)*C^2) *
              (H^2 *
                ‖squaredReciprocalKernel (min 1 (p.toReal/2))
                  (lt_min (by norm_num : (1/2:ℝ)<1)
                    (by
                      have hpr : 1 < p.toReal :=
                        (ENNReal.toReal_lt_toReal (by simp) hp).mpr hp1
                      linarith))‖) := by
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
    ⟨⟨hφV₁,hφV₂⟩,hWreal hφ⟩,K,C,R,H,hC,hR,hH,?_⟩
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
  obtain ⟨Bq,Bg,hpoint,hBq,hBg⟩ :=
    hmajor ψ hψ.1.1 a α hα
  refine ⟨Bq,Bg,?_,hBq,hBg⟩
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

/-- The factor majorants may be chosen with common sequence-norm bounds
throughout a neighborhood of a real-type source. -/
theorem exists_local_sourceNormalizedAction_factor_uniformMajorants
    [Fact (1 ≤ q)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (hq1 : 1 < q) (hq : q ≠ ⊤)
    (hhalf : ENNReal.ofReal (p.toReal/2) ≤ q)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∃ K : ℕ, ∃ Lq Lg : ℝ, ∀ ψ ∈ V,
        ∃ Bq : Coeff q, ∃ Bg : Coeff (ENNReal.ofReal (p.toReal/2)),
          (∀ n : ℤ, K ≤ n.natAbs → ∀ θ : ℝ,
            ‖I * sourceCriticalRootRatioExtension hp hp1 n ψ
              (sourceStandardRootMidpoint hp hp1 ψ n +
                sourceStandardRootHalfGap hp hp1 ψ n * (Real.cos θ:ℂ)) - 1‖ ≤
              ‖Bq n‖ + ‖Bg n‖) ∧
          ‖Bq‖ ≤ Lq ∧ ‖Bg‖ ≤ Lg := by
  obtain ⟨V₁,hV₁open,hφV₁,K,C,R,H,hC,hR,hH,hfactor⟩ :=
    exists_local_sourceNormalizedAction_factor_sequenceMajorants
      hp hp1 hq1 hq hhalf φ hφ
  obtain ⟨V₂,hV₂open,hφV₂,A,hA,hα⟩ :=
    exists_local_sourceCriticalMidpointOffsetAtExponent_bound
      hp hp1 hq1.le hq hhalf φ hφ
  let u : ℝ := Real.pi⁻¹ *
    (Fourier.hilbertTransformBound hq1 hq + ‖Fourier.hilbertSquareCoeffs‖) +
      C*R*‖Fourier.hilbertSquareCoeffs‖
  let d : ℝ := (C/2) * Fourier.absoluteSampledRowConstant hq
  let v : ℝ := ‖Coeff.puncturedLattice q.conjExponent
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt q q.conjExponent).mp hq.lt_top)‖
  have hpr : 1 < p.toReal :=
    (ENNReal.toReal_lt_toReal (by simp) hp).mpr hp1
  let w : ℝ := ‖squaredReciprocalKernel (min 1 (p.toReal/2))
    (lt_min (by norm_num : (1/2:ℝ)<1) (by linarith))‖
  let Lq : ℝ := u*A + Real.exp (d*A)*(d*A)^2
  let Lg : ℝ := (Real.exp (C*A*v)*C^2)*(H^2*w)
  have hv : 0 ≤ v := lp.norm_nonneg' _
  have hw : 0 ≤ w := lp.norm_nonneg' _
  have hu : 0 ≤ u := by
    dsimp [u]
    have := Fourier.hilbertTransformBound_nonneg hq1 hq
    positivity
  have hd : 0 ≤ d := by
    dsimp [d]
    have := Fourier.absoluteSampledRowConstant_nonneg hq
    positivity
  refine ⟨V₁ ∩ V₂,hV₁open.inter hV₂open,⟨hφV₁,hφV₂⟩,
    K,Lq,Lg,?_⟩
  intro ψ hψ
  obtain ⟨Bq,Bg,hpoint,hBq,hBg⟩ := hfactor ψ hψ.1
  let α := sourceCriticalMidpointOffsetAtExponent hp hp1 hhalf ψ
  have hαA : ‖α‖ ≤ A := hα ψ hψ.2
  have hdA : d*‖α‖ ≤ d*A := mul_le_mul_of_nonneg_left hαA hd
  have hBq' : ‖Bq‖ ≤ u*‖α‖ + Real.exp (d*‖α‖)*(d*‖α‖)^2 := by
    simpa only [u,d,α] using hBq
  have hBg' : ‖Bg‖ ≤ (Real.exp (C*‖α‖*v)*C^2)*(H^2*w) := by
    simpa only [v,w,α] using hBg
  refine ⟨Bq,Bg,hpoint,?_,?_⟩
  · apply hBq'.trans
    dsimp [Lq]
    apply add_le_add (mul_le_mul_of_nonneg_left hαA hu)
    apply mul_le_mul
      (Real.exp_le_exp.mpr hdA)
      (pow_le_pow_left₀ (mul_nonneg hd (lp.norm_nonneg' α)) hdA 2)
      (sq_nonneg _)
      (Real.exp_nonneg _)
  · apply hBg'.trans
    dsimp [Lg]
    apply mul_le_mul_of_nonneg_right _ (mul_nonneg (sq_nonneg _) hw)
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hαA (by linarith : 0 ≤ C))
      hv

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
  obtain ⟨V,hVopen,hφV,K,_,_,_,_,_,_,hfactor⟩ :=
    exists_local_sourceNormalizedAction_factor_sequenceMajorants
      hp hp1 hq1 hq hhalf φ hφ
  refine ⟨V,hVopen,hφV,K,?_⟩
  intro ψ hψ
  obtain ⟨Bq,Bg,hB,_,_⟩ := hfactor ψ hψ
  refine ⟨Bq,Bg,?_⟩
  intro n hn hreal hopen
  exact norm_sourceRawNormalizedAction_sub_one_le_of_factor_bound
    hp hp1 ψ hreal n hopen (‖Bq n‖ + ‖Bg n‖)
    (hB n hn)

/-- The gap-squared critical term belongs to the squared-gap sequence
class, with its exact pointwise magnitude. -/
def sourceNormalizedActionCriticalMajorant
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) : Coeff (ENNReal.ofReal (p.toReal/2)) :=
  Coeff.multiplier
    (Coeff.multiplier
      (Coeff.exponentInclusion (le_top : p ≤ ⊤)
        (sourceCriticalGapQuotient hp hp1 ψ))
      (Coeff.exponentInclusion (le_top : p ≤ ⊤)
        (sourceCriticalGapQuotient hp hp1 ψ)))
    (sourcePeriodicSquaredGapCoeff hp hp1 ψ)

@[simp] theorem norm_sourceNormalizedActionCriticalMajorant_apply
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) :
    ‖sourceNormalizedActionCriticalMajorant hp hp1 ψ n‖ =
      ‖sourcePeriodicGapDisplacement hp hp1 ψ n‖^2 *
        ‖sourceCriticalGapQuotient hp hp1 ψ n‖^2 := by
  simp only [sourceNormalizedActionCriticalMajorant,
    Coeff.multiplier_apply, Coeff.exponentInclusion_apply,
    sourcePeriodicSquaredGapCoeff_apply, norm_mul, norm_pow]
  ring

/-- The remaining critical contribution is uniformly bounded by the
squared-gap norm times the square of the critical quotient norm. -/
theorem norm_sourceNormalizedActionCriticalMajorant_le
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) :
    ‖sourceNormalizedActionCriticalMajorant hp hp1 ψ‖ ≤
      ‖sourceCriticalGapQuotient hp hp1 ψ‖^2 *
        ‖sourcePeriodicSquaredGapCoeff hp hp1 ψ‖ := by
  let B := sourceCriticalGapQuotient hp hp1 ψ
  let Btop := Coeff.exponentInclusion (le_top : p ≤ ⊤) B
  let S := sourcePeriodicSquaredGapCoeff hp hp1 ψ
  have hpr : 0 < p.toReal :=
    ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans hp1)) hp
  have hhalfPos : 0 < ENNReal.ofReal (p.toReal/2) :=
    ENNReal.ofReal_pos.mpr (by positivity)
  calc
    ‖sourceNormalizedActionCriticalMajorant hp hp1 ψ‖ =
        ‖Coeff.multiplier (Coeff.multiplier Btop Btop) S‖ := rfl
    _ ≤ ‖Coeff.multiplier Btop Btop‖ * ‖S‖ :=
      Coeff.norm_multiplier_le_quasi hhalfPos.ne' _ _
    _ ≤ (‖Btop‖ * ‖Btop‖) * ‖S‖ :=
      mul_le_mul_of_nonneg_right (Coeff.norm_multiplier_le Btop Btop)
        (lp.norm_nonneg' S)
    _ ≤ ‖B‖^2 * ‖S‖ := by
      have hB := Coeff.norm_exponentInclusion_le le_top B
      have hsq : ‖Btop‖^2 ≤ ‖B‖^2 :=
        pow_le_pow_left₀ (lp.norm_nonneg' _) hB 2
      rw [← pow_two]
      exact mul_le_mul_of_nonneg_right hsq (lp.norm_nonneg' S)

/-- The critical contribution to the normalized-action error has a
common `ℓ^(p/2)` norm bound near each real-type source. -/
theorem exists_local_sourceNormalizedActionCriticalMajorant_bound
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∃ L : ℝ, 0 ≤ L ∧
        ∀ ψ ∈ V, ‖sourceNormalizedActionCriticalMajorant hp hp1 ψ‖ ≤ L := by
  obtain ⟨V₁,hV₁open,hφV₁,R,hR,hS⟩ :=
    exists_local_sourcePeriodicSquaredGapCoeff_bound hp hp1 φ
  obtain ⟨V₂,hV₂open,hφV₂,B,hB,hquot⟩ :=
    exists_local_uniform_sourceCriticalGapQuotient hp hp1 φ hφ
  refine ⟨V₁ ∩ V₂,hV₁open.inter hV₂open,⟨hφV₁,hφV₂⟩,
    B^2*R^2,by positivity,?_⟩
  intro ψ hψ
  have hBsq : ‖sourceCriticalGapQuotient hp hp1 ψ‖^2 ≤ B^2 :=
    pow_le_pow_left₀ (lp.norm_nonneg' _) (hquot ψ hψ.2).1 2
  exact (norm_sourceNormalizedActionCriticalMajorant_le hp hp1 ψ).trans
    (mul_le_mul hBsq (hS ψ hψ.1)
      (lp.norm_nonneg' _) (sq_nonneg _))

theorem norm_smul_magnitude_apply {r : ℝ≥0∞}
    (a : Coeff r) (c : ℝ) (hc : 0 ≤ c) (n : ℤ) :
    ‖((c : ℂ) • Coeff.magnitude a) n‖ = c * ‖a n‖ := by
  simp only [lp.coeFn_smul, Pi.smul_apply, Coeff.magnitude_apply,
    smul_eq_mul, ← Complex.ofReal_mul, Complex.norm_real,
    Real.norm_of_nonneg (mul_nonneg hc (norm_nonneg _))]

theorem norm_add_smul_magnitude_apply {r : ℝ≥0∞}
    (a b : Coeff r) (c d : ℝ) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (n : ℤ) :
    ‖(((c : ℂ) • Coeff.magnitude a) +
        ((d : ℂ) • Coeff.magnitude b)) n‖ =
      c * ‖a n‖ + d * ‖b n‖ := by
  simp only [lp.coeFn_add, Pi.add_apply, lp.coeFn_smul, Pi.smul_apply,
    Coeff.magnitude_apply, smul_eq_mul, ← Complex.ofReal_mul,
    ← Complex.ofReal_add, Complex.norm_real,
    Real.norm_of_nonneg (add_nonneg
      (mul_nonneg hc (norm_nonneg _))
      (mul_nonneg hd (norm_nonneg _)))]

/-- On distant open real-type gaps, the normalized-action deviation
has an actual `ℓq + ℓ^(p/2)` two-sequence majorant. In particular,
`q = p/2` is available above `p = 2`; below it one may take any
finite `q > 1`. -/
theorem exists_local_sourceRawNormalizedAction_twoSequenceMajorants
    [Fact (1 ≤ q)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (hq1 : 1 < q) (hq : q ≠ ⊤)
    (hhalf : ENNReal.ofReal (p.toReal/2) ≤ q)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∃ K : ℕ, ∀ ψ ∈ V,
        ∃ Cq : Coeff q, ∃ Cg : Coeff (ENNReal.ofReal (p.toReal/2)),
          ∀ n : ℤ, K ≤ n.natAbs →
            IsRealType (CoeffPair.toMax p ψ) →
            (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
              (periodOnePotential_mem ψ) n).re <
              (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
                (periodOnePotential_mem ψ) n).re →
            ‖4 * sourceRawNormalizedAction hp hp1 n ψ - 1‖ ≤
              ‖Cq n‖ + ‖Cg n‖ := by
  obtain ⟨V,hVopen,hφV,K,hmajor⟩ :=
    exists_local_sourceRawNormalizedAction_sequenceMajorants
      hp hp1 hq1 hq hhalf φ hφ
  refine ⟨V,hVopen,hφV,K,?_⟩
  intro ψ hψ
  obtain ⟨Bq,Bg,hB⟩ := hmajor ψ hψ
  let γ := sourcePeriodicGapDisplacement hp hp1 ψ
  let B := sourceCriticalGapQuotient hp hp1 ψ
  let M : ℝ := 2 * (2 * ‖γ‖ * ‖B‖ + 1)^2
  have hM : 0 ≤ M := by dsimp [M]; positivity
  let D := sourceNormalizedActionCriticalMajorant hp hp1 ψ
  let Cq : Coeff q := (M:ℂ) • Coeff.magnitude Bq
  let Cg : Coeff (ENNReal.ofReal (p.toReal/2)) :=
    (8:ℂ) • Coeff.magnitude D + (M:ℂ) • Coeff.magnitude Bg
  refine ⟨Cq,Cg,?_⟩
  intro n hn hreal hopen
  have hγn : ‖γ n‖ ≤ ‖γ‖ :=
    lp.norm_apply_le_norm (zero_lt_one.trans hp1).ne' γ n
  have hBn : ‖B n‖ ≤ ‖B‖ :=
    lp.norm_apply_le_norm (zero_lt_one.trans hp1).ne' B n
  have hfactor :
      2 * (2 * ‖γ n‖ * ‖B n‖ + 1)^2 ≤ M := by
    dsimp [M]
    gcongr
  have hbound := hB n hn hreal hopen
  change ‖4 * sourceRawNormalizedAction hp hp1 n ψ - 1‖ ≤
    8 * ‖γ n‖^2 * ‖B n‖^2 +
    2 * (2 * ‖γ n‖ * ‖B n‖ + 1)^2 *
      (‖Bq n‖ + ‖Bg n‖) at hbound
  have hCq : ‖Cq n‖ = M * ‖Bq n‖ :=
    norm_smul_magnitude_apply Bq M hM n
  have hCg : ‖Cg n‖ =
      8 * ‖γ n‖^2 * ‖B n‖^2 + M * ‖Bg n‖ := by
    rw [show ‖Cg n‖ = 8 * ‖D n‖ + M * ‖Bg n‖ from
      norm_add_smul_magnitude_apply D Bg 8 M (by norm_num) hM n]
    simp only [D, norm_sourceNormalizedActionCriticalMajorant_apply, γ, B]
    ring
  rw [hCq,hCg]
  nlinarith [mul_le_mul_of_nonneg_right hfactor
    (add_nonneg (norm_nonneg (Bq n)) (norm_nonneg (Bg n)))]

/-- The action majorants are locally uniformly bounded in their
respective sequence norms, including the quasi-Banach exponent
`p/2 < 1`. -/
theorem exists_local_sourceRawNormalizedAction_uniformSequenceMajorants
    [Fact (1 ≤ q)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (hq1 : 1 < q) (hq : q ≠ ⊤)
    (hhalf : ENNReal.ofReal (p.toReal/2) ≤ q)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∃ K : ℕ, ∃ Lq Lg : ℝ, ∀ ψ ∈ V,
        ∃ Cq : Coeff q, ∃ Cg : Coeff (ENNReal.ofReal (p.toReal/2)),
          (∀ n : ℤ, K ≤ n.natAbs →
            IsRealType (CoeffPair.toMax p ψ) →
            (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
              (periodOnePotential_mem ψ) n).re <
              (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
                (periodOnePotential_mem ψ) n).re →
            ‖4 * sourceRawNormalizedAction hp hp1 n ψ - 1‖ ≤
              ‖Cq n‖ + ‖Cg n‖) ∧
          ‖Cq‖ ≤ Lq ∧ ‖Cg‖ ≤ Lg := by
  obtain ⟨Vf,hVfopen,hφVf,K,Lfq,Lfg,hfactor⟩ :=
    exists_local_sourceNormalizedAction_factor_uniformMajorants
      hp hp1 hq1 hq hhalf φ hφ
  obtain ⟨Vd,hVdopen,hφVd,Ld,hLd0,hD⟩ :=
    exists_local_sourceNormalizedActionCriticalMajorant_bound hp hp1 φ hφ
  obtain ⟨_,_,Vγ,hVγopen,hφVγ,G,hG,hγ⟩ :=
    exists_uniform_small_sourcePeriodicGapDisplacement hp hp1 φ
      (by norm_num : (0:ℝ) < 1)
  obtain ⟨Vb,hVbopen,hφVb,T,hT,hB⟩ :=
    exists_local_uniform_sourceCriticalGapQuotient hp hp1 φ hφ
  obtain ⟨Bq₀,Bg₀,_,hBq₀,hBg₀⟩ := hfactor φ hφVf
  have hLfq : 0 ≤ Lfq := (lp.norm_nonneg' Bq₀).trans hBq₀
  have hLfg : 0 ≤ Lfg := (lp.norm_nonneg' Bg₀).trans hBg₀
  let V := ((Vf ∩ Vd) ∩ Vγ) ∩ Vb
  let M₀ : ℝ := 2 * (2*G*T+1)^2
  let Aq : ℝ := M₀*Lfq
  let Ad : ℝ := 8*Ld
  let Ag : ℝ := M₀*Lfg
  let r := ENNReal.ofReal (p.toReal/2)
  have hpr : 0 < p.toReal :=
    ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans hp1)) hp
  have hrEq : r.toReal = p.toReal/2 := by
    simp only [r, ENNReal.toReal_ofReal (by positivity : 0 ≤ p.toReal/2)]
  have hr : 0 < r.toReal := by rw [hrEq]; positivity
  have hrENN : 0 < r := ENNReal.ofReal_pos.mpr (by positivity)
  let Lg : ℝ := max (Ad+Ag)
    ((Ad^r.toReal+Ag^r.toReal)^(r.toReal)⁻¹)
  have hM₀ : 0 ≤ M₀ := by dsimp [M₀]; positivity
  refine ⟨V,(((hVfopen.inter hVdopen).inter hVγopen).inter hVbopen),
    ⟨⟨⟨hφVf,hφVd⟩,hφVγ⟩,hφVb⟩,K,Aq,Lg,?_⟩
  intro ψ hψ
  obtain ⟨Bq,Bg,hpoint,hBq,hBg⟩ := hfactor ψ hψ.1.1.1
  let γ := sourcePeriodicGapDisplacement hp hp1 ψ
  let B := sourceCriticalGapQuotient hp hp1 ψ
  let M : ℝ := 2*(2*‖γ‖*‖B‖+1)^2
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hMle : M ≤ M₀ := by
    dsimp [M,M₀]
    gcongr
    · exact (hγ ψ hψ.1.2).1
    · exact (hB ψ hψ.2).1
  let D := sourceNormalizedActionCriticalMajorant hp hp1 ψ
  let Cq : Coeff q := (M:ℂ) • Coeff.magnitude Bq
  let Da : Coeff r := (8:ℂ) • Coeff.magnitude D
  let Gb : Coeff r := (M:ℂ) • Coeff.magnitude Bg
  let Cg : Coeff r := Da + Gb
  have hCqNorm : ‖Cq‖ ≤ Aq := by
    have hn : ‖Cq‖ = M*‖Bq‖ := by
      simp only [Cq, lp.norm_const_smul (zero_lt_one.trans hq1).ne',
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hM,
        Coeff.norm_magnitude]
    rw [hn]
    exact mul_le_mul hMle hBq (lp.norm_nonneg' Bq) hM₀
  have hDaNorm : ‖Da‖ ≤ Ad := by
    have hn : ‖Da‖ = 8*‖D‖ := by
      change ‖(8:ℂ) • Coeff.magnitude D‖ = 8*‖D‖
      rw [lp.norm_const_smul hrENN.ne', Coeff.norm_magnitude_quasi hrENN.ne']
      norm_num
    rw [hn]
    exact mul_le_mul_of_nonneg_left (hD ψ hψ.1.1.2) (by norm_num)
  have hGbNorm : ‖Gb‖ ≤ Ag := by
    have hn : ‖Gb‖ = M*‖Bg‖ := by
      change ‖(M:ℂ) • Coeff.magnitude Bg‖ = M*‖Bg‖
      rw [lp.norm_const_smul hrENN.ne', Coeff.norm_magnitude_quasi hrENN.ne']
      simp [Complex.norm_real, Real.norm_eq_abs, hM]
    rw [hn]
    exact mul_le_mul hMle hBg (lp.norm_nonneg' Bg) hM₀
  have hCgNorm : ‖Cg‖ ≤ Lg :=
    Coeff.norm_add_le_uniform hr Da Gb hDaNorm hGbNorm
  refine ⟨Cq,Cg,?_,hCqNorm,hCgNorm⟩
  intro n hn hreal hopen
  have hγn : ‖γ n‖ ≤ ‖γ‖ :=
    lp.norm_apply_le_norm (zero_lt_one.trans hp1).ne' γ n
  have hBn : ‖B n‖ ≤ ‖B‖ :=
    lp.norm_apply_le_norm (zero_lt_one.trans hp1).ne' B n
  have hfactorN :
      2 * (2 * ‖γ n‖ * ‖B n‖ + 1)^2 ≤ M := by
    dsimp [M]
    gcongr
  have hbound := norm_sourceRawNormalizedAction_sub_one_le_of_factor_bound
    hp hp1 ψ hreal n hopen (‖Bq n‖+‖Bg n‖) (hpoint n hn)
  change ‖4 * sourceRawNormalizedAction hp hp1 n ψ - 1‖ ≤
    8 * ‖γ n‖^2 * ‖B n‖^2 +
    2 * (2 * ‖γ n‖ * ‖B n‖ + 1)^2 *
      (‖Bq n‖ + ‖Bg n‖) at hbound
  have hCq : ‖Cq n‖ = M*‖Bq n‖ :=
    norm_smul_magnitude_apply Bq M hM n
  have hCg : ‖Cg n‖ =
      8*‖γ n‖^2*‖B n‖^2 + M*‖Bg n‖ := by
    rw [show ‖Cg n‖ = 8*‖D n‖ + M*‖Bg n‖ from
      norm_add_smul_magnitude_apply D Bg 8 M (by norm_num) hM n]
    simp only [D, norm_sourceNormalizedActionCriticalMajorant_apply, γ, B]
    ring
  rw [hCq,hCg]
  nlinarith [mul_le_mul_of_nonneg_right hfactorN
    (add_nonneg (norm_nonneg (Bq n)) (norm_nonneg (Bg n)))]

end NLS.ZakharovShabat
