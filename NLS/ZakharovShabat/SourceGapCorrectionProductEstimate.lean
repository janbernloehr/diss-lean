import NLS.ZakharovShabat.SourceQuotientDiscSupDecomposition

/-!
# The literal inverse-square-root product in Lemma 10.8

Taking the actual midpoints as numerator roots identifies the unordered
inverse-square-root product. Its supremum on each distant original disk
has an actual half-exponent coefficient, uniformly on the supplied source
neighborhood. The finite head is set to zero in this tail coefficient;
the full quotient estimates separately retain every central disk.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The literal unordered correction product equals the quotient with midpoint numerator roots. -/
theorem hasProd_sourceInverseSqrtGapCorrection (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (z : ℂ) (n : ℤ)
    (hz : z ∈ sourceStandardRootOmittedDomain hp hp1 ψ n) :
    HasProd (fun m : {m : ℤ // m ≠ n} =>
      (Complex.sqrt (1-sourceSingleRootGapRadicand hp hp1 ψ m z))⁻¹)
      (sourceSingleRootQuotientJointProduct hp hp1 n
        (z,(sourcePeriodicMidpointDisplacement hp hp1 ψ,ψ))) := by
  have he (m : {m : ℤ // m ≠ n}) :
      (displacedRoots (sourcePeriodicMidpointDisplacement hp hp1 ψ) m-z)/
        sourceStandardRoot hp hp1 ψ m z =
      (Complex.sqrt (1-sourceSingleRootGapRadicand hp hp1 ψ m z))⁻¹ := by
    have hmid : canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) m-z ≠ 0 := by
      intro h
      have he := sub_eq_zero.mp h
      exact hz m m.property (he ▸ sourcePeriodicMidpoint_mem_segment hp hp1 ψ m)
    have hroots : displacedRoots (sourcePeriodicMidpointDisplacement hp hp1 ψ) m =
        canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m := by
      simp only [displacedRoots,sourcePeriodicMidpointDisplacement_apply]
      ring
    rw [hroots,sourceStandardRoot,singleRootQuotient_factor,div_self hmid,one_mul]
    rfl
  have h := hasProd_sourceSingleRootQuotient_subtype hp hp1 ψ
    (sourcePeriodicMidpointDisplacement hp hp1 ψ) z n hz
  simpa only [he] using h

/-- One half-exponent majorant bound works on every distant original disk and nearby source. -/
theorem SourceQuotientDiscEstimates.inverseSqrtGapMajorant
    {hp : p ≠ ⊤} {hp1 : 1 < p} {U : Set (Coeff p × CoeffPair p)}
    {D : ℤ → Set ℂ} {c R H M : ℝ} {N K : ℕ}
    (h : SourceQuotientDiscEstimates hp hp1 U D c R H M N K) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ t ∈ U,
      ∃ B : Coeff (ENNReal.ofReal (p.toReal/2)), ‖B‖ ≤ L ∧
        ∀ n : ℤ, K ≤ n.natAbs → ∀ z ∈ D n,
          ‖(∏' m : {m : ℤ // m ≠ n},
            (Complex.sqrt (1-sourceSingleRootGapRadicand hp hp1 t.2 m z))⁻¹)-1‖ ≤ ‖B n‖ := by
  have hpr : 1 < p.toReal := (ENNReal.toReal_lt_toReal (by simp) hp).mpr hp1
  let w := squaredReciprocalKernel (min 1 (p.toReal/2))
    (lt_min (by norm_num : (1/2:ℝ)<1) (by linarith))
  have hw : 0 ≤ ‖w‖ := lp.norm_nonneg' w
  refine ⟨c^2*(H^2*‖w‖),by positivity,?_⟩
  intro t ht
  let a := sourcePeriodicMidpointDisplacement hp hp1 t.2
  have hoff (m : ℤ) : displacedRoots a m-
      canonicalPeriodicMidpoint hp hp1 (periodOnePotential t.2) (periodOnePotential_mem t.2) m =
        (0 : Coeff p) m := by
    simp only [a,displacedRoots,sourcePeriodicMidpointDisplacement_apply,lp.coeFn_zero,Pi.zero_apply]
    ring
  have hdom (n : ℤ) (hn : K ≤ n.natAbs) (z : ℂ)
      (hz : z ∈ sourceIsolatingDisc hp hp1 (0 : CoeffPair p) N 0 n) :
      (z,(a,t.2)) ∈ sourceSingleRootQuotientJointDomain hp hp1 univ n := by
    refine ⟨mem_univ _,h.domain t ht n z ?_⟩
    rw [h.tail n (h.threshold.trans_le hn)]
    simpa only [sourceIsolatingDisc,if_neg (not_le.mpr (h.threshold.trans_le hn))] using hz
  obtain ⟨B,hB,hBn⟩ := exists_sourceSingleRootGapCorrectionDiscMajorant hp hp1 hp
    (0 : CoeffPair p) t.2 a (0 : Coeff p) hoff N K 0 c h.one_le
    (h.separation t ht) hdom (h.small t ht)
  refine ⟨B,?_,?_⟩
  · have hb : ‖B‖ ≤ c^2*(‖sourcePeriodicSquaredGapCoeff hp hp1 t.2‖*‖w‖) := by
      simpa only [norm_zero,mul_zero,zero_mul,Real.exp_zero,one_mul] using hBn
    exact hb.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (h.squared_gap t ht) hw) (sq_nonneg _))
  · intro n hn z hz
    have hza : z ∈ sourceIsolatingDisc hp hp1 (0 : CoeffPair p) N 0 n := by
      simpa only [sourceIsolatingDisc,if_neg (not_le.mpr (h.threshold.trans_le hn)),
        ← h.tail n (h.threshold.trans_le hn)] using hz
    have hb := hB n hn z hza
    have hpure := (hasProd_sourceInverseSqrtGapCorrection hp hp1 t.2 z n
      (h.domain t ht n z hz)).tprod_eq
    rw [hpure]
    simpa [sourceMidpointProductRow,a] using hb

/-- The actual disk supremum is a uniformly bounded half-exponent tail sequence, including below one. -/
theorem SourceQuotientDiscEstimates.inverseSqrtGapSup
    {hp : p ≠ ⊤} {hp1 : 1 < p} {U : Set (Coeff p × CoeffPair p)}
    {D : ℤ → Set ℂ} {c R H M : ℝ} {N K : ℕ}
    (h : SourceQuotientDiscEstimates hp hp1 U D c R H M N K) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ t ∈ U,
      ∃ E : Coeff (ENNReal.ofReal (p.toReal/2)), ‖E‖ ≤ L ∧
        (∀ n : ℤ, K ≤ n.natAbs → E n =
          ((sSup ((fun z => ‖(∏' m : {m : ℤ // m ≠ n},
            (Complex.sqrt (1-sourceSingleRootGapRadicand hp hp1 t.2 m z))⁻¹)-1‖) '' D n) : ℝ) : ℂ)) ∧
        (∀ n : ℤ, n.natAbs < K → E n = 0) := by
  obtain ⟨L,hL,hbound⟩ := h.inverseSqrtGapMajorant
  refine ⟨L,hL,?_⟩
  intro t ht
  obtain ⟨B,hBn,hB⟩ := hbound t ht
  let f (n : ℤ) (z : ℂ) := ‖(∏' m : {m : ℤ // m ≠ n},
    (Complex.sqrt (1-sourceSingleRootGapRadicand hp hp1 t.2 m z))⁻¹)-1‖
  let F : ℤ → ℂ := fun n => if K ≤ n.natAbs then (sSup (f n '' D n) : ℝ) else 0
  have hF (n : ℤ) : ‖F n‖ ≤ ‖B n‖ := by
    by_cases hn : K ≤ n.natAbs
    · have hbounded : BddAbove (f n '' D n) := by
        refine ⟨‖B n‖,?_⟩
        rintro _ ⟨z,hz,rfl⟩
        exact hB n hn z hz
      obtain ⟨z,hz⟩ := h.nonempty n
      have hnonneg : 0 ≤ sSup (f n '' D n) :=
        (norm_nonneg _).trans (le_csSup hbounded ⟨z,hz,rfl⟩)
      simp only [F,if_pos hn,Complex.norm_real,Real.norm_of_nonneg hnonneg]
      apply csSup_le ((h.nonempty n).image _)
      rintro _ ⟨w,hw,rfl⟩
      exact hB n hn w hw
    · simp only [F,if_neg hn,norm_zero]
      exact norm_nonneg _
  let E : Coeff (ENNReal.ofReal (p.toReal/2)) := ⟨F,(lp.memℓp B).mono' hF⟩
  have hhalf : ENNReal.ofReal (p.toReal/2) ≠ 0 := by
    have hpr := ENNReal.toReal_pos (zero_lt_one.trans hp1).ne' hp
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))
  refine ⟨E,(lp.norm_mono hhalf hF).trans hBn,?_,?_⟩
  · intro n hn
    simp only [E,F,if_pos hn]
    rfl
  · intro n hn
    simp only [E,F,if_neg (not_le.mpr hn)]

end NLS.ZakharovShabat
