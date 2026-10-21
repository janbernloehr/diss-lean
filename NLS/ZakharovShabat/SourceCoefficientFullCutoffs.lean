import NLS.ZakharovShabat.FullCutoffSummability
import NLS.ZakharovShabat.SourceLemma6_8

/-! # Sharper corrected Section 6 cutoff estimates

The original source norms and spectral data are retained. The additive leading-tail
term is not removed; the refuted printed estimates are not asserted.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The original coefficient estimate retains the full-cutoff Fourier tail. -/
theorem exists_uniform_diagonalSummability_fullCutoff (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ∀ N : ℕ, N₀ ≤ N →
        Summable (fun n : ℤ => if N ≤ n.natAbs then (resonantDiagonalSup hp w ψ n)^p.toReal else 0) ∧
        (∑' n : ℤ, if N ≤ n.natAbs then (resonantDiagonalSup hp w ψ n)^p.toReal else 0) ≤
          diagonalSummationConstant p * ‖w.forgetPairWeight ψ‖^p.toReal *
            (‖w.forgetPairWeight ψ‖^p.toReal / (N : ℝ)^(min 1 (p.toReal-1)) +
              ‖weightedPairFourierTail SpectralWeight.one.toWeight N (w.forgetPairWeight ψ)‖^p.toReal) := by
  obtain ⟨N₀, hN₀, U, ho, hc, hφ, h0, hb⟩ := exists_uniform_resonantDiagonalSup hp w φ
  refine ⟨N₀, hN₀, U, ho, hc, hφ, h0, ?_⟩
  intro ψ hψ N hN
  have hbound (n : ℤ) (hn : N ≤ n.natAbs) :
      0 ≤ resonantDiagonalSup hp w ψ n ∧
      resonantDiagonalSup hp w ψ n ≤ resonantDiagonalBound hp w ψ n := ⟨(hb ψ hψ n (hN.trans hn)).1, (hb ψ hψ n (hN.trans hn)).2.1⟩
  exact ⟨summable_diagonalSup_tail hp hp1 w ψ N (by omega) hbound,
    diagonalSup_tail_sum_le_pair_fullCutoff hp hp1 w ψ N (by omega) hbound⟩

/-- The original coefficient estimate retains the full-cutoff Fourier tail. -/
theorem exists_uniform_offDiagonalSummability_fullCutoff (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ∀ N : ℕ, N₀ ≤ N →
        (Summable (fun n : ℤ => if N ≤ n.natAbs then (resonantBMinusRemainderSup hp w ψ n)^p.toReal else 0) ∧
          (∑' n : ℤ, if N ≤ n.natAbs then (resonantBMinusRemainderSup hp w ψ n)^p.toReal else 0) ≤
            offDiagonalSummationConstant p * ‖ψ.fst‖^p.toReal *
              (‖ψ‖^(2*p.toReal) / (N : ℝ)^(min 1 (p.toReal-1)) +
                ‖weightedPairFourierTail w.toWeight N ψ‖^(2*p.toReal))) ∧
        (Summable (fun n : ℤ => if N ≤ n.natAbs then (resonantBPlusRemainderSup hp w ψ n)^p.toReal else 0) ∧
          (∑' n : ℤ, if N ≤ n.natAbs then (resonantBPlusRemainderSup hp w ψ n)^p.toReal else 0) ≤
            offDiagonalSummationConstant p * ‖ψ.snd‖^p.toReal *
              (‖ψ‖^(2*p.toReal) / (N : ℝ)^(min 1 (p.toReal-1)) +
                ‖weightedPairFourierTail w.toWeight N ψ‖^(2*p.toReal))) := by
  obtain ⟨N₀, hN₀, U, ho, hc, hφ, h0, hb⟩ := exists_uniform_offDiagonalSup hp hp1 w φ
  refine ⟨N₀, hN₀, U, ho, hc, hφ, h0, ?_⟩
  intro ψ hψ N hN
  exact ⟨resonantBMinusSup_tail_summable_and_le_fullCutoff hp hp1 w ψ N (hN₀.trans hN)
      (fun n hn => (hb ψ hψ N hN n hn).1),
    resonantBPlusSup_tail_summable_and_le_fullCutoff hp hp1 w ψ N (hN₀.trans hN)
      (fun n hn => (hb ψ hψ N hN n hn).2.1)⟩

/-- The original coefficient estimate retains the full-cutoff Fourier tail. -/
def sourceDiagonalTailBudget_fullCutoff (φ : CoeffPair p) (N : ℕ) : ℝ :=
  diagonalSummationConstant p * ‖φ‖^p.toReal *
    (‖φ‖^p.toReal / (N : ℝ)^(min 1 (p.toReal-1)) + ‖sourceFourierTail N φ‖^p.toReal)

/-- The original coefficient estimate retains the full-cutoff Fourier tail. -/
theorem sourceDiagonalTailBudget_weightedInput_fullCutoff (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (N : ℕ) :
    sourceDiagonalTailBudget_fullCutoff (sourceWeightedPeriodTwoInput w φ) N =
      diagonalSummationConstant p * ‖w.forgetPairWeight φ‖^p.toReal *
        (‖w.forgetPairWeight φ‖^p.toReal / (N : ℝ)^(min 1 (p.toReal-1)) +
          ‖weightedPairFourierTail SpectralWeight.one.toWeight N (w.forgetPairWeight φ)‖^p.toReal) := by
  rw [← unitWeightedPairEquiv_sourceWeightedInput w φ]
  simp only [sourceDiagonalTailBudget_fullCutoff,weightedPairFourierTail_unitWeightedPairEquiv,LinearIsometryEquiv.norm_map]

/-- The original coefficient estimate retains the full-cutoff Fourier tail. -/
def sourceOffDiagonalTailBudget_fullCutoff (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight p)
    (componentNorm : ℝ) (N : ℕ) : ℝ :=
  offDiagonalSummationConstant p * componentNorm^p.toReal *
    (‖φ‖^(2*p.toReal) / (N : ℝ)^(min 1 (p.toReal-1)) +
      ‖weightedPairFourierTail w.toWeight N φ‖^(2*p.toReal))

/-- The original coefficient estimate retains the full-cutoff Fourier tail. -/
theorem sourceOffDiagonalTailBudget_unit_fullCutoff (φ : CoeffPair p) (c : ℝ) (N : ℕ) :
    sourceOffDiagonalTailBudget_fullCutoff SpectralWeight.one (unitWeightedPairEquiv φ) c N =
      offDiagonalSummationConstant p * c^p.toReal *
        (‖φ‖^(2*p.toReal) / (N : ℝ)^(min 1 (p.toReal-1)) + ‖sourceFourierTail N φ‖^(2*p.toReal)) := by
  simp only [sourceOffDiagonalTailBudget_fullCutoff,weightedPairFourierTail_unitWeightedPairEquiv,LinearIsometryEquiv.norm_map]

/-- The original coefficient estimate retains the full-cutoff Fourier tail. -/
def SourceCoefficientTailEstimates_fullCutoff (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (N : ℕ) : Prop :=
  let ψ := sourceWeightedPeriodTwoInput w φ
  (Summable (sourceCoefficientPowerTail p N (sourceResonantDiagonalSup hp ψ)) ∧
    (∑' n : ℤ, sourceCoefficientPowerTail p N (sourceResonantDiagonalSup hp ψ) n) ≤ sourceDiagonalTailBudget_fullCutoff ψ N) ∧
  (Summable (sourceCoefficientPowerTail p N (sourceResonantBMinusSup hp w ψ)) ∧
    (∑' n : ℤ, sourceCoefficientPowerTail p N (sourceResonantBMinusSup hp w ψ) n) ≤ sourceOffDiagonalTailBudget_fullCutoff w φ ‖φ.fst‖ N) ∧
  (Summable (sourceCoefficientPowerTail p N (sourceResonantBPlusSup hp w ψ)) ∧
    (∑' n : ℤ, sourceCoefficientPowerTail p N (sourceResonantBPlusSup hp w ψ) n) ≤ sourceOffDiagonalTailBudget_fullCutoff w φ ‖φ.snd‖ N)

/-- The original coefficient estimate retains the full-cutoff Fourier tail. -/
theorem sourceLemma6_8_summability_fullCutoff (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ∀ N : ℕ, N₀ ≤ N → SourceCoefficientTailEstimates_fullCutoff hp w ψ N := by
  obtain ⟨Na,hNa,Ua,hoa,hca,hφa,h0a,ha⟩ := exists_uniform_diagonalSummability_fullCutoff hp hp1 w φ
  obtain ⟨Nb,hNb,Ub,hob,hcb,hφb,h0b,hb⟩ := exists_uniform_offDiagonalSummability_fullCutoff hp hp1 w φ
  obtain ⟨Ne,hNe,Ue,hoe,hce,hφe,h0e,he⟩ := exists_uniform_sourceResonantSup_eq hp w φ
  refine ⟨max Na (max Nb Ne),by omega,Ua ∩ Ub ∩ Ue,(hoa.inter hob).inter hoe,
    (hca.inter hcb).inter hce,⟨⟨hφa,hφb⟩,hφe⟩,⟨⟨h0a,h0b⟩,h0e⟩,?_⟩
  intro ψ hψ N hN
  have hea : sourceCoefficientPowerTail p N (sourceResonantDiagonalSup hp (sourceWeightedPeriodTwoInput w ψ)) =
      fun n : ℤ => if N ≤ n.natAbs then (resonantDiagonalSup hp w ψ n)^p.toReal else 0 := by
    funext n
    unfold sourceCoefficientPowerTail
    split_ifs with hn
    · rw [(he ψ hψ.2 n (by omega)).1]
    · rfl
  have hem : sourceCoefficientPowerTail p N (sourceResonantBMinusSup hp w (sourceWeightedPeriodTwoInput w ψ)) =
      fun n : ℤ => if N ≤ n.natAbs then (resonantBMinusRemainderSup hp w ψ n)^p.toReal else 0 := by
    funext n
    unfold sourceCoefficientPowerTail
    split_ifs with hn
    · rw [(he ψ hψ.2 n (by omega)).2.1]
    · rfl
  have hep : sourceCoefficientPowerTail p N (sourceResonantBPlusSup hp w (sourceWeightedPeriodTwoInput w ψ)) =
      fun n : ℤ => if N ≤ n.natAbs then (resonantBPlusRemainderSup hp w ψ n)^p.toReal else 0 := by
    funext n
    unfold sourceCoefficientPowerTail
    split_ifs with hn
    · rw [(he ψ hψ.2 n (by omega)).2.2]
    · rfl
  unfold SourceCoefficientTailEstimates_fullCutoff
  dsimp only
  rw [hea,hem,hep,sourceDiagonalTailBudget_weightedInput_fullCutoff]
  exact ⟨ha ψ hψ.1.1 N (by omega),hb ψ hψ.1.2 N (by omega)⟩

/-- The original coefficient estimate retains the full-cutoff Fourier tail. -/
theorem sourceLemma6_8_quantitative_fullCutoff (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      (∀ ψ ∈ U, ∀ n : ℤ, N₀ ≤ n.natAbs → SourceCoefficientStripBounds hp w (sourceWeightedPeriodTwoInput w ψ) n) ∧
      (∀ ψ ∈ U, ∀ N : ℕ, N₀ ≤ N → SourceCoefficientTailEstimates_fullCutoff hp w ψ N) := by
  obtain ⟨Ns,hNs,Us,hos,hcs,hφs,h0s,hs⟩ := sourceLemma6_8_summability_fullCutoff hp hp1 w φ
  obtain ⟨Nb,hNb,Ub,hob,hcb,hφb,h0b,hb⟩ := exists_uniform_sourceCoefficientStripBounds hp hp1 w φ
  exact ⟨max Ns Nb,by omega,Us ∩ Ub,hos.inter hob,hcs.inter hcb,⟨hφs,hφb⟩,⟨h0s,h0b⟩,
    fun ψ hψ n hn => hb ψ hψ.2 n (by omega),fun ψ hψ N hN => hs ψ hψ.1 N (by omega)⟩

/-- The original coefficient estimate retains the full-cutoff Fourier tail. -/
theorem sourceLemma6_8_unweighted_fullCutoff (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (CoeffPair p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U,
        (∀ n : ℤ, N₀ ≤ n.natAbs → SourceCoefficientStripBounds hp SpectralWeight.one ψ n) ∧
        (∀ N : ℕ, N₀ ≤ N → SourceCoefficientTailEstimates_fullCutoff hp SpectralWeight.one (unitWeightedPairEquiv ψ) N) := by
  have h := sourceLemma6_8_quantitative_fullCutoff hp hp1 SpectralWeight.one (unitWeightedPairEquiv φ)
  have ht : ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ V : Set (WeightedCoeffPair SpectralWeight.one.toWeight p),
      IsOpen V ∧ Convex ℝ V ∧ unitWeightedPairEquiv φ ∈ V ∧ 0 ∈ V ∧
      ∀ ψ ∈ V,
        (∀ n : ℤ, N₀ ≤ n.natAbs → SourceCoefficientStripBounds hp SpectralWeight.one (sourceWeightedPeriodTwoInput SpectralWeight.one ψ) n) ∧
        (∀ N : ℕ, N₀ ≤ N → SourceCoefficientTailEstimates_fullCutoff hp SpectralWeight.one ψ N) := by
    obtain ⟨N,hN,V,ho,hc,hφ,h0,hb,hs⟩ := h
    exact ⟨N,hN,V,ho,hc,hφ,h0,fun ψ hψ => ⟨hb ψ hψ,hs ψ hψ⟩⟩
  have hpull := sourceUnitWeightedUniformPullback unitWeightedPairEquiv φ _ ht
  simpa only [sourceWeightedInput_unitWeightedPairEquiv] using hpull

end NLS.ZakharovShabat
