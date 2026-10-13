import NLS.ZakharovShabat.SourceResonantSup
import NLS.ZakharovShabat.DiagonalSummability
import NLS.ZakharovShabat.OffDiagonalSummability

/-!
# Quantitative coefficient tails in the original source realization

The diagonal estimate uses the original unweighted component-sum norm.
The off-diagonal estimates use p-power sums and the full weighted pair norm,
as in the source's concluding proof, rather than its literal printed (ii).
All quantitative statements require 1 < p < ∞; N/2 is natural division.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Lemma 6.8(i)'s budget in the exact original unweighted norm. -/
def sourceDiagonalTailBudget (φ : CoeffPair p) (N : ℕ) : ℝ :=
  diagonalSummationConstant p * ‖φ‖^p.toReal *
    (‖φ‖^p.toReal / (N : ℝ)^(min 1 (p.toReal-1)) + ‖sourceFourierTail (N/2) φ‖^p.toReal)

/-- Forgetting a weight gives exactly the original diagonal budget, with the same tail cutoff. -/
theorem sourceDiagonalTailBudget_weightedInput (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (N : ℕ) :
    sourceDiagonalTailBudget (sourceWeightedPeriodTwoInput w φ) N =
      diagonalSummationConstant p * ‖w.forgetPairWeight φ‖^p.toReal *
        (‖w.forgetPairWeight φ‖^p.toReal / (N : ℝ)^(min 1 (p.toReal-1)) +
          ‖weightedPairFourierTail SpectralWeight.one.toWeight (N/2) (w.forgetPairWeight φ)‖^p.toReal) := by
  rw [← unitWeightedPairEquiv_sourceWeightedInput w φ]
  simp only [sourceDiagonalTailBudget,weightedPairFourierTail_unitWeightedPairEquiv,LinearIsometryEquiv.norm_map]

/-- Proof-consistent off-diagonal budget, retaining the distinguished component norm. -/
def sourceOffDiagonalTailBudget (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight p)
    (componentNorm : ℝ) (N : ℕ) : ℝ :=
  offDiagonalSummationConstant p * componentNorm^p.toReal *
    (‖φ‖^(2*p.toReal) / (N : ℝ)^(min 1 (p.toReal-1)) +
      ‖weightedPairFourierTail w.toWeight (N/2) φ‖^(2*p.toReal))

/-- The unit-weight off-diagonal budget uses exactly the original norm and tail. -/
theorem sourceOffDiagonalTailBudget_unit (φ : CoeffPair p) (c : ℝ) (N : ℕ) :
    sourceOffDiagonalTailBudget SpectralWeight.one (unitWeightedPairEquiv φ) c N =
      offDiagonalSummationConstant p * c^p.toReal *
        (‖φ‖^(2*p.toReal) / (N : ℝ)^(min 1 (p.toReal-1)) + ‖sourceFourierTail (N/2) φ‖^(2*p.toReal)) := by
  simp only [sourceOffDiagonalTailBudget,weightedPairFourierTail_unitWeightedPairEquiv,LinearIsometryEquiv.norm_map]

/-- Unit weighting preserves each distinguished component norm. -/
theorem sourceUnitWeighted_component_norms (φ : CoeffPair p) :
    ‖(unitWeightedPairEquiv φ).fst‖ = ‖φ.fst‖ ∧ ‖(unitWeightedPairEquiv φ).snd‖ = ‖φ.snd‖ := by
  constructor
  · change ‖(WeightedCoeff.weightIsometry SpectralWeight.one.toWeight p).symm φ.fst‖ = _
    exact LinearIsometryEquiv.norm_map _ _
  · change ‖(WeightedCoeff.weightIsometry SpectralWeight.one.toWeight p).symm φ.snd‖ = _
    exact LinearIsometryEquiv.norm_map _ _

/-- Full signed p-power tail, including the cutoff boundary. -/
def sourceCoefficientPowerTail (p : ℝ≥0∞) (N : ℕ) (a : ℤ → ℝ) (n : ℤ) : ℝ :=
  if N ≤ n.natAbs then (a n)^p.toReal else 0

/-- All three source coefficient tails are summable and satisfy their exact budgets. -/
def SourceCoefficientTailEstimates (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (N : ℕ) : Prop :=
  let ψ := sourceWeightedPeriodTwoInput w φ
  (Summable (sourceCoefficientPowerTail p N (sourceResonantDiagonalSup hp ψ)) ∧
    (∑' n : ℤ, sourceCoefficientPowerTail p N (sourceResonantDiagonalSup hp ψ) n) ≤ sourceDiagonalTailBudget ψ N) ∧
  (Summable (sourceCoefficientPowerTail p N (sourceResonantBMinusSup hp w ψ)) ∧
    (∑' n : ℤ, sourceCoefficientPowerTail p N (sourceResonantBMinusSup hp w ψ) n) ≤ sourceOffDiagonalTailBudget w φ ‖φ.fst‖ N) ∧
  (Summable (sourceCoefficientPowerTail p N (sourceResonantBPlusSup hp w ψ)) ∧
    (∑' n : ℤ, sourceCoefficientPowerTail p N (sourceResonantBPlusSup hp w ψ) n) ≤ sourceOffDiagonalTailBudget w φ ‖φ.snd‖ N)

/-- Lemma 6.8(i) and the proof-consistent version of (ii), for actual original coefficients. -/
theorem sourceLemma6_8_summability (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ∀ N : ℕ, N₀ ≤ N → SourceCoefficientTailEstimates hp w ψ N := by
  obtain ⟨Na,hNa,Ua,hoa,hca,hφa,h0a,ha⟩ := exists_uniform_diagonalSummability hp hp1 w φ
  obtain ⟨Nb,hNb,Ub,hob,hcb,hφb,h0b,hb⟩ := exists_uniform_offDiagonalSummability hp hp1 w φ
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
  unfold SourceCoefficientTailEstimates
  dsimp only
  rw [hea,hem,hep,sourceDiagonalTailBudget_weightedInput]
  exact ⟨ha ψ hψ.1.1 N (by omega),hb ψ hψ.1.2 N (by omega)⟩

/-- Bounded full-strip images and all three quantitative estimates hold on the same neighborhood. -/
theorem sourceLemma6_8_quantitative (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      (∀ ψ ∈ U, ∀ n : ℤ, N₀ ≤ n.natAbs → SourceCoefficientStripBounds hp w (sourceWeightedPeriodTwoInput w ψ) n) ∧
      (∀ ψ ∈ U, ∀ N : ℕ, N₀ ≤ N → SourceCoefficientTailEstimates hp w ψ N) := by
  obtain ⟨Ns,hNs,Us,hos,hcs,hφs,h0s,hs⟩ := sourceLemma6_8_summability hp hp1 w φ
  obtain ⟨Nb,hNb,Ub,hob,hcb,hφb,h0b,hb⟩ := exists_uniform_sourceCoefficientStripBounds hp hp1 w φ
  exact ⟨max Ns Nb,by omega,Us ∩ Ub,hos.inter hob,hcs.inter hcb,⟨hφs,hφb⟩,⟨h0s,h0b⟩,
    fun ψ hψ n hn => hb ψ hψ.2 n (by omega),fun ψ hψ N hN => hs ψ hψ.1 N (by omega)⟩

/-- The quantitative theorem also has a neighborhood in the original unweighted source space. -/
theorem sourceLemma6_8_unweighted (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (CoeffPair p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U,
        (∀ n : ℤ, N₀ ≤ n.natAbs → SourceCoefficientStripBounds hp SpectralWeight.one ψ n) ∧
        (∀ N : ℕ, N₀ ≤ N → SourceCoefficientTailEstimates hp SpectralWeight.one (unitWeightedPairEquiv ψ) N) := by
  have h := sourceLemma6_8_quantitative hp hp1 SpectralWeight.one (unitWeightedPairEquiv φ)
  have ht : ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ V : Set (WeightedCoeffPair SpectralWeight.one.toWeight p),
      IsOpen V ∧ Convex ℝ V ∧ unitWeightedPairEquiv φ ∈ V ∧ 0 ∈ V ∧
      ∀ ψ ∈ V,
        (∀ n : ℤ, N₀ ≤ n.natAbs → SourceCoefficientStripBounds hp SpectralWeight.one (sourceWeightedPeriodTwoInput SpectralWeight.one ψ) n) ∧
        (∀ N : ℕ, N₀ ≤ N → SourceCoefficientTailEstimates hp SpectralWeight.one ψ N) := by
    obtain ⟨N,hN,V,ho,hc,hφ,h0,hb,hs⟩ := h
    exact ⟨N,hN,V,ho,hc,hφ,h0,fun ψ hψ => ⟨hb ψ hψ,hs ψ hψ⟩⟩
  have hpull := sourceUnitWeightedUniformPullback unitWeightedPairEquiv φ _ ht
  simpa only [sourceWeightedInput_unitWeightedPairEquiv] using hpull

end NLS.ZakharovShabat
