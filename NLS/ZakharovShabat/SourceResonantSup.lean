import NLS.ZakharovShabat.SourceResonantAnalytic
import NLS.ZakharovShabat.ResonantDiagonalSup
import NLS.ZakharovShabat.OffDiagonalSup

/-!
# Full-strip suprema of the original resonant coefficients

The suprema use the original coefficient functions on the entire closed strip.
Weight compatibility identifies the actual images, not just their majorants.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The full-strip supremum of the original diagonal coefficient. -/
def sourceResonantDiagonalSup (hp : p ≠ ⊤) (φ : CoeffPair p) (n : ℤ) : ℝ :=
  sSup ((fun z : ℂ => ‖sourceResonantAFunction hp φ n z‖) '' resonantStrip n)

/-- The weighted full-strip supremum of the original negative remainder. -/
def sourceResonantBMinusSup (hp : p ≠ ⊤) (w : SpectralWeight) (φ : CoeffPair p) (n : ℤ) : ℝ :=
  weightedStripSup w n (fun z => sourceResonantBMinusFunction hp φ n z - φ.fst (-(2*n)))

/-- The weighted full-strip supremum of the original positive remainder. -/
def sourceResonantBPlusSup (hp : p ≠ ⊤) (w : SpectralWeight) (φ : CoeffPair p) (n : ℤ) : ℝ :=
  weightedStripSup w n (fun z => sourceResonantBPlusFunction hp φ n z - φ.snd (2*n))

/-- Equality of coefficient functions on a whole strip gives equality of all three actual suprema. -/
theorem sourceResonantSup_eq_weighted (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ)
    (heq : ∀ z ∈ resonantStrip n,
      sourceResonantAFunction hp (sourceWeightedPeriodTwoInput w φ) n z = weightedResonantAExtension hp w φ n z ∧
      sourceResonantBPlusFunction hp (sourceWeightedPeriodTwoInput w φ) n z = weightedResonantBPlusExtension hp w φ n z ∧
      sourceResonantBMinusFunction hp (sourceWeightedPeriodTwoInput w φ) n z = weightedResonantBMinusExtension hp w φ n z) :
    sourceResonantDiagonalSup hp (sourceWeightedPeriodTwoInput w φ) n = resonantDiagonalSup hp w φ n ∧
    sourceResonantBMinusSup hp w (sourceWeightedPeriodTwoInput w φ) n = resonantBMinusRemainderSup hp w φ n ∧
    sourceResonantBPlusSup hp w (sourceWeightedPeriodTwoInput w φ) n = resonantBPlusRemainderSup hp w φ n := by
  refine ⟨?_,?_,?_⟩
  · unfold sourceResonantDiagonalSup resonantDiagonalSup
    apply congrArg sSup
    apply Set.image_congr
    intro z hz
    rw [(heq z hz).1]
  · unfold sourceResonantBMinusSup resonantBMinusRemainderSup weightedStripSup
    apply congrArg sSup
    apply Set.image_congr
    intro z hz
    simp only [(heq z hz).2.2,sourceWeightedPeriodTwoInput_fst]
  · unfold sourceResonantBPlusSup resonantBPlusRemainderSup weightedStripSup
    apply congrArg sSup
    apply Set.image_congr
    intro z hz
    simp only [(heq z hz).2.1,sourceWeightedPeriodTwoInput_snd]

/-- One neighborhood and cutoff identify the original and weighted strip suprema. -/
theorem exists_uniform_sourceResonantSup_eq (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ∀ n : ℤ, N ≤ n.natAbs →
        sourceResonantDiagonalSup hp (sourceWeightedPeriodTwoInput w ψ) n = resonantDiagonalSup hp w ψ n ∧
        sourceResonantBMinusSup hp w (sourceWeightedPeriodTwoInput w ψ) n = resonantBMinusRemainderSup hp w ψ n ∧
        sourceResonantBPlusSup hp w (sourceWeightedPeriodTwoInput w ψ) n = resonantBPlusRemainderSup hp w ψ n := by
  obtain ⟨N,hN,U,ho,hc,hφ,h0,heq⟩ := exists_uniform_sourceResonantFunctions_weightedInput hp w φ
  exact ⟨N,hN,U,ho,hc,hφ,h0,fun ψ hψ n hn => sourceResonantSup_eq_weighted hp w ψ n (heq ψ hψ n hn)⟩

/-- Unit weighting identifies the diagonal supremum at every index, without a smallness condition. -/
theorem sourceResonantDiagonalSup_unit (hp : p ≠ ⊤) (φ : CoeffPair p) (n : ℤ) :
    sourceResonantDiagonalSup hp φ n = resonantDiagonalSup hp SpectralWeight.one (unitWeightedPairEquiv φ) n := rfl

/-- The actual strip images are bounded, and their suprema dominate every value. -/
def SourceCoefficientStripBounds (hp : p ≠ ⊤) (w : SpectralWeight) (φ : CoeffPair p) (n : ℤ) : Prop :=
  BddAbove ((fun z : ℂ => ‖sourceResonantAFunction hp φ n z‖) '' resonantStrip n) ∧
  BddAbove ((fun z : ℂ => w (2*n) * ‖sourceResonantBMinusFunction hp φ n z - φ.fst (-(2*n))‖) '' resonantStrip n) ∧
  BddAbove ((fun z : ℂ => w (2*n) * ‖sourceResonantBPlusFunction hp φ n z - φ.snd (2*n)‖) '' resonantStrip n) ∧
  0 ≤ sourceResonantDiagonalSup hp φ n ∧ 0 ≤ sourceResonantBMinusSup hp w φ n ∧ 0 ≤ sourceResonantBPlusSup hp w φ n ∧
  ∀ z ∈ resonantStrip n,
    ‖sourceResonantAFunction hp φ n z‖ ≤ sourceResonantDiagonalSup hp φ n ∧
    w (2*n) * ‖sourceResonantBMinusFunction hp φ n z - φ.fst (-(2*n))‖ ≤ sourceResonantBMinusSup hp w φ n ∧
    w (2*n) * ‖sourceResonantBPlusFunction hp φ n z - φ.snd (2*n)‖ ≤ sourceResonantBPlusSup hp w φ n

/-- Uniform majorants establish genuine full-strip suprema for the original functions. -/
theorem sourceCoefficientStripBounds_of_bound (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : CoeffPair p) (n : ℤ) (A M P : ℝ)
    (hb : ∀ z ∈ resonantStrip n,
      ‖sourceResonantAFunction hp φ n z‖ ≤ A ∧
      w (2*n) * ‖sourceResonantBMinusFunction hp φ n z - φ.fst (-(2*n))‖ ≤ M ∧
      w (2*n) * ‖sourceResonantBPlusFunction hp φ n z - φ.snd (2*n)‖ ≤ P) :
    SourceCoefficientStripBounds hp w φ n := by
  have hba : BddAbove ((fun z : ℂ => ‖sourceResonantAFunction hp φ n z‖) '' resonantStrip n) := by
    refine ⟨A,?_⟩
    rintro _ ⟨z,hz,rfl⟩
    exact (hb z hz).1
  have hbm : BddAbove ((fun z : ℂ => w (2*n) * ‖sourceResonantBMinusFunction hp φ n z - φ.fst (-(2*n))‖) '' resonantStrip n) := by
    refine ⟨M,?_⟩
    rintro _ ⟨z,hz,rfl⟩
    exact (hb z hz).2.1
  have hbp : BddAbove ((fun z : ℂ => w (2*n) * ‖sourceResonantBPlusFunction hp φ n z - φ.snd (2*n)‖) '' resonantStrip n) := by
    refine ⟨P,?_⟩
    rintro _ ⟨z,hz,rfl⟩
    exact (hb z hz).2.2
  have ha (z : ℂ) (hz : z ∈ resonantStrip n) :
      ‖sourceResonantAFunction hp φ n z‖ ≤ sourceResonantDiagonalSup hp φ n := le_csSup hba ⟨z,hz,rfl⟩
  have hm := weightedStripSup_bounds w n (fun z => sourceResonantBMinusFunction hp φ n z - φ.fst (-(2*n))) M
    (fun z hz => (hb z hz).2.1)
  have hp' := weightedStripSup_bounds w n (fun z => sourceResonantBPlusFunction hp φ n z - φ.snd (2*n)) P
    (fun z hz => (hb z hz).2.2)
  exact ⟨hba,hbm,hbp,(norm_nonneg _).trans (ha _ (center_mem_resonantStrip n)),hm.1,hp'.1,
    fun z hz => ⟨ha z hz,hm.2.2 z hz,hp'.2.2 z hz⟩⟩

/-- The full original coefficient images are bounded uniformly on distant strips. -/
theorem exists_uniform_sourceCoefficientStripBounds (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N : ℕ, 2 ≤ N ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ∀ n : ℤ, N ≤ n.natAbs → SourceCoefficientStripBounds hp w (sourceWeightedPeriodTwoInput w ψ) n := by
  obtain ⟨Na,hNa,Ua,hoa,hca,hφa,h0a,ha⟩ := exists_uniform_resonantDiagonalBound hp w φ
  obtain ⟨Nb,hNb,Ub,hob,hcb,hφb,h0b,hb⟩ := exists_uniform_offDiagonalTailBound hp hp1 w φ
  obtain ⟨Ne,hNe,Ue,hoe,hce,hφe,h0e,he⟩ := exists_uniform_sourceResonantFunctions_weightedInput hp w φ
  refine ⟨max Na (max Nb Ne),by omega,Ua ∩ Ub ∩ Ue,(hoa.inter hob).inter hoe,
    (hca.inter hcb).inter hce,⟨⟨hφa,hφb⟩,hφe⟩,⟨⟨h0a,h0b⟩,h0e⟩,?_⟩
  intro ψ hψ n hn
  apply sourceCoefficientStripBounds_of_bound hp w _ n (resonantDiagonalBound hp w ψ n)
    (offDiagonalTailBound hp w (w.reflection ψ.fst) ψ.snd Nb n)
    (offDiagonalTailBound hp w ψ.snd (w.reflection ψ.fst) Nb n)
  intro z hz
  obtain ⟨_,_,ha'⟩ := ha ψ hψ.1.1 n (by omega) z hz
  obtain ⟨hm,hp'⟩ := hb ψ hψ.1.2 Nb le_rfl n (by omega) z hz
  obtain ⟨hea,hep,hem⟩ := he ψ hψ.2 n (by omega) z hz
  simpa only [hea,hem,hep,sourceWeightedPeriodTwoInput_fst,sourceWeightedPeriodTwoInput_snd] using ⟨ha',hm,hp'⟩

end NLS.ZakharovShabat
