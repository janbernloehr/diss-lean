import NLS.ZakharovShabat.SourceLemma6_7
import NLS.ZakharovShabat.ResonantRealityCounterexample

/-!
# The missing reality hypothesis in the original Lemma 6.7(ii)

The single fixed original potential (1,i) has a_n(nπ)=i/(2πn).
It violates the printed unconditional conjugation identity at arbitrarily
large positive resonances where the half-contraction already holds.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A spatially constant potential in the original period-two coefficient space. -/
def sourceConstantPotential (a b : ℂ) : CoeffPair p :=
  sourceWeightedPeriodTwoInput SpectralWeight.one (constantSpectralPotential SpectralWeight.one a b)

@[simp] theorem sourceConstantPotential_fst (a b : ℂ) (k : ℤ) :
    (sourceConstantPotential (p := p) a b).fst k = if k=0 then a else 0 := by
  simp [sourceConstantPotential,constantSpectralPotential]

@[simp] theorem sourceConstantPotential_snd (a b : ℂ) (k : ℤ) :
    (sourceConstantPotential (p := p) a b).snd k = if k=0 then b else 0 := by
  simp [sourceConstantPotential,constantSpectralPotential]

@[simp] theorem unitWeightedPairEquiv_sourceConstantPotential (a b : ℂ) :
    unitWeightedPairEquiv (sourceConstantPotential (p := p) a b) =
      constantSpectralPotential SpectralWeight.one a b := by
  apply weightedPair_ext <;> intro k <;> simp [constantSpectralPotential]

/-- The actual original diagonal for constant potentials at a nonzero free center. -/
theorem sourceResonantA_constant_center (hp : p ≠ ⊤) (a b : ℂ) (n : ℤ) (hn : n ≠ 0)
    (h : ‖weightedPotentialSquareInShift hp SpectralWeight.one (unitWeightedPairEquiv (sourceConstantPotential a b)) n
      ((Real.pi : ℂ)*n) (center_mem_resonantStrip n)‖ < 1) :
    sourceResonantA hp (sourceConstantPotential a b) n ((Real.pi : ℂ)*n) (center_mem_resonantStrip n) h =
      a*b / ((2*Real.pi*(n : ℝ) : ℝ) : ℂ) := by
  simpa only [sourceResonantA,unitWeightedPairEquiv_sourceConstantPotential] using
    weightedResonantA_constant_center hp SpectralWeight.one a b n hn
      (by simpa only [unitWeightedPairEquiv_sourceConstantPotential] using h)

/-- The fixed original potential (1,i) violates diagonal reality beyond every proposed cutoff. -/
theorem exists_large_nonreal_sourceResonantA (hp : p ≠ ⊤) (M : ℕ) :
    ∃ n : ℤ, (M : ℤ) ≤ n ∧ 0 < n ∧
      ∃ h : ‖weightedPotentialSquareInShift hp SpectralWeight.one
        (unitWeightedPairEquiv (sourceConstantPotential 1 Complex.I)) n
        ((Real.pi : ℂ)*n) (center_mem_resonantStrip n)‖ < 1,
        ‖weightedPotentialSquareInShift hp SpectralWeight.one
          (unitWeightedPairEquiv (sourceConstantPotential 1 Complex.I)) n
          ((Real.pi : ℂ)*n) (center_mem_resonantStrip n)‖ ≤ 1/2 ∧
        (starRingEnd ℂ) (sourceResonantA hp (sourceConstantPotential 1 Complex.I) n
          ((Real.pi : ℂ)*n) (center_mem_resonantStrip n) h) ≠
        sourceResonantA hp (sourceConstantPotential 1 Complex.I) n
          ((Real.pi : ℂ)*n) (center_mem_resonantStrip n) h := by
  simpa only [sourceResonantA,unitWeightedPairEquiv_sourceConstantPotential] using
    exists_large_nonreal_resonantA (p := p) hp SpectralWeight.one M

/-- No individual frequency cutoff makes the printed unconditional diagonal reality claim true. -/
theorem not_sourceLemma6_7_printed_diagonal (hp : p ≠ ⊤) :
    ¬ ∃ N : ℕ, ∀ n : ℤ, N ≤ n.natAbs → ∀ z : ℂ, ∀ hz : z ∈ resonantStrip n,
      ∀ h : ‖weightedPotentialSquareInShift hp SpectralWeight.one
        (unitWeightedPairEquiv (sourceConstantPotential 1 Complex.I)) n z hz‖ < 1,
      ∀ hc : ‖weightedPotentialSquareInShift hp SpectralWeight.one
        (unitWeightedPairEquiv (sourceConstantPotential 1 Complex.I)) n
        ((starRingEnd ℂ) z) (conj_mem_resonantStrip hz)‖ < 1,
        sourceResonantA hp (sourceConstantPotential 1 Complex.I) n
          ((starRingEnd ℂ) z) (conj_mem_resonantStrip hz) hc =
        (starRingEnd ℂ) (sourceResonantA hp (sourceConstantPotential 1 Complex.I) n z hz h) := by
  rintro ⟨N,hN⟩
  obtain ⟨n,hnN,hn,h,hhalf,hne⟩ := exists_large_nonreal_sourceResonantA hp N
  have hNabs : N ≤ n.natAbs := by omega
  have hc : ‖weightedPotentialSquareInShift hp SpectralWeight.one
      (unitWeightedPairEquiv (sourceConstantPotential 1 Complex.I)) n
      ((starRingEnd ℂ) ((Real.pi : ℂ)*n)) (conj_mem_resonantStrip (center_mem_resonantStrip n))‖ < 1 := by
    simpa only [map_mul,Complex.conj_ofReal,map_intCast] using h
  have he := hN n hNabs ((Real.pi : ℂ)*n) (center_mem_resonantStrip n) h hc
  apply hne
  simpa only [map_mul,Complex.conj_ofReal,map_intCast] using he.symm

end NLS.ZakharovShabat
