import NLS.ZakharovShabat.DoubleResolventEstimates
import Mathlib.Analysis.Convex.PathConnected

/-!
# Uniform high-frequency resolvents on potential neighborhoods

The reciprocal factor tends to zero, and Fourier remainders are contractive
and decrease with the cutoff. A bound on the full potential and one remainder
therefore gives a common high-frequency resolvent region. The neighborhood
can be chosen open and convex and to contain both the given potential and zero.
-/

open scoped ENNReal Topology
open Filter
noncomputable section

namespace NLS.ZakharovShabat

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The symmetric pair remainder as a continuous linear operator. -/
def pairFourierTailCLM (N : ℕ) : PairSpace p →L[ℂ] PairSpace p :=
  (ContinuousLinearMap.id ℂ (Coeff p) - Coeff.truncateCLM (Coeff.lowFrequencies N)).prodMap
    (ContinuousLinearMap.id ℂ (Coeff p) - Coeff.truncateCLM (Coeff.lowFrequencies N))

@[simp] theorem pairFourierTailCLM_apply (N : ℕ) (φ : PairSpace p) :
    pairFourierTailCLM N φ = pairFourierTail N φ := rfl

@[simp] theorem pairFourierTail_zero_potential (N : ℕ) : pairFourierTail N (0 : PairSpace p) = 0 :=
  (pairFourierTailCLM N).map_zero

theorem norm_pairFourierTail_antitone (φ : PairSpace p) :
    Antitone (fun N => ‖pairFourierTail N φ‖) := by
  intro M N hMN
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (show 1 ≤ p from Fact.out)).ne'
  exact max_le_max (Coeff.norm_fourierTail_antitone hp0 φ.1 hMN)
    (Coeff.norm_fourierTail_antitone hp0 φ.2 hMN)

/-- Bounding the full potential and one symmetric tail gives a useful neighborhood. -/
def frequencyNeighborhood (N : ℕ) (M δ : ℝ) : Set (PairSpace p) :=
  Metric.ball 0 M ∩ (pairFourierTailCLM N) ⁻¹' Metric.ball 0 δ

@[simp] theorem mem_frequencyNeighborhood (N : ℕ) (M δ : ℝ) (ψ : PairSpace p) :
    ψ ∈ frequencyNeighborhood N M δ ↔ ‖ψ‖ < M ∧ ‖pairFourierTail N ψ‖ < δ := by
  simp [frequencyNeighborhood]

theorem isOpen_frequencyNeighborhood (N : ℕ) (M δ : ℝ) :
    IsOpen (frequencyNeighborhood (p := p) N M δ) :=
  Metric.isOpen_ball.inter (Metric.isOpen_ball.preimage (pairFourierTailCLM N).continuous)

theorem convex_frequencyNeighborhood (N : ℕ) (M δ : ℝ) :
    Convex ℝ (frequencyNeighborhood (p := p) N M δ) :=
  (convex_ball (0 : PairSpace p) M).inter
    ((convex_ball (0 : PairSpace p) δ).linear_preimage
      ((pairFourierTailCLM N).restrictScalars ℝ).toLinearMap)

theorem zero_mem_frequencyNeighborhood (N : ℕ) {M δ : ℝ} (hM : 0 < M) (hδ : 0 < δ) :
    (0 : PairSpace p) ∈ frequencyNeighborhood N M δ := by
  change 0 ∈ Metric.ball 0 M ∩ (pairFourierTailCLM N) ⁻¹' Metric.ball 0 δ
  simpa using And.intro hM hδ

/-- The reciprocal-frequency contribution vanishes at every finite Banach exponent. -/
theorem tendsto_frequency_reciprocal_zero (hp : p ≠ ⊤) (M : ℝ) :
    Tendsto (fun N : ℕ => M / (N : ℝ) ^ (1 / p.toReal)) atTop (𝓝 0) := by
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos
    (zero_lt_one.trans_le (show 1 ≤ p from Fact.out)).ne' hp
  have hpow : Tendsto (fun N : ℕ => (N : ℝ) ^ (1 / p.toReal)) atTop atTop :=
    (tendsto_rpow_atTop (by positivity : 0 < 1 / p.toReal)).comp tendsto_natCast_atTop_atTop
  exact tendsto_const_nhds.div_atTop hpow

/-- An open convex neighborhood containing zero has a uniform half-size
squared Neumann bound at all sufficiently large Fourier indices. -/
theorem exists_uniform_frequencyNeighborhood (hp : p ≠ ⊤) (φ : PairSpace p)
    {r : ℝ} (hr : 0 < r) :
    ∃ N : ℕ, ∃ U : Set (PairSpace p), IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      (∀ ψ ∈ U, ‖ψ‖ < ‖φ‖ + 1) ∧
      ∀ ψ ∈ U, ∀ n : ℤ, N ≤ n.natAbs →
        ‖ψ‖ * ((32 * p.toReal ^ 2 / r ^ 2) *
          (‖ψ‖ / |(n : ℝ)| ^ (1 / p.toReal) + ‖pairFourierTail n.natAbs ψ‖)) ≤ 1 / 2 := by
  let M := ‖φ‖ + 1
  let C := 32 * p.toReal ^ 2 / r ^ 2
  have hM : 0 < M := by dsimp [M]; positivity
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos
    (zero_lt_one.trans_le (show 1 ≤ p from Fact.out)).ne' hp
  have hC : 0 < C := by dsimp [C]; positivity
  let δ := 1 / (4 * M * C)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have ht := (tendsto_pairFourierTail hp φ).norm
  simp only [norm_zero] at ht
  have hevent : ∀ᶠ N : ℕ in atTop,
      ‖pairFourierTail N φ‖ < δ ∧ M / (N : ℝ) ^ (1 / p.toReal) < δ :=
    (ht.eventually_lt_const hδ).and ((tendsto_frequency_reciprocal_zero hp M).eventually_lt_const hδ)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  let U : Set (PairSpace p) := frequencyNeighborhood N M δ
  refine ⟨N, U, isOpen_frequencyNeighborhood N M δ, convex_frequencyNeighborhood N M δ,
    ?_, zero_mem_frequencyNeighborhood N hM hδ, ?_, ?_⟩
  · exact (mem_frequencyNeighborhood N M δ φ).mpr ⟨by dsimp [M]; linarith, (hN N le_rfl).1⟩
  · intro ψ hψ
    exact ((mem_frequencyNeighborhood N M δ ψ).mp hψ).1
  · intro ψ hψ n hn
    obtain ⟨hψM, hψT⟩ := (mem_frequencyNeighborhood N M δ ψ).mp hψ
    have htail : ‖pairFourierTail n.natAbs ψ‖ ≤ δ :=
      (norm_pairFourierTail_antitone ψ hn).trans hψT.le
    have hrec : ‖ψ‖ / |(n : ℝ)| ^ (1 / p.toReal) ≤ δ := by
      have he : |(n : ℝ)| = (n.natAbs : ℝ) := by simp only [Nat.cast_natAbs, Int.cast_abs]
      rw [he]
      exact (div_le_div_of_nonneg_right hψM.le (by positivity)).trans (hN n.natAbs hn).2.le
    change ‖ψ‖ * (C * (_ + _)) ≤ _
    calc
      _ ≤ M * (C * (δ + δ)) := by gcongr
      _ = 1 / 2 := by dsimp [δ]; field_simp; ring

/-- The neighborhood above puts all sufficiently far punctured strips in the resolvent set. -/
theorem exists_uniform_highFrequency_resolvent (hp : p ≠ ⊤) (φ : PairSpace p)
    {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi / 4) :
    ∃ N : ℕ, ∃ U : Set (PairSpace p), IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      (∀ ψ ∈ U, ‖ψ‖ < ‖φ‖ + 1) ∧
      ∀ ψ ∈ U, ∀ n : ℤ, N ≤ n.natAbs → verticalStrip n r ⊆ resolventSet hp ψ := by
  obtain ⟨N, U, ho, hc, hφ, h0, hnorm, hsmall⟩ := exists_uniform_frequencyNeighborhood hp φ hr
  refine ⟨N, U, ho, hc, hφ, h0, hnorm, ?_⟩
  intro ψ hψ n hn z hz
  exact mem_resolventSet_of_frequencyTail hp ψ hr hrπ hz ((hsmall ψ hψ n hn).trans_lt (by norm_num))

end NLS.ZakharovShabat
