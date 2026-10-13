import NLS.ZakharovShabat.SourceResonantCoefficients
import NLS.ZakharovShabat.ResonantConjugation
import NLS.ZakharovShabat.RealType

/-!
# Lemma 6.7 with the source proof's reality hypothesis

Diagonal equality holds for arbitrary complex potentials. Conjugation of the
spectral parameter requires φ*=εφ, ε²=1, for both the common diagonal and
the signed off-diagonal relation. Physical conjugation reverses Fourier indices.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Physical conjugation followed by component exchange on the original source potential. -/
def sourcePotentialStar (φ : CoeffPair p) : CoeffPair p :=
  sourceWeightedPeriodTwoInput SpectralWeight.one (weightedPotentialStar SpectralWeight.one (unitWeightedPairEquiv φ))

@[simp] theorem sourcePotentialStar_fst (φ : CoeffPair p) (k : ℤ) :
    (sourcePotentialStar φ).fst k = (starRingEnd ℂ) (φ.snd (-k)) := by
  simp [sourcePotentialStar, weightedPotentialStar]

@[simp] theorem sourcePotentialStar_snd (φ : CoeffPair p) (k : ℤ) :
    (sourcePotentialStar φ).snd k = (starRingEnd ℂ) (φ.fst (-k)) := by
  simp [sourcePotentialStar, weightedPotentialStar]

/-- The actual original-source condition φ*=εφ; ε=1 and ε=−1 give real and imaginary type. -/
def SourceHasRealitySign (ε : ℂ) (φ : CoeffPair p) : Prop := sourcePotentialStar φ = ε • φ

/-- Both raw coefficient identities of the original source reality condition. -/
theorem sourceHasRealitySign_iff_coeff (ε : ℂ) (φ : CoeffPair p) :
    SourceHasRealitySign ε φ ↔
      (∀ k, (starRingEnd ℂ) (φ.snd (-k)) = ε * φ.fst k) ∧
      (∀ k, (starRingEnd ℂ) (φ.fst (-k)) = ε * φ.snd k) := by
  constructor
  · intro h
    exact ⟨fun k => by simpa [SourceHasRealitySign] using congrArg (fun a => a.fst k) h,
      fun k => by simpa [SourceHasRealitySign] using congrArg (fun a => a.snd k) h⟩
  · rintro ⟨h₁,h₂⟩
    apply (CoeffPair.toMax p).injective
    apply Prod.ext <;> ext k
    · simpa [sourcePotentialStar,weightedPotentialStar] using h₁ k
    · simpa [sourcePotentialStar,weightedPotentialStar] using h₂ k

/-- Unit weighting preserves the physical reality sign exactly. -/
theorem sourceHasRealitySign_iff (ε : ℂ) (φ : CoeffPair p) :
    SourceHasRealitySign ε φ ↔ HasRealitySign SpectralWeight.one ε (unitWeightedPairEquiv φ) := by
  rw [sourceHasRealitySign_iff_coeff,hasRealitySign_iff]
  simp only [unitWeightedPairEquiv_fst,unitWeightedPairEquiv_snd]

/-- The sign-one condition is the existing original real-type condition. -/
theorem sourceHasRealitySign_one_iff (φ : CoeffPair p) :
    SourceHasRealitySign 1 φ ↔ IsRealType (CoeffPair.toMax p φ) := by
  rw [sourceHasRealitySign_iff_coeff]
  constructor
  · intro h k
    simpa using (h.2 k).symm
  · intro h
    exact ⟨fun k => by simpa using (h.fst_eq _ k).symm,
      fun k => by simpa using (h k).symm⟩

/-- Corrected Lemma 6.7(ii): the reality hypothesis applies to both conclusions. -/
theorem sourceLemma6_7_ii (hp : p ≠ ⊤) (ε : ℂ) (hε : ε*ε=1)
    (φ : CoeffPair p) (hφ : SourceHasRealitySign ε φ)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz‖ < 1)
    (hc : ‖weightedPotentialSquareInShift hp SpectralWeight.one (unitWeightedPairEquiv φ) n
      ((starRingEnd ℂ) z) (conj_mem_resonantStrip hz)‖ < 1) :
    sourceResonantA hp φ n ((starRingEnd ℂ) z) (conj_mem_resonantStrip hz) hc =
      (starRingEnd ℂ) (sourceResonantA hp φ n z hz h) ∧
    sourceResonantBPlus hp φ n ((starRingEnd ℂ) z) (conj_mem_resonantStrip hz) hc =
      ε * (starRingEnd ℂ) (sourceResonantBMinus hp φ n z hz h) :=
  ⟨weightedResonantA_conj hp SpectralWeight.one ε hε (unitWeightedPairEquiv φ)
      ((sourceHasRealitySign_iff ε φ).mp hφ) n z hz h hc,
    weightedResonantBPlus_conj hp SpectralWeight.one ε hε (unitWeightedPairEquiv φ)
      ((sourceHasRealitySign_iff ε φ).mp hφ) n z hz h hc⟩

/-- Either reality sign makes the common diagonal real on the real spectral axis. -/
theorem sourceResonantA_im_eq_zero (hp : p ≠ ⊤) (ε : ℂ) (hε : ε*ε=1)
    (φ : CoeffPair p) (hφ : SourceHasRealitySign ε φ) (n : ℤ) (x : ℝ)
    (hx : (x : ℂ) ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp SpectralWeight.one (unitWeightedPairEquiv φ) n (x : ℂ) hx‖ < 1) :
    (sourceResonantA hp φ n (x : ℂ) hx h).im = 0 :=
  weightedResonantA_im_eq_zero hp SpectralWeight.one ε hε (unitWeightedPairEquiv φ)
    ((sourceHasRealitySign_iff ε φ).mp hφ) n x hx h

private theorem sourceSymmetryPullback
    (e : CoeffPair p ≃ₗᵢ[ℂ] WeightedCoeffPair SpectralWeight.one.toWeight p)
    (φ : CoeffPair p) (P : ℕ → WeightedCoeffPair SpectralWeight.one.toWeight p → Prop)
    (h : ∃ N : ℕ, 1 ≤ N ∧ ∃ V : Set (WeightedCoeffPair SpectralWeight.one.toWeight p),
      IsOpen V ∧ Convex ℝ V ∧ e φ ∈ V ∧ 0 ∈ V ∧ ∀ ψ ∈ V, P N ψ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ U : Set (CoeffPair p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧ ∀ ψ ∈ U, P N (e ψ) := by
  obtain ⟨N,hN,V,ho,hc,hφ,h0,hP⟩ := h
  exact ⟨N,hN,e ⁻¹' V,ho.preimage e.continuous,
    hc.linear_preimage (e.toLinearEquiv.toLinearMap.restrictScalars ℝ),hφ,
    by simpa only [Set.mem_preimage,map_zero] using h0,fun ψ hψ => hP (e ψ) hψ⟩

/-- Both source symmetry statements hold on a single local neighborhood and all distant closed strips. -/
theorem sourceLemma6_7_uniform (hp : p ≠ ⊤) (φ : CoeffPair p) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ U : Set (CoeffPair p), IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ∀ n : ℤ, N ≤ n.natAbs → ∀ z : ℂ, ∀ hz : z ∈ resonantStrip n,
        ∃ h : ‖weightedPotentialSquareInShift hp SpectralWeight.one (unitWeightedPairEquiv ψ) n z hz‖ < 1,
        ∃ hc : ‖weightedPotentialSquareInShift hp SpectralWeight.one (unitWeightedPairEquiv ψ) n
          ((starRingEnd ℂ) z) (conj_mem_resonantStrip hz)‖ < 1,
          sourceCorrectionMatrix hp ψ n z hz h 0 0 = sourceCorrectionMatrix hp ψ n z hz h 1 1 ∧
          ∀ ε : ℂ, ε*ε=1 → SourceHasRealitySign ε ψ →
            sourceResonantA hp ψ n ((starRingEnd ℂ) z) (conj_mem_resonantStrip hz) hc =
              (starRingEnd ℂ) (sourceResonantA hp ψ n z hz h) ∧
            sourceResonantBPlus hp ψ n ((starRingEnd ℂ) z) (conj_mem_resonantStrip hz) hc =
              ε * (starRingEnd ℂ) (sourceResonantBMinus hp ψ n z hz h) := by
  obtain ⟨N,hN,U,ho,hv,hφ,h0,hdata⟩ := sourceSymmetryPullback unitWeightedPairEquiv φ _
    (exists_uniform_resonantConjugation hp SpectralWeight.one (unitWeightedPairEquiv φ))
  refine ⟨N,hN,U,ho,hv,hφ,h0,?_⟩
  intro ψ hψ n hn z hz
  obtain ⟨h,hc,_⟩ := hdata ψ hψ n hn z hz
  exact ⟨h,hc,sourceLemma6_7_i hp ψ n z hz h,fun ε hε hr => sourceLemma6_7_ii hp ε hε ψ hr n z hz h hc⟩

end NLS.ZakharovShabat
