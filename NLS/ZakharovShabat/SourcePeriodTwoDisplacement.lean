import NLS.ZakharovShabat.SourceFourierTail
import NLS.ZakharovShabat.SourceResolvent
import NLS.ZakharovShabat.PeriodicRootSequence
import NLS.ZakharovShabat.PeriodicSpectralProductExistence

/-!
# Proposition 6.1 in the original period-two norm

Unit weighting preserves every Fourier coefficient and the component-sum norm.
The actual periodic eigenvalue pairs obey a corrected quantitative estimate:
the leading Fourier tail is additive, outside the nonlinear norm factors.
No period doubling is used here.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

@[simp] theorem unitWeightedPairEquiv_fst (φ : CoeffPair p) (k : ℤ) :
    (unitWeightedPairEquiv φ).fst.val k = φ.fst k := by
  change φ.fst k / (SpectralWeight.one k : ℂ) = _
  simp

@[simp] theorem unitWeightedPairEquiv_snd (φ : CoeffPair p) (k : ℤ) :
    (unitWeightedPairEquiv φ).snd.val k = φ.snd k := by
  change φ.snd k / (SpectralWeight.one k : ℂ) = _
  simp

/-- The unit-weight realization retains the original period-two input coefficients. -/
theorem weightedBaseToPair_unitWeightedPairEquiv (φ : CoeffPair p) :
    weightedBaseToPair SpectralWeight.one (unitWeightedPairEquiv φ) = CoeffPair.toMax p φ := by
  rw [← unitBaseEquiv_eq]
  apply Prod.ext <;> ext k <;> simp

/-- The original tail commutes with unit weighting at the same cutoff. -/
theorem weightedPairFourierTail_unitWeightedPairEquiv (N : ℕ) (φ : CoeffPair p) :
    weightedPairFourierTail SpectralWeight.one.toWeight N (unitWeightedPairEquiv φ) =
      unitWeightedPairEquiv (sourceFourierTail N φ) := by
  apply weightedPair_ext <;> intro k <;> simp

/-- The corrected right-hand side of Proposition 6.1 in its literal original norm. -/
def sourcePeriodTwoDisplacementBudget (φ : CoeffPair p) (N : ℕ) : ℝ :=
  rootDisplacementSummationConstant p *
    (‖sourceFourierTail (N/2) φ‖^p.toReal +
      (‖φ‖^p.toReal/(N : ℝ)^(min 1 (p.toReal-1)) + ‖sourceFourierTail (N/2) φ‖^p.toReal) *
        (1+‖φ‖^p.toReal)*‖φ‖^p.toReal)

theorem rootDisplacementBudget_unitWeightedPairEquiv (φ : CoeffPair p) (N : ℕ) :
    rootDisplacementBudget SpectralWeight.one (unitWeightedPairEquiv φ) N =
      sourcePeriodTwoDisplacementBudget φ N := by
  simp only [rootDisplacementBudget, sourcePeriodTwoDisplacementBudget,
    weightedPairFourierTail_unitWeightedPairEquiv, LinearIsometryEquiv.norm_map]

/-- The actual source pencil detects exactly the weighted spectral points. -/
theorem sourcePeriodTwoSpectrum_iff (hp : p ≠ ⊤) (φ : CoeffPair p) (z : ℂ) :
    z ∉ sourceResolventSet hp φ ↔
      z ∈ periodicSpectrum hp (weightedBaseToPair SpectralWeight.one (unitWeightedPairEquiv φ)) := by
  rw [weightedBaseToPair_unitWeightedPairEquiv, sourceResolventSet_eq]
  rfl

private theorem sourceUnitWeightedNeighborhood
    (e : CoeffPair p ≃ₗᵢ[ℂ] WeightedCoeffPair SpectralWeight.one.toWeight p)
    (V : Set (WeightedCoeffPair SpectralWeight.one.toWeight p))
    (ho : IsOpen V) (hc : Convex ℝ V) (φ : CoeffPair p) (hφ : e φ ∈ V) (h0 : 0 ∈ V) :
    IsOpen (e ⁻¹' V) ∧ Convex ℝ (e ⁻¹' V) ∧ φ ∈ e ⁻¹' V ∧ 0 ∈ e ⁻¹' V := by
  exact ⟨ho.preimage e.continuous,
    hc.linear_preimage (e.toLinearEquiv.toLinearMap.restrictScalars ℝ),
    hφ, by simpa only [Set.mem_preimage, map_zero] using h0⟩

/-- Pull a uniform open convex weighted neighborhood back through an exact source isometry. -/
theorem sourceUnitWeightedUniformPullback
    (e : CoeffPair p ≃ₗᵢ[ℂ] WeightedCoeffPair SpectralWeight.one.toWeight p)
    (φ : CoeffPair p) (P : ℕ → WeightedCoeffPair SpectralWeight.one.toWeight p → Prop)
    (h : ∃ N : ℕ, 2 ≤ N ∧ ∃ V : Set (WeightedCoeffPair SpectralWeight.one.toWeight p),
      IsOpen V ∧ Convex ℝ V ∧ e φ ∈ V ∧ 0 ∈ V ∧ ∀ ψ ∈ V, P N ψ) :
    ∃ N : ℕ, 2 ≤ N ∧ ∃ U : Set (CoeffPair p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧ ∀ ψ ∈ U, P N (e ψ) := by
  obtain ⟨N,hN,V,ho,hc,hφ,h0,hP⟩ := h
  obtain ⟨ho',hc',hφ',h0'⟩ := sourceUnitWeightedNeighborhood e V ho hc φ hφ h0
  exact ⟨N,hN,e ⁻¹' V,ho',hc',hφ',h0',fun ψ hψ => hP (e ψ) hψ⟩

private theorem sourcePeriodTwoDisplacementData (hp : p ≠ ⊤) (ψ : CoeffPair p) (N : ℕ)
    (ξ η : ℤ → ℂ)
    (hr : ∀ n : ℤ, N ≤ n.natAbs →
      PeriodicResonantPair hp SpectralWeight.one (unitWeightedPairEquiv ψ) n (ξ n) (η n))
    (ht : ∀ K : ℕ, N ≤ K → Summable (rootDisplacementPowerTail p K ξ η) ∧
      (∑' n : ℤ, rootDisplacementPowerTail p K ξ η n) ≤
        rootDisplacementBudget SpectralWeight.one (unitWeightedPairEquiv ψ) K) :
    (∀ n : ℤ, N ≤ n.natAbs → ∀ z ∈ resonantStrip n,
      z ∉ sourceResolventSet hp ψ ↔ z = ξ n ∨ z = η n) ∧
    ∀ K : ℕ, N ≤ K → Summable (rootDisplacementPowerTail p K ξ η) ∧
      (∑' n : ℤ, rootDisplacementPowerTail p K ξ η n) ≤ sourcePeriodTwoDisplacementBudget ψ K := by
  constructor
  · intro n hn z hz
    exact (sourcePeriodTwoSpectrum_iff hp ψ z).trans ((hr n hn).spectrum_iff z hz)
  · intro K hK
    exact ⟨(ht K hK).1,(ht K hK).2.trans_eq (rootDisplacementBudget_unitWeightedPairEquiv ψ K)⟩

/-- The corrected quantitative estimate, actual spectral pairs, and multiplicities,
on one original-input neighborhood for all larger cutoffs. -/
theorem exists_uniform_sourcePeriodTwoDisplacement (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (CoeffPair p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧ ∀ ψ ∈ U,
        ∃ ξ η : ℤ → ℂ,
          (∀ n : ℤ, N₀ ≤ n.natAbs →
            PeriodicResonantPair hp SpectralWeight.one (unitWeightedPairEquiv ψ) n (ξ n) (η n)) ∧
          (∀ n : ℤ, N₀ ≤ n.natAbs → ∀ z ∈ resonantStrip n,
            z ∉ sourceResolventSet hp ψ ↔ z = ξ n ∨ z = η n) ∧
          ∀ N : ℕ, N₀ ≤ N → Summable (rootDisplacementPowerTail p N ξ η) ∧
            (∑' n : ℤ, rootDisplacementPowerTail p N ξ η n) ≤ sourcePeriodTwoDisplacementBudget ψ N := by
  obtain ⟨N,hN,U,ho,hc,hφ,h0,hroots⟩ := sourceUnitWeightedUniformPullback
    unitWeightedPairEquiv φ _
    (exists_uniform_periodicRoots_with_power_sums hp hp1 SpectralWeight.one (unitWeightedPairEquiv φ))
  refine ⟨N,hN,U,ho,hc,hφ,h0,?_⟩
  intro ψ hψ
  obtain ⟨ξ,η,hr,ht⟩ := hroots ψ hψ
  obtain ⟨hs,hb⟩ := sourcePeriodTwoDisplacementData hp ψ N ξ η hr
    (fun K hK => ⟨(ht K hK).1,(ht K hK).2.1⟩)
  exact ⟨ξ,η,hr,hs,hb⟩


end NLS.ZakharovShabat
