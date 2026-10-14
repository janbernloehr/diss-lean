import NLS.ZakharovShabat.ResonantDiagonalQuadraticSummability
import NLS.ZakharovShabat.ResonantDiagonalNonlinearRemainder
import NLS.ZakharovShabat.SourceWeightedPeriodOne

/-!
# Quadratic diagonal expansion in the original source variables

Period-one transport retains the physical signs and the factor 1/(2π)
at free centers. The source quadratic term has half-exponent disk
suprema, and the actual diagonal has a uniform quartic error on one
original source neighborhood and every distant closed resonant strip.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ r)]
local instance sourceResonantDiagonalQuadraticConjFact : Fact (1 ≤ p.conjExponent) :=
  ⟨ENNReal.HolderConjugate.one_le p.conjExponent p⟩

/-- Only even physical frequencies contribute for a period-one input. -/
theorem resonantDiagonalQuadratic_periodDouble (a b : Coeff p) (n : ℤ) (z : ℂ) :
    resonantDiagonalQuadratic (Coeff.periodDouble a) (Coeff.periodDouble b) n z =
      ∑' m : ℤ, if m = n then 0 else b m*a (-m)/(z+(Real.pi:ℂ)*n-2*(Real.pi:ℂ)*m) := by
  unfold resonantDiagonalQuadratic
  have hs := (Coeff.parityEmbedding 0).injective.tsum_eq
    (f := fun j : ℤ => if j = 2*n then (0:ℂ) else
      Coeff.periodDouble b j*Coeff.periodDouble a (-j)/(z+(Real.pi:ℂ)*n-(Real.pi:ℂ)*j)) (by
        intro j hj
        by_contra hout
        have hb := Coeff.insert_apply_outside (Coeff.parityEmbedding 0) b j hout
        have hb' : Coeff.periodDouble b j = 0 := hb
        exact hj (by simp [hb']))
  rw [← hs]
  apply tsum_congr
  intro m
  simp only [Coeff.parityEmbedding_apply,add_zero,Coeff.periodDouble_even]
  rw [show -(2*m) = 2*(-m) by ring,Coeff.periodDouble_even]
  have hm : 2*m = 2*n ↔ m = n := by omega
  simp only [hm]
  split_ifs
  · rfl
  · congr 2
    push_cast
    ring

/-- The weighted physical source has the exact original-source reciprocal series. -/
theorem resonantDiagonalQuadratic_sourceWeightedPeriodOne (φ : CoeffPair p) (n : ℤ) (z : ℂ) :
    resonantDiagonalQuadratic (SpectralWeight.one.toCoeff (sourceWeightedPeriodOne φ).fst)
      (SpectralWeight.one.toCoeff (sourceWeightedPeriodOne φ).snd) n z =
      ∑' m : ℤ, if m = n then 0 else φ.snd m*φ.fst (-m)/(z+(Real.pi:ℂ)*n-2*(Real.pi:ℂ)*m) := by
  have hf : SpectralWeight.one.toCoeff (sourceWeightedPeriodOne φ).fst = Coeff.periodDouble φ.fst := by
    ext k
    simp [SpectralWeight.toCoeff_apply,sourceWeightedPeriodOne_fst]
  have hg : SpectralWeight.one.toCoeff (sourceWeightedPeriodOne φ).snd = Coeff.periodDouble φ.snd := by
    ext k
    simp [SpectralWeight.toCoeff_apply,sourceWeightedPeriodOne_snd]
  rw [hf,hg]
  exact resonantDiagonalQuadratic_periodDouble φ.fst φ.snd n z

/-- At the free center the original-source Hilbert row has factor minus 1/(2π). -/
theorem resonantDiagonalQuadratic_periodDouble_center (a b : Coeff p) (n : ℤ) :
    resonantDiagonalQuadratic (Coeff.periodDouble a) (Coeff.periodDouble b) n ((Real.pi:ℂ)*n) =
      -(2*(Real.pi:ℂ))⁻¹ * ∑' m : ℤ, (b m*a (-m))/((m:ℂ)-n) := by
  rw [resonantDiagonalQuadratic_periodDouble,← tsum_mul_left]
  apply tsum_congr
  intro m
  by_cases hm : m = n
  · simp [hm]
  · rw [if_neg hm]
    have hd : (Real.pi:ℂ)*n+(Real.pi:ℂ)*n-2*(Real.pi:ℂ)*m =
        -(2*(Real.pi:ℂ))*((m:ℂ)-n) := by ring
    rw [hd,div_eq_mul_inv,div_eq_mul_inv,mul_inv_rev,inv_neg]
    ring

/-- The quadratic diagonal term for the original period-one coefficient pair. -/
def sourceResonantDiagonalQuadratic (φ : CoeffPair p) (n : ℤ) (z : ℂ) : ℂ :=
  resonantDiagonalQuadratic (Coeff.periodDouble φ.fst) (Coeff.periodDouble φ.snd) n z

/-- The original-source series keeps the signed reflected component and doubled spacing. -/
theorem sourceResonantDiagonalQuadratic_eq (φ : CoeffPair p) (n : ℤ) (z : ℂ) :
    sourceResonantDiagonalQuadratic φ n z =
      ∑' m : ℤ, if m = n then 0 else φ.snd m*φ.fst (-m)/(z+(Real.pi:ℂ)*n-2*(Real.pi:ℂ)*m) :=
  resonantDiagonalQuadratic_periodDouble φ.fst φ.snd n z

/-- The original source actual diagonal has the explicit second-iterate remainder. -/
theorem sourceResonantA_sub_quadratic (hp : p ≠ ⊤) (φ : CoeffPair p)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp SpectralWeight.one (sourceWeightedPeriodOne φ) n z hz‖ < 1) :
    weightedResonantA hp SpectralWeight.one (sourceWeightedPeriodOne φ) n z hz h-sourceResonantDiagonalQuadratic φ n z =
      weightedResonantDiagonalRemainder hp SpectralWeight.one (sourceWeightedPeriodOne φ) n z hz h := by
  have he := weightedResonantA_sub_quadratic hp SpectralWeight.one (sourceWeightedPeriodOne φ) n z hz h
  rw [resonantDiagonalQuadratic_sourceWeightedPeriodOne,← sourceResonantDiagonalQuadratic_eq] at he
  exact he

/-- The original-source quadratic supremum is bounded by the square of the pair norm. -/
theorem exists_sourceResonantDiagonalQuadraticSup (hp : p ≠ ⊤) (hr1 : 1 < r) (hr : r ≠ ⊤) (hpr : p/2 ≤ r)
    (φ : CoeffPair p) :
    ∃ B : Coeff r,
      (∀ n : ℤ, B n = ((sSup ((fun z => ‖sourceResonantDiagonalQuadratic φ n z‖) '' refinedResonantDisk n) : ℝ):ℂ)) ∧
      (∀ n : ℤ, ∀ z ∈ refinedResonantDisk n, ‖sourceResonantDiagonalQuadratic φ n z‖ ≤ ‖B n‖) ∧
      ‖B‖ ≤ Real.pi⁻¹*(Fourier.hilbertTransformBound hr1 hr+‖Fourier.hilbertSquareCoeffs‖)*‖φ‖^2 := by
  obtain ⟨B,he,hpoint,hbound⟩ := exists_resonantDiagonalQuadraticSup hp hr1 hr hpr
    (Coeff.periodDouble φ.fst) (Coeff.periodDouble φ.snd)
  refine ⟨B,he,hpoint,?_⟩
  rw [Coeff.norm_periodDouble,Coeff.norm_periodDouble] at hbound
  have hC : 0 ≤ Real.pi⁻¹*(Fourier.hilbertTransformBound hr1 hr+‖Fourier.hilbertSquareCoeffs‖) := by
    have := Fourier.hilbertTransformBound_nonneg hr1 hr
    positivity
  apply hbound.trans
  apply mul_le_mul_of_nonneg_left _ hC
  simpa only [pow_two] using mul_le_mul (WithLp.norm_fst_le _ φ) (WithLp.norm_snd_le _ φ)
    (norm_nonneg φ.snd) (norm_nonneg φ)

/-- Forgetting the unit weight leaves the physical source exactly unchanged. -/
theorem sourceWeightedPeriodOne_forget (φ : CoeffPair p) :
    SpectralWeight.one.forgetPairWeight (sourceWeightedPeriodOne φ) = sourceWeightedPeriodOne φ := by
  apply weightedPair_ext <;> intro k <;> simp

/-- The source diagonal's actual quadratic error has an exponent-only quartic bound. -/
theorem norm_sourceResonantA_sub_quadratic_le (hp : p ≠ ⊤) (φ : CoeffPair p)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (hw : ‖weightedPotentialSquareInShift hp SpectralWeight.one (sourceWeightedPeriodOne φ) n z hz‖ < 1)
    (hh : ‖weightedPotentialSquareInShift hp SpectralWeight.one (sourceWeightedPeriodOne φ) n z hz‖ ≤ 1/2) :
    ‖weightedResonantA hp SpectralWeight.one (sourceWeightedPeriodOne φ) n z hz hw-
      sourceResonantDiagonalQuadratic φ n z‖ ≤ resonantDiagonalRemainderConstant hp*‖φ‖^4 := by
  rw [sourceResonantA_sub_quadratic]
  have h1 : ‖weightedPotentialSquareInShift hp SpectralWeight.one
      (SpectralWeight.one.forgetPairWeight (sourceWeightedPeriodOne φ)) n z hz‖ < 1 := by
    rw [sourceWeightedPeriodOne_forget]
    exact hw
  have hhalf : ‖weightedPotentialSquareInShift hp SpectralWeight.one
      (SpectralWeight.one.forgetPairWeight (sourceWeightedPeriodOne φ)) n z hz‖ ≤ 1/2 := by
    rw [sourceWeightedPeriodOne_forget]
    exact hh
  have hb := norm_weightedResonantDiagonalRemainder_le_quartic hp SpectralWeight.one
    (sourceWeightedPeriodOne φ) n z hz hw h1 hhalf
  simpa only [sourceWeightedPeriodOne_forget,norm_sourceWeightedPeriodOne,resonantDiagonalRemainderConstant] using! hb

/-- Retain only the contraction data used by the source quadratic expansion. -/
theorem exists_uniform_weightedDiagonalContraction (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p), IsOpen U ∧ φ ∈ U ∧
      ∀ ψ ∈ U, ∀ n : ℤ, N ≤ n.natAbs → ∀ z : ℂ, ∀ hz : z ∈ resonantStrip n,
        ‖weightedPotentialSquareInShift hp w ψ n z hz‖ ≤ 1/2 := by
  obtain ⟨N,hN,U,ho,_,hφ,_,_,hb⟩ := exists_uniform_complementarySquare_half hp w φ
  exact ⟨N,hN,U,ho,hφ,fun ψ hψ n hn z hz => (hb ψ hψ n hn z hz).1⟩

private theorem quadratic_open_pullback {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (e : A → B) (he : Continuous e) (a : A) (P : ℕ → B → Prop)
    (h : ∃ N : ℕ, 1 ≤ N ∧ ∃ U : Set B, IsOpen U ∧ e a ∈ U ∧ ∀ x ∈ U, P N x) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ V : Set A, IsOpen V ∧ a ∈ V ∧ ∀ x ∈ V, P N (e x) := by
  obtain ⟨N,hN,U,ho,ha,hP⟩ := h
  exact ⟨N,hN,e ⁻¹' U,ho.preimage he,ha,fun x hx => hP (e x) hx⟩

private theorem quadratic_open_imp {A : Type*} [TopologicalSpace A]
    (a : A) (P Q : ℕ → A → Prop)
    (h : ∃ N : ℕ, 1 ≤ N ∧ ∃ U : Set A, IsOpen U ∧ a ∈ U ∧ ∀ x ∈ U, P N x)
    (hPQ : ∀ N x, P N x → Q N x) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ U : Set A, IsOpen U ∧ a ∈ U ∧ ∀ x ∈ U, Q N x := by
  obtain ⟨N,hN,U,ho,ha,hP⟩ := h
  exact ⟨N,hN,U,ho,ha,fun x hx => hPQ N x (hP x hx)⟩

/-- A common original-source neighborhood has the actual half-contraction on every distant strip. -/
theorem exists_uniform_sourceDiagonalContraction (hp : p ≠ ⊤) (φ : CoeffPair p) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∀ ψ ∈ V, ∀ n : ℤ, N ≤ n.natAbs → ∀ z : ℂ, ∀ hz : z ∈ resonantStrip n,
        ‖weightedPotentialSquareInShift hp SpectralWeight.one (sourceWeightedPeriodOne ψ) n z hz‖ ≤ 1/2 := by
  exact quadratic_open_pullback (sourceWeightedPeriodOne (p := p))
    (sourceWeightedPeriodOne (p := p)).toContinuousLinearMap.continuous φ _
    (exists_uniform_weightedDiagonalContraction hp SpectralWeight.one (sourceWeightedPeriodOne φ))

/-- One source neighborhood and cutoff give an actual quartic expansion on every distant strip. -/
theorem exists_local_sourceResonantDiagonalQuadraticExpansion (hp : p ≠ ⊤) (φ : CoeffPair p) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∀ ψ ∈ V, ∀ n : ℤ, N ≤ n.natAbs → ∀ z : ℂ, ∀ hz : z ∈ resonantStrip n,
        ‖weightedPotentialSquareInShift hp SpectralWeight.one (sourceWeightedPeriodOne ψ) n z hz‖ ≤ 1/2 ∧
        ‖weightedResonantAExtension hp SpectralWeight.one (sourceWeightedPeriodOne ψ) n z-
          sourceResonantDiagonalQuadratic ψ n z‖ ≤ resonantDiagonalRemainderConstant hp*‖ψ‖^4 := by
  apply quadratic_open_imp φ _ _ (exists_uniform_sourceDiagonalContraction hp φ)
  intro N ψ hb n hn z hz
  have hw := hb n hn z hz
  have hw' := hw.trans_lt (by norm_num : (1/2:ℝ) < 1)
  refine ⟨hw,?_⟩
  rw [weightedResonantAExtension_eq hp SpectralWeight.one (sourceWeightedPeriodOne ψ) n z hz hw']
  exact norm_sourceResonantA_sub_quadratic_le hp ψ n z hz hw' hw

end NLS.ZakharovShabat
