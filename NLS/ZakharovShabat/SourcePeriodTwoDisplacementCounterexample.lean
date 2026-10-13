import NLS.ZakharovShabat.SourcePeriodTwoDisplacement
import NLS.ZakharovShabat.RootDisplacementSourceAudit

/-!
# The printed Proposition 6.1 budget fails for the actual source operator

At p=2, arbitrarily small resonant inputs have a quadratic displacement
while the printed budget is quartic. The witness lies beyond any proposed
uniform cutoff in any original-norm neighborhood of zero. Spectral membership
is noninvertibility of the actual original-domain pencil, not only a reduced
determinant equation.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The literal printed Hilbert budget in the original period-two norm. -/
def sourcePrintedHilbertDisplacementBudget (C : ℝ) (φ : CoeffPair 2) (N : ℕ) : ℝ :=
  C * (‖φ‖^2/(N : ℝ)+‖sourceFourierTail ((N+1)/2) φ‖^2) * (1+‖φ‖^2)*‖φ‖^2

/-- Ceiling at the half-cutoff only decreases the old floor-cutoff budget. -/
theorem sourcePrintedHilbertDisplacementBudget_le (C : ℝ) (hC : 0 ≤ C)
    (φ : CoeffPair 2) (N : ℕ) :
    sourcePrintedHilbertDisplacementBudget C φ N ≤
      printedHilbertRootBudget C (unitWeightedPairEquiv φ) N := by
  simp only [printedHilbertRootBudget, sourcePrintedHilbertDisplacementBudget,
    weightedPairFourierTail_unitWeightedPairEquiv, LinearIsometryEquiv.norm_map]
  have ht := norm_sourceFourierTail_antitone (p := 2) (by simp) φ
    (show N/2 ≤ (N+1)/2 by omega)
  gcongr

/-- The existing reduced-root counterexample is an actual periodic spectral point. -/
theorem exists_periodicRoot_exceeding_printed_budget (C : ℝ) (hC : 0 ≤ C)
    (U : Set (WeightedCoeffPair SpectralWeight.one.toWeight 2)) (ho : IsOpen U) (h0 : 0 ∈ U) (M : ℕ) :
    ∃ n : ℕ, M ≤ n ∧ 2 ≤ n ∧ ∃ φ ∈ U, ∃ z ∈ refinedResonantDisk (n : ℤ),
      z ∈ periodicSpectrum (by norm_num) (weightedBaseToPair SpectralWeight.one φ) ∧
        printedHilbertRootBudget C φ n < ‖z-(Real.pi : ℂ)*(n : ℤ)‖^2 := by
  obtain ⟨N,_,V,hVo,_,_,hV0,hspec⟩ :=
    exists_uniform_weightedDeterminant_spectral_iff (p := 2) (by norm_num) SpectralWeight.one 0
  obtain ⟨n,hn,hn2,φ,hφ,z,hz,hzs,_,hzero,hbad⟩ :=
    exists_resonantRoot_exceeding_printed_budget C hC (U ∩ V) (ho.inter hVo) ⟨h0,hV0⟩ (max M N)
  refine ⟨n,(le_max_left _ _).trans hn,hn2,φ,hφ.1,z,hz,?_,hbad⟩
  exact (hspec φ hφ.2 (n : ℤ) (by simpa using (le_max_right M N).trans hn) z hzs).mpr hzero

private theorem exists_sourceUnitWeightedWitness
    (e : CoeffPair 2 ≃ₗᵢ[ℂ] WeightedCoeffPair SpectralWeight.one.toWeight 2)
    (U : Set (CoeffPair 2)) (ho : IsOpen U) (h0 : 0 ∈ U)
    (P : WeightedCoeffPair SpectralWeight.one.toWeight 2 → Prop)
    (h : ∀ V : Set (WeightedCoeffPair SpectralWeight.one.toWeight 2),
      IsOpen V → 0 ∈ V → ∃ ψ ∈ V, P ψ) : ∃ φ ∈ U, P (e φ) := by
  obtain ⟨ψ,hψ,hP⟩ := h (e.symm ⁻¹' U) (ho.preimage e.symm.continuous)
    (by simpa only [Set.mem_preimage,map_zero] using h0)
  exact ⟨e.symm ψ,hψ,by simpa only [LinearIsometryEquiv.apply_symm_apply] using hP⟩

/-- No original-input neighborhood and uniform cutoff support the printed bound,
even for one actual eigenvalue. -/
theorem exists_sourcePeriodTwoRoot_exceeding_printed_budget (C : ℝ) (hC : 0 ≤ C)
    (U : Set (CoeffPair 2)) (ho : IsOpen U) (h0 : 0 ∈ U) (M : ℕ) :
    ∃ n : ℕ, M ≤ n ∧ 2 ≤ n ∧ ∃ φ ∈ U, ∃ z ∈ refinedResonantDisk (n : ℤ),
      z ∉ sourceResolventSet (by norm_num) φ ∧
        sourcePrintedHilbertDisplacementBudget C φ n < ‖z-(Real.pi : ℂ)*(n : ℤ)‖^2 := by
  have hw : ∀ V : Set (WeightedCoeffPair SpectralWeight.one.toWeight 2), IsOpen V → 0 ∈ V →
      ∃ ψ ∈ V, ∃ n : ℕ, M ≤ n ∧ 2 ≤ n ∧ ∃ z ∈ refinedResonantDisk (n : ℤ),
        z ∈ periodicSpectrum (by norm_num) (weightedBaseToPair SpectralWeight.one ψ) ∧
          printedHilbertRootBudget C ψ n < ‖z-(Real.pi : ℂ)*(n : ℤ)‖^2 := by
    intro V hVo hV0
    obtain ⟨n,hn,hn2,ψ,hψ,z,hz,hs,hb⟩ := exists_periodicRoot_exceeding_printed_budget C hC V hVo hV0 M
    exact ⟨ψ,hψ,n,hn,hn2,z,hz,hs,hb⟩
  obtain ⟨φ,hφ,n,hn,hn2,z,hz,hs,hb⟩ := exists_sourceUnitWeightedWitness unitWeightedPairEquiv U ho h0 _ hw
  exact ⟨n,hn,hn2,φ,hφ,z,hz,(sourcePeriodTwoSpectrum_iff (by norm_num) φ z).mpr hs,
    (sourcePrintedHilbertDisplacementBudget_le C hC φ n).trans_lt hb⟩

/-- The single-root consequence of the printed source estimate is false locally at zero. -/
theorem not_exists_locally_uniform_sourcePrintedDisplacementBudget :
    ¬ ∃ C : ℝ, 0 ≤ C ∧ ∃ M : ℕ, ∃ U : Set (CoeffPair 2), IsOpen U ∧ 0 ∈ U ∧
      ∀ φ ∈ U, ∀ n : ℕ, M ≤ n → 2 ≤ n → ∀ z ∈ refinedResonantDisk (n : ℤ),
        z ∉ sourceResolventSet (by norm_num) φ →
          ‖z-(Real.pi : ℂ)*(n : ℤ)‖^2 ≤ sourcePrintedHilbertDisplacementBudget C φ n := by
  rintro ⟨C,hC,M,U,ho,h0,hbound⟩
  obtain ⟨n,hn,hn2,φ,hφ,z,hz,hspec,hbad⟩ :=
    exists_sourcePeriodTwoRoot_exceeding_printed_budget C hC U ho h0 M
  exact (not_le_of_gt hbad) (hbound φ hφ n hn hn2 z hz hspec)

/-- Each actual member of a labeled pair is bounded by its convergent Hilbert tail. -/
theorem sourcePeriodTwoRoot_sq_le_pair_tail (N n : ℕ) (hn : N ≤ n)
    (ξ η : ℤ → ℂ) (z : ℂ) (hz : z = ξ n ∨ z = η n)
    (hs : Summable (rootDisplacementPowerTail 2 N ξ η)) :
    ‖z-(Real.pi : ℂ)*(n : ℤ)‖^2 ≤ ∑' k : ℤ, rootDisplacementPowerTail 2 N ξ η k := by
  have hnonneg (k : ℤ) : 0 ≤ rootDisplacementPowerTail 2 N ξ η k := by
    unfold rootDisplacementPowerTail
    split_ifs <;> positivity
  have hterm := hs.le_tsum (n : ℤ) (fun k _ => hnonneg k)
  have he : rootDisplacementPowerTail 2 N ξ η (n : ℤ) =
      ‖ξ n-(Real.pi : ℂ)*(n : ℤ)‖^2 + ‖η n-(Real.pi : ℂ)*(n : ℤ)‖^2 := by
    simp [rootDisplacementPowerTail, hn]
  rw [he] at hterm
  rcases hz with rfl | rfl
  · exact (le_add_of_nonneg_right (sq_nonneg _)).trans hterm
  · exact (le_add_of_nonneg_left (sq_nonneg _)).trans hterm

/-- The printed pair-sum estimate itself fails, irrespective of the choice of
high-eigenvalue labels, on every original-input neighborhood of zero. -/
theorem not_sourceProposition6_1_printed_pair_sum :
    ¬ ∃ C : ℝ, 0 ≤ C ∧ ∃ M : ℕ, ∃ U : Set (CoeffPair 2), IsOpen U ∧ 0 ∈ U ∧
      ∀ φ ∈ U, ∃ ξ η : ℤ → ℂ,
        (∀ n : ℕ, M ≤ n → 2 ≤ n → ∀ z ∈ refinedResonantDisk (n : ℤ),
          z ∉ sourceResolventSet (by norm_num) φ → z = ξ n ∨ z = η n) ∧
        ∀ N : ℕ, M ≤ N → 2 ≤ N → Summable (rootDisplacementPowerTail 2 N ξ η) ∧
          (∑' n : ℤ, rootDisplacementPowerTail 2 N ξ η n) ≤
            sourcePrintedHilbertDisplacementBudget C φ N := by
  rintro ⟨C,hC,M,U,ho,h0,hbound⟩
  obtain ⟨n,hn,hn2,φ,hφ,z,hz,hspec,hbad⟩ :=
    exists_sourcePeriodTwoRoot_exceeding_printed_budget C hC U ho h0 M
  obtain ⟨ξ,η,hr,ht⟩ := hbound φ hφ
  have hb := sourcePeriodTwoRoot_sq_le_pair_tail n n le_rfl ξ η z
    (hr n hn hn2 z hz hspec) (ht n hn hn2).1
  exact (not_le_of_gt hbad) (hb.trans (ht n hn hn2).2)

end NLS.ZakharovShabat
