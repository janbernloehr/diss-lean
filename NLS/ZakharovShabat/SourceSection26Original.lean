import NLS.ZakharovShabat.SourceSection25Original
import NLS.ZakharovShabat.SourceSection26Actions
import NLS.ZakharovShabat.SourceSection26Sum
import NLS.ZakharovShabat.SourceSection26SignCorrection

/-! # Section 26 for one retained original family

The action estimate has the physical Hamiltonian sign. The remainder and
Hamiltonian bounds share one constant chosen before every real Hᵐ source.
The original family and both domains U and T are retained unchanged.
-/
noncomputable section
open Set MeasureTheory
namespace NLS.ZakharovShabat

/-- Lemma 26.3 with one uniform constant for its actual physical integral and Hamiltonian. -/
structure SourceSection26RemainderBounds (m : ℕ) (hm : 1 ≤ m) (ε C : ℝ) : Prop where
  constant_nonneg : 0 ≤ C
  remainder : ∀ a : realTypeHigherSobolevSourceLocus m,
    (∫ x in (0:ℝ)..1, ‖sobolevPolynomialField m (nlsOddReducedPolynomial m hm) a.val
      (x : AddCircle (2:ℝ))‖) ≤ ε*‖hierarchySobolevJetL2 m m le_rfl a.val.1‖^2+
      C*(1+‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) a.val.1‖^(4*m))*
        ‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) a.val.1‖^2
  hamiltonian : ∀ a : realTypeHigherSobolevSourceLocus m,
    ‖sobolevOddHamiltonian m hm a.val‖ ≤
      (1+ε)*‖hierarchySobolevJetL2 m m le_rfl a.val.1‖^2+
      C*(1+‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) a.val.1‖^(4*m))*
        ‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) a.val.1‖^2

/-- The two conclusions of Lemma 26.3 hold uniformly with the same constant. -/
theorem exists_sourceSection26_remainder_bounds (m : ℕ) (hm : 1 ≤ m) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, SourceSection26RemainderBounds m hm ε C := by
  obtain ⟨C₁,h₁,H₁⟩ := exists_sobolevOddRemainder_derivative_absorption m hm ε hε
  obtain ⟨C₂,_,H₂⟩ := exists_sobolevOddHamiltonian_energy_estimates m hm ε hε
  refine ⟨max C₁ C₂,h₁.trans (le_max_left _ _),?_,?_⟩
  · intro a
    exact (H₁ a).trans (by gcongr; exact le_max_left _ _)
  · intro a
    exact (H₂ a).2.trans (by gcongr; exact le_max_right _ _)

/-- Corrected original action estimates and uniform physical remainder bounds. -/
structure SourceSection26Data
    {W₀ W V : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
    (D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s)
    {Wa : Set (CoeffPair 2)} (A : SourceAbelianMomentAtlas (by simp) (by norm_num) Wa s)
    (B U T : Set (CoeffPair 2)) : Prop extends SourceSection25Data D A B U T where
  action_estimate : ∀ m : ℕ, ∀ hm : 1 ≤ m, ∀ a : realTypeHigherSobolevSourceLocus m,
    Summable (sourceIndexedWeightedActionTerm ⟨higherSobolevSourceInclusion m a.val,a.property⟩ m) ∧
    (∑' n : ℤ, sourceIndexedWeightedActionTerm ⟨higherSobolevSourceInclusion m a.val,a.property⟩ m n) ≤
      (1+16*Real.pi)^(2*m)*(1+‖sourcePiSobolevCoordinates m 1 hm a.val‖)^(4*m)*
        (‖higherSobolevSourceInclusion m a.val‖^2/2)+2^m*(sobolevOddHamiltonian m hm a.val).re
  remainder_estimates : ∀ m : ℕ, ∀ hm : 1 ≤ m, ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, SourceSection26RemainderBounds m hm ε C

/-- Extend any retained original family without changing U or T. -/
theorem SourceSection25Data.section26
    {W₀ W V Wa B U T : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
    {D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s}
    {A : SourceAbelianMomentAtlas (by simp) (by norm_num) Wa s}
    (Q : SourceSection25Data D A B U T) : SourceSection26Data D A B U T :=
  ⟨Q,sourceSection26_action_estimate_half_mass,exists_sourceSection26_remainder_bounds⟩

/-- Every retained original domain contains a counterexample to the full printed Lemma 26.2. -/
theorem SourceSection26Data.printed_counterexample
    {W₀ W V Wa B U T : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
    {D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s}
    {A : SourceAbelianMomentAtlas (by simp) (by norm_num) Wa s}
    (Q : SourceSection26Data D A B U T) :
    ∃ a : realTypeHigherSobolevSourceLocus 2,
      higherSobolevSourceInclusion 2 a.val ∈ U ∩ T ∧
      Summable (sourceIndexedWeightedActionTerm ⟨higherSobolevSourceInclusion 2 a.val,a.property⟩ 2) ∧
      (1+16*Real.pi)^4*(1+‖sourcePiSobolevCoordinates 2 1 (by omega) a.val‖)^8*
          ‖higherSobolevSourceInclusion 2 a.val‖^2 +
          (-1:ℝ)^3*2^2*(sobolevOddHamiltonian 2 (by omega) a.val).re <
        (∑' n : ℤ, sourceIndexedWeightedActionTerm ⟨higherSobolevSourceInclusion 2 a.val,a.property⟩ 2 n) := by
  obtain ⟨a,hs,ha⟩ := section26_printedInequality_strict_counterexample
  exact ⟨a,⟨Q.real_subset a.property,Q.gap_real_subset a.property⟩,hs,ha⟩

/-- One original family supports all Section 26 orders and uniform constants. -/
theorem sourceSection26_original :
    ∃ W₀ W V : Set (CoeffPair 2), ∃ s,
      ∃ D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s,
      ∃ Wa : Set (CoeffPair 2), ∃ A : SourceAbelianMomentAtlas (by simp) (by norm_num) Wa s,
      ∃ B U T : Set (CoeffPair 2), SourceSection26Data D A B U T := by
  obtain ⟨W₀,W,V,s,D,Wa,A,B,U,T,Q⟩ := sourceSection25_original
  exact ⟨W₀,W,V,s,D,Wa,A,B,U,T,Q.section26⟩

end NLS.ZakharovShabat
