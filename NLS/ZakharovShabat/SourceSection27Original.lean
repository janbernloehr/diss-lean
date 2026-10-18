import NLS.ZakharovShabat.SourceSection26Original
import NLS.ZakharovShabat.SourceSection27DerivativeBound

/-! # Section 27 for one retained original family

The physical identity (5.13), earlier Lemmas 27.1–27.2 estimates, and the
derivative estimate retain the same family, U, and T. The later module
`SourceSection27SharpEndpoint` proves the exact all-order Lemma 27.2 bound
on this retained family without altering its existing weaker fields.
-/
noncomputable section
open Set MeasureTheory
namespace NLS.ZakharovShabat

/-- Formula (5.13), with the original higher actions and actual physical remainder integral. -/
theorem SourceSection26Data.section27_top_jet_identity
    {W₀ W V Wa B U T : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
    {D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s}
    {A : SourceAbelianMomentAtlas (by simp) (by norm_num) Wa s}
    (Q : SourceSection26Data D A B U T) (m : ℕ) (hm : 1 ≤ m)
    (a : realTypeHigherSobolevSourceLocus m) :
    (‖hierarchySobolevJetL2 m m le_rfl a.val.1‖^2:ℂ) =
      4^m*(∑' n : ℤ, sourceIndexedHigherAction (by simp) (by norm_num) n (2*m)
        (higherSobolevSourceInclusion m a.val))-
        ∫ x in (0:ℝ)..1, sobolevPolynomialField m (nlsOddReducedPolynomial m hm) a.val
          (x : AddCircle (2:ℝ)) := by
  rw [Q.odd_trace m hm a.val (Q.real_subset a.property),
    mul_div_cancel₀ _ (pow_ne_zero m (by norm_num : (4:ℂ) ≠ 0)),
    sobolevOddHamiltonian_real_decomposition]
  rw [sobolevPolynomialMean_eq_physical_integral]
  push_cast
  ring

/-- Formula (5.13) with both derivative components and its exact factor 1/2. -/
theorem SourceSection26Data.section27_pair_top_jet_identity
    {W₀ W V Wa B U T : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
    {D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s}
    {A : SourceAbelianMomentAtlas (by simp) (by norm_num) Wa s}
    (Q : SourceSection26Data D A B U T) (m : ℕ) (hm : 1 ≤ m)
    (a : realTypeHigherSobolevSourceLocus m) :
    Complex.ofReal ((1/2:ℝ)*(‖hierarchySobolevJetL2 m m le_rfl a.val.1‖^2+
      ‖hierarchySobolevJetL2 m m le_rfl a.val.2‖^2)) =
      4^m*(∑' n : ℤ, sourceIndexedHigherAction (by simp) (by norm_num) n (2*m)
        (higherSobolevSourceInclusion m a.val))-
        ∫ x in (0:ℝ)..1, sobolevPolynomialField m (nlsOddReducedPolynomial m hm) a.val
          (x : AddCircle (2:ℝ)) := by
  rw [sourceSection27_pair_jet_norm]
  simpa only [Complex.ofReal_pow] using Q.section27_top_jet_identity m hm a

/-- The scaled original higher-action series sums to the independently defined Hamiltonian. -/
theorem SourceSection26Data.section27_hamiltonian_hasSum
    {W₀ W V Wa B U T : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
    {D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s}
    {A : SourceAbelianMomentAtlas (by simp) (by norm_num) Wa s}
    (Q : SourceSection26Data D A B U T) (m : ℕ) (hm : 1 ≤ m)
    (a : realTypeHigherSobolevSourceLocus m) :
    HasSum (fun n : ℤ => (4:ℂ)^m*sourceIndexedHigherAction (by simp) (by norm_num) n (2*m)
      (higherSobolevSourceInclusion m a.val)) (sobolevOddHamiltonian m hm a.val) := by
  have ha := Q.real_subset a.property
  have hs := ((Q.absolute_convergence m (2*m) le_rfl a.val ha).of_norm.hasSum).mul_left ((4:ℂ)^m)
  simpa only [Q.odd_trace m hm a.val ha,mul_div_cancel₀ _ (pow_ne_zero m (by norm_num : (4:ℂ) ≠ 0))] using hs

/-- The retained original Section 27 estimates; the exact endpoint is supplied by the later sharp-endpoint theorem. -/
structure SourceSection27Data
    {W₀ W V : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
    (D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s)
    {Wa : Set (CoeffPair 2)} (A : SourceAbelianMomentAtlas (by simp) (by norm_num) Wa s)
    (B U T : Set (CoeffPair 2)) : Prop extends SourceSection26Data D A B U T where
  hamiltonian_estimate : ∀ m : ℕ, ∀ hm : 2 ≤ m, ∀ a : realTypeHigherSobolevSourceLocus m,
    (sobolevOddHamiltonian m (by omega) a.val).re ≤
      (∑' n : ℤ, sourceIndexedWeightedActionTerm ⟨higherSobolevSourceInclusion m a.val,a.property⟩ m n)+
      (64*Real.pi)^(2*m-2)*
        (1+∑' n : ℤ, sourceIndexedWeightedActionTerm ⟨higherSobolevSourceInclusion m a.val,a.property⟩ 1 n)^(4*m-3)*
        (∑' n : ℤ, sourceIndexedWeightedActionTerm ⟨higherSobolevSourceInclusion m a.val,a.property⟩ 1 n)
  hamiltonian_estimate_all : ∀ m : ℕ, ∀ hm : 1 ≤ m, ∀ a : realTypeHigherSobolevSourceLocus m,
    (sobolevOddHamiltonian m hm a.val).re ≤
      (∑' n : ℤ, sourceIndexedWeightedActionTerm ⟨higherSobolevSourceInclusion m a.val,a.property⟩ m n)+
      2*(64*Real.pi)^(2*m-2)*
        (1+∑' n : ℤ, sourceIndexedWeightedActionTerm ⟨higherSobolevSourceInclusion m a.val,a.property⟩ 1 n)^(4*m-3)*
        (∑' n : ℤ, sourceIndexedWeightedActionTerm ⟨higherSobolevSourceInclusion m a.val,a.property⟩ 1 n)
  H1_norm : ∀ m : ℕ, ∀ hm : 1 ≤ m, ∀ a : realTypeHigherSobolevSourceLocus m,
    (1/3:ℝ)*‖sourcePiSobolevCoordinates m 1 hm a.val‖^2 ≤
      (∑' n : ℤ, sourceIndexedWeightedActionTerm ⟨higherSobolevSourceInclusion m a.val,a.property⟩ 1 n)+
      (∑' n : ℤ, sourceIndexedWeightedActionTerm ⟨higherSobolevSourceInclusion m a.val,a.property⟩ 0 n)^2
  derivative_bound : ∀ m : ℕ, ∀ _hm : 2 ≤ m, ∃ C : ℝ, 0 ≤ C ∧ ∀ a : realTypeHigherSobolevSourceLocus m,
    (1/4:ℝ)*(‖hierarchySobolevJetL2 m m le_rfl a.val.1‖^2+
      ‖hierarchySobolevJetL2 m m le_rfl a.val.2‖^2) ≤
      (∑' n : ℤ, sourceIndexedWeightedActionTerm ⟨higherSobolevSourceInclusion m a.val,a.property⟩ m n)+
      C*(1+∑' n : ℤ, sourceIndexedWeightedActionTerm ⟨higherSobolevSourceInclusion m a.val,a.property⟩ 1 n)^(4*m-3)*
        (∑' n : ℤ, sourceIndexedWeightedActionTerm ⟨higherSobolevSourceInclusion m a.val,a.property⟩ 0 n)

/-- Extend any retained original family without selecting new domains. -/
theorem SourceSection26Data.section27
    {W₀ W V Wa B U T : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
    {D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s}
    {A : SourceAbelianMomentAtlas (by simp) (by norm_num) Wa s}
    (Q : SourceSection26Data D A B U T) : SourceSection27Data D A B U T :=
  ⟨Q,sourceSection27_hamiltonian_estimate,sourceSection27_hamiltonian_estimate_all,
    sourceSection27_H1_norm,exists_sourceSection27_derivative_bound⟩

/-- One original family supports every order and all uniform Section 27 constants. -/
theorem sourceSection27_original :
    ∃ W₀ W V : Set (CoeffPair 2), ∃ s,
      ∃ D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s,
      ∃ Wa : Set (CoeffPair 2), ∃ A : SourceAbelianMomentAtlas (by simp) (by norm_num) Wa s,
      ∃ B U T : Set (CoeffPair 2), SourceSection27Data D A B U T := by
  obtain ⟨W₀,W,V,s,D,Wa,A,B,U,T,Q⟩ := sourceSection26_original
  exact ⟨W₀,W,V,s,D,Wa,A,B,U,T,Q.section27⟩

end NLS.ZakharovShabat
