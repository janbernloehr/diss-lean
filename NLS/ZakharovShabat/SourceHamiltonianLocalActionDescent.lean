import NLS.ZakharovShabat.SourcePrimitivePowerIsospectral
import NLS.ZakharovShabat.SourceFrequencyComplexSignInvariance
import NLS.SequenceSpaces.NonzeroFiniteCenter
import NLS.SequenceSpaces.LocalScalarActionDescent

/-! # Local analytic Hamiltonians on ℓ² action space

Each real FL⁴ source admits an open complex Birkhoff neighborhood on
which the actual Hamiltonian factors analytically through its complete
spectral action sequence. Tail actions may vanish.
-/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat.SourcePrimitivePowerAtlas
local instance : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
local instance : (4 : ℝ≥0∞).HolderTriple 4 2 := (ENNReal.holderTriple_iff _ _ _).mpr (by
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_add])
variable {W : Set (CoeffPair 4)}
variable (A : SourcePrimitivePowerAtlas (by simp) (by norm_num) W)

/-- Actual local analytic action factors exist at every real FL⁴ source,
with recovery on an open complex Birkhoff neighborhood. -/
theorem exists_local_hamiltonian_action_factors :
    ∃ W₀ B X : Set (CoeffPair 4), ∃ t : (n : ℤ) → CoeffPair 4 → DeletedCoeff 4 n,
      ∃ D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B X t,
      ∃ U : Set (CoeffPair 4), IsOpen U ∧ realTypeSourceLocus 4 ⊆ U ∧
        ∀ φ : realTypeSourceSubmodule 4, ∃ C : SourceBirkhoffInverseChart D φ U,
          ∃ Z : Set (Coeff 4 × Coeff 4), ∃ T : Set (Coeff 2), ∃ g : Coeff 2 → ℂ,
            IsOpen Z ∧ sourceBirkhoffMap (by simp) (by norm_num) t φ.val ∈ Z ∧ Z ⊆ C.target ∧
            IsOpen T ∧ quadraticActionsExponent (q := 2) '' Z = T ∧ AnalyticOnNhd ℂ g T ∧
            ∀ z ∈ Z, g (sourceActionSequence (q := 2) (by simp) (by norm_num) t (C.inverse z)) =
              A.renormalizedHamiltonian (C.inverse z) := by
  obtain ⟨U,hU,_,hreal,_,ha,_,_⟩ := A.exists_renormalizedHamiltonian_analytic
  obtain ⟨W₀,B,X,t,D⟩ := exists_sourceBirkhoffMap_complex_analytic (p := 4) (by simp) (by norm_num)
  refine ⟨W₀,B,X,t,D,U,hU,hreal,?_⟩
  intro φ
  obtain ⟨C⟩ := D.exists_inverseChart φ U hU (hreal φ.property)
  have hF := C.analytic_comp A.renormalizedHamiltonian ha
  obtain ⟨S,R,hR,hbase,hball,hhead⟩ := Coeff.exists_nonzeroFiniteCenter_ball
    (by simp : (4:ℝ≥0∞) ≠ ⊤) C.target C.target_open _ C.center_mem
  let c := Coeff.truncatePair S (sourceBirkhoffMap (by simp) (by norm_num) t φ.val)
  have hc : c ∈ Coeff.realPairLocus 4 :=
    Coeff.truncatePair_mem_realPairLocus S _ ((Coeff.mem_realPairLocus_iff _).mpr
      ⟨sourceRealBirkhoffMap (by simp) (by norm_num) t φ,D.real_map_complex_inclusion φ⟩)
  have hrealInv := fun a b hab => A.renormalizedHamiltonian_real_eq_of_actions A a b hab
  have hsign : ∀ e d : ℤ → Bool, (∀ n ∈ S, e n = false) → (∀ n ∈ S, d n = false) →
      ∀ z ∈ ball c R, (A.renormalizedHamiltonian ∘ C.inverse) (Coeff.pairSignChange e d z) =
        (A.renormalizedHamiltonian ∘ C.inverse) z := by
    intro e d he hd z hz
    exact C.complex_sign_invariance _ hF hrealInv c hc R hR hball e d
      (Coeff.pairSignChange_truncatePair S _ e d he hd) z hz
  have hrot : ∀ z ∈ ball c R, ∀ k, fderiv ℂ (A.renormalizedHamiltonian ∘ C.inverse) z
      (Coeff.actionRotationVectorCLM 4 k z) = 0 := by
    intro z hz k
    exact Coeff.fderiv_actionRotationVector_eq_zero_of_real_action_invariance _ _ isOpen_ball
      (convex_ball c R) c (mem_ball_self hR) hc (hF.mono hball)
      (fun a ha b hb har hbr he => C.lifted_real_action_invariance _ hrealInv a b
        (hball ha) (hball hb) har hbr he) z hz k
  obtain ⟨Z,T,g,hZ,hz₀,hZV,hT,himage,hg,hrec⟩ := Coeff.exists_local_scalar_action_factor
    (q := 2) (by simp : (4:ℝ≥0∞) ≠ ⊤) S (A.renormalizedHamiltonian ∘ C.inverse)
    (ball c R) isOpen_ball (hF.mono hball) hsign hrot _ hbase hhead
  refine ⟨C,Z,T,g,hZ,hz₀,hZV.trans hball,hT,himage,hg,?_⟩
  intro z hz
  rw [C.actionSequence_eq z (hball (hZV hz))]
  exact hrec z hz

end NLS.ZakharovShabat.SourcePrimitivePowerAtlas
