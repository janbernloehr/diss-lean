import NLS.ZakharovShabat.SourceFrequencyComplexSignInvariance
import NLS.ZakharovShabat.SourceRealActionLifting
import NLS.SequenceSpaces.NonzeroFiniteCenter
import NLS.SequenceSpaces.LocalScalarActionDescent

/-! # Scalar action descent on an open source domain

Only real representatives in the original domain enter the invariance
hypothesis. Inverse charts are restricted to that domain before descent,
so no value or invariance outside it is prescribed. Collapsed actions are
included by quadratic action descent in the infinite tail.
-/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderTriple p q]
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B X U : Set (CoeffPair p)}
  {t : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
  {D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t}
  {φ : realTypeSourceSubmodule p}

namespace SourceBirkhoffInverseChart

/-- Transport invariance between real sources in the prescribed domain. -/
theorem lifted_real_action_invariance_on {F : Type*}
    (C : SourceBirkhoffInverseChart D φ U) (f : CoeffPair p → F)
    (hinv : ∀ a b : realTypeSourceSubmodule p, a.val ∈ U → b.val ∈ U →
      b ∈ sourceRealActionLevelSet hp hp1 a → f b.val = f a.val)
    (z w : Coeff p × Coeff p) (hz : z ∈ C.target) (hw : w ∈ C.target)
    (hzr : z ∈ Coeff.realPairLocus p) (hwr : w ∈ Coeff.realPairLocus p)
    (he : ∀ n, w.1 n^2+w.2 n^2 = z.1 n^2+z.2 n^2) :
    f (C.inverse w) = f (C.inverse z) := by
  obtain ⟨a,rfl⟩ := (Coeff.mem_realPairLocus_iff z).mp hzr
  obtain ⟨b,rfl⟩ := (Coeff.mem_realPairLocus_iff w).mp hwr
  apply hinv (C.realInverse a hz) (C.realInverse b hw)
    (C.image_subset hz).2 (C.image_subset hw).2
  apply C.realInverse_mem_actionLevelSet a b hz hw
  intro n
  have h := he n
  change (b.1 n:ℂ)^2+(b.2 n:ℂ)^2 = (a.1 n:ℂ)^2+(a.2 n:ℂ)^2 at h
  have hr : b.1 n^2+b.2 n^2 = a.1 n^2+a.2 n^2 := by exact_mod_cast h
  unfold RealCoeff.pairAction
  rw [hr]

/-- Recovery uses only the two real representatives in the open domain. -/
theorem recover_of_real_action_lift_on {F : Type*}
    (C : SourceBirkhoffInverseChart D φ U)
    (Z : Set (Coeff p × Coeff p)) (hZC : Z ⊆ C.target)
    (f : CoeffPair p → F) (G : Coeff q → F)
    (hinv : ∀ a b : realTypeSourceSubmodule p, a.val ∈ U → b.val ∈ U →
      b ∈ sourceRealActionLevelSet hp hp1 a → f b.val = f a.val)
    (hrec : ∀ z ∈ Z, G (quadraticActionsExponent z) = f (C.inverse z))
    (ψ : realTypeSourceSubmodule p) (hψ : ψ.val ∈ U)
    (hlift : sourceActionSequence (q := q) hp hp1 t ψ.val ∈
      quadraticActionsExponent (q := q) '' (Z ∩ Coeff.realPairLocus p)) :
    G (sourceActionSequence (q := q) hp hp1 t ψ.val) = f ψ.val := by
  obtain ⟨z, ⟨hz, hzr⟩, he⟩ := hlift
  have hreal : C.inverse z ∈ realTypeSourceLocus p := by
    obtain ⟨w, hw⟩ := (Coeff.mem_realPairLocus_iff z).mp hzr
    rw [← hw]
    exact C.real_preserving w (hw.symm ▸ hZC hz)
  let χ : realTypeSourceSubmodule p := ⟨C.inverse z, hreal⟩
  have hχ : sourceActionSequence (q := q) hp hp1 t χ.val = sourceActionSequence (q := q) hp hp1 t ψ.val :=
    (C.actionSequence_eq z (hZC hz)).trans he
  calc
    G (sourceActionSequence (q := q) hp hp1 t ψ.val) = G (quadraticActionsExponent z) := by rw [he]
    _ = f (C.inverse z) := hrec z hz
    _ = f ψ.val := hinv ψ χ hψ (C.image_subset (hZC hz)).2
      (D.mem_actionLevelSet_of_actionSequence_eq ψ χ hχ)

end SourceBirkhoffInverseChart

namespace SourceBirkhoffMapComplexData

/-- Local analytic scalar factors in any open source domain. Invariance
is required only on real action fibers meeting that domain. -/
theorem exists_local_scalar_action_factor_on
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t)
    (f : CoeffPair p → ℂ) (hU : IsOpen U) (hf : AnalyticOnNhd ℂ f U)
    (hinv : ∀ a b : realTypeSourceSubmodule p, a.val ∈ U → b.val ∈ U →
      b ∈ sourceRealActionLevelSet hp hp1 a → f b.val = f a.val)
    (φ : realTypeSourceSubmodule p) (hφ : φ.val ∈ U) :
    ∃ C : SourceBirkhoffInverseChart D φ U,
      ∃ Z : Set (Coeff p × Coeff p), ∃ T : Set (Coeff q), ∃ g : Coeff q → ℂ,
        IsOpen Z ∧ sourceBirkhoffMap hp hp1 t φ.val ∈ Z ∧ Z ⊆ C.target ∧
        IsOpen T ∧ quadraticActionsExponent (q := q) '' Z = T ∧ AnalyticOnNhd ℂ g T ∧
        ∀ z ∈ Z, g (quadraticActionsExponent z) = f (C.inverse z) := by
  obtain ⟨C⟩ := D.exists_inverseChart φ U hU hφ
  have hF := C.analytic_comp f hf
  obtain ⟨S,R,hR,hbase,hball,hhead⟩ := Coeff.exists_nonzeroFiniteCenter_ball
    hp C.target C.target_open _ C.center_mem
  let c := Coeff.truncatePair S (sourceBirkhoffMap hp hp1 t φ.val)
  have hc : c ∈ Coeff.realPairLocus p :=
    Coeff.truncatePair_mem_realPairLocus S _ ((Coeff.mem_realPairLocus_iff _).mpr
      ⟨sourceRealBirkhoffMap hp hp1 t φ,D.real_map_complex_inclusion φ⟩)
  have hsign : ∀ e d : ℤ → Bool, (∀ n ∈ S, e n = false) → (∀ n ∈ S, d n = false) →
      ∀ z ∈ ball c R, (f ∘ C.inverse) (Coeff.pairSignChange e d z) = (f ∘ C.inverse) z := by
    intro e d he hd z hz
    exact Coeff.eqOn_pairSignChange_of_real_action_invariance (f ∘ C.inverse) c R hR hc
      (hF.mono hball) (fun a ha b hb har hbr hab =>
        C.lifted_real_action_invariance_on f hinv a b (hball ha) (hball hb) har hbr hab)
      e d (Coeff.pairSignChange_truncatePair S _ e d he hd) hz
  have hrot : ∀ z ∈ ball c R, ∀ k, fderiv ℂ (f ∘ C.inverse) z
      (Coeff.actionRotationVectorCLM p k z) = 0 := by
    intro z hz k
    exact Coeff.fderiv_actionRotationVector_eq_zero_of_real_action_invariance _ _ isOpen_ball
      (convex_ball c R) c (mem_ball_self hR) hc (hF.mono hball)
      (fun a ha b hb har hbr hab => C.lifted_real_action_invariance_on f hinv a b
        (hball ha) (hball hb) har hbr hab) z hz k
  obtain ⟨Z,T,g,hZ,hz₀,hZV,hT,himage,hg,hrec⟩ := Coeff.exists_local_scalar_action_factor
    (q := q) hp S (f ∘ C.inverse) (ball c R) isOpen_ball (hF.mono hball)
    hsign hrot _ hbase hhead
  exact ⟨C,Z,T,g,hZ,hz₀,hZV.trans hball,hT,himage,hg,hrec⟩

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
