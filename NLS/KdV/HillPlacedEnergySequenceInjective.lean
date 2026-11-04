import NLS.KdV.HillCanonicalZeroSequencePeriods

/-! Balanced roots placed in the ORIGINAL signed isolating discs
have distinct squared energies at ALL positive labels. Both signs in
the quadratic identity are ruled out by actual disc disjointness. -/
noncomputable section
open Set Complex
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

theorem placed_energySequence_injective (P : HillProductEquationPatch) (c : ℂ)
    (d : lp (fun _ : ℕ+ => ℂ) 2) (hplace : ∀ k : ℤ, hillIndependentFrequency (c,d) k ∈ P.discs k) :
    Function.Injective (fun m : ℕ+ => hillEnergySequenceZero m d) := by
  intro m k he
  change hillEnergySequenceZero m d = hillEnergySequenceZero k d at he
  by_contra hmk
  have hmpos : (0:ℤ) < ((m:ℕ):ℤ) := by exact_mod_cast m.pos
  have hkpos : (0:ℤ) < ((k:ℕ):ℤ) := by exact_mod_cast k.pos
  have hmk' : ((m:ℕ):ℤ) ≠ ((k:ℕ):ℤ) := fun h => hmk (Subtype.ext (Int.ofNat.inj h))
  have hmkneg : ((m:ℕ):ℤ) ≠ -((k:ℕ):ℤ) := by omega
  have hsq : hillIndependentFrequency (c,d) ((m:ℕ):ℤ)^2 = hillIndependentFrequency (c,d) ((k:ℕ):ℤ)^2 := by
    rw [hillIndependentFrequency_positive_sq,hillIndependentFrequency_positive_sq,he]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with hsame | hneg
  · have hm := hplace ((m:ℕ):ℤ)
    rw [hsame] at hm
    exact Set.disjoint_left.mp (P.isolating.disjoint _ _ hmk') hm (hplace _)
  · have hm := hplace ((m:ℕ):ℤ)
    rw [hneg,← hillIndependentFrequency_neg] at hm
    exact Set.disjoint_left.mp (P.isolating.disjoint _ _ hmkneg) hm (hplace _)

theorem actual_complex_zero_energySequence_injective (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (n : ℕ+)
    (ht : (hillHminusCanonicalZeroSequence n q,q) ∈ P.inputDomain) :
    Function.Injective (fun m : ℕ+ => hillEnergySequenceZero m (hillHminusCanonicalZeroSequence n q)) :=
  P.placed_energySequence_injective (P.parent.parent.miuraBall.actionBall.shift:ℂ) _ ht.1.2

end NLS.KdV.HillProductEquationPatch
