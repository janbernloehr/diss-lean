import NLS.KdV.HillPhysicalMiuraSecondMoment
import NLS.ZakharovShabat.SourceWeightedSecondMomentSums

/-! # The physical weighted sum is the analytic signed Dirac moment sum -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.ZakharovShabat
open scoped ComplexConjugate
namespace NLS.KdV.HillHminusPsiChart

theorem physical_weighted_secondMoment_sum (P : HillHminusPsiChart)
    (q : RealPeriodOneHillPotential) (hq : hillOriginalHminusSource q.val ∈ P.source)
    (hreal : ∀ a ∈ P.miura.domain, IsRealPeriodOneHminusOne a → ∀ j : ℤ,
      P.miura.lift a (-j) = conj (P.miura.lift a j))
    (houtside : hillHminusRadicand (hillOriginalHminusSource q.val) (-P.miura.energyShift) ≠ 0)
    (c : ℝ) (hshift : P.miura.energyShift = (c : ℂ)^2)
    {W : Set (CoeffPair 2)}
    (A : SourceAbelianMomentAtlas (by simp) (by norm_num) W P.family.roots)
    (n : ℕ+)
    (hs : Summable (fun k : ℤ => ‖(k : ℂ)*A.moment (n : ℤ) k 2
      (hillMiuraDiagonal (P.miura.lift (hillOriginalHminusSource q.val)))‖)) :
    Summable (fun k : ℕ+ => ‖(k : ℂ)*hillPhysicalFrequencyMoment q.val q.property.1 q.property.2 n n.pos k 2‖) ∧
      (∑' k : ℕ, (k : ℂ)*hillPhysicalFrequencyMoment q.val q.property.1 q.property.2 n n.pos k 2) =
        A.weightedSecondMomentSum (n : ℤ) (hillMiuraDiagonal (P.miura.lift (hillOriginalHminusSource q.val))) := by
  have hpair := NLS.SequenceSpaces.int_weighted_sum_eq_positive_pairs
    (fun k => A.moment (n : ℤ) k 2 (hillMiuraDiagonal (P.miura.lift (hillOriginalHminusSource q.val)))) hs
  have hm (k : ℕ+) := P.physical_secondMoment_eq_miura_pair q hq hreal houtside c hshift A n k
  refine ⟨hpair.1.congr (fun k => by rw [hm k]),?_⟩
  have hpos :
      (∑' k : ℕ+, (k : ℂ)*hillPhysicalFrequencyMoment q.val q.property.1 q.property.2 n n.pos k 2) =
        ∑' k : ℕ, (k : ℂ)*hillPhysicalFrequencyMoment q.val q.property.1 q.property.2 n n.pos k 2 := by
    convert! (tsum_subtype_eq_of_support_subset (s := {k : ℕ | 0<k})
      (f := fun (k : ℕ) => (k : ℂ)*hillPhysicalFrequencyMoment q.val q.property.1 q.property.2 n n.pos k 2) ?_) using 1
    intro k hk
    by_contra h
    have hk0 : k=0 := by simpa only [Set.mem_ofPred_eq,not_lt,Nat.le_zero] using h
    exact hk (by simp only [hk0,Nat.cast_zero,zero_mul])
  rw [← hpos]
  unfold SourceAbelianMomentAtlas.weightedSecondMomentSum
  rw [hpair.2]
  exact tsum_congr (fun k => by rw [hm k])

end NLS.KdV.HillHminusPsiChart
