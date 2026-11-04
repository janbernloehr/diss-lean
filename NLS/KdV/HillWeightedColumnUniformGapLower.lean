import NLS.KdV.HillWeightedColumnIndexRatios
import NLS.ZakharovShabat.SourcePsiGapQuotientUniformLower

/-! A single positive lower bound controls the regular weighted diagonal
column on every original real gap, before all numerator indices and all
balanced full gap inputs. -/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV

theorem hillWeightedColumnGapNumerator_uniform_gap_lower
    {V : Set (CoeffPair 2)} {D : ℤ → Set ℂ} {C : ℝ}
    (hD : SourceIsolatingNeighborhoods (by norm_num) (by norm_num) V D C)
    (ψ : CoeffPair 2) (hψ : ψ ∈ V) (hreal : IsRealType (CoeffPair.toMax 2 ψ)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ c : ℂ, ∀ d : lp (fun _ : ℕ+ => ℂ) 2,
      hillIndependentFrequencyDisplacement (c,d) ∈ sourcePeriodicGapRootSet (by norm_num) (by norm_num) ψ →
      ∀ n m : ℕ+, m ≠ n → ∀ z ∈ sourcePeriodicSegment (by norm_num) (by norm_num) ψ ((m:ℕ):ℤ),
        δ ≤ ‖hillPeriodEquationWeight n m*hillProductColumnGapNumerator n m c ψ ((m:ℕ):ℤ) d z‖ := by
  obtain ⟨γ,hγ,hR⟩ := hD.indexRatio_uniform_lower
  obtain ⟨b,hb,hQ⟩ := hD.gap_quotient_uniform_lower ψ hψ hreal
  refine ⟨γ*γ*γ*b,by positivity,?_⟩
  intro c d ha n m hmn z hz
  let a := hillIndependentFrequencyDisplacement (c,d)
  have hplace : a ∈ sourcePsiOriginalRootPlacement (p := 2) D := fun k => hD.gap ψ hψ k (ha k)
  have hmn' : ((n:ℕ):ℤ) ≠ ((m:ℕ):ℤ) := by intro h; exact hmn (Subtype.ext (Int.ofNat.inj h.symm))
  have hmneg : -((m:ℕ):ℤ) ≠ ((m:ℕ):ℤ) := by have := m.pos; omega
  have hnneg : -((n:ℕ):ℤ) ≠ ((m:ℕ):ℤ) := by have := n.pos; have := m.pos; omega
  have hother : z ∈ sourceStandardRootOmittedDomain (by norm_num) (by norm_num) ψ ((m:ℕ):ℤ) := by
    intro k hkm hzk
    exact Set.disjoint_left.mp (hD.disjoint ((m:ℕ):ℤ) k hkm.symm) (hD.gap ψ hψ _ hz) (hD.gap ψ hψ k hzk)
  rw [hillWeightedColumnGapNumerator_eq_indexRatios hD ψ c d hplace n m hmn z
    (subset_closure (hD.gap ψ hψ _ hz)) hother,norm_mul,norm_mul,norm_mul,norm_neg]
  exact mul_le_mul
    (mul_le_mul (mul_le_mul (hR a hplace _ _ hmneg z (hD.gap ψ hψ _ hz))
      (hR a hplace _ _ hmn' z (hD.gap ψ hψ _ hz)) hγ.le (norm_nonneg _))
      (hR a hplace _ _ hnneg z (hD.gap ψ hψ _ hz)) hγ.le (by positivity))
    (hQ a ha _ z hz) hb.le (by positivity)

end NLS.KdV
