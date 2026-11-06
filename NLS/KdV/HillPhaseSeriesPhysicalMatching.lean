import NLS.KdV.HillPhaseFiniteHead
import NLS.KdV.HillSummedRegularCorrection
import NLS.SequenceSpaces.FiniteHeadSeries

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
include h0q h0r

/-- The finite-head/normal-tail phase is the actual full summed physical
regular correction plus the selected own angle, with its exact anchor. -/
theorem eventually_hillPhaseSeries_eq_full_physical_phase
    (n N : ℕ) (hn : 1≤n) (hN : 1≤N)
    (V : Set RealPeriodOneHillPotential) (hV : IsOpen V) (hqV : (⟨q,hq,hr⟩ : RealPeriodOneHillPotential)∈V)
    (β : ℕ → WeightedCoeff SpectralWeight.one.toWeight 2 → ℂ)
    (hz : ∀ j : ℕ, ¬(N≤j+1 ∧ j+1≠n) → β j=0)
    (hβreal : ∀ p∈V, ∀ j : ℕ, ∀ _hj : N≤j+1, j+1≠n → β j p.val=
      hillRegularAbelianCorrection p.val p.property.1 p.property.2 n hn (j+1) (by omega))
    (B ε : ℕ → Coeff 2 → ℂ)
    (hmatch : ∀ j : ℕ, ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      B j (SpectralWeight.one.toCoeff p.val)=hillRegularAbelianCorrection p.val p.property.1 p.property.2 n hn (j+1) (by omega)+
        (if j+1=n then 1 else 0)*(ε j (SpectralWeight.one.toCoeff p.val)-(Real.pi : ℂ))) :
    ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      (∑ j∈hillPhaseFiniteHead N n,B j (SpectralWeight.one.toCoeff p.val))+(∑' j : ℕ,β j p.val)=
        hillSummedRegularAbelianCorrection p.val p.property.1 p.property.2 n hn+
          ε (n-1) (SpectralWeight.one.toCoeff p.val)-(Real.pi : ℂ) := by
  let J := hillPhaseFiniteHead N n
  have hm : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      ∀ j∈J, B j (SpectralWeight.one.toCoeff p.val)=hillRegularAbelianCorrection p.val p.property.1 p.property.2 n hn (j+1) (by omega)+
        (if j+1=n then 1 else 0)*(ε j (SpectralWeight.one.toCoeff p.val)-(Real.pi : ℂ)) :=
    (Filter.eventually_all_finset J).mpr (fun j _ => hmatch j)
  filter_upwards [hV.mem_nhds hqV,hm] with p hpV hphead
  let r : ℕ → ℂ := fun j => hillRegularAbelianCorrection p.val p.property.1 p.property.2 n hn (j+1) (by omega)
  have hβid (j : ℕ) : β j p.val=if j∈J then 0 else r j := by
    by_cases hj : j∈J
    · have hh := (mem_hillPhaseFiniteHead N n hN hn j).mp hj
      rw [hz j (by omega),if_pos hj]
      rfl
    · have hh := (mem_hillPhaseFiniteHead N n hN hn j).not.mp hj
      rw [if_neg hj]
      exact hβreal p hpV j (by omega) (by omega)
  have hown : (∑ j∈J,(if j+1=n then 1 else 0 : ℂ)*(ε j (SpectralWeight.one.toCoeff p.val)-(Real.pi : ℂ)))=
      ε (n-1) (SpectralWeight.one.toCoeff p.val)-(Real.pi : ℂ) := by
    calc
      _ = (if (n-1)+1=n then 1 else 0 : ℂ)*(ε (n-1) (SpectralWeight.one.toCoeff p.val)-(Real.pi : ℂ)) := by
        apply Finset.sum_eq_single (n-1)
        · intro j _ hj
          rw [if_neg (by omega : j+1≠n),zero_mul]
        · intro hh
          exact False.elim (hh (Finset.mem_insert_self (n-1) (Finset.range (N-1))))
      _ = _ := by rw [if_pos (by omega : n-1+1=n),one_mul]
  have hhead : (∑ j∈J,B j (SpectralWeight.one.toCoeff p.val))=
      (∑ j∈J,r j)+ε (n-1) (SpectralWeight.one.toCoeff p.val)-(Real.pi : ℂ) := by
    calc
      _ = ∑ j∈J,(r j+(if j+1=n then 1 else 0 : ℂ)*(ε j (SpectralWeight.one.toCoeff p.val)-(Real.pi : ℂ))) :=
        Finset.sum_congr rfl (fun j hj => hphead j hj)
      _ = (∑ j∈J,r j)+∑ j∈J,(if j+1=n then 1 else 0 : ℂ)*(ε j (SpectralWeight.one.toCoeff p.val)-(Real.pi : ℂ)) :=
        Finset.sum_add_distrib
      _ = _ := by rw [hown];ring
  change (∑ j∈J,B j (SpectralWeight.one.toCoeff p.val))+(∑' j : ℕ,β j p.val)=_
  rw [hhead,tsum_congr hβid]
  have hs := sum_finite_head_add_tsum_complement r
    (summable_hillRegularAbelianCorrection h0q h0r p.val p.property.1 p.property.2 n hn) J
  change ((∑ j∈J,r j)+ε (n-1) (SpectralWeight.one.toCoeff p.val)-(Real.pi : ℂ))+
    (∑' j : ℕ,if j∈J then 0 else r j)=(∑' j : ℕ,r j)+ε (n-1) (SpectralWeight.one.toCoeff p.val)-(Real.pi : ℂ)
  linear_combination hs

end NLS.KdV
