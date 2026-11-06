import NLS.KdV.HillMiuraGroundFiniteGap
import NLS.ZakharovShabat.SourceFiniteGapCompactContainer

/-! # Norm compactness for bounded actual factors with fixed gap support

The original Dirac Hilbert compact container and the continuous Miura map
provide a genuine H-minus-one compact container. Both the constant shift
and the factor are actual; no weak-limit or no-energy-loss premise is used.
-/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV

/-- A common finite actual Dirac gap support and a factor norm bound give
a norm-compact container for the corresponding normalized rough sources. -/
theorem exists_compact_hillHminus_container_of_finite_ground_support
    (S : Finset ℤ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ K : Set PeriodOneHminusOne, IsCompact K ∧
      ∀ (q : PeriodOneHminusOne) (u : PeriodOneRealL2), ‖u.val‖ ≤ R →
      periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 (‖u.val‖^2 : ℂ)) →
      (∀ n ∉ S, canonicalPeriodicGap (by simp) (by norm_num)
        (periodOnePotential (hillMiuraDiagonal u.val)) (periodOnePotential_mem _) n = 0) → q ∈ K := by
  obtain ⟨C,hC,hcontains⟩ := exists_compact_source_container_of_finite_gap_support S (2*R) (by positivity)
  let f : realTypeSourceSubmodule 2 → PeriodOneHminusOne := fun φ =>
    periodOneMiura φ.val.fst-periodOneL2Inclusion (lp.single 2 0 (‖φ.val.fst‖^2 : ℂ))
  have hfst : Continuous (fun φ : realTypeSourceSubmodule 2 => φ.val.fst) :=
    (WithLp.continuous_fst _ _ _).comp continuous_subtype_val
  have hf : Continuous f := (continuous_periodOneMiura.comp hfst).sub
    (periodOneL2Inclusion.continuous.comp
      ((lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) 2 0).continuous.comp
        ((continuous_ofReal.comp hfst.norm).pow 2)))
  refine ⟨f '' C,hC.image hf,?_⟩
  intro q u hu hi hclosed
  have hn := WithLp.prod_norm_sq_eq_of_L2 (hillMiuraDiagonal u.val)
  rw [hillMiuraDiagonal_fst,hillMiuraDiagonal_snd] at hn
  have hpair : ‖(hillMiuraRealSource u).val‖ ≤ 2*R := by
    change ‖hillMiuraDiagonal u.val‖ ≤ 2*R
    nlinarith [norm_nonneg (hillMiuraDiagonal u.val),norm_nonneg u.val]
  refine ⟨hillMiuraRealSource u,hcontains _ hpair hclosed,?_⟩
  dsimp only [f,hillMiuraRealSource]
  rw [hillMiuraDiagonal_fst,hi,add_sub_cancel_right]

/-- A closed actual Hill tail gives a fixed finite support for EVERY
actual normalized factor, retaining both signs of the Dirac spectrum. -/
theorem hillMiura_gap_zero_outside_ground_tail
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q)
    (u : PeriodOneRealL2) (e : ℝ) (hu : u.val 0 = 0)
    (hi : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 (e : ℂ)))
    (N : ℕ) (hN : 1 ≤ N)
    (hclosed : ∀ n : ℕ, N ≤ n → hillHminusRealLabels q hr (2*n)=hillHminusRealLabels q hr (2*n-1))
    (j : ℤ) (hj : j ∉ Finset.Icc (-(N : ℤ)) (N : ℤ)) :
    canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (hillMiuraDiagonal u.val)) (periodOnePotential_mem _) j = 0 := by
  have hpair (n : ℕ) (hn : N ≤ n) : hillMiuraDiracLeft u.val n=hillMiuraDiracRight u.val n :=
    (hillHminus_closed_gap_iff_miuraDirac_pair_eq_of_meanZero q hr u e hi hu n (by omega)).mp (hclosed n hn)
  change hillMiuraDiracRight u.val j-hillMiuraDiracLeft u.val j=0
  simp only [Finset.mem_Icc] at hj
  cases j with
  | ofNat n =>
    simp only [Int.ofNat_eq_natCast] at hj
    exact sub_eq_zero.mpr (hpair n (by omega)).symm
  | negSucc n =>
    have hneg := hillMiuraCanonicalEndpoints_neg u.val ((n+1 : ℕ) : ℤ)
    change hillMiuraDiracLeft u.val (-((n+1 : ℕ) : ℤ)) = -hillMiuraDiracRight u.val (n+1) ∧
      hillMiuraDiracRight u.val (-((n+1 : ℕ) : ℤ)) = -hillMiuraDiracLeft u.val (n+1) at hneg
    change hillMiuraDiracRight u.val (-((n+1 : ℕ) : ℤ))-
      hillMiuraDiracLeft u.val (-((n+1 : ℕ) : ℤ))=0
    rw [hneg.1,hneg.2]
    have hp : hillMiuraDiracLeft u.val ((n : ℤ)+1)=hillMiuraDiracRight u.val ((n : ℤ)+1) := by
      simpa only [Nat.cast_add,Nat.cast_one] using hpair (n+1) (by omega)
    rw [hp,sub_self]

end NLS.KdV
