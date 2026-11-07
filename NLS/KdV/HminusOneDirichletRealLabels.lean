import NLS.KdV.HminusOneDirichletRealEnumeration
import NLS.KdV.HminusOneDirichletSimplicity
import Mathlib.Order.WellFounded

/-! Intrinsic FULL ordered scalar Dirichlet characteristic labels on
every real original H-minus-one potential. Positive indices start at one;
central values, the index offset and analytic multiplicities are retained.
Native H_dir^1 to H_dir^(-1) operator identification remains separate. -/
noncomputable section
open Set Complex
open scoped Classical
namespace NLS.KdV

/-- Every real original potential has a strictly ordered positive-index
enumeration of its ENTIRE scalar Dirichlet characteristic zero set. -/
theorem exists_hillHminusDirichlet_real_labels
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) :
    ∃ mu : ℕ+ → ℝ, StrictMono mu ∧ ∀ lambda : ℂ,
      hillHminusDirichlet q lambda = 0 ↔ ∃ n : ℕ+, lambda = (mu n:ℂ) := by
  obtain ⟨c,_,_,u,hi⟩ := exists_real_periodOneMiura_shift q hq 0
  have hi' : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 ((c^2:ℝ):ℂ)) :=
    by simpa only [Complex.ofReal_pow] using hi
  let mu : ℕ+ → ℝ := fun n => (hillMiuraDirichletEnergy u.val (c^2:ℝ) (n:ℕ)).re
  refine ⟨mu,strictMono_hillMiuraDirichletEnergy_re_positive u (c^2),fun lambda => ?_⟩
  rw [hillHminusDirichlet_roots_iff_positive_miura q hq u (c^2) hi' lambda]
  apply exists_congr
  intro n
  change (lambda = hillMiuraDirichletEnergy u.val (c^2:ℝ) (n:ℕ)) ↔
    lambda = ((hillMiuraDirichletEnergy u.val (c^2:ℝ) (n:ℕ)).re:ℂ)
  rw [hillMiuraDirichletEnergy_ofReal_re]

/-- Intrinsic original positive scalar Dirichlet labels, including the
finite central block, in strictly increasing real order. -/
def hillHminusDirichletLabels (q : PeriodOneHminusOne)
    (hq : IsRealPeriodOneHminusOne q) : ℕ+ → ℝ :=
  (exists_hillHminusDirichlet_real_labels q hq).choose

theorem strictMono_hillHminusDirichletLabels (q : PeriodOneHminusOne)
    (hq : IsRealPeriodOneHminusOne q) : StrictMono (hillHminusDirichletLabels q hq) :=
  (exists_hillHminusDirichlet_real_labels q hq).choose_spec.1

/-- Every scalar characteristic zero is listed, including every low
energy, with the exact original positive index convention. -/
theorem hillHminusDirichletLabels_roots_iff (q : PeriodOneHminusOne)
    (hq : IsRealPeriodOneHminusOne q) (lambda : ℂ) :
    hillHminusDirichlet q lambda = 0 ↔
      ∃ n : ℕ+, lambda = (hillHminusDirichletLabels q hq n:ℂ) :=
  (exists_hillHminusDirichlet_real_labels q hq).choose_spec.2 lambda

theorem hillHminusDirichletLabels_is_root (q : PeriodOneHminusOne)
    (hq : IsRealPeriodOneHminusOne q) (n : ℕ+) :
    hillHminusDirichlet q (hillHminusDirichletLabels q hq n) = 0 :=
  (hillHminusDirichletLabels_roots_iff q hq _).mpr ⟨n,rfl⟩

/-- Strict order and the complete zero set determine every scalar label,
without an assumed common high tail or a supplied central root list. -/
theorem hillHminusDirichletLabels_unique (q : PeriodOneHminusOne)
    (hq : IsRealPeriodOneHminusOne q) (mu : ℕ+ → ℝ) (hm : StrictMono mu)
    (hr : ∀ lambda : ℂ, hillHminusDirichlet q lambda = 0 ↔
      ∃ n : ℕ+, lambda = (mu n:ℂ)) : mu = hillHminusDirichletLabels q hq := by
  apply (hm.range_inj (strictMono_hillHminusDirichletLabels q hq)).mp
  ext x
  constructor
  · rintro ⟨n,rfl⟩
    have hz := (hr (mu n)).mpr ⟨n,rfl⟩
    obtain ⟨m,he⟩ := (hillHminusDirichletLabels_roots_iff q hq _).mp hz
    exact ⟨m,Complex.ofReal_inj.mp he.symm⟩
  · rintro ⟨n,rfl⟩
    have hz := hillHminusDirichletLabels_is_root q hq n
    obtain ⟨m,he⟩ := (hr _).mp hz
    exact ⟨m,Complex.ofReal_inj.mp he.symm⟩

/-- ANY actual real shifted Miura representation gives the SAME entire
intrinsic scalar sequence at the SAME positive index, including central values. -/
theorem hillHminusDirichletLabels_eq_miura (q : PeriodOneHminusOne)
    (hq : IsRealPeriodOneHminusOne q) (u : PeriodOneRealL2) (c : ℝ)
    (hi : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 (c:ℂ))) :
    hillHminusDirichletLabels q hq =
      fun n : ℕ+ => (hillMiuraDirichletEnergy u.val c (n:ℕ)).re := by
  symm
  apply hillHminusDirichletLabels_unique q hq _
    (strictMono_hillMiuraDirichletEnergy_re_positive u c)
  intro lambda
  rw [hillHminusDirichlet_roots_iff_positive_miura q hq u c hi lambda]
  apply exists_congr
  intro n
  rw [hillMiuraDirichletEnergy_ofReal_re]

/-- The full ordered scalar list counts exactly every analytic
multiplicity. All real-potential Dirichlet zeros are simple, including low ones. -/
theorem hillHminusDirichletLabels_global_multiplicity
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) (lambda : ℂ) :
    (∑ᶠ n : ℕ+, if (hillHminusDirichletLabels q hq n:ℂ) = lambda then (1:ℕ) else 0) =
      analyticOrderNatAt (hillHminusDirichlet q) lambda := by
  have hInjective : Function.Injective (fun n : ℕ+ => (hillHminusDirichletLabels q hq n:ℂ)) :=
    fun i j he => (strictMono_hillHminusDirichletLabels q hq).injective (Complex.ofReal_inj.mp he)
  by_cases hz : hillHminusDirichlet q lambda = 0
  · obtain ⟨n,hn⟩ := (hillHminusDirichletLabels_roots_iff q hq lambda).mp hz
    have hothers (m : ℕ+) (hmn : m ≠ n) :
        (if (hillHminusDirichletLabels q hq m:ℂ) = lambda then (1:ℕ) else 0) = 0 := by
      apply if_neg
      intro he
      exact hmn (hInjective (he.trans hn))
    rw [finsum_eq_single _ n hothers,if_pos hn.symm,
      analyticOrderNatAt_hillHminusDirichlet_eq_one_of_real q hq lambda hz]
  · have hterms : (fun n : ℕ+ =>
        if (hillHminusDirichletLabels q hq n:ℂ) = lambda then (1:ℕ) else 0) = 0 := by
      funext n
      apply if_neg
      intro he
      exact hz (he ▸ hillHminusDirichletLabels_is_root q hq n)
    rw [hterms]
    change (∑ᶠ _ : ℕ+, (0:ℕ)) = analyticOrderNatAt (hillHminusDirichlet q) lambda
    have ho : analyticOrderAt (hillHminusDirichlet q) lambda = 0 :=
      analyticOrderAt_eq_zero.mpr (Or.inr hz)
    rw [finsum_zero,analyticOrderNatAt,ho,ENat.toNat_zero]

end NLS.KdV
