import NLS.KdV.HillPhysicalMiuraMomentSum
import NLS.KdV.HillHminusWeightedSecondMoments

/-! # Actual analytic physical moment-frequency charts in H-minus-one

The chart is constructed at every real rough source. Its scalar functions
recover the original physical weighted moment series at every original
real source in the domain, with all indices on one common open set.
-/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.ZakharovShabat
open scoped ComplexConjugate
namespace NLS.KdV

structure PhysicalMiuraFrequencyChart where
  psi : HillHminusPsiChart
  shift : ℝ
  shift_pos : 0 < shift
  energyShift_eq : psi.miura.energyShift = (shift : ℂ)^2
  rootNeighborhood : Set (CoeffPair 2)
  atlas : SourceAbelianMomentAtlas (by simp) (by norm_num) rootNeighborhood psi.family.roots
  domain : Set PeriodOneHminusOne
  domain_open : IsOpen domain
  domain_subset : domain ⊆ psi.source
  real_lift : ∀ a ∈ psi.miura.domain, IsRealPeriodOneHminusOne a → ∀ j : ℤ,
    psi.miura.lift a (-j) = conj (psi.miura.lift a j)
  outside_shift : ∀ a ∈ psi.miura.domain, hillHminusRadicand a (-psi.miura.energyShift) ≠ 0
  analytic_moments : ∀ n : ℤ, AnalyticOnNhd ℂ
    (fun a => atlas.weightedSecondMomentSum n (hillMiuraDiagonal (psi.miura.lift a))) domain
  absolute_moments : ∀ a ∈ domain, ∀ n : ℤ, Summable
    (fun k : ℤ => ‖(k : ℂ)*atlas.moment n k 2 (hillMiuraDiagonal (psi.miura.lift a))‖)
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  moment_bound : ∀ a ∈ domain, ∀ n : ℤ,
    ‖atlas.weightedSecondMomentSum n (hillMiuraDiagonal (psi.miura.lift a))‖ ≤ (1+‖(n : ℂ)‖)*bound

namespace PhysicalMiuraFrequencyChart

def correction (B : PhysicalMiuraFrequencyChart) (n : ℕ+) (a : PeriodOneHminusOne) : ℂ :=
  -12*B.atlas.weightedSecondMomentSum (n : ℤ) (hillMiuraDiagonal (B.psi.miura.lift a))

theorem analytic_correction (B : PhysicalMiuraFrequencyChart) (n : ℕ+) :
    AnalyticOnNhd ℂ (B.correction n) B.domain :=
  analyticOnNhd_const.mul (B.analytic_moments (n : ℤ))

/-- The scalar chart has the exact physical weighted moment series,
including its coefficient -12, at every original source in its domain. -/
theorem correction_eq_physical (B : PhysicalMiuraFrequencyChart)
    (q : RealPeriodOneHillPotential) (hq : hillOriginalHminusSource q.val ∈ B.domain) (n : ℕ+) :
    B.correction n (hillOriginalHminusSource q.val) =
      -12*∑' k : ℕ, (k : ℂ)*hillPhysicalFrequencyMoment q.val q.property.1 q.property.2 n n.pos k 2 := by
  have h := B.psi.physical_weighted_secondMoment_sum q (B.domain_subset hq) B.real_lift
    (B.outside_shift _ (B.domain_subset hq).1) B.shift B.energyShift_eq B.atlas n
    (B.absolute_moments _ hq (n : ℤ))
  exact congrArg (fun z : ℂ => -12*z) h.2.symm

theorem summable_physical_secondMoments (B : PhysicalMiuraFrequencyChart)
    (q : RealPeriodOneHillPotential) (hq : hillOriginalHminusSource q.val ∈ B.domain) (n : ℕ+) :
    Summable (fun k : ℕ+ => ‖(k : ℂ)*hillPhysicalFrequencyMoment q.val q.property.1 q.property.2 n n.pos k 2‖) :=
  (B.psi.physical_weighted_secondMoment_sum q (B.domain_subset hq) B.real_lift
    (B.outside_shift _ (B.domain_subset hq).1) B.shift B.energyShift_eq B.atlas n
    (B.absolute_moments _ hq (n : ℤ))).1

end PhysicalMiuraFrequencyChart

/-- No Miura inverse, root branch or series hypothesis is supplied by
the caller. One common domain contains the specified real rough source. -/
theorem exists_physicalMiuraFrequencyChart (q : PeriodOneHminusOne)
    (hq : IsRealPeriodOneHminusOne q) (M : ℝ) :
    ∃ B : PhysicalMiuraFrequencyChart, q ∈ B.domain ∧ M < B.shift := by
  obtain ⟨P,c,W,A,T,hc,hMc,hshift,hT,hqT,hTP,hreal,houtside,ha,hsum,C,hC,hbound⟩ :=
    exists_hillHminus_weighted_secondMoment_chart q hq M
  exact ⟨⟨P,c,hc,hshift,W,A,T,hT,hTP,hreal,houtside,ha,hsum,C,hC,hbound⟩,hqT,hMc⟩

end NLS.KdV
