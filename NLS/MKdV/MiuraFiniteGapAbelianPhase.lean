import NLS.MKdV.MiuraFiniteAbelianPhases
import NLS.MKdV.MiuraFiniteGap
import NLS.KdV.HillFiniteAbelianSupport

/-! # Independent Abelian divisor phases on finite-gap Miura profiles

The support set is selected from the original physical contour actions.
It contains all open Hill gaps. All further summands vanish exactly, so
the result is the full Abelian series and is independent of the selected
finite support set. No action-generator identity is assumed or asserted.
-/
noncomputable section
open Set Complex
open NLS.KdV NLS.ZakharovShabat
open scoped ComplexConjugate
namespace NLS.MKdV

def miuraFiniteGapAbelianSupport (a : ScalarDomain 2) (ha : ∀ j, a.val j = conj (a.val (-j)))
    (hfg : miuraFiniteGap a ha) : Finset ℕ :=
  ((miuraFiniteGap_iff_action_support a ha).mp hfg).toFinset.image (fun j => j-1)

theorem miuraFiniteGapAbelianSupport_closed_complement (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (hfg : miuraFiniteGap a ha) (k : ℕ)
    (hk : k ∉ miuraFiniteGapAbelianSupport a ha hfg) :
    hillRealGapHalfLength (realSobolevMiuraHillPotential a ha).val
      (realSobolevMiuraHillPotential a ha).property.1 (realSobolevMiuraHillPotential a ha).property.2 (k+1) = 0 := by
  apply (realSobolevMiuraHill_halfLength_zero_iff_action_zero a ha (k+1) (by omega)).mpr
  by_contra hJ
  apply hk
  apply Finset.mem_image.mpr
  refine ⟨k+1,?_,by omega⟩
  have hfin := (miuraFiniteGap_iff_action_support a ha).mp hfg
  exact hfin.mem_toFinset.mpr ⟨by omega,hJ⟩

def miuraFiniteGapAbelianPhase (a : ScalarDomain 2) (ha : ∀ j, a.val j = conj (a.val (-j)))
    (hfg : miuraFiniteGap a ha) (n : ℕ) (hn : 1 ≤ n) : ℂ :=
  miuraFiniteAbelianPhase a ha n hn (miuraFiniteGapAbelianSupport a ha hfg)

theorem miuraFiniteGapAbelian_corrections_summable (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (hfg : miuraFiniteGap a ha) (n : ℕ) (hn : 1 ≤ n) :
    Summable (fun k : ℕ => hillDirichletRegularAbelianTerm (realSobolevMiuraHillPotential a ha)
      n hn (k+1) (by omega)) :=
  summable_hillDirichletRegularAbelianTerm_of_closed_complement _ n hn
    (miuraFiniteGapAbelianSupport a ha hfg) (miuraFiniteGapAbelianSupport_closed_complement a ha hfg)

theorem miuraFiniteGapAbelianPhase_eq_full_series (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (hfg : miuraFiniteGap a ha) (n : ℕ) (hn : 1 ≤ n) :
    miuraFiniteGapAbelianPhase a ha hfg n hn =
      hillDirichletUnitPhase (realSobolevMiuraHillPotential a ha) n hn*
        exp (I*∑' k : ℕ,hillDirichletRegularAbelianTerm (realSobolevMiuraHillPotential a ha)
          n hn (k+1) (by omega)) := by
  rw [miuraFiniteGapAbelianPhase,miuraFiniteAbelianPhase,hillFiniteAbelianPhase,
    hillFiniteRegularAbelianSum_eq_tsum_of_closed_complement _ n hn
      (miuraFiniteGapAbelianSupport a ha hfg) (miuraFiniteGapAbelianSupport_closed_complement a ha hfg)]

theorem norm_miuraFiniteGapAbelianPhase (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (hfg : miuraFiniteGap a ha) (n : ℕ) (hn : 1 ≤ n)
    (hJ : miuraMKdVAction a ha n ≠ 0) : ‖miuraFiniteGapAbelianPhase a ha hfg n hn‖ = 1 :=
  norm_miuraFiniteAbelianPhase a ha n hn hJ _

theorem miuraFiniteGapAbelianPhase_independent_support (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (hfg : miuraFiniteGap a ha) (n : ℕ) (hn : 1 ≤ n)
    (F : Finset ℕ) (hF : ∀ k, k ∉ F → miuraMKdVAction a ha (k+1) = 0) :
    miuraFiniteGapAbelianPhase a ha hfg n hn = miuraFiniteAbelianPhase a ha n hn F :=
  hillFiniteAbelianPhase_independent_support _ n hn _ F
    (miuraFiniteGapAbelianSupport_closed_complement a ha hfg)
    (fun k hk => (realSobolevMiuraHill_halfLength_zero_iff_action_zero a ha (k+1) (by omega)).mpr (hF k hk))

end NLS.MKdV
