import NLS.KdV.HillFiniteAbelianPhase
import NLS.MKdV.MiuraDirichletBranchCompatibility
import NLS.MKdV.MiuraSpectralActions

/-! # Independent finite Abelian phases on the original real H¹ mKdV domain

The phase is constructed from the original Hill Dirichlet divisor and
normalized Abelian integrals. Its own open domain is exactly the original
nonzero physical-action locus. Other gaps may be closed. The infinite
correction sum and its action generators are not asserted here.
-/
noncomputable section
open Set Complex Filter Topology
open NLS.KdV NLS.ZakharovShabat
open scoped ComplexConjugate
namespace NLS.MKdV

theorem realSobolevMiuraHill_halfLength_zero_iff_action_zero (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (hn : 1 ≤ n) :
    hillRealGapHalfLength (realSobolevMiuraHillPotential a ha).val
      (realSobolevMiuraHillPotential a ha).property.1 (realSobolevMiuraHillPotential a ha).property.2 n = 0 ↔
        miuraMKdVAction a ha n = 0 := by
  have he : hillRealGapHalfLength (realSobolevMiuraHillPotential a ha).val
      (realSobolevMiuraHillPotential a ha).property.1 (realSobolevMiuraHillPotential a ha).property.2 n = 0 ↔
      miuraHillLabels a ha (2*n-1) = miuraHillLabels a ha (2*n) := by
    change (miuraHillLabels a ha (2*n)-miuraHillLabels a ha (2*n-1))/2 = 0 ↔ _
    constructor <;> intro h <;> linarith
  exact he.trans ((miuraNLSAction_zero_iff_hillGap_collapsed a ha n hn).symm.trans
    (miuraMKdVAction_nonnegative_and_zero_iff a ha n hn).2.2.symm)

def miuraFiniteAbelianPhase (a : ScalarDomain 2) (ha : ∀ j, a.val j = conj (a.val (-j)))
    (n : ℕ) (hn : 1 ≤ n) (F : Finset ℕ) : ℂ :=
  hillFiniteAbelianPhase (realSobolevMiuraHillPotential a ha) n hn F

theorem norm_miuraFiniteAbelianPhase (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (hn : 1 ≤ n)
    (hJ : miuraMKdVAction a ha n ≠ 0) (F : Finset ℕ) :
    ‖miuraFiniteAbelianPhase a ha n hn F‖ = 1 :=
  norm_hillFiniteAbelianPhase _ n hn
    (fun h => hJ ((realSobolevMiuraHill_halfLength_zero_iff_action_zero a ha n hn).mp h)) F

theorem miuraFiniteAbelianPhase_closed (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (hn : 1 ≤ n)
    (hJ : miuraMKdVAction a ha n = 0) (F : Finset ℕ) :
    miuraFiniteAbelianPhase a ha n hn F = 0 :=
  hillFiniteAbelianPhase_closed _ n hn
    ((realSobolevMiuraHill_halfLength_zero_iff_action_zero a ha n hn).mpr hJ) F

theorem exists_miuraFiniteAbelianPhase_analytic_extension_along_real_family
    (a : ScalarDomain 2) (ha : ∀ j, a.val j = conj (a.val (-j)))
    (n : ℕ) (hn : 1 ≤ n) (hJ : miuraMKdVAction a ha n ≠ 0) (F : Finset ℕ)
    {T : Type*} [TopologicalSpace T] (A : T → ScalarDomain 2) (hA : Continuous A)
    (hreal : ∀ t j, (A t).val j = conj ((A t).val (-j))) (t0 : T) (h0 : A t0 = a) :
    ∃ P : ScalarDomain 2 → ℂ, AnalyticAt ℂ P a ∧
      P a = miuraFiniteAbelianPhase a ha n hn F ∧
      ∀ᶠ t in 𝓝 t0, P (A t) = miuraFiniteAbelianPhase (A t) (hreal t) n hn F := by
  obtain ⟨B,hB,hB0,hmatch⟩ := exists_hillFiniteAbelianPhase_analytic_extension
    (realSobolevMiuraHillPotential a ha) n hn
    (fun h => hJ ((realSobolevMiuraHill_halfLength_zero_iff_action_zero a ha n hn).mp h)) F
  let P : ScalarDomain 2 → ℂ := fun b => B (sobolevMiuraHillPotential b)
  have hP : AnalyticAt ℂ P a := by
    rw [realSobolevMiuraHillPotential_toCoeff] at hB
    exact hB.comp (f := sobolevMiuraHillPotential) (analyticAt_sobolevMiuraHillPotential a)
  have hc := continuous_realSobolevMiuraHillPotential_family A hA hreal
  have he : realSobolevMiuraHillPotential (A t0) (hreal t0) = realSobolevMiuraHillPotential a ha := by
    apply Subtype.ext
    exact congrArg sobolevMiuraWeightedPotential h0
  have ht : Tendsto (fun t => realSobolevMiuraHillPotential (A t) (hreal t))
      (𝓝 t0) (𝓝 (realSobolevMiuraHillPotential (A t0) (hreal t0))) := hc.tendsto t0
  rw [he] at ht
  refine ⟨P,hP,?_,?_⟩
  · exact (congrArg B (realSobolevMiuraHillPotential_toCoeff a ha).symm).trans hB0
  · filter_upwards [ht.eventually hmatch] with t hp
    exact (congrArg B (realSobolevMiuraHillPotential_toCoeff (A t) (hreal t)).symm).trans hp

theorem exists_miuraFiniteAbelianPhase_original_H1_analytic_extension
    (a : ScalarDomain 2) (ha : ∀ j, a.val j = conj (a.val (-j)))
    (n : ℕ) (hn : 1 ≤ n) (hJ : miuraMKdVAction a ha n ≠ 0) (F : Finset ℕ) :
    ∃ P : ScalarDomain 2 → ℂ, AnalyticAt ℂ P a ∧
      P a = miuraFiniteAbelianPhase a ha n hn F ∧
      ∀ᶠ b : {b : ScalarDomain 2 // ∀ j, b.val j = conj (b.val (-j))} in 𝓝 ⟨a,ha⟩,
        P b.val = miuraFiniteAbelianPhase b.val b.property n hn F :=
  exists_miuraFiniteAbelianPhase_analytic_extension_along_real_family a ha n hn hJ F
    (fun b : {b : ScalarDomain 2 // ∀ j, b.val j = conj (b.val (-j))} => b.val)
    continuous_subtype_val (fun b => b.property) ⟨a,ha⟩ rfl

end NLS.MKdV
