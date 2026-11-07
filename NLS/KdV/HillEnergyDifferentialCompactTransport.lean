import NLS.KdV.HillCanonicalEnergyDifferentials
import NLS.ComplexAnalysis.CompactSliceLocalProperties
import NLS.ComplexAnalysis.PiecewiseOpenDiscPeriod

/-! One complex source ball identifies the canonical sheet and ALL
canonical differentials with a given actual local Miura presentation
on an ENTIRE compact energy set or actual piecewise contour. The source
radius precedes ALL numerator indices and every point of the contour. -/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.KdV

theorem exists_uniform_canonical_energy_compact_transport
    (B : HillHminusDirichletBall) (A : MiuraHillPsiFamily) (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (K : Set ℂ) (hK : IsCompact K)
    (hbase : ∀ E ∈ K, (E,q) ∈ B.energyDomain A) :
    ∃ r : ℝ, 0 < r ∧ ∀ y ∈ ball q r, ∀ E ∈ K,
      (E,y) ∈ hillHminusCanonicalEnergyRootDomain ∧ (E,y) ∈ B.energyDomain A ∧
      hillHminusCanonicalEnergyRoot (E,y) = B.energyRoot (E,y) ∧
      ∀ n : ℕ+, hillHminusCanonicalEnergyDifferential n (E,y) = B.energyDifferential A n (E,y) := by
  let P : ℂ × PeriodOneHminusOne → Prop := fun t =>
    t ∈ hillHminusCanonicalEnergyRootDomain ∧ t ∈ B.energyDomain A ∧
      hillHminusCanonicalEnergyRoot t = B.energyRoot t ∧
      ∀ n : ℕ+, hillHminusCanonicalEnergyDifferential n t = B.energyDifferential A n t
  have hlocal : ∀ E ∈ K, ∃ U, IsOpen U ∧ (E,q) ∈ U ∧ ∀ t ∈ U, P t := by
    intro E hE
    obtain ⟨C,hparent,hfamily,_,_,hC⟩ := exists_hillHminusEnergyRootBox_of_real_mem B A E q hr (hbase E hE)
    refine ⟨C.domain,C.domain_open,hC,?_⟩
    intro t ht
    have hdom : t ∈ hillHminusCanonicalEnergyRootDomain := mem_iUnion.mpr ⟨C,ht⟩
    have hlocaldom : t ∈ B.energyDomain A := by simpa only [hparent,hfamily] using C.subset ht
    have hroot : hillHminusCanonicalEnergyRoot t = B.energyRoot t := by
      rw [C.canonical_root_eq t ht]
      change C.parent.energyRoot t = B.energyRoot t
      rw [hparent]
    refine ⟨hdom,hlocaldom,hroot,?_⟩
    intro n
    rw [C.canonical_differential_eq n t ht,hparent,hfamily]
  obtain ⟨V,hV,hq,hprop⟩ := exists_uniform_local_property_near_compact_slice K hK q P hlocal
  obtain ⟨r,hrpos,hball⟩ := Metric.isOpen_iff.mp hV q hq
  exact ⟨r,hrpos,fun y hy E hE => hprop y (hball hy) E hE⟩

theorem exists_uniform_canonical_energy_loop_transport
    (B : HillHminusDirichletBall) (A : MiuraHillPsiFamily) (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (Γ : PiecewiseC1Loop)
    (hΓ : Γ.Inside {E | (E,q) ∈ B.energyDomain A}) :
    ∃ r : ℝ, 0 < r ∧ ∀ y ∈ ball q r,
      Γ.Inside {E | (E,y) ∈ hillHminusCanonicalEnergyRootDomain} ∧
      ∀ n : ℕ+, Γ.integral (fun E => hillHminusCanonicalEnergyDifferential n (E,y)) =
        Γ.integral (fun E => B.energyDifferential A n (E,y)) := by
  obtain ⟨r,hrpos,hcontrol⟩ := exists_uniform_canonical_energy_compact_transport B A q hr Γ.trace Γ.isCompact_trace
    ((Γ.inside_iff_trace_subset _).mp hΓ)
  have htrace : Γ.Inside Γ.trace := (Γ.inside_iff_trace_subset _).mpr (Subset.refl _)
  refine ⟨r,hrpos,?_⟩
  intro y hy
  exact ⟨(fun i t => (hcontrol y hy _ (htrace i t)).1),fun n => Γ.integral_congr htrace
    (fun E hE => (hcontrol y hy E hE).2.2.2 n)⟩

end NLS.KdV
