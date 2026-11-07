import NLS.KdV.SingularDirichletCharacteristicSufficiency
import NLS.KdV.SingularDirichletRootSpace

/-! # Geometric uniqueness on the full native Dirichlet domain

The original scalar Dirichlet IVP has one free initial quasi-derivative.
Its verified weak-state classification therefore forces every native
Dirichlet eigenspace to be a single line, at every complex source potential.
-/
noncomputable section
open Set Complex NLS.LinearVolterra
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.ZakharovShabat NLS.MKdV

/-- Simultaneous constant translation of potential and energy leaves the native
eigen-equation unchanged on every original zero-trace H1 vector. -/
theorem singularDirichlet_source_eigen_add_constant_iff
    (q : PeriodOneHminusOne) (lambda c : ℂ) (f : UnitDirichletH1) :
    singularDirichletOperator (periodOneOriginal (q+periodOneL2Inclusion (lp.single 2 0 c))) f =
      (lambda+c) • singularDirichletDomainInclusion f ↔
        singularDirichletOperator (periodOneOriginal q) f = lambda • singularDirichletDomainInclusion f := by
  rw [singularDirichletOperator_source_add_constant]
  change singularDirichletOperator (periodOneOriginal q) f+c • singularDirichletDomainInclusion f =
    (lambda+c) • singularDirichletDomainInclusion f ↔ _
  constructor
  · intro he
    have hh : singularDirichletOperator (periodOneOriginal q) f+c • singularDirichletDomainInclusion f =
        lambda • singularDirichletDomainInclusion f+c • singularDirichletDomainInclusion f :=
      he.trans (add_smul lambda c (singularDirichletDomainInclusion f))
    exact add_right_cancel hh
  · intro he
    rw [he]
    exact (add_smul lambda c (singularDirichletDomainInclusion f)).symm

/-- At EVERY complex original potential and energy, every native eigenvector
is a scalar multiple of any fixed nonzero native eigenvector. -/
theorem singularDirichlet_native_eigenvectors_proportional
    (q : PeriodOneHminusOne) (lambda : ℂ) (f g : UnitDirichletH1) (hf : f ≠ 0)
    (hef : singularDirichletOperator (periodOneOriginal q) f = lambda • singularDirichletDomainInclusion f)
    (heg : singularDirichletOperator (periodOneOriginal q) g = lambda • singularDirichletDomainInclusion g) :
    ∃ c : ℂ, g = c • f := by
  let C := hillHminusMiuraChartAt q
  have hi := C.image q (mem_hillHminusMiuraChartAt q)
  have hsf : singularDirichletOperator (periodOneOriginal (periodOneMiura (C.lift q))) f =
      (lambda+C.energyShift) • singularDirichletDomainInclusion f := by
    rw [hi]
    exact (singularDirichlet_source_eigen_add_constant_iff q lambda C.energyShift f).mpr hef
  have hsg : singularDirichletOperator (periodOneOriginal (periodOneMiura (C.lift q))) g =
      (lambda+C.energyShift) • singularDirichletDomainInclusion g := by
    rw [hi]
    exact (singularDirichlet_source_eigen_add_constant_iff q lambda C.energyShift g).mpr heg
  obtain ⟨wf, hwf, hpf⟩ := exists_quasiHill_state_of_native_Miura_eigen
    (C.lift q) (lambda+C.energyShift) f hsf
  obtain ⟨wg, hwg, hpg⟩ := exists_quasiHill_state_of_native_Miura_eigen
    (C.lift q) (lambda+C.energyShift) g hsg
  obtain ⟨cf, hcf, _⟩ := (isQuasiHillL2DirichletState_iff_scalar _ _ wf).mp hwf
  obtain ⟨cg, hcg, _⟩ := (isQuasiHillL2DirichletState_iff_scalar _ _ wg).mp hwg
  let S := quasiHillL2SolutionCurve (C.lift q) (lambda+C.energyShift) (0,1)
  have hvalf (t : Icc (0:ℝ) 1) : unitDirichletRepresentative f t.val = cf*(S t).1 := by
    rw [← hpf t, hcf]
    rfl
  have hvalg (t : Icc (0:ℝ) 1) : unitDirichletRepresentative g t.val = cg*(S t).1 := by
    rw [← hpg t, hcg]
    rfl
  have hcf0 : cf ≠ 0 := by
    intro hz
    apply hf
    apply unitDirichletRepresentative_injective_on_interval f 0
    intro x hx
    rw [hvalf ⟨x,hx⟩, hz, zero_mul]
    change (0:ℂ) = periodOneSobolevSynthesis (0 : ScalarDomain 2) (x : AddCircle (2:ℝ))
    rw [map_zero]
    rfl
  refine ⟨cg/cf, ?_⟩
  apply unitDirichletRepresentative_injective_on_interval g ((cg/cf) • f)
  intro x hx
  change unitDirichletRepresentative g x =
    periodOneSobolevSynthesis ((cg/cf) • f.val) (x : AddCircle (2:ℝ))
  rw [map_smul]
  change unitDirichletRepresentative g x = (cg/cf)*unitDirichletRepresentative f x
  rw [hvalg ⟨x,hx⟩, hvalf ⟨x,hx⟩, ← mul_assoc, div_mul_cancel₀ _ hcf0]

/-- The entire native pencil kernel is exactly the line of any nonzero
native eigenvector. This is geometric, not an algebraic-order assertion. -/
theorem singularDirichletPencil_ker_eq_span
    (q : PeriodOneHminusOne) (lambda : ℂ) (f : UnitDirichletH1) (hf : f ≠ 0)
    (he : singularDirichletOperator (periodOneOriginal q) f = lambda • singularDirichletDomainInclusion f) :
    LinearMap.ker (singularDirichletPencil (periodOneOriginal q) lambda).toLinearMap =
      Submodule.span ℂ {f} := by
  apply le_antisymm
  · intro g hg
    obtain ⟨c, rfl⟩ := singularDirichlet_native_eigenvectors_proportional q lambda f g hf he
      ((singularDirichletPencil_eq_zero_iff _ lambda g).mp hg)
    exact Submodule.smul_mem _ c (Submodule.subset_span (by simp))
  · apply Submodule.span_le.mpr
    intro g hg
    have hgf : g = f := by simpa only [Set.mem_singleton_iff] using hg
    rw [hgf]
    exact (singularDirichletPencil_eq_zero_iff _ lambda f).mpr he

/-- Off the independently normalized characteristic zero set, the entire
native domain eigenspace is trivial, and conversely. -/
theorem singularDirichletEigenspace_eq_bot_iff (q : PeriodOneHminusOne) (lambda : ℂ) :
    singularDirichletEigenspace (periodOneOriginal q) lambda = ⊥ ↔
      hillHminusDirichlet q lambda ≠ 0 := by
  constructor
  · intro hb hd
    obtain ⟨f, hf, he⟩ := (hillHminusDirichlet_eq_zero_iff_native_eigen q lambda).mp hd
    have hm : f ∈ singularDirichletEigenspace (periodOneOriginal q) lambda :=
      (singularDirichletPencil_eq_zero_iff _ lambda f).mpr he
    rw [hb] at hm
    exact hf hm
  · intro hd
    apply bot_unique
    intro f hf
    by_contra hn
    exact hd (hillHminusDirichlet_eq_zero_of_native_eigen q lambda f hn
      ((singularDirichletPencil_eq_zero_iff _ lambda f).mp hf))

/-- Every native Dirichlet domain eigenspace is finite dimensional, without
a realness hypothesis or an assumed resolvent. -/
theorem finiteDimensional_singularDirichletEigenspace (q : PeriodOneHminusOne) (lambda : ℂ) :
    FiniteDimensional ℂ (singularDirichletEigenspace (periodOneOriginal q) lambda) := by
  by_cases hd : hillHminusDirichlet q lambda = 0
  · obtain ⟨f, hf, he⟩ := (hillHminusDirichlet_eq_zero_iff_native_eigen q lambda).mp hd
    change FiniteDimensional ℂ (LinearMap.ker (singularDirichletPencil (periodOneOriginal q) lambda).toLinearMap)
    rw [singularDirichletPencil_ker_eq_span q lambda f hf he]
    infer_instance
  · rw [(singularDirichletEigenspace_eq_bot_iff q lambda).mpr hd]
    infer_instance

/-- Exact geometric multiplicity: one at every complex characteristic zero,
and zero elsewhere. This is distinct from analytic order and Jordan multiplicity. -/
theorem finrank_singularDirichletEigenspace (q : PeriodOneHminusOne) (lambda : ℂ) :
    Module.finrank ℂ (singularDirichletEigenspace (periodOneOriginal q) lambda) =
      if hillHminusDirichlet q lambda = 0 then 1 else 0 := by
  by_cases hd : hillHminusDirichlet q lambda = 0
  · rw [if_pos hd]
    obtain ⟨f, hf, he⟩ := (hillHminusDirichlet_eq_zero_iff_native_eigen q lambda).mp hd
    change Module.finrank ℂ (LinearMap.ker (singularDirichletPencil (periodOneOriginal q) lambda).toLinearMap) = 1
    rw [singularDirichletPencil_ker_eq_span q lambda f hf he]
    exact finrank_span_singleton hf
  · rw [if_neg hd, (singularDirichletEigenspace_eq_bot_iff q lambda).mpr hd]
    simp only [finrank_bot]

end NLS.KdV
