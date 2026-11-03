import NLS.KdV.SingularDirichletChainTaylorEquivalence
import NLS.ComplexAnalysis.AnalyticScalarJetOrder
import NLS.ComplexAnalysis.AnalyticZeroCount

/-! # Full COMPLEX native Dirichlet algebraic multiplicity equals characteristic order

The exact native-chain/scalar-Taylor-kernel equivalence is compared at
eventually stable dimensions. An actual native resolvent point excludes
an identically zero characteristic. No realness, simple-root or distant-
energy assumption is used.
-/
noncomputable section
open Set Filter Topology
namespace NLS.KdV
open NLS.ComplexAnalysis

/-- Every original complex source has a genuinely entire scalar Dirichlet characteristic. -/
theorem analyticOnNhd_hillHminusDirichlet_energy (q : PeriodOneHminusOne) :
    AnalyticOnNhd ℂ (hillHminusDirichlet q) univ := by
  intro lambda _
  exact (analyticOnNhd_hillHminusDirichlet_joint (lambda,q) (mem_univ _)).comp
    (f := fun z : ℂ => (z,q)) (analyticAt_id.prod analyticAt_const)

/-- The actual nonempty native resolvent excludes infinite characteristic order
at EVERY complex energy, without any spectral labeling hypothesis. -/
theorem analyticOrderAt_hillHminusDirichlet_ne_top (q : PeriodOneHminusOne) (lambda : ℂ) :
    analyticOrderAt (hillHminusDirichlet q) lambda ≠ ⊤ := by
  obtain ⟨a,ha⟩ := singularDirichletResolventSet_nonempty (periodOneOriginal q)
  have hDa := (mem_singularDirichletResolventSet_source_iff q a).mp ha
  exact analyticOrderAt_ne_top_on_connected isPreconnected_univ
    (analyticOnNhd_hillHminusDirichlet_energy q) (mem_univ a) hDa (mem_univ lambda)

/-- The ENTIRE actual native algebraic multiplicity equals the ORIGINAL
normalized characteristic's natural analytic zero order, for EVERY complex
source and EVERY energy, including zero and the complete central region. -/
theorem singularDirichletAlgebraicMultiplicity_eq_analyticOrderNatAt
    (q : PeriodOneHminusOne) (lambda : ℂ) :
    singularDirichletAlgebraicMultiplicity (periodOneOriginal q) lambda =
      analyticOrderNatAt (hillHminusDirichlet q) lambda := by
  let f := fun t : ℂ => hillHminusDirichlet q (lambda+t)
  have hD := analyticOnNhd_hillHminusDirichlet_energy q lambda (mem_univ _)
  have hf : AnalyticAt ℂ f 0 := by
    have hD' : AnalyticAt ℂ (hillHminusDirichlet q) (lambda+(0:ℂ)) := by
      simpa only [add_zero] using hD
    exact hD'.comp (f := fun t : ℂ => lambda+t) (analyticAt_const.add analyticAt_id)
  obtain ⟨p,hp⟩ := hf
  have ho : analyticOrderAt f 0 = analyticOrderAt (hillHminusDirichlet q) lambda :=
    analyticOrderAt_const_add_zero hD
  have hfin : analyticOrderAt f 0 ≠ ⊤ := by
    rw [ho]
    exact analyticOrderAt_hillHminusDirichlet_ne_top q lambda
  have hm : analyticOrderAt f 0 = ((analyticOrderAt f 0).toNat:ℕ∞) :=
    (ENat.natCast_toNat hfin).symm
  have hscalar := eventually_finrank_scalarTaylorKernel_of_analyticOrder hp _ hm
  have hnative := eventually_finrank_singularDirichletChainSpace (periodOneOriginal q) lambda
  obtain ⟨N,hNscalar,hNnative⟩ := (hscalar.and hnative).exists
  have he := finrank_singularDirichletChain_eq_scalarTaylorKernel q lambda p hp N
  rw [hNnative,hNscalar] at he
  exact he.trans (congrArg ENat.toNat ho)

/-- Extended analytic order and actual operator algebraic multiplicity agree exactly. -/
theorem singularDirichletAlgebraicMultiplicity_eq_analyticOrderAt
    (q : PeriodOneHminusOne) (lambda : ℂ) :
    (singularDirichletAlgebraicMultiplicity (periodOneOriginal q) lambda : ℕ∞) =
      analyticOrderAt (hillHminusDirichlet q) lambda := by
  rw [singularDirichletAlgebraicMultiplicity_eq_analyticOrderNatAt, analyticOrderNatAt]
  exact ENat.natCast_toNat (analyticOrderAt_hillHminusDirichlet_ne_top q lambda)

/-- The full actual native algebraic root-space dimension is the original
characteristic order, including all complex multiple roots. -/
theorem finrank_singularDirichletRootSpaceTop_eq_analyticOrder
    (q : PeriodOneHminusOne) (lambda : ℂ) :
    Module.finrank ℂ (singularDirichletRootSpaceTop (periodOneOriginal q) lambda) =
      analyticOrderNatAt (hillHminusDirichlet q) lambda :=
  singularDirichletAlgebraicMultiplicity_eq_analyticOrderNatAt q lambda

/-- Every finite actual chain level has EXACTLY the truncated original
characteristic order as dimension. All Jordan lengths are included. -/
theorem finrank_singularDirichletChainSpace_eq_min_order
    (q : PeriodOneHminusOne) (lambda : ℂ) (N : ℕ) :
    Module.finrank ℂ (singularDirichletChainSpace (periodOneOriginal q) lambda N) =
      min N (analyticOrderNatAt (hillHminusDirichlet q) lambda) := by
  let f := fun t : ℂ => hillHminusDirichlet q (lambda+t)
  have hD := analyticOnNhd_hillHminusDirichlet_energy q lambda (mem_univ _)
  have hf : AnalyticAt ℂ f 0 := by
    have hD' : AnalyticAt ℂ (hillHminusDirichlet q) (lambda+(0:ℂ)) := by
      simpa only [add_zero] using hD
    exact hD'.comp (f := fun t : ℂ => lambda+t) (analyticAt_const.add analyticAt_id)
  obtain ⟨p,hp⟩ := hf
  have ho : analyticOrderAt f 0 = analyticOrderAt (hillHminusDirichlet q) lambda :=
    analyticOrderAt_const_add_zero hD
  have hm : analyticOrderAt f 0 = (analyticOrderNatAt (hillHminusDirichlet q) lambda : ℕ∞) := by
    rw [ho,analyticOrderNatAt]
    exact (ENat.natCast_toNat (analyticOrderAt_hillHminusDirichlet_ne_top q lambda)).symm
  rw [finrank_singularDirichletChain_eq_scalarTaylorKernel q lambda p hp N]
  exact finrank_scalarTaylorKernel_of_analyticOrder hp _ hm N

/-- The actual native root levels have dimension min(length, algebraic multiplicity). -/
theorem finrank_singularDirichletRootSpace_eq_min_multiplicity
    (q : PeriodOneHminusOne) (lambda : ℂ) (N : ℕ) :
    Module.finrank ℂ (singularDirichletRootSpace (periodOneOriginal q) lambda N) =
      min N (singularDirichletAlgebraicMultiplicity (periodOneOriginal q) lambda) := by
  rw [← finrank_singularDirichletChainSpace,
    finrank_singularDirichletChainSpace_eq_min_order,
    singularDirichletAlgebraicMultiplicity_eq_analyticOrderNatAt]

end NLS.KdV
