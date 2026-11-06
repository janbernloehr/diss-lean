import NLS.MKdV.MiuraPositiveCartesianProperness

/-! # The actual native Cartesian inverse chart at the free profile

The free Jacobian is proved to be a bounded Fourier equivalence, and the
actual nonlinear map has an analytic inverse on full open complex L² and
positive-index native target neighborhoods. The physical map into this
natural target is globally proper. Gardner canonicity and a global inverse
at general profiles remain separate essential obligations.
-/
noncomputable section
open Set Complex NLS.MKdV
namespace NLS.Articles.MKdVNLSHierarchies

/-- The actual free Cartesian derivative is an equivalence of the full
original complex L² space and the full native positive/mean target. -/
theorem native_cartesian_free_jacobian_equivalence :
    ∃ e : Coeff 2 ≃L[ℂ] MiuraPositiveCartesianTarget,
      fderiv ℂ miuraPositiveCartesianMap 0 = e.toContinuousLinearMap :=
  ⟨miuraCartesianFreeEquiv,rfl⟩

/-- The original nonlinear map, with every positive coordinate and signed
mean, has an actual analytic inverse near zero in its full Banach norms. -/
theorem native_cartesian_zero_local_inverse :
    ∃ U : Set (Coeff 2), ∃ V : Set MiuraPositiveCartesianTarget,
      IsOpen U ∧ IsOpen V ∧ (0 : Coeff 2) ∈ U ∧ (0 : MiuraPositiveCartesianTarget) ∈ V ∧
      miuraPositiveCartesianMap '' U = V ∧ BijOn miuraPositiveCartesianMap U V ∧
      ∃ G : MiuraPositiveCartesianTarget → Coeff 2,
        AnalyticOnNhd ℂ miuraPositiveCartesianMap U ∧ AnalyticOnNhd ℂ G V ∧ G 0 = 0 ∧
        (∀ a ∈ U, G (miuraPositiveCartesianMap a) = a) ∧
        (∀ z ∈ V, G z ∈ U ∧ miuraPositiveCartesianMap (G z) = z) :=
  exists_miuraPositiveCartesian_localInverse_at_zero

/-- Natural positive-index Cartesian data and signed mean give a proper
map on the entire original physical real L² source, including closed gaps. -/
theorem native_positive_cartesian_real_L2_map_proper : IsProperMap miuraRealPositiveCartesianMap :=
  isProperMap_miuraRealPositiveCartesianMap

end NLS.Articles.MKdVNLSHierarchies
