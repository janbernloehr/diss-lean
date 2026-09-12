import NLS.ZakharovShabat.DirichletIntervalL2
import NLS.ZakharovShabat.IntervalComponentFlip

/-!
# Signed interval `L²` isomorphisms

Both coefficient boundary base spaces are continuously linearly equivalent to
the original physical interval `L²` space. The forward maps realize the actual
signed reflection almost everywhere; their inverses are actual restriction to
`[0,1]`. Compatibility with classical domain inclusion identifies the two sides
of the original operator's domain/base diagram.
-/

noncomputable section
open MeasureTheory Set NLS.Fourier
namespace NLS.ZakharovShabat

/-- The full Neumann base-space equivalence, using two component sign changes. -/
def neumannIntervalL2Equiv : IntervalPairL2 ≃L[ℂ] neumannSubspace (p := 2) :=
  (intervalComponentFlip.toContinuousLinearEquiv.trans dirichletIntervalL2Equiv).trans
    dirichletToNeumann.toContinuousLinearEquiv

namespace BoundaryCondition

/-- The selected signed extension isomorphism on the original physical `L²` space. -/
def intervalL2Equiv : (b : BoundaryCondition) → IntervalPairL2 ≃L[ℂ] space (p := 2) b
  | .dirichlet => dirichletIntervalL2Equiv
  | .neumann => neumannIntervalL2Equiv

/-- Both signed extensions have the same exact norm factor. -/
theorem norm_intervalL2Equiv (b : BoundaryCondition) (u : IntervalPairL2) :
    ‖intervalL2Equiv b u‖ = (Real.sqrt 2 / 2) * ‖u‖ := by
  cases b
  · exact norm_dirichletIntervalL2Equiv u
  · change ‖dirichletToNeumann (dirichletIntervalL2Equiv (intervalComponentFlip u))‖ = _
    rw [dirichletToNeumann.norm_map, norm_dirichletIntervalL2Equiv, intervalComponentFlip.norm_map]

/-- Both inverse restriction maps have the reciprocal physical norm factor. -/
theorem norm_intervalL2Equiv_symm (b : BoundaryCondition) (a : space (p := 2) b) :
    ‖(intervalL2Equiv b).symm a‖ = Real.sqrt 2 * ‖a‖ := by
  cases b
  · exact norm_dirichletIntervalL2Equiv_symm a
  · change ‖intervalComponentFlip.symm (dirichletIntervalL2Equiv.symm (dirichletToNeumann.symm a))‖ = _
    rw [intervalComponentFlip.symm.norm_map, norm_dirichletIntervalL2Equiv_symm]
    exact congrArg (fun t : ℝ => Real.sqrt 2 * t) (dirichletToNeumann.symm.norm_map a)

/-- The coefficient isomorphism reconstructs the actual signed extension of the physical representative. -/
theorem physicalBase_intervalL2Equiv (b : BoundaryCondition) (u : IntervalPairL2) :
    physicalBase (intervalL2Equiv b u).val =ᵐ[volume.restrict (Ioc 0 2)]
      intervalExtension b (intervalL2Representative u) := by
  cases b
  · exact physicalBase_dirichletPotentialCoefficients _ (memLp_intervalL2Representative u)
  · have hD := physicalBase_dirichletPotentialCoefficients
      (intervalL2Representative (intervalComponentFlip u)) (memLp_intervalL2Representative _)
    have hE := intervalExtension_congr_ae .dirichlet (intervalL2Representative_componentFlip u)
    have hF := physicalBase_componentFlip (dirichletIntervalL2Equiv (intervalComponentFlip u)).val
    apply hF.trans
    apply ((hD.trans hE).fun_comp componentFlip).trans
    exact Filter.Eventually.of_forall (intervalExtension_neumann_componentFlip (intervalL2Representative u))

/-- Actual original functions have exactly their signed physical extension after Fourier synthesis. -/
theorem physicalBase_intervalL2Equiv_ofFunction (b : BoundaryCondition) (f : ℝ → ℂ × ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 1))) :
    physicalBase (intervalL2Equiv b (intervalL2OfFunction f hf)).val =ᵐ[volume.restrict (Ioc 0 2)]
      intervalExtension b f :=
  (physicalBase_intervalL2Equiv b _).trans (intervalExtension_congr_ae b (intervalL2Representative_ofFunction f hf))

/-- The first output sequence is the actual normalized Fourier integral of signed extension. -/
theorem intervalL2Equiv_ofFunction_fst (b : BoundaryCondition) (f : ℝ → ℂ × ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 1))) (n : ℤ) :
    (intervalL2Equiv b (intervalL2OfFunction f hf)).val.1 n =
      periodTwoCoefficient (fun x => (intervalExtension b f x).1) n := by
  have h := congrFun (fourierCoeffOn_congr_ae (by norm_num : (0 : ℝ) < 2)
    ((physicalBase_intervalL2Equiv_ofFunction b f hf).fun_comp Prod.fst)) n
  simpa only [Function.comp_def, physicalBase, ← periodTwoCoefficient_eq_fourierCoeffOn,
    periodTwoCoefficient_circlePullback, fourierCoeff_l2Synthesis] using h

/-- The second output sequence has the same physical normalization. -/
theorem intervalL2Equiv_ofFunction_snd (b : BoundaryCondition) (f : ℝ → ℂ × ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 1))) (n : ℤ) :
    (intervalL2Equiv b (intervalL2OfFunction f hf)).val.2 n =
      periodTwoCoefficient (fun x => (intervalExtension b f x).2) n := by
  have h := congrFun (fourierCoeffOn_congr_ae (by norm_num : (0 : ℝ) < 2)
    ((physicalBase_intervalL2Equiv_ofFunction b f hf).fun_comp Prod.snd)) n
  simpa only [Function.comp_def, physicalBase, ← periodTwoCoefficient_eq_fourierCoeffOn,
    periodTwoCoefficient_circlePullback, fourierCoeff_l2Synthesis] using h

/-- The inverse of signed extension is the actual physical restriction on the original interval. -/
theorem intervalL2Equiv_symm_restrict (b : BoundaryCondition) (a : space (p := 2) b) :
    intervalL2Representative ((intervalL2Equiv b).symm a) =ᵐ[volume.restrict (Ioc 0 1)] physicalBase a.val := by
  have h := physicalBase_intervalL2Equiv b ((intervalL2Equiv b).symm a)
  rw [(intervalL2Equiv b).apply_symm_apply] at h
  have hr := ae_restrict_of_ae_restrict_of_subset
    (Ioc_subset_Ioc_right (show (1 : ℝ) ≤ 2 by norm_num)) h
  filter_upwards [hr, ae_restrict_mem measurableSet_Ioc] with x hx hmem
  exact ((intervalExtension_left b _ x hmem.2).symm.trans hx.symm)

/-- The base-space isomorphism agrees with unweighted inclusion of every classical boundary vector. -/
theorem intervalL2Equiv_classicalRestriction (b : BoundaryCondition) (a : Domain 2) (ha : a ∈ domain b) :
    (intervalL2Equiv b (intervalL2OfFunction (classicalIntervalRestriction a)
      (memLp_classicalIntervalRestriction b a ha))).val = domainInclusion a := by
  apply physicalBase_injective
  have h := physicalBase_intervalL2Equiv_ofFunction b (classicalIntervalRestriction a)
    (memLp_classicalIntervalRestriction b a ha)
  filter_upwards [h, physicalBase_domainInclusion a] with x hx hy
  rw [intervalExtension_classicalIntervalRestriction b a ha x] at hx
  exact hx.trans hy.symm

/-- An original classical function has the same base coefficients as its weighted signed extension. -/
theorem intervalL2Equiv_classicalFunction (b : BoundaryCondition) (f : ℝ → ℂ × ℂ)
    (hf : HasClassicalIntervalDomain b f) (hL : MemLp f 2 (volume.restrict (Ioc 0 1))) :
    (intervalL2Equiv b (intervalL2OfFunction f hL)).val =
      domainInclusion (classicalIntervalExtension b f hf) := by
  let a := classicalIntervalExtension b f hf
  have ha := classicalIntervalExtension_mem b f hf
  have he : intervalL2OfFunction f hL = intervalL2OfFunction (classicalIntervalRestriction a)
      (memLp_classicalIntervalRestriction b a ha) := by
    apply (intervalL2OfFunction_eq_iff _ _ _ _).mpr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact (classicalIntervalExtension_restrict b f hf (Ioc_subset_Icc_self hx)).symm
  rw [he]
  exact intervalL2Equiv_classicalRestriction b a ha

/-- The inverse inclusion diagram recovers the original physical class of every weighted boundary vector. -/
theorem intervalL2Equiv_symm_inclusion (b : BoundaryCondition) (a : domain (p := 2) b) :
    (intervalL2Equiv b).symm (inclusion b a) = intervalL2OfFunction (classicalIntervalRestriction a.val)
      (memLp_classicalIntervalRestriction b a.val a.property) := by
  apply (intervalL2Equiv b).injective
  rw [(intervalL2Equiv b).apply_symm_apply]
  exact (Subtype.ext (intervalL2Equiv_classicalRestriction b a.val a.property)).symm

end BoundaryCondition
end NLS.ZakharovShabat
