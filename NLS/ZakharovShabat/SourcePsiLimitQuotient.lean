import NLS.SequenceSpaces.DeletedCoordinateAtInfinity
import NLS.ZakharovShabat.SourceSingleRootQuotientAnalytic

/-!
# Fixed-row quotient as the deleted index escapes

The quotient attached to a fixed selected row depends continuously
on the full displacement sequence. Deleting a root coordinate at an
index with growing absolute value therefore does not change its
limit. This is one of the two factors in the scalar matrix-entry
limit in Lemma 12.10.
-/

noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- At a fixed spectral point outside the other standard-root gaps,
the single-root quotient is continuous in its root-displacement
sequence. -/
theorem continuousAt_sourceSingleRootQuotient_rootParameter
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (m : ℤ) (ψ : CoeffPair p)
    (hψ : IsRealType (CoeffPair.toMax p ψ))
    (z : ℂ) (hz : z ∈ sourceStandardRootOmittedDomain hp hp1 ψ m)
    (a : Coeff p) :
    ContinuousAt (fun b : Coeff p =>
      sourceSingleRootQuotientJointProduct hp hp1 m (z,(b,ψ))) a := by
  obtain ⟨W,_,_,hreal,hdata⟩ :=
    exists_global_source_analytic_singleRootQuotient hp hp1
  have ht : (z,(a,ψ)) ∈ sourceSingleRootQuotientJointDomain hp hp1 W m :=
    ⟨hreal hψ,hz⟩
  have hAna := (hdata m).2 (z,(a,ψ)) ht
  have hinc : ContinuousAt (fun b : Coeff p => (z,(b,ψ))) a := by fun_prop
  exact hAna.continuousAt.comp
    (f := fun b : Coeff p => (z,(b,ψ))) hinc

/-- At every fixed valid spectral point, the quotient computed from
the sequence with coordinate `n` deleted tends to the quotient of
the undeleted sequence as `|n|` grows. -/
theorem tendsto_sourceSingleRootQuotient_deleteCoordinate
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (m : ℤ) (ψ : CoeffPair p)
    (hψ : IsRealType (CoeffPair.toMax p ψ))
    (z : ℂ) (hz : z ∈ sourceStandardRootOmittedDomain hp hp1 ψ m)
    (a : Coeff p) :
    Tendsto (fun n : ℤ =>
      sourceSingleRootQuotientJointProduct hp hp1 m
        (z,(Coeff.deleteCoordinate n a,ψ)))
      (Filter.comap Int.natAbs Filter.atTop)
      (𝓝 (sourceSingleRootQuotientJointProduct hp hp1 m (z,(a,ψ)))) := by
  exact (continuousAt_sourceSingleRootQuotient_rootParameter
    hp hp1 m ψ hψ z hz a).tendsto.comp
      (Coeff.tendsto_deleteCoordinate_at_natAbs hp a)

end NLS.ZakharovShabat
