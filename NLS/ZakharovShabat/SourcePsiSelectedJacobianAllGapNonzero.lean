import NLS.ZakharovShabat.SourcePsiSelectedJacobianEntry
import NLS.ZakharovShabat.SourcePsiJacobianAllGapNonzero

/-!
# Selected psi Jacobian nonvanishing at any real gap

The selected sequence equation retains valid contours for all rows,
including its finite head. The all-gap scalar diagonal theorem can
therefore be applied to its bounded Fréchet derivative wherever the
remaining root-separation and regular-factor conditions hold.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- At any retained row of a locally selected sequence equation, the
diagonal entry of its bounded Jacobian is nonzero when the selected
root contour misses the deleted root, the regular factor is analytic,
and the other retained roots miss that row's spectral gap. This also
covers collapsed gaps and finite head rows. -/
theorem exists_local_sourcePsi_selectedJacobian_allGapNonzero
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (n : ℤ) (a₀ : DeletedCoeff p n) :
    ∃ U : Set (DeletedCoeff p n × CoeffPair p), IsOpen U ∧
      (a₀,φ) ∈ U ∧
      ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
        ∀ a : DeletedCoeff p n, ∀ ψ : CoeffPair p,
          (a,ψ) ∈ U →
          IsRealType (CoeffPair.toMax p ψ) →
          (∀ k : ℤ, (displacedRoots (a : Coeff p) k).im = 0) →
          ∀ m : ℤ, ∀ hmn : m ≠ n,
            (∀ z ∈ sphere (c m) (R m),
              z ≠ displacedRoots (a : Coeff p) n) →
            AnalyticOnNhd ℂ
              (fun z => (((n-m : ℤ) : ℂ) *
                sourcePsiGapRegularFactor hp hp1 n m (a : Coeff p) ψ z))
              (closedBall (c m) (R m)) →
            (∀ z ∈ standardRootGapSegment
              (sourceStandardRootMidpoint hp hp1 ψ m)
              (sourceStandardRootHalfGap hp hp1 ψ m),
              ∀ k : ℤ, k ≠ m →
                z ≠ displacedRoots (a : Coeff p) k) →
            ((sourcePsiSelectedRootJacobian hp hp1 n c R a ψ
              (Coeff.deletedSingleCLM n m hmn 1) :
                DeletedCoeff p n) : Coeff p) m ≠ 0 := by
  obtain ⟨U,hUopen,hbase,K,c,R,hcReal,hchoice,hgeom,_,C,hC,hcoord,
    hbound,hrealCoord,hdiff⟩ :=
    exists_local_sourcePsi_globalEquation_formula_analytic
      hp hp1 φ hφ n a₀
  refine ⟨U,hUopen,hbase,c,R,?_⟩
  intro a ψ hpair hreal hroots m hmn havoidn hreg hother
  let x : ℝ := (c m).re
  have hx : (x : ℂ) = c m := by
    apply Complex.ext
    · rfl
    · simpa [x] using (hcReal m).symm
  obtain ⟨hR,hseg,hdom,hcircle⟩ := hgeom (a,ψ) hpair m
  have hscalar := sourcePsi_diagonalJacobian_ne_zero_all_real_gaps
    hp hp1 ψ hreal n m hmn a hroots x (R m) hR
      (by simpa only [hx] using hseg)
      (by simpa only [hx] using hdom)
      (by simpa only [hx] using hcircle)
      (by simpa only [hx] using havoidn)
      (by simpa only [hx] using hreg) hother
  rw [sourcePsiSelectedRootJacobian_entry_eq_deletedCoordinate
    hp hp1 n c R U hUopen hcoord hdiff a ψ hpair m m hmn]
  simpa only [hx] using hscalar

end NLS.ZakharovShabat
