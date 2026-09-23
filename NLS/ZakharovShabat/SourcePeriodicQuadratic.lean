import NLS.ZakharovShabat.SourceSymmetricContour

/-!
# The jointly analytic periodic pair factor

The product of the two canonical periodic endpoint factors is a polynomial
in the midpoint, squared gap, and spectral parameter. Hence it is jointly
analytic even where the individual endpoint labels collide.
-/

noncomputable section
open Set Complex Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The quadratic factor identity in Lemma 10.2(iii), with the actual
canonical periodic endpoints. -/
theorem sourcePeriodicPair_factorization
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ) (z : ℂ) :
    (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n - z) *
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n - z) =
        (canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n - z)^2 -
          (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)^2/4 := by
  unfold canonicalPeriodicMidpoint canonicalPeriodicGap
  ring

/-- On the connected almost-real source domain, every indexed periodic
quadratic factor is jointly analytic in the spectral parameter and source
coefficients. -/
theorem exists_global_source_analytic_periodicPair_factor
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ IsConnected W ∧
      realTypeSourceLocus p ⊆ W ∧
      ∀ (z : ℂ) (ψ : CoeffPair p), ψ ∈ W → ∀ n : ℤ,
        AnalyticAt ℂ (fun t : ℂ × CoeffPair p =>
          (canonicalPeriodicLeft hp hp1 (periodOnePotential t.2) (periodOnePotential_mem t.2) n - t.1) *
            (canonicalPeriodicRight hp hp1 (periodOnePotential t.2) (periodOnePotential_mem t.2) n - t.1))
          (z, ψ) := by
  obtain ⟨W, hWopen, hWconnected, hR, hA⟩ :=
    exists_global_source_analytic_midpoint_squaredGap hp hp1
  refine ⟨W, hWopen, hWconnected, hR, ?_⟩
  intro z ψ hψ n
  obtain ⟨hMid, hGap⟩ := hA ψ hψ n
  have hMidJoint : AnalyticAt ℂ (fun t : ℂ × CoeffPair p =>
      canonicalPeriodicMidpoint hp hp1 (periodOnePotential t.2) (periodOnePotential_mem t.2) n) (z,ψ) :=
    hMid.comp (analyticAt_snd (p := (z,ψ)))
  have hGapJoint : AnalyticAt ℂ (fun t : ℂ × CoeffPair p =>
      (canonicalPeriodicGap hp hp1 (periodOnePotential t.2) (periodOnePotential_mem t.2) n)^2) (z,ψ) :=
    hGap.comp (analyticAt_snd (p := (z,ψ)))
  have hPoly : AnalyticAt ℂ (fun t : ℂ × CoeffPair p =>
      (canonicalPeriodicMidpoint hp hp1 (periodOnePotential t.2) (periodOnePotential_mem t.2) n - t.1)^2 -
        (canonicalPeriodicGap hp hp1 (periodOnePotential t.2) (periodOnePotential_mem t.2) n)^2/4) (z,ψ) :=
    (hMidJoint.sub analyticAt_fst).pow 2 |>.sub hGapJoint.div_const
  exact hPoly.congr (Filter.Eventually.of_forall fun t =>
    (sourcePeriodicPair_factorization hp hp1 t.2 n t.1).symm)

end NLS.ZakharovShabat
