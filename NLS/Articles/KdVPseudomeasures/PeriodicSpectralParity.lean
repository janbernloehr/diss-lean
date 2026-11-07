import NLS.Articles.KdVPseudomeasures.PeriodicFreeModeLowerBound
import NLS.KdV.SingularHillPhysicalParity
import NLS.Fourier.PeriodicDistributionParity

/-! The ENTIRE high physical source spectral range has the ORIGINAL mode
parity, for complex physically period-one potentials, including associated vectors. -/
noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue

/-- Physical period one gives vanishing original odd native potential coefficients. -/
theorem sourceComplexHminusOne_odd_vanish (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (hp : IsPeriodicDistribution 1 q.val.toTempered) :
    ∀ k : ℤ, k%2 ≠ 0 → (sourceComplexHminusOne r hr q).val (mode (-k))=0 := by
  have ho := (Distribution.toTempered_period_one_iff_odd q.val).mp hp
  intro k hk
  have he : k=2*(k/2)+1 := by omega
  rw [sourceComplexHminusOne_val,he]
  exact ho (k/2)

/-- ONE original endpoint norm-ball cutoff, above ANY supplied prior cutoff,
gives the exact parity-n identity on the ENTIRE actual source-circle spectral
range. Every associated-vector direction and coincident root is included. -/
theorem exists_uniform_sourcePeriodicRange_parity (r : ℝ) (hr : AdmissiblePredualOrder r)
    (R : ℝ) (Nmin : ℕ) :
    ∃ N : ℕ, 2 ≤ N ∧ Nmin ≤ N ∧ ∀ q : FourierLebesgueSpace (2:ℝ) (-r) ⊤, ‖q‖ ≤ R →
      IsPeriodicDistribution 1 q.val.toTempered → ∀ n : ℕ+, N ≤ (n:ℕ) → ∀ F : CircleL2,
        F ∈ (singularHillL2RieszProjection (sourceComplexHminusOne r hr q) (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)).range →
        circleL2ParityProjection (n:ℤ) F=F := by
  obtain ⟨NF,hNF,hmin,hlower⟩ := exists_uniform_sourcePeriodicRange_freeMode_lower r hr R Nmin
  obtain ⟨NC,_,hcircles⟩ := exists_uniform_sourcePeriodicCircle_rank_two r hr R
  refine ⟨max NF NC,hNF.trans (le_max_left _ _),hmin.trans (le_max_left _ _),?_⟩
  intro q hq hp n hn F hF
  have hc := (hcircles q hq n ((le_max_right _ _).trans hn)).1
  let P := singularHillL2RieszProjection (sourceComplexHminusOne r hr q) (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)
  let T := circleL2ParityProjection (n:ℤ)
  have hfixed : P F=F := by
    obtain ⟨X,hX⟩ := hF
    rw [← hX]
    exact congrArg (fun S : CircleL2 →L[ℂ] CircleL2 => S X)
      (isIdempotentElem_singularHillL2RieszProjection _ _ _ (by exact_mod_cast n.property) hc)
  have hcomm (Y : CircleL2) : P (T Y)=T (P Y) :=
    (singularHillL2RieszProjection_parity _ (sourceComplexHminusOne_odd_vanish r hr q hp) _ _
      (by positivity) hc (n:ℤ) Y).symm
  let G := F-T F
  have hGfixed : P G=G := by
    change P (F-T F)=F-T F
    rw [map_sub,hfixed,hcomm,hfixed]
  have hGmem : G ∈ P.range := ⟨G,hGfixed⟩
  have hGfree : hillFreeL2ModeProjection (n:ℕ) G=0 := by
    change hillFreeL2ModeProjection (n:ℕ) (F-circleL2ParityProjection (n:ℤ) F)=0
    rw [map_sub,hillFreeL2ModeProjection_parity,sub_self]
  have hlow := hlower q hq n ((le_max_left _ _).trans hn) G hGmem
  rw [hGfree,norm_zero] at hlow
  have hGzero : G=0 := norm_eq_zero.mp (le_antisymm (by linarith) (norm_nonneg G))
  exact (sub_eq_zero.mp hGzero).symm

end NLS.Articles.KdVPseudomeasures
