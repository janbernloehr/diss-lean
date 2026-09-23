import NLS.ZakharovShabat.SourcePeriodicQuadratic

/-!
# Analytic periodic power sums

The sum of the kth powers of two roots obeys a second-order recurrence
whose coefficients are their midpoint and squared gap. This proves the
all-powers analyticity assertion of Lemma 10.2(i), including root
collisions, from the analytic symmetric coordinates.
-/

noncomputable section
open Set Complex Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The kth two-root power sum as a polynomial expression in midpoint
and squared gap. -/
def symmetricPairPowerSum (t g : ℂ) : ℕ → ℂ
  | 0 => 2
  | 1 => 2*t
  | k+2 => 2*t*symmetricPairPowerSum t g (k+1) - (t^2-g/4)*symmetricPairPowerSum t g k

/-- The symmetric recurrence really equals the sum of root powers. -/
theorem symmetricPairPowerSum_eq (a b : ℂ) (k : ℕ) :
    symmetricPairPowerSum ((a+b)/2) ((a-b)^2) k = a^k+b^k := by
  induction k using Nat.twoStepInduction with
  | zero => norm_num [symmetricPairPowerSum]
  | one => simp [symmetricPairPowerSum]; ring
  | more k hk hk1 =>
      rw [symmetricPairPowerSum, hk, hk1]
      have hprod : ((a+b)/2)^2 - (a-b)^2/4 = a*b := by ring
      rw [hprod]
      simp only [pow_succ]
      ring

/-- The recurrence is analytic in any analytic midpoint and squared-gap
families. -/
theorem analyticAt_symmetricPairPowerSum
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    {t g : X → ℂ} {x : X}
    (ht : AnalyticAt ℂ t x) (hg : AnalyticAt ℂ g x) (k : ℕ) :
    AnalyticAt ℂ (fun y => symmetricPairPowerSum (t y) (g y) k) x := by
  induction k using Nat.twoStepInduction with
  | zero => simpa only [symmetricPairPowerSum] using (analyticAt_const : AnalyticAt ℂ (fun _ : X => (2 : ℂ)) x)
  | one =>
      change AnalyticAt ℂ (fun y : X => (2 : ℂ)*t y) x
      exact analyticAt_const.mul ht
  | more k hk hk1 =>
      change AnalyticAt ℂ (fun y : X =>
        2*t y*symmetricPairPowerSum (t y) (g y) (k+1) -
          (t y^2-g y/4)*symmetricPairPowerSum (t y) (g y) k) x
      exact ((analyticAt_const.mul ht).mul hk1).sub
        (((ht.pow 2).sub hg.div_const).mul hk)

/-- On one open connected almost-real source domain, all indexed periodic
endpoint power sums are analytic at every source parameter. -/
theorem exists_global_source_analytic_periodicPowerSums
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ IsConnected W ∧
      realTypeSourceLocus p ⊆ W ∧
      ∀ ψ ∈ W, ∀ (n : ℤ) (k : ℕ),
        AnalyticAt ℂ (fun χ : CoeffPair p =>
          (canonicalPeriodicLeft hp hp1 (periodOnePotential χ) (periodOnePotential_mem χ) n)^k +
            (canonicalPeriodicRight hp hp1 (periodOnePotential χ) (periodOnePotential_mem χ) n)^k) ψ := by
  obtain ⟨W, hWopen, hWconnected, hR, hA⟩ :=
    exists_global_source_analytic_midpoint_squaredGap hp hp1
  refine ⟨W, hWopen, hWconnected, hR, ?_⟩
  intro ψ hψ n k
  obtain ⟨hMid, hGap⟩ := hA ψ hψ n
  have hPoly := analyticAt_symmetricPairPowerSum hMid hGap k
  apply hPoly.congr
  filter_upwards with χ
  unfold canonicalPeriodicMidpoint canonicalPeriodicGap
  have hgap :
      (canonicalPeriodicRight hp hp1 (periodOnePotential χ) (periodOnePotential_mem χ) n -
        canonicalPeriodicLeft hp hp1 (periodOnePotential χ) (periodOnePotential_mem χ) n)^2 =
      (canonicalPeriodicLeft hp hp1 (periodOnePotential χ) (periodOnePotential_mem χ) n -
        canonicalPeriodicRight hp hp1 (periodOnePotential χ) (periodOnePotential_mem χ) n)^2 := by ring
  rw [hgap]
  exact symmetricPairPowerSum_eq _ _ k

end NLS.ZakharovShabat
