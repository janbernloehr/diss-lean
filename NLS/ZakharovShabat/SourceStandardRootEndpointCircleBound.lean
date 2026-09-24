import NLS.ZakharovShabat.SourceCriticalRootRatioConnectorBound

/-!
# Standard-root lower bounds on small endpoint circles

On a small circle around either endpoint of an open periodic gap, the
distance to that endpoint is the circle radius, while the distance to
the opposite endpoint stays at least half the real gap length. The
selected standard-root norm is therefore bounded below by the square
root of their product.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A small circle around the right endpoint has a uniform
square-root lower bound for the selected root. -/
theorem sourceStandardRoot_rightEndpoint_circle_norm_lower_bound
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hρsmall : ρ ≤
      ((canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re -
        (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
          (periodOnePotential_mem ψ) n).re)/2)
    (z : ℂ) (hz : z ∉ sourcePeriodicSegment hp hp1 ψ n)
    (hzdist : ‖canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n-z‖ = ρ) :
    let a := (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re
    let b := (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re
    Real.sqrt (((b-a)/2)*ρ) ≤ ‖sourceStandardRoot hp hp1 ψ n z‖ := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let R := sourceStandardRoot hp hp1 ψ n z
  have hgapdist : r.re-l.re ≤ ‖l-r‖ := by
    calc
      r.re-l.re = |(l-r).re| := by
        rw [Complex.sub_re, abs_of_neg (sub_neg.mpr hopen)]
        ring
      _ ≤ ‖l-r‖ := Complex.abs_re_le_norm _
  have htri : ‖l-r‖ ≤ ‖l-z‖ + ‖r-z‖ := by
    calc
      ‖l-r‖ = ‖(l-z)-(r-z)‖ := by congr 1; ring
      _ ≤ ‖l-z‖ + ‖r-z‖ := norm_sub_le _ _
  have hlong : (r.re-l.re)/2 ≤ ‖l-z‖ := by
    change ρ ≤ (r.re-l.re)/2 at hρsmall
    change ‖r-z‖ = ρ at hzdist
    linarith
  have hsq : ‖R‖^2 = ‖l-z‖*‖r-z‖ :=
    sourceStandardRoot_norm_sq hp hp1 ψ n z hz
  have hprod : ((r.re-l.re)/2)*ρ ≤ ‖R‖^2 := by
    rw [hsq,hzdist]
    exact mul_le_mul_of_nonneg_right hlong hρ
  have hnonneg : 0 ≤ ((r.re-l.re)/2)*ρ := by
    apply mul_nonneg
    · linarith
    · exact hρ
  have hsqrt : (Real.sqrt (((r.re-l.re)/2)*ρ))^2 =
      ((r.re-l.re)/2)*ρ := Real.sq_sqrt hnonneg
  change Real.sqrt (((r.re-l.re)/2)*ρ) ≤ ‖R‖
  nlinarith [Real.sqrt_nonneg (((r.re-l.re)/2)*ρ), norm_nonneg R]


/-- The same lower bound holds on a small circle around the left
endpoint. -/
theorem sourceStandardRoot_leftEndpoint_circle_norm_lower_bound
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hρsmall : ρ ≤
      ((canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re -
        (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
          (periodOnePotential_mem ψ) n).re)/2)
    (z : ℂ) (hz : z ∉ sourcePeriodicSegment hp hp1 ψ n)
    (hzdist : ‖canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n-z‖ = ρ) :
    let a := (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re
    let b := (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re
    Real.sqrt (((b-a)/2)*ρ) ≤ ‖sourceStandardRoot hp hp1 ψ n z‖ := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let R := sourceStandardRoot hp hp1 ψ n z
  have hgapdist : r.re-l.re ≤ ‖l-r‖ := by
    calc
      r.re-l.re = |(l-r).re| := by
        rw [Complex.sub_re, abs_of_neg (sub_neg.mpr hopen)]
        ring
      _ ≤ ‖l-r‖ := Complex.abs_re_le_norm _
  have htri : ‖l-r‖ ≤ ‖l-z‖ + ‖r-z‖ := by
    calc
      ‖l-r‖ = ‖(l-z)-(r-z)‖ := by congr 1; ring
      _ ≤ ‖l-z‖ + ‖r-z‖ := norm_sub_le _ _
  have hlong : (r.re-l.re)/2 ≤ ‖r-z‖ := by
    change ρ ≤ (r.re-l.re)/2 at hρsmall
    change ‖l-z‖ = ρ at hzdist
    linarith
  have hsq : ‖R‖^2 = ‖l-z‖*‖r-z‖ :=
    sourceStandardRoot_norm_sq hp hp1 ψ n z hz
  have hprod : ((r.re-l.re)/2)*ρ ≤ ‖R‖^2 := by
    calc
      ((r.re-l.re)/2)*ρ = ρ*((r.re-l.re)/2) := by ring
      _ ≤ ρ*‖r-z‖ := mul_le_mul_of_nonneg_left hlong hρ
      _ = ‖R‖^2 := by rw [hsq,hzdist]
  have hnonneg : 0 ≤ ((r.re-l.re)/2)*ρ := by
    apply mul_nonneg
    · linarith
    · exact hρ
  have hsqrt : (Real.sqrt (((r.re-l.re)/2)*ρ))^2 =
      ((r.re-l.re)/2)*ρ := Real.sq_sqrt hnonneg
  change Real.sqrt (((r.re-l.re)/2)*ρ) ≤ ‖R‖
  nlinarith [Real.sqrt_nonneg (((r.re-l.re)/2)*ρ), norm_nonneg R]

end NLS.ZakharovShabat
