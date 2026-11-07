import NLS.KdV.HillFilledMixedGardner

/-! The native discriminant Hamiltonian has an actual jointly
analytic filled Dirichlet velocity through all physical zero sheets.
Only the proved nonzero simple energy derivative is divided out. -/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.KdV

theorem analyticOnNhd_hillHminusDirichletEnergyDerivative (m : ℕ+) :
    AnalyticOnNhd ℂ (fun q => deriv (hillHminusDirichlet q) (hillHminusCanonicalDirichlet m q))
      hillHminusCanonicalDirichletDomain := by
  have ha : AnalyticOnNhd ℂ (fun q => hillHminusDirichletFilledQuotient m
      (hillHminusCanonicalDirichlet m q,q)) hillHminusCanonicalDirichletDomain := by
    intro q hq
    exact (analyticOnNhd_hillHminusDirichletFilledQuotient m
      (hillHminusCanonicalDirichlet m q,q) ⟨mem_univ _,hq⟩).comp
        (f := fun p : PeriodOneHminusOne => (hillHminusCanonicalDirichlet m p,p))
        ((analyticOnNhd_hillHminusCanonicalDirichlet m q hq).prod analyticAt_id)
  simpa only [hillHminusDirichletFilledQuotient_at_root] using ha

def hillHminusDiscriminantDirichletVelocity (m : ℕ+) (t : ℂ × PeriodOneHminusOne) : ℂ :=
  hillHminusDirichletFilledQuotient m t/
    (2*deriv (hillHminusDirichlet t.2) (hillHminusCanonicalDirichlet m t.2))

theorem analyticOnNhd_hillHminusDiscriminantDirichletVelocity (m : ℕ+) :
    AnalyticOnNhd ℂ (hillHminusDiscriminantDirichletVelocity m)
      (univ ×ˢ hillHminusCanonicalDirichletDomain) := by
  intro t ht
  exact (analyticOnNhd_hillHminusDirichletFilledQuotient m t ht).div
    (analyticAt_const.mul ((analyticOnNhd_hillHminusDirichletEnergyDerivative m t.2 ht.2).comp
      (f := Prod.snd) analyticAt_snd))
    (mul_ne_zero (by norm_num) (deriv_hillHminusCanonicalDirichlet_ne_zero m t.2 ht.2))

theorem hillHminus_Dirichlet_discriminant_velocity (m : ℕ+) (E : ℂ)
    (q : PeriodOneHminusOne) (hq : q ∈ hillHminusCanonicalDirichletDomain) :
    NLS.Poisson.hminusGardnerBracket (hillHminusCanonicalDirichlet m) (fun p => hillHminusDiscriminant p E) q =
      hillHminusDirichletSheet m q*hillHminusDiscriminantDirichletVelocity m (E,q) := by
  have hd := deriv_hillHminusCanonicalDirichlet_ne_zero m q hq
  have htwo : (2:ℂ) ≠ 0 := by norm_num
  have he := hillHminus_filled_discriminant_Dirichlet_Gardner m q hq E
  rw [NLS.Poisson.hminusGardnerBracket_antisymm (fun p => hillHminusDiscriminant p E)] at he
  apply mul_left_cancel₀ (mul_ne_zero htwo hd)
  dsimp only [hillHminusDiscriminantDirichletVelocity]
  field_simp [hd]
  linear_combination -he

end NLS.KdV
