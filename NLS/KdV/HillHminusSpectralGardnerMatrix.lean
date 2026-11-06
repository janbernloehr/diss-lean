import NLS.KdV.HillHminusDirichletGardner

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
namespace NLS.KdV

/-- All actual labelled Dirichlet energies and logarithmic norming coordinates
have simultaneous families of H-minus-one analytic germs at every original
real source. Their genuine H-minus-one Gardner brackets have the full original
separation-variable matrix, including its exact minus-one-half mixed factor.
No open-gap or finite-gap hypothesis is imposed; each germ has its own
neighborhood, and no uniform common neighborhood is asserted. -/
theorem exists_hillHminus_physical_spectral_Gardner_matrix
    (q : RealPeriodOneHillPotential) :
    ∃ a k : ℕ+ → PeriodOneHminusOne → ℂ,
      (∀ n : ℕ+,
        AnalyticAt ℂ (a n) (hillOriginalHminusSource q.val) ∧
        AnalyticAt ℂ (k n) (hillOriginalHminusSource q.val) ∧
        (∀ᶠ r in 𝓝 (hillOriginalHminusSource q.val), hillHminusDirichlet r (a n r)=0) ∧
        ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
          a n (hillOriginalHminusSource p.val)=
            (hillDirichletEnergy p.val p.property.1 p.property.2 n n.property : ℂ) ∧
          k n (hillOriginalHminusSource p.val)=
            (hillDirichletLogMultiplier p.val p.property.1 p.property.2 n n.property : ℂ)) ∧
      ∀ n m : ℕ+,
        NLS.Poisson.hminusGardnerBracket (a n) (a m) (hillOriginalHminusSource q.val)=0 ∧
        NLS.Poisson.hminusGardnerBracket (k n) (k m) (hillOriginalHminusSource q.val)=0 ∧
        NLS.Poisson.hminusGardnerBracket (a n) (k m) (hillOriginalHminusSource q.val)=
          (if (n : ℕ)=(m : ℕ) then -(1/2 : ℂ) else 0) ∧
        NLS.Poisson.hminusGardnerBracket (k n) (a m) (hillOriginalHminusSource q.val)=
          (if (n : ℕ)=(m : ℕ) then (1/2 : ℂ) else 0) := by
  have H (n : ℕ+) : ∃ a k : PeriodOneHminusOne → ℂ,
      AnalyticAt ℂ a (hillOriginalHminusSource q.val) ∧
      AnalyticAt ℂ k (hillOriginalHminusSource q.val) ∧
      (∀ᶠ r in 𝓝 (hillOriginalHminusSource q.val), hillHminusDirichlet r (a r)=0) ∧
      ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
        a (hillOriginalHminusSource p.val)=
          (hillDirichletEnergy p.val p.property.1 p.property.2 n n.property : ℂ) ∧
        k (hillOriginalHminusSource p.val)=
          (hillDirichletLogMultiplier p.val p.property.1 p.property.2 n n.property : ℂ) := by
    obtain ⟨a,T,k,ha,hT,hk,ha0,hT0,hk0,hroot,hmatch⟩ :=
      exists_hillDirichlet_norming_hminus_analytic_extension q n n.property
    exact ⟨a,k,ha,hk,hroot.mono (fun _ hp => hp.1),hmatch.mono (fun _ hp => ⟨hp.1,hp.2.2⟩)⟩
  choose a k ha hk hr hp using H
  have ham (n : ℕ+) : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      a n (hillOriginalHminusSource p.val)=
        (hillDirichletEnergy p.val p.property.1 p.property.2 n n.property : ℂ) :=
    (hp n).mono (fun _ h => h.1)
  have hkm (n : ℕ+) : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      k n (hillOriginalHminusSource p.val)=
        (hillDirichletLogMultiplier p.val p.property.1 p.property.2 n n.property : ℂ) :=
    (hp n).mono (fun _ h => h.2)
  refine ⟨a,k,(fun n => ⟨ha n,hk n,hr n,hp n⟩),?_⟩
  intro n m
  refine ⟨hillDirichletEnergies_hminus_Gardner_commute q n m n.property m.property
    (a n) (a m) (ha n) (ha m) (ham n) (ham m),
    hillLogNormings_hminus_Gardner_commute q n m n.property m.property
      (k n) (k m) (hk n) (hk m) (hkm n) (hkm m),
    hillDirichletLogNorming_hminus_Gardner_eq q n m n.property m.property
      (a n) (k m) (ha n) (hk m) (ham n) (hkm m),?_⟩
  rw [NLS.Poisson.hminusGardnerBracket_antisymm,
    hillDirichletLogNorming_hminus_Gardner_eq q m n m.property n.property
      (a m) (k n) (ha m) (hk n) (ham m) (hkm n)]
  by_cases h : (n : ℕ)=(m : ℕ)
  · rw [if_pos h,if_pos h.symm]
    norm_num
  · rw [if_neg h,if_neg (Ne.symm h),neg_zero]

end NLS.KdV
