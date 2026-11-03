import NLS.KdV.HminusOneCanonicalDirichlet

/-! # The analytic Dirichlet coordinates exhaust the full complex spectrum

Full signed auxiliary reflection continues from the real form on each
actual Miura ball. Its zero coordinate is exactly zero. The scalar shift
is excluded from the Dirichlet spectrum on the whole ball, so squaring
the positive auxiliary indices loses no scalar zero, including centrally.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ZakharovShabat NLS.ComplexAnalysis
namespace NLS.KdV
namespace HillHminusDirichletBall

theorem auxiliary_neg (B : HillHminusDirichletBall) (n : ℤ)
    (q : PeriodOneHminusOne) (hq : q ∈ B.source) :
    hillMiuraDiracDirichlet (B.miuraBall.actionBall.lift q) (-n) =
      -hillMiuraDiracDirichlet (B.miuraBall.actionBall.lift q) n := by
  have he := analytic_eqOn_of_real_periodOneHminus B.source B.source_open
    (convex_ball B.miuraBall.actionBall.center B.miuraBall.actionBall.radius).isPreconnected
    ⟨B.miuraBall.actionBall.center,mem_ball_self B.miuraBall.actionBall.radius_pos,B.miuraBall.actionBall.center_real⟩
    (fun a => hillMiuraDiracDirichlet (B.miuraBall.actionBall.lift a) (-n))
    (fun a => -hillMiuraDiracDirichlet (B.miuraBall.actionBall.lift a) n)
    (B.auxiliary_analytic (-n)) (fun a ha => (B.auxiliary_analytic n a ha).neg) (by
      intro a ha har
      exact hillMiuraDiracDirichlet_neg
        ⟨B.miuraBall.actionBall.lift a,B.miuraBall.actionBall.lift_real a ha har⟩ n)
  exact he hq

theorem auxiliary_zero (B : HillHminusDirichletBall) (q : PeriodOneHminusOne) (hq : q ∈ B.source) :
    hillMiuraDiracDirichlet (B.miuraBall.actionBall.lift q) 0 = 0 := by
  have he := B.auxiliary_neg 0 q hq
  simp only [neg_zero] at he
  linear_combination (1/2 : ℂ)*he

theorem energy_exhaustive (B : HillHminusDirichletBall) (q : PeriodOneHminusOne)
    (hq : q ∈ B.source) (energy : ℂ) :
    hillHminusDirichlet q energy = 0 ↔ ∃ n : ℕ+, energy = B.energy n q := by
  constructor
  · intro henergy
    let u := B.miuraBall.actionBall.lift q
    let c : ℂ := B.miuraBall.actionBall.shift
    have hshift : energy+c ≠ 0 := by
      intro hz
      have he : energy = -c := by linear_combination hz
      apply B.excluded_shift q hq
      rw [← he]
      exact henergy
    let z := Complex.sqrt (energy+c)
    have hsq : z^2 = energy+c := complex_sqrt_sq _
    have hz : z ≠ 0 := by
      intro he
      apply hshift
      rw [← hsq,he]
      norm_num
    have hs := (hillHminusDirichlet_eq_zero_iff_auxiliarySpectrum q u c energy z
      (B.miuraBall.actionBall.image q hq) hsq hz).mp henergy
    obtain ⟨k,hk⟩ := (canonicalAuxiliaryPeriodOneRoots_exhaustive (by simp) (by norm_num)
      .dirichlet (hillMiuraDiagonal u) z).mp hs
    change hillMiuraDiracDirichlet u k = z at hk
    have hk0 : k ≠ 0 := by
      intro he
      rw [he,B.auxiliary_zero q hq] at hk
      exact hz hk.symm
    have hnp : 0 < k.natAbs := by
      have h := Int.natAbs_ne_zero.mpr hk0
      omega
    let n : ℕ+ := ⟨k.natAbs,hnp⟩
    refine ⟨n,?_⟩
    have he : B.energy n q = energy := by
      change (hillMiuraDiracDirichlet u (n : ℕ))^2-c = energy
      rcases lt_or_gt_of_ne hk0 with hneg | hpos
      · have hi : ((n : ℕ) : ℤ) = -k := by
          change (k.natAbs : ℤ) = -k
          rw [Int.natCast_natAbs,abs_of_neg hneg]
        rw [hi,B.auxiliary_neg k q hq,hk,neg_sq,hsq]
        ring
      · have hi : ((n : ℕ) : ℤ) = k := by
          change (k.natAbs : ℤ) = k
          rw [Int.natCast_natAbs,abs_of_pos hpos]
        rw [hi,hk,hsq]
        ring
    exact he.symm
  · rintro ⟨n,rfl⟩
    exact B.energy_is_root n q hq

end HillHminusDirichletBall

theorem hillHminusCanonicalDirichlet_roots_iff (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusCanonicalDirichletDomain) (energy : ℂ) :
    hillHminusDirichlet q energy = 0 ↔ ∃ n : ℕ+, energy = hillHminusCanonicalDirichlet n q := by
  obtain ⟨B,hB⟩ := mem_iUnion.mp hq
  rw [B.energy_exhaustive q hB energy]
  apply exists_congr
  intro n
  rw [B.canonical_dirichlet_eq n q hB]

theorem hillHminusCanonicalDirichlet_spectrum_iff (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusCanonicalDirichletDomain) (energy : ℂ) :
    energy ∈ singularDirichletSpectrum (periodOneOriginal q) ↔ ∃ n : ℕ+, energy = hillHminusCanonicalDirichlet n q :=
  (mem_singularDirichletSpectrum_source_iff q energy).trans (hillHminusCanonicalDirichlet_roots_iff q hq energy)

end NLS.KdV
