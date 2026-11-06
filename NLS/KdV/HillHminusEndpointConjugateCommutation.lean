import NLS.KdV.HillHminusEndpointCartesianMixed

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ComplexConjugate
namespace NLS.KdV

theorem exists_hillOriginal_cartesian_hminus_physical_germ
    (q : RealPeriodOneHillPotential) (n : ℕ+)
    (hgap : hillRealGapHalfLength q.val q.property.1 q.property.2 n ≠ 0) :
    ∃ Z : PeriodOneHminusOne → ℂ,
      AnalyticAt ℂ Z (hillOriginalHminusSource q.val) ∧
      ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
        Z (hillOriginalHminusSource p.val) = hillSpectralCartesian p.val p.property.1 p.property.2 n n.pos := by
  obtain ⟨ε,hε,Z,hZ,hZM⟩ :=
    exists_hillOriginal_cartesian_hminus_isospectral_physical_germs q n hgap
  obtain ⟨V,hV,hqV,hZV⟩ := hZM q (mem_ball_self hε) (fun _ => rfl)
  exact ⟨Z,hZ _ (mem_ball_self hε),
    Filter.Eventually.mono (hV.mem_nhds hqV) (fun p hp => hZV p hp)⟩

/-- The original Cartesian product identity fixes the entire H-minus-one
differential, including its physical factor two, for ANY analytic germs. -/
theorem hillOriginalCartesian_conjugate_product_fderiv
    (q : RealPeriodOneHillPotential) (n : ℕ+)
    (Z C J : PeriodOneHminusOne → ℂ)
    (hZ : AnalyticAt ℂ Z (hillOriginalHminusSource q.val))
    (hC : AnalyticAt ℂ C (hillOriginalHminusSource q.val))
    (hJ : AnalyticAt ℂ J (hillOriginalHminusSource q.val))
    (hZM : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      Z (hillOriginalHminusSource p.val) = hillSpectralCartesian p.val p.property.1 p.property.2 n n.pos)
    (hCM : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      C (hillOriginalHminusSource p.val) = conj (hillSpectralCartesian p.val p.property.1 p.property.2 n n.pos))
    (hJM : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      J (hillOriginalHminusSource p.val) = (hillRealGapIntegral p.val p.property.1 p.property.2 n 0 : ℂ)) :
    fderiv ℂ (fun a => Z a * C a) (hillOriginalHminusSource q.val) =
      (2:ℂ) • fderiv ℂ J (hillOriginalHminusSource q.val) := by
  have he := hillHminusPhysicalGerm_fderiv_eq_of_eventuallyEq q
    (fun a => Z a * C a) (fun a => 2 * J a) (hZ.mul hC) (analyticAt_const.mul hJ) (by
      filter_upwards [hZM,hCM,hJM] with p hz hc hj
      rw [hz,hc,hj]
      exact hillSpectralCartesian_mul_conj p n)
  rw [he]
  exact (hJ.differentiableAt.hasFDerivAt.const_mul 2).fderiv

/-- The conjugates of the ORIGINAL Cartesian coordinates also commute
at all-periodic sources, in the same genuine H-minus-one bracket. -/
theorem hillOriginalConjugateCartesians_hminus_Gardner_endpoint_zero
    (q : RealPeriodOneHillPotential) (n m : ℕ+)
    (hgapn : hillRealGapHalfLength q.val q.property.1 q.property.2 n ≠ 0)
    (hgapm : hillRealGapHalfLength q.val q.property.1 q.property.2 m ≠ 0)
    (hterminal : ∀ k : ℕ, ∀ hk : 1 ≤ k,
      hillDirichletLogMultiplier q.val q.property.1 q.property.2 k hk = 0)
    (C D : PeriodOneHminusOne → ℂ)
    (hC : AnalyticAt ℂ C (hillOriginalHminusSource q.val))
    (hD : AnalyticAt ℂ D (hillOriginalHminusSource q.val))
    (hCM : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      C (hillOriginalHminusSource p.val) = conj (hillSpectralCartesian p.val p.property.1 p.property.2 n n.pos))
    (hDM : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      D (hillOriginalHminusSource p.val) = conj (hillSpectralCartesian p.val p.property.1 p.property.2 m m.pos)) :
    NLS.Poisson.hminusGardnerBracket C D (hillOriginalHminusSource q.val) = 0 := by
  by_cases hnm : (n:ℕ)=(m:ℕ)
  · have he : n=m := Subtype.ext hnm
    subst m
    have heq := hillHminusPhysicalGerm_fderiv_eq_of_eventuallyEq q C D hC hD (by
      filter_upwards [hCM,hDM] with p hc hd
      exact hc.trans hd.symm)
    unfold NLS.Poisson.hminusGardnerBracket NLS.Poisson.hminusScalarGradient
    rw [heq]
    exact NLS.Poisson.gardnerBivector_self _
  · obtain ⟨Z,hZ,hZM⟩ := exists_hillOriginal_cartesian_hminus_physical_germ q n hgapn
    obtain ⟨W,hW,hWM⟩ := exists_hillOriginal_cartesian_hminus_physical_germ q m hgapm
    obtain ⟨J,A,hJ,_,hJM,_,_,_⟩ := exists_hillOriginal_action_amplitude_hminus_differentials q n hgapn
    obtain ⟨K,B,hK,_,hKM,_,_,_⟩ := exists_hillOriginal_action_amplitude_hminus_differentials q m hgapm
    let a := hillOriginalHminusSource q.val
    have hZn : Z a ≠ 0 := by
      rw [hZM.self_of_nhds]
      exact hillSpectralCartesian_ne_zero_open q n hgapn
    have hWn : W a ≠ 0 := by
      rw [hWM.self_of_nhds]
      exact hillSpectralCartesian_ne_zero_open q m hgapm
    have hZC := hillOriginalCartesian_conjugate_product_fderiv q n Z C J hZ hC hJ hZM hCM hJM
    have hWD := hillOriginalCartesian_conjugate_product_fderiv q m W D K hW hD hK hWM hDM hKM
    have hKZ : NLS.Poisson.hminusGardnerBracket K Z a = 0 := by
      rw [NLS.Poisson.hminusGardnerBracket_antisymm,
        hillOriginalCartesian_action_hminus_Gardner_eq q n m Z K hZ hK hZM hKM,
        if_neg (Ne.symm hnm),mul_zero,zero_mul,neg_zero]
    have hKJ := hillOriginalActions_hminus_Gardner_commute q m n K J hK hJ hKM hJM
    have hKprod : NLS.Poisson.hminusGardnerBracket K (fun b => Z b * C b) a = 0 := by
      rw [NLS.Poisson.hminusGardnerBracket_of_fderiv_smul_right K _ J a 2 hZC,hKJ,mul_zero]
    have hKC : NLS.Poisson.hminusGardnerBracket K C a = 0 := by
      rw [NLS.Poisson.hminusGardnerBracket_mul_right K Z C a hZ.differentiableAt hC.differentiableAt,
        hKZ,mul_zero,add_zero] at hKprod
      exact (mul_eq_zero.mp hKprod).resolve_left hZn
    have hCK : NLS.Poisson.hminusGardnerBracket C K a = 0 := by
      rw [NLS.Poisson.hminusGardnerBracket_antisymm,hKC,neg_zero]
    have hCW : NLS.Poisson.hminusGardnerBracket C W a = 0 := by
      rw [NLS.Poisson.hminusGardnerBracket_antisymm,
        hillOriginalCartesian_conjugate_hminus_Gardner_endpoint_eq q m n hgapm hgapn hterminal
          W C hW hC hWM hCM,if_neg (Ne.symm hnm),mul_zero,neg_zero]
    have hCprod : NLS.Poisson.hminusGardnerBracket C (fun b => W b * D b) a = 0 := by
      rw [NLS.Poisson.hminusGardnerBracket_of_fderiv_smul_right C _ K a 2 hWD,hCK,mul_zero]
    rw [NLS.Poisson.hminusGardnerBracket_mul_right C W D a hW.differentiableAt hD.differentiableAt,
      hCW,mul_zero,add_zero] at hCprod
    exact (mul_eq_zero.mp hCprod).resolve_left hWn

end NLS.KdV
