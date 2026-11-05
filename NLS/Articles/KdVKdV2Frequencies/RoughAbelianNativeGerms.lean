import NLS.Articles.KdVKdV2Frequencies.RoughAbelianNativeSquare
import NLS.Articles.KdVKdV2Frequencies.RoughAbelianScalarGerms
import NLS.KdV.HillPhysicalSheetRegularGermIdentity
import NLS.ComplexAnalysis.AnalyticZeroLinearBound

/-! # Fixing every native rough Abelian sign by the original physical germs -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies
open NLS.KdV

private theorem zero_parity : SpectralWeight.one.toCoeff
    (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0 := by simp
private theorem zero_real : IsRealHillPotential (SpectralWeight.one.toCoeff
    (0 : WeightedCoeff SpectralWeight.one.toWeight 2)) := by intro j; simp

private theorem exists_physical_abelian_sign (η : ℝ) (hη : 0<η)
    (G : PeriodOneHminusOne → Coeff 2)
    (hGa : AnalyticOnNhd ℂ G (ball (0 : PeriodOneHminusOne) η))
    (hGp : ∀ p : RealPeriodOneHillPotential,
      (hillPhysicalHminusEmbedding p).val∈ball (0 : PeriodOneHminusOne) η → ∀ n : ℕ+,
      hillDirichletSheetRoot (SpectralWeight.one.toCoeff p.val)
        (hillDirichletEnergy p.val p.property.1 p.property.2 n n.pos)≠0 →
      (G (hillPhysicalHminusEmbedding p).val (n : ℤ))^2=
        (hillDirichletAbelianCoordinate p.val p.property.1 p.property.2 n n.pos)^2/(1+(n : ℕ) : ℂ))
    (n : ℕ+) : ∃ e : ℂ, (e=1 ∨ e=-1) ∧
      ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 ⟨0,zero_parity,zero_real⟩,
        e*G (hillPhysicalHminusEmbedding p).val (n : ℤ)=
          hillDirichletAbelianCoordinate p.val p.property.1 p.property.2 n n.pos/
            (Real.sqrt (1+(n : ℝ)) : ℂ) := by
  obtain ⟨F,hFa,_hF0,hFp⟩ := exists_hillDirichletAbelianCoordinate_rough_scalar_germ n
  let f : Coeff 2 → ℂ := fun u => G (periodOneL2Inclusion u) (n : ℤ)
  let g : Coeff 2 → ℂ := fun u => F (periodOneL2Inclusion u)/(Real.sqrt (1+(n : ℝ)) : ℂ)
  have hG0a : AnalyticAt ℂ G (periodOneL2Inclusion 0) := by
    simpa only [map_zero] using hGa 0 (mem_ball_self hη)
  have hF0a : AnalyticAt ℂ F (periodOneL2Inclusion 0) := by simpa only [map_zero] using hFa
  have hf : AnalyticAt ℂ f 0 :=
    ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 (n : ℤ)).analyticAt _).comp
      (hG0a.comp (f := periodOneL2Inclusion) (periodOneL2Inclusion.analyticAt 0))
  have hg : AnalyticAt ℂ g 0 :=
    (hF0a.comp (f := periodOneL2Inclusion) (periodOneL2Inclusion.analyticAt 0)).div_const
  have ht : Tendsto (fun p : RealPeriodOneHillPotential => hillOriginalHminusSource p.val)
      (𝓝 (⟨0,zero_parity,zero_real⟩ : RealPeriodOneHillPotential)) (𝓝 (0 : PeriodOneHminusOne)) := by
    simpa only [Function.comp_def,map_zero] using
      (hillOriginalHminusSource.continuous.comp continuous_subtype_val).tendsto
        (⟨0,zero_parity,zero_real⟩ : RealPeriodOneHillPotential)
  have hsq : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 ⟨0,zero_parity,zero_real⟩,
      hillDirichletSheetRoot (SpectralWeight.one.toCoeff p.val)
        (hillDirichletEnergy p.val p.property.1 p.property.2 n n.pos)≠0 →
      (f (Fourier.paritySample 0 (SpectralWeight.one.toCoeff p.val)))^2=
        (g (Fourier.paritySample 0 (SpectralWeight.one.toCoeff p.val)))^2 := by
    filter_upwards [hFp,ht.eventually (ball_mem_nhds (0 : PeriodOneHminusOne) hη)] with p hFp hp
    intro hw
    have hsqrt : (Real.sqrt (1+(n : ℝ)) : ℂ)^2=(1+(n : ℕ) : ℂ) := by
      rw [← ofReal_pow,Real.sq_sqrt (by positivity),ofReal_add,ofReal_one,ofReal_natCast]
    change (G (hillPhysicalHminusEmbedding p).val (n : ℤ))^2=
      (F (hillPhysicalHminusEmbedding p).val/(Real.sqrt (1+(n : ℝ)) : ℂ))^2
    rw [hFp,div_pow,hsqrt]
    exact hGp p hp n hw
  have hsign := eventuallyEq_or_neg_native_of_physical_sheet_regular_sq zero_parity zero_real n f g hf hg hsq
  let S : RealPeriodOneHillPotential → Coeff 2 := fun p => Fourier.paritySample 0 (SpectralWeight.one.toCoeff p.val)
  have hSt : Tendsto S (𝓝 (⟨0,zero_parity,zero_real⟩ : RealPeriodOneHillPotential)) (𝓝 (0 : Coeff 2)) := by
    simpa only [S,Function.comp_def,map_zero] using
      ((Fourier.paritySample (p := 2) 0).continuous.comp
        (SpectralWeight.one.toCoeff.continuous.comp continuous_subtype_val)).tendsto
          (⟨0,zero_parity,zero_real⟩ : RealPeriodOneHillPotential)
  rcases hsign with he | he
  · refine ⟨1,Or.inl rfl,?_⟩
    filter_upwards [hSt.eventually he,hFp] with p hp hFp
    change G (hillPhysicalHminusEmbedding p).val (n : ℤ)=
      F (hillPhysicalHminusEmbedding p).val/(Real.sqrt (1+(n : ℝ)) : ℂ) at hp
    simpa only [one_mul,hFp] using hp
  · refine ⟨-1,Or.inr rfl,?_⟩
    filter_upwards [hSt.eventually he,hFp] with p hp hFp
    change G (hillPhysicalHminusEmbedding p).val (n : ℤ)=
      -(F (hillPhysicalHminusEmbedding p).val/(Real.sqrt (1+(n : ℝ)) : ℂ)) at hp
    rw [hp,hFp,neg_one_mul,neg_neg]

theorem exists_hillHminus_native_abelian_physical_germs :
    ∃ η C : ℝ, ∃ Z : PeriodOneHminusOne → Coeff 2,
      0 < η ∧ 0 < C ∧ AnalyticOnNhd ℂ Z (ball (0 : PeriodOneHminusOne) η) ∧ Z 0=0 ∧
      (∀ q∈ball (0 : PeriodOneHminusOne) η, ‖Z q‖ ≤ C*‖q‖ ∧ ∀ j : ℤ, j≤0 → Z q j=0) ∧
      ∀ n : ℕ+, ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 ⟨0,zero_parity,zero_real⟩,
        Z (hillPhysicalHminusEmbedding p).val (n : ℤ)=
          hillDirichletAbelianCoordinate p.val p.property.1 p.property.2 n n.pos/
            (Real.sqrt (1+(n : ℝ)) : ℂ) := by
  classical
  obtain ⟨r,_CG,G,hr,_hCG,hGa,hGb,hGp⟩ := exists_hillHminus_native_abelian_squared_packet
  choose e he hep using exists_physical_abelian_sign r hr G hGa hGp
  let a : ℤ → ℂ := Coeff.positiveFamilyCoordinates e
  have hb (j : ℤ) : ‖a j‖≤1 := by
    by_cases hj : 0<j
    · simp only [a,Coeff.positiveFamilyCoordinates,dif_pos hj]
      rcases he (Coeff.positivePoleIndex j hj) with h | h <;> rw [h] <;> norm_num
    · simp only [a,Coeff.positiveFamilyCoordinates,dif_neg hj,norm_zero]
      norm_num
  let m : Coeff ⊤ := ⟨a,memℓp_infty ⟨1,by rintro _ ⟨j,rfl⟩; exact hb j⟩⟩
  let L : Coeff 2 →L[ℂ] Coeff 2 := Coeff.multiplierCLM m
  let Z : PeriodOneHminusOne → Coeff 2 := fun q => L (G q)
  have hZa : AnalyticOnNhd ℂ Z (ball (0 : PeriodOneHminusOne) r) :=
    fun q hq => (L.analyticAt _).comp (hGa q hq)
  have hZp (n : ℕ+) : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 ⟨0,zero_parity,zero_real⟩,
      Z (hillPhysicalHminusEmbedding p).val (n : ℤ)=
        hillDirichletAbelianCoordinate p.val p.property.1 p.property.2 n n.pos/
          (Real.sqrt (1+(n : ℝ)) : ℂ) := by
    have hm : m (n : ℤ)=e n := Coeff.positiveFamilyCoordinates_nat e n
    filter_upwards [hep n] with p hp
    change m (n : ℤ)*G (hillPhysicalHminusEmbedding p).val (n : ℤ)=_
    rw [hm]
    exact hp
  have hZnonpos (q : PeriodOneHminusOne) (hq : q∈ball 0 r) (j : ℤ) (hj : j≤0) : Z q j=0 := by
    change m j*G q j=0
    rw [(hGb q hq).2 j hj,mul_zero]
  have hZ0 : Z 0=0 := by
    apply lp.ext
    funext j
    change Z 0 j=0
    by_cases hj : 0<j
    · let n : ℕ+ := ⟨j.toNat,by omega⟩
      have hn : (n : ℤ)=j := Int.toNat_of_nonneg hj.le
      have hh := (hZp n).self_of_nhds
      have hc := hillFreeGapHalfLength zero_parity zero_real (n : ℕ) n.pos
      simpa only [hillPhysicalHminusEmbedding,map_zero,hn,
        hillDirichletAbelianCoordinate_closed 0 zero_parity zero_real (n : ℕ) n.pos hc,zero_div] using hh
    · exact hZnonpos 0 (mem_ball_self hr) j (le_of_not_gt hj)
  obtain ⟨s,C,hs,hC,hsa,hlin⟩ := exists_analytic_zero_linear_bound Z (hZa 0 (mem_ball_self hr)) hZ0
  let η := min r s
  refine ⟨η,C,Z,lt_min hr hs,hC,hsa.mono (ball_subset_ball (min_le_right r s)),hZ0,?_,hZp⟩
  intro q hq
  exact ⟨hlin q (ball_subset_ball (min_le_right r s) hq),
    hZnonpos q (ball_subset_ball (min_le_left r s) hq)⟩

end NLS.Articles.KdVKdV2Frequencies
