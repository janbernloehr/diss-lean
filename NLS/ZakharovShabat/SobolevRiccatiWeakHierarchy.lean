import NLS.ZakharovShabat.SobolevRiccatiClassicalAgreement
import NLS.Fourier.SobolevDistributionDerivative

/-! # The last Riccati recurrence at the weak H⁻¹ boundary

For an Hˢ source, u_(s+2) has one derivative beyond the L² density.
The recurrence still makes sense: the differentiated term belongs to H⁻¹,
while every factor in the nonlinear terms has at least one Sobolev order.
-/
noncomputable section
open Set NLS.Fourier
open scoped ContDiff
namespace NLS.ZakharovShabat

abbrev WeakRiccatiSpace := WeightedCoeff (Weight.sobolev (-1)) 2

/-- Forget nonnegative regularity while preserving the original period-one coefficients. -/
def weakRiccatiInclusion (s : ℕ) : ScalarSobolev s →L[ℂ] WeakRiccatiSpace :=
  WeightedCoeff.sobolevInclusion (show (-1 : ℝ) ≤ (s : ℝ) by have := Nat.cast_nonneg (α := ℝ) s; linarith)

@[simp] theorem weakRiccatiInclusion_apply (s : ℕ) (a : ScalarSobolev s) (j : ℤ) :
    (weakRiccatiInclusion s a).val j = a.val j := WeightedCoeff.sobolevInclusion_apply _ _ _

/-- The weak derivative of an L² source has the original period-one multiplier 2*pi*i*j. -/
def weakRiccatiDerivative : ScalarSobolev 0 →L[ℂ] WeakRiccatiSpace :=
  (2 : ℂ) • ((WeightedCoeff.sobolevDerivative (-1)).comp
    (WeightedCoeff.sobolevInclusion (show (-1 : ℝ)+1 ≤ (0 : ℕ) by norm_num)))

@[simp] theorem weakRiccatiDerivative_apply (a : ScalarSobolev 0) (j : ℤ) :
    (weakRiccatiDerivative a).val j = 2*Complex.I*(Real.pi : ℂ)*j*a.val j := by
  change (2 : ℂ)*(Complex.I*(Real.pi : ℂ)*j*
    (WeightedCoeff.sobolevInclusion _ a).val j) = _
  rw [WeightedCoeff.sobolevInclusion_apply]
  ring

/-- At the weak boundary all nonlinear factors still have H¹ regularity. -/
def weakRiccatiNonlinear : (s : ℕ) → SobolevSource s → ScalarSobolev 0
  | 0, _ => 0
  | s+1, ab => ∑ ij ∈ (Finset.antidiagonal s).attach,
      hierarchySobolevTriple 0
        (hierarchySobolevInclusion (s+1) 1 (by omega) ab.1)
        (hierarchySobolevInclusion (s+1-ij.val.1) 1
          (by have he := Finset.mem_antidiagonal.mp ij.property; omega)
          (sobolevRiccatiDensity (s+1) ab ij.val.1
            (by have he := Finset.mem_antidiagonal.mp ij.property; omega)))
        (hierarchySobolevInclusion (s+1-ij.val.2) 1
          (by have he := Finset.mem_antidiagonal.mp ij.property; omega)
          (sobolevRiccatiDensity (s+1) ab ij.val.2
            (by have he := Finset.mem_antidiagonal.mp ij.property; omega)))

/-- The next density is defined by the actual derivative-plus-convolution recurrence. -/
def weakSobolevRiccatiDensity (s : ℕ) (ab : SobolevSource s) : WeakRiccatiSpace :=
  weakRiccatiDerivative (hierarchySobolevInclusion (s-s) 0 (by omega)
    (sobolevRiccatiDensity s ab s le_rfl)) + weakRiccatiInclusion 0 (weakRiccatiNonlinear s ab)

@[simp] theorem weakSobolevRiccatiDensity_apply (s : ℕ) (ab : SobolevSource s) (j : ℤ) :
    (weakSobolevRiccatiDensity s ab).val j =
      2*Complex.I*(Real.pi : ℂ)*j*(sobolevRiccatiDensity s ab s le_rfl).val j+
        (weakRiccatiNonlinear s ab).val j := by
  simp only [weakSobolevRiccatiDensity,WeightedCoeff.add_val,weakRiccatiDerivative_apply,
    hierarchySobolevInclusion_apply,weakRiccatiInclusion_apply]

/-- The H⁰ endpoint has no nonlinear remainder: u₂ is the weak derivative of -b. -/
theorem weakSobolevRiccatiDensity_zero_apply (ab : SobolevSource 0) (j : ℤ) :
    (weakSobolevRiccatiDensity 0 ab).val j = -(2*Complex.I*(Real.pi : ℂ)*j*ab.2.val j) := by
  simp [weakSobolevRiccatiDensity_apply,weakRiccatiNonlinear]

/-- The first nonlinear weak density is -b''+a*b² already for H¹ inputs. -/
theorem weakSobolevRiccatiDensity_one_apply (ab : SobolevSource 1) (j : ℤ) :
    (weakSobolevRiccatiDensity 1 ab).val j = -(2*Complex.I*(Real.pi : ℂ)*j)^2*ab.2.val j+
      ∑' l : ℤ, ab.1.val (j-l)*∑' m : ℤ, ab.2.val (l-m)*ab.2.val m := by
  have hattach : (Finset.antidiagonal 0).attach = {⟨(0,0),by simp⟩} := by
    ext ⟨⟨u,v⟩,huv⟩
    have he := Finset.mem_antidiagonal.mp huv
    have hu : u = 0 := by omega
    have hv : v = 0 := by omega
    subst u
    subst v
    exact iff_of_true (Finset.mem_attach _ _) (Finset.mem_singleton.mpr rfl)
  rw [weakSobolevRiccatiDensity_apply,weakRiccatiNonlinear,hattach,Finset.sum_singleton]
  simp only [hierarchySobolevTriple_apply,hierarchySobolevInclusion_apply,sobolevRiccatiDensity_zero,
    WeightedCoeff.neg_val,neg_mul_neg]
  have h1 := congrArg (fun a : ScalarSobolev (1-1) => a.val j) (sobolevRiccatiDensity_one 1 ab le_rfl)
  simp only [WeightedCoeff.neg_val,hierarchySobolevDerivative_apply] at h1
  rw [h1]
  ring

theorem analyticAt_weakRiccatiNonlinear (s : ℕ) (ab : SobolevSource s) :
    AnalyticAt ℂ (weakRiccatiNonlinear s) ab := by
  cases s with
  | zero => exact analyticAt_const
  | succ s =>
    unfold weakRiccatiNonlinear
    apply Finset.analyticAt_fun_sum
    intro ij _
    have he := Finset.mem_antidiagonal.mp ij.property
    apply analyticAt_hierarchySobolevTriple
    · exact ((hierarchySobolevInclusion (s+1) 1 (by omega)).analyticAt ab.1).comp analyticAt_fst
    · exact ((hierarchySobolevInclusion (s+1-ij.val.1) 1 (by omega)).analyticAt _).comp
        (analyticAt_sobolevRiccatiDensity (s+1) ij.val.1 (by omega) ab)
    · exact ((hierarchySobolevInclusion (s+1-ij.val.2) 1 (by omega)).analyticAt _).comp
        (analyticAt_sobolevRiccatiDensity (s+1) ij.val.2 (by omega) ab)

/-- The entire weak density depends analytically on the full complex Hˢ source. -/
theorem analyticAt_weakSobolevRiccatiDensity (s : ℕ) (ab : SobolevSource s) :
    AnalyticAt ℂ (weakSobolevRiccatiDensity s) ab := by
  apply AnalyticAt.add
  · exact (weakRiccatiDerivative.analyticAt _).comp
      (((hierarchySobolevInclusion (s-s) 0 (by omega)).analyticAt _).comp
        (analyticAt_sobolevRiccatiDensity s s le_rfl ab))
  · exact ((weakRiccatiInclusion 0).analyticAt _).comp (analyticAt_weakRiccatiNonlinear s ab)

private theorem sum_val {ι : Type*} (S : Finset ι) (f : ι → ScalarSobolev 0) (j : ℤ) :
    (∑ i ∈ S, f i).val j = ∑ i ∈ S, (f i).val j := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty,WeightedCoeff.zero_val]
  | @insert a S ha ih => simp only [Finset.sum_insert ha,WeightedCoeff.add_val,ih]

/-- The weak construction retains the actual smooth Riccati density, at the previously missing order. -/
theorem weakSobolevRiccatiDensity_eq_classical_coefficients
    (s : ℕ) (ab : SobolevSource s) (f g : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hpf : Function.Periodic f 1) (hpg : Function.Periodic g 1)
    (ha : ∀ j, ab.1.val j = periodOneCoefficient f j)
    (hb : ∀ j, ab.2.val j = periodOneCoefficient g j) (j : ℤ) :
    (weakSobolevRiccatiDensity s ab).val j = periodOneCoefficient (nlsRiccatiDensity f g (s+1)) j := by
  rw [weakSobolevRiccatiDensity_apply,
    sobolevRiccatiDensity_eq_classical_coefficients s ab f g hf hg hpf hpg ha hb s le_rfl]
  have hd (m : ℕ) := contDiff_nlsRiccatiDensity f g hf hg m
  have hp (m : ℕ) := periodic_nlsRiccatiDensity f g 1 hpf hpg m
  cases s with
  | zero =>
    simp only [Nat.zero_add,weakRiccatiNonlinear,WeightedCoeff.zero_val,add_zero,nlsRiccatiDensity_zero,
      nlsRiccatiDensity_one,periodOneCoefficient_neg]
    rw [periodOneCoefficient_deriv_of_smooth_periodic g hg hpg]
    ring
  | succ s =>
    let F : {ij : ℕ × ℕ // ij ∈ Finset.antidiagonal s} → ℝ → ℂ :=
      fun ij => f*(nlsRiccatiDensity f g ij.val.1*nlsRiccatiDensity f g ij.val.2)
    have hF (ij) : Continuous (F ij) := hf.continuous.mul ((hd ij.val.1).continuous.mul (hd ij.val.2).continuous)
    have hsum : Continuous (∑ ij ∈ (Finset.antidiagonal s).attach, F ij) := by
      change Continuous (fun x => (∑ ij ∈ (Finset.antidiagonal s).attach, F ij) x)
      simp only [Finset.sum_apply]
      exact continuous_finsetSum _ (fun ij _ => hF ij)
    rw [show s+1+1 = s+2 by omega,nlsRiccatiDensity]
    simp only [Finset.mul_sum]
    rw [periodOneCoefficient_add _ (∑ ij ∈ (Finset.antidiagonal s).attach, F ij)
      ((contDiff_infty_iff_deriv.mp (hd (s+1))).2.continuous) hsum,
      periodOneCoefficient_sum _ F (fun ij _ => hF ij),
      periodOneCoefficient_deriv_of_smooth_periodic _ (hd (s+1)) (hp (s+1))]
    congr 1
    simp only [weakRiccatiNonlinear,sum_val]
    apply Finset.sum_congr rfl
    intro ij _
    have hij := Finset.mem_antidiagonal.mp ij.property
    dsimp only [F]
    simp only [hierarchySobolevTriple_apply,hierarchySobolevInclusion_apply]
    rw [periodOneCoefficient_mul_of_smooth_periodic f
      (nlsRiccatiDensity f g ij.val.1*nlsRiccatiDensity f g ij.val.2)
      hf ((hd ij.val.1).mul (hd ij.val.2)) hpf ((hp ij.val.1).mul (hp ij.val.2))]
    apply tsum_congr
    intro l
    rw [ha]
    congr 1
    rw [periodOneCoefficient_mul_of_smooth_periodic _ _ (hd ij.val.1) (hd ij.val.2)
      (hp ij.val.1) (hp ij.val.2)]
    apply tsum_congr
    intro m
    rw [sobolevRiccatiDensity_eq_classical_coefficients _ ab f g hf hg hpf hpg ha hb ij.val.1 (by omega),
      sobolevRiccatiDensity_eq_classical_coefficients _ ab f g hf hg hpf hpg ha hb ij.val.2 (by omega)]

end NLS.ZakharovShabat
