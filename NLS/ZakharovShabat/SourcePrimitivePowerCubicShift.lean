import NLS.ZakharovShabat.SourcePrimitivePowerAction

/-! # The cubic shift and primitive-power moments

Expanding `F_0 = F_n - i*pi*n` on a local isolating circle leaves only
the first and third moments, since the zeroth and second moments vanish.
-/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat.SourcePrimitivePowerAtlas
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
variable (A : SourcePrimitivePowerAtlas hp hp1 W)

/-- Recover the literal primitive-power integral from the atlas moment. -/
theorem local_power_integral (φ : realTypeSourceLocus p) (ψ : CoeffPair p)
    (hψ : ψ ∈ A.sourceBall φ) (n : ℤ) (m : ℕ) :
    (∮ z in C((A.localChart φ).center n,(A.localChart φ).contourRadius n),
      (sourceFullAbelianPrimitive hp hp1 W n (z,ψ))^m) = -(Real.pi:ℂ)*A.moment n m ψ := by
  rw [A.moment_eq_local n m φ hψ]
  dsimp only [localMoment,sourcePrimitivePowerCircle]
  have hπ : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

/-- Exact contribution of one isolating circle to the unshifted cubic integral. -/
theorem unshifted_cubic_circle (φ : realTypeSourceLocus p) (ψ : CoeffPair p)
    (hψ : ψ ∈ A.sourceBall φ) (n : ℤ) :
    (∮ z in C((A.localChart φ).center n,(A.localChart φ).contourRadius n),
      (sourceFullAbelianPrimitive hp hp1 W 0 (z,ψ))^3) =
        (Real.pi:ℂ)*(3*((Real.pi:ℂ)*n)^2*A.moment n 1 ψ-A.moment n 3 ψ) := by
  obtain ⟨D⟩ := (A.localChart φ).charts ψ hψ
  have hfamily := (A.localChart φ).family ψ hψ
  have hψU : ψ ∈ A.domain := mem_iUnion.mpr ⟨φ,hψ⟩
  let c := (A.localChart φ).center n
  let R := (A.localChart φ).contourRadius n
  let f (m : ℕ) (z : ℂ) := (sourceFullAbelianPrimitive hp hp1 W n (z,ψ))^m
  let a : ℂ := (Real.pi:ℂ)*n
  have hci (m : ℕ) : CircleIntegrable (f m) c R := by
    have ha : AnalyticOnNhd ℂ (f m) (sourceCanonicalRootDomain hp hp1 ψ) :=
      fun z hz => (sourceFullAbelianPrimitive_spectral_analytic D n z
        (sourceCanonicalRootDomain_subset_openGapComplement hp hp1 ψ hz)).pow m
    exact (ha.continuousOn.mono (hfamily.2 n).2.2.2).circleIntegrable (hfamily.2 n).1.le
  have he (z : ℂ) (hz : z ∈ sphere c R) :
      (sourceFullAbelianPrimitive hp hp1 W 0 (z,ψ))^3 =
        f 3 z-(3*I*a)*f 2 z-(3*a^2)*f 1 z+(I*a^3)*f 0 z := by
    dsimp only [f,a]
    rw [sourceFullAbelianPrimitive_index_shift D n z
      (sourceCanonicalRootDomain_subset_openGapComplement hp hp1 ψ ((hfamily.2 n).2.2.2 hz))]
    simp only [pow_one,pow_zero,mul_one]
    ring_nf
    simp only [I_sq,I_pow_three]
    ring
  have hci2 : CircleIntegrable (fun z => (3*I*a)*f 2 z) c R := (hci 2).const_mul (3*I*a)
  have hci1 : CircleIntegrable (fun z => (3*a^2)*f 1 z) c R := (hci 1).const_mul (3*a^2)
  have hci0 : CircleIntegrable (fun z => (I*a^3)*f 0 z) c R := (hci 0).const_mul (I*a^3)
  have hci32 : CircleIntegrable (fun z => f 3 z-(3*I*a)*f 2 z) c R := (hci 3).sub hci2
  have hci321 : CircleIntegrable (fun z => f 3 z-(3*I*a)*f 2 z-(3*a^2)*f 1 z) c R := hci32.sub hci1
  calc
    _ = ∮ z in C(c,R), f 3 z-(3*I*a)*f 2 z-(3*a^2)*f 1 z+(I*a^3)*f 0 z :=
      circleIntegral.integral_congr (hfamily.2 n).1.le he
    _ = (∮ z in C(c,R), f 3 z)-(3*I*a)*(∮ z in C(c,R), f 2 z)-
        (3*a^2)*(∮ z in C(c,R), f 1 z)+(I*a^3)*(∮ z in C(c,R), f 0 z) := by
      rw [circleIntegral.integral_add hci321 hci0,
        circleIntegral.integral_sub hci32 hci1,
        circleIntegral.integral_sub (hci 3) hci2]
      simp only [circleIntegral.integral_const_mul]
    _ = _ := by
      simp only [f,c,R,A.local_power_integral φ ψ hψ n]
      rw [A.moment_even ψ hψU n 1,A.moment_even ψ hψU n 0]
      dsimp only [a]
      ring

end NLS.ZakharovShabat.SourcePrimitivePowerAtlas
