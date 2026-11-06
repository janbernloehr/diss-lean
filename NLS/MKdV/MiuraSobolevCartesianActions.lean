import NLS.MKdV.MiuraSobolevCartesianSequence
import NLS.SequenceSpaces.WeightedHilbertProduct

/-! # Native weighted action recovery at every Sobolev order

The Cartesian half-order shift squares to precisely the physical action
weight. The full quadratic radius map is analytic between these native
Banach targets, and recovers every actual original mKdV action sequence.
-/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

abbrev MiuraSobolevCartesianTarget (s : ℕ) :=
  WeightedCoeff (miuraCartesianWeight s) 2 × WeightedCoeff (miuraCartesianWeight s) 2

theorem miuraCartesianWeight_squared (s : ℕ) (n : ℤ) :
    miuraCartesianWeight s n*miuraCartesianWeight s n = miuraSpectralActionWeight s n := by
  simp only [miuraCartesianWeight,miuraSpectralActionWeight,Weight.sobolev_apply]
  rw [← Real.rpow_add (by positivity)]
  congr 1
  push_cast
  ring

def miuraSobolevCartesianActions (s : ℕ) (z : MiuraSobolevCartesianTarget s) :
    WeightedCoeff (miuraSpectralActionWeight s) 1 :=
  (WeightedCoeff.weightIsometry (miuraSpectralActionWeight s) 1).symm
    (WeightedCoeff.weightIsometry ((miuraCartesianWeight s).product (miuraCartesianWeight s)) 1
      ((1/2 : ℂ) • (WeightedCoeff.hilbertProduct _ _ z.1 z.1+WeightedCoeff.hilbertProduct _ _ z.2 z.2)))

theorem miuraSobolevCartesianActions_apply (s : ℕ) (z : MiuraSobolevCartesianTarget s) (n : ℤ) :
    (miuraSobolevCartesianActions s z).val n = (1/2 : ℂ)*((z.1.val n)^2+(z.2.val n)^2) := by
  change (((miuraCartesianWeight s n*miuraCartesianWeight s n : ℝ) : ℂ)*
    ((1/2 : ℂ)*((WeightedCoeff.hilbertProduct _ _ z.1 z.1).val n+
      (WeightedCoeff.hilbertProduct _ _ z.2 z.2).val n)))/(miuraSpectralActionWeight s n : ℂ) = _
  rw [miuraCartesianWeight_squared,WeightedCoeff.hilbertProduct_apply,WeightedCoeff.hilbertProduct_apply,
    mul_div_cancel_left₀ _ ((miuraSpectralActionWeight s).complex_ne_zero n)]
  ring

theorem analyticOnNhd_miuraSobolevCartesianActions (s : ℕ) :
    AnalyticOnNhd ℂ (miuraSobolevCartesianActions s) univ := by
  intro z _
  have hx := ((WeightedCoeff.analyticOnNhd_hilbertProduct (miuraCartesianWeight s) (miuraCartesianWeight s))
    (z.1,z.1) (mem_univ _)).comp (f := fun v : MiuraSobolevCartesianTarget s => (v.1,v.1))
      (analyticAt_fst.prod analyticAt_fst)
  have hy := ((WeightedCoeff.analyticOnNhd_hilbertProduct (miuraCartesianWeight s) (miuraCartesianWeight s))
    (z.2,z.2) (mem_univ _)).comp (f := fun v : MiuraSobolevCartesianTarget s => (v.2,v.2))
      (analyticAt_snd.prod analyticAt_snd)
  have hc : AnalyticAt ℂ (fun _ : MiuraSobolevCartesianTarget s => (1/2 : ℂ)) z := analyticAt_const
  have hpoly : AnalyticAt ℂ (fun v : MiuraSobolevCartesianTarget s => (1/2 : ℂ) •
      (WeightedCoeff.hilbertProduct _ _ v.1 v.1+WeightedCoeff.hilbertProduct _ _ v.2 v.2)) z := by
    simpa only [Function.comp_def,Pi.add_apply,Pi.smul_apply] using! hc.smul (hx.add hy)
  exact (((WeightedCoeff.weightIsometry (miuraSpectralActionWeight s) 1).symm.toContinuousLinearEquiv.analyticAt _).comp
    (((WeightedCoeff.weightIsometry ((miuraCartesianWeight s).product (miuraCartesianWeight s)) 1).toContinuousLinearEquiv.analyticAt _).comp hpoly))

theorem analyticAt_miuraSobolevCartesianSequence (s : ℕ) (a : ScalarSobolev s)
    (ha : ∀ j, a.val j = conj (a.val (-j))) : AnalyticAt ℂ (miuraSobolevCartesianSequence s) a := by
  obtain ⟨U,_,hreal,hA,_⟩ := exists_miuraSobolevCartesianSequence_domain s
  exact hA a (hreal ha)

/-- Every positive native coordinate is exactly the original selected
Cartesian pair, without altering its raw Fourier profile. -/
theorem miuraSobolevCartesianSequence_positive (s : ℕ) (a : ScalarSobolev s)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (hn : 1 ≤ n) :
    ((miuraSobolevCartesianSequence s a).1.val n,(miuraSobolevCartesianSequence s a).2.val n) =
      miuraL2CartesianCoordinates n (hierarchySobolevJetL2 s 0 (Nat.zero_le s) a) := by
  obtain ⟨U,_,hreal,_,hcoord⟩ := exists_miuraSobolevCartesianSequence_domain s
  have hnZ : (0 : ℤ) < n := by omega
  simpa only [miuraL2CartesianCoefficient,if_pos hnZ,Int.toNat_natCast] using hcoord a (hreal ha) n

/-- The complete actual native weighted action map is the quadratic
radius of the complete native Cartesian map at every integer order. -/
theorem miuraSobolevCartesianActions_sequence_eq (s : ℕ) (a : ScalarSobolev s)
    (ha : ∀ j, a.val j = conj (a.val (-j))) :
    miuraSobolevCartesianActions s (miuraSobolevCartesianSequence s a) = miuraSobolevActionSequence s a := by
  obtain ⟨U,_,hreal,_,hcoord⟩ := exists_miuraSobolevCartesianSequence_domain s
  obtain ⟨V,_,hrealV,_,hact⟩ := exists_miuraSobolevActionSequence_domain s
  have har : ∀ j, hierarchySobolevJetL2 s 0 (Nat.zero_le s) a j =
      conj (hierarchySobolevJetL2 s 0 (Nat.zero_le s) a (-j)) := by
    intro j
    simpa only [hierarchySobolevJetL2_apply,pow_zero,one_mul] using ha j
  apply Subtype.ext
  funext n
  have he := hcoord a (hreal ha) n
  have hx := congrArg Prod.fst he
  have hy := congrArg Prod.snd he
  change (miuraSobolevCartesianSequence s a).1.val n = (miuraL2CartesianCoefficient _ n).1 at hx
  change (miuraSobolevCartesianSequence s a).2.val n = (miuraL2CartesianCoefficient _ n).2 at hy
  rw [miuraSobolevCartesianActions_apply,hx,hy]
  by_cases hn : 0 < n
  · have hi : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn.le
    have hnat : 1 ≤ n.toNat := by omega
    rw [miuraL2CartesianCoefficient,if_pos hn,miuraL2CartesianCoordinates_radius _ har n.toNat hnat,
      hact a (hrealV ha) n hn]
    unfold miuraL2Action
    rw [hi,← miuraSobolevActionSource_eq_L2_diagonal]
    ring
  · rw [miuraL2CartesianCoefficient,if_neg hn,miuraSobolevActionSequence_nonpositive s a n hn]
    norm_num

/-- Every native weighted realization is the same original L² Cartesian
family coefficient by coefficient. -/
theorem miuraSobolevCartesianSequence_L2_coefficients (s : ℕ) (a : ScalarSobolev s)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℤ) :
    ((miuraSobolevCartesianSequence s a).1.val n,(miuraSobolevCartesianSequence s a).2.val n) =
      ((miuraL2CartesianSequence (hierarchySobolevJetL2 s 0 (Nat.zero_le s) a)).1.val n,
        (miuraL2CartesianSequence (hierarchySobolevJetL2 s 0 (Nat.zero_le s) a)).2.val n) := by
  have har : ∀ j, hierarchySobolevJetL2 s 0 (Nat.zero_le s) a j =
      conj (hierarchySobolevJetL2 s 0 (Nat.zero_le s) a (-j)) := by
    intro j
    simpa only [hierarchySobolevJetL2_apply,pow_zero,one_mul] using ha j
  obtain ⟨U,_,hreal,_,hcoord⟩ := exists_miuraSobolevCartesianSequence_domain s
  obtain ⟨V,_,hrealV,_,hcoordV⟩ := exists_miuraL2CartesianSequence_domain
  exact (hcoord a (hreal ha) n).trans (hcoordV _ (hrealV har) n).symm

/-- The full native maps take physical Sobolev profiles to real Cartesian
coordinate sequences, including all nonpositive encoding slots. -/
theorem miuraSobolevCartesianSequence_real (s : ℕ) (a : ScalarSobolev s)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℤ) :
    ((miuraSobolevCartesianSequence s a).1.val n).im = 0 ∧
      ((miuraSobolevCartesianSequence s a).2.val n).im = 0 := by
  have har : ∀ j, hierarchySobolevJetL2 s 0 (Nat.zero_le s) a j =
      conj (hierarchySobolevJetL2 s 0 (Nat.zero_le s) a (-j)) := by
    intro j
    simpa only [hierarchySobolevJetL2_apply,pow_zero,one_mul] using ha j
  obtain ⟨U,_,hreal,_,hcoord⟩ := exists_miuraSobolevCartesianSequence_domain s
  have he := hcoord a (hreal ha) n
  have hx := congrArg (fun z : ℂ × ℂ => z.1.im) he
  have hy := congrArg (fun z : ℂ × ℂ => z.2.im) he
  have hr : (miuraL2CartesianCoefficient (hierarchySobolevJetL2 s 0 (Nat.zero_le s) a) n).1.im = 0 ∧
      (miuraL2CartesianCoefficient (hierarchySobolevJetL2 s 0 (Nat.zero_le s) a) n).2.im = 0 := by
    by_cases hn : 0 < n
    · simp only [miuraL2CartesianCoefficient,if_pos hn]
      exact miuraL2CartesianCoordinates_real _ har n.toNat (by omega)
    · simp [miuraL2CartesianCoefficient,if_neg hn]
  exact ⟨hx.trans hr.1,hy.trans hr.2⟩

end NLS.MKdV
