import NLS.Articles.MKdVBelowL2.OrdinaryFourthClassicalUniqueness
import NLS.Articles.MKdVBelowL2.OrdinaryFourthScalarCoordinates

/-! # The actual ordinary smooth scalar solution map

The mass-restored native flow represents an ordinary physical mKdV solution
in every finite scalar exponent p>=2. Physical PDE uniqueness identifies any
classical smooth solution map with this actual trajectory and its calibrated
fixed Birkhoff coordinate evolution.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology Complex NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.MKdV
open scoped ContDiff ENNReal
namespace NLS.Articles.MKdVBelowL2
open NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual physical classical evolution, of the original unrenormalized equation
and unchanged original Fourier coefficients. -/
def IsClassicalOrdinaryPhysicalScalarTrajectory (u : PhysicalScalarRealInput p)
    (γ : ℝ → PhysicalScalarRealInput p) : Prop :=
  ∃ f : ℝ → ℂ, ContDiff ℝ ∞ f ∧ Function.Periodic f 1 ∧ (∀ x, (f x).im = 0) ∧
    (∀ n : ℤ, u.val.val (mode (-n)) = periodOneCoefficient f n) ∧
    ∃ w : ℝ → C(AddCircle (2:ℝ),ℂ),
      IsClassicalMKdVTrajectory (0:ℂ) w ∧
      (∀ x : ℝ, w 0 (x : AddCircle (2:ℝ)) = f x) ∧
      ∀ t : ℝ, ∀ n : ℤ, (γ t).val.val (mode (-n)) =
        periodOneCoefficient (fun x : ℝ => w t (x : AddCircle (2:ℝ))) n

/-- Uniqueness is inherited from the physical PDE and Fourier uniqueness. -/
theorem IsClassicalOrdinaryPhysicalScalarTrajectory.unique
    {u : PhysicalScalarRealInput p} {γ δ : ℝ → PhysicalScalarRealInput p}
    (hγ : IsClassicalOrdinaryPhysicalScalarTrajectory u γ)
    (hδ : IsClassicalOrdinaryPhysicalScalarTrajectory u δ) : γ = δ := by
  obtain ⟨f,hf,hpf,_,hcf,w,hw,hw0,hwc⟩ := hγ
  obtain ⟨g,hg,hpg,_,hcg,v,hv,hv0,hvc⟩ := hδ
  have hfg : f = g := eq_of_periodOneCoefficient_eq f g hf.continuous hg.continuous hpf hpg
    (fun n => (hcf n).symm.trans (hcg n))
  subst g
  have hinit : w 0 = v 0 := by
    apply ContinuousMap.ext
    intro x
    induction x using QuotientAddGroup.induction_on with
    | H x => exact (hw0 x).trans (hv0 x).symm
  have he : w = v := hw.eq_of_eq_at hv 0 hinit
  funext t
  apply Subtype.ext
  apply Subtype.ext
  apply Distribution.ext_coefficients
  intro n
  exact (hwc t n).trans ((congrArg (fun z : ℝ → C(AddCircle (2:ℝ),ℂ) =>
    periodOneCoefficient (fun x : ℝ => z t (x : AddCircle (2:ℝ))) n) he).trans (hvc t n).symm)

/-- Scalar smoothness of the original distribution gives smoothness of the
unchanged native physical field by actual Fourier uniqueness. -/
theorem contDiff_nativePhysical_of_isSmoothPhysicalScalarInput (h2p : 2 ≤ p) (a : FourthClassicalSource)
    (ha : (originalWeightedRealSource _ a).val.fst = (originalWeightedRealSource _ a).val.snd)
    (hs : IsSmoothPhysicalScalarInput (fourthClassicalScalarInput h2p a ha)) :
    ContDiff ℝ ∞ (fun x : ℝ => (nativeSobolevPhysicalJetCLM 4 0 (by omega) a).1 (x : AddCircle (2:ℝ))) := by
  obtain ⟨f,hf,hp,_,hcoeff⟩ := hs
  have he : (fun x : ℝ => (nativeSobolevPhysicalJetCLM 4 0 (by omega) a).1 (x : AddCircle (2:ℝ))) = f := by
    apply eq_of_periodOneCoefficient_eq _ _
      (((nativeSobolevPhysicalJetCLM 4 0 (by omega) a).1).continuous.comp continuous_quotient_mk')
      hf.continuous (hierarchySobolevJetContinuous_periodic 4 0 (by omega) _) hp
    intro n
    exact (periodOneCoefficient_nativeSobolevPhysicalJet_zero 4 (by omega) a n).1.trans
      ((fourthClassicalScalarInput_coefficients h2p a ha n).symm.trans (hcoeff n))
  rw [he]
  exact hf

/-- The actual mass-restored native source trajectory represents a classical
ordinary scalar physical solution, with its exact original distributions. -/
theorem isClassicalOrdinaryPhysicalScalarTrajectory_ordinaryFourthClassicalSourceFlow
    (h2p : 2 ≤ p) (a : FourthClassicalSource)
    (ha : (originalWeightedRealSource _ a).val.fst = (originalWeightedRealSource _ a).val.snd)
    (hs : IsSmoothPhysicalScalarInput (fourthClassicalScalarInput h2p a ha)) :
    IsClassicalOrdinaryPhysicalScalarTrajectory (fourthClassicalScalarInput h2p a ha)
      (fun time => fourthClassicalScalarInput h2p (ordinaryFourthClassicalSourceFlow a time)
        (ordinaryFourthClassicalSourceFlow_diagonal a ha time)) := by
  let f := fun x : ℝ => (nativeSobolevPhysicalJetCLM 4 0 (by omega) a).1 (x : AddCircle (2:ℝ))
  have hf : ContDiff ℝ ∞ f := contDiff_nativePhysical_of_isSmoothPhysicalScalarInput h2p a ha hs
  have hp : Function.Periodic f 1 := hierarchySobolevJetContinuous_periodic 4 0 (by omega) _
  have hr (x : ℝ) : (f x).im = 0 := by
    have h := fourthClassicalPhysicalValue_im_eq_zero a ha 0 x
    simpa only [fourthClassicalPhysicalValue,fourthClassicalPhysicalFlow,fourthClassicalSourceFlow_zero] using h
  have h0 : (fun x => (ordinaryFourthClassicalPhysicalValue a 0 x).1) = f := by
    simp only [ordinaryFourthClassicalPhysicalValue,ordinaryFourthClassicalPhysicalFlow,ordinaryFourthClassicalSourceFlow_zero,f]
  refine ⟨f,hf,hp,hr,?_,fun r => (ordinaryFourthClassicalPhysicalFlow a r).1,
    isClassicalMKdVTrajectory_ordinaryFourthClassicalPhysicalFlow a ha f hf hp hr h0,
    fun x => congrFun h0 x,?_⟩
  · intro n
    exact (fourthClassicalScalarInput_coefficients h2p a ha n).trans
      (periodOneCoefficient_nativeSobolevPhysicalJet_zero 4 (by omega) a n).1.symm
  · intro time n
    exact (fourthClassicalScalarInput_coefficients h2p (ordinaryFourthClassicalSourceFlow a time)
      (ordinaryFourthClassicalSourceFlow_diagonal a ha time) n).trans
      (periodOneCoefficient_ordinaryFourthClassicalPhysicalValue a time n).1.symm

/-- Every smooth original real scalar input has an ordinary classical
physical solution in its original finite-p distribution realization. -/
theorem exists_classicalOrdinaryPhysicalScalarTrajectory (h2p : 2 ≤ p)
    (u : PhysicalScalarRealInput p) (hu : IsSmoothPhysicalScalarInput u) :
    ∃ γ : ℝ → PhysicalScalarRealInput p, IsClassicalOrdinaryPhysicalScalarTrajectory u γ := by
  obtain ⟨f,a,hf,hp,hr,ha,h0,h1,_⟩ := exists_fourthClassicalSource_of_smooth_scalar h2p u hu
  have hcf (n : ℤ) : u.val.val (mode (-n)) = periodOneCoefficient f n := by
    have he := congrArg (fun T : Distribution 1 => T (mode (-n))) h1
    have hc := (fourthClassicalPhysicalValue_physical_coefficients a 0 n).1
    rw [fourthPhysicalImageFlow_zero] at hc
    exact he.symm.trans (hc.symm.trans (congrArg (fun g : ℝ → ℂ => periodOneCoefficient g n) h0))
  have heq : fourthClassicalScalarInput h2p a ha = u := by
    apply Subtype.ext
    apply Subtype.ext
    apply Distribution.ext_coefficients
    intro n
    rw [fourthClassicalScalarInput_coefficients]
    have h := (periodOneCoefficient_fourthClassicalPhysicalValue a 0 n).1
    rw [fourthClassicalSourceFlow_zero] at h
    exact h.symm.trans ((congrArg (fun g : ℝ → ℂ => periodOneCoefficient g n) h0).trans (hcf n).symm)
  have hs : IsSmoothPhysicalScalarInput (fourthClassicalScalarInput h2p a ha) := heq.symm ▸ hu
  refine ⟨(fun time => fourthClassicalScalarInput h2p (ordinaryFourthClassicalSourceFlow a time)
    (ordinaryFourthClassicalSourceFlow_diagonal a ha time)),?_⟩
  have h := isClassicalOrdinaryPhysicalScalarTrajectory_ordinaryFourthClassicalSourceFlow h2p a ha hs
  rwa [heq] at h

/-- A canonical ordinary smooth solution map is a choice of the unique
classical physical solution at every original smooth real scalar datum. -/
def IsClassicalOrdinaryScalarSolutionMap (S : PhysicalScalarRealInput p → ℝ → PhysicalScalarRealInput p) : Prop :=
  ∀ u : PhysicalScalarRealInput p, IsSmoothPhysicalScalarInput u → IsClassicalOrdinaryPhysicalScalarTrajectory u (S u)

/-- The ordinary smooth map exists; smooth agreement is not a vacuous condition. -/
theorem exists_classicalOrdinaryScalarSolutionMap (h2p : 2 ≤ p) :
    ∃ S : PhysicalScalarRealInput p → ℝ → PhysicalScalarRealInput p, IsClassicalOrdinaryScalarSolutionMap S := by
  classical
  let S := fun u : PhysicalScalarRealInput p => if h : IsSmoothPhysicalScalarInput u then
    Classical.choose (exists_classicalOrdinaryPhysicalScalarTrajectory h2p u h) else fun _ => u
  refine ⟨S,fun u hu => ?_⟩
  dsimp only [S]
  rw [dif_pos hu]
  exact Classical.choose_spec (exists_classicalOrdinaryPhysicalScalarTrajectory h2p u hu)

/-- Any canonical ordinary classical smooth map has exactly the restored
fourth coordinate evolution on every smooth native physical scalar input. -/
theorem classicalOrdinaryScalarSolutionMap_coordinates
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : 2 ≤ p)
    (S : PhysicalScalarRealInput p → ℝ → PhysicalScalarRealInput p)
    (hS : IsClassicalOrdinaryScalarSolutionMap S) (a : FourthClassicalSource)
    (ha : (originalWeightedRealSource _ a).val.fst = (originalWeightedRealSource _ a).val.snd)
    (hs : IsSmoothPhysicalScalarInput (fourthClassicalScalarInput h2p a ha)) (time : ℝ) (n : ℤ) :
    (compatibleBirkhoff hp hp1 (physicalScalarPairCLM (S (fourthClassicalScalarInput h2p a ha) time)).val).1 n =
      fourthScalarOrdinaryCoordinate hp hp1 h2p n time a ha := by
  have he := (hS _ hs).unique
    (isClassicalOrdinaryPhysicalScalarTrajectory_ordinaryFourthClassicalSourceFlow h2p a ha hs)
  rw [congrFun he time]
  exact compatibleBirkhoff_ordinaryFourthClassicalSourceFlow hp hp1 h2p a ha time n

end NLS.Articles.MKdVBelowL2
