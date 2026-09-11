/-
Derived from pcbcos/Ripple contributors and licensed under Apache-2.0.
See ../../../licenses/Ripple-Apache-2.0.txt.

Extracted and modified from Ripple/CTMC/CanonicalLaw.lean at commit
83d6a77319d1bbb9bd397f9613244d396dc48583. Only the canonical-record API
required by SSPRK is retained; CTMCPath construction and path helpers are removed.
-/

import SSPRK.CTMC.Core
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

namespace Ripple.CTMC

open Finset MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal

variable {S : Type*}

/-- One jump-hold record: the holding time just sampled and the state reached
after that hold. Record zero is used as the deterministic initial marker. -/
abbrev QMatrix.JumpHoldRecord (S : Type*) := ℝ × S

/-- Ionescu-Tulcea state space for the record trajectory. -/
abbrev QMatrix.JumpHoldTrajectorySpace (S : Type*) (_n : ℕ) :=
  QMatrix.JumpHoldRecord S

/-- The current state encoded by a finite record history is the state component
of the last record. -/
noncomputable def QMatrix.currentStateFromHistory
    (n : ℕ) (hist : (i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i) : S :=
  (hist ⟨n, mem_Iic.mpr le_rfl⟩).2

/-- Reading the current state from the final coordinate of a finite history is
measurable. -/
theorem QMatrix.measurable_currentStateFromHistory [MeasurableSpace S] (n : ℕ) :
    Measurable (fun hist : ((i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i) ↦
      QMatrix.currentStateFromHistory (S := S) n hist) := by
  unfold QMatrix.currentStateFromHistory QMatrix.JumpHoldTrajectorySpace QMatrix.JumpHoldRecord
  fun_prop

/-- Reading the current state from a restricted infinite record sequence returns
the state component of record `n`. -/
@[simp]
theorem QMatrix.currentStateFromHistory_frestrictLe
    (records : (m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) (n : ℕ) :
    QMatrix.currentStateFromHistory (S := S) n (Preorder.frestrictLe n records) =
      (records n).2 := by
  rfl

variable [Fintype S] [DecidableEq S] [Countable S] [MeasurableSpace S]
  [MeasurableSingletonClass S]

/-- The history-dependent kernel required by Mathlib's Ionescu-Tulcea theorem:
look at the last state in the history and sample the next jump-hold record from
the total one-step CTMC kernel. -/
noncomputable def QMatrix.jumpHoldTrajectoryStepKernel (Q : QMatrix S) (n : ℕ) :
    Kernel ((i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i)
      (QMatrix.JumpHoldTrajectorySpace S (n + 1)) :=
  Q.jumpHoldStepKernel.comap
    (fun hist ↦ QMatrix.currentStateFromHistory (S := S) n hist)
    (QMatrix.measurable_currentStateFromHistory (S := S) n)

/-- Applying the history-dependent trajectory kernel just applies the one-step
jump-hold kernel to the current state encoded in the last history record. -/
theorem QMatrix.jumpHoldTrajectoryStepKernel_apply
    (Q : QMatrix S) (n : ℕ)
    (hist : (i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i) :
    Q.jumpHoldTrajectoryStepKernel n hist =
      Q.jumpHoldStepKernel (QMatrix.currentStateFromHistory (S := S) n hist) :=
  rfl

/-- Each history-dependent record kernel is Markov. -/
theorem QMatrix.isMarkovKernel_jumpHoldTrajectoryStepKernel
    (Q : QMatrix S) (n : ℕ) :
    IsMarkovKernel (Q.jumpHoldTrajectoryStepKernel n) := by
  unfold QMatrix.jumpHoldTrajectoryStepKernel
  haveI : IsMarkovKernel Q.jumpHoldStepKernel := Q.isMarkovKernel_jumpHoldStepKernel
  exact Kernel.IsMarkovKernel.comap Q.jumpHoldStepKernel
    (QMatrix.measurable_currentStateFromHistory (S := S) n)

/-- For a non-absorbing current state, the trajectory step samples a positive
holding time almost surely. -/
theorem QMatrix.jumpHoldTrajectoryStepKernel_holdingTime_pos_ae_of_nonabsorbing
    (Q : QMatrix S) (n : ℕ)
    (hist : (i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i)
    (h : ¬Q.IsAbsorbing (QMatrix.currentStateFromHistory (S := S) n hist)) :
    ∀ᵐ r ∂Q.jumpHoldTrajectoryStepKernel n hist, 0 < r.1 := by
  rw [Q.jumpHoldTrajectoryStepKernel_apply, Q.jumpHoldStepKernel_apply,
    Q.jumpHoldStepMeasureTotal_of_nonabsorbing h]
  exact Q.jumpHoldStepMeasure_holdingTime_pos_ae h

/-- For a non-absorbing current state, the trajectory step samples a next state
different from the current state almost surely. -/
theorem QMatrix.jumpHoldTrajectoryStepKernel_next_ne_current_ae_of_nonabsorbing
    (Q : QMatrix S) (n : ℕ)
    (hist : (i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i)
    (h : ¬Q.IsAbsorbing (QMatrix.currentStateFromHistory (S := S) n hist)) :
    ∀ᵐ r ∂Q.jumpHoldTrajectoryStepKernel n hist,
      r.2 ≠ QMatrix.currentStateFromHistory (S := S) n hist := by
  rw [Q.jumpHoldTrajectoryStepKernel_apply, Q.jumpHoldStepKernel_apply,
    Q.jumpHoldStepMeasureTotal_of_nonabsorbing h]
  exact Q.jumpHoldStepMeasure_next_ne_self_ae h

/-- Canonical record trajectory measure started from `s₀`.
Record zero is deterministically `(0, s₀)`, and subsequent records are generated
by the history-dependent jump-hold kernels. -/
noncomputable def QMatrix.canonicalRecordMeasure (Q : QMatrix S) (s₀ : S) :
    Measure ((n : ℕ) → QMatrix.JumpHoldTrajectorySpace S n) := by
  let κ := Q.jumpHoldTrajectoryStepKernel
  letI : ∀ n, IsMarkovKernel (κ n) :=
    fun n ↦ Q.isMarkovKernel_jumpHoldTrajectoryStepKernel n
  exact Kernel.trajMeasure (Measure.dirac (0, s₀)) κ

/-- The canonical record trajectory measure is a probability measure. -/
theorem QMatrix.isProbabilityMeasure_canonicalRecordMeasure
    (Q : QMatrix S) (s₀ : S) :
    IsProbabilityMeasure (Q.canonicalRecordMeasure s₀) := by
  unfold QMatrix.canonicalRecordMeasure
  infer_instance

instance QMatrix.instIsProbabilityMeasureCanonicalRecordMeasure
    (Q : QMatrix S) (s₀ : S) :
    IsProbabilityMeasure (Q.canonicalRecordMeasure s₀) :=
  Q.isProbabilityMeasure_canonicalRecordMeasure s₀

/-- The initial one-coordinate history under the canonical record law is
deterministically `(0, s₀)`. -/
theorem QMatrix.canonicalRecordMeasure_map_frestrictLe_zero
    (Q : QMatrix S) (s₀ : S) :
    (Q.canonicalRecordMeasure s₀).map (Preorder.frestrictLe 0) =
      (Measure.dirac (0, s₀)).map
        (MeasurableEquiv.piUnique
          (fun i : Iic 0 ↦ QMatrix.JumpHoldTrajectorySpace S i)).symm := by
  unfold QMatrix.canonicalRecordMeasure
  let κ := Q.jumpHoldTrajectoryStepKernel
  letI : ∀ n, IsMarkovKernel (κ n) :=
    fun n ↦ Q.isMarkovKernel_jumpHoldTrajectoryStepKernel n
  rw [Kernel.trajMeasure, Measure.map_comp _ _ (by fun_prop),
    Kernel.traj_map_frestrictLe]
  simp

/-- Under the canonical record law, record zero is almost surely the
deterministic initial marker `(0, s₀)`. -/
theorem QMatrix.canonicalRecordMeasure_record_zero_eq_init_ae
    (Q : QMatrix S) (s₀ : S) :
    ∀ᵐ records ∂Q.canonicalRecordMeasure s₀, records 0 = (0, s₀) := by
  let e := (MeasurableEquiv.piUnique
    (fun i : Iic 0 ↦ QMatrix.JumpHoldTrajectorySpace S i)).symm
  have hhist :
      ∀ᵐ hist ∂(Q.canonicalRecordMeasure s₀).map (Preorder.frestrictLe 0),
        hist = e (0, s₀) := by
    rw [Q.canonicalRecordMeasure_map_frestrictLe_zero s₀]
    simp [e]
  have hrecords :
      ∀ᵐ records ∂Q.canonicalRecordMeasure s₀,
        Preorder.frestrictLe 0 records = e (0, s₀) :=
    MeasureTheory.ae_of_ae_map (Preorder.measurable_frestrictLe 0).aemeasurable hhist
  filter_upwards [hrecords] with records hrecords
  have hcoord := congrFun hrecords ⟨0, mem_Iic.mpr le_rfl⟩
  simpa [e] using hcoord

/-- The joint law of the history through step `n` and the next record is the
history marginal composed with the history-dependent jump-hold step kernel. -/
theorem QMatrix.canonicalRecordMeasure_history_next
    (Q : QMatrix S) (s₀ : S) (n : ℕ) :
    (Q.canonicalRecordMeasure s₀).map
        (fun records ↦ (Preorder.frestrictLe n records, records (n + 1))) =
      (Q.canonicalRecordMeasure s₀).map (Preorder.frestrictLe n) ⊗ₘ
        Q.jumpHoldTrajectoryStepKernel n := by
  unfold QMatrix.canonicalRecordMeasure
  let κ := Q.jumpHoldTrajectoryStepKernel
  letI : ∀ n, IsMarkovKernel (κ n) :=
    fun n ↦ Q.isMarkovKernel_jumpHoldTrajectoryStepKernel n
  exact (Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    (μ₀ := Measure.dirac (0, s₀)) (κ := κ) (a := n)).symm

/-- Under the canonical record law, conditional on a non-absorbing history
through step `n`, the next sampled holding time is positive almost surely. -/
theorem QMatrix.canonicalRecordMeasure_next_holdingTime_pos_ae_of_nonabsorbing
    (Q : QMatrix S) (s₀ : S) (n : ℕ) :
    ∀ᵐ records ∂Q.canonicalRecordMeasure s₀,
      ¬Q.IsAbsorbing
          (QMatrix.currentStateFromHistory (S := S) n (Preorder.frestrictLe n records)) →
        0 < (records (n + 1)).1 := by
  let μ := Q.canonicalRecordMeasure s₀
  let x : ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) →
      ((i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i) :=
    Preorder.frestrictLe n
  let y : ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) →
      QMatrix.JumpHoldTrajectorySpace S (n + 1) :=
    fun records ↦ records (n + 1)
  let p :
      (((i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i) ×
        QMatrix.JumpHoldTrajectorySpace S (n + 1)) → Prop :=
    fun z ↦
      ¬Q.IsAbsorbing (QMatrix.currentStateFromHistory (S := S) n z.1) → 0 < z.2.1
  have hp : MeasurableSet {z | p z} := by
    have h_abs : MeasurableSet
        {z : (((i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i) ×
            QMatrix.JumpHoldTrajectorySpace S (n + 1)) |
          Q.IsAbsorbing (QMatrix.currentStateFromHistory (S := S) n z.1)} := by
      exact ((QMatrix.measurable_currentStateFromHistory (S := S) n).comp measurable_fst)
        ((Set.to_countable {s : S | Q.IsAbsorbing s}).measurableSet)
    have h_pos : MeasurableSet
        {z : (((i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i) ×
            QMatrix.JumpHoldTrajectorySpace S (n + 1)) | 0 < z.2.1} := by
      exact (measurable_fst.comp measurable_snd) measurableSet_Ioi
    rw [show {z | p z} =
        {z : (((i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i) ×
            QMatrix.JumpHoldTrajectorySpace S (n + 1)) |
          Q.IsAbsorbing (QMatrix.currentStateFromHistory (S := S) n z.1)} ∪
        {z : (((i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i) ×
            QMatrix.JumpHoldTrajectorySpace S (n + 1)) | 0 < z.2.1} by
      ext z
      by_cases h : Q.IsAbsorbing (QMatrix.currentStateFromHistory (S := S) n z.1)
      · simp [p, h]
      · simp [p, h]]
    exact h_abs.union h_pos
  have hkernel :
      ∀ᵐ hist ∂μ.map x,
        ∀ᵐ r ∂Q.jumpHoldTrajectoryStepKernel n hist, p (hist, r) := by
    refine Filter.Eventually.of_forall ?_
    intro hist
    by_cases h : Q.IsAbsorbing (QMatrix.currentStateFromHistory (S := S) n hist)
    · filter_upwards with r
      intro hnon
      exact (hnon h).elim
    · exact (Q.jumpHoldTrajectoryStepKernel_holdingTime_pos_ae_of_nonabsorbing n hist h).mono
        (fun r hr _hnon ↦ hr)
  have hpair : ∀ᵐ z ∂(μ.map fun records ↦ (x records, y records)), p z := by
    rw [show μ.map (fun records ↦ (x records, y records)) =
        μ.map (fun records ↦ (Preorder.frestrictLe n records, records (n + 1))) by
          rfl]
    rw [show μ.map x = μ.map (Preorder.frestrictLe n) by rfl] at hkernel
    rw [show μ = Q.canonicalRecordMeasure s₀ by rfl]
    rw [Q.canonicalRecordMeasure_history_next s₀ n]
    exact Measure.ae_compProd_of_ae_ae hp hkernel
  have hrecords : ∀ᵐ records ∂μ, p (x records, y records) :=
    MeasureTheory.ae_of_ae_map (by fun_prop) hpair
  simpa [μ, x, y, p] using hrecords

/-- Under the canonical record law, all next holding times are positive whenever
the corresponding finite history is non-absorbing. -/
theorem QMatrix.canonicalRecordMeasure_all_next_holdingTime_pos_ae_of_nonabsorbing
    (Q : QMatrix S) (s₀ : S) :
    ∀ᵐ records ∂Q.canonicalRecordMeasure s₀, ∀ n,
      ¬Q.IsAbsorbing
          (QMatrix.currentStateFromHistory (S := S) n (Preorder.frestrictLe n records)) →
        0 < (records (n + 1)).1 := by
  exact ae_all_iff.mpr fun n ↦
    Q.canonicalRecordMeasure_next_holdingTime_pos_ae_of_nonabsorbing s₀ n

/-- Under the canonical record law, conditional on a non-absorbing history,
the next sampled state differs from the current state almost surely. -/
theorem QMatrix.canonicalRecordMeasure_next_state_ne_current_ae_of_nonabsorbing
    (Q : QMatrix S) (s₀ : S) (n : ℕ) :
    ∀ᵐ records ∂Q.canonicalRecordMeasure s₀,
      ¬Q.IsAbsorbing
          (QMatrix.currentStateFromHistory (S := S) n (Preorder.frestrictLe n records)) →
        (records (n + 1)).2 ≠
          QMatrix.currentStateFromHistory (S := S) n (Preorder.frestrictLe n records) := by
  let μ := Q.canonicalRecordMeasure s₀
  let x : ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) →
      ((i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i) :=
    Preorder.frestrictLe n
  let y : ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) →
      QMatrix.JumpHoldTrajectorySpace S (n + 1) :=
    fun records ↦ records (n + 1)
  let p :
      (((i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i) ×
        QMatrix.JumpHoldTrajectorySpace S (n + 1)) → Prop :=
    fun z ↦
      ¬Q.IsAbsorbing (QMatrix.currentStateFromHistory (S := S) n z.1) →
        z.2.2 ≠ QMatrix.currentStateFromHistory (S := S) n z.1
  have hp : MeasurableSet {z | p z} := by
    have h_abs : MeasurableSet
        {z : (((i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i) ×
            QMatrix.JumpHoldTrajectorySpace S (n + 1)) |
          Q.IsAbsorbing (QMatrix.currentStateFromHistory (S := S) n z.1)} := by
      exact ((QMatrix.measurable_currentStateFromHistory (S := S) n).comp measurable_fst)
        ((Set.to_countable {s : S | Q.IsAbsorbing s}).measurableSet)
    have h_ne : MeasurableSet
        {z : (((i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i) ×
            QMatrix.JumpHoldTrajectorySpace S (n + 1)) |
          z.2.2 ≠ QMatrix.currentStateFromHistory (S := S) n z.1} := by
      have h_eq : MeasurableSet
          {z : (((i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i) ×
              QMatrix.JumpHoldTrajectorySpace S (n + 1)) |
            z.2.2 = QMatrix.currentStateFromHistory (S := S) n z.1} :=
        measurableSet_eq_fun (measurable_snd.comp measurable_snd)
          ((QMatrix.measurable_currentStateFromHistory (S := S) n).comp measurable_fst)
      convert h_eq.compl using 1
    rw [show {z | p z} =
        {z : (((i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i) ×
            QMatrix.JumpHoldTrajectorySpace S (n + 1)) |
          Q.IsAbsorbing (QMatrix.currentStateFromHistory (S := S) n z.1)} ∪
        {z : (((i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i) ×
            QMatrix.JumpHoldTrajectorySpace S (n + 1)) |
          z.2.2 ≠ QMatrix.currentStateFromHistory (S := S) n z.1} by
      ext z
      by_cases h : Q.IsAbsorbing (QMatrix.currentStateFromHistory (S := S) n z.1)
      · simp [p, h]
      · simp [p, h]]
    exact h_abs.union h_ne
  have hkernel :
      ∀ᵐ hist ∂μ.map x,
        ∀ᵐ r ∂Q.jumpHoldTrajectoryStepKernel n hist, p (hist, r) := by
    refine Filter.Eventually.of_forall ?_
    intro hist
    by_cases h : Q.IsAbsorbing (QMatrix.currentStateFromHistory (S := S) n hist)
    · filter_upwards with r
      intro hnon
      exact (hnon h).elim
    · exact
        (Q.jumpHoldTrajectoryStepKernel_next_ne_current_ae_of_nonabsorbing n hist h).mono
          (fun r hr _hnon ↦ hr)
  have hpair : ∀ᵐ z ∂(μ.map fun records ↦ (x records, y records)), p z := by
    rw [show μ.map (fun records ↦ (x records, y records)) =
        μ.map (fun records ↦ (Preorder.frestrictLe n records, records (n + 1))) by
          rfl]
    rw [show μ.map x = μ.map (Preorder.frestrictLe n) by rfl] at hkernel
    rw [show μ = Q.canonicalRecordMeasure s₀ by rfl]
    rw [Q.canonicalRecordMeasure_history_next s₀ n]
    exact Measure.ae_compProd_of_ae_ae hp hkernel
  have hrecords : ∀ᵐ records ∂μ, p (x records, y records) :=
    MeasureTheory.ae_of_ae_map (by fun_prop) hpair
  simpa [μ, x, y, p] using hrecords

/-- Under the canonical record law, all non-absorbing steps change state. -/
theorem QMatrix.canonicalRecordMeasure_all_next_state_ne_current_ae_of_nonabsorbing
    (Q : QMatrix S) (s₀ : S) :
    ∀ᵐ records ∂Q.canonicalRecordMeasure s₀, ∀ n,
      ¬Q.IsAbsorbing
          (QMatrix.currentStateFromHistory (S := S) n (Preorder.frestrictLe n records)) →
        (records (n + 1)).2 ≠
          QMatrix.currentStateFromHistory (S := S) n (Preorder.frestrictLe n records) := by
  exact ae_all_iff.mpr fun n ↦
    Q.canonicalRecordMeasure_next_state_ne_current_ae_of_nonabsorbing s₀ n

/-- Under the canonical record law, once a history is in an absorbing state,
the next sampled state is the same state almost surely. -/
theorem QMatrix.canonicalRecordMeasure_all_next_state_eq_current_ae_of_absorbing
    (Q : QMatrix S) (s₀ : S) :
    ∀ᵐ records ∂Q.canonicalRecordMeasure s₀, ∀ n,
      Q.IsAbsorbing
          (QMatrix.currentStateFromHistory (S := S) n (Preorder.frestrictLe n records)) →
        (records (n + 1)).2 =
          QMatrix.currentStateFromHistory (S := S) n (Preorder.frestrictLe n records) := by
  refine ae_all_iff.mpr ?_
  intro n
  let μ := Q.canonicalRecordMeasure s₀
  let x : ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) →
      ((i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i) :=
    Preorder.frestrictLe n
  let y : ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) →
      QMatrix.JumpHoldTrajectorySpace S (n + 1) :=
    fun records ↦ records (n + 1)
  let p :
      (((i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i) ×
        QMatrix.JumpHoldTrajectorySpace S (n + 1)) → Prop :=
    fun z ↦
      Q.IsAbsorbing (QMatrix.currentStateFromHistory (S := S) n z.1) →
        z.2.2 = QMatrix.currentStateFromHistory (S := S) n z.1
  have hp : MeasurableSet {z | p z} := by
    have h_abs : MeasurableSet
        {z : (((i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i) ×
            QMatrix.JumpHoldTrajectorySpace S (n + 1)) |
          Q.IsAbsorbing (QMatrix.currentStateFromHistory (S := S) n z.1)} := by
      exact ((QMatrix.measurable_currentStateFromHistory (S := S) n).comp measurable_fst)
        ((Set.to_countable {s : S | Q.IsAbsorbing s}).measurableSet)
    have h_eq : MeasurableSet
        {z : (((i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i) ×
            QMatrix.JumpHoldTrajectorySpace S (n + 1)) |
          z.2.2 = QMatrix.currentStateFromHistory (S := S) n z.1} :=
      measurableSet_eq_fun (measurable_snd.comp measurable_snd)
        ((QMatrix.measurable_currentStateFromHistory (S := S) n).comp measurable_fst)
    rw [show {z | p z} =
        {z : (((i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i) ×
            QMatrix.JumpHoldTrajectorySpace S (n + 1)) |
          ¬Q.IsAbsorbing (QMatrix.currentStateFromHistory (S := S) n z.1)} ∪
        {z : (((i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i) ×
            QMatrix.JumpHoldTrajectorySpace S (n + 1)) |
          z.2.2 = QMatrix.currentStateFromHistory (S := S) n z.1} by
      ext z
      by_cases h : Q.IsAbsorbing (QMatrix.currentStateFromHistory (S := S) n z.1)
      · simp [p, h]
      · simp [p, h]]
    exact h_abs.compl.union h_eq
  have hkernel :
      ∀ᵐ hist ∂μ.map x,
        ∀ᵐ r ∂Q.jumpHoldTrajectoryStepKernel n hist, p (hist, r) := by
    refine Filter.Eventually.of_forall ?_
    intro hist
    by_cases h : Q.IsAbsorbing (QMatrix.currentStateFromHistory (S := S) n hist)
    · rw [Q.jumpHoldTrajectoryStepKernel_apply, Q.jumpHoldStepKernel_apply,
        Q.jumpHoldStepMeasureTotal_of_absorbing h]
      simp [p, h]
    · filter_upwards with r
      intro h_abs
      exact (h h_abs).elim
  have hpair : ∀ᵐ z ∂(μ.map fun records ↦ (x records, y records)), p z := by
    rw [show μ.map (fun records ↦ (x records, y records)) =
        μ.map (fun records ↦ (Preorder.frestrictLe n records, records (n + 1))) by
          rfl]
    rw [show μ.map x = μ.map (Preorder.frestrictLe n) by rfl] at hkernel
    rw [show μ = Q.canonicalRecordMeasure s₀ by rfl]
    rw [Q.canonicalRecordMeasure_history_next s₀ n]
    exact Measure.ae_compProd_of_ae_ae hp hkernel
  have hrecords : ∀ᵐ records ∂μ, p (x records, y records) :=
    MeasureTheory.ae_of_ae_map (by fun_prop) hpair
  simpa [μ, x, y, p] using hrecords

/-- Under the canonical record law, once a history is absorbing, the next
sampled holding time is the terminal marker zero almost surely. -/
theorem QMatrix.canonicalRecordMeasure_all_next_holdingTime_eq_zero_ae_of_absorbing
    (Q : QMatrix S) (s₀ : S) :
    ∀ᵐ records ∂Q.canonicalRecordMeasure s₀, ∀ n,
      Q.IsAbsorbing
          (QMatrix.currentStateFromHistory (S := S) n (Preorder.frestrictLe n records)) →
        (records (n + 1)).1 = 0 := by
  refine ae_all_iff.mpr ?_
  intro n
  let μ := Q.canonicalRecordMeasure s₀
  let x : ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) →
      ((i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i) :=
    Preorder.frestrictLe n
  let y : ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) →
      QMatrix.JumpHoldTrajectorySpace S (n + 1) :=
    fun records ↦ records (n + 1)
  let p :
      (((i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i) ×
        QMatrix.JumpHoldTrajectorySpace S (n + 1)) → Prop :=
    fun z ↦
      Q.IsAbsorbing (QMatrix.currentStateFromHistory (S := S) n z.1) →
        z.2.1 = 0
  have hp : MeasurableSet {z | p z} := by
    have h_abs : MeasurableSet
        {z : (((i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i) ×
            QMatrix.JumpHoldTrajectorySpace S (n + 1)) |
          Q.IsAbsorbing (QMatrix.currentStateFromHistory (S := S) n z.1)} := by
      exact ((QMatrix.measurable_currentStateFromHistory (S := S) n).comp measurable_fst)
        ((Set.to_countable {s : S | Q.IsAbsorbing s}).measurableSet)
    have h_eq : MeasurableSet
        {z : (((i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i) ×
            QMatrix.JumpHoldTrajectorySpace S (n + 1)) |
          z.2.1 = (0 : ℝ)} :=
      measurableSet_eq_fun (measurable_fst.comp measurable_snd) measurable_const
    rw [show {z | p z} =
        {z : (((i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i) ×
            QMatrix.JumpHoldTrajectorySpace S (n + 1)) |
          ¬Q.IsAbsorbing (QMatrix.currentStateFromHistory (S := S) n z.1)} ∪
        {z : (((i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i) ×
            QMatrix.JumpHoldTrajectorySpace S (n + 1)) |
          z.2.1 = (0 : ℝ)} by
      ext z
      by_cases h : Q.IsAbsorbing (QMatrix.currentStateFromHistory (S := S) n z.1)
      · simp [p, h]
      · simp [p, h]]
    exact h_abs.compl.union h_eq
  have hkernel :
      ∀ᵐ hist ∂μ.map x,
        ∀ᵐ r ∂Q.jumpHoldTrajectoryStepKernel n hist, p (hist, r) := by
    refine Filter.Eventually.of_forall ?_
    intro hist
    by_cases h : Q.IsAbsorbing (QMatrix.currentStateFromHistory (S := S) n hist)
    · rw [Q.jumpHoldTrajectoryStepKernel_apply, Q.jumpHoldStepKernel_apply,
        Q.jumpHoldStepMeasureTotal_of_absorbing h]
      simp [p, h]
    · filter_upwards with r
      intro h_abs
      exact (h h_abs).elim
  have hpair : ∀ᵐ z ∂(μ.map fun records ↦ (x records, y records)), p z := by
    rw [show μ.map (fun records ↦ (x records, y records)) =
        μ.map (fun records ↦ (Preorder.frestrictLe n records, records (n + 1))) by
          rfl]
    rw [show μ.map x = μ.map (Preorder.frestrictLe n) by rfl] at hkernel
    rw [show μ = Q.canonicalRecordMeasure s₀ by rfl]
    rw [Q.canonicalRecordMeasure_history_next s₀ n]
    exact Measure.ae_compProd_of_ae_ae hp hkernel
  have hrecords : ∀ᵐ records ∂μ, p (x records, y records) :=
    MeasureTheory.ae_of_ae_map (by fun_prop) hpair
  simpa [μ, x, y, p] using hrecords

/-- Under the canonical record law, every sampled next holding time is
nonnegative. -/
theorem QMatrix.canonicalRecordMeasure_all_next_holdingTime_nonneg_ae
    (Q : QMatrix S) (s₀ : S) :
    ∀ᵐ records ∂Q.canonicalRecordMeasure s₀, ∀ n,
      0 ≤ (records (n + 1)).1 := by
  filter_upwards
    [Q.canonicalRecordMeasure_all_next_holdingTime_pos_ae_of_nonabsorbing s₀,
      Q.canonicalRecordMeasure_all_next_holdingTime_eq_zero_ae_of_absorbing s₀]
    with records hpos hzero n
  by_cases h :
      Q.IsAbsorbing
        (QMatrix.currentStateFromHistory (S := S) n (Preorder.frestrictLe n records))
  · exact le_of_eq (hzero n h).symm
  · exact le_of_lt (hpos n h)

end Ripple.CTMC
