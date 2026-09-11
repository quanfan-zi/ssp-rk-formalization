import SSPRK.ChainMatrices
import SSPRK.PhaseType

/-!
# Erlang phase-type representations

The deterministic downward chain with one initial top phase has an Erlang law.
-/

open scoped BigOperators ENNReal

open MeasureTheory

namespace SSPRK

noncomputable section

lemma shiftDown_pow_apply (s n : ℕ) (i j : Fin s) :
    (shiftDown s ^ n) i j = if i.val = j.val + n then 1 else 0 := by
  induction n generalizing i j with
  | zero =>
    by_cases hij : i = j
    · subst i
      simp
    · have hval : i.val ≠ j.val := by
        intro h
        apply hij
        exact Fin.ext h
      simp [hij, hval]
  | succ n ih =>
    rw [pow_succ, Matrix.mul_apply]
    simp_rw [ih]
    simp only [shiftDown, mul_ite, mul_one, mul_zero]
    by_cases hlast : j.val + 1 < s
    · let k : Fin s := ⟨j.val + 1, hlast⟩
      have hsum : (∑ x : Fin s, if x.val = j.val + 1 then
          (if i.val = x.val + n then (1 : ℝ) else 0) else 0) =
          if i.val = k.val + n then 1 else 0 := by
        simpa [k] using fin_sum_val_ite hlast
          (fun x : Fin s ↦ if i.val = x.val + n then (1 : ℝ) else 0)
      rw [hsum]
      have hk : k.val = j.val + 1 := rfl
      have hval : k.val + n = j.val + (n + 1) := by omega
      simp [hval]
    · have hsum : (∑ x : Fin s, if x.val = j.val + 1 then
          (if i.val = x.val + n then (1 : ℝ) else 0) else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro x _
        by_cases hx : x.val = j.val + 1
        · exfalso
          apply hlast
          omega
        · simp [hx]
      rw [hsum]
      have hne : ¬i.val = j.val + (n + 1) := by
        intro h
        apply hlast
        omega
      simp [hne]

/-- The initial row concentrated at the top state of a chain with `n + 1` states. -/
def erlangInitial (n : ℕ) : Fin (n + 1) → ℝ := fun i ↦ if i = Fin.last n then 1 else 0

/-- The standard `n + 1`-stage Erlang phase-type representation at rate `κ`. -/
def erlangPhaseType (n : ℕ) (κ : ℝ) (hκ : 0 < κ) : PhaseTypeData (n + 1) where
  transition := shiftDown (n + 1)
  initial := erlangInitial n
  rate := κ
  rate_pos := hκ
  substochastic := by
    constructor
    · exact shiftDown_nonneg (n + 1)
    · intro i
      have hrow : Matrix.mulVec (shiftDown (n + 1)) (ones (n + 1)) i ≤ 1 := by
        rw [shiftDown_mulVec_ones]
        split_ifs <;> norm_num
      simpa [Matrix.mulVec, dotProduct, ones] using hrow
  transient := by
    intro hzero
    have h := congrArg Matrix.det (chainD_mul_chainL (n + 1))
    simp [chainD, Matrix.det_mul, hzero] at h
  initial_nonneg := by
    intro i
    unfold erlangInitial
    split_ifs <;> norm_num
  initial_mass_le := by
    have hsum : (∑ i : Fin (n + 1), erlangInitial n i) = 1 := by
      unfold erlangInitial
      rw [Fintype.sum_ite_eq' (Fin.last n)]
    linarith

lemma erlangPhaseType_mass (n : ℕ) (κ : ℝ) (hκ : 0 < κ) :
    (erlangPhaseType n κ hκ).mass = 1 := by
  unfold PhaseTypeData.mass erlangPhaseType
  rw [show (∑ i : Fin (n + 1), erlangInitial n i) = 1 by
    unfold erlangInitial
    rw [Fintype.sum_ite_eq' (Fin.last n)]
    ]

lemma erlangPhaseType_exit (n : ℕ) (κ : ℝ) (hκ : 0 < κ) (i : Fin (n + 1)) :
    (erlangPhaseType n κ hκ).exit i = if i.val = 0 then 1 else 0 := by
  unfold PhaseTypeData.exit erlangPhaseType
  exact chainD_mulVec_ones (n + 1) i

lemma erlangPhaseType_weight (n k : ℕ) (κ : ℝ) (hκ : 0 < κ) :
    (erlangPhaseType n κ hκ).weight k = if k = n then 1 else 0 := by
  have hentry := shiftDown_pow_apply (n + 1) k (Fin.last n) (0 : Fin (n + 1))
  have hentry' : (shiftDown (n + 1) ^ k) (Fin.last n) 0 = if k = n then 1 else 0 := by
    simpa [eq_comm] using hentry
  have htop (f : Fin (n + 1) → ℝ) : dotProduct (erlangInitial n) f = f (Fin.last n) := by
    unfold dotProduct erlangInitial
    calc
      (∑ i : Fin (n + 1), (if i = Fin.last n then 1 else 0) * f i) =
          ∑ i : Fin (n + 1), if i = Fin.last n then f i else 0 := by
            apply Finset.sum_congr rfl
            intro i _
            split_ifs <;> ring
      _ = f (Fin.last n) := Fintype.sum_ite_eq' (Fin.last n) f
  have hzero (a : Fin (n + 1)) :
      (∑ j : Fin (n + 1), (shiftDown (n + 1) ^ k) a j *
          (if j.val = 0 then 1 else 0)) = (shiftDown (n + 1) ^ k) a 0 := by
    calc
      (∑ j : Fin (n + 1), (shiftDown (n + 1) ^ k) a j *
          (if j.val = 0 then 1 else 0)) =
          ∑ j : Fin (n + 1), if j = 0 then (shiftDown (n + 1) ^ k) a j else 0 := by
            apply Finset.sum_congr rfl
            intro j _
            by_cases hj : j = 0
            · subst j
              simp
            · have hjval : j.val ≠ 0 := by
                intro h
                apply hj
                exact Fin.ext h
              simp [hj, hjval]
      _ = (shiftDown (n + 1) ^ k) a 0 :=
        Fintype.sum_ite_eq' 0 (fun j ↦ (shiftDown (n + 1) ^ k) a j)
  unfold PhaseTypeData.weight
  change dotProduct (erlangInitial n)
    ((shiftDown (n + 1) ^ k).mulVec (erlangPhaseType n κ hκ).exit) = _
  rw [htop]
  simp only [Matrix.mulVec, dotProduct]
  simp_rw [erlangPhaseType_exit]
  rw [hzero]
  exact hentry'

/-- The deterministic `n + 1`-stage chain has the Erlang law of shape `n + 1`. -/
theorem erlangPhaseType_measure (n : ℕ) (κ : ℝ) (hκ : 0 < κ) :
    (erlangPhaseType n κ hκ).measure = ProbabilityTheory.gammaMeasure (n + 1) κ := by
  apply Measure.ext
  intro U hU
  rw [PhaseTypeData.measure, PhaseTypeData.positiveMeasure, Measure.add_apply,
    Measure.smul_apply, Measure.sum_apply _ hU, erlangPhaseType_mass]
  simp_rw [erlangPhaseType_weight]
  simp only [sub_self, ENNReal.ofReal_zero, Measure.smul_apply, smul_eq_mul,
    zero_mul, zero_add]
  change (∑' i : ℕ, ENNReal.ofReal (if i = n then (1 : ℝ) else 0) *
      (ProbabilityTheory.gammaMeasure ((i : ℝ) + 1) κ) U) =
    (ProbabilityTheory.gammaMeasure ((n : ℝ) + 1) κ) U
  calc
    ∑' i : ℕ, ENNReal.ofReal (if i = n then (1 : ℝ) else 0) *
        (ProbabilityTheory.gammaMeasure ((i : ℝ) + 1) κ) U =
        ∑' i : ℕ, if i = n then (ProbabilityTheory.gammaMeasure ((n : ℝ) + 1) κ) U else 0 := by
          apply tsum_congr
          intro i
          by_cases hi : i = n
          · subst i
            simp
          · simp [hi]
    _ = (ProbabilityTheory.gammaMeasure ((n : ℝ) + 1) κ) U := tsum_ite_eq n _

end

end SSPRK
