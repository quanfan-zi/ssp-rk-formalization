import SSPRK.RKTransform

/-!
# First three moments under one-state block decomposition

These finite matrix identities isolate the scalar and off-diagonal contributions of a
distinguished state whose Green diagonal entry equals one. No positivity is required.
-/

open scoped BigOperators

namespace SSPRK

/-- Upper off-diagonal block at the distinguished state. -/
def phaseBlockU {n : ℕ} (G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) : Fin n → ℝ :=
  fun j ↦ G 0 j.succ

/-- Lower off-diagonal block at the distinguished state. -/
def phaseBlockV {n : ℕ} (G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) : Fin n → ℝ :=
  fun i ↦ G i.succ 0

/-- Remaining principal block after removing the distinguished state. -/
def phaseBlockW {n : ℕ} (G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    Matrix (Fin n) (Fin n) ℝ := fun i j ↦ G i.succ j.succ

/-- Schur complement when the distinguished diagonal entry equals one. -/
def phaseBlockH {n : ℕ} (G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  phaseBlockW G - Matrix.vecMulVec (phaseBlockV G) (phaseBlockU G)

/-- The distinguished coordinate of multiplication by a block matrix. -/
lemma phaseBlock_mulVec_zero {n : ℕ} (G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hG : G 0 0 = 1) (x : Fin (n + 1) → ℝ) :
    G.mulVec x 0 = x 0 + dotProduct (phaseBlockU G) (fun j ↦ x j.succ) := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, hG, one_mul, phaseBlockU]

/-- The remaining coordinates of multiplication by a block matrix. -/
lemma phaseBlock_mulVec_succ {n : ℕ} (G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (x : Fin (n + 1) → ℝ) (i : Fin n) :
    G.mulVec x i.succ = phaseBlockV G i * x 0 +
      (phaseBlockW G).mulVec (fun j ↦ x j.succ) i := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, phaseBlockV, phaseBlockW]

/-- The tail of matrix-vector multiplication, expressed in block form. -/
lemma phaseBlock_mulVec_tail {n : ℕ} (G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (x : Fin (n + 1) → ℝ) :
    (fun i ↦ G.mulVec x i.succ) =
      x 0 • phaseBlockV G + (phaseBlockW G).mulVec (fun j ↦ x j.succ) := by
  funext i
  rw [phaseBlock_mulVec_succ]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The factorial Green moment from the distinguished state. -/
def phaseBlockMoment {n : ℕ} (G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (k : ℕ) : ℝ :=
  (k.factorial : ℝ) * (G ^ k).mulVec (fun _ ↦ 1) 0

/-- First weighted moment in the remaining principal block. -/
def phaseBlockZ1 {n : ℕ} (G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) : ℝ :=
  dotProduct (phaseBlockU G) (fun _ ↦ 1)

/-- Second weighted moment in the remaining principal block. -/
def phaseBlockZ2 {n : ℕ} (G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) : ℝ :=
  2 * dotProduct (phaseBlockU G) ((phaseBlockW G).mulVec (fun _ ↦ 1))

/-- Third weighted moment in the remaining principal block. -/
def phaseBlockZ3 {n : ℕ} (G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) : ℝ :=
  6 * dotProduct (phaseBlockU G) ((phaseBlockW G).mulVec ((phaseBlockW G).mulVec (fun _ ↦ 1)))

/-- Immediate return weight through the remaining states. -/
def phaseBlockEta1 {n : ℕ} (G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) : ℝ :=
  dotProduct (phaseBlockU G) (phaseBlockV G)

/-- Second return moment in the Schur complement block. -/
def phaseBlockEta2 {n : ℕ} (G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) : ℝ :=
  2 * dotProduct (phaseBlockU G) ((phaseBlockH G).mulVec (phaseBlockV G))

/-- The normalized first moment separates the distinguished state from the tail. -/
theorem phaseBlock_first_moment {n : ℕ} (G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hG : G 0 0 = 1) : phaseBlockMoment G 1 = phaseBlockZ1 G + 1 := by
  simp only [phaseBlockMoment, Nat.factorial_one, Nat.cast_one, one_mul, pow_one]
  rw [phaseBlock_mulVec_zero G hG]
  change 1 + phaseBlockZ1 G = phaseBlockZ1 G + 1
  ring

/-- The normalized second moment separates the principal-block and immediate-return terms. -/
theorem phaseBlock_second_moment {n : ℕ} (G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hG : G 0 0 = 1) : phaseBlockMoment G 2 =
      phaseBlockZ2 G + 2 * phaseBlockZ1 G + 2 * (1 + phaseBlockEta1 G) := by
  norm_num only [phaseBlockMoment, Nat.factorial_succ, Nat.factorial_zero]
  rw [pow_two, ← Matrix.mulVec_mulVec, phaseBlock_mulVec_zero G hG,
    phaseBlock_mulVec_zero G hG, phaseBlock_mulVec_tail]
  simp only [one_smul, dotProduct_add]
  change 2 * (1 + phaseBlockZ1 G +
    (phaseBlockEta1 G + dotProduct (phaseBlockU G) ((phaseBlockW G).mulVec (fun _ ↦ 1)))) = _
  unfold phaseBlockZ2
  ring

/-- The Schur return correction removes the square of the immediate return weight. -/
lemma phaseBlock_schur_return {n : ℕ} (G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    dotProduct (phaseBlockU G) ((phaseBlockH G).mulVec (phaseBlockV G)) =
      dotProduct (phaseBlockU G) ((phaseBlockW G).mulVec (phaseBlockV G)) -
        (phaseBlockEta1 G) ^ 2 := by
  rw [phaseBlockH, Matrix.sub_mulVec, Matrix.vecMulVec_mulVec, dotProduct_sub]
  simp only [op_smul_eq_smul, dotProduct_smul, smul_eq_mul, phaseBlockEta1, pow_two]

/-- The normalized third moment separates the principal block from its return correction. -/
theorem phaseBlock_third_moment {n : ℕ} (G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hG : G 0 0 = 1) : phaseBlockMoment G 3 =
      phaseBlockZ3 G + 3 * phaseBlockZ2 G +
        6 * phaseBlockZ1 G * (1 + phaseBlockEta1 G) +
        6 * (1 + phaseBlockEta1 G) ^ 2 + 3 * phaseBlockEta2 G := by
  norm_num only [phaseBlockMoment, Nat.factorial_succ, Nat.factorial_zero]
  rw [show (3 : ℕ) = 1 + 2 from rfl, pow_add, pow_one, ← Matrix.mulVec_mulVec,
    phaseBlock_mulVec_zero G hG]
  simp only [pow_two, ← Matrix.mulVec_mulVec, phaseBlock_mulVec_zero G hG,
    phaseBlock_mulVec_tail, Matrix.mulVec_add, dotProduct_add, dotProduct_smul, one_smul]
  unfold phaseBlockZ1 phaseBlockZ2 phaseBlockZ3 phaseBlockEta2
  rw [phaseBlock_schur_return]
  simp only [phaseBlockEta1, smul_eq_mul]
  ring

end SSPRK
