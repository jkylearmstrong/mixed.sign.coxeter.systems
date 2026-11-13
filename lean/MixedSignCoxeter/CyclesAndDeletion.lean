/-
Copyright (c) 2026 Johnathon Kyle Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Fin.VecNotation
import MixedSignCoxeter.MixedSign

/-!
# Odd Cycles and Failure of the Deletion Property (Chapter 3, Section 3.2)

Formalization of Section 3.2 of:
Johnathon Kyle Armstrong, *Principal Elements of Mixed-Sign Coxeter Systems* (FSU, 2012).

## Main results
* `tildeAminus2_fails_deletion` (**Lemma 3.21 & Theorem 1.2**): In `W(~A_{-2})`, the word
  `w = [0, 1, 0, 2, 0]` (`s₁ s₂ s₁ s₃ s₁`, length 5) equals `[2, 0, 1]` (`s₃ s₁ s₂`, length 3),
  so `w` is not reduced, yet deleting any two letters from `w` never yields `w`.
* `cyclePosForm_posSemidef` (**Theorem 1.6, part 1**): For `m ≥ 3`, `B(~A_{m-1})` is positive
  semidefinite (`vᵀ B v = ∑ i, (v i - v (i+1))^2 ≥ 0`) and degenerate (`B * 1 = 0`).
* `oddCycleNegForm_negDef` (**Theorem 1.6, part 2**): For odd `m ≥ 3` (`~A_{-n}` with `n` even),
  `B(~A_{-n})` is strictly negative definite (`vᵀ B v < 0` for all `v ≠ 0`).
-/

open Matrix

namespace MixedSignCoxeter

/-! ### Lemma 3.21 & Theorem 1.2: Failure of the Deletion Property in `W(~A_{-2})` -/

section DeletionFailure

private def s0Z : Matrix (Fin 3) (Fin 3) ℤ :=
  !![-1, -1, -1;
      0,  1,  0;
      0,  0,  1]

private def s1Z : Matrix (Fin 3) (Fin 3) ℤ :=
  !![ 1,  0,  0;
     -1, -1, -1;
      0,  0,  1]

private def s2Z : Matrix (Fin 3) (Fin 3) ℤ :=
  !![ 1,  0,  0;
      0,  1,  0;
     -1, -1, -1]

private def genZ : Fin 3 → Matrix (Fin 3) (Fin 3) ℤ
  | 0 => s0Z
  | 1 => s1Z
  | 2 => s2Z

private def evalZ (w : List (Fin 3)) : Matrix (Fin 3) (Fin 3) ℤ :=
  (w.map genZ).prod

private lemma genZ_cast (i : Fin 3) :
    (genZ i).map (Int.cast : ℤ → ℝ) =
      match i with
      | 0 => s1TildeAminus2
      | 1 => s2TildeAminus2
      | 2 => s3TildeAminus2 := by
  fin_cases i <;> ext r c <;> fin_cases r <;> fin_cases c <;>
    simp [genZ, s0Z, s1Z, s2Z, s1TildeAminus2, s2TildeAminus2, s3TildeAminus2]

/-- The `~A_{-2}` mixed-sign Coxeter graph on 3 nodes (all signs `-`, all edges weight `3`). -/
def tildeAminus2Graph : MixedSignCoxeterGraph 3 where
  sign _ := Sign.neg
  weight _ _ := some 3
  weight_symm _ _ := rfl
  weight_ge_two _ _ _ h := by cases h; omega

lemma tildeAminus2_generators (i : Fin 3) :
    ReflectionSystem.reflectionMatrix tildeAminus2Graph.toBilinearForm i =
      (genZ i).map (Int.cast : ℤ → ℝ) := by
  rw [genZ_cast]
  fin_cases i <;> ext r c <;> fin_cases r <;> fin_cases c <;>
    simp [tildeAminus2Graph, MixedSignCoxeterGraph.toBilinearForm,
      ReflectionSystem.reflectionMatrix_apply, Sign.toReal, edgeEntry, Real.cos_pi_div_three,
      s1TildeAminus2, s2TildeAminus2, s3TildeAminus2] <;>
    norm_num

lemma evalZ_cast (w : List (Fin 3)) :
    tildeAminus2Graph.toReflectionSystem.wordProd w =
      (evalZ w).map (Int.cast : ℤ → ℝ) := by
  simp only [ReflectionSystem.wordProd, evalZ]
  induction w with
  | nil =>
    ext r c
    fin_cases r <;> fin_cases c <;> simp
  | cons a t ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [ih]
    -- `(A.map cast) * (B.map cast) = (A * B).map cast`
    have hmul :
        (genZ a).map (Int.cast : ℤ → ℝ) * (evalZ t).map (Int.cast : ℤ → ℝ) =
          (genZ a * evalZ t).map (Int.cast : ℤ → ℝ) := by
      ext r c
      simp [Matrix.mul_apply, Int.cast_sum, Int.cast_mul]
    dsimp only [MixedSignCoxeterGraph.toReflectionSystem]
    simp only [evalZ] at hmul
    rw [tildeAminus2_generators a, hmul]

/-- Delete the elements at indices `i` and `j` (`i < j`) from a list. -/
private def deleteTwo {α : Type*} (w : List α) (i j : ℕ) : List α :=
  (w.zipIdx.filter fun p => p.2 ≠ i ∧ p.2 ≠ j).map Prod.fst

private lemma evalZ_bad_eq_reduced :
    evalZ [0, 1, 0, 2, 0] = evalZ [2, 0, 1] := by
  decide

private lemma evalZ_bad_no_two_deletion :
    ∀ i j : Fin 5, i < j →
      evalZ (deleteTwo [0, 1, 0, 2, 0] i.val j.val) ≠ evalZ [0, 1, 0, 2, 0] := by
  decide

/-- **Lemma 3.21 & Theorem 1.2**: In `W(~A_{-2})`, the word `w = [0, 1, 0, 2, 0]` (length 5)
represents the same group element as `[2, 0, 1]` (length 3, so `w` is not reduced), yet
no deletion of two generators from `w` yields the same element. Hence `W(~A_{-2})` fails
the Deletion Property. -/
theorem tildeAminus2_fails_deletion :
    let S := tildeAminus2Graph.toReflectionSystem
    let w : List (Fin 3) := [0, 1, 0, 2, 0]
    S.wordProd w = S.wordProd [2, 0, 1] ∧
    ∀ i j : Fin 5, i < j → S.wordProd (deleteTwo w i.val j.val) ≠ S.wordProd w := by
  intro S w
  constructor
  · simp only [S, w, evalZ_cast, evalZ_bad_eq_reduced]
  · intro i j hij hEq
    have hZ := evalZ_bad_no_two_deletion i j hij
    apply hZ
    simp only [S, w, evalZ_cast] at hEq
    ext r c
    have hrc := congr_arg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M r c) hEq
    simp only [Matrix.map_apply] at hrc
    exact Int.cast_injective hrc

end DeletionFailure

/-! ### Theorem 1.6: Odd Cycles `~A_{-n}` vs `~A_n` -/

section OddCycles

/-- Bilinear form of the positive cycle `~A_{m-1}` on `m` nodes (`m ≥ 3`):
diagonal `2`, adjacent off-diagonal `-1`. -/
def cyclePosForm (m : ℕ) [NeZero m] : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun i j =>
    (if i = j then (2 : ℝ) else 0) -
    (if j = i + 1 then (1 : ℝ) else 0) -
    (if i = j + 1 then (1 : ℝ) else 0)

/-- Bilinear form of the negative cycle `~A_{-(m-1)}` on `m` nodes (`m ≥ 3`):
diagonal `-2`, adjacent off-diagonal `-1`. -/
def cycleNegForm (m : ℕ) [NeZero m] : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun i j =>
    -(if i = j then (2 : ℝ) else 0) -
    (if j = i + 1 then (1 : ℝ) else 0) -
    (if i = j + 1 then (1 : ℝ) else 0)

private lemma sum_shift_sq {m : ℕ} [NeZero m] (v : Fin m → ℝ) :
    ∑ i : Fin m, v (i + 1) ^ 2 = ∑ i : Fin m, v i ^ 2 :=
  Equiv.sum_comp (Equiv.addRight (1 : Fin m)) (fun i => v i ^ 2)

/-- Quadratic form identity for `~A_{m-1}`:
`∑ i j, v i * cyclePosForm m i j * v j = ∑ i, (v i - v (i + 1))^2`. -/
theorem cyclePosForm_quad (m : ℕ) [NeZero m] (v : Fin m → ℝ) :
    (∑ i : Fin m, ∑ j : Fin m, v i * cyclePosForm m i j * v j) =
      ∑ i : Fin m, (v i - v (i + 1)) ^ 2 := by
  have h1 : ∀ i : Fin m,
      ∑ j : Fin m, v i * cyclePosForm m i j * v j =
        2 * v i ^ 2 - v i * v (i + 1) - ∑ j : Fin m, (if i = j + 1 then v i * v j else 0) := by
    intro i
    simp only [cyclePosForm, Matrix.of_apply]
    have hsplit : ∀ j : Fin m,
        v i * ((if i = j then (2 : ℝ) else 0) - (if j = i + 1 then 1 else 0) -
          (if i = j + 1 then 1 else 0)) * v j =
        (if i = j then 2 * v i * v j else 0) -
        (if j = i + 1 then v i * v j else 0) -
        (if i = j + 1 then v i * v j else 0) := by
      intro j; split_ifs <;> ring
    simp_rw [hsplit, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq']
    simp only [Finset.mem_univ, ↓reduceIte]
    ring
  simp_rw [h1, Finset.sum_sub_distrib]
  have h3 : ∑ i : Fin m, ∑ j : Fin m, (if i = j + 1 then v i * v j else 0) =
      ∑ j : Fin m, v (j + 1) * v j := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp
  rw [h3]
  have hrhs : ∑ i : Fin m, (v i - v (i + 1)) ^ 2 =
      (∑ i : Fin m, v i ^ 2) + (∑ i : Fin m, v (i + 1) ^ 2) -
        2 * (∑ i : Fin m, v i * v (i + 1)) := by
    have hsq : ∀ i : Fin m, (v i - v (i + 1)) ^ 2 =
        v i ^ 2 + v (i + 1) ^ 2 - 2 * (v i * v (i + 1)) := fun i => by ring
    simp_rw [hsq, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hrhs, sum_shift_sq]
  have hcomm : ∑ j : Fin m, v (j + 1) * v j = ∑ i : Fin m, v i * v (i + 1) := by
    refine Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [hcomm]
  have h2v : ∑ i : Fin m, 2 * v i ^ 2 = (∑ i : Fin m, v i ^ 2) + (∑ i : Fin m, v i ^ 2) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => by ring
  rw [h2v]
  ring

/-- **Theorem 1.6 (part 1)**: `cyclePosForm m` is positive semidefinite and degenerate
(`1` is in its kernel). -/
theorem cyclePosForm_posSemidef (m : ℕ) [NeZero m] (v : Fin m → ℝ) :
    0 ≤ ∑ i : Fin m, ∑ j : Fin m, v i * cyclePosForm m i j * v j := by
  rw [cyclePosForm_quad]
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

theorem cyclePosForm_degenerate (m : ℕ) [NeZero m] :
    (∑ i : Fin m, ∑ j : Fin m, (1 : ℝ) * cyclePosForm m i j * 1) = 0 := by
  rw [cyclePosForm_quad]
  simp

/-- Quadratic form identity for `~A_{-(m-1)}`:
`∑ i j, v i * cycleNegForm m i j * v j = - ∑ i, (v i + v (i + 1))^2`. -/
theorem cycleNegForm_quad (m : ℕ) [NeZero m] (v : Fin m → ℝ) :
    (∑ i : Fin m, ∑ j : Fin m, v i * cycleNegForm m i j * v j) =
      -∑ i : Fin m, (v i + v (i + 1)) ^ 2 := by
  have h1 : ∀ i : Fin m,
      ∑ j : Fin m, v i * cycleNegForm m i j * v j =
        -(2 * v i ^ 2) - v i * v (i + 1) - ∑ j : Fin m, (if i = j + 1 then v i * v j else 0) := by
    intro i
    simp only [cycleNegForm, Matrix.of_apply]
    have hsplit : ∀ j : Fin m,
        v i * (-(if i = j then (2 : ℝ) else 0) - (if j = i + 1 then 1 else 0) -
          (if i = j + 1 then 1 else 0)) * v j =
        -(if i = j then 2 * v i * v j else 0) -
        (if j = i + 1 then v i * v j else 0) -
        (if i = j + 1 then v i * v j else 0) := by
      intro j; split_ifs <;> ring
    simp_rw [hsplit, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.sum_ite_eq,
      Finset.sum_ite_eq']
    simp only [Finset.mem_univ, ↓reduceIte]
    ring
  simp_rw [h1, Finset.sum_sub_distrib]
  have h3 : ∑ i : Fin m, ∑ j : Fin m, (if i = j + 1 then v i * v j else 0) =
      ∑ j : Fin m, v (j + 1) * v j := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp
  rw [h3]
  have hrhs : ∑ i : Fin m, (v i + v (i + 1)) ^ 2 =
      (∑ i : Fin m, v i ^ 2) + (∑ i : Fin m, v (i + 1) ^ 2) +
        2 * (∑ i : Fin m, v i * v (i + 1)) := by
    have hsq : ∀ i : Fin m, (v i + v (i + 1)) ^ 2 =
        v i ^ 2 + v (i + 1) ^ 2 + 2 * (v i * v (i + 1)) := fun i => by ring
    simp_rw [hsq, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hrhs, sum_shift_sq]
  have hcomm : ∑ j : Fin m, v (j + 1) * v j = ∑ i : Fin m, v i * v (i + 1) := by
    refine Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [hcomm, Finset.sum_neg_distrib]
  have h2v : ∑ i : Fin m, 2 * v i ^ 2 = (∑ i : Fin m, v i ^ 2) + (∑ i : Fin m, v i ^ 2) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => by ring
  rw [h2v]
  ring

/-- **Theorem 1.6 (part 2)**: For any odd cycle `~A_{-n}` (`m = n + 1` odd), `cycleNegForm m`
is strictly negative definite: `vᵀ B v < 0` for all `v ≠ 0`. -/
theorem oddCycleNegForm_negDef (m : ℕ) [NeZero m] (hm : Odd m) (v : Fin m → ℝ)
    (hv : v ≠ 0) :
    (∑ i : Fin m, ∑ j : Fin m, v i * cycleNegForm m i j * v j) < 0 := by
  rw [cycleNegForm_quad]
  have hnonneg : 0 ≤ ∑ i : Fin m, (v i + v (i + 1)) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  suffices hne : ∑ i : Fin m, (v i + v (i + 1)) ^ 2 ≠ 0 by
    have hpos : 0 < ∑ i : Fin m, (v i + v (i + 1)) ^ 2 :=
      lt_of_le_of_ne hnonneg (Ne.symm hne)
    linarith
  intro hzero
  have hall : ∀ i : Fin m, v i + v (i + 1) = 0 := by
    intro i
    have hsq : (v i + v (i + 1)) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg _)).mp hzero i (Finset.mem_univ i)
    exact sq_eq_zero_iff.mp hsq
  have hstep : ∀ k : ℕ, v (Fin.ofNat m k) = (-1 : ℝ) ^ k * v 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h := hall (Fin.ofNat m k)
      have hcast : Fin.ofNat m (k + 1) = Fin.ofNat m k + 1 := by
        ext
        simp [Fin.val_add]
      rw [hcast]
      have hneg : v (Fin.ofNat m k + 1) = -v (Fin.ofNat m k) := by linarith
      rw [hneg, ih, pow_succ]
      ring
  have hm0 : Fin.ofNat m m = 0 := by simp
  have hm_eq := hstep m
  rw [hm0, hm.neg_one_pow] at hm_eq
  have hv0 : v 0 = 0 := by linarith
  apply hv
  ext i
  have hi := hstep i.val
  simp only [Fin.ofNat_eq_cast, Fin.cast_val_eq_self] at hi
  rw [hi, hv0, mul_zero]
  rfl

end OddCycles

end MixedSignCoxeter

