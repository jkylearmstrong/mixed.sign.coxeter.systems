/-
Copyright (c) 2026 Johnathon Kyle Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Fin.VecNotation
import MixedSignCoxeter.Conjugacy
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
def deleteTwo {α : Type*} (w : List α) (i j : ℕ) : List α :=
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

/-- Extend `~A_{-2}` by `k` isolated positive nodes, producing an infinite family of mixed-sign
Coxeter graphs of rank `3 + k` (Theorem 1.2). -/
def tildeAminus2Extended (k : ℕ) : MixedSignCoxeterGraph (3 + k) where
  sign i := if i.val < 3 then Sign.neg else Sign.pos
  weight i j := if i.val < 3 ∧ j.val < 3 then some 3 else some 2
  weight_symm i j := by
    by_cases h1 : i.val < 3 <;> by_cases h2 : j.val < 3 <;> simp [h1, h2]
  weight_ge_two i j m h := by
    split_ifs at h <;> cases h <;> omega

private lemma tildeAminus2Extended_block (k : ℕ) (a : Fin 3) (r c : Fin 3) :
    ReflectionSystem.reflectionMatrix (tildeAminus2Extended k).toBilinearForm
        (Fin.castAdd k a) (Fin.castAdd k r) (Fin.castAdd k c) =
      ReflectionSystem.reflectionMatrix tildeAminus2Graph.toBilinearForm a r c := by
  simp [tildeAminus2Extended, tildeAminus2Graph, MixedSignCoxeterGraph.toBilinearForm,
    ReflectionSystem.reflectionMatrix_apply, a.isLt, r.isLt, c.isLt]

private lemma tildeAminus2Extended_offblock (k : ℕ) (a : Fin 3) (r : Fin 3) (c : Fin (3 + k))
    (hc : 3 ≤ c.val) :
    ReflectionSystem.reflectionMatrix (tildeAminus2Extended k).toBilinearForm
        (Fin.castAdd k a) (Fin.castAdd k r) c = 0 := by
  have hne : Fin.castAdd k r ≠ c := by
    intro h; have := congr_arg Fin.val h; simp at this; omega
  have hne2 : Fin.castAdd k a ≠ c := by
    intro h; have := congr_arg Fin.val h; simp at this; omega
  have hc_lt : ¬(c.val < 3) := by omega
  simp [tildeAminus2Extended, MixedSignCoxeterGraph.toBilinearForm,
    ReflectionSystem.reflectionMatrix_apply, hne, hne2, hc_lt, edgeEntry, Real.cos_pi_div_two]

private lemma tildeAminus2Extended_wordProd_block (k : ℕ) (w : List (Fin 3)) (r c : Fin 3) :
    (tildeAminus2Extended k).toReflectionSystem.wordProd (w.map (Fin.castAdd k))
        (Fin.castAdd k r) (Fin.castAdd k c) =
      tildeAminus2Graph.toReflectionSystem.wordProd w r c := by
  induction w generalizing r with
  | nil =>
    simp [ReflectionSystem.wordProd, Matrix.one_apply]
  | cons a t ih =>
    simp only [ReflectionSystem.wordProd, List.map_cons, List.prod_cons, Matrix.mul_apply]
    dsimp only [MixedSignCoxeterGraph.toReflectionSystem]
    rw [Fin.sum_univ_add]
    have hrest :
        (∑ x : Fin k,
          ReflectionSystem.reflectionMatrix (tildeAminus2Extended k).toBilinearForm
              (Fin.castAdd k a) (Fin.castAdd k r) (Fin.natAdd 3 x) *
            ((List.map (Fin.castAdd k) t).map
              (ReflectionSystem.reflectionMatrix
                (tildeAminus2Extended k).toBilinearForm)).prod
              (Fin.natAdd 3 x) (Fin.castAdd k c)) = 0 := by
      refine Finset.sum_eq_zero fun x _ => ?_
      have h0 : ReflectionSystem.reflectionMatrix (tildeAminus2Extended k).toBilinearForm
          (Fin.castAdd k a) (Fin.castAdd k r) (Fin.natAdd 3 x) = 0 :=
        tildeAminus2Extended_offblock k a r (Fin.natAdd 3 x) (by simp)
      rw [h0, zero_mul]
    rw [hrest, add_zero]
    refine Finset.sum_congr rfl fun x _ => ?_
    have hih := ih x
    simp only [ReflectionSystem.wordProd, MixedSignCoxeterGraph.toReflectionSystem] at hih
    rw [tildeAminus2Extended_block, hih]

private lemma tildeAminus2Extended_row_ge (k : ℕ) (a : Fin 3) (r c : Fin (3 + k))
    (hr : 3 ≤ r.val) :
    ReflectionSystem.reflectionMatrix (tildeAminus2Extended k).toBilinearForm
        (Fin.castAdd k a) r c = if r = c then 1 else 0 := by
  have hne : r ≠ Fin.castAdd k a := by
    intro h; have := congr_arg Fin.val h; simp at this; omega
  simp [ReflectionSystem.reflectionMatrix_apply, hne]

private lemma tildeAminus2Extended_col_ge (k : ℕ) (a : Fin 3) (r c : Fin (3 + k))
    (hc : 3 ≤ c.val) :
    ReflectionSystem.reflectionMatrix (tildeAminus2Extended k).toBilinearForm
        (Fin.castAdd k a) r c = if r = c then 1 else 0 := by
  by_cases hrc : r = c
  · subst hrc
    have hne : r ≠ Fin.castAdd k a := by
      intro h; have := congr_arg Fin.val h; simp at this; omega
    simp [ReflectionSystem.reflectionMatrix_apply, hne]
  · have hne_ac : Fin.castAdd k a ≠ c := by
      intro h; have := congr_arg Fin.val h; simp at this; omega
    have hnc : ¬(c.val < 3) := by omega
    simp [tildeAminus2Extended, MixedSignCoxeterGraph.toBilinearForm,
      ReflectionSystem.reflectionMatrix_apply, hrc, hne_ac, hnc, edgeEntry, Real.cos_pi_div_two]

private lemma tildeAminus2Extended_wordProd_row_ge (k : ℕ) (w : List (Fin 3))
    (r c : Fin (3 + k)) (hr : 3 ≤ r.val) :
    (tildeAminus2Extended k).toReflectionSystem.wordProd (w.map (Fin.castAdd k)) r c =
      if r = c then 1 else 0 := by
  induction w generalizing r with
  | nil => simp [ReflectionSystem.wordProd, Matrix.one_apply]
  | cons a t ih =>
    simp only [ReflectionSystem.wordProd, List.map_cons, List.prod_cons, Matrix.mul_apply]
    dsimp only [MixedSignCoxeterGraph.toReflectionSystem]
    have hrow : ∀ x : Fin (3 + k),
        ReflectionSystem.reflectionMatrix (tildeAminus2Extended k).toBilinearForm
            (Fin.castAdd k a) r x *
          ((List.map (Fin.castAdd k) t).map
            (ReflectionSystem.reflectionMatrix
              (tildeAminus2Extended k).toBilinearForm)).prod x c =
        if r = x then
          ((List.map (Fin.castAdd k) t).map
            (ReflectionSystem.reflectionMatrix
              (tildeAminus2Extended k).toBilinearForm)).prod x c
        else 0 := by
      intro x
      rw [tildeAminus2Extended_row_ge k a r x hr]
      split_ifs <;> simp
    rw [Finset.sum_congr rfl fun x _ => hrow x]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    exact ih r hr

private lemma tildeAminus2Extended_wordProd_col_ge (k : ℕ) (w : List (Fin 3))
    (r c : Fin (3 + k)) (hc : 3 ≤ c.val) :
    (tildeAminus2Extended k).toReflectionSystem.wordProd (w.map (Fin.castAdd k)) r c =
      if r = c then 1 else 0 := by
  induction w generalizing r with
  | nil => simp [ReflectionSystem.wordProd, Matrix.one_apply]
  | cons a t ih =>
    simp only [ReflectionSystem.wordProd, List.map_cons, List.prod_cons, Matrix.mul_apply]
    dsimp only [MixedSignCoxeterGraph.toReflectionSystem]
    have hcol : ∀ x : Fin (3 + k),
        ReflectionSystem.reflectionMatrix (tildeAminus2Extended k).toBilinearForm
            (Fin.castAdd k a) r x *
          ((List.map (Fin.castAdd k) t).map
            (ReflectionSystem.reflectionMatrix
              (tildeAminus2Extended k).toBilinearForm)).prod x c =
        if x = c then
          ReflectionSystem.reflectionMatrix (tildeAminus2Extended k).toBilinearForm
            (Fin.castAdd k a) r x
        else 0 := by
      intro x
      have hx := ih x
      simp only [ReflectionSystem.wordProd] at hx
      dsimp only [MixedSignCoxeterGraph.toReflectionSystem] at hx
      rw [hx]
      split_ifs <;> simp
    rw [Finset.sum_congr rfl fun x _ => hcol x]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    exact tildeAminus2Extended_col_ge k a r c hc

/-- **Theorem 1.2**: There exists an infinite family of mixed-sign Coxeter systems
(`tildeAminus2Extended k` for every `k : ℕ`, rank `3 + k`) that do not satisfy the Deletion Property:
for each `k`, `w' = [0, 1, 0, 2, 0].map (Fin.castAdd k)` equals `[2, 0, 1].map (Fin.castAdd k)`,
yet no two-letter deletion from `w'` equals `w'`. -/
theorem theorem_1_2_infinite_family (k : ℕ) :
    let S := (tildeAminus2Extended k).toReflectionSystem
    let w : List (Fin (3 + k)) := [0, 1, 0, 2, 0].map (Fin.castAdd k)
    S.wordProd w = S.wordProd ([2, 0, 1].map (Fin.castAdd k)) ∧
    ∀ i j : Fin 5, i < j → S.wordProd (deleteTwo w i.val j.val) ≠ S.wordProd w := by
  intro S w
  have hbase := tildeAminus2_fails_deletion
  constructor
  · ext r c
    by_cases hr : r.val < 3
    · by_cases hc : c.val < 3
      · have hr' : r = Fin.castAdd k ⟨r.val, hr⟩ := by ext; rfl
        have hc' : c = Fin.castAdd k ⟨c.val, hc⟩ := by ext; rfl
        rw [hr', hc']
        simp only [S, w, tildeAminus2Extended_wordProd_block]
        exact congr_fun (congr_fun hbase.1 ⟨r.val, hr⟩) ⟨c.val, hc⟩
      · have hc' : 3 ≤ c.val := Nat.le_of_not_lt hc
        simp only [S, w, tildeAminus2Extended_wordProd_col_ge k _ r c hc']
    · have hr' : 3 ≤ r.val := Nat.le_of_not_lt hr
      simp only [S, w, tildeAminus2Extended_wordProd_row_ge k _ r c hr']
  · intro i j hij hEq
    apply hbase.2 i j hij
    ext r c
    have hdel : deleteTwo (([0, 1, 0, 2, 0] : List (Fin 3)).map (Fin.castAdd k)) i.val j.val =
        (deleteTwo ([0, 1, 0, 2, 0] : List (Fin 3)) i.val j.val).map (Fin.castAdd k) := by
      fin_cases i <;> fin_cases j <;> simp [deleteTwo]
    have hrc := congr_arg (fun M : Matrix (Fin (3 + k)) (Fin (3 + k)) ℝ =>
      M (Fin.castAdd k r) (Fin.castAdd k c)) hEq
    simp only [S, w, hdel, tildeAminus2Extended_wordProd_block] at hrc
    exact hrc

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

/-- **Theorem 1.6 (non-conjugacy)**: For any odd cycle length `m` (`~A_{-n}` with `n = m - 1` even),
`cyclePosForm m` and `± cycleNegForm m` are not `𝒪`-conjugate. -/
theorem oddCycle_not_O_conjugate (m : ℕ) [NeZero m] (hm : Odd m) :
    (¬ ∃ P : ReflectionSystem.SignedPerm m,
      P.toMatrixᵀ * cyclePosForm m * P.toMatrix = cycleNegForm m) ∧
    (¬ ∃ P : ReflectionSystem.SignedPerm m,
      P.toMatrixᵀ * cyclePosForm m * P.toMatrix = -cycleNegForm m) := by
  have hdot : ∀ (P : ReflectionSystem.SignedPerm m),
      let v : Fin m → ℝ := P.toMatrixᵀ.mulVec (fun _ => 1)
      v ≠ 0 ∧
      (∑ i : Fin m, ∑ j : Fin m, v i * (P.toMatrixᵀ * cyclePosForm m * P.toMatrix) i j * v j) = 0 := by
    intro P v
    have hPv : P.toMatrix.mulVec v = (fun _ => 1) := by
      dsimp only [v]
      have hPP : P.toMatrix * P.toMatrixᵀ = 1 := by
        ext r c
        simp only [Matrix.mul_apply, Matrix.transpose_apply,
          ReflectionSystem.SignedPerm.toMatrix_apply, Matrix.one_apply]
        have hsum : ∀ x : Fin m,
            (if r = P.perm x then P.signReal x else 0) *
              (if c = P.perm x then P.signReal x else 0) =
            if x = P.perm.symm r then (if r = c then 1 else 0) else 0 := by
          intro x
          by_cases hx : x = P.perm.symm r
          · subst hx
            simp only [Equiv.apply_symm_apply, ↓reduceIte]
            by_cases hrc : r = c
            · subst hrc; simp
            · simp [hrc, Ne.symm hrc]
          · have hne : r ≠ P.perm x := fun h => hx (P.perm.eq_symm_apply.mpr h.symm)
            simp [hx, hne]
        rw [Finset.sum_congr rfl fun x _ => hsum x]
        simp
      rw [Matrix.mulVec_mulVec, hPP, Matrix.one_mulVec]
    have hv : v ≠ 0 := by
      intro h0
      have h1 : P.toMatrix.mulVec 0 = (fun _ => 1) := by rw [← h0, hPv]
      rw [Matrix.mulVec_zero] at h1
      have h00 := congr_fun h1 0
      simp at h00
    refine ⟨hv, ?_⟩
    have hquad_dot : ∀ M : Matrix (Fin m) (Fin m) ℝ,
        (∑ i : Fin m, ∑ j : Fin m, v i * M i j * v j) = dotProduct v (M.mulVec v) := by
      intro M
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    have hdot_transpose : ∀ u : Fin m → ℝ,
        dotProduct v (P.toMatrixᵀ.mulVec u) = dotProduct (P.toMatrix.mulVec v) u := by
      intro u
      simp only [dotProduct, Matrix.mulVec, Matrix.transpose_apply, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
    have hmul : ∀ (A B : Matrix (Fin m) (Fin m) ℝ) (x : Fin m → ℝ),
        (A * B).mulVec x = A.mulVec (B.mulVec x) := fun A B x => (Matrix.mulVec_mulVec x A B).symm
    have hquad_eq :
        (∑ i : Fin m, ∑ j : Fin m, v i * (P.toMatrixᵀ * cyclePosForm m * P.toMatrix) i j * v j) =
          dotProduct (P.toMatrix.mulVec v) ((cyclePosForm m).mulVec (P.toMatrix.mulVec v)) := by
      calc (∑ i : Fin m, ∑ j : Fin m, v i * (P.toMatrixᵀ * cyclePosForm m * P.toMatrix) i j * v j)
          = dotProduct v ((P.toMatrixᵀ * cyclePosForm m * P.toMatrix).mulVec v) := hquad_dot _
        _ = dotProduct v (P.toMatrixᵀ.mulVec ((cyclePosForm m).mulVec (P.toMatrix.mulVec v))) := by
              rw [Matrix.mul_assoc, hmul P.toMatrixᵀ (cyclePosForm m * P.toMatrix) v,
                hmul (cyclePosForm m) P.toMatrix v]
        _ = dotProduct (P.toMatrix.mulVec v) ((cyclePosForm m).mulVec (P.toMatrix.mulVec v)) :=
              hdot_transpose _
    rw [hquad_eq, hPv]
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    simpa [one_mul, mul_one] using cyclePosForm_degenerate m
  constructor
  · rintro ⟨P, hP⟩
    obtain ⟨hv, hzero⟩ := hdot P
    rw [hP] at hzero
    have hneg := oddCycleNegForm_negDef m hm (P.toMatrixᵀ.mulVec (fun _ => 1)) hv
    linarith
  · rintro ⟨P, hP⟩
    obtain ⟨hv, hzero⟩ := hdot P
    rw [hP] at hzero
    have hneg := oddCycleNegForm_negDef m hm (P.toMatrixᵀ.mulVec (fun _ => 1)) hv
    have hneg2 : (∑ i : Fin m, ∑ j : Fin m,
        (P.toMatrixᵀ.mulVec (fun _ => 1)) i * (-cycleNegForm m) i j *
          (P.toMatrixᵀ.mulVec (fun _ => 1)) j) =
        -(∑ i : Fin m, ∑ j : Fin m,
        (P.toMatrixᵀ.mulVec (fun _ => 1)) i * cycleNegForm m i j *
          (P.toMatrixᵀ.mulVec (fun _ => 1)) j) := by
      simp only [Matrix.neg_apply, mul_neg, neg_mul, Finset.sum_neg_distrib]
    linarith

/-! ### Lemma 3.25: Infinite Order in `W(Ã₂)` vs. Finite Order in `W(Ã₋₂)` -/

/-- Integer generating reflections for classical `Ã₂(+, +, +)`. -/
def sA2TildeZ : Fin 3 → Matrix (Fin 3) (Fin 3) ℤ
  | 0 => !![-1, 1, 1; 0, 1, 0; 0, 0, 1]
  | 1 => !![1, 0, 0; 1, -1, 1; 0, 0, 1]
  | 2 => !![1, 0, 0; 0, 1, 0; 1, 1, -1]

def wA2TildeSqZ : Matrix (Fin 3) (Fin 3) ℤ :=
  (sA2TildeZ 0 * sA2TildeZ 1 * sA2TildeZ 2) ^ 2

def diffA2TildeZ : Matrix (Fin 3) (Fin 3) ℤ :=
  wA2TildeSqZ - 1

private lemma diffA2TildeZ_sq : diffA2TildeZ * diffA2TildeZ = 0 := by decide

private lemma wA2TildeSqZ_eq : wA2TildeSqZ = 1 + diffA2TildeZ := by
  simp [diffA2TildeZ]

/-- **Lemma 3.25**: In `W(Ã₂)`, `((s₀ s₁ s₂)^2)^k = I + k • (w² - I)`, so `(s₀ s₁ s₂)^(2k) ≠ 1`
for all `k ≥ 1`. Combined with `tildeAminus2_principal_order_four` (and `|W(Ã₋₂)| = 24`),
`W(Ã₂)` has infinite order while `W(Ã₋₂)` is finite. -/
theorem wA2TildeSqZ_pow (k : ℕ) :
    wA2TildeSqZ ^ k = 1 + (k : ℤ) • diffA2TildeZ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, wA2TildeSqZ_eq]
    simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm,
      diffA2TildeZ_sq, smul_zero, add_zero]
    push_cast
    rw [add_smul, one_smul]
    abel

theorem tildeA2_infinite_order (k : ℕ) (hk : 1 ≤ k) :
    (sA2TildeZ 0 * sA2TildeZ 1 * sA2TildeZ 2) ^ (2 * k) ≠ 1 := by
  intro h
  have hsq : wA2TildeSqZ ^ k = 1 := by
    simpa [wA2TildeSqZ, pow_mul] using h
  rw [wA2TildeSqZ_pow] at hsq
  have h00 := congr_fun (congr_fun hsq 0) 0
  have hd00 : diffA2TildeZ 0 0 = 3 := by decide
  simp only [Matrix.add_apply, Matrix.one_apply, ↓reduceIte, Matrix.smul_apply, hd00,
    smul_eq_mul] at h00
  omega

end OddCycles

end MixedSignCoxeter

