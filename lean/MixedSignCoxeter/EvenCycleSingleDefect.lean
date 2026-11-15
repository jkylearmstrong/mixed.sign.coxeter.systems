/-
Copyright (c) 2026 Johnathon Kyle Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MixedSignCoxeter.Howlett
import Mathlib.Topology.Order.IntermediateValue

/-!
# Even Cycles with a Single Positive Vertex $C_{2m}(+, -, \dots, -)$

Proves the even-cycle counterpart to `OddCycleSingleDefect.lean` for all $m \ge 2$
($k = 2m \ge 4$):
* `evenCycleSinglePlus_charpoly_at_neg_one`: $\det(-I - w) = -4 < 0$.
* `evenCycleSinglePlus_charpoly_at_neg_five`: $\det(-5I - w) > 0$.
* `evenCycleSinglePlus_has_eigenvalue_lt_neg_one`: the principal element
  $w = s_0 s_1 \cdots s_{2m-1}$ has a real eigenvalue $\mu \in (-5, -1)$, hence
  $|\mu| > 1$ (hyperbolic, contrasting with $\rho(w) = 1$ on odd cycles $C_{2m+1}(+,-,\dots,-)$).
-/

open Matrix ReflectionSystem

namespace MixedSignCoxeter

section EvenCycleSingleDefect

/-- Bilinear form of the even cycle $C_{2m}(+, -, \dots, -)$: vertex $0$ has diagonal $+2$,
vertices $1, \dots, 2m-1$ have diagonal $-2$, and adjacent vertices mod $2m$ have
off-diagonal $-1$. -/
def B_evenCycleSinglePlus (m : ℕ) : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ :=
  Matrix.of fun i j =>
    if i = j then (if i.val = 0 then 2 else -2)
    else if (i.val + 1 = j.val ∨ j.val + 1 = i.val ∨
        (i.val = 0 ∧ j.val = 2 * m - 1) ∨ (j.val = 0 ∧ i.val = 2 * m - 1)) then -1
    else 0

/-- `B_evenCycleSinglePlus m` defines a valid `ReflectionSystem (2 * m)` for `m ≥ 2`. -/
def evenCycleSinglePlusSystem (m : ℕ) (_hm : 2 ≤ m) : ReflectionSystem (2 * m) where
  B := B_evenCycleSinglePlus m
  B_symm := by
    ext i j
    simp only [transpose_apply, B_evenCycleSinglePlus, of_apply]
    by_cases hij : i = j
    · subst hij; simp
    · have hji : j ≠ i := Ne.symm hij
      simp only [hij, hji, ↓reduceIte]
      by_cases hadj : i.val + 1 = j.val ∨ j.val + 1 = i.val ∨
          (i.val = 0 ∧ j.val = 2 * m - 1) ∨ (j.val = 0 ∧ i.val = 2 * m - 1)
      · split_ifs <;> first | rfl | (exfalso; tauto)
      · split_ifs <;> first | rfl | (exfalso; tauto)
  B_diag_ne_zero := by
    intro i
    simp only [B_evenCycleSinglePlus, of_apply, ↓reduceIte]
    split_ifs <;> norm_num

/-- Principal Coxeter element `w = s_0 * s_1 * ... * s_{2m-1}` of `C_{2m}(+, -, ..., -)`. -/
noncomputable def w_evenCycleSinglePlus (m : ℕ) (hm : 2 ≤ m) :
    Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ :=
  principalElement (evenCycleSinglePlusSystem m hm)

private lemma howlettU_evenCycle_det (m : ℕ) (hm : 2 ≤ m) :
    (howlettU (evenCycleSinglePlusSystem m hm).B).det = -1 := by
  have : NeZero (2 * m) := ⟨by omega⟩
  rw [howlettU_det]
  have hprod : (∏ i : Fin (2 * m), (evenCycleSinglePlusSystem m hm).B i i / 2) =
      ∏ i : Fin (2 * m), if i = (0 : Fin (2 * m)) then (1 : ℝ) else (-1 : ℝ) := by
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [evenCycleSinglePlusSystem, B_evenCycleSinglePlus, of_apply, ↓reduceIte,
      Fin.ext_iff]
    split_ifs <;> (simp only [Fin.val_zero] at *; first | omega | norm_num)
  rw [hprod, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (0 : Fin (2 * m)))]
  simp only [↓reduceIte, one_mul]
  have hrest : ∀ i ∈ Finset.univ.erase (0 : Fin (2 * m)),
      (if i = (0 : Fin (2 * m)) then (1 : ℝ) else (-1 : ℝ)) = -1 :=
    fun i hi => if_neg (Finset.ne_of_mem_erase hi)
  rw [Finset.prod_congr rfl hrest, Finset.prod_const]
  have hcard : (Finset.univ.erase (0 : Fin (2 * m))).card = 2 * m - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_fin]
  rw [hcard]
  have hpow : (-1 : ℝ) ^ (2 * m - 1) = -1 := by
    have hsplit : 2 * m - 1 = 2 * (m - 1) + 1 := by omega
    rw [hsplit, pow_add, pow_mul]
    norm_num
  exact hpow

private lemma det_add_smul_row {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (i j : Fin n) (hij : i ≠ j) (c : ℝ) :
    Matrix.det (Function.update M i (M i + c • M j)) = M.det := by
  change (Matrix.updateRow M i (M i + c • M j)).det = M.det
  rw [Matrix.det_updateRow_add, Matrix.det_updateRow_smul]
  have hzero : (Matrix.updateRow M i (M j)).det = 0 :=
    Matrix.det_zero_of_row_eq hij (by ext k; simp [Matrix.updateRow, Function.update, hij.symm])
  simp [hzero]

private lemma det_add_smul_col {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (i j : Fin n) (hij : i ≠ j) (c : ℝ) :
    (Matrix.of fun r s => if s = i then M r i + c * M r j else M r s).det = M.det := by
  have hT : (Matrix.of fun r s => if s = i then M r i + c * M r j else M r s)ᵀ =
      Function.update Mᵀ i (Mᵀ i + c • Mᵀ j) := by
    ext r s
    simp only [transpose_apply, of_apply, Function.update]
    by_cases hr : r = i
    · subst hr; simp
    · simp [hr]
  rw [← Matrix.det_transpose, hT, det_add_smul_row Mᵀ i j hij c, Matrix.det_transpose]

private lemma det_eq_single_row_zero {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (k : Fin (n + 1)) (hk : ∀ j : Fin (n + 1), j ≠ k → M 0 j = 0) :
    M.det = (-1 : ℝ) ^ (k : ℕ) * M 0 k * (M.submatrix Fin.succ k.succAbove).det := by
  rw [Matrix.det_succ_row_zero]
  refine Finset.sum_eq_single k (fun j _ hjk => ?_) (fun hkmem => absurd (Finset.mem_univ k) hkmem)
  simp [hk j hjk]

private lemma det_eq_single_col_zero {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (k : Fin (n + 1)) (hk : ∀ i : Fin (n + 1), i ≠ k → M i 0 = 0) :
    M.det = (-1 : ℝ) ^ (k : ℕ) * M k 0 * (M.submatrix k.succAbove Fin.succ).det := by
  rw [← Matrix.det_transpose, det_eq_single_row_zero Mᵀ k (fun j hj => hk j hj)]
  simp only [transpose_apply]
  have hsub : (Mᵀ.submatrix Fin.succ k.succAbove) = (M.submatrix k.succAbove Fin.succ)ᵀ := by
    ext i j; simp
  rw [hsub, Matrix.det_transpose]

private lemma det_eq_single_row_last {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (k : Fin (n + 1)) (hk : ∀ j : Fin (n + 1), j ≠ k → M (Fin.last n) j = 0) :
    M.det = (-1 : ℝ) ^ (n + (k : ℕ)) * M (Fin.last n) k *
      (M.submatrix Fin.castSucc k.succAbove).det := by
  rw [Matrix.det_succ_row M (Fin.last n)]
  simp only [Fin.val_last, Fin.succAbove_last]
  refine Finset.sum_eq_single k (fun j _ hjk => ?_) (fun hkmem => absurd (Finset.mem_univ k) hkmem)
  simp [hk j hjk]

private lemma det_eq_single_col_last {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (k : Fin (n + 1)) (hk : ∀ i : Fin (n + 1), i ≠ k → M i (Fin.last n) = 0) :
    M.det = (-1 : ℝ) ^ (n + (k : ℕ)) * M k (Fin.last n) *
      (M.submatrix k.succAbove Fin.castSucc).det := by
  rw [← Matrix.det_transpose, det_eq_single_row_last Mᵀ k (fun j hj => hk j hj)]
  simp only [transpose_apply]
  have hsub : (Mᵀ.submatrix Fin.castSucc k.succAbove) = (M.submatrix k.succAbove Fin.castSucc)ᵀ := by
    ext i j; simp
  rw [hsub, Matrix.det_transpose]

/-- Skew-symmetric tridiagonal matrix of size `n` with `0` diagonal, `+1` superdiagonal,
and `-1` subdiagonal. -/
private def skewTridiag (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j =>
    if i.val + 1 = j.val then 1 else if j.val + 1 = i.val then -1 else 0

private lemma det_skewTridiag_even : ∀ r : ℕ, (skewTridiag (2 * r)).det = 1
  | 0 => by simp
  | r + 1 => by
    have h2r : 2 * (r + 1) = (2 * r + 1) + 1 := by omega
    let M := skewTridiag (2 * (r + 1))
    have hrow0 : ∀ j : Fin (2 * (r + 1)), j ≠ ⟨1, by omega⟩ → M 0 j = 0 := by
      intro j hj
      simp only [M, skewTridiag, of_apply, Fin.val_zero, zero_add]
      have hj1 : (1 : ℕ) ≠ j.val := fun h => hj (Fin.ext h.symm)
      simp [hj1]
    have h1 := det_eq_single_row_zero M ⟨1, by omega⟩ hrow0
    have hM01 : M 0 ⟨1, by omega⟩ = 1 := by
      simp [M, skewTridiag, Nat.mod_eq_of_lt (by omega : 1 < 2 * (r + 1))]
    rw [hM01, Fin.val_mk, pow_one, mul_one] at h1
    let N := M.submatrix Fin.succ (Fin.succAbove ⟨1, by omega⟩)
    have hcol0 : ∀ i : Fin (2 * r + 1), i ≠ 0 → N i 0 = 0 := by
      intro i hi
      simp only [N, submatrix_apply, Fin.val_succ, M, skewTridiag, of_apply]
      have hsucc : (Fin.succAbove ⟨1, by omega⟩ (0 : Fin (2 * r + 1))).val = 0 := by
        simp [Fin.succAbove]
      rw [hsucc]
      have hi0 : i.val ≠ 0 := fun h => hi (Fin.ext h)
      simp [hi0]
    have h2 := det_eq_single_col_zero N 0 hcol0
    have hN00 : N 0 0 = -1 := by
      simp only [N, submatrix_apply, Fin.succ_zero_eq_one, M, skewTridiag, of_apply]
      have hsucc : (Fin.succAbove ⟨1, by omega⟩ (0 : Fin (2 * r + 1))).val = 0 := by
        simp [Fin.succAbove]
      rw [hsucc]
      simp [Nat.mod_eq_of_lt (by omega : 1 < 2 * (r + 1))]
    rw [hN00, Fin.val_zero, pow_zero, one_mul] at h2
    have hsub : N.submatrix (Fin.succAbove 0) Fin.succ = skewTridiag (2 * r) := by
      ext i j
      simp only [N, submatrix_apply, Fin.succAbove_zero, M, skewTridiag, of_apply]
      have hsucc : (Fin.succAbove ⟨1, by omega⟩ j.succ).val = j.val + 2 := by
        simp only [Fin.succAbove]
        split_ifs with h
        · exfalso; simp [Fin.lt_def] at h
        · simp
      rw [hsucc]
      simp only [Fin.val_succ]
      split_ifs <;> first | rfl | omega
    rw [hsub, det_skewTridiag_even r] at h2
    rw [h1, h2]
    ring

/-- Auxiliary matrix for `M(-1) = -1 • U + Uᵀ` on `C_{2m}(+,-,...,-)`:
skew-symmetric with `0` diagonal, `+1` superdiagonal & `(0, 2m-1)`, `-1` subdiagonal & `(2m-1, 0)`. -/
private def matNegOne (m : ℕ) : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ :=
  Matrix.of fun i j =>
    if i.val + 1 = j.val ∨ (i.val = 0 ∧ j.val = 2 * m - 1) then 1
    else if j.val + 1 = i.val ∨ (j.val = 0 ∧ i.val = 2 * m - 1) then -1
    else 0

private lemma howlett_neg_one_eq (m : ℕ) (hm : 2 ≤ m) :
    (-1 : ℝ) • howlettU (evenCycleSinglePlusSystem m hm).B +
      (howlettU (evenCycleSinglePlusSystem m hm).B)ᵀ = matNegOne m := by
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, transpose_apply, howlettU_apply,
    evenCycleSinglePlusSystem, B_evenCycleSinglePlus, of_apply, matNegOne]
  by_cases hij : i = j
  · subst hij
    have hi_ne : ¬(i.val + 1 = i.val ∨ (i.val = 0 ∧ i.val = 2 * m - 1)) := by omega
    simp only [lt_self_iff_false, ↓reduceIte, hi_ne, or_self]
    split_ifs <;> norm_num
  · rcases lt_trichotomy i j with hlt | heq | hgt
    · have hgt' : ¬(j < i) := not_lt_of_gt hlt
      have hji : j ≠ i := Ne.symm hij
      have hi_lt : i.val < j.val := hlt
      have hno2 : ¬(j.val + 1 = i.val ∨ (j.val = 0 ∧ i.val = 2 * m - 1)) := by omega
      simp only [hlt, hgt', hij, hji, ↓reduceIte, hno2]
      by_cases hadj : i.val + 1 = j.val ∨ (i.val = 0 ∧ j.val = 2 * m - 1)
      · have hadj' : i.val + 1 = j.val ∨ j.val + 1 = i.val ∨
            (i.val = 0 ∧ j.val = 2 * m - 1) ∨ (j.val = 0 ∧ i.val = 2 * m - 1) := by tauto
        simp [hadj, hadj']
      · have hadj' : ¬(i.val + 1 = j.val ∨ j.val + 1 = i.val ∨
            (i.val = 0 ∧ j.val = 2 * m - 1) ∨ (j.val = 0 ∧ i.val = 2 * m - 1)) := by omega
        simp [hadj, hadj']
    · exact absurd heq hij
    · have hlt' : ¬(i < j) := not_lt_of_gt hgt
      have hji : j ≠ i := Ne.symm hij
      have hj_lt : j.val < i.val := hgt
      have hno1 : ¬(i.val + 1 = j.val ∨ (i.val = 0 ∧ j.val = 2 * m - 1)) := by omega
      simp only [hlt', hgt, hij, hji, ↓reduceIte, hno1]
      by_cases hadj : j.val + 1 = i.val ∨ (j.val = 0 ∧ i.val = 2 * m - 1)
      · simp only [hadj, ↓reduceIte]
        split_ifs <;> first | rfl | (norm_num; try omega) | tauto
      · simp only [hadj, ↓reduceIte]
        split_ifs <;> first | rfl | (norm_num; try omega) | tauto

private lemma det_matNegOne (m : ℕ) (hm : 2 ≤ m) : (matNegOne m).det = 4 := by
  have : NeZero (2 * m) := ⟨by omega⟩
  -- Step 1: Add rows 2, 4, ..., 2*m - 2 to row 0.
  let row0 : Fin (2 * m) → ℝ := fun j => if j.val = 2 * m - 1 then 2 else 0
  let M1 : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ := (matNegOne m).updateRow 0 row0
  let rowF : ℕ → (Fin (2 * m) → ℝ) := fun k =>
    if hk : 2 * k < 2 * m then matNegOne m ⟨2 * k, hk⟩ else 0
  have hM1_det : M1.det = (matNegOne m).det := by
    have hind : ∀ t : ℕ, t ≤ m - 1 →
        Matrix.det ((matNegOne m).updateRow 0
          (matNegOne m 0 + ∑ k ∈ Finset.Ico 1 (t + 1), rowF k)) =
          (matNegOne m).det := by
      intro t ht
      induction t with
      | zero =>
        simp only [zero_add, Finset.Ico_self, Finset.sum_empty, add_zero]
        have h0 : (matNegOne m).updateRow 0 (matNegOne m 0) = matNegOne m := by
          ext r s; simp only [Matrix.updateRow_apply]; by_cases hr : r = 0 <;> simp [hr]
        rw [h0]
      | succ t ih =>
        have hsum : ∑ k ∈ Finset.Ico 1 (t + 1 + 1), rowF k =
            (∑ k ∈ Finset.Ico 1 (t + 1), rowF k) + rowF (t + 1) := by
          rw [Finset.sum_Ico_succ_top (by omega)]
        rw [hsum, ← add_assoc]
        have hlt : 2 * (t + 1) < 2 * m := by omega
        have hrowF : rowF (t + 1) = matNegOne m ⟨2 * (t + 1), hlt⟩ := dif_pos hlt
        rw [hrowF]
        have hne : (0 : Fin (2 * m)) ≠ ⟨2 * (t + 1), hlt⟩ := by
          simp [Fin.ext_iff]
        have hupd : (matNegOne m).updateRow 0
            (matNegOne m 0 + ∑ k ∈ Finset.Ico 1 (t + 1), rowF k +
              matNegOne m ⟨2 * (t + 1), hlt⟩) =
            ((matNegOne m).updateRow 0
                (matNegOne m 0 + ∑ k ∈ Finset.Ico 1 (t + 1), rowF k)).updateRow
              0
              (((matNegOne m).updateRow 0
                (matNegOne m 0 + ∑ k ∈ Finset.Ico 1 (t + 1), rowF k)) 0 +
                (1 : ℝ) • ((matNegOne m).updateRow 0
                  (matNegOne m 0 + ∑ k ∈ Finset.Ico 1 (t + 1), rowF k))
                  ⟨2 * (t + 1), hlt⟩) := by
          ext i j
          simp only [Matrix.updateRow_apply]
          by_cases hi : i = 0
          · subst hi; simp [hne, hne.symm]
          · simp [hi]
        have hstep : (((matNegOne m).updateRow 0 (matNegOne m 0 + ∑ k ∈ Finset.Ico 1 (t + 1), rowF k)).updateRow 0
            (((matNegOne m).updateRow 0 (matNegOne m 0 + ∑ k ∈ Finset.Ico 1 (t + 1), rowF k)) 0 +
              (1 : ℝ) • ((matNegOne m).updateRow 0 (matNegOne m 0 + ∑ k ∈ Finset.Ico 1 (t + 1), rowF k))
                ⟨2 * (t + 1), hlt⟩)).det =
            ((matNegOne m).updateRow 0 (matNegOne m 0 + ∑ k ∈ Finset.Ico 1 (t + 1), rowF k)).det :=
          det_add_smul_row
            ((matNegOne m).updateRow 0 (matNegOne m 0 + ∑ k ∈ Finset.Ico 1 (t + 1), rowF k))
            0 ⟨2 * (t + 1), hlt⟩ hne 1
        rw [hupd, hstep, ih (by omega)]
    have hfull := hind (m - 1) (le_refl _)
    have hrow_eq : matNegOne m 0 + ∑ k ∈ Finset.Ico 1 (m - 1 + 1), rowF k = row0 := by
      ext j
      simp only [Pi.add_apply, Finset.sum_apply, row0]
      have hm1 : m - 1 + 1 = m := by omega
      rw [hm1]
      have hcongr : ∑ k ∈ Finset.Ico 1 m, rowF k j =
          ∑ k ∈ Finset.Ico 1 m,
            (if 2 * k + 1 = j.val ∨ (2 * k = 0 ∧ j.val = 2 * m - 1) then (1 : ℝ)
             else if j.val + 1 = 2 * k ∨ (j.val = 0 ∧ 2 * k = 2 * m - 1) then -1 else 0) := by
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [Finset.mem_Ico] at hk
        have hlt : 2 * k < 2 * m := by omega
        dsimp only [rowF]
        rw [dif_pos hlt]
        rfl
      rw [hcongr]
      have hmat0 : matNegOne m 0 j =
          if j.val = 1 ∨ j.val = 2 * m - 1 then (1 : ℝ) else 0 := by
        by_cases hj1 : j.val = 1
        · simp [matNegOne, of_apply, hj1]
        · by_cases hj_last : j.val = 2 * m - 1
          · have h1 : (0 : ℕ) + 1 = j.val ∨ (0 = 0 ∧ j.val = 2 * m - 1) := Or.inr ⟨rfl, hj_last⟩
            simp [matNegOne, of_apply, h1, hj_last]
          · have h1 : ¬((0 : ℕ) + 1 = j.val ∨ (0 = 0 ∧ j.val = 2 * m - 1)) := by omega
            have h2 : ¬(j.val + 1 = 0 ∨ (j.val = 0 ∧ 0 = 2 * m - 1)) := by omega
            simp [matNegOne, of_apply, h1, h2, hj1, hj_last]
            simp [show (1 : ℕ) ≠ j.val by omega, show (0 : ℕ) ≠ 2 * m - 1 by omega]
      rw [hmat0]
      by_cases hj1 : j.val = 1
      · have hsum : ∑ k ∈ Finset.Ico 1 m,
            (if 2 * k + 1 = j.val ∨ (2 * k = 0 ∧ j.val = 2 * m - 1) then (1 : ℝ)
             else if j.val + 1 = 2 * k ∨ (j.val = 0 ∧ 2 * k = 2 * m - 1) then -1 else 0) = -1 := by
          rw [Finset.sum_eq_single 1]
          · split_ifs <;> (try norm_num) <;> omega
          · intro b hb hb1
            rw [Finset.mem_Ico] at hb
            split_ifs <;> (try norm_num) <;> omega
          · intro h1; exfalso; apply h1; rw [Finset.mem_Ico]; omega
        rw [hsum]; split_ifs <;> (try norm_num) <;> omega
      · by_cases hj_last : j.val = 2 * m - 1
        · have hsum : ∑ k ∈ Finset.Ico 1 m,
              (if 2 * k + 1 = j.val ∨ (2 * k = 0 ∧ j.val = 2 * m - 1) then (1 : ℝ)
               else if j.val + 1 = 2 * k ∨ (j.val = 0 ∧ 2 * k = 2 * m - 1) then -1 else 0) = 1 := by
            rw [Finset.sum_eq_single (m - 1)]
            · split_ifs <;> (try norm_num) <;> omega
            · intro b hb hbm
              rw [Finset.mem_Ico] at hb
              split_ifs <;> (try norm_num) <;> omega
            · intro h1; exfalso; apply h1; rw [Finset.mem_Ico]; omega
          rw [hsum]; split_ifs <;> first | (norm_num; done) | omega
        · by_cases hj0 : j.val = 0
          · have hsum : ∑ k ∈ Finset.Ico 1 m,
                (if 2 * k + 1 = j.val ∨ (2 * k = 0 ∧ j.val = 2 * m - 1) then (1 : ℝ)
                 else if j.val + 1 = 2 * k ∨ (j.val = 0 ∧ 2 * k = 2 * m - 1) then -1 else 0) = 0 := by
              refine Finset.sum_eq_zero fun b hb => ?_
              rw [Finset.mem_Ico] at hb
              split_ifs <;> (try norm_num) <;> omega
            rw [hsum]; split_ifs <;> first | (norm_num; done) | omega
          · by_cases hj_even : j.val % 2 = 0
            · have hsum : ∑ k ∈ Finset.Ico 1 m,
                  (if 2 * k + 1 = j.val ∨ (2 * k = 0 ∧ j.val = 2 * m - 1) then (1 : ℝ)
                   else if j.val + 1 = 2 * k ∨ (j.val = 0 ∧ 2 * k = 2 * m - 1) then -1 else 0) = 0 := by
                refine Finset.sum_eq_zero fun b hb => ?_
                rw [Finset.mem_Ico] at hb
                split_ifs <;> (try norm_num) <;> omega
              rw [hsum]; split_ifs <;> first | (norm_num; done) | omega
            · have hq_lt : j.val / 2 < m := by omega
              have hq_ge : 1 ≤ j.val / 2 := by omega
              have hsum : ∑ k ∈ Finset.Ico 1 m,
                  (if 2 * k + 1 = j.val ∨ (2 * k = 0 ∧ j.val = 2 * m - 1) then (1 : ℝ)
                   else if j.val + 1 = 2 * k ∨ (j.val = 0 ∧ 2 * k = 2 * m - 1) then -1 else 0) = 0 := by
                have h2 : ∑ k ∈ Finset.Ico 1 m,
                    (if 2 * k + 1 = j.val ∨ (2 * k = 0 ∧ j.val = 2 * m - 1) then (1 : ℝ)
                     else if j.val + 1 = 2 * k ∨ (j.val = 0 ∧ 2 * k = 2 * m - 1) then -1 else 0) =
                    ∑ k ∈ ({j.val / 2, j.val / 2 + 1} : Finset ℕ),
                      (if 2 * k + 1 = j.val ∨ (2 * k = 0 ∧ j.val = 2 * m - 1) then (1 : ℝ)
                       else if j.val + 1 = 2 * k ∨ (j.val = 0 ∧ 2 * k = 2 * m - 1) then -1 else 0) := by
                  refine (Finset.sum_subset ?_ ?_).symm
                  · intro x hx
                    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                    rw [Finset.mem_Ico]
                    rcases hx with rfl | rfl <;> omega
                  · intro x hx hnx
                    rw [Finset.mem_Ico] at hx
                    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnx
                    split_ifs <;> (try norm_num) <;> omega
                rw [h2, Finset.sum_pair (by omega)]
                split_ifs <;> (try norm_num) <;> omega
              rw [hsum]; split_ifs <;> first | (norm_num; done) | omega
    dsimp only [M1]
    rw [← hrow_eq]
    exact hfull
  -- Step 2: Expand M1 along row 0
  have h2m_pos : 2 * m = (2 * m - 1) + 1 := by omega
  let M1' : Matrix (Fin ((2 * m - 1) + 1)) (Fin ((2 * m - 1) + 1)) ℝ :=
    M1.submatrix (Fin.cast h2m_pos.symm) (Fin.cast h2m_pos.symm)
  have hM1'_det : M1'.det = M1.det :=
    Matrix.det_submatrix_equiv_self (finCongr h2m_pos.symm) M1
  have hM1'_exp : M1'.det = (-1 : ℝ) ^ (2 * m - 1) * 2 *
      (M1'.submatrix Fin.succ (Fin.succAbove (Fin.last (2 * m - 1)))).det := by
    have h := det_eq_single_row_zero M1' (Fin.last (2 * m - 1)) (fun j hj => by
      simp only [M1', submatrix_apply, Fin.cast_zero, M1, Matrix.updateRow_apply, ↓reduceIte, row0]
      have hjv : j.val ≠ 2 * m - 1 := fun hval => hj (Fin.ext (by simp [hval]))
      simp [hjv])
    have hlast : M1' 0 (Fin.last (2 * m - 1)) = 2 := by
      simp only [M1', submatrix_apply, Fin.cast_zero, M1, Matrix.updateRow_apply, ↓reduceIte, row0,
        Fin.val_cast, Fin.val_last, ↓reduceIte]
    rw [hlast, Fin.val_last] at h
    exact h
  -- Step 3: In the minor N := M1'.submatrix Fin.succ last.succAbove, add cols 2, 4, ..., 2*m - 2 to col 0
  have : NeZero (2 * m - 1) := ⟨by omega⟩
  let N := M1'.submatrix Fin.succ (Fin.succAbove (Fin.last (2 * m - 1)))
  let colF : Fin (2 * m - 1) → ℕ → ℝ := fun r k =>
    if hk : 2 * k < 2 * m - 1 then N r ⟨2 * k, hk⟩ else 0
  have hN_det : N.det = -2 * (skewTridiag (2 * (m - 1))).det := by
    have hind : ∀ t : ℕ, t ≤ m - 1 →
        (Matrix.of fun r s : Fin (2 * m - 1) =>
          if s = 0 then N r 0 + ∑ k ∈ Finset.Ico 1 (t + 1), colF r k
          else N r s).det = N.det := by
      intro t ht
      induction t with
      | zero =>
        have hN0 : (Matrix.of fun r s : Fin (2 * m - 1) =>
            if s = 0 then N r 0 + ∑ k ∈ Finset.Ico 1 (0 + 1), colF r k else N r s) = N := by
          ext r s
          simp only [of_apply, zero_add, Finset.Ico_self, Finset.sum_empty, add_zero]
          split_ifs with hs <;> simp [hs]
        rw [hN0]
      | succ t ih =>
        have hsum : (fun r => ∑ k ∈ Finset.Ico 1 (t + 1 + 1), colF r k) =
            fun r => (∑ k ∈ Finset.Ico 1 (t + 1), colF r k) + colF r (t + 1) := by
          ext r; rw [Finset.sum_Ico_succ_top (by omega)]
        have hlt : 2 * (t + 1) < 2 * m - 1 := by omega
        have hne : (0 : Fin (2 * m - 1)) ≠ ⟨2 * (t + 1), hlt⟩ := by
          simp [Fin.ext_iff]
        let N_prev : Matrix (Fin (2 * m - 1)) (Fin (2 * m - 1)) ℝ :=
          Matrix.of fun r s =>
            if s = 0 then N r 0 + ∑ k ∈ Finset.Ico 1 (t + 1), colF r k
            else N r s
        have hstep : (Matrix.of fun r s : Fin (2 * m - 1) =>
            if s = 0 then N r 0 + ∑ k ∈ Finset.Ico 1 (t + 1 + 1), colF r k
            else N r s) =
            Matrix.of fun r s =>
              if s = 0 then N_prev r 0 + 1 * N_prev r ⟨2 * (t + 1), hlt⟩
              else N_prev r s := by
          ext r s
          simp only [of_apply, N_prev]
          split_ifs with hs h0
          · exact absurd h0.symm hne
          · have hfn := congrFun hsum r
            have hcolF : colF r (t + 1) = N r ⟨2 * (t + 1), hlt⟩ := dif_pos hlt
            rw [hfn, hcolF]
            ring
          · rfl
        rw [hstep, det_add_smul_col N_prev 0 ⟨2 * (t + 1), hlt⟩ hne 1]
        exact ih (by omega)
    let col0_target : Matrix (Fin (2 * m - 1)) (Fin (2 * m - 1)) ℝ :=
      Matrix.of fun r s =>
        if s = 0 then N r 0 + ∑ k ∈ Finset.Ico 1 m, colF r k
        else N r s
    have hcol_det : col0_target.det = N.det := by
      have h := hind (m - 1) (le_refl _)
      have hm1 : m - 1 + 1 = m := by omega
      rw [hm1] at h
      exact h
    have hcolF_val : ∀ r : Fin (2 * m - 1), ∀ k (hk : k ∈ Finset.Ico 1 m),
        colF r k = N r ⟨2 * k, by rw [Finset.mem_Ico] at hk; omega⟩ := by
      intro r k hk
      rw [Finset.mem_Ico] at hk
      simp [colF, show 2 * k < 2 * m - 1 by omega]
    have hcol0_zero : ∀ r : Fin (2 * m - 1), r ≠ ⟨2 * m - 2, by omega⟩ → col0_target r 0 = 0 := by
      intro r hr
      simp only [col0_target, of_apply, ↓reduceIte]
      have hr_ne0 : (Fin.cast h2m_pos.symm r.succ) ≠ 0 := by
        intro h; have hv := congrArg Fin.val h; simp at hv
      have hr_lt : r.val < 2 * m - 2 := by
        have := r.isLt
        have hrv : r.val ≠ 2 * m - 2 := fun h => hr (Fin.ext h)
        omega
      have hsucc0 : (Fin.succAbove (Fin.last (2 * m - 1)) (0 : Fin (2 * m - 1))).val = 0 := by
        simp [Fin.succAbove_last]
      have hNr0 : N r 0 = if r.val = 0 then -1 else 0 := by
        simp only [N, submatrix_apply, M1', M1, Matrix.updateRow_apply, hr_ne0, ↓reduceIte,
          matNegOne, of_apply, Fin.val_cast, Fin.val_succ, hsucc0]
        have h1 : ¬(r.val + 1 + 1 = 0 ∨ (r.val + 1 = 0 ∧ 0 = 2 * m - 1)) := by omega
        by_cases hr0 : r.val = 0
        · have h2 : 0 + 1 = r.val + 1 ∨ (0 = 0 ∧ r.val + 1 = 2 * m - 1) := Or.inl (by omega)
          simp [h1, h2, hr0]
        · have h2 : ¬(0 + 1 = r.val + 1 ∨ (0 = 0 ∧ r.val + 1 = 2 * m - 1)) := by omega
          simp [h1, h2, hr0]
          omega
      rw [hNr0]
      have hcol_congr : ∑ k ∈ Finset.Ico 1 m, colF r k =
          ∑ k ∈ Finset.Ico 1 m,
            if r.val + 1 + 1 = 2 * k ∨ (r.val + 1 = 0 ∧ 2 * k = 2 * m - 1) then (1 : ℝ)
            else if 2 * k + 1 = r.val + 1 ∨ (2 * k = 0 ∧ r.val + 1 = 2 * m - 1) then -1 else 0 := by
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [hcolF_val r k hk]
        rw [Finset.mem_Ico] at hk
        simp only [N, submatrix_apply, M1', M1, Matrix.updateRow_apply, hr_ne0, ↓reduceIte, matNegOne]
        have hs : (Fin.succAbove (Fin.last (2 * m - 1)) ⟨2 * k, by omega⟩).val = 2 * k := by
          simp only [Fin.succAbove_last, Fin.val_castSucc]
        simp only [of_apply, Fin.val_cast, Fin.val_succ, hs]
      rw [hcol_congr]
      by_cases hr0 : r.val = 0
      · have hsum : ∑ k ∈ Finset.Ico 1 m,
            (if r.val + 1 + 1 = 2 * k ∨ (r.val + 1 = 0 ∧ 2 * k = 2 * m - 1) then (1 : ℝ)
             else if 2 * k + 1 = r.val + 1 ∨ (2 * k = 0 ∧ r.val + 1 = 2 * m - 1) then -1 else 0) = 1 := by
          rw [Finset.sum_eq_single 1]
          · split_ifs <;> (try norm_num) <;> omega
          · intro b hb hb1
            rw [Finset.mem_Ico] at hb
            split_ifs <;> (try norm_num) <;> omega
          · intro h1; exfalso; apply h1; rw [Finset.mem_Ico]; omega
        rw [hsum]; simp [hr0]
      · by_cases hr_even : r.val % 2 = 0
        · have hsum : ∑ k ∈ Finset.Ico 1 m,
              (if r.val + 1 + 1 = 2 * k ∨ (r.val + 1 = 0 ∧ 2 * k = 2 * m - 1) then (1 : ℝ)
               else if 2 * k + 1 = r.val + 1 ∨ (2 * k = 0 ∧ r.val + 1 = 2 * m - 1) then -1 else 0) = 0 := by
            have h2 : ∑ k ∈ Finset.Ico 1 m,
                (if r.val + 1 + 1 = 2 * k ∨ (r.val + 1 = 0 ∧ 2 * k = 2 * m - 1) then (1 : ℝ)
                 else if 2 * k + 1 = r.val + 1 ∨ (2 * k = 0 ∧ r.val + 1 = 2 * m - 1) then -1 else 0) =
                ∑ k ∈ ({r.val / 2, r.val / 2 + 1} : Finset ℕ),
                  (if r.val + 1 + 1 = 2 * k ∨ (r.val + 1 = 0 ∧ 2 * k = 2 * m - 1) then (1 : ℝ)
                   else if 2 * k + 1 = r.val + 1 ∨ (2 * k = 0 ∧ r.val + 1 = 2 * m - 1) then -1 else 0) := by
              refine (Finset.sum_subset ?_ ?_).symm
              · intro x hx
                simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                rw [Finset.mem_Ico]
                rcases hx with rfl | rfl <;> omega
              · intro x hx hnx
                rw [Finset.mem_Ico] at hx
                simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnx
                split_ifs <;> (try norm_num) <;> omega
            rw [h2, Finset.sum_pair (by omega)]
            split_ifs <;> (try norm_num) <;> omega
          rw [hsum]; simp [hr0]
        · have hsum : ∑ k ∈ Finset.Ico 1 m,
              (if r.val + 1 + 1 = 2 * k ∨ (r.val + 1 = 0 ∧ 2 * k = 2 * m - 1) then (1 : ℝ)
               else if 2 * k + 1 = r.val + 1 ∨ (2 * k = 0 ∧ r.val + 1 = 2 * m - 1) then -1 else 0) = 0 := by
            refine Finset.sum_eq_zero fun x hx => ?_
            rw [Finset.mem_Ico] at hx
            split_ifs <;> (try norm_num) <;> omega
          rw [hsum]; simp [hr0]
    have hcol0_last : col0_target ⟨2 * m - 2, by omega⟩ 0 = -2 := by
      simp only [col0_target, of_apply, ↓reduceIte]
      have hsucc0 : (Fin.succAbove (Fin.last (2 * m - 1)) (0 : Fin (2 * m - 1))).val = 0 := by
        simp [Fin.succAbove_last]
      have hr_ne0 : (Fin.cast h2m_pos.symm (⟨2 * m - 2, by omega⟩ : Fin (2 * m - 1)).succ) ≠ 0 := by
        intro h; have hv := congrArg Fin.val h; simp at hv
      have hNr0 : N ⟨2 * m - 2, by omega⟩ 0 = -1 := by
        simp only [N, submatrix_apply, M1', M1, Matrix.updateRow_apply, hr_ne0, ↓reduceIte,
          matNegOne, of_apply, Fin.val_cast, Fin.val_succ, hsucc0]
        have h1 : ¬((2 * m - 2) + 1 + 1 = 0 ∨ ((2 * m - 2) + 1 = 0 ∧ 0 = 2 * m - 1)) := by omega
        have h2 : 0 + 1 = (2 * m - 2) + 1 ∨ (0 = 0 ∧ (2 * m - 2) + 1 = 2 * m - 1) := by omega
        simp [h1, h2]
        omega
      have hcol_congr : ∑ k ∈ Finset.Ico 1 m, colF ⟨2 * m - 2, by omega⟩ k = -1 := by
        have hcongr : ∑ k ∈ Finset.Ico 1 m, colF ⟨2 * m - 2, by omega⟩ k =
            ∑ k ∈ Finset.Ico 1 m,
              if (2 * m - 2) + 1 + 1 = 2 * k ∨ ((2 * m - 2) + 1 = 0 ∧ 2 * k = 2 * m - 1) then (1 : ℝ)
              else if 2 * k + 1 = (2 * m - 2) + 1 ∨ (2 * k = 0 ∧ (2 * m - 2) + 1 = 2 * m - 1) then -1 else 0 := by
          refine Finset.sum_congr rfl fun k hk => ?_
          rw [hcolF_val ⟨2 * m - 2, by omega⟩ k hk]
          rw [Finset.mem_Ico] at hk
          simp only [N, submatrix_apply, M1', M1, Matrix.updateRow_apply, hr_ne0, ↓reduceIte, matNegOne]
          have hs : (Fin.succAbove (Fin.last (2 * m - 1)) ⟨2 * k, by omega⟩).val = 2 * k := by
            simp only [Fin.succAbove_last, Fin.val_castSucc]
          simp only [of_apply, Fin.val_cast, Fin.val_succ, hs]
        rw [hcongr, Finset.sum_eq_single (m - 1)]
        · split_ifs <;> (try norm_num) <;> omega
        · intro b hb hbm
          rw [Finset.mem_Ico] at hb
          split_ifs <;> (try norm_num) <;> omega
        · intro h1; exfalso; apply h1; rw [Finset.mem_Ico]; omega
      rw [hNr0, hcol_congr]; norm_num
    have h2m2 : 2 * m - 1 = (2 * m - 2) + 1 := by omega
    let C' : Matrix (Fin ((2 * m - 2) + 1)) (Fin ((2 * m - 2) + 1)) ℝ :=
      col0_target.submatrix (Fin.cast h2m2.symm) (Fin.cast h2m2.symm)
    have hC'_det : C'.det = col0_target.det :=
      Matrix.det_submatrix_equiv_self (finCongr h2m2.symm) col0_target
    have hC'_exp := det_eq_single_col_zero C' (Fin.last (2 * m - 2)) (fun i hi => by
      simp only [C', submatrix_apply, Fin.cast_zero]
      exact hcol0_zero (Fin.cast h2m2.symm i) (fun h => hi (Fin.ext (by simp [Fin.ext_iff] at h; exact h))))
    have hC'_last : C' (Fin.last (2 * m - 2)) 0 = -2 := by
      have hidx : Fin.cast h2m2.symm (Fin.last (2 * m - 2)) = ⟨2 * m - 2, by omega⟩ := by
        ext; simp
      have hidx0 : Fin.cast h2m2.symm (0 : Fin ((2 * m - 2) + 1)) = 0 := by ext; simp
      simp only [C', submatrix_apply, hidx, hidx0]
      exact hcol0_last
    rw [hC'_last, Fin.val_last] at hC'_exp
    have h2m_sub : 2 * m - 2 = 2 * (m - 1) := by omega
    have hsub_eq : C'.submatrix (Fin.last (2 * m - 2)).succAbove Fin.succ =
        (skewTridiag (2 * (m - 1))).submatrix (Fin.cast h2m_sub) (Fin.cast h2m_sub) := by
      ext i j
      simp only [C', submatrix_apply, col0_target, of_apply, Fin.val_succ, Fin.val_cast]
      have hne0' : (Fin.cast h2m2.symm (Fin.succ j)) ≠ (0 : Fin (2 * m - 1)) := by
        simp [Fin.ext_iff]
      simp only [hne0', ↓reduceIte, N, submatrix_apply, M1', M1]
      have hi_lt : i.val < 2 * m - 2 := i.isLt
      have hsuccAbove_i : (Fin.cast h2m2.symm ((Fin.last (2 * m - 2)).succAbove i)).val = i.val := by
        simp [Fin.succAbove_last]
      have hsucc_i : (Fin.cast h2m_pos.symm (Fin.cast h2m2.symm ((Fin.last (2 * m - 2)).succAbove i)).succ).val = i.val + 1 := by
        simp [Fin.val_cast, Fin.val_succ, hsuccAbove_i]
      have hne0_row : (Fin.cast h2m_pos.symm (Fin.cast h2m2.symm ((Fin.last (2 * m - 2)).succAbove i)).succ) ≠ 0 := by
        simp [Fin.ext_iff]
      have hsucc_j : (Fin.cast h2m_pos.symm (Fin.succAbove (Fin.last (2 * m - 1)) (Fin.cast h2m2.symm j.succ))).val = j.val + 1 := by
        simp only [Fin.succAbove_last, Fin.val_castSucc, Fin.val_cast, Fin.val_succ]
      simp only [Matrix.updateRow_apply, hne0_row, ↓reduceIte, matNegOne, of_apply, Fin.val_cast,
        hsucc_i, hsucc_j, skewTridiag]
      have h1f : ¬(i.val + 1 = 0 ∧ j.val + 1 = 2 * m - 1) := by omega
      have h2f : ¬(j.val + 1 = 0 ∧ i.val + 1 = 2 * m - 1) := by omega
      simp [h1f, h2f]
    have hsub_det : ((skewTridiag (2 * (m - 1))).submatrix (Fin.cast h2m_sub) (Fin.cast h2m_sub)).det =
        (skewTridiag (2 * (m - 1))).det :=
      Matrix.det_submatrix_equiv_self (finCongr h2m_sub) (skewTridiag (2 * (m - 1)))
    rw [hsub_eq, hsub_det] at hC'_exp
    have heven_pow : (-1 : ℝ) ^ (2 * m - 2) = 1 := by
      rw [h2m_sub, pow_mul]; norm_num
    rw [heven_pow, one_mul] at hC'_exp
    rw [← hcol_det, ← hC'_det, hC'_exp]
  rw [← hM1_det, ← hM1'_det, hM1'_exp, hN_det, det_skewTridiag_even (m - 1)]
  have hodd_pow : (-1 : ℝ) ^ (2 * m - 1) = -1 := by
    have : 2 * m - 1 = 2 * (m - 1) + 1 := by omega
    rw [this, pow_add, pow_mul]; norm_num
  rw [hodd_pow]
  ring

/-- Tridiagonal matrix of size `n` with `4` on the diagonal, `5` on the superdiagonal,
and `-1` on the subdiagonal. -/
private def tridiagFive (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j =>
    if i = j then 4
    else if i.val + 1 = j.val then 5
    else if j.val + 1 = i.val then -1
    else 0

private lemma det_tridiagFive_ge_four :
    (∀ n : ℕ, 1 ≤ (tridiagFive n).det) ∧ (∀ n : ℕ, 1 ≤ n → 4 ≤ (tridiagFive n).det) := by
  have hrec : ∀ n : ℕ,
      (tridiagFive (n + 2)).det = 4 * (tridiagFive (n + 1)).det + 5 * (tridiagFive n).det := by
    intro n
    let T := tridiagFive (n + 2)
    rw [Matrix.det_succ_row T (Fin.last (n + 1))]
    have hsum : ∑ j : Fin (n + 2), (-1) ^ ((Fin.last (n + 1) : ℕ) + (j : ℕ)) *
          T (Fin.last (n + 1)) j * (T.submatrix (Fin.last (n + 1)).succAbove j.succAbove).det =
        (-1) ^ ((n + 1) + n) * (-1) * (T.submatrix (Fin.last (n + 1)).succAbove (Fin.succAbove ⟨n, by omega⟩)).det +
        (-1) ^ ((n + 1) + (n + 1)) * 4 * (T.submatrix (Fin.last (n + 1)).succAbove (Fin.last (n + 1)).succAbove).det := by
      have hsub : ∑ j : Fin (n + 2), (-1) ^ ((Fin.last (n + 1) : ℕ) + (j : ℕ)) *
            T (Fin.last (n + 1)) j * (T.submatrix (Fin.last (n + 1)).succAbove j.succAbove).det =
          ∑ j ∈ ({⟨n, by omega⟩, Fin.last (n + 1)} : Finset (Fin (n + 2))),
            (-1) ^ ((Fin.last (n + 1) : ℕ) + (j : ℕ)) *
              T (Fin.last (n + 1)) j * (T.submatrix (Fin.last (n + 1)).succAbove j.succAbove).det := by
        refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
        intro j _ hj
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
        have hjv1 : j.val ≠ n := fun h => hj.1 (Fin.ext h)
        have hjv2 : j.val ≠ n + 1 := fun h => hj.2 (Fin.ext h)
        have hT0 : T (Fin.last (n + 1)) j = 0 := by
          simp only [T, tridiagFive, of_apply, Fin.val_last, Fin.ext_iff]
          split_ifs <;> (try norm_num) <;> omega
        simp [hT0]
      rw [hsub, Finset.sum_pair (by simp [Fin.ext_iff])]
      have h1 : T (Fin.last (n + 1)) ⟨n, by omega⟩ = -1 := by
        simp [T, tridiagFive, Fin.ext_iff]; omega
      have h2 : T (Fin.last (n + 1)) (Fin.last (n + 1)) = 4 := by
        simp [T, tridiagFive]
      simp [h1, h2, Fin.val_last]
    rw [hsum]
    have hdiag : T.submatrix (Fin.last (n + 1)).succAbove (Fin.last (n + 1)).succAbove = tridiagFive (n + 1) := by
      ext i j
      simp [T, tridiagFive, Fin.succAbove_last, Fin.ext_iff]
    have hsub2 : (T.submatrix (Fin.last (n + 1)).succAbove (Fin.succAbove ⟨n, by omega⟩)).det =
        5 * (tridiagFive n).det := by
      let S := T.submatrix (Fin.last (n + 1)).succAbove (Fin.succAbove ⟨n, by omega⟩)
      have hcol : ∀ i : Fin (n + 1), i ≠ Fin.last n → S i (Fin.last n) = 0 := by
        intro i hi
        have hiv : i.val < n := by
          have := i.isLt
          have hne : i.val ≠ n := fun h => hi (Fin.ext (by simp [h]))
          omega
        have hcol_val : ((Fin.succAbove ⟨n, by omega⟩) (Fin.last n)).val = n + 1 := by
          simp only [Fin.succAbove]
          split_ifs with h
          · exfalso; simp [Fin.lt_def] at h
          · simp
        simp only [S, T, tridiagFive, submatrix_apply, of_apply, Fin.succAbove_last,
          Fin.val_castSucc, Fin.ext_iff, hcol_val]
        split_ifs <;> first | rfl | (norm_num; omega)
      have hS := det_eq_single_col_last S (Fin.last n) hcol
      have hSnn : S (Fin.last n) (Fin.last n) = 5 := by
        have hcol_val : ((Fin.succAbove ⟨n, by omega⟩) (Fin.last n)).val = n + 1 := by
          simp only [Fin.succAbove]
          split_ifs with h
          · exfalso; simp [Fin.lt_def] at h
          · simp
        simp only [S, T, tridiagFive, submatrix_apply, of_apply, Fin.succAbove_last,
          Fin.val_last, Fin.val_castSucc, hcol_val, Fin.ext_iff]
        split_ifs <;> first | rfl | (norm_num; omega)
      have hsub3 : S.submatrix (Fin.last n).succAbove Fin.castSucc = tridiagFive n := by
        ext i j
        have hi_lt : i.val < n := i.isLt
        have hj_lt : j.val < n := j.isLt
        have h2 : ((Fin.succAbove ⟨n, by omega⟩) j.castSucc).val = j.val := by
          simp only [Fin.succAbove]
          split_ifs with h
          · rfl
          · exfalso; simp only [Fin.lt_def, Fin.val_castSucc] at h; omega
        simp [S, T, tridiagFive, Fin.ext_iff, h2]
      rw [hSnn, Fin.val_last, hsub3] at hS
      have heven : (-1 : ℝ) ^ (n + n) = 1 := by
        have : n + n = 2 * n := by omega
        rw [this, pow_mul]; norm_num
      rw [heven, one_mul] at hS
      exact hS
    have hpow1 : (-1 : ℝ) ^ (n + 1 + n) = -1 := by
      have : n + 1 + n = 2 * n + 1 := by omega
      rw [this, pow_add, pow_mul]; norm_num
    have hpow2 : (-1 : ℝ) ^ (n + 1 + (n + 1)) = 1 := by
      have : n + 1 + (n + 1) = 2 * (n + 1) := by omega
      rw [this, pow_mul]; norm_num
    rw [hdiag, hsub2, hpow1, hpow2]
    ring
  have hge1 : ∀ n : ℕ, 1 ≤ (tridiagFive n).det := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      rcases n with _ | _ | n
      · simp
      · have h1 : (tridiagFive 1).det = 4 := by
          simp [tridiagFive]
        linarith
      · rw [hrec n]
        have ih1 := ih (n + 1) (by omega)
        have ih0 := ih n (by omega)
        linarith
  have hge4 : ∀ n : ℕ, 1 ≤ n → 4 ≤ (tridiagFive n).det := by
    intro n hn
    rcases n with _ | _ | n
    · omega
    · have h1 : (tridiagFive 1).det = 4 := by
        simp [tridiagFive]
      linarith
    · rw [hrec n]
      have h1 := hge1 (n + 1)
      have h0 := hge1 n
      linarith
  exact ⟨hge1, hge4⟩

/-- Auxiliary matrix for `M(-5) = -5 • U + Uᵀ` on `C_{2m}(+,-,...,-)`:
diagonal `-4` at `0`, `4` at `1..2m-1`; superdiagonal & `(0, 2m-1)` = `5`;
subdiagonal & `(2m-1, 0)` = `-1`. -/
private def matNegFive (m : ℕ) : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ :=
  Matrix.of fun i j =>
    if i = j then (if i.val = 0 then -4 else 4)
    else if i.val + 1 = j.val ∨ (i.val = 0 ∧ j.val = 2 * m - 1) then 5
    else if j.val + 1 = i.val ∨ (j.val = 0 ∧ i.val = 2 * m - 1) then -1
    else 0

private lemma matNegFive_ne_zero (m : ℕ) (i j : Fin (2 * m)) (hi : i.val ≠ 0) (hj : j.val ≠ 0) :
    matNegFive m i j =
      if i.val = j.val then 4
      else if i.val + 1 = j.val then 5
      else if j.val + 1 = i.val then -1
      else 0 := by
  simp only [matNegFive, of_apply, Fin.ext_iff, hi, ↓reduceIte, false_and, hj, or_false]

private lemma howlett_neg_five_eq (m : ℕ) (hm : 2 ≤ m) :
    (-5 : ℝ) • howlettU (evenCycleSinglePlusSystem m hm).B +
      (howlettU (evenCycleSinglePlusSystem m hm).B)ᵀ = matNegFive m := by
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, transpose_apply, howlettU_apply,
    evenCycleSinglePlusSystem, B_evenCycleSinglePlus, of_apply, matNegFive]
  by_cases hij : i = j
  · subst hij
    simp only [lt_self_iff_false, ↓reduceIte]
    split_ifs <;> norm_num
  · rcases lt_trichotomy i j with hlt | heq | hgt
    · have hgt' : ¬(j < i) := not_lt_of_gt hlt
      have hji : j ≠ i := Ne.symm hij
      have hi_lt : i.val < j.val := hlt
      simp only [hlt, hgt', hij, hji, ↓reduceIte]
      by_cases hadj : i.val + 1 = j.val ∨ (i.val = 0 ∧ j.val = 2 * m - 1)
      · have hadj' : i.val + 1 = j.val ∨ j.val + 1 = i.val ∨
            (i.val = 0 ∧ j.val = 2 * m - 1) ∨ (j.val = 0 ∧ i.val = 2 * m - 1) := by tauto
        split_ifs <;> (norm_num; try omega)
      · have hadj' : ¬(i.val + 1 = j.val ∨ j.val + 1 = i.val ∨
            (i.val = 0 ∧ j.val = 2 * m - 1) ∨ (j.val = 0 ∧ i.val = 2 * m - 1)) := by omega
        split_ifs <;> (norm_num; try omega)
    · exact absurd heq hij
    · have hlt' : ¬(i < j) := not_lt_of_gt hgt
      have hji : j ≠ i := Ne.symm hij
      have hj_lt : j.val < i.val := hgt
      have hno1 : ¬(i.val + 1 = j.val ∨ (i.val = 0 ∧ j.val = 2 * m - 1)) := by omega
      simp only [hlt', hgt, hij, hji, ↓reduceIte, hno1]
      by_cases hadj : j.val + 1 = i.val ∨ (j.val = 0 ∧ i.val = 2 * m - 1)
      · have hadj' : i.val + 1 = j.val ∨ j.val + 1 = i.val ∨
            (i.val = 0 ∧ j.val = 2 * m - 1) ∨ (j.val = 0 ∧ i.val = 2 * m - 1) := by tauto
        split_ifs <;> (norm_num; try omega)
      · have hadj' : ¬(i.val + 1 = j.val ∨ j.val + 1 = i.val ∨
            (i.val = 0 ∧ j.val = 2 * m - 1) ∨ (j.val = 0 ∧ i.val = 2 * m - 1)) := by omega
        split_ifs <;> (norm_num; try omega)

private lemma det_matNegFive_lt_zero (m : ℕ) (hm : 2 ≤ m) : (matNegFive m).det < 0 := by
  have : NeZero (2 * m) := ⟨by omega⟩
  -- Step 1: Replace row 0 with row 0 + ∑_{i=1}^{2m-1} (-1)^i * row i = (-2, 0, ..., 0, 6)
  let row0 : Fin (2 * m) → ℝ := fun j =>
    if j.val = 0 then -2 else if j.val = 2 * m - 1 then 6 else 0
  let M1 : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ := Matrix.updateRow (matNegFive m) 0 row0
  have hM1_det : M1.det = (matNegFive m).det := by
    let altRow : ℕ → Fin (2 * m) → ℝ := fun i =>
      if h : i < 2 * m then ((-1 : ℝ) ^ i) • matNegFive m ⟨i, h⟩ else 0
    have hind : ∀ t : ℕ, t ≤ 2 * m - 1 →
        Matrix.det (Function.update (matNegFive m) 0
          (matNegFive m 0 + ∑ i ∈ Finset.Ico 1 (t + 1), altRow i)) =
          (matNegFive m).det := by
      intro t ht
      induction t with
      | zero =>
        simp only [Finset.Ico_self, Finset.sum_empty, add_zero]
        rw [show (Function.update (matNegFive m) 0 (matNegFive m 0) :
          Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ) = matNegFive m from by
            ext r s; by_cases hr : r = 0 <;> simp [Function.update, hr]]
      | succ t ih =>
        have hsum : ∑ i ∈ Finset.Ico 1 (t + 1 + 1), altRow i =
            (∑ i ∈ Finset.Ico 1 (t + 1), altRow i) + altRow (t + 1) := by
          rw [Finset.sum_Ico_succ_top (by omega)]
        have halt : altRow (t + 1) = ((-1 : ℝ) ^ (t + 1)) • matNegFive m ⟨t + 1, by omega⟩ := by
          simp [altRow, show t + 1 < 2 * m by omega]
        rw [hsum, halt, ← add_assoc]
        have hne : (0 : Fin (2 * m)) ≠ ⟨t + 1, by omega⟩ := by simp [Fin.ext_iff]
        let prev : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ := Function.update (matNegFive m) 0
          (matNegFive m 0 + ∑ i ∈ Finset.Ico 1 (t + 1), altRow i)
        have hupd : (Function.update (matNegFive m) 0
            (matNegFive m 0 + ∑ i ∈ Finset.Ico 1 (t + 1), altRow i +
              ((-1 : ℝ) ^ (t + 1)) • matNegFive m ⟨t + 1, by omega⟩) :
            Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ) =
            Function.update prev 0 (prev 0 + ((-1 : ℝ) ^ (t + 1)) • prev ⟨t + 1, by omega⟩) := by
          ext r s
          simp only [prev, Function.update]
          by_cases hr : r = 0
          · subst hr
            simp [hne.symm]
          · simp [hr]
        rw [hupd, det_add_smul_row prev 0 ⟨t + 1, by omega⟩ hne ((-1 : ℝ) ^ (t + 1)), ih (by omega)]
    have hfull := hind (2 * m - 1) (le_refl _)
    have hrow_eq : matNegFive m 0 + ∑ i ∈ Finset.Ico 1 (2 * m - 1 + 1), altRow i = row0 := by
      ext j
      simp only [Pi.add_apply, Finset.sum_apply]
      have h2m1 : 2 * m - 1 + 1 = 2 * m := by omega
      rw [h2m1]
      let g : ℕ → ℝ := fun i => (-1 : ℝ) ^ i *
        (if i = j.val then (if i = 0 then (-4 : ℝ) else 4)
         else if i + 1 = j.val ∨ i = 0 ∧ j.val = 2 * m - 1 then 5
         else if j.val + 1 = i ∨ j.val = 0 ∧ i = 2 * m - 1 then -1 else 0)
      have hsum_rw : (∑ i ∈ Finset.Ico 1 (2 * m), altRow i j) =
          ∑ i ∈ Finset.Ico 1 (2 * m), g i := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [Finset.mem_Ico] at hi
        simp only [altRow]
        split_ifs with hlt
        · simp only [Pi.smul_apply, smul_eq_mul, matNegFive, of_apply, g, Fin.ext_iff]
        · exact absurd hi.2 hlt
      rw [hsum_rw]
      simp only [row0, matNegFive, of_apply, Fin.val_zero, zero_add]
      by_cases hj0 : j.val = 0
      · have hsum : ∑ i ∈ Finset.Ico 1 (2 * m), g i = 2 := by
          have hpair : ∑ i ∈ Finset.Ico 1 (2 * m), g i =
              ∑ i ∈ ({1, 2 * m - 1} : Finset ℕ), g i := by
            refine (Finset.sum_subset ?_ ?_).symm
            · intro x hx
              simp only [Finset.mem_insert, Finset.mem_singleton] at hx
              rw [Finset.mem_Ico]; rcases hx with rfl | rfl <;> omega
            · intro x hx hnx
              rw [Finset.mem_Ico] at hx
              simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnx
              simp [g, hj0]; split_ifs <;> first | omega | simp
          rw [hpair, Finset.sum_pair (by omega)]
          have hpow1 : (-1 : ℝ) ^ (2 * m - 1) = -1 := by
            have : 2 * m - 1 = 2 * (m - 1) + 1 := by omega
            rw [this, pow_add, pow_mul]; norm_num
          simp [g, hj0, hpow1]
          split_ifs
          all_goals first | omega | ring
        rw [hsum]
        have h0j : (0 : Fin (2 * m)) = j := Fin.ext hj0.symm
        simp [hj0, h0j]
        all_goals first | omega | norm_num
      · by_cases hj_last : j.val = 2 * m - 1
        · have hsum : ∑ i ∈ Finset.Ico 1 (2 * m), g i = 1 := by
            have hpair : ∑ i ∈ Finset.Ico 1 (2 * m), g i =
                ∑ i ∈ ({2 * m - 2, 2 * m - 1} : Finset ℕ), g i := by
              refine (Finset.sum_subset ?_ ?_).symm
              · intro x hx
                simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                rw [Finset.mem_Ico]; rcases hx with rfl | rfl <;> omega
              · intro x hx hnx
                rw [Finset.mem_Ico] at hx
                simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnx
                simp [g, hj_last]; split_ifs <;> first | omega | simp
            rw [hpair, Finset.sum_pair (by omega)]
            have hpow_even : (-1 : ℝ) ^ (2 * m - 2) = 1 := by
              have : 2 * m - 2 = 2 * (m - 1) := by omega
              rw [this, pow_mul]; norm_num
            have hpow_odd : (-1 : ℝ) ^ (2 * m - 1) = -1 := by
              have : 2 * m - 1 = 2 * (m - 1) + 1 := by omega
              rw [this, pow_add, pow_mul]; norm_num
            simp [g, hj_last, hpow_even, hpow_odd]
            split_ifs
            all_goals first | omega | norm_num
          rw [hsum]
          split_ifs <;> first | (simp only [Fin.ext_iff, Fin.val_zero] at *; omega) | tauto | (norm_num; done)
        · have hj1_lt : 1 ≤ j.val := by omega
          have hj_lt_last : j.val < 2 * m - 1 := by omega
          have hsum : ∑ i ∈ Finset.Ico 1 (2 * m), g i = if j.val = 1 then -5 else 0 := by
            by_cases hj1 : j.val = 1
            · have hpair : ∑ i ∈ Finset.Ico 1 (2 * m), g i =
                  ∑ i ∈ ({1, 2} : Finset ℕ), g i := by
                refine (Finset.sum_subset ?_ ?_).symm
                · intro x hx
                  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                  rw [Finset.mem_Ico]; rcases hx with rfl | rfl <;> omega
                · intro x hx hnx
                  rw [Finset.mem_Ico] at hx
                  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnx
                  simp [g, hj1]; split_ifs <;> first | omega | simp
              rw [hpair, Finset.sum_pair (by omega)]
              simp [g, hj1]
              all_goals first | omega | norm_num
            · have hpair : ∑ i ∈ Finset.Ico 1 (2 * m), g i =
                  ∑ i ∈ ({j.val - 1, j.val, j.val + 1} : Finset ℕ), g i := by
                refine (Finset.sum_subset ?_ ?_).symm
                · intro x hx
                  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                  rw [Finset.mem_Ico]; rcases hx with rfl | rfl | rfl <;> omega
                · intro x hx hnx
                  rw [Finset.mem_Ico] at hx
                  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnx
                  have hj0_fin : j ≠ 0 := by simp [Fin.ext_iff, hj0]
                  simp [g, hj0_fin]; split_ifs <;> first | omega | simp
              rw [hpair, Finset.sum_insert (by simp; omega), Finset.sum_pair (by omega)]
              have ha : j.val - 1 + 1 = j.val := by omega
              have hpow_a : (-1 : ℝ) ^ (j.val - 1) = -((-1 : ℝ) ^ j.val) := by
                have : j.val = (j.val - 1) + 1 := by omega
                conv_rhs => rw [this, pow_succ]
                ring
              have hpow_b : (-1 : ℝ) ^ (j.val + 1) = -((-1 : ℝ) ^ j.val) := by
                rw [pow_succ]; ring
              simp [g, hj0, hj1, ha, hpow_a, hpow_b]
              split_ifs
              all_goals first | omega | ring
          rw [hsum]
          split_ifs <;> first | (simp only [Fin.ext_iff, Fin.val_zero] at *; omega) | tauto | (norm_num; done)
    dsimp only [M1]; rw [← hrow_eq]; exact hfull
  -- Step 2: Add 3 * col 0 to col (2*m - 1)
  let M2 : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ :=
    Matrix.of fun r s => if s = ⟨2 * m - 1, by omega⟩ then M1 r ⟨2 * m - 1, by omega⟩ + 3 * M1 r 0 else M1 r s
  have hM2_det : M2.det = M1.det := by
    have hne : (⟨2 * m - 1, by omega⟩ : Fin (2 * m)) ≠ 0 := by simp [Fin.ext_iff]; omega
    exact det_add_smul_col M1 ⟨2 * m - 1, by omega⟩ 0 hne 3
  -- Step 3: Expand M2 along row 0 (only col 0 is -2)
  have h2m_pos : 2 * m = (2 * m - 1) + 1 := by omega
  let M2' : Matrix (Fin ((2 * m - 1) + 1)) (Fin ((2 * m - 1) + 1)) ℝ :=
    M2.submatrix (Fin.cast h2m_pos.symm) (Fin.cast h2m_pos.symm)
  have hM2'_det : M2'.det = M2.det := Matrix.det_submatrix_equiv_self (finCongr h2m_pos.symm) M2
  have hM2'_exp : M2'.det = -2 * (M2'.submatrix Fin.succ Fin.succ).det := by
    have h := det_eq_single_row_zero M2' 0 (fun j hj => by
      simp only [M2', submatrix_apply, Fin.cast_zero, M2, of_apply, M1, Matrix.updateRow_apply,
        ↓reduceIte, row0]
      have hj0 : j.val ≠ 0 := fun hz => hj (Fin.ext hz)
      by_cases hsv : j.val = 2 * m - 1
      · have hs : Fin.cast h2m_pos.symm j = ⟨2 * m - 1, by omega⟩ := Fin.ext (by simp [hsv])
        have hne0 : 2 * m - 1 ≠ 0 := by omega
        simp [hs, hne0]; norm_num
      · have hs : Fin.cast h2m_pos.symm j ≠ ⟨2 * m - 1, by omega⟩ :=
          fun h => hsv (by simpa [Fin.ext_iff] using h)
        simp [hs, hsv, hj0])
    have h00 : M2' 0 0 = -2 := by
      have hne_last : (0 : Fin (2 * m)) ≠ ⟨2 * m - 1, by omega⟩ := by
        simp [Fin.ext_iff]; omega
      simp [M2', M2, M1, Matrix.updateRow_apply, row0, hne_last]
    simpa [h00] using h
  -- Step 4: Analyze S := M2'.submatrix Fin.succ Fin.succ of size (2*m - 1) = (2*m - 2) + 1
  let S := M2'.submatrix Fin.succ Fin.succ
  have hS_pos : 0 < S.det := by
    have h2m2 : 2 * m - 1 = (2 * m - 2) + 1 := by omega
    let S' : Matrix (Fin ((2 * m - 2) + 1)) (Fin ((2 * m - 2) + 1)) ℝ :=
      S.submatrix (Fin.cast h2m2.symm) (Fin.cast h2m2.symm)
    have hS'_det : S'.det = S.det := Matrix.det_submatrix_equiv_self (finCongr h2m2.symm) S
    -- Split last column of S' into base_col + pert_col
    let base_col : Fin ((2 * m - 2) + 1) → ℝ := fun i =>
      if i.val = 2 * m - 2 then 1 else if i.val + 1 = 2 * m - 2 then 5 else 0
    let pert_col : Fin ((2 * m - 2) + 1) → ℝ := fun i => if i.val = 0 then -3 else 0
    let S_base : Matrix (Fin ((2 * m - 2) + 1)) (Fin ((2 * m - 2) + 1)) ℝ :=
      Matrix.of fun i j => if j = Fin.last (2 * m - 2) then base_col i else S' i j
    let S_pert : Matrix (Fin ((2 * m - 2) + 1)) (Fin ((2 * m - 2) + 1)) ℝ :=
      Matrix.of fun i j => if j = Fin.last (2 * m - 2) then pert_col i else S' i j
    have hS'_split : S' = Matrix.of fun i j =>
        if j = Fin.last (2 * m - 2) then base_col i + pert_col i else S' i j := by
      ext i j
      simp only [of_apply]
      split_ifs with hj
      · subst hj
        simp only [base_col, pert_col, S', submatrix_apply, S, M2', M2, of_apply, M1]
        have hcol_eq : (Fin.cast h2m_pos.symm (Fin.cast h2m2.symm (Fin.last (2 * m - 2))).succ) =
            ⟨2 * m - 1, by omega⟩ := by
          simp only [Fin.ext_iff, Fin.val_cast, Fin.val_succ, Fin.val_last]; omega
        have hrow_ne0 : (Fin.cast h2m_pos.symm (Fin.cast h2m2.symm i).succ) ≠ 0 := by
          intro h; simp only [Fin.ext_iff, Fin.val_cast, Fin.val_succ, Fin.val_zero] at h; omega
        have hrow_val : (Fin.cast h2m_pos.symm (Fin.cast h2m2.symm i).succ).val = i.val + 1 := by
          simp
        have hrow_ne0' : (Fin.cast h2m_pos.symm (Fin.cast h2m2.symm i).succ).val ≠ 0 := by omega
        have hcol_ne0' : (⟨2 * m - 1, by omega⟩ : Fin (2 * m)).val ≠ 0 := by simp; omega
        simp only [hcol_eq, ↓reduceIte, Matrix.updateRow_apply, hrow_ne0]
        rw [matNegFive_ne_zero m _ ⟨2 * m - 1, by omega⟩ hrow_ne0' hcol_ne0']
        have h0_val : (0 : Fin (2 * m)).val = 0 := by simp
        have hlast_val : (⟨2 * m - 1, by omega⟩ : Fin (2 * m)).val = 2 * m - 1 := rfl
        have hM1_0 : matNegFive m (Fin.cast h2m_pos.symm (Fin.cast h2m2.symm i).succ) 0 =
            if i.val = 0 ∨ i.val = 2 * m - 2 then -1 else 0 := by
          simp only [matNegFive, of_apply, Fin.ext_iff, hrow_val, h0_val]
          have hno1 : i.val + 1 ≠ 0 := by omega
          simp only [hno1, ↓reduceIte]
          by_cases h0 : i.val = 0
          · simp [h0]
          · by_cases hlast : i.val = 2 * m - 2
            · simp [hlast]; omega
            · simp [h0, hlast]; omega
        rw [hM1_0, hrow_val, hlast_val]
        split_ifs <;> first | (norm_num; done) | omega
      · rfl
    have hdet_split : S'.det = S_base.det + S_pert.det := by
      have hT : S'ᵀ = Matrix.updateRow S_baseᵀ (Fin.last (2 * m - 2)) (base_col + pert_col) := by
        ext r s
        rw [hS'_split]
        simp only [transpose_apply, of_apply, S_base, Matrix.updateRow_apply]
        by_cases hr : r = Fin.last (2 * m - 2) <;> simp [hr]
      have hB : S_baseᵀ = Matrix.updateRow S'ᵀ (Fin.last (2 * m - 2)) base_col := by
        ext r s
        simp only [transpose_apply, of_apply, S_base, Matrix.updateRow_apply]
      have hP : S_pertᵀ = Matrix.updateRow S'ᵀ (Fin.last (2 * m - 2)) pert_col := by
        ext r s
        simp only [transpose_apply, of_apply, S_pert, Matrix.updateRow_apply]
      rw [← Matrix.det_transpose S', hT]
      have hadd := Matrix.det_updateRow_add S_baseᵀ (Fin.last (2 * m - 2)) base_col pert_col
      have hupd1 : Matrix.updateRow S_baseᵀ (Fin.last (2 * m - 2)) base_col = S_baseᵀ := by
        rw [hB]; ext r s; simp only [Matrix.updateRow_apply]; by_cases hr : r = Fin.last (2 * m - 2) <;> simp [hr]
      have hupd2 : Matrix.updateRow S_baseᵀ (Fin.last (2 * m - 2)) pert_col = S_pertᵀ := by
        rw [hB, hP]; ext r s; simp only [Matrix.updateRow_apply]; by_cases hr : r = Fin.last (2 * m - 2) <;> simp [hr]
      rw [hupd1, hupd2] at hadd
      rw [hadd, Matrix.det_transpose, Matrix.det_transpose]
    -- Compute S_pert.det = -3
    have hpert_det : S_pert.det = -3 := by
      have hcol : ∀ i : Fin ((2 * m - 2) + 1), i ≠ 0 → S_pert i (Fin.last (2 * m - 2)) = 0 := by
        intro i hi
        simp [S_pert, pert_col, hi]
      have hexp := det_eq_single_col_last S_pert 0 hcol
      have hval : S_pert 0 (Fin.last (2 * m - 2)) = -3 := by simp [S_pert, pert_col]
      rw [hval, Fin.val_zero, add_zero] at hexp
      have heven : (-1 : ℝ) ^ (2 * m - 2) = 1 := by
        have : 2 * m - 2 = 2 * (m - 1) := by omega
        rw [this, pow_mul]; norm_num
      have hsub_tri : (S_pert.submatrix (Fin.succAbove 0) Fin.castSucc).det = 1 := by
        let L := S_pert.submatrix (Fin.succAbove 0) Fin.castSucc
        have htri : L.BlockTriangular id := by
          intro i j hij
          dsimp only [id] at hij
          have hij_lt : j.val < i.val := hij
          have hj_ne : j.castSucc ≠ Fin.last (2 * m - 2) := Fin.castSucc_ne_last j
          simp only [L, submatrix_apply, S_pert, of_apply, hj_ne, ↓reduceIte, S', S, M2', M2, M1,
            Fin.succAbove_zero]
          have hrow_ne0 : (Fin.cast h2m_pos.symm (Fin.cast h2m2.symm i.succ).succ) ≠ 0 := by
            intro h; simp only [Fin.ext_iff, Fin.val_cast, Fin.val_succ, Fin.val_zero] at h; omega
          have hcol_ne : (Fin.cast h2m_pos.symm (Fin.cast h2m2.symm j.castSucc).succ) ≠
              ⟨2 * m - 1, by omega⟩ := by
            intro h; simp only [Fin.ext_iff, Fin.val_cast, Fin.val_succ, Fin.val_castSucc] at h; omega
          have hrow_val : (Fin.cast h2m_pos.symm (Fin.cast h2m2.symm i.succ).succ).val = i.val + 2 := by
            simp
          have hcol_val : (Fin.cast h2m_pos.symm (Fin.cast h2m2.symm j.castSucc).succ).val = j.val + 1 := by
            simp
          have hrow_ne0' : (Fin.cast h2m_pos.symm (Fin.cast h2m2.symm i.succ).succ).val ≠ 0 := by omega
          have hcol_ne0' : (Fin.cast h2m_pos.symm (Fin.cast h2m2.symm j.castSucc).succ).val ≠ 0 := by omega
          simp only [hcol_ne, ↓reduceIte, Matrix.updateRow_apply, hrow_ne0]
          rw [matNegFive_ne_zero m _ _ hrow_ne0' hcol_ne0', hrow_val, hcol_val]
          simp [show i.val + 2 ≠ j.val + 1 by omega]
          split_ifs <;> (try norm_num) <;> omega
        rw [Matrix.det_of_isUpperTriangular htri]
        have hdiag : ∀ i : Fin (2 * m - 2), L i i = -1 := by
          intro i
          have hi_ne : i.castSucc ≠ Fin.last (2 * m - 2) := Fin.castSucc_ne_last i
          simp only [L, submatrix_apply, S_pert, of_apply, hi_ne, ↓reduceIte, S', S, M2', M2, M1,
            Fin.succAbove_zero]
          have hrow_ne0 : (Fin.cast h2m_pos.symm (Fin.cast h2m2.symm i.succ).succ) ≠ 0 := by
            intro h; simp only [Fin.ext_iff, Fin.val_cast, Fin.val_succ, Fin.val_zero] at h; omega
          have hcol_ne : (Fin.cast h2m_pos.symm (Fin.cast h2m2.symm i.castSucc).succ) ≠
              ⟨2 * m - 1, by omega⟩ := by
            intro h; simp only [Fin.ext_iff, Fin.val_cast, Fin.val_succ, Fin.val_castSucc] at h; omega
          have hrow_val : (Fin.cast h2m_pos.symm (Fin.cast h2m2.symm i.succ).succ).val = i.val + 2 := by
            simp
          have hcol_val : (Fin.cast h2m_pos.symm (Fin.cast h2m2.symm i.castSucc).succ).val = i.val + 1 := by
            simp
          have hrow_ne0' : (Fin.cast h2m_pos.symm (Fin.cast h2m2.symm i.succ).succ).val ≠ 0 := by omega
          have hcol_ne0' : (Fin.cast h2m_pos.symm (Fin.cast h2m2.symm i.castSucc).succ).val ≠ 0 := by omega
          simp only [hcol_ne, ↓reduceIte, Matrix.updateRow_apply, hrow_ne0]
          rw [matNegFive_ne_zero m _ _ hrow_ne0' hcol_ne0', hrow_val, hcol_val]
          simp
        simp only [hdiag, Finset.prod_const, Finset.card_fin]
        have : 2 * m - 2 = 2 * (m - 1) := by omega
        rw [this, pow_mul]; norm_num
      rw [heven, one_mul, hsub_tri, mul_one] at hexp
      exact hexp
    -- Compute S_base.det = (tridiagFive (2 * m - 2)).det + 5 * (tridiagFive (2 * m - 3)).det
    have hbase_det : S_base.det =
        (tridiagFive (2 * m - 2)).det + 5 * (tridiagFive (2 * m - 3)).det := by
      rw [Matrix.det_succ_row S_base (Fin.last (2 * m - 2))]
      have hlast_row : ∀ j : Fin ((2 * m - 2) + 1),
          j ≠ ⟨2 * m - 3, by omega⟩ → j ≠ Fin.last (2 * m - 2) →
          S_base (Fin.last (2 * m - 2)) j = 0 := by
        intro j hj1 hj2
        have hjv1 : j.val ≠ 2 * m - 3 := fun h => hj1 (Fin.ext h)
        have hjv2 : j.val ≠ 2 * m - 2 := fun h => hj2 (Fin.ext (by simp [h]))
        simp only [S_base, of_apply, hj2, ↓reduceIte, S', submatrix_apply, S, M2', M2, M1]
        have hrow_ne0 : (Fin.cast h2m_pos.symm (Fin.cast h2m2.symm (Fin.last (2 * m - 2))).succ) ≠ 0 := by
          intro h; simp only [Fin.ext_iff, Fin.val_cast, Fin.val_succ, Fin.val_last, Fin.val_zero] at h; omega
        have hcol_ne : (Fin.cast h2m_pos.symm (Fin.cast h2m2.symm j).succ) ≠
            ⟨2 * m - 1, by omega⟩ := by
          intro h; simp only [Fin.ext_iff, Fin.val_cast, Fin.val_succ] at h; omega
        have hrow_val : (Fin.cast h2m_pos.symm (Fin.cast h2m2.symm (Fin.last (2 * m - 2))).succ).val = 2 * m - 1 := by
          simp only [Fin.val_cast, Fin.val_succ, Fin.val_last]; omega
        have hcol_val : (Fin.cast h2m_pos.symm (Fin.cast h2m2.symm j).succ).val = j.val + 1 := by
          simp
        have hrow_ne0' : (Fin.cast h2m_pos.symm (Fin.cast h2m2.symm (Fin.last (2 * m - 2))).succ).val ≠ 0 := by omega
        have hcol_ne0' : (Fin.cast h2m_pos.symm (Fin.cast h2m2.symm j).succ).val ≠ 0 := by omega
        simp only [hcol_ne, ↓reduceIte, Matrix.updateRow_apply, hrow_ne0]
        rw [matNegFive_ne_zero m _ _ hrow_ne0' hcol_ne0', hrow_val, hcol_val]
        simp [show 2 * m - 1 ≠ j.val + 1 by omega, show j.val + 1 + 1 ≠ 2 * m - 1 by omega]
        omega
      have hsum : ∑ j : Fin ((2 * m - 2) + 1), (-1) ^ ((Fin.last (2 * m - 2) : ℕ) + (j : ℕ)) *
            S_base (Fin.last (2 * m - 2)) j *
            (S_base.submatrix (Fin.last (2 * m - 2)).succAbove j.succAbove).det =
          (-1) ^ ((2 * m - 2) + (2 * m - 3)) * (-1) *
            (S_base.submatrix (Fin.last (2 * m - 2)).succAbove (⟨2 * m - 3, by omega⟩ : Fin ((2 * m - 2) + 1)).succAbove).det +
          (-1) ^ ((2 * m - 2) + (2 * m - 2)) * 1 *
            (S_base.submatrix (Fin.last (2 * m - 2)).succAbove (Fin.last (2 * m - 2)).succAbove).det := by
        have hsub : ∑ j : Fin ((2 * m - 2) + 1), (-1) ^ ((Fin.last (2 * m - 2) : ℕ) + (j : ℕ)) *
              S_base (Fin.last (2 * m - 2)) j *
              (S_base.submatrix (Fin.last (2 * m - 2)).succAbove j.succAbove).det =
            ∑ j ∈ ({⟨2 * m - 3, by omega⟩, Fin.last (2 * m - 2)} : Finset (Fin ((2 * m - 2) + 1))),
              (-1) ^ ((Fin.last (2 * m - 2) : ℕ) + (j : ℕ)) *
                S_base (Fin.last (2 * m - 2)) j *
                (S_base.submatrix (Fin.last (2 * m - 2)).succAbove j.succAbove).det := by
          refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
          intro j _ hj
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
          simp [hlast_row j hj.1 hj.2]
        rw [hsub, Finset.sum_pair (by simp [Fin.ext_iff]; omega)]
        have hv1 : S_base (Fin.last (2 * m - 2)) ⟨2 * m - 3, by omega⟩ = -1 := by
          have hne : (⟨2 * m - 3, by omega⟩ : Fin ((2 * m - 2) + 1)) ≠ Fin.last (2 * m - 2) := by
            simp [Fin.ext_iff]; omega
          simp only [S_base, of_apply, hne, ↓reduceIte, S', submatrix_apply, S, M2', M2, M1]
          have hrow_ne0 : (Fin.cast h2m_pos.symm (Fin.cast h2m2.symm (Fin.last (2 * m - 2))).succ) ≠ 0 := by
            simp [Fin.ext_iff]
          have hcol_ne : (Fin.cast h2m_pos.symm (Fin.cast h2m2.symm ⟨2 * m - 3, by omega⟩).succ) ≠
              ⟨2 * m - 1, by omega⟩ := by
            simp [Fin.ext_iff]; omega
          simp only [hcol_ne, ↓reduceIte, Matrix.updateRow_apply, hrow_ne0, matNegFive]
          simp only [of_apply, Fin.ext_iff, Fin.val_cast, Fin.val_succ, Fin.val_last]
          split_ifs <;> (try norm_num) <;> omega
        have hv2 : S_base (Fin.last (2 * m - 2)) (Fin.last (2 * m - 2)) = 1 := by
          simp [S_base, base_col]
        -- Note: fix j.succAbove for ⟨2*m-3⟩
        simp [hv1, hv2, Fin.val_last]
      -- Simplify the two minors of S_base
      have hmin1 : S_base.submatrix (Fin.last (2 * m - 2)).succAbove (Fin.last (2 * m - 2)).succAbove =
          tridiagFive (2 * m - 2) := by
        ext i j
        have hi_lt : i.val < 2 * m - 2 := i.isLt
        have hj_lt : j.val < 2 * m - 2 := j.isLt
        simp only [submatrix_apply, S_base, of_apply, Fin.succAbove_last, Fin.castSucc_ne_last,
          ↓reduceIte, S', S, M2', M2, M1, tridiagFive]
        have hrow_ne0 : (Fin.cast h2m_pos.symm (Fin.cast h2m2.symm i.castSucc).succ) ≠ 0 := by
          simp [Fin.ext_iff]
        have hcol_ne : (Fin.cast h2m_pos.symm (Fin.cast h2m2.symm j.castSucc).succ) ≠
            ⟨2 * m - 1, by omega⟩ := by
          simp [Fin.ext_iff]; omega
        simp only [hcol_ne, ↓reduceIte, Matrix.updateRow_apply, hrow_ne0, matNegFive]
        simp only [of_apply, Fin.ext_iff, Fin.val_cast, Fin.val_succ, Fin.val_castSucc]
        split_ifs <;> (try norm_num) <;> omega
      have hmin2 : (S_base.submatrix (Fin.last (2 * m - 2)).succAbove
          ((⟨2 * m - 3, by omega⟩ : Fin ((2 * m - 2) + 1)).succAbove)).det =
          5 * (tridiagFive (2 * m - 3)).det := by
        have h2m2' : 2 * m - 2 = (2 * m - 3) + 1 := by omega
        let U := (S_base.submatrix (Fin.last (2 * m - 2)).succAbove
          ((⟨2 * m - 3, by omega⟩ : Fin ((2 * m - 2) + 1)).succAbove)).submatrix
          (Fin.cast h2m2'.symm) (Fin.cast h2m2'.symm)
        have hU_det : U.det =
            (S_base.submatrix (Fin.last (2 * m - 2)).succAbove
              ((⟨2 * m - 3, by omega⟩ : Fin ((2 * m - 2) + 1)).succAbove)).det :=
          Matrix.det_submatrix_equiv_self (finCongr h2m2'.symm) _
        have hcol : ∀ i : Fin ((2 * m - 3) + 1), i ≠ Fin.last (2 * m - 3) →
            U i (Fin.last (2 * m - 3)) = 0 := by
          intro i hi
          have hiv : i.val < 2 * m - 3 := by
            have := i.isLt
            have hne : i.val ≠ 2 * m - 3 := fun h => hi (Fin.ext (by simp [h]))
            omega
          have hcol_eq : (⟨2 * m - 3, by omega⟩ : Fin ((2 * m - 2) + 1)).succAbove
              (Fin.cast h2m2'.symm (Fin.last (2 * m - 3))) = Fin.last (2 * m - 2) := by
            simp only [Fin.succAbove, Fin.ext_iff, Fin.val_last]
            split_ifs with h
            · exfalso; simp [Fin.lt_def] at h
            · simp; omega
          simp only [U, submatrix_apply, hcol_eq, S_base, of_apply, ↓reduceIte, base_col,
            Fin.succAbove_last, Fin.val_castSucc, Fin.val_cast]
          split_ifs <;> first | rfl | (norm_num; omega)
        have hU_exp := det_eq_single_col_last U (Fin.last (2 * m - 3)) hcol
        have hU_last : U (Fin.last (2 * m - 3)) (Fin.last (2 * m - 3)) = 5 := by
          have hcol_eq : (⟨2 * m - 3, by omega⟩ : Fin ((2 * m - 2) + 1)).succAbove
              (Fin.cast h2m2'.symm (Fin.last (2 * m - 3))) = Fin.last (2 * m - 2) := by
            simp only [Fin.succAbove, Fin.ext_iff, Fin.val_last]
            split_ifs with h
            · exfalso; simp [Fin.lt_def] at h
            · simp; omega
          simp only [U, submatrix_apply, hcol_eq, S_base, of_apply, ↓reduceIte, base_col,
            Fin.succAbove_last, Fin.val_castSucc, Fin.val_cast, Fin.val_last]
          split_ifs <;> first | rfl | (norm_num; omega)
        have hU_sub : U.submatrix (Fin.last (2 * m - 3)).succAbove Fin.castSucc = tridiagFive (2 * m - 3) := by
          ext i j
          have hi_lt : i.val < 2 * m - 3 := i.isLt
          have hj_lt : j.val < 2 * m - 3 := j.isLt
          have hcol_ne : (⟨2 * m - 3, by omega⟩ : Fin ((2 * m - 2) + 1)).succAbove
              (Fin.cast h2m2'.symm j.castSucc) ≠ Fin.last (2 * m - 2) := by
            simp only [Fin.succAbove]
            split_ifs with h
            · simp
            · exfalso; simp only [Fin.lt_def, Fin.val_cast, Fin.val_castSucc] at h; omega
          have hcol_val : ((⟨2 * m - 3, by omega⟩ : Fin ((2 * m - 2) + 1)).succAbove
              (Fin.cast h2m2'.symm j.castSucc)).val = j.val := by
            simp only [Fin.succAbove]
            split_ifs with h
            · rfl
            · exfalso; simp only [Fin.lt_def, Fin.val_cast, Fin.val_castSucc] at h; omega
          simp only [U, submatrix_apply, S_base, of_apply, hcol_ne, ↓reduceIte, S', S, M2', M2, M1,
            Fin.succAbove_last, tridiagFive]
          have hrow_ne0 : (Fin.cast h2m_pos.symm (Fin.cast h2m2.symm
              ((Fin.cast h2m2'.symm i.castSucc).castSucc)).succ) ≠ 0 := by
            simp [Fin.ext_iff]
          have hcol_ne' : (Fin.cast h2m_pos.symm (Fin.cast h2m2.symm
              ((⟨2 * m - 3, by omega⟩ : Fin ((2 * m - 2) + 1)).succAbove (Fin.cast h2m2'.symm j.castSucc))).succ) ≠
              ⟨2 * m - 1, by omega⟩ := by
            simp [Fin.ext_iff, hcol_val]; omega
          have hrow_val : (Fin.cast h2m_pos.symm (Fin.cast h2m2.symm
              ((Fin.cast h2m2'.symm i.castSucc).castSucc)).succ).val = i.val + 1 := by
            simp
          have hcol_val' : (Fin.cast h2m_pos.symm (Fin.cast h2m2.symm
              ((⟨2 * m - 3, by omega⟩ : Fin ((2 * m - 2) + 1)).succAbove (Fin.cast h2m2'.symm j.castSucc))).succ).val = j.val + 1 := by
            simp [hcol_val]
          have hrow_ne0' : (Fin.cast h2m_pos.symm (Fin.cast h2m2.symm
              ((Fin.cast h2m2'.symm i.castSucc).castSucc)).succ).val ≠ 0 := by omega
          have hcol_ne0' : (Fin.cast h2m_pos.symm (Fin.cast h2m2.symm
              ((⟨2 * m - 3, by omega⟩ : Fin ((2 * m - 2) + 1)).succAbove (Fin.cast h2m2'.symm j.castSucc))).succ).val ≠ 0 := by omega
          simp only [hcol_ne', ↓reduceIte, Matrix.updateRow_apply, hrow_ne0]
          rw [matNegFive_ne_zero m _ _ hrow_ne0' hcol_ne0', hrow_val, hcol_val']
          simp [Fin.ext_iff]
        rw [hU_last, Fin.val_last, hU_sub] at hU_exp
        have heven : (-1 : ℝ) ^ ((2 * m - 3) + (2 * m - 3)) = 1 := by
          have : (2 * m - 3) + (2 * m - 3) = 2 * (2 * m - 3) := by omega
          rw [this, pow_mul]; norm_num
        rw [heven, one_mul] at hU_exp
        rw [← hU_det, hU_exp]
      -- Finish hbase_det: note Fin.succAbove in hsum
      have hpow_odd : (-1 : ℝ) ^ ((2 * m - 2) + (2 * m - 3)) = -1 := by
        have : (2 * m - 2) + (2 * m - 3) = 2 * (2 * m - 3) + 1 := by omega
        rw [this, pow_add, pow_mul]; norm_num
      have hpow_even : (-1 : ℝ) ^ ((2 * m - 2) + (2 * m - 2)) = 1 := by
        have : (2 * m - 2) + (2 * m - 2) = 2 * (2 * m - 2) := by omega
        rw [this, pow_mul]; norm_num
      rw [hsum, hmin1, hmin2, hpow_odd, hpow_even]
      ring
    have hge4 := det_tridiagFive_ge_four.2
    have h1 := hge4 (2 * m - 2) (by omega)
    have h2 := hge4 (2 * m - 3) (by omega)
    rw [← hS'_det, hdet_split, hbase_det, hpert_det]
    linarith
  rw [← hM1_det, ← hM2_det, ← hM2'_det, hM2'_exp]
  linarith

/-- At `x = -1`, `det (-I - w) = -4 < 0` for every `C_{2m}(+, -, ..., -)` (`m ≥ 2`). -/
theorem evenCycleSinglePlus_charpoly_at_neg_one (m : ℕ) (hm : 2 ≤ m) :
    ((-1 : ℝ) • (1 : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ) - w_evenCycleSinglePlus m hm).det = -4 := by
  unfold w_evenCycleSinglePlus
  rw [principal_charpoly_eq, howlettU_evenCycle_det, howlett_neg_one_eq, det_matNegOne m hm]
  norm_num

/-- At `x = -5`, `det (-5 I - w) > 0` for every `C_{2m}(+, -, ..., -)` (`m ≥ 2`). -/
theorem evenCycleSinglePlus_charpoly_at_neg_five (m : ℕ) (hm : 2 ≤ m) :
    0 < ((-5 : ℝ) • (1 : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ) - w_evenCycleSinglePlus m hm).det := by
  unfold w_evenCycleSinglePlus
  rw [principal_charpoly_eq, howlettU_evenCycle_det, howlett_neg_five_eq]
  have hneg := det_matNegFive_lt_zero m hm
  linarith

/-- **Hyperbolicity of Even Single-Defect Cycles**: For every `m ≥ 2`, the principal element
`w_evenCycleSinglePlus m hm` of `C_{2m}(+, -, ..., -)` has a real eigenvalue `μ < -1`
(in `(-5, -1)`), hence `|μ| > 1` (spectral radius `> 1`). -/
theorem evenCycleSinglePlus_has_eigenvalue_lt_neg_one (m : ℕ) (hm : 2 ≤ m) :
    ∃ μ : ℝ, μ < -1 ∧ ∃ v : Fin (2 * m) → ℝ, v ≠ 0 ∧
      (w_evenCycleSinglePlus m hm).mulVec v = μ • v := by
  let f : ℝ → ℝ := fun x =>
    (x • (1 : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ) - w_evenCycleSinglePlus m hm).det
  have hf_cont : Continuous f := by
    dsimp only [f]
    simp_rw [Matrix.det_apply]
    refine continuous_finsetSum _ fun σ _ => ?_
    refine Continuous.const_smul ?_ _
    refine continuous_finsetProd _ fun i _ => ?_
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, one_apply]
    exact ((continuous_id.mul continuous_const).sub continuous_const)
  have hf5 : 0 < f (-5) := evenCycleSinglePlus_charpoly_at_neg_five m hm
  have hf1 : f (-1) < 0 := by
    change ((-1 : ℝ) • 1 - w_evenCycleSinglePlus m hm).det < 0
    rw [evenCycleSinglePlus_charpoly_at_neg_one m hm]
    norm_num
  have hmem : (0 : ℝ) ∈ Set.Icc (f (-1)) (f (-5)) := ⟨le_of_lt hf1, le_of_lt hf5⟩
  obtain ⟨μ, hμ_icc, hμ_root⟩ :=
    intermediate_value_Icc' (by norm_num : (-5 : ℝ) ≤ -1) hf_cont.continuousOn hmem
  have hμ_lt : μ < -1 := by
    rcases lt_or_eq_of_le hμ_icc.2 with hlt | heq
    · exact hlt
    · exfalso; rw [heq] at hμ_root; linarith
  have hsing : ∃ v : Fin (2 * m) → ℝ, v ≠ 0 ∧
      (μ • (1 : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ) - w_evenCycleSinglePlus m hm).mulVec v = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.mpr hμ_root
  obtain ⟨v, hv, hmul⟩ := hsing
  refine ⟨μ, hμ_lt, v, hv, ?_⟩
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hmul
  exact hmul.symm

end EvenCycleSingleDefect

end MixedSignCoxeter
