import Mathlib


----------------------------------------------------------------
--------------------------Lemmas--------------------------------
----------------------------------------------------------------

/--
`2` is nonzero in `ℂ`.
Used to justify inverses such as `(2 : ℂ)⁻¹` in normalization proofs.
-/
lemma two_ne_zero_complex : (2 : ℂ) ≠ 0 := by
  norm_num


/--
In `ℂ`, squaring `√2` gives `2`.
This is the algebraic identity needed to simplify the `1 / √2` factors
when proving normalization of `|+⟩` and `|s⟩`.
-/
lemma sqrt2_sq_complex : ((Real.sqrt 2 : ℂ) ^ 2) = (2 : ℂ) := by
  have hR : (Real.sqrt 2) ^ 2 = (2 : ℝ) := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  exact_mod_cast hR



----------------------------------------------------------------
--------------------------Bra State-----------------------------
----------------------------------------------------------------
/-- Bra associated to `ψ` in any finite-dimensional computational basis. -/
noncomputable def bra {n : ℕ} (ψ : Fin n → ℂ) : (Fin n → ℂ) → ℂ :=
  fun φ => ∑ i : Fin n, star (ψ i) * φ i



----------------------------------------------------------------
--------------------------Single Qubit--------------------------
----------------------------------------------------------------

/-- A single-qubit pure state represented as amplitudes on basis indices `0,1`. -/
abbrev Qubit := Fin 2 → ℂ

/-- Computational basis state `|0⟩`. -/
def ket0 : Qubit :=
  ![1, 0]

/-- Computational basis state `|1⟩`. -/
def ket1 : Qubit :=
  ![0, 1]

/-- Hadamard gate on a single qubit. -/
noncomputable def hadamard (ψ : Qubit) : Qubit :=
  ![
    (ψ 0 + ψ 1) / Real.sqrt 2,
    (ψ 0 - ψ 1) / Real.sqrt 2
  ]

/-- `|+⟩ = H|0⟩` for a single qubit. -/
noncomputable def ketPlus : Qubit :=
  hadamard ket0


/-- Single qubit state normalization and orthogonalization. -/
theorem bra_ket0_ket0 : bra ket0 ket0 = 1 := by
  simp [bra, ket0]

theorem bra_ket1_ket1 : bra ket1 ket1 = 1 := by
  simp [bra, ket1]

theorem bra_ket0_ket1 : bra ket0 ket1 = 0 := by
  simp [bra, ket0, ket1]

theorem bra_ket1_ket0 : bra ket1 ket0 = 0 := by
  simp [bra, ket0, ket1]

/-- The `|+⟩` state is normalized: `⟨+|+⟩ = 1`. -/
theorem bra_ketPlus_ketPlus : bra ketPlus ketPlus = 1 := by
  simp [bra, ketPlus, hadamard, ket0]
  ring_nf
  simp [sqrt2_sq_complex]



----------------------------------------------------------------
--------------------------n-Qubits State------------------------
----------------------------------------------------------------

/-- Computational-basis index type for `(n+1)` qubits. -/
abbrev BasisIdx (n : ℕ) := Fin (2 ^ (n + 1))

/-- State space for `(n+1)` qubits in computational basis indexing. -/
abbrev State (n : ℕ) := BasisIdx n → ℂ

/-- Linear operators acting on `State n`. -/
abbrev Operator (n : ℕ) := State n → State n

/-- Computational basis ket `|y⟩` as a state function. -/
def basisKet (n : ℕ) (y : BasisIdx n) : State n :=
  fun x => if x = y then 1 else 0

/--
Adjoint (dagger) of an operator in the computational basis.
Defined by conjugate-transposing its matrix elements.
-/
noncomputable def dagger (n : ℕ) (U : Operator n) : Operator n :=
  fun ψ x => ∑ y : BasisIdx n, star (U (basisKet n y) x) * ψ y

/-- Density matrices on `(n+1)` qubits in the computational basis. -/
abbrev DensityMatrix (n : ℕ) := Matrix (BasisIdx n) (BasisIdx n) ℂ

/-- Pure-state density matrix `|ψ⟩⟨ψ|`. -/
noncomputable def pureDensity (n : ℕ) (ψ : State n) : DensityMatrix n :=
  fun x y => ψ x * star (ψ y)


/--
Split an index of `2^(n+1)` basis states into:
1 qubit index (`Fin 2`) and the remaining `n`-qubit index (`Fin (2^n)`).
-/
def splitQubitIndex {n : ℕ} (i : BasisIdx n) : Fin 2 × Fin (2 ^ n) :=
  ( ⟨i.1 % 2, Nat.mod_lt _ (by decide)⟩
  , ⟨i.1 / 2, by
      have hi : i.1 < 2 ^ n * 2 := by
        simpa [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using i.2
      exact (Nat.div_lt_iff_lt_mul (by decide : 0 < (2 : ℕ))).2 <| by
        simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hi
    ⟩ )

/--
Initial QAOA state on `n+1` qubits, defined as `|s⟩ = |+⟩^{⊗ (n+1)}`.
This encoding avoids the `n=0` scalar base case.
-/
noncomputable def s : (n : ℕ) → State n
  | 0 => ketPlus
  | n + 1 => fun i =>
      let p := splitQubitIndex (n := n + 1) i
      ketPlus p.1 * s n p.2

/-- Density matrix of the initial state `|s⟩`: `ρ_s = |s⟩⟨s|`. -/
noncomputable def rho_s (n : ℕ) : DensityMatrix n :=
  pureDensity n (s n)

/-- The initial state's density matrix has unit trace. -/
theorem trace_rho_s_eq_one (n : ℕ) : Matrix.trace (rho_s n) = 1 := by
  let c : ℂ := (Real.sqrt 2 : ℂ)⁻¹
  have hketPlus : ∀ i : Fin 2, ketPlus i = c := by
    intro i
    fin_cases i <;> simp [ketPlus, hadamard, ket0, c]
  have hs_const : ∀ n : ℕ, ∀ i : BasisIdx n, s n i = c ^ (n + 1) := by
    intro n
    induction n with
    | zero =>
        intro i
        fin_cases i <;> simp [s, hketPlus, c]
    | succ n ih =>
        intro i
        simp [s, hketPlus, ih, pow_succ, mul_comm]
  have hc2 : c * c = (2 : ℂ)⁻¹ := by
    dsimp [c]
    ring_nf
    simp [sqrt2_sq_complex]
  calc
    Matrix.trace (rho_s n)
        = ∑ i : BasisIdx n, s n i * star (s n i) := by
            unfold rho_s pureDensity
            simp [Matrix.trace]
    _ = ∑ i : BasisIdx n, star (s n i) * s n i := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          ring
    _ = ∑ _i : BasisIdx n, star (c ^ (n + 1)) * (c ^ (n + 1)) := by
          simp [hs_const]
    _ = (2 ^ (n + 1) : ℂ) * (star (c ^ (n + 1)) * c ^ (n + 1)) := by
          simp
    _ = (2 ^ (n + 1) : ℂ) * (c ^ (n + 1) * c ^ (n + 1)) := by
          simp [c]
    _ = (2 ^ (n + 1) : ℂ) * ((c * c) ^ (n + 1)) := by
          rw [← mul_pow]
    _ = (2 ^ (n + 1) : ℂ) * (((2 : ℂ)⁻¹) ^ (n + 1)) := by
          simp [hc2]
    _ = (2 : ℂ) ^ (n + 1) * ((2 : ℂ)⁻¹ ^ (n + 1)) := by
          norm_num
    _ = ((2 : ℂ) * (2 : ℂ)⁻¹) ^ (n + 1) := by
          rw [(mul_pow (2 : ℂ) ((2 : ℂ)⁻¹) (n + 1)).symm]
    _ = 1 := by
          simp



----------------------------------------------------------------
--------------------------The Mixer Operator--------------------
----------------------------------------------------------------

/-- Hamming distance between computational-basis indices (`(n+1)`-bit strings). -/
def basisHammingDist (n : ℕ) (x y : BasisIdx n) : ℕ :=
  ((Finset.range (n + 1)).filter (fun j => Nat.testBit x.1 j ≠ Nat.testBit y.1 j)).card

/-- Basic bound: a Hamming distance on `(n+1)` bits is at most `n+1`. -/
lemma basisHammingDist_le (n : ℕ) (x y : BasisIdx n) :
    basisHammingDist n x y ≤ n + 1 := by
  let p : ℕ → Prop := fun j => Nat.testBit x.1 j ≠ Nat.testBit y.1 j
  unfold basisHammingDist
  calc
    ((Finset.range (n + 1)).filter p).card ≤ (Finset.range (n + 1)).card := by
      exact Finset.card_le_card (Finset.filter_subset (s := Finset.range (n + 1)) (p := p))
    _ = n + 1 := by simp

/-- Computational-basis matrix element of `U_B(β) = exp(-i β ∑_j X_j)`. -/
noncomputable def mixerEntry (n : ℕ) (β : ℝ) (x y : BasisIdx n) : ℂ :=
  let d := basisHammingDist n x y
  (Real.cos β : ℂ) ^ ((n + 1) - d) * ((-Complex.I) * (Real.sin β : ℂ)) ^ d

/-- Explicit mixer unitary action in the computational basis. -/
noncomputable def U_B (n : ℕ) (β : ℝ) : Operator n :=
  fun ψ x => ∑ y : BasisIdx n, mixerEntry n β x y * ψ y


/-- Dagger mixer operator, defined as the adjoint of `U_B`. -/
noncomputable def U_B_dagger (n : ℕ) (β : ℝ) : Operator n :=
  dagger n (U_B n β)

/--
Orthonormality of the mixer kernel:
`∑_z conj(K_{zx}) K_{zy} = δ_{xy}`.
-/
theorem MixerKernelOrthonormal (n : ℕ) (β : ℝ) :
    ∀ x y : BasisIdx n,
      (∑ z : BasisIdx n, star (mixerEntry n β z x) * mixerEntry n β z y)
        = if x = y then 1 else 0 := by
  sorry

/--
The mixer operator preserves the norm of the initial state:
`Tr((U_B†U_B) ρ_s) = 1` if the mixer kernel is orthonormal.
-/
theorem trace_U_B_dagger_mul_U_B_rho_s_eq_one
    (n : ℕ) (β : ℝ) :
    Matrix.trace
      ((let UBUB : DensityMatrix n :=
          fun x y => ∑ z : BasisIdx n, star (mixerEntry n β z x) * mixerEntry n β z y
        UBUB) * rho_s n)
      = 1 := by
  let UBUB : DensityMatrix n :=
    fun x y => ∑ z : BasisIdx n, star (mixerEntry n β z x) * mixerEntry n β z y
  have hId :
      UBUB = (1 : DensityMatrix n) := by
    ext x y
    simpa [UBUB, Matrix.one_apply] using (MixerKernelOrthonormal n β x y)
  calc
    Matrix.trace
        ((let UBUB : DensityMatrix n :=
            fun x y => ∑ z : BasisIdx n, star (mixerEntry n β z x) * mixerEntry n β z y
          UBUB) * rho_s n)
        = Matrix.trace (UBUB * rho_s n) := by simp [UBUB]
    _ = Matrix.trace ((1 : DensityMatrix n) * rho_s n) := by simp [hId]
    _ = Matrix.trace (rho_s n) := by simp
    _ = 1 := trace_rho_s_eq_one n


----------------------------------------------------------------
-------------------------SK Cost Function-----------------------
----------------------------------------------------------------

/-- SK couplings `J_{jk}` on `(n+1)` qubits. -/
abbrev SKCoupling (n : ℕ) := Fin (n + 1) → Fin (n + 1) → ℝ

/-- Spin value (`±1`) of qubit `j` in basis state `z`. -/
def spinAt (n : ℕ) (z : BasisIdx n) (j : Fin (n + 1)) : ℝ :=
  if Nat.testBit z.1 j.1 then (-1 : ℝ) else (1 : ℝ)

/-- Unordered edge set `{(j,k) | j < k}` used by the SK Hamiltonian. -/
def skEdgeSet (n : ℕ) : Finset (Fin (n + 1) × Fin (n + 1)) :=
  (Finset.univ.product Finset.univ).filter (fun jk => jk.1.1 < jk.2.1)

/-- SK normalization factor `1 / √(n+1)`. -/
noncomputable def skNormFactor (n : ℕ) : ℝ :=
  (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹

/-- SK cost value `C_J(z)` on computational basis state `z`. -/
noncomputable def skCostOnBasis (n : ℕ) (J : SKCoupling n) (z : BasisIdx n) : ℝ :=
  skNormFactor n *
    Finset.sum (skEdgeSet n) (fun jk => J jk.1 jk.2 * spinAt n z jk.1 * spinAt n z jk.2)

/-- Phase factor of the SK cost unitary `U_C(γ)` on basis state `|z⟩`. -/
noncomputable def U_C_phase (n : ℕ) (J : SKCoupling n) (γ : ℝ) (z : BasisIdx n) : ℂ :=
  Complex.exp (((-Complex.I) * (γ : ℂ)) * (skCostOnBasis n J z : ℂ))

/-- Phase factor of the adjoint cost unitary `U_C(γ)†` on basis state `|z⟩`. -/
noncomputable def U_C_dagger_phase (n : ℕ) (J : SKCoupling n) (γ : ℝ) (z : BasisIdx n) : ℂ :=
  Complex.exp (((Complex.I) * (γ : ℂ)) * (skCostOnBasis n J z : ℂ))


----------------------------------------------------------------
-----------QAOA at level p=1 state for the SK model-------------
----------------------------------------------------------------


/-- Pointwise phase cancellation: `U_C(γ)†(z) * U_C(γ)(z) = 1`. -/
lemma U_C_dagger_phase_mul_U_C_phase_eq_one
    (n : ℕ) (J : SKCoupling n) (γ : ℝ) (z : BasisIdx n) :
    U_C_dagger_phase n J γ z * U_C_phase n J γ z = 1 := by
  let a : ℂ := ((γ : ℂ) * (skCostOnBasis n J z : ℂ))
  have hsum : Complex.I * a + (-Complex.I) * a = 0 := by ring
  calc
    U_C_dagger_phase n J γ z * U_C_phase n J γ z
        = Complex.exp (Complex.I * a) * Complex.exp ((-Complex.I) * a) := by
            simp [U_C_dagger_phase, U_C_phase, a, mul_left_comm, mul_comm]
    _ = Complex.exp ((Complex.I * a) + ((-Complex.I) * a)) := by
          simpa [Complex.exp_add] using (Complex.exp_add (Complex.I * a) ((-Complex.I) * a)).symm
    _ = Complex.exp 0 := by simp
    _ = 1 := by simp

/--
Matrix entries of `U_C† U_B† U_B U_C` in computational basis.
`U_C` contributes only diagonal phase factors on the two outer sides.
-/
noncomputable def U_C_dagger_mul_U_B_dagger_mul_U_B_mul_U_C_matrix
    (n : ℕ) (J : SKCoupling n) (β γ : ℝ) : DensityMatrix n :=
  fun x y =>
    U_C_dagger_phase n J γ x *
      (∑ z : BasisIdx n, star (mixerEntry n β z x) * mixerEntry n β z y) *
      U_C_phase n J γ y

/--
`Tr((U_C† U_B† U_B U_C) ρ_s) = 1`
-/
theorem trace_U_C_dagger_mul_U_B_dagger_mul_U_B_mul_U_C_rho_s_eq_one
    (n : ℕ) (J : SKCoupling n) (β γ : ℝ) :
    Matrix.trace
      (U_C_dagger_mul_U_B_dagger_mul_U_B_mul_U_C_matrix n J β γ * rho_s n) = 1 := by
  have hIdAll :
      U_C_dagger_mul_U_B_dagger_mul_U_B_mul_U_C_matrix n J β γ = (1 : DensityMatrix n) := by
    ext x y
    calc
      U_C_dagger_mul_U_B_dagger_mul_U_B_mul_U_C_matrix n J β γ x y
          = (U_C_dagger_phase n J γ x *
              (∑ z : BasisIdx n, star (mixerEntry n β z x) * mixerEntry n β z y)) *
              U_C_phase n J γ y := by
                simp [U_C_dagger_mul_U_B_dagger_mul_U_B_mul_U_C_matrix]
      _ = (U_C_dagger_phase n J γ x * (if x = y then 1 else 0)) * U_C_phase n J γ y := by
            rw [MixerKernelOrthonormal n β x y]
      _ = if x = y then (U_C_dagger_phase n J γ x * U_C_phase n J γ y) else 0 := by
            by_cases hxy : x = y <;> simp [hxy]
      _ = if x = y then 1 else 0 := by
            by_cases hxy : x = y
            · subst hxy
              simp [U_C_dagger_phase_mul_U_C_phase_eq_one]
            · simp [hxy]
      _ = (1 : DensityMatrix n) x y := by simp [Matrix.one_apply]
  calc
    Matrix.trace (U_C_dagger_mul_U_B_dagger_mul_U_B_mul_U_C_matrix n J β γ * rho_s n)
        = Matrix.trace ((1 : DensityMatrix n) * rho_s n) := by simp [hIdAll]
    _ = Matrix.trace (rho_s n) := by simp
    _ = 1 := trace_rho_s_eq_one n
