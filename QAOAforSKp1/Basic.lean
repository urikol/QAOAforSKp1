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

/--
`⟨i|s⟩ = 1/√(2^(n+1))`
is the normalization factor for the uniform superposition on `2^(n+1)` basis states.
-/
lemma s_entry_const (n : ℕ) (i : BasisIdx n) :
    s n i = ((Real.sqrt 2 : ℂ)⁻¹) ^ (n + 1) := by
  let c : ℂ := (Real.sqrt 2 : ℂ)⁻¹
  have hketPlus : ∀ j : Fin 2, ketPlus j = c := by
    intro j
    fin_cases j <;> simp [ketPlus, hadamard, ket0, c]
  have hs_const : ∀ n : ℕ, ∀ j : BasisIdx n, s n j = c ^ (n + 1) := by
    intro n
    induction n with
    | zero =>
        intro j
        fin_cases j <;> simp [s, hketPlus, c]
    | succ n ih =>
        intro j
        simp [s, hketPlus, ih, pow_succ, mul_comm]
  simpa [c] using hs_const n i

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

/-- Computational-basis matrix element of `U_B(β) = exp(-i β ∑_j X_j)`:
⟨x|U_B(β)|y⟩ = cos(β)^(n+1-d) * (-i sin(β))^d where d is the Hamming distance between x and y.
-/
noncomputable def mixerKernel (n : ℕ) (β : ℝ) (x y : BasisIdx n) : ℂ :=
  let d := basisHammingDist n x y
  (Real.cos β : ℂ) ^ ((n + 1) - d) * ((-Complex.I) * (Real.sin β : ℂ)) ^ d

/-- Explicit mixer unitary action in the computational basis. -/
noncomputable def U_B (n : ℕ) (β : ℝ) : Operator n :=
  fun ψ x => ∑ y : BasisIdx n, mixerKernel n β x y * ψ y


/-- Dagger mixer operator, defined as the adjoint of `U_B`. -/
noncomputable def U_B_dagger (n : ℕ) (β : ℝ) : Operator n :=
  dagger n (U_B n β)

/--
Orthonormality of the mixer kernel:
`∑_z conj(K_{zx}) K_{zy} = δ_{xy}`.
-/
theorem MixerKernelOrthonormal (n : ℕ) (β : ℝ) :
    ∀ x y : BasisIdx n,
      (∑ z : BasisIdx n, star (mixerKernel n β z x) * mixerKernel n β z y)
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
          fun x y => ∑ z : BasisIdx n, star (mixerKernel n β z x) * mixerKernel n β z y
        UBUB) * rho_s n)
      = 1 := by
  let UBUB : DensityMatrix n :=
    fun x y => ∑ z : BasisIdx n, star (mixerKernel n β z x) * mixerKernel n β z y
  have hId :
      UBUB = (1 : DensityMatrix n) := by
    ext x y
    simpa [UBUB, Matrix.one_apply] using (MixerKernelOrthonormal n β x y)
  calc
    Matrix.trace
        ((let UBUB : DensityMatrix n :=
            fun x y => ∑ z : BasisIdx n, star (mixerKernel n β z x) * mixerKernel n β z y
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
      (∑ z : BasisIdx n, star (mixerKernel n β z x) * mixerKernel n β z y) *
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
              (∑ z : BasisIdx n, star (mixerKernel n β z x) * mixerKernel n β z y)) *
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


----------------------------------------------------------------
--------Expectation of the SK cost operator - Definition--------
----------------------------------------------------------------

/--
Matrix entries of `U_C† U_B† (C/(n+1)) U_B U_C` in the computational basis.
-/
noncomputable def QAOACostMatrix
    (n : ℕ) (J : SKCoupling n) (β γ : ℝ) : DensityMatrix n :=
  fun x y =>
    U_C_dagger_phase n J γ x *
      (∑ z : BasisIdx n,
        star (mixerKernel n β z x) *
          ((skCostOnBasis n J z / (n + 1 : ℝ)) : ℂ) *
          mixerKernel n β z y) *
      U_C_phase n J γ y

/--
For fixed SK coupling `J`, the p=1 QAOA normalized cost expectation:
`⟨s| U_C† U_B† (C/(n+1)) U_B U_C |s⟩`
written as a trace with `ρ_s = |s⟩⟨s|`.
-/
noncomputable def QAOACostVEV
    (n : ℕ) (J : SKCoupling n) (β γ : ℝ) : ℂ :=
  Matrix.trace
    (QAOACostMatrix n J β γ * rho_s n)

/--
Ensemble expectation over SK couplings:
`E_J(⟨s| U_C† U_B† (C/(n+1)) U_B U_C |s⟩)`.
`μ` is the probability measure for `J`.
-/
noncomputable def expectedQAOACostVEV
    (n : ℕ) (μ : MeasureTheory.Measure (SKCoupling n)) (β γ : ℝ) : ℂ :=
  ∫ J, QAOACostVEV n J β γ ∂μ


----------------------------------------------------------------
--------Expectation of the SK cost operator - Evaluation--------
----------------------------------------------------------------

/--
Insert complete computational-basis resolutions to expand
`E_J(⟨s|U_C† U_B† (C/(n+1)) U_B U_C|s⟩)` as an explicit `x,y,z` sum.
-/
theorem expectedQAOACostVEV_insert_basis
    (n : ℕ) (μ : MeasureTheory.Measure (SKCoupling n)) (β γ : ℝ) :
    expectedQAOACostVEV n μ β γ
      =
    ∫ J, ∑ x : BasisIdx n, ∑ y : BasisIdx n, ∑ z : BasisIdx n,
      star (s n x) *
        U_C_dagger_phase n J γ x *
        star (mixerKernel n β z x) *
        ((skCostOnBasis n J z / (n + 1 : ℝ)) : ℂ) *
        mixerKernel n β z y *
        U_C_phase n J γ y *
        s n y ∂μ := by
  unfold expectedQAOACostVEV QAOACostVEV QAOACostMatrix
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with J
  simp [Matrix.trace, Matrix.mul_apply, rho_s, pureDensity, mul_assoc, mul_left_comm, mul_comm]
  simp [Finset.mul_sum, mul_left_comm, mul_comm]

/--
Same basis expansion, emphasizing the replacement
`⟨z| (C/(n+1)) |z⟩ = C_J(z)/(n+1)` from diagonal action in the computational basis.
-/
theorem expectedQAOACostVEV_insert_basis_cost_value
    (n : ℕ) (μ : MeasureTheory.Measure (SKCoupling n)) (β γ : ℝ) :
    expectedQAOACostVEV n μ β γ
      =
    ∫ J, ∑ x : BasisIdx n, ∑ y : BasisIdx n, ∑ z : BasisIdx n,
      star (s n x) *
        U_C_dagger_phase n J γ x *
        star (mixerKernel n β z x) *
        ((skCostOnBasis n J z / (n + 1 : ℝ)) : ℂ) *
        mixerKernel n β z y *
        U_C_phase n J γ y *
        s n y ∂μ := by
  simpa using expectedQAOACostVEV_insert_basis n μ β γ

/-- Product of the two uniform-state amplitudes appearing in the basis expansion. -/
lemma s_star_mul_s_eq_const (n : ℕ) (x y : BasisIdx n) :
    star (s n x) * s n y = (((2 : ℂ)⁻¹) ^ (n + 1)) := by
  have hc2 : ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = (2 : ℂ)⁻¹ := by
    ring_nf
    simp [sqrt2_sq_complex]
  calc
    star (s n x) * s n y
        = (((Real.sqrt 2 : ℂ)⁻¹) ^ (n + 1)) * (((Real.sqrt 2 : ℂ)⁻¹) ^ (n + 1)) := by
            simp [s_entry_const]
    _ = ((((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹)) ^ (n + 1)) := by
          rw [← mul_pow]
    _ = (((2 : ℂ)⁻¹) ^ (n + 1)) := by simp [hc2]

/-- Pull a constant outside a triple finite sum. -/
lemma const_mul_triple_sum {n : ℕ} (c : ℂ) (f : BasisIdx n → BasisIdx n → BasisIdx n → ℂ) :
    (∑ x : BasisIdx n, ∑ y : BasisIdx n, ∑ z : BasisIdx n, c * f x y z)
      = c * (∑ x : BasisIdx n, ∑ y : BasisIdx n, ∑ z : BasisIdx n, f x y z) := by
  simp [Finset.mul_sum]

/--
After inserting basis resolutions, replace `star (s n x)` and `s n y`
by their constant value and merge the two factors into `((1/2)^(n+1))`.
-/
theorem expectedQAOACostVEV_insert_basis_replace_s_factors
    (n : ℕ) (μ : MeasureTheory.Measure (SKCoupling n)) (β γ : ℝ) :
    expectedQAOACostVEV n μ β γ
      =
    ∫ J, ∑ x : BasisIdx n, ∑ y : BasisIdx n, ∑ z : BasisIdx n,
      (((2 : ℂ)⁻¹) ^ (n + 1)) *
        (U_C_dagger_phase n J γ x *
          star (mixerKernel n β z x) *
          ((skCostOnBasis n J z / (n + 1 : ℝ)) : ℂ) *
          mixerKernel n β z y *
          U_C_phase n J γ y) ∂μ := by
  rw [expectedQAOACostVEV_insert_basis_cost_value]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with J
  refine Finset.sum_congr rfl ?_
  intro x hx
  refine Finset.sum_congr rfl ?_
  intro y hy
  refine Finset.sum_congr rfl ?_
  intro z hz
  calc
    star (s n x) *
        U_C_dagger_phase n J γ x *
        star (mixerKernel n β z x) *
        ((skCostOnBasis n J z / (n + 1 : ℝ)) : ℂ) *
        mixerKernel n β z y *
        U_C_phase n J γ y *
        s n y
        = (star (s n x) * s n y) *
      (U_C_dagger_phase n J γ x *
        star (mixerKernel n β z x) *
        ((skCostOnBasis n J z / (n + 1 : ℝ)) : ℂ) *
        mixerKernel n β z y *
        U_C_phase n J γ y) := by ring
    _ = (((2 : ℂ)⁻¹) ^ (n + 1)) *
      (U_C_dagger_phase n J γ x *
        star (mixerKernel n β z x) *
        ((skCostOnBasis n J z / (n + 1 : ℝ)) : ℂ) *
        mixerKernel n β z y *
        U_C_phase n J γ y) := by
          rw [s_star_mul_s_eq_const n x y]

/--
Pull the constant factor `((1/2)^(n+1))` outside the finite sums and then outside the integral.
-/
theorem expectedQAOACostVEV_insert_basis_pull_out_s_factor
    (n : ℕ) (μ : MeasureTheory.Measure (SKCoupling n)) (β γ : ℝ) :
    expectedQAOACostVEV n μ β γ
      =
    (((2 : ℂ)⁻¹) ^ (n + 1)) *
      (∫ J, ∑ x : BasisIdx n, ∑ y : BasisIdx n, ∑ z : BasisIdx n,
        U_C_dagger_phase n J γ x *
          star (mixerKernel n β z x) *
          ((skCostOnBasis n J z / (n + 1 : ℝ)) : ℂ) *
          mixerKernel n β z y *
          U_C_phase n J γ y ∂μ) := by
  let c : ℂ := (((2 : ℂ)⁻¹) ^ (n + 1))
  rw [expectedQAOACostVEV_insert_basis_replace_s_factors]
  calc
    (∫ J, ∑ x : BasisIdx n, ∑ y : BasisIdx n, ∑ z : BasisIdx n,
      c *
        (U_C_dagger_phase n J γ x *
          star (mixerKernel n β z x) *
          ((skCostOnBasis n J z / (n + 1 : ℝ)) : ℂ) *
          mixerKernel n β z y *
          U_C_phase n J γ y) ∂μ)
        =
    ∫ J, c *
      (∑ x : BasisIdx n, ∑ y : BasisIdx n, ∑ z : BasisIdx n,
        U_C_dagger_phase n J γ x *
          star (mixerKernel n β z x) *
          ((skCostOnBasis n J z / (n + 1 : ℝ)) : ℂ) *
          mixerKernel n β z y *
          U_C_phase n J γ y) ∂μ := by
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards with J
            exact (const_mul_triple_sum c
              (fun x y z =>
                U_C_dagger_phase n J γ x *
                  star (mixerKernel n β z x) *
                  ((skCostOnBasis n J z / (n + 1 : ℝ)) : ℂ) *
                  mixerKernel n β z y *
                  U_C_phase n J γ y))
    _ = c *
        (∫ J, ∑ x : BasisIdx n, ∑ y : BasisIdx n, ∑ z : BasisIdx n,
          U_C_dagger_phase n J γ x *
            star (mixerKernel n β z x) *
            ((skCostOnBasis n J z / (n + 1 : ℝ)) : ℂ) *
            mixerKernel n β z y *
            U_C_phase n J γ y ∂μ) := by
              rw [MeasureTheory.integral_const_mul]
    _ = (((2 : ℂ)⁻¹) ^ (n + 1)) *
        (∫ J, ∑ x : BasisIdx n, ∑ y : BasisIdx n, ∑ z : BasisIdx n,
          U_C_dagger_phase n J γ x *
            star (mixerKernel n β z x) *
            ((skCostOnBasis n J z / (n + 1 : ℝ)) : ℂ) *
            mixerKernel n β z y *
            U_C_phase n J γ y ∂μ) := by rfl

/--
Swap the order of the integral and the three finite sums in the expanded expected cost.
Assumption `hInt` means: for every basis triple `(x,y,z)`, the function of couplings
`J ↦ U_C_dagger_phase(x;J) * conj(mixerKernel(z,x)) * (C_J(z)/(n+1)) *
mixerKernel(z,y) * U_C_phase(y;J)`
is Bochner-integrable with respect to `μ`.
Equivalently, each such summand is measurable and has finite `L¹` norm, so
`∫ ‖f_{x,y,z}(J)‖ dμ < ∞`.
This is exactly the hypothesis needed to apply `MeasureTheory.integral_finset_sum`
repeatedly and justify
`∫ (∑ x, ∑ y, ∑ z, f x y z J) dμ = ∑ x, ∑ y, ∑ z, ∫ f x y z J dμ`.
-/
theorem expectedQAOACostVEV_swap_integral_sum
    (n : ℕ) (μ : MeasureTheory.Measure (SKCoupling n)) (β γ : ℝ)
    (hInt : ∀ x y z : BasisIdx n, MeasureTheory.Integrable
      (fun J : SKCoupling n =>
        U_C_dagger_phase n J γ x *
          star (mixerKernel n β z x) *
          ((skCostOnBasis n J z / (n + 1 : ℝ)) : ℂ) *
          mixerKernel n β z y *
          U_C_phase n J γ y) μ) :
    expectedQAOACostVEV n μ β γ
      =
    (((2 : ℂ)⁻¹) ^ (n + 1)) *
      (∑ x : BasisIdx n, ∑ y : BasisIdx n, ∑ z : BasisIdx n,
        ∫ J, U_C_dagger_phase n J γ x *
          star (mixerKernel n β z x) *
          ((skCostOnBasis n J z / (n + 1 : ℝ)) : ℂ) *
          mixerKernel n β z y *
          U_C_phase n J γ y ∂μ) := by
  rw [expectedQAOACostVEV_insert_basis_pull_out_s_factor]
  congr 1
  let f : BasisIdx n → BasisIdx n → BasisIdx n → SKCoupling n → ℂ :=
    fun x y z J =>
      U_C_dagger_phase n J γ x *
        star (mixerKernel n β z x) *
        ((skCostOnBasis n J z / (n + 1 : ℝ)) : ℂ) *
        mixerKernel n β z y *
        U_C_phase n J γ y
  have hswapX :
      (∫ J, ∑ x : BasisIdx n, ∑ y : BasisIdx n, ∑ z : BasisIdx n, f x y z J ∂μ)
        =
      ∑ x : BasisIdx n, ∫ J, ∑ y : BasisIdx n, ∑ z : BasisIdx n, f x y z J ∂μ := by
    simpa using
      (MeasureTheory.integral_finset_sum (μ := μ) (s := (Finset.univ : Finset (BasisIdx n)))
        (f := fun x J => ∑ y : BasisIdx n, ∑ z : BasisIdx n, f x y z J)
        (by
          intro x hx
          exact MeasureTheory.integrable_finset_sum
            (μ := μ) (s := (Finset.univ : Finset (BasisIdx n)))
            (f := fun y J => ∑ z : BasisIdx n, f x y z J)
            (by
              intro y hy
              exact MeasureTheory.integrable_finset_sum
                (μ := μ) (s := (Finset.univ : Finset (BasisIdx n)))
                (f := fun z J => f x y z J)
                (by intro z hz; simpa [f] using hInt x y z))))
  have hswapY :
      (∑ x : BasisIdx n, ∫ J, ∑ y : BasisIdx n, ∑ z : BasisIdx n, f x y z J ∂μ)
        =
      ∑ x : BasisIdx n, ∑ y : BasisIdx n, ∫ J, ∑ z : BasisIdx n, f x y z J ∂μ := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    simpa using
      (MeasureTheory.integral_finset_sum (μ := μ) (s := (Finset.univ : Finset (BasisIdx n)))
        (f := fun y J => ∑ z : BasisIdx n, f x y z J)
        (by
          intro y hy
          exact MeasureTheory.integrable_finset_sum
            (μ := μ) (s := (Finset.univ : Finset (BasisIdx n)))
            (f := fun z J => f x y z J)
            (by intro z hz; simpa [f] using hInt x y z)))
  have hswapZ :
      (∑ x : BasisIdx n, ∑ y : BasisIdx n, ∫ J, ∑ z : BasisIdx n, f x y z J ∂μ)
        =
      ∑ x : BasisIdx n, ∑ y : BasisIdx n, ∑ z : BasisIdx n, ∫ J, f x y z J ∂μ := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    refine Finset.sum_congr rfl ?_
    intro y hy
    simpa using
      (MeasureTheory.integral_finset_sum (μ := μ) (s := (Finset.univ : Finset (BasisIdx n)))
        (f := fun z J => f x y z J)
        (by intro z hz; simpa [f] using hInt x y z))
  calc
    (∫ J, ∑ x : BasisIdx n, ∑ y : BasisIdx n, ∑ z : BasisIdx n, f x y z J ∂μ)
        = ∑ x : BasisIdx n, ∫ J, ∑ y : BasisIdx n, ∑ z : BasisIdx n, f x y z J ∂μ := hswapX
    _ = ∑ x : BasisIdx n, ∑ y : BasisIdx n, ∫ J, ∑ z : BasisIdx n, f x y z J ∂μ := hswapY
    _ = ∑ x : BasisIdx n, ∑ y : BasisIdx n, ∑ z : BasisIdx n, ∫ J, f x y z J ∂μ := hswapZ
    _ = ∑ x : BasisIdx n, ∑ y : BasisIdx n, ∑ z : BasisIdx n,
          ∫ J, U_C_dagger_phase n J γ x *
            star (mixerKernel n β z x) *
            ((skCostOnBasis n J z / (n + 1 : ℝ)) : ℂ) *
            mixerKernel n β z y *
            U_C_phase n J γ y ∂μ := by
          simp [f]

/--
In the swapped-sum form, `mixerKernel n β z x` and `mixerKernel n β z y` are independent of `J`,
so they can be factored outside each `J`-integral.
-/
theorem expectedQAOACostVEV_pull_kernels_outside_integral
    (n : ℕ) (μ : MeasureTheory.Measure (SKCoupling n)) (β γ : ℝ)
    (hInt : ∀ x y z : BasisIdx n, MeasureTheory.Integrable
      (fun J : SKCoupling n =>
        U_C_dagger_phase n J γ x *
          star (mixerKernel n β z x) *
          ((skCostOnBasis n J z / (n + 1 : ℝ)) : ℂ) *
          mixerKernel n β z y *
          U_C_phase n J γ y) μ) :
    expectedQAOACostVEV n μ β γ
      =
    (((2 : ℂ)⁻¹) ^ (n + 1)) *
      (∑ x : BasisIdx n, ∑ y : BasisIdx n, ∑ z : BasisIdx n,
        (star (mixerKernel n β z x) * mixerKernel n β z y) *
          (∫ J, U_C_dagger_phase n J γ x *
            ((skCostOnBasis n J z / (n + 1 : ℝ)) : ℂ) *
            U_C_phase n J γ y ∂μ)) := by
  rw [expectedQAOACostVEV_swap_integral_sum n μ β γ hInt]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro x hx
  refine Finset.sum_congr rfl ?_
  intro y hy
  refine Finset.sum_congr rfl ?_
  intro z hz
  calc
    (∫ J, U_C_dagger_phase n J γ x *
      star (mixerKernel n β z x) *
      ((skCostOnBasis n J z / (n + 1 : ℝ)) : ℂ) *
      mixerKernel n β z y *
      U_C_phase n J γ y ∂μ)
        =
    (∫ J, (star (mixerKernel n β z x) * mixerKernel n β z y) *
      (U_C_dagger_phase n J γ x *
        ((skCostOnBasis n J z / (n + 1 : ℝ)) : ℂ) *
        U_C_phase n J γ y) ∂μ) := by
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards with J
          simp [mul_assoc, mul_left_comm, mul_comm]
    _ =
    (star (mixerKernel n β z x) * mixerKernel n β z y) *
      (∫ J, U_C_dagger_phase n J γ x *
        ((skCostOnBasis n J z / (n + 1 : ℝ)) : ℂ) *
        U_C_phase n J γ y ∂μ) := by
          rw [MeasureTheory.integral_const_mul]
