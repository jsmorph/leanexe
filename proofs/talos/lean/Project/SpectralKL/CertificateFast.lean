import Project.SpectralKL.CertificateSound

namespace Project.SpectralKL.Certificate.Fast
open Matrix Samples
open scoped Matrix
variable {m : Nat}

/-- Keep the vector as data throughout accumulation. Returning a function here
would allow eta expansion to move allocation inside each coordinate lookup. -/
def store (v : Fin m → ℚ) : Vector ℚ m := Vector.ofFn v
def view (v : Vector ℚ m) : Fin m → ℚ := fun i => v[i.val]

@[simp] theorem view_store (v : Fin m → ℚ) : view (store v) = v := by
  ext i
  simp [view, store]

def sumRows (rows : List (Fin m → ℚ)) (acc : Vector ℚ m) : Vector ℚ m :=
  rows.foldl (fun a v => store (view a+v)) acc

theorem sumRows_eq (rows : List (Fin m → ℚ)) (acc : Vector ℚ m) :
    view (sumRows rows acc) = view acc + meanSum rows := by
  induction rows generalizing acc with
  | nil => simp [sumRows, meanSum]
  | cons v vs ih => simpa [sumRows, meanSum, add_assoc] using ih (store (view acc+v))

def mean (rows : List (Fin m → ℚ)) : Vector ℚ m :=
  store ((1 / (rows.length : ℚ)) • view (sumRows rows (store 0)))

@[simp] theorem mean_eq (rows : List (Fin m → ℚ)) : view (mean rows) = Samples.mean rows := by
  simp [mean, sumRows_eq, Samples.mean]

def applyRows (rows : List (Fin m → ℚ)) (x : Fin m → ℚ) (acc : Vector ℚ m) : Vector ℚ m :=
  rows.foldl (fun a v => let t := v ⬝ᵥ x; store (view a + t • v)) acc

theorem applyRows_eq (rows : List (Fin m → ℚ)) (x : Fin m → ℚ) (acc : Vector ℚ m) :
    view (applyRows rows x acc) = view acc + actionSum x rows := by
  induction rows generalizing acc with
  | nil => simp [applyRows, actionSum]
  | cons v vs ih =>
    simpa [applyRows, actionSum, add_assoc] using ih (store (view acc+(v ⬝ᵥ x) • v))

def action (rows : List (Fin m → ℚ)) (x : Fin m → ℚ) : Vector ℚ m :=
  store ((1 / (rows.length : ℚ)) • view (applyRows rows x (store 0)))

@[simp] theorem action_eq (rows : List (Fin m → ℚ)) (x : Fin m → ℚ) :
    view (action rows x) = Samples.action rows x := by
  simp [action, applyRows_eq, Samples.action]

def cell (p q : List (Fin m → ℚ)) (d : Vector ℚ m)
    (eta a b : ℚ) (x : Fin m → ℚ) : Bounds ℚ :=
  let px := action p x
  let qx := action q x
  let u := 2 * (view d ⬝ᵥ x) - x ⬝ᵥ (view qx + eta • x)
  let v := x ⬝ᵥ (view qx-view px)
  let ra := store (view d - (a • view px + (1-a) • view qx + eta • x))
  let rb := store (view d - (b • view px + (1-b) • view qx + eta • x))
  let e := ((view ra ⬝ᵥ view ra) + (view rb ⬝ᵥ view rb)) / eta
  let w := (b-a) - (b^2-a^2)/2
  let z := (b^2-a^2)/2 - (b^3-a^3)/3
  let lower := u*w+v*z
  ⟨lower, lower+e*w⟩

theorem cell_eq (p q : List (Fin m → ℚ)) (eta a b : ℚ) (x : Fin m → ℚ) :
    cell p q (store (Samples.mean p - Samples.mean q)) eta a b x =
      Certificate.cell p q eta a b x := by simp [cell, Certificate.cell]

def enclose (p q : List (Fin m → ℚ)) (d : Vector ℚ m) (eta : ℚ) :
    ℚ → List (ℚ × (Fin m → ℚ)) → Option (Bounds ℚ)
  | a, [] => if a = 1 then some ⟨0,0⟩ else none
  | a, (b,x) :: xs =>
      if 0 ≤ a ∧ a ≤ b ∧ b ≤ 1 then
        match enclose p q d eta b xs with
        | none => none
        | some rest => some (add (cell p q d eta a b x) rest)
      else none

theorem enclose_eq (p q : List (Fin m → ℚ)) (eta a : ℚ)
    (cells : List (ℚ × (Fin m → ℚ))) :
    enclose p q (store (view (mean p) - view (mean q))) eta a cells =
      Certificate.enclose p q eta a cells := by
  induction cells generalizing a with
  | nil => rfl
  | cons c cs ih =>
    rcases c with ⟨b,x⟩
    simp only [mean_eq] at ih
    simp only [enclose, Certificate.enclose, ih, mean_eq, cell_eq]
    rfl

/-- The stored-vector implementation returns the same mathematical guarantee,
while retaining the already computed enclosure for the audit output. -/
def certify (p q : List (Fin m → ℚ)) (eta score tolerance : ℚ)
    (cells : List (ℚ × (Fin m → ℚ))) :
    Option (VerifiedScore p q eta tolerance × Bounds ℚ) :=
  if hg : p.isEmpty || q.isEmpty || eta ≤ 0 || tolerance < 0 then none
  else
    match hb : enclose p q (store (view (mean p) - view (mean q))) eta 0 cells with
    | none => none
    | some bound =>
      if hc : score-tolerance ≤ bound.lower ∧ bound.upper ≤ score+tolerance then
        have ha : accepts p q eta score tolerance cells = true := by
          simp only [enclose_eq] at hb
          simp [accepts, hg, hb, hc]
        some (⟨score,accepts_sound p q eta score tolerance cells ha⟩,bound)
      else none

theorem certify_score (p q : List (Fin m → ℚ)) (eta score tolerance : ℚ)
    (cells : List (ℚ × (Fin m → ℚ)))
    (result : VerifiedScore p q eta tolerance × Bounds ℚ)
    (h : certify p q eta score tolerance cells = some result) : result.1.score = score := by
  unfold certify at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · cases Option.some.inj h
        rfl
      · simp at h

/-- Public numerical guarantee naming the function called by the native checker
and the proposed score passed by the CLI. -/
theorem accepted_error (p q : List (Fin m → ℚ)) (eta score tolerance : ℚ)
    (cells : List (ℚ × (Fin m → ℚ)))
    (result : VerifiedScore p q eta tolerance × Bounds ℚ)
    (h : certify p q eta score tolerance cells = some result) :
    |(score:ℝ)-target (realRows p) (realRows q) (eta:ℝ)| ≤ (tolerance:ℝ) := by
  simpa only [certify_score p q eta score tolerance cells result h] using result.1.accuracy

#print axioms certify
#print axioms certify_score
#print axioms accepted_error
end Project.SpectralKL.Certificate.Fast
