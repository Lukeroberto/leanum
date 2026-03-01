
structure Matrix (m n : Nat) where
  data : Array Float
  data_size : data.size = m * n

instance : ToString (Matrix m n) where
  toString mat :=
    let rowStrings := (List.range m).map fun i =>
      let row := mat.data[i*n : (i + 1) * n]
      toString row
    String.intercalate "\n" rowStrings

instance : GetElem (Matrix m n) (Nat × Nat) Float (fun _ idx => idx.1 < m ∧ idx.2 < n) where
  getElem mat idx h :=
    let (i, j) := idx
    let ⟨hi, hj⟩ := h
    mat.data[i * n + j]'(by
      rw [mat.data_size]

      -- 2. Since i < m, we know (i + 1) * n <= m * n
      have h_upper : (i + 1) * n ≤ m * n := Nat.mul_le_mul_right n hi
      
      -- 3. Expanding (i + 1) * n gives us i * n + n
      rw [Nat.succ_mul] at h_upper 
      
      -- 4. Since j < n, we know i * n + j < i * n + n
      have h_lower : i * n + j < i * n + n := Nat.add_lt_add_left hj (i * n)
      
      -- 5. Combine: i * n + j < i * n + n <= m * n
      exact Nat.lt_of_lt_of_le h_lower h_upper
    )

def Matrix.T {m n : Nat} [hm : NeZero m] (mat : Matrix m n) : Matrix n m := 
  let range := Array.range (n * m)
  let data := range.attach.map fun ⟨k, hk⟩ =>
    let j := k / m
    let i := k % m
    
    -- 1. Convert membership to inequality
    have h_k_lt : k < n * m := Array.mem_range.1 hk
    
    -- 2. Handle the n*m vs m*n commutativity
    have h_bound : k < m * n := (Nat.mul_comm n m) ▸ h_k_lt
    
    -- 3. Final index proofs
    have hi : i < m := Nat.mod_lt k (Nat.pos_of_ne_zero hm.out)
    have hj : j < n := Nat.div_lt_of_lt_mul h_bound
    
    mat[(i, j)]'⟨hi, hj⟩

  { data := data, 
    data_size := by simp [data, range, Array.size_range] }

-- Array Creation 
------------------------------------------------------

def fill (m n : Nat) (val : Float) : Matrix m n := {
  data := Array.replicate (m * n) val,
  data_size := by simp
}

def zeros (m n : Nat) : Matrix m n := fill m n 0.0
def ones (m n : Nat) : Matrix m n := fill m n 1.0

def eye (n : Nat) : Matrix n n := 
  let data := (Array.range (n * n)).map fun i =>
    let row := i / n
    let col := i % n
    if row == col then 1.0 else 0.0
  { data := data, 
    data_size := by simp [data]
  }

-- UFuncs
------------------------------------------------------

instance : Add (Matrix m n) where
  add a b := 
    let newData := Array.zipWith (. + .) a.data b.data
    { data := newData,
      data_size := by
        have h1 := a.data_size
        have h2 := b.data_size
        simp [newData, h1, h2]
    }


def apply_ufunc (f : Float -> Float) (mat : Matrix m n) : Matrix m n := 

  let mapped_data := mat.data.map f
  {
    data := mapped_data
    data_size := by 
      simp [mapped_data, Array.size_map, mat.data_size]
  }


def sin_mat (mat : Matrix m n) : Matrix m n := apply_ufunc Float.sin mat
def cos_mat (mat : Matrix m n) : Matrix m n := apply_ufunc Float.cos mat
def exp_mat (mat : Matrix m n) : Matrix m n := apply_ufunc Float.exp mat
def log_mat (mat : Matrix m n) : Matrix m n := apply_ufunc Float.log mat


-- Basic Linear Algebra

def dot (matA : Matrix 1 n) (matB : Matrix n 1) : Float := 
  let products := matA.data.zipWith (. * .) matB.data
  products.foldl (. + .) 0.0

def inner [hk : NeZero k] (matA : Matrix m n) (matB : Matrix n k) : Matrix m k := 
  let rangeMK := Array.range (m * k)
  let data := rangeMK.attach.map fun ⟨idx, h_idx⟩ =>
    -- 1. Get coordinates for the result cell
    let r := idx / k
    let c := idx % k
    
    -- 2. Proofs for result coordinates (r < m, c < k)
    have h_idx_lt : idx < m * k := Array.mem_range.1 h_idx
    have hr : r < m := Nat.div_lt_of_lt_mul ((Nat.mul_comm m k) ▸ h_idx_lt)
    have hc : c < k := Nat.mod_lt idx (Nat.pos_of_ne_zero hk.out)

    -- 3. Sum over the shared dimension 'n'
    let rangeN := Array.range n
    rangeN.attach.foldl (init := 0.0) fun acc ⟨l, hl⟩ =>
      let hl_lt : l < n := Array.mem_range.1 hl
      -- Multiply matA[r, l] by matB[l, c]
      acc + matA[(r, l)]'⟨hr, hl_lt⟩ * matB[(l, c)]'⟨hl_lt, hc⟩

  { data := data, data_size := by simp [data, rangeMK, Array.size_range] }
    


