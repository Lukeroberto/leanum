
structure Matrix (m n : Nat) where
  data : Array Float
  data_size : data.size = m * n

instance : ToString (Matrix m n) where
  toString mat :=
    let rowStrings := (List.range m).map fun i =>
      let row := mat.data[i*n : (i + 1) * n]
      toString row
    String.intercalate "\n" rowStrings


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

