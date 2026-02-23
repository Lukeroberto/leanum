
structure Matrix (m n : Nat) where
  data : Array Float
  data_size : data.size = m * n

instance : ToString (Matrix m n) where
  toString mat :=
    let rowStrings := (List.range m).map fun i =>
      let row := mat.data[i*n : (i + 1) * n]
      toString row
    String.intercalate "\n" rowStrings

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

def testMata : Matrix 2 3 := { 
  data := #[1.1, 1.2, 1.3, 2.1, 2.2, 2.3] 
  data_size := by rfl
}

def testMatb : Matrix 2 3 := { 
  data := #[2.0, 3.0, 4.0, 5.0, 1.0, 2.0] 
  data_size := by rfl
}

def testMatc : Matrix 2 2 := { 
  data := #[1.0, 0.0, 1.0, 0.0] 
  data_size := by rfl
}

#eval testMata
#eval testMatb
#eval testMatc
#eval eye 4


