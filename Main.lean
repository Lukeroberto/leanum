import Leanum

def testMata : Matrix 2 3 := { 
  data := #[1.1, 1.2, 1.3, 2.1, 2.3, 3] 
  data_size := by rfl
}

def testMatb : Matrix 2 3 := { 
  data := #[2.0, 3.0, 4.0, 5.0, 1.0, 2.0] 
  data_size := by rfl
}

def testMatc : Matrix 2 2 := { 
  data := #[1.0, 0.0, 0.0, 1.0] 
  data_size := by rfl
}

#eval testMata
#eval testMata + testMatb 
#eval testMatc
#eval eye 5
#eval sin_mat testMata
#eval exp_mat testMata

