import Leanum

/-- 
  Helper to force evaluation. 
  Without this, Lean's lazy features might skip the computation.
-/
def checksum (mat : Matrix m n) : Float :=
  mat.data.foldl (· + ·) 0.0

/-- 
  Measures the throughput of performing an operation on a batch of matrices.
  This avoids stack overflows by keeping individual matrix sizes small 
  but increases the total work by repeating the operation many times.
-/
def run_batch_bench (name : String) (batch_size : Nat) (ops_per_mat : Float) (op : Unit → Matrix m n) : IO Unit := do
  let start ← IO.monoNanosNow
  
  let mut total_check := 0.0
  for _ in [:batch_size] do
    let res := op ()
    total_check := total_check + checksum res
    
  let finish ← IO.monoNanosNow
  
  let duration_secs := (finish - start).toFloat / 1_000_000_000.0
  let total_ops := ops_per_mat * batch_size.toFloat
  let gflops := if duration_secs > 0 then (total_ops / duration_secs) / 1_000_000_000.0 else 0.0
  
  let pad := String.mk (List.replicate (25 - name.length) ' ')
  IO.println s!"{name}{pad} | Batch: {batch_size} | Time: {duration_secs.toString.take 6}s | GFLOPS: {gflops.toString.take 6} | Check: {total_check}"

def main : IO Unit := do
  -- Configuration: Small matrices, large batches
  let size := 32 
  let batch_size := 100
  
  let m := size; let n := size; let k := size
  
  IO.println s!"--- Batch Benchmark: {batch_size} iterations of {size}x{size} matrices ---"
  
  let a := ones m n
  let b := ones n k

  -- 1. Addition Bench (M * N operations per matrix)
  let add_ops := (m * n).toFloat
  run_batch_bench "Batch Addition" batch_size add_ops (fun _ => a + b)

  -- 2. Transpose Bench (M * N operations per matrix)
  if hm : m > 0 then
    let trans_ops := (m * n).toFloat
    run_batch_bench "Batch Transpose" batch_size trans_ops (fun _ => a.T (hm := ⟨Nat.ne_of_gt hm⟩))

  -- 3. Multiplication Bench (2 * M * N * K operations per matrix)
  if hk : k > 0 then
    let mul_ops := 2.0 * m.toFloat * n.toFloat * k.toFloat
    run_batch_bench "Batch Multiplication" batch_size mul_ops (fun _ => inner (hk := ⟨Nat.ne_of_gt hk⟩) a b)

  -- 4. UFunc Bench (M * N operations per matrix)
  run_batch_bench "Batch Sin (UFunc)" batch_size add_ops (fun _ => sin_mat a)

  IO.println "------------------------------------------------------------"
