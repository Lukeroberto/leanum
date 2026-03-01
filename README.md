# leanum (WIP)

This package provides a lean implementation closely mirroring numpy.


This package includes:

- [x] Matrix dependent type
- [ ] NDarray object
- [x] Universal functions (element-wise operations)
    - [x] sin
    - [x] cos 
    - [x] log
    - [x] exp
- [x] Array creation routines
    - [x] zeros 
    - [x] ones
    - [x] eye
    - [x] fill
- [ ] linear algebra routines
    - [x] dot
    - [x] inner 
    - [ ] eigen
- [ ] array manipulation
    - [ ] reshape
    - [ ] stack 
    - [ ] transpose

Current Benchmarks (AMD Ryzen Threadripper 2950X 16-Core Processor):

--- Batch Benchmark: 100 iterations of 32x32 matrices ---
Batch Addition            | Batch: 100 | Time: 0.0019s | GFLOPS: 0.0514 | 
Batch Transpose           | Batch: 100 | Time: 0.0078s | GFLOPS: 0.0130 | 
Batch Multiplication      | Batch: 100 | Time: 0.2586s | GFLOPS: 0.0253 | 
Batch Sin (UFunc)         | Batch: 100 | Time: 0.0022s | GFLOPS: 0.0456 | 
