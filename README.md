# formal-verification
Repository for practicing PlusCal (TLA+) and temporal logic

## Build C++ impl
in `cxx_impl` dir:
```
clang++-15 -std=c++20 -pthread -latomic main.cc
```
Next install **Anaconda!**
Install **spot via conda**
```
conda create --name myenv python=3.8 # adjust as desired
conda activate myenv
conda install -c conda-forge spot
```

## Run
```
cxx_impl/a.out &> trace.log
python3 verifier.py trace.log model.hoa
```


## See Also
```
cxx_impl/boundedQueue
TLA_practice/
```
